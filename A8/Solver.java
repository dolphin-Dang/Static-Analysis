/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.MapSetMultiMap;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.util.collection.Pair;

import java.awt.*;
import java.util.Map;
import java.util.Set;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    private MultiMap<Pointer, Pair<Pointer, Type>> taintFlowGraph;
    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        taintFlowGraph = Maps.newMultiMap();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if(!callGraph.contains(csMethod)){
            callGraph.addReachableMethod(csMethod);
            csMethod.getMethod().getIR().getStmts().forEach(stmt->{
                        stmt.accept(new StmtProcessor(csMethod));
                    }
            );
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt){
            Pointer pointer = csManager.getCSVar(this.context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            PointsToSet pointsToSet = PointsToSetFactory.make(csManager.getCSObj(heapContext, obj));
            workList.addEntry(pointer, pointsToSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt){
            Pointer src = csManager.getCSVar(context, stmt.getRValue());
            Pointer dst = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(src, dst);
            return null;
        }

        @Override
        public Void visit(StoreField stmt){
            // T.f = y
            // y -> T.f
            if(stmt.isStatic()){
                Pointer src = csManager.getCSVar(context, stmt.getRValue());
                Pointer dst = csManager.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(src, dst);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt){
            if(stmt.isStatic()){
                Pointer src = csManager.getStaticField(stmt.getFieldRef().resolve());
                Pointer dst = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(src, dst);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt){
            if(stmt.isStatic()){
                // static call here, arg to result transfer only
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context calleeContext = contextSelector.selectContext(csCallSite, callee);
                CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee))){
                    addReachable(csCallee);
                    // a_i -> m_i
                    for(int i=0; i<callee.getParamCount(); i++){
                        Pointer src = csManager.getCSVar(context, stmt.getInvokeExp().getArg(i));
                        Pointer dst = csManager.getCSVar(calleeContext, callee.getIR().getParam(i));
                        addPFGEdge(src, dst);
                        if(stmt.getResult() != null){
                            // have result, do arg to result transfer
                            // get type from taint config and return back
                            Type a2rtype = taintAnalysis.Arg2Result(callee, i);
                            if(a2rtype != null){
                                CSVar result = csManager.getCSVar(calleeContext, stmt.getResult());
                                addTFGEdge(src, result, a2rtype);
//                                taintFlowGraph.put(src, new Pair<>(result, a2rtype));
                            }

                        }
                    }
                    // m_ret ->r
                    for(int i=0; i<callee.getIR().getReturnVars().size(); i++){
                        Var r = stmt.getLValue();
                        if(r != null){
                            Pointer src = csManager.getCSVar(calleeContext, callee.getIR().getReturnVars().get(i));
                            addPFGEdge(src, csManager.getCSVar(context, r));
                        }
                    }
                    if(stmt.getResult() != null){
                        // result not null -> add taint obj to wl
                        // be source here
                        Type type = taintAnalysis.getMethodTypeSource(callee);
                        if(type != null){
                            Pointer dst = csManager.getCSVar(context, stmt.getResult());

                            PointsToSet pts = PointsToSetFactory.make(taintAnalysis.getTaintObj(stmt, type));
                            workList.addEntry(dst, pts);
                        }

                    }
                }

            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source, target)){
            // PFG changed
            if(!source.getPointsToSet().isEmpty()){
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }
    private void addTFGEdge(Pointer source, Pointer target, Type type){
        if(taintFlowGraph.put(source, new Pair<>(target, type))){
            PointsToSet pts = source.getPointsToSet();
            PointsToSet taintSet = PointsToSetFactory.make();
            for(CSObj csObj: pts){
                if(taintAnalysis.isTaint(csObj)){
//                    System.out.println("here");
                    CSObj taintObj = taintAnalysis.getTaintObj(taintAnalysis.getSource(csObj), type);
                    taintSet.addObject(taintObj);
                }
            }
            if(!taintSet.isEmpty()){
                workList.addEntry(target, taintSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            Pointer ptr = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(ptr, pts);

            if(ptr instanceof CSVar csVar){
                Var var = csVar.getVar();
                Context context = csVar.getContext();

                for(CSObj o: delta){
                    var.getStoreFields().forEach(stmt -> {
                        // x.f = y
                        JField field = stmt.getFieldRef().resolve();
                        addPFGEdge(csManager.getCSVar(context, stmt.getRValue()),
                                csManager.getInstanceField(o, field));
                    });
                    var.getLoadFields().forEach(stmt -> {
                        // y = x.f
                        JField field = stmt.getFieldRef().resolve();
                        addPFGEdge(csManager.getInstanceField(o, field),
                                csManager.getCSVar(context, stmt.getLValue()));
                    });
                    var.getStoreArrays().forEach(stmt -> {
                        // x[*] = y
                        addPFGEdge(csManager.getCSVar(context, stmt.getRValue()),
                                csManager.getArrayIndex(o));
                    });
                    var.getLoadArrays().forEach(stmt -> {
                        // y = x[*]
                        addPFGEdge(csManager.getArrayIndex(o),
                                csManager.getCSVar(context, stmt.getLValue()));
                    });
                    processCall(csVar, o);
                }

            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = PointsToSetFactory.make();

        for(CSObj o: pointsToSet){
            if(pointer.getPointsToSet().addObject(o)){
                delta.addObject(o);
                // propagate taint objs
                if(taintAnalysis.isTaint(o)){
                    // real taint obj
                    taintFlowGraph.get(pointer).forEach(elem -> {
                        // taint flow from pointer to elem
                        Invoke srcCall = taintAnalysis.getSource(o);
                        // change type

                        CSObj taintObj = taintAnalysis.getTaintObj(srcCall, elem.second());
                        workList.addEntry(elem.first(), PointsToSetFactory.make(taintObj));
                    });
                }
            }
        }
        // check if delta is empty now
        if(!delta.isEmpty()){
            pointerFlowGraph.getSuccsOf(pointer).forEach(ptr -> {
                workList.addEntry(ptr, delta);
            });

        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        recv.getVar().getInvokes().forEach(invoke -> {
            // Dispatch
            JMethod callee = resolveCallee(recvObj, invoke);
            // Select
            Context callSiteContext = recv.getContext();
            CSCallSite csCallSite = csManager.getCSCallSite(callSiteContext, invoke);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            // add this to WL
            workList.addEntry(csManager.getCSVar(calleeContext, callee.getIR().getThis()),
                    PointsToSetFactory.make(recvObj));
            // if not in call-graph
            CSMethod csMethod = csManager.getCSMethod(calleeContext, callee);
            if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),
                    csCallSite, csMethod))){
                addReachable(csMethod);
                // for-each add a_i -> p_i
                for(int i=0; i<invoke.getInvokeExp().getArgCount(); i++){
                    Pointer src = csManager.getCSVar(callSiteContext, invoke.getInvokeExp().getArg(i));
                    Pointer dst = csManager.getCSVar(calleeContext, callee.getIR().getParam(i));
                    addPFGEdge(src, dst);
                    // taint arg 2 base / arg 2 result
                    Type a2bType = taintAnalysis.Arg2Base(callee, i);
                    if(a2bType != null){
                        addTFGEdge(src, recv, a2bType);
//                        taintFlowGraph.put(src, new Pair<>(recv, a2bType));
                    }

                    if(invoke.getResult() != null){
                        // have result: do arg2result
                        Type a2rType = taintAnalysis.Arg2Result(callee, i);
                        if(a2rType != null){
                            CSVar result = csManager.getCSVar(callSiteContext, invoke.getResult());
                            addTFGEdge(src, result, a2rType);
//                            taintFlowGraph.put(src, new Pair<>(result, a2rType));
                        }

                    }
                }
                // m_ret -> r
                for(int i=0; i<callee.getIR().getReturnVars().size(); i++){
                    Var r = invoke.getLValue();
                    // bug here that r is null ?!
                    // the return val can be null !!!
                    if(r != null){
                        Var m_ret = callee.getIR().getReturnVars().get(i);
                        addPFGEdge(csManager.getCSVar(calleeContext, m_ret),
                                csManager.getCSVar(callSiteContext, r));
                    }
                }
                if(invoke.getResult() != null){
                    // be source here
                    Type type = taintAnalysis.getMethodTypeSource(callee);
                    if(type != null){
                        Pointer dst = csManager.getCSVar(calleeContext, invoke.getResult());
                        PointsToSet pts = PointsToSetFactory.make(taintAnalysis.getTaintObj(invoke, type));
                        workList.addEntry(dst, pts);
                    }

                    // base 2 result
                    Type b2rType = taintAnalysis.Base2Result(callee);
                    if(b2rType != null){
                        CSVar result = csManager.getCSVar(callSiteContext, invoke.getResult());
                        addTFGEdge(recv, result, b2rType);
//                        taintFlowGraph.put(recv, new Pair<>(result, b2rType));
                    }

                }
            }

        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    public JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
