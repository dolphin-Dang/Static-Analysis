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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import pascal.taie.language.classes.JField;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(!callGraph.contains(method)){
            callGraph.addReachableMethod(method);
            method.getIR().getStmts().forEach(stmt -> {
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(Invoke stmt){
            if(stmt.isStatic()){
                JMethod callee = resolveCallee(null, stmt);
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, callee))){
                    // another new method callee
                    addReachable(callee);
                    // a_i -> m_i
                    for(int i=0; i<callee.getParamCount(); i++){
                        Var m_i = callee.getIR().getParam(i);
                        Var a_i = stmt.getInvokeExp().getArg(i);
                        addPFGEdge(pointerFlowGraph.getVarPtr(a_i), pointerFlowGraph.getVarPtr(m_i));
                    }
                    // m_ret -> r
                    for(int i=0; i<callee.getIR().getReturnVars().size(); i++){
                        Var r = stmt.getLValue();
                        if(r != null){
                            Var m_ret = callee.getIR().getReturnVars().get(i);
                            addPFGEdge(pointerFlowGraph.getVarPtr(m_ret), pointerFlowGraph.getVarPtr(r));
                        }
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(New stmt){
            VarPtr ptr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(ptr, new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        @Override
        public Void visit(Copy stmt){
            // x = y
            // addEdge(y, x)
            VarPtr x = pointerFlowGraph.getVarPtr(stmt.getLValue());
            VarPtr y = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(y, x);
            return null;
        }

        @Override
        public Void visit(StoreField stmt){
            // T.f = y
            // y -> T.f
            if(stmt.isStatic()){
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = pointerFlowGraph.getStaticField(field);
                VarPtr ptr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(ptr, staticField);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt){
            // y = T.f
            // T.f -> y
            if(stmt.isStatic()){
                JField field = stmt.getFieldRef().resolve();
                StaticField staticField = pointerFlowGraph.getStaticField(field);
                VarPtr ptr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(staticField, ptr);
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
                // ptr(source) not empty
                workList.addEntry(target, source.getPointsToSet());
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
            PointsToSet p2s = entry.pointsToSet();
            PointsToSet delta = propagate(ptr, p2s);

            if(ptr instanceof VarPtr varPtr){
                Var var = varPtr.getVar();
                List<StoreField> storeFields = var.getStoreFields();
                List<LoadField> loadFields = var.getLoadFields();
                List<StoreArray> storeArrays = var.getStoreArrays();
                List<LoadArray> loadArrays = var.getLoadArrays();

                for(Obj o: delta){
                    storeFields.forEach(stmt -> {
                        // x.f = y
                        JField field = stmt.getFieldRef().resolve();
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getInstanceField(o, field));
                    });
                    loadFields.forEach(stmt -> {
                        // y = x.f
                        JField field = stmt.getFieldRef().resolve();
                        addPFGEdge(pointerFlowGraph.getInstanceField(o, field), pointerFlowGraph.getVarPtr(stmt.getLValue()));
                    });
                    storeArrays.forEach(stmt -> {
                        // x[*] = y
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getArrayIndex(o));
                    });
                    loadArrays.forEach(stmt -> {
                        // y = x[*]
                        addPFGEdge(pointerFlowGraph.getArrayIndex(o), pointerFlowGraph.getVarPtr(stmt.getLValue()));
                    });
                    processCall(var, o);
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
        PointsToSet delta = new PointsToSet();

        // if(!pointsToSet.isEmpty()){ ::: no need to do this cause pointsToSet here is not delta.

        for(Obj o: pointsToSet){
            if(pointer.getPointsToSet().addObject(o)){
                delta.addObject(o);
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
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        List<Invoke> invokeList = var.getInvokes();
        invokeList.forEach(invoke -> {
            JMethod callee = resolveCallee(recv, invoke);
            workList.addEntry(pointerFlowGraph.getVarPtr(callee.getIR().getThis()), new PointsToSet(recv));

            if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, callee))){
                addReachable(callee);
                for(int i=0; i<callee.getParamCount(); i++){
                    Var m_i = callee.getIR().getParam(i);
                    Var a_i = invoke.getInvokeExp().getArg(i);
                    addPFGEdge(pointerFlowGraph.getVarPtr(a_i), pointerFlowGraph.getVarPtr(m_i));
                }
                // m_ret -> r
                for(int i=0; i<callee.getIR().getReturnVars().size(); i++){
                    Var r = invoke.getLValue();
                    // bug here that r is null ?!
                    // the return val can be null !!!
                    if(r != null){
                        Var m_ret = callee.getIR().getReturnVars().get(i);
                        addPFGEdge(pointerFlowGraph.getVarPtr(m_ret), pointerFlowGraph.getVarPtr(r));
                    }
                }
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
