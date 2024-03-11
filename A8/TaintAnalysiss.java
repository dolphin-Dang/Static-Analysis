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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

//    public boolean isSource(Invoke invoke, CSObj csObj, CSVar csVar){
//        JMethod jMethod = solver.resolveCallee(csObj, invoke);
//        Source source = new Source(jMethod, jMethod.getReturnType());
//        return config.getSources().contains(source);
//    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.

        // go over all edges in CSCallGraph
        // all method args can be a sink
        result.getCSCallGraph().edges().forEach(edge->{
            JMethod method = edge.getCallee().getMethod();
            CSCallSite csCallSite = edge.getCallSite();
            Context ctx = csCallSite.getContext();
            Invoke invoke = csCallSite.getCallSite();
            for(int i=0; i< method.getParamCount(); i++){
                Var arg = invoke.getInvokeExp().getArg(i);
                CSVar csArg = csManager.getCSVar(ctx, arg);
                if(config.getSinks().contains(new Sink(method, i))){
                    // be a real sink
                    // then test if it holds a taint in PTS
                    PointsToSet argPTS = csArg.getPointsToSet();
                    for(CSObj csObj: argPTS){
                        if(manager.isTaint(csObj.getObject())){
                            Invoke source = manager.getSourceCall(csObj.getObject());
                            taintFlows.add(new TaintFlow(source, invoke, i));
                        }
                    }
                }
            }
        });
        return taintFlows;
    }

    public CSObj getTaintObj(Invoke source, Type type){
        return csManager.getCSObj(emptyContext, manager.makeTaint(source, type));
    }

    public Type getMethodTypeSource(JMethod method){
        Type ret = null;
        for(Source src: config.getSources()){
            if(src.method() == method){
                ret = src.type();
            }
        }
        return ret;
    }

    private Type getType(JMethod method, int from, int to){
        Set<TaintTransfer> taintTransferSet = config.getTransfers();
        for(TaintTransfer taintTransfer: taintTransferSet){
            if(taintTransfer.method() == method && taintTransfer.from() == from && taintTransfer.to() == to){
                return taintTransfer.type();
            }
        }
        return null;
    }
    public Type Arg2Result(JMethod method, int i){
        return getType(method, i, TaintTransfer.RESULT);
    }

    public Type Arg2Base(JMethod method, int i) {
        return getType(method, i, TaintTransfer.BASE);
    }

    public Type Base2Result(JMethod method) {
        return getType(method, TaintTransfer.BASE, TaintTransfer.RESULT);
    }

//    private Set<Type> getType(JMethod method, int from, int to){
//        Set<Type> ret = new HashSet<>();
//        Set<TaintTransfer> taintTransferSet = config.getTransfers();
//        for(TaintTransfer taintTransfer: taintTransferSet){
//            if(taintTransfer.method() == method && taintTransfer.from() == from && taintTransfer.to() == to){
//                ret.add(taintTransfer.type());
//            }
//        }
//        return ret;
//    }


    public boolean isTaint(CSObj csObj){
        return manager.isTaint(csObj.getObject());
    }

    public Invoke getSource(CSObj csObj) {
        // get src call for csobj
        return manager.getSourceCall(csObj.getObject());
    }
}
