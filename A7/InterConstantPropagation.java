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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import soot.util.Cons;

import java.util.HashSet;
import java.util.List;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private PointerAnalysisResult pta;
    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if(out.equals(in)){
            return false;
        }
        out.copyFrom(in);
        return true;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
//        return cp.transferNode(stmt, in, out);
        // cp is not enough, load/store/arrayLoad/arrayStore are required
        CPFact originalOut = out.copy();

        if(stmt instanceof LoadField loadFieldStmt){
            // y = x.f / T.f
            Var lval = loadFieldStmt.getLValue();
            if(!ConstantPropagation.canHoldInt(lval)){
                return out.copyFrom(in);
            }
            Value val = Value.getUndef();
            if(loadFieldStmt.isStatic()){
                // static load field: y = T.f
                for(Stmt s: icfg){
                    if(s instanceof StoreField storeFieldStmt && storeFieldStmt.isStatic()){
                        JField loadField = loadFieldStmt.getFieldAccess().getFieldRef().resolve();
                        JField storeField = storeFieldStmt.getFieldAccess().getFieldRef().resolve();
                        JClass loadClass = loadFieldStmt.getFieldRef().getDeclaringClass();
                        JClass storeClass = storeFieldStmt.getFieldRef().getDeclaringClass();
                        if(storeField == loadField && loadClass == storeClass){
                            val = cp.meetValue(val,
                                    solver.getResult().getOutFact(storeFieldStmt).get(storeFieldStmt.getRValue()));
                        }
                    }
                }
            }else{
                // y = x.f
                Var base = ((InstanceFieldAccess)(loadFieldStmt.getFieldAccess())).getBase();
                // need import pta.core.heap.Obj here
                HashSet<Obj> baseSet = new HashSet<>(pta.getPointsToSet(base));
                for(Var var: pta.getVars()){
                    HashSet<Obj> varSet = new HashSet<>(pta.getPointsToSet(var));
                    HashSet<Obj> intersectionSet = new HashSet<>(baseSet);
                    intersectionSet.retainAll(varSet);
                    if(!intersectionSet.isEmpty()){
                        // intersection not empty: alias
                        for(StoreField storeFieldStmt: var.getStoreFields()){
                            if(!storeFieldStmt.isStatic()){
                                JField loadField = loadFieldStmt.getFieldAccess().getFieldRef().resolve();
                                JField storeField = storeFieldStmt.getFieldAccess().getFieldRef().resolve();
                                if(storeField == loadField){
                                    val = cp.meetValue(val,
                                            solver.getResult().getOutFact(storeFieldStmt).get(storeFieldStmt.getRValue()));
                                }
                            }
                        }
                    }
                }
            }
            out.copyFrom(in);
            out.update(loadFieldStmt.getLValue(), val);
            return !out.equals(originalOut);
        } else if (stmt instanceof StoreField storeFieldStmt) {
            if(storeFieldStmt.isStatic()){
                // T.f = y
                for(Stmt s: icfg){
                    if(s instanceof LoadField loadFieldStmt && loadFieldStmt.isStatic()){
                        JField loadField = loadFieldStmt.getFieldAccess().getFieldRef().resolve();
                        JField storeField = storeFieldStmt.getFieldAccess().getFieldRef().resolve();
                        if(storeField == loadField){
                            solver.add2WorkList(loadFieldStmt);
                        }
                    }
                }
            }else{
                // x.f = y
                Var base = ((InstanceFieldAccess)(storeFieldStmt.getFieldAccess())).getBase();
                // need import pta.core.heap.Obj here
                HashSet<Obj> baseSet = new HashSet<>(pta.getPointsToSet(base));
                for(Var var: pta.getVars()){
                    HashSet<Obj> varSet = new HashSet<>(pta.getPointsToSet(var));
                    HashSet<Obj> intersectionSet = new HashSet<>(baseSet);
                    intersectionSet.retainAll(varSet);
                    if(!intersectionSet.isEmpty()){
                        // intersection not empty: alias
                        for(LoadField loadFieldStmt: var.getLoadFields()){
                            if(!storeFieldStmt.isStatic()){
                                JField loadField = loadFieldStmt.getFieldAccess().getFieldRef().resolve();
                                JField storeField = storeFieldStmt.getFieldAccess().getFieldRef().resolve();
                                JClass loadClass = loadFieldStmt.getFieldRef().getDeclaringClass();
                                JClass storeClass = storeFieldStmt.getFieldRef().getDeclaringClass();
                                if(storeField == loadField && loadClass == storeClass){
                                    solver.add2WorkList(loadFieldStmt);
                                }
                            }
                        }
                    }
                }
            }
        } else if (stmt instanceof LoadArray loadArrayStmt) {
            // x = a[i]
            Var base = loadArrayStmt.getArrayAccess().getBase();
            HashSet<Obj> baseSet = new HashSet<>(pta.getPointsToSet(base));
            Value val = Value.getUndef();
            for(Var var: pta.getVars()){
                HashSet<Obj> varSet = new HashSet<>(pta.getPointsToSet(var));
                HashSet<Obj> intersectionSet = new HashSet<>(baseSet);
                intersectionSet.retainAll(varSet);
                if(!intersectionSet.isEmpty()){
                    // not empty: base intersection, but not always alias
                    for(StoreArray storeArrayStmt: var.getStoreArrays()){
                        Var storeIndex = storeArrayStmt.getArrayAccess().getIndex();
                        CPFact storeOutFact = solver.getResult().getOutFact(storeArrayStmt);
                        Var loadIndex = loadArrayStmt.getArrayAccess().getIndex();
                        CPFact loadOutFact = solver.getResult().getOutFact(loadArrayStmt);
                        // check the index
                        if(isIndexIntersect(loadOutFact.get(loadIndex), storeOutFact.get(storeIndex)) ||
                        isIndexIntersect(storeOutFact.get(storeIndex), in.get(loadIndex))){
                            // alias
                            val = cp.meetValue(val, storeOutFact.get(storeArrayStmt.getRValue()));
                        }
                    }
                }
            }
            out.copyFrom(in);
            out.update(loadArrayStmt.getLValue(), val);
            return !out.equals(originalOut);
        } else if (stmt instanceof StoreArray storeArrayStmt) {
            // a[i] = x
            Var base = storeArrayStmt.getArrayAccess().getBase();
            HashSet<Obj> baseSet = new HashSet<>(pta.getPointsToSet(base));
            Value val = Value.getUndef();
            for(Var var: pta.getVars()){
                HashSet<Obj> varSet = new HashSet<>(pta.getPointsToSet(var));
                HashSet<Obj> intersectionSet = new HashSet<>(baseSet);
                intersectionSet.retainAll(varSet);
                if(!intersectionSet.isEmpty()){
                    for(LoadArray loadArrayStmt: var.getLoadArrays()){
                        Var storeIndex = storeArrayStmt.getArrayAccess().getIndex();
                        CPFact storeOutFact = solver.getResult().getOutFact(storeArrayStmt);
                        Var loadIndex = loadArrayStmt.getArrayAccess().getIndex();
                        CPFact loadOutFact = solver.getResult().getOutFact(loadArrayStmt);
                        // check the index
                        if(isIndexIntersect(loadOutFact.get(loadIndex), storeOutFact.get(storeIndex)) ||
                        isIndexIntersect(loadOutFact.get(loadIndex), in.get(storeIndex))){
                            solver.add2WorkList(loadArrayStmt);
                        }
                    }
                }
            }
        }
        return cp.transferNode(stmt, in, out);
    }

    private boolean isIndexIntersect(Value v1, Value v2){
        if(v1.isUndef() || v2.isUndef()){
            return false;
        } else if (v1.isConstant() && v2.isConstant()) {
            return v1.getConstant() == v2.getConstant();
        }else{
            return true;
        }
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact retFact = out.copy();
        Stmt stmt = edge.getSource();
        if(stmt instanceof DefinitionStmt<?,?> definitionStmt){
            LValue lval = definitionStmt.getLValue();
            if(lval != null && lval instanceof Var lvar){
                retFact.remove(lvar);
            }
        }
        return retFact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact retFact = new CPFact();
        Invoke invoke = (Invoke) edge.getSource();
        List<Var> args = invoke.getInvokeExp().getArgs();

        List<Var> paramList = edge.getCallee().getIR().getParams();
        for(int i=0; i<args.size(); i++){
            retFact.update(paramList.get(i), callSiteOut.get(args.get(i)));
        }
        return retFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact retFact = new CPFact();
        Invoke invoke = (Invoke) edge.getCallSite();
        Var lvar = invoke.getLValue();

        if(lvar != null){
            edge.getReturnVars().forEach(var -> {
                retFact.update(lvar, cp.meetValue(retFact.get(lvar), returnOut.get(var)));
            });
        }

        return retFact;
    }
}
