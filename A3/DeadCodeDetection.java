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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        // to analyze control flow unreachable
        // we need a set liveCode to do the minus thing: deadCode = Universal - liveCode
        Set<Stmt> liveCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        Queue<Stmt> queue = new LinkedList<>();
        queue.add(cfg.getEntry());
        while(!queue.isEmpty()){
            Stmt stmt = queue.poll();

            if(deadCode.contains(stmt) || liveCode.contains(stmt)){
                continue;
            }

            // useless assign
            if(stmt instanceof AssignStmt<?,?> assignStmt) {
                if (hasNoSideEffect(assignStmt.getRValue()) && assignStmt.getLValue() instanceof Var var &&
                        !liveVars.getOutFact(assignStmt).contains(var)) {
                    // out do not contain dead code
                    deadCode.add(stmt);
                } else {
                    liveCode.add(stmt);
                }
                for(Edge<Stmt> e: cfg.getOutEdgesOf(stmt)){
                    queue.add(e.getTarget());
                }
            }
            else if (stmt instanceof If ifstmt) {
                // if stmt
                liveCode.add(stmt);

                Value condition = ConstantPropagation.evaluate(ifstmt.getCondition(), constants.getInFact(ifstmt));
                if(condition.isConstant()){
                    if(condition.getConstant() == 0){
                        // if-false reached
                        for(Edge<Stmt> e: cfg.getOutEdgesOf(ifstmt)){
                            if(e.getKind() == Edge.Kind.IF_FALSE){
                                queue.add(e.getTarget());
                            }
                        }
                    }else{
                        // if-true reached
                        for(Edge<Stmt> e: cfg.getOutEdgesOf(ifstmt)){
                            if(e.getKind() == Edge.Kind.IF_TRUE){
                                queue.add(e.getTarget());
                            }
                        }
                    }
                }
                else{
                    // all reachable
                    for(Edge<Stmt> e: cfg.getOutEdgesOf(stmt)){
                        queue.add(e.getTarget());
                    }
                }
            }
            else if (stmt instanceof SwitchStmt switchStmt) {
                liveCode.add(stmt);

                Value condition = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(switchStmt));
                if(condition.isConstant()){
                    // case has the constant val
                    // or doesn't have -> default
                    if(switchStmt.getCaseValues().contains(condition.getConstant())){
                        for(Edge<Stmt> e: cfg.getOutEdgesOf(switchStmt)){
                            if(e.isSwitchCase() && e.getCaseValue() == condition.getConstant()){
                                queue.add(e.getTarget());
                            }
                        }
                    }
                    else{
                        queue.add(switchStmt.getDefaultTarget());
                    }
                }
                else{
                    for(Edge<Stmt> e: cfg.getOutEdgesOf(stmt)){
                        queue.add(e.getTarget());
                    }
                }
            }
            else{
                // live
                liveCode.add(stmt);
                for(Edge<Stmt> e: cfg.getOutEdgesOf(stmt)){
                    queue.add(e.getTarget());
                }
            }
        }
        deadCode.addAll(cfg.getNodes());
        deadCode.removeAll(liveCode);
        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
