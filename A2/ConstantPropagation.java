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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact ret = new CPFact();
        for(Var para: cfg.getIR().getParams()) {
            if (canHoldInt(para)){
                ret.update(para, Value.getNAC());
            }
        }
        return ret;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((k,v)->{
                Value newVal = meetValue(v, target.get(k));
                target.update(k, newVal);
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
//        return null;
        // undef -> another
        // one NAC -> NAC
        // both constant -> equal?
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if(v1.isUndef()){
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        } else {
            // both constant
            if(v1.getConstant() == v2.getConstant()){
                return v1;
            }else{
                return Value.getNAC();
            }
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
//        return false;
        CPFact ret = in.copy();
//        boolean flag = false;
        if(stmt instanceof DefinitionStmt<?,?> defStmt){
            // focus on can hold INT only
            if(defStmt.getDef().isPresent()) {
                LValue def = defStmt.getDef().get();
                if(def instanceof Var v && canHoldInt(v)) {
                    Value newVal = evaluate(defStmt.getRValue(), in);
                    ret.update(v, newVal);
                }
            }
        }

//        return flag;
        // changed?
        if(ret.equals(out)){
            return false;
        }else{
            out.copyFrom(ret);
            return true;
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
//        return null;
        // 3 conditions:
        // IntLiteral \ Var \ BinaryExp
        if (exp instanceof IntLiteral intl) {
            return Value.makeConstant(intl.getValue());
        }
        else if (exp instanceof Var v) {
            return in.get(v);
        }
        else if (exp instanceof BinaryExp be) {
            // BinaryExp
//            BinaryExp be = (BinaryExp) exp;
            BinaryExp.Op op = be.getOperator();
            Var v1 = be.getOperand1();
            Var v2 = be.getOperand2();

            // both constant -> val(v1) op val(v2)
            // one val(v)==NAC -> NAC
            // otherwise -> UNDEF
            if (in.get(v1).isConstant() && in.get(v2).isConstant()) {
                int cons1 = in.get(v1).getConstant();
                int cons2 = in.get(v2).getConstant();
                if (op instanceof ArithmeticExp.Op arop) {
                    switch (arop) {
                        case ADD -> {
                            return Value.makeConstant(cons1 + cons2);
                        }
                        case DIV -> {
                            if (cons2 == 0) return Value.getUndef();
                            return Value.makeConstant(cons1 / cons2);
                        }
                        case MUL -> {
                            return Value.makeConstant(cons1 * cons2);
                        }
                        case REM -> {
                            if (cons2 == 0) return Value.getUndef();
                            return Value.makeConstant(cons1 % cons2);
                        }
                        case SUB -> {
                            return Value.makeConstant(cons1 - cons2);
                        }
                    }
                } else if (op instanceof ConditionExp.Op conop) {
                    switch (conop) {
                        case EQ -> {
                            return Value.makeConstant(cons1 == cons2 ? 1 : 0);
                        }
                        case GE -> {
                            return Value.makeConstant(cons1 >= cons2 ? 1 : 0);
                        }
                        case GT -> {
                            return Value.makeConstant(cons1 > cons2 ? 1 : 0);
                        }
                        case LE -> {
                            return Value.makeConstant(cons1 <= cons2 ? 1 : 0);
                        }
                        case LT -> {
                            return Value.makeConstant(cons1 < cons2 ? 1 : 0);
                        }
                        case NE -> {
                            return Value.makeConstant(cons1 != cons2 ? 1 : 0);
                        }
                    }
                } else if (op instanceof BitwiseExp.Op bitop) {
                    switch (bitop) {
                        case OR -> {
                            return Value.makeConstant(cons1 | cons2);
                        }
                        case AND -> {
                            return Value.makeConstant(cons1 & cons2);
                        }
                        case XOR -> {
                            return Value.makeConstant(cons1 ^ cons2);
                        }
                    }
                } else if (op instanceof ShiftExp.Op shop) {
                    switch (shop) {
                        case SHL -> {
                            return Value.makeConstant(cons1 << cons2);
                        }
                        case SHR -> {
                            return Value.makeConstant(cons1 >> cons2);
                        }
                        case USHR -> {
                            return Value.makeConstant(cons1 >>> cons2);
                        }
                    }
                }
            }
            else if (in.get(v1).isNAC() || in.get(v2).isNAC()) {
                if(exp instanceof ArithmeticExp && (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)){
                    if(in.get(v2).isConstant() && in.get(v2).getConstant() == 0){
                        return Value.getUndef();
                    }
                }
                return Value.getNAC();
            }
            else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}
