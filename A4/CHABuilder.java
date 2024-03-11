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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;
import java.util.stream.Stream;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> methodQueue = new LinkedList<>();
        methodQueue.offer(entry);

        while(!methodQueue.isEmpty()){
            JMethod jMethod = methodQueue.poll();
            if(!callGraph.contains(jMethod)){
                callGraph.addReachableMethod(jMethod);
                callGraph.callSitesIn(jMethod).forEach(callSite->{
                    Set<JMethod> jMethodSet = resolve(callSite);
                    for(JMethod jm: jMethodSet){
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, jm));
                        methodQueue.offer(jm);
                    }
                });

            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> retSet = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature subsignature = methodRef.getSubsignature();
        // CallKind callkind = CallGraphs.getCallKind(callSite);

        if(callSite.isStatic()){
            retSet.add(methodRef.getDeclaringClass().getDeclaredMethod(subsignature));
        } else if (callSite.isSpecial()) {
            JClass jClass = methodRef.getDeclaringClass();
            JMethod jMethod = dispatch(jClass, subsignature);
            if(jMethod != null) {
                retSet.add(jMethod);
            }
        } else if (callSite.isVirtual() || callSite.isInterface()) {
            JClass jClassReceiver = methodRef.getDeclaringClass();
            Queue<JClass> jClassQueue = new LinkedList<>();
            jClassQueue.offer(jClassReceiver);
            while(!jClassQueue.isEmpty()){
                JClass jClass = jClassQueue.poll();
                JMethod jMethod = dispatch(jClass, subsignature);
                if(jMethod != null){
                    retSet.add(jMethod);
                }
                jClassQueue.addAll(hierarchy.getDirectImplementorsOf(jClass));
                jClassQueue.addAll(hierarchy.getDirectSubclassesOf(jClass));
                jClassQueue.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
            }
        }
        return retSet;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if(jclass == null){
            return null;
        }
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if(method != null && !method.isAbstract()){
            return method;
        }else if(jclass.getSuperClass() == null){
            return null;
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
