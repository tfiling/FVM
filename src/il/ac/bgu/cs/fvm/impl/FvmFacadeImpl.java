package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import java.io.InputStream;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its 
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
    	return new TransitionSystemImpl<S, A, P>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
    	// if size greater then 1 so for sure it's not deterministic....
    	if (ts.getInitialStates().size() > 1) {
              return false;
          }

    	  Set<Transition<S, A>> transitions = ts.getTransitions();
          Transition<S, A>[] TS = transitions.toArray(new Transition[transitions.size()]);
          for (int i = 0; i < TS.length; i++) {
              Transition<S, A> test = TS[i];
              for (int j = i+1; j < TS.length; j++) {
                  Transition<S, A> transitionCompared = TS[j];
                  // we checking every time two sequentialize transitions i,i+1
                  //Compare by form & action.
                  boolean sameForm = test.getFrom().equals(transitionCompared.getFrom());
                  boolean sameAction = test.getAction().equals(transitionCompared.getAction());
                  if (sameForm && sameAction) {
                      return false;
                  }
              }
          }

          return true;    
    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
    	 if (ts.getInitialStates().size() > 1) {
             return false;
         }
         for (S state : ts.getStates()) {
             Set<S> post = this.post(ts, state);
             for(S postState : post) {
                 Set<P> propositions = ts.getLabelingFunction().get(postState);
                 for(S toComp : post) {
                     if (!postState.equals(toComp)) {
                         Set<P> propositionsToBeCompared = ts.getLabelingFunction().get(toComp);
                         if ((propositions == null || propositions.isEmpty()) && 
                        		 (propositionsToBeCompared == null || propositionsToBeCompared.isEmpty())) {
                             return false;
                         }
                         if (propositions != null && propositions.equals(propositionsToBeCompared)) {
                             return false;
                         }
                     }
                 }
             }
         }
         return true;    
    }	

    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isInitialExecutionFragment(ts, e) && this.isMaximalExecutionFragment(ts, e);
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
    	 if (e == null || e.isEmpty() || e.tail().isEmpty()) {
    	    	// handle the scenario where n <= 1 (non or only one state within the execution s_0)    		 
             return true;
         }
         S beforeAct = e.head();
         // take the following one
         A action = e.tail().head();
         // same
         S afterAct = e.tail().tail().head();
         if (!ts.getStates().contains(beforeAct)) {
             throw new StateNotFoundException(beforeAct);
         }
         if (!ts.getStates().contains(afterAct)) {
             throw new StateNotFoundException(afterAct);
         }
         if (!ts.getActions().contains(action)) {
             throw new ActionNotFoundException(action);
         }
         Set<Transition<S,A>> trasitions = ts.getTransitions();
         for(Transition<S, A> t : trasitions) {
             if (t.getFrom().equals(beforeAct) && 
            		 t.getAction().equals(action) && 
            		 t.getTo().equals(afterAct)) {
            	 // current link s_0, a_1, s_1 is a valid transition in the given transition system 
            	 // recursively check if the following links (s_1, a_2, s_3 and so on) are also valid execution
                 return this.isExecutionFragment(ts, e.tail().tail());
             }
         }
         return false;  // current first link s_i, a_i+1, s_i+1 was not detected as a valid transition hence this is not an execution fragment  
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (e.isEmpty()) {
            return false;
        }
        S head = e.head();
        return this.isExecutionFragment(ts, e) && ts.getInitialStates().contains(head);
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (e == null || e.isEmpty()) {
            return false;
        }        
        if (!this.isExecutionFragment(ts, e)) {
        	//this is not a valid execution fragment
        	return false;
        }
        AlternatingSequence<S,A> iter = e;
        S finalState = e.head();
        while (!iter.tail().isEmpty()) { 
        	// iterate until the last states
            iter = iter.tail().tail();
            finalState = iter.head();
        }
        return this.isStateTerminal(ts, finalState);
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        return this.post(ts, s).isEmpty();
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        Set<? extends Transition<S, ?>> transitions = ts.getTransitions();
        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
        Set<S> returnedPostStates = new HashSet<S>();
        for (Transition<S, ?> transition : transitions) {
            if (transition.getFrom().equals(s)) {
                returnedPostStates.add(transition.getTo());
            }
        }
        return returnedPostStates;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S>PostStates = new HashSet<S>();
        for (Iterator<S> it = c.iterator(); it.hasNext(); ) {
        	S state = it.next();
            PostStates.addAll(this.post(ts, state));
        }
        return PostStates;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S>toRet = new HashSet<S>();
        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
        for(Transition<S, A> transition : ts.getTransitions()) {
            if (transition.getFrom().equals(s) && 
            		transition.getAction().equals(a)) {
                toRet.add(transition.getTo());
            }
        }

        return toRet;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S>toRet = new HashSet<S>();
        for (Iterator<S> it = c.iterator(); it.hasNext(); ) {
        	S state = it.next();
            toRet.addAll(this.post(ts, state, a));
        }

        return toRet;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S>toRet = new HashSet<S>();

        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
        for (Transition<S, ?> transition : ts.getTransitions()) {
            if (transition.getTo().equals(s)) {
                toRet.add(transition.getFrom());
            }
        }

        return toRet;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S>toRet = new HashSet<S>();
        for (Iterator<S> it = c.iterator(); it.hasNext(); ) {
        	S state = it.next();
            toRet.addAll(this.pre(ts, state));
        }      
        return toRet;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S>PS = new HashSet<S>();
        for (Iterator<S> it = c.iterator(); it.hasNext(); ) {
        	S state = it.next();
            PS.addAll(this.pre(ts, state, a));
        }

        return PS;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S>toRet = new HashSet<S>();
        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
        for(Transition<S, A> transition : ts.getTransitions()) {
            if (transition.getTo().equals(s) && 
            		transition.getAction().equals(a)) {
                toRet.add(transition.getFrom());
            }
        }
        return toRet;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> reachStates = new HashSet<S>();
        Set<S> currState = ts.getInitialStates();
        while (!currState.isEmpty()) {
            reachStates.addAll(currState);
            currState = this.post(ts, currState);
            currState.removeAll(reachStates);
        }
        return reachStates;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement createProgramGraph
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement verifyAnOmegaRegularProperty
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }

   
}
