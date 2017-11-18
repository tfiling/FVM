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
          Transition<S, A>[] transitionsInTS = transitions.toArray(new Transition[transitions.size()]);

          for (int i = 0; i < transitionsInTS.length; i++) {
              Transition<S, A> transitionTested = transitionsInTS[i];

              for (int j = i+1; j < transitionsInTS.length; j++) {
                  Transition<S, A> transitionCompared = transitionsInTS[j];
                  // we checking every time two sequentialize transitions i,i+1
                  //Compare by form & action.
                  boolean transitionHaveSameFrom = transitionTested.getFrom().equals(transitionCompared.getFrom());
                  boolean transitionHaveSameAction = transitionTested.getAction().equals(transitionCompared.getAction());
                  if (transitionHaveSameFrom && transitionHaveSameAction) {
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
             Set<S> postStates = this.post(ts, state);

             for(S postState : postStates) {
                 Set<P> propositionsForPostState = ts.getLabelingFunction().get(postState);

                 for(S comparedPostState : postStates) {
                     if (!postState.equals(comparedPostState)) {
                         Set<P> propositionsForComparedPostState = ts.getLabelingFunction().get(comparedPostState);

                         if ((propositionsForPostState == null || propositionsForPostState.isEmpty()) && 
                        		 (propositionsForComparedPostState == null || propositionsForComparedPostState.isEmpty())) {
                             return false;
                         }

                         if (propositionsForPostState != null && propositionsForPostState.equals(propositionsForComparedPostState)) {
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

         S stateBeforeAction = e.head();
         // take the following one
         A action = e.tail().head();
         // same
         S stateAfterAction = e.tail().tail().head();

         if (!ts.getStates().contains(stateBeforeAction)) {
             throw new StateNotFoundException(stateBeforeAction);
         }
         if (!ts.getStates().contains(stateAfterAction)) {
             throw new StateNotFoundException(stateAfterAction);
         }
         if (!ts.getActions().contains(action)) {
             throw new ActionNotFoundException(action);
         }

         Set<Transition<S,A>> trasitions = ts.getTransitions();

         for(Transition<S, A> transition : trasitions) {
             if (transition.getFrom().equals(stateBeforeAction) && 
            		 transition.getAction().equals(action) && 
            		 transition.getTo().equals(stateAfterAction)) {
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
        AlternatingSequence<S,A> iteratedSequence = e;
        S sequenceEndState = e.head();
        while (!iteratedSequence.tail().isEmpty()) { 
        	// iterate until the last states
            iteratedSequence = iteratedSequence.tail().tail();
            sequenceEndState = iteratedSequence.head();
        }

        return this.isStateTerminal(ts, sequenceEndState);
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
        Set<S>returnedPostStates = new HashSet<S>();

        for(S state : c) {
            returnedPostStates.addAll(this.post(ts, state));
        }

        return returnedPostStates;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S>returnedPostStates = new HashSet<S>();

        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
        for(Transition<S, A> transition : ts.getTransitions()) {
            if (transition.getFrom().equals(s) && 
            		transition.getAction().equals(a)) {
                returnedPostStates.add(transition.getTo());
            }
        }

        return returnedPostStates;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S>returnedPostStates = new HashSet<S>();

        for(S state : c) {
            returnedPostStates.addAll(this.post(ts, state, a));
        }

        return returnedPostStates;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S>returnedPreStates = new HashSet<S>();

        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
        for (Transition<S, ?> transition : ts.getTransitions()) {
            if (transition.getTo().equals(s)) {
                returnedPreStates.add(transition.getFrom());
            }
        }

        return returnedPreStates;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S>returnedPreStates = new HashSet<S>();

        for(S state : c) {
            returnedPreStates.addAll(this.pre(ts, state));
        }

        return returnedPreStates;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S>postStates = new HashSet<S>();

        for(S state : c) {
            postStates.addAll(this.pre(ts, state, a));
        }

        return postStates;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S>returnedPreStates = new HashSet<S>();

        if (!ts.getStates().contains(s)) {
            throw new StateNotFoundException(s);
        }
        for(Transition<S, A> transition : ts.getTransitions()) {
            if (transition.getTo().equals(s) && 
            		transition.getAction().equals(a)) {
                returnedPreStates.add(transition.getFrom());
            }
        }

        return returnedPreStates;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> reachableStates = new HashSet<S>();
        Set<S> currentTestedStates = ts.getInitialStates();

        while (!currentTestedStates.isEmpty()) {
            reachableStates.addAll(currentTestedStates);
            currentTestedStates = this.post(ts, currentTestedStates);
            currentTestedStates.removeAll(reachableStates);
        }

        return reachableStates;
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
