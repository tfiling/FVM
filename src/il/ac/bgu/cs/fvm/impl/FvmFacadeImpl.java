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
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
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
    
    private <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts, S state) {
        Set<S> reachableStates = new HashSet<S>();

        Set<S> currentTestedStates = post(ts, state);

        while (!currentTestedStates.isEmpty()) {
            reachableStates.addAll(currentTestedStates);

            currentTestedStates = this.post(ts, currentTestedStates);
            currentTestedStates.removeAll(reachableStates);
        }

        return reachableStates;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        return interleave(ts1, ts2, null);
    }

    /*private functions of us */
    private <S, A> Set<Transition<S, A>>transitionsInTransitionSystemForAction(TransitionSystem<S, A, ?> ts, A action) {
        Set<Transition<S, A>> transitions = new HashSet<>();

        for (Transition<S, A> transitionInTS : ts.getTransitions()) {
            if (transitionInTS.getAction().equals(action)) {
                transitions.add(transitionInTS);
            }
        }

        return transitions;
    }

    private <S1, S2> Set<Pair<S1, S2>>cartesianProductSets(Set<S1> first, Set<S2> second) {
        if (first == null || second == null) {
            return new HashSet<>();
        }

        Set<Pair<S1, S2>> interleavedSet = new HashSet<>();

        for (S1 firstObject: first) {
            for (S2 secondObject : second) {
                Pair<S1, S2> interleavedPair = new Pair<S1, S2>(firstObject, secondObject);
                interleavedSet.add(interleavedPair);
            }
        }

        return interleavedSet;
    }

    private <S> Set<S>intersectSets(Set<S> set1, Set<S> set2) {
        if (set1 == null) {
            return set2;
        }
        if (set2 == null) {
            return set1;
        }

        Set<S> set1Copy = new HashSet<S>(set1);
        set1Copy.retainAll(set2);
        return set1Copy;
    }

    private <S> Set<S>unionSets(Set<S> set1, Set<S> set2) {
        Set<S> set1Copy = new HashSet<S>(set1);
        set1Copy.addAll(set2);
        return set1Copy;
    }

    private <S> Set<S>differenceSets(Set<S> set1, Set<S> set2) {
        Set<S> unionSet = unionSets(set1, set2);
        Set<S> intersectSet = intersectSets(set1, set2);
        unionSet.removeAll(intersectSet);
        return unionSet;
    }

    //Set1 minus set2
    private <S> Set<S>complementSet(Set<S> set1, Set<S> set2) {
        if (set2 == null) {
            return set1;
        }

        Set<S>set1Copy = new HashSet<S>(set1);
        set1Copy.removeAll(set2);
        return set1Copy;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P>  interleavedTransitionSystem = new TransitionSystemImpl<Pair<S1, S2>, A, P>();

        //Interleave states
        Set<Pair<S1, S2>> interleavedStates = cartesianProductSets(ts1.getStates(), ts2.getStates());

        for (Pair<S1, S2> interleavedState : interleavedStates) {
            interleavedTransitionSystem.addState(interleavedState);
        }

        //Interleave initial states
        for (Pair<S1, S2> interleavedState : interleavedStates) {
            if (ts1.getInitialStates().contains(interleavedState.first) && ts2.getInitialStates().contains(interleavedState.second)) {
                interleavedTransitionSystem.addInitialState(interleavedState);
            }
        }

        //Interleave actions
        for (A action : ts1.getActions()) {
            interleavedTransitionSystem.addAction(action);
        }
        for (A action : ts2.getActions()) {
            interleavedTransitionSystem.addAction(action);
        }

        //Interleave atomic propositions
        for (P atomicProposition : ts1.getAtomicPropositions()) {
            interleavedTransitionSystem.addAtomicProposition(atomicProposition);
        }
        for (P atomicProposition : ts2.getAtomicPropositions()) {
            interleavedTransitionSystem.addAtomicProposition(atomicProposition);
        }

        //Interleave labeling function (should come after interleaving states and APs
        for (Pair<S1, S2> interleavedState : interleavedStates) {
            Set<P> apsForState1InTS1 = ts1.getLabel(interleavedState.first);
            Set<P> apsForState2InTS2 = ts2.getLabel(interleavedState.second);

            Set<P> intersectedApsForState1And2 = unionSets(apsForState1InTS1, apsForState2InTS2);
            for (P atomicPropositionForInterleavedState : intersectedApsForState1And2) {
                interleavedTransitionSystem.addToLabel(interleavedState, atomicPropositionForInterleavedState);
            }
        }

        //Intersect transitions - for action in handshake
        if (handShakingActions != null) {
            for (A action : handShakingActions) {
                Set<Transition<S1, A>> transitionsForActionInTs1 = transitionsInTransitionSystemForAction(ts1, action);
                Set<Transition<S2, A>> transitionsForActionInTs2 = transitionsInTransitionSystemForAction(ts2, action);

                for (Transition<S1, A> transitionForActionInTs1 : transitionsForActionInTs1) {
                    for (Transition<S2, A> transitionForActionInTs2 : transitionsForActionInTs2) {
                        Pair<S1, S2> intersectedFromState = new Pair<S1, S2>(transitionForActionInTs1.getFrom(), transitionForActionInTs2.getFrom());
                        Pair<S1, S2> intersectedToState = new Pair<S1, S2>(transitionForActionInTs1.getTo(), transitionForActionInTs2.getTo());
                        Transition<Pair<S1, S2>, A> intersectedTransition = new Transition<Pair<S1, S2>, A>(intersectedFromState, action, intersectedToState);
                        interleavedTransitionSystem.addTransition(intersectedTransition);
                    }
                }
            }
        }

        //Intersect transitions - for action not in H
        Set<A> actionsInTs1AndNotInHandshake = complementSet(ts1.getActions(), handShakingActions);
        for (A actionInTs1AndNotInHandshake : actionsInTs1AndNotInHandshake) {
            Set<Transition<S1, A>> transitionsForActionInTs1 = transitionsInTransitionSystemForAction(ts1, actionInTs1AndNotInHandshake);

            for(Transition<S1, A> transitionForActionInTs1 : transitionsForActionInTs1) {
                for(S2 stateInTs2 : ts2.getStates()) {
                    Pair<S1, S2> intersectedFromState = new Pair<S1, S2>(transitionForActionInTs1.getFrom(), stateInTs2);
                    Pair<S1, S2> intersectedToState = new Pair<S1, S2>(transitionForActionInTs1.getTo(), stateInTs2);
                    Transition<Pair<S1, S2>, A> intersectedTransition = new Transition<Pair<S1, S2>, A>(intersectedFromState, transitionForActionInTs1.getAction(), intersectedToState);
                    interleavedTransitionSystem.addTransition(intersectedTransition);
                }
            }
        }
        Set<A> actionsInTs2AndNotInHandshake = intersectSets(ts2.getActions(), handShakingActions);
        for (A actionInTs2AndNotInHandshake : actionsInTs2AndNotInHandshake) {
            Set<Transition<S2, A>> transitionsForActionInTs2 = transitionsInTransitionSystemForAction(ts2, actionInTs2AndNotInHandshake);

            for(Transition<S2, A> transitionForActionInTs2 : transitionsForActionInTs2) {
                for(S1 stateInTs1 : ts1.getStates()) {
                    Pair<S1, S2> intersectedFromState = new Pair<S1, S2>(stateInTs1, transitionForActionInTs2.getFrom());
                    Pair<S1, S2> intersectedToState = new Pair<S1, S2>(stateInTs1, transitionForActionInTs2.getTo());
                    Transition<Pair<S1, S2>, A> intersectedTransition = new Transition<Pair<S1, S2>, A>(intersectedFromState, transitionForActionInTs2.getAction(), intersectedToState);
                    interleavedTransitionSystem.addTransition(intersectedTransition);
                }
            }
        }

        return interleavedTransitionSystem;
    }


    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl<L, A>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> interleavedProgramGraph = new ProgramGraphImpl<Pair<L1, L2>, A>();

        //Interleave locations
        Set<Pair<L1, L2>> interleavedLocations = cartesianProductSets(pg1.getLocations(), pg2.getLocations());
        for (Pair<L1, L2> interleavedLocation : interleavedLocations) {
            interleavedProgramGraph.addLocation(interleavedLocation);
        }

        //Interleave initial locations
        Set<Pair<L1, L2>> interleavedInitialLocations = cartesianProductSets(pg1.getInitialLocations(), pg2.getInitialLocations());
        for (Pair<L1, L2> interleavedInitialLocation : interleavedInitialLocations) {
            interleavedProgramGraph.addInitialLocation(interleavedInitialLocation);
        }

        //Interleave initializations
        for (List<String> pg1Initialization : pg1.getInitalizations()) {
            for (List<String> pg2Initialization : pg2.getInitalizations()) {
                List<String> interlevedInitialization = new LinkedList<String>(pg1Initialization);
                interlevedInitialization.addAll(pg2Initialization);
                interleavedProgramGraph.addInitalization(interlevedInitialization);
            }
        }

        //Interleave transitions
        for (PGTransition<L1, A> transitionInPg1 : pg1.getTransitions()) {
            for (L2 locationInPg2 : pg2.getLocations()) {
                Pair<L1, L2> fromLocation = new Pair<L1, L2>(transitionInPg1.getFrom(), locationInPg2);
                Pair<L1, L2> toLocation = new Pair<L1, L2>(transitionInPg1.getTo(), locationInPg2);
                PGTransition<Pair<L1, L2>, A> interleavedTransition = new PGTransition<Pair<L1, L2>, A>(fromLocation, transitionInPg1.getCondition(), transitionInPg1.getAction(), toLocation);
                interleavedProgramGraph.addTransition(interleavedTransition);
            }
        }
        for (PGTransition<L2, A> transitionInPg2 : pg2.getTransitions()) {
            for (L1 locationInPg1 : pg1.getLocations()) {
                Pair<L1, L2> fromLocation = new Pair<L1, L2>(locationInPg1, transitionInPg2.getFrom());
                Pair<L1, L2> toLocation = new Pair<L1, L2>(locationInPg1, transitionInPg2.getTo());
                PGTransition<Pair<L1, L2>, A> interleavedTransition = new PGTransition<Pair<L1, L2>, A>(fromLocation, transitionInPg2.getCondition(), transitionInPg2.getAction(), toLocation);
                interleavedProgramGraph.addTransition(interleavedTransition);
            }
        }

        return interleavedProgramGraph;
    }
    
   
    @Override               //States               						      //Actions            //Tags 
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
    	TransitionSystem<Pair<Map<String,Boolean>, Map<String,Boolean>>, Map<String, Boolean>, Object> transitionSystem = new TransitionSystemImpl<>();

        //Atomic propositions
        for (String inputPortName : c.getInputPortNames()) {
            transitionSystem.addAtomicProposition(inputPortName);
        }
        for (String registerName : c.getRegisterNames()) {
            transitionSystem.addAtomicProposition(registerName);
        }
        for (String outputPortName : c.getOutputPortNames()) {
            transitionSystem.addAtomicProposition(outputPortName);
        }

        //Apply all the possible combinations upon the inputs
        Set<Map<String, Boolean>> fullTruthTable = fullTruthTable(c.getInputPortNames());

        //Actions
        for (Map<String, Boolean> action : fullTruthTable) {
            transitionSystem.addAction(action);
        }

        
        //Initial state and states, transitions and labeling
        for (Map<String, Boolean> inputInitialValues : fullTruthTable) {
        	Map<String, Boolean> registerInitialValues = new HashMap<String,Boolean>();
            for(String regName : c.getRegisterNames()) {
                registerInitialValues.put(regName, new Boolean(false));
            }

            Pair<Map<String, Boolean>, Map<String, Boolean>> initialState = new Pair<>(registerInitialValues, inputInitialValues);
            walkThroughtCircut(c, transitionSystem, true, initialState);
        }

        return transitionSystem;
    }

    private Set<Map<String, Boolean>> fullTruthTable (Set<String> inputs) {

    	int listsSize = powerOf2(inputs.size());
    	Map<String, Boolean>[] lists = new HashMap[listsSize];
    	 List<Boolean>[] listsJustBool = new List[listsSize];
    	ArrayList <String> inputNames = new ArrayList<String>();   	
    	for (String aix: inputs)
    	{
    		inputNames.add(aix);
    	}
    	fillListWithTruthTable(listsJustBool);
    	
    	for(int i = 0; i<listsSize; ++i)
    	{
    		lists[i] = new HashMap<String, Boolean>();
    	}
    	for(int i = 0; i<listsSize; ++i)
    	{//iterate the lists of possible configurations
    		for (int j = 0; j < inputNames.size(); ++j)
    		{//iterate the names of inputs
    			lists[i].put(inputNames.get(j), listsJustBool[i].get(j));
    		}
    	}  	

        Set<Map<String, Boolean>> listsSet = new HashSet<>();
        for (int i = 0; i < lists.length; i++) {
            listsSet.add(lists[i]);
        }

        return listsSet;
    }

    private int powerOf2 (int numberOfVars) {
        int power = 1;
        for (int i = 0; i < numberOfVars; i++) {
            power *= 2;
        }
        return power;
    }

    private void fillListWithTruthTable (List<Boolean>[] lists) {
        if (lists.length == 2) {
            if (lists[0] == null) {
                lists[0] = new LinkedList<Boolean>();
            }
            lists[0].add(new Boolean(true));
            if (lists[1] == null) {
                lists[1] = new LinkedList<Boolean>();
            }
            lists[1].add(new Boolean(false));
            return;
        }

        List<Boolean>[] firstHalf = new List[lists.length / 2];
        List<Boolean>[] secondHalf = new List[lists.length / 2];

        for (int i = 0; i < lists.length; i++) {
            if (lists[i] == null) {
                lists[i] = new LinkedList<Boolean>();
            }
            if (i < lists.length / 2) {
                lists[i].add(new Boolean(true));
                firstHalf[i] = lists[i];
            } else {
                lists[i].add(new Boolean(false));
                secondHalf[i - lists.length / 2] = lists[i];
            }
        }

        fillListWithTruthTable(firstHalf);
        fillListWithTruthTable(secondHalf);
    }


    private void walkThroughtCircut(Circuit c, TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystem, boolean isInitial, Pair<Map<String, Boolean>, Map<String, Boolean>> initialState) {
        boolean transitionSystemContainedState = transitionSystem.getStates().contains(initialState);

        //States
        transitionSystem.addState(initialState);
        if (isInitial) {
            transitionSystem.addInitialState(initialState);
        }

        if (transitionSystemContainedState) {
            return;
        }

        //Labeling
        Map<String, Boolean> currentStateRegisters = initialState.first;
        Set<String> currentStateRegistersNames = currentStateRegisters.keySet();
        String[] RegNames = (String[]) currentStateRegistersNames.toArray();
        for (int i = 0; i < currentStateRegisters.size(); i++) {
            if (currentStateRegisters.get(i).booleanValue()) {
                transitionSystem.addToLabel(initialState, RegNames[i]); ;
            }
        }
        Map<String, Boolean>  currentStateInput = initialState.second;
        Set<String> currentStateInputNames = currentStateRegisters.keySet();
        String[] InNames = (String[]) currentStateInputNames.toArray();
        for (int i = 0; i < currentStateInput.size(); i++) {
            if (currentStateInput.get(i).booleanValue()) {
                transitionSystem.addToLabel(initialState, InNames[i]); ;
            }
        }
        Map<String, Boolean>  currentStateOutput = c.computeOutputs(currentStateRegisters, currentStateInput);
        Set<String> currentStateOutputNames = currentStateRegisters.keySet();
        String[] OutNames = (String[]) currentStateInputNames.toArray();
        for (int i = 0; i < currentStateOutput.size(); i++) {
            if (currentStateOutput.get(i).booleanValue()) {
                transitionSystem.addToLabel(initialState, OutNames[i]); ;
            }
        }


        //Go recursive
        Set<Map<String, Boolean>> fullTruthTableForInputs = fullTruthTable(c.getInputPortNames());
        for (Map<String, Boolean>  inputValue : fullTruthTableForInputs) {
        	Map<String, Boolean>  updatedRegisters = c.updateRegisters(initialState.first, initialState.second);

            Pair<Map<String, Boolean> , Map<String, Boolean>> nextState = new Pair<>(updatedRegisters, inputValue);
            walkThroughtCircut(c, transitionSystem, false, nextState);

            //Transitions
            Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> transition = new Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>(initialState, inputValue, nextState);
            transitionSystem.addTransition(transition);
        }
    }
	@Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
    	   TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystem = new TransitionSystemImpl<Pair<L, Map<String, Object>>, A, String>();

           //Actions
           for (PGTransition<L,A> transition : pg.getTransitions()) {
               transitionSystem.addAction(transition.getAction());
           }

           //States, labeling function, transitions and initial states (needs actions and APs to be set before this part)
           for (List<String> initializationSeq : pg.getInitalizations()) {
               Map<String, Object> initialEval = new HashMap<>();
               for (String initialization : initializationSeq) {
                   initialEval = ActionDef.effect(actionDefs, initialEval, initialization);
               }
               for (L initialLocation : pg.getInitialLocations()) {
                   walkInProgramGraphAndPopulateStates(pg, initialLocation, initialEval, actionDefs, conditionDefs, true, transitionSystem);
               }
           }

           return transitionSystem;
       }

    //return stateForLocationAndEval
    private <L, A>  Pair<L, Map<String, Object>> walkInProgramGraphAndPopulateStates(ProgramGraph<L, A> pg, L currentLocation, Map<String, Object> currentEval, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs, boolean isInitial, TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemToPopulate) {
        Pair<L, Map<String, Object>> stateForLocationAndEval = new Pair<L, Map<String, Object>>(currentLocation, currentEval);

        if (transitionSystemToPopulate.getStates().contains(stateForLocationAndEval)) {
            return stateForLocationAndEval;
        }

        //Add current state
        transitionSystemToPopulate.addState(stateForLocationAndEval);
        //Add initial state
        if (isInitial) {
            transitionSystemToPopulate.addInitialState(stateForLocationAndEval);
        }

        //Add labeling function
        stateForLocationAndEval.second.forEach( (k, v) -> {
            transitionSystemToPopulate.addAtomicProposition(k + " = " + v);
            transitionSystemToPopulate.addToLabel(stateForLocationAndEval, k + " = " + v);
        });

        //Go to transitions from this state
        for (PGTransition<L, A> transition : transitionsInProgramGraphWhereStartLocationEquals(pg, currentLocation)) {
            String condition = transition.getCondition();
            if (ConditionDef.evaluate(conditionDefs, currentEval, condition)) {
                //This is a transition that works
                L nextLocation = transition.getTo();
                Map<String, Object> nextEval = ActionDef.effect(actionDefs, currentEval, transition.getAction());
                Pair<L, Map<String, Object>> stateForConditionAndAction = walkInProgramGraphAndPopulateStates(pg, nextLocation, nextEval, actionDefs, conditionDefs, false, transitionSystemToPopulate);

                //Add transition to the transition system
                Transition<Pair<L, Map<String, Object>>, A> transitionForTransitionSystem = new Transition<Pair<L, Map<String, Object>>, A>(stateForLocationAndEval, transition.getAction(), stateForConditionAndAction);
                transitionSystemToPopulate.addTransition(transitionForTransitionSystem);
            }
        }

        return stateForLocationAndEval;
    }

    private <L, A> Set<PGTransition<L, A>> transitionsInProgramGraphWhereStartLocationEquals(ProgramGraph<L, A> pg, L startLocation) {
        Set<PGTransition<L, A>> allTransitions = pg.getTransitions();
        Set<PGTransition<L, A>> transitionsInProgramGraphWhereStartLocationEquals = new HashSet<>();

        for (PGTransition<L, A> transition : allTransitions) {
            if (transition.getFrom().equals(startLocation)) {
                transitionsInProgramGraphWhereStartLocationEquals.add(transition);
            }
        }

        return transitionsInProgramGraphWhereStartLocationEquals;
    }

    
    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
    	 TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystem = new TransitionSystemImpl<Pair<List<L>, Map<String, Object>>, A, String>();

         //Actions
         for (ProgramGraph<L, A> pg : cs.getProgramGraphs()) {
             for (PGTransition<L,A> transition : pg.getTransitions()) {
                 transitionSystem.addAction(transition.getAction());
             }
         }

         //initial states, states, actions, transitions
         Set<List<L>> cartesianSumOfLocation = null;
         for (ProgramGraph<L, A> pg : cs.getProgramGraphs()) {
             cartesianSumOfLocation = cartesianSumOfList(cartesianSumOfLocation, pg.getInitialLocations());
         }

         for (List<L> initialLocationList : cartesianSumOfLocation) {
             Map<String, Object> emptyAssignment = new HashMap<>();
             walkChannelSystem(transitionSystem, cs, initialLocationList, emptyAssignment, true);
         }

         return transitionSystem;
     }
    private <L> Set<List<L>> cartesianSumOfList(Set<List<L>> setsOfLists , Set<L> sets) {
        if (setsOfLists == null) {
            setsOfLists = new HashSet<>();
        }

        if (setsOfLists.size() == 0) {
            for (L object : sets) {
                List<L> newObjectList = new LinkedList<L>();
                newObjectList.add(object);
                setsOfLists.add(newObjectList);
            }
            return setsOfLists;
        }

        Set<List<L>> resultList = new HashSet<>();
        for (L set : sets) {
            for (List<L> listInSet : setsOfLists) {
                List<L> listCopy = new LinkedList<L>(listInSet);
                listCopy.add(set);
                resultList.add(listCopy);
            }
        }
        return resultList;
    }

    private <L, A> Pair<List<L>, Map<String, Object>> walkChannelSystem(TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ts, ChannelSystem<L, A> cs, List<L>currentLocations, Map<String, Object> currentAssignments, boolean isInitial) {
        HashMap<String, Object> copiedCurrentAssignments = new HashMap<>();
        for (Map.Entry<String, Object> entry : currentAssignments.entrySet()) {
            if (entry.getValue() instanceof List) {
                copiedCurrentAssignments.put(entry.getKey(), new LinkedList<>((List)entry.getValue()));
            } else {
                copiedCurrentAssignments.put(entry.getKey(), entry.getValue());
            }
        }
        Pair<List<L>, Map<String, Object>> currentState = new Pair<>(new LinkedList<L>(currentLocations), copiedCurrentAssignments);

        boolean tsContainsStates = ts.getStates().contains(currentState);

        ts.addState(currentState);
        if (isInitial) {
            ts.addInitialState(currentState);
        }

        if (tsContainsStates) {
            return currentState;
        }

        //Build transitionsCartesianProduct
        Set<List<PGTransition<L, A>>> transitionsCartesianProduct = null;
        for (int i = 0; i < cs.getProgramGraphs().size(); i++) {
            ProgramGraph<L, A> pg = cs.getProgramGraphs().get(i);
            L locationInPG = currentLocations.get(i);

            Set<PGTransition<L, A>> transitionsFromLocation = transitionsInProgramGraphWhereStartLocationEquals(pg, locationInPG);
            transitionsCartesianProduct = cartesianSumOfList(transitionsCartesianProduct, transitionsFromLocation);
        }

        //Go through all transitionsCartesianProduct and create transitions if terms are met
        for (List<PGTransition<L, A>> transitionList : transitionsCartesianProduct) {
            Map<String, Object> nextAssignment = new HashMap<String, Object>(currentAssignments);

            A action = null;
            List<L> nextLocations = new LinkedList<L>(currentLocations);

            for (PGTransition<L, A> tranition : transitionList) {
                //This action is to get from queue
                if (messageIsGetFromQueue(tranition.getAction().toString())) {
                    String varName = tranition.getAction().toString().substring(2);
                    String channelName = Character.toString(tranition.getAction().toString().charAt(0));
                    Object currentQueue = currentAssignments.get(channelName);
                    if (currentQueue != null && ((List) currentQueue).size() > 0) {
                        Object newValue = ((List) currentQueue).remove(0);
                        nextAssignment.put(varName, newValue);
                        action = tranition.getAction();

                        for (L location : currentLocations) {
                            if (location.equals(tranition.getFrom())) {
                                int indexOfLocation = nextLocations.indexOf(tranition.getFrom());
                                nextLocations.remove(indexOfLocation);
                                nextLocations.add(indexOfLocation, tranition.getTo());
                            }
                        }

                        Pair<List<L>, Map<String, Object>> nextState = walkChannelSystem(ts, cs, nextLocations, nextAssignment, false);
                        ts.addAction(action);
                        Transition<Pair<List<L>, Map<String, Object>>, A> transitionToAdd = new Transition<Pair<List<L>, Map<String, Object>>, A>(currentState, action, nextState);
                        ts.addState(currentState);
                        ts.addTransition(transitionToAdd);
                    }
                }

                //Sync recievers
                if (messageIsGetFromQueueSync(tranition.getAction().toString())) {
                    String varName = subMessageInSyncQueue(tranition.getAction().toString());

                    boolean foundMatchingSync = false;
                    for (PGTransition<L, A> matchingTransition : transitionList) {
                        if (messageIsSendToQueueSync(tranition.getAction().toString())) {
                            if (varName.equals(subMessageInSyncQueue(tranition.getAction().toString()))) {
                                foundMatchingSync = true;
                                action = (A) (subMessageInSyncQueue(tranition.getAction().toString()) + "|" + varName);

                                for (L location : currentLocations) {
                                    if (location.equals(tranition.getFrom())) {
                                        int indexOfLocation = nextLocations.indexOf(tranition.getFrom());
                                        nextLocations.remove(indexOfLocation);
                                        nextLocations.add(indexOfLocation, tranition.getTo());
                                    }
                                }

                                Pair<List<L>, Map<String, Object>> nextState = walkChannelSystem(ts, cs, nextLocations, nextAssignment, false);
                                ts.addAction(action);
                                Transition<Pair<List<L>, Map<String, Object>>, A> transitionToAdd = new Transition<Pair<List<L>, Map<String, Object>>, A>(currentState, action, nextState);
                                ts.addTransition(transitionToAdd);
                            }
                        }
                    }
                }

                //Sync senders
                if (messageIsSendToQueueSync(tranition.getAction().toString())) {
                    String varName = subMessageInSyncQueue(tranition.getAction().toString());

                    boolean foundMatchingSync = false;
                    for (PGTransition<L, A> matchingTransition : transitionList) {
                        if (messageIsGetFromQueueSync(tranition.getAction().toString())) {
                            if (varName.equals(subMessageInSyncQueue(tranition.getAction().toString()))) {
                                foundMatchingSync = true;

                                for (L location : currentLocations) {
                                    if (location.equals(tranition.getFrom())) {
                                        int indexOfLocation = nextLocations.indexOf(tranition.getFrom());
                                        nextLocations.remove(indexOfLocation);
                                        nextLocations.add(indexOfLocation, tranition.getTo());
                                    }
                                }

                                Pair<List<L>, Map<String, Object>> nextState = walkChannelSystem(ts, cs, nextLocations, nextAssignment, false);
                                ts.addAction(action);
                                Transition<Pair<List<L>, Map<String, Object>>, A> transitionToAdd = new Transition<Pair<List<L>, Map<String, Object>>, A>(currentState, action, nextState);
                                ts.addTransition(transitionToAdd);
                            }
                        }
                    }
                }

                //Sender
                if (messageIsSendToQueue(tranition.getAction().toString())) {
                    Object valueToSendToChannel = tranition.getAction().toString().substring(2);
                    String channelName = Character.toString(tranition.getAction().toString().charAt(0));

                    List currentAssignmentToChannel = (List)nextAssignment.getOrDefault(channelName, new LinkedList<>());
                    currentAssignmentToChannel = new LinkedList(currentAssignmentToChannel);
                    currentAssignmentToChannel.add(valueToSendToChannel);
                    nextAssignment.put(channelName, currentAssignmentToChannel);

                    for (L location : currentLocations) {
                        if (location.equals(tranition.getFrom())) {
                            int indexOfLocation = nextLocations.indexOf(tranition.getFrom());
                            nextLocations.remove(indexOfLocation);
                            nextLocations.add(indexOfLocation, tranition.getTo());
                        }
                    }

                    Pair<List<L>, Map<String, Object>> nextState = walkChannelSystem(ts, cs, nextLocations, nextAssignment, false);
                    ts.addAction(action);
                    Transition<Pair<List<L>, Map<String, Object>>, A> transitionToAdd = new Transition<Pair<List<L>, Map<String, Object>>, A>(currentState, action, nextState);
                    ts.addTransition(transitionToAdd);
                }

                //No action
                String message = tranition.getAction().toString();
                if (!messageIsGetFromQueueSync(message) && !messageIsGetFromQueue(message) && !messageIsSendToQueue(message) && !messageIsSendToQueueSync(message)) {
                    for (L location : currentLocations) {
                        if (location.equals(tranition.getFrom())) {
                            int indexOfLocation = nextLocations.indexOf(tranition.getFrom());
                            nextLocations.remove(indexOfLocation);
                            nextLocations.add(indexOfLocation, tranition.getTo());
                        }
                    }

                    Pair<List<L>, Map<String, Object>> nextState = walkChannelSystem(ts, cs, nextLocations, nextAssignment, false);
                    ts.addAction(action);
                    Transition<Pair<List<L>, Map<String, Object>>, A> transitionToAdd = new Transition<Pair<List<L>, Map<String, Object>>, A>(currentState, action, nextState);
                    ts.addTransition(transitionToAdd);
                }
            } //Finish for loop for all transitions
        }

        return currentState;
    }


    private boolean messageIsSendToQueue (String message) {
        if (message.length() > 2 && Character.isUpperCase(message.charAt(0)) && message.charAt(1) == '!') {
            return true;
        }
        return false;
    }

    private boolean messageIsGetFromQueue (String message) {
        if (message.length() > 2 && Character.isUpperCase(message.charAt(0)) && message.charAt(1) == '?') {
            return true;
        }
        return false;
    }

    private boolean messageIsSendToQueueSync (String message) {
        if (message.length() > 2 && message.charAt(0) == '_' && message.charAt(message.length() - 1) == '!') {
            return true;
        }
        return false;
    }

    private boolean messageIsGetFromQueueSync (String message) {
        if (message.length() > 2 && message.charAt(0) == '_' && message.charAt(message.length() - 1) == '?') {
            return true;
        }
        return false;
    }

    private String subMessageInSyncQueue (String message) {
        if (message.length() > 2) {
            return message.substring(1, message.length() - 1);
        }
        return message;
        
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    /*TODO*/
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
