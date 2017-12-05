package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.map;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.p;

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
//dasda
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
    

    /*///////////////////////////////////////////
     * ////////////////HW1 ENDS HERE//////////////
     *//////////////////////////////////////////
     
    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        return interleave(ts1, ts2, new HashSet<A>());
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem transitionSystem = createTransitionSystem();

        // Extract actions
        for (Object action : ts1.getActions()) {
            transitionSystem.addAction(action);
        }

        for (Object action : ts2.getActions()) {
            transitionSystem.addAction(action);
        }

        // Extract AP
        for (Object ap : ts1.getAtomicPropositions()) {
            transitionSystem.addAtomicProposition(ap);
        }

        for (Object ap : ts2.getAtomicPropositions()) {
            transitionSystem.addAtomicProposition(ap);
        }

        // Extract states and initials
        for (Object s1 : ts1.getStates()) {
            for (Object s2 : ts2.getStates()) {

                Pair<S1, S2> state = p(s1, s2);
                transitionSystem.addState(state);

                if (ts1.getInitialStates().contains(s1) && ts2.getInitialStates().contains(s2)) {
                    transitionSystem.addInitialState(state);
                }

                Set<P> ap = ts1.getLabel(state.first);
                if (ap.size() > 0) {
                    for (P p : ap) {
                        transitionSystem.addToLabel(state, p);
                    }
                }
                ap = ts2.getLabel(state.second);
                if (ap.size() > 0) {
                    for (P p : ap) {
                        transitionSystem.addToLabel(state, p);
                    }
                }
            }
        }


        // Transitions
        List<Pair> states = new ArrayList<>(transitionSystem.getInitialStates());
        for (int i = 0; i < states.size(); i++) {
            Pair<S1, S2> state = states.get(i);

            for (Transition t1 : ts1.getTransitions()) {
                if (t1.getFrom().equals(state.first) && !handShakingActions.contains(t1.getAction())) {
                    Pair<S1, S2> toState = p(t1.getTo(), state.second);
                    addInterleaveState(ts1, ts2, transitionSystem, states, toState);
                    transitionSystem.addTransition(new Transition(state, t1.getAction(), toState));
                }
            }

            for (Transition t2 : ts2.getTransitions()) {
                if (t2.getFrom().equals(state.second) && !handShakingActions.contains(t2.getAction())) {
                    Pair<S1, S2> toState = p(state.first, t2.getTo());
                    addInterleaveState(ts1, ts2, transitionSystem, states, toState);
                    transitionSystem.addTransition(new Transition(state, t2.getAction(), toState));
                }
            }

            for (Transition t1 : ts1.getTransitions()) {
                if (t1.getFrom().equals(state.first) && handShakingActions.contains(t1.getAction())) {
                    for (Transition t2 : ts2.getTransitions()) {
                        if (t2.getFrom().equals(state.second) && t1.getAction().equals(t2.getAction())) {
                            Pair<S1, S2> toState = p(t1.getTo(), t2.getTo());
                            addInterleaveState(ts1, ts2, transitionSystem, states, toState);
                            transitionSystem.addTransition(new Transition(state, t2.getAction(), toState));
                        }
                    }
                }
            }
        }

        return transitionSystem;

    }

    private <S1, S2, A, P> void addInterleaveState(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, TransitionSystem transitionSystem, List<Pair> states, Pair<S1, S2> toState) {
        if (!states.contains(toState)) {
            states.add(toState);
            transitionSystem.addState(toState);
            Set<P> ap = ts1.getLabel(toState.first);
            if (ap.size() > 0) {
                for (P p : ap) {
                    transitionSystem.addToLabel(toState, p);
                }
            }
            ap = ts2.getLabel(toState.second);
            if (ap.size() > 0) {
                for (P p : ap) {
                    transitionSystem.addToLabel(toState, p);
                }
            }
        }
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl<>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph programGraph = createProgramGraph();

        // Extract locations
        for (L1 l1 : pg1.getLocations()) {
            for (L2 l2 : pg2.getLocations()) {
                programGraph.addLocation(p(l1, l2));
            }
        }

        // Extract initial locations
        for (L1 l1 : pg1.getInitialLocations()) {
            for (L2 l2 : pg2.getInitialLocations()) {
                programGraph.addInitialLocation(p(l1, l2));
            }
        }

        // Extract initialization
        for (List<String> l1 : pg1.getInitalizations()) {
            for (List<String> l2 : pg2.getInitalizations()) {
                List<String> helper = new ArrayList<>(l1);
                helper.addAll(l2);
                programGraph.addInitalization(helper);
            }
        }

        List<Pair<L1, L2>> states = new ArrayList<>(programGraph.getInitialLocations());

        for (int i = 0; i < states.size(); i++) {
            Pair<L1, L2> state = states.get(i);

            for (PGTransition<L1, A> pgTransition : pg1.getTransitions()) {
                if (state.first.equals(pgTransition.getFrom())) {
                    Pair<L1, L2> toState = p(pgTransition.getTo(), state.second);

                    if (!states.contains(toState)) {
                        states.add(toState);
                        programGraph.addLocation(toState);
                    }

                    programGraph.addTransition(new PGTransition(state, pgTransition.getCondition(), pgTransition.getAction(), toState));
                }
            }

            for (PGTransition<L2, A> pgTransition : pg2.getTransitions()) {
                if (state.second.equals(pgTransition.getFrom())) {
                    Pair<L1, L2> toState = p(state.first, pgTransition.getTo());

                    if (!states.contains(toState)) {
                        states.add(toState);
                        programGraph.addLocation(toState);
                    }

                    programGraph.addTransition(new PGTransition(state, pgTransition.getCondition(), pgTransition.getAction(), toState));
                }
            }
        }

        return programGraph;
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
        Object[] RegNames = currentStateRegistersNames.toArray();
        int j=0;
        for(Boolean curr: currentStateRegisters.values())
        {
        	if (curr)
        	{
                transitionSystem.addToLabel(initialState, RegNames[j]); ;

        	}
        	++j;
        }
       
        Map<String, Boolean>  currentStateInput = initialState.second;
        Set<String> currentStateInputNames = currentStateInput.keySet();
        Object[] InNames = currentStateInputNames.toArray();
        j=0;
        for(Boolean currIn: currentStateInput.values())
        {
        	if (currIn)
        	{
        		 transitionSystem.addToLabel(initialState, InNames[j]);

        	}
        	++j;
        }
        
        Map<String, Boolean>  currentStateOutput = c.computeOutputs(currentStateRegisters, currentStateInput);
        Set<String> currentStateOutputNames = currentStateOutput.keySet();
        Object[] OutNames = currentStateOutputNames.toArray();
        j=0;
        for(Boolean currOut: currentStateOutput.values())
        {
        	if (currOut)
        	{
        		 transitionSystem.addToLabel(initialState, OutNames[j]);

        	}
        	++j;
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
    	List<ConditionDef> c = new ArrayList<>(conditionDefs);
        TransitionSystem transitionSystem = createTransitionSystem();

        // Initialize states
        for (L l : pg.getInitialLocations()) {
            if (pg.getInitalizations().size() > 0) {
                for (List<String> initialization : pg.getInitalizations()) {
                    Map<String, Object> eval = new HashMap<>();
                    for (String action : initialization) {
                        for (ActionDef actionDef : actionDefs) {
                            if (actionDef.isMatchingAction(action)) {
                                eval = actionDef.effect(eval, action);
                            }
                        }
                    }
                    Pair state = p(l, eval);
                    transitionSystem.addState(state);
                    transitionSystem.addInitialState(state);



                    // Add AP and L
                    for (Map.Entry atomic : eval.entrySet()) {
                        transitionSystem.addAtomicProposition(atomic.getKey() + " = " + atomic.getValue());
                        transitionSystem.addToLabel(state, atomic.getKey() + " = " + atomic.getValue());
                    }

                    transitionSystem.addAtomicProposition(l.toString());
                    transitionSystem.addToLabel(state, l.toString());

                }
            } else {
                Pair state = p(l, new HashMap<>());
                transitionSystem.addState(state);
                transitionSystem.addInitialState(state);

                transitionSystem.addAtomicProposition(l.toString());
                transitionSystem.addToLabel(state, l.toString());
            }
        }


        // Add all states
        List<Pair<String, Map<String, Object>>> states = new ArrayList<>(transitionSystem.getInitialStates());
        for (int i = 0; i < states.size(); i++) {
            Pair<String, Map<String, Object>> state = states.get(i);
            for (PGTransition pgTransition : pg.getTransitions()) {
                if (pgTransition.getFrom().equals(state.first)) {
                    for (ConditionDef conditionDef : conditionDefs) {
                        if (conditionDef.evaluate(state.second, pgTransition.getCondition())) {
                            Map<String, Object> eval = state.second;
                            for (ActionDef actionDef : actionDefs) {
                                if (actionDef.isMatchingAction(pgTransition.getAction())) {
                                    eval = actionDef.effect(eval, pgTransition.getAction());
                                }
                            }
                            Pair toState = p(pgTransition.getTo(), eval);
                            if (!states.contains(toState)) {
                                states.add(toState);
                                transitionSystem.addState(toState);



                                // Add AP and L
                                for (Map.Entry atomic : eval.entrySet()) {
                                    transitionSystem.addAtomicProposition(atomic.getKey() + " = " + atomic.getValue());
                                    transitionSystem.addToLabel(toState, atomic.getKey() + " = " + atomic.getValue());
                                }

                                transitionSystem.addAtomicProposition(pgTransition.getTo().toString());
                                transitionSystem.addToLabel(toState, pgTransition.getTo().toString());

                            }
                            transitionSystem.addAction(pgTransition.getAction());
                            transitionSystem.addTransition(new Transition(state, pgTransition.getAction(), toState));
                            break;
                        }
                    }
                }
            }
        }
        return transitionSystem;
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

        ParserBasedActDef parserBasedActDef = new ParserBasedActDef();
        ParserBasedInterleavingActDef parserBasedInterleavingActDef = new ParserBasedInterleavingActDef();


        Set<ConditionDef> conditionDefs = new HashSet<ConditionDef>() {
            {
                add(new ParserBasedCondDef());
            }
        };

        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystem = createTransitionSystem();

        List<List<L>> initialLocations = extractInitialLocations(new ArrayList<>(), cs.getProgramGraphs());

        for (List<L> location : initialLocations) {
            Pair<List<L>, Map<String, Object>> state = p(location, map());
            transitionSystem.addState(state);
            transitionSystem.addInitialState(state);
        }


        List<Pair<List<L>, Map<String, Object>>> states = new ArrayList<>(transitionSystem.getStates());

        for (int s = 0; s < states.size(); s++) {

            Pair<List<L>, Map<String, Object>> state = states.get(s);
            List<List<PGTransition<L, A>>> possibleTransitions = new ArrayList<>();

            for (int i = 0; i < cs.getProgramGraphs().size(); i++) {
                possibleTransitions.add(new ArrayList<PGTransition<L, A>>());

                for (PGTransition<L, A> pgTransition : cs.getProgramGraphs().get(i).getTransitions()) {

                    if (pgTransition.getFrom().equals(state.first.get(i))) {
                        boolean conditionMatched = true;
                        for (ConditionDef conditionDef : conditionDefs) {
                            if (!conditionDef.evaluate(state.second, pgTransition.getCondition())) {
                                conditionMatched = false;
                            }
                        }

                        if (conditionMatched) {

                            Map<String, Object> eval = state.second;
                            if (parserBasedInterleavingActDef.isOneSidedAction(pgTransition.getAction().toString())) {
                                possibleTransitions.get(i).add(pgTransition);
                                continue;
                            } else {
                                if (parserBasedInterleavingActDef.isMatchingAction(pgTransition.getAction())) {
                                    eval = parserBasedInterleavingActDef.effect(eval, pgTransition.getAction());
                                } else {
                                    eval = parserBasedActDef.effect(eval, pgTransition.getAction());
                                    if (eval == null) {
                                        possibleTransitions.get(i).add(pgTransition);
                                        continue;
                                    }
                                }

                                List<L> location = new ArrayList<L>(state.first);
                                location.set(i, pgTransition.getTo());

                                Pair<List<L>, Map<String, Object>> newState = p(location, eval);

                                transitionSystem.addState(newState);
                                transitionSystem.addAction(pgTransition.getAction());
                                transitionSystem.addTransition(new Transition<Pair<List<L>, Map<String, Object>>, A>(state, pgTransition.getAction(), newState));

                                if (!states.contains(newState)) {
                                    states.add(newState);
                                }
                            }
                        }
                    }
                }
            }

            for (int i = 0; i < possibleTransitions.size(); i++) {
                List<PGTransition<L, A>> firstPossibleTransitions = possibleTransitions.get(i);
                for (int j = i + 1; j < possibleTransitions.size(); j++) {
                    List<PGTransition<L, A>> secondPossibleTransitions = possibleTransitions.get(j);
                    for (int t = 0; t < possibleTransitions.get(i).size(); t++) {
                        for (int t2 = 0; t2 < possibleTransitions.get(j).size(); t2++) {
                            String action = firstPossibleTransitions.get(t).getAction() + " | " + secondPossibleTransitions.get(t2).getAction();
                            Map<String, Object> eval = state.second;
                            if (parserBasedInterleavingActDef.isMatchingAction(action)) {
                                eval = parserBasedInterleavingActDef.effect(eval, action);

                                if (eval != null) {


                                    List<L> location = new ArrayList<L>(state.first);
                                    location.set(i, firstPossibleTransitions.get(t).getTo());
                                    location.set(j, secondPossibleTransitions.get(t2).getTo());

                                    Pair<List<L>, Map<String, Object>> newState = p(location, eval);

                                    transitionSystem.addState(newState);
                                    transitionSystem.addAction((A) action);
                                    transitionSystem.addTransition(new Transition<Pair<List<L>, Map<String, Object>>, A>(state, (A) action, newState));

                                    if (!states.contains(newState)) {
                                        states.add(newState);
                                    }
                                }
                            }
                        }
                    }
                }
            }

        }


        return transitionSystem;
    }


    private <L, A> List<List<L>> extractInitialLocations(List<L> prev, List<ProgramGraph<L, A>> programGraphs) {
        List<List<L>> result = new ArrayList<>();
        if (programGraphs.size() == 0) {
            result.add(prev);
        } else {

            ProgramGraph<L, A> programGraph = programGraphs.get(0);
            for (L location : programGraph.getInitialLocations()) {
                List<L> loc = new ArrayList<>(prev);
                loc.add(location);
                List<ProgramGraph<L, A>> nextGraphs = new ArrayList<>(programGraphs);
                nextGraphs.remove(0);
                result.addAll(extractInitialLocations(loc, nextGraphs));
            }
        }

        return result;
    }


    /*no need for hw2*/
    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }
/*no need for hw2*/

    
    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
    	  NanoPromelaParser.StmtContext root = NanoPromelaFileReader.pareseNanoPromelaFile(filename);
          return programGraphFromStmtContext(root);
         }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
    	NanoPromelaParser.StmtContext root = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
        return programGraphFromStmtContext(root);
        }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
    	NanoPromelaParser.StmtContext root = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
        return programGraphFromStmtContext(root);
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
    
    
    private ProgramGraph<String, String> programGraphFromStmtContext(NanoPromelaParser.StmtContext root) {

        ProgramGraph<String, String> programGraph = createProgramGraph();
        StmtNode rootNode = new StmtNode(root, "");

        // initial
        programGraph.addInitialLocation(rootNode.getStateString());

        // exit
        programGraph.addLocation("");

        List<StmtNode> stmtNodes = new ArrayList<>();
        stmtNodes.add(rootNode);
        for (int i = 0; i < stmtNodes.size(); i++) {
            StmtNode node = stmtNodes.get(i);
            switch (node.getType()) {
                case ENDING:
                    programGraph.addLocation(node.getStateString());
                    programGraph.addTransition(node.getTransaction());
                    break;
                case IF:
                    handleIfstmt(stmtNodes, programGraph, node);
                    break;
                case DO:
                    handleDostmt(stmtNodes, programGraph, node);
                    break;
                case STMTSTMT:
                    handleStmtStmt(stmtNodes, programGraph, node);
                    break;
            }
        }

        return programGraph;
    }

    private void handleStmtStmt(List<StmtNode> stmtNodes, ProgramGraph<String, String> programGraph, StmtNode state) {
        Pair<StmtNode, StmtNode> split = state.split();
        if (split.first.getType() == StmtNode.Type.ENDING) {
            programGraph.addTransition(split.first.getTransaction());
        } else {
            stmtNodes.add(split.first);
        }

        stmtNodes.add(split.second);
    }

    private void handleIfstmt(List<StmtNode> stmtNodes, ProgramGraph<String, String> programGraph, StmtNode state) {

        if (state.parent == null || state.parent.getType() != StmtNode.Type.IF) {
            programGraph.addLocation(state.getStateString());
        }

        for (int i = 0; i < state.root.ifstmt().option().size(); i++) {
            NanoPromelaParser.OptionContext option = state.root.ifstmt().option(i);
            String condition = "(" + option.boolexpr().getText() + ")";
            StmtNode optionStmt = new StmtNode(option.stmt(), state.next, condition, state);
            handleOptionStmt(stmtNodes, programGraph, optionStmt);
        }
    }

    private void handleDostmt(List<StmtNode> stmtNodes, ProgramGraph<String, String> programGraph, StmtNode state) {
        programGraph.addLocation(state.getStateString());
        StmtNode exitNode = new StmtNode(state.root, state.next, "", state, true);

        for (int i = 0; i < state.root.dostmt().option().size(); i++) {
            NanoPromelaParser.OptionContext option = state.root.dostmt().option(i);

            String condition = "(" + option.boolexpr().getText() + ")";
            StmtNode optionStmt = new StmtNode(option.stmt(), state.getStateString(), condition, state);
            exitNode.appendCondition(condition);

            handleOptionStmt(stmtNodes, programGraph, optionStmt);


            StmtNode innerOptionStmt = optionStmt.clone();
            innerOptionStmt.parent = state.clone();
            innerOptionStmt.parent.parent = null;
            innerOptionStmt.parent.condition = "";
            handleOptionStmt(stmtNodes, programGraph, innerOptionStmt);
        }

        exitNode.condition = "!(" + exitNode.condition + ")";
        programGraph.addTransition(exitNode.getTransaction());


        StmtNode innerExitNode = exitNode.clone();
        innerExitNode.parent = state.clone();
        innerExitNode.parent.parent = null;
        innerExitNode.parent.condition = "";
        programGraph.addTransition(innerExitNode.getTransaction());
    }

    private void handleOptionStmt(List<StmtNode> stmtNodes, ProgramGraph<String, String> programGraph, StmtNode optionStmt) {
        switch (optionStmt.getType()) {
            case ENDING:
                programGraph.addTransition(optionStmt.getTransaction());
                break;

            case IF:
                stmtNodes.add(optionStmt);
                break;

            case DO:
                stmtNodes.add(optionStmt);
                break;

            case STMTSTMT:
                Pair<StmtNode, StmtNode> split = optionStmt.split();
                if (split.first.getType() == StmtNode.Type.ENDING) {
                    programGraph.addTransition(split.first.getTransaction());
                } else {
                    stmtNodes.add(split.first);
                }

                stmtNodes.add(split.second);
                break;
        }
    }


    private static class StmtNode {

        private NanoPromelaParser.StmtContext root;
        private StmtNode parent;
        private String condition;
        private String next;
        private boolean exit;

        public StmtNode(NanoPromelaParser.StmtContext root, String next) {
            this.root = root;
            this.next = next;
            this.exit = false;
            this.condition = "";
        }

        public StmtNode(NanoPromelaParser.StmtContext root, String next, String condition) {
            this(root, next);
            this.condition = condition;
        }

        public StmtNode(NanoPromelaParser.StmtContext root, String next, String condition, StmtNode parent) {
            this(root, next, condition);
            this.parent = parent;
        }


        public StmtNode(NanoPromelaParser.StmtContext root, String next, String condition, StmtNode parent, boolean exit) {
            this(root, next, condition, parent);
            this.exit = exit;
        }

        public StmtNode clone() {
            return new StmtNode(root, next, condition, parent, exit);
        }

        public void appendCondition(String condition) {
            if (this.condition.isEmpty()) {
                this.condition = condition;
            } else {
                this.condition = this.condition + "||" + condition;
            }
        }

        public String getConditionsString() {
            String result = condition;

            StmtNode parent = this.parent;
            while (parent != null) {
                if (!parent.condition.isEmpty()) {
                    result = parent.condition + " && (" + result + ")";
                } else {
                    break;
                }
                parent = parent.parent;
            }
            return result;
        }

        public String getStateString() {
            return root.getText() + (next.isEmpty() ? "" : ";") + next;
        }

        public PGTransition<String, String> getTransaction() {

            StmtNode parent = this.parent;
            if (parent == null) {

                if (exit) {

                    return new PGTransition(getStateString(),
                            getConditionsString(),
                            "",
                            next);
                } else {
                    return new PGTransition(getStateString(),
                            getConditionsString(),
                            root.getText(),
                            next);
                }

            } else {

                while (parent.parent != null) {

                    if (parent.getType() == Type.ENDING) {
                        break;
                    } else {
                        parent = parent.parent;

                    }
                }

                if (getType() == Type.ENDING) {
                    return new PGTransition(parent.getStateString(),
                            getConditionsString(),
                            root.getText(),
                            next);
                } else {
                    return new PGTransition(parent.getStateString(),
                            getConditionsString(),
                            "",
                            next);
                }
            }
        }

        public Pair<StmtNode, StmtNode> split() {
            StmtNode second = new StmtNode(root.stmt(1), next, "", null);
            StmtNode first = new StmtNode(root.stmt(0), second.getStateString(), condition, parent);

            return p(first, second);
        }


        public Type getType() {
            if (root.assstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null || root.atomicstmt() != null || root.skipstmt() != null) {
                return Type.ENDING;
            } else if (root.ifstmt() != null) {
                return Type.IF;
            } else if (root.dostmt() != null) {
                return Type.DO;
            } else {
                return Type.STMTSTMT;
            }
        }

        public void appendNext(String stateString) {
            if (next.isEmpty()) {
                next = stateString;
            } else {
                next = stateString + ";" + next;
            }
        }

        enum Type {
            ENDING, IF, DO, STMTSTMT
        }
    }
   
}
