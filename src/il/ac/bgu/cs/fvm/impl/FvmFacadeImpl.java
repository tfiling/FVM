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
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;
import il.ac.bgu.cs.fvm.ltl.*;
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
import java.util.Stack;
import java.util.stream.Collectors;


/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its 
 * sub-packages.
 */
//dasda
public class FvmFacadeImpl implements FvmFacade {
	public boolean _debugFLAG =false;

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


	/*///////////////////////////////////////////
	 * ////////////////Private Functions//////////////
	 *//////////////////////////////////////////
	
	private <S1, S2, A, P> void addNewState(
			TransitionSystem<S1, A, P> ts1, 
			TransitionSystem<S2, A, P> ts2, 
			TransitionSystem transitionSystem, 
			Pair<S1, S2> state) {

		transitionSystem.addState(state);
		if (_debugFLAG)
		{
			System.out.println("About Adding new state... " + transitionSystem.getName());
		}
		Set<P> ap = ts1.getLabel(state.first);
		Iterator<P> apIterator = ts1.getLabel(state.first).iterator();
		while (apIterator.hasNext()) {
			transitionSystem.addToLabel(state, apIterator.next());
		}

		apIterator = ts2.getLabel(state.second).iterator();
		while (apIterator.hasNext()) {
			transitionSystem.addToLabel(state, apIterator.next());
		}
	}

	private <S1, S2, A, P>void uniteActionsAndAP(
			TransitionSystem<S1, A, P> ts1, 
			TransitionSystem<S2, A, P> ts2, 
			TransitionSystem transitionSystem)
	{
		if (_debugFLAG)
		{
			System.out.println("unite actions from both transition systems");
		}
		
		for (Object action : ts1.getActions()) {
			if (this._debugFLAG)
			{
				System.out.println("appended action: " + action.toString());
			}
			transitionSystem.addAction(action);
		}

		for (Object action : ts2.getActions()) {
			if (this._debugFLAG)
			{
				System.out.println("appended action: " + action.toString());
			}
			transitionSystem.addAction(action);
		}

		// unite AP from both transition systems
		for (Object ap : ts1.getAtomicPropositions()) {
			if (this._debugFLAG)
			{
				System.out.println("appended AP: " + ap.toString());
			}
			transitionSystem.addAtomicProposition(ap);
		}

		for (Object ap : ts2.getAtomicPropositions()) {
			if (this._debugFLAG)
			{
				System.out.println("appended AP: " + ap.toString());
			}
			transitionSystem.addAtomicProposition(ap);
		}

	}

	private List<Map<String, Boolean>> generateAllPossibleCombinations (String[] inputs) {

		List<Map<String, Boolean>> results = new LinkedList<Map<String,Boolean>>();
		int resultSize = (int)Math.pow(2, inputs.length);
		List<Boolean>[] possibleBooleanCombinations = new List[resultSize];
		fillListPossibleCombinations(possibleBooleanCombinations);

		for(int i = 0; i<resultSize; ++i)
		{//iterate the lists of possible configurations
			results.add(new HashMap<String, Boolean>());
			for (int j = 0; j < inputs.length; ++j)
			{//iterate the names of inputs
				results.get(i).put(inputs[j], possibleBooleanCombinations[i].get(j));
			}
		}  	

		return results;
	}

	private void fillListPossibleCombinations (List<Boolean>[] possibleBooleanCombinations) {
		if (possibleBooleanCombinations.length == 2) {
			if (possibleBooleanCombinations[0] == null) {
				possibleBooleanCombinations[0] = new LinkedList<Boolean>();
			}
			if (possibleBooleanCombinations[1] == null) {
				possibleBooleanCombinations[1] = new LinkedList<Boolean>();
			}
			possibleBooleanCombinations[0].add(new Boolean(true));
			possibleBooleanCombinations[1].add(new Boolean(false));
			return;
		}

		List<Boolean>[] firstHalf = new List[possibleBooleanCombinations.length / 2];
		List<Boolean>[] secondHalf = new List[possibleBooleanCombinations.length / 2];

		for (int i = 0; i < possibleBooleanCombinations.length; i++) {
			if (possibleBooleanCombinations[i] == null) {
				possibleBooleanCombinations[i] = new LinkedList<Boolean>();
			}
			if (i < possibleBooleanCombinations.length / 2) {
				possibleBooleanCombinations[i].add(new Boolean(true));
				firstHalf[i] = possibleBooleanCombinations[i];
			} else {
				possibleBooleanCombinations[i].add(new Boolean(false));
				secondHalf[i - possibleBooleanCombinations.length / 2] = possibleBooleanCombinations[i];
			}
		}

		fillListPossibleCombinations(firstHalf);
		fillListPossibleCombinations(secondHalf);
	}


	private void generateTransitionSystem(Circuit c, TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystem, Pair<Map<String, Boolean>, Map<String, Boolean>> currentState) {

		if (transitionSystem.getStates().contains(currentState)) {
			return;
		}

		transitionSystem.addState(currentState);

		for(String registerName : currentState.second.keySet())
		{
			if (currentState.second.get(registerName))
			{
				transitionSystem.addToLabel(currentState, registerName); ;
			}
		}

		for(String InputName : currentState.first.keySet())
		{
			if (currentState.first.get(InputName))
			{
				transitionSystem.addToLabel(currentState, InputName); ;
			}
		}

		Map<String, Boolean>  out = c.computeOutputs(currentState.first, currentState.second);
		for(String outName: out.keySet())
		{
			if (out.get(outName))
			{
				transitionSystem.addToLabel(currentState, outName);
			}
		}

		String[] inputNames = new String[c.getInputPortNames().size()]; 
		c.getInputPortNames().toArray(inputNames);

		List<Map<String, Boolean>> allPossibleInputs = generateAllPossibleCombinations(inputNames);
		for (Map<String, Boolean>  possibleInput : allPossibleInputs) {
			Map<String, Boolean>  resultedRegisters = c.updateRegisters(currentState.first, currentState.second);

			Pair<Map<String, Boolean> , Map<String, Boolean>> newState = new Pair<>(possibleInput, resultedRegisters);
			generateTransitionSystem(c, transitionSystem, newState);

			//Transitions
			Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>> transition = new Transition<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>>(currentState, possibleInput, newState);
			transitionSystem.addTransition(transition);
		}
	}
	
	private <L> void addStateToTransitionSystem(
			TransitionSystem resultedTransitionSystem, 
			L location,
			Map<String, Object> eval, Pair state) {
		resultedTransitionSystem.addState(state);

		if (_debugFLAG)
		{
			System.out.println("In addStateToTransitionSystem, doin' to add AP and L");
		}
		
		for (Map.Entry at : eval.entrySet()) {
			resultedTransitionSystem.addAtomicProposition(at.getKey() + " = " + at.getValue());
			resultedTransitionSystem.addToLabel(state, at.getKey() + " = " + at.getValue());
		}

		resultedTransitionSystem.addAtomicProposition(location.toString());
		resultedTransitionSystem.addToLabel(state, location.toString());
	}

	private <L> void addStateToTransitionSystem(
			TransitionSystem resultedTransitionSystem, 
			List<L> locations,
			Map<String, Object> eval, Pair state) {
		for (L location : locations)
			addStateToTransitionSystem(resultedTransitionSystem, location, eval, state);
	}
	

	private <L, A> void generateInitals(
			TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> resultedTransitionSystem, 
			List<List<L>> initialLocations, 
			List<List<String>> initialEvals) {
		ParserBasedActDef actionDefinition = new ParserBasedActDef();

		for (int i = 0; i < initialLocations.size(); i++) {
			Map<String, Object> eval = new HashMap<>();
			for (List<String> initialization : initialEvals) {
				for (String action : initialization) {
					if (actionDefinition.isMatchingAction(action)) {
						eval = actionDefinition.effect(eval, action);
					}
				}
				Pair state = p(initialLocations.get(i), eval);
				addStateToTransitionSystem(resultedTransitionSystem, initialLocations.get(i), eval, state);
				resultedTransitionSystem.addInitialState(state);
			}
			if (initialEvals.size() == 0) {
				Pair state = p(initialLocations.get(i), eval);
				addStateToTransitionSystem(resultedTransitionSystem, initialLocations.get(i), eval, state);
				resultedTransitionSystem.addInitialState(state);
			}
		}
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

	private <L, A> List<List<String>> extractAllPossibleInitialEvals(List<String> prev, List<ProgramGraph<L, A>> programGraphs) {
		List<List<String>> result = new ArrayList<>();


		if (programGraphs.size() == 0) {
			result.add(prev);
		} else {
			ProgramGraph<L, A> programGraph = programGraphs.get(0);
			if (programGraph.getInitalizations().size() > 0)
			{
				for (List<String> initialization : programGraph.getInitalizations()) {
					List<String> init = new ArrayList<>(prev);
					init.addAll(initialization);
					List<ProgramGraph<L, A>> nextGraphs = new ArrayList<>(programGraphs);
					nextGraphs.remove(0);
					result.addAll(extractAllPossibleInitialEvals(init, nextGraphs));
				}            	
			}
			else
			{
				List<ProgramGraph<L, A>> nextGraphs = new ArrayList<>(programGraphs);
				nextGraphs.remove(0);
				result.addAll(extractAllPossibleInitialEvals(prev, nextGraphs));	
			}
		}

		return result;
	}

	
	private <L, A>void applyNewState(
			TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> resultedTransitionSystem, 
			Pair<List<L>, Map<String, Object>> currentState,
			List<L> currentLocation,
			A action,
			List<Pair<List<L>, Map<String, Object>>> accumulatedStates,
			Map<String, Object> eval) {

		Pair<List<L>, Map<String, Object>> newState = p(currentLocation, eval);

		addStateToTransitionSystem(resultedTransitionSystem, currentLocation, eval, newState);
		resultedTransitionSystem.addAction(action);
		resultedTransitionSystem.addTransition(new Transition<Pair<List<L>, Map<String, Object>>, A>(currentState, action, newState));

		if (!accumulatedStates.contains(newState)) {
			accumulatedStates.add(newState);
		}
	}
	
	private ProgramGraph<String, String> checkKindStmtPG(NanoPromelaParser.StmtContext root) {

		ProgramGraph<String, String> _PG = createProgramGraph();
		NanoStmt rootNode = new NanoStmt(root, "");
		// initial
		_PG.addInitialLocation(rootNode.getState());
		// DONE 
		_PG.addLocation("");

		List<NanoStmt> stmt = new ArrayList<>();
		stmt.add(rootNode);
		NanoStmt node;
		for (int i = 0; i < stmt.size(); i++) {
			node = stmt.get(i);
			if (this._debugFLAG)
			{
				System.out.println("Checking Kind..." + node.toString());
			}
			switch (node.getStmtKind()) {
			case DO:
				handleDostmt(stmt, _PG, node);
				break;
			case DONE:
				_PG.addLocation(node.getState());
				_PG.addTransition(node.getTrans());
				break;
			case STMTSTMT:
				handleAppendedStmt(stmt, _PG, node);
				break;
			case IF:
				handleIfstmt(stmt, _PG, node);
				break;                      
			}
		}

		return _PG;
	}

	private void handleAppendedStmt(List<NanoStmt> stmtNodes, ProgramGraph<String, String> programGraph, NanoStmt state) {
		Pair<NanoStmt, NanoStmt> splitedStmt = state.breakStmt();
		if (splitedStmt.first.getStmtKind() == NanoStmt.Kind.DONE) {
			if (this._debugFLAG)
			{
				System.out.println("In appended STMT there is Done stmt" + splitedStmt.first.toString());
			}

			programGraph.addTransition(splitedStmt.first.getTrans());
		} else {
			if (this._debugFLAG)
			{
				System.out.println("In appended STMT there is trans stmt" + splitedStmt.first.toString());
			}
			stmtNodes.add(splitedStmt.first);
		}

		stmtNodes.add(splitedStmt.second);
	}

	private void handleIfstmt(List<NanoStmt> stmtNodes, ProgramGraph<String, String> programGraph, NanoStmt state) {

		if (state._StmtMainNode == null || state._StmtMainNode.getStmtKind() != NanoStmt.Kind.IF) {
			if (this._debugFLAG)
			{
				System.out.println("In handle IF STMT, adding new location" + state.toString());
			}
			programGraph.addLocation(state.getState());
		}

		for (int i = 0; i < state._rootNano.ifstmt().option().size(); i++) {
			NanoPromelaParser.OptionContext option = state._rootNano.ifstmt().option(i);
			String condition = "(" + option.boolexpr().getText() + ")";
			NanoStmt optionStmt = new NanoStmt(option.stmt(), state._nextStmt, condition, state);
			if (this._debugFLAG)
			{
				System.out.println("In handle IF STMT, seding to handle STMT" + optionStmt.toString());
			}
			handleStmt(stmtNodes, programGraph, optionStmt);
		}
	}

	private void handleDostmt(List<NanoStmt> stmtNodes, ProgramGraph<String, String> PG, NanoStmt nanoStmt) {

		NanoStmt doneStmt = new NanoStmt(nanoStmt._rootNano, nanoStmt._nextStmt, "", nanoStmt, true);
		PG.addLocation(nanoStmt.getState());

		if (this._debugFLAG)
		{
			System.out.println("handle DO STMT...");
		}

		for (int i = 0; i < nanoStmt._rootNano.dostmt().option().size(); ++i) 
		{
			NanoPromelaParser.OptionContext optNano = nanoStmt._rootNano.dostmt().option(i);

			String condStmt = "(" + optNano.boolexpr().getText() + ")";
			NanoStmt optionStmt = new NanoStmt(optNano.stmt(), nanoStmt.getState(), condStmt, nanoStmt);
			doneStmt.consCondStmt(condStmt);
			if (this._debugFLAG)
			{
				System.out.println("about to handle regular STMT now...");
			}       
			handleStmt(stmtNodes, PG, optionStmt);

			NanoStmt agregOpt = optionStmt.clone();
			agregOpt._StmtMainNode = nanoStmt.clone();
			agregOpt._StmtMainNode._condStmt = "";
			agregOpt._StmtMainNode._StmtMainNode = null;
			handleStmt(stmtNodes, PG, agregOpt);
			if (this._debugFLAG)
			{
				System.out.println("handle STMT..." + agregOpt.toString());
			}

		}

		doneStmt._condStmt = "!(" + doneStmt._condStmt + ")";
		PG.addTransition(doneStmt.getTrans());
		if (this._debugFLAG)
		{
			System.out.println("About addong new trans to PG" + doneStmt.getTrans().toString());
		}
		NanoStmt agregDoneStmt = doneStmt.clone();
		agregDoneStmt._StmtMainNode = nanoStmt.clone();
		agregDoneStmt._StmtMainNode._condStmt = "";
		agregDoneStmt._StmtMainNode._StmtMainNode = null;
		PG.addTransition(agregDoneStmt.getTrans());
		if (this._debugFLAG)
		{
			System.out.println("About addong new trans to PG" + agregDoneStmt.getTrans().toString());
		}
	}

	private void handleStmt(List<NanoStmt> stmtList, ProgramGraph<String, String> PG, NanoStmt optionStmt) {
		switch (optionStmt.getStmtKind()) {
		case DONE:
			PG.addTransition(optionStmt.getTrans());
			break;

		case IF:
			stmtList.add(optionStmt);
			break;

		case DO:
			stmtList.add(optionStmt);
			break;

		case STMTSTMT:
			Pair<NanoStmt, NanoStmt> split = optionStmt.breakStmt();
			if (split.first.getStmtKind() == NanoStmt.Kind.DONE) {
				PG.addTransition(split.first.getTrans());
			} else {
				stmtList.add(split.first);
			}

			stmtList.add(split.second);
			break;
		}
	}


	private static class NanoStmt {
		enum Kind {
			STMTSTMT, DONE, IF, DO
		}
		private NanoPromelaParser.StmtContext _rootNano;
		private String _nextStmt;
		private boolean _doneStmt;
		private String _condStmt;
		private NanoStmt _StmtMainNode;
		private boolean debug = false;

		public NanoStmt(NanoPromelaParser.StmtContext begin, String nextStmt) {
			this._rootNano = begin;
			this._nextStmt = nextStmt;
			this._condStmt = "";
			this._doneStmt = false;

		}

		public NanoStmt(NanoPromelaParser.StmtContext begin, String nextStmt, String condStmt) {
			this(begin, nextStmt);
			this._condStmt = condStmt;
		}

		public NanoStmt(NanoPromelaParser.StmtContext begin,String nextStmt,  String condStmt, NanoStmt mainNode) {
			this(begin, nextStmt, condStmt);
			this._StmtMainNode = mainNode;
		}

		public NanoStmt(NanoPromelaParser.StmtContext begin, String nextStmt, String condStmt, NanoStmt mainNode, boolean exit) {
			this(begin, nextStmt, condStmt, mainNode);
			this._doneStmt = exit;
		}

		public NanoStmt clone() {
			if (debug)
			{
				System.out.println("Im in clone ");
			}
			return new NanoStmt(_rootNano, _nextStmt, _condStmt, _StmtMainNode, _doneStmt);
		}

		public String getState() {
			return _rootNano.getText() + (_nextStmt.isEmpty() ? "" : ";") + _nextStmt;
		}

		public String getCondStmt() {
			String toRet = _condStmt;
			if (debug)
			{
				System.out.println("Im in getCond");
			}
			NanoStmt parent = this._StmtMainNode;
			while (parent != null) {
				if (!parent._condStmt.isEmpty()) {
					if (debug)
					{
						System.out.println("There is a parent");
					}
					toRet = parent._condStmt + " && (" + toRet + ")";
				} else {
					break;
				}
				parent = parent._StmtMainNode;
			}
			return toRet;
		}

		public void consCondStmt(String condition) {
			if (this._condStmt.isEmpty()) {
				if (debug)
				{
					System.out.println("Nothing to cons, just this stmt ");
				}
				this._condStmt = condition;
			} else {
				if (debug)
				{
					System.out.println("Cons new stmt");
				}
				this._condStmt = this._condStmt + "||" + condition;
			}
		}    

		public PGTransition<String, String> getTrans() {
			NanoStmt parent = this._StmtMainNode;
			if (parent == null) 
			{
				if (_doneStmt) 
				{
					if (debug)
					{
						System.out.println("it's EXIT trans, so about to DONE");
					}
					return new PGTransition(getState(),
							getCondStmt(),
							"",
							_nextStmt);
				}else
				{
					return new PGTransition(getState(),
							getCondStmt(),
							_rootNano.getText(),
							_nextStmt);
				}

			} else
			{
				while (parent._StmtMainNode != null)
				{
					if (debug)
					{
						System.out.println("There is a parent");
					}
					if (parent.getStmtKind() == Kind.DONE) {
						break;
					} else {
						parent = parent._StmtMainNode;

					}
				}
				if (getStmtKind() == Kind.DONE) {
					if (debug)
					{
						System.out.println("There is a parent, and In DONE stmt");
					}
					return new PGTransition(parent.getState(),
							getCondStmt(),
							_rootNano.getText(),
							_nextStmt);
				} else {
					return new PGTransition(parent.getState(),
							getCondStmt(),
							"",
							_nextStmt);
				}
			}
		}

		public Kind getStmtKind() {
			if (_rootNano.assstmt() != null || _rootNano.chanreadstmt() != null || _rootNano.chanwritestmt() != null || _rootNano.atomicstmt() != null || _rootNano.skipstmt() != null) {
				return Kind.DONE;
			} else if (_rootNano.ifstmt() != null) {
				return Kind.IF;
			} else if (_rootNano.dostmt() != null) {
				return Kind.DO;
			} else {
				return Kind.STMTSTMT;
			}
		}

		public Pair<NanoStmt, NanoStmt> breakStmt() {
			NanoStmt _sec = new NanoStmt(_rootNano.stmt(1), _nextStmt, "", null);
			NanoStmt _fir = new NanoStmt(_rootNano.stmt(0), _sec.getState(), _condStmt, _StmtMainNode);
			if (debug)
			{
				System.out.println("About to split stmt...");
			}
			return p(_fir, _sec);
		}     

		public void consNextStmt(String newStmt) {
			if (_nextStmt.isEmpty()) {
				if (debug)
				{
					System.out.println("nothis to cons .");
				}
				_nextStmt = newStmt;
			} else {
				if (debug)
				{
					System.out.println("Cons next stmt");
				}
				_nextStmt = newStmt + ";" + _nextStmt;
			}
		}

	}



	
	
	@Override
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(			
			TransitionSystem<S1, A, P> ts1, 
			TransitionSystem<S2, A, P> ts2) {
		if (_debugFLAG)
		{
			System.out.println("In interleave, about to interleave " + ts1.toString() + " " + ts2.toString());
		}
		return interleave(ts1, ts2, new HashSet<A>());
	}

	@Override
	public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(
			TransitionSystem<S1, A, P> ts1, 
			TransitionSystem<S2, A, P> ts2, 
			Set<A> handShakingActions) {
		TransitionSystem toRetTS = createTransitionSystem();

		uniteActionsAndAP(ts1, ts2, toRetTS);
		if (_debugFLAG)
		{
			System.out.println("About to do Cartesian Product");
		}
		Iterator<S1> firstIt = ts1.getInitialStates().iterator();
		while (firstIt.hasNext()) {
			Iterator<S2> secondIt = ts2.getInitialStates().iterator();
			while(secondIt.hasNext()) {
				Object s1 = firstIt.next();
				Object s2 = secondIt.next();
				if (this._debugFLAG)
				{
					System.out.println(new String("initial state: " + s1.toString()+ ", " + s1.toString()));
				}

				Pair<S1, S2> newInitialState = p(s1, s2);
				addNewState(ts1, ts2, toRetTS, newInitialState);
				toRetTS.addInitialState(newInitialState);

			}
		}

		if (_debugFLAG)
		{
			System.out.println("In interleave, about to doing transitions");
		}
		List<Pair> states = new ArrayList<>(toRetTS.getInitialStates());
		for (int i = 0; i < states.size(); i++) {
			Pair<S1, S2> state = states.get(i);
			Transition currTrans;
			Iterator<Transition<S1,A>> firstTransitionIterator = ts1.getTransitions().iterator();
			while (firstTransitionIterator.hasNext()) {
				currTrans = firstTransitionIterator.next();
				Pair<S1, S2> destState = p(currTrans.getTo(), state.second);
				if (currTrans.getFrom().equals(state.first) && 
						!handShakingActions.contains(currTrans.getAction())) {
					if (!states.contains(destState)){
						states.add(destState);
						addNewState(ts1, ts2, toRetTS, destState);
					}
					toRetTS.addTransition(new Transition(state, currTrans.getAction(), destState));
				}
			}
			if (_debugFLAG)
			{
				System.out.println("Finishing doin states for" + state.first.toString());
			}
			Iterator<Transition<S2,A>> secondTransitionIterator = ts2.getTransitions().iterator();
			while (secondTransitionIterator.hasNext()) {
				currTrans = secondTransitionIterator.next();
				Pair<S1, S2> destState = p(state.first, currTrans.getTo());
				if (currTrans.getFrom().equals(state.second) && 
						!handShakingActions.contains(currTrans.getAction())) {
					if (!states.contains(destState)){
						states.add(destState);
						addNewState(ts1, ts2, toRetTS, destState);
					}
					toRetTS.addTransition(new Transition(state, currTrans.getAction(), destState));
				}
			}

			for (Transition t1 : ts1.getTransitions()) {
				if (t1.getFrom().equals(state.first) && handShakingActions.contains(t1.getAction())) {
					for (Transition t2 : ts2.getTransitions()) {
						if (t2.getFrom().equals(state.second) && t1.getAction().equals(t2.getAction())) {
							Pair<S1, S2> destState = p(t1.getTo(), t2.getTo());
							states.add(destState);
							addNewState(ts1, ts2, toRetTS, destState);
							toRetTS.addTransition(new Transition(state, t2.getAction(), destState));
						}
					}
				}
			}
		}

		return toRetTS;

	}
	
	@Override
	public <L, A> ProgramGraph<L, A> createProgramGraph() {
		return new ProgramGraphImpl<>();
	}

	@Override
	public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
		ProgramGraph programGraph = createProgramGraph();

		if (_debugFLAG)
		{
			System.out.println("In interleave, doin'  Extract locations");
		}
		
		for (L1 l1 : pg1.getLocations()) {
			for (L2 l2 : pg2.getLocations()) {
				programGraph.addLocation(p(l1, l2));
			}
		}

		if (_debugFLAG)
		{
			System.out.println("Extract initial locations");
		}
		 
		for (L1 l1 : pg1.getInitialLocations()) {
			for (L2 l2 : pg2.getInitialLocations()) {
				programGraph.addInitialLocation(p(l1, l2));
			}
		}

		if (_debugFLAG)
		{
			System.out.println("Extract initialization");
		}
		
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

					if (_debugFLAG)
					{
						System.out.println("Adding new trans to PG");
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
		TransitionSystem<Pair<Map<String,Boolean>, Map<String,Boolean>>, Map<String, Boolean>, Object> resultedTransitionSystem = new TransitionSystemImpl<>();

		//Atomic propositions
		for (String inputPortName : c.getInputPortNames()) {
			resultedTransitionSystem.addAtomicProposition(inputPortName);
		}
		for (String registerName : c.getRegisterNames()) {
			resultedTransitionSystem.addAtomicProposition(registerName);
		}
		for (String outputPortName : c.getOutputPortNames()) {
			resultedTransitionSystem.addAtomicProposition(outputPortName);
		}

		String[] inputNames = new String[c.getInputPortNames().size()]; 
		c.getInputPortNames().toArray(inputNames);
		//Apply all the possible combinations upon the inputs
		List<Map<String, Boolean>> allPossibleInputs = generateAllPossibleCombinations(inputNames);

		//Actions
		for (Map<String, Boolean> possibleInput : allPossibleInputs) {
			resultedTransitionSystem.addAction(possibleInput);
		}


		Map<String, Boolean> possibleInput;
		List<Pair<Map<String, Boolean>, Map<String, Boolean>>> allInitialStates = new ArrayList<>(); 
		//Initial state and states, transitions and labeling
		for (int i = 0; i < allPossibleInputs.size(); i++) {
			possibleInput = allPossibleInputs.get(i);
			Map<String, Boolean> registerInitialValues = new HashMap<String,Boolean>();
			for(String regName : c.getRegisterNames()) {
				registerInitialValues.put(regName, new Boolean(false));
			}
			Pair<Map<String, Boolean>, Map<String, Boolean>> initialState = new Pair<>(possibleInput, registerInitialValues);
			allInitialStates.add(initialState);
		}

		for (Pair<Map<String, Boolean>, Map<String, Boolean>> initialState : allInitialStates) {
			generateTransitionSystem(c, resultedTransitionSystem, initialState);			
		}

		for (int i = 0; i < allInitialStates.size(); i++) {
			resultedTransitionSystem.addInitialState(allInitialStates.get(i));
		}

		return resultedTransitionSystem;
	}


	@Override
	public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
			ProgramGraph<L, A> pg, 
			Set<ActionDef> actionDefs, 
			Set<ConditionDef> conditionDefs) {
		TransitionSystem resultedTransitionSystem = createTransitionSystem();
		L[] locations = (L[])pg.getInitialLocations().toArray();
		List<List<String>> initilizations = new ArrayList<>(pg.getInitalizations());

		if (_debugFLAG)
		{
			System.out.println("In transitionSystemFromProgramGraph, doin' Initialize states");
		}
		
		for (int i = 0; i < locations.length; i++) {
		Map<String, Object> eval = new HashMap<>();
		for (int j = 0; j < initilizations.size(); j++) {
			for (String action : initilizations.get(j)) {
				for (ActionDef actD : actionDefs) {
					if (actD.isMatchingAction(action)) {
						eval = actD.effect(eval, action);
					}
				}
			}
				Pair newStates = p(locations[i], eval);
				addStateToTransitionSystem(resultedTransitionSystem, locations[i], eval, newStates);
				resultedTransitionSystem.addInitialState(newStates);

			}

			if (initilizations.size() == 0) {
				Pair state = p(locations[i], new HashMap<>());
				addStateToTransitionSystem(resultedTransitionSystem, locations[i], eval, state);
				resultedTransitionSystem.addInitialState(state);
			}
		}

		List<Pair<String, Map<String, Object>>> accumulatedStates = new ArrayList<>(resultedTransitionSystem.getInitialStates());
		for (int i = 0; i < accumulatedStates.size(); i++) {
			Pair<String, Map<String, Object>> state = accumulatedStates.get(i);
			for (PGTransition transition : pg.getTransitions()) {
				if (transition.getFrom().equals(state.first)) {
					for (ConditionDef conditionDef : conditionDefs) 
						evaluatorItration: {
						if (conditionDef.evaluate(state.second, transition.getCondition())) {
							Map<String, Object> eval = state.second;
							for (ActionDef actionDef : actionDefs) {
								if (actionDef.isMatchingAction(transition.getAction())) {
									eval = actionDef.effect(eval, transition.getAction());
								}
							}
							Pair destState = p(transition.getTo(), eval);
							if (!accumulatedStates.contains(destState)) {
								accumulatedStates.add(destState);
								addStateToTransitionSystem(resultedTransitionSystem, transition.getTo(), eval, destState);
							}
							resultedTransitionSystem.addAction(transition.getAction());
							resultedTransitionSystem.addTransition(new Transition(state, transition.getAction(), destState));
							break evaluatorItration;
						}
					}
				}
			}
		}
		return resultedTransitionSystem;
	}


	@Override
	public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {

		TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> toRetTS = createTransitionSystem();
		ParserBasedCondDef conditionDefinition = new ParserBasedCondDef();
		ParserBasedActDef actionDefinition = new ParserBasedActDef();
		ParserBasedInterleavingActDef interleavingActionDefinition = new ParserBasedInterleavingActDef();

		List<List<L>> initialLocations = extractInitialLocations(new ArrayList<>(), cs.getProgramGraphs());
		List<List<String>> initialEvals = extractAllPossibleInitialEvals(new ArrayList<>(), cs.getProgramGraphs());

		generateInitals(toRetTS, initialLocations, initialEvals);

		List<Pair<List<L>, Map<String, Object>>> accumulatedStates = new ArrayList<>(toRetTS.getStates());

		for (int currentStateIndex = 0; currentStateIndex < accumulatedStates.size(); currentStateIndex++) {

			Pair<List<L>, Map<String, Object>> currentState = accumulatedStates.get(currentStateIndex);
			List<List<PGTransition<L, A>>> possibleTransitions = new ArrayList<>();

			for (int i = 0; i < cs.getProgramGraphs().size(); i++) {
				possibleTransitions.add(new ArrayList<PGTransition<L, A>>());
				Map<String, Object> eval = currentState.second;
				final int currentProgramGraphIndex = i;
				final Map<String, Object> currentEval = new HashMap<>(eval); 

				List<PGTransition<L, A>> relevantTransitions = cs.getProgramGraphs().get(i).getTransitions()
						.stream()
						.filter(t -> t.getFrom().equals(currentState.first.get(currentProgramGraphIndex)) &&
								conditionDefinition.evaluate(currentEval, t.getCondition()))
						.collect(Collectors.toList());
				for (PGTransition<L, A> transition : relevantTransitions) {
					if (interleavingActionDefinition.isOneSidedAction(transition.getAction().toString())) {
						possibleTransitions.get(i).add(transition);
						continue;
					} else {
						if (interleavingActionDefinition.isMatchingAction(transition.getAction())) {
							eval = interleavingActionDefinition.effect(eval, transition.getAction());
						} else {
							eval = actionDefinition.effect(eval, transition.getAction());
							if (eval == null) {
								possibleTransitions.get(i).add(transition);
								continue;
							}
						}
						List<L> currentLocation = new ArrayList<L>(currentState.first);
						currentLocation.set(i, transition.getTo());

						applyNewState(toRetTS, 
								currentState, 
								currentLocation,
								transition.getAction(), 
								accumulatedStates, 
								eval);
					}
				}
			}

			if (_debugFLAG)
			{
				System.out.println("in transitionSystemFromChannelSystem doin' iterate all possible transition "
						+ "combinations and find the combinations of actions that should happen in the same time ");

			}
			int i = 0, j;
			Iterator<List<PGTransition<L, A>>> it1 = possibleTransitions.listIterator();
			while (it1.hasNext()) {
				List<PGTransition<L, A>> firstIter = it1.next();
				j = i + 1;
				Iterator<List<PGTransition<L, A>>> it2 = possibleTransitions.listIterator(j);
				while (it2.hasNext()) {
					List<PGTransition<L, A>> secIter = it2.next();
					for (PGTransition<L, A> firstTransition : firstIter) {
						for (PGTransition<L, A> secondTransition : secIter) {
							String action = firstTransition.getAction() + "|" + secondTransition.getAction();
							Map<String, Object> eval = currentState.second;
							if (interleavingActionDefinition.isMatchingAction(action)) {
								eval = interleavingActionDefinition.effect(eval, action);

								if (eval != null) {
									List<L> currentLocation = new ArrayList<L>(currentState.first);
									currentLocation.set(i, firstTransition.getTo());
									currentLocation.set(j, secondTransition.getTo());

									applyNewState(toRetTS, 
											currentState, 
											currentLocation, 
											(A)action, 
											accumulatedStates, 
											eval);
								}
							}
						}
					}
				}
				++i;
			}
		}
		return toRetTS;
	}

	private <Sts, Saut, A, P> void generateProductInitialStates(TransitionSystem<Pair<Sts, Saut>, A, Saut> res, TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut)
	{
		Iterator<Sts> tsInitialStatesIt = ts.getInitialStates().iterator();
		while (tsInitialStatesIt.hasNext()){
			{
				Sts tsState = tsInitialStatesIt.next();
				Set<P> tsStateLabel = ts.getLabel(tsState);
				Iterator<Saut> automatonInitialStatesIt = aut.getInitialStates().iterator();
				while (automatonInitialStatesIt.hasNext())
				{
					Saut automatonState = automatonInitialStatesIt.next();
					if (aut.nextStates(automatonState, tsStateLabel) != null)
					{
						Iterator<Saut> nextAutomatonStatesIterator = aut.nextStates(automatonState, tsStateLabel).iterator();
						while (nextAutomatonStatesIterator.hasNext())
						{
							Saut nextAutomatonState = nextAutomatonStatesIterator.next();
							Pair<Sts, Saut> newInitialState = new Pair<>(tsState, nextAutomatonState);
							res.addState(newInitialState);
							res.addInitialState(newInitialState);
						}
					}
				}
			}
		}
	}

	// will add the state for future transition examinations if was not processed yet
	private <Sts, Saut, A> Pair<Sts,Saut> getNextState(TransitionSystem<Pair<Sts, Saut>, A, Saut> res, Saut destAut, Sts destTs, LinkedList<Pair<Sts,Saut>> states)
	{
		Iterator<Pair<Sts,Saut>> existingStatesIt = res.getStates().iterator();
		while (existingStatesIt.hasNext())
		{
			Pair<Sts, Saut> examinedState = existingStatesIt.next();
			if(examinedState.getFirst().equals(destTs) &&
					examinedState.getSecond().equals(destAut))
			{
				return examinedState;
			}
		}
		// the required state was not yet added to the product result states list, add it
		Pair<Sts,Saut> newlyCreatedState = new Pair<>(destTs,destAut);
		res.addState(newlyCreatedState);
		states.add(newlyCreatedState);
		return newlyCreatedState;
	}

	private <Sts, A, Saut> void applyLabeling(TransitionSystem<Pair<Sts, Saut>, A, Saut> res)
	{
		for(Pair<Sts,Saut> state : res.getStates()){
			Saut saut = state.getSecond();
			res.addAtomicProposition(saut);
			res.addToLabel(state, saut);
		}
	}

	/*no need for hw2*/
	@Override
	public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut)
	{
		TransitionSystem<Pair<Sts, Saut>, A, Saut> res = new TransitionSystemImpl();
		generateProductInitialStates(res, ts, aut);

		LinkedList<Pair<Sts,Saut>> states = new LinkedList<>(res.getInitialStates());
		while(states.size()>0){
			Pair<Sts,Saut> s = states.removeFirst();
			Sts currentTsState = s.getFirst();
			Saut currentAutomatonState = s.getSecond();
			for(Transition<Sts,A> transition : ts.getTransitions()){
				if(transition.getFrom().equals(currentTsState)){
					Sts tsDestState = transition.getTo();
					Set<P> tsDestStateLabel = ts.getLabel(tsDestState);
					A action = transition.getAction();
					if(aut.nextStates(currentAutomatonState, tsDestStateLabel) != null){
						Iterator<Saut> destAutomatonStateIt = aut.nextStates(currentAutomatonState, tsDestStateLabel).iterator();
						while (destAutomatonStateIt.hasNext())
						{
							Saut destAutomatonState = destAutomatonStateIt.next();
							Pair<Sts,Saut> destState = getNextState(res, destAutomatonState, tsDestState, states);
							res.addAction(action);
							Transition<Pair<Sts,Saut>,A> newlyCreatedTransition = new Transition<>(s, action, destState);
							res.addTransition(newlyCreatedTransition);
						}
					}
				}
			}
		}
		applyLabeling(res);
		return res;
	}

	@Override
	public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
		NanoPromelaParser.StmtContext root = NanoPromelaFileReader.pareseNanoPromelaFile(filename);
		return checkKindStmtPG(root);
	}

	@Override
	public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
		NanoPromelaParser.StmtContext root = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
		return checkKindStmtPG(root);
	}

	@Override
	public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
		NanoPromelaParser.StmtContext root = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
		return checkKindStmtPG(root);
	}

	private <S, Saut, A, P> Map<Pair<S,Saut>,List<S>> generateInvalidPaths(TransitionSystem<Pair<S, Saut>, A, Saut> product, Automaton<Saut, P> aut)
	{
		Map<Pair<S,Saut>,List<S>> accumulatedInvalidPaths = new HashMap<>();
		Set<Pair<S, Saut>> statesAlreadyInspected = new HashSet<>();
		Set<Pair<S,Saut>> initialStates = new HashSet<>(product.getInitialStates());
		Stack<Pair<S, Saut>> statesRequiringInspection = new Stack<>();
		List<S> prefix;
		while(!initialStates.isEmpty())
		{
			Pair<S,Saut> examinedInitialState = initialStates.iterator().next();
			statesRequiringInspection.push(examinedInitialState);
			statesAlreadyInspected.add(examinedInitialState);
			prefix  = new ArrayList<>();
			prefix.add(statesRequiringInspection.peek().getFirst());
			while(!statesRequiringInspection.isEmpty())
			{
				Pair<S, Saut> inspectedState = statesRequiringInspection.peek();
				Set<Pair<S, Saut>> postStates = post(product, inspectedState);
				List<Pair<S, Saut>> postStatesForInspection = postStates
						.stream()
						.filter(x -> !statesAlreadyInspected.contains(x))
						.collect(Collectors.toList());
				if(postStatesForInspection.size() == 0)
				{
					statesRequiringInspection.pop();
					if(aut.getAcceptingStates().contains(inspectedState.getSecond()))
					{
						if(!accumulatedInvalidPaths.containsKey(inspectedState))
						{
							accumulatedInvalidPaths.put(inspectedState, new ArrayList<>(prefix));
						}
					}
					if(prefix.size()>0)
						prefix.remove(prefix.size()-1);
				}
				else
				{
					Pair<S, Saut> stateForInspection = postStatesForInspection.get(0);
					prefix.add(stateForInspection.getFirst());
					statesRequiringInspection.push(stateForInspection);
					statesAlreadyInspected.add(stateForInspection);
				}
			}
			initialStates.removeAll(statesAlreadyInspected);
		}
		return accumulatedInvalidPaths;
	}

	@Override
	public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
		VerificationSucceeded success = new VerificationSucceeded();
		TransitionSystem<Pair<S, Saut>, A, Saut>  product = product(ts,aut);
		Map<Pair<S, Saut>,List<S>> invalidPaths = generateInvalidPaths(product, aut);

		List<S> cycle;
		Set<Pair<S, Saut>> states = invalidPaths.keySet();
		for(Pair<S,Saut> currentState : states){
			final Set<Pair<S, Saut>> statesAlreadyExamined = new HashSet<>();
			Stack<Pair<S, Saut>> statesRequiringInspection = new Stack<>();
			statesRequiringInspection.push(currentState);
			statesAlreadyExamined.add(currentState);
			cycle = new ArrayList<>();
			while(!statesRequiringInspection.isEmpty()){
				Pair<S, Saut> examinedState = statesRequiringInspection.peek();
				Set<Pair<S, Saut>> postStates = post(product, examinedState);
				if(postStates.contains(currentState)){
					cycle.add(currentState.getFirst());
					VerificationFailed<S> verificationFailure = new VerificationFailed<>();
					verificationFailure.setPrefix(invalidPaths.get(currentState));
					verificationFailure.setCycle(cycle);
					return verificationFailure;
				}
				else{
					List<Pair<S, Saut>> postStatesRequiringInspection = postStates
							.stream()
							.filter(x -> !statesAlreadyExamined.contains(x))
							.collect(Collectors.toList());
					if(postStatesRequiringInspection.isEmpty()){
						statesRequiringInspection.pop();
						if(cycle.size()>0){
							cycle.remove(cycle.size()-1);
						}
					}
					else{
						Pair<S, Saut> state = postStatesRequiringInspection.get(0);
						cycle.add(state.getFirst());
						statesRequiringInspection.push(state);
						statesAlreadyExamined.add(state);
					}
				}
			}
		}
		return success;
	}

	@Override
	public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
		Automaton<Set<String>, L> automaton = new Automaton<>();


		Set<LTL<L>> subFormulas = extractAllSubFormulas(ltl);
		ArrayList<Pair<LTL<L>, LTL<L>>> atomics = new ArrayList<>();
		for (LTL subFormula : subFormulas)
		{
			atomics.add(p(subFormula, LTL.not(subFormula)));
		}
		List<Set<LTL<L>>> allPossibleStates = generateAllPossibleStates(atomics);
		List<Set<LTL<L>>> formulas = filterInvalidStates(allPossibleStates);

		Map<LTL<L>, Integer> mapUntils = new HashMap<>();
		int colorNumber = 0;
		for (Pair<LTL<L>, LTL<L>> a : atomics) {
			if (a.getFirst() instanceof Until) {
				mapUntils.put(a.getFirst(), colorNumber);
				mapUntils.put(a.getSecond(), colorNumber);
				colorNumber++;
			}
		}

		// states

		for (Set<LTL<L>> formula : formulas) {
			Set<String> state = formula
							.stream()
							.map(ltlSet -> ltlSet.toString())
							.collect(Collectors.toSet());


			automaton.addState(state);

			if (mapUntils.size() > 0) {
				for (LTL<L> l : formula) {
					if (l instanceof Until && formula.contains(((Until) l).getRight())
							|| l instanceof Not && ((Not) l).getInner() instanceof Until) {
						automaton.setAccepting(state, mapUntils.get(l));
					}
				}

			} else {
				automaton.setAccepting(state);
			}

			if (formula.contains(ltl)) {
				automaton.setInitial(state);
			}
		}

		// transitions
		for (Set<LTL<L>> formula : formulas) {

			Set<String> state = formula
					.stream()
					.map(ltlSet -> ltlSet.toString())
					.collect(Collectors.toSet());


			Set<L> aps = new HashSet<>();
			List<LTL<L>> nextAP = new ArrayList<>();
			boolean stateWithUntil = false;

			for (LTL<L> l : formula) {
				if (!stateWithUntil && (l instanceof Until
						|| l instanceof Not && ((Not) l).getInner() instanceof Until)) {
					stateWithUntil = true;
				} else {
					if (l instanceof Next) {
						nextAP.add(((Next) l).getInner());
					} else if (l instanceof Not && ((Not) l).getInner() instanceof Next) {
						nextAP.add(LTL.not(((Next) (((Not) l).getInner())).getInner()));
					}
				}

				if (l instanceof AP) {
					aps.add((L) ((AP) l).getName());
				}
			}

			for (Set<LTL<L>> nextFormula : formulas) {

				boolean shouldAddTransition = true;
				for (LTL<L> l : nextAP) {
					if (!nextFormula.contains(l)) {
						shouldAddTransition = false;
						break;
					}
				}


				for (LTL<L> l : formula) {
					if (l instanceof Until) {
						if (!formula.contains(((Until) l).getRight())
								&& (!formula.contains(((Until) l).getLeft()) || !nextFormula.contains(l))) {
							shouldAddTransition = false;
							break;
						}
					} else if (l instanceof Not && ((Not) l).getInner() instanceof Until) {
						if (formula.contains(((Until) ((Not) l).getInner()).getRight())
								|| (formula.contains(((Until) ((Not) l).getInner()).getLeft()) && nextFormula.contains(((Not) l).getInner()))) {
							shouldAddTransition = false;
							break;
						}
					}


				}


				if (shouldAddTransition) {
					Set<String> nextFormulaString = nextFormula
							.stream()
							.map(ltlSet -> ltlSet.toString())
							.collect(Collectors.toSet());
					automaton.addTransition(state, aps, nextFormulaString);
				}
			}

		}

		return GNBA2NBA(automaton);
	}

	private <L> Set<LTL<L>> extractAllSubFormulas(LTL<L> ltl)
	{
		Set<LTL<L>> result = new HashSet<>();
		if (ltl instanceof And)
		{
			result.addAll(extractAllSubFormulas(((And) ltl).getLeft()));
			result.addAll(extractAllSubFormulas(((And) ltl).getRight()));
			result.add(ltl);
		}
		else if (ltl instanceof Until)
		{
			result.addAll(extractAllSubFormulas(((Until) ltl).getLeft()));
			result.addAll(extractAllSubFormulas(((Until) ltl).getRight()));
			result.add(ltl);
		}
		else if (ltl instanceof Not)
		{//not will be added later as the negative form
			result.addAll(extractAllSubFormulas(((Not) ltl).getInner()));
		}
		else if (ltl instanceof Next)
		{
			result.addAll(extractAllSubFormulas(((Next) ltl).getInner()));
			result.add(ltl);
		}
		else
		{//atomic formula
			result.add(ltl);
		}
		return result;
	}

	private <L> List<Set<LTL<L>>> generateAllPossibleStates(ArrayList<Pair<LTL<L>, LTL<L>>> atomics)
	{
		List<Set<LTL<L>>> result = new ArrayList<>();
		for (Pair<LTL<L>, LTL<L>> ltlPair : atomics)
		{
			if (result.size() == 0)
			{
				Set<LTL<L>> stateSet = new HashSet<>();
				stateSet.add(atomics.get(0).getFirst());
				result.add(stateSet);
				stateSet = new HashSet<>();
				stateSet.add(atomics.get(0).getSecond());
				result.add(stateSet);
			}
			else
			{
				int originalSize = result.size();
				for (int i = 0; i < originalSize; i++)
				{
					Set<LTL<L>> newState = new HashSet<>(result.get(i));
					result.add(newState);
				}
				for (int i = 0; i < result.size() / 2; i++)
				{
					result.get(i).add(ltlPair.getFirst());
				}
				for (int i = result.size() / 2; i < result.size(); i++)
				{
					result.get(i).add(ltlPair.getSecond());
				}
			}
		}
		return result;
	}

	private <L> List<Set<LTL<L>>> filterInvalidStates(List<Set<LTL<L>>> allPossibleStates)
	{
		List<Set<LTL<L>>> result = new ArrayList<>(allPossibleStates);
		for (Set<LTL<L>> state : allPossibleStates)
		{
			for (LTL<L> ltl : state)
			{
				if (ltl instanceof And)
				{
					if (!(state.contains(((And) ltl).getLeft()) && state.contains(((And) ltl).getRight())))
					{
						result.remove(state);
					}
				}
				else if (ltl.equals(LTL.not(new TRUE<>())))
				{
					result.remove(state);
				}
				else if (ltl instanceof Until)
				{
					if (!state.contains(((Until) ltl).getRight()) &&
							!state.contains(((Until) ltl).getLeft()))
					{
						result.remove(state);
					}
				}
			}
		}
		return result;
	}

	@Override
	public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
		Automaton<Pair<Integer, Integer>, L> automaton = new Automaton<>();

		List<Integer> colors = new ArrayList<>(mulAut.getColors());

		Map<Object, Integer> stateMap = new HashMap<>();
		{
			int stateNumber = 0;
			for (Map.Entry state : mulAut.getTransitions().entrySet()) {
				stateMap.put(state.getKey(), stateNumber);
				stateNumber++;
			}
		}

		// Initials
		for (Object state : mulAut.getInitialStates()) {
			automaton.setInitial(p(stateMap.get(state), colors.get(0)));
		}

		// States
		for (int i = 0; i < colors.size(); i++) {
			Integer color = colors.get(i);

			for (Map.Entry state : mulAut.getTransitions().entrySet()) {
				automaton.addState(p(stateMap.get(state.getKey()), color));
			}
		}

		// Accepting
		for (Object state : mulAut.getAcceptingStates(colors.get(0))) {
			automaton.setAccepting(p(stateMap.get(state), colors.get(0)));
		}


		for (int i = 0; i < colors.size(); i++) {
			Integer color = colors.get(i);

			List acceptingStates = new ArrayList(mulAut.getAcceptingStates(color));

			for (Map.Entry state : mulAut.getTransitions().entrySet()) {

				Integer nextColor = color;
				if (acceptingStates.contains(state.getKey())) {
					nextColor = colors.get((i + 1) % colors.size());
				}


				for (Map.Entry transition : ((Map<Set<L>, String>) state.getValue()).entrySet()) {
					for (Object toState : (Set) transition.getValue()) {
						automaton.addTransition(p(stateMap.get(state.getKey()), color), (Set<L>) transition.getKey(), p(stateMap.get(toState), nextColor));
					}
				}
			}
		}


		return automaton;
	}

	// returns the states in I that are not in R
}