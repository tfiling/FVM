package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static il.ac.bgu.cs.fvm.exceptions.TransitionSystemPart.*;


public class TransitionSystemImpl<STATE ,ACTION ,ATOMIC_PROPOSITION> implements TransitionSystem<STATE ,ACTION ,ATOMIC_PROPOSITION> {

	private String name;

	private Set<STATE> initialStates;// I

	private Set<STATE> states;// S

	private Map<STATE, Set<ATOMIC_PROPOSITION>> labelingFunction;// L

	private Set<ACTION> actions;// Act

	private Set<Transition<STATE,ACTION>> transitions;// -> 

	private Set<ATOMIC_PROPOSITION> atomicPropositions;// AP

	public TransitionSystemImpl() {

		this.initialStates = new HashSet<STATE>();
		this.states = new HashSet<STATE>();
		this.labelingFunction = new HashMap<STATE, Set<ATOMIC_PROPOSITION>>();
		this.actions = new HashSet<ACTION>();
		this.transitions = new HashSet<Transition<STATE,ACTION>>();
		this.atomicPropositions = new HashSet<ATOMIC_PROPOSITION>();
	}

	public TransitionSystemImpl(TransitionSystemImpl<STATE, ACTION, ATOMIC_PROPOSITION> other) {

		this.name = other.name;
		this.initialStates = new HashSet<STATE>(other.initialStates);
		this.states = new HashSet<STATE>(other.states);
		this.labelingFunction = new HashMap<STATE, Set<ATOMIC_PROPOSITION>>();
		for (STATE state : other.labelingFunction.keySet()) {
			Set<ATOMIC_PROPOSITION> otherAPsForState = other.labelingFunction.get(state);
			this.labelingFunction.put(state, new HashSet<ATOMIC_PROPOSITION>(otherAPsForState));
		}
		this.actions = new HashSet<ACTION>(other.actions);
		this.transitions = new HashSet<>(other.transitions);
		this.atomicPropositions = new HashSet<ATOMIC_PROPOSITION>(other.atomicPropositions);
	}

	@Override
	public String getName() {
		return this.name;
	}

	@Override
	public void setName(String name) {
		this.name = name;
	}

	public void addAction(ACTION action) {
		this.actions.add(action);
	}

	@Override
	public void addInitialState(STATE initialState) throws FVMException {
		if (!this.states.contains(initialState)) {
			throw new InvalidInitialStateException(initialState);
		}
		this.initialStates.add(initialState);
	}

	@Override
	public void addState(STATE state) {
		this.states.add(state);
	}

	@Override
	public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
		boolean fromExists = this.states.contains(t.getFrom());
		boolean toExists = this.states.contains(t.getTo());
		boolean actionExists = this.actions.contains(t.getAction());

		if (!fromExists || !toExists || !actionExists) {
			throw new InvalidTransitionException(t);
		}
		this.transitions.add(t);
	}

	@Override
	public Set<ACTION> getActions() {
		return this.actions;
	}

	@Override
	public void addAtomicProposition(ATOMIC_PROPOSITION p) {
		this.atomicPropositions.add(p);
	}

	@Override
	public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
		return this.atomicPropositions;
	}

	@Override
	public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
		boolean stateExists = this.states.contains(s);
		boolean isAtomicProp = this.atomicPropositions.contains(l);

		if (!stateExists) {
			throw new InvalidLablingPairException(s, l);
		} 
		if (!isAtomicProp) {
			throw new InvalidLablingPairException(s, l);
		}
		Set<ATOMIC_PROPOSITION> labelsOfState = this.labelingFunction.containsKey(s) ? this.labelingFunction.get(s) : new HashSet<ATOMIC_PROPOSITION>(); 
		labelsOfState.add(l);
		this.labelingFunction.put(s, labelsOfState);
	}

	@Override
	public Set<ATOMIC_PROPOSITION> getLabel(Object s) {
		if (!this.states.contains(s)) {
			throw new StateNotFoundException(s);
		}

		return this.labelingFunction.containsKey(s) ? this.labelingFunction.get(s) : new HashSet<ATOMIC_PROPOSITION>();
	}

	@Override
	public Set<STATE> getInitialStates() {
		return this.initialStates;
	}

	@Override
	public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
		return this.labelingFunction;
	}

	@Override
	public Set<STATE> getStates() {
		return this.states;
	}

	@Override
	public Set<Transition<STATE,ACTION>> getTransitions() {
		return this.transitions;
	}

	@Override
	public void removeAction(ACTION action) throws FVMException {
		for(Transition<STATE, ACTION> transition : this.transitions) {
			// make sure the deleted action is not part of any transition
			if (transition.getAction().equals(action)) {
				throw new DeletionOfAttachedActionException(action, TRANSITIONS);
			}

			this.actions.remove(action);
		}
	}



	@Override
	public void removeAtomicProposition(ATOMIC_PROPOSITION ap) throws FVMException {
		for(Set<ATOMIC_PROPOSITION> labels : this.labelingFunction.values()) {
			// make sure the deleted AP is not used to label existing state
			if (labels.contains(ap)) {
				throw new DeletionOfAttachedAtomicPropositionException(ap, STATES);
			}
		}

		this.atomicPropositions.remove(ap);
	}


	@Override
	public void removeInitialState(STATE initialState) {
		this.initialStates.remove(initialState);
	}

	@Override
	public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
		if (this.labelingFunction.containsKey(s))
		{
			this.labelingFunction.get(s).remove(l);
		}
	}
	
	@Override
	public void removeState(STATE state) throws FVMException {
		
		//make sure the state does not take part in any transition
		for(Transition<STATE, ACTION> transition : this.transitions) {
			if (transition.getFrom().equals(state) || transition.getTo().equals(state)) {
				throw new DeletionOfAttachedStateException(state, TRANSITIONS);
			}
		}
		
		//make sure the state is not labeled
		Set<ATOMIC_PROPOSITION> labels = this.labelingFunction.get(state);
		if (labels != null && !labels.isEmpty()) {
			throw new DeletionOfAttachedStateException(state, LABELING_FUNCTION);
		}

		// make the state is not an initial state 
		if (this.initialStates.contains(state))
		{
			throw new DeletionOfAttachedStateException(state, INITIAL_STATES);
		}
		
		this.states.remove(state);
	}

	@Override
	public void removeTransition(Transition t) {
		this.transitions.remove(t);
	}
}
