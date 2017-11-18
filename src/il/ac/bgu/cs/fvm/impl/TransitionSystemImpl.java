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

    private Set<STATE> initialStates;
    private Set<STATE> states;
    private Map<STATE, Set<ATOMIC_PROPOSITION>> labelingFunction;

    private Set<ACTION> actions;

    private Set<Transition<STATE,ACTION>> transitions;

    private Set<ATOMIC_PROPOSITION> atomicPropositions;

    public TransitionSystemImpl() {
        this.initialStates = new HashSet<STATE>();
        this.states = new HashSet<STATE>();
        this.labelingFunction = new HashMap<STATE, Set<ATOMIC_PROPOSITION>>();

        this.actions = new HashSet<ACTION>();

        this.transitions = new HashSet<Transition<STATE,ACTION>>();

        this.atomicPropositions = new HashSet<ATOMIC_PROPOSITION>();
    }

    public TransitionSystemImpl(TransitionSystemImpl other) {
        this.name = other.name;

        this.initialStates = new HashSet<STATE>(other.initialStates);
        this.states = new HashSet<STATE>(other.states);

        this.labelingFunction = new HashMap<STATE, Set<ATOMIC_PROPOSITION>>();
        for (STATE state : ((Map<STATE, Set<ATOMIC_PROPOSITION>>)other.labelingFunction).keySet()) {
            Set<ATOMIC_PROPOSITION> otherAPsForState = (Set<ATOMIC_PROPOSITION>)other.labelingFunction.get(state);
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
        if (this.states.contains(initialState)) {
            this.initialStates.add(initialState);
        } else {
            throw new InvalidInitialStateException(initialState);
        }
    }

    @Override
    public void addState(STATE state) {
        this.states.add(state);
    }

    @Override
    public void addTransition(Transition t) throws FVMException {
        boolean fromExists = this.states.contains(t.getFrom());
        boolean toExists = this.states.contains(t.getTo());
        boolean actionExists = this.actions.contains(t.getAction());

        if (!fromExists || !toExists || !actionExists) {
            throw new InvalidTransitionException(t);
        } else {
            this.transitions.add(t);
        }
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
        } else if (!isAtomicProp) {
            throw new InvalidLablingPairException(s, l);
        } else {
            Set<ATOMIC_PROPOSITION> labelsForState = this.labelingFunction.getOrDefault(s, new HashSet<ATOMIC_PROPOSITION>());
            labelsForState.add(l);
            this.labelingFunction.put(s, labelsForState);
        }
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getLabel(Object s) {
        if (!this.states.contains(s)) {
            throw new StateNotFoundException(s);
        }

        return this.labelingFunction.getOrDefault(s, new HashSet<ATOMIC_PROPOSITION>());
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
        boolean actionIsInUseByTransition = this.actionIsInUseByATransition(action);

        if (actionIsInUseByTransition) {
            throw new DeletionOfAttachedActionException(action, TRANSITIONS);
        } else {
            this.actions.remove(action);
        }
    }

    private boolean actionIsInUseByATransition (ACTION action) {
        boolean isInUse = false;

        for(Transition<STATE, ACTION> t : this.transitions) {
            if (t.getAction().equals(action)) {
                isInUse = true;
            }
        }

        return isInUse;
    }

    @Override
    public void removeAtomicProposition(ATOMIC_PROPOSITION ap) throws FVMException {
        boolean atomicPropositionIsUsedAsLabelOnAState = this.atomicPropositionIsUsedAsLabelOnAState(ap);

        if (atomicPropositionIsUsedAsLabelOnAState) {
            throw new DeletionOfAttachedAtomicPropositionException(ap, STATES);
        } else {
            this.atomicPropositions.remove(ap);
        }
    }

    private boolean atomicPropositionIsUsedAsLabelOnAState (ATOMIC_PROPOSITION ap) {

        for(Set<ATOMIC_PROPOSITION> labels : this.labelingFunction.values()) {
            if (labels.contains(ap)) {
                return true;
            }
        }

        return false;
    }

    @Override
    public void removeInitialState(STATE initialState) {
        this.initialStates.remove(initialState);
    }

    @Override
    public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
        Set<ATOMIC_PROPOSITION> labelsForState = this.labelingFunction.getOrDefault(s, new HashSet<ATOMIC_PROPOSITION>());
        labelsForState.remove(l);
    }

    @Override
    public void removeState(STATE state) throws FVMException {
        boolean stateInUseByTransition = this.stateInUseByATransition(state);
        boolean stateIsLabeled = this.stateIsLabeled(state);
        boolean stateIsInitial = this.initialStates.contains(state);

        if (stateInUseByTransition) {
            throw new DeletionOfAttachedStateException(state, TRANSITIONS);
        } else if (stateIsLabeled) {
            throw new DeletionOfAttachedStateException(state, LABELING_FUNCTION);
        } else if (stateIsInitial) {
            throw new DeletionOfAttachedStateException(state, INITIAL_STATES);
        } else {
            this.states.remove(state);
        }
    }

    private boolean stateInUseByATransition(STATE state) {
        boolean isInUse = false;

        for(Transition<STATE, ACTION> transition : this.transitions) {
            if (transition.getFrom().equals(state) || transition.getTo().equals(state)) {
                isInUse = true;
            }
        }

        return isInUse;
    }

    private boolean stateIsLabeled(STATE state) {
        Set<ATOMIC_PROPOSITION> labels = this.labelingFunction.get(state);
        if (labels == null) {
            return false;
        }
        if (labels.isEmpty()) {
            return false;
        }
        return true;
    }

    @Override
    public void removeTransition(Transition t) {
        this.transitions.remove(t);
    }
}
