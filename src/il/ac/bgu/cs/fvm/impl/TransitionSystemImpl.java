package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

import java.util.*;

/**
 * Created by Nir on 11/28/16.
 */
public class TransitionSystemImpl<S, A, P> implements TransitionSystem<S, A, P> {

    private String mName;

    private Set<S> mStates, mInitialStates;

    private Set<Transition<S, A>> mTransitions;

    private Set<A> mActions;

    private Set<P> mAtomicPropositions;

    private HashMap<S, Set<P>> mLabels;


    public TransitionSystemImpl() {
        mStates = new HashSet<>();
        mInitialStates = new HashSet<>();
        mTransitions = new HashSet<>();
        mActions = new HashSet<>();
        mAtomicPropositions = new HashSet<>();
        mLabels = new LinkedHashMap<>();
    }

    @Override
    public String getName() {
        return mName;
    }

    @Override
    public void setName(String name) {
        mName = name;
    }

    @Override
    public void addAction(A a) {
        mActions.add(a);
    }

    @Override
    public void addInitialState(S s) throws FVMException {
        if (mStates.contains(s)) {
            mInitialStates.add(s);
        } else {
            throw new InvalidInitialStateException(s);
        }
    }

    @Override
    public void addState(S s) {
        if (!mStates.contains(s)) {
            mStates.add(s);
        }
    }

    @Override
    public void addTransition(Transition<S, A> t) throws FVMException {
        if (mStates.contains(t.getFrom()) && mStates.contains(t.getTo()) && mActions.contains(t.getAction())) {
            mTransitions.add(t);
        } else {
            throw new InvalidTransitionException(t);
        }
    }

    @Override
    public Set<A> getActions() {
        return mActions;
    }

    @Override
    public void addAtomicProposition(P p) {
        if (!mAtomicPropositions.contains(p)) {
            mAtomicPropositions.add(p);
        }
    }

    @Override
    public Set<P> getAtomicPropositions() {
        return mAtomicPropositions;
    }

    @Override
    public void addToLabel(S s, P l) throws FVMException {
        if (mStates.contains(s) && mAtomicPropositions.contains(l)) {
            if (!mLabels.containsKey(s)) {
                mLabels.put(s, new HashSet<P>());
            }

            if (!mLabels.get(s).contains(l)) {
                mLabels.get(s).add(l);
            }

        } else {
            throw new InvalidLablingPairException(s, l);
        }
    }

    @Override
    public Set<P> getLabel(S s) {
        if (mStates.contains(s)) {
            return mLabels.containsKey(s) ? mLabels.get(s) : new HashSet<>();
        } else {
            throw new StateNotFoundException(s);
        }
    }

    @Override
    public Set<S> getInitialStates() {
        return mInitialStates;
    }

    @Override
    public Map<S, Set<P>> getLabelingFunction() {
        return mLabels;
    }

    @Override
    public Set<S> getStates() {
        return mStates;
    }

    @Override
    public Set<Transition<S, A>> getTransitions() {
        return mTransitions;
    }

    @Override
    public void removeAction(A a) throws FVMException {
        Iterator<Transition<S, A>> iterator = mTransitions.iterator();
        while (iterator.hasNext()) {
            Transition transition = iterator.next();
            if (transition.getAction().equals(a)) {
                throw new DeletionOfAttachedActionException(a, TransitionSystemPart.ACTIONS);
            }
        }

        mActions.remove(a);
    }

    @Override
    public void removeAtomicProposition(P p) throws FVMException {
        for (Map.Entry<S, Set<P>> label : mLabels.entrySet()) {
            if (label.getValue().contains(p)) {
                throw new DeletionOfAttachedAtomicPropositionException(p, TransitionSystemPart.ATOMIC_PROPOSITIONS);
            }
        }
        mAtomicPropositions.remove(p);
    }

    @Override
    public void removeInitialState(S s) {
        mInitialStates.remove(s);
    }

    @Override
    public void removeLabel(S s, P l) {
        if (mLabels.containsKey(s)) {
            mLabels.get(s).remove(l);
            if (mLabels.get(s).size() == 0) {
                mLabels.remove(s);
            }
        }
    }

    @Override
    public void removeState(S s) throws FVMException {
        Iterator<Transition<S, A>> iterator = mTransitions.iterator();
        while (iterator.hasNext()) {
            Transition transition = iterator.next();
            if (transition.getFrom().equals(s) || transition.getTo().equals(s)) {
                throw new DeletionOfAttachedStateException(s, TransitionSystemPart.STATES);
            }
        }

        if (!mLabels.containsKey(s) && !mInitialStates.contains(s)) {
            mStates.remove(s);
        } else {
            throw new DeletionOfAttachedStateException(s, TransitionSystemPart.STATES);
        }
    }

    @Override
    public void removeTransition(Transition<S, A> t) {
        mTransitions.remove(t);
    }
}
