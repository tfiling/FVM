package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.*;

/**
 * Created by Nir on 12/14/16.
 */
public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {


    private Set<List<String>> mInitializations;
    private Map<String, Object> mInitialEval;
    private Set<L> mInitialLocations, mLocations;
    private Set<PGTransition<L, A>> mTransitions;
    private String mName;


    public ProgramGraphImpl() {
        mInitializations = new HashSet<>();
        mInitialEval = new LinkedHashMap<String, Object>();
        mInitialLocations = new HashSet<L>();
        mLocations = new HashSet<L>();
        mTransitions = new HashSet<>();
    }

    @Override
    public void addInitalization(List<String> init) {
        mInitializations.add(init);
    }

    @Override
    public void addInitialLocation(L location) {
        mInitialLocations.add(location);
    }

    @Override
    public void addLocation(L l) {
        mLocations.add(l);
    }

    @Override
    public void addTransition(PGTransition<L, A> t) {
        mTransitions.add(t);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return mInitializations;
    }

    @Override
    public Set<L> getInitialLocations() {
        return mInitialLocations;
    }

    @Override
    public Set<L> getLocations() {
        return mLocations;
    }

    @Override
    public String getName() {
        return mName;
    }

    @Override
    public Set<PGTransition<L, A>> getTransitions() {
        return mTransitions;
    }

    @Override
    public void removeLocation(L l) {
        mLocations.remove(l);
    }

    @Override
    public void removeTransition(PGTransition<L, A> t) {
        mTransitions.remove(t);
    }

    @Override
    public void setName(String name) {
        mName = name;
    }
}
