package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {

    private String name;

    private Set<L> initialLocations;
    private Set<L> locations;
    private Set<PGTransition<L, A>> transitions;
    private Set<List<String>> initalizations;

    public ProgramGraphImpl() {
        this.initialLocations = new HashSet<L>();
        this.locations = new HashSet<L>();
        this.transitions = new HashSet<PGTransition<L, A>>();
        this.initalizations = new HashSet<List<String>>();
    }

    @Override
    public void addInitalization(List<String> init) {
        this.initalizations.add(init);
    }

    @Override
    public void addInitialLocation(L location) {
        if (this.locations.contains(location)) {
            this.initialLocations.add(location);
        } else {
            throw new RuntimeException(); //TODO
        }
    }

    @Override
    public void addLocation(L location) {
        this.locations.add(location);
    }

    @Override
    public void addTransition(PGTransition<L, A> transition) {
        this.transitions.add(transition);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return this.initalizations;
    }

    @Override
    public Set<L> getInitialLocations() {
        return this.initialLocations;
    }

    @Override
    public Set<L> getLocations() {
        return this.locations;
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public Set<PGTransition<L, A>> getTransitions() {
        return this.transitions;
    }

    @Override
    public void removeLocation(L location) {
        if (this.locations.contains(location)) {
            this.locations.remove(location);
        } else {
            throw new RuntimeException(); //TODO
        }
    }

    @Override
    public void removeTransition(PGTransition<L,A> transition) {
        if (this.transitions.contains(transition)) {
            this.transitions.remove(transition);
        } else {
            throw new RuntimeException(); //TODO
        }
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }
}
