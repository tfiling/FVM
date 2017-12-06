package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.*;


public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {

    private String _PgName;
    private Set<List<String>> _PgInitialize;
    private Set<L> _PgInitLocs, _PgAllLocs;
    private Set<PGTransition<L, A>> _PgAllTS;



    public ProgramGraphImpl() {
        _PgInitialize = new HashSet<>();
        _PgInitLocs = new HashSet<L>();
        _PgAllLocs = new HashSet<L>();
        _PgAllTS = new HashSet<>();
    }

    @Override
    public void addInitalization(List<String> init) {
        _PgInitialize.add(init);
    }

    @Override
    public void addInitialLocation(L location) {
        _PgInitLocs.add(location);
    }

    @Override
    public void addLocation(L l) {
        _PgAllLocs.add(l);
    }

    @Override
    public void addTransition(PGTransition<L, A> t) {
        _PgAllTS.add(t);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return _PgInitialize;
    }

    @Override
    public Set<L> getInitialLocations() {
        return _PgInitLocs;
    }

    @Override
    public Set<L> getLocations() {
    	if (_PgInitLocs.size() > 0)
    	{
    		for (L loc : _PgInitLocs)
    		_PgAllLocs.add(loc);
    	}
        return _PgAllLocs;
    }

    @Override
    public String getName() {
        return _PgName;
    }

    @Override
    public Set<PGTransition<L, A>> getTransitions() {
        return _PgAllTS;
    }

    @Override
    public void removeLocation(L l) {
        _PgAllLocs.remove(l);
    }

    @Override
    public void removeTransition(PGTransition<L, A> t) {
        _PgAllTS.remove(t);
    }

    @Override
    public void setName(String name) {
        _PgName = name;
    }
}
