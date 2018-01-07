package il.ac.bgu.cs.fvm.impl;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import static java.util.Arrays.asList;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;

public class MutualExclusionDemo {

	public static void main(String[] args) {

		try {
			Peterson.PetersonA();
			Peterson.PetersonB();
			Peterson.PetersonC();
			verifySemaphore();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}
	
	
	private static void verifySemaphore() throws Exception{
		System.out.println("verify semaphore");
		FvmFacade fvmFacadeImpl = FvmFacade.createInstance();
		ProgramGraph<String, String> pg1 = build(1);
		ProgramGraph<String, String> pg2 = build(2);

		ProgramGraph<Pair<String, String>, String> pg = fvmFacadeImpl.interleave(pg1, pg2);

		Set<ActionDef> ad = set(new ParserBasedActDef());
		Set<ConditionDef> cd = set(new ParserBasedCondDef());

		TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts;
		ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, ad, cd);

		Peterson.addLabels(ts);
		Peterson.checkAndVerifyTS(ts);
	}
	
	public static ProgramGraph<String, String> build(int id) {
        ProgramGraph<String, String> pg = FvmFacade.createInstance().createProgramGraph();

        String noncrit = "noncrit" + id;
        String wait = "wait" + id;
        String crit = "crit" + id;

        pg.addLocation(noncrit);
        pg.addLocation(wait);
        pg.addLocation(crit);

        pg.addInitialLocation(noncrit);

        pg.addTransition(new PGTransition<>(noncrit, "true", "", wait));
        pg.addTransition(new PGTransition<>(wait, "y>0", "y:=y-1", crit));
        pg.addTransition(new PGTransition<>(crit, "true", "y:=y+1", noncrit));

        pg.addInitalization(asList("y:=1"));

        return pg;

    }
	
	
	
}
