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

	public static String petersonP1 =
			"do :: true -> \n"
					+ "    atomic {b1:=1 ; x:=2};\n"
					+ "    if :: (x==1) || (b2==0) -> crit1:=1 fi; \n"
					+ "    atomic { crit1:= 0 ; b1:=0}\n"
					+ "od";

	public static String petersonP2 =
			"do :: true -> \n"
					+ "    atomic{b2:=1 ; x:=1};\n"
					+ "    if :: (x==2) || (b1==0) -> crit2:=1 fi; \n"
					+ "    atomic {crit2:= 0 ; b2:=0}\n"
					+ "od";


	public static void main(String[] args) throws Exception
	{
		System.out.println("We decided to test the peterson algorithm version, described in nano promela," +
				"in slide #8, in the 8th lecture presentation");
		System.out.println("nano promela description of the algorithm for process #1");
		System.out.println(petersonP1);
		System.out.println("---------------------------------------------------------------");
		System.out.println("nano promela description of the algorithm for process #2");
		System.out.println(petersonP2);

		//create a fvm
		FvmFacade fvmImpl = FvmFacade.createInstance();

		//create 2 PG and then intreleave them
		ProgramGraph<String, String> pg1 = fvmImpl.programGraphFromNanoPromelaString(petersonP1);
		ProgramGraph<String, String> pg2 = fvmImpl.programGraphFromNanoPromelaString(petersonP2);
		ProgramGraph<Pair<String,String>, String> pg = fvmImpl.interleave(pg1, pg2);


		Set<ActionDef> actDef = set(new ParserBasedActDef());
		Set<ConditionDef> condDef = set(new ParserBasedCondDef());
		TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts = fvmImpl.transitionSystemFromProgramGraph(pg, actDef, condDef);

		Peterson.analyzeAlgorithm(ts);
	}
	
}
