package il.ac.bgu.cs.fvm.impl;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;

public class Peterson {

	public static FvmFacade fvmFacade = FvmFacade.createInstance();

	public static void analyzeAlgorithm(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts)
	{
		filterUnwantedLabels(ts);
		analyzeMutualExclusion(ts);
		analyzeStarvationFreedom(ts);

	}

	public static void filterUnwantedLabels(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
		List<Pair<Pair<String, String>, Map<String, Object>>>  allStates = new ArrayList<>(ts.getStates());

		System.out.println("filtering labels, keeping only labels related to variables x, b1, b2");
		for(int i = 0 ; i<allStates.size();i++){
			Set<String> label = new HashSet<>(ts.getLabel(allStates.get(i)));
			Iterator<String> iterator = label.iterator();

			while(iterator.hasNext())
			{
				String labelElement = iterator.next();
				if(labelElement.startsWith("<") || labelElement.endsWith("0"))
				{
					ts.removeLabel(allStates.get(i), labelElement);
				}
			}
		}
	}

	public static Automaton<String, String> createAutoMutualExclusion(){

		Automaton<String, String> auto = new Automaton<>();

		auto.setInitial("q0");
		auto.setAccepting("q1");
		
		for(int i = 0; i < 2 ;i++){
			for(int j = 0; j < 2 ; j++){
				for(int k = 0; k < 2; k++)	{
					for(int l = 0; l < 2 ; l++){
						for(int m = 0; m <= 2; m++)	{ // x in {0, 1, 2}
							Set<String> transitionLabels = new HashSet<>();
							transitionLabels.add("crit1 = " + i);
							transitionLabels.add("crit2 = " + j);
							transitionLabels.add("b1 = " + k);
							transitionLabels.add("b2 = " + l);
							transitionLabels.add("x = " + m);
							// remove labels of variables == 0 since ignored in the TS labels
							transitionLabels.removeIf(label -> label.endsWith("0"));
							auto.addTransition("q0", transitionLabels, "q0");
							auto.addTransition("q1", transitionLabels, "q1");
							if (transitionLabels.contains("crit1 = 1") && transitionLabels.contains("crit2 = 1"))
							{// both processes are in the critical section -> apply transition to the accepting state of the automaton
								auto.addTransition("q0", transitionLabels, "q1");
							}
						}
					}
				}
			}
		}
		return auto;
	}

	private static void analyzeMutualExclusion(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts)
	{
		VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> verificationRes = fvmFacade.verifyAnOmegaRegularProperty(ts, createAutoMutualExclusion());

		if(verificationRes instanceof VerificationSucceeded){
			System.out.println("the analyzed algorithm holds mutual exclusion");
		}
		else if(verificationRes instanceof VerificationFailed){
			System.out.println("the analyzed algorithm DOES NOT hold mutual exclusion");
			System.out.println("a possible scenario leading both processes in the critical section in the same time:");
			System.out.println(verificationRes);
		}

	}

	public static void analyzeStarvationFreedom(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {

		VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> verificationRes2 = fvmFacade.verifyAnOmegaRegularProperty(ts, createAutoStarvation(1));
		if(verificationRes2 instanceof VerificationSucceeded){
			System.out.println("The is starvation freedom property - P1 . YES BABY!!! ");
		}else if(verificationRes2 instanceof VerificationFailed){
			System.out.println("Its not a starvation for P1!! \n for example:");
			System.out.println(verificationRes2);
		}

		VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> verificationRes3 = fvmFacade.verifyAnOmegaRegularProperty(ts, createAutoStarvation(2));
		if(verificationRes3 instanceof VerificationSucceeded){
			System.out.println("The is starvation freedom property - P2 . YES BABY!!!");
		}else if(verificationRes3 instanceof VerificationFailed){
			System.out.println("Its not a starvation for P2!! \n for example:");
			System.out.println(verificationRes3);
		}

	}


	public static Automaton<String, String> createAutoStarvation(int processID) {

		Automaton<String, String> auto = new Automaton<>();
		auto.setInitial("q0"); // initial state
		auto.setAccepting("q1"); // p1 waits for the critical section
		auto.addState("q2"); // p1 entered the critical section

		for(int i = 0 ; i<2 ;i++){
			for(int j=0 ; j<2 ; j++){
				for(int k=0;k<2;k++){
					for(int l=0;l<2;l++){
						Set<String> transitionLabels = new HashSet<>();
						if(!(i==1 && k==0)){
							transitionLabels.add("crit1 = " + i);
							transitionLabels.add("crit2 = " + j);
							transitionLabels.add("b1 = " + k);
							transitionLabels.add("b2 = " + l);

							transitionLabels.removeIf(label -> label.endsWith("0"));

							if (transitionLabels.contains(String.format("b%d = 1", processID)) && !transitionLabels.contains(String.format("crit%d = 1", processID)))
							{//the transition is made when pi waits for the critical section but still didn't get into the critical section
								auto.addTransition("q0", transitionLabels, "q1");
							}
							if (transitionLabels.contains(String.format("crit%d = 1", processID)))
							{//pi entered the critical section hence has not starvation, move from the accepting state to the non accepting state
								auto.addTransition("q1", transitionLabels, "q2");
							}
							auto.addTransition("q2",transitionLabels, "q2");
						}
					}
				}
			}
		}
		return auto;
	}

}
