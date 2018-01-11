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

	/**
	 *	analyzes mutual exclusion and starvation freedom for the algorithm represented by the transition system
	 * @param ts the transition system representing the algorithm implementation
	 */
	public static void analyzeAlgorithm(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts)
	{
		filterUnwantedLabels(ts);
		analyzeMutualExclusion(ts);
		analyzeStarvationFreedom(ts);

	}

	/**
	 * filter labels that dont influence the analyzed features
	 * @param ts the transition system representing the algorithm implementation
	 */
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

	/**
	 *
	 * @return an automaton that accepts if both processes were in the critical section in the same time
	 */
	public static Automaton<String, String> createAutoMutualExclusion(){

		System.out.println("creating an automaton that will accept when both processes are in the critical section");
		Automaton<String, String> automaton = new Automaton<>();

		System.out.println("q0 is the initial non accepting where up to one process is in the critical section");
		automaton.setInitial("q0");
		System.out.println("q1 is the accepting state where both processes are in the critical section");
		automaton.setAccepting("q1");

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
							automaton.addTransition("q0", transitionLabels, "q0");
							automaton.addTransition("q1", transitionLabels, "q1");
							if (transitionLabels.contains("crit1 = 1") && transitionLabels.contains("crit2 = 1"))
							{// both processes are in the critical section -> apply transition to the accepting state of the automaton
								automaton.addTransition("q0", transitionLabels, "q1");
							}
						}
					}
				}
			}
		}
		return automaton;
	}


	/**
	 * analyze the algorithm for mutual exclusion
	 * @param ts the transition system representing the algorithm implementation
	 */
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
		System.out.println("\n------------------------------------------------------------\n");

	}

	/**
	 * analyze the algorithm for starvation freedom for both processes
	 * @param ts the transition system representing the algorithm implementation
	 */
	public static void analyzeStarvationFreedom(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {

		VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> verificationRes = fvmFacade.verifyAnOmegaRegularProperty(ts, createAutoStarvation(1));
		if(verificationRes instanceof VerificationSucceeded){
			System.out.println("the analyzed algorithm holds starvation freedom for p1");
		}else if(verificationRes instanceof VerificationFailed){
			System.out.println("the analyzed algorithm DOES NOT hold starvation freedom for p1");
			System.out.println("a possible scenario leading p1 into starvation:");
			System.out.println(verificationRes);
		}
		System.out.println("\n---------------------------------------------\n");

		verificationRes = fvmFacade.verifyAnOmegaRegularProperty(ts, createAutoStarvation(2));
		if(verificationRes instanceof VerificationSucceeded){
			System.out.println("the analyzed algorithm holds starvation freedom for p2");
		}else if(verificationRes instanceof VerificationFailed){
			System.out.println("the analyzed algorithm DOES NOT hold starvation freedom for p2");
			System.out.println("a possible scenario leading p2 into starvation:");
			System.out.println(verificationRes);
		}

	}


	/**
	 *
	 * @param processID
	 * @return the automaton that accepts if the process with processID had an intention to get into the critical section but did not manage to get in
	 */
	public static Automaton<String, String> createAutoStarvation(int processID) {

		System.out.println(String.format("creating an automaton that will accept if p%d is starved - " +
				"waiting for the critical section but not getting in", processID));
		Automaton<String, String> automaton = new Automaton<>();
		System.out.println(String.format("q0 is the initial state where p%d still didn't wait for the critical section", processID));
		automaton.setInitial("q0"); // initial state
		System.out.println(String.format("q1 is the accepting state where p%d waits for the critical section", processID));
		automaton.setAccepting("q1"); // pi waits for the critical section
		System.out.println(String.format("q2 is the non-accepting state where p%d entered the critical section", processID));
		automaton.addState("q2"); // pi entered the critical section

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
								automaton.addTransition("q0", transitionLabels, "q1");
							}
							if (transitionLabels.contains(String.format("crit%d = 1", processID)))
							{//pi entered the critical section hence has not starvation, move from the accepting state to the non accepting state
								automaton.addTransition("q1", transitionLabels, "q2");
							}
							automaton.addTransition("q2",transitionLabels, "q2");
						}
					}
				}
			}
		}
		return automaton;
	}

}
