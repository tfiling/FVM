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

		VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> verificationRes2 = fvmFacade.verifyAnOmegaRegularProperty(ts, createAutoStarvation1());
		if(verificationRes2 instanceof VerificationSucceeded){
			System.out.println("The is starvation freedom property - P1 . YES BABY!!! ");
		}else if(verificationRes2 instanceof VerificationFailed){
			System.out.println("Its not a starvation for P1!! \n for example:");
			System.out.println(verificationRes2);
		}

		VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> verificationRes3 = fvmFacade.verifyAnOmegaRegularProperty(ts, createAutoStarvation2());
		if(verificationRes3 instanceof VerificationSucceeded){
			System.out.println("The is starvation freedom property - P2 . YES BABY!!!");
		}else if(verificationRes3 instanceof VerificationFailed){
			System.out.println("Its not a starvation for P2!! \n for example:");
			System.out.println(verificationRes3);
		}

	}



	public static Automaton<String, String> createAutoStarvation1(){
		Automaton<String, String> auto = new Automaton<>();
		auto.setInitial("q0");
		auto.setAccepting("q1");
		auto.addState("q2");
		createAutoStarvation1A(auto);
		createAutoStarvation1B(auto);
		createAutoStarvation1C(auto);

		return auto;
	}



	public static Automaton<String, String> createAutoStarvation2(){
		Automaton<String, String> auto = new Automaton<>();
		auto.setInitial("q0");
		auto.setAccepting("q1");
		auto.addState("q2");
		createAutoStarvation2A(auto);
		createAutoStarvation2B(auto);
		createAutoStarvation2C(auto);

		return auto;
	}




	/*///////////////////////////////////////////
	 * ////////////////Helpers//////////////
	 *//////////////////////////////////////////

	public static void createAutoStarvation1C(Automaton<String, String> auto) {
		for(int i = 0 ; i<2 ;i++){
			for(int j=0 ; j<2 ; j++){
				for(int k=0;k<2;k++){
					for(int m=0;m<2;m++){
						Set<String> t = new HashSet<>();
						Set<String> t2 = new HashSet<>();
						t.add("crit1 = "+k);
						t.add("crit2 = "+m);
						t.add("b1 = "+i);
						t.add("b2 = "+j);
						for(String ss : t){
							if(!ss.endsWith("0"))
								t2.add(ss);
						}
						auto.addTransition("q2",t2, "q2");
						auto.addTransition("q0",new HashSet<>(t2), "q0");
					}
				}
			}
		}

	}

	public static void createAutoStarvation1B(Automaton<String, String> auto) {
		for(int i = 0 ; i<2 ;i++){
			for(int j=0 ; j<2 ; j++){
				for(int k=0;k<2;k++){
					for(int m=0;m<2;m++){
						Set<String> t = new HashSet<>();
						Set<String> t2 = new HashSet<>();
						if(!(i==1 && k==0)){
							t.add("crit1 = "+k);
							t.add("crit2 = "+m);
							t.add("b1 = "+i);
							t.add("b2 = "+j);
							for(String ss : t){
								if(!ss.endsWith("0"))
									t2.add(ss);
							}
							auto.addTransition("q1",t2, "q2");
						}
					}
				}
			}
		}

	}

	public static void createAutoStarvation1A(Automaton<String, String> auto) {
		for(int i = 0 ; i<2 ;i++){
			for(int j=0 ; j<2 ; j++){
				Set<String> t = new HashSet<>();
				Set<String> t2 = new HashSet<>();
				t.add("crit2 = "+i);
				t.add("b1 = 1");
				t.add("b2 = "+j);
				for(String ss : t){
					if(!ss.endsWith("0"))
						t2.add(ss);
				}
				auto.addTransition("q0",t2, "q1");
				auto.addTransition("q1",new HashSet<>(t2), "q1");
			}
		}
	}

	public static void createAutoMutualExclusionA(Automaton<String, String> auto) {
		for(int i = 0 ; i<2 ;i++){
			for(int j=0 ; j<2 ; j++){
				Set<String> t = new HashSet<>();
				Set<String> t2 = new HashSet<>();
				t.add("crit1 = 1");
				t.add("crit2 = 1");
				t.add("b1 = "+i);
				t.add("b2 = "+j);
				for(String ss : t){
					if(!ss.endsWith("0"))
						t2.add(ss);
				}
				auto.addTransition("q0",t2, "q1");
			}
		}

	}

	public static void createAutoMutualExclusionB(Automaton<String, String> auto) {
		for(int i = 0 ; i<2 ;i++){
			for(int j=0 ; j<2 ; j++){
				for(int k=0;k<2;k++){
					for(int m=0;m<2;m++){
						Set<String> t = new HashSet<>();
						Set<String> t2 = new HashSet<>();
						if(k+m<2){
							t.add("crit1 = "+k);
							t.add("crit2 = "+m);
							t.add("b1 = "+i);
							t.add("b2 = "+j);
							for(String ss : t){
								if(!ss.endsWith("0"))
									t2.add(ss);
							}
							auto.addTransition("q0",t2, "q0");
						}
					}
				}
			}
		}

	}

	public static void createAutoMutualExclusionC(Automaton<String, String> auto) {
		for(int i = 0 ; i<2 ;i++){
			for(int j=0 ; j<2 ; j++){
				for(int k=0;k<2;k++){
					for(int m=0;m<2;m++){
						Set<String> t = new HashSet<>();
						Set<String> t2 = new HashSet<>();
						t.add("crit1 = "+k);
						t.add("crit2 = "+m);
						t.add("b1 = "+i);
						t.add("b2 = "+j);
						for(String ss : t){
							if(!ss.endsWith("0"))
								t2.add(ss);
						}
						auto.addTransition("q1",t2, "q1");
					}
				}
			}
		}
	}


	public static void createAutoStarvation2A(Automaton<String, String> auto) {
		for(int i = 0 ; i<2 ;i++){
			for(int j=0 ; j<2 ; j++){
				Set<String> t = new HashSet<>();
				Set<String> t2 = new HashSet<>();
				t.add("crit1 = "+i);
				t.add("b2 = 1");
				t.add("b1 = "+j);
				for(String ss : t){
					if(!ss.endsWith("0"))
						t2.add(ss);
				}
				auto.addTransition("q0",t2, "q1");
				auto.addTransition("q1",new HashSet<>(t2), "q1");
			}
		}

	}

	public static void createAutoStarvation2B(Automaton<String, String> auto) {
		for(int i = 0 ; i<2 ;i++){
			for(int j=0 ; j<2 ; j++){
				for(int k=0;k<2;k++){
					for(int m=0;m<2;m++){
						Set<String> t = new HashSet<>();
						Set<String> t2 = new HashSet<>();
						if(!(i==1 && k==0)){
							t.add("crit2 = "+k);
							t.add("crit1 = "+m);
							t.add("b2 = "+i);
							t.add("b1 = "+j);
							for(String str : t){
								if(!str.endsWith("0"))
									t2.add(str);
							}
							auto.addTransition("q1",t2, "q2");
						}
					}
				}
			}
		}

	}

	public static void createAutoStarvation2C(Automaton<String, String> auto) {
		for(int i = 0 ; i<2 ;i++){
			for(int j=0 ; j<2 ; j++){
				for(int k=0;k<2;k++){
					for(int m=0;m<2;m++){
						Set<String> t = new HashSet<>();
						Set<String> t2 = new HashSet<>();
						t.add("crit2 = "+k);
						t.add("crit1 = "+m);
						t.add("b2 = "+i);
						t.add("b1 = "+j);
						for(String str : t){
							if(!str.endsWith("0"))
								t2.add(str);
						}
						auto.addTransition("q2",t2, "q2");
						auto.addTransition("q0",new HashSet<>(t2), "q0");
					}
				}
			}
		}

	}


}
