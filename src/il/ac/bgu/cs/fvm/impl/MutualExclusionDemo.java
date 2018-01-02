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
			verifyPeterson1();
			verifyPeterson2();
			verifyPeterson3();
			verifySemaphore();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}
	private static void verifyPeterson1() throws Exception{
		/*Regular Peterson code for 2 processes. */
		  String peterson1P1 = 
				  "do :: true -> \n"
				+ "    atomic {b1:=1 ; x:=2};\n"
				+ "    if :: (x==1) || (b2==0) -> crit1:=1 fi; \n"
				+ "    atomic { crit1:= 0 ; b1:=0}\n"
				+ "od";
		
		  String peterson1P2 = 
				  "do :: true -> \n"
				+ "    atomic{b2:=1 ; x:=1};\n"
				+ "    if :: (x==2) || (b1==0) -> crit2:=1 fi; \n"
				+ "    atomic {crit2:= 0 ; b2:=0}\n"
				+ "od";
		  
		  System.out.println("******************");
		  System.out.println("verify peterson 1\n"); 
		  verifyStrings(peterson1P1, peterson1P2);
		  System.out.println("******************");
		  System.out.println();
		  
	}
	private static void verifyPeterson2() throws Exception{
		/*Regular Peterson code for 2 processes. */
		  String peterson2P1 = 
				  "do :: true -> \n"
				+ "    b1:=1 ; x:=2;\n"
				+ "    if :: (x==1) || (b2==0) -> crit1:=1 fi; \n"
				+ "    atomic { crit1:= 0 ; b1:=0}\n"
				+ "od";
		
		  String peterson2P2 = 
				  "do :: true -> \n"
				+ "    b2:=1 ; x:=1;\n"
				+ "    if :: (x==2) || (b1==0) -> crit2:=1 fi; \n"
				+ "    atomic {crit2:= 0 ; b2:=0}\n"
				+ "od";
		  
		  System.out.println("******************");
		  System.out.println("verify peterson 2\n"); 
		  verifyStrings(peterson2P1, peterson2P2);
		  System.out.println("******************");
		  System.out.println();
		  
	}
	private static void verifyPeterson3() throws Exception{
		/*Regular Peterson code for 2 processes. */
		  String peterson3P1 = 
				  "do :: true -> \n"
				+ "    x:=2; b1:=1 ;\n"
				+ "    if :: (x==1) || (b2==0) -> crit1:=1 fi; \n"
				+ "    atomic { crit1:= 0 ; b1:=0}\n"
				+ "od";
		
		  String peterson3P2 = 
				  "do :: true -> \n"
				+ "    x:=1; b2:=1 ;\n"
				+ "    if :: (x==2) || (b1==0) -> crit2:=1 fi; \n"
				+ "    atomic {crit2:= 0 ; b2:=0}\n"
				+ "od";
		  
		  System.out.println("******************");
		  System.out.println("verify peterson 3\n"); 
		  verifyStrings(peterson3P1, peterson3P2);
		  System.out.println("******************");
		  System.out.println();
		  
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

		addLabels(ts);
		verifyTS(ts);
	}
	
	private static void verifyStrings(String s1,String s2) throws Exception{
		
		/* create TransitionSystem from the nano promela code*/
		FvmFacade fvmFacadeImpl = FvmFacade.createInstance();
		ProgramGraph<String, String> pg1 = fvmFacadeImpl.programGraphFromNanoPromelaString(s1);
		ProgramGraph<String, String> pg2 = fvmFacadeImpl.programGraphFromNanoPromelaString(s2);
		ProgramGraph<Pair<String,String>, String> pg = fvmFacadeImpl.interleave(pg1, pg2);
		Set<ActionDef> ad = set(new ParserBasedActDef());
		Set<ConditionDef> cd = set(new ParserBasedCondDef());
		TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, ad, cd);
		
		verifyTS(ts);
	}
	private static void verifyTS(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
		FvmFacade fvmFacadeImpl = FvmFacade.createInstance();
		/*The labels in the transition system include only the relevant variables */
		List<Pair<Pair<String, String>, Map<String, Object>>>  states = new ArrayList<>(ts.getStates());
		for(int i = 0 ; i<states.size();i++){
			Set<String> label = new HashSet<>(ts.getLabel(states.get(i)));
			for(String s : label){
				if(s.startsWith("<") || s.startsWith("x") || s.startsWith("y")|| s.endsWith("0")){
					ts.removeLabel(states.get(i), s);
				}
			}
		}
		
		/*verify the transition system  - mutual exclusion property*/
		VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> vr = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, createAutoMutualExclusion());
		if(vr instanceof VerificationSucceeded){
			System.out.println("wohoooo! the is mutual execlusion ");
		}
		else if(vr instanceof VerificationFailed){
			System.out.println("There is a problem - no mutual execlusion!! \nfor example:");
			System.out.println(vr);
		}
		
		/*verify the transition system  - starvation freedom property - P1*/
		VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> vr2 = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, createAutoStarvation1());
		if(vr2 instanceof VerificationSucceeded){
			System.out.println("wohoooo! the is starvation freedom property - P1 ");
		}else if(vr2 instanceof VerificationFailed){
			System.out.println("There is a problem - starvation P1!! \nfor example:");
			System.out.println(vr2);
		}
		
		/*verify the transition system  - starvation freedom property - P2*/
		VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> vr3 = fvmFacadeImpl.verifyAnOmegaRegularProperty(ts, createAutoStarvation2());
		if(vr3 instanceof VerificationSucceeded){
			System.out.println("wohoooo! the is starvation freedom property - P2 ");
		}else if(vr3 instanceof VerificationFailed){
			System.out.println("There is a problem - starvation P2!! \nfor example:");
			System.out.println(vr3);
		}
	}
	
	private static Automaton<String, String> createAutoMutualExclusion(){
		Automaton<String, String> auto = new Automaton<>();
		auto.setInitial("q0");
		auto.setAccepting("q1");
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
		return auto;
	}

	private static Automaton<String, String> createAutoStarvation1(){
		Automaton<String, String> auto = new Automaton<>();
		auto.setInitial("q0");
		auto.setAccepting("q1");
		auto.addState("q2");
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
		return auto;
	}

	private static Automaton<String, String> createAutoStarvation2(){
		Automaton<String, String> auto = new Automaton<>();
		auto.setInitial("q0");
		auto.setAccepting("q1");
		auto.addState("q2");
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
		return auto;
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
	
	// Add labels to ts for formulating mutual exclusion properties.
	private static void addLabels(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
		seq("b1 = 1", "b2 = 1", "crit1 = 1", "crit2 = 1").stream().forEach(s -> ts.addAtomicPropositions(s));

		ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("crit1")).forEach(s -> ts.addToLabel(s, "crit1 = 1"));
		ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("wait1")).forEach(s -> ts.addToLabel(s, "b1 = 1"));

		ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("crit2")).forEach(s -> ts.addToLabel(s, "crit2 = 1"));
		ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("wait2")).forEach(s -> ts.addToLabel(s, "b2 = 1"));
	}
	
}
