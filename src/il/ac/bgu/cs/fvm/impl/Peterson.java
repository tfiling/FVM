package il.ac.bgu.cs.fvm.impl;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;

public class Peterson {

	public Peterson() {}
	
public static void PetersonA() throws Exception{
		  String petersonA1 = 
				  "do :: true -> \n"
				+ "    atomic {b1:=1 ; x:=2};\n"
				+ "    if :: (x==1) || (b2==0) -> crit1:=1 fi; \n"
				+ "    atomic { crit1:= 0 ; b1:=0}\n"
				+ "od";
		
		  String petersonA2 = 
				  "do :: true -> \n"
				+ "    atomic{b2:=1 ; x:=1};\n"
				+ "    if :: (x==2) || (b1==0) -> crit2:=1 fi; \n"
				+ "    atomic {crit2:= 0 ; b2:=0}\n"
				+ "od";
		  
		  System.out.println("verify peterson 1\n"); 
		  checkTheWord(petersonA1, petersonA2);	  
	}
	
public static void PetersonB() throws Exception{
	  String petersonB1 = 
			  "do :: true -> \n"
			+ "    b1:=1 ; x:=2;\n"
			+ "    if :: (x==1) || (b2==0) -> crit1:=1 fi; \n"
			+ "    atomic { crit1:= 0 ; b1:=0}\n"
			+ "od";
	
	  String petersonB2 = 
			  "do :: true -> \n"
			+ "    b2:=1 ; x:=1;\n"
			+ "    if :: (x==2) || (b1==0) -> crit2:=1 fi; \n"
			+ "    atomic {crit2:= 0 ; b2:=0}\n"
			+ "od";
	  
	  System.out.println("verify peterson 2\n"); 
	  checkTheWord(petersonB1, petersonB2);  
}

public static void PetersonC() throws Exception{
	  String petersonC1 = 
			  "do :: true -> \n"
			+ "    x:=2; b1:=1 ;\n"
			+ "    if :: (x==1) || (b2==0) -> crit1:=1 fi; \n"
			+ "    atomic { crit1:= 0 ; b1:=0}\n"
			+ "od";
	
	  String petersonC2 = 
			  "do :: true -> \n"
			+ "    x:=1; b2:=1 ;\n"
			+ "    if :: (x==2) || (b1==0) -> crit2:=1 fi; \n"
			+ "    atomic {crit2:= 0 ; b2:=0}\n"
			+ "od";
	  
	  System.out.println("verify peterson 3\n"); 
	  checkTheWord(petersonC1, petersonC2);
	  
}


private static void checkTheWord(String str1,String str2) throws Exception{
		//create a fvm
		FvmFacade fvmImpl = FvmFacade.createInstance();
		
		//create 2 PG and then intreleave them
		ProgramGraph<String, String> pg1 = fvmImpl.programGraphFromNanoPromelaString(str1);
		ProgramGraph<String, String> pg2 = fvmImpl.programGraphFromNanoPromelaString(str2);
		ProgramGraph<Pair<String,String>, String> pg = fvmImpl.interleave(pg1, pg2);
		
		
		Set<ActionDef> actDef = set(new ParserBasedActDef());
		Set<ConditionDef> condDef = set(new ParserBasedCondDef());
		TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts = fvmImpl.transitionSystemFromProgramGraph(pg, actDef, condDef);
		
		checkAndVerifyTS(ts);
	}

public static void checkAndVerifyTS(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
	FvmFacade fvmImpl = FvmFacade.createInstance();
	List<Pair<Pair<String, String>, Map<String, Object>>>  allStates = new ArrayList<>(ts.getStates());
	
	for(int i = 0 ; i<allStates.size();i++){
		Set<String> label = new HashSet<>(ts.getLabel(allStates.get(i)));
	    Iterator<String> iterator = label.iterator();

	    while(iterator.hasNext()) 
		{
			String labelElement = iterator.next();
			if(labelElement.startsWith("<") || labelElement.startsWith("x") || labelElement.startsWith("y")|| labelElement.endsWith("0")){
				ts.removeLabel(allStates.get(i), labelElement);
			}
		}
	}

	VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> verificationRes = fvmImpl.verifyAnOmegaRegularProperty(ts, createAutoMutualExclusion());
	
	verifyTheResults(verificationRes, fvmImpl, ts);
	
}

public static void addLabels(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
	seq("b1 = 1", "b2 = 1", "crit1 = 1", "crit2 = 1").stream().forEach(s -> ts.addAtomicPropositions(s));
		
	ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("crit1")).forEach(s -> ts.addToLabel(s, "crit1 = 1"));
	ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("wait1")).forEach(s -> ts.addToLabel(s, "b1 = 1"));
	ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("crit2")).forEach(s -> ts.addToLabel(s, "crit2 = 1"));
	ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("wait2")).forEach(s -> ts.addToLabel(s, "b2 = 1"));
}


private static void verifyTheResults(
		VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> verificationRes, FvmFacade fvmImpl, TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
	if(verificationRes instanceof VerificationSucceeded){
		System.out.println("The is mutual execlusion Baby");
	}
	else if(verificationRes instanceof VerificationFailed){
		System.out.println("Its not mutual execlusion!! \n for example mutual execlusion is:");
		System.out.println(verificationRes);
	}
	
	VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> verificationRes2 = fvmImpl.verifyAnOmegaRegularProperty(ts, createAutoStarvation1());
	if(verificationRes2 instanceof VerificationSucceeded){
		System.out.println("The is starvation freedom property - P1 . YES BABY!!! ");
	}else if(verificationRes2 instanceof VerificationFailed){
		System.out.println("Its not a starvation for P1!! \n for example:");
		System.out.println(verificationRes2);
	}
	
	VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> verificationRes3 = fvmImpl.verifyAnOmegaRegularProperty(ts, createAutoStarvation2());
	if(verificationRes3 instanceof VerificationSucceeded){
		System.out.println("The is starvation freedom property - P2 . YES BABY!!!");
	}else if(verificationRes3 instanceof VerificationFailed){
		System.out.println("Its not a starvation for P2!! \n for example:");
		System.out.println(verificationRes3);
	}
	
}

private static Automaton<String, String> createAutoMutualExclusion(){
	Automaton<String, String> auto = new Automaton<>();
	auto.setInitial("q0");
	auto.setAccepting("q1");
	createAutoMutualExclusionA(auto);
	createAutoMutualExclusionB(auto);
	createAutoMutualExclusionC(auto);
	
	return auto;
}



private static Automaton<String, String> createAutoStarvation1(){
	Automaton<String, String> auto = new Automaton<>();
	auto.setInitial("q0");
	auto.setAccepting("q1");
	auto.addState("q2");
	createAutoStarvation1A(auto);
	createAutoStarvation1B(auto);
	createAutoStarvation1C(auto);
	
	return auto;
}



private static Automaton<String, String> createAutoStarvation2(){
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

private static void createAutoStarvation1C(Automaton<String, String> auto) {
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

private static void createAutoStarvation1B(Automaton<String, String> auto) {
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

private static void createAutoStarvation1A(Automaton<String, String> auto) {
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

private static void createAutoMutualExclusionA(Automaton<String, String> auto) {
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

private static void createAutoMutualExclusionB(Automaton<String, String> auto) {
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

private static void createAutoMutualExclusionC(Automaton<String, String> auto) {
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


private static void createAutoStarvation2A(Automaton<String, String> auto) {
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

private static void createAutoStarvation2B(Automaton<String, String> auto) {
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

private static void createAutoStarvation2C(Automaton<String, String> auto) {
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
