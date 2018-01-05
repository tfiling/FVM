package il.ac.bgu.cs.fvm.impl;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;

import java.util.ArrayList;
import java.util.HashSet;
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
	
public static void verifyPeterson1() throws Exception{
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
		  
		  System.out.println("verify peterson 1\n"); 
		  verifyStrings(peterson1P1, peterson1P2);
		  System.out.println();
		  
	}
	
public static void verifyPeterson2() throws Exception{
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
	  
	  System.out.println("verify peterson 2\n"); 
	  verifyStrings(peterson2P1, peterson2P2);
	  System.out.println();
	  
}

public static void verifyPeterson3() throws Exception{
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
	  
	  System.out.println("verify peterson 3\n"); 
	  verifyStrings(peterson3P1, peterson3P2);
	  System.out.println();
	  
}


private static void verifyStrings(String s1,String s2) throws Exception{
		
		FvmFacade fvmImpl = FvmFacade.createInstance();
		ProgramGraph<String, String> pg1 = fvmImpl.programGraphFromNanoPromelaString(s1);
		ProgramGraph<String, String> pg2 = fvmImpl.programGraphFromNanoPromelaString(s2);
		ProgramGraph<Pair<String,String>, String> pg = fvmImpl.interleave(pg1, pg2);
		Set<ActionDef> ad = set(new ParserBasedActDef());
		Set<ConditionDef> cd = set(new ParserBasedCondDef());
		TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts = fvmImpl.transitionSystemFromProgramGraph(pg, ad, cd);
		
		checkAndVerifyTS(ts);
	}

static void checkAndVerifyTS(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
	FvmFacade fvmImpl = FvmFacade.createInstance();
	List<Pair<Pair<String, String>, Map<String, Object>>>  states = new ArrayList<>(ts.getStates());
	for(int i = 0 ; i<states.size();i++){
		Set<String> label = new HashSet<>(ts.getLabel(states.get(i)));
		for(String s : label){
			if(s.startsWith("<") || s.startsWith("x") || s.startsWith("y")|| s.endsWith("0")){
				ts.removeLabel(states.get(i), s);
			}
		}
	}
	
	VerificationResult<Pair<Pair<String,String>,Map<String,Object>>> verificationRes = fvmImpl.verifyAnOmegaRegularProperty(ts, createAutoMutualExclusion());
	
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
	
	/*verify the transition system  - starvation freedom property - P2*/
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
	int i,j,k;
	Automaton<String, String> auto = new Automaton<>();
	auto.setInitial("q0");
	auto.setAccepting("q1");
	auto.addState("q2");
	for( i = 0 ; i<2 ;i++){
		for( j=0 ; j<2 ; j++){
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
	createTranA(auto);
	createTranB(auto);
	
	return auto;
}

private static void createTranA(Automaton<String, String> auto) {
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

private static void createTranB(Automaton<String, String> auto) {
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
