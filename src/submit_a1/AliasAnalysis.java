package submit_a1;

import java.util.*;
import java.util.Map.Entry;

import dont_submit.AliasQuery;
import heros.solver.Pair;
import soot.ArrayType;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.RefLikeType;
import soot.SootField;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;

class DS {
	Map<String,Set<String>> rho = new HashMap<>();
	Map<String,Map<String,Set<String>>> sigma = new HashMap<>();
}

public class AliasAnalysis extends BodyTransformer{

	List<Unit> worklist = new ArrayList<Unit>();
	Map<Unit,DS> object = new HashMap<>();
	UnitGraph g;
	int count = 1;
	Map<Unit,String> visited = new HashMap<>();
	
	Set<String> Reachables(String operand, DS d){
		Set<String> s = new HashSet<>();
		Queue<String> q = new LinkedList<>();
		Set<String> visited = new HashSet<>();
		
		for(String s1 : d.rho.get(operand)) {
			
			q.add(s1);
			visited.add(s1);
			s.add(s1);
		}
		
		while(!q.isEmpty()) {
			String s1 = q.poll();
			if(d.sigma.containsKey(s1)) {
				for(Entry<String,Set<String>> entry : d.sigma.get(s1).entrySet()) {
					for(String s2 : entry.getValue()) {
						if(!visited.contains(s2)) {
							q.add(s2);
							visited.add(s2);
						}
						if(!s.contains(s2)) {
							s.add(s2);
						}
					}
				}
			}
		}
		
		return s;
	}
	
	DS Union(DS d1, DS d2) {

		Map<String,Set<String>> m1 = new HashMap<>();
		Map<String,Map<String,Set<String>>> m2 = new HashMap<>();
		DS d = new DS();
		
		for(Entry<String,Set<String>> entry : d1.rho.entrySet()) {
			m1.put(entry.getKey(), new HashSet<>(entry.getValue()));
		}
		
		for(Entry<String,Set<String>> entry : d2.rho.entrySet()) {
			if(m1.containsKey(entry.getKey())) {
				
				Set<String> s1 = new HashSet<>();
				s1.addAll(m1.get(entry.getKey()));
				s1.addAll(entry.getValue());
				
				m1.put(entry.getKey(),s1);
				
			}
			else {
				
				m1.put(entry.getKey(), new HashSet<>(entry.getValue()));
			}
		}
		
		for(Entry<String,Map<String,Set<String>>> objEntry : d1.sigma.entrySet()) {
			
			Map<String,Set<String>> m3 = new HashMap<>();
			for(Entry<String,Set<String>> fEntry : d1.sigma.get(objEntry.getKey()).entrySet()) {
				m3.put(fEntry.getKey(), new HashSet<>(fEntry.getValue()));
			}
			m2.put(objEntry.getKey(), m3);
			
		}
		
		for(Entry<String,Map<String,Set<String>>> objEntry : d2.sigma.entrySet()) {
			
			if(m2.containsKey(objEntry.getKey())) {
				
				for(Entry<String,Set<String>> fEntry : d2.sigma.get(objEntry.getKey()).entrySet()) {
					
					if(m2.get(objEntry.getKey()).containsKey(fEntry.getKey())) {
						
						Set<String> s1 = new HashSet<>();
						
						s1.addAll(m2.get(objEntry.getKey()).get(fEntry.getKey()));
						s1.addAll(fEntry.getValue());
						
						Map<String,Set<String>> m3 = new HashMap<>();
						m3.put(fEntry.getKey(), s1);
						
						m2.put(objEntry.getKey(), m3);
					}
					
					else {
						
						Map<String,Set<String>> m3 = new HashMap<>();
						for(Entry<String,Set<String>> fEntry1 : d2.sigma.get(objEntry.getKey()).entrySet()) {
							m3.put(fEntry.getKey(), new HashSet<>(fEntry1.getValue()));
						}
						m2.put(objEntry.getKey(), m3);
					}
				}
			}
			
			else {
				
				Map<String,Set<String>> m3 = new HashMap<>();
				for(Entry<String,Set<String>> fEntry : d2.sigma.get(objEntry.getKey()).entrySet()) {
					m3.put(fEntry.getKey(), new HashSet<>(fEntry.getValue()));
				}
				m2.put(objEntry.getKey(), m3);
			
			}
			
		}
		
		d.rho.putAll(m1);
		d.sigma.putAll(m2);
		
		return d;
	}
	
	void Method(Unit u, String className, String methodName, DS d1) {
		Stmt s = (Stmt)u;
		
		if(s instanceof DefinitionStmt) {
			DefinitionStmt ds = ((DefinitionStmt)s);
			Value leftOperand = ds.getLeftOp();
			Value rightOperand = ds.getRightOp();
			String leftName = className + " " + methodName + " " + leftOperand;
			String rightName = className + " " + methodName + " " + rightOperand;
			
			if(leftOperand.getType() instanceof RefLikeType) {
				if(rightOperand.getType() instanceof RefLikeType) {
					
					if(rightOperand.toString().contains("@parameter") || rightOperand.toString().contains("@this")) {
						Set<String> s1 = new HashSet<>();
						s1.add("Og");
						d1.rho.put(leftName, s1);
						
						object.put(u, d1);
					}
					
					if(ds.containsInvokeExpr()) {
						// x = y.foo();
						
						Set<String> s1 = new HashSet<>();
						s1.add("Og");
						d1.rho.put(leftName, s1);
						
						Set<String> s2 = new HashSet<>(); 
						InvokeExpr exp = s.getInvokeExpr();
						VirtualInvokeExpr vexp = (VirtualInvokeExpr)exp;
						String variableName = vexp.getBase().toString();
						leftName = className + " " + methodName + " " + variableName;
						if(variableName != "this") {
//							System.out.println(leftName);
							s2.addAll(d1.rho.get(leftName));
						
						
							Set<String> reachable = new HashSet<>();
							reachable = Reachables(leftName,d1);
							for(String s3 : reachable) {
								if(d1.sigma.containsKey(s3)) {
									for(Entry<String,Set<String>> entry : d1.sigma.get(s3).entrySet()) {
										d1.sigma.get(s3).put(entry.getKey(), new HashSet<>(s1));
									}
								}
							}
						
							List<Value> args = vexp.getArgs();
							for(Value v : args) {
								
								leftName = className + " " + methodName + " " + v;	
								Set<String> reach = new HashSet<>();
								reach = Reachables(leftName,d1);
								for(String s3 : reach) {
									if(d1.sigma.containsKey(s3)) {
										for(Entry<String,Set<String>> entry : d1.sigma.get(s3).entrySet()) {
											d1.sigma.get(s3).put(entry.getKey(), new HashSet<>(s1));
										}
									}
								}
							}
						}
						
						object.put(u, d1);
						
					}
					
					if(rightOperand instanceof NewExpr) {
						// x = new A();
						
						if(!visited.containsKey(u)) {
							String r = "R" + count;
							count++;
							
							Set<String> ref = new HashSet<>();
							ref.add(r);
							
							d1.rho.put(leftName,ref);
							
							Map<String,Set<String>> m = new HashMap<>();
							Chain<SootField> chain = ((NewExpr)rightOperand).getBaseType().getSootClass().getFields();
							for(SootField field : chain) {
								m.put(field.getName(), new HashSet<String>());
							}
							d1.sigma.put(r, m);
							
							object.put(u, d1);
							visited.put(u, r);
							
						}
						
						else {
							Set<String> s1 = new HashSet<>();
							s1.add(visited.get(u));
							d1.rho.put(leftName, s1);
							
							Map<String,Set<String>> m = new HashMap<>();
							Chain<SootField> chain = ((NewExpr)rightOperand).getBaseType().getSootClass().getFields();
							for(SootField field : chain) {
								m.put(field.getName(), new HashSet<String>());
							}
							d1.sigma.put(visited.get(u), m);
							
							object.put(u, d1);
						}
						
					}
					
					else if(rightOperand instanceof InstanceFieldRef) {
						// x = y.f;
						
						SootField field = ((InstanceFieldRef)rightOperand).getField();
						String f = field.getName();
						
						String variableName = rightOperand.toString();
						char[] c = variableName.toCharArray();
						int i = 0;
						variableName = "";
						while(c[i] != '.') {
							variableName += c[i];
							i++;
						}
						rightName = className + " " + methodName + " " + variableName;
						
						if(d1.rho.get(rightName).contains("Og")) {
							
							Set<String> s1 = new HashSet<>();
							s1.add("Og");
							d1.rho.put(leftName, s1);
						}
						else {
							Set<String> s1 = new HashSet<>();
							s1.addAll(d1.rho.get(rightName));
							
							Set<String> s2 = new HashSet<>();
							for(String s3 : s1) {
								s2.addAll(d1.sigma.get(s3).get(f));
							}
							
							d1.rho.put(leftName, s2);
						}
						
						object.put(u, d1);
						
					}
					
					else if(leftOperand instanceof InstanceFieldRef) {
						// x.f = y;
						
						SootField field = ((InstanceFieldRef)leftOperand).getField();
						String f = field.getName();
						
						String variableName = leftOperand.toString();
						char[] c = variableName.toCharArray();
						int i = 0;
						variableName = "";
						while(c[i] != '.') {
							variableName += c[i];
							i++;
						}
						leftName = className + " " + methodName + " " + variableName;
						
						if(d1.rho.containsKey(leftName) && d1.rho.get(leftName).contains("Og")) {
							
						}
						
						else if(d1.rho.get(rightName).contains("Og")) {
							
							Set<String> s1 = new HashSet<>();
							if(d1.rho.containsKey(leftName)) {
								s1.addAll(d1.rho.get(leftName));
							}
							
							for(String s2 : s1) {
								d1.sigma.get(s2).replace(f, new HashSet<>(d1.rho.get(rightName)));
							}
							
						}
						
						else if(d1.rho.get(leftName).size() == 1) {
							// Strong Update
						
							Set<String> s1 = new HashSet<>();
							s1.addAll(d1.rho.get(leftName));
							
							for(String s2 : s1) {
								d1.sigma.get(s2).replace(f, new HashSet<>(d1.rho.get(rightName)));
							}
															
						}
						
						else {
							// Weak Update
							
							Set<String> s1 = new HashSet<>();
							
							Set<String> s2 = new HashSet<>();
							if(d1.rho.containsKey(leftName)) {
								s2.addAll(d1.rho.get(leftName));
							}
							for(String s4 : s2) {
								s1.addAll(d1.sigma.get(s4).get(f));
							}
							s1.addAll(d1.rho.get(rightName));
							
							for(String s3 : s2) {
								d1.sigma.get(s3).replace(f, s1);
							}
						}
						
						object.put(u, d1);
							
					}
					
					else if(leftOperand instanceof Local && (rightOperand instanceof Local)){
						// x = y;
					
						d1.rho.put(leftName,new HashSet<>(d1.rho.get(rightName)));
												
						object.put(u, d1);
						
					}
					
					else if(rightOperand.getType() instanceof ArrayType) {
					//	System.out.println("adbxbc");
						if(!visited.containsKey(u)) {
							String r = "R" + count;
							count++;
							
							Set<String> ref = new HashSet<>();
							ref.add(r);
							
							d1.rho.put(leftName,ref);
							
							object.put(u, d1);
							visited.put(u, r);
							
						}
						
						else {
							Set<String> s1 = new HashSet<>();
							s1.add(visited.get(u));
							d1.rho.put(leftName, s1);
							
							object.put(u, d1);
						}
					}
					
					else {
						
						object.put(u, d1);
					}
				}
				
				else {
					
					object.put(u, d1);
				}
				
			}
			
			else {
				
				object.put(u, d1);
			}
		}
		
		else {
				
			object.put(u, d1);
		}
		
	}
	
	@Override
	protected synchronized void internalTransform(Body arg0, String arg1, Map<String, String> arg2) {
		/*
		 * Implement your alias analysis here. A1.answers should include the Yes/No answers for 
		 * the queries
		 */
		
		Body b = arg0;
		String className = b.getMethod().getDeclaringClass().toString();
		String methodName = b.getMethod().getName();
		
//		System.out.println("_________method start___________");
//		System.out.println("Method name: "+ methodName);
//		System.out.println(b);
	
		g = new BriefUnitGraph(arg0);
		for(Unit u : g) {
			object.put(u,new DS());
			worklist.add(u);
		}
		
		while(!worklist.isEmpty()) {
//			System.out.println("*****unit start*****");
			
			Unit unit = worklist.remove(0);
			
//			System.out.println("Unit is "+unit);
			
			DS dPrev = new DS();
			DS dCurr = new DS();
			List<Unit> pred = g.getPredsOf(unit);
			for(Unit u : pred) {
				Method(u, className, methodName, object.get(u));
//				System.out.println("Unit "+u);
//				System.out.println(object.get(u).rho);
//				System.out.println(object.get(u).sigma);
//				System.out.println();
				dPrev = Union(dPrev, object.get(u));
			}
			
			dCurr = object.get(unit);
//			System.out.println(dCurr.rho);
//			System.out.println(dCurr.sigma);
						
			boolean addSucc = false;
			if(dPrev.rho.equals(dCurr.rho)) {
				if(dPrev.sigma.equals(dCurr.sigma)) {
					addSucc = true;
				}
			}
			
			if(!addSucc) {
				
				for(Unit succ : g.getSuccsOf(unit)) {
					
//					System.out.println("Succ added " + succ);
					worklist.add(succ);
				}
				
				object.put(unit, dPrev);
			}
			
			dCurr = object.get(unit);
//			System.out.println(dCurr.rho);
//			System.out.println(dCurr.sigma);
//			
//			System.out.println("****unit end*****");
//			System.out.println();
		}	
		
		
		DS ds = new DS();
		for(Unit u : g) {
			if(g.getSuccsOf(u).isEmpty()) {
				ds = object.get(u);
			}
		}
		
//		System.out.println("Final");
//		System.out.println(ds.rho);
//		System.out.println(ds.sigma);
		
		for(int i = 0; i < A1.queryList.size(); i++) {
			AliasQuery q = A1.queryList.get(i);
			
			if(q.getClassName().equals(className) && q.getMethodName().equals(methodName)) {
				
				String s1 = className + " " + methodName + " " + q.getLeftVar();
				String s2 = className + " " + methodName + " " + q.getRightVar();
				
				if(ds.rho.containsKey(s1) && ds.rho.containsKey(s2)) {
					
					Set<String> s3 = new HashSet<>();
					Set<String> s4 = new HashSet<>();
					s3.addAll(ds.rho.get(s1));
					s4.addAll(ds.rho.get(s2));
					
					if(s3.contains("Og") || s4.contains("Og")) {
						A1.answers[i] = "Yes";
//						System.out.println("1");
					}
					else {
						
						boolean flag = false;
						for(String obj : s3) {
							if(s4.contains(obj)) {
								flag = true;
								break;
							}
						}
						
						if(flag) {
							A1.answers[i] = "Yes";
//							System.out.println("2");
						}
						
						else {
							A1.answers[i] = "No";
//							System.out.println("3");
						}
					}

				}
				
				else {
					A1.answers[i] = "No";
//					System.out.println("4");
				}
			}
		}
		
//		System.out.println("_________method end___________");
//		System.out.println();
	}
}
/*
	
*/
