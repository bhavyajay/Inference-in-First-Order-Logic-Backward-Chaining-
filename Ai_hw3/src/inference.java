import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;


public class inference {

	public static HashMap< String, HashMap<Integer, List<predicate>>> kb = new HashMap< String, HashMap<Integer, List<predicate>>>();
	public static HashMap< String, HashMap<Integer, predicate>> consequent = new HashMap< String, HashMap<Integer, predicate>>();
	public static HashMap<Integer, predicate> queries = new HashMap<Integer, predicate>();
	public static HashMap<String, List<String>> poo_kb = new HashMap<String, List<String>>();
	public static HashMap<String, List<Integer>> facts_list = new HashMap<String, List<Integer>>(); //list of those facts that were used for substitution 
	public static List<String> factss = new ArrayList<String>(); 
	public static Node currentNode;
	public static predicate root;
	public static int sub =0;
	public static int sub_cons = -1;
	public static class Node	{
		
		String curr_pred;
		predicate pred;
		List<predicate> premises = new ArrayList<predicate>();
		HashMap<String, String> Currunifications = new HashMap<String, String>();	//substitution from sibling and parent
		HashMap<String, String> Currunifications_forchildren = new HashMap<String, String>();	//substitution from sibling and parent for children
		HashMap<String, String> Childunifications = new HashMap<String, String>();	//substitution from children  that will scrap if ret = 0
		HashMap<String, String> child_parent = new HashMap<String, String>();	//mapping of child to parent variables

		int[] truth;
		int ret;
		int premise_no;
	
	}
	
	
	public static class predicate {
	    public String name;
	 	    List<String> arguments;
	    
	    //constructor
	    public predicate(String name, String arg_list) {
	        this.name = name;
	        String[] args_list = arg_list.split(",");
	        this.arguments = Arrays.asList(args_list);
	        
	    	
	    }
	    @Override
	    public int hashCode() {
	       int len = name.length();
	    	for(int i=0;i<arguments.size();i++)
	    	{
	    		len += arguments.get(i).length();
	    	}
	    	
	    	return len;
	    }
	    
	    @Override
	    public boolean equals(Object o) {
	    	 if (o instanceof predicate) {
	    		 
	    		 if(this.name.equals(((predicate)o).name))
	    		 {
	    			
	    			 for(int i=0;i<arguments.size();i++)
	    		     {
	    				 if(!this.arguments.get(i).equals(((predicate)o).arguments.get(i)))
	    				 {
	    					
	    					 return false;
	    				 }
	    		     }
	    			 return true;
	    		 }
	    		 else
	    			 return false;
	             
	         }
	    	 
	    	 return false;
	         
	    }
	 
	}
	public static Node doQuery(predicate p, Node parentNode, int premiseNo, HashMap<String,HashMap<Integer, predicate>> facts,LinkedList<predicate> loop)
	{
	
		int fact_count = 1;
		
		Node currNode = new Node();
		currNode.ret =1;
		currNode.pred = p;
		List<String> copy_of_args = new ArrayList<String>();
		//System.out.println("argsize"+p.name+" "+p.arguments);
		for(int i=0;i<currNode.pred.arguments.size();i++)
		{
			copy_of_args.add(currNode.pred.arguments.get(i)) ;
		}
		
		if(parentNode == null)   //rootnode
		{
			
			 loop = new LinkedList<predicate>(); 

			if(isFact(p, facts) != null)
			{
				currNode.ret = 1;
				return currNode;
			}
			else
			{
			
				HashMap<Integer, List<predicate>> hm = kb.get(p.name); 
				HashMap<Integer, predicate> chm = consequent.get(p.name); 
				for(int i=1;i<=hm.size();i++)  // see all rules containing p
				{
					if(sub!=2)
					{
						if(loop.contains(currNode.pred))
						{
							currNode.ret=0;
							return currNode;
						}
						loop.add(currNode.pred);
						//System.out.println("loop");
						for(int ii =0;ii<loop.size();ii++)
						{
							//System.out.print(" "+loop.get(ii).name);
						}
					//System.out.println();
					}
					currNode.ret=1;
					//System.out.println("ggggggggggggggggggggggggggggg"+i);
					//System.out.println(sub+" "+sub_cons);
					if(sub == 2)
					{
						if(sub_cons != i)
							continue;
					}
					if(sub==2)
					{
						if(loop.contains(currNode.pred))
						{
							currNode.ret=0;
							return currNode;
						}
						loop.add(currNode.pred);
						//System.out.println("loop");
						for(int ii =0;ii<loop.size();ii++)
						{
							//System.out.print(" "+loop.get(ii).name);
						}
					//System.out.println();
					}
						currNode.premises = hm.get(i);
						currNode.truth = new int[currNode.premises.size()];
						for(int j=0;j<currNode.truth.length;j++) 
						{
							currNode.truth[j] = 0;
						}
						
						List<String> arg = chm.get(i).arguments;
						for(int j=0;j<arg.size();j++)  //fill child-parent
						{
							currNode.child_parent.put(arg.get(j), arg.get(j));
							currNode.Currunifications.put(arg.get(j), copy_of_args.get(j));
							currNode.Currunifications_forchildren.put(arg.get(j), copy_of_args.get(j));
							//System.out.println("mmm"+j+" "+arg.get(j)+" "+copy_of_args.get(j));

						}
						
						for(int j=0;j<currNode.premises.size();j++)  //see all premises for a rule
						{
							String pass_str= "";
							for(int t =0;t<currNode.premises.get(j).arguments.size(); t++)
								pass_str+=(currNode.premises.get(j).arguments.get(t))+",";
							
							predicate pass = new predicate(currNode.premises.get(j).name, pass_str);
							//System.out.println("came"+currNode.pred.name+" "+currNode.truth[0]);
							doQuery(pass, currNode, j, facts, loop);
							
							//System.out.println("cameback"+ j);
							//System.out.println("came"+currNode.truth[0]+" "+currNode.pred.name);
							
						}
					
						
						for(int j=0;j<currNode.truth.length;j++)  //update currNode arguments
						{
						
							 if(currNode.truth[j]!=1)							 
							 {
								 //System.out.println("hh"+j);
								 currNode.ret = 0;
							 }
						}
						
					if(currNode.ret == 0)
					{
						if(sub == 2)
						{
							//System.out.println("did i go here");
							return currNode;
						}
						if(facts_list.isEmpty())
						{
							//System.out.println("I continued");
							
						}
						else
						{
							//System.out.println("did I just go here "+i);
							sub_cons=i;
							//try all possible combinations
							if(sub!=2)
							{
									
									
								//System.out.println("factss"+factss);
								List<List<predicate>> resultset = new ArrayList<List<predicate>>();
								for(int k=0;k<factss.size();k++)
								{
									
									HashMap<Integer, predicate> facthm = facts.get(factss.get(k));
										
									List<predicate> toadd = new ArrayList<predicate>();
									for(int l=1;l<=facthm.size();l++)
									{
										toadd.add(facthm.get(l));
										//System.out.print(facthm.get(l).name+" "+facthm.get(l).arguments+",");
									}
									resultset.add(toadd);
									//System.out.println();
								}
								
								List<predicate> toadd = new ArrayList<predicate>();
								for(int k=0;k<factss.size();k++)
								{
									HashMap<Integer, predicate> facthm = facts.get(factss.get(k));
									for(int l=1;l<=facthm.size();l++)
									{
										toadd.add(facthm.get(l));
									
									}
									
								}
									
								List<List<predicate>> result = new ArrayList<List<predicate>>();
								List<predicate> current = new ArrayList<predicate>();
								GeneratePermutations(resultset, result, 0, current);
	
								//System.out.println("GeneratePermutations");
								for(int k=0;k<result.size();k++)
								{
									List<predicate> b = result.get(k);
									//System.out.println("size"+b.size());
									for(int o=0;o<b.size();o++)
									{
										//System.out.print("*"+b.get(o).name+" "+b.get(o).arguments);
									}
									//System.out.println();
								}
									
								//System.out.println(result.size());
								for(int k=0;k<result.size();k++)
								{
									//System.out.println(result.get(k).size());
								}
									

								for(int k=0;k<result.size();k++)
								{
									HashMap<String,HashMap<Integer, predicate>> sub_facts = new HashMap<String, HashMap<Integer, predicate>>();

									List<predicate> it = result.get(k);
									for(int l=0;l<it.size();l++)
									{
										predicate o = it.get(l);
										String pred_name = o.name;
										HashMap<Integer, predicate> to_put = new HashMap<Integer, predicate>();
										to_put.put(1, o);
										sub_facts.put(pred_name, to_put);
										
									}
									sub = 2;
									//System.out.println("rootargsss"+root.arguments.size());
									Node node = doQuery(root, null, 0, sub_facts,loop);
									
									//System.out.println("cycle complete"+k+" "+currNode.ret);
										
									if(node.ret == 1)
									{
										currNode.ret=1;
										return currNode;
									}
									else
										continue;
										
								}
							/*	
								List<List<predicate>> result_oftoadd = new ArrayList<List<predicate>>();
								 for(int l=1; l<=2; l++){
								         result_oftoadd.addAll(getAllLists(toadd, l));
								    }
								 for(int m=0; m<result_oftoadd.size(); m++){
									 for (int x=0; x<result_oftoadd.get(m).size(); x++) {
										 //System.out.print(result_oftoadd.get(m).get(x).name + "  " + result_oftoadd.get(m).get(x).arguments + "; ");
									 }
							            //System.out.println();
							     }
								 //System.out.println("---------------------------------------------------size :" + result_oftoadd.size());
								
								 for(int k=0;k<result_oftoadd.size();k++)
									{
										HashMap<String,HashMap<Integer, predicate>> sub_facts = new HashMap<String, HashMap<Integer, predicate>>();

										List<predicate> it = result_oftoadd.get(k);
										for(int l=0;l<it.size();l++)
										{
											predicate o = it.get(l);
											String pred_name = o.name;
											HashMap<Integer, predicate> to_put = new HashMap<Integer, predicate>();
											to_put.put(1, o);
											sub_facts.put(pred_name, to_put);
											
										}
										sub = 2;
										//System.out.println("rootargsss"+root.arguments.size());
										Node node = doQuery(root, null, 0, sub_facts,loop);
										//System.out.println("bobobobobob");
										//System.out.println("cycle complete"+k+" "+currNode.ret);
											
										if(node.ret == 1)
										{
											currNode.ret=1;
											return currNode;
										}
										else
											continue;
											
									}*/
									
								sub =0;
								sub_cons = -1;
							}
							else
							{
								return currNode;
							}
						}
					}
					else
					{
						//System.out.println("returned from here");
						return currNode;
					}
						//System.out.println("looooooooooooooooooooooooooooooooooooooooooooooooooppppppppppppppppp");
					for(int j=0;j<loop.size();j++)
						 //System.out.println(loop.get(j).name+" "+loop.get(j).arguments);
				
					
				//	if(sub!=2)
					{
						loop.clear();
						//System.out.println("loop");
						for(int ii =0;ii<loop.size();ii++)
						{
							//System.out.print(" "+loop.get(ii).name);
						}
						//System.out.println();
					}
					
					
				}
				return currNode;
					
			}
		}
		else
		{
			//System.out.println("copy_of_args copy_of_args "+copy_of_args);
			List<String> arr = new ArrayList<String>();
			
			for(int i=0;i<currNode.pred.arguments.size();i++)
			{
				if(parentNode.Currunifications_forchildren.containsKey(currNode.pred.arguments.get(i)))
				{	
					currNode.Currunifications.put(currNode.pred.arguments.get(i),parentNode.Currunifications_forchildren.get(p.arguments.get(i)));
					currNode.pred.arguments.set(i, parentNode.Currunifications_forchildren.get(currNode.pred.arguments.get(i)));
				}
			
			}
			
			//System.out.println("fvfvfv  "+currNode.pred.name+" "+currNode.pred.arguments);
			////System.out.println(facts.get("D").get(1));
			if (facts.containsKey(currNode.pred.name))
			{	
				
				if(!factss.contains(currNode.pred.name))
					factss.add(currNode.pred.name);

				//System.out.println("wtf"+factss);
				
				List<String> to_remove = new ArrayList<String>();
				
				HashMap<Integer, predicate> hm = facts.get(currNode.pred.name);
				for(int i=1;i<=hm.size();i++)
				{
					HashMap<String,String> checking= new HashMap<String,String>();
					predicate temp = hm.get(i);	//////System.out.println(temp);		
					String check = "";
					int flag =0;
					int checking_flag = 0;
					for(int j=0;j<currNode.pred.arguments.size();j++)
					{
						if(currNode.pred.arguments.get(j).charAt(0)>='A' && currNode.pred.arguments.get(j).charAt(0)<='Z')
							check += currNode.pred.arguments.get(j)+",";
						else
						{	
							check += temp.arguments.get(j)+","; //there is some substitution
							flag = 1;
							
							to_remove.add(currNode.pred.arguments.get(j));
						
							arr.add(currNode.pred.arguments.get(j)+","+ temp.arguments.get(j));
							
							if(checking.containsKey(currNode.pred.arguments.get(j)))
							{
								if(!checking.get(currNode.pred.arguments.get(j)).equals(temp.arguments.get(j)))
								{
									//System.out.println("breaking");
									checking_flag=1;
									break;
								}
							}
							else
							{
								//System.out.println(currNode.pred.arguments.get(j)+","+ temp.arguments.get(j));
								checking.put(currNode.pred.arguments.get(j),temp.arguments.get(j));
							}
						}							
						
					}
					//System.out.println("checking"+checking_flag);
				
					predicate test = new predicate(currNode.pred.name, check);
					//System.out.println("test "+test.name+" "+test.arguments);
					if(hm.containsValue(test) && checking_flag!=1) //it is a fact
					{
					
						if(flag == 1){	//there is substitution
							
							for(int j=0;j<arr.size();j++)  //updated parent currunification for children
							{
								String[] v = arr.get(j).split(",");
								parentNode.Currunifications_forchildren.put(v[0], v[1]);
							
								currNode.Currunifications.put(v[0],v[1]);
								/*if(parentNode.child_parent.containsKey(v[0]))	//udated parent currunification 
								{
									parentNode.Currunifications.put(parentNode.child_parent.get(v[0]), v[1]);
								}*/
							}
						
							if(facts_list.containsKey(currNode.pred.name))  
							{
								 List<Integer> fact_list = facts_list.get(currNode.pred.name);
								 fact_count++;
								 fact_list.add(fact_count);
								 facts_list.put(currNode.pred.name, fact_list );
								 
							}
							else   			//first time adding in facts list
							{	
								List<Integer> fact_list = new ArrayList<Integer>();
								fact_list.add(fact_count);
								facts_list.put(currNode.pred.name, fact_list );
							
							}
							flag = 0;
							
							//System.out.println("b and d returned this");
							
							parentNode.truth[premiseNo]=1;
							return parentNode;
						}
						else
						{
							
							//System.out.println("q returned this"+" "+parentNode.pred.name+" "+premiseNo+" "+parentNode.truth.length);
							//System.out.println(parentNode.truth[premiseNo]+" "+parentNode.pred.name);
							parentNode.truth[premiseNo]=1;
						//	parentNode.pred.name="M";
							//System.out.println(parentNode.truth[premiseNo]+" "+parentNode.pred.name);
							return parentNode;
						}
						////////////////////////////
					}
					else
					{
						continue;
						
					}
				}
			/*	//System.out.println("qreturned");
				parentNode.truth[premiseNo]=0;
				return parentNode;
			*/
				
				if(kb.containsKey(p.name))
				{
					HashMap<Integer, List<predicate>> hmm = kb.get(p.name); 
					HashMap<Integer, predicate> cm = consequent.get(p.name);
					for(int i=1;i<=hmm.size();i++)  // see all rules containing p
					{
						//System.out.println("**"+currNode.pred.name);
						int loopflag =0;
						for(int ii=0;ii<currNode.pred.arguments.size();ii++)
						{
							if(currNode.pred.arguments.get(ii).charAt(0)>='A' && currNode.pred.arguments.get(ii).charAt(0)<='Z')
							{
								
							}
							else
								{
									loopflag=1;
									break;
								}
						}
						//System.out.println("loopflag"+loopflag);
						if(loopflag==0)// && sub!=2)
						{	
							if(loop.contains(currNode.pred))
							{
								parentNode.truth[premiseNo]=0;
								return parentNode;
							}
							loop.add(currNode.pred);
							//System.out.println("loop");
							for(int ii =0;ii<loop.size();ii++)
							{
								//System.out.print(" "+loop.get(ii).name+" "+loop.get(ii).arguments);
							}
							//System.out.println();
						}
						currNode.ret =1;
						//System.out.println(i);
						currNode.premises = hmm.get(i);
						currNode.truth = new int[currNode.premises.size()];
					
						arr = cm.get(i).arguments;
						int flag_tocheck =0;
						HashMap<String,String> tocheck = new HashMap<String,String>();
						for(int ii=0;ii<arr.size();ii++)
						{
							if(tocheck.containsKey(copy_of_args.get(ii)))
							{
								if(!tocheck.get(copy_of_args.get(ii)).equals(arr.get(ii)))
								{
									flag_tocheck = 1;
								}
							}
							else
								tocheck.put(copy_of_args.get(ii), arr.get(ii));
						}
						
						if(flag_tocheck == 1)
							continue;
						
						//System.out.println("uuut"+copy_of_args);
						for(int j=0;j<arr.size();j++)  //fill child-parent
						{
							//System.out.println(arr.get(j)+" uttt "+ copy_of_args.get(j));
							currNode.child_parent.put(arr.get(j), copy_of_args.get(j));
							if(copy_of_args.get(j).charAt(0)>='A' && copy_of_args.get(j).charAt(0)<='Z')
								currNode.Currunifications_forchildren.put(arr.get(j), copy_of_args.get(j));
							if(currNode.Currunifications.containsKey(copy_of_args.get(j)))
							{
								currNode.Currunifications_forchildren.put(arr.get(j), currNode.Currunifications.get(copy_of_args.get(j)));
								//System.out.println("mmm "+arr.get(j)+" "+ currNode.Currunifications.get(copy_of_args.get(j)));
							}
						}
						for(int j=0;j<currNode.premises.size();j++)  //see all premises for a rule
						{
							//System.out.println("ooooooooooo"+currNode.premises.get(j).name+" "+currNode.premises.get(j).arguments);
							String pass_str= "";
							for(int t =0;t<currNode.premises.get(j).arguments.size(); t++)
								pass_str+=(currNode.premises.get(j).arguments.get(t))+",";
							
							predicate pass = new predicate(currNode.premises.get(j).name, pass_str);
							//System.out.println("pass"+pass.arguments);
							doQuery(pass, currNode, j, facts, loop);
							
						}
						
						for(int k=0;k<currNode.truth.length;k++)
						{
							
							 if(currNode.truth[k]!=1)							 
							 {
								 currNode.ret = 0;
							 }
						}
						
						if(currNode.ret == 0)
						{
							//System.out.println(currNode.pred.name+" got 0 from children");
							currNode.Currunifications_forchildren.clear();
							currNode.child_parent.clear();
							
						}
						else
						{
							//System.out.println("it better come here");
							
							
							
							//update parent currunification_for children and parent currunification  
							
							Iterator<Map.Entry<String, String>> iterator_currunification_forc = currNode.Currunifications_forchildren.entrySet().iterator() ;
						    while(iterator_currunification_forc.hasNext()){
						    	Map.Entry<String, String> unificationEntryy = iterator_currunification_forc.next();
					    		if(!currNode.Currunifications.containsKey(currNode.child_parent.get(unificationEntryy.getKey())  )   ) //udated current currunification
					    		{
					    			currNode.Currunifications.put(currNode.child_parent.get(unificationEntryy.getKey()),unificationEntryy.getValue() );

					    		}
						    }
							
							////
							Iterator<Map.Entry<String, String>> iterator_currunification = currNode.Currunifications.entrySet().iterator() ;
						    while(iterator_currunification.hasNext()){
						    	Map.Entry<String, String> unificationEntry = iterator_currunification.next();
						    		if(!parentNode.Currunifications_forchildren.containsKey(unificationEntry.getKey()))//udated parent currunification for child
						    		{
						    			parentNode.Currunifications_forchildren.put(unificationEntry.getKey(),unificationEntry.getValue() );
						    		}
						    		if(parentNode.child_parent.containsKey(unificationEntry.getKey()))	//udated parent currunification 
									{
										parentNode.Currunifications.put(parentNode.child_parent.get(unificationEntry.getKey()), unificationEntry.getValue());
									}
						           
						        }
						    
						    if(sub!=2)
							{
							int pos = loop.indexOf(currNode.pred);
							/*//System.out.println("d"+pos+" "+loop.size());*/
							//System.out.println(currNode.pred.name);
							if(loop.contains(currNode.pred))
							loop.subList(pos,loop.size() ).clear();
							//System.out.println("loop after remove"+currNode.pred.name);
							for(int ii =0;ii<loop.size();ii++)
							{
								//System.out.print(" "+loop.get(ii).name+" "+loop.get(ii).arguments);
							}
							//System.out.println();
							}
						    
							parentNode.truth[premiseNo]=currNode.ret;
							return parentNode;
						}
						
					//	if(sub!=2)
						{
						int pos = loop.indexOf(currNode.pred);
						/*//System.out.println("d"+pos+" "+loop.size());*/
						//System.out.println(currNode.pred.name);
						if(loop.contains(currNode.pred))
						loop.subList(pos,loop.size() ).clear();
						//System.out.println("loop after remove"+currNode.pred.name);
						for(int ii =0;ii<loop.size();ii++)
						{
							//System.out.print(" "+loop.get(ii).name+" "+loop.get(ii).arguments);
						}
						//System.out.println();
						}
					}
					parentNode.truth[premiseNo]=0;
					return parentNode;
			    }	
				else
				{
					//System.out.println("i returned 0");
					parentNode.truth[premiseNo]=0;
					return parentNode;
				}
			}	
			else   ///not a fact
			{
				
				if(kb.containsKey(p.name))
				{
					HashMap<Integer, List<predicate>> hm = kb.get(p.name); 
					HashMap<Integer, predicate> cm = consequent.get(p.name);
					for(int i=1;i<=hm.size();i++)  // see all rules containing p
					{
						//System.out.println("**"+currNode.pred.name);
						int loopflag =0;
						for(int ii=0;ii<currNode.pred.arguments.size();ii++)
						{
							if(currNode.pred.arguments.get(ii).charAt(0)>='A' && currNode.pred.arguments.get(ii).charAt(0)<='Z')
							{
								
							}
							else
								{
									loopflag=1;
									break;
								}
						}
						//System.out.println("loopflag"+loopflag);
						if(loopflag==0)// && sub!=2)
						{	
							if(loop.contains(currNode.pred))
							{
								parentNode.truth[premiseNo]=0;
								return parentNode;
							}
							loop.add(currNode.pred);
							//System.out.println("loop");
							for(int ii =0;ii<loop.size();ii++)
							{
								//System.out.print(" "+loop.get(ii).name+" "+loop.get(ii).arguments);
							}
							//System.out.println();
						}
						currNode.ret =1;
						//System.out.println(i);
						currNode.premises = hm.get(i);
						currNode.truth = new int[currNode.premises.size()];
					
						arr = cm.get(i).arguments;
						//System.out.println("uuut"+copy_of_args);
						for(int j=0;j<arr.size();j++)  //fill child-parent
						{
							//System.out.println(arr.get(j)+" uttt "+ copy_of_args.get(j));
							currNode.child_parent.put(arr.get(j), copy_of_args.get(j));
							if(copy_of_args.get(j).charAt(0)>='A' && copy_of_args.get(j).charAt(0)<='Z')
								currNode.Currunifications_forchildren.put(arr.get(j), copy_of_args.get(j));
							if(currNode.Currunifications.containsKey(copy_of_args.get(j)))
							{
								currNode.Currunifications_forchildren.put(arr.get(j), currNode.Currunifications.get(copy_of_args.get(j)));
								//System.out.println("mmm "+arr.get(j)+" "+ currNode.Currunifications.get(copy_of_args.get(j)));
							}
						}
						for(int j=0;j<currNode.premises.size();j++)  //see all premises for a rule
						{
							//System.out.println("ooooooooooo"+currNode.premises.get(j).name+" "+currNode.premises.get(j).arguments);
							String pass_str= "";
							for(int t =0;t<currNode.premises.get(j).arguments.size(); t++)
								pass_str+=(currNode.premises.get(j).arguments.get(t))+",";
							
							predicate pass = new predicate(currNode.premises.get(j).name, pass_str);
							//System.out.println("pass"+pass.arguments);
							doQuery(pass, currNode, j, facts, loop);
							
						}
						
						for(int k=0;k<currNode.truth.length;k++)
						{
							
							 if(currNode.truth[k]!=1)							 
							 {
								 currNode.ret = 0;
							 }
						}
						
						if(currNode.ret == 0)
						{
							//System.out.println(currNode.pred.name+" got 0 from children");
							currNode.Currunifications_forchildren.clear();
							currNode.child_parent.clear();
							
						}
						else
						{
							//System.out.println("it better come here");
							
							
							
							//update parent currunification_for children and parent currunification  
							
							Iterator<Map.Entry<String, String>> iterator_currunification_forc = currNode.Currunifications_forchildren.entrySet().iterator() ;
						    while(iterator_currunification_forc.hasNext()){
						    	Map.Entry<String, String> unificationEntryy = iterator_currunification_forc.next();
					    		if(!currNode.Currunifications.containsKey(currNode.child_parent.get(unificationEntryy.getKey())  )   ) //udated current currunification
					    		{
					    			currNode.Currunifications.put(currNode.child_parent.get(unificationEntryy.getKey()),unificationEntryy.getValue() );

					    		}
						    }
							
							////
							Iterator<Map.Entry<String, String>> iterator_currunification = currNode.Currunifications.entrySet().iterator() ;
						    while(iterator_currunification.hasNext()){
						    	Map.Entry<String, String> unificationEntry = iterator_currunification.next();
						    		if(!parentNode.Currunifications_forchildren.containsKey(unificationEntry.getKey()))//udated parent currunification for child
						    		{
						    			parentNode.Currunifications_forchildren.put(unificationEntry.getKey(),unificationEntry.getValue() );
						    		}
						    		if(parentNode.child_parent.containsKey(unificationEntry.getKey()))	//udated parent currunification 
									{
										parentNode.Currunifications.put(parentNode.child_parent.get(unificationEntry.getKey()), unificationEntry.getValue());
									}
						           
						        }
						    
						    if(sub!=2)
							{
							int pos = loop.indexOf(currNode.pred);
							/*//System.out.println("d"+pos+" "+loop.size());*/
							//System.out.println(currNode.pred.name);
							if(loop.contains(currNode.pred))
							loop.subList(pos,loop.size() ).clear();
							//System.out.println("loop after remove"+currNode.pred.name);
							for(int ii =0;ii<loop.size();ii++)
							{
								//System.out.print(" "+loop.get(ii).name+" "+loop.get(ii).arguments);
							}
							//System.out.println();
							}
						    
							parentNode.truth[premiseNo]=currNode.ret;
							return parentNode;
						}
						
					//	if(sub!=2)
						{
						int pos = loop.indexOf(currNode.pred);
						/*//System.out.println("d"+pos+" "+loop.size());*/
						//System.out.println(currNode.pred.name);
						if(loop.contains(currNode.pred))
						loop.subList(pos,loop.size() ).clear();
						//System.out.println("loop after remove"+currNode.pred.name);
						for(int ii =0;ii<loop.size();ii++)
						{
							//System.out.print(" "+loop.get(ii).name+" "+loop.get(ii).arguments);
						}
						//System.out.println();
						}
					}
					parentNode.truth[premiseNo]=0;
					return parentNode;
			    }	
				else
				{
					//System.out.println("i returned 0");
					parentNode.truth[premiseNo]=0;
					return parentNode;
				}
				
			}
		}
	}
	
	
	public static void GeneratePermutations(List<List<predicate>> Lists, List<List<predicate>> result, int depth, List<predicate> current)
	{
	    if(depth == Lists.size())
	    {
	       result.add(current);
	       return;
	     }

	    for(int i = 0; i < Lists.get(depth).size(); ++i)
	    {
	    	List<predicate> toBePassed = new ArrayList<predicate>();
    		toBePassed.addAll(current);
	    	toBePassed.add(Lists.get(depth).get(i));
	        GeneratePermutations(Lists, result, depth + 1, toBePassed );
		}

	}
	
	public static List<List<predicate>> getAllLists(List<predicate> elements, int lengthOfList)
	{
	    //initialize our returned list with the number of elements calculated above
	    List<List<predicate>> allLists = new ArrayList<List<predicate>>(); //predicate[(int)Math.pow(elements.size(), lengthOfList)];

	    //lists of length 1 are just the original elements
	    if(lengthOfList == 1) {
	    	for (int i=0; i<elements.size(); i++) {
	    		List<predicate> elem = new ArrayList<predicate>();
	    		elem.add(elements.get(i));
	    		allLists.add(elem);
	    	}
	    	return allLists; 
	    }
	    else {
	        //the recursion--get all lists of length 3, length 2, all the way up to 1
	       List<List<predicate>> allSublists = getAllLists(elements, lengthOfList - 1);

	        //append the sublists to each element
	        
	        for(int i = 0; i < allSublists.size(); i++){
	         	List<predicate> newListItem =  allSublists.get(i);
	        	for(int j = 0; j < elements.size(); j++){
	                //add the newly appended combination to the list
	            	List<predicate> pri = new ArrayList<predicate>();
	            	pri.addAll(newListItem);
	            	pri.add(elements.get(j));
	            	allLists.add(pri);
	            }
	        }
	        
	        

	        return allLists;
	    }
	}
	
	public static List<predicate> findInRHS(predicate p)
	{
		List<predicate> list = new ArrayList<predicate>();
		return list;
	}
	
	public static void substitute(predicate p, predicate q)
	{
		List<String> plist = p.arguments;
		List<String> qlist = q.arguments;
		
		if(p.name.equals(q.name))
		{
			for(int i=0;i<plist.size()-1;i=i+2)
			{
				if(plist.get(i+1).equals("") && !qlist.get(i+1).equals(""))
				{
					plist.set(i+1, qlist.get(i+1)) ;
				}
				if(qlist.get(i+1).equals("") && !plist.get(i+1).equals(""))
				{
					qlist.set(i+1, plist.get(i+1)) ;
				}
			}
		}
		else
		{
			for(int i=0;i<plist.size()-1;i=i+2)
			{
				for(int j=0;j<qlist.size();j=j+2)
				{
					if(plist.get(i).equals(qlist.get(j)))
					{
						if(plist.get(i+1).equals("") && !qlist.get(i+1).equals(""))
						{
							plist.set(i+1, qlist.get(i+1)) ;
						}
						if(qlist.get(i+1).equals("") && !plist.get(i+1).equals(""))
						{
							qlist.set(i+1, plist.get(i+1)) ;
						}
						
					}
				}
				
			}
		}
		
	}
	
	public static String isFact(predicate p, HashMap<String,HashMap<Integer, predicate>> facts)
	{
		
		
		if (!facts.containsKey(p.name))
			return null;
				
		HashMap<Integer, predicate> hm = facts.get(p.name);
		for(int i=1;i<=hm.size();i++)
		{
			predicate temp = hm.get(i);	//////System.out.println(temp);		
			String check = "";
			for(int j=0;j<p.arguments.size();j++)
			{
				
				if(p.arguments.get(j).charAt(0)>='A' && p.arguments.get(j).charAt(0)<='Z')
					check += p.arguments.get(j)+",";
				else
				{	
					check += temp.arguments.get(j)+",";
				}	
			}
			predicate test = new predicate(p.name, check);
			if(hm.containsValue(test))
				return check;
			
		}
		
		return null;
	
	}
	
	
	public static void main(String[] args) throws IOException, CloneNotSupportedException {
		// TODO Auto-generated method stub
		HashMap<String,HashMap<Integer, predicate>> facts = new HashMap<String, HashMap<Integer, predicate>>();

		String file_name = args[1];
		////////System.out.println(file_name);
		File file = new File(file_name);
		//File file = new File("input.txt");
		PrintStream fileStream = new PrintStream(new File("output.txt"));
		
		BufferedReader br = null;
		br = new BufferedReader(new FileReader(file));
		String line = br.readLine();
		
		int count_query = Integer.parseInt(line);
	
		for(int i=0;i<count_query; i++)
		{
			
			line = br.readLine();
			String[] tokenize = line.split("\\(");
			String name = tokenize[0];
			String arg_list = tokenize[1].substring(0, (tokenize[1].length()-1));		
			predicate pred = new predicate(name, arg_list);
			queries.put(i, pred);
			
		}
		
		line = br.readLine();
		int count_kb = Integer.parseInt(line);
		
		for(int i=0;i<count_kb; i++)
		{
			line = br.readLine();
		
			if(line.contains("=>"))
			{
				
				String[] splits = line.split(" => ");
				String[] lhs = splits[0].split(" \\^ ");
				List<predicate> lhs_pred = new ArrayList<predicate>();
				for(int j=0;j<lhs.length; j++)
				{
					String[] tokenize = lhs[j].split("\\(");
					String name = tokenize[0];
					String arg_list = tokenize[1].substring(0, (tokenize[1].length()-1));
					predicate pred = new predicate(name, arg_list);
					lhs_pred.add(pred);
					
				}
				
				
				String[] tokenize = splits[1].split("\\(");
				String name = tokenize[0];
				String arg_list = tokenize[1].substring(0, (tokenize[1].length()-1));
				
				predicate pred = new predicate(name, arg_list);
				if(kb.containsKey(name))
				{
					HashMap<Integer, List<predicate>> hm = kb.get(name);
					int size = hm.size();
					hm.put(size+1,lhs_pred );
					kb.put(pred.name, hm);
				
				}
				else
				{
					HashMap<Integer, List<predicate>> hm = new HashMap<Integer, List<predicate>>();
					hm.put(1, lhs_pred);
					kb.put(pred.name, hm);
				}
				
				if(consequent.containsKey(name))
				{
					HashMap<Integer,predicate> hm = consequent.get(name);
					int size = hm.size();
					hm.put(size+1,pred );
					consequent.put(pred.name, hm);
				
				}
				else
				{
					HashMap<Integer, predicate> hm = new HashMap<Integer, predicate>();
					hm.put(1, pred);
					consequent.put(pred.name, hm);
				}
				
				
			}
			else
			{
				
				String[] tokenize = line.split("\\(");
				String name = tokenize[0];
				////////System.out.println(name);
				String arg_list = tokenize[1].substring(0, (tokenize[1].length()-1));
				
				predicate pred = new predicate(name, arg_list);
				
				if(facts.containsKey(name))
				{
					HashMap<Integer, predicate> hm = facts.get(name);
					int size = hm.size();
					hm.put((size+1),pred );
					facts.put(pred.name, hm);
			
				}
				else
				{
					HashMap<Integer, predicate> hm = new HashMap<Integer, predicate>();
					hm.put(1, pred);
					facts.put(pred.name, hm);
			
				}
			
			}
				
		}
	
				        
			       
		for(int i=0;i<count_query;i++)
		{
		
			Node parentNode =null;
			
			root = queries.get(i);
			int flag_r=0;
			if(kb.containsKey(root.name))
			{
				for(int j=0;j<root.arguments.size();j++)
				{
					if(root.arguments.get(j).charAt(0)>='A' && root.arguments.get(j).charAt(0)<='Z')
						continue;
					else
					{
						flag_r = 1;
						break;
					}
				}
				if(flag_r==0)
				{
					currentNode=  doQuery(queries.get(i), parentNode, 0, facts, null);
					if(currentNode.ret == 0)
						fileStream.println("FALSE");
					else
						fileStream.println("TRUE");
				}
				else
					fileStream.println("FALSE");
				
			}
			else
			{
				fileStream.println("FALSE");
			}
			
		}
		
			        
		br.close();
		fileStream.close();
	}

}
