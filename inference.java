/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package inference;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author AshwinKumar
 */

class Clause {
    
    String clauseName;
    ArrayList <String> variables = new ArrayList<>();
    ArrayList <String> LHS = new ArrayList<>();
    ArrayList <String> RHS = new ArrayList<>();
    Clause(){
    }

    Clause(String cls){
       
            String HS[] = cls.split("=>");
            int index = HS[1].trim().indexOf("(");
            this.clauseName = HS[1].trim().substring(0,index);
            Clause c=null;
            if(inference.KB.containsKey(this.clauseName))
                c = inference.KB.get(this.clauseName);
            if(c!=null){
                c.LHS.add(HS[0].trim());
                //if(!c.RHS.contains(HS[1].trim()))
                    c.RHS.add(HS[1].trim());
            }
            else {
                String vars = HS[1].trim().substring(index+1,HS[1].trim().indexOf(")"));
                String varsarray[] = vars.split(",");
                for (String varsarray1 : varsarray) {
                    variables.add(varsarray1.trim());
                }
                this.LHS.add(HS[0].trim());
                this.RHS.add(HS[1].trim());
                inference.KB.put(this.clauseName,this);
            }
    }
    static Clause newClause(String cls){
            Clause kb1 = new Clause();
       
            int index = cls.trim().indexOf("(");
            kb1.clauseName = cls.trim().substring(0,index);
            String vars = cls.trim().substring((index+1),cls.trim().indexOf(")"));
            String varsarray[] = vars.split(",");
            for (String varsarray1 : varsarray) {
                kb1.variables.add(varsarray1.trim());
            }          
            return kb1;
    }
}
class Fact {
    
    String clauseName,name;
    ArrayList <String> variables = new ArrayList<String>();
    ArrayList <String> LHS = new ArrayList<String>();
    
    Fact(String cls){  
            int index = cls.indexOf("(");
            this.clauseName = cls.substring(0,index); 
            if(inference.facts.containsKey(this.clauseName)){
                Fact f = inference.facts.get(this.clauseName);
                f.variables.add(cls);
            }
            else{
                this.variables.add(cls);
                inference.facts.put(clauseName, this);
                
            }
        }     
} 

public class inference {

    /**
     * @param args the command line arguments
     */
    static HashMap <String,Clause>KB = new HashMap<>();
    static HashMap <String,Fact>facts = new HashMap<>();
    static HashMap <String,String>factConst = new HashMap<>();
    static String currentQuery;
    ArrayList <String> queries = new ArrayList<>();
    ArrayList <String> clauses = new ArrayList<>();
    ArrayList <HashMap> subst = new ArrayList<>();
    ArrayList<String> standKB = new ArrayList<>();
    BufferedWriter writer ;
    PrintWriter pw ;
    int noq,noc;
    void createKB() {
        
        for(String clauses1:standKB){
              if(clauses1.contains("=>")){
                  
                  new Clause(clauses1);
              }  
              else {
                  factConst.put(clauses1, clauses1);
                  new Fact(clauses1);
              }
        }
      
    }
    HashMap<String,String> unify(String prove,String query,ArrayList <HashMap<String,String>> theta){
            
                ArrayList <String> RHS = getRHSVariables(query);
                ArrayList <String> LHS = getRHSVariables(prove);
                HashMap <String,String> hm = new HashMap<>();
                int same=0;
                for(int i=0;i<RHS.size();i++){               
                    //x Constant
                    if(Character.isLowerCase(LHS.get(i).charAt(0))&&Character.isUpperCase(RHS.get(i).charAt(0))){
                        if(hm.containsKey(LHS.get(i))){
                            if(!hm.get(LHS.get(i)).equals(RHS.get(i))){
                                hm.clear();
                                return hm;
                            }
                        }
                        hm.put(LHS.get(i),RHS.get(i));
                    }
                    //Constant x
                    if(Character.isUpperCase(LHS.get(i).charAt(0))&&Character.isLowerCase(RHS.get(i).charAt(0))){
                        if(hm.containsKey(RHS.get(i))){
                            if(!hm.get(RHS.get(i)).equals(LHS.get(i))){
                                hm.clear();
                                return hm;
                            }
                        }
                        hm.put(RHS.get(i),LHS.get(i));
                    } 
                    //constant constant
                   
                    if(Character.isUpperCase(LHS.get(i).charAt(0))&&Character.isUpperCase(RHS.get(i).charAt(0))&&!LHS.get(i).equals(RHS.get(i))){
                        hm.clear();
                        return hm;
                    }
                    // var var
                    if(Character.isLowerCase(LHS.get(i).charAt(0))&&Character.isLowerCase(RHS.get(i).charAt(0))&&!LHS.get(i).equals(RHS.get(i))){
                        hm.put(LHS.get(i),RHS.get(i));
                    }
                    
                    if(Character.isUpperCase(LHS.get(i).charAt(0))&&Character.isUpperCase(RHS.get(i).charAt(0))){
                        same++;
                    }
                   
                }
               if(same==RHS.size()){
                   hm.put("C", "C");
               } 
               runThroughUnify(hm);
               return hm;
    }
    void runThroughUnify(HashMap<String,String> hm){
        HashMap hmcopy = (HashMap) hm.clone();
        Iterator it = hmcopy.entrySet().iterator();
        while (it.hasNext()) {
            HashMap.Entry pair = (HashMap.Entry)it.next();
            String key = (String) pair.getKey();
            String value = (String) pair.getValue();
            if(Character.isLowerCase(value.charAt(0))&&hm.containsKey(value)){
                hm.put(key,hm.get(value));
                runThroughUnify(hm);
            }
            it.remove(); // avoids a ConcurrentModificationException
        }
    }        
    
    ArrayList<String> getRHSVariables(String RHS){
        ArrayList <String> variables = new ArrayList<>();
        int index = RHS.indexOf("(");
        String vars = RHS.substring(index+1,RHS.indexOf(")"));
                String varsarray[] = vars.split(",");
                for (String varsarray1 : varsarray) {
                    variables.add(varsarray1.trim());
                }
                return variables;
    }
    ArrayList <HashMap<String,String>> BackwardOr(String goal,ArrayList <HashMap<String,String>> theta,ArrayList<String> goalCheck){
        
        if(isInFact(goal)){
            return theta;
        }
         ArrayList <String> goalCheckList = new ArrayList<>();
        goalCheckList.addAll(goalCheck);
        if(goalCheckList.contains(goal)){
            theta.clear();
            return theta;
        }
        else {
                    goalCheckList.add(goal);
        }
        ArrayList <HashMap<String,String>> thetaDuplicate = (ArrayList <HashMap<String,String>>) theta.clone();
        ArrayList <HashMap<String,String>> thetaFromAnd = new ArrayList <>();
        ArrayList <HashMap<String,String>> thetareturn=new ArrayList<>();
         ArrayList <HashMap<String,String>> thetamerge=new ArrayList<>();
        ArrayList <String> toprove = new ArrayList<>();
        ArrayList <String> toproveRHS = new ArrayList<>();
       
        
        HashMap<String,String> hm = new HashMap<>();
        Clause goalClause = Clause.newClause(goal);
        Clause KbCluase=null;
        Fact f=null;
        if(KB.containsKey(goalClause.clauseName)){
            KbCluase = KB.get(goalClause.clauseName);
            toprove.addAll(KbCluase.LHS);
            toproveRHS.addAll(KbCluase.RHS);
        }
        if(facts.containsKey(goalClause.clauseName)){
             f = facts.get(goalClause.clauseName);
             toprove.addAll(f.variables);
        }
        for(int i=0;i<toprove.size();i++){
                ArrayList <HashMap<String,String>> thetaToAnd = new ArrayList <>();
                if(KbCluase!=null&&i<KbCluase.LHS.size()){
                    
                   
                    hm = unify(toproveRHS.get(i),goal,thetaDuplicate);
//                    if(hm==null||hm.size()==0){
//                        theta = new ArrayList<>();
//                        return theta;
//                    }
                     if(isInFact(toprove.get(i))){
                        hm.put("F!", "F!");
                    }
                    if(hm.size()>0){
                    thetaToAnd.add(hm);
                    thetaFromAnd = BackwardAnd(toprove.get(i),thetaToAnd,goalCheckList);}
                    if(goal==currentQuery&&thetaFromAnd.size()>0){
                        return thetaFromAnd;
                    }
                   /* Do not return need to go the second tree
                    if(thetaFromAnd==null||thetaFromAnd.size()==0){
                        return new ArrayList <HashMap<String,String>>();
                    }
                           */
                    thetareturn.addAll(thetaFromAnd);
                }
                else {
                    hm = unify(toprove.get(i), goal, thetaDuplicate);
                    //Dont return null return it at the end need for facts
                    if(hm!=null&&hm.size()>0){
                       thetaToAnd.add(hm);
                       thetareturn.addAll(thetaToAnd);
                    }
                    
                } 
        } 
        //Standardize merge values and return
        
       
        thetamerge = mergeVariables(theta, thetareturn);
        return thetamerge;
    }
ArrayList<HashMap<String,String>> mergeVariables(ArrayList<HashMap<String,String>> theta,ArrayList <HashMap<String,String>> thetareturn) {
     ArrayList <HashMap<String,String>> result=new ArrayList<>();
     HashMap <String,String> cum = new HashMap<>();
     for(int i=0;i<theta.size();i++){
         cum.putAll(theta.get(i));
     }
     for(int j=0;j<thetareturn.size();j++){ 
                HashMap<String,String> r = new HashMap<>();
                HashMap<String,String> right = thetareturn.get(j);
                Set<String> keys= right.keySet();
                Iterator<String> it = keys.iterator();
                while(it.hasNext()){
	    	String t = it.next();
                    if(cum.containsKey(t)){
	    		r.put(cum.get(t),right.get(t));
                    }
                    else {
                        r.put(t, right.get(t));
                    }
                } 
                if(r.size()>0)
                    result.add(r);
        }
     return result;
}
/*
    ArrayList<HashMap<String,String>> mergeVariables(ArrayList<HashMap<String,String>> theta,ArrayList <HashMap<String,String>> thetareturn){
        ArrayList <HashMap<String,String>> result=new ArrayList<>();
        for(int i=0;i<thetareturn.size();i++) {
             HashMap<String,String> r = new HashMap<>();
             for(int j=0;j<theta.size();j++){ 
                HashMap<String,String> right = theta.get(j);
                HashMap<String,String> left = thetareturn.get(i);
                Set<String> keys= right.keySet();
                Iterator<String> it = keys.iterator();
                while(it.hasNext()){
	    	String t = it.next();
                    if(left.containsKey(t)){
	    		r.put(left.get(t),right.get(t));
                    }
                    else {
                        r.put(t, right.get(t));
                    }
                }         
                 
            }
            if(r.size()>0)
            result.add(r);
        }
        return result;
    }'
    */
    
     ArrayList <HashMap<String,String>> BackwardAnd(String goal,ArrayList <HashMap<String,String>> theta,ArrayList <String> goalcheck){
        //Nothing to substitute or goals base condition 
        if(theta.size()==0||theta==null||goal==null){
             return new ArrayList <HashMap<String,String>>();
        }
        ArrayList <HashMap<String,String>> thetaDuplicate = (ArrayList <HashMap<String,String>>) theta.clone();
        
        ArrayList <HashMap<String,String>> afterrest = new ArrayList<>();
        ArrayList <HashMap<String,String>> thetatoreturn = new ArrayList<>();
        String firstGoal,restGoal;
        ArrayList <HashMap<String,String>> thetadash=null;
        if(goal.contains("^"))
        {
            firstGoal =goal.substring(0,goal.indexOf("^")).trim();
            restGoal = goal.substring(goal.indexOf("^")+1,goal.length());
        }
        else{
                firstGoal = goal;
                restGoal= null;
        }
        for(int i=0;i<thetaDuplicate.size();i++){
            ArrayList <HashMap<String,String>> toOr = new ArrayList<>();
            String sub = substituteVars(firstGoal,thetaDuplicate.get(i));
            toOr.add(thetaDuplicate.get(i));
            thetadash = BackwardOr(sub, toOr,goalcheck);
            if(thetadash.size()==0||thetadash==null){
                theta.clear();
                return theta;
            }
          
            if(restGoal!=null){
                for (int j=0;j<thetadash.size();j++) {
                    for(int k=0;k<theta.size();k++){
                        thetadash.get(j).putAll(theta.get(k));
                    }
				
		}
                for(int l=0;l<thetadash.size();l++){
                    ArrayList <HashMap<String,String>> afterOR = new ArrayList<>();
                    afterOR.add(thetadash.get(l));
                    afterrest = BackwardAnd(restGoal, afterOR,goalcheck);
                    thetatoreturn.addAll(afterrest);
                }
            }
            else {
                thetatoreturn.addAll(thetadash);
            }
            
        }
       
        return thetatoreturn;
     }
    
    String substituteVars(String goal,HashMap<String,String> theta){
        Clause goalClause = Clause.newClause(goal);
        String substitute= goalClause.clauseName+"(";
        for(int i=0;i<goalClause.variables.size();i++){
                
             
                if(theta.containsKey(goalClause.variables.get(i))&&Character.isUpperCase(theta.get(goalClause.variables.get(i)).charAt(0))){
                    substitute+=theta.get(goalClause.variables.get(i));
                }
                else {
                    substitute+=goalClause.variables.get(i);
                }
            
                if(goalClause.variables.size()!=1&&i!=(goalClause.variables.size()-1)){
                substitute+=",";
                }
        }
        substitute+=")";
        return substitute;
        
    }
     
    void readInput(String fileName) {
            try {
                    FileReader fileReader = new FileReader(fileName);
                    writer = new BufferedWriter(new FileWriter("output.txt"));
                    pw = new PrintWriter(writer);
                    BufferedReader bufferedReader = new BufferedReader(fileReader);
                    noq = Integer.parseInt(bufferedReader.readLine());
                    for(int i=0;i<noq;i++){
                        queries.add( bufferedReader.readLine());
                    }
                    noc = Integer.parseInt(bufferedReader.readLine());
                    for(int i=0;i<noc;i++){
                        clauses.add(bufferedReader.readLine());
                    }
                    
                    
                    StandardizeKB();
                    createKB(); 
                    executeQueries();
            }
            catch(Exception e) {
                e.printStackTrace();
            }
    }
    void StandardizeKB(){
        int count=0;
        
        for(int i=0;i<clauses.size();i++){ 
            
            String clause = clauses.get(i);
            String result = "";
            if(clause.contains("=>")){
                HashMap <String,String> hm = new HashMap<>();
                String HS[]=clause.split("=>");
                String LHS[] = HS[0].trim().split(" \\^ ");
                String RHS = HS[1].trim();
                //Process LHS
                for(int j=0;j<LHS.length;j++){
                    Clause LHSClause = Clause.newClause(LHS[j]);
                    result+=LHSClause.clauseName+"(";
                    for(int k=0;k<LHSClause.variables.size();k++){
                        if(hm.containsKey(LHSClause.variables.get(k))){
                            result+=hm.get(LHSClause.variables.get(k));
                        }
                        else if(Character.isUpperCase(LHSClause.variables.get(k).charAt(0))){
                            result+=LHSClause.variables.get(k);
                        }
                        else {
                            result+=("x"+(++count));
                            hm.put(LHSClause.variables.get(k),("x"+(count)));
                            
                        }
                        if(k<LHSClause.variables.size()-1){
                            result+=",";
                        }
                        else{
                            result+=")";
                        }
                    }
                    if(j<LHS.length-1){
                        result+=" ^ ";
                    }
                }
                result+=" => ";
                Clause RHSClause = Clause.newClause(RHS);
                result+=RHSClause.clauseName+"(";
                for(int k=0;k<RHSClause.variables.size();k++){
                        if(hm.containsKey(RHSClause.variables.get(k))){
                            result+=hm.get(RHSClause.variables.get(k));
                        }
                        else if(Character.isUpperCase(RHSClause.variables.get(k).charAt(0))){
                            result+=RHSClause.variables.get(k);
                        }
                        else {
                            result+=("x"+(++count));
                            hm.put(RHSClause.variables.get(k),("x"+(count)));
                            
                        }
                        if(k<RHSClause.variables.size()-1){
                            result+=",";
                        }
                        else{
                            result+=")";
                        }
                 }
                standKB.add(result);
            }
            else {
                standKB.add(clauses.get(i));
            }
            
        }
    }
    void executeQueries() throws IOException {
         for(int i = 0 ;i<queries.size();i++){
            currentQuery = queries.get(i);
            if(isInFact(currentQuery)){
              System.out.println("True");
              pw.println("TRUE");
            }
            else{
            ArrayList<HashMap<String,String>> al = BackwardOr(queries.get(i),new ArrayList<HashMap<String,String>>(),new ArrayList<String>());
            if(al.size()>0){
                System.out.println("True");
                pw.println("TRUE");
            }
            else {
                System.out.println("False");
                pw.println("FALSE");
            }}
         }
         pw.close();
         writer.close();
       
    }
    boolean isInFact(String goal){
        
        if(factConst.containsKey(goal))
            return true;
        else 
            return false;
        
    }
    public static void main(String[] args) {
        // TODO code application logic here
        inference obj = new inference();
        obj.readInput(args[1]);
    }
    
}
