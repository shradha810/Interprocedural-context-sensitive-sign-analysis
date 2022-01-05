
package CallGraphCreation;

import soot.jimple.DefinitionStmt;
import java.util.*;

import soot.Value;

import soot.toolkits.scalar.ArraySparseSet;
import soot.toolkits.scalar.ForwardFlowAnalysis;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.FlowSet;
import soot.util.Chain;
import soot.Body;
import soot.Local;
import soot.SootMethod;
import soot.JimpleBodyPack;
import soot.Unit;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.tagkit.LineNumberTag;
import soot.jimple.DefinitionStmt;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;


import soot.toolkits.scalar.AbstractFlowSet;
import soot.toolkits.scalar.Pair;

import java.util.*;

public class InterSign extends ForwardFlowAnalysis {
    Body b;
    FlowSet inval, outval, merge_result;
    int flag=0;
    HashMap<SootMethod, ArrayList<String>> func_par_sign;
    HashMap<SootMethod, String> func_ret_sign;
    SootMethod current_method;
    static char[] operators=new char[] {'[', '+', '-', '*', '/'}; 

    public InterSign(UnitGraph g) {
        super(g);
        b = g.getBody();
        Chain<Local> local_variables = b.getLocals();
        ArrayList<String> ar1 = new ArrayList<String>();
        for (Local s : local_variables) {
            String ss=s.toString();
            ar1.add(ss);
        }
        System.out.println("local variables: "+ar1);
        doAnalysis();
        Iterator iter = outval.iterator();
        System.out.println("FINAL SIGN:");
        while (iter.hasNext()) {
            Pair inv = (Pair<String, String>) iter.next();
            String s1 = inv.getO1().toString();
            String s2 = inv.getO2().toString();
            System.out.println("Variable: " + s1 + " Sign: " + s2);
        }
    }
    public InterSign(UnitGraph graph, SootMethod method, HashMap<SootMethod, String> return_var_sign, HashMap<SootMethod, ArrayList<String>> par_sign)
    {
        super(graph);   
        b = graph.getBody();
        current_method=method;
        func_ret_sign=return_var_sign;
        func_par_sign=par_sign;
        doAnalysis();
        Iterator iter = outval.iterator();
        System.out.println("FINAL SIGN:");
        while (iter.hasNext()) {
            Pair inv = (Pair<String, String>) iter.next();
            String s1 = inv.getO1().toString();
            String s2 = inv.getO2().toString();
            System.out.println("Variable: " + s1 + " Sign: " + s2);
        }
    }
    public static Pair<String, String> iterate(FlowSet set, String str){
        Iterator it = set.iterator();
        while(it.hasNext()){
            Pair pair = (Pair<String, String>)it.next();
            String test = pair.getO1().toString();
            if(test.equals(str))
                return pair;
        }
        Pair<String, String> ep=new Pair<String, String>("reference", null);
        return ep;
    }
    
    public static int check_operands(String string, int i){
        //----------------------Creating array of operators and operands ------------------
        
        for(int var = 0; var < 5; var++) {
            if(operators[var] == string.charAt(i)) {
                return 1;
            }
        }
        return 0;
    }
    
    public String Handle_Invoke(Stmt u) {
        String return_sign="", res_sign = "";
        SootMethod method = u.getInvokeExpr().getMethod();
        ArrayList<String> signs = new ArrayList<String>();
        String op3="";
        if(!(method.isJavaLibraryMethod()))
        {
            if(!(method.isConstructor())) {
                System.out.println("method invoked: "+method);
                String s=u.getInvokeExpr().toString();
                int ind1 = s.lastIndexOf('(');
                int ind2 = s.lastIndexOf(')');
                String operands = s.substring(ind1+1, ind2);
                List l1=Arrays.asList(operands.split(", "));
                int len = l1.size();
                // Finding the resultant signs of each parameter of the called function
                for(int variable = 0;variable < len; variable++) {
                    op3=l1.get(variable).toString();
                    char c = op3.charAt(0);
                    if(c == '-') {
                        res_sign="-";
                    }
                    else if(Character.isDigit(c)) {
                        int par=Integer.parseInt(op3);      
                        res_sign = par==0?"0":"+";
                    }
                    else {
                        res_sign = iterate(inval, op3).getO2().toString();
                    }
                    signs.add(res_sign);
                }
                func_par_sign.put(method,  signs);         
                new InterSign((new ExceptionalUnitGraph(method.getActiveBody())), method, func_ret_sign, func_par_sign);
                return_sign = func_ret_sign.get(method);
            }
        }
        // returning the final sign of the return variable
        return return_sign;
        
    }
    @Override
    protected void flowThrough(Object in, Object unit, Object out) {
        inval = (FlowSet) in;
        outval = (FlowSet) out;
        List<String> rhs_array = new ArrayList<String>();
        Stmt u = (Stmt) unit;
        Iterator<ValueBox> defIt = u.getDefBoxes().iterator();
        ArrayList<Pair<String, String>> to_kill = new ArrayList<Pair<String, String>>();
        System.out.println("Statement: " + u);
        if(flag == 1) {
            inval=merge_result;
            flag=0;
        }
        inval.copy(outval);
        String var;
        if(u instanceof AssignStmt || u instanceof IdentityStmt ) { 
            System.out.println("\nInSet: ");
            Iterator it = inval.iterator();
            while (it.hasNext()) {
                Pair inv = (Pair<String, String>) it.next();
                System.out.println(inv.toString().substring(5));
            }
        }
            
      //Kill the var which is defined
        String kill_var_sign="";
        if (u instanceof AssignStmt) {
            if(defIt.hasNext()) {
                ValueBox lll=defIt.next();
                String definedVar = lll.getValue().toString();
                Iterator itOut = outval.iterator();
                while (itOut.hasNext()) {
                    Pair p = (Pair<String, String>) itOut.next();
                    String str1 = p.getO1().toString();
                    if(str1.charAt(0) != '&' && str1.equals(definedVar)) {            
                        System.out.println("pair to be killed: "+p.getO1().toString()+ ',' +p.getO2().toString());
                        kill_var_sign=p.getO2().toString();
                        to_kill.add(p);                     
                    }
                }
            }
            Iterator<Pair<String, String>> pIt = to_kill.iterator();
            while (pIt.hasNext()) {
                Pair<String, String> p = pIt.next();
                outval.remove(p);
                System.out.println("After Killing" + outval);
            }
        }
        //Gen the variable which is defined
        if(u instanceof AssignStmt) {
            String lhs_string=((AssignStmt) u).getLeftOp().toString();
            String rhs_string=((AssignStmt) u).getRightOp().toString();
            
            //--------Bin_exp 0 is for unary expressions and Bin_exp 1 is for binary expressions---------------         
            int Bin_exp=0,i=0, func_exp = 0, op_at = 0;
            String str1="";
            if(rhs_string.charAt(0) == '-') {
                i=1;
            }
            else if(rhs_string.indexOf("neg")==0) {
                i=4;
            }
            if(rhs_string.charAt(0) == '-' || rhs_string.indexOf("neg")==0) {
                str1="-";
                while(i<rhs_string.length()) {
                    if(rhs_string.charAt(i) != ' '){
                        Bin_exp = check_operands(rhs_string, i);
                        if(Bin_exp==1) 
                            break;
                        else{
                            str1+=rhs_string.charAt(i);
                            i+=1;
                        }  
                    }
                }
            }
            else if(rhs_string.contains("invoke"))
            {
                func_exp=1;
                int j=0;
                int start = rhs_string.lastIndexOf('(');
                int end = rhs_string.lastIndexOf(')');
                int len = rhs_string.length();
                while(j<len)
                {
                    char c = rhs_string.charAt(j);
                    if(j == start)
                    {
                        while(j<len && j!=end)
                        {
                            j +=1;
                        }
                    }
                    else
                    {
                        for(int variable = 0; variable < 5; variable++) {
                            if(operators[variable] == rhs_string.charAt(j)) {
                                Bin_exp=1;
                                op_at = j;
                                break;
                            }
                        }
                    }
                    j +=1;
                }
            }
            else
            {
                while(i<rhs_string.length()) {
                    Bin_exp = check_operands(rhs_string, i);
                    if(Bin_exp==1) 
                        break;
                    else{
                        str1+=rhs_string.charAt(i);
                        i+=1;
                    }
                }
            }
            if(func_exp == 1) {
                if(Bin_exp == 0)
                    rhs_array.add(rhs_string);
                else {
                    rhs_array.add(rhs_string.substring(0,op_at-1));
                    rhs_array.add(rhs_string.substring(op_at+2));
                }
            }
            else if(Bin_exp == 0) {
                rhs_array.add(str1);
            }
            else {
                rhs_array = Arrays.asList(rhs_string.split(" ", 0));
            }

            //-----------------------------------------------------------------------------------------
            
            // ------- Unary Expressions ---------------
            
            if(rhs_array.size() == 1) {
                
                String resultant_sign = "";
                
                
                if (u.toString().contains("invoke"))
                {
                    resultant_sign = Handle_Invoke(u);
                    
                }
                //---------RHS like y=500 ------------
                if(Character.isDigit(rhs_array.get(0).charAt(0)) && rhs_array.get(0).charAt(0) != '0'){
                    resultant_sign = "+";
                }
                
                //---------RHS like y= arr[r]------------
                else if(rhs_array.get(0).charAt(rhs_array.get(0).length()-1) == ']') {
                    resultant_sign = "T";
                }
                
                //---------RHS like y=0 ------------
                else if(rhs_array.get(0).charAt(0) == '0') {
                    resultant_sign = "0";
                }
                
                else if(rhs_array.get(0).charAt(0) == '-') {
                    
                    //---------RHS like y=-x ------------
                    if(rhs_array.get(0).charAt(1)<'0' || rhs_array.get(0).charAt(1)>'9') {
                        String operand = rhs_array.get(0);
                        operand = operand.substring(1, operand.length());
                        String res = iterate(inval, operand).getO2().toString();
                        resultant_sign = res == "+" ? "-": "+";
                    }
                    
                    //---------RHS like y=-500 ------------
                    else {
                        resultant_sign = "-";}
                }
                //---------RHS like y=x------------
                else {
                    Iterator it = inval.iterator();
                    while(it.hasNext()){
                        Pair pair = (Pair<String, String>)it.next();
                        String s1 = pair.getO1().toString();
                        String s2 = pair.getO2().toString();
                        if(s1.equals(rhs_array.get(0))) {
                            resultant_sign = s2;
                        }
                    }
                    //String operand = rhs_array.get(0);
                    //resultant_sign = iterate(inval, operand).getO2().toString();
                }
                Pair pair = new Pair(((AssignStmt) u).getLeftOp(), resultant_sign);
                outval.add(pair);               
                System.out.println("Generating " + pair.getO1() + " " + pair.getO2());
            }
            
            //------------- Binary expressions ------------
            else if(rhs_array.size() == 3) {
                String final_sign=""; 
                String first_operand=rhs_array.get(0);
                String operator=rhs_array.get(1);
                String second_operand=rhs_array.get(2);
                
                
                //-------------------- working on the first operand----------------
                String sign1="";
                //operand is a function call
                if (first_operand.contains("invoke"))
                {
                    sign1 = Handle_Invoke(u);
                    
                }
                Iterator it1 = inval.iterator();
                // operand is a number
                if(Character.isDigit(first_operand.charAt(0)) && first_operand.charAt(0) != '0'){
                    sign1 = "+";
                }
                // operand is a negative number
                else if(first_operand.charAt(0) == '-'){
                    sign1 = "-";
                }
                // operand is 0
                else if(first_operand.charAt(0) == '0'){
                    sign1 = "0";
                }
                // operand is a variable
                if((first_operand.charAt(0) < '0' || first_operand.charAt(0) > '9') && first_operand.charAt(0) != '-') {
                    sign1 = iterate(inval, first_operand).getO2().toString();
                }
                
                
                
                //-------------------- working on the second operand----------------    
                String sign2="";
                
                // operand is a function call
                if (second_operand.contains("invoke"))
                {
                    sign2 = Handle_Invoke(u);
                }
                // operand is a variable
                
                if((second_operand.charAt(0) < '0' || second_operand.charAt(0) > '9') && second_operand.charAt(0) != '-') {
                    sign2 = iterate(inval, second_operand).getO2().toString();
                }
                // operand is a number
                else if(Character.isDigit(second_operand.charAt(0)) && second_operand.charAt(0) != '0'){
                    sign2 = "+";
                }
                // operand is a negative number
                else if(second_operand.charAt(0) == '-'){
                    sign2 = "-";
                }
                // operand is 0
                else if(second_operand.charAt(0) == '0'){
                    sign2 = "0";
                }
                
                
                // cases where lhs variable is used in rhs 
                if(first_operand.equals(lhs_string)) {
                    sign1=kill_var_sign;
                }
                else if(second_operand.equals(lhs_string)) {
                    sign2=kill_var_sign;
                }
                
                // --------------comparing the operands's signs and using the operator to assign the new sign ------------------
                //operator is addition
                if(operator.equals("+")) {
                    if(sign1.equals("B") || sign2.equals("B")) {
                        final_sign = "B";
                    }
                    else if(sign1.equals("T") || sign2.equals("T")) {
                        final_sign = "T";
                    }
                    else if(sign2.equals("0")) {
                        final_sign = sign1;
                    }
                    else if(sign1.equals("0")) {
                        final_sign = sign2;
                    }
                    else if(sign1.equals("+") && sign2.equals("+")) {
                        final_sign = "+";
                    }
                    else if(sign1.equals("-") && sign2.equals("-")) {
                        final_sign = "-";
                    }
                    else {
                        final_sign = "T";
                    }
                }
                
                // operator is subtraction
                else if(operator.equals("-")) {
                    if(sign1.equals("B") || sign2.equals("B")) {
                        final_sign = "B"; 
                    }
                    else if(sign1.equals("T") || sign2.equals("T")) {
                        final_sign = "T";
                    }
                    else if((sign1.equals("+") && sign2.equals("+"))|| (sign1.equals("-") && sign2.equals("-"))) {
                        final_sign = "T";
                    }
                    else if(sign1.equals("+") || (sign1.equals("0") && sign2.equals("-"))) {
                        final_sign = "+";
                    }
                    else if(sign2.equals("+") ||(sign1.equals("-") && sign2.equals("0"))) {
                        final_sign = "-";
                    }
                    else if(sign1.equals("0") && sign2.equals("0")) {
                        final_sign = "0";
                    }
                }

                // operator is multiplication
                else if(operator.equals("*")) {
                    if(sign1.equals("B") || sign2.equals("B")) {
                        final_sign = "B";
                    }
                    else if(sign1.equals("0") || sign2.equals("0")) {
                        final_sign = "0";
                    }
                    else if(sign1.equals("T") || sign2.equals("T")) {
                        final_sign = "T";
                    }
                    else if((sign1.equals("+") && sign2.equals("-"))|| (sign1.equals("-") && sign2.equals("+"))) {
                        final_sign = "-";
                    }
                    else {
                        final_sign = "+";
                    }
                }
                
                // operator is division
                else if(operator.equals("/")) {
                    if(sign1.equals("B") || sign2.equals("B") || sign2.equals("0")) {
                        final_sign = "B";
                    }
                    else if((sign2.equals("-") || sign2.equals("+")) && sign1.equals("0")) {
                        final_sign = "0";
                    }
                    else {
                        final_sign = "T";
                    }
                }
                Pair p8 = new Pair(((AssignStmt) u).getLeftOp(), final_sign);
                outval.add(p8);
                System.out.println("gen set :"+p8);
            }
        }
        
      //--------------------Printing the outset--------------------------
        if(u instanceof AssignStmt || u instanceof IdentityStmt) {
            System.out.println("\nOutset: ");
            Iterator itOut = outval.iterator();
            while (itOut.hasNext()) {
                Pair inv = (Pair<String, String>) itOut.next();
                System.out.println(inv.toString().substring(5));
            }
            System.out.println();
        }
     // Store return variable's sign
        if(u instanceof ReturnStmt)
        {
            String ret = Arrays.asList(u.toString().split(" ",0)).get(1);
            Pair<String, String> res = iterate(outval, ret);
            String s1 = res.getO2().toString();
            func_ret_sign.put(current_method, s1);
            System.out.println("Returning from method: "+current_method);
        }
        // Find the parameter's sign for the function  
        if(u instanceof IdentityStmt)
        {
            IdentityStmt ident = (IdentityStmt)u;
            String Var = u.toString();
            String leftop = ident.getLeftOp().toString();
            Iterator itr = outval.iterator();
            while(itr.hasNext()) {
                Pair<String, String> temp = (Pair<String, String>)itr.next();
                String s1 = temp.getO1().toString();
                if(s1.equals(leftop) && Var.contains("@parameter")) {
                    int start = Var.indexOf("@parameter")+10;
                    int end = Var.indexOf(":", start);
                    int parameter_num = Integer.parseInt(Var.substring(start, end));
                    String leftopsign = func_par_sign.get(current_method).get(parameter_num);
                    Pair<String, String> p = iterate(outval, leftop);
                    p.setO2(leftopsign);
                }
            }
            System.out.println("Outval after parameter update: "+outval);
        }
    }

    @Override
    protected void copy(Object source, Object dest) {
        FlowSet srcSet = (FlowSet) source;
        FlowSet destSet = (FlowSet) dest;
        srcSet.copy(destSet);
        Iterator it = destSet.iterator();
    }

    @Override
    protected Object entryInitialFlow() {
        ArraySparseSet arr = new ArraySparseSet();
        Chain<Local> local_variables = this.b.getMethod().getActiveBody().getLocals();
        Iterator<Local> itr = local_variables.iterator();
        Pair<String, String> p=new Pair<String, String>();
        while (itr.hasNext()) {
            Local local = itr.next(); 
            String var = local.getName();
            String str = local.getType().toString();
            if(str!="int" && str!="byte") {
                var = "#" + var;
                p = new Pair<String, String>(var, "b");

            }
            else if (!((var.equals("this")))) {
               p = new Pair<String, String>(var, "T");
                    
            }
            arr.add(p);
            System.out.println("Initial pairs: " + p.toString().substring(5));
        }
        return arr;
    }

    @Override
    protected void merge(Object in1, Object in2, Object out) {
        FlowSet inval1 = (FlowSet) in1;
        FlowSet inval2 = (FlowSet) in2;
        FlowSet outSet = (FlowSet) out;
        flag=1;
        
        ArraySparseSet array_final = new ArraySparseSet();
        Dictionary dict = new Hashtable();
        Iterator iter = inval1.iterator();
        
        
        while (iter.hasNext()) {
            Pair pair = (Pair<String, String>) iter.next();
            String s1 = pair.getO1().toString();
            String s2 = pair.getO2().toString();
            dict.put(s1, s2);
        }
        Iterator iter1 = inval2.iterator();
        if(!iter1.hasNext()) {
            iter = inval1.iterator();
            while(iter.hasNext()) {
                Pair pair = (Pair<String, String>) iter.next();
                array_final.add(pair);
            }
        }
        else {
            while (iter1.hasNext()) {
                 Pair pair = (Pair<String, String>) iter1.next();
                 String s1 = pair.getO1().toString();
                 String s2 = pair.getO2().toString();
                 boolean res = dict.get(s1).equals(s2)? true: false;
                 if(res) {
                    Pair<String, String> pair1 = new Pair<String, String>(s1, s2);
                    array_final.add(pair1);
                }
                else {
                    Pair<String, String> pair1 = new Pair<String, String>(s1, "T");
                    array_final.add(pair1);
                }
            }
        }
        outSet = (FlowSet) array_final;
        merge_result = outSet;
    }

    @Override
    protected Object newInitialFlow() {
        ArraySparseSet as = new ArraySparseSet();
        return as;
    }

}

