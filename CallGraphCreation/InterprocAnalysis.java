package CallGraphCreation;


import java.util.*;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import soot.*;
import soot.options.*;
import soot.tagkit.LineNumberTag;
import soot.tagkit.Tag;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.*;
import soot.baf.*;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.CHATransformer;
import soot.jimple.toolkits.callgraph.CallGraph;

public class InterprocAnalysis {
	
	//summaries accessible to my intra class for updation and access
	static HashMap<SootMethod, ArrayList<String>> func_par_sign;
	static HashMap<SootMethod, String> func_ret_sign;
	public InterprocAnalysis()
	{
		//initialize summary
		
	}
	public static void main(String[] args) {
		//* initializing the summary hashtable.
		func_ret_sign = new HashMap<>();
		func_par_sign = new HashMap<>();
		
		System.out.println("***----------------starting-analysis----------------***");
		
		//* taking class name to be analyzed as command line argument input.
		final String classname=args[0];//"CallGraphCreation.Sample_test";//args[0]; //class whose main method would be analysed
		
		//* don't understand.
		Options.v().set_keep_line_number(true);
    	Options.v().setPhaseOption("jb", "use-original-names:true");
    	List<String> argsList = new ArrayList<String>(Arrays.asList(args));
 	   argsList.addAll(Arrays.asList(new String[]{
 			   "-w","-no-bodies-for-excluded",
 			   "-main-class",   
 			   classname,//main-class
 			   classname//"CallGraphCreation.Sample_test"//argument classes
 	   }));
 	
 	   //* don't understand.
 	   //To perform transformation on whole application(interprocedural)
 	   PackManager.v().getPack("wjtp").add(new Transform("wjtp.myTrans", new SceneTransformer() {
 		  @Override
 			protected void internalTransform(String phaseName, Map options) {
 			       CHATransformer.v().transform();
 	               SootClass a = Scene.v().getSootClass(classname);
 	               SootMethod src = Scene.v().getMainClass().getMethodByName("main");    //root of cg
 			       CallGraph cg = Scene.v().getCallGraph();   //call graph generated
 			       Stack<SootMethod> stack=new CallGraphBuilder().obtaincallgraph(cg,src);	 //call graph sorted topologically
 			       if(stack.peek().getName().contains("init")) {
 			    	   stack.pop(); //to eliminate some init method
 			       }
 			  
 			}   
 		   }));
 	    PackManager.v().getPack("jtp").add(new Transform("jtp.instrumenter", new BodyTransformer()
 	    {
			protected void internalTransform(Body body, String phase, Map options)
			{		
				if(body.getMethod().getName().equals("main"))
				{
					SootMethod soot_method=body.getMethod();
					InterSign analysis = new InterSign((new ExceptionalUnitGraph(body)),soot_method,func_ret_sign,func_par_sign);
				}			
			}
	    }));
 	    
 	args = argsList.toArray(new String[0]);
	Options.v().set_output_format(Options.output_format_jimple);
    
    String path = Scene.v().getSootClassPath();
    System.out.println("\npath:" + path + "\n");
	Scene.v().setSootClassPath(path);
	
	soot.Main.main(args);
    }
}
