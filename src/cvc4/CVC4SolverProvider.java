package cvc4;

import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider;

public class CVC4SolverProvider implements ConstraintSolverProvider {

	@Override
	public String[] getNames() {
		return new String[]{"cvc4","CVC4"};
	}

	@Override
	public ConstraintSolver createSolver(Properties config) {
		 Map<String, String> options= new HashMap<>();
		 if(!config.containsKey("cvc4.options")){
			 //TODO Throw Something
		 }else {
		String conf = config.getProperty("cvc4.options").trim();
		String[] opts =conf.split(";");
		for( String o : opts){
			o=o.trim();
			if(o.length()>=1){
				String[] val= o.split("=");
				options.put(val[0].trim(), val[1].trim());
			}
		}}
		return new CVC4Solver(options);
		
	}

}
