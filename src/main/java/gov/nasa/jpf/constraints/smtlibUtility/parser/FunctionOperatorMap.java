package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;

import java.util.HashMap;

/**
 * The same function operators are slightly named differently in jConstraints
 * and SMT-LIB due to historic reasons.
 * While jConstraints use function operators closer to programming languages
 * SMT-LIB uses them in the mathematical sense.
 *
 * @Author Malte Mues
 */
public class FunctionOperatorMap {
    public static FunctionOperatorMap instance;
    public HashMap<String, String> typeMap;

    public FunctionOperatorMap(){
        typeMap = new HashMap();
        initializeBasicTypes();
    }

    public void initializeBasicTypes(){
        typeMap.put("=", "==");
        typeMap.put("and", "&&");
        typeMap.put("or", "||");
    }

    private static FunctionOperatorMap getInstance(){
        if(instance == null){
            instance = new FunctionOperatorMap();
        }
        return instance;
    }

    public static String getjConstraintOperatorName(String symbol){
        return getInstance().typeMap.getOrDefault(symbol.toLowerCase(), symbol);
    }
}
