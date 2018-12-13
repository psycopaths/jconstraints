package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;

import java.util.HashMap;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.Constants.sortInt;

public class FunctionOperatorMap {
    public static FunctionOperatorMap instance;
    public HashMap<String, Type> typeMap;

    public FunctionOperatorMap(){
        typeMap = new HashMap();
        initializeBasicTypes();
    }

    public void initializeBasicTypes(){
        typeMap.put(sortInt.toLowerCase(), BuiltinTypes.INTEGER);
    }

    private static FunctionOperatorMap getInstance(){
        if(instance == null){
            instance = new FunctionOperatorMap();
        }
        return instance;
    }

    public static Type getType(String symbol){
        return getInstance().typeMap.get(symbol.toLowerCase());
    }
}
