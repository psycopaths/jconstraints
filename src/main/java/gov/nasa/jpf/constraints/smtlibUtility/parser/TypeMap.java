package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import org.smtlib.sexpr.Lexer;

import java.util.HashMap;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.Constants.sortInt;

public class TypeMap {
    public static TypeMap instance;
    public HashMap<String, Type> typeMap;

    public TypeMap(){
        typeMap = new HashMap();
        initializeBasicTypes();
    }

    public void initializeBasicTypes(){
        typeMap.put(sortInt.toLowerCase(), BuiltinTypes.INTEGER);
    }

    private static TypeMap getInstance(){
        if(instance == null){
            instance = new TypeMap();
        }
        return instance;
    }

    public static <E> Type<E> getType(String symbol){
        return getInstance().typeMap.get(symbol.toLowerCase());
    }

}
