package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.types.BuiltinTypes;
import gov.nasa.jpf.constraints.types.Type;
import org.smtlib.sexpr.Lexer;

import java.util.HashMap;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.Constants.SORT_INT;
import static gov.nasa.jpf.constraints.smtlibUtility.parser.Constants.SORT_BOOL;
import static gov.nasa.jpf.constraints.smtlibUtility.parser.Constants.SORT_REAL;
import static gov.nasa.jpf.constraints.smtlibUtility.parser.Constants.SORT_STRING;

public class TypeMap {
    public static TypeMap instance;
    public HashMap<String, Type> typeMap;

    public TypeMap(){
        typeMap = new HashMap();
        initializeBasicTypes();
    }

    public void initializeBasicTypes(){
        typeMap.put(SORT_INT.toLowerCase(), BuiltinTypes.INTEGER);
        typeMap.put(SORT_BOOL.toLowerCase(), BuiltinTypes.BOOL);
        typeMap.put(SORT_REAL.toLowerCase(), BuiltinTypes.DECIMAL);
        typeMap.put(SORT_STRING.toLowerCase(),BuiltinTypes.STRING);
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
