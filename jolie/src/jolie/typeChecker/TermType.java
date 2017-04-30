package jolie.typeChecker;

import jolie.lang.NativeType;

import java.util.HashMap;
import java.util.Map;

public enum TermType {
    STRING(NativeType.STRING.id()),
    INT(NativeType.INT.id()),
    LONG(NativeType.LONG.id()),
    BOOL(NativeType.BOOL.id()),
    DOUBLE(NativeType.DOUBLE.id()),
    VOID(NativeType.VOID.id()),
    VAR("var");

    private final static Map<String, TermType> idMap = new HashMap<>();

    static {
        for (TermType type : TermType.values()) {
            idMap.put(type.id(), type);
        }
    }

    private final String id;

    TermType(String id) {
        this.id = id;
    }

    public String id() {
        return id;
    }

    public static TermType fromString(String id) {
        return idMap.get(id);
    }

    public static boolean isMeaningful(TermType type) {
        return type.equals(STRING) ||
                type.equals(INT) ||
                type.equals(LONG) ||
                type.equals(BOOL) ||
                type.equals(DOUBLE);
    }
}
