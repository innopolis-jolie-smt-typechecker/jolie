package jolie.typeChecker;

import jolie.lang.NativeType;

import java.io.IOException;
import java.io.Writer;
import java.util.HashSet;

public class TypeCheckerWriter {

    private Writer writer;
    private StringBuilder sb;

    private HashSet<String> declaredConsts = new HashSet<>();

    public TypeCheckerWriter(Writer writer) throws IOException {
        this.writer = writer;
        sb = new StringBuilder();
        sb.append(
                "(declare-sort Type)\n" +
                "(declare-sort Term)\n" +
                "\n" +
                "(declare-fun hasType (Term Type) Bool)\n" +
                "(declare-fun sameType (Term Term) Bool)\n" +
                "(declare-fun typeOf (Term) Type)\n" +
                "\n"
        );

        NativeType[] nativeTypes = NativeType.values();
        int nativeTypesLength = nativeTypes.length;

        String[] types = new String[nativeTypesLength];

        for (int i = 0; i < nativeTypesLength; i++) {
            NativeType type = nativeTypes[i];

            // we don't need 'any' type here, but we do need 'undefined', so just replace it
            if (!type.equals(NativeType.ANY)) {
                types[i] = type.id();
            } else {
                types[i] = "undefined";
            }
        }

        sb.append(";; Define types\n");
        for (String type : types) {
            sb.append("(declare-fun ").append(type).append(" () Type)\n");
        }
        sb.append("(declare-fun any () Type)\n"); // TODO clarify equality with other types
        sb.append("\n");

        sb.append(";; Ensure non-equality of types\n");
        for (int i = 0; i < types.length; i++) {
            for (int j = i + 1; j < types.length; j++) {
                sb.append("(assert (not (= ").append(types[i]).append(" ").append(types[j]).append(")))\n");
            }
            sb.append("\n");
        }

        sb.append(";; Describe type functions behavior\n"); // TODO maybe biconitional assertions needed?
        for (String type : types) {
            sb.append("(assert (forall ((t Term)) (= (hasType t ").append(type).append(") (= (typeOf t) ").append(type).append("))))\n");
        }

        sb.append("\n");
        sb.append("(assert (forall ((t1 Term) (t2 Term)) (= (sameType t1 t2) (= (typeOf t1) (typeOf t2)))))\n");
        sb.append("\n");

        sb.append(";; Program constraints\n");
    }

    protected void flush() throws IOException {
        writer.write(sb.toString());
        writer.write("\n(check-sat)\n");
        writer.flush();
    }

    public void write(String s) {
        sb.append(s);
    }

    public void writeLine() {
        sb.append("\n");
    }

    public void writeLine(String s) {
        sb.append(s);
        sb.append("\n");
    }

    public boolean declareTermOnce(String name) {
        if (!declaredConsts.contains(name)) {
            writeLine("(declare-const " + name + " Term)");
            declaredConsts.add(name);
            return true;
        }
        return false;
    }
}
