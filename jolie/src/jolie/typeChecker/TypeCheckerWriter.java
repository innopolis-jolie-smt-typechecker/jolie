package jolie.typeChecker;

import java.io.IOException;
import java.io.Writer;
import java.util.HashSet;

/**
 * Created by Timur on 19.07.2016.
 */
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

        String[] types = {"bool", "int", "long", "double", "string", "raw", "void", "undefined"};

        sb.append(";; Define types\n");
        for (int i = 0; i < types.length; i++) {
            sb.append("(declare-fun " + types[i] + " () Type)\n");
        }
        sb.append("(declare-fun any () Type)\n"); // TODO clarify equality with other types
        sb.append("\n");

        sb.append(";; Ensure non-equality of types\n");
        for (int i = 0; i < types.length; i++) {
            for (int j = i + 1; j < types.length; j++) {
                sb.append("(assert (not (= " + types[i] + " " + types[j] + ")))\n");
            }
            sb.append("\n");
        }

        sb.append(";; Describe type functions behavior\n");
        for (int i = 0; i < types.length; i++) {
            sb.append("(assert (forall ((t Term)) (=> (hasType t " + types[i] + ") (= (typeOf t) " + types[i] + "))))\n");
        }

        sb.append("\n");
        sb.append("(assert (forall ((t1 Term) (t2 Term)) (=> (sameType t1 t2) (= (typeOf t1) (typeOf t2)))))\n");
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
