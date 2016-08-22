package jolie.typeChecker;

import java.io.IOException;
import java.io.Writer;

/**
 * Created by Timur on 19.07.2016.
 */
public class TypeCheckerWriter {

    private Writer writer;
    private StringBuilder sb;

    public TypeCheckerWriter(Writer writer) throws IOException {
        this.writer = writer;
        sb = new StringBuilder();
        sb.append("(declare-sort Type)\n" +
                "(declare-sort Term)\n" +
                "(declare-sort Long)\n" +
                "(declare-sort Raw)\n" +
                "(declare-sort Void)\n" +
                "(declare-sort Any)\n" +
                "(declare-sort Undefined)\n" +
                "(declare-fun hasType (Term Type) Bool)\n" +
                "\n" +
                "(declare-fun int () Type)\n" +
                "(declare-fun real () Type)\n" +
                "(declare-fun long () Type)\n" +
                "(declare-fun bool () Type)\n" +
                "(declare-fun string () Type)\n" +
                "(declare-fun raw () Type)\n" +
                "(declare-fun void () Type)\n" +
                "(declare-fun any () Type)\n" +
                "(declare-fun undefined () Type)");
        this.flush();
    }

    protected void flush() throws IOException {
        writer.write(sb.toString());
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
}
