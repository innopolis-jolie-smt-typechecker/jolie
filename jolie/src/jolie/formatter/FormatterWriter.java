package jolie.formatter;

import java.io.IOException;
import java.io.Writer;

/**
 * Created by nick on 5/2/16.
 */
public class FormatterWriter {

    private Writer writer;
    private int indentation = 0;
    private StringBuilder sb;
    private boolean shouldPrintQuotes;

    public FormatterWriter(Writer writer) {
        this.writer = writer;
        sb = new StringBuilder();
        shouldPrintQuotes = true;
    }

    public int getIndentation() {
        return indentation;
    }

    public void setPrintQuotes(boolean shouldPrintQuotes) {
        this.shouldPrintQuotes = shouldPrintQuotes;
    }

    public boolean shouldPrintQuotes() {
        return shouldPrintQuotes;
    }

    protected void setIndentation(int indentation) {
        if (indentation < 0) {
            throw new IllegalArgumentException();
        }

        this.indentation = indentation;
    }

    protected void flush() throws IOException {
        writer.write(sb.toString());
        writer.flush();
    }

    public void write(String s) {
        sb.append(s);
    }

    public void writeLineIndented(String s) {
        for (int i = 0; i < indentation; i++) {
            sb.append("\t");
        }
        sb.append(s);
        sb.append("\n");
    }

    public void writeIndented(String s) {
        for (int i = 0; i < indentation; i++) {
            sb.append("\t");
        }
        sb.append(s);
    }

    public void indent() {
        indentation++;
    }

    public void unindent() {
        indentation--;
    }

    public void writeLine() {
        sb.append("\n");
    }

    public void writeLine(String s) {
        sb.append(s);
        sb.append("\n");
    }
}
