package jolie.formatter;


import jolie.lang.parse.OLVisitor;
import jolie.lang.parse.ast.OLSyntaxNode;

import java.io.IOException;
import java.io.Writer;

/**
 * Created by nick on 4/25/16.
 */
public class Formatter {

    private Writer writer;
    private OLSyntaxNode root;

    public Formatter(Writer writer, OLSyntaxNode root) {
        this.writer = writer;
        this.root = root;
    }

    public void run() throws IOException {
        FormatterWriter formatterWriter = new FormatterWriter(writer);
        OLVisitor visitor = new FormatterVisitor(formatterWriter);

        root.accept(visitor);
        formatterWriter.flush();
    }
}
