package jolie.typeChecker;

/**
 * Created by Timur on 19.07.2016.
 */

import jolie.lang.parse.OLVisitor;
import jolie.lang.parse.ast.OLSyntaxNode;

import java.io.IOException;
import java.io.Writer;

public class TypeChecker {

    private Writer writer;
    private OLSyntaxNode root;

    public TypeChecker(Writer writer, OLSyntaxNode root) {
        this.writer = writer;
        this.root = root;
    }

    public void run() throws IOException {
        TypeCheckerWriter typeCheckerWriter = new TypeCheckerWriter(writer);
        OLVisitor visitor = new TypeCheckerVisitor(typeCheckerWriter);

        root.accept(visitor);
        typeCheckerWriter.flush();
    }
}
