package jolie;

import jolie.lang.parse.OLParser;
import jolie.lang.parse.ParserException;
import jolie.lang.parse.Scanner;
import jolie.lang.parse.ast.Program;
import jolie.typeChecker.TypeChecker;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;

public class StaticTypeChecker {
    public static void main(String[] args) throws CommandLineException, IOException, ParserException {
        CommandLineParser cmdParser = new CommandLineParser(args, null, false);

        OLParser olParser = new OLParser(new Scanner(cmdParser.programStream(), cmdParser.programFilepath().toURI(), cmdParser.charset()), cmdParser.includePaths(), cmdParser.jolieClassLoader());

        Program program = olParser.parse();

        File tempFile = new File("checker.z3");
        Writer fw = new FileWriter(tempFile);
        TypeChecker checker = new jolie.typeChecker.TypeChecker(fw, program);
        checker.run();
    }
}
