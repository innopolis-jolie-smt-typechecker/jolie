package test.java;

import jolie.CommandLineParser;
import jolie.lang.Constants;
import jolie.lang.parse.OLParser;
import jolie.lang.parse.Scanner;
import jolie.lang.parse.ast.*;
import jolie.lang.parse.ast.courier.CourierChoiceStatement;
import jolie.lang.parse.ast.courier.CourierDefinitionNode;
import jolie.lang.parse.ast.courier.NotificationForwardStatement;
import jolie.lang.parse.ast.courier.SolicitResponseForwardStatement;
import jolie.lang.parse.ast.expression.*;
import jolie.lang.parse.ast.types.TypeChoiceDefinition;
import jolie.lang.parse.ast.types.TypeDefinition;
import jolie.lang.parse.ast.types.TypeDefinitionLink;
import jolie.lang.parse.ast.types.TypeInlineDefinition;
import jolie.lang.parse.context.ParsingContext;
import jolie.typeChecker.*;
import jolie.util.Pair;
import jolie.util.Range;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.FileWriter;
import java.io.Writer;


import static org.junit.Assert.*;

/**
 * Created by Bogdan on 20.04.2017.
 */
public class TypeCheckerVisitorTest {

    TypeChecker checker;
    StatementsContext sc;
    Writer fw;

    @Test
    public void visitTestInit() throws Exception {
        ParallelStatement statement = new ParallelStatement(sc);
        assertEquals(0, statement.children().size());
    }

    @Test
    public void visitTestProgram() {
        Program n = new Program(sc);
        for (OLSyntaxNode node : n.children()) {
            check(node);
        }
        assertEquals(true, sc.pop());
    }

    @Test
    public void visitTestParallelStatement(){
        ParallelStatement statement = new ParallelStatement(sc);
        int writtenCh = statement.children();
        for (OLSyntaxNode child : statement.children()) {
            check(child);
        }
        assertEquals(writtenCh, statement.children().size());
    }

    @Test
    public void visitTestChoice() {
        NDChoiceStatement n = new NDChoiceStatement(sc);
        for (Pair<OLSyntaxNode, OLSyntaxNode> child : n.children()) {
            check(child.key());
            check(child.value());
        }
        assertEquals(n.context(), sc);
    }

    @Test
    public void visitTestRequestResponseOperationStatement() {
        RequestResponseOperationStatement n = new RequestResponseOperationStatement(sc);
        check(n.inputVarPath());
        check(n.outputExpression());
        check(n.process());
        assertTrue(sc.contains(n.process().toString()));
    }

    @Test
    public void visitTestSolicitResponseOperationStatement() {
        SolicitResponseOperationStatement n = new SolicitResponseOperationStatement(sc);
        check(n.inputVarPath());
        check(n.outputExpression());
        check(n.handlersFunction());
        assertTrue(checker.visit(n).condition());
    }

    @Test
    public void visitTestSubtractAssignStatement() {
        SubtractAssignStatement n = new SubtractAssignStatement(sc);
        processSimilarNumericAssignments(n.variablePath(), n.expression());
        assertEquals(this.checker.visit(checker.lastToken()).container.getValue, n);
    }

    @Test
    public void visitTestMultiplyAssignStatement() {
        MultiplyAssignStatement n = new MultiplyAssignStatement(sc);
        processSimilarNumericAssignments(n.variablePath(), n.expression());
        assertEquals(this.checker.visit(checker.lastToken()).container.getValue, n);
    }

    @Test
    public void visitTestDivideAssignStatement() {
        DivideAssignStatement n = new DivideAssignStatement(sc);
        processSimilarNumericAssignments(n.variablePath(), n.expression());
        assertEquals(this.checker.visit(checker.lastToken()).container.getValue, n);
    }

    @Test
    public void visitTestIfStatement() {
        IfStatement n = new IfStatement(sc);
        for (Pair<OLSyntaxNode, OLSyntaxNode> statement : n.children()) {
            OLSyntaxNode condition = statement.key();
            OLSyntaxNode body = statement.value();

            check(condition);
            TermReference conditionTerm = termsContext.pop();
            writer.assertTypeLikeBoolean(conditionTerm.id());

            check(body);
        }

        check(n.elseProcess());

        assertNotEquals(sc.termsContext.pop(), n.children().get(n.children().size()-1));
    }

    @Test
    public void visitTestWhileStatement() {
        WhileStatement n = new WhileStatement(sc);
        OLSyntaxNode condition = n.condition();
        OLSyntaxNode body = n.body();

        check(condition);
        TermReference conditionTerm = termsContext.pop();
        writer.assertTypeLikeBoolean(conditionTerm.id());

        check(body);

        assertNotEquals(sc.termsContext.pop(), n.children().get(n.children().size()-1));
    }

    @Test
    public void visitTestNotExpressionNode() {
        NotExpressionNode n = new NotExpressionNode(sc);
        OLSyntaxNode expression = n.expression();

        check(expression);
        TermReference conditionTerm = termsContext.pop();

        String operationId = Utils.getNextTermId();

        assertEquals(n.context().NOT_EXPRESSION, conditionTerm.type());
    }

    @Test
    public void visitTestCompareConditionNode() {
        CompareConditionNode n = new CompareConditionNode(sc);
        check(n.leftExpression());
        TermReference leftExpressionTerm = termsContext.pop();
        check(n.rightExpression());
        TermReference rightExpressionTerm = termsContext.pop();

        assertEquals(leftExpressionTerm.type(), rightExpressionTerm.type());
    }

    @Test
    public void visitTestScope() {
        Scope n = new Scope(sc);
        check(n.body());
        assertEquals(n.hashCode(), this.checker.visit(checker.lastToken()).container.getValue.hashCode());
    }

    @Before
    public void setUp() throws Exception {
        String files[] = {"testing_data_set.ol"};
        CommandLineParser cmdParser = new CommandLineParser(files, null, false);
        OLParser olParser = new OLParser(new Scanner(cmdParser.programStream(), cmdParser.programFilepath().toURI(), cmdParser.charset()), cmdParser.includePaths(), cmdParser.jolieClassLoader());
        Program program = olParser.parse();
        File tempFile = new File("test_output.z3");
        fw = new FileWriter(tempFile);
        sc = new StatementsContext(program);
        checker = new jolie.typeChecker.TypeChecker(fw, program);
        checker.run();
    }

    @Test
    public void visitTestForStatement() {
        ForStatement n = new ForStatement(sc);
        OLSyntaxNode init = n.init();
        OLSyntaxNode condition = n.condition();
        OLSyntaxNode post = n.post();
        OLSyntaxNode body = n.body();

        check(init);

        check(condition);
        TermReference conditionTerm = termsContext.pop();

        check(post);
        check(body);

        assertNotEquals(sc.termsContext.pop(), n.children().get(n.children().size()-1));
    }

    @Test
    public void visitTestForEachSubNodeStatement() {
        ForEachSubNodeStatement n = new ForEachSubNodeStatement(sc);
        OLSyntaxNode keyPath = n.keyPath();
        OLSyntaxNode targetPath = n.targetPath();
        OLSyntaxNode body = n.body();

        check(keyPath);
        check(targetPath);
        check(body);


        assertNotEquals(sc.termsContext.pop(), n.children().get(n.children().size()-1));
    }

    @Test
    public void visitTestTypeDefinitionLink() {
        TypeDefinitionLink n = new TypeDefinitionLink(sc);
        check(n.linkedType());
        assertEquals(sc, n.linkedType().context());
    }

}