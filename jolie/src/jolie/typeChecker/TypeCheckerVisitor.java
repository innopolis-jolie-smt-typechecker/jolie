package jolie.typeChecker;

/**
 * Created by Timur on 19.07.2016.
 */

import jolie.lang.Constants;
import jolie.lang.parse.OLVisitor;
import jolie.lang.parse.Scanner;
import jolie.lang.parse.ast.*;
import jolie.lang.parse.ast.courier.CourierChoiceStatement;
import jolie.lang.parse.ast.courier.CourierDefinitionNode;
import jolie.lang.parse.ast.courier.NotificationForwardStatement;
import jolie.lang.parse.ast.courier.SolicitResponseForwardStatement;
import jolie.lang.parse.ast.expression.*;
import jolie.lang.parse.ast.types.TypeChoiceDefinition;
import jolie.lang.parse.ast.types.TypeDefinitionLink;
import jolie.lang.parse.ast.types.TypeInlineDefinition;
import jolie.util.Pair;
import jolie.util.Range;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.Stack;

public class TypeCheckerVisitor implements OLVisitor {
    private Integer nextConstId = 0;
    private TypeCheckerWriter writer;
    private Stack<TermReference> usedTerms = new Stack<>();

    public TypeCheckerVisitor(TypeCheckerWriter writer) {
        this.writer = writer;
    }

    private String getNextTermId() {
        String id = "$$__term_id_" + nextConstId.toString();
        nextConstId++;
        return id;
    }

    private void check(OLSyntaxNode node) {
        if (node != null) {
            node.accept(this);
        }
    }

    private void check(Scanner.TokenType tokenType) {

    }

    @Override
    public void visit(Program n) {
        for (OLSyntaxNode node : n.children()) {
            check(node);
        }
    }

    @Override
    public void visit(OneWayOperationDeclaration decl) {
        writer.writeLine("(assert (forall ((i Undefined))(hasType (boxUndefined i) undefined)))");
    }

    @Override
    public void visit(RequestResponseOperationDeclaration decl) {

    }

    @Override
    public void visit(DefinitionNode n) {
        if (!n.id().equals("main") && !n.id().equals("init")) {
            writer.write("(assert (forall ((i Void))(hasType (boxVoid i) void)))");
        }
        n.body().accept(this);
    }

    @Override
    public void visit(ParallelStatement n) {
        n.children().forEach(this::check);
    }

    @Override
    public void visit(SequenceStatement n) {
        n.children().forEach(this::check);
    }

    @Override
    public void visit(NDChoiceStatement n) {
    }

    @Override
    public void visit(OneWayOperationStatement n) {
    }

    @Override
    public void visit(RequestResponseOperationStatement n) {
    }

    @Override
    public void visit(NotificationOperationStatement n) {
    }

    @Override
    public void visit(SolicitResponseOperationStatement n) {
    }

    @Override
    public void visit(LinkInStatement n) {

    }

    @Override
    public void visit(LinkOutStatement n) {

    }

    @Override
    public void visit(AssignStatement n) {
        String variablePath = n.variablePath().toPrettyString();
        writer.declareTermOnce(variablePath);

        check(n.expression());
        TermReference expressionTerm = usedTerms.pop();

        String formula = "(assert (sameType " + variablePath + " " + expressionTerm.id + "))\n";
        switch (expressionTerm.type) {
            case BOOL:
                formula += "(assert (hasType " + variablePath + " bool))\n";
                break;
            case INT:
                formula += "(assert (hasType " + variablePath + " int))\n";
                break;
            case LONG:
                formula += "(assert (hasType " + variablePath + " long))\n";
                break;
            case DOUBLE:
                formula += "(assert (hasType " + variablePath + " double))\n";
                break;
            case STRING:
                formula += "(assert (hasType " + variablePath + " string))\n";
                break;
            case VAR:
                break;
        }
        writer.write(formula);

        String statementId = getNextTermId();
        writer.declareTermOnce(statementId);
        usedTerms.push(new TermReference(statementId, expressionTerm.type));
    }

    @Override
    public void visit(AddAssignStatement n) {
    }

    @Override
    public void visit(SubtractAssignStatement n) {
    }

    @Override
    public void visit(MultiplyAssignStatement n) {
    }

    @Override
    public void visit(DivideAssignStatement n) {
    }

    @Override
    public void visit(IfStatement n) {
        for (Pair<OLSyntaxNode, OLSyntaxNode> statement : n.children()) {
            OLSyntaxNode condition = statement.key();
            OLSyntaxNode body = statement.value();

            check(condition);
            TermReference conditionTerm = usedTerms.pop();
            writer.writeLine("(assert (hasType " + conditionTerm.id + " bool))");

            if (body != null) {
                body.accept(this);
            }
        }
        if (n.elseProcess() != null) {
            n.elseProcess().accept(this);
        }
    }

    @Override
    public void visit(DefinitionCallStatement n) {

    }

    @Override
    public void visit(WhileStatement n) {
        OLSyntaxNode condition = n.condition();
        OLSyntaxNode body = n.body();

        check(condition);
        TermReference conditionTerm = usedTerms.pop();
        writer.writeLine("(assert (hasType " + conditionTerm.id + " bool))");

        if (body != null) {
            body.accept(this);
        }
    }

    @Override
    public void visit(OrConditionNode n) {
        int childrenSize = n.children().size();
        LinkedList<TermReference> refs = new LinkedList<>();

        for (int i = 0; i < childrenSize; i++) {
            check(n.children().get(i));
            refs.add(usedTerms.pop());
        }

        processLogicalExpression(refs);
    }

    @Override
    public void visit(AndConditionNode n) {
        int childrenSize = n.children().size();
        LinkedList<TermReference> refs = new LinkedList<>();

        for (int i = 0; i < childrenSize; i++) {
            check(n.children().get(i));
            refs.add(usedTerms.pop());
        }

        processLogicalExpression(refs);
    }

    private void processLogicalExpression(LinkedList<TermReference> refs) {
        JolieTermType expressionType;

        if (refs.size() == 1) {
            expressionType = refs.getFirst().type;
        } else { // then we assume for now that it should be a boolean expression. In actual programs it can be wrong. Just to start with.
            // TODO process not-boolean constructions
            expressionType = JolieTermType.BOOL;
            StringBuilder sb = new StringBuilder();
            sb.append("(assert (= ");
            for (TermReference ref : refs) {
                sb.append("(typeOf ").append(ref.id).append(")").append(" ");
            }
            sb.append("bool))");
            writer.writeLine(sb.toString());
        }

        String operationId = getNextTermId();
        writer.declareTermOnce(operationId);

        String formula = "";
        switch (expressionType) {
            case BOOL:
                formula += "(assert (hasType " + operationId + " bool))\n";
                break;
            case INT:
                formula += "(assert (hasType " + operationId + " int))\n";
                break;
            case LONG:
                formula += "(assert (hasType " + operationId + " long))\n";
                break;
            case DOUBLE:
                formula += "(assert (hasType " + operationId + " double))\n";
                break;
            case STRING:
                formula += "(assert (hasType " + operationId + " string))\n";
                break;
            case VAR:
                break;
        }
        writer.writeLine(formula);

        usedTerms.push(new TermReference(operationId, expressionType));
    }

    @Override
    public void visit(NotExpressionNode n) {
        OLSyntaxNode expression = n.expression();

        check(expression);
        TermReference conditionTerm = usedTerms.pop();
        writer.writeLine("(assert (hasType " + conditionTerm.id + " bool))");

        String operationId = getNextTermId();
        writer.declareTermOnce(operationId);
        usedTerms.push(new TermReference(operationId, JolieTermType.BOOL));
    }

    @Override
    public void visit(CompareConditionNode n) {
        check(n.leftExpression());
        TermReference leftExpressionTerm = usedTerms.pop();
        check(n.rightExpression());
        TermReference rightExpressionTerm = usedTerms.pop();

        writer.writeLine("(assert (sameType " + leftExpressionTerm.id + " " + rightExpressionTerm.id + "))");

        String operationId = getNextTermId();
        writer.declareTermOnce(operationId);
        usedTerms.push(new TermReference(operationId, JolieTermType.BOOL));
    }

    @Override
    public void visit(ConstantIntegerExpression n) {
        String constId = getNextTermId();
        writer.declareTermOnce(constId);
        writer.writeLine("(assert (hasType " + constId + " int))");
        usedTerms.push(new TermReference(constId, JolieTermType.INT));
    }

    @Override
    public void visit(ConstantDoubleExpression n) {
        String constId = getNextTermId();
        writer.declareTermOnce(constId);
        writer.writeLine("(assert (hasType " + constId + " double))");
        usedTerms.push(new TermReference(constId, JolieTermType.DOUBLE));
    }

    @Override
    public void visit(ConstantBoolExpression n) {
        String constId = getNextTermId();
        writer.declareTermOnce(constId);
        writer.writeLine("(assert (hasType " + constId + " bool))");
        usedTerms.push(new TermReference(constId, JolieTermType.BOOL));
    }

    @Override
    public void visit(ConstantLongExpression n) {
        String constId = getNextTermId();
        writer.declareTermOnce(constId);
        writer.writeLine("(assert (hasType " + constId + " long))");
        usedTerms.push(new TermReference(constId, JolieTermType.LONG));
    }

    @Override
    public void visit(ConstantStringExpression n) {
        String constId = getNextTermId();
        writer.declareTermOnce(constId);
        writer.writeLine("(assert (hasType " + constId + " string))");
        usedTerms.push(new TermReference(constId, JolieTermType.STRING));
    }

    @Override
    public void visit(ProductExpressionNode n) {
        Pair<Constants.OperandType, OLSyntaxNode> pair;
        Iterator<Pair<Constants.OperandType, OLSyntaxNode>> it =
                n.operands().iterator();
        for (int i = 0; i < n.operands().size(); i++) {
            pair = it.next();
            if (i > 0) {
                switch (pair.key()) {
                    case MULTIPLY:
//                        writer.write(" * ");
                        break;
                    case DIVIDE:
//                        writer.write(" / ");
                        break;
                    case MODULUS:
//                        writer.write(" % ");
                        break;
                    default:
                        break;
                }
                //if (pair.key() == Constants.OperandType.ADD) {
                //   writer.write(" + ");
                //} else {
                //   writer.write(" - ");
                //}
            }
            check(pair.value());
        }
    }

    @Override
    public void visit(SumExpressionNode n) {
        Pair<Constants.OperandType, OLSyntaxNode> pair;
        Iterator<Pair<Constants.OperandType, OLSyntaxNode>> it = n.operands().iterator();
        for (int i = 0; i < n.operands().size(); i++) {
            pair = it.next();
            if (i > 0) {
                if (pair.key() == Constants.OperandType.ADD) {
//                    writer.write(" + ");
                } else {
//                    writer.write(" - ");
                }
            }
            check(pair.value());
        }
    }

    @Override
    public void visit(VariableExpressionNode n) {
        check(n.variablePath());
    }

    @Override
    public void visit(NullProcessStatement n) {

    }

    @Override
    public void visit(Scope n) {
    }

    @Override
    public void visit(InstallStatement n) {

    }

    @Override
    public void visit(CompensateStatement n) {

    }

    @Override
    public void visit(ThrowStatement n) {

    }

    @Override
    public void visit(ExitStatement n) {

    }

    @Override
    public void visit(ExecutionInfo n) {
    }

    @Override
    public void visit(CorrelationSetInfo n) {
    }

    @Override
    public void visit(InputPortInfo n) {
    }

    @Override
    public void visit(OutputPortInfo n) {
    }

    @Override
    public void visit(PointerStatement n) {
    }

    @Override
    public void visit(DeepCopyStatement n) {
    }

    @Override
    public void visit(RunStatement n) {

    }

    @Override
    public void visit(UndefStatement n) {
    }

    @Override
    public void visit(ValueVectorSizeExpressionNode n) {
        writer.write("#");
        check(n.variablePath());
    }

    @Override
    public void visit(PreIncrementStatement n) {
    }

    @Override
    public void visit(PostIncrementStatement n) {
    }

    @Override
    public void visit(PreDecrementStatement n) {
    }

    @Override
    public void visit(PostDecrementStatement n) {
    }

    @Override
    public void visit(ForStatement n) {
    }

    @Override
    public void visit(ForEachStatement n) {
    }

    @Override
    public void visit(SpawnStatement n) {

    }

    @Override
    public void visit(IsTypeExpressionNode n) {
        if (n.type() == IsTypeExpressionNode.CheckType.DEFINED) {
            writer.write("is_defined(");
            check(n.variablePath());
            writer.write(")");
        }
    }

    @Override
    public void visit(InstanceOfExpressionNode n) {
        if (n.expression() instanceof AssignStatement) {
            writer.write("(");
            check(((AssignStatement) n.expression()).variablePath());
            writer.write(" = ");
            check(((AssignStatement) n.expression()).expression());
            writer.write(")");
        } else {
            check(n.expression());
        }
        writer.write(" instanceof ");
        writer.write(n.type().id());
    }

    @Override
    public void visit(TypeCastExpressionNode n) {
        writer.write(n.type().id());
        writer.write("(");
        check(n.expression());
        writer.write(")");
    }

    @Override
    public void visit(SynchronizedStatement n) {
    }

    @Override
    public void visit(CurrentHandlerStatement n) {

    }

    @Override
    public void visit(EmbeddedServiceNode n) {

    }

    @Override
    public void visit(InstallFixedVariableExpressionNode n) {

    }

    @Override
    public void visit(VariablePathNode n) {
        usedTerms.push(new TermReference(n.toPrettyString(), JolieTermType.VAR));
    }

    @Override
    public void visit(TypeInlineDefinition n) {
    }

    public void check(Range r) {
        if (r.min() == r.max() && r.min() == 1) {
            return;
        }

        if (r.min() == 0 && r.max() == 1) {
            writer.write("?");
        } else if (r.min() == 0 && r.max() == Integer.MAX_VALUE) {
            writer.write("*");
        } else if (r.max() == Integer.MAX_VALUE) {
            writer.write("[" + r.min() + ", " + "*]");
        } else {
            writer.write("[" + r.min() + ", " + r.max() + "]");
        }
    }

    @Override
    public void visit(TypeDefinitionLink n) {

    }

    @Override
    public void visit(InterfaceDefinition n) {
    }

    @Override
    public void visit(DocumentationComment n) {

    }

    @Override
    public void visit(FreshValueExpressionNode n) {
        writer.write("new");
    }

    @Override
    public void visit(CourierDefinitionNode n) {

    }

    @Override
    public void visit(CourierChoiceStatement n) {

    }

    @Override
    public void visit(NotificationForwardStatement n) {

    }

    @Override
    public void visit(SolicitResponseForwardStatement n) {

    }

    @Override
    public void visit(InterfaceExtenderDefinition n) {

    }

    @Override
    public void visit(InlineTreeExpressionNode n) {

    }

    @Override
    public void visit(VoidExpressionNode n) {

    }

    @Override
    public void visit(ProvideUntilStatement n) {

    }

    @Override
    public void visit(TypeChoiceDefinition n) {

    }

    private enum JolieTermType {
        STRING, INT, LONG, BOOL, DOUBLE, VAR
    }

    private class TermReference {
        public String id;
        public JolieTermType type;

        TermReference(String id, JolieTermType type) {
            this.id = id;
            this.type = type;
        }
    }
}
