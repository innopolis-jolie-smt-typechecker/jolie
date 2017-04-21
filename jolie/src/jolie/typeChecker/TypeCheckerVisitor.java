package jolie.typeChecker;

import jolie.lang.Constants;
import jolie.lang.NativeType;
import jolie.lang.parse.OLVisitor;
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
import jolie.util.Pair;
import jolie.util.Range;

import java.util.*;

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

    }

    @Override
    public void visit(RequestResponseOperationDeclaration decl) {

    }

    @Override
    public void visit(DefinitionNode n) {
        if (!n.id().equals("main") && !n.id().equals("init")) {

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
        processSimilarAssignments(n.variablePath(), n.expression());
    }

    @Override
    public void visit(AddAssignStatement n) {
        processSimilarAssignments(n.variablePath(), n.expression());
    }

    private void processSimilarAssignments(VariablePathNode variablePath, OLSyntaxNode expression) {
        check(variablePath);
        TermReference variablePathTerm = usedTerms.pop();

        check(expression);
        TermReference expressionTerm = usedTerms.pop();

        String formula = "(assert (sameType " + variablePathTerm.id + " " + expressionTerm.id + "))\n";
        if (JolieTermType.isMeaningfulType(expressionTerm.type)) {
            formula += "(assert (hasType " + variablePathTerm.id + " " + expressionTerm.type.id() + "))\n";
        }
        writer.write(formula);

        String statementId = getNextTermId();
        writer.declareTermOnce(statementId);
        usedTerms.push(new TermReference(statementId, expressionTerm.type));
    }

    @Override
    public void visit(SubtractAssignStatement n) {
        processSimilarNumericAssignments(n.variablePath(), n.expression());
    }

    @Override
    public void visit(MultiplyAssignStatement n) {
        processSimilarNumericAssignments(n.variablePath(), n.expression());
    }

    @Override
    public void visit(DivideAssignStatement n) {
        processSimilarNumericAssignments(n.variablePath(), n.expression());
    }

    private void processSimilarNumericAssignments(VariablePathNode variablePath, OLSyntaxNode expression) {
        check(variablePath);
        TermReference variablePathTerm = usedTerms.pop();

        check(expression);
        TermReference expressionTerm = usedTerms.pop();

        String formula = "(assert (sameType " + variablePathTerm.id + " " + expressionTerm.id + "))\n";
        formula += assertTypeNumber(variablePathTerm);
        writer.write(formula);

        String statementId = getNextTermId();
        writer.declareTermOnce(statementId);
        usedTerms.push(new TermReference(statementId, expressionTerm.type));
    }

    @Override
    public void visit(IfStatement n) {
        for (Pair<OLSyntaxNode, OLSyntaxNode> statement : n.children()) {
            OLSyntaxNode condition = statement.key();
            OLSyntaxNode body = statement.value();

            check(condition);
            TermReference conditionTerm = usedTerms.pop();
            writer.writeLine(assertTypeLikeBoolean(conditionTerm));

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
        writer.writeLine(assertTypeLikeBoolean(conditionTerm));

        if (body != null) {
            body.accept(this);
        }
    }

    @Override
    public void visit(OrConditionNode n) {
        processLogicalExpression(n.children());
    }

    @Override
    public void visit(AndConditionNode n) {
        processLogicalExpression(n.children());
    }

    private void processLogicalExpression(List<OLSyntaxNode> children) {
        LinkedList<TermReference> refs = new LinkedList<>();

        for (OLSyntaxNode child : children) {
            check(child);
            refs.add(usedTerms.pop());
        }

        JolieTermType expressionType;
        String operationId = getNextTermId();

        if (refs.size() == 1) {
            TermReference ref = refs.getFirst();
            expressionType = ref.type;
            if (expressionType.equals(JolieTermType.VAR)) {
                operationId = ref.id;
            }
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

        writer.declareTermOnce(operationId);

        if (JolieTermType.isMeaningfulType(expressionType)) {
            writer.writeLine("(assert (hasType " + operationId + " " + expressionType.id() + "))");
        }

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
        processArithmetic(n.operands());
    }

    @Override
    public void visit(SumExpressionNode n) {
        processArithmetic(n.operands());
    }

    private void processArithmetic(List<Pair<Constants.OperandType, OLSyntaxNode>> operands) {
        LinkedList<TermReference> refs = new LinkedList<>();

        for (Pair<Constants.OperandType, OLSyntaxNode> pair : operands) {
            check(pair.value());
            refs.add(usedTerms.pop());
        }

        TermReference firstRef = refs.getFirst();
        JolieTermType expressionType = firstRef.type;
        String operationId = getNextTermId();

        if (refs.size() == 1) { // if it is a constant or a variable, leave it be
            if (expressionType.equals(JolieTermType.VAR)) {
                operationId = firstRef.id;
            }
        } else { // else assume that every operand should be the same type as the first one
            // TODO make type numeric? we can add int to long
            StringBuilder sb = new StringBuilder();
            sb.append("(assert (= ");
            for (TermReference ref : refs) {
                sb.append("(typeOf ").append(ref.id).append(")").append(" ");
            }
            sb.append("))");
            writer.writeLine(sb.toString());
        }

        writer.declareTermOnce(operationId);

        if (JolieTermType.isMeaningfulType(expressionType)) {
            writer.writeLine("(assert (hasType " + operationId + " " + expressionType.id() + "))");
        } else if (!operationId.equals(firstRef.id)) {
            writer.writeLine("(assert (sameType " + operationId + " " + firstRef.id + "))");
        }

        usedTerms.push(new TermReference(operationId, expressionType));
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
        String termId = getNextTermId();

        writer.declareTermOnce(termId);

        check(n.variablePath());

        // we assume that size of vector is Integer
        // However, maybe we need to handle it as some kind of 'numeric' type and allow the precise type
        // to be specified later (or before)
        // TODO decide on 'numeric' type
        TermReference termRef = new TermReference(termId, JolieTermType.INT);

        writer.writeLine("(assert (hasType " + termId + " " + termRef.type.id() + "))");

        usedTerms.push(termRef);
    }

    @Override
    public void visit(PreIncrementStatement n) {
        processIncDec(n.variablePath());
    }

    @Override
    public void visit(PostIncrementStatement n) {
        processIncDec(n.variablePath());
    }

    @Override
    public void visit(PreDecrementStatement n) {
        processIncDec(n.variablePath());
    }

    @Override
    public void visit(PostDecrementStatement n) {
        processIncDec(n.variablePath());
    }

    private void processIncDec(VariablePathNode variablePath) {
        check(variablePath);
        TermReference variablePathTerm = usedTerms.pop();

        writer.write(assertTypeNumber(variablePathTerm));

        String statementId = getNextTermId();
        writer.declareTermOnce(statementId);
        usedTerms.push(new TermReference(statementId, variablePathTerm.type));
    }

    @Override
    public void visit(ForStatement n) {
        OLSyntaxNode init = n.init();
        OLSyntaxNode condition = n.condition();
        OLSyntaxNode post = n.post();
        OLSyntaxNode body = n.body();

        check(init);

        check(condition);
        TermReference conditionTerm = usedTerms.pop();
        writer.writeLine(assertTypeLikeBoolean(conditionTerm));

        check(post);

        if (body != null) {
            body.accept(this);
        }
    }

    @Override
    public void visit(ForEachSubNodeStatement n) {
    }

    @Override
    public void visit(ForEachArrayItemStatement n) {
        OLSyntaxNode keyPath = n.keyPath();
        OLSyntaxNode targetPath = n.targetPath();
        OLSyntaxNode body = n.body();

        check(keyPath);
        TermReference keyTerm = usedTerms.pop();

        check(targetPath);
        TermReference targetTerm = usedTerms.pop();

        writer.writeLine("(assert (sameType " + keyTerm.id + " " + targetTerm.id + "))");

        if (body != null) {
            body.accept(this);
        }
    }

    @Override
    public void visit(SpawnStatement n) {

    }

    @Override
    public void visit(IsTypeExpressionNode n) {
        TermReference newTerm = new TermReference(getNextTermId(), JolieTermType.BOOL);

        writer.declareTermOnce(newTerm.id);
        writer.writeLine("(assert (hasType " + newTerm.id + " " + newTerm.type.id() + "))");

        check(n.variablePath());

        usedTerms.push(newTerm);
    }

    @Override
    public void visit(InstanceOfExpressionNode n) {
        String termId = getNextTermId();
        JolieTermType termType = JolieTermType.BOOL;

        writer.declareTermOnce(termId);
        writer.writeLine("(assert (hasType " + termId + " " + termType.id() + "))");

        check(n.expression());

        usedTerms.push(new TermReference(termId, termType));
    }

    @Override
    public void visit(TypeCastExpressionNode n) {
        String termId = getNextTermId();
        JolieTermType termType = JolieTermType.fromString(n.type().id());

        writer.declareTermOnce(termId);
        writer.writeLine("(assert (hasType " + termId + " " + termType.id() + "))");

        check(n.expression());

        usedTerms.push(new TermReference(termId, termType));
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
        // a[i] -> a
        // a[i].b -> a.b
        // brackets don't matter in type definition
        // we assume that if a variable is an array, it is of the same type, as its first element

        StringBuilder variablePath = new StringBuilder();

        for (int i = 0; i < n.path().size(); i++) {
            Pair<OLSyntaxNode, OLSyntaxNode> node = n.path().get(i);

            if (n.isGlobal()) {
                variablePath.append("global.");
            }

            if (node.key() instanceof ConstantStringExpression) {
                variablePath.append(((ConstantStringExpression) node.key()).value());
            } else {
                // TODO throw an exception or handle the case
            }

            if (node.value() != null) {
                check(node.value());
                TermReference nodeValueTerm = usedTerms.pop();
                writer.writeLine(assertTypeNumber(nodeValueTerm));
            }

            if (n.path().size() - 1 > i) {
                variablePath.append(".");
            }

            writer.declareTermOnce(variablePath.toString());
        }

        usedTerms.push(new TermReference(variablePath.toString(), JolieTermType.VAR));
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

    public void visit(TypeDefinition n) {

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

    private String assertTypeLikeBoolean(TermReference termRef) {
        return oneOfTypes(termRef,
                JolieTermType.BOOL,
                JolieTermType.DOUBLE,
                JolieTermType.INT,
                JolieTermType.LONG,
                JolieTermType.STRING);
    }

    private String assertTypeNumber(TermReference termRef) {
        return oneOfTypes(termRef,
                JolieTermType.INT,
                JolieTermType.LONG,
                JolieTermType.DOUBLE);
    }

    private String oneOfTypes(TermReference termRef, JolieTermType... types) {
        StringBuilder sb = new StringBuilder();
        sb.append("(assert (or ");
        for (JolieTermType type : types) {
            sb.append("(hasType ").append(termRef.id).append(" ").append(type.id()).append(") ");
        }
        sb.append("))\n");
        return sb.toString();
    }

    private enum JolieTermType {
        STRING(NativeType.STRING.id()),
        INT(NativeType.INT.id()),
        LONG(NativeType.LONG.id()),
        BOOL(NativeType.BOOL.id()),
        DOUBLE(NativeType.DOUBLE.id()),
        VAR("var");

        private final static Map<String, JolieTermType> idMap = new HashMap<>();

        static {
            for (JolieTermType type : JolieTermType.values()) {
                idMap.put(type.id(), type);
            }
        }

        private final String id;

        JolieTermType(String id) {
            this.id = id;
        }

        public String id() {
            return id;
        }

        public static JolieTermType fromString(String id) {
            return idMap.get(id);
        }

        public static boolean isMeaningfulType(JolieTermType type) {
            return type.equals(STRING) ||
                    type.equals(INT) ||
                    type.equals(LONG) ||
                    type.equals(BOOL) ||
                    type.equals(DOUBLE);
        }
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
