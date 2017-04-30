package jolie.typeChecker;

import jolie.lang.Constants;
import jolie.lang.parse.OLVisitor;
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
    private TypeCheckerWriter writer;
    private Stack<TermReference> termsContext = new Stack<>();

    TypeCheckerVisitor(TypeCheckerWriter writer) {
        this.writer = writer;
    }

    private void check(OLSyntaxNode node) {
        if (node != null) {
            node.accept(this);
        }
    }

    private void check(InstallFunctionNode node) {
        if (node != null) {
            visit(node);
        }
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
        check(n.body());
    }

    @Override
    public void visit(ParallelStatement n) {
        for (OLSyntaxNode child : n.children()) {
            writer.enterScope();
            check(child);
            writer.exitScope();
        }
    }

    @Override
    public void visit(SequenceStatement n) {
        n.children().forEach(this::check);
    }

    @Override
    public void visit(NDChoiceStatement n) {
        for (Pair<OLSyntaxNode, OLSyntaxNode> child : n.children()) {
            writer.enterScope();
            check(child.key());
            check(child.value());
            writer.exitScope();
        }
    }

    @Override
    public void visit(OneWayOperationStatement n) {
        check(n.inputVarPath());
    }

    @Override
    public void visit(RequestResponseOperationStatement n) {
        check(n.inputVarPath());
        check(n.outputExpression());
        writer.enterScope();
        check(n.process());
        writer.exitScope();
    }

    @Override
    public void visit(NotificationOperationStatement n) {
        check(n.outputExpression());
    }

    @Override
    public void visit(SolicitResponseOperationStatement n) {
        check(n.inputVarPath());
        check(n.outputExpression());
        check(n.handlersFunction());
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
        TermReference variablePathTerm = termsContext.pop();

        check(expression);
        TermReference expressionTerm = termsContext.pop();

        String formula = "(assert (sameType " + variablePathTerm.id() + " " + expressionTerm.id() + "))\n";
        if (TermType.isMeaningful(expressionTerm.type())) {
            formula += "(assert (hasType " + variablePathTerm.id() + " " + expressionTerm.type().id() + "))\n";
        }
        writer.write(formula);

        String statementId = Utils.getNextTermId();
        writer.declareTermOnce(statementId);
        termsContext.push(new TermReference(statementId, expressionTerm.type()));
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
        TermReference variablePathTerm = termsContext.pop();

        check(expression);
        TermReference expressionTerm = termsContext.pop();

        writer.writeLine("(assert (sameType " + variablePathTerm.id() + " " + expressionTerm.id() + "))");
        writer.assertTypeNumber(variablePathTerm.id());

        String statementId = Utils.getNextTermId();
        writer.declareTermOnce(statementId);
        termsContext.push(new TermReference(statementId, expressionTerm.type()));
    }

    @Override
    public void visit(IfStatement n) {
        for (Pair<OLSyntaxNode, OLSyntaxNode> statement : n.children()) {
            OLSyntaxNode condition = statement.key();
            OLSyntaxNode body = statement.value();

            check(condition);
            TermReference conditionTerm = termsContext.pop();
            writer.assertTypeLikeBoolean(conditionTerm.id());

            check(body);
        }

        check(n.elseProcess());
    }

    @Override
    public void visit(DefinitionCallStatement n) {
    }

    @Override
    public void visit(WhileStatement n) {
        OLSyntaxNode condition = n.condition();
        OLSyntaxNode body = n.body();

        check(condition);
        TermReference conditionTerm = termsContext.pop();
        writer.assertTypeLikeBoolean(conditionTerm.id());

        check(body);
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
            refs.add(termsContext.pop());
        }

        TermType expressionType;
        String operationId = Utils.getNextTermId();

        if (refs.size() == 1) {
            TermReference ref = refs.getFirst();
            expressionType = ref.type();
            if (expressionType.equals(TermType.VAR)) {
                operationId = ref.id();
            }
        } else { // then we assume for now that it should be a boolean expression. In actual programs it can be wrong. Just to start with.
            // TODO process not-boolean constructions
            expressionType = TermType.BOOL;
            StringBuilder sb = new StringBuilder();
            sb.append("(assert (= ");
            for (TermReference ref : refs) {
                sb.append("(typeOf ").append(ref.id()).append(")").append(" ");
            }
            sb.append("bool))");
            writer.writeLine(sb.toString());
        }

        writer.declareTermOnce(operationId);

        if (TermType.isMeaningful(expressionType)) {
            writer.writeLine("(assert (hasType " + operationId + " " + expressionType.id() + "))");
        }

        termsContext.push(new TermReference(operationId, expressionType));
    }

    @Override
    public void visit(NotExpressionNode n) {
        OLSyntaxNode expression = n.expression();

        check(expression);
        TermReference conditionTerm = termsContext.pop();
        writer.writeLine("(assert (hasType " + conditionTerm.id() + " bool))");

        String operationId = Utils.getNextTermId();
        writer.declareTermOnce(operationId);
        termsContext.push(new TermReference(operationId, TermType.BOOL));
    }

    @Override
    public void visit(CompareConditionNode n) {
        check(n.leftExpression());
        TermReference leftExpressionTerm = termsContext.pop();
        check(n.rightExpression());
        TermReference rightExpressionTerm = termsContext.pop();

        writer.writeLine("(assert (sameType " + leftExpressionTerm.id() + " " + rightExpressionTerm.id() + "))");

        String operationId = Utils.getNextTermId();
        writer.declareTermOnce(operationId);
        termsContext.push(new TermReference(operationId, TermType.BOOL));
    }

    @Override
    public void visit(ConstantIntegerExpression n) {
        String constId = Utils.getNextTermId();
        writer.declareTermOnce(constId);
        writer.writeLine("(assert (hasType " + constId + " int))");
        termsContext.push(new TermReference(constId, TermType.INT));
    }

    @Override
    public void visit(ConstantDoubleExpression n) {
        String constId = Utils.getNextTermId();
        writer.declareTermOnce(constId);
        writer.writeLine("(assert (hasType " + constId + " double))");
        termsContext.push(new TermReference(constId, TermType.DOUBLE));
    }

    @Override
    public void visit(ConstantBoolExpression n) {
        String constId = Utils.getNextTermId();
        writer.declareTermOnce(constId);
        writer.writeLine("(assert (hasType " + constId + " bool))");
        termsContext.push(new TermReference(constId, TermType.BOOL));
    }

    @Override
    public void visit(ConstantLongExpression n) {
        String constId = Utils.getNextTermId();
        writer.declareTermOnce(constId);
        writer.writeLine("(assert (hasType " + constId + " long))");
        termsContext.push(new TermReference(constId, TermType.LONG));
    }

    @Override
    public void visit(ConstantStringExpression n) {
        String constId = Utils.getNextTermId();
        writer.declareTermOnce(constId);
        writer.writeLine("(assert (hasType " + constId + " string))");
        termsContext.push(new TermReference(constId, TermType.STRING));
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
            refs.add(termsContext.pop());
        }

        TermReference firstRef = refs.getFirst();
        TermType expressionType = firstRef.type();
        String operationId = Utils.getNextTermId();

        if (refs.size() == 1) { // if it is a constant or a variable, leave it be
            if (expressionType.equals(TermType.VAR)) {
                operationId = firstRef.id();
            }
        } else { // else assume that every operand should be the same type as the first one
            // TODO make type numeric? we can add int to long
            StringBuilder sb = new StringBuilder();
            sb.append("(assert (= ");
            for (TermReference ref : refs) {
                sb.append("(typeOf ").append(ref.id()).append(")").append(" ");
            }
            sb.append("))");
            writer.writeLine(sb.toString());
        }

        writer.declareTermOnce(operationId);

        if (TermType.isMeaningful(expressionType)) {
            writer.writeLine("(assert (hasType " + operationId + " " + expressionType.id() + "))");
        } else if (!operationId.equals(firstRef.id())) {
            writer.writeLine("(assert (sameType " + operationId + " " + firstRef.id() + "))");
        }

        termsContext.push(new TermReference(operationId, expressionType));
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
        check(n.body());
    }

    @Override
    public void visit(InstallStatement n) {
        check(n.handlersFunction());
    }

    public void visit(InstallFunctionNode handlersFunction) {
        if (handlersFunction != null) {
            Pair<String, OLSyntaxNode>[] pairs = handlersFunction.pairs();

            if (pairs != null) {
                for (Pair<String, OLSyntaxNode> pair : pairs) {
                    check(pair.value());
                }
            }
        }
    }

    @Override
    public void visit(CompensateStatement n) {
    }

    @Override
    public void visit(ThrowStatement n) {
        check(n.expression());
    }

    @Override
    public void visit(ExitStatement n) {
    }

    @Override
    public void visit(ExecutionInfo n) {
    }

    @Override
    public void visit(CorrelationSetInfo n) {
        // TODO
    }

    @Override
    public void visit(InputPortInfo n) {
        // TODO
    }

    @Override
    public void visit(OutputPortInfo n) {
        // TODO
    }

    @Override
    public void visit(PointerStatement n) {
        // TODO assertions?
        check(n.leftPath());
        check(n.rightPath());
    }

    @Override
    public void visit(DeepCopyStatement n) {
        // TODO
    }

    @Override
    public void visit(RunStatement n) {
        // TODO scope?
        check(n.expression());
    }

    @Override
    public void visit(UndefStatement n) {
        // TODO how to process undef?
    }

    @Override
    public void visit(ValueVectorSizeExpressionNode n) {
        String termId = Utils.getNextTermId();

        writer.declareTermOnce(termId);

        check(n.variablePath());

        // we assume that size of vector is Integer
        // However, maybe we need to handle it as some kind of 'numeric' type and allow the precise type
        // to be specified later (or before)
        // TODO decide on 'numeric' type
        TermReference termRef = new TermReference(termId, TermType.INT);

        writer.writeLine("(assert (hasType " + termId + " " + termRef.type().id() + "))");

        termsContext.push(termRef);
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
        TermReference variablePathTerm = termsContext.pop();

        writer.assertTypeNumber(variablePathTerm.id());

        String statementId = Utils.getNextTermId();
        writer.declareTermOnce(statementId);
        termsContext.push(new TermReference(statementId, variablePathTerm.type()));
    }

    @Override
    public void visit(ForStatement n) {
        OLSyntaxNode init = n.init();
        OLSyntaxNode condition = n.condition();
        OLSyntaxNode post = n.post();
        OLSyntaxNode body = n.body();

        check(init);

        check(condition);
        TermReference conditionTerm = termsContext.pop();
        writer.assertTypeLikeBoolean(conditionTerm.id());

        check(post);
        check(body);
    }

    @Override
    public void visit(ForEachSubNodeStatement n) {
        OLSyntaxNode keyPath = n.keyPath();
        OLSyntaxNode targetPath = n.targetPath();
        OLSyntaxNode body = n.body();

        writer.enterScope();

        check(keyPath);
        check(targetPath);
        check(body);

        writer.exitScope();
    }

    @Override
    public void visit(ForEachArrayItemStatement n) {
        OLSyntaxNode keyPath = n.keyPath();
        OLSyntaxNode targetPath = n.targetPath();
        OLSyntaxNode body = n.body();

        writer.enterScope();

        check(keyPath);
        TermReference keyTerm = termsContext.pop();

        check(targetPath);
        TermReference targetTerm = termsContext.pop();

        writer.writeLine("(assert (sameType " + keyTerm.id() + " " + targetTerm.id() + "))");

        check(body);

        writer.exitScope();
    }

    @Override
    public void visit(SpawnStatement n) {
        // TODO
    }

    @Override
    public void visit(IsTypeExpressionNode n) {
        TermReference newTerm = new TermReference(Utils.getNextTermId(), TermType.BOOL);

        writer.declareTermOnce(newTerm.id());
        writer.writeLine("(assert (hasType " + newTerm.id() + " " + newTerm.type().id() + "))");

        check(n.variablePath());

        termsContext.push(newTerm);
    }

    @Override
    public void visit(InstanceOfExpressionNode n) {
        String termId = Utils.getNextTermId();
        TermType termType = TermType.BOOL;

        writer.declareTermOnce(termId);
        writer.writeLine("(assert (hasType " + termId + " " + termType.id() + "))");

        check(n.expression());

        termsContext.push(new TermReference(termId, termType));
    }

    @Override
    public void visit(TypeCastExpressionNode n) {
        String termId = Utils.getNextTermId();
        TermType termType = TermType.fromString(n.type().id());

        writer.declareTermOnce(termId);
        writer.writeLine("(assert (hasType " + termId + " " + termType.id() + "))");

        check(n.expression());

        termsContext.push(new TermReference(termId, termType));
    }

    @Override
    public void visit(SynchronizedStatement n) {
        check(n.body());
    }

    @Override
    public void visit(CurrentHandlerStatement n) {
    }

    @Override
    public void visit(EmbeddedServiceNode n) {
        // TODO
    }

    @Override
    public void visit(InstallFixedVariableExpressionNode n) {
        check(n.variablePath());
    }

    @Override
    public void visit(VariablePathNode n) {
        // a[i] -> a
        // a[i].b -> a.b
        // brackets don't matter in type definition
        // we assume that if a variable is an array, it is of the same type, as its first element

        // TODO come up with a solution to dynamic keys in variable paths
        // a.(key) -> skip
        // variable path is set in runtime. We can't know the type of the resulting variable path.

        StringBuilder variablePath = new StringBuilder();

        for (int i = 0; i < n.path().size(); i++) {
            Pair<OLSyntaxNode, OLSyntaxNode> node = n.path().get(i);

            if (n.isGlobal()) {
                variablePath.append("global.");
            }

            if (node.key() instanceof ConstantStringExpression) {
                variablePath.append(((ConstantStringExpression) node.key()).value());
            } else {
                check(node.key());

                TermReference keyValueTerm = termsContext.pop();

                if (TermType.isMeaningful(keyValueTerm.type())) {
                    variablePath.append(keyValueTerm.id());
                } else {
                    variablePath.append("DYNAMIC_PATH_").append(Utils.getNextTermId());
                    writer.declareTermOnce(variablePath.toString());
                    break;
                }
            }

            if (node.value() != null) {
                check(node.value());
                TermReference nodeValueTerm = termsContext.pop();
                writer.assertTypeNumber(nodeValueTerm.id());
            }

            writer.declareTermOnce(variablePath.toString());

            if (n.path().size() - 1 > i) {
                variablePath.append(".");
            }
        }

        termsContext.push(new TermReference(variablePath.toString(), TermType.VAR));
    }

    @Override
    public void visit(TypeInlineDefinition n) {
        // TODO
    }

    public void check(Range r) {
        // used in TypeInlineDefinition
    }

    public void visit(TypeDefinition n) {
        // TODO
    }

    @Override
    public void visit(TypeDefinitionLink n) {
        // TODO make sure nothing else needs to be handled here in TypeDefinitionLink
        check(n.linkedType());
    }

    @Override
    public void visit(InterfaceDefinition n) {
        // TODO
    }

    @Override
    public void visit(DocumentationComment n) {
    }

    @Override
    public void visit(FreshValueExpressionNode n) {
    }

    @Override
    public void visit(CourierDefinitionNode n) {
        check(n.body());
    }

    @Override
    public void visit(CourierChoiceStatement n) {
        // TODO
    }

    @Override
    public void visit(NotificationForwardStatement n) {
        // TODO
    }

    @Override
    public void visit(SolicitResponseForwardStatement n) {
        check(n.inputVariablePath());
        check(n.outputVariablePath());
    }

    @Override
    public void visit(InterfaceExtenderDefinition n) {
        // TODO
    }

    @Override
    public void visit(InlineTreeExpressionNode n) {
        // TODO
    }

    @Override
    public void visit(VoidExpressionNode n) {
        // TODO should void be type checked? Maybe interpret it as "type is to be defined later"
        // However, VOID is not in "meaningful" types, so maybe it is ok
        String constId = Utils.getNextTermId();
        writer.declareTermOnce(constId);
        writer.writeLine("(assert (hasType " + constId + " void))");
        termsContext.push(new TermReference(constId, TermType.VOID));
    }

    @Override
    public void visit(ProvideUntilStatement n) {
        // TODO
    }

    @Override
    public void visit(TypeChoiceDefinition n) {
        // TODO
    }
}
