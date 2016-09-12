package jolie.typeChecker;

/**
 * Created by Timur on 19.07.2016.
 */

import jolie.lang.Constants;
import jolie.lang.parse.*;
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
    private TypeCheckerWriter writer;

    boolean insideType = false;

    public TypeCheckerVisitor(TypeCheckerWriter writer) {
        this.writer = writer;
    }

    private void format(OLSyntaxNode node) {
        if (node != null) {
            node.accept(this);
        }
    }

    private void format(Scanner.TokenType tokenType) {

    }

    @Override
    public void visit(Program n) {
        for (OLSyntaxNode node : n.children()) {
            format(node);
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
    }


    @Override
    public void visit(ParallelStatement n) {
    }

    @Override
    public void visit(SequenceStatement n) {
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
        String s = "(declare-fun properType (Term Term) Bool)\n+" +
                "(assert (forall ((x Term)(y Term))(properType x y bool)))\n";
        writer.write(s);
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
    }

    @Override
    public void visit(DefinitionCallStatement n) {

    }

    @Override
    public void visit(WhileStatement n) {
    }

    @Override
    public void visit(OrConditionNode n) {
        int i = 0;
        format(n.children().get(0));
        i++;
        for (; i < n.children().size(); i++) {
            writer.write(" || ");
            format(n.children().get(i));
        }
    }

    @Override
    public void visit(AndConditionNode n) {
        int i = 0;
        format(n.children().get(0));
        i++;
        for (; i < n.children().size(); i++) {
            writer.write(" && ");
            format(n.children().get(i));
        }
    }

    @Override
    public void visit(NotExpressionNode n) {

    }

    @Override
    public void visit(CompareConditionNode n) {
        format(n.leftExpression());
        writer.write(" ");
        format(n.opType());
        writer.write(" ");
        format(n.rightExpression());
    }

    @Override
    public void visit(ConstantIntegerExpression n) {
        //writer.write("\"");
        writer.write(Integer.toString(n.value()));
        //writer.write("\"");

    }

    @Override
    public void visit(ConstantDoubleExpression n) {
        writer.write(Double.toString(n.value()));
    }

    @Override
    public void visit(ConstantBoolExpression n) {
        writer.write(Boolean.toString(n.value()));
    }

    @Override
    public void visit(ConstantLongExpression n) {
        writer.write(Long.toString(n.value()) + "L");
    }

    @Override
    public void visit(ConstantStringExpression n) {
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
                        writer.write(" * ");
                        break;
                    case DIVIDE:
                        writer.write(" / ");
                        break;
                    case MODULUS:
                        writer.write(" % ");
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
            format(pair.value());
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
                    writer.write(" + ");
                } else {
                    writer.write(" - ");
                }
            }
            format(pair.value());
        }
    }

    @Override
    public void visit(VariableExpressionNode n) {
        format(n.variablePath());
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
        format(n.variablePath());
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
            format(n.variablePath());
            writer.write(")");
        }
    }

    @Override
    public void visit(InstanceOfExpressionNode n) {
        if (n.expression() instanceof AssignStatement) {
            writer.write("(");
            format(((AssignStatement) n.expression()).variablePath());
            writer.write(" = ");
            format(((AssignStatement) n.expression()).expression());
            writer.write(")");
        } else {
            format(n.expression());
        }
        writer.write(" instanceof ");
        writer.write(n.type().id());
    }

    @Override
    public void visit(TypeCastExpressionNode n) {
        writer.write(n.type().id());
        writer.write("(");
        format(n.expression());
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
    }

    @Override
    public void visit(TypeInlineDefinition n) {
    }

    public void format(Range r) {
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
}
