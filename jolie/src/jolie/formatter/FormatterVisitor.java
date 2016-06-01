package jolie.formatter;

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

/**
 * Created by nick on 4/25/16.
 */
public class FormatterVisitor implements OLVisitor {

    private FormatterWriter writer;

    boolean insideType = false;

    public FormatterVisitor(FormatterWriter writer) {
        this.writer = writer;
    }

    private void format(OLSyntaxNode node) {
        if (node != null) {
            System.out.println(node);
            node.accept(this);
        }
    }

    private void format(Scanner.TokenType tokenType) {
        String s = "";
        switch (tokenType) {
            case EQUAL:
                s = "==";
                break;
            case NOT_EQUAL:
                s = "!=";
                break;
            case LANGLE:
                s = "<";
                break;
            case RANGLE:
                s = ">";
                break;
            case MAJOR_OR_EQUAL:
                s = ">=";
                break;
            case MINOR_OR_EQUAL:
                s = "<=";
                break;
        }
        writer.write(s);
    }

    @Override
    public void visit(Program n) {
        for (OLSyntaxNode node : n.children()) {
            format(node);
        }
    }

    @Override
    public void visit(OneWayOperationDeclaration decl) {
        writer.writeLineIndented(decl.id() + "(undefined)");
    }

    @Override
    public void visit(RequestResponseOperationDeclaration decl) {

    }

    @Override
    public void visit(DefinitionNode n) {
        if (!n.id().equals("main") && !n.id().equals("init")) {
            writer.write("define ");
        }
        writer.writeLineIndented(n.id());
        writer.writeLineIndented("{");
        writer.indent();
        format(n.body());
        writer.writeLine();
        writer.unindent();
        writer.writeLineIndented("}");
        writer.writeLine();
    }


    @Override
    public void visit(ParallelStatement n) {
        for (int i = 0; i < n.children().size(); i++) {
            System.out.println(n.children().get(i));
            if (n.children().get(i) instanceof SequenceStatement) {
                writer.writeLineIndented("{");
                writer.indent();
            }
            format(n.children().get(i));
            if (n.children().get(i) instanceof SequenceStatement) {
                writer.unindent();
                writer.writeLineIndented("}");
            }
            writer.writeLine();
            if (i < n.children().size() - 1) {
                writer.writeLineIndented("|");
            }
        }
    }

    @Override
    public void visit(SequenceStatement n) {
        for (int i = 0; i < n.children().size(); i++) {
            if (n.children().get(i) instanceof ParallelStatement) {
                writer.writeLineIndented("{");
                writer.indent();
            }
            format(n.children().get(i));
            if (n.children().get(i) instanceof ParallelStatement) {
                writer.unindent();
                writer.writeLineIndented("}");
            }
            if (i < n.children().size() - 1) {
                writer.writeLine(";");
            } else {
                writer.write("");
            }
        }
    }

    @Override
    public void visit(NDChoiceStatement n) {
        int level;
        Pair<OLSyntaxNode, OLSyntaxNode> pair;
        for (int i = 0; i < n.children().size(); i++) {
            pair = n.children().get(i);
            writer.writeIndented("[ ");
            level = writer.getIndentation();
            writer.setIndentation(0);
            format(pair.key());
            writer.setIndentation(level);
            writer.writeLine(" ] {");
            writer.indent();
            format(pair.value());
            writer.unindent();
            writer.writeLine();
            writer.writeIndented("}");
            if (i < n.children().size() - 1) {
                writer.writeLine();
            }
        }
    }

    @Override
    public void visit(OneWayOperationStatement n) {
        writer.writeIndented(n.id() + "(");
        format(n.inputVarPath());
        writer.write(")");
    }

    @Override
    public void visit(RequestResponseOperationStatement n) {
        writer.write(n.id() + "(");
        System.out.println(writer.getIndentation());
        format(n.inputVarPath());
        writer.write(")(");
        format(n.outputExpression());
        writer.writeLineIndented(") {");
        writer.indent();
        writer.indent();
        System.out.println(n.process());
        format(n.process());
        writer.unindent();
        writer.unindent();
        writer.writeLineIndented("");
        writer.indent();
        writer.writeIndented("}");
    }

    @Override
    public void visit(NotificationOperationStatement n) {
        writer.writeIndented(n.id() + "@" + n.outputPortId() + "(");
        format(n.outputExpression());
        writer.write(")");
    }

    @Override
    public void visit(SolicitResponseOperationStatement n) {
        writer.writeIndented(n.id() + "@" + n.outputPortId() + "(");
        format(n.outputExpression());
        writer.write(")(");
        format(n.inputVarPath());
        writer.write(")");
    }

    @Override
    public void visit(LinkInStatement n) {

    }

    @Override
    public void visit(LinkOutStatement n) {

    }

    @Override
    public void visit(AssignStatement n) {
        // adds indentation before statement
        writer.writeIndented("");
        format(n.variablePath());
        writer.write(" = ");
        format(n.expression());
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
        Pair<OLSyntaxNode, OLSyntaxNode> choice;
        for (int i = 0; i < n.children().size(); i++) {
            if (i == 0) {
                writer.writeIndented("if (");
            } else {
                writer.write(" else if (");
            }
            choice = n.children().get(i);
            format(choice.key());
            writer.writeLine(") {");
            writer.indent();
            format(choice.value());
            writer.unindent();
            writer.writeLine();
            writer.writeIndented("}");
        }
        if (n.elseProcess() != null) {
            writer.writeLine(" else {");
            writer.indent();
            format(n.elseProcess());
            writer.unindent();
            writer.writeLine();
            writer.writeIndented("}");
        }
    }

    @Override
    public void visit(DefinitionCallStatement n) {

    }

    @Override
    public void visit(WhileStatement n) {
        writer.writeIndented("while (");
        format(n.condition());
        writer.writeLine(") {");
        writer.indent();
        format(n.body());
        writer.unindent();
        writer.writeLine();
        writer.writeIndented("}");
    }

    @Override
    public void visit(OrConditionNode n) {

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
        if (writer.shouldPrintQuotes()) {
            writer.write("\"");
        }
        String s = n.value();
        // TODO: add special characters handling.
        s = s.replace("\n", "\\n");
        writer.write(s);
        if (writer.shouldPrintQuotes()) {
            writer.write("\"");
        }
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
        writer.writeIndented("execution { ");
        writer.write(n.mode().name().toLowerCase());
        writer.writeLineIndented(" }");
        writer.writeLine();
    }

    @Override
    public void visit(CorrelationSetInfo n) {
        writer.writeLineIndented("cset { ");
        for (CorrelationSetInfo.CorrelationVariableInfo var : n.variables()) {
            format(var.correlationVariablePath());
            writer.writeLine(":");
            writer.indent();
            writer.writeIndented("");
            int i = 0;
            for (CorrelationSetInfo.CorrelationAliasInfo alias : var.aliases()) {
                writer.write(alias.guardName() + ".");
                format(alias.variablePath());
                if (i++ < var.aliases().size() - 1) {
                    writer.write(", ");
                } else {
                    writer.writeLine();
                }
            }
            writer.unindent();
        }
        writer.writeLineIndented("}");
        writer.writeLine();
    }

    @Override
    public void visit(InputPortInfo n) {
        writer.writeLineIndented("inputPort " + n.id() + " {");
        writer.writeIndented("Location: ");
        writer.writeLine("\"" + n.location().toString() + "\"");
        if (n.protocolId() != null) {
            writer.writeIndented("Protocol: ");
            writer.writeLine(n.protocolId());
        }
        if (!n.getInterfaceList().isEmpty()) {
            writer.writeIndented("Interfaces: ");
            int i = 0;
            for (InterfaceDefinition iface : n.getInterfaceList()) {
                writer.write(iface.name());
                if (i++ < n.getInterfaceList().size() - 1) {
                    writer.write(", ");
                }
            }
            writer.writeLine();
        }
        writer.writeLineIndented("}");
        writer.writeLine();
    }

    @Override
    public void visit(OutputPortInfo n) {
        writer.writeLineIndented("outputPort " + n.id() + " {");
        if (n.location() != null) {
            writer.writeIndented("Location: ");
            writer.writeLine("\"" + n.location().toString() + "\"");
        }
        if (n.protocolId() != null) {
            writer.writeIndented("Protocol: ");
            writer.writeLine(n.protocolId());
        }
        if (!n.getInterfaceList().isEmpty()) {
            writer.writeIndented("Interfaces: ");
            int i = 0;
            for (InterfaceDefinition iface : n.getInterfaceList()) {
                writer.write(iface.name());
                if (i++ < n.getInterfaceList().size() - 1) {
                    writer.write(", ");
                }
            }
            writer.writeLine();
        }
        printOperationDeclarations(n);
        writer.writeLineIndented("}");
        writer.writeLine();
    }

    @Override
    public void visit(PointerStatement n) {

    }

    @Override
    public void visit(DeepCopyStatement n) {
        writer.writeIndented("");
        format(n.leftPath());
        writer.write(" << ");
        format(n.rightExpression());
    }

    @Override
    public void visit(RunStatement n) {

    }

    @Override
    public void visit(UndefStatement n) {
        writer.writeIndented("undef(");
        format(n.variablePath());
        writer.write(")");
    }

    @Override
    public void visit(ValueVectorSizeExpressionNode n) {
        writer.write("#");
        format(n.variablePath());
    }

    @Override
    public void visit(PreIncrementStatement n) {
        writer.writeIndented("");
        writer.write("++");
        format(n.variablePath());
    }

    @Override
    public void visit(PostIncrementStatement n) {
        writer.writeIndented("");
        format(n.variablePath());
        writer.write("++");
    }

    @Override
    public void visit(PreDecrementStatement n) {
        writer.writeIndented("");
        writer.write("--");
        format(n.variablePath());
    }

    @Override
    public void visit(PostDecrementStatement n) {
        writer.writeIndented("");
        format(n.variablePath());
        writer.write("--");
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
        writer.writeLineIndented("synchronized(" + n.id() + ") {");
        writer.indent();
        format(n.body());
        writer.unindent();
        writer.writeIndented("}");
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
        for (int i = 0; i < n.path().size(); i++) {
            Pair<OLSyntaxNode, OLSyntaxNode> node = n.path().get(i);
            writer.setPrintQuotes(false);
            format(node.key());
            writer.setPrintQuotes(true);

            if ((node.value() instanceof ConstantIntegerExpression)) {
                int value = ((ConstantIntegerExpression) node.value()).value();
            }

            if (node.value() instanceof ConstantIntegerExpression //&&
                //!(((ConstantIntegerExpression) node.value()).value() == 0)
                    ) {
                writer.write("[");
                format(node.value());
                writer.write("]");
            }
            if (n.path().size() - 1 > i) {
                writer.write(".");
            }
        }
    }

    @Override
    public void visit(TypeInlineDefinition n) {
        if (insideType == false) {
            writer.writeIndented("type ");
        }
        writer.write(n.id());
        format(n.cardinality());
        writer.write(":" + n.nativeType().id());
        if (n.untypedSubTypes()) {
            writer.write(" { ? }");
        } else if (n.hasSubTypes()) {
            boolean backup = insideType;
            insideType = true;
            writer.writeLine(" {");
            writer.indent();
            for (Map.Entry<String, TypeDefinition> entry : n.subTypes()) {
                writer.writeIndented(".");
                format(entry.getValue());
            }
            writer.unindent();
            writer.writeIndented("}");
            insideType = backup;
        }
        writer.writeLine();
        if (insideType == false) {
            writer.writeLine();
        }
    }

    public void format(Range r) {
        if (r.min() == r.max() && r.min() == 1) {
            return;
        }

        if (r.min() == 0 && r.max() == 1) {
            writer.write("?");
        } else if (r.min() == 0 && r.max() == Integer.MAX_VALUE) {
            writer.write("*");
        } else {
            writer.write("[" + r.min() + "," + r.max() + "]");
        }
    }

    @Override
    public void visit(TypeDefinitionLink n) {

    }

    @Override
    public void visit(InterfaceDefinition n) {
        writer.writeLineIndented("interface " + n.name() + " {");
        printOperationDeclarations(n);
        writer.writeLineIndented("}");
        writer.writeLine();
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

    private void printOperationDeclarations(OperationCollector c) {
        Set<Map.Entry<String, OperationDeclaration>> entries = c.operationsMap().entrySet();
        Map<String, OneWayOperationDeclaration> ow = new HashMap<String, OneWayOperationDeclaration>();
        Map<String, RequestResponseOperationDeclaration> rr = new HashMap<String, RequestResponseOperationDeclaration>();
        for (Map.Entry<String, OperationDeclaration> entry : entries) {
            if (entry.getValue() instanceof OneWayOperationDeclaration) {
                ow.put(entry.getValue().id(), (OneWayOperationDeclaration) entry.getValue());
            } else {
                rr.put(entry.getValue().id(), (RequestResponseOperationDeclaration) entry.getValue());
            }
        }
        if (ow.isEmpty() == false) {
            writer.writeLineIndented("OneWay:");
            writer.indent();
            writer.writeIndented("");
            int i = 0;
            for (OneWayOperationDeclaration decl : ow.values()) {
                writer.write(decl.id());
                if (decl.requestType() != null) {
                    writer.write("(" + decl.requestType().id() + ")");
                }
                if (i++ < ow.size() - 1) {
                    writer.write(", ");
                }
            }
            writer.unindent();
            writer.writeLine();
        }
        if (rr.isEmpty() == false) {
            writer.writeLineIndented("RequestResponse:");
            writer.indent();
            writer.writeIndented("");
            int i = 0;
            for (RequestResponseOperationDeclaration decl : rr.values()) {
                writer.write(decl.id());
                if (decl.requestType() != null) {
                    writer.write("(" + decl.requestType().id() + ")");
                }
                if (decl.responseType() != null) {
                    writer.write("(" + decl.responseType().id() + ")");
                }
                if (i++ < rr.size() - 1) {
                    writer.write(", ");
                }
            }
            writer.unindent();
            writer.writeLine();
        }
    }
}
