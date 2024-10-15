package org.checkerframework.checker.dividebyzero;

import com.sun.source.tree.*;
import java.lang.annotation.Annotation;
import java.util.EnumSet;
import java.util.Set;
import javax.lang.model.type.TypeKind;
import org.checkerframework.checker.dividebyzero.qual.*;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;

public class DivByZeroVisitor extends BaseTypeVisitor<DivByZeroAnnotatedTypeFactory> {

  /** Set of operators we care about */
  private static final Set<Tree.Kind> DIVISION_OPERATORS =
      EnumSet.of(
          /* x /  y */ Tree.Kind.DIVIDE,
          /* x /= y */ Tree.Kind.DIVIDE_ASSIGNMENT,
          /* x %  y */ Tree.Kind.REMAINDER,
          /* x %= y */ Tree.Kind.REMAINDER_ASSIGNMENT);

  /**
   * Determine whether to report an error at the given binary AST node. The error text is defined in
   * the messages.properties file.
   *
   * @param node the AST node to inspect
   * @return true if an error should be reported, false otherwise
   */
private boolean errorAt(BinaryTree node) {
    // A BinaryTree can represent any binary operator, including + or -.
    
    // Check if the operator is one of the division or remainder operators
    if (DIVISION_OPERATORS.contains(node.getKind())) {
        // Get the right-hand side operand
        Tree rhs = node.getRightOperand();

        // Check if the right-hand operand could be zero or top
        if (rhs != null) {
            if (hasAnnotation(rhs, Zero.class) || hasAnnotation(rhs, Top.class)) {
                return true;  // Flag a divide-by-zero if rhs has @Zero or is top
            }
        }
    }
    return false;     
}

  /**
   * Determine whether to report an error at the given compound assignment AST node. The error text
   * is defined in the messages.properties file.
   *
   * @param node the AST node to inspect
   * @return true if an error should be reported, false otherwise
   */
private boolean errorAt(CompoundAssignmentTree node) {
    // A CompoundAssignmentTree represents any binary operator combined with an assignment,
    // such as "x += 10".
    
    if (DIVISION_OPERATORS.contains(node.getKind())) {
        // Get the right-hand side operand
        Tree rhs = node.getExpression();
        
        // Check if the right-hand operand could be zero or top
        if (rhs != null) {
            if (hasAnnotation(rhs, Zero.class) || hasAnnotation(rhs, Top.class)) {
                return true;  // Flag divide-by-zero if rhs is zero or is top
            }
        }
    }
    return false;
}
  // ========================================================================
  // Useful helpers

  private static final Set<TypeKind> INT_TYPES = EnumSet.of(TypeKind.INT, TypeKind.LONG);

  private boolean isInt(Tree node) {
    return INT_TYPES.contains(atypeFactory.getAnnotatedType(node).getKind());
  }

  private boolean hasAnnotation(Tree node, Class<? extends Annotation> c) {
    return atypeFactory.getAnnotatedType(node).hasPrimaryAnnotation(c);
  }

  // ========================================================================
  // Checker Framework plumbing

  public DivByZeroVisitor(BaseTypeChecker c) {
    super(c);
  }

  @Override
  public Void visitBinary(BinaryTree node, Void p) {
    if (isInt(node)) {
      if (errorAt(node)) {
        checker.reportError(node, "divide.by.zero");
      }
    }
    return super.visitBinary(node, p);
  }

  @Override
  public Void visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
    if (isInt(node.getExpression())) {
      if (errorAt(node)) {
        checker.reportError(node, "divide.by.zero");
      }
    }
    return super.visitCompoundAssignment(node, p);
  }
}
