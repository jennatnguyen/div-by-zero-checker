package org.checkerframework.checker.dividebyzero;

import java.lang.annotation.Annotation;
import java.util.Set;
import javax.lang.model.element.AnnotationMirror;
import org.checkerframework.checker.dividebyzero.qual.*;
import org.checkerframework.dataflow.analysis.ConditionalTransferResult;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;

public class DivByZeroTransfer extends CFTransfer {

  enum Comparison {
    /** == */
    EQ,
    /** != */
    NE,
    /** < */
    LT,
    /** <= */
    LE,
    /** > */
    GT,
    /** >= */
    GE
  }

  enum BinaryOperator {
    /** + */
    PLUS,
    /** - */
    MINUS,
    /** * */
    TIMES,
    /** / */
    DIVIDE,
    /** % */
    MOD
  }

  // ========================================================================
  // Transfer functions to implement

  /**
   * Assuming that a simple comparison (lhs `op` rhs) returns true, this function should refine what
   * we know about the left-hand side (lhs). (The input value "lhs" is always a legal return value,
   * but not a very useful one.)
   *
   * <p>For example, given the code
   *
   * <pre>
   * if (y != 0) { x = 1 / y; }
   * </pre>
   *
   * the comparison "y != 0" causes us to learn the fact that "y is not zero" inside the body of the
   * if-statement. This function would be called with "NE", "top", and "zero", and should return
   * "not zero" (or the appropriate result for your lattice).
   *
   * <p>Note that the returned value should always be lower in the lattice than the given point for
   * lhs. The "glb" helper function below will probably be useful here.
   *
   * @param operator a comparison operator
   * @param lhs the lattice point for the left-hand side of the comparison expression
   * @param rhs the lattice point for the right-hand side of the comparison expression
   * @return a refined type for lhs
   */
    
private AnnotationMirror refineLhsOfComparison(
    Comparison operator, AnnotationMirror lhs, AnnotationMirror rhs) {

  // Handle "not equal" comparison
  	//top NE 0 then top is nonzero
    if (operator == Comparison.NE) {
        // If rhs is zero, lhs must be NonZero
        if (equal(rhs, reflect(Zero.class))) {
            return reflect(NonZero.class); // lhs cannot be Zero if it is not equal to Zero
        }
    } 
    // Handle "equal" comparison
    //top is equal to zero then top is zero
    else if (operator == Comparison.EQ) {
        // If rhs is zero, refine lhs to Zero
        if (equal(rhs, reflect(Zero.class))) {
            return reflect(Zero.class); 
        }
    } 
    // Handle "less than" comparison LHS < VALUE
    //top is < zero then top is negative
    else if (operator == Comparison.LT) {
        // If lhs is Negative, it remains Negative
        if (equal(rhs, reflect(Zero.class))) {
            return reflect(Negative.class); 
        } 
    }
    
    // Handle "less than or equal" comparison
    //top is LE 0 then top is top()
    else if (operator == Comparison.LE) {
        // If rhs is zero, lhs could be Zero or any positive value
        if (equal(rhs, reflect(Zero.class))) {
            return top(); // lhs could be zero or greater
        }
    } 
    // Handle "greater than" comparison >
    else if (operator == Comparison.GT) {
	//top is > 0 then top is nonzero
        if (equal(rhs, reflect(Zero.class))) {
            return reflect(NonZero.class); 
        } 
        // top is > negative can be zero
        else if (equal(rhs, reflect(Negative.class))) {
            return top(); 
        } 
        // If lhs is Negative, no refinement can be made
        else if (equal(rhs, reflect(Positive.class))) {
            return reflect(Positive.class); 
        } 
    } 
    // Handle "greater than or equal" comparison
    else if (operator == Comparison.GE) {
        // If rhs is zero, lhs could be Zero or greater
        if (equal(rhs, reflect(Zero.class))) {
            return top(); 
        }
    }

    // Return the original lhs if no refinements apply
    return lhs; 
}

  /**
   * For an arithmetic expression (lhs `op` rhs), compute the point in the lattice for the result of
   * evaluating the expression. ("Top" is always a legal return value, but not a very useful one.)
   *
   * <p>For example,
   *
   * <pre>x = 1 + 0</pre>
   *
   * should cause us to conclude that "x is not zero".
   *
   * @param operator a binary operator
   * @param lhs the lattice point for the left-hand side of the expression
   * @param rhs the lattice point for the right-hand side of the expression
   * @return the lattice point for the result of the expression
   */
private AnnotationMirror arithmeticTransfer(
    BinaryOperator operator, AnnotationMirror lhs, AnnotationMirror rhs) {
    
    if (operator == BinaryOperator.DIVIDE) {
        // Check for division by zero
        if (equal(rhs, reflect(Zero.class))) {
            return bottom(); // Return Bottom to indicate invalid operation
        } else if (equal(lhs, top())) {
            return reflect(NonZero.class); // Return NonZero if lhs is uncertain
        }
        
        // If lhs is NonZero, the result is NonZero
        if (equal(lhs, reflect(NonZero.class))) {
            return reflect(NonZero.class); 
        }

        // If lhs is Zero, the result of division is Zero
        if (equal(lhs, reflect(Zero.class))) {
            return reflect(Zero.class);
        }

        // If both lhs and rhs are unknown, we can't make any conclusions
        return top();
    }

    // Handle addition
    if (operator == BinaryOperator.PLUS) {
        // Result is equal to rhs if lhs is Zero
        if (equal(lhs, reflect(Zero.class))) {
            return rhs; // The result reflects rhs directly
        }
        
        // Result is equal to lhs if rhs is Zero
        if (equal(rhs, reflect(Zero.class))) {
            return lhs; // The result reflects lhs directly
        }

        // If both operands are NonZero, the result is NonZero
        if (equal(lhs, reflect(NonZero.class)) && equal(rhs, reflect(NonZero.class))) {
            return reflect(NonZero.class); // Result is NonZero
        }

        // If operand is Positive 
        if (equal(lhs, reflect(Positive.class)) || equal(rhs, reflect(Positive.class))) {
            return reflect(Positive.class); // Result could be Positive
        }

        // If one operand is Negative and the other is NonZero
        if (equal(lhs, reflect(Negative.class)) || equal(rhs, reflect(Negative.class))) {
            return reflect(Negative.class); // Result could be Negative
        }
	
	// Handle cancellation between positive and negative
	if ((equal(lhs, reflect(Positive.class)) && equal(rhs, reflect(Negative.class))) ||
	(equal(lhs, reflect(Negative.class)) && equal(rhs, reflect(Positive.class)))) {
		return top(); // The result could cancel out and become Zero or NonZero
	}
	
        // When both operands are not equal to Zero but exact values are unknown,
        // it represents possible outcomes without definitive conclusion
        return lub(lhs, rhs); // Return least upper bound
    }

    // Handle subtraction
    if (operator == BinaryOperator.MINUS) {
        if (equal(lhs, rhs)) {
            return reflect(Zero.class); // Result is Zero
        }
        
        // Handle cases for NonZero, Positive, and Negative
        if (equal(lhs, reflect(Positive.class)) && equal(rhs, reflect(Positive.class))) {
            return reflect(NonZero.class); 
        } 
        if (equal(lhs, reflect(Negative.class)) && equal(rhs, reflect(Negative.class))) {
            return reflect(NonZero.class); 
        }
        
       	// Handle cancellation between positive and negative
	if ((equal(lhs, reflect(Positive.class)) && equal(rhs, reflect(Negative.class))) ||
	(equal(lhs, reflect(Negative.class)) && equal(rhs, reflect(Positive.class)))) {
		return top(); // The result could cancel out and become Zero or NonZero
	}

        return lub(lhs, rhs); // Return least upper bound
    }

    // Handle multiplication
    if (operator == BinaryOperator.TIMES) {
        if (equal(lhs, reflect(Zero.class)) || equal(rhs, reflect(Zero.class))) {
            return reflect(Zero.class); // Result is Zero if either operand is Zero
        }

        // If both operands are NonZero, check for Positive and Negative
        if (equal(lhs, reflect(NonZero.class)) && equal(rhs, reflect(NonZero.class))) {
            return reflect(NonZero.class); // Result is NonZero
        }
        
        // If one is Positive and the other is Negative, the result is Negative
        if ((equal(lhs, reflect(Positive.class)) && equal(rhs, reflect(Negative.class))) || 
            (equal(lhs, reflect(Negative.class)) && equal(rhs, reflect(Positive.class)))) {
            return reflect(Negative.class); // Positive * Negative = Negative
        }

        // If both are Positive, the result is Positive
        if (equal(lhs, reflect(Positive.class)) && equal(rhs, reflect(Positive.class))) {
            return reflect(Positive.class); // Positive * Positive = Positive
        }

        return lub(lhs, rhs); // Return least upper bound if we can't determine
    }

    return top(); // Return top for undefined operations
}


  // ========================================================================
  // Useful helpers

  /** Get the top of the lattice */
  private AnnotationMirror top() {
    return analysis.getTypeFactory().getQualifierHierarchy().getTopAnnotations().iterator().next();
  }

  /** Get the bottom of the lattice */
  private AnnotationMirror bottom() {
    return analysis
        .getTypeFactory()
        .getQualifierHierarchy()
        .getBottomAnnotations()
        .iterator()
        .next();
  }

  /** Compute the least-upper-bound of two points in the lattice */
  private AnnotationMirror lub(AnnotationMirror x, AnnotationMirror y) {
    return analysis.getTypeFactory().getQualifierHierarchy().leastUpperBoundQualifiersOnly(x, y);
  }

  /** Compute the greatest-lower-bound of two points in the lattice */
  private AnnotationMirror glb(AnnotationMirror x, AnnotationMirror y) {
    return analysis.getTypeFactory().getQualifierHierarchy().greatestLowerBoundQualifiersOnly(x, y);
  }

  /** Convert a "Class" object (e.g. "Top.class") to a point in the lattice */
  private AnnotationMirror reflect(Class<? extends Annotation> qualifier) {
    return AnnotationBuilder.fromClass(
        analysis.getTypeFactory().getProcessingEnv().getElementUtils(), qualifier);
  }

  /** Determine whether two AnnotationMirrors are the same point in the lattice */
  private boolean equal(AnnotationMirror x, AnnotationMirror y) {
    return AnnotationUtils.areSame(x, y);
  }

  /** `x op y` == `y flip(op) x` */
  private Comparison flip(Comparison op) {
    switch (op) {
      case EQ:
        return Comparison.EQ;
      case NE:
        return Comparison.NE;
      case LT:
        return Comparison.GT;
      case LE:
        return Comparison.GE;
      case GT:
        return Comparison.LT;
      case GE:
        return Comparison.LE;
      default:
        throw new IllegalArgumentException(op.toString());
    }
  }

  /** `x op y` == `!(x negate(op) y)` */
  private Comparison negate(Comparison op) {
    switch (op) {
      case EQ:
        return Comparison.NE;
      case NE:
        return Comparison.EQ;
      case LT:
        return Comparison.GE;
      case LE:
        return Comparison.GT;
      case GT:
        return Comparison.LE;
      case GE:
        return Comparison.LT;
      default:
        throw new IllegalArgumentException(op.toString());
    }
  }

  // ========================================================================
  // Checker Framework plumbing

  public DivByZeroTransfer(CFAnalysis analysis) {
    super(analysis);
  }

  private TransferResult<CFValue, CFStore> implementComparison(
      Comparison op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
    QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
    AnnotationMirror l =
        findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
    AnnotationMirror r =
        findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

    if (l == null || r == null) {
      // this can happen for generic types
      return out;
    }

    CFStore thenStore = out.getThenStore().copy();
    CFStore elseStore = out.getElseStore().copy();

    thenStore.insertValue(
        JavaExpression.fromNode(n.getLeftOperand()), refineLhsOfComparison(op, l, r));

    thenStore.insertValue(
        JavaExpression.fromNode(n.getRightOperand()), refineLhsOfComparison(flip(op), r, l));

    elseStore.insertValue(
        JavaExpression.fromNode(n.getLeftOperand()), refineLhsOfComparison(negate(op), l, r));

    elseStore.insertValue(
        JavaExpression.fromNode(n.getRightOperand()),
        refineLhsOfComparison(flip(negate(op)), r, l));

    return new ConditionalTransferResult<>(out.getResultValue(), thenStore, elseStore);
  }

  private TransferResult<CFValue, CFStore> implementOperator(
      BinaryOperator op, BinaryOperationNode n, TransferResult<CFValue, CFStore> out) {
    QualifierHierarchy hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
    AnnotationMirror l =
        findAnnotation(analysis.getValue(n.getLeftOperand()).getAnnotations(), hierarchy);
    AnnotationMirror r =
        findAnnotation(analysis.getValue(n.getRightOperand()).getAnnotations(), hierarchy);

    if (l == null || r == null) {
      // this can happen for generic types
      return out;
    }

    AnnotationMirror res = arithmeticTransfer(op, l, r);
    CFValue newResultValue =
        analysis.createSingleAnnotationValue(res, out.getResultValue().getUnderlyingType());
    return new RegularTransferResult<>(newResultValue, out.getRegularStore());
  }

  @Override
  public TransferResult<CFValue, CFStore> visitEqualTo(
      EqualToNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.EQ, n, super.visitEqualTo(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNotEqual(
      NotEqualNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.NE, n, super.visitNotEqual(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitGreaterThan(
      GreaterThanNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.GT, n, super.visitGreaterThan(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitGreaterThanOrEqual(
      GreaterThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.GE, n, super.visitGreaterThanOrEqual(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitLessThan(
      LessThanNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.LT, n, super.visitLessThan(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitLessThanOrEqual(
      LessThanOrEqualNode n, TransferInput<CFValue, CFStore> p) {
    return implementComparison(Comparison.LE, n, super.visitLessThanOrEqual(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitIntegerDivision(
      IntegerDivisionNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.DIVIDE, n, super.visitIntegerDivision(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitIntegerRemainder(
      IntegerRemainderNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.MOD, n, super.visitIntegerRemainder(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitFloatingDivision(
      FloatingDivisionNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.DIVIDE, n, super.visitFloatingDivision(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitFloatingRemainder(
      FloatingRemainderNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.MOD, n, super.visitFloatingRemainder(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNumericalMultiplication(
      NumericalMultiplicationNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.TIMES, n, super.visitNumericalMultiplication(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNumericalAddition(
      NumericalAdditionNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.PLUS, n, super.visitNumericalAddition(n, p));
  }

  @Override
  public TransferResult<CFValue, CFStore> visitNumericalSubtraction(
      NumericalSubtractionNode n, TransferInput<CFValue, CFStore> p) {
    return implementOperator(BinaryOperator.MINUS, n, super.visitNumericalSubtraction(n, p));
  }

  private static AnnotationMirror findAnnotation(
      Set<AnnotationMirror> set, QualifierHierarchy hierarchy) {
    if (set.size() == 0) {
      return null;
    }
    Set<? extends AnnotationMirror> tops = hierarchy.getTopAnnotations();
    return hierarchy.findAnnotationInSameHierarchy(set, tops.iterator().next());
  }
}
