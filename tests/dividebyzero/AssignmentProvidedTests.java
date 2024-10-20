import org.checkerframework.checker.dividebyzero.qual.*;

// A simple test case for your divide-by-zero checker.
// The file contains "// ::" comments to indicate expected
// errors and warnings.
//
// Passing this test does not guarantee a perfect grade on this assignment,
// but it is an important start. You should always write your own test cases,
// in addition to using those provided to you.
class AssignmentProvidedTests {

  public static void f() {
    int one = 1;
    int zero = 0;
    // :: error: divide.by.zero
    int x = one / zero;
    int y = zero / one;
    // :: error: divide.by.zero
    int z = x / y;
    String s = "hello";
  }

  public static void g(int y) {
    if (y == 0) {
      // :: error: divide.by.zero
      int x = 1 / y;
    } else {
      int x = 1 / y;
    }

    if (y != 0) {
      int x = 1 / y;
    } else {
      // :: error: divide.by.zero
      int x = 1 / y;
    }

    if (!(y == 0)) {
      int x = 1 / y;
    } else {
      // :: error: divide.by.zero
      int x = 1 / y;
    }

    if (!(y != 0)) {
      // :: error: divide.by.zero
      int x = 1 / y;
    } else {
      int x = 1 / y;
    }

    if (y < 0) {
      int x = 1 / y;
    }

    if (y <= 0) {
      // :: error: divide.by.zero
      int x = 1 / y;
    }

    if (y > 0) {
      int x = 1 / y;
    }

    if (y >= 0) {
      // :: error: divide.by.zero
      int x = 1 / y;
    }
  }

  public static void h() {
    int zero_the_hard_way = 0 + 0 - 0 * 0;
    // :: error: divide.by.zero
    int x = 1 / zero_the_hard_way;

    int one_the_hard_way = 0 * 1 + 1;
    int y = 1 / one_the_hard_way;
  }

  public static void l() {
    // :: error: divide.by.zero
    int a = 1 / (1 - 1);
    int y = 1;
    // :: error: divide.by.zero
    int x = 1 / (y - y);
    int z = y - y;
    // :: error: divide.by.zero
    int k = 1 / z;
  }

   public static void loopTest(int a) {
    // Division inside a loop
    for (int i = 0; i < 10; i++) {
      if (a == 0) {
        // :: error: divide.by.zero
        int result = i / a;
      }
    }
  }

   public void testChainedArithmetic() {
    int a = 3;
    int b = 6;
    int c = 2;
    // :: error: divide.by.zero
    int result = a / (b - b); 
   }
   
   public void testDivideByZeroWithMultipleOperators() {
    int a = 5;
    int b = 10;
    // :: error: divide.by.zero
    int result = (a * 2) / (b - 10); // b - 10 equals zero, should detect division by zero
    }
    
   public void anotherCase(int x, int y) {
    if (x > y) {
      // :: error: divide.by.zero
      int result = x / y; 
    }
  }
  
   public static void anotherCase1() {
    int x = -1;
    int y = 1;
    int z = 0;
    int a = y/x;
    if (x != y) {
      // :: error: divide.by.zero
      int result = x / (x+y); 
    }
    
    if(0 == z) {
      // :: error: divide.by.zero    
    	int product = y / z;
    }
    
    if (-5 < x){
    	int answer = z / (y-x);
    }
    
    if (x <= 0){
    	int answer2 = 5/x;
    }
    
  }
  
  public static void coinFLip(){
	int x = coinflip()? 1 : -1;
	int y = coinflip()? 1: -1; 
	int z = x + y;  
	// :: error: divide.by.zero
	int a = 5/z;	
  }


}
