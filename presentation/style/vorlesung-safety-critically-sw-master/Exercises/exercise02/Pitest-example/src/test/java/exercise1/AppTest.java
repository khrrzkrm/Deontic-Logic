package exercise1;


import org.junit.Test;
import static org.junit.Assert.*;

import org.junit.Before;

import exercise1.Triangle;
import exercise1.Triangle.Type;

public class AppTest{
	Triangle codeUnderTest;

	@Before
	public void initApp() {
		codeUnderTest = new Triangle();		
	}

	@Test
	public void validScalene() {
		assertEquals(Type.SCALENE, codeUnderTest.triangleType(2, 3, 4));
	}
	
	@Test
	public void validEquiliteral() {
		//	TODO: Add test cases to fulfill coverage	
	}
	
	@Test
	public void validIsosceles() {
        assertEquals(Type.ISOSCELES, codeUnderTest.triangleType(1, 1, 1)); 
	}
	
	@Test
	public void invalid() {
		assertEquals(Type.INVALID, codeUnderTest.triangleType(0, 1, 1)); 
        assertEquals(Type.INVALID, codeUnderTest.triangleType(1, 0, 1));  
        assertEquals(Type.INVALID, codeUnderTest.triangleType(1, 1, 0));
        assertEquals(Type.INVALID, codeUnderTest.triangleType(3, 1, 1));  
        assertEquals(Type.INVALID, codeUnderTest.triangleType(1, 3, 1));  
        assertEquals(Type.INVALID, codeUnderTest.triangleType(1, 1, 3));  		
    }

}
