package quickcheck_exercise;

import com.pholser.junit.quickcheck.Property;
import com.pholser.junit.quickcheck.generator.InRange;
import com.pholser.junit.quickcheck.runner.JUnitQuickcheck;
import org.junit.runner.RunWith;
import org.junit.Before;
import static org.hamcrest.Matchers.*;

import static org.junit.Assert.*;
import static org.junit.Assume.*;

import java.util.List;

@RunWith(JUnitQuickcheck.class)
public class PrimeNumberTests {
	private PrimeCalculator CodeUnderTest;
    @Before
    public void init() {
    	CodeUnderTest = new PrimeCalculator();		
    }
    
    @Property
    public void primeFactorsShouldBePrimeNumbers(@InRange(min = "2", max = "999999999") Long a) {
    	List<Long> factorsA = CodeUnderTest.PrimeFactorization(a);    	
    	for(int i=0; i<factorsA.size(); i++) {
    		assertTrue("All prime factors should be primes!" ,CodeUnderTest.isPrime(factorsA.get(i)));
    	}
    }
	
    
    @Property 
    public void productOfPrimeFactorsShouldBeTheOriginalNumber(@InRange(min = "1", max = "9999999999999") Long a) {
    	List<Long> factorsA = CodeUnderTest.PrimeFactorization(a);
    	Long expectedResult = (long) 1;
    	for (int i = 0; i < factorsA.size(); i++) {
    		expectedResult *= factorsA.get(i);
		}
    	assertEquals("The product of the prime factors should equal the original number!" ,expectedResult, a);
    }
    


    @Property
    public void factorizationsAreUnique(@InRange(min = "2", max = "1000") Long a, @InRange(min = "2", max = "1000") Long b) {
    	assumeThat(a, not(equalTo(b)));
    	List<Long> factorsA = CodeUnderTest.PrimeFactorization(a);    	
    	List<Long> factorsB = CodeUnderTest.PrimeFactorization(b);    	
    	
        assertThat(factorsA, not(equalTo(factorsB)));

    }
}