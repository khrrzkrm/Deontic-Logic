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
    	// TODO: Write property-based test
    }
	
    // TODO: Write two more.
}