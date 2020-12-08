package quickcheck_exercise;

import java.util.ArrayList;
import java.util.List;

public class PrimeCalculator 
{
    List<Long> PrimeFactorization(Long i) {
      List<Long> primeFactors = new ArrayList<>();
      long divisor = 1;
      double squareRoot = Math.sqrt(i);
      while (i > 1)
      {
        divisor++;
        while (i % divisor == 0)
        {
          primeFactors.add(divisor);
          i /= divisor;
        }
        if (divisor > squareRoot)
        {
          divisor = i - 1;
        }
      }
      return primeFactors;
    }
        
    public boolean isPrime(Long number) 
    {
            if (number == 2) 
                return true;
            if (number < 2 || number % 2 == 0) 
                return false;
            for (int i = 3; i * i <= number; i += 2)
                if (number % i == 0) 
                    return false;
            return true;
    }
}
