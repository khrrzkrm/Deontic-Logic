package exercise1;


public class Triangle{
	
	public static enum Type{
		SCALENE, ISOSCELES, EQUILITERAL, INVALID;
	}
	public Type triangleType(int a, int b, int c) {
	    if (a<1 || b<1 || c<1){
	        return Type.INVALID;
	    }
	    if ((a+b<=c) || (a+c<=b) || (b+c<a)){
	    	return Type.INVALID;
	    }
	    if (a==b && b==c){
	        return Type.ISOSCELES;
	    }
	    if (a==b || a==c || b==c){
	        return Type.EQUILITERAL;
	    }
	    return Type.SCALENE;
	}

}
