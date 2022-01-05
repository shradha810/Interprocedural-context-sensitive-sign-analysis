package CallGraphCreation;

import java.util.*;

public class Sample_test {
      public static int foo(int x, int y, int z) {
		int r;
		if(z >= 0){
			r = factorial(z);
		}
		else{
			r = x * y;
		}
		r = r + bar(x, y);
		return(r);
	}

	public static int bar(int u, int v) {
		u = factorial(u);
		v = factorial(v);
		int w = u + v;
		return(w);
	}

	public static int baz(int s){
		int t = s * s;
		t = -t;
		return(t);
	}

	public static int factorial(int input) {
		int i, res;
		res = 1;
		for(i = 2; i <= input; i++){
			res = res * i;
		}
		return(res);
	}

	public static void main(String[] args) {	
		int a = 6;
		int n = factorial(a);
		int p = foo(-2, -3, 4);
		int q = p * baz(-10);

		System.out.printf("a: %d \nn: %d \np: %d \nq: %d \n", a, n, p, q);
	}
}