abstract class Function {
	Object arg, res;
	abstract void apply();
} 

class Res {
	long res = 0;
}

public class ThreadSafety {
	// Encoding of:
	// sum n = if (n == 0) then 0 else n + sum (n-1)
	static class Sum extends Function {
		void apply() {	
			long n = (Long) arg;
			if (n == 0)
				res = 0L;
			else {
				arg = n-1;
				this.apply();
				long r = (Long) res;
				res = n + r; 
			}
		}
	};
	
	public static void main(String args[]) {
		// SEQUENTIAL CODE (CORRECT RESULT)
		System.out.println("SEQUENTIAL CODE (CORRECT RESULT)");
		Function sum = new Sum();
		sum.arg = 6000L;
		sum.apply();
		System.out.println("sum 6000 = " + sum.res);
		sum.arg = 5000L;
		sum.apply();
		System.out.println("sum 5000 = " + sum.res);
		
		// THREAD-UNSAFE CODE
		System.out.println("\nTHREAD-UNSAFE CODE (SOMETIMES GIVES INCORRECT RESULT)");
		Res res1 = new Res();
		Res res2 = new Res();
		
		Thread thread1 = new Thread() {
		    public void run() {
		    	sum.arg = 6000L;
				sum.apply();
				res1.res = (Long) sum.res;
		    }
		};
		
		Thread thread2 = new Thread() {
		    public void run() {
		    	sum.arg = 5000L;
				sum.apply();
				res2.res = (Long) sum.res;
		    }
		};
		
		thread1.start();
		thread2.start();
		
		try {
			thread1.join();
			thread2.join();
		} catch (Exception e) {}
		
		System.out.println("sum 6000 = " + res1.res);
		System.out.println("sum 5000 = " + res2.res);
		
		// THREAD-SAFE CODE
		System.out.println("\nTHREAD-SAFE CODE (ALWAYS GIVES CORRECT RESULT)");
		thread1 = new Thread() {
		    public void run() {
		    	Function sum1 = new Sum();
		    	sum1.arg = 6000L;
				sum1.apply();
				res1.res = (Long) sum1.res;
		    }
		};
		
		thread2 = new Thread() {
		    public void run() {
		    	Function sum2 = new Sum();
		    	sum2.arg = 5000L;
				sum2.apply();
				res2.res = (Long) sum2.res;
		    }
		};
		
		thread1.start();
		thread2.start();
		
		try {
			thread1.join();
			thread2.join();
		} catch (Exception e) {}
		
		System.out.println("sum 6000 = " + res1.res);
		System.out.println("sum 5000 = " + res2.res);
		
		/*
		TCE version follows similarly; one extra difference
		for thread-safe code is that the
		auxiliary control structure Next has to be
		local for the function instances, i.e. functions
		need to be provided with an instance of
		class Next {
			Function next;
		} 
		*/
		
	}
}
