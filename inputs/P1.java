class P5 {
	void m1() {
		A x,y,z;
		B a,b,c,i,j;
		boolean cond = false;
		x = new A();
		y = new A();
		x.b_ref = new B();
		y.b_ref = new B();
		if (cond) {
			z = x;
			i = z.b_ref;
		} else {
			z = y;
			j = z.b_ref;
		}
		a = new B();
		z.b_ref = a;	// Weak update
		b = x.b_ref;
		c = y.b_ref;
	}
}
class A{
	B b_ref;
	void foo() {
		System.out.println(10);
	}
}
class B{
	void bar() {
		System.out.println(10);
	}
}
class P1{}