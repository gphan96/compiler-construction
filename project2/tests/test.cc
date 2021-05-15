
struct s {
	int i;
};

void f(double k) {
	int z;
}

void main() {
	s s;

	double j = 10;

	f(10.0);
	//true ? 1 : 1; //pass OK
	//1 ? 1 : 1; //fail OK
	//1.5 ? 1 : 1; //fail OK
	//f() ? 1 : 1; //fail
	//s ? 1 : 1; //fail OK


	//true ? true : true; //pass OK
	//true ? 1 : 1; //pass OK
	//true ? 1.5 : 1.5; //pass OK
	//true ? f() : f(); //pass OK
	//true ? s : s; //pass OK

	//true ? true : 1; //fail OK
	//true ? true : 1.5; //fail OK
	//true ? true : f(); //fail OK
	//true ? true : s; //fail OK

	//true ? 1 : true; //fail OK
	//true ? 1 : 1.5; //pass OK
	//true ? 1 : f(); //fail OK
	//true ? 1 : s; //fail OK

	//true ? 1.5 : true; //fail
	//true ? 1.5 : 1; //pass OK
	//true ? 1.5 : f(); //fail OK
	//true ? 1.5 : s; //fail OK

	//true ? f() : true; //fail OK
	//true ? f() : 1; //fail OK
	//true ? f() : 1.5; //fail OK
	//true ? f() : s; //fail OK

	//true ? s : true; //fail OK
	//true ? s : 1; //fail OK
	//true ? s : 1.5; //fail OK
	//true ? s : f(); //fail OK

	return;
}
