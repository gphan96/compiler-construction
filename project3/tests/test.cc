
struct str {
	int a;
};

struct next {
	str s;
};

int main() {
	next n;

	n.s.a = 10;

	int i;

	i = 20;

	return i;
}