
struct str {
	int a;
};

struct next {
	str s;
};

int main() {
	next n;

	return n.s.a;
}