
struct str {
	int a;
};

struct next {
	str s;
};

int main() {
	int i = 0, j;
	double d = 0.0, f;
	j = i++;
	j = ++i;
	j = i--;
	j = --i;
	f = d++;
	f = ++d;
	f = d--;
	f = --d;

	return i;
}