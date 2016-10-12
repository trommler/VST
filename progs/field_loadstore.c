struct IntPair {int a; int b; };
struct ToyType {struct IntPair f1; struct IntPair f2[10]; };
struct ToyType2 {struct IntPair g1; int g2[20]; };

struct ToyType p;
struct ToyType2 q;

void toy_sub(void) {
  int i;
  i = p.f1.b;
  p.f1.a = i + 1;
  return;
}

void toy_sub2(void) {
  int i, j;
  i = q.g1.a;
  j = q.g1.b;
  q.g2[0] = j;
  q.g2[1] = i;
  i = q.g2[2];
  j = q.g2[3];
  q.g1.a = i;
  q.g1.b = j;
  q.g2[2] = 0;
  q.g2[3] = 0;
  return;
}

int main()
{
}
