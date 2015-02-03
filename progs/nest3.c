struct a {int x1,x2;};
struct b {struct a y1, y2;};
struct c {struct b z1,z2;};

struct c p;

int get(void) {
  int i;
  i = p.z2.y2.x2;
  return i;
}

void set(int i) {
  p.z2.y2.x2 = i;
}

void multi_command(void) {
  int i;
  i = p.z1.y1.x1;
  p.z2.y2.x2 = i + 1;
  i = p.z1.y1.x2;
  p.z2.y2.x1 = i + 2;
  i = p.z1.y2.x1;
  p.z2.y1.x2 = i + 3;
  i = p.z1.y2.x2;
  p.z2.y1.x1 = i + 4;
}


