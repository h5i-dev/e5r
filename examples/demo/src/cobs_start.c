/* Entry point of the binary the proof is about: decode a fixed frame and
 * exit with the decoded length (qemu-riscv64 examples/demo/cobs/cobs.elf; echo $?). */
struct cobs_report { unsigned long tag, a, b; };
void cobs_decode(struct cobs_report *r, unsigned char *buf, unsigned long len);

static unsigned char frame[] = {3, 'h', 'i', 2, '!', 0};

void _start(void) {
  struct cobs_report r;
  cobs_decode(&r, frame, sizeof frame);
  register long a7 asm("a7") = 93;
  register long a0 asm("a0") = r.tag == 0 ? (long)r.b : 255;
  asm volatile("ecall" : : "r"(a7), "r"(a0) : "memory");
  for (;;) {
  }
}
