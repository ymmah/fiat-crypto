static void freeze(uint32_t out[11], const uint32_t in1[11]) {
  { const uint32_t x19 = in1[10];
  { const uint32_t x20 = in1[9];
  { const uint32_t x18 = in1[8];
  { const uint32_t x16 = in1[7];
  { const uint32_t x14 = in1[6];
  { const uint32_t x12 = in1[5];
  { const uint32_t x10 = in1[4];
  { const uint32_t x8 = in1[3];
  { const uint32_t x6 = in1[2];
  { const uint32_t x4 = in1[1];
  { const uint32_t x2 = in1[0];
  { uint32_t x22, ℤ x23 = Op (Syntax.SubWithGetBorrow 21 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 3) (Syntax.TWord 5) Syntax.TZ) (0x0, Return x2, 0x1);
  { uint32_t x25, ℤ x26 = Op (Syntax.SubWithGetBorrow 20 Syntax.TZ (Syntax.TWord 5) (Syntax.TWord 3) (Syntax.TWord 5) Syntax.TZ) (Return x23, Return x4, 0x0);
  { uint32_t x28, ℤ x29 = Op (Syntax.SubWithGetBorrow 21 Syntax.TZ (Syntax.TWord 5) (Syntax.TWord 3) (Syntax.TWord 5) Syntax.TZ) (Return x26, Return x6, 0x0);
  { uint32_t x31, ℤ x32 = Op (Syntax.SubWithGetBorrow 20 Syntax.TZ (Syntax.TWord 5) (Syntax.TWord 3) (Syntax.TWord 5) Syntax.TZ) (Return x29, Return x8, 0x0);
  { uint32_t x34, uint8_t x35 = Op (Syntax.SubWithGetBorrow 20 Syntax.TZ (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x32, Return x10, 0xfc000);
  { uint32_t x37, uint8_t x38 = Op (Syntax.SubWithGetBorrow 21 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x35, Return x12, 0x1fffff);
  { uint32_t x40, uint8_t x41 = Op (Syntax.SubWithGetBorrow 20 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x38, Return x14, 0xfffff);
  { uint32_t x43, uint8_t x44 = Op (Syntax.SubWithGetBorrow 20 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x41, Return x16, 0xfffff);
  { uint32_t x46, uint8_t x47 = Op (Syntax.SubWithGetBorrow 21 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x44, Return x18, 0x1fffff);
  { uint32_t x49, uint8_t x50 = Op (Syntax.SubWithGetBorrow 20 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x47, Return x20, 0xfffff);
  { uint32_t x52, uint8_t x53 = Op (Syntax.SubWithGetBorrow 20 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x50, Return x19, 0xfffff);
  { uint32_t x54 = cmovznz32(x53, 0x0, 0xffffffff);
  { uint8_t x55 = ((uint8_t)x54 & 0x1);
  { uint32_t x57, uint8_t x58 = Op (Syntax.AddWithGetCarry 21 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 3)) (0x0, Return x22, Return x55);
  { uint32_t x60, uint8_t x61 = Op (Syntax.AddWithGetCarry 20 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x58, Return x25, 0x0);
  { uint32_t x63, uint8_t x64 = Op (Syntax.AddWithGetCarry 21 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x61, Return x28, 0x0);
  { uint32_t x66, uint8_t x67 = Op (Syntax.AddWithGetCarry 20 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x64, Return x31, 0x0);
  { uint32_t x68 = (x54 & 0xfc000);
  { uint32_t x70, uint8_t x71 = Op (Syntax.AddWithGetCarry 20 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x67, Return x34, Return x68);
  { uint32_t x72 = (x54 & 0x1fffff);
  { uint32_t x74, uint8_t x75 = Op (Syntax.AddWithGetCarry 21 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x71, Return x37, Return x72);
  { uint32_t x76 = (x54 & 0xfffff);
  { uint32_t x78, uint8_t x79 = Op (Syntax.AddWithGetCarry 20 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x75, Return x40, Return x76);
  { uint32_t x80 = (x54 & 0xfffff);
  { uint32_t x82, uint8_t x83 = Op (Syntax.AddWithGetCarry 20 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x79, Return x43, Return x80);
  { uint32_t x84 = (x54 & 0x1fffff);
  { uint32_t x86, uint8_t x87 = Op (Syntax.AddWithGetCarry 21 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x83, Return x46, Return x84);
  { uint32_t x88 = (x54 & 0xfffff);
  { uint32_t x90, uint8_t x91 = Op (Syntax.AddWithGetCarry 20 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x87, Return x49, Return x88);
  { uint32_t x92 = (x54 & 0xfffff);
  { uint32_t x94, uint8_t _ = Op (Syntax.AddWithGetCarry 20 (Syntax.TWord 3) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 5) (Syntax.TWord 3)) (Return x91, Return x52, Return x92);
  out[0] = x57;
  out[1] = x60;
  out[2] = x63;
  out[3] = x66;
  out[4] = x70;
  out[5] = x74;
  out[6] = x78;
  out[7] = x82;
  out[8] = x86;
  out[9] = x90;
  out[10] = x94;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}