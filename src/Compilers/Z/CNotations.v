Require Export Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Export Crypto.Compilers.Z.HexNotationConstants.
Require Export Crypto.Util.Notations.

Reserved Notation "T x = A ; b" (at level 200, b at level 200, format "T  x  =  A ; '//' b").
Reserved Notation "T x = A ; 'return' b" (at level 200, b at level 200, format "T  x  =  A ; '//' 'return'  b").
Reserved Notation "T x = A ; 'return' ( b0 , b1 , .. , b2 )" (at level 200, format "T  x  =  A ; '//' 'return'  ( b0 ,  b1 ,  .. ,  b2 )").
Reserved Notation "T0 x , T1 y = A ; b" (at level 200, b at level 200, format "T0  x ,  T1  y  =  A ; '//' b").
Reserved Notation "T0 x , T1 y = A ; 'return' b" (at level 200, b at level 200, format "T0  x ,  T1  y  =  A ; '//' 'return'  b").
Reserved Notation "T0 x , T1 y = A ; 'return' ( b0 , b1 , .. , b2 )" (at level 200, format "T0  x ,  T1  y  =  A ; '//' 'return'  ( b0 ,  b1 ,  .. ,  b2 )").
Reserved Notation "v == 0 ? a : b" (at level 40, a at level 10, b at level 10).
Reserved Notation "v == 0 ?ℤ a : b" (at level 40, a at level 10, b at level 10).
Reserved Notation "x & y" (at level 40).
Reserved Notation "x | y" (at level 45).

Global Open Scope expr_scope.

Notation "T x = A ; b" := (LetIn (tx:=T) A (fun x => b)) : expr_scope.
Notation "T x = A ; 'return' b" := (LetIn (tx:=T) A (fun x => Var b)) : expr_scope.
Notation "T x = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=T) A (fun x => Pair .. (Pair b0%expr b1%expr) .. b2%expr)) : expr_scope.
Notation "T x = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=T) A (fun x => Pair .. (Pair (Var b0) (Var b1)) .. (Var b2))) : expr_scope.
Notation "T0 x , T1 y = A ; b" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => b)) : expr_scope.
Notation "T0 x , T1 y = A ; 'return' b" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => Var b)) : expr_scope.
(*Notation "T0 x , T1 y = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => (Pair .. (Pair b0%expr b1%expr) .. b2%expr))) : expr_scope.*) (* Error: Unsupported construction in recursive notations., https://coq.inria.fr/bugs/show_bug.cgi?id=5523 *)
(*Notation "T0 x , T1 y = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => (Pair .. (Pair (Var b0) (Var b1)) .. (Var b2)))) : expr_scope.*) (* Error: Unsupported construction in recursive notations., https://coq.inria.fr/bugs/show_bug.cgi?id=5523 *)

(* for now, handle with
<<
sed s':^\([^,]*\) \([^, ]*\)\(\s*\),\(.*\)\(addcarryx.*\))\([; ]*\)$:\1 \2\3;\4_\5, \&\2)\6:'
sed s':^\([^,]*\) \([^, ]*\)\(\s*\),\(.*\)\(subborrow.*\))\([; ]*\)$:\1 \2\3;\4_\5, \&\2)\6:'
sed s':^\([^,]*\) \([^, ]*\)\(\s*\),\(.*\)\(mulx.*\))\([; ]*\)$:\1 \2\3;\4_\5, \&\2)\6:'
>>

   Once we get https://coq.inria.fr/bugs/show_bug.cgi?id=5526, we can print actual C notations:
<<
Reserved Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c_in , a , b , & out ) ; REST"
 (at level 200, REST at level 200, only printing format "T0  out ; '//' T1  c_out  =  '_addcarryx_u32' ( c_in ,  a ,  b ,  & out ) ; '//' REST").
Reserved Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c_in , a , b , & out ) ; REST"
 (at level 200, REST at level 200, only printing format "T0  out ; '//' T1  c_out  =  '_addcarryx_u64' ( c_in ,  a ,  b ,  & out ) ; '//' REST").
>> *)
Reserved Notation "'addcarryx_u32' ( c , a , b )" (format "'addcarryx_u32' ( c ,  a ,  b )").
Reserved Notation "'addcarryx_u64' ( c , a , b )" (format "'addcarryx_u64' ( c ,  a ,  b )").
Reserved Notation "'addcarryx_u128' ( c , a , b )" (format "'addcarryx_u128' ( c ,  a ,  b )").
Reserved Notation "'addcarryx_u25' ( c , a , b )" (format "'addcarryx_u25' ( c ,  a ,  b )").
Reserved Notation "'addcarryx_u26' ( c , a , b )" (format "'addcarryx_u26' ( c ,  a ,  b )").
Reserved Notation "'addcarryx_u51' ( c , a , b )" (format "'addcarryx_u51' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u32' ( c , a , b )" (format "'subborrow_u32' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u64' ( c , a , b )" (format "'subborrow_u64' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u128' ( c , a , b )" (format "'subborrow_u128' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u25' ( c , a , b )" (format "'subborrow_u25' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u26' ( c , a , b )" (format "'subborrow_u26' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u51' ( c , a , b )" (format "'subborrow_u51' ( c ,  a ,  b )").
Reserved Notation "'addcarryx_u32ℤ' ( c , a , b )" (format "'addcarryx_u32ℤ' ( c ,  a ,  b )").
Reserved Notation "'addcarryx_u64ℤ' ( c , a , b )" (format "'addcarryx_u64ℤ' ( c ,  a ,  b )").
Reserved Notation "'addcarryx_u128ℤ' ( c , a , b )" (format "'addcarryx_u128ℤ' ( c ,  a ,  b )").
Reserved Notation "'addcarryx_u25ℤ' ( c , a , b )" (format "'addcarryx_u25ℤ' ( c ,  a ,  b )").
Reserved Notation "'addcarryx_u26ℤ' ( c , a , b )" (format "'addcarryx_u26ℤ' ( c ,  a ,  b )").
Reserved Notation "'addcarryx_u51ℤ' ( c , a , b )" (format "'addcarryx_u51ℤ' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u32ℤ' ( c , a , b )" (format "'subborrow_u32ℤ' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u64ℤ' ( c , a , b )" (format "'subborrow_u64ℤ' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u128ℤ' ( c , a , b )" (format "'subborrow_u128ℤ' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u25ℤ' ( c , a , b )" (format "'subborrow_u25ℤ' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u26ℤ' ( c , a , b )" (format "'subborrow_u26ℤ' ( c ,  a ,  b )").
Reserved Notation "'subborrow_u51ℤ' ( c , a , b )" (format "'subborrow_u51ℤ' ( c ,  a ,  b )").

Reserved Notation "'mulx_u32' ( a , b )" (format "'mulx_u32' ( a ,  b )").
Reserved Notation "'mulx_u64' ( a , b )" (format "'mulx_u64' ( a ,  b )").
Reserved Notation "'mulx_u128' ( a , b )" (format "'mulx_u128' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u32' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u64' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u128' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u32' ( a , b )" (format "'(uint8_t)' 'mulx_u32' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u64' ( a , b )" (format "'(uint8_t)' 'mulx_u64' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u128' ( a , b )" (format "'(uint8_t)' 'mulx_u128' ( a ,  b )").
Reserved Notation "'mulx_u32_out_u8' ( a , b )" (format "'mulx_u32_out_u8' ( a ,  b )").
Reserved Notation "'mulx_u64_out_u8' ( a , b )" (format "'mulx_u64_out_u8' ( a ,  b )").
Reserved Notation "'mulx_u128_out_u8' ( a , b )" (format "'mulx_u128_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u32_out_u8' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u32_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u64_out_u8' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u64_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u128_out_u8' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u128_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" (format "'(uint8_t)' 'mulx_u32_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" (format "'(uint8_t)' 'mulx_u64_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" (format "'(uint8_t)' 'mulx_u128_out_u8' ( a ,  b )").
Reserved Notation "'mulx_u32_out_u1' ( a , b )" (format "'mulx_u32_out_u1' ( a ,  b )").
Reserved Notation "'mulx_u64_out_u1' ( a , b )" (format "'mulx_u64_out_u1' ( a ,  b )").
Reserved Notation "'mulx_u128_out_u1' ( a , b )" (format "'mulx_u128_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u32_out_u1' ( a , b )" (format "'(uint8_t)' 'mulx_u32_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u64_out_u1' ( a , b )" (format "'(uint8_t)' 'mulx_u64_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u128_out_u1' ( a , b )" (format "'(uint8_t)' 'mulx_u128_out_u1' ( a ,  b )").

Reserved Notation "'mulx_u32ℤ' ( a , b )" (format "'mulx_u32ℤ' ( a ,  b )").
Reserved Notation "'mulx_u64ℤ' ( a , b )" (format "'mulx_u64ℤ' ( a ,  b )").
Reserved Notation "'mulx_u128ℤ' ( a , b )" (format "'mulx_u128ℤ' ( a ,  b )").

Reserved Notation "'cmovznz32' ( v , a , b )" (format "'cmovznz32' ( v ,  a ,  b )").
Reserved Notation "'cmovznz64' ( v , a , b )" (format "'cmovznz64' ( v ,  a ,  b )").
Reserved Notation "'cmovznz128' ( v , a , b )" (format "'cmovznz128' ( v ,  a ,  b )").
Reserved Notation "'cmovznz' ( v , a , b )" (format "'cmovznz' ( v ,  a ,  b )").
Reserved Notation "'cmovznzℤ' ( v , a , b )" (format "'cmovznzℤ' ( v ,  a ,  b )").
(* python:
<<
#!/usr/bin/env python
# -*- coding: utf-8 -*-
import math

PARENTHESIZED = True
ADD_CARRY_SUB_BORROW_SIZES = (32, 64, 128, 25, 26, 51)

print(r"""Require Export Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Export Crypto.Compilers.Z.HexNotationConstants.
Require Export Crypto.Util.Notations.

Reserved Notation "T x = A ; b" (at level 200, b at level 200, format "T  x  =  A ; '//' b").
Reserved Notation "T x = A ; 'return' b" (at level 200, b at level 200, format "T  x  =  A ; '//' 'return'  b").
Reserved Notation "T x = A ; 'return' ( b0 , b1 , .. , b2 )" (at level 200, format "T  x  =  A ; '//' 'return'  ( b0 ,  b1 ,  .. ,  b2 )").
Reserved Notation "T0 x , T1 y = A ; b" (at level 200, b at level 200, format "T0  x ,  T1  y  =  A ; '//' b").
Reserved Notation "T0 x , T1 y = A ; 'return' b" (at level 200, b at level 200, format "T0  x ,  T1  y  =  A ; '//' 'return'  b").
Reserved Notation "T0 x , T1 y = A ; 'return' ( b0 , b1 , .. , b2 )" (at level 200, format "T0  x ,  T1  y  =  A ; '//' 'return'  ( b0 ,  b1 ,  .. ,  b2 )").
Reserved Notation "v == 0 ? a : b" (at level 40, a at level 10, b at level 10).
Reserved Notation "v == 0 ?ℤ a : b" (at level 40, a at level 10, b at level 10).
Reserved Notation "x & y" (at level 40).
Reserved Notation "x | y" (at level 45).

Global Open Scope expr_scope.

Notation "T x = A ; b" := (LetIn (tx:=T) A (fun x => b)) : expr_scope.
Notation "T x = A ; 'return' b" := (LetIn (tx:=T) A (fun x => Var b)) : expr_scope.
Notation "T x = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=T) A (fun x => Pair .. (Pair b0%expr b1%expr) .. b2%expr)) : expr_scope.
Notation "T x = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=T) A (fun x => Pair .. (Pair (Var b0) (Var b1)) .. (Var b2))) : expr_scope.
Notation "T0 x , T1 y = A ; b" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => b)) : expr_scope.
Notation "T0 x , T1 y = A ; 'return' b" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => Var b)) : expr_scope.
(""" + r"""*Notation "T0 x , T1 y = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => (Pair .. (Pair b0%expr b1%expr) .. b2%expr))) : expr_scope.*""" + r""") (""" + r"""* Error: Unsupported construction in recursive notations., https://coq.inria.fr/bugs/show_bug.cgi?id=5523 *""" + r""")
(""" + r"""*Notation "T0 x , T1 y = A ; 'return' ( b0 , b1 , .. , b2 )" := (LetIn (tx:=Prod T0 T1) A (fun '((x, y)%core) => (Pair .. (Pair (Var b0) (Var b1)) .. (Var b2)))) : expr_scope.*""" + r""") (""" + r"""* Error: Unsupported construction in recursive notations., https://coq.inria.fr/bugs/show_bug.cgi?id=5523 *""" + r""")

(""" + r"""* for now, handle with
<<
sed s':^\([^,]*\) \([^, ]*\)\(\s*\),\(.*\)\(addcarryx.*\))\([; ]*\)$:\1 \2\3;\4_\5, \&\2)\6:'
sed s':^\([^,]*\) \([^, ]*\)\(\s*\),\(.*\)\(subborrow.*\))\([; ]*\)$:\1 \2\3;\4_\5, \&\2)\6:'
sed s':^\([^,]*\) \([^, ]*\)\(\s*\),\(.*\)\(mulx.*\))\([; ]*\)$:\1 \2\3;\4_\5, \&\2)\6:'
>>

   Once we get https://coq.inria.fr/bugs/show_bug.cgi?id=5526, we can print actual C notations:
<<
Reserved Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c_in , a , b , & out ) ; REST"
 (at level 200, REST at level 200, only printing format "T0  out ; '//' T1  c_out  =  '_addcarryx_u32' ( c_in ,  a ,  b ,  & out ) ; '//' REST").
Reserved Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c_in , a , b , & out ) ; REST"
 (at level 200, REST at level 200, only printing format "T0  out ; '//' T1  c_out  =  '_addcarryx_u64' ( c_in ,  a ,  b ,  & out ) ; '//' REST").
>> *""" + r""")""")
for postfix in ('', 'ℤ'):
    for opn in ('addcarryx', 'subborrow'):
        for sz in ADD_CARRY_SUB_BORROW_SIZES:
            print(r"""Reserved Notation "'%s_u%d%s' ( c , a , b )" (format "'%s_u%d%s' ( c ,  a ,  b )").""" % (opn, sz, postfix, opn, sz, postfix))
print(r"""
Reserved Notation "'mulx_u32' ( a , b )" (format "'mulx_u32' ( a ,  b )").
Reserved Notation "'mulx_u64' ( a , b )" (format "'mulx_u64' ( a ,  b )").
Reserved Notation "'mulx_u128' ( a , b )" (format "'mulx_u128' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u32' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u64' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u128' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u32' ( a , b )" (format "'(uint8_t)' 'mulx_u32' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u64' ( a , b )" (format "'(uint8_t)' 'mulx_u64' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u128' ( a , b )" (format "'(uint8_t)' 'mulx_u128' ( a ,  b )").
Reserved Notation "'mulx_u32_out_u8' ( a , b )" (format "'mulx_u32_out_u8' ( a ,  b )").
Reserved Notation "'mulx_u64_out_u8' ( a , b )" (format "'mulx_u64_out_u8' ( a ,  b )").
Reserved Notation "'mulx_u128_out_u8' ( a , b )" (format "'mulx_u128_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u32_out_u8' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u32_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u64_out_u8' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u64_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u128_out_u8' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u128_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" (format "'(uint8_t)' 'mulx_u32_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" (format "'(uint8_t)' 'mulx_u64_out_u8' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" (format "'(uint8_t)' 'mulx_u128_out_u8' ( a ,  b )").
Reserved Notation "'mulx_u32_out_u1' ( a , b )" (format "'mulx_u32_out_u1' ( a ,  b )").
Reserved Notation "'mulx_u64_out_u1' ( a , b )" (format "'mulx_u64_out_u1' ( a ,  b )").
Reserved Notation "'mulx_u128_out_u1' ( a , b )" (format "'mulx_u128_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" (format "'(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u32_out_u1' ( a , b )" (format "'(uint8_t)' 'mulx_u32_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u64_out_u1' ( a , b )" (format "'(uint8_t)' 'mulx_u64_out_u1' ( a ,  b )").
Reserved Notation "'(uint8_t)' 'mulx_u128_out_u1' ( a , b )" (format "'(uint8_t)' 'mulx_u128_out_u1' ( a ,  b )").

Reserved Notation "'mulx_u32ℤ' ( a , b )" (format "'mulx_u32ℤ' ( a ,  b )").
Reserved Notation "'mulx_u64ℤ' ( a , b )" (format "'mulx_u64ℤ' ( a ,  b )").
Reserved Notation "'mulx_u128ℤ' ( a , b )" (format "'mulx_u128ℤ' ( a ,  b )").

Reserved Notation "'cmovznz32' ( v , a , b )" (format "'cmovznz32' ( v ,  a ,  b )").
Reserved Notation "'cmovznz64' ( v , a , b )" (format "'cmovznz64' ( v ,  a ,  b )").
Reserved Notation "'cmovznz128' ( v , a , b )" (format "'cmovznz128' ( v ,  a ,  b )").
Reserved Notation "'cmovznz' ( v , a , b )" (format "'cmovznz' ( v ,  a ,  b )").
Reserved Notation "'cmovznzℤ' ( v , a , b )" (format "'cmovznzℤ' ( v ,  a ,  b )").
(""" + r"""* python:
<<""")

print(open(__file__).read())

print('>> *' + ')')

OPEN = ('( ' if PARENTHESIZED else '')
CLOSE = (' )' if PARENTHESIZED else '')

def log2_up(x):
    return int(math.ceil(math.log(x, 2)))
types = ('uint8_t/*bool*/', 'uint8_t', 'uint8_t', 'uint8_t', 'uint16_t', 'uint32_t', 'uint64_t', 'uint128_t', 'uint256_t')
for lgwordsz in range(0, len(types)):
    print('Notation "\'%s\'" := (Tbase (TWord %d)) : expr_scope.' % (types[lgwordsz], lgwordsz))
print('Notation ℤ := (Tbase TZ).')
print('')
cast_pat = "%s %s"
cast_types = tuple(["'1&(%s)'" % i for i in types[:1]] +
                   ["'(%s)'" % i for i in types[1:]])
def at_least_S_pattern(n):
    return '(S ' * n + '_' + ')' * n

_ = '_'
TZ = 'TZ'
def TWord(v): return '(TWord %s)' % str(v)

def print_notation_string(xisvar, yisvar, opn, op, arg_tuple, lvl=None, xsz=None, ysz=None, xlvl=None, ylvl=None):
    lhs = ('x' if not xisvar else '(Var x)')
    rhs = ('y' if not yisvar else '(Var y)')
    x = ('x' if xsz is None else (cast_pat % (cast_types[xsz], 'x')))
    y = ('y' if ysz is None else (cast_pat % (cast_types[ysz], 'y')))
    ret = 'Notation "%s%s %s %s%s" := (Op (%s %s) (Pair %s %s))' % (OPEN, x, opn, y, CLOSE, op, ' '.join(arg_tuple), lhs, rhs)
    modifiers = []
    for var, l in (('', lvl), ('x ', xlvl), ('y ', ylvl)):
        if l is not None:
            modifiers.append('%sat level %s' % (var, str(l)))
    if (OPEN + CLOSE) != '':
        modifiers.append('format "%s%s  %s  %s%s"' % (OPEN, x, opn, y, CLOSE))
    if len(modifiers) > 0:
        ret = '%s (%s) : expr_scope.' % (ret, ', '.join(modifiers))
    else:
        ret = '%s : expr_scope.' % (ret,)
    print(ret)

for opn, op, lvl in (('*', 'Mul', 40), ('+', 'Add', 50), ('-', 'Sub', 50)):
    for v1 in (False, True):
        for v2 in (False, True):
            print_notation_string(v1, v2, opn, op, (_, _, _))
            print_notation_string(v1, v2, opn + 'ℤ', op, (_, _, TZ), lvl=lvl)
    for lgwordsz in range(0, len(types)):
        for v1 in (False, True):
            for v2 in (False, True):
                print_notation_string(v1, v2, opn, op, (TWord(_), TWord(_), TWord(lgwordsz)), xsz=lgwordsz, lvl=lvl, xlvl=9)
                print_notation_string(v1, v2, opn, op, (TWord(_), TWord(at_least_S_pattern(lgwordsz)), TWord(lgwordsz)), ysz=lgwordsz, lvl=lvl, ylvl=9)
                print_notation_string(v1, v2, opn, op, (TWord(at_least_S_pattern(lgwordsz)), TWord(at_least_S_pattern(lgwordsz)), TWord(lgwordsz)), xsz=lgwordsz, ysz=lgwordsz, lvl=lvl, xlvl=9, ylvl=9)
        for v1 in (False, True):
            for v2 in (False, True):
                print_notation_string(v1, v2, opn, op, (TWord(lgwordsz), TWord(_), TWord(lgwordsz)))
                print_notation_string(v1, v2, opn, op, (TWord(_), TWord(lgwordsz), TWord(lgwordsz)))
                print_notation_string(v1, v2, opn, op, (TWord(lgwordsz), TWord(at_least_S_pattern(lgwordsz)), TWord(lgwordsz)), ysz=lgwordsz, lvl=lvl, ylvl=9)
                print_notation_string(v1, v2, opn, op, (TWord(at_least_S_pattern(lgwordsz)), TWord(lgwordsz), TWord(lgwordsz)), xsz=lgwordsz, lvl=lvl, xlvl=9)
        for v1 in (False, True):
            for v2 in (False, True):
                print_notation_string(v1, v2, opn, op, (TWord(lgwordsz), TWord(lgwordsz), TWord(lgwordsz)))
for opn, op, lvl in (('*', 'Mul', 40), ('+', 'Add', 50), ('-', 'Sub', 50)):
    for v1 in (False, True):
        for v2 in (False, True):
            x = ('x' if not v1 else '(Var x)')
            y = ('y' if not v2 else '(Var y)')
            print('''Notation "%s'1&(' %s %s %s ')'%s" := (Op (%s %s) (Pair %s %s)) (at level %d, format "%s'1&(' %s  %s  %s ')'%s").''' %
                  (OPEN, 'x', opn, 'y', CLOSE,
                   op, ' '.join((TWord(0), TWord(_), TWord(_))), x, y, lvl,
                   OPEN, 'x', opn, 'y', CLOSE))
for opn, op, lvl in (('&', 'Land', 40), ('|', 'Lor', 45)):
    for v1 in (False, True):
        for v2 in (False, True):
            print_notation_string(v1, v2, opn, op, (_, _, _))
            print_notation_string(v1, v2, opn + 'ℤ', op, (_, _, TZ), lvl=lvl)
    for lgwordsz in range(0, len(types)):
        for v1 in (False, True):
            for v2 in (False, True):
                print_notation_string(v1, v2, opn, op, (TWord(_), TWord(_), TWord(lgwordsz)), xsz=lgwordsz, ysz=lgwordsz, lvl=lvl, xlvl=9, ylvl=9)
        for v1 in (False, True):
            for v2 in (False, True):
                print_notation_string(v1, v2, opn, op, (TWord(lgwordsz), TWord(_), TWord(lgwordsz)), ysz=lgwordsz, lvl=lvl, ylvl=9)
                print_notation_string(v1, v2, opn, op, (TWord(_), TWord(lgwordsz), TWord(lgwordsz)), xsz=lgwordsz, lvl=lvl, xlvl=9)
        for v1 in (False, True):
            for v2 in (False, True):
                print_notation_string(v1, v2, opn, op, (TWord(lgwordsz), TWord(lgwordsz), TWord(lgwordsz)))
for opn, op, lvl in (('<<', 'Shl', 30),):
    for v1 in (False, True):
        for v2 in (False, True):
            print_notation_string(v1, v2, opn, op, (_, _, _))
            print_notation_string(v1, v2, opn + 'ℤ', op, (_, _, TZ), lvl=lvl)
    for lgwordsz in range(0, len(types)):
        for v1 in (False, True):
            for v2 in (False, True):
                print_notation_string(v1, v2, opn, op, (TWord(_), TWord(_), TWord(lgwordsz)), xsz=lgwordsz, lvl=lvl)
                print_notation_string(v1, v2, opn, op, (TWord(lgwordsz), TWord(_), TWord(lgwordsz)))
for opn, op, lvl in (('>>', 'Shr', 30),):
    for v1 in (False, True):
        for v2 in (False, True):
            print_notation_string(v1, v2, opn, op, (_, _, _))
            print_notation_string(v1, v2, opn + 'ℤ', op, (_, _, TZ), lvl=lvl)
    for lgwordsz in range(0, len(types)):
        for v1 in (False, True):
            for v2 in (False, True):
                lhs = ('x' if not v1 else '(Var x)')
                rhs = ('y' if not v2 else '(Var y)')
                print('Notation "\'(%s)\' ( x %s y )" := (Op (%s (TWord _) (TWord _) (TWord %d)) (Pair %s %s)) (at level %d) : expr_scope.'
                      % (types[lgwordsz], opn, op, lgwordsz, lhs, rhs, lvl))
                print_notation_string(v1, v2, opn, op, (TWord(lgwordsz), TWord(_), TWord(lgwordsz)))
for v0 in (False, True):
    for v1 in (False, True):
        for v2 in (False, True):
            tes = ('v' if not v0 else '(Var v)')
            lhs = ('x' if not v1 else '(Var x)')
            rhs = ('y' if not v2 else '(Var y)')
            print('Notation "\'cmovznz32\' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord _) (TWord _)) (Pair (Pair %s %s) %s)) : expr_scope.' % (tes, lhs, rhs))
for (wordsz, cmovsz) in ((16,'32'), (32,'64'), (64,'128'), (128,'ℤ')):
    lgwordsz = log2_up(wordsz)
    for lgwordsz_out in range(0, lgwordsz+2): # + 2 so that we get one instance of lgwordsz_out > lgwordsz
        for v0 in (False, True):
            for v1 in (False, True):
                for v2 in (False, True):
                    tes = ('v' if not v0 else '(Var v)')
                    lhs = ('x' if not v1 else '(Var x)')
                    rhs = ('y' if not v2 else '(Var y)')
                    TWordSz = TWord(at_least_S_pattern(lgwordsz+1)) # + 1, because we need strictly not equal
                    TWordSz_out = TWord(at_least_S_pattern(lgwordsz_out))
                    if lgwordsz_out > lgwordsz:
                        pat = 'Notation "\'cmovznz%s\' ( v , x , y )" := (Op (Zselect %s %s %s %s) (Pair (Pair %s %s) %s)) : expr_scope.'
                        print(pat % (cmovsz, TWordSz, TWord(_), TWord(_), TWordSz_out, tes, lhs, rhs))
                        print(pat % (cmovsz, TWord(_), TWordSz, TWord(_), TWordSz_out, tes, lhs, rhs))
                        print(pat % (cmovsz, TWord(_), TWord(_), TWordSz, TWordSz_out, tes, lhs, rhs))
                    else:
                        pat = 'Notation "\'(%s)\' \'cmovznz%s\' ( v , x , y )" := (Op (Zselect %s %s %s %s) (Pair (Pair %s %s) %s)) (format "\'(%s)\' \'cmovznz%s\' ( v ,  x ,  y )") : expr_scope.'
                        print(pat % (types[lgwordsz_out], cmovsz, TWordSz, TWord(_), TWord(_), TWordSz_out, tes, lhs, rhs, types[lgwordsz_out], cmovsz))
                        print(pat % (types[lgwordsz_out], cmovsz, TWord(_), TWordSz, TWord(_), TWordSz_out, tes, lhs, rhs, types[lgwordsz_out], cmovsz))
                        print(pat % (types[lgwordsz_out], cmovsz, TWord(_), TWord(_), TWordSz, TWordSz_out, tes, lhs, rhs, types[lgwordsz_out], cmovsz))
for v0 in (False, True):
    for v1 in (False, True):
        for v2 in (False, True):
            tes = ('v' if not v0 else '(Var v)')
            lhs = ('x' if not v1 else '(Var x)')
            rhs = ('y' if not v2 else '(Var y)')
            print('Notation "\'cmovznzℤ\' ( v , x , y )" := (Op (Zselect TZ _ _ _) (Pair (Pair %s %s) %s)) : expr_scope.' % (tes, lhs, rhs))
            print('Notation "\'cmovznzℤ\' ( v , x , y )" := (Op (Zselect _ TZ _ _) (Pair (Pair %s %s) %s)) : expr_scope.' % (tes, lhs, rhs))
            print('Notation "\'cmovznzℤ\' ( v , x , y )" := (Op (Zselect _ _ TZ _) (Pair (Pair %s %s) %s)) : expr_scope.' % (tes, lhs, rhs))
            print('Notation "\'cmovznzℤ\' ( v , x , y )" := (Op (Zselect _ _ _ TZ) (Pair (Pair %s %s) %s)) : expr_scope.' % (tes, lhs, rhs))
for opn, op in (('addcarryx', 'AddWithGetCarry'), ('subborrow', 'SubWithGetBorrow')):
    for wordsz in ADD_CARRY_SUB_BORROW_SIZES:
        lgwordsz = log2_up(wordsz)
        for v0 in (False, True):
            for v1 in (False, True):
                for v2 in (False, True):
                    c = ('c' if not v0 else '(Var c)')
                    a = ('a' if not v1 else '(Var a)')
                    b = ('b' if not v2 else '(Var b)')
                    for lgwordsz_small in (0, ): # (0, 3):
                        for notation_string in ('Notation "\'%s_u%d\' ( c , a , b )" := (Op (%s %d (TWord %d) (TWord %d) (TWord %d) (TWord %d) (TWord %d)) (Pair (Pair %s %s) %s)) : expr_scope.',
                                                ('(' + '*Notation "T0 out ; T1 c_out = \'_%s_u%d\' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (%s %d (TWord %d) (TWord %d) (TWord %d) (TWord %d) (TWord %d)) (Pair (Pair %s %s) %s)) (fun \'((out, c_out)%%core) => REST)) : expr_scope.*' + ')')):
                            print(notation_string % (opn, wordsz, op, wordsz, lgwordsz_small, lgwordsz, lgwordsz, lgwordsz, lgwordsz_small, c, a, b))
                            print(notation_string % (opn, wordsz, op, wordsz, lgwordsz_small, lgwordsz_small, lgwordsz, lgwordsz, lgwordsz_small, c, a, b))
                            print(notation_string % (opn, wordsz, op, wordsz, lgwordsz_small, lgwordsz, lgwordsz_small, lgwordsz, lgwordsz_small, c, a, b))
                            print(notation_string % (opn, wordsz, op, wordsz, lgwordsz_small, lgwordsz_small, lgwordsz_small, lgwordsz, lgwordsz_small, c, a, b))
for opn, op in (('mulx', 'MulSplit'),):
    for wordsz in (32, 64, 128, 51):
        lgwordsz = log2_up(wordsz)
        for v0 in (False, True):
            for v1 in (False, True):
                a = ('a' if not v0 else '(Var a)')
                b = ('b' if not v1 else '(Var b)')
                for lgwordsz_small in (0, 3):
                    for notation_string in ('Notation "%s\'%s_u%d%s\' ( a , b )" := (Op (%s %d (TWord %d) (TWord %d) (TWord %d) (TWord %d)) (Pair %s %s)) : expr_scope.',
                                            ('(' + '*Notation "T0 out ; T1 c_out = %s\'_%s_u%d%s\' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (%s %d (TWord %d) (TWord %d) (TWord %d) (TWord %d)) (Pair %s %s)) (fun \'((out, c_out)%%core) => REST)) : expr_scope.*' + ')')):
                        for arg1 in (lgwordsz_small, lgwordsz):
                            for arg2 in (lgwordsz_small, lgwordsz):
                                for arg3 in (lgwordsz_small, lgwordsz):
                                    for arg4 in (lgwordsz_small, lgwordsz): # N.B. the final argument, which is the high bits, must be of a compatible pointer type, and cannot be a pointer to a short word, without invoking a separate function
                                        cast_val = ('' if arg3 == lgwordsz else (cast_pat % (cast_types[lgwordsz_small], '')))
                                        extra_fun = ('' if arg4 == lgwordsz else ('_out_u%d' % (2**arg4)))
                                        print(notation_string % (cast_val, opn, wordsz, extra_fun, op, wordsz, arg1, arg2, arg3, arg4, a, b))
for opn, op in (('mulx', 'MulSplit'),):
    for wordsz in (32, 64, 128, 51):
        lgwordsz = log2_up(wordsz)
        for v0 in (False, True):
            for v1 in (False, True):
                a = ('a' if not v0 else '(Var a)')
                b = ('b' if not v1 else '(Var b)')
                print(('Notation "\'%s_u%d\' ( a , b )" := (Op (%s %d (TWord %d) (TWord %d) (TWord %d) (TWord %d)) (Pair %s %s)) : expr_scope.') % (opn, wordsz, op, wordsz, lgwordsz, lgwordsz, lgwordsz, lgwordsz, a, b))
                print(('(' + '*Notation "T0 out ; T1 c_out = \'_%s_u%d\' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (%s %d (TWord %d) (TWord %d) (TWord %d) (TWord %d)) (Pair %s %s)) (fun \'((out, c_out)%%core) => REST)) : expr_scope.*' + ')') % (opn, wordsz, op, wordsz, lgwordsz, lgwordsz, lgwordsz, lgwordsz, a, b))
for opn, op in (('addcarryx', 'AddWithGetCarry'), ('subborrow', 'SubWithGetBorrow')):
    for wordsz in ADD_CARRY_SUB_BORROW_SIZES:
        lgwordsz = log2_up(wordsz)
        for v0 in (False, True):
            for v1 in (False, True):
                for v2 in (False, True):
                    c = ('c' if not v0 else '(Var c)')
                    a = ('a' if not v1 else '(Var a)')
                    b = ('b' if not v2 else '(Var b)')
                    print(('Notation "\'%s_u%dℤ\' ( c , a , b )" := (Op (%s %d _ _ _ _ TZ) (Pair (Pair %s %s) %s)) : expr_scope.') % (opn, wordsz, op, wordsz, c, a, b))
                    print(('Notation "\'%s_u%dℤ\' ( c , a , b )" := (Op (%s %d _ _ _ TZ _) (Pair (Pair %s %s) %s)) : expr_scope.') % (opn, wordsz, op, wordsz, c, a, b))
                    print(('(' + '*Notation "T0 out ; T1 c_out = \'_%s_u%dℤ\' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (%s %d _ _ _ _ TZ) (Pair (Pair %s %s) %s)) (fun \'((out, c_out)%%core) => REST)) : expr_scope.*' + ')') % (opn, wordsz, op, wordsz, c, a, b))
                    print(('(' + '*Notation "T0 out ; T1 c_out = \'_%s_u%dℤ\' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (%s %d _ _ _ TZ _) (Pair (Pair %s %s) %s)) (fun \'((out, c_out)%%core) => REST)) : expr_scope.*' + ')') % (opn, wordsz, op, wordsz, c, a, b))
for opn, op in (('mulx', 'MulSplit'),):
    for wordsz in (32, 64, 128, 51):
        lgwordsz = log2_up(wordsz)
        for v0 in (False, True):
            for v1 in (False, True):
                a = ('a' if not v0 else '(Var a)')
                b = ('b' if not v1 else '(Var b)')
                print(('Notation "\'%s_u%dℤ\' ( a , b )" := (Op (%s %d _ _ _ TZ) (Pair %s %s)) : expr_scope.') % (opn, wordsz, op, wordsz, a, b))
                print(('Notation "\'%s_u%dℤ\' ( a , b )" := (Op (%s %d _ _ TZ _) (Pair %s %s)) : expr_scope.') % (opn, wordsz, op, wordsz, a, b))
                print(('(' + '*Notation "T0 out ; T1 c_out = \'_%s_u%dℤ\' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (%s %d _ _ _ TZ) (Pair %s %s)) (fun \'((out, c_out)%%core) => REST)) : expr_scope.*' + ')') % (opn, wordsz, op, wordsz, a, b))
                print(('(' + '*Notation "T0 out ; T1 c_out = \'_%s_u%dℤ\' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (%s %d _ _ TZ _) (Pair %s %s)) (fun \'((out, c_out)%%core) => REST)) : expr_scope.*' + ')') % (opn, wordsz, op, wordsz, a, b))
print('Notation Return x := (Var x).')
print('Notation C_like := (Expr base_type op _).')

>> *)
Notation "'uint8_t/*bool*/'" := (Tbase (TWord 0)) : expr_scope.
Notation "'uint8_t'" := (Tbase (TWord 1)) : expr_scope.
Notation "'uint8_t'" := (Tbase (TWord 2)) : expr_scope.
Notation "'uint8_t'" := (Tbase (TWord 3)) : expr_scope.
Notation "'uint16_t'" := (Tbase (TWord 4)) : expr_scope.
Notation "'uint32_t'" := (Tbase (TWord 5)) : expr_scope.
Notation "'uint64_t'" := (Tbase (TWord 6)) : expr_scope.
Notation "'uint128_t'" := (Tbase (TWord 7)) : expr_scope.
Notation "'uint256_t'" := (Tbase (TWord 8)) : expr_scope.
Notation ℤ := (Tbase TZ).

Notation "( x * y )" := (Op (Mul _ _ _) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x *ℤ y )" := (Op (Mul _ _ TZ) (Pair x y)) (at level 40, format "( x  *ℤ  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul _ _ _) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x *ℤ y )" := (Op (Mul _ _ TZ) (Pair x (Var y))) (at level 40, format "( x  *ℤ  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul _ _ _) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x *ℤ y )" := (Op (Mul _ _ TZ) (Pair (Var x) y)) (at level 40, format "( x  *ℤ  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul _ _ _) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x *ℤ y )" := (Op (Mul _ _ TZ) (Pair (Var x) (Var y))) (at level 40, format "( x  *ℤ  y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  *  y )") : expr_scope.
Notation "( x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  *  y )") : expr_scope.
Notation "( x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  *  y )") : expr_scope.
Notation "( x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  *  y )") : expr_scope.
Notation "( x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * y )" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * y )" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * y )" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '1&(uint8_t/*bool*/)' y )" := (Op (Mul (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x * y )" := (Op (Mul (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 0) (TWord 0) (TWord 0)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 0) (TWord 0) (TWord 0)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 1) (TWord _) (TWord 1)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 1) (TWord 1)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 1) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S _)) (TWord 1) (TWord 1)) (Pair x y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 1) (TWord 1)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 1) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S _)) (TWord 1) (TWord 1)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 1) (TWord 1) (TWord 1)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 1) (TWord 1) (TWord 1)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 2) (TWord _) (TWord 2)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 2) (TWord 2)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 2) (TWord 2)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 2) (TWord 2) (TWord 2)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 2) (TWord 2) (TWord 2)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * '(uint8_t)' y )" := (Op (Mul (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  *  '(uint8_t)' y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 3) (TWord _) (TWord 3)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 3) (TWord 3)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 3) (TWord 3)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint8_t)' y )" := (Op (Mul (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x * y )" := (Op (Mul (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 3) (TWord 3) (TWord 3)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 3) (TWord 3) (TWord 3)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( '(uint16_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 40, x at level 9, format "( '(uint16_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint16_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x * '(uint16_t)' y )" := (Op (Mul (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint16_t)' x  *  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint16_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint16_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x * '(uint16_t)' y )" := (Op (Mul (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint16_t)' x  *  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint16_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint16_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x * '(uint16_t)' y )" := (Op (Mul (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint16_t)' x  *  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint16_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint16_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x * '(uint16_t)' y )" := (Op (Mul (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint16_t)' x  *  '(uint16_t)' y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 4) (TWord _) (TWord 4)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 4) (TWord 4)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint16_t)' y )" := (Op (Mul (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x * y )" := (Op (Mul (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x y)) (at level 40, x at level 9, format "( '(uint16_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 4) (TWord 4)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint16_t)' y )" := (Op (Mul (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x * y )" := (Op (Mul (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint16_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint16_t)' y )" := (Op (Mul (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x * y )" := (Op (Mul (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint16_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint16_t)' y )" := (Op (Mul (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x * y )" := (Op (Mul (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint16_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 4) (TWord 4) (TWord 4)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 4) (TWord 4) (TWord 4)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( '(uint32_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 40, x at level 9, format "( '(uint32_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint32_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x * '(uint32_t)' y )" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint32_t)' x  *  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint32_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint32_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x * '(uint32_t)' y )" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint32_t)' x  *  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint32_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint32_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x * '(uint32_t)' y )" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint32_t)' x  *  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint32_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint32_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x * '(uint32_t)' y )" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint32_t)' x  *  '(uint32_t)' y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 5) (TWord _) (TWord 5)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 5) (TWord 5)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint32_t)' y )" := (Op (Mul (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x y)) (at level 40, x at level 9, format "( '(uint32_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 5) (TWord 5)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint32_t)' y )" := (Op (Mul (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint32_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint32_t)' y )" := (Op (Mul (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint32_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint32_t)' y )" := (Op (Mul (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint32_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 5) (TWord 5) (TWord 5)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 5) (TWord 5) (TWord 5)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( '(uint64_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 40, x at level 9, format "( '(uint64_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint64_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x * '(uint64_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint64_t)' x  *  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint64_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint64_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x * '(uint64_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint64_t)' x  *  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint64_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint64_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x * '(uint64_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint64_t)' x  *  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint64_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint64_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x * '(uint64_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint64_t)' x  *  '(uint64_t)' y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 6) (TWord _) (TWord 6)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 6) (TWord 6)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint64_t)' y )" := (Op (Mul (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x y)) (at level 40, x at level 9, format "( '(uint64_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 6) (TWord 6)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint64_t)' y )" := (Op (Mul (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint64_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint64_t)' y )" := (Op (Mul (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint64_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint64_t)' y )" := (Op (Mul (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint64_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 6) (TWord 6) (TWord 6)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 6) (TWord 6) (TWord 6)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( '(uint128_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 40, x at level 9, format "( '(uint128_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint128_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x * '(uint128_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint128_t)' x  *  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint128_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint128_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x * '(uint128_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint128_t)' x  *  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint128_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint128_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x * '(uint128_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint128_t)' x  *  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint128_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint128_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x * '(uint128_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint128_t)' x  *  '(uint128_t)' y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 7) (TWord _) (TWord 7)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 7) (TWord 7)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint128_t)' y )" := (Op (Mul (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x y)) (at level 40, x at level 9, format "( '(uint128_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 7) (TWord 7)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint128_t)' y )" := (Op (Mul (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint128_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint128_t)' y )" := (Op (Mul (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint128_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint128_t)' y )" := (Op (Mul (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint128_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 7) (TWord 7) (TWord 7)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 7) (TWord 7) (TWord 7)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( '(uint256_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 40, x at level 9, format "( '(uint256_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint256_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x * '(uint256_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint256_t)' x  *  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint256_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint256_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x * '(uint256_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint256_t)' x  *  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint256_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint256_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x * '(uint256_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint256_t)' x  *  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x * y )" := (Op (Mul (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint256_t)' x  *  y )") : expr_scope.
Notation "( x * '(uint256_t)' y )" := (Op (Mul (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x * '(uint256_t)' y )" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint256_t)' x  *  '(uint256_t)' y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 8) (TWord _) (TWord 8)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 8) (TWord 8)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint256_t)' y )" := (Op (Mul (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 40, y at level 9, format "( x  *  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x y)) (at level 40, x at level 9, format "( '(uint256_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 8) (TWord 8)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint256_t)' y )" := (Op (Mul (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  *  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint256_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint256_t)' y )" := (Op (Mul (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  *  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint256_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * '(uint256_t)' y )" := (Op (Mul (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  *  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x * y )" := (Op (Mul (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint256_t)' x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 8) (TWord 8) (TWord 8)) (Pair x y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 8) (TWord 8) (TWord 8)) (Pair x (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) y)) (format "( x  *  y )") : expr_scope.
Notation "( x * y )" := (Op (Mul (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  *  y )") : expr_scope.
Notation "( x + y )" := (Op (Add _ _ _) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x +ℤ y )" := (Op (Add _ _ TZ) (Pair x y)) (at level 50, format "( x  +ℤ  y )") : expr_scope.
Notation "( x + y )" := (Op (Add _ _ _) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x +ℤ y )" := (Op (Add _ _ TZ) (Pair x (Var y))) (at level 50, format "( x  +ℤ  y )") : expr_scope.
Notation "( x + y )" := (Op (Add _ _ _) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x +ℤ y )" := (Op (Add _ _ TZ) (Pair (Var x) y)) (at level 50, format "( x  +ℤ  y )") : expr_scope.
Notation "( x + y )" := (Op (Add _ _ _) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x +ℤ y )" := (Op (Add _ _ TZ) (Pair (Var x) (Var y))) (at level 50, format "( x  +ℤ  y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  +  y )") : expr_scope.
Notation "( x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  +  y )") : expr_scope.
Notation "( x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  +  y )") : expr_scope.
Notation "( x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  +  y )") : expr_scope.
Notation "( x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + y )" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + y )" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + y )" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '1&(uint8_t/*bool*/)' y )" := (Op (Add (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x + y )" := (Op (Add (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 0) (TWord 0) (TWord 0)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 0) (TWord 0) (TWord 0)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 1) (TWord _) (TWord 1)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 1) (TWord 1)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 1) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S _)) (TWord 1) (TWord 1)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 1) (TWord 1)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 1) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S _)) (TWord 1) (TWord 1)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 1) (TWord 1) (TWord 1)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 1) (TWord 1) (TWord 1)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 2) (TWord _) (TWord 2)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 2) (TWord 2)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 2) (TWord 2)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 2) (TWord 2) (TWord 2)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 2) (TWord 2) (TWord 2)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + '(uint8_t)' y )" := (Op (Add (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  +  '(uint8_t)' y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 3) (TWord _) (TWord 3)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 3) (TWord 3)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 3) (TWord 3)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint8_t)' y )" := (Op (Add (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x + y )" := (Op (Add (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 3) (TWord 3) (TWord 3)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 3) (TWord 3) (TWord 3)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( '(uint16_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 50, x at level 9, format "( '(uint16_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint16_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x + '(uint16_t)' y )" := (Op (Add (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint16_t)' x  +  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint16_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint16_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x + '(uint16_t)' y )" := (Op (Add (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint16_t)' x  +  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint16_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint16_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x + '(uint16_t)' y )" := (Op (Add (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint16_t)' x  +  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint16_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint16_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x + '(uint16_t)' y )" := (Op (Add (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint16_t)' x  +  '(uint16_t)' y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 4) (TWord _) (TWord 4)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 4) (TWord 4)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint16_t)' y )" := (Op (Add (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x + y )" := (Op (Add (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x y)) (at level 50, x at level 9, format "( '(uint16_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 4) (TWord 4)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint16_t)' y )" := (Op (Add (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x + y )" := (Op (Add (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint16_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint16_t)' y )" := (Op (Add (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x + y )" := (Op (Add (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint16_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint16_t)' y )" := (Op (Add (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x + y )" := (Op (Add (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint16_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 4) (TWord 4) (TWord 4)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 4) (TWord 4) (TWord 4)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( '(uint32_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 50, x at level 9, format "( '(uint32_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint32_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x + '(uint32_t)' y )" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint32_t)' x  +  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint32_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint32_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x + '(uint32_t)' y )" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint32_t)' x  +  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint32_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint32_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x + '(uint32_t)' y )" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint32_t)' x  +  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint32_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint32_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x + '(uint32_t)' y )" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint32_t)' x  +  '(uint32_t)' y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 5) (TWord _) (TWord 5)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 5) (TWord 5)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint32_t)' y )" := (Op (Add (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x y)) (at level 50, x at level 9, format "( '(uint32_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 5) (TWord 5)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint32_t)' y )" := (Op (Add (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint32_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint32_t)' y )" := (Op (Add (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint32_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint32_t)' y )" := (Op (Add (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint32_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 5) (TWord 5) (TWord 5)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 5) (TWord 5) (TWord 5)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( '(uint64_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 50, x at level 9, format "( '(uint64_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint64_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x + '(uint64_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint64_t)' x  +  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint64_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint64_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x + '(uint64_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint64_t)' x  +  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint64_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint64_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x + '(uint64_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint64_t)' x  +  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint64_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint64_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x + '(uint64_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint64_t)' x  +  '(uint64_t)' y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 6) (TWord _) (TWord 6)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 6) (TWord 6)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint64_t)' y )" := (Op (Add (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x y)) (at level 50, x at level 9, format "( '(uint64_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 6) (TWord 6)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint64_t)' y )" := (Op (Add (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint64_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint64_t)' y )" := (Op (Add (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint64_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint64_t)' y )" := (Op (Add (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint64_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 6) (TWord 6) (TWord 6)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 6) (TWord 6) (TWord 6)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( '(uint128_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 50, x at level 9, format "( '(uint128_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint128_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x + '(uint128_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint128_t)' x  +  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint128_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint128_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x + '(uint128_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint128_t)' x  +  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint128_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint128_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x + '(uint128_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint128_t)' x  +  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint128_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint128_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x + '(uint128_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint128_t)' x  +  '(uint128_t)' y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 7) (TWord _) (TWord 7)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 7) (TWord 7)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint128_t)' y )" := (Op (Add (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x y)) (at level 50, x at level 9, format "( '(uint128_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 7) (TWord 7)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint128_t)' y )" := (Op (Add (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint128_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint128_t)' y )" := (Op (Add (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint128_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint128_t)' y )" := (Op (Add (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint128_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 7) (TWord 7) (TWord 7)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 7) (TWord 7) (TWord 7)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( '(uint256_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 50, x at level 9, format "( '(uint256_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint256_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x + '(uint256_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint256_t)' x  +  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint256_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint256_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x + '(uint256_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint256_t)' x  +  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint256_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint256_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x + '(uint256_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint256_t)' x  +  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x + y )" := (Op (Add (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint256_t)' x  +  y )") : expr_scope.
Notation "( x + '(uint256_t)' y )" := (Op (Add (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x + '(uint256_t)' y )" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint256_t)' x  +  '(uint256_t)' y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 8) (TWord _) (TWord 8)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 8) (TWord 8)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint256_t)' y )" := (Op (Add (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50, y at level 9, format "( x  +  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x y)) (at level 50, x at level 9, format "( '(uint256_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 8) (TWord 8)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint256_t)' y )" := (Op (Add (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  +  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint256_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint256_t)' y )" := (Op (Add (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  +  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint256_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + '(uint256_t)' y )" := (Op (Add (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  +  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x + y )" := (Op (Add (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint256_t)' x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 8) (TWord 8) (TWord 8)) (Pair x y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 8) (TWord 8) (TWord 8)) (Pair x (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) y)) (format "( x  +  y )") : expr_scope.
Notation "( x + y )" := (Op (Add (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  +  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub _ _ _) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x -ℤ y )" := (Op (Sub _ _ TZ) (Pair x y)) (at level 50, format "( x  -ℤ  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub _ _ _) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x -ℤ y )" := (Op (Sub _ _ TZ) (Pair x (Var y))) (at level 50, format "( x  -ℤ  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub _ _ _) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x -ℤ y )" := (Op (Sub _ _ TZ) (Pair (Var x) y)) (at level 50, format "( x  -ℤ  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub _ _ _) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x -ℤ y )" := (Op (Sub _ _ TZ) (Pair (Var x) (Var y))) (at level 50, format "( x  -ℤ  y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  -  y )") : expr_scope.
Notation "( x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  -  y )") : expr_scope.
Notation "( x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  -  y )") : expr_scope.
Notation "( x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  -  y )") : expr_scope.
Notation "( x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - y )" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - y )" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - y )" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '1&(uint8_t/*bool*/)' y )" := (Op (Sub (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x - y )" := (Op (Sub (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '1&(uint8_t/*bool*/)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 0) (TWord 0) (TWord 0)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 0) (TWord 0) (TWord 0)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S _)) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 1) (TWord _) (TWord 1)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 1) (TWord 1)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 1) (TWord (S _)) (TWord 1)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S _)) (TWord 1) (TWord 1)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 1) (TWord 1)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 1) (TWord (S _)) (TWord 1)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S _)) (TWord 1) (TWord 1)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 1) (TWord (S _)) (TWord 1)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S _)) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 1) (TWord 1) (TWord 1)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 1) (TWord 1) (TWord 1)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S (S _))) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 2) (TWord _) (TWord 2)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 2) (TWord 2)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 2) (TWord 2)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 2) (TWord (S (S _))) (TWord 2)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S (S _))) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 2) (TWord 2) (TWord 2)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 2) (TWord 2) (TWord 2)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - '(uint8_t)' y )" := (Op (Sub (TWord (S (S (S _)))) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint8_t)' x  -  '(uint8_t)' y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 3) (TWord _) (TWord 3)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 3) (TWord 3)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 3) (TWord 3)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint8_t)' y )" := (Op (Sub (TWord 3) (TWord (S (S (S _)))) (TWord 3)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x - y )" := (Op (Sub (TWord (S (S (S _)))) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint8_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 3) (TWord 3) (TWord 3)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 3) (TWord 3) (TWord 3)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( '(uint16_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 50, x at level 9, format "( '(uint16_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint16_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x - '(uint16_t)' y )" := (Op (Sub (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint16_t)' x  -  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint16_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint16_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x - '(uint16_t)' y )" := (Op (Sub (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint16_t)' x  -  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint16_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint16_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x - '(uint16_t)' y )" := (Op (Sub (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint16_t)' x  -  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint16_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint16_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x - '(uint16_t)' y )" := (Op (Sub (TWord (S (S (S (S _))))) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint16_t)' x  -  '(uint16_t)' y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 4) (TWord _) (TWord 4)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 4) (TWord 4)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint16_t)' y )" := (Op (Sub (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x - y )" := (Op (Sub (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x y)) (at level 50, x at level 9, format "( '(uint16_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 4) (TWord 4)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint16_t)' y )" := (Op (Sub (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x - y )" := (Op (Sub (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint16_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint16_t)' y )" := (Op (Sub (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x - y )" := (Op (Sub (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint16_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint16_t)' y )" := (Op (Sub (TWord 4) (TWord (S (S (S (S _))))) (TWord 4)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x - y )" := (Op (Sub (TWord (S (S (S (S _))))) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint16_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 4) (TWord 4) (TWord 4)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 4) (TWord 4) (TWord 4)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( '(uint32_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 50, x at level 9, format "( '(uint32_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint32_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x - '(uint32_t)' y )" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint32_t)' x  -  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint32_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint32_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x - '(uint32_t)' y )" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint32_t)' x  -  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint32_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint32_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x - '(uint32_t)' y )" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint32_t)' x  -  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint32_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint32_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x - '(uint32_t)' y )" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint32_t)' x  -  '(uint32_t)' y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 5) (TWord _) (TWord 5)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 5) (TWord 5)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint32_t)' y )" := (Op (Sub (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x y)) (at level 50, x at level 9, format "( '(uint32_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 5) (TWord 5)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint32_t)' y )" := (Op (Sub (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint32_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint32_t)' y )" := (Op (Sub (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint32_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint32_t)' y )" := (Op (Sub (TWord 5) (TWord (S (S (S (S (S _)))))) (TWord 5)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S _)))))) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint32_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 5) (TWord 5) (TWord 5)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 5) (TWord 5) (TWord 5)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( '(uint64_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 50, x at level 9, format "( '(uint64_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint64_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x - '(uint64_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint64_t)' x  -  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint64_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint64_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x - '(uint64_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint64_t)' x  -  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint64_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint64_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x - '(uint64_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint64_t)' x  -  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint64_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint64_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x - '(uint64_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint64_t)' x  -  '(uint64_t)' y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 6) (TWord _) (TWord 6)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 6) (TWord 6)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint64_t)' y )" := (Op (Sub (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x y)) (at level 50, x at level 9, format "( '(uint64_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 6) (TWord 6)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint64_t)' y )" := (Op (Sub (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint64_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint64_t)' y )" := (Op (Sub (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint64_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint64_t)' y )" := (Op (Sub (TWord 6) (TWord (S (S (S (S (S (S _))))))) (TWord 6)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S _))))))) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint64_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 6) (TWord 6) (TWord 6)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 6) (TWord 6) (TWord 6)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( '(uint128_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 50, x at level 9, format "( '(uint128_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint128_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x - '(uint128_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint128_t)' x  -  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint128_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint128_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x - '(uint128_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint128_t)' x  -  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint128_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint128_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x - '(uint128_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint128_t)' x  -  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint128_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint128_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x - '(uint128_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint128_t)' x  -  '(uint128_t)' y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 7) (TWord _) (TWord 7)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 7) (TWord 7)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint128_t)' y )" := (Op (Sub (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x y)) (at level 50, x at level 9, format "( '(uint128_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 7) (TWord 7)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint128_t)' y )" := (Op (Sub (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint128_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint128_t)' y )" := (Op (Sub (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint128_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint128_t)' y )" := (Op (Sub (TWord 7) (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S (S _)))))))) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint128_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 7) (TWord 7) (TWord 7)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 7) (TWord 7) (TWord 7)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( '(uint256_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 50, x at level 9, format "( '(uint256_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint256_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x - '(uint256_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50, x at level 9, y at level 9, format "( '(uint256_t)' x  -  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint256_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint256_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x - '(uint256_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint256_t)' x  -  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint256_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint256_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x - '(uint256_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50, x at level 9, y at level 9, format "( '(uint256_t)' x  -  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x - y )" := (Op (Sub (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint256_t)' x  -  y )") : expr_scope.
Notation "( x - '(uint256_t)' y )" := (Op (Sub (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x - '(uint256_t)' y )" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50, x at level 9, y at level 9, format "( '(uint256_t)' x  -  '(uint256_t)' y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 8) (TWord _) (TWord 8)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 8) (TWord 8)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint256_t)' y )" := (Op (Sub (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x y)) (at level 50, y at level 9, format "( x  -  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x y)) (at level 50, x at level 9, format "( '(uint256_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 8) (TWord 8)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint256_t)' y )" := (Op (Sub (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair x (Var y))) (at level 50, y at level 9, format "( x  -  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair x (Var y))) (at level 50, x at level 9, format "( '(uint256_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint256_t)' y )" := (Op (Sub (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) y)) (at level 50, y at level 9, format "( x  -  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) y)) (at level 50, x at level 9, format "( '(uint256_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - '(uint256_t)' y )" := (Op (Sub (TWord 8) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8)) (Pair (Var x) (Var y))) (at level 50, y at level 9, format "( x  -  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x - y )" := (Op (Sub (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (at level 50, x at level 9, format "( '(uint256_t)' x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 8) (TWord 8) (TWord 8)) (Pair x y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 8) (TWord 8) (TWord 8)) (Pair x (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) y)) (format "( x  -  y )") : expr_scope.
Notation "( x - y )" := (Op (Sub (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  -  y )") : expr_scope.
Notation "( '1&(' x * y ')' )" := (Op (Mul (TWord 0) (TWord _) (TWord _)) (Pair x y)) (at level 40, format "( '1&(' x  *  y ')' )").
Notation "( '1&(' x * y ')' )" := (Op (Mul (TWord 0) (TWord _) (TWord _)) (Pair x (Var y))) (at level 40, format "( '1&(' x  *  y ')' )").
Notation "( '1&(' x * y ')' )" := (Op (Mul (TWord 0) (TWord _) (TWord _)) (Pair (Var x) y)) (at level 40, format "( '1&(' x  *  y ')' )").
Notation "( '1&(' x * y ')' )" := (Op (Mul (TWord 0) (TWord _) (TWord _)) (Pair (Var x) (Var y))) (at level 40, format "( '1&(' x  *  y ')' )").
Notation "( '1&(' x + y ')' )" := (Op (Add (TWord 0) (TWord _) (TWord _)) (Pair x y)) (at level 50, format "( '1&(' x  +  y ')' )").
Notation "( '1&(' x + y ')' )" := (Op (Add (TWord 0) (TWord _) (TWord _)) (Pair x (Var y))) (at level 50, format "( '1&(' x  +  y ')' )").
Notation "( '1&(' x + y ')' )" := (Op (Add (TWord 0) (TWord _) (TWord _)) (Pair (Var x) y)) (at level 50, format "( '1&(' x  +  y ')' )").
Notation "( '1&(' x + y ')' )" := (Op (Add (TWord 0) (TWord _) (TWord _)) (Pair (Var x) (Var y))) (at level 50, format "( '1&(' x  +  y ')' )").
Notation "( '1&(' x - y ')' )" := (Op (Sub (TWord 0) (TWord _) (TWord _)) (Pair x y)) (at level 50, format "( '1&(' x  -  y ')' )").
Notation "( '1&(' x - y ')' )" := (Op (Sub (TWord 0) (TWord _) (TWord _)) (Pair x (Var y))) (at level 50, format "( '1&(' x  -  y ')' )").
Notation "( '1&(' x - y ')' )" := (Op (Sub (TWord 0) (TWord _) (TWord _)) (Pair (Var x) y)) (at level 50, format "( '1&(' x  -  y ')' )").
Notation "( '1&(' x - y ')' )" := (Op (Sub (TWord 0) (TWord _) (TWord _)) (Pair (Var x) (Var y))) (at level 50, format "( '1&(' x  -  y ')' )").
Notation "( x & y )" := (Op (Land _ _ _) (Pair x y)) (format "( x  &  y )") : expr_scope.
Notation "( x &ℤ y )" := (Op (Land _ _ TZ) (Pair x y)) (at level 40, format "( x  &ℤ  y )") : expr_scope.
Notation "( x & y )" := (Op (Land _ _ _) (Pair x (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x &ℤ y )" := (Op (Land _ _ TZ) (Pair x (Var y))) (at level 40, format "( x  &ℤ  y )") : expr_scope.
Notation "( x & y )" := (Op (Land _ _ _) (Pair (Var x) y)) (format "( x  &  y )") : expr_scope.
Notation "( x &ℤ y )" := (Op (Land _ _ TZ) (Pair (Var x) y)) (at level 40, format "( x  &ℤ  y )") : expr_scope.
Notation "( x & y )" := (Op (Land _ _ _) (Pair (Var x) (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x &ℤ y )" := (Op (Land _ _ TZ) (Pair (Var x) (Var y))) (at level 40, format "( x  &ℤ  y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x & '1&(uint8_t/*bool*/)' y )" := (Op (Land (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  &  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x & '1&(uint8_t/*bool*/)' y )" := (Op (Land (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  &  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x & '1&(uint8_t/*bool*/)' y )" := (Op (Land (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  &  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x & '1&(uint8_t/*bool*/)' y )" := (Op (Land (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  &  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( x & '1&(uint8_t/*bool*/)' y )" := (Op (Land (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (at level 40, y at level 9, format "( x  &  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x & y )" := (Op (Land (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  &  y )") : expr_scope.
Notation "( x & '1&(uint8_t/*bool*/)' y )" := (Op (Land (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  &  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x & y )" := (Op (Land (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  &  y )") : expr_scope.
Notation "( x & '1&(uint8_t/*bool*/)' y )" := (Op (Land (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  &  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x & y )" := (Op (Land (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  &  y )") : expr_scope.
Notation "( x & '1&(uint8_t/*bool*/)' y )" := (Op (Land (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  &  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x & y )" := (Op (Land (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '1&(uint8_t/*bool*/)' x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 0) (TWord 0) (TWord 0)) (Pair x y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 0) (TWord 0) (TWord 0)) (Pair x (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 1) (TWord _) (TWord 1)) (Pair x y)) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 1) (TWord 1)) (Pair x y)) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 1) (TWord 1)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 1) (TWord 1) (TWord 1)) (Pair x y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 1) (TWord 1) (TWord 1)) (Pair x (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 2) (TWord _) (TWord 2)) (Pair x y)) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 2) (TWord 2)) (Pair x y)) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 2) (TWord 2)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 2) (TWord 2) (TWord 2)) (Pair x y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 2) (TWord 2) (TWord 2)) (Pair x (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & '(uint8_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint8_t)' x  &  '(uint8_t)' y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 3) (TWord _) (TWord 3)) (Pair x y)) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 3) (TWord 3)) (Pair x y)) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 3) (TWord 3)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint8_t)' y )" := (Op (Land (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  &  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x & y )" := (Op (Land (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint8_t)' x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 3) (TWord 3) (TWord 3)) (Pair x y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 3) (TWord 3) (TWord 3)) (Pair x (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( '(uint16_t)' x & '(uint16_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint16_t)' x  &  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x & '(uint16_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint16_t)' x  &  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x & '(uint16_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint16_t)' x  &  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x & '(uint16_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint16_t)' x  &  '(uint16_t)' y )") : expr_scope.
Notation "( x & '(uint16_t)' y )" := (Op (Land (TWord 4) (TWord _) (TWord 4)) (Pair x y)) (at level 40, y at level 9, format "( x  &  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x & y )" := (Op (Land (TWord _) (TWord 4) (TWord 4)) (Pair x y)) (at level 40, x at level 9, format "( '(uint16_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint16_t)' y )" := (Op (Land (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  &  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x & y )" := (Op (Land (TWord _) (TWord 4) (TWord 4)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint16_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint16_t)' y )" := (Op (Land (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  &  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x & y )" := (Op (Land (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint16_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint16_t)' y )" := (Op (Land (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  &  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x & y )" := (Op (Land (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint16_t)' x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 4) (TWord 4) (TWord 4)) (Pair x y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 4) (TWord 4) (TWord 4)) (Pair x (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( '(uint32_t)' x & '(uint32_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint32_t)' x  &  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x & '(uint32_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint32_t)' x  &  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x & '(uint32_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint32_t)' x  &  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x & '(uint32_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint32_t)' x  &  '(uint32_t)' y )") : expr_scope.
Notation "( x & '(uint32_t)' y )" := (Op (Land (TWord 5) (TWord _) (TWord 5)) (Pair x y)) (at level 40, y at level 9, format "( x  &  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x & y )" := (Op (Land (TWord _) (TWord 5) (TWord 5)) (Pair x y)) (at level 40, x at level 9, format "( '(uint32_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint32_t)' y )" := (Op (Land (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  &  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x & y )" := (Op (Land (TWord _) (TWord 5) (TWord 5)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint32_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint32_t)' y )" := (Op (Land (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  &  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x & y )" := (Op (Land (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint32_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint32_t)' y )" := (Op (Land (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  &  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x & y )" := (Op (Land (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint32_t)' x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 5) (TWord 5) (TWord 5)) (Pair x y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 5) (TWord 5) (TWord 5)) (Pair x (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( '(uint64_t)' x & '(uint64_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint64_t)' x  &  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x & '(uint64_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint64_t)' x  &  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x & '(uint64_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint64_t)' x  &  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x & '(uint64_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint64_t)' x  &  '(uint64_t)' y )") : expr_scope.
Notation "( x & '(uint64_t)' y )" := (Op (Land (TWord 6) (TWord _) (TWord 6)) (Pair x y)) (at level 40, y at level 9, format "( x  &  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x & y )" := (Op (Land (TWord _) (TWord 6) (TWord 6)) (Pair x y)) (at level 40, x at level 9, format "( '(uint64_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint64_t)' y )" := (Op (Land (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  &  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x & y )" := (Op (Land (TWord _) (TWord 6) (TWord 6)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint64_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint64_t)' y )" := (Op (Land (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  &  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x & y )" := (Op (Land (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint64_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint64_t)' y )" := (Op (Land (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  &  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x & y )" := (Op (Land (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint64_t)' x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 6) (TWord 6) (TWord 6)) (Pair x y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 6) (TWord 6) (TWord 6)) (Pair x (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( '(uint128_t)' x & '(uint128_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint128_t)' x  &  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x & '(uint128_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint128_t)' x  &  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x & '(uint128_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint128_t)' x  &  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x & '(uint128_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint128_t)' x  &  '(uint128_t)' y )") : expr_scope.
Notation "( x & '(uint128_t)' y )" := (Op (Land (TWord 7) (TWord _) (TWord 7)) (Pair x y)) (at level 40, y at level 9, format "( x  &  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x & y )" := (Op (Land (TWord _) (TWord 7) (TWord 7)) (Pair x y)) (at level 40, x at level 9, format "( '(uint128_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint128_t)' y )" := (Op (Land (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  &  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x & y )" := (Op (Land (TWord _) (TWord 7) (TWord 7)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint128_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint128_t)' y )" := (Op (Land (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  &  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x & y )" := (Op (Land (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint128_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint128_t)' y )" := (Op (Land (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  &  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x & y )" := (Op (Land (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint128_t)' x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 7) (TWord 7) (TWord 7)) (Pair x y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 7) (TWord 7) (TWord 7)) (Pair x (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( '(uint256_t)' x & '(uint256_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 40, x at level 9, y at level 9, format "( '(uint256_t)' x  &  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x & '(uint256_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint256_t)' x  &  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x & '(uint256_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 40, x at level 9, y at level 9, format "( '(uint256_t)' x  &  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x & '(uint256_t)' y )" := (Op (Land (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 40, x at level 9, y at level 9, format "( '(uint256_t)' x  &  '(uint256_t)' y )") : expr_scope.
Notation "( x & '(uint256_t)' y )" := (Op (Land (TWord 8) (TWord _) (TWord 8)) (Pair x y)) (at level 40, y at level 9, format "( x  &  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x & y )" := (Op (Land (TWord _) (TWord 8) (TWord 8)) (Pair x y)) (at level 40, x at level 9, format "( '(uint256_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint256_t)' y )" := (Op (Land (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 40, y at level 9, format "( x  &  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x & y )" := (Op (Land (TWord _) (TWord 8) (TWord 8)) (Pair x (Var y))) (at level 40, x at level 9, format "( '(uint256_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint256_t)' y )" := (Op (Land (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 40, y at level 9, format "( x  &  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x & y )" := (Op (Land (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) y)) (at level 40, x at level 9, format "( '(uint256_t)' x  &  y )") : expr_scope.
Notation "( x & '(uint256_t)' y )" := (Op (Land (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 40, y at level 9, format "( x  &  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x & y )" := (Op (Land (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (at level 40, x at level 9, format "( '(uint256_t)' x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 8) (TWord 8) (TWord 8)) (Pair x y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 8) (TWord 8) (TWord 8)) (Pair x (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) y)) (format "( x  &  y )") : expr_scope.
Notation "( x & y )" := (Op (Land (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  &  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor _ _ _) (Pair x y)) (format "( x  |  y )") : expr_scope.
Notation "( x |ℤ y )" := (Op (Lor _ _ TZ) (Pair x y)) (at level 45, format "( x  |ℤ  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor _ _ _) (Pair x (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x |ℤ y )" := (Op (Lor _ _ TZ) (Pair x (Var y))) (at level 45, format "( x  |ℤ  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor _ _ _) (Pair (Var x) y)) (format "( x  |  y )") : expr_scope.
Notation "( x |ℤ y )" := (Op (Lor _ _ TZ) (Pair (Var x) y)) (at level 45, format "( x  |ℤ  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor _ _ _) (Pair (Var x) (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x |ℤ y )" := (Op (Lor _ _ TZ) (Pair (Var x) (Var y))) (at level 45, format "( x  |ℤ  y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x | '1&(uint8_t/*bool*/)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 45, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  |  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x | '1&(uint8_t/*bool*/)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 45, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  |  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x | '1&(uint8_t/*bool*/)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 45, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  |  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x | '1&(uint8_t/*bool*/)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 45, x at level 9, y at level 9, format "( '1&(uint8_t/*bool*/)' x  |  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( x | '1&(uint8_t/*bool*/)' y )" := (Op (Lor (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (at level 45, y at level 9, format "( x  |  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x | y )" := (Op (Lor (TWord _) (TWord 0) (TWord 0)) (Pair x y)) (at level 45, x at level 9, format "( '1&(uint8_t/*bool*/)' x  |  y )") : expr_scope.
Notation "( x | '1&(uint8_t/*bool*/)' y )" := (Op (Lor (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 45, y at level 9, format "( x  |  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x | y )" := (Op (Lor (TWord _) (TWord 0) (TWord 0)) (Pair x (Var y))) (at level 45, x at level 9, format "( '1&(uint8_t/*bool*/)' x  |  y )") : expr_scope.
Notation "( x | '1&(uint8_t/*bool*/)' y )" := (Op (Lor (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 45, y at level 9, format "( x  |  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x | y )" := (Op (Lor (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) y)) (at level 45, x at level 9, format "( '1&(uint8_t/*bool*/)' x  |  y )") : expr_scope.
Notation "( x | '1&(uint8_t/*bool*/)' y )" := (Op (Lor (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 45, y at level 9, format "( x  |  '1&(uint8_t/*bool*/)' y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x | y )" := (Op (Lor (TWord _) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (at level 45, x at level 9, format "( '1&(uint8_t/*bool*/)' x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 0) (TWord 0) (TWord 0)) (Pair x y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 0) (TWord 0) (TWord 0)) (Pair x (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 0) (TWord 0) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 1) (TWord _) (TWord 1)) (Pair x y)) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 1) (TWord 1)) (Pair x y)) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 1) (TWord 1)) (Pair x (Var y))) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) y)) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 1) (TWord 1) (TWord 1)) (Pair x y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 1) (TWord 1) (TWord 1)) (Pair x (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 1) (TWord 1) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 2) (TWord _) (TWord 2)) (Pair x y)) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 2) (TWord 2)) (Pair x y)) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 2) (TWord 2)) (Pair x (Var y))) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) y)) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 2) (TWord 2) (TWord 2)) (Pair x y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 2) (TWord 2) (TWord 2)) (Pair x (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 2) (TWord 2) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | '(uint8_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint8_t)' x  |  '(uint8_t)' y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 3) (TWord _) (TWord 3)) (Pair x y)) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 3) (TWord 3)) (Pair x y)) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 3) (TWord 3)) (Pair x (Var y))) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) y)) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint8_t)' y )" := (Op (Lor (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 45, y at level 9, format "( x  |  '(uint8_t)' y )") : expr_scope.
Notation "( '(uint8_t)' x | y )" := (Op (Lor (TWord _) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (at level 45, x at level 9, format "( '(uint8_t)' x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 3) (TWord 3) (TWord 3)) (Pair x y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 3) (TWord 3) (TWord 3)) (Pair x (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 3) (TWord 3) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( '(uint16_t)' x | '(uint16_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 45, x at level 9, y at level 9, format "( '(uint16_t)' x  |  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x | '(uint16_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint16_t)' x  |  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x | '(uint16_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 45, x at level 9, y at level 9, format "( '(uint16_t)' x  |  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x | '(uint16_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint16_t)' x  |  '(uint16_t)' y )") : expr_scope.
Notation "( x | '(uint16_t)' y )" := (Op (Lor (TWord 4) (TWord _) (TWord 4)) (Pair x y)) (at level 45, y at level 9, format "( x  |  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x | y )" := (Op (Lor (TWord _) (TWord 4) (TWord 4)) (Pair x y)) (at level 45, x at level 9, format "( '(uint16_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint16_t)' y )" := (Op (Lor (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 45, y at level 9, format "( x  |  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x | y )" := (Op (Lor (TWord _) (TWord 4) (TWord 4)) (Pair x (Var y))) (at level 45, x at level 9, format "( '(uint16_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint16_t)' y )" := (Op (Lor (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 45, y at level 9, format "( x  |  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x | y )" := (Op (Lor (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) y)) (at level 45, x at level 9, format "( '(uint16_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint16_t)' y )" := (Op (Lor (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 45, y at level 9, format "( x  |  '(uint16_t)' y )") : expr_scope.
Notation "( '(uint16_t)' x | y )" := (Op (Lor (TWord _) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (at level 45, x at level 9, format "( '(uint16_t)' x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 4) (TWord 4) (TWord 4)) (Pair x y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 4) (TWord 4) (TWord 4)) (Pair x (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 4) (TWord 4) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( '(uint32_t)' x | '(uint32_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 45, x at level 9, y at level 9, format "( '(uint32_t)' x  |  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x | '(uint32_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint32_t)' x  |  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x | '(uint32_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 45, x at level 9, y at level 9, format "( '(uint32_t)' x  |  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x | '(uint32_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint32_t)' x  |  '(uint32_t)' y )") : expr_scope.
Notation "( x | '(uint32_t)' y )" := (Op (Lor (TWord 5) (TWord _) (TWord 5)) (Pair x y)) (at level 45, y at level 9, format "( x  |  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x | y )" := (Op (Lor (TWord _) (TWord 5) (TWord 5)) (Pair x y)) (at level 45, x at level 9, format "( '(uint32_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint32_t)' y )" := (Op (Lor (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 45, y at level 9, format "( x  |  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x | y )" := (Op (Lor (TWord _) (TWord 5) (TWord 5)) (Pair x (Var y))) (at level 45, x at level 9, format "( '(uint32_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint32_t)' y )" := (Op (Lor (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 45, y at level 9, format "( x  |  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x | y )" := (Op (Lor (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) y)) (at level 45, x at level 9, format "( '(uint32_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint32_t)' y )" := (Op (Lor (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 45, y at level 9, format "( x  |  '(uint32_t)' y )") : expr_scope.
Notation "( '(uint32_t)' x | y )" := (Op (Lor (TWord _) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (at level 45, x at level 9, format "( '(uint32_t)' x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 5) (TWord 5) (TWord 5)) (Pair x y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 5) (TWord 5) (TWord 5)) (Pair x (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 5) (TWord 5) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( '(uint64_t)' x | '(uint64_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 45, x at level 9, y at level 9, format "( '(uint64_t)' x  |  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x | '(uint64_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint64_t)' x  |  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x | '(uint64_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 45, x at level 9, y at level 9, format "( '(uint64_t)' x  |  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x | '(uint64_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint64_t)' x  |  '(uint64_t)' y )") : expr_scope.
Notation "( x | '(uint64_t)' y )" := (Op (Lor (TWord 6) (TWord _) (TWord 6)) (Pair x y)) (at level 45, y at level 9, format "( x  |  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x | y )" := (Op (Lor (TWord _) (TWord 6) (TWord 6)) (Pair x y)) (at level 45, x at level 9, format "( '(uint64_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint64_t)' y )" := (Op (Lor (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 45, y at level 9, format "( x  |  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x | y )" := (Op (Lor (TWord _) (TWord 6) (TWord 6)) (Pair x (Var y))) (at level 45, x at level 9, format "( '(uint64_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint64_t)' y )" := (Op (Lor (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 45, y at level 9, format "( x  |  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x | y )" := (Op (Lor (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) y)) (at level 45, x at level 9, format "( '(uint64_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint64_t)' y )" := (Op (Lor (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 45, y at level 9, format "( x  |  '(uint64_t)' y )") : expr_scope.
Notation "( '(uint64_t)' x | y )" := (Op (Lor (TWord _) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (at level 45, x at level 9, format "( '(uint64_t)' x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 6) (TWord 6) (TWord 6)) (Pair x y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 6) (TWord 6) (TWord 6)) (Pair x (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 6) (TWord 6) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( '(uint128_t)' x | '(uint128_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 45, x at level 9, y at level 9, format "( '(uint128_t)' x  |  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x | '(uint128_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint128_t)' x  |  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x | '(uint128_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 45, x at level 9, y at level 9, format "( '(uint128_t)' x  |  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x | '(uint128_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint128_t)' x  |  '(uint128_t)' y )") : expr_scope.
Notation "( x | '(uint128_t)' y )" := (Op (Lor (TWord 7) (TWord _) (TWord 7)) (Pair x y)) (at level 45, y at level 9, format "( x  |  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x | y )" := (Op (Lor (TWord _) (TWord 7) (TWord 7)) (Pair x y)) (at level 45, x at level 9, format "( '(uint128_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint128_t)' y )" := (Op (Lor (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 45, y at level 9, format "( x  |  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x | y )" := (Op (Lor (TWord _) (TWord 7) (TWord 7)) (Pair x (Var y))) (at level 45, x at level 9, format "( '(uint128_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint128_t)' y )" := (Op (Lor (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 45, y at level 9, format "( x  |  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x | y )" := (Op (Lor (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) y)) (at level 45, x at level 9, format "( '(uint128_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint128_t)' y )" := (Op (Lor (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 45, y at level 9, format "( x  |  '(uint128_t)' y )") : expr_scope.
Notation "( '(uint128_t)' x | y )" := (Op (Lor (TWord _) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (at level 45, x at level 9, format "( '(uint128_t)' x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 7) (TWord 7) (TWord 7)) (Pair x y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 7) (TWord 7) (TWord 7)) (Pair x (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 7) (TWord 7) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( '(uint256_t)' x | '(uint256_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 45, x at level 9, y at level 9, format "( '(uint256_t)' x  |  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x | '(uint256_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint256_t)' x  |  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x | '(uint256_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 45, x at level 9, y at level 9, format "( '(uint256_t)' x  |  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x | '(uint256_t)' y )" := (Op (Lor (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 45, x at level 9, y at level 9, format "( '(uint256_t)' x  |  '(uint256_t)' y )") : expr_scope.
Notation "( x | '(uint256_t)' y )" := (Op (Lor (TWord 8) (TWord _) (TWord 8)) (Pair x y)) (at level 45, y at level 9, format "( x  |  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x | y )" := (Op (Lor (TWord _) (TWord 8) (TWord 8)) (Pair x y)) (at level 45, x at level 9, format "( '(uint256_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint256_t)' y )" := (Op (Lor (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 45, y at level 9, format "( x  |  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x | y )" := (Op (Lor (TWord _) (TWord 8) (TWord 8)) (Pair x (Var y))) (at level 45, x at level 9, format "( '(uint256_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint256_t)' y )" := (Op (Lor (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 45, y at level 9, format "( x  |  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x | y )" := (Op (Lor (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) y)) (at level 45, x at level 9, format "( '(uint256_t)' x  |  y )") : expr_scope.
Notation "( x | '(uint256_t)' y )" := (Op (Lor (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 45, y at level 9, format "( x  |  '(uint256_t)' y )") : expr_scope.
Notation "( '(uint256_t)' x | y )" := (Op (Lor (TWord _) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (at level 45, x at level 9, format "( '(uint256_t)' x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 8) (TWord 8) (TWord 8)) (Pair x y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 8) (TWord 8) (TWord 8)) (Pair x (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) y)) (format "( x  |  y )") : expr_scope.
Notation "( x | y )" := (Op (Lor (TWord 8) (TWord 8) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  |  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl _ _ _) (Pair x y)) (format "( x  <<  y )") : expr_scope.
Notation "( x <<ℤ y )" := (Op (Shl _ _ TZ) (Pair x y)) (at level 30, format "( x  <<ℤ  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl _ _ _) (Pair x (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( x <<ℤ y )" := (Op (Shl _ _ TZ) (Pair x (Var y))) (at level 30, format "( x  <<ℤ  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl _ _ _) (Pair (Var x) y)) (format "( x  <<  y )") : expr_scope.
Notation "( x <<ℤ y )" := (Op (Shl _ _ TZ) (Pair (Var x) y)) (at level 30, format "( x  <<ℤ  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl _ _ _) (Pair (Var x) (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( x <<ℤ y )" := (Op (Shl _ _ TZ) (Pair (Var x) (Var y))) (at level 30, format "( x  <<ℤ  y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 30, format "( '1&(uint8_t/*bool*/)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (format "( x  <<  y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 30, format "( '1&(uint8_t/*bool*/)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 30, format "( '1&(uint8_t/*bool*/)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (format "( x  <<  y )") : expr_scope.
Notation "( '1&(uint8_t/*bool*/)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 30, format "( '1&(uint8_t/*bool*/)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 1) (TWord _) (TWord 1)) (Pair x y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 2) (TWord _) (TWord 2)) (Pair x y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 3) (TWord _) (TWord 3)) (Pair x y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint8_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 30, format "( '(uint8_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint16_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 30, format "( '(uint16_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 4) (TWord _) (TWord 4)) (Pair x y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint16_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 30, format "( '(uint16_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint16_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 30, format "( '(uint16_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint16_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 30, format "( '(uint16_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint32_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 30, format "( '(uint32_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 5) (TWord _) (TWord 5)) (Pair x y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint32_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 30, format "( '(uint32_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint32_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 30, format "( '(uint32_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint32_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 30, format "( '(uint32_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint64_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 30, format "( '(uint64_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 6) (TWord _) (TWord 6)) (Pair x y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint64_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 30, format "( '(uint64_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint64_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 30, format "( '(uint64_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint64_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 30, format "( '(uint64_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint128_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 30, format "( '(uint128_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 7) (TWord _) (TWord 7)) (Pair x y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint128_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 30, format "( '(uint128_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint128_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 30, format "( '(uint128_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint128_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 30, format "( '(uint128_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint256_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 30, format "( '(uint256_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 8) (TWord _) (TWord 8)) (Pair x y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint256_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 30, format "( '(uint256_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint256_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 30, format "( '(uint256_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)) (format "( x  <<  y )") : expr_scope.
Notation "( '(uint256_t)' x << y )" := (Op (Shl (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 30, format "( '(uint256_t)' x  <<  y )") : expr_scope.
Notation "( x << y )" := (Op (Shl (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  <<  y )") : expr_scope.
Notation "( x >> y )" := (Op (Shr _ _ _) (Pair x y)) (format "( x  >>  y )") : expr_scope.
Notation "( x >>ℤ y )" := (Op (Shr _ _ TZ) (Pair x y)) (at level 30, format "( x  >>ℤ  y )") : expr_scope.
Notation "( x >> y )" := (Op (Shr _ _ _) (Pair x (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "( x >>ℤ y )" := (Op (Shr _ _ TZ) (Pair x (Var y))) (at level 30, format "( x  >>ℤ  y )") : expr_scope.
Notation "( x >> y )" := (Op (Shr _ _ _) (Pair (Var x) y)) (format "( x  >>  y )") : expr_scope.
Notation "( x >>ℤ y )" := (Op (Shr _ _ TZ) (Pair (Var x) y)) (at level 30, format "( x  >>ℤ  y )") : expr_scope.
Notation "( x >> y )" := (Op (Shr _ _ _) (Pair (Var x) (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "( x >>ℤ y )" := (Op (Shr _ _ TZ) (Pair (Var x) (Var y))) (at level 30, format "( x  >>ℤ  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 0)) (Pair x y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 0) (TWord _) (TWord 0)) (Pair x y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 0)) (Pair x (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 0) (TWord _) (TWord 0)) (Pair x (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 0)) (Pair (Var x) y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 0) (TWord _) (TWord 0)) (Pair (Var x) (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 1)) (Pair x y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 1) (TWord _) (TWord 1)) (Pair x y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 1)) (Pair x (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 1) (TWord _) (TWord 1)) (Pair x (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 1)) (Pair (Var x) y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 1) (TWord _) (TWord 1)) (Pair (Var x) (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 2)) (Pair x y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 2) (TWord _) (TWord 2)) (Pair x y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 2)) (Pair x (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 2) (TWord _) (TWord 2)) (Pair x (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 2)) (Pair (Var x) y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 2) (TWord _) (TWord 2)) (Pair (Var x) (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 3)) (Pair x y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 3) (TWord _) (TWord 3)) (Pair x y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 3)) (Pair x (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 3) (TWord _) (TWord 3)) (Pair x (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 3)) (Pair (Var x) y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint8_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 3) (TWord _) (TWord 3)) (Pair (Var x) (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint16_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 4)) (Pair x y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 4) (TWord _) (TWord 4)) (Pair x y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint16_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 4)) (Pair x (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 4) (TWord _) (TWord 4)) (Pair x (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint16_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 4)) (Pair (Var x) y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint16_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 4) (TWord _) (TWord 4)) (Pair (Var x) (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint32_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 5)) (Pair x y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 5) (TWord _) (TWord 5)) (Pair x y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint32_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 5)) (Pair x (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 5) (TWord _) (TWord 5)) (Pair x (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint32_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 5)) (Pair (Var x) y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint32_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 5) (TWord _) (TWord 5)) (Pair (Var x) (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint64_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 6)) (Pair x y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 6) (TWord _) (TWord 6)) (Pair x y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint64_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 6)) (Pair x (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 6) (TWord _) (TWord 6)) (Pair x (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint64_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 6)) (Pair (Var x) y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint64_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 6) (TWord _) (TWord 6)) (Pair (Var x) (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint128_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 7)) (Pair x y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 7) (TWord _) (TWord 7)) (Pair x y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint128_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 7)) (Pair x (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 7) (TWord _) (TWord 7)) (Pair x (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint128_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 7)) (Pair (Var x) y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint128_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 7) (TWord _) (TWord 7)) (Pair (Var x) (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint256_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 8)) (Pair x y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 8) (TWord _) (TWord 8)) (Pair x y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint256_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 8)) (Pair x (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 8) (TWord _) (TWord 8)) (Pair x (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'(uint256_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 8)) (Pair (Var x) y)) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) y)) (format "( x  >>  y )") : expr_scope.
Notation "'(uint256_t)' ( x >> y )" := (Op (Shr (TWord _) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (at level 30) : expr_scope.
Notation "( x >> y )" := (Op (Shr (TWord 8) (TWord _) (TWord 8)) (Pair (Var x) (Var y))) (format "( x  >>  y )") : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord _) (TWord _)) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord _) (TWord _)) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord _) (TWord _)) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord _) (TWord _)) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz32' ( v ,  x ,  y )") : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S _)))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S _)))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz32' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S _)))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz64' ( v ,  x ,  y )") : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz64' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S _))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznz128' ( v ,  x ,  y )") : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznz128' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _)))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _)) (Pair (Pair v x) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _)) (Pair (Pair v x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _)) (Pair (Pair v (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _)) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _)) (Pair (Pair (Var v) x) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _)) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _)) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _)) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t/*bool*/)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S _))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S _))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S _))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S _))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S _))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S _))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S _))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S _))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S _)))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S _)))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S _)))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S _)))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S _)))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S _)))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S _)))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S _))))) (Pair (Pair v x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S _))))) (Pair (Pair v x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S _))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint8_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S _))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint8_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v x) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v x) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S _)))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint16_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S _)))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint16_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v x) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint32_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S _))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint32_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v x) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint64_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S _)))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint64_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v x) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair v (Var x)) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) x) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) y)) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'(uint128_t)' 'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S _))))))))) (Pair (Pair (Var v) (Var x)) (Var y))) (format "'(uint128_t)' 'cmovznzℤ' ( v ,  x ,  y )") : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord _) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect (TWord _) (TWord _) (TWord (S (S (S (S (S (S (S (S _))))))))) (TWord (S (S (S (S (S (S (S (S _)))))))))) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect TZ _ _ _) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ TZ _ _) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ TZ _) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ _ TZ) (Pair (Pair v x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect TZ _ _ _) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ TZ _ _) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ TZ _) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ _ TZ) (Pair (Pair v x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect TZ _ _ _) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ TZ _ _) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ TZ _) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ _ TZ) (Pair (Pair v (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect TZ _ _ _) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ TZ _ _) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ TZ _) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ _ TZ) (Pair (Pair v (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect TZ _ _ _) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ TZ _ _) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ TZ _) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ _ TZ) (Pair (Pair (Var v) x) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect TZ _ _ _) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ TZ _ _) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ TZ _) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ _ TZ) (Pair (Pair (Var v) x) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect TZ _ _ _) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ TZ _ _) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ TZ _) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ _ TZ) (Pair (Pair (Var v) (Var x)) y)) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect TZ _ _ _) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ TZ _ _) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ TZ _) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'cmovznzℤ' ( v , x , y )" := (Op (Zselect _ _ _ TZ) (Pair (Pair (Var v) (Var x)) (Var y))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u32' ( c , a , b )" := (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u64' ( c , a , b )" := (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u128' ( c , a , b )" := (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u25' ( c , a , b )" := (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u26' ( c , a , b )" := (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u51' ( c , a , b )" := (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u32' ( c , a , b )" := (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u64' ( c , a , b )" := (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u128' ( c , a , b )" := (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u25' ( c , a , b )" := (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u26' ( c , a , b )" := (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 (TWord 0) (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u51' ( c , a , b )" := (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 5)) (Pair a b)) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 5)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 5)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32_out_u1' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 0) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 0) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 0) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 0) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 0) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 0) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 0) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32_out_u8' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 3) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 3) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 3) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 3) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 3) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 3) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 3) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64_out_u1' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64_out_u8' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 7)) (Pair a b)) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 7)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 7)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128_out_u1' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 0) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 0) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 0) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 0) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 0) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 0) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 0) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128_out_u8' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 3) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 3) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 3) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 3) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 3) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 3) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 3) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair a b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair a b)) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair a b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'1&(uint8_t/*bool*/)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51_out_u1' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 0) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 0) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '1&(uint8_t/*bool*/)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 0) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u1' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 0)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'(uint8_t)' 'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51_out_u8' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 3) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 3) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '(uint8_t)' '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 3) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51_out_u8' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 3)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u32' ( a , b )" := (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u32' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 (TWord 5) (TWord 5) (TWord 5) (TWord 5)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u64' ( a , b )" := (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u64' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u128' ( a , b )" := (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u128' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 (TWord 7) (TWord 7) (TWord 7) (TWord 7)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u51' ( a , b )" := (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u51' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 (TWord 6) (TWord 6) (TWord 6) (TWord 6)) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u32ℤ' ( c , a , b )" := (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 32 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u64ℤ' ( c , a , b )" := (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 64 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u128ℤ' ( c , a , b )" := (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 128 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u25ℤ' ( c , a , b )" := (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 25 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u26ℤ' ( c , a , b )" := (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 26 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'addcarryx_u51ℤ' ( c , a , b )" := (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_addcarryx_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (AddWithGetCarry 51 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u32ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u32ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 32 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u64ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u64ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 64 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u128ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u128ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 128 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u25ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u25ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 25 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u26ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u26ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 26 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair c a) b)) : expr_scope.
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair c a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair c a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) : expr_scope.
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair c a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair c a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) : expr_scope.
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair c (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair c (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) : expr_scope.
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair (Var c) a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair (Var c) a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
Notation "'subborrow_u51ℤ' ( c , a , b )" := (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ _ TZ) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_subborrow_u51ℤ' ( c , a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (SubWithGetBorrow 51 _ _ _ TZ _) (Pair (Pair (Var c) (Var a)) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u32ℤ' ( a , b )" := (Op (MulSplit 32 _ _ _ TZ) (Pair a b)) : expr_scope.
Notation "'mulx_u32ℤ' ( a , b )" := (Op (MulSplit 32 _ _ TZ _) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u32ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 _ _ _ TZ) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 _ _ TZ _) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u32ℤ' ( a , b )" := (Op (MulSplit 32 _ _ _ TZ) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u32ℤ' ( a , b )" := (Op (MulSplit 32 _ _ TZ _) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u32ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 _ _ _ TZ) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 _ _ TZ _) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u32ℤ' ( a , b )" := (Op (MulSplit 32 _ _ _ TZ) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u32ℤ' ( a , b )" := (Op (MulSplit 32 _ _ TZ _) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u32ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 _ _ _ TZ) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 _ _ TZ _) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u32ℤ' ( a , b )" := (Op (MulSplit 32 _ _ _ TZ) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u32ℤ' ( a , b )" := (Op (MulSplit 32 _ _ TZ _) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u32ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 _ _ _ TZ) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u32ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 32 _ _ TZ _) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u64ℤ' ( a , b )" := (Op (MulSplit 64 _ _ _ TZ) (Pair a b)) : expr_scope.
Notation "'mulx_u64ℤ' ( a , b )" := (Op (MulSplit 64 _ _ TZ _) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u64ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 _ _ _ TZ) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 _ _ TZ _) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u64ℤ' ( a , b )" := (Op (MulSplit 64 _ _ _ TZ) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u64ℤ' ( a , b )" := (Op (MulSplit 64 _ _ TZ _) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u64ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 _ _ _ TZ) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 _ _ TZ _) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u64ℤ' ( a , b )" := (Op (MulSplit 64 _ _ _ TZ) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u64ℤ' ( a , b )" := (Op (MulSplit 64 _ _ TZ _) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u64ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 _ _ _ TZ) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 _ _ TZ _) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u64ℤ' ( a , b )" := (Op (MulSplit 64 _ _ _ TZ) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u64ℤ' ( a , b )" := (Op (MulSplit 64 _ _ TZ _) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u64ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 _ _ _ TZ) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u64ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 64 _ _ TZ _) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u128ℤ' ( a , b )" := (Op (MulSplit 128 _ _ _ TZ) (Pair a b)) : expr_scope.
Notation "'mulx_u128ℤ' ( a , b )" := (Op (MulSplit 128 _ _ TZ _) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u128ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 _ _ _ TZ) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 _ _ TZ _) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u128ℤ' ( a , b )" := (Op (MulSplit 128 _ _ _ TZ) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u128ℤ' ( a , b )" := (Op (MulSplit 128 _ _ TZ _) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u128ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 _ _ _ TZ) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 _ _ TZ _) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u128ℤ' ( a , b )" := (Op (MulSplit 128 _ _ _ TZ) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u128ℤ' ( a , b )" := (Op (MulSplit 128 _ _ TZ _) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u128ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 _ _ _ TZ) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 _ _ TZ _) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u128ℤ' ( a , b )" := (Op (MulSplit 128 _ _ _ TZ) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u128ℤ' ( a , b )" := (Op (MulSplit 128 _ _ TZ _) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u128ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 _ _ _ TZ) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u128ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 128 _ _ TZ _) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u51ℤ' ( a , b )" := (Op (MulSplit 51 _ _ _ TZ) (Pair a b)) : expr_scope.
Notation "'mulx_u51ℤ' ( a , b )" := (Op (MulSplit 51 _ _ TZ _) (Pair a b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u51ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 _ _ _ TZ) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 _ _ TZ _) (Pair a b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u51ℤ' ( a , b )" := (Op (MulSplit 51 _ _ _ TZ) (Pair a (Var b))) : expr_scope.
Notation "'mulx_u51ℤ' ( a , b )" := (Op (MulSplit 51 _ _ TZ _) (Pair a (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u51ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 _ _ _ TZ) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 _ _ TZ _) (Pair a (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u51ℤ' ( a , b )" := (Op (MulSplit 51 _ _ _ TZ) (Pair (Var a) b)) : expr_scope.
Notation "'mulx_u51ℤ' ( a , b )" := (Op (MulSplit 51 _ _ TZ _) (Pair (Var a) b)) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u51ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 _ _ _ TZ) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 _ _ TZ _) (Pair (Var a) b)) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation "'mulx_u51ℤ' ( a , b )" := (Op (MulSplit 51 _ _ _ TZ) (Pair (Var a) (Var b))) : expr_scope.
Notation "'mulx_u51ℤ' ( a , b )" := (Op (MulSplit 51 _ _ TZ _) (Pair (Var a) (Var b))) : expr_scope.
(*Notation "T0 out ; T1 c_out = '_mulx_u51ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 _ _ _ TZ) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
(*Notation "T0 out ; T1 c_out = '_mulx_u51ℤ' ( a , b , & out ) ; REST" := (LetIn (tx:=Prod T0 T1) (Op (MulSplit 51 _ _ TZ _) (Pair (Var a) (Var b))) (fun '((out, c_out)%core) => REST)) : expr_scope.*)
Notation Return x := (Var x).
Notation C_like := (Expr base_type op _).
