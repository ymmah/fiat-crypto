Require Import Crypto.Spec.Encoding.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.CompleteEdwardsCurve.

Require Import Crypto.Util.WordUtil.
Require Bedrock.Word.
Require Coq.ZArith.Znumtheory Coq.ZArith.BinInt.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.

Coercion Word.wordToNat : Word.word >-> nat.

Infix "^" := NPeano.pow.
Infix "mod" := NPeano.modulo.
Infix "++" := Word.combine.

Section EdDSAParams.

  Class EdDSAParams := { (* <https://eprint.iacr.org/2015/677.pdf> *)
    E : TwistedEdwardsParams; (* underlying elliptic curve *)

    b : nat; (* public keys are k bits, signatures are 2*k bits *)
    b_valid : 2^(b - 1) > BinInt.Z.to_nat q;
    FqEncoding : encoding of F q as Word.word (b-1);
    PointEncoding : encoding of point as Word.word b;

    H : forall {n}, Word.word n -> Word.word (b + b); (* main hash function *)

    c : nat; (* cofactor E = 2^c *)
    c_valid : c = 2 \/ c = 3;

    n : nat; (* secret keys are (n+1) bits *)
    n_ge_c : n >= c;
    n_le_b : n <= b;

    B : point;
    B_not_identity : B <> zero;

    l : nat; (* order of the subgroup of E generated by B *)
    l_prime : Znumtheory.prime (BinInt.Z.of_nat l);
    l_odd : l > 2;
    l_order_B : (l*B)%E = zero;
    FlEncoding : encoding of F (BinInt.Z.of_nat l) as Word.word b
  }.
End EdDSAParams.

Section EdDSA.
  Context {prm:EdDSAParams}.
  Existing Instance E.
  Existing Instance PointEncoding.
  Existing Instance FlEncoding.
  Existing Class le.
  Existing Instance n_le_b.

  Notation secretkey := (Word.word b) (only parsing).
  Notation publickey := (Word.word b) (only parsing).
  Notation signature := (Word.word (b + b)) (only parsing).
  Let point_eq_dec : forall P Q, {P = Q} + {P <> Q} := CompleteEdwardsCurveTheorems.point_eq_dec.
  Local Infix "==" := point_eq_dec (at level 70) : E_scope .

  (* TODO: proofread curveKey and definition of n *)
  Definition curveKey (sk:secretkey) : nat :=
    let x := wfirstn n sk in (* first half of the secret key is a scalar *)
    let x := x - (x mod (2^c)) in (* it is implicitly 0 mod (2^c) *)
             x + 2^n. (* and the high bit is always set *)
  Definition prngKey (sk:secretkey) : Word.word b := Word.split2 b b (H sk).
  Definition public (sk:secretkey) : publickey := enc (curveKey sk * B)%E.

  Definition sign (A_:publickey) sk {n} (M : Word.word n) :=
    let r : nat := H (prngKey sk ++ M) in (* secret nonce *)
    let R : point := (r * B)%E in (* commitment to nonce *)
    let s : nat := curveKey sk in (* secret scalar *)
    let S : F (BinInt.Z.of_nat l) := ZToField (BinInt.Z.of_nat
                              (r + H (enc R ++ public sk ++ M) * s)) in
        enc R ++ enc S.

  Definition verify (A_:publickey) {n:nat} (M : Word.word n) (sig:signature) : bool :=
    let R_ := Word.split1 b b sig in
    let S_ := Word.split2 b b sig in
    match dec S_ : option (F (BinInt.Z.of_nat l)) with None => false | Some S' =>
    match dec A_ : option point with None => false | Some A =>
    match dec R_ : option point with None => false | Some R =>
    if BinInt.Z.to_nat (FieldToZ S') * B == R + (H (R_ ++ A_ ++ M)) * A
    then true else false
    end
    end
    end%E.
End EdDSA.