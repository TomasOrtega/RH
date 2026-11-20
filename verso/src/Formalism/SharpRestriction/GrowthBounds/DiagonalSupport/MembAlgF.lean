import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembTop
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Imports

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section K

variable {O : Type} [CommRing O] [IsDomain O] {n' m r K : ℕ} (hk : m + 1 = r + K)

/- English proof (translation)
Unfold `toKK`. Rewrite using `[map_mul, map_mul]`.
-/
theorem toKK_mul (P Q : RRing O n' (r + K)) : toKK hk (P * Q) = toKK hk P * toKK hk Q := by
  unfold toKK
  rw [map_mul, map_mul]

/- English proof (translation)
Unfold `toKK`. Rewrite using `[map_add, map_add]`.
-/
theorem toKK_add (P Q : RRing O n' (r + K)) : toKK hk (P + Q) = toKK hk P + toKK hk Q := by
  unfold toKK
  rw [map_add, map_add]

/- English proof (translation)
Simplify using `[toKK]`.
-/
theorem toKK_C (a : O) : toKK hk (C a : RRing O n' (r + K)) = C (algebraMap O (KK O) a) := by
  simp [toKK]

/- English proof (translation)
Simplify using `only [toKK, map_pow, rename_X, map_X]`. Both sides reduce to the same expression.
-/
theorem toKK_X_pow (v : Fin n' × Fin (r + K)) (n : ℕ) :
    toKK hk ((X v : RRing O n' (r + K)) ^ n) = (X (v.1, Fin.cast hk.symm v.2)) ^ n := by
  simp only [toKK, map_pow, rename_X, map_X]
  rfl

end K

section Shift

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J]

/- English proof (translation)
Establish `hv : (j + 1).val = (j.val + 1) % J`. Rewrite using `[ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]`. Establish `hlt` using `ZMod.val_lt j`. Break down `Nat.lt_or_ge (j.val + 1) J with h | h` into its components or cases. Use `⟨0, Or.inl rfl, fun i => ?_⟩` and prove the remaining obligations.

Establish `e : segZ (j + 1) = segZ j + 1`. Unfold `segZ`. Rewrite using `[hv, Nat.mod_eq_of_lt h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Simplify using the standard rewrite rules. Establish `hJe : j.val + 1 = J` using `by omega`. Use `⟨n', Or.inr rfl, fun i => ?_⟩` and prove the remaining obligations. Establish `e : segZ (j + 1) = 0`.

Unfold `segZ`. Rewrite using `[hv, hJe, Nat.mod_self]`. Both sides reduce to the same expression. Establish `e2 : segZ j + 1 = 0 + (Fr.J : ℤ)`. Unfold `segZ`.

Rewrite using `[← hJ]`. Use linear arithmetic over natural numbers and integers. Establish `e3 : segZ j = -1 + (Fr.J : ℤ)` using `by omega`. Rewrite using `[e, e2, e3]`. Conclude with `⟨hV.2.1 0 i, by simpa using hV.2.1 (-1) i⟩`.
-/
theorem seg_shift' (hV : Fr.Valid L₁ N₁) (hJ : J = Fr.J) (j : ZMod J) :
    ∃ s : ℤ, (s = 0 ∨ s = n') ∧
      ∀ i, Fr.fr (segZ j + 1) i = Fr.fr (segZ (j + 1)) i + s ∧ Fr.fr (segZ j) i = Fr.fr (segZ (j + 1) - 1) i + s := by
  have hv : (j + 1).val = (j.val + 1) % J := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  have hlt := ZMod.val_lt j
  rcases Nat.lt_or_ge (j.val + 1) J with h | h
  · refine ⟨0, Or.inl rfl, fun i => ?_⟩
    have e : segZ (j + 1) = segZ j + 1 := by
      unfold segZ
      rw [hv, Nat.mod_eq_of_lt h]
      push_cast; ring
    rw [e]
    simp
  · have hJe : j.val + 1 = J := by omega
    refine ⟨n', Or.inr rfl, fun i => ?_⟩
    have e : segZ (j + 1) = 0 := by
      unfold segZ
      rw [hv, hJe, Nat.mod_self]
      rfl
    have e2 : segZ j + 1 = 0 + (Fr.J : ℤ) := by
      unfold segZ
      rw [← hJ]
      omega
    have e3 : segZ j = -1 + (Fr.J : ℤ) := by omega
    rw [e, e2, e3]
    exact ⟨hV.2.1 0 i, by simpa using hV.2.1 (-1) i⟩

/- English proof (translation)
Take `⟨s, hs, h⟩` from `seg_shift' hV hJ j`. Establish `h1` using `(h i).2`. Establish `h2` using `(h (r - 1)).1`. Establish `h3` using `ph_z_mono Fr hV hr (j := segZ j) (j' := segZ j + 1) (by omega)`. Establish `h4` using `frame_entry_le_last Fr L₁ N₁ hV (segZ j) i hi`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`. Break down `hs with rfl | rfl` into its components or cases. Rewrite using `[add_zero]`. Conclude with `(bf_posOf_add _).symm`.

Unfold `Frames.dist`. Use linear arithmetic over natural numbers and integers.
-/
theorem wc_geom (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (j : ZMod J) (i : ℕ) (hi : i < r) :
    posOf n' (Fr.fr (segZ (j + 1) - 1) i) = posOf n' (Fr.fr (segZ j) i) ∧
    Fr.dist (segZ (j + 1)) (Fr.fr (segZ (j + 1) - 1) i) =
      Fr.dist (segZ j) (Fr.fr (segZ j) i) + (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat := by
  obtain ⟨s, hs, h⟩ := seg_shift' hV hJ j
  have h1 := (h i).2
  have h2 := (h (r - 1)).1
  have h3 := ph_z_mono Fr hV hr (j := segZ j) (j' := segZ j + 1) (by omega)
  have h4 := frame_entry_le_last Fr L₁ N₁ hV (segZ j) i hi
  refine ⟨?_, ?_⟩
  · rw [h1]
    rcases hs with rfl | rfl
    · rw [add_zero]
    · exact (bf_posOf_add _).symm
  · unfold Frames.dist
    omega

end Shift

section Hom

variable (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) {L₁ N₁ : ℕ} {J : ℕ} [NeZero J]
  (Dt : SignedChainData p O r J)

/- English proof (translation)
Take `⟨x, a⟩` from `v`. Unfold `xiPl PhiPl`. Rewrite using `[rename_X, aeval_X, toKK_X_pow]`. Unfold `SignedChainData.ph upPl`. Rewrite using `[aeval_X]`.

Consider the cases of `x with`. Consider the case `ll j l => simp only [aeval_X]`. Both sides reduce to the same expression. Consider the case `lab j mm => simp only [aeval_X]`. Both sides reduce to the same expression.

Consider the case `tp j mm h => simp only [aeval_X]`. Both sides reduce to the same expression. Consider the case `wc j mm`. Simplify using `only [map_pow, aeval_X]`. Take `⟨g1, g2⟩` from `wc_geom (Fr := Fr) hV hr hJ j (r - 1 - mm.val) (by omega)`.

Rewrite using `[← pow_mul]`. Establish `e1 : (mlPos Fr Dt.nL (ML.wc j mm)) = (j + 1, Fr.fr (segZ (j + 1) - 1) (r - 1 - mm.val))` using `rfl`. Simplify using `only [e1]`. Rewrite using `[g1, g2, pow_add]`. Unfold `SignedChainData.P`.

Rewrite using `[hgP]`. Both sides reduce to the same expression.
-/
theorem plane_X (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hgP : ∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat)
    (v : ML J Dt.nL r × Fin r) :
    toKK hk (PhiPl Fr p O K J (xiPl Fr O Dt.nL (X v))) = upPl Fr p O hk Dt.nL (Dt.ph (X v)) := by
  obtain ⟨x, a⟩ := v
  unfold xiPl PhiPl
  rw [rename_X, aeval_X, toKK_X_pow]
  unfold SignedChainData.ph upPl
  rw [aeval_X]
  cases x with
  | ll j l => simp only [aeval_X]; rfl
  | lab j mm => simp only [aeval_X]; rfl
  | tp j mm h => simp only [aeval_X]; rfl
  | wc j mm =>
    simp only [map_pow, aeval_X]
    obtain ⟨g1, g2⟩ := wc_geom (Fr := Fr) hV hr hJ j (r - 1 - mm.val) (by omega)
    rw [← pow_mul]
    have e1 : (mlPos Fr Dt.nL (ML.wc j mm)) = (j + 1, Fr.fr (segZ (j + 1) - 1) (r - 1 - mm.val)) := rfl
    simp only [e1]
    rw [g1, g2, pow_add]
    unfold SignedChainData.P
    rw [hgP]
    rfl

/- English proof (translation)
Proceed by induction on `Go using MvPolynomial.induction_on with`. Consider the case `C a`. Unfold `xiPl`. Rewrite using `[rename_C, map_C]`. Establish `h1 : PhiPl Fr p O K J (C a) = C a` using `by unfold PhiPl; rw [aeval_C]; rfl`.

Establish `h2 : Dt.ph (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a)`. Unfold `SignedChainData.ph`. Rewrite using `[aeval_C]`. Both sides reduce to the same expression. Establish `h3 : upPl Fr p O hk Dt.nL (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a)`.

Unfold `upPl`. Rewrite using `[aeval_C]`. Both sides reduce to the same expression. Rewrite using `[h1, h2, h3, toKK_C]`. Consider the case `add P Q hP hQ`.

Establish `e : xiPl Fr O Dt.nL (P + Q) = xiPl Fr O Dt.nL P + xiPl Fr O Dt.nL Q` using `by unfold xiPl; rw [map_add]`. Rewrite using `[e, map_add, toKK_add, hP, hQ, map_add, map_add, map_add]`. Consider the case `mul_X P v hP`. Establish `e : xiPl Fr O Dt.nL (P * X v) = xiPl Fr O Dt.nL P * xiPl Fr O Dt.nL (X v)` using `by unfold xiPl; rw [map_mul]`. Rewrite using `[e, map_mul, toKK_mul, hP, plane_X p O hk Fr Dt hV hr hJ hgP v, map_mul, map_mul, map_mul, map_X]`.
-/
theorem plane_hom (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hgP : ∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat)
    (Go : MvPolynomial (ML J Dt.nL r × Fin r) O) :
    toKK hk (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go)) =
      upPl Fr p O hk Dt.nL (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go)) := by
  induction Go using MvPolynomial.induction_on with
  | C a =>
    unfold xiPl
    rw [rename_C, map_C]
    have h1 : PhiPl Fr p O K J (C a) = C a := by unfold PhiPl; rw [aeval_C]; rfl
    have h2 : Dt.ph (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a) := by
      unfold SignedChainData.ph; rw [aeval_C]; rfl
    have h3 : upPl Fr p O hk Dt.nL (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a) := by
      unfold upPl; rw [aeval_C]; rfl
    rw [h1, h2, h3, toKK_C]
  | add P Q hP hQ =>
    have e : xiPl Fr O Dt.nL (P + Q) = xiPl Fr O Dt.nL P + xiPl Fr O Dt.nL Q := by unfold xiPl; rw [map_add]
    rw [e, map_add, toKK_add, hP, hQ, map_add, map_add, map_add]
  | mul_X P v hP =>
    have e : xiPl Fr O Dt.nL (P * X v) = xiPl Fr O Dt.nL P * xiPl Fr O Dt.nL (X v) := by unfold xiPl; rw [map_mul]
    rw [e, map_mul, toKK_mul, hP, plane_X p O hk Fr Dt hV hr hJ hgP v, map_mul, map_mul, map_mul, map_X]

/- English proof (translation)
Proceed by induction on `No using MvPolynomial.induction_on with`. Consider the case `C a`. Unfold `xiNo`. Rewrite using `[rename_C, map_C]`. Establish `h1 : PhiNo Fr p O K J (C a) = C a` using `by unfold PhiNo; rw [aeval_C]; rfl`.

Establish `h3 : upNo Fr p O hk nL (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a)`. Unfold `upNo`. Rewrite using `[aeval_C]`. Both sides reduce to the same expression. Rewrite using `[h1, h3, toKK_C]`.

Consider the case `add P Q hP hQ`. Establish `e : xiNo Fr O K nL (P + Q) = xiNo Fr O K nL P + xiNo Fr O K nL Q` using `by unfold xiNo; rw [map_add]`. Rewrite using `[e, map_add, toKK_add, hP, hQ, map_add, map_add]`. Consider the case `mul_X P v hP`. Establish `e : xiNo Fr O K nL (P * X v) = xiNo Fr O K nL P * xiNo Fr O K nL (X v)` using `by unfold xiNo; rw [map_mul]`.

Establish `hX : toKK hk (PhiNo Fr p O K J (xiNo Fr O K nL (X v))) = upNo Fr p O hk nL (X v)`. Unfold `xiNo PhiNo upNo`. Rewrite using `[rename_X, aeval_X, toKK_X_pow, aeval_X]`. Both sides reduce to the same expression. Rewrite using `[e, map_mul, toKK_mul, hP, hX, map_mul, map_mul, map_X]`.
-/
theorem normal_hom (nL : ZMod J → ℕ) (No : MvPolynomial (TL J nL r × Fin K) O) :
    toKK hk (PhiNo Fr p O K J (xiNo Fr O K nL No)) =
      upNo Fr p O hk nL (MvPolynomial.map (algebraMap O (KK O)) No) := by
  induction No using MvPolynomial.induction_on with
  | C a =>
    unfold xiNo
    rw [rename_C, map_C]
    have h1 : PhiNo Fr p O K J (C a) = C a := by unfold PhiNo; rw [aeval_C]; rfl
    have h3 : upNo Fr p O hk nL (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a) := by
      unfold upNo; rw [aeval_C]; rfl
    rw [h1, h3, toKK_C]
  | add P Q hP hQ =>
    have e : xiNo Fr O K nL (P + Q) = xiNo Fr O K nL P + xiNo Fr O K nL Q := by unfold xiNo; rw [map_add]
    rw [e, map_add, toKK_add, hP, hQ, map_add, map_add]
  | mul_X P v hP =>
    have e : xiNo Fr O K nL (P * X v) = xiNo Fr O K nL P * xiNo Fr O K nL (X v) := by unfold xiNo; rw [map_mul]
    have hX : toKK hk (PhiNo Fr p O K J (xiNo Fr O K nL (X v))) = upNo Fr p O hk nL (X v) := by
      unfold xiNo PhiNo upNo
      rw [rename_X, aeval_X, toKK_X_pow, aeval_X]
      rfl
    rw [e, map_mul, toKK_mul, hP, hX, map_mul, map_mul, map_X]

/- English proof (translation)
Establish `h : Finsupp.mapDomain (castVK (n'` using `n') hk) (labO Fr K nL rho) = labMon Fr hk nL rho := by`. Rewrite using `[labMon_eq, Fintype.sum_prod_type]`. Unfold `labO`. Rewrite using `[Finsupp.mapDomain_finsetSum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.mapDomain_finsetSum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.mapDomain_single]`. Both sides reduce to the same expression. Unfold `toKK`.

Rewrite using `[rename_monomial, map_monomial, map_one, h]`.
-/
theorem label_hom (nL : ZMod J → ℕ) (rho : TL J nL r × Fin (r + K) → ℕ) :
    toKK hk (monomial (labO Fr K nL rho) (1 : O)) = monomial (labMon Fr hk nL rho) 1 := by
  have h : Finsupp.mapDomain (castVK (n' := n') hk) (labO Fr K nL rho) = labMon Fr hk nL rho := by
    rw [labMon_eq, Fintype.sum_prod_type]
    unfold labO
    rw [Finsupp.mapDomain_finsetSum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finsupp.mapDomain_finsetSum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finsupp.mapDomain_single]
    rfl
  unfold toKK
  rw [rename_monomial, map_monomial, map_one, h]

/- English proof (translation)
Unfold `AlgAt asm`. Rewrite using `[toKK_mul, toKK_mul, label_hom, plane_hom p O hk Fr Dt hV hr hJ hgP, normal_hom, mul_assoc]`.
-/
theorem alg_identity (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hgP : ∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat)
    (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
    (Go : MvPolynomial (ML J Dt.nL r × Fin r) O) : AlgAt p O hk Fr Dt rho No Go := by
  unfold AlgAt asm
  rw [toKK_mul, toKK_mul, label_hom, plane_hom p O hk Fr Dt hV hr hJ hgP, normal_hom, mul_assoc]

end Hom

/- English proof (translation)
Introduce `p _ n' r K m _ _ _ O _ _ _ _ hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka rho No Go hMH`. Conclude with `alg_identity p O hk Fr Dt hM.frames.2.1 (le_trans (by norm_num) hM.two_le_r) hMH.1.1.1 hMH.1.1.2.2.2.2.1 rho No Go`.
-/
theorem restAlgG : RestAlgG := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka rho No Go hMH
  exact alg_identity p O hk Fr Dt hM.frames.2.1 (le_trans (by norm_num) hM.two_le_r) hMH.1.1.1 hMH.1.1.2.2.2.2.1 rho No Go

end Formalism.MainNotions.Proposition5Numerics
