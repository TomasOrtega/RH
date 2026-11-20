import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipRat
import Formalism.HermitianLattices.HermitianLatticesProofs.MajLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped Classical

namespace Formalism.L2.SG.Pf.RCoc

open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
The claim follows from `hx.map (RingHom.toIntAlgHom (X.ιE.symm : D.host.E →+* X.B.I.E))`.
-/
theorem isInt_symm {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (X.ιE.symm x) :=
  hx.map (RingHom.toIntAlgHom (X.ιE.symm : D.host.E →+* X.B.I.E))

/- English proof (translation)
The claim follows from `hx.map (RingHom.toIntAlgHom (X.ιE : X.B.I.E →+* D.host.E))`.
-/
theorem isInt_fwd {x : X.B.I.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (X.ιE x) :=
  hx.map (RingHom.toIntAlgHom (X.ιE : X.B.I.E →+* D.host.E))

/- English proof (translation)
Rewrite using `[← Int.cast_natCast, Nat.cast_pow, Int.natCast_natAbs, sq_abs, sq, Int.cast_mul]`.
-/
theorem natAbs_sq_cast {K : Type*} [Ring K] (z : ℤ) : (((z.natAbs ^ 2 : ℕ)) : K) = (z : K) * (z : K) := by
  rw [← Int.cast_natCast, Nat.cast_pow, Int.natCast_natAbs, sq_abs, sq, Int.cast_mul]

/- English proof (translation)
Use `first`. Consider the case `exact Formalism.L2.SG.Pf.Vanish2.crd_sub' (X := X) a b`. Consider the case `exact map_sub _ a b`. Consider the case `(funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf])`.
-/
theorem crd_sub_lat (a b : (VS D).V) : X.crd (a - b) = X.crd a - X.crd b := by
  first
    | exact Formalism.L2.SG.Pf.Vanish2.crd_sub' (X := X) a b
    | exact map_sub _ a b
    | (funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf])

/- English proof (translation)
Simplify using `[Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]`.
-/
theorem repr_crd (a : (VS D).V) (i : Fin X.B.I.n) : X.bas.repr a i = X.ιE (X.crd a i) := by
  simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

/- English proof (translation)
Take `⟨d, hd0, hd⟩` from `Formalism.HermitianLatticesTheory.majLattice_exists_d X.bas Λ hΛ.fg`. Establish `hc : ∀ i, ∃ c : ℤ, c ≠ 0 ∧ c • X.bas i ∈ Λ` using `fun i => Formalism.HermitianLatticesTheory.majLattice_exists_c Λ hΛ.span_eq_top (X.bas i)`. Use `choose c hc0 hcm using hc`. Use `set C : ℤ := ∏ i, c i with hC`. Establish `hCm : ∀ i, (C * C) • X.bas i ∈ Λ`.

Introduce `i`. Establish `e : C = (∏ j ∈ Finset.univ.erase i, c j) * c i`. Rewrite using `[hC, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]`. Establish `h1 : C • X.bas i ∈ Λ`. Rewrite using `[e, mul_smul]`.

Conclude with `zsmul_mem (hcm i) _`. Rewrite using `[mul_smul]`. Conclude with `zsmul_mem h1 _`. Establish `hC0 : C ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => hc0 i`. Use `⟨d.natAbs ^ 2 * C.natAbs ^ 2, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : 0 < d.natAbs` using `Int.natAbs_pos.2 hd0`. Establish `h2 : 0 < C.natAbs` using `Int.natAbs_pos.2 hC0`. Use `Nat.mul_pos (pow_pos h1 2) (pow_pos h2 2)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce and unpack `G ⟨A, hA, hGA⟩ g hg y hy`.

Use `set v := A *ᵥ X.crd y with hv`. Establish `hw : X.crd (g y - y) = ((d.natAbs ^ 2 * C.natAbs ^ 2 : ℕ) : X.B.I.E) • v`. Rewrite using `[crd_sub_lat, hg, ← Matrix.one_mulVec (X.crd y), Matrix.mulVec_mulVec, Matrix.mul_one, ← Matrix.sub_mulVec, hGA, Matrix.smul_mulVec]`. Establish `hvi : ∀ i, IsIntegral ℤ (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i)`. Introduce `i`.

Rewrite using `[hv, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `IsIntegral.sum _ fun j _ => ?_` and prove the remaining obligations. Establish `e : ((d.natAbs ^ 2 : ℕ) : X.B.I.E) * (A i j * X.crd y j) = A i j * X.ιE.symm ((d : D.host.E) * ((d : D.host.E) * X.bas.repr y j))`. Rewrite using `[natAbs_sq_cast]`. Simplify using `only [HidaSetting.crd, crdOf, map_mul, map_intCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(hA i j).mul (isInt_symm X ((isInt_intCast d).mul (hd y hy j)))`. Use `choose r hr using fun i => (⟨⟨X.ιE (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i), isInt_fwd X (hvi i)⟩, rfl⟩ : ∃ r : 𝓞 D.host.E, (r : D.host.E) = X.ιE (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i))`. Establish `hsum : g y - y = ∑ i, r i • ((C * C) • X.bas i)` using `by conv_lhs => rw [← X.bas.sum_repr (g y - y)]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[repr_crd, hw, Pi.smul_apply, smul_eq_mul, ← algebraMap_smul D.host.E (r i), ← Int.cast_smul_eq_zsmul D.host.E, smul_smul]`. Use `congr 1`. Use `show _ = (r i : D.host.E) * _`. Rewrite using `[hr, Nat.cast_mul, mul_assoc, mul_comm, map_mul, map_mul, map_natCast, natAbs_sq_cast]`.

Simplify using `only [map_mul, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : g y - y ∈ Λ`. Rewrite using `[hsum]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hCm i)`. Establish `e : g y = y + (g y - y)` using `by abel`. Rewrite using `[e]`. Conclude with `Λ.add_mem hy hmem`.
-/
theorem lat_pres (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E, IntDiv c (G - 1) →
      ∀ g : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ y, X.crd (g y) = G *ᵥ X.crd y) → ∀ y ∈ Λ, g y ∈ Λ := by
  obtain ⟨d, hd0, hd⟩ := Formalism.HermitianLatticesTheory.majLattice_exists_d X.bas Λ hΛ.fg
  have hc : ∀ i, ∃ c : ℤ, c ≠ 0 ∧ c • X.bas i ∈ Λ := fun i =>
    Formalism.HermitianLatticesTheory.majLattice_exists_c Λ hΛ.span_eq_top (X.bas i)
  choose c hc0 hcm using hc
  set C : ℤ := ∏ i, c i with hC
  have hCm : ∀ i, (C * C) • X.bas i ∈ Λ := by
    intro i
    have e : C = (∏ j ∈ Finset.univ.erase i, c j) * c i := by
      rw [hC, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    have h1 : C • X.bas i ∈ Λ := by
      rw [e, mul_smul]
      exact zsmul_mem (hcm i) _
    rw [mul_smul]
    exact zsmul_mem h1 _
  have hC0 : C ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hc0 i
  refine ⟨d.natAbs ^ 2 * C.natAbs ^ 2, ?_, ?_⟩
  · have h1 : 0 < d.natAbs := Int.natAbs_pos.2 hd0
    have h2 : 0 < C.natAbs := Int.natAbs_pos.2 hC0
    have := Nat.mul_pos (pow_pos h1 2) (pow_pos h2 2)
    omega
  rintro G ⟨A, hA, hGA⟩ g hg y hy
  set v := A *ᵥ X.crd y with hv
  have hw : X.crd (g y - y) = ((d.natAbs ^ 2 * C.natAbs ^ 2 : ℕ) : X.B.I.E) • v := by
    rw [crd_sub_lat, hg, ← Matrix.one_mulVec (X.crd y), Matrix.mulVec_mulVec, Matrix.mul_one,
      ← Matrix.sub_mulVec, hGA, Matrix.smul_mulVec]
  have hvi : ∀ i, IsIntegral ℤ (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i) := by
    intro i
    rw [hv, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine IsIntegral.sum _ fun j _ => ?_
    have e : ((d.natAbs ^ 2 : ℕ) : X.B.I.E) * (A i j * X.crd y j) =
        A i j * X.ιE.symm ((d : D.host.E) * ((d : D.host.E) * X.bas.repr y j)) := by
      rw [natAbs_sq_cast]
      simp only [HidaSetting.crd, crdOf, map_mul, map_intCast]
      ring
    rw [e]
    exact (hA i j).mul (isInt_symm X ((isInt_intCast d).mul (hd y hy j)))
  choose r hr using fun i => (⟨⟨X.ιE (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i), isInt_fwd X (hvi i)⟩, rfl⟩ :
    ∃ r : 𝓞 D.host.E, (r : D.host.E) = X.ιE (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i))
  have hsum : g y - y = ∑ i, r i • ((C * C) • X.bas i) := by
    conv_lhs => rw [← X.bas.sum_repr (g y - y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repr_crd, hw, Pi.smul_apply, smul_eq_mul, ← algebraMap_smul D.host.E (r i), ← Int.cast_smul_eq_zsmul D.host.E,
      smul_smul]
    congr 1
    show _ = (r i : D.host.E) * _
    rw [hr, Nat.cast_mul, mul_assoc, mul_comm, map_mul, map_mul, map_natCast, natAbs_sq_cast]
    simp only [map_mul, map_natCast]
    push_cast
    ring
  have hmem : g y - y ∈ Λ := by
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hCm i)
  have e : g y = y + (g y - y) := by abel
  rw [e]
  exact Λ.add_mem hy hmem

/- English proof (translation)
Establish `hint : ∀ k : ℕ, IsIntegral ℤ ((k : X.B.I.E))` using `fun k => by`. Simplify using `using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ X.B.I.E (k : ℤ)))`. Take `⟨d1, hd1, A, hA, hAe⟩` from `exists_den (fun x => Formalism.L2.SG.Pf.nt_int_mul_of X.B.I x) P`. Take `⟨d2, hd2, B, hB, hBe⟩` from `exists_den (fun x => Formalism.L2.SG.Pf.nt_int_mul_of X.B.I x) Q`. Use `⟨d1 * d2, Nat.mul_pos hd1 hd2, ⟨(d2 : X.B.I.E) • A, fun i j => ?_, ?_⟩, ⟨(d1 : X.B.I.E) • B, fun i j => ?_, ?_⟩⟩` and prove the remaining obligations.

Simplify `(hint d2).mul (hA i j)` using `[Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[Nat.cast_mul, mul_comm, mul_smul, hAe]`. Simplify using the standard rewrite rules. Simplify `(hint d1).mul (hB i j)` using `[Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[Nat.cast_mul, mul_smul, hBe]`.

Simplify using the standard rewrite rules.
-/
theorem lat_den_two {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (P : Matrix α β X.B.I.E) (Q : Matrix γ δ X.B.I.E) :
    ∃ m : ℕ, 0 < m ∧ IntDiv 1 ((m : X.B.I.E) • P) ∧ IntDiv 1 ((m : X.B.I.E) • Q) := by
  have hint : ∀ k : ℕ, IsIntegral ℤ ((k : X.B.I.E)) := fun k => by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ X.B.I.E (k : ℤ)))
  obtain ⟨d1, hd1, A, hA, hAe⟩ := exists_den (fun x => Formalism.L2.SG.Pf.nt_int_mul_of X.B.I x) P
  obtain ⟨d2, hd2, B, hB, hBe⟩ := exists_den (fun x => Formalism.L2.SG.Pf.nt_int_mul_of X.B.I x) Q
  refine ⟨d1 * d2, Nat.mul_pos hd1 hd2, ⟨(d2 : X.B.I.E) • A, fun i j => ?_, ?_⟩,
    ⟨(d1 : X.B.I.E) • B, fun i j => ?_, ?_⟩⟩
  · simpa [Matrix.smul_apply, smul_eq_mul] using (hint d2).mul (hA i j)
  · rw [Nat.cast_mul, mul_comm, mul_smul, hAe]
    simp
  · simpa [Matrix.smul_apply, smul_eq_mul] using (hint d1).mul (hB i j)
  · rw [Nat.cast_mul, mul_smul, hBe]
    simp

/- English proof (translation)
Use `show Bm X * cay (N0 D) Z * Bm' X - 1 = Bm X * (cay (N0 D) Z - 1) * Bm' X`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Bm_mul_Bm']`.
-/
theorem lat_gE_sub_one (Z : Matrix (Kap X) (Kap X) X.B.I.E) :
    Formalism.L2.SG.Pf.UnipB.gE X Z - 1 = Bm X * (cay (N0 D) Z - 1) * Bm' X := by
  show Bm X * cay (N0 D) Z * Bm' X - 1 = Bm X * (cay (N0 D) Z - 1) * Bm' X
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Bm_mul_Bm']

/- English proof (translation)
Substitute `hZ` using the available equality. Establish `hh : (⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A) = ((c * mB ^ 2 : ℕ) : X.B.I.E) • A`. Rewrite using `[smul_smul]`. Use `congr 1`. Rewrite using `[show ((2 * c * mB ^ 2 : ℕ) : X.B.I.E) = 2 * ((c * mB ^ 2 : ℕ) : X.B.I.E) by push_cast; ring, ← mul_assoc, invOf_mul_self, one_mul]`.

Establish `hAi : IntDiv 1 A` using `⟨A, hA, by simp⟩`. Establish `hhalf : IntDiv 1 ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))`. Rewrite using `[hh]`. Use `⟨((c * mB ^ 2 : ℕ) : X.B.I.E) • A, fun i j => ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`.

Conclude with `(isInt_natCast _).mul (hA i j)`. Establish `hgeo : IntDiv 1 (geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A)))`. Unfold `geo`. Use `intDiv_sum fun j _ => ?_` and prove the remaining obligations. Use `intDiv_pow hhalf j` as an intermediate fact.

Rewrite `this` using `[one_pow]`. Then use the resulting hypothesis. Establish `hP` using `intDiv_mul (intDiv_mul hB (intDiv_mul hAi hgeo)) hB'`. Rewrite `hP` using `[show (1 * (1 * 1) * 1 : ℕ) = 1 by norm_num]`. Take `⟨W, hW, hWe⟩` from `hP`. Use `⟨W, hW, ?_⟩` and prove the remaining obligations.

Rewrite using `[lat_gE_sub_one]`. Unfold `cay`. Rewrite using `[add_sub_cancel_left]`. Establish `e : Bm X * ((((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A) * geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))) * Bm' X = ((2 * c : ℕ) : X.B.I.E) • (((mB : X.B.I.E) • Bm X) * (A * geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))) * ((mB : X.B.I.E) • …`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hWe, Nat.cast_one, one_smul]`.
-/
theorem lat_gE_intDiv (mB : ℕ) (hB : IntDiv 1 ((mB : X.B.I.E) • Bm X)) (hB' : IntDiv 1 ((mB : X.B.I.E) • Bm' X))
    (c : ℕ) (A : Matrix (Kap X) (Kap X) X.B.I.E) (hA : ∀ i j, IsIntegral ℤ (A i j))
    (Z : Matrix (Kap X) (Kap X) X.B.I.E) (hZ : Z = ((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A) :
    IntDiv (2 * c) (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) := by
  subst hZ
  have hh : (⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A) = ((c * mB ^ 2 : ℕ) : X.B.I.E) • A := by
    rw [smul_smul]
    congr 1
    rw [show ((2 * c * mB ^ 2 : ℕ) : X.B.I.E) = 2 * ((c * mB ^ 2 : ℕ) : X.B.I.E) by push_cast; ring,
      ← mul_assoc, invOf_mul_self, one_mul]
  have hAi : IntDiv 1 A := ⟨A, hA, by simp⟩
  have hhalf : IntDiv 1 ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A)) := by
    rw [hh]
    refine ⟨((c * mB ^ 2 : ℕ) : X.B.I.E) • A, fun i j => ?_, by simp⟩
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (isInt_natCast _).mul (hA i j)
  have hgeo : IntDiv 1 (geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))) := by
    unfold geo
    refine intDiv_sum fun j _ => ?_
    have := intDiv_pow hhalf j
    rwa [one_pow] at this
  have hP := intDiv_mul (intDiv_mul hB (intDiv_mul hAi hgeo)) hB'
  rw [show (1 * (1 * 1) * 1 : ℕ) = 1 by norm_num] at hP
  obtain ⟨W, hW, hWe⟩ := hP
  refine ⟨W, hW, ?_⟩
  rw [lat_gE_sub_one]
  unfold cay
  rw [add_sub_cancel_left]
  have e : Bm X * ((((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A) *
      geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))) * Bm' X =
      ((2 * c : ℕ) : X.B.I.E) • (((mB : X.B.I.E) • Bm X) *
        (A * geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))) * ((mB : X.B.I.E) • Bm' X)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [e, hWe, Nat.cast_one, one_smul]

end Formalism.L2.SG.Pf.RCoc

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Pf.RCoc Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

/- English proof (translation)
Introduce `D X Λ hΛ`. Take `⟨c, hc, H⟩` from `lat_pres X Λ hΛ`. Take `⟨mB, hmB, hB, hB'⟩` from `lat_den_two X (Bm X) (Bm' X)`. Use `⟨2 * c * mB ^ 2, Nat.mul_pos (Nat.mul_pos two_pos hc) (pow_pos hmB 2), fun Z n hZ hA hn => ?_⟩` and prove the remaining obligations. Take `⟨A, hA⟩` from `hA`.

Establish `hAi : ∀ i j, IsIntegral ℤ ((A.map (fun a => (a : X.B.I.E))) i j)` using `fun i j => (A i j).isIntegral_coe`. Establish `h1 : IntDiv c (Formalism.L2.SG.Pf.UnipB.gE X Z - 1)`. Use `lat_gE_intDiv X mB hB hB' c _ hAi Z hA` as an intermediate fact. Conclude with `intDiv_dvd (d := 2) (by rwa [mul_comm c 2])`. Establish `h2 : IntDiv c (Formalism.L2.SG.Pf.UnipB.gE X (-Z) - 1)`.

Establish `hneg : -Z = ((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • (-(A.map (fun a => (a : X.B.I.E))))`. Rewrite using `[hA, smul_neg]`. Use `lat_gE_intDiv X mB hB hB' c _ (fun i j => (hAi i j).neg) (-Z) hneg` as an intermediate fact. Conclude with `intDiv_dvd (d := 2) (by rwa [mul_comm c 2])`. Establish `hinv : Formalism.L2.SG.Pf.UnipB.gE X (-Z) * Formalism.L2.SG.Pf.UnipB.gE X Z = 1` using `gE_mul X le_rfl hZ`.

Establish `hn' : ∀ y, X.crd (n.symm y) = Formalism.L2.SG.Pf.UnipB.gE X (-Z) *ᵥ X.crd y`. Introduce `y`. Use `conv_rhs => rw [← n.apply_symm_apply y, hn, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Rewrite using `[Formalism.L2.SG.Pf.gmap_eq_iff]`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `H _ h2 n.symm.toLinearMap hn' (n x) hx` as an intermediate fact. Simplify using `using this`. Introduce `hx`.

Conclude with `H _ h1 n.toLinearMap hn x hx`.
-/
theorem memLatOf_holds : MemLatOf := by
  intro D X Λ hΛ
  obtain ⟨c, hc, H⟩ := lat_pres X Λ hΛ
  obtain ⟨mB, hmB, hB, hB'⟩ := lat_den_two X (Bm X) (Bm' X)
  refine ⟨2 * c * mB ^ 2, Nat.mul_pos (Nat.mul_pos two_pos hc) (pow_pos hmB 2), fun Z n hZ hA hn => ?_⟩
  obtain ⟨A, hA⟩ := hA
  have hAi : ∀ i j, IsIntegral ℤ ((A.map (fun a => (a : X.B.I.E))) i j) := fun i j => (A i j).isIntegral_coe
  have h1 : IntDiv c (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) := by
    have := lat_gE_intDiv X mB hB hB' c _ hAi Z hA
    exact intDiv_dvd (d := 2) (by rwa [mul_comm c 2])
  have h2 : IntDiv c (Formalism.L2.SG.Pf.UnipB.gE X (-Z) - 1) := by
    have hneg : -Z = ((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • (-(A.map (fun a => (a : X.B.I.E)))) := by
      rw [hA, smul_neg]
    have := lat_gE_intDiv X mB hB hB' c _ (fun i j => (hAi i j).neg) (-Z) hneg
    exact intDiv_dvd (d := 2) (by rwa [mul_comm c 2])
  have hinv : Formalism.L2.SG.Pf.UnipB.gE X (-Z) * Formalism.L2.SG.Pf.UnipB.gE X Z = 1 := gE_mul X le_rfl hZ
  have hn' : ∀ y, X.crd (n.symm y) = Formalism.L2.SG.Pf.UnipB.gE X (-Z) *ᵥ X.crd y := by
    intro y
    conv_rhs => rw [← n.apply_symm_apply y, hn, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [Formalism.L2.SG.Pf.gmap_eq_iff]
  intro x
  constructor
  · intro hx
    have := H _ h2 n.symm.toLinearMap hn' (n x) hx
    simpa using this
  · intro hx
    exact H _ h1 n.toLinearMap hn x hx

end Formalism.L2.SG.TermOp.Vanish
