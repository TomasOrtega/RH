import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsRank
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SectionModuleEqSpanPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Pointwise

noncomputable section

namespace SectionsRank

/- English proof (translation)
Unfold `sec`. Rewrite using `[← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow, MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp, Submodule.span_pow]`. Use `congr 3`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem sec_eq_span (o : Type*) [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}
    (x : ι → Ω) (n : ℕ) : sec o x n = Submodule.span o (Set.range x ^ n) := by
  unfold sec
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow,
    MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
    Submodule.span_pow]
  congr 3
  ext i
  simp

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C q`. Use `⟨q.den, q.pos, C q.num, ?_⟩` and prove the remaining obligations. Rewrite using `[map_C, smul_eq_C_mul, ← C_mul, Rat.den_mul_eq_num]`. Both sides reduce to the same expression.

Consider the case `add f g hf hg`. Take `⟨a, ha, p, hp⟩` from `hf`. Take `⟨b, hb, r, hr⟩` from `hg`. Use `⟨a * b, Nat.mul_pos ha hb, (b : ℤ) • p + (a : ℤ) • r, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, hp, hr, map_C, map_C]`.

Simplify using `only [smul_eq_C_mul, eq_intCast, Int.cast_natCast, Nat.cast_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X f i hf`. Take `⟨a, ha, p, hp⟩` from `hf`. Use `⟨a, ha, p * X i, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hp, map_X, smul_mul_assoc]`.
-/
theorem exists_int_multiple {ι : Type*} (f : MvPolynomial ι ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ p : MvPolynomial ι ℤ, map (Int.castRingHom ℚ) p = (N : ℚ) • f := by
  induction f using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, q.pos, C q.num, ?_⟩
    rw [map_C, smul_eq_C_mul, ← C_mul, Rat.den_mul_eq_num]
    rfl
  | add f g hf hg =>
    obtain ⟨a, ha, p, hp⟩ := hf
    obtain ⟨b, hb, r, hr⟩ := hg
    refine ⟨a * b, Nat.mul_pos ha hb, (b : ℤ) • p + (a : ℤ) • r, ?_⟩
    rw [map_add, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, hp, hr, map_C, map_C]
    simp only [smul_eq_C_mul, eq_intCast, Int.cast_natCast, Nat.cast_mul, map_mul]
    ring
  | mul_X f i hf =>
    obtain ⟨a, ha, p, hp⟩ := hf
    refine ⟨a, ha, p * X i, ?_⟩
    rw [map_mul, hp, map_X, smul_mul_assoc]

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hle : (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) ≤ RingHom.ker (aeval x : MvPolynomial J ℚ →ₐ[ℚ] Ω)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `p hp`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq]`. Express the relevant statement in the definitionally equal form `aeval x (MvPolynomial.map (algebraMap ℤ ℚ) p) = 0`. Rewrite using `[aeval_map_algebraMap]`. Conclude with `aeval_eq_zero_of_mem_coordIdeal hp`. Conclude with `hle h`.

Introduce `h`. Take `⟨N, hN, p, hp⟩` from `exists_int_multiple f`. Establish `hpn : p.IsHomogeneous n`. Use `IsHomogeneous.of_map (f := Int.castRingHom ℚ) (RingHom.injective_int _) ?_` and prove the remaining obligations. Rewrite using `[hp]`.

Conclude with `(mem_homogeneousSubmodule n _).mp (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule n f).mpr hf))`. Establish `hp0 : aeval x p = 0`. Rewrite using `[← aeval_map_algebraMap ℚ, algebraMap_int_eq, hp, map_smul, h, smul_zero]`. Establish `hmem` using `Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom ℚ)) (mem_coordIdeal_of_isHomogeneous ℤ x hpn hp0)`. Rewrite `hmem` using `[hp, smul_eq_C_mul]`.

Establish `hN' : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Use `Ideal.mul_mem_left _ (C (N : ℚ)⁻¹) hmem` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← C_mul, inv_mul_cancel₀ hN', C_1, one_mul]`. Then use the resulting hypothesis.
-/
theorem mem_map_coordIdeal_iff [Fintype J] (x : J → Ω) {n : ℕ} {f : MvPolynomial J ℚ}
    (hf : f.IsHomogeneous n) :
    f ∈ (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) ↔ aeval x f = 0 := by
  constructor
  · intro h
    have hle : (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) ≤
        RingHom.ker (aeval x : MvPolynomial J ℚ →ₐ[ℚ] Ω) := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq]
      change aeval x (MvPolynomial.map (algebraMap ℤ ℚ) p) = 0
      rw [aeval_map_algebraMap]
      exact aeval_eq_zero_of_mem_coordIdeal hp
    exact hle h
  · intro h
    obtain ⟨N, hN, p, hp⟩ := exists_int_multiple f
    have hpn : p.IsHomogeneous n := by
      refine IsHomogeneous.of_map (f := Int.castRingHom ℚ) (RingHom.injective_int _) ?_
      rw [hp]
      exact (mem_homogeneousSubmodule n _).mp
        (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule n f).mpr hf))
    have hp0 : aeval x p = 0 := by
      rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, hp, map_smul, h, smul_zero]
    have hmem := Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom ℚ))
      (mem_coordIdeal_of_isHomogeneous ℤ x hpn hp0)
    rw [hp, smul_eq_C_mul] at hmem
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have := Ideal.mul_mem_left _ (C (N : ℚ)⁻¹) hmem
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hN', C_1, one_mul] at this

/- English proof (translation)
Establish `ef : V.map f = LinearMap.range (f ∘ₗ V.subtype)`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`. Establish `eg : V.map g = LinearMap.range (g ∘ₗ V.subtype)`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`. Establish `hk : LinearMap.ker (f ∘ₗ V.subtype) = LinearMap.ker (g ∘ₗ V.subtype)`.

Use extensionality with `v`. Simplify using `using h v v.2`. Rewrite using `[ef, eg]`. Conclude with `((f ∘ₗ V.subtype).quotKerEquivRange.symm.trans ((Submodule.quotEquivOfEq _ _ hk).trans (g ∘ₗ V.subtype).quotKerEquivRange)).finrank_eq`.
-/
theorem finrank_map_eq {K M N N' : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] (V : Submodule K M)
    (f : M →ₗ[K] N) (g : M →ₗ[K] N') (h : ∀ v ∈ V, f v = 0 ↔ g v = 0) :
    Module.finrank K (V.map f) = Module.finrank K (V.map g) := by
  have ef : V.map f = LinearMap.range (f ∘ₗ V.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eg : V.map g = LinearMap.range (g ∘ₗ V.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker (f ∘ₗ V.subtype) = LinearMap.ker (g ∘ₗ V.subtype) := by
    ext v
    simpa using h v v.2
  rw [ef, eg]
  exact ((f ∘ₗ V.subtype).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (g ∘ₗ V.subtype).quotKerEquivRange)).finrank_eq

/- English proof (translation)
Establish `: Module.Finite ℤ (sec ℤ x n)` using `Module.Finite.iff_fg.mpr (sec_fg x n)`. Set `b` to `Module.Free.chooseBasis ℤ (sec ℤ x n)`. Set `v : Module.Free.ChooseBasisIndex ℤ (sec ℤ x n) → Ω` to `fun i => (b i : Ω)`. Establish `hli : LinearIndependent ℤ v` using `b.linearIndependent.map' (sec ℤ x n).subtype (Submodule.ker_subtype _)`. Establish `hliQ : LinearIndependent ℚ v` using `(LinearIndependent.iff_fractionRing ℤ ℚ).mp hli`.

Establish `hspanZ : Submodule.span ℤ (Set.range v) = sec ℤ x n`. Establish `: Set.range v = (sec ℤ x n).subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]`.

Establish `hspanQ : Submodule.span ℚ (Set.range v) = sec ℚ x n`. Rewrite using `[← Submodule.span_span_of_tower ℤ, hspanZ, sec_eq_span ℤ, sec_eq_span ℚ, Submodule.span_span_of_tower]`. Rewrite using `[Module.finrank_eq_card_chooseBasisIndex, ← hspanQ, finrank_span_eq_card hliQ]`.
-/
theorem finrank_sec_int [Fintype J] (x : J → Ω) (n : ℕ) :
    Module.finrank ℤ (sec ℤ x n) = Module.finrank ℚ (sec ℚ x n) := by
  have : Module.Finite ℤ (sec ℤ x n) := Module.Finite.iff_fg.mpr (sec_fg x n)
  let b := Module.Free.chooseBasis ℤ (sec ℤ x n)
  let v : Module.Free.ChooseBasisIndex ℤ (sec ℤ x n) → Ω := fun i => (b i : Ω)
  have hli : LinearIndependent ℤ v :=
    b.linearIndependent.map' (sec ℤ x n).subtype (Submodule.ker_subtype _)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hli
  have hspanZ : Submodule.span ℤ (Set.range v) = sec ℤ x n := by
    have : Set.range v = (sec ℤ x n).subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspanQ : Submodule.span ℚ (Set.range v) = sec ℚ x n := by
    rw [← Submodule.span_span_of_tower ℤ, hspanZ, sec_eq_span ℤ, sec_eq_span ℚ,
      Submodule.span_span_of_tower]
  rw [Module.finrank_eq_card_chooseBasisIndex, ← hspanQ, finrank_span_eq_card hliQ]

end SectionsRank

open SectionsRank in

/- English proof (translation)
Introduce `Ω _ _ κ _ x n`. Use `set q := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))`. Establish `hw : GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ) = fun _ _ => 1`. Use function extensionality and compare the values at `v u`. Simplify using `[GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]`.

Establish `hV : weightedHomogeneousSubmodule ℚ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ)) (fun _ => n) = homogeneousSubmodule (Ix κ) ℚ n`. Use extensionality with `f`. Rewrite using `[mem_weightedHomogeneousSubmodule, mem_homogeneousSubmodule, hw]`. Establish `hwt : ∀ d : Ix κ →₀ ℕ, Finsupp.weight (fun _ _ => (1 : ℕ) : Ix κ → Unit → ℕ) d = fun _ => Finsupp.weight 1 d`. Introduce `d`.

Use function extensionality and compare the values at `u`. Simplify using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Simplify using `only [IsHomogeneous, IsWeightedHomogeneous, hwt, funext_iff, forall_const]`. Establish `hg : ∀ m : Unit → ℕ, m = (fun _ => n) → GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece q m = (homogeneousSubmodule (Ix κ) ℚ n).map (Ideal.Quotient.mkₐ ℚ q).toLinearMap`. Introduce and unpack `m rfl`.

Unfold `GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece`. Rewrite using `[hV]`. Unfold `GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn`. Rewrite using `[if_pos (fun _ => Int.natCast_nonneg n), hg _ (by funext; simp), finrank_sec_int]`. Use `congr 1`.

Use `finrank_map_eq _ _ _ fun f hf => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, AlgHom.toLinearMap_apply]`. Conclude with `mem_map_coordIdeal_iff x ((mem_homogeneousSubmodule n f).mp hf)`.
-/
theorem SectionsRank.proof : SectionsRank.Statement := by
  intro Ω _ _ κ _ x n
  set q := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))
  have hw : GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ) = fun _ _ => 1 := by
    funext v u
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  have hV : weightedHomogeneousSubmodule ℚ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (GlobalTheory κ))
      (fun _ => n) = homogeneousSubmodule (Ix κ) ℚ n := by
    ext f
    rw [mem_weightedHomogeneousSubmodule, mem_homogeneousSubmodule, hw]
    have hwt : ∀ d : Ix κ →₀ ℕ,
        Finsupp.weight (fun _ _ => (1 : ℕ) : Ix κ → Unit → ℕ) d = fun _ => Finsupp.weight 1 d := by
      intro d
      funext u
      simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    simp only [IsHomogeneous, IsWeightedHomogeneous, hwt, funext_iff, forall_const]
  have hg : ∀ m : Unit → ℕ, m = (fun _ => n) →
      GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece q m =
        (homogeneousSubmodule (Ix κ) ℚ n).map (Ideal.Quotient.mkₐ ℚ q).toLinearMap := by
    rintro m rfl
    unfold GroundTheory.Heights₂.Heights.NumbersDVR.gradedPiece
    rw [hV]
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
  rw [if_pos (fun _ => Int.natCast_nonneg n), hg _ (by funext; simp), finrank_sec_int]
  congr 1
  refine finrank_map_eq _ _ _ fun f hf => ?_
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    AlgHom.toLinearMap_apply]
  exact mem_map_coordIdeal_iff x ((mem_homogeneousSubmodule n f).mp hf)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
