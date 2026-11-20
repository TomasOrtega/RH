import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.StatementsMean
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PPeriodLatticeCM
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField NumberField.InfinitePlace GroundTheory.Global GroundTheory.Global.Elliptic Module
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

omit [Algebra.IsQuadraticExtension ℚ K] in

/- English proof (translation)
Use extensionality with `z`. Rewrite using `[mem_idealLattice, scaleLattice, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨t, ht, rfl⟩` from `FractionalIdeal.mem_singleton_mul.1 hy`.

Conclude with `⟨σ t, map_mem_idealLattice σ ht, by simp [map_mul]⟩`. Introduce and unpack `⟨u, hu, rfl⟩`. Take `⟨t, ht, rfl⟩` from `(mem_idealLattice σ).1 hu`. Conclude with `⟨x * t, FractionalIdeal.mem_singleton_mul.2 ⟨t, ht, rfl⟩, by simp [map_mul]⟩`.
-/
theorem idealLattice_spanSingleton_mul_eq (σ : K →+* ℂ) (x : K) (J : FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice σ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J) =
      scaleLattice (σ x) (idealLattice σ J) := by
  ext z
  rw [mem_idealLattice, scaleLattice, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, ht, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hy
    exact ⟨σ t, map_mem_idealLattice σ ht, by simp [map_mul]⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_idealLattice σ).1 hu
    exact ⟨x * t, FractionalIdeal.mem_singleton_mul.2 ⟨t, ht, rfl⟩, by simp [map_mul]⟩

/- English proof (translation)
Simplify using `only [scaleLattice]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.mul_le]`. Introduce `m hm n hn`. Take `⟨a, ha, rfl⟩` from `Submodule.mem_map.1 hm`.

Use `Submodule.mem_map.2 ⟨a * n, Submodule.mul_mem_mul ha hn, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.mulLeft_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Submodule.map_le_iff_le_comap, Submodule.mul_le]`. Introduce `a ha n hn`.

Rewrite using `[Submodule.mem_comap, LinearMap.mulLeft_apply, ← mul_assoc]`. Conclude with `Submodule.mul_mem_mul (Submodule.mem_map.2 ⟨a, ha, rfl⟩) hn`.
-/
theorem scaleLattice_mul (c : ℂ) (A B : Submodule ℤ ℂ) :
    scaleLattice c A * B = scaleLattice c (A * B) := by
  simp only [scaleLattice]
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hm
    refine Submodule.mem_map.2 ⟨a * n, Submodule.mul_mem_mul ha hn, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    ring
  · rw [Submodule.map_le_iff_le_comap, Submodule.mul_le]
    intro a ha n hn
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, ← mul_assoc]
    exact Submodule.mul_mem_mul (Submodule.mem_map.2 ⟨a, ha, rfl⟩) hn

omit [Algebra.IsQuadraticExtension ℚ K] in

/- English proof (translation)
Take `⟨a, I, -, hI⟩` from `FractionalIdeal.exists_eq_spanSingleton_mul (((𝔟⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) : FractionalIdeal (𝓞 K)⁰ K)`. Establish `hI0 : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0`. Introduce `h`. Rewrite `hI` using `[h, mul_zero]`. Conclude with `Units.ne_zero _ hI`.

Establish `hImem : I ∈ (Ideal (𝓞 K))⁰` using `mem_nonZeroDivisors_of_ne_zero fun h ↦ hI0 (by rw [h]; simp)`. Use `⟨algebraMap (𝓞 K) K a, ⟨I, hImem⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0]`. Establish `h1 : (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = ((((𝔟⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) : FractionalIdeal (𝓞 K)⁰ K))⁻¹`. Rewrite using `[Units.val_inv_eq_inv_val, inv_inv]`.

Rewrite using `[h1, hI, mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]`.
-/
theorem exists_eq_spanSingleton_mul_inv (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (x : K) (𝔞 : (Ideal (𝓞 K))⁰), (𝔟 : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * ↑(FractionalIdeal.mk0 K 𝔞)⁻¹ := by
  obtain ⟨a, I, -, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul
    (((𝔟⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) : FractionalIdeal (𝓞 K)⁰ K)
  have hI0 : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hI
    exact Units.ne_zero _ hI
  have hImem : I ∈ (Ideal (𝓞 K))⁰ :=
    mem_nonZeroDivisors_of_ne_zero fun h ↦ hI0 (by rw [h]; simp)
  refine ⟨algebraMap (𝓞 K) K a, ⟨I, hImem⟩, ?_⟩
  rw [Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0]
  have h1 : (𝔟 : FractionalIdeal (𝓞 K)⁰ K) =
      ((((𝔟⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
    rw [Units.val_inv_eq_inv_val, inv_inv]
  rw [h1, hI, mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]

/- English proof (translation)
Establish `hΔ : latticeDiscr L.lattice ≠ 0`. Rewrite using `[latticeDiscr_lattice]`. Conclude with `discr_ne_zero L`. Establish `hA : 0 < latticeArea L.lattice` using `ZLattice.covolume_pos L.lattice MeasureTheory.volume`. Establish `hN : (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors 𝔞)`.

Establish `hD : latticeDiscr (idealLattice σ ↑(FractionalIdeal.mk0 K 𝔞)⁻¹ * L.lattice) = discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞) * latticeDiscr L.lattice`. Rewrite using `[discrRatio, div_mul_cancel₀ _ hΔ]`. Unfold `logPeriod`. Rewrite using `[hArea σ L hL 𝔞, hD, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 hΔ), div_right_comm, Real.log_div (div_pos hA Real.pi_pos).ne' hN]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logPeriod_idealInv_mul {S : PrimeDiscriminant K} (hArea : IdealInvArea.Statement S)
    (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (𝔞 : (Ideal (𝓞 K))⁰)
    (hw : discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞) ≠ 0) :
    logPeriod (idealLattice σ ↑(FractionalIdeal.mk0 K 𝔞)⁻¹ * L.lattice) =
      logPeriod L.lattice - Real.log (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) +
        (1 / 6) * Real.log ‖discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞)‖ := by
  have hΔ : latticeDiscr L.lattice ≠ 0 := by
    rw [latticeDiscr_lattice]
    exact discr_ne_zero L
  have hA : 0 < latticeArea L.lattice := ZLattice.covolume_pos L.lattice MeasureTheory.volume
  have hN : (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors 𝔞)
  have hD : latticeDiscr (idealLattice σ ↑(FractionalIdeal.mk0 K 𝔞)⁻¹ * L.lattice) =
      discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞) * latticeDiscr L.lattice := by
    rw [discrRatio, div_mul_cancel₀ _ hΔ]
  unfold logPeriod
  rw [hArea σ L hL 𝔞, hD, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 hΔ),
    div_right_comm, Real.log_div (div_pos hA Real.pi_pos).ne' hN]
  ring

/- English proof (translation)
Establish `hK : finrank ℚ K = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two ℚ K`. Take `⟨k', _, _, _, w, hw⟩` from `hConj (FractionalIdeal.mk0 K 𝔞)`. Set `_ : Algebra K k'` to `((algebraMap F.k k').comp (algebraMap K F.k)).toAlgebra`. Establish `: IsScalarTower K F.k k'` using `IsScalarTower.of_algebraMap_eq fun _ ↦ rfl`. Take `⟨s₀⟩ : Nonempty (k' →+* ℂ)` from `inferInstance`.

Take `⟨L₀, hL₀, hE₀⟩` from `hCM (s₀.comp (algebraMap F.k k'))`. Take `⟨w₀, hw₀, hspan⟩` from `(hIdeal (F.restrict (s₀.comp (algebraMap F.k k'))) L₀ hE₀ 𝔞).2 k' (algebraMap K k') s₀ (RingHom.ext fun _ ↦ rfl) ⟨w, by rw [hw s₀, hL₀]⟩`. Establish `hw₀w : (w₀ : k') = w` using `s₀.injective (by rw [hw₀, hw s₀, hL₀])`. Establish `hN : Ideal.absNorm (𝔞 : Ideal (𝓞 K)) ≠ 0` using `Ideal.absNorm_ne_zero_of_nonZeroDivisors 𝔞`. Establish `hmap : Ideal.map (RingOfIntegers.mapRingHom (algebraMap K k')) (𝔞 : Ideal (𝓞 K)) = Ideal.map (algebraMap (𝓞 K) (𝓞 k')) (𝔞 : Ideal (𝓞 K))` using `rfl`.

Establish `hnormI : Ideal.absNorm (Ideal.span {w₀}) = Ideal.absNorm (𝔞 : Ideal (𝓞 K)) ^ (12 * finrank K k')`. Rewrite using `[hspan, map_pow, hmap, Ideal.absNorm_algebraMap, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 k') k', ← pow_mul, mul_comm]`. Establish `hnormQ : |Algebra.norm ℚ w| = (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℚ) ^ (12 * finrank K k')`. Rewrite using `[← hw₀w, ← Algebra.coe_norm_int, ← Int.cast_abs, Int.abs_eq_natAbs, ← Ideal.absNorm_span_singleton, hnormI]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hwne : w ≠ 0`. Introduce and unpack `rfl`. Rewrite `hnormQ` using `[Algebra.norm_zero, abs_zero]`. Conclude with `pow_ne_zero _ (Nat.cast_ne_zero.mpr hN) hnormQ.symm`.

Establish `hfib : ∀ s : F.k →+* ℂ, s (Algebra.norm F.k w) = discrRatio (F.restrict s) (F.periodLattice s) (FractionalIdeal.mk0 K 𝔞) ^ finrank F.k k'`. Introduce `s`. Set `_ : Algebra F.k ℂ` to `s.toAlgebra`. Establish `h` using `Algebra.norm_eq_prod_embeddings F.k ℂ w`. Establish `hτ : ∀ τ : k' →ₐ[F.k] ℂ, τ w = discrRatio (F.restrict s) (F.periodLattice s) (FractionalIdeal.mk0 K 𝔞)`.

Introduce `τ`. Establish `hcomp : (τ : k' →+* ℂ).comp (algebraMap F.k k') = s` using `τ.comp_algebraMap`. Use `hw (τ : k' →+* ℂ)` as an intermediate fact. Rewrite `this` using `[hcomp]`. Conclude with `this`.

Use `show algebraMap F.k ℂ (Algebra.norm F.k w) = _`. Rewrite using `[h, Finset.prod_congr rfl (fun τ _ ↦ hτ τ), Finset.prod_const, Finset.card_univ, AlgHom.card]`. Establish `hprod : ∀ y : F.k, ∏ s : F.k →+* ℂ, ‖s y‖ = |(Algebra.norm ℚ y : ℝ)|`. Introduce `y`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom F.k ℂ) (fun f ↦ ‖f y‖) (fun φ ↦ ‖φ y‖) (fun _ ↦ by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ y]`.

Simplify using `[Complex.norm_ratCast]`. Establish `hy : Algebra.norm ℚ (Algebra.norm F.k w) = Algebra.norm ℚ w` using `Algebra.norm_norm`. Establish `hyne : Algebra.norm F.k w ≠ 0` using `Algebra.norm_ne_zero_iff.2 hwne`. Establish `hsum : (finrank F.k k' : ℝ) * ∑ s : F.k →+* ℂ, Real.log ‖discrRatio (F.restrict s) (F.periodLattice s) (FractionalIdeal.mk0 K 𝔞)‖ = Real.log |(Algebra.norm ℚ w : ℝ)|`. Rewrite using `[← hy, ← hprod, Real.log_prod (fun s _ ↦ norm_ne_zero_iff.2 ((map_ne_zero s).2 hyne)), Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun s _ ↦ ?_` and prove the remaining obligations. Rewrite using `[hfib s, norm_pow, Real.log_pow]`. Establish `hlogN : Real.log |(Algebra.norm ℚ w : ℝ)| = (12 * finrank K k' : ℕ) * Real.log (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ)`. Rewrite using `[← Rat.cast_abs, hnormQ]`. Use `push_cast`.

Rewrite using `[Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hdeg : finrank F.k k' * finrank ℚ F.k = 2 * finrank K k'`. Rewrite using `[mul_comm, Module.finrank_mul_finrank ℚ F.k k', ← hK, Module.finrank_mul_finrank ℚ K k']`.

Establish `hdeg' : (finrank F.k k' : ℝ) * finrank ℚ F.k = 2 * finrank K k'` using `by exact_mod_cast hdeg`. Establish `hpos : (0 : ℝ) < finrank F.k k'` using `by exact_mod_cast Module.finrank_pos`. Use `⟨mul_left_cancel₀ hpos.ne' ?_, fun s h0 ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[hsum, hlogN]`. Use `push_cast`.

Take the linear combination `(-6 * Real.log (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ)) * hdeg'`. Use `hfib s` as an intermediate fact. Rewrite `this` using `[h0, zero_pow Module.finrank_pos.ne']`. Conclude with `hyne (s.injective (this.trans (map_zero s).symm))`.
-/
theorem sum_log_norm_discrRatio {S : PrimeDiscriminant K} {F : CMFamily K}
    (hConj : WConjugate.Statement S F) (hIdeal : WIdeal.Statement S)
    (hCM : PeriodLatticeCM.Statement S F) (𝔞 : (Ideal (𝓞 K))⁰) :
    (∑ s : F.k →+* ℂ, Real.log ‖discrRatio (F.restrict s) (F.periodLattice s)
        (FractionalIdeal.mk0 K 𝔞)‖) =
      6 * finrank ℚ F.k * Real.log (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) ∧
    ∀ s : F.k →+* ℂ, discrRatio (F.restrict s) (F.periodLattice s) (FractionalIdeal.mk0 K 𝔞) ≠ 0 := by
  classical
  have hK : finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  obtain ⟨k', _, _, _, w, hw⟩ := hConj (FractionalIdeal.mk0 K 𝔞)
  let _ : Algebra K k' := ((algebraMap F.k k').comp (algebraMap K F.k)).toAlgebra
  have : IsScalarTower K F.k k' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

  obtain ⟨s₀⟩ : Nonempty (k' →+* ℂ) := inferInstance
  obtain ⟨L₀, hL₀, hE₀⟩ := hCM (s₀.comp (algebraMap F.k k'))
  obtain ⟨w₀, hw₀, hspan⟩ := (hIdeal (F.restrict (s₀.comp (algebraMap F.k k'))) L₀ hE₀ 𝔞).2 k'
    (algebraMap K k') s₀ (RingHom.ext fun _ ↦ rfl) ⟨w, by rw [hw s₀, hL₀]⟩
  have hw₀w : (w₀ : k') = w := s₀.injective (by rw [hw₀, hw s₀, hL₀])
  have hN : Ideal.absNorm (𝔞 : Ideal (𝓞 K)) ≠ 0 := Ideal.absNorm_ne_zero_of_nonZeroDivisors 𝔞
  have hmap : Ideal.map (RingOfIntegers.mapRingHom (algebraMap K k')) (𝔞 : Ideal (𝓞 K)) =
      Ideal.map (algebraMap (𝓞 K) (𝓞 k')) (𝔞 : Ideal (𝓞 K)) := rfl
  have hnormI : Ideal.absNorm (Ideal.span {w₀}) =
      Ideal.absNorm (𝔞 : Ideal (𝓞 K)) ^ (12 * finrank K k') := by
    rw [hspan, map_pow, hmap, Ideal.absNorm_algebraMap,
      IsFractionRing.finrank_eq (𝓞 K) K (𝓞 k') k', ← pow_mul, mul_comm]
  have hnormQ : |Algebra.norm ℚ w| =
      (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℚ) ^ (12 * finrank K k') := by
    rw [← hw₀w, ← Algebra.coe_norm_int, ← Int.cast_abs, Int.abs_eq_natAbs,
      ← Ideal.absNorm_span_singleton, hnormI]
    push_cast
    rfl
  have hwne : w ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero, abs_zero] at hnormQ
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hN) hnormQ.symm

  have hfib : ∀ s : F.k →+* ℂ, s (Algebra.norm F.k w) =
      discrRatio (F.restrict s) (F.periodLattice s) (FractionalIdeal.mk0 K 𝔞) ^ finrank F.k k' := by
    intro s
    let _ : Algebra F.k ℂ := s.toAlgebra
    have h := Algebra.norm_eq_prod_embeddings F.k ℂ w
    have hτ : ∀ τ : k' →ₐ[F.k] ℂ,
        τ w = discrRatio (F.restrict s) (F.periodLattice s) (FractionalIdeal.mk0 K 𝔞) := by
      intro τ
      have hcomp : (τ : k' →+* ℂ).comp (algebraMap F.k k') = s := τ.comp_algebraMap
      have := hw (τ : k' →+* ℂ)
      rw [hcomp] at this
      exact this
    show algebraMap F.k ℂ (Algebra.norm F.k w) = _
    rw [h, Finset.prod_congr rfl (fun τ _ ↦ hτ τ), Finset.prod_const, Finset.card_univ,
      AlgHom.card]

  have hprod : ∀ y : F.k, ∏ s : F.k →+* ℂ, ‖s y‖ = |(Algebra.norm ℚ y : ℝ)| := by
    intro y
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom F.k ℂ) (fun f ↦ ‖f y‖) (fun φ ↦ ‖φ y‖)
      (fun _ ↦ by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod,
      ← Algebra.norm_eq_prod_embeddings ℚ ℂ y]
    simp [Complex.norm_ratCast]
  have hy : Algebra.norm ℚ (Algebra.norm F.k w) = Algebra.norm ℚ w := Algebra.norm_norm
  have hyne : Algebra.norm F.k w ≠ 0 := Algebra.norm_ne_zero_iff.2 hwne
  have hsum : (finrank F.k k' : ℝ) * ∑ s : F.k →+* ℂ, Real.log ‖discrRatio (F.restrict s)
      (F.periodLattice s) (FractionalIdeal.mk0 K 𝔞)‖ = Real.log |(Algebra.norm ℚ w : ℝ)| := by
    rw [← hy, ← hprod, Real.log_prod (fun s _ ↦ norm_ne_zero_iff.2 ((map_ne_zero s).2 hyne)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [hfib s, norm_pow, Real.log_pow]
  have hlogN : Real.log |(Algebra.norm ℚ w : ℝ)| =
      (12 * finrank K k' : ℕ) * Real.log (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) := by
    rw [← Rat.cast_abs, hnormQ]
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have hdeg : finrank F.k k' * finrank ℚ F.k = 2 * finrank K k' := by
    rw [mul_comm, Module.finrank_mul_finrank ℚ F.k k', ← hK, Module.finrank_mul_finrank ℚ K k']
  have hdeg' : (finrank F.k k' : ℝ) * finrank ℚ F.k = 2 * finrank K k' := by exact_mod_cast hdeg
  have hpos : (0 : ℝ) < finrank F.k k' := by exact_mod_cast Module.finrank_pos
  refine ⟨mul_left_cancel₀ hpos.ne' ?_, fun s h0 ↦ ?_⟩
  · rw [hsum, hlogN]
    push_cast
    linear_combination (-6 * Real.log (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ)) * hdeg'
  · have := hfib s
    rw [h0, zero_pow Module.finrank_pos.ne'] at this
    exact hyne (s.injective (this.trans (map_zero s).symm))

/- English proof (translation)
Use `S.isTotallyComplex` as an intermediate fact. Establish `hCM` using `PeriodLatticeCM.proof S F`. Establish `hK : finrank ℚ K = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two ℚ K`. Introduce `𝔟`. Take `⟨x, 𝔞, h𝔟⟩` from `exists_eq_spanSingleton_mul_inv 𝔟`.

Take `⟨hsum, hne⟩` from `sum_log_norm_discrRatio hConj hIdeal hCM 𝔞`. Establish `hx : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `h𝔟` using `[FractionalIdeal.spanSingleton_zero, zero_mul]`. Conclude with `Units.ne_zero 𝔟 h𝔟`.

Establish `hs : ∀ s : F.k →+* ℂ, logPeriod (idealLattice (F.restrict s) 𝔟 * F.periodLattice s) = logPeriod (F.periodLattice s) - Real.log (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) + (1 / 6) * Real.log ‖discrRatio (F.restrict s) (F.periodLattice s) (FractionalIdeal.mk0 K 𝔞)‖`. Introduce `s`. Take `⟨L, hL, hE⟩` from `hCM s`. Take `⟨L', hL', -⟩` from `exists_lattice_mul (F.restrict s) hK L hE (FractionalIdeal.mk0 K 𝔞)`. Establish `hne'` using `hne s`.

Rewrite `hne'`, the goal using `[hL]`. Rewrite using `[h𝔟, idealLattice_spanSingleton_mul_eq, scaleLattice_mul, ← hL', hScale L' _ ((map_ne_zero _).2 hx), hL']`. Conclude with `logPeriod_idealInv_mul hArea (F.restrict s) L hE 𝔞 hne'`. Unfold `embMean`. Rewrite using `[Finset.sum_congr rfl fun s _ ↦ hs s, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem MeanOverEmbeddings.proof {S : PrimeDiscriminant K} {F : CMFamily K}
    (hScale : PhScale.Statement) (hConj : WConjugate.Statement S F) (hIdeal : WIdeal.Statement S)
    (hArea : IdealInvArea.Statement S) :
    MeanOverEmbeddings.Statement S F := by
  have := S.isTotallyComplex
  have hCM := PeriodLatticeCM.proof S F
  have hK : finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  intro 𝔟
  obtain ⟨x, 𝔞, h𝔟⟩ := exists_eq_spanSingleton_mul_inv 𝔟
  obtain ⟨hsum, hne⟩ := sum_log_norm_discrRatio hConj hIdeal hCM 𝔞
  have hx : x ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero, zero_mul] at h𝔟
    exact Units.ne_zero 𝔟 h𝔟
  have hs : ∀ s : F.k →+* ℂ,
      logPeriod (idealLattice (F.restrict s) 𝔟 * F.periodLattice s) =
        logPeriod (F.periodLattice s) - Real.log (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) +
          (1 / 6) * Real.log ‖discrRatio (F.restrict s) (F.periodLattice s)
            (FractionalIdeal.mk0 K 𝔞)‖ := by
    intro s
    obtain ⟨L, hL, hE⟩ := hCM s
    obtain ⟨L', hL', -⟩ := exists_lattice_mul (F.restrict s) hK L hE (FractionalIdeal.mk0 K 𝔞)
    have hne' := hne s
    rw [hL] at hne' ⊢
    rw [h𝔟, idealLattice_spanSingleton_mul_eq, scaleLattice_mul, ← hL',
      hScale L' _ ((map_ne_zero _).2 hx), hL']
    exact logPeriod_idealInv_mul hArea (F.restrict s) L hE 𝔞 hne'
  unfold embMean
  rw [Finset.sum_congr rfl fun s _ ↦ hs s, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul]
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
