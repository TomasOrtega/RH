import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ hu t t' c hc`. Establish `hE : IsTotallyComplex E` using `hσ.2.1`. Establish `hdE : (discr E : ℝ) ≠ 0` using `by exact_mod_cast discr_ne_zero E`. Establish `hdF : (discr F : ℝ) ≠ 0` using `by exact_mod_cast discr_ne_zero F`. Establish `hd : |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2`.

Establish `h1` using `congrArg (Nat.cast : ℕ → ℤ) (FrameDual.natAbs_discr_sq (F := F) (E := E) hσ.2.2.1)`. Rewrite `h1` using `[Nat.cast_pow, Int.natCast_natAbs, Int.natCast_natAbs]`. Rewrite using `[sq_abs]`. Establish `h2 : ((|discr E| : ℤ) : ℝ) = ((|discr F| ^ 2 : ℤ) : ℝ)` using `by rw [h1]`. Move the coercions through the operations in `at h2`.

Rewrite using `[h2, sq_abs]`. Use `set I := dInv E t * (dInv E t')⁻¹ with hIdef`. Establish `hNI : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = (|(discr E : ℝ)|⁻¹ ^ t) * (|(discr E : ℝ)|⁻¹ ^ t')⁻¹`. Rewrite using `[hIdef, map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, FrameDual.absNorm_dInv, FrameDual.absNorm_dInv]`. Establish `hI : I ≠ 0`.

Introduce `h0`. Establish `h1 : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = 0` using `by rw [h0, map_zero, Rat.cast_zero]`. Rewrite `h1` using `[hNI]`. Establish `: |(discr E : ℝ)| ≠ 0` using `abs_ne_zero.2 hdE`. Simplify the hypotheses and the goal together.

Take `⟨L₀, hL₀, hcov⟩` from `HomCovolume.exists_idealLat E hE I hI`. Establish `hc0 : (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`. Set `f : (InfinitePlace E → ℂ) →ₗ[ℝ] (InfinitePlace E → ℂ)` to `LinearMap.pi fun w => (Algebra.lmul ℝ ℂ ((c : ℂ))⁻¹).comp (LinearMap.proj w)`. Establish `hf : ∀ z w, f z w = ((c : ℂ))⁻¹ * z w` using `fun _ _ => rfl`. Establish `hdet : LinearMap.det f = (∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2)⁻¹`.

Rewrite using `[LinearMap.det_pi, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]`. Establish `hpos : 0 < ∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2` using `Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 hc0) _`. Set `L : Submodule ℤ (InfinitePlace E → ℂ)` to `L₀.comap (f.restrictScalars ℤ)`.

Take `⟨_, _, h⟩` from `HomCovolume.HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne') (fun _ => Iff.rfl) hcov`. Establish `hL : ∀ z, z ∈ L ↔ z ∈ (ideLat I c : Set (InfinitePlace E → ℂ))`. Introduce `z`. Express the relevant statement in the definitionally equal form `f z ∈ L₀ ↔ ∃ y ∈ I, ∀ w, z w = (c : ℂ) * w.embedding y`. Rewrite using `[hL₀]`.

Use `exists_congr fun y => and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩` and prove the remaining obligations. Rewrite using `[← h w, hf, mul_inv_cancel_left₀ hc0]`. Rewrite using `[hf, h w, inv_mul_cancel_left₀ hc0]`. Use `⟨latticeDomain L, measurableSet_latticeDomain L, fun a => ?_, ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hu'⟩` from `existsUnique_add_mem_latticeDomain L a`.

Use `⟨z, ⟨(hL z).1 z.2, hz⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `l ⟨hl, hl'⟩`. Conclude with `congrArg Subtype.val (hu' ⟨l, (hL l).2 hl⟩ hl')`. Rewrite `h` using `[ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet, abs_of_pos (inv_pos.2 hpos), div_inv_eq_mul]`. Establish `hfin : volume (latticeDomain L) ≠ ⊤` using `(ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne`.

Rewrite using `[← ENNReal.ofReal_toReal hfin, h]`. Use `congr 1`. Establish `hn : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E)`. Rewrite using `[InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`. Establish `hDpos : 0 < |(discr F : ℝ)|` using `abs_pos.2 hdF`.

Establish `hr : |(discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) = |(discr F : ℝ)| ^ (1 + 2 * t') / |(discr F : ℝ)| ^ (2 * t)`. Rewrite using `[show (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) = ((1 + 2 * t' : ℕ) : ℝ) - ((2 * t : ℕ) : ℝ) by push_cast; ring, Real.rpow_sub hDpos, Real.rpow_natCast, Real.rpow_natCast]`. Rewrite using `[hNI, HomCovolume.vInv_pow E hE, hn, hd, Real.sqrt_sq hDpos.le, hr, Finset.prod_const, Finset.card_univ, Complex.norm_real, Real.norm_of_nonneg hc.le]`. Generalize the expression as in `|(discr F : ℝ)| = D at hDpos`. Generalize the expression as in `Fintype.card (InfinitePlace E) = n`.

Rewrite using `[inv_pow, inv_pow, inv_inv, ← pow_mul, ← pow_mul, ← pow_mul, pow_add, pow_one, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDom_ideLat_dInv_div : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * (dInv E t')⁻¹) c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  intro F E _ _ _ _ _ σ hσ hu t t' c hc
  have hE : IsTotallyComplex E := hσ.2.1
  have hdE : (discr E : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero E
  have hdF : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have hd : |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ℤ) (FrameDual.natAbs_discr_sq (F := F) (E := E) hσ.2.2.1)
    rw [Nat.cast_pow, Int.natCast_natAbs, Int.natCast_natAbs] at h1
    rw [sq_abs]
    have h2 : ((|discr E| : ℤ) : ℝ) = ((|discr F| ^ 2 : ℤ) : ℝ) := by rw [h1]
    push_cast at h2
    rw [h2, sq_abs]
  set I := dInv E t * (dInv E t')⁻¹ with hIdef
  have hNI : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = (|(discr E : ℝ)|⁻¹ ^ t) * (|(discr E : ℝ)|⁻¹ ^ t')⁻¹ := by
    rw [hIdef, map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, FrameDual.absNorm_dInv, FrameDual.absNorm_dInv]
  have hI : I ≠ 0 := by
    intro h0
    have h1 : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = 0 := by rw [h0, map_zero, Rat.cast_zero]
    rw [hNI] at h1
    have : |(discr E : ℝ)| ≠ 0 := abs_ne_zero.2 hdE
    simp_all
  obtain ⟨L₀, hL₀, hcov⟩ := HomCovolume.exists_idealLat E hE I hI
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let f : (InfinitePlace E → ℂ) →ₗ[ℝ] (InfinitePlace E → ℂ) :=
    LinearMap.pi fun w => (Algebra.lmul ℝ ℂ ((c : ℂ))⁻¹).comp (LinearMap.proj w)
  have hf : ∀ z w, f z w = ((c : ℂ))⁻¹ * z w := fun _ _ => rfl
  have hdet : LinearMap.det f = (∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2)⁻¹ := by
    rw [LinearMap.det_pi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]
  have hpos : 0 < ∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2 :=
    Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 hc0) _
  let L : Submodule ℤ (InfinitePlace E → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HomCovolume.HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ z ∈ (ideLat I c : Set (InfinitePlace E → ℂ)) := by
    intro z
    change f z ∈ L₀ ↔ ∃ y ∈ I, ∀ w, z w = (c : ℂ) * w.embedding y
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩
    · rw [← h w, hf, mul_inv_cancel_left₀ hc0]
    · rw [hf, h w, inv_mul_cancel_left₀ hc0]
  refine ⟨latticeDomain L, measurableSet_latticeDomain L, fun a => ?_, ?_⟩
  · obtain ⟨z, hz, hu'⟩ := existsUnique_add_mem_latticeDomain L a
    refine ⟨z, ⟨(hL z).1 z.2, hz⟩, ?_⟩
    rintro l ⟨hl, hl'⟩
    exact congrArg Subtype.val (hu' ⟨l, (hL l).2 hl⟩ hl')
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet, abs_of_pos (inv_pos.2 hpos),
      div_inv_eq_mul] at h
    have hfin : volume (latticeDomain L) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]
    congr 1
    have hn : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have hDpos : 0 < |(discr F : ℝ)| := abs_pos.2 hdF
    have hr : |(discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) =
        |(discr F : ℝ)| ^ (1 + 2 * t') / |(discr F : ℝ)| ^ (2 * t) := by
      rw [show (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) = ((1 + 2 * t' : ℕ) : ℝ) - ((2 * t : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_sub hDpos, Real.rpow_natCast, Real.rpow_natCast]
    rw [hNI, HomCovolume.vInv_pow E hE, hn, hd, Real.sqrt_sq hDpos.le, hr, Finset.prod_const, Finset.card_univ,
      Complex.norm_real, Real.norm_of_nonneg hc.le]
    generalize |(discr F : ℝ)| = D at hDpos
    generalize Fintype.card (InfinitePlace E) = n
    rw [inv_pow, inv_pow, inv_inv, ← pow_mul, ← pow_mul, ← pow_mul, pow_add, pow_one, div_eq_mul_inv]
    ring

end GlobalTheory.SnMass.VolN
