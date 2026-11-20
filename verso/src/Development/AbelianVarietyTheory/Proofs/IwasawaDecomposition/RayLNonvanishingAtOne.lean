import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassPartialZetaContinuationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DedekindZetaFactorizationRayStatement

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

namespace GlobalTheory.Mem

/- English proof (translation)
Use `⟨dslope f 1, ?_, fun s => ?_⟩` and prove the remaining obligations. Rewrite `hf`, the goal using `[← differentiableOn_univ]`. Conclude with `(Complex.differentiableOn_dslope Filter.univ_mem).2 hf`. Use `sub_smul_dslope f 1 s` as an intermediate fact. Rewrite `this` using `[h1, sub_zero, smul_eq_mul]`.

Conclude with `this.symm`.
-/
lemma exists_entire_div_sub_one {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h1 : f 1 = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s, f s = (s - 1) * g s := by
  refine ⟨dslope f 1, ?_, fun s => ?_⟩
  · rw [← differentiableOn_univ] at hf ⊢
    exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hf
  · have := sub_smul_dslope f 1 s
    rw [h1, sub_zero, smul_eq_mul] at this
    exact this.symm

/- English proof (translation)
Establish `e : D.coef χ = ∑ c, (χ c : ℂ) • D.cnt c`. Use function extensionality and compare the values at `n`. Simplify using `[RayData.coef, Finset.sum_apply]`. Rewrite using `[e, LSeries_sum (fun c _ => (h c).smul _)]`. Simplify using `[LSeries_smul]`.
-/
lemma RayData.LSeries_coef_eq_sum {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
    (χ : D.G →* ℂˣ) (s : ℂ) (h : ∀ c, LSeriesSummable (D.cnt c) s) :
    LSeries (D.coef χ) s = ∑ c, (χ c : ℂ) * LSeries (D.cnt c) s := by
  have e : D.coef χ = ∑ c, (χ c : ℂ) • D.cnt c := by
    funext n
    simp [RayData.coef, Finset.sum_apply]
  rw [e, LSeries_sum (fun c _ => (h c).smul _)]
  simp [LSeries_smul]

/- English proof (translation)
Introduce `K _ _ _ hK M hM D χ₀ hχ₀`. Take `⟨ρ, -, hZ⟩` from `GlobalTheory.T.ray_class_partial_zeta_continuation K hK M hM D`. Use `choose Z hZd hZ1 hZm hZs using hZ`. Set `Y : (D.G →* ℂˣ) → ℂ → ℂ` to `fun χ s => ∑ c, (χ c : ℂ) * Z c s`. Establish `hYd : ∀ χ, Differentiable ℂ (Y χ)` using `fun χ => Differentiable.fun_sum fun c _ => (hZd c).const_mul _`.

Establish `hYm : ∀ χ, Y χ (-1) = 0` using `fun χ => by simp [Y, hZm]`. Establish `hYs : ∀ χ s, 1 < s.re → Y χ s = (s - 1) * LSeries (D.coef χ) s`. Introduce `χ s hs`. Rewrite using `[D.LSeries_coef_eq_sum χ s fun c => (hZs c s hs).1, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[(hZs c s hs).2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hY1 : ∀ χ, χ ≠ 1 → Y χ 1 = 0`. Introduce `χ hχ`. Establish `h0 : ∑ c, (χ c : ℂ) = 0`.

Use `sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) (by` as an intermediate fact. Introduce `h`. Apply `hχ` to reduce the goal to its premises. Use extensionality with `c`. Simplify using `using DFunLike.congr_fun h c)`.

Simplify using `using this`. Simplify using `only [Y, hZ1]`. Rewrite using `[← Finset.sum_mul, h0, zero_mul]`. Establish `hL : ∀ χ : D.G →* ℂˣ, ∃ L : ℂ → ℂ, χ ≠ 1 → Differentiable ℂ L ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s`. Introduce `χ`.

Distinguish the cases in `hχ : χ = 1`. Conclude with `⟨0, fun h => absurd hχ h⟩`. Take `⟨g, hg, hg'⟩` from `exists_entire_div_sub_one (hYd χ) (hY1 χ hχ)`. Use `⟨g, fun _ => ⟨hg, fun s hs => ?_⟩⟩` and prove the remaining obligations. Establish `hs1 : s - 1 ≠ 0`.

Rewrite using `[sub_ne_zero]`. Introduce and unpack `rfl`. Simplify using `at hs`. Conclude with `mul_left_cancel₀ hs1 ((hg' s).symm.trans (hYs χ s hs))`. Use `choose L hL using hL`.

Use `⟨L χ₀, (hL χ₀ hχ₀).1, fun h0 => ?_, (hL χ₀ hχ₀).2⟩` and prove the remaining obligations. Take `⟨g, hg, hg'⟩` from `exists_entire_div_sub_one (hL χ₀ hχ₀).1 h0`. Use `haveI : NeZero ((Monoid.exponent D.G : ℕ) : ℂ) := ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩`. Use `haveI : Finite (D.G →* ℂˣ) := by`. Take `⟨e⟩` from `CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity D.G ℂ`.

Conclude with `Finite.of_equiv _ e.toEquiv.symm`. Use `haveI : Fintype (D.G →* ℂˣ) := Fintype.ofFinite _`. Take `⟨b, hb0, hb1, hba, hbs⟩` from `GlobalTheory.T.dedekind_zeta_factorization_ray K M hM D`. Set `F : ℂ → ℂ` to `fun s => Y 1 s * (g s * ∏ χ ∈ (Finset.univ.erase 1).erase χ₀, L χ s)`. Establish `hFd : Differentiable ℂ F`.

Use `(hYd 1).mul (hg.mul ?_)` and prove the remaining obligations. Use `Differentiable.fun_finset_prod fun χ hχ => (hL χ ?_).1` and prove the remaining obligations. Conclude with `Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hχ)`. Establish `hFs : {s : ℂ | (1 : ℝ) < s.re}.EqOn F (LSeries b)`. Introduce `s hs`.

Establish `hs' : 1 < s.re` using `hs`. Rewrite using `[hbs s hs', ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : D.G →* ℂˣ)), ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hχ₀, Finset.mem_univ χ₀⟩), ← (hL χ₀ hχ₀).2 s hs', hg' s]`. Simplify using `only [F]`. Rewrite using `[hYs 1 s hs', Finset.prod_congr rfl fun χ hχ => (hL χ (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hχ))).2 s hs']`. Expand and normalize the polynomial expressions, which then agree.

Establish `hpos` using `LSeries.positive_of_differentiable_of_eqOn hb0 hb1 hFd (x := 1) (by exact_mod_cast hba) hFs (-1)`. Establish `: F ((-1 : ℝ) : ℂ) = 0`. Simplify using `[F, hYm]`. Rewrite `hpos` using `[this]`. Conclude with `lt_irrefl _ hpos`.
-/
theorem rayLSeries_entire_ne_zero_one : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ), χ ≠ 1 → ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ L 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
  intro K _ _ _ hK M hM D χ₀ hχ₀
  classical
  obtain ⟨ρ, -, hZ⟩ := GlobalTheory.T.ray_class_partial_zeta_continuation K hK M hM D
  choose Z hZd hZ1 hZm hZs using hZ
  let Y : (D.G →* ℂˣ) → ℂ → ℂ := fun χ s => ∑ c, (χ c : ℂ) * Z c s
  have hYd : ∀ χ, Differentiable ℂ (Y χ) := fun χ =>
    Differentiable.fun_sum fun c _ => (hZd c).const_mul _
  have hYm : ∀ χ, Y χ (-1) = 0 := fun χ => by simp [Y, hZm]
  have hYs : ∀ χ s, 1 < s.re → Y χ s = (s - 1) * LSeries (D.coef χ) s := by
    intro χ s hs
    rw [D.LSeries_coef_eq_sum χ s fun c => (hZs c s hs).1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [(hZs c s hs).2]; ring
  have hY1 : ∀ χ, χ ≠ 1 → Y χ 1 = 0 := by
    intro χ hχ
    have h0 : ∑ c, (χ c : ℂ) = 0 := by
      have := sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) (by
        intro h
        apply hχ
        ext c
        simpa using DFunLike.congr_fun h c)
      simpa using this
    simp only [Y, hZ1]
    rw [← Finset.sum_mul, h0, zero_mul]
  have hL : ∀ χ : D.G →* ℂˣ, ∃ L : ℂ → ℂ, χ ≠ 1 →
      Differentiable ℂ L ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨0, fun h => absurd hχ h⟩
    obtain ⟨g, hg, hg'⟩ := exists_entire_div_sub_one (hYd χ) (hY1 χ hχ)
    refine ⟨g, fun _ => ⟨hg, fun s hs => ?_⟩⟩
    have hs1 : s - 1 ≠ 0 := by
      rw [sub_ne_zero]; rintro rfl; simp at hs
    exact mul_left_cancel₀ hs1 ((hg' s).symm.trans (hYs χ s hs))
  choose L hL using hL
  refine ⟨L χ₀, (hL χ₀ hχ₀).1, fun h0 => ?_, (hL χ₀ hχ₀).2⟩
  obtain ⟨g, hg, hg'⟩ := exists_entire_div_sub_one (hL χ₀ hχ₀).1 h0
  haveI : NeZero ((Monoid.exponent D.G : ℕ) : ℂ) := ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  haveI : Finite (D.G →* ℂˣ) := by
    obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity D.G ℂ
    exact Finite.of_equiv _ e.toEquiv.symm
  haveI : Fintype (D.G →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨b, hb0, hb1, hba, hbs⟩ := GlobalTheory.T.dedekind_zeta_factorization_ray K M hM D
  let F : ℂ → ℂ := fun s => Y 1 s * (g s * ∏ χ ∈ (Finset.univ.erase 1).erase χ₀, L χ s)
  have hFd : Differentiable ℂ F := by
    refine (hYd 1).mul (hg.mul ?_)
    refine Differentiable.fun_finset_prod fun χ hχ => (hL χ ?_).1
    exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hχ)
  have hFs : {s : ℂ | (1 : ℝ) < s.re}.EqOn F (LSeries b) := by
    intro s hs
    have hs' : 1 < s.re := hs
    rw [hbs s hs', ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : D.G →* ℂˣ)),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hχ₀, Finset.mem_univ χ₀⟩),
      ← (hL χ₀ hχ₀).2 s hs', hg' s]
    simp only [F]
    rw [hYs 1 s hs', Finset.prod_congr rfl fun χ hχ =>
      (hL χ (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hχ))).2 s hs']
    ring
  have hpos := LSeries.positive_of_differentiable_of_eqOn hb0 hb1 hFd (x := 1)
    (by exact_mod_cast hba) hFs (-1)
  have : F ((-1 : ℝ) : ℂ) = 0 := by
    simp [F, hYm]
  rw [this] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.Mem
