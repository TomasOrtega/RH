import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

namespace GlobalTheory.Adelic.HeightScaling

variable {F K : Type} [Field F] [Field K] [NumberField K] {N n : ℕ}

/- English proof (translation)
Use `Set.Finite.subset (FinitePlace.hasFiniteMulSupport hc) fun v hv h1 => hv ?_` and prove the remaining obligations. Simplify using `only at h1`. Simplify using `[h1]`.
-/
theorem finite_support_log {c : K} (hc : c ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (v c)).Finite := by
  refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport hc) fun v hv h1 => hv ?_
  simp only at h1
  simp [h1]

/- English proof (translation)
Establish `hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite` using `FinitePlace.hasFiniteMulSupport hc`. Establish `h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c)`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hmul.toFinset), finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp), Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]`. Introduce `w hw`. Simplify using `only [Set.Finite.coe_toFinset, Function.mem_mulSupport]`.

Introduce `h1`. Apply `hw` to reduce the goal to its premises. Simplify using `[h1]`. Establish `h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c|`. Rewrite using `[← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]`.

Use `congr 1`. Use `congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)` as an intermediate fact. Rewrite `this` using `[norm_prod]`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]`. Rewrite using `[eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]`.

Rewrite using `[h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]`. Use `push_cast`. Rewrite using `[Real.log_inv, neg_add_cancel]`.
-/
theorem sum_log_eq_zero {c : K} (hc : c ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log (v c)) + ∑ τ : K →+* ℂ, Real.log ‖τ c‖ = 0 := by
  have hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv, neg_add_cancel]

/- English proof (translation)
Establish `hfin : (⋃ k : {k : Fin n // ∑ j, φ (w j k) * y j ≠ 0}, Function.mulSupport fun v : FinitePlace K => v (∑ j, φ (w j k.1) * y j)).Finite` using `Set.finite_iUnion fun k => FinitePlace.hasFiniteMulSupport k.2`. Use `hfin.subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Apply `hv` to reduce the goal to its premises. Establish `h1 : ∀ k : Fin n, ∑ j, φ (w j k) * y j ≠ 0 → v.1 (∑ j, φ (w j k) * y j) = 1` using `fun k hk => by`.

Assume the negation of the conclusion as `h`. Conclude with `hn (Set.mem_iUnion.2 ⟨⟨k, hk⟩, h⟩)`. Establish `hpos` using `finSize_pos hw φ v.1 hy`. Establish `hle : finSize w φ v.1 y ≤ 1` using `Real.iSup_le (fun k => by`. Distinguish the cases in `hk : ∑ j, φ (w j k) * y j = 0`.

Rewrite using `[hk, map_zero]`. Conclude with `zero_le_one`. Conclude with `(h1 k hk).le) zero_le_one`. Establish `hge : 1 ≤ finSize w φ v.1 y`. Assume the negation of the conclusion as `h`.

Use `hpos.not_ge (Real.iSup_le (fun k => ?_) le_rfl)` and prove the remaining obligations. Distinguish the cases in `hk : ∑ j, φ (w j k) * y j = 0`. Rewrite using `[hk, map_zero]`. Conclude with `absurd ((h1 k hk).ge.trans (le_finSize w φ v.1 y k)) h`. Simplify using `only [le_antisymm hle hge, Real.log_one]`.
-/
theorem finite_support_log_finSize {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤)
    (φ : F →+* K) {y : Fin N → K} (hy : y ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (finSize w φ v.1 y)).Finite := by
  have hfin : (⋃ k : {k : Fin n // ∑ j, φ (w j k) * y j ≠ 0},
      Function.mulSupport fun v : FinitePlace K => v (∑ j, φ (w j k.1) * y j)).Finite :=
    Set.finite_iUnion fun k => FinitePlace.hasFiniteMulSupport k.2
  refine hfin.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ k : Fin n, ∑ j, φ (w j k) * y j ≠ 0 → v.1 (∑ j, φ (w j k) * y j) = 1 := fun k hk => by
    by_contra h
    exact hn (Set.mem_iUnion.2 ⟨⟨k, hk⟩, h⟩)
  have hpos := finSize_pos hw φ v.1 hy
  have hle : finSize w φ v.1 y ≤ 1 := Real.iSup_le (fun k => by
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]; exact zero_le_one
    · exact (h1 k hk).le) zero_le_one
  have hge : 1 ≤ finSize w φ v.1 y := by
    by_contra h
    refine hpos.not_ge (Real.iSup_le (fun k => ?_) le_rfl)
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]
    · exact absurd ((h1 k hk).ge.trans (le_finSize w φ v.1 y k)) h
  simp only [le_antisymm hle hge, Real.log_one]

/- English proof (translation)
Introduce `F K _ _ _ _ _ N n w A hw hA y c hy hc`. Rewrite using `[pointHeight_eq, pointHeight_eq]`. Use `congr 1`. Establish `e1 : ∀ v : FinitePlace K, Real.log (finSize w (algebraMap F K) v.1 (c • y)) = Real.log (v c) + Real.log (finSize w (algebraMap F K) v.1 y)` using `fun v => by`. Rewrite using `[finSize_smul, Real.log_mul (v.1.ne_zero hc) (finSize_pos hw _ v.1 hy).ne']`.

Both sides reduce to the same expression. Establish `e2 : ∀ τ : K →+* ℂ, Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ ((c • y) j)) = Real.log ‖τ c‖ + Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j))` using `fun τ => by`. Establish `h0 : (fun j => τ (y j)) ≠ 0` using `fun h => hy (funext fun j => (map_eq_zero τ).1 (congrFun h j))`. Establish `h1 : (fun j => τ ((c • y) j)) = τ c • fun j => τ (y j)` using `funext fun j => by simp`. Rewrite using `[h1, archSize_smul, Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero τ).2 hc)) (archSize_pos (hA _) h0).ne']`.

Rewrite using `[finsum_congr e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_add_distrib, finsum_add_distrib (finite_support_log hc) (finite_support_log_finSize hw _ hy)]`. Combine the linear relations using `[sum_log_eq_zero hc]`.
-/
theorem pointHeight_smul : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (y : Fin N → K) (c : K), y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y := by
  intro F K _ _ _ _ _ N n w A hw hA y c hy hc
  rw [pointHeight_eq, pointHeight_eq]
  congr 1
  have e1 : ∀ v : FinitePlace K, Real.log (finSize w (algebraMap F K) v.1 (c • y)) =
      Real.log (v c) + Real.log (finSize w (algebraMap F K) v.1 y) := fun v => by
    rw [finSize_smul, Real.log_mul (v.1.ne_zero hc) (finSize_pos hw _ v.1 hy).ne']
    rfl
  have e2 : ∀ τ : K →+* ℂ, Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ ((c • y) j)) =
      Real.log ‖τ c‖ + Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j)) := fun τ => by
    have h0 : (fun j => τ (y j)) ≠ 0 := fun h => hy (funext fun j => (map_eq_zero τ).1 (congrFun h j))
    have h1 : (fun j => τ ((c • y) j)) = τ c • fun j => τ (y j) := funext fun j => by simp
    rw [h1, archSize_smul, Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero τ).2 hc)) (archSize_pos (hA _) h0).ne']
  rw [finsum_congr e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_add_distrib,
    finsum_add_distrib (finite_support_log hc) (finite_support_log_finSize hw _ hy)]
  linarith [sum_log_eq_zero hc]

end GlobalTheory.Adelic.HeightScaling
