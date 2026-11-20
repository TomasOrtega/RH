import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

/- English proof (translation)
Establish `hsplit : ∀ f : InfinitePlace F → ℝ, ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)}, f v.1 = ∑ w, f w - f (w₀ : InfinitePlace F)`. Introduce `f`. Rewrite using `[← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (w₀ : InfinitePlace F)), add_sub_cancel_right]`. Conclude with `(Finset.sum_subtype _ (fun w => by simp) f).symm`. Set `a : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ` to `fun v => D v.1 / (mult v.1 : ℝ) - D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ)`.

Set `φ : ({w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) →ₗ[ℝ] ℝ` to `{ toFun := fun x => ∑ v, x v * a v map_add' := fun x y => by simp [Finset.sum_add_distrib, add_mul] map_smul' := fun r x => by simp [Finset.mul_sum, mul_assoc] }`. Establish `hφ : ∀ u : (𝓞 F)ˣ, φ (logEmbedding F (Additive.ofMul u)) = 0`. Introduce `u`. Establish `e1 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)}, Real.log (v.1 (algebraMap (𝓞 F) F u)) * D v.1 = 0 - Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u)) * D (w₀ : InfinitePlace F)`. Rewrite using `[← h u]`.

Conclude with `hsplit (fun w => Real.log (w (algebraMap (𝓞 F) F u)) * D w)`. Establish `e2 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)}, (mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u)) = 0 - (mult (w₀ : InfinitePlace F) : ℝ) * Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u))`. Rewrite using `[← sum_mult_mul_log u]`. Conclude with `hsplit (fun w => (mult w : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)))`. Establish `hm0 : (mult (w₀ : InfinitePlace F) : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr mult_ne_zero`.

Use `show ∑ v, logEmbedding F (Additive.ofMul u) v * a v = 0`. Simplify using `only [logEmbedding_component]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `v _`.

Establish `hm : (mult v.1 : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr mult_ne_zero`. Simplify using `only [a]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Use `_ = 0 := by`.

Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Establish `hle : Submodule.span ℝ (unitLattice F : Set (logSpace F)) ≤ LinearMap.ker φ`. Rewrite using `[Submodule.span_le]`.

Introduce `x hx`. Take `⟨y, -, rfl⟩` from `hx`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker]`. Conclude with `hφ (Additive.toMul y)`. Rewrite `hle` using `[unitLattice_span_eq_top F]`.

Establish `ha : ∀ v, a v = 0`. Introduce `v`. Establish `hv : (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) ∈ LinearMap.ker φ` using `hle Submodule.mem_top`. Rewrite `hv` using `[LinearMap.mem_ker]`. Establish `hφv : φ (Pi.single v (1 : ℝ)) = a v` using `by show ∑ v', (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) v' * a v' = a v`.

Simplify using `[Pi.single_apply]`. Rewrite using `[← hφv]`. Conclude with `hv`. Use `⟨D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ), fun w => ?_⟩` and prove the remaining obligations. Establish `hm : (mult w : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr mult_ne_zero`.

Distinguish the cases in `hw : w = (w₀ : InfinitePlace F)`. Substitute `hw` using the available equality. Clear the denominators using the available nonvanishing facts. Establish `hv` using `ha ⟨w, hw⟩`. Simplify using `only [a, sub_eq_zero] at hv`.

Rewrite using `[← hv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_eq_mul_mult_of_units (F : Type) [Field F] [NumberField F]
    (D : InfinitePlace F → ℝ)
    (h : ∀ u : (𝓞 F)ˣ, ∑ w : InfinitePlace F, Real.log (w ((u : 𝓞 F) : F)) * D w = 0) :
    ∃ c : ℝ, ∀ w, D w = c * (mult w : ℝ) := by
  classical
  have hsplit : ∀ f : InfinitePlace F → ℝ,
      ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)}, f v.1 = ∑ w, f w - f (w₀ : InfinitePlace F) := by
    intro f
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (w₀ : InfinitePlace F)), add_sub_cancel_right]
    exact (Finset.sum_subtype _ (fun w => by simp) f).symm
  let a : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ :=
    fun v => D v.1 / (mult v.1 : ℝ) - D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ)
  let φ : ({w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ v, x v * a v
      map_add' := fun x y => by simp [Finset.sum_add_distrib, add_mul]
      map_smul' := fun r x => by simp [Finset.mul_sum, mul_assoc] }
  have hφ : ∀ u : (𝓞 F)ˣ, φ (logEmbedding F (Additive.ofMul u)) = 0 := by
    intro u
    have e1 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
        Real.log (v.1 (algebraMap (𝓞 F) F u)) * D v.1
          = 0 - Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u)) * D (w₀ : InfinitePlace F) := by
      rw [← h u]
      exact hsplit (fun w => Real.log (w (algebraMap (𝓞 F) F u)) * D w)
    have e2 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
        (mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u))
          = 0 - (mult (w₀ : InfinitePlace F) : ℝ) * Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u)) := by
      rw [← sum_mult_mul_log u]
      exact hsplit (fun w => (mult w : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)))
    have hm0 : (mult (w₀ : InfinitePlace F) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
    show ∑ v, logEmbedding F (Additive.ofMul u) v * a v = 0
    simp only [logEmbedding_component]
    calc ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
          (mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u)) * a v
        = ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
          (Real.log (v.1 (algebraMap (𝓞 F) F u)) * D v.1
            - D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ) * ((mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u)))) := by
          apply Finset.sum_congr rfl
          intro v _
          have hm : (mult v.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
          simp only [a]
          field_simp
          try ring
      _ = 0 := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2]
          field_simp
          try ring
  have hle : Submodule.span ℝ (unitLattice F : Set (logSpace F)) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hφ (Additive.toMul y)
  rw [unitLattice_span_eq_top F] at hle
  have ha : ∀ v, a v = 0 := by
    intro v
    have hv : (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) ∈ LinearMap.ker φ :=
      hle Submodule.mem_top
    rw [LinearMap.mem_ker] at hv
    have hφv : φ (Pi.single v (1 : ℝ)) = a v := by
      show ∑ v', (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) v' * a v' = a v
      simp [Pi.single_apply]
    rw [← hφv]
    exact hv
  refine ⟨D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ), fun w => ?_⟩
  have hm : (mult w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
  by_cases hw : w = (w₀ : InfinitePlace F)
  · subst hw
    field_simp
  · have hv := ha ⟨w, hw⟩
    simp only [a, sub_eq_zero] at hv
    rw [← hv]
    field_simp

/- English proof (translation)
Introduce `F _ _ d t hd ht`. Establish `hfib : ∀ f : (F →+* ℂ) → ℝ, ∑ σ, f σ = ∑ w : InfinitePlace F, ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ` using `fun f => (Finset.sum_fiberwise Finset.univ InfinitePlace.mk f).symm`. Take `⟨c, hc⟩` from `exists_eq_mul_mult_of_units F (fun w => ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), d σ) (by`. Introduce `u`. Establish `h1` using `hd u`.

Rewrite `h1` using `[hfib]`. Use `Eq.trans ?_ h1` and prove the remaining obligations. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Simplify using `only [Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `σ hσ`. Take `⟨-, rfl⟩` from `Finset.mem_filter.mp hσ`. Rewrite using `[InfinitePlace.apply])`. Establish `ht' : ∀ σ : F →+* ℂ, t σ = t (InfinitePlace.mk σ).embedding`.

Introduce `σ`. Establish `h2 : InfinitePlace.mk (InfinitePlace.mk σ).embedding = InfinitePlace.mk σ` using `InfinitePlace.mk_embedding _`. Break down `InfinitePlace.mk_eq_iff.mp h2 with h3 | h3` into its components or cases. Rewrite using `[h3]`. Establish `h4` using `ht (InfinitePlace.mk σ).embedding`.

Rewrite `h4` using `[h3]`. Conclude with `h4`. Establish `hTfib : ∀ (w : InfinitePlace F) (f : (F →+* ℂ) → ℝ), ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), t σ * f σ = t w.embedding * ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ`. Introduce `w f`. Rewrite using `[Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `σ hσ`. Take `⟨-, rfl⟩` from `Finset.mem_filter.mp hσ`. Rewrite using `[← ht' σ]`. Establish `hn : (Module.finrank ℚ F : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr Module.finrank_pos.ne'`.

Establish `hsum_d : ∑ σ, d σ = c * (Module.finrank ℚ F : ℝ)`. Rewrite using `[hfib, ← InfinitePlace.sum_mult_eq, Nat.cast_sum, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Conclude with `hc w`.

Establish `hsum_t : ∑ σ, t σ = ∑ w : InfinitePlace F, t w.embedding * (w.mult : ℝ)`. Rewrite using `[hfib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Establish `h5` using `hTfib w (fun _ => 1)`.

Simplify using `only [mul_one, Finset.sum_const, nsmul_eq_mul] at h5`. Rewrite using `[h5, InfinitePlace.card_filter_mk_eq]`. Establish `hsum_td : ∑ σ, t σ * d σ = c * ∑ σ, t σ` using `by conv_lhs => rw [hfib]`. Rewrite using `[hsum_t, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `w _`. Rewrite using `[hTfib w d]`. Establish `h6` using `hc w`. Rewrite using `[h6]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsum_td, hsum_d, div_mul_eq_mul_div, eq_div_iff hn]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_eq_mean_of_units :
    ∀ (F : Type) [Field F] [NumberField F] (d t : (F →+* ℂ) → ℝ),
      (∀ u : (𝓞 F)ˣ, ∑ σ : F →+* ℂ, Real.log ‖σ ((u : 𝓞 F) : F)‖ * d σ = 0) →
      (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) →
      ∑ σ : F →+* ℂ, t σ * d σ =
        (∑ σ : F →+* ℂ, t σ) / (Module.finrank ℚ F : ℝ) * ∑ σ : F →+* ℂ, d σ := by
  intro F _ _ d t hd ht
  classical
  have hfib : ∀ f : (F →+* ℂ) → ℝ, ∑ σ, f σ
      = ∑ w : InfinitePlace F, ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ :=
    fun f => (Finset.sum_fiberwise Finset.univ InfinitePlace.mk f).symm
  obtain ⟨c, hc⟩ := exists_eq_mul_mult_of_units F
    (fun w => ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), d σ) (by
      intro u
      have h1 := hd u
      rw [hfib] at h1
      refine Eq.trans ?_ h1
      apply Finset.sum_congr rfl
      intro w _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hσ
      rw [InfinitePlace.apply])
  have ht' : ∀ σ : F →+* ℂ, t σ = t (InfinitePlace.mk σ).embedding := by
    intro σ
    have h2 : InfinitePlace.mk (InfinitePlace.mk σ).embedding = InfinitePlace.mk σ :=
      InfinitePlace.mk_embedding _
    rcases InfinitePlace.mk_eq_iff.mp h2 with h3 | h3
    · rw [h3]
    · have h4 := ht (InfinitePlace.mk σ).embedding
      rw [h3] at h4
      exact h4
  have hTfib : ∀ (w : InfinitePlace F) (f : (F →+* ℂ) → ℝ),
      ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), t σ * f σ
        = t w.embedding * ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ := by
    intro w f
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hσ
    rw [← ht' σ]
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hsum_d : ∑ σ, d σ = c * (Module.finrank ℚ F : ℝ) := by
    rw [hfib, ← InfinitePlace.sum_mult_eq, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    exact hc w
  have hsum_t : ∑ σ, t σ = ∑ w : InfinitePlace F, t w.embedding * (w.mult : ℝ) := by
    rw [hfib]
    apply Finset.sum_congr rfl
    intro w _
    have h5 := hTfib w (fun _ => 1)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h5
    rw [h5, InfinitePlace.card_filter_mk_eq]
  have hsum_td : ∑ σ, t σ * d σ = c * ∑ σ, t σ := by
    conv_lhs => rw [hfib]
    rw [hsum_t, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [hTfib w d]
    have h6 := hc w
    rw [h6]
    ring
  rw [hsum_td, hsum_d, div_mul_eq_mul_div, eq_div_iff hn]
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
