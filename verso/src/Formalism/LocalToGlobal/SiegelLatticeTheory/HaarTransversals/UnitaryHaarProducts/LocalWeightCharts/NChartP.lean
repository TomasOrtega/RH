import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NShear
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.OpnContinuous
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilpotentChartNormBound

open MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.SplitPrimeNormLemmas Matrix

noncomputable section

namespace WlocSk

/- English proof (translation)
Simplify using `only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]`. Establish `h : Fintype.card (NB.UP r) ≤ Fintype.card (Fin r × Fin r)` using `Fintype.card_le_of_injective Subtype.val Subtype.val_injective`. Simplify using `only [Fintype.card_prod, Fintype.card_fin] at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_CI_le (k r : ℕ) : Fintype.card (NB.CI k r) ≤ r * r + r * (k + 1) + r * r := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have h : Fintype.card (NB.UP r) ≤ Fintype.card (Fin r × Fin r) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega

/- English proof (translation)
Establish `hc` using `card_CI_le k r`. Establish `h1 : 2 * (2 * Fintype.card (NB.CI k r) + r) < 4 * (2 * r + k + 1) ^ 2`. Establish `: 2 * (2 * Fintype.card (NB.CI k r) + r) ≤ 2 * (2 * (r * r + r * (k + 1) + r * r) + r)`. Use linear arithmetic over natural numbers and integers. Use `lt_of_le_of_lt this ?_` and prove the remaining obligations.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (1 : ℝ) ≤ Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))`. Rewrite using `[Real.one_le_sqrt]`. Establish `: (0 : ℝ) ≤ (r : ℝ)` using `Nat.cast_nonneg r`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Unfold `N1H`. Establish `h1' : (((2 * (2 * Fintype.card (NB.CI k r) + r)) : ℕ) : ℝ) < 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2`. Conclude with `h1` after adjusting the coercions. Establish `hp : (0 : ℝ) ≤ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem dim_lt (k r : ℕ) :
    (((2 * (2 * Fintype.card (NB.CI k r) + r)) : ℕ) : ℝ) < N1H k r := by
  have hc := card_CI_le k r
  have h1 : 2 * (2 * Fintype.card (NB.CI k r) + r) < 4 * (2 * r + k + 1) ^ 2 := by
    have : 2 * (2 * Fintype.card (NB.CI k r) + r) ≤ 2 * (2 * (r * r + r * (k + 1) + r * r) + r) := by
      omega
    refine lt_of_le_of_lt this ?_
    nlinarith
  have h2 : (1 : ℝ) ≤ Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) := by
    rw [Real.one_le_sqrt]
    have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    push_cast; linarith
  unfold N1H
  have h1' : (((2 * (2 * Fintype.card (NB.CI k r) + r)) : ℕ) : ℝ) < 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast h1
  have hp : (0 : ℝ) ≤ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  nlinarith

/- English proof (translation)
Introduce `k r`. Set `eC` to `Fintype.equivFin (NB.CI k r)`. Set `Φ : CSp (Fintype.card (NB.CI k r)) r → Mt k r` to `fun t => NB.phi0 (t.1 ∘ eC) t.2`. Set `ψ : Mt k r → CSp (Fintype.card (NB.CI k r)) r` to `fun x => (NB.psiC x ∘ eC.symm, NB.psiR x)`. Establish `hcomp : Continuous fun t : CSp (Fintype.card (NB.CI k r)) r => (t.1 ∘ eC, t.2)` using `(continuous_pi fun i => (continuous_apply (eC i)).comp continuous_fst).prodMk continuous_snd`.

Establish `hΦc : Continuous Φ` using `NB.continuous_nilpotent_chart.comp hcomp`. Establish `hψc : Continuous ψ` using `(continuous_pi fun j => (continuous_apply (eC.symm j)).comp NB.continuous_psiC).prodMk NB.continuous_psiR`. Establish `hleft : Function.LeftInverse ψ Φ`. Introduce `t`. Take `⟨h1, h2⟩` from `NB.nilpotent_chart_right_inverse (t.1 ∘ eC) t.2`.

Use `show (NB.psiC (NB.phi0 (t.1 ∘ eC) t.2) ∘ eC.symm, NB.psiR (NB.phi0 (t.1 ∘ eC) t.2)) = t`. Rewrite using `[h1, h2]`. Apply the tactic sequence `ext j <;> simp`. Establish `hright : ∀ x : Mt k r, Matrix.of x ∈ Nset k r → Φ (ψ x) = x`. Introduce `x hx`.

Use `show NB.phi0 ((NB.psiC x ∘ eC.symm) ∘ eC) (NB.psiR x) = x`. Establish `: (NB.psiC x ∘ eC.symm) ∘ eC = NB.psiC x` using `by funext i; simp`. Rewrite using `[this]`. Conclude with `NB.nilpotent_chart_left_inverse hx`. Establish `hrange : Set.range Φ = {x | Matrix.of x ∈ Nset k r}`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, rfl⟩`. Conclude with `NB.test_vector_mem_schwartz_bruhat _ _`. Introduce `hx`.

Conclude with `⟨ψ x, hright x hx⟩`. Use `⟨Fintype.card (NB.CI k r), r, 2, Φ, (r : ℝ) + 2, by norm_num, dim_lt k r, by positivity, ?_, hrange, ?_, ?_⟩` and prove the remaining obligations. Use `MeasurableEmbedding.of_measurable_inverse hΦc.measurable ?_ hψc.measurable hleft` and prove the remaining obligations. Establish `: Set.range Φ = {x | Φ (ψ x) = x}`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, rfl⟩ show Φ (ψ (Φ t)) = Φ t`. Rewrite using `[hleft t]`. Introduce `hx`. Conclude with `⟨ψ x, hx⟩`.

Rewrite using `[this]`. Conclude with `(isClosed_eq (hΦc.comp hψc) continuous_id).measurableSet`. Introduce `m₀ h0`. Set `G : (Fin (Fintype.card (NB.CI k r)) → ℂ) → Fin (Fintype.card (NB.CI k r)) → ℂ` to `fun y j => NB.shG m₀ (y ∘ eC) (eC.symm j)`. Set `H : (Fin (Fintype.card (NB.CI k r)) → ℂ) → Fin r → ℝ` to `fun y => NB.shH m₀ (y ∘ eC)`.

Establish `hyc : Continuous fun y : Fin (Fintype.card (NB.CI k r)) → ℂ => y ∘ eC` using `continuous_pi fun i => continuous_apply (eC i)`. Use `⟨fun t => (t.1 + G t.1, t.2 + H t.1), ?_, ?_⟩` and prove the remaining obligations. Use `NB.shear_mp (fun j => NB.rk (eC.symm j)) G H (fun j => ((NB.continuous_shG m₀ (eC.symm j)).comp hyc).measurable) ?_ ((NB.continuous_shH m₀).comp hyc).measurable` and prove the remaining obligations. Introduce `j y y' hyy`. Use `NB.shG_dep m₀ (eC.symm j) (y ∘ eC) (y' ∘ eC) fun i hi => ?_` and prove the remaining obligations.

Conclude with `hyy (eC i) (by simpa using hi)`. Introduce `t`. Take `⟨h1, h2⟩` from `NB.lmul_coord h0 (t.1 ∘ eC) t.2`. Establish `hmem : m₀ * NB.phi0 (t.1 ∘ eC) t.2 ∈ Nset k r` using `UnitaryGroupBasics.mem_n_mul h0 (NB.test_vector_mem_schwartz_bruhat _ _)`. Use `show m₀ * NB.phi0 (t.1 ∘ eC) t.2 = NB.phi0 ((t.1 + G t.1) ∘ eC) (t.2 + H t.1)`.

Establish `e1 : (t.1 + G t.1) ∘ eC = t.1 ∘ eC + NB.shG m₀ (t.1 ∘ eC)`. Use function extensionality and compare the values at `i`. Simplify using `[G]`. Rewrite using `[e1, ← h1]`. Use `show _ = NB.phi0 (NB.psiC (m₀ * NB.phi0 (t.1 ∘ eC) t.2)) (t.2 + NB.shH m₀ (t.1 ∘ eC))`.

Rewrite using `[← h2]`. Conclude with `(NB.nilpotent_chart_left_inverse hmem).symm`. Introduce `t`. Establish `hg` using `NB.nilpotent_chart_norm_bound (t.1 ∘ eC) t.2`. Establish `hn : ‖t‖ ≤ ‖(t.1 ∘ eC, t.2)‖`.

Rewrite using `[Prod.norm_def, Prod.norm_def]`. Use `max_le_max ?_ le_rfl` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_` and prove the remaining obligations. Use `norm_le_pi_norm (t.1 ∘ eC) (eC.symm j)` as an intermediate fact. Simplify using `using this`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem nilpotent_chart_exists : NChart := by
  intro k r
  let eC := Fintype.equivFin (NB.CI k r)
  let Φ : CSp (Fintype.card (NB.CI k r)) r → Mt k r := fun t => NB.phi0 (t.1 ∘ eC) t.2
  let ψ : Mt k r → CSp (Fintype.card (NB.CI k r)) r := fun x => (NB.psiC x ∘ eC.symm, NB.psiR x)
  have hcomp : Continuous fun t : CSp (Fintype.card (NB.CI k r)) r => (t.1 ∘ eC, t.2) :=
    (continuous_pi fun i => (continuous_apply (eC i)).comp continuous_fst).prodMk continuous_snd
  have hΦc : Continuous Φ := NB.continuous_nilpotent_chart.comp hcomp
  have hψc : Continuous ψ :=
    (continuous_pi fun j => (continuous_apply (eC.symm j)).comp NB.continuous_psiC).prodMk
      NB.continuous_psiR
  have hleft : Function.LeftInverse ψ Φ := by
    intro t
    obtain ⟨h1, h2⟩ := NB.nilpotent_chart_right_inverse (t.1 ∘ eC) t.2
    show (NB.psiC (NB.phi0 (t.1 ∘ eC) t.2) ∘ eC.symm, NB.psiR (NB.phi0 (t.1 ∘ eC) t.2)) = t
    rw [h1, h2]
    ext j <;> simp
  have hright : ∀ x : Mt k r, Matrix.of x ∈ Nset k r → Φ (ψ x) = x := by
    intro x hx
    show NB.phi0 ((NB.psiC x ∘ eC.symm) ∘ eC) (NB.psiR x) = x
    have : (NB.psiC x ∘ eC.symm) ∘ eC = NB.psiC x := by funext i; simp
    rw [this]
    exact NB.nilpotent_chart_left_inverse hx
  have hrange : Set.range Φ = {x | Matrix.of x ∈ Nset k r} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact NB.test_vector_mem_schwartz_bruhat _ _
    · intro hx
      exact ⟨ψ x, hright x hx⟩
  refine ⟨Fintype.card (NB.CI k r), r, 2, Φ, (r : ℝ) + 2, by norm_num, dim_lt k r, by positivity,
    ?_, hrange, ?_, ?_⟩
  ·
    refine MeasurableEmbedding.of_measurable_inverse hΦc.measurable ?_ hψc.measurable hleft
    have : Set.range Φ = {x | Φ (ψ x) = x} := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        show Φ (ψ (Φ t)) = Φ t
        rw [hleft t]
      · intro hx
        exact ⟨ψ x, hx⟩
    rw [this]
    exact (isClosed_eq (hΦc.comp hψc) continuous_id).measurableSet
  ·
    intro m₀ h0
    let G : (Fin (Fintype.card (NB.CI k r)) → ℂ) → Fin (Fintype.card (NB.CI k r)) → ℂ :=
      fun y j => NB.shG m₀ (y ∘ eC) (eC.symm j)
    let H : (Fin (Fintype.card (NB.CI k r)) → ℂ) → Fin r → ℝ := fun y => NB.shH m₀ (y ∘ eC)
    have hyc : Continuous fun y : Fin (Fintype.card (NB.CI k r)) → ℂ => y ∘ eC :=
      continuous_pi fun i => continuous_apply (eC i)
    refine ⟨fun t => (t.1 + G t.1, t.2 + H t.1), ?_, ?_⟩
    · refine NB.shear_mp (fun j => NB.rk (eC.symm j)) G H
        (fun j => ((NB.continuous_shG m₀ (eC.symm j)).comp hyc).measurable) ?_
        ((NB.continuous_shH m₀).comp hyc).measurable
      intro j y y' hyy
      refine NB.shG_dep m₀ (eC.symm j) (y ∘ eC) (y' ∘ eC) fun i hi => ?_
      exact hyy (eC i) (by simpa using hi)
    · intro t
      obtain ⟨h1, h2⟩ := NB.lmul_coord h0 (t.1 ∘ eC) t.2
      have hmem : m₀ * NB.phi0 (t.1 ∘ eC) t.2 ∈ Nset k r := UnitaryGroupBasics.mem_n_mul h0 (NB.test_vector_mem_schwartz_bruhat _ _)
      show m₀ * NB.phi0 (t.1 ∘ eC) t.2 = NB.phi0 ((t.1 + G t.1) ∘ eC) (t.2 + H t.1)
      have e1 : (t.1 + G t.1) ∘ eC = t.1 ∘ eC + NB.shG m₀ (t.1 ∘ eC) := by
        funext i; simp [G]
      rw [e1, ← h1]
      show _ = NB.phi0 (NB.psiC (m₀ * NB.phi0 (t.1 ∘ eC) t.2)) (t.2 + NB.shH m₀ (t.1 ∘ eC))
      rw [← h2]
      exact (NB.nilpotent_chart_left_inverse hmem).symm
  ·
    intro t
    have hg := NB.nilpotent_chart_norm_bound (t.1 ∘ eC) t.2
    have hn : ‖t‖ ≤ ‖(t.1 ∘ eC, t.2)‖ := by
      rw [Prod.norm_def, Prod.norm_def]
      refine max_le_max ?_ le_rfl
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
      have := norm_le_pi_norm (t.1 ∘ eC) (eC.symm j)
      simpa using this
    calc 1 + ‖t‖ ≤ 1 + ‖(t.1 ∘ eC, t.2)‖ := by linarith
      _ ≤ _ := hg

end WlocSk
