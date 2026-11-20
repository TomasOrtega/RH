import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff Topology

namespace GlobalTheory.AdaptedCover

noncomputable section

def affineHomeo {e : ℕ} (c : Fin e → ℂ) (ε : ℝ) (hε : ε ≠ 0) :
    (Fin e → ℂ) ≃ₜ (Fin e → ℂ) where
  toFun z := ((ε : ℂ)⁻¹) • (z - c)
  invFun z := c + (ε : ℂ) • z
  left_inv z := by
    have h : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
    simp [smul_smul, h]
  right_inv z := by
    have h : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
    show ((ε : ℂ)⁻¹) • (c + (ε : ℂ) • z - c) = z
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h, one_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/- English proof (translation)
Introduce `z _`. Use `show AnalyticAt ℂ (fun z => ((ε : ℂ)⁻¹) • (z - c)) z`. Use `fun_prop`.
-/
theorem affineHomeo_analytic {e : ℕ} (c : Fin e → ℂ) (ε : ℝ) (hε : ε ≠ 0) :
    AnalyticOnNhd ℂ (affineHomeo c ε hε) Set.univ := by
  intro z _
  show AnalyticAt ℂ (fun z => ((ε : ℂ)⁻¹) • (z - c)) z
  fun_prop

/- English proof (translation)
Introduce `z _`. Use `show AnalyticAt ℂ (fun z => c + (ε : ℂ) • z) z`. Use `fun_prop`.
-/
theorem affineHomeo_symm_analytic {e : ℕ} (c : Fin e → ℂ) (ε : ℝ) (hε : ε ≠ 0) :
    AnalyticOnNhd ℂ (affineHomeo c ε hε).symm Set.univ := by
  intro z _
  show AnalyticAt ℂ (fun z => c + (ε : ℂ) • z) z
  fun_prop

/- English proof (translation)
Use `set c := ψ' x with hc`. Take `⟨ε₀, hε₀, hball⟩` from `Metric.isOpen_iff.1 ψ'.open_target c (ψ'.map_source hx)`. Establish `h1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε` using `self_mem_nhdsWithin`. Establish `h2 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε ≤ ε₀` using `eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds hε₀)`. Establish `h3 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ i, c i ≠ 0 → ε ≤ ‖c i‖`.

Use `Filter.eventually_all.2 fun i => ?_` and prove the remaining obligations. Distinguish the cases in `hi : c i = 0`. Conclude with `Filter.Eventually.of_forall fun _ h => absurd hi h`. Conclude with `(eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (norm_pos_iff.2 hi))).mono fun _ h _ => h`. Take `⟨ε, hε, hεε₀, hεc⟩` from `(h1.and (h2.and h3)).exists`.

Use `set H := affineHomeo c ε hε.ne' with hH`. Set `ψ : OpenPartialHomeomorph X (Fin e → ℂ)` to `ψ'.trans H.toOpenPartialHomeomorph`. Set `σ : Fin m → Option (Fin e)` to `fun k => (σ' k).bind fun i => if c i = 0 then some i else none`. Establish `hσ : ∀ k i, σ k = some i ↔ σ' k = some i ∧ c i = 0`. Introduce `k i`.

Simplify using `only [σ]`. Consider the cases of `h : σ' k with`. Consider the case `none => simp`. Consider the case `some j`. Simplify using `only [Option.bind_some]`.

Use `split_ifs with hj`. Prove the components needed by the constructor for the conclusion. Introduce `h'`. Consider the cases of `h'`. Conclude with `⟨rfl, hj⟩`.

Introduce and unpack `⟨h', -⟩`. Conclude with `h'`. Prove the components needed by the constructor for the conclusion. Introduce `h'`. Consider the cases of `h'`.

Introduce and unpack `⟨h', h''⟩`. Consider the cases of `h'`. Conclude with `absurd h'' hj`. Establish `hsrc : ψ.source = ψ'.source`. Simplify using `[ψ, OpenPartialHomeomorph.trans_source]`.

Establish `htgt : ∀ z, z ∈ ψ.target ↔ H.symm z ∈ ψ'.target`. Introduce `z`. Simplify using `[ψ, OpenPartialHomeomorph.trans_target]`. Establish `hsymm : ∀ z, ψ.symm z = ψ'.symm (H.symm z)`. Introduce `z`.

Both sides reduce to the same expression. Establish `hHs : ∀ z, H.symm z = c + (ε : ℂ) • z` using `fun z => rfl`. Establish `hin : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1, H.symm z ∈ ψ'.target`. Introduce `z hz`. Apply `hball` to reduce the goal to its premises.

Rewrite using `[hHs, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]`. Rewrite `hz` using `[mem_ball_zero_iff]`. Simplify using `only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨ψ, σ, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce `j`. Prove the components needed by the constructor for the conclusion. Establish `hset : (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source = (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ'.source` using `by rw [hsrc]`. Rewrite using `[hset]`. Use `(affineHomeo_analytic c ε hε.ne').comp (hψ' j).1 (Set.mapsTo_univ _ _)` as an intermediate fact.

Conclude with `this`. Conclude with `(hψ' j).2.comp ((affineHomeo_symm_analytic c ε hε.ne').mono (Set.subset_univ _)) (fun z hz => ⟨(htgt z).1 hz.1, by simpa [hsymm] using hz.2⟩)`. Introduce `z hz`. Conclude with `(htgt z).2 (hin z hz)`. Introduce `i i' k hi hi'`.

Conclude with `hσ' i i' k ((hσ i k).1 hi).1 ((hσ i' k).1 hi').1`. Introduce `z hz k`. Establish `hzt` using `hin z hz`. Establish `hys : ψ'.symm (H.symm z) ∈ ψ'.source` using `ψ'.map_target hzt`. Establish `hyy : ψ' (ψ'.symm (H.symm z)) = H.symm z` using `ψ'.right_inv hzt`.

Rewrite using `[hsymm]`. Establish `key : ψ'.symm (H.symm z) ∈ D k ↔ ∃ i, σ' k = some i ∧ (c + (ε : ℂ) • z) i = 0`. Use `Set.ext_iff.1 (hD k) (ψ'.symm (H.symm z))` as an intermediate fact. Rewrite `this`, `hys`, `hyy`, the goal using `[hHs]`. Simplify `this` using `only [Set.mem_inter_iff, Set.mem_setOf_eq, hys, and_true, true_and, hyy]`.

Rewrite using `[key]`. Establish `hz1 : ‖z‖ < 1` using `mem_ball_zero_iff.1 hz`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, hzero⟩`. Establish `hzero' : c i + (ε : ℂ) * z i = 0` using `by simpa using hzero`.

Distinguish the cases in `hci : c i = 0`. Use `⟨i, (hσ k i).2 ⟨hi, hci⟩, ?_⟩` and prove the remaining obligations. Rewrite `hzero'` using `[hci, zero_add]`. Establish `: (ε : ℂ) ≠ 0` using `by exact_mod_cast hε.ne'`. Conclude with `(mul_eq_zero.1 hzero').resolve_left this`.

It suffices to derive a contradiction. Establish `hle` using `hεc i hci`. Establish `heq : c i = -((ε : ℂ) * z i)` using `eq_neg_of_add_eq_zero_left hzero'`. Establish `hnorm : ‖c i‖ = ε * ‖z i‖`. Rewrite using `[heq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]`.

Establish `hzi : ‖z i‖ < 1` using `lt_of_le_of_lt (norm_le_pi_norm z i) hz1`. Establish `: ε * ‖z i‖ < ε` using `by nlinarith [norm_nonneg (z i)]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce and unpack `⟨i, hi, hzi⟩`. Take `⟨hi', hci⟩` from `(hσ k i).1 hi`.

Conclude with `⟨i, hi', by simp [hci, hzi]⟩`. Rewrite using `[hsrc]`. Conclude with `hx`. Use `show H (ψ' x) = 0 show ((ε : ℂ)⁻¹) • (ψ' x - c) = 0`. Rewrite using `[hc, sub_self, smul_zero]`.
-/
theorem exists_adapted_of_chart {e m : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (D : Fin m → Set X) (ψ' : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ' : IsCompatChart A ψ')
    (x : X) (hx : x ∈ ψ'.source) (σ' : Fin m → Option (Fin e))
    (hσ' : ∀ k k' i, σ' k = some i → σ' k' = some i → k = k')
    (hD : ∀ k, D k ∩ ψ'.source = {y ∈ ψ'.source | ∃ i, σ' k = some i ∧ ψ' y i = 0}) :
    ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)),
      IsAdaptedPolydisc A D ψ σ ∧ x ∈ ψ.source ∧ ψ x = 0 := by
  set c := ψ' x with hc
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 ψ'.open_target c (ψ'.map_source hx)
  have h1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
  have h2 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε ≤ ε₀ :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds hε₀)
  have h3 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ i, c i ≠ 0 → ε ≤ ‖c i‖ := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : c i = 0
    · exact Filter.Eventually.of_forall fun _ h => absurd hi h
    · exact (eventually_nhdsWithin_of_eventually_nhds
        (eventually_le_nhds (norm_pos_iff.2 hi))).mono fun _ h _ => h
  obtain ⟨ε, hε, hεε₀, hεc⟩ := (h1.and (h2.and h3)).exists
  set H := affineHomeo c ε hε.ne' with hH
  let ψ : OpenPartialHomeomorph X (Fin e → ℂ) := ψ'.trans H.toOpenPartialHomeomorph
  let σ : Fin m → Option (Fin e) := fun k => (σ' k).bind fun i => if c i = 0 then some i else none
  have hσ : ∀ k i, σ k = some i ↔ σ' k = some i ∧ c i = 0 := by
    intro k i
    simp only [σ]
    cases h : σ' k with
    | none => simp
    | some j =>
      simp only [Option.bind_some]
      split_ifs with hj
      · constructor
        · intro h'; cases h'; exact ⟨rfl, hj⟩
        · rintro ⟨h', -⟩; exact h'
      · constructor
        · intro h'; cases h'
        · rintro ⟨h', h''⟩; cases h'; exact absurd h'' hj
  have hsrc : ψ.source = ψ'.source := by
    simp [ψ, OpenPartialHomeomorph.trans_source]
  have htgt : ∀ z, z ∈ ψ.target ↔ H.symm z ∈ ψ'.target := by
    intro z
    simp [ψ, OpenPartialHomeomorph.trans_target]
  have hsymm : ∀ z, ψ.symm z = ψ'.symm (H.symm z) := by
    intro z; rfl
  have hHs : ∀ z, H.symm z = c + (ε : ℂ) • z := fun z => rfl
  have hin : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) 1, H.symm z ∈ ψ'.target := by
    intro z hz
    apply hball
    rw [hHs, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    rw [mem_ball_zero_iff] at hz
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    calc ε * ‖z‖ < ε * 1 := mul_lt_mul_of_pos_left hz hε
      _ = ε := mul_one ε
      _ ≤ ε₀ := hεε₀
  refine ⟨ψ, σ, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    constructor
    · have hset : (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source
          = (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ'.source := by rw [hsrc]
      rw [hset]
      have := (affineHomeo_analytic c ε hε.ne').comp (hψ' j).1 (Set.mapsTo_univ _ _)
      exact this
    · exact (hψ' j).2.comp ((affineHomeo_symm_analytic c ε hε.ne').mono (Set.subset_univ _))
        (fun z hz => ⟨(htgt z).1 hz.1, by simpa [hsymm] using hz.2⟩)
  · intro z hz
    exact (htgt z).2 (hin z hz)
  · intro i i' k hi hi'
    exact hσ' i i' k ((hσ i k).1 hi).1 ((hσ i' k).1 hi').1
  · intro z hz k
    have hzt := hin z hz
    have hys : ψ'.symm (H.symm z) ∈ ψ'.source := ψ'.map_target hzt
    have hyy : ψ' (ψ'.symm (H.symm z)) = H.symm z := ψ'.right_inv hzt
    rw [hsymm]
    have key : ψ'.symm (H.symm z) ∈ D k ↔ ∃ i, σ' k = some i ∧ (c + (ε : ℂ) • z) i = 0 := by
      have := Set.ext_iff.1 (hD k) (ψ'.symm (H.symm z))
      rw [hHs] at this hys hyy ⊢
      simpa only [Set.mem_inter_iff, Set.mem_setOf_eq, hys, and_true, true_and, hyy] using this
    rw [key]
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    constructor
    · rintro ⟨i, hi, hzero⟩
      have hzero' : c i + (ε : ℂ) * z i = 0 := by simpa using hzero
      by_cases hci : c i = 0
      · refine ⟨i, (hσ k i).2 ⟨hi, hci⟩, ?_⟩
        rw [hci, zero_add] at hzero'
        have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
        exact (mul_eq_zero.1 hzero').resolve_left this
      · exfalso
        have hle := hεc i hci
        have heq : c i = -((ε : ℂ) * z i) := eq_neg_of_add_eq_zero_left hzero'
        have hnorm : ‖c i‖ = ε * ‖z i‖ := by
          rw [heq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
        have hzi : ‖z i‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm z i) hz1
        have : ε * ‖z i‖ < ε := by nlinarith [norm_nonneg (z i)]
        linarith
    · rintro ⟨i, hi, hzi⟩
      obtain ⟨hi', hci⟩ := (hσ k i).1 hi
      exact ⟨i, hi', by simp [hci, hzi]⟩
  · rw [hsrc]; exact hx
  · show H (ψ' x) = 0
    show ((ε : ℂ)⁻¹) • (ψ' x - c) = 0
    rw [hc, sub_self, smul_zero]

/- English proof (translation)
Introduce `e X _ A m L s D hB x`. Consider the cases of `m with`. Consider the case `zero`. Take `⟨j, hj⟩` from `A.cover x`. Conclude with `exists_adapted_of_chart A D (A.chart j) (fun k => ⟨A.holo k j, A.holo j k⟩) x hj (fun k => Fin.elim0 k) (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)`.

Consider the case `succ n`. Take `⟨-, -, hsnc, -⟩` from `hB 0`. Take `⟨ψ', hc, hx, -, σ', hσ', hD, -⟩` from `hsnc x`. Conclude with `exists_adapted_of_chart A D ψ' hc x hx σ' hσ' hD`.
-/
theorem exists_adaptedPolydisc_centred :
    ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ} (L : Fin m → LocPot X)
      (s : Fin m → X → X → ℂ) (D : Fin m → Set X), IsBoundary A L s D → ∀ x : X,
      ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)),
        IsAdaptedPolydisc A D ψ σ ∧ x ∈ ψ.source ∧ ψ x = 0 := by
  intro e X _ A m L s D hB x
  cases m with
  | zero =>
    obtain ⟨j, hj⟩ := A.cover x
    exact exists_adapted_of_chart A D (A.chart j) (fun k => ⟨A.holo k j, A.holo j k⟩) x hj
      (fun k => Fin.elim0 k) (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)
  | succ n =>
    obtain ⟨-, -, hsnc, -⟩ := hB 0
    obtain ⟨ψ', hc, hx, -, σ', hσ', hD, -⟩ := hsnc x
    exact exists_adapted_of_chart A D ψ' hc x hx σ' hσ' hD

end

end GlobalTheory.AdaptedCover
