import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMulIsIntegralChart
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model

/- English proof (translation)
Establish `hmem : (⇑(b.repr v) : Fin N → K) ∈ Submodule.span K (Set.range g.col)`. Rewrite using `[hg]`. Conclude with `Submodule.mem_top`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hmem`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Establish `hv : v = ∑ k, c k • ∑ j, g j k • b j` using `by conv_lhs => rw [← b.sum_repr v]`. Rewrite using `[← hc]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Both sides reduce to the same expression.

Rewrite using `[hv]`. Simplify using `only [map_sum, map_smul, Algebra.smul_def]`.
-/
theorem exists_comb {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {N m : ℕ} (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) (v : V) :
    ∃ c : Fin m → K, ev v = ∑ k, algebraMap K Ω (c k) * ev (∑ j, g j k • b j) := by
  have hmem : (⇑(b.repr v) : Fin N → K) ∈ Submodule.span K (Set.range g.col) := by
    rw [hg]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  refine ⟨c, ?_⟩
  have hv : v = ∑ k, c k • ∑ j, g j k • b j := by
    conv_lhs => rw [← b.sum_repr v]
    rw [← hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    rfl
  rw [hv]
  simp only [map_sum, map_smul, Algebra.smul_def]

/- English proof (translation)
Use `set F := Subfield.closure (Set.range (algebraMap (𝓞 K) Ω) ∪ {x | ∃ i j, x = t j / t i}) with hF`. Establish `hK : ∀ x : K, algebraMap K Ω x ∈ F`. Introduce `x`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) x`. Rewrite using `[map_div₀]`.

Establish `e : ∀ y : 𝓞 K, algebraMap K Ω (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) Ω y` using `fun y => (IsScalarTower.algebraMap_apply (𝓞 K) K Ω y).symm`. Rewrite using `[e, e]`. Conclude with `div_mem (Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) (Subfield.subset_closure (Or.inl ⟨b, rfl⟩))`. Establish `key : ∀ u, ev u / t i ∈ F`. Introduce `u`.

Take `⟨c, hc⟩` from `ht u`. Rewrite using `[hc, Finset.sum_div]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_div_assoc]`. Conclude with `mul_mem (hK (c k)) (Subfield.subset_closure (Or.inr ⟨i, k, rfl⟩))`.

Establish `hS : {a : Ω | ∃ v w, a = ev v / ev w} ⊆ (F.toIntermediateField hK : Set Ω)`. Introduce and unpack `_ ⟨v, w, rfl⟩`. Use `show ev v / ev w ∈ F`. Rewrite using `[← div_div_div_cancel_right₀ hi (ev v) (ev w)]`. Conclude with `div_mem (key v) (key w)`.

Establish `hle` using `(IntermediateField.adjoin_le_iff).2 hS`. Rewrite `hle` using `[hr]`. Conclude with `eq_top_iff.2 fun x _ => hle (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField K Ω))`.
-/
theorem closure_eq_top {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {m : ℕ} (t : Fin m → Ω)
    (ht : ∀ v, ∃ c : Fin m → K, ev v = ∑ k, algebraMap K Ω (c k) * t k) (i : Fin m) (hi : t i ≠ 0)
    (hr : IntermediateField.adjoin K {a : Ω | ∃ v w, a = ev v / ev w} = ⊤) :
    Subfield.closure (Set.range (algebraMap (𝓞 K) Ω) ∪ {x | ∃ i j, x = t j / t i}) = ⊤ := by
  set F := Subfield.closure (Set.range (algebraMap (𝓞 K) Ω) ∪ {x | ∃ i j, x = t j / t i}) with hF
  have hK : ∀ x : K, algebraMap K Ω x ∈ F := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    rw [map_div₀]
    have e : ∀ y : 𝓞 K, algebraMap K Ω (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) Ω y :=
      fun y => (IsScalarTower.algebraMap_apply (𝓞 K) K Ω y).symm
    rw [e, e]
    exact div_mem (Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) (Subfield.subset_closure (Or.inl ⟨b, rfl⟩))
  have key : ∀ u, ev u / t i ∈ F := by
    intro u
    obtain ⟨c, hc⟩ := ht u
    rw [hc, Finset.sum_div]
    refine sum_mem fun k _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (hK (c k)) (Subfield.subset_closure (Or.inr ⟨i, k, rfl⟩))
  have hS : {a : Ω | ∃ v w, a = ev v / ev w} ⊆ (F.toIntermediateField hK : Set Ω) := by
    rintro _ ⟨v, w, rfl⟩
    show ev v / ev w ∈ F
    rw [← div_div_div_cancel_right₀ hi (ev v) (ev w)]
    exact div_mem (key v) (key w)
  have hle := (IntermediateField.adjoin_le_iff).2 hS
  rw [hr] at hle
  exact eq_top_iff.2 fun x _ => hle (IntermediateField.mem_top : x ∈ (⊤ : IntermediateField K Ω))

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_model
