import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAvgClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerKAvgNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRankStatement

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

/- English proof (translation)
Introduce `n ε H _ _ _ σ h a ha v hv`. Take `⟨a1, a2, a3, a4, a5⟩` from `isAvg_closure n ε H σ h.1`. Take `⟨c1, c2, c3, c4⟩` from `kCoef_kAvg n ε H σ h.1`. Set `A : Submodule ℂ H` to `{ carrier := {x | ∃ T : H → H, IsAvg ε σ T ∧ T a = x} add_mem' := by`. Introduce and unpack `_ _ ⟨T, hT, rfl⟩ ⟨T', hT', rfl⟩`.

Conclude with `⟨_, (a2 T T' hT hT').1, rfl⟩`. Use the proof step `zero_mem' := ⟨_, a5, rfl⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨T, hT, rfl⟩`. Conclude with `⟨_, a3 c T hT, rfl⟩ }`.

Establish `hA : ∀ T : H → H, IsAvg ε σ T → ∀ x ∈ A, T x ∈ A`. Introduce and unpack `T hT _ ⟨T', hT', rfl⟩`. Conclude with `⟨_, (a2 T T' hT hT').2, rfl⟩`. Establish `haA : a ∈ A` using `⟨_, a1 1 (one_mem_UJ ε), sigma_one h.1 a⟩`. Establish `hdense : Dense (A : Set H)` using `dense_of_irred h.2.1 (fun g hg x hx => hA _ (a1 g hg) x hx) ((Submodule.ne_bot_iff _).2 ⟨a, haA, ha⟩)`.

Establish `hrange : ∀ e : KG ε → ℂ, KFinFun ε e → Continuous e → ∀ w, kAvg ε σ e w ∈ A`. Introduce `e he hc w`. Take `⟨m, b, c, -, -, -, hbc⟩` from `GlobalTheory.T.compactAverage_kFinite_finiteRank n ε H σ h e he`. Take `⟨Q, hQ⟩` from `c3 e hc`. Set `F : Submodule ℂ H` to `Submodule.span ℂ (Set.range b)`.

Use `haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)`. Use `haveI : FiniteDimensional ℂ (A ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_inf_right A F`. Establish `hcl : IsClosed (Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H))` using `(Submodule.closed_of_finiteDimensional _).preimage Q.continuous`. Establish `hsub : (A : Set H) ⊆ Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H)`. Introduce `x hx`.

Use `Submodule.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hQ]`. Conclude with `hA _ (a4 e hc) x hx`. Rewrite using `[hQ, hbc]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.

Use `closure_minimal hsub hcl (hdense w)` as an intermediate fact. Rewrite using `[← hQ]`. Conclude with `(Submodule.mem_inf.1 this).1`. Take `⟨S, hS, hvS, hK⟩` from `hv`. Use `haveI : FiniteDimensional ℂ (S ⊓ A : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S A`.

Take `⟨w, hw, y, hy, hvwy⟩` from `(S ⊓ A).exists_add_mem_mem_orthogonal v`. Establish `hyS : y ∈ S`. Use `S.sub_mem hvS (Submodule.mem_inf.1 hw).1` as an intermediate fact. Rewrite `this` using `[hvwy, add_sub_cancel_left]`. Then use the resulting hypothesis. Establish `hy0 : y = 0`.

Assume the negation of the conclusion as `hy0`. Establish `hk` using `c1 y ⟨S, hS, hyS, hK⟩`. Establish `hc : Continuous fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ`. Take `⟨F, -, h1, h2, -⟩` from `hk`. Conclude with `h2 _ h1`.

Conclude with `c2 y hy0 (Submodule.inner_left_of_mem_orthogonal (Submodule.mem_inf.2 ⟨c4 _ hc S hS hK y hyS, hrange _ hk hc y⟩) hy)`. Rewrite using `[hvwy, hy0, add_zero]`. Conclude with `(Submodule.mem_inf.1 hw).2`.
-/
theorem exists_isAvg_apply_eq : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ a : H, a ≠ 0 → ∀ v, IsKFin ε σ v → ∃ T : H → H, IsAvg ε σ T ∧ T a = v := by
  intro n ε H _ _ _ σ h a ha v hv
  obtain ⟨a1, a2, a3, a4, a5⟩ := isAvg_closure n ε H σ h.1
  obtain ⟨c1, c2, c3, c4⟩ := kCoef_kAvg n ε H σ h.1
  let A : Submodule ℂ H :=
    { carrier := {x | ∃ T : H → H, IsAvg ε σ T ∧ T a = x}
      add_mem' := by
        rintro _ _ ⟨T, hT, rfl⟩ ⟨T', hT', rfl⟩
        exact ⟨_, (a2 T T' hT hT').1, rfl⟩
      zero_mem' := ⟨_, a5, rfl⟩
      smul_mem' := by
        rintro c _ ⟨T, hT, rfl⟩
        exact ⟨_, a3 c T hT, rfl⟩ }
  have hA : ∀ T : H → H, IsAvg ε σ T → ∀ x ∈ A, T x ∈ A := by
    rintro T hT _ ⟨T', hT', rfl⟩
    exact ⟨_, (a2 T T' hT hT').2, rfl⟩
  have haA : a ∈ A := ⟨_, a1 1 (one_mem_UJ ε), sigma_one h.1 a⟩
  have hdense : Dense (A : Set H) :=
    dense_of_irred h.2.1 (fun g hg x hx => hA _ (a1 g hg) x hx) ((Submodule.ne_bot_iff _).2 ⟨a, haA, ha⟩)
  have hrange : ∀ e : KG ε → ℂ, KFinFun ε e → Continuous e → ∀ w, kAvg ε σ e w ∈ A := by
    intro e he hc w
    obtain ⟨m, b, c, -, -, -, hbc⟩ := GlobalTheory.T.compactAverage_kFinite_finiteRank n ε H σ h e he
    obtain ⟨Q, hQ⟩ := c3 e hc
    let F : Submodule ℂ H := Submodule.span ℂ (Set.range b)
    haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
    haveI : FiniteDimensional ℂ (A ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_inf_right A F
    have hcl : IsClosed (Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H)) :=
      (Submodule.closed_of_finiteDimensional _).preimage Q.continuous
    have hsub : (A : Set H) ⊆ Q ⁻¹' ((A ⊓ F : Submodule ℂ H) : Set H) := by
      intro x hx
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hQ]; exact hA _ (a4 e hc) x hx
      · rw [hQ, hbc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := closure_minimal hsub hcl (hdense w)
    rw [← hQ]
    exact (Submodule.mem_inf.1 this).1
  obtain ⟨S, hS, hvS, hK⟩ := hv
  haveI : FiniteDimensional ℂ (S ⊓ A : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S A
  obtain ⟨w, hw, y, hy, hvwy⟩ := (S ⊓ A).exists_add_mem_mem_orthogonal v
  have hyS : y ∈ S := by
    have := S.sub_mem hvS (Submodule.mem_inf.1 hw).1
    rwa [hvwy, add_sub_cancel_left] at this
  have hy0 : y = 0 := by
    by_contra hy0
    have hk := c1 y ⟨S, hS, hyS, hK⟩
    have hc : Continuous fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ := by
      obtain ⟨F, -, h1, h2, -⟩ := hk
      exact h2 _ h1
    exact c2 y hy0 (Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_inf.2 ⟨c4 _ hc S hS hK y hyS, hrange _ hk hc y⟩) hy)
  rw [hvwy, hy0, add_zero]
  exact (Submodule.mem_inf.1 hw).2

end GlobalTheory.TypeSum

end
