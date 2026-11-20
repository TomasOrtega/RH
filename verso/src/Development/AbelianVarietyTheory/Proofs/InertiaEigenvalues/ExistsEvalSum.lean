import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.KFinExp

/- English proof (translation)
Set `ev : GA E N → Module.Dual ℂ W` to `fun x => (LinearMap.proj x : (GA E N → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (Sm E N).subtype ∘ₗ W.subtype`. Establish `hs : Submodule.span ℂ (Set.range ev) = ⊤` using `Submodule.span_eq_top_of_ne_zero fun z hz => by`. Assume the negation of the conclusion as `h`. Use `hz (Subtype.ext (Subtype.ext (funext fun x => ?_)))` and prove the remaining obligations. Assume the negation of the conclusion as `hx`.

Conclude with `h ⟨ev x, ⟨x, rfl⟩, hx⟩`. Take `⟨a, ha⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 (hs ▸ Submodule.mem_top : l ∈ _)`. Use `⟨a, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, Finsupp.sum, LinearMap.sum_apply]`. Both sides reduce to the same expression.
-/
theorem exists_eval_sum {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    (W : Submodule ℂ (Sm E N)) [FiniteDimensional ℂ W] (l : Module.Dual ℂ W) :
    ∃ a : GA E N →₀ ℂ, ∀ w : W, l w = ∑ x ∈ a.support, a x * w.1.1 x := by
  let ev : GA E N → Module.Dual ℂ W := fun x =>
    (LinearMap.proj x : (GA E N → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (Sm E N).subtype ∘ₗ W.subtype
  have hs : Submodule.span ℂ (Set.range ev) = ⊤ := Submodule.span_eq_top_of_ne_zero fun z hz => by
    by_contra h
    refine hz (Subtype.ext (Subtype.ext (funext fun x => ?_)))
    by_contra hx
    exact h ⟨ev x, ⟨x, rfl⟩, hx⟩
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hs ▸ Submodule.mem_top : l ∈ _)
  refine ⟨a, fun w => ?_⟩
  rw [← ha, Finsupp.sum, LinearMap.sum_apply]
  rfl

/- English proof (translation)
Use `set W := Submodule.span ℂ (Set.range fun k => cptRep E N k φ)`. Establish `hf : FiniteDimensional ℂ W` using `hφ`. Set `b` to `Module.finBasis ℂ W`. Use `choose a ha using fun j => exists_eval_sum W (b.coord j)`. Use `⟨_, fun j => (b j).1, fun j y => ∑ x ∈ (a j).support, a j x * chart φ.1 x y, fun j => (b j).2, fun j => ContDiffAt.sum fun x _ => contDiffAt_const.mul (contDiffAt_chart φ.2 x isUnit_one), fun k => ?_⟩` and prove the remaining obligations.

Set `w : W` to `⟨cptRep E N k φ, Submodule.subset_span ⟨k, rfl⟩⟩`. Establish `h` using `congrArg Subtype.val (b.sum_repr w)`. Rewrite `h` using `[Submodule.coe_sum]`. Use `h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul]`.

Use `congr 1`. Use `(ha j w).trans (Finset.sum_congr rfl fun x _ => ?_)` and prove the remaining obligations. Use `congr 1`. Conclude with `(chart_val φ.1 x (Unitary.toUnits k)).symm`.
-/
theorem exists_expansion (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (φ : Sm E N)
    (hφ : φ ∈ finVec (cptRep E N)) :
    ∃ (r : ℕ) (ψ : Fin r → Sm E N) (C : Fin r → Lie E N → ℂ),
      (∀ j, ψ j ∈ Submodule.span ℂ (Set.range fun k => cptRep E N k φ)) ∧
      (∀ j, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (C j) (oneL E N)) ∧
      ∀ k : Kinf E N, cptRep E N k φ = ∑ j, C j (toL k.1) • ψ j := by
  set W := Submodule.span ℂ (Set.range fun k => cptRep E N k φ)
  have hf : FiniteDimensional ℂ W := hφ
  let b := Module.finBasis ℂ W
  choose a ha using fun j => exists_eval_sum W (b.coord j)
  refine ⟨_, fun j => (b j).1, fun j y => ∑ x ∈ (a j).support, a j x * chart φ.1 x y, fun j => (b j).2,
    fun j => ContDiffAt.sum fun x _ => contDiffAt_const.mul (contDiffAt_chart φ.2 x isUnit_one), fun k => ?_⟩
  let w : W := ⟨cptRep E N k φ, Submodule.subset_span ⟨k, rfl⟩⟩
  have h := congrArg Subtype.val (b.sum_repr w)
  rw [Submodule.coe_sum] at h
  refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Submodule.coe_smul]
  congr 1
  refine (ha j w).trans (Finset.sum_congr rfl fun x _ => ?_)
  congr 1
  exact (chart_val φ.1 x (Unitary.toUnits k)).symm

end GlobalTheory.KFinExp
