import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversalStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

namespace GlobalTheory.DefU.EquivWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `h1` using `(Subgroup.mem_inf.1 hx).2`. Rewrite `h1` using `[Subgroup.mem_iInf]`. Establish `h2` using `h1 τ'`. Rewrite `h2` using `[Subgroup.mem_iInf]`. Conclude with `h2 h`.
-/
theorem cEmb_eq_one_of_mem_embU {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) {x : UA E n}
    (hx : x ∈ embU n τ) : cEmb τ' x = 1 := by
  have h1 := (Subgroup.mem_inf.1 hx).2
  rw [Subgroup.mem_iInf] at h1
  have h2 := h1 τ'
  rw [Subgroup.mem_iInf] at h2
  exact h2 h

/- English proof (translation)
Rewrite using `[rhoK_tenMul]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Distinguish the cases in `h : τ = τ₀`. Substitute `h` using the available equality.

Simplify using `only [Function.update_self]`. Both sides reduce to the same expression. Establish `hne : InfinitePlace.mk (σ τ) ≠ InfinitePlace.mk (σ τ₀)` using `fun e' => h (hσ e')`. Simplify using `only [Function.update_of_ne h, MonoidHom.pi_apply, cEmb_eq_one_of_mem_embU hne hx, map_one, Module.End.one_apply]`.
-/
theorem rhoK_tenMul_update {ι : Type} [Fintype ι] [DecidableEq ι] (σ : ι → (E →+* ℂ)) (lam : ι → DomWeight n)
    (hσ : Function.Injective (fun τ => InfinitePlace.mk (σ τ))) (τ₀ : ι) {x : UA E n} (hx : x ∈ embU n (σ τ₀))
    (e : ∀ τ, nablaSq ℂ n (lam τ)) (a : nablaSq ℂ n (lam τ₀)) :
    Formalism.L2.DIV.rhoK (K := ℂ) lam ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)) x)
              (GlobalTheory.CoefIrred.tenMul lam (Function.update e τ₀ a)) =
      GlobalTheory.CoefIrred.tenMul lam (Function.update e τ₀ (GlobalTheory.Branching.sqRep ℂ n (lam τ₀) (cEmb (σ τ₀) x) a)) := by
  rw [rhoK_tenMul]
  congr 1
  funext τ
  by_cases h : τ = τ₀
  · subst h
    simp only [Function.update_self]
    rfl
  · have hne : InfinitePlace.mk (σ τ) ≠ InfinitePlace.mk (σ τ₀) := fun e' => h (hσ e')
    simp only [Function.update_of_ne h, MonoidHom.pi_apply, cEmb_eq_one_of_mem_embU hne hx, map_one,
      Module.End.one_apply]

/- English proof (translation)
Introduce `E _ _ _ n ι _ σ lam hσ π hπ f hf0 hfπ hfeq τ₀`. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e, f (GlobalTheory.CoefIrred.tenMul lam e) ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h1` using `(GlobalTheory.T.dualWeylModule_tensor_coefficient_universal ι n lam (UA E n → ℂ) 0).unique (y₁ := f) (y₂ := 0) (fun u => hc u) (fun u => rfl)`.

Conclude with `hf0 h1`. Establish `h1 : HasWeightAt π (σ τ₀) (lam τ₀)`. Use `⟨isIrreducible_sqRep n (lam τ₀), f ∘ₗ (GlobalTheory.CoefIrred.tenMul lam).toLinearMap e τ₀, fun h0 => he ?_, fun a => hfπ _, fun x a => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun h0 (e τ₀)` as an intermediate fact. Simplify `this` using `[MultilinearMap.toLinearMap]`.

Establish `hx : x.1 ∈ infU E n` using `embU_le_infU _ x.2`. Establish `h2` using `hfeq ⟨x.1, hx⟩ (GlobalTheory.CoefIrred.tenMul lam (Function.update e τ₀ a))`. Express the relevant statement in the definitionally equal form `f (Formalism.L2.DIV.rhoK (K := ℂ) lam ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)) x.1) _) = _ at h2`. Rewrite `h2` using `[rhoK_tenMul_update σ lam hσ τ₀ x.2]`. Conclude with `h2`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `h3 : (AU.mk (⟨π, hπ⟩ : AutSub E n)).HasWt (σ τ₀) (lam τ₀)` using `(AU.hasWt_mk _ _ _).2 h1`. Conclude with `(AU.hasWt_mk _ _ _).1 h3.conjugate`.
-/
theorem hasWeightAt_of_equivariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι]
    (σ : ι → (E →+* ℂ)) (lam : ι → DomWeight n), Function.Injective (fun τ => InfinitePlace.mk (σ τ)) →
    ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] (UA E n → ℂ)), f ≠ 0 →
    (∀ v, f v ∈ π) → (∀ (x : infU E n) v, f (((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp
      ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)).comp (infU E n).subtype)) x v) = RU E n x (f v)) →
    ∀ τ, HasWeightAt π (σ τ) (lam τ) ∧ HasWeightAt π (ComplexEmbedding.conjugate (σ τ)) (lam τ).dual := by
  intro E _ _ _ n ι _ σ lam hσ π hπ f hf0 hfπ hfeq τ₀
  classical
  obtain ⟨e, he⟩ : ∃ e, f (GlobalTheory.CoefIrred.tenMul lam e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h1 := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal ι n lam (UA E n → ℂ) 0).unique (y₁ := f) (y₂ := 0)
      (fun u => hc u) (fun u => rfl)
    exact hf0 h1
  have h1 : HasWeightAt π (σ τ₀) (lam τ₀) := by
    refine ⟨isIrreducible_sqRep n (lam τ₀), f ∘ₗ (GlobalTheory.CoefIrred.tenMul lam).toLinearMap e τ₀, fun h0 => he ?_,
      fun a => hfπ _, fun x a => ?_⟩
    · have := LinearMap.congr_fun h0 (e τ₀)
      simpa [MultilinearMap.toLinearMap] using this
    · have hx : x.1 ∈ infU E n := embU_le_infU _ x.2
      have h2 := hfeq ⟨x.1, hx⟩ (GlobalTheory.CoefIrred.tenMul lam (Function.update e τ₀ a))
      change f (Formalism.L2.DIV.rhoK (K := ℂ) lam ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)) x.1) _) = _ at h2
      rw [rhoK_tenMul_update σ lam hσ τ₀ x.2] at h2
      exact h2
  refine ⟨h1, ?_⟩
  have h3 : (AU.mk (⟨π, hπ⟩ : AutSub E n)).HasWt (σ τ₀) (lam τ₀) := (AU.hasWt_mk _ _ _).2 h1
  exact (AU.hasWt_mk _ _ _).1 h3.conjugate

end GlobalTheory.DefU.EquivWt

end
