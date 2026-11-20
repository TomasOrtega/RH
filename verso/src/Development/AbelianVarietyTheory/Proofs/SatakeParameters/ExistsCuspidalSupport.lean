import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.CuspidalSupportZero

/- English proof (translation)
Use `haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩`. Set `d : Fin 0 → ℕ` to `fun a => a.elim0`. Set `σ : ∀ a, Irr k (d a)` to `fun a => a.elim0`. Use `⟨0, d, σ, π.irr, fun a => a.elim0, ?_⟩` and prove the remaining obligations. Set `e : (Σ a, Fin (d a)) ≃ Fin 0` to `Equiv.equivOfIsEmpty _ _`.

Use `⟨e, ?_⟩` and prove the remaining obligations. Take `⟨φ⟩` from `GlobalTheory.LocGL.SupportRing.nonempty_equiv_unit (k := k) e (fun a => (σ a).π)`. Establish `hirr` using `π.irr`. Choose the witnesses or unpack the hypotheses as in `⟨v₀, hv₀⟩ : ∃ v : π.V, v ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `(bot_ne_top : (⊥ : Subrepresentation π.π) ≠ ⊤)` to reduce the goal to its premises. Use extensionality with `v`. Simplify using `[h v]`. Set `L : Subrepresentation π.π` to `⟨ℂ ∙ v₀, fun g v hv => by`.

Rewrite using `[Subsingleton.elim g 1, map_one]`. Conclude with `hv⟩`. Establish `hL : L = ⊤`. Break down `eq_bot_or_eq_top L with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `: v₀ ∈ L.toSubmodule` using `Submodule.mem_span_singleton_self v₀`. Rewrite `this` using `[h]`. Conclude with `hv₀ ((Submodule.mem_bot ℂ).1 this)`. Conclude with `h`. Set `f : (multiProd e fun a => (σ a).π).IntertwiningMap π.π` to `{ toLinearMap := (LinearMap.toSpanSingleton ℂ π.V v₀) ∘ₗ φ.toLinearEquiv.toLinearMap isIntertwining' := fun g => by`.

Rewrite using `[Subsingleton.elim g 1, map_one, map_one]`. Use `rfl }`. Use `IsSubquotient.of_surjective f fun v => ?_` and prove the remaining obligations. Establish `hv : v ∈ L.toSubmodule` using `by rw [hL]; trivial`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hv`.

Use `⟨φ.toLinearEquiv.symm c, ?_⟩` and prove the remaining obligations. Use `show (LinearMap.toSpanSingleton ℂ π.V v₀) (φ.toLinearEquiv (φ.toLinearEquiv.symm c)) = c • v₀`. Use `erw [LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem exists_isCuspSupport_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (π : Irr k 0) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let d : Fin 0 → ℕ := fun a => a.elim0
  let σ : ∀ a, Irr k (d a) := fun a => a.elim0
  refine ⟨0, d, σ, π.irr, fun a => a.elim0, ?_⟩
  let e : (Σ a, Fin (d a)) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  refine ⟨e, ?_⟩
  obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportRing.nonempty_equiv_unit (k := k) e (fun a => (σ a).π)
  have hirr := π.irr

  obtain ⟨v₀, hv₀⟩ : ∃ v : π.V, v ≠ 0 := by
    by_contra h
    push_neg at h
    apply (bot_ne_top : (⊥ : Subrepresentation π.π) ≠ ⊤)
    ext v
    simp [h v]
  let L : Subrepresentation π.π := ⟨ℂ ∙ v₀, fun g v hv => by
    rw [Subsingleton.elim g 1, map_one]; exact hv⟩
  have hL : L = ⊤ := by
    rcases eq_bot_or_eq_top L with h | h
    · exfalso
      have : v₀ ∈ L.toSubmodule := Submodule.mem_span_singleton_self v₀
      rw [h] at this
      exact hv₀ ((Submodule.mem_bot ℂ).1 this)
    · exact h
  let f : (multiProd e fun a => (σ a).π).IntertwiningMap π.π :=
    { toLinearMap := (LinearMap.toSpanSingleton ℂ π.V v₀) ∘ₗ φ.toLinearEquiv.toLinearMap
      isIntertwining' := fun g => by
        rw [Subsingleton.elim g 1, map_one, map_one]; rfl }
  refine IsSubquotient.of_surjective f fun v => ?_
  have hv : v ∈ L.toSubmodule := by rw [hL]; trivial
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  refine ⟨φ.toLinearEquiv.symm c, ?_⟩
  show (LinearMap.toSpanSingleton ℂ π.V v₀) (φ.toLinearEquiv (φ.toLinearEquiv.symm c)) = c • v₀
  erw [LinearEquiv.apply_symm_apply]
  rfl

end GlobalTheory.CuspidalSupportZero
