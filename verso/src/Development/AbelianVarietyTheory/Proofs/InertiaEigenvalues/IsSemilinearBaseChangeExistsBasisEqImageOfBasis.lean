import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.Prism

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem semiBC_basis (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M]
    [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (h : SemiBC u)
    (ι : Type) (e : Module.Basis ι A M) : ∃ b : Module.Basis ι B N, ∀ i, b i = u (e i) := by
  classical
  let g : (ι →₀ B) →ₗ[B] N := Finsupp.linearCombination B (fun i => u (e i))
  let v : M →ₛₗ[f] (ι →₀ B) :=
    { toFun := fun x => Finsupp.mapRange f f.map_zero (e.repr x)
      map_add' := fun x y => by
        ext i; simp
      map_smul' := fun a x => by
        ext i; simp }
  obtain ⟨w, hw, -⟩ := h (ι →₀ B) v
  have key : ∀ x : M, g (v x) = u x := by
    intro x
    conv_rhs => rw [← e.linearCombination_repr x]
    simp only [g, v, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (fun i => by simp), map_finsuppSum]
    refine Finsupp.sum_congr (fun i _ => ?_)
    simp
  have h1 : w.comp g = LinearMap.id := by
    ext i
    simp [g, hw, v]
  have h2 : g.comp w = LinearMap.id := by
    obtain ⟨w0, -, huniq⟩ := h N u
    have a1 := huniq (g.comp w) (fun x => by simp [hw, key])
    have a2 := huniq LinearMap.id (fun x => rfl)
    rw [a1, a2]
  let E : N ≃ₗ[B] (ι →₀ B) := LinearEquiv.ofLinear w g h1 h2
  refine ⟨Module.Basis.ofRepr E, fun i => ?_⟩
  simp [Module.Basis.ofRepr, E, g]

end GlobalTheory.Prism
