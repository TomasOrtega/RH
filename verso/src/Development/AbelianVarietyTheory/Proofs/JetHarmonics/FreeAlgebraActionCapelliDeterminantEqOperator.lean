import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliFreeAction

/- English proof (translation)
Unfold `Formalism.REAL.qdet Formalism.REAL.qminor`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_intCast, map_list_prod, List.map_ofFn]`. Use `congr 3`.

Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp, Formalism.REAL.Tm]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}
    (φ : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp, Formalism.REAL.Tm]
  split_ifs <;> simp

/- English proof (translation)
Introduce `n ε H _ _ σ S E hE u v`. Set `F : FreeMonoid (Fin n × Fin n) →* Module.End ℂ S` to `FreeMonoid.lift fun ab => E ab.1 ab.2`. Set `ψ : MonoidAlgebra ℂ (FreeMonoid (Fin n × Fin n)) →ₐ[ℂ] Module.End ℂ S` to `MonoidAlgebra.lift ℂ _ _ F`. Set `φ : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ S` to `ψ.comp (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℂ (Fin n × Fin n) ≃ₐ[ℂ] _).toAlgHom`. Establish `hw : ∀ l : List (Fin n × Fin n), PI.DSInfCharCap.dsigCW ε σ (l.map PI.DSInfCharCap.unitM) (v : H) = ((F (FreeMonoid.ofList l) v : S) : H)`.

Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => simp [PI.DSInfCharCap.dsigCW]`. Consider the case `cons a l ih`. Rewrite using `[List.map_cons, PI.DSInfCharCap.dsigCW, ih, FreeMonoid.ofList_cons, map_mul, Module.End.mul_apply, ← hE a.1 a.2]`.

Simplify using `[F]`. Establish `hφ : ∀ p, PI.DSInfCharCap.actU ε σ p v = ((φ p v : S) : H)`. Introduce `p`. Establish `: φ p = ψ (FreeAlgebra.equivMonoidAlgebraFreeMonoid p)` using `rfl`. Rewrite using `[this]`.

Simplify using `only [ψ, MonoidAlgebra.lift_apply, PI.DSInfCharCap.actU, Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[hw]`. Both sides reduce to the same expression. Establish `hE' : (fun a b => φ (PI.DSInfCharCap.Egl n a b)) = E`.

Use function extensionality and compare the values at `a b`. Simplify using `[φ, ψ, F, PI.DSInfCharCap.Egl, FreeAlgebra.equivMonoidAlgebraFreeMonoid]`. Rewrite using `[hφ, map_qdet, hE']`.
-/
theorem actU_qdet : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S), (∀ a b (v : S), ((E a b v : S) : H) = PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM (a, b)) v) → ∀ (u : ℂ) (v : S), PI.DSInfCharCap.actU ε σ (Formalism.REAL.qdet (PI.DSInfCharCap.Egl n) u) v = ((Formalism.REAL.qdet E u v : S) : H) := by
  intro n ε H _ _ σ S E hE u v
  let F : FreeMonoid (Fin n × Fin n) →* Module.End ℂ S := FreeMonoid.lift fun ab => E ab.1 ab.2
  let ψ : MonoidAlgebra ℂ (FreeMonoid (Fin n × Fin n)) →ₐ[ℂ] Module.End ℂ S :=
    MonoidAlgebra.lift ℂ _ _ F
  let φ : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ S :=
    ψ.comp (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℂ (Fin n × Fin n) ≃ₐ[ℂ] _).toAlgHom
  have hw : ∀ l : List (Fin n × Fin n),
      PI.DSInfCharCap.dsigCW ε σ (l.map PI.DSInfCharCap.unitM) (v : H) =
        ((F (FreeMonoid.ofList l) v : S) : H) := by
    intro l
    induction l with
    | nil => simp [PI.DSInfCharCap.dsigCW]
    | cons a l ih =>
      rw [List.map_cons, PI.DSInfCharCap.dsigCW, ih, FreeMonoid.ofList_cons, map_mul,
        Module.End.mul_apply, ← hE a.1 a.2]
      simp [F]
  have hφ : ∀ p, PI.DSInfCharCap.actU ε σ p v = ((φ p v : S) : H) := by
    intro p
    have : φ p = ψ (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) := rfl
    rw [this]
    simp only [ψ, MonoidAlgebra.lift_apply, PI.DSInfCharCap.actU, Finsupp.sum,
      LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hw]
    rfl
  have hE' : (fun a b => φ (PI.DSInfCharCap.Egl n a b)) = E := by
    funext a b
    simp [φ, ψ, F, PI.DSInfCharCap.Egl, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [hφ, map_qdet, hE']

end GlobalTheory.CapelliFreeAction
