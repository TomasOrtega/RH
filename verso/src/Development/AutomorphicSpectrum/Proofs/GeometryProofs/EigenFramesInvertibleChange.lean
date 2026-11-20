import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange

/- English proof (translation)
Introduce `S R _ _ G _ _ x O _ act σ n r u V hu hV`. Take `⟨E, _, _, ⟨M⟩⟩` from `lieModel_exists S G R x`. Take `⟨ρ, hρ, -⟩` from `lieModel_exists_unique_act S G R x E M O act.act act.hom act.one act.mul act.add`. Take `⟨hc, hf⟩` from `GlobalTheory.T.lie_model_eigenvectors_action S R G x E M`. Establish `hfr` using `(hf O act ρ σ hρ).2`.

Use `choose u' hu' using fun i => M.onto (u i) (hu.1 i).1`. Use `choose V' hV' using fun i => M.onto (V i) (hV.1 i).1`. Take `rfl : (fun k => M.pt (u' k)) = u` from `funext hu'`. Take `rfl : (fun k => M.pt (V' k)) = V` from `funext hV'`. Take `⟨lu, su⟩` from `(hfr n u').1 hu`.

Take `⟨lV, sV⟩` from `(hfr r V').1 hV`. Set `bu : Module.Basis (Fin n) R (eigSp ρ σ)` to `(Module.Basis.span lu).map (LinearEquiv.ofEq _ _ su)`. Set `bV : Module.Basis (Fin r) R (eigSp ρ σ)` to `(Module.Basis.span lV).map (LinearEquiv.ofEq _ _ sV)`. Establish `bu_eq : ∀ i, (bu i : E) = u' i` using `fun i => by`. Simplify using `[bu, Module.Basis.span_apply]`.

Establish `bV_eq : ∀ i, (bV i : E) = V' i` using `fun i => by`. Simplify using `[bV, Module.Basis.span_apply]`. Establish `hrn : r = n` using `by simpa using Fintype.card_congr (bV.indexEquiv bu)`. Use `⟨hrn, (bu.toMatrix bV).transpose, fun i => ?_, (bV.toMatrix bu).transpose, ?_, ?_⟩` and prove the remaining obligations. Use `(hc n _ u' _).2 ?_` and prove the remaining obligations.

Establish `h : V' i = ∑ k, (bu.toMatrix bV).transpose i k • u' k`. Establish `h` using `congrArg Subtype.val (bu.sum_repr (bV i))`. Rewrite `h` using `[bV_eq]`. Rewrite using `[← h]`. Use `clear h hc hf hfr hu hV hu' hV' hρ`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, bu_eq, Matrix.transpose_apply, Module.Basis.toMatrix_apply]`. Conclude with `congrArg M.pt h`. Rewrite using `[← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]`. Rewrite using `[← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]`.
-/
theorem eigFrame_change : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] [Nontrivial R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (O : Type) [CommRing O] (act : OAct O G) (σ : O →+* R) (n r : ℕ) (u : Fin n → (epsAt x ⟶ G)) (V : Fin r → (epsAt x ⟶ G)), IsEigFrame act x σ u → IsEigFrame act x σ V → r = n ∧ ∃ C : Matrix (Fin r) (Fin n) R, (∀ i, IsComb (C i) u (V i)) ∧ ∃ C' : Matrix (Fin n) (Fin r) R, C * C' = 1 ∧ C' * C = 1 := by
  intro S R _ _ G _ _ x O _ act σ n r u V hu hV
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G R x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G R x E M O act.act act.hom act.one act.mul act.add
  obtain ⟨hc, hf⟩ := GlobalTheory.T.lie_model_eigenvectors_action S R G x E M
  have hfr := (hf O act ρ σ hρ).2
  choose u' hu' using fun i => M.onto (u i) (hu.1 i).1
  choose V' hV' using fun i => M.onto (V i) (hV.1 i).1
  obtain rfl : (fun k => M.pt (u' k)) = u := funext hu'
  obtain rfl : (fun k => M.pt (V' k)) = V := funext hV'
  obtain ⟨lu, su⟩ := (hfr n u').1 hu
  obtain ⟨lV, sV⟩ := (hfr r V').1 hV
  let bu : Module.Basis (Fin n) R (eigSp ρ σ) := (Module.Basis.span lu).map (LinearEquiv.ofEq _ _ su)
  let bV : Module.Basis (Fin r) R (eigSp ρ σ) := (Module.Basis.span lV).map (LinearEquiv.ofEq _ _ sV)
  have bu_eq : ∀ i, (bu i : E) = u' i := fun i => by
    simp [bu, Module.Basis.span_apply]
  have bV_eq : ∀ i, (bV i : E) = V' i := fun i => by
    simp [bV, Module.Basis.span_apply]
  have hrn : r = n := by simpa using Fintype.card_congr (bV.indexEquiv bu)
  refine ⟨hrn, (bu.toMatrix bV).transpose, fun i => ?_, (bV.toMatrix bu).transpose, ?_, ?_⟩
  · refine (hc n _ u' _).2 ?_
    have h : V' i = ∑ k, (bu.toMatrix bV).transpose i k • u' k := by
      have h := congrArg Subtype.val (bu.sum_repr (bV i))
      rw [bV_eq] at h
      rw [← h]
      clear h hc hf hfr hu hV hu' hV' hρ
      simp only [Submodule.coe_sum, Submodule.coe_smul, bu_eq, Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    exact congrArg M.pt h
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]

end GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange
