import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TrLevel

def tiHom : AdelicGLn.FiniteAdelicGL ℚ 3 →* AdelicGLn.FiniteAdelicGL ℚ 3 where
  toFun := ti
  map_one' := by
    apply Units.ext
    change ((1 : AdelicGLn.FiniteAdelicGL ℚ 3)⁻¹ : AdelicGLn.FiniteAdelicGL ℚ 3).val.transpose = 1
    simp
  map_mul' a b := by
    apply Units.ext
    change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
    rw [Matrix.transpose_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. A detailed English derivation is pending.
-/
theorem continuous_tiHom : Continuous tiHom := by
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_id.matrix_transpose).comp Units.continuous_coe_inv
  · exact (continuous_id.matrix_transpose).comp Units.continuous_val

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem ti_mul_adelic (a b : G3) : ti (a * b) = ti a * ti b := by
  apply Units.ext
  change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
  rw [Matrix.transpose_mul]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
theorem ti_one' {R : Type*} [CommRing R] : ti (1 : GL (Fin 3) R) = 1 := by
  apply Units.ext
  change ((1 : GL (Fin 3) R)⁻¹ : GL (Fin 3) R).val.transpose = 1
  simp

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem prodEquiv_ti (x : G3) :
    AdelicGLn.prodEquiv ℚ 3 (ti x) =
      (ti (AdelicGLn.prodEquiv ℚ 3 x).1, ti (AdelicGLn.prodEquiv ℚ 3 x).2) := by
  have h : AdelicGLn.prodEquiv ℚ 3 x⁻¹ = (AdelicGLn.prodEquiv ℚ 3 x)⁻¹ := map_inv _ _
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · refine Matrix.ext fun a b => ?_
    have h1 : ((AdelicGLn.prodEquiv ℚ 3 x)⁻¹).1 b a = ((x⁻¹ : G3) b a).1 := by rw [← h]; rfl
    exact h1.symm
  · refine Matrix.ext fun a b => ?_
    have h1 : ((AdelicGLn.prodEquiv ℚ 3 x)⁻¹).2 b a = ((x⁻¹ : G3) b a).2 := by rw [← h]; rfl
    exact h1.symm

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem ti_finEmb (u : AdelicGLn.FiniteAdelicGL ℚ 3) :
    ti (finEmb ℚ 3 u) = finEmb ℚ 3 (ti u) := by
  apply (AdelicGLn.prodEquiv ℚ 3).injective
  rw [prodEquiv_ti, prodEquiv_finEmb, prodEquiv_finEmb, ti_one']

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem ti_level : ∀ U₀ : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3), ∃ U₁ : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3),
    ∀ u ∈ U₁, ∃ u' ∈ U₀, ∀ g : G3, ti (g * finEmb ℚ 3 u) = ti g * finEmb ℚ 3 u' := by
  intro U₀
  refine ⟨U₀.comap tiHom continuous_tiHom, fun u hu => ⟨ti u, hu, fun g => ?_⟩⟩
  rw [ti_mul_adelic, ti_finEmb]

end GlobalTheory.CompanionTheory.UnfoldingAlt.TrLevel
