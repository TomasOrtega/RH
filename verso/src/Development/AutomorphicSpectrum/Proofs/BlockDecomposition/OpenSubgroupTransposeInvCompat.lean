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
Rewrite using `[Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion. Conclude with `(continuous_id.matrix_transpose).comp Units.continuous_coe_inv`. Conclude with `(continuous_id.matrix_transpose).comp Units.continuous_val`.
-/
theorem continuous_tiHom : Continuous tiHom := by
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_id.matrix_transpose).comp Units.continuous_coe_inv
  · exact (continuous_id.matrix_transpose).comp Units.continuous_val

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose`. Rewrite using `[Matrix.transpose_mul]`.
-/
theorem ti_mul_adelic (a b : G3) : ti (a * b) = ti a * ti b := by
  apply Units.ext
  change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
  rw [Matrix.transpose_mul]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((1 : GL (Fin 3) R)⁻¹ : GL (Fin 3) R).val.transpose = 1`. Simplify using the standard rewrite rules.
-/
theorem ti_one' {R : Type*} [CommRing R] : ti (1 : GL (Fin 3) R) = 1 := by
  apply Units.ext
  change ((1 : GL (Fin 3) R)⁻¹ : GL (Fin 3) R).val.transpose = 1
  simp

/- English proof (translation)
Establish `h : AdelicGLn.prodEquiv ℚ 3 x⁻¹ = (AdelicGLn.prodEquiv ℚ 3 x)⁻¹` using `map_inv _ _`. Use `Prod.ext (Units.ext ?_) (Units.ext ?_)` and prove the remaining obligations. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Establish `h1 : ((AdelicGLn.prodEquiv ℚ 3 x)⁻¹).1 b a = ((x⁻¹ : G3) b a).1` using `by rw [← h]; rfl`. Conclude with `h1.symm`.

Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Establish `h1 : ((AdelicGLn.prodEquiv ℚ 3 x)⁻¹).2 b a = ((x⁻¹ : G3) b a).2` using `by rw [← h]; rfl`. Conclude with `h1.symm`.
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
Apply `(AdelicGLn.prodEquiv ℚ 3).injective` to reduce the goal to its premises. Rewrite using `[prodEquiv_ti, prodEquiv_finEmb, prodEquiv_finEmb, ti_one']`.
-/
theorem ti_finEmb (u : AdelicGLn.FiniteAdelicGL ℚ 3) :
    ti (finEmb ℚ 3 u) = finEmb ℚ 3 (ti u) := by
  apply (AdelicGLn.prodEquiv ℚ 3).injective
  rw [prodEquiv_ti, prodEquiv_finEmb, prodEquiv_finEmb, ti_one']

/- English proof (translation)
Introduce `U₀`. Use `⟨U₀.comap tiHom continuous_tiHom, fun u hu => ⟨ti u, hu, fun g => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[ti_mul_adelic, ti_finEmb]`.
-/
theorem ti_level : ∀ U₀ : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3), ∃ U₁ : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3),
    ∀ u ∈ U₁, ∃ u' ∈ U₀, ∀ g : G3, ti (g * finEmb ℚ 3 u) = ti g * finEmb ℚ 3 u' := by
  intro U₀
  refine ⟨U₀.comap tiHom continuous_tiHom, fun u hu => ⟨ti u, hu, fun g => ?_⟩⟩
  rw [ti_mul_adelic, ti_finEmb]

end GlobalTheory.CompanionTheory.UnfoldingAlt.TrLevel
