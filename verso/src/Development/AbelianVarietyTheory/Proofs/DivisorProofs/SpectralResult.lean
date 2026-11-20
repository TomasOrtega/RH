import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open MonObj
open GlobalTheory.HalfGeo

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HalfGeo.SpecProof

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z R K k _ _ _ u ψ hu x₀ ξ₀ y₀ q hq a b a₁ b₁ a₂ b₂ ha hb ha₁ hb₁ ha₂ hb₂ r hr`. Set `P` to `GlobalTheory.Obj.toPolAV Z.oF`. Establish `hK : spMap u ≫ x₀ = ξ₀`. Establish `h1` using `Over.w a₁`. Establish `h2` using `Over.w a`.

Simplify using `only [Over.mk_hom, Functor.id_obj, Functor.const_obj_obj] at h1 h2`. Rewrite using `[← h1, ha₁, Category.assoc, h2]`. Establish `hC : spMap ψ ≫ x₀ = y₀`. Establish `h1` using `Over.w a₂`. Establish `h2` using `Over.w a`.

Simplify using `only [Over.mk_hom, Functor.id_obj, Functor.const_obj_obj] at h1 h2`. Rewrite using `[← h1, ha₂, Category.assoc, h2]`. Take `⟨cc, hcc, -⟩` from `GlobalTheory.LevelCompare.weil_existsUnique P q a b ha hb`. Take `⟨r', rfl⟩` from `GlobalTheory.Ex.Specialise.unitOn_bijective.2 cc`. Set `hKo : Over.mk ξ₀ ⟶ Over.mk x₀` to `Over.homMk (spMap u) hK`.

Set `hCo : Over.mk y₀ ⟶ Over.mk x₀` to `Over.homMk (spMap ψ) hC`. Establish `hKl : hKo.left = spMap u` using `rfl`. Establish `hCl : hCo.left = spMap ψ` using `rfl`. Establish `e1 : hKo ≫ a = a₁` using `Over.OverMorphism.ext (by rw [Over.comp_left, hKl, ha₁])`. Establish `f1 : hKo ≫ b = b₁` using `Over.OverMorphism.ext (by rw [Over.comp_left, hKl, hb₁])`.

Establish `e2 : hCo ≫ a = a₂` using `Over.OverMorphism.ext (by rw [Over.comp_left, hCl, ha₂])`. Establish `f2 : hCo ≫ b = b₂` using `Over.OverMorphism.ext (by rw [Over.comp_left, hCl, hb₂])`. Establish `hN` using `(GlobalTheory.LevelCompare.weil_skew_natural P q (Over.mk x₀)).2 (Over.mk ξ₀) hKo a b (unitOn r') hcc`. Rewrite `hN` using `[hKl, GlobalTheory.Ex.Specialise.map_unitOn]`. Establish `t1 : (hKo ≫ a) ^ q = 1` using `by rw [← MonObj.comp_pow, ha, MonObj.comp_one]`.

Establish `t2 : (hKo ≫ b) ^ q = 1` using `by rw [← MonObj.comp_pow, hb, MonObj.comp_one]`. Rewrite `hr` using `[← e1, ← f1]`. Establish `huK` using `(GlobalTheory.LevelCompare.weil_existsUnique P q (hKo ≫ a) (hKo ≫ b) t1 t2).unique hN hr`. Establish `huK'` using `GlobalTheory.Ex.Specialise.unitOn_bijective.1 huK`. Establish `hrr : r' = r`.

Use `ext`. Apply `hu` to reduce the goal to its premises. Use `congrArg (fun v : Kˣ => (v : K)) huK'` as an intermediate fact. Simplify `this` using `only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`. Substitute `hrr` using the available equality.

Establish `hN2` using `(GlobalTheory.LevelCompare.weil_skew_natural P q (Over.mk x₀)).2 (Over.mk y₀) hCo a b (unitOn r') hcc`. Rewrite `hN2` using `[hCl, GlobalTheory.Ex.Specialise.map_unitOn]`. Rewrite using `[← e2, ← f2]`. Conclude with `hN2`.
-/
theorem specSt : SpecSt := by
  intro E _ _ _ H Dw l Xo c O _ β Z R K k _ _ _ u ψ hu x₀ ξ₀ y₀ q hq a b a₁ b₁ a₂ b₂ ha hb ha₁ hb₁ ha₂ hb₂ r hr
  let P := GlobalTheory.Obj.toPolAV Z.oF
  have hK : spMap u ≫ x₀ = ξ₀ := by
    have h1 := Over.w a₁
    have h2 := Over.w a
    simp only [Over.mk_hom, Functor.id_obj, Functor.const_obj_obj] at h1 h2
    rw [← h1, ha₁, Category.assoc, h2]
  have hC : spMap ψ ≫ x₀ = y₀ := by
    have h1 := Over.w a₂
    have h2 := Over.w a
    simp only [Over.mk_hom, Functor.id_obj, Functor.const_obj_obj] at h1 h2
    rw [← h1, ha₂, Category.assoc, h2]
  obtain ⟨cc, hcc, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P q a b ha hb
  obtain ⟨r', rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 cc
  let hKo : Over.mk ξ₀ ⟶ Over.mk x₀ := Over.homMk (spMap u) hK
  let hCo : Over.mk y₀ ⟶ Over.mk x₀ := Over.homMk (spMap ψ) hC
  have hKl : hKo.left = spMap u := rfl
  have hCl : hCo.left = spMap ψ := rfl
  have e1 : hKo ≫ a = a₁ := Over.OverMorphism.ext (by rw [Over.comp_left, hKl, ha₁])
  have f1 : hKo ≫ b = b₁ := Over.OverMorphism.ext (by rw [Over.comp_left, hKl, hb₁])
  have e2 : hCo ≫ a = a₂ := Over.OverMorphism.ext (by rw [Over.comp_left, hCl, ha₂])
  have f2 : hCo ≫ b = b₂ := Over.OverMorphism.ext (by rw [Over.comp_left, hCl, hb₂])
  have hN := (GlobalTheory.LevelCompare.weil_skew_natural P q (Over.mk x₀)).2 (Over.mk ξ₀) hKo a b (unitOn r') hcc
  rw [hKl, GlobalTheory.Ex.Specialise.map_unitOn] at hN
  have t1 : (hKo ≫ a) ^ q = 1 := by rw [← MonObj.comp_pow, ha, MonObj.comp_one]
  have t2 : (hKo ≫ b) ^ q = 1 := by rw [← MonObj.comp_pow, hb, MonObj.comp_one]
  rw [← e1, ← f1] at hr
  have huK := (GlobalTheory.LevelCompare.weil_existsUnique P q (hKo ≫ a) (hKo ≫ b) t1 t2).unique hN hr
  have huK' := GlobalTheory.Ex.Specialise.unitOn_bijective.1 huK
  have hrr : r' = r := by
    ext
    apply hu
    have := congrArg (fun v : Kˣ => (v : K)) huK'
    simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe] using this
  subst hrr
  have hN2 := (GlobalTheory.LevelCompare.weil_skew_natural P q (Over.mk x₀)).2 (Over.mk y₀) hCo a b (unitOn r') hcc
  rw [hCl, GlobalTheory.Ex.Specialise.map_unitOn] at hN2
  rw [← e2, ← f2]
  exact hN2

end GlobalTheory.HalfGeo.SpecProof
