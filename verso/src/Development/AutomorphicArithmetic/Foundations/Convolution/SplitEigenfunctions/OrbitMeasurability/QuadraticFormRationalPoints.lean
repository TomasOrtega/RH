import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianStandardVector
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianMatrixBasisOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Introduce `ξ ξ' h`. Use function extensionality and compare the values at `i`. Conclude with `AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ (congrFun h i)`.
-/
private theorem rp_injective : Function.Injective (rp : (Fin 4 → ℚ) → V4 ℚ) := by
  intro ξ ξ' h
  funext i
  exact AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ (congrFun h i)

/- English proof (translation)
Simplify using `[q4, qr, rp, map_sub, map_mul, map_pow]`.
-/
private theorem quadraticForm_rational_points (δ : ℚ) (ξ : Fin 4 → ℚ) : q4 δ (rp ξ) = rt (qr δ ξ) := by
  simp [q4, qr, rp, map_sub, map_mul, map_pow]

variable (E) in

private noncomputable def jE : G1 ℚ →* G1 E := Matrix.SpecialLinearGroup.map (am E)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
private theorem gl_jE (g : G1 ℚ) : gl (jE E g) = em E (gl g) := by
  apply Units.ext
  ext i j
  rfl

/- English proof (translation)
Establish `h : Continuous fun g : G1 ℚ => (g.1).map (am E)` using `continuous_subtype_val.matrix_map continuous_am`. Conclude with `h.subtype_mk _`.
-/
private theorem continuous_jE : Continuous (jE E) := by
  have h : Continuous fun g : G1 ℚ => (g.1).map (am E) :=
    continuous_subtype_val.matrix_map continuous_am
  exact h.subtype_mk _

/- English proof (translation)
Introduce `g g' h`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `am_injective (E := E) (congrFun (congrFun (congrArg Subtype.val h) i) j)`.
-/
private theorem injective_jE : Function.Injective (jE E) := by
  intro g g' h
  apply Subtype.ext
  ext i j
  exact am_injective (E := E) (congrFun (congrFun (congrArg Subtype.val h) i) j)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `am_rt (g i j)`.
-/
private theorem jE_ratS (g : Matrix.SpecialLinearGroup (Fin 2) ℚ) :
    jE E (ratS ℚ g) = ratS E (Matrix.SpecialLinearGroup.map (algebraMap ℚ E) g) := by
  apply Subtype.ext
  ext i j
  exact am_rt (g i j)

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

open UpperTheory.ConvolutionTheory.RankTwoDescent.Cp in
/- English proof (translation)
Introduce `E _ _ _ D`. Take `⟨h1, h2, h3⟩` from `orbS E D`. Take `⟨ρ1, -⟩` from `orb1 E D`. Use `choose γ hγ using fun i : Orb D.δ => h1 i.1 i.2`. Use `⟨jE E, fun i => ratS E (γ i), gl_jE, continuous_jE, injective_jE, fun i => ⟨⟨γ i, rfl⟩, hγ i⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨_, (jE_ratS g).symm⟩`. Introduce and unpack `_ ⟨c, rfl⟩`. Take `⟨ρ, hρ⟩` from `ρ1 c`. Establish `hq : qr D.δ (ρ X0) = qr D.δ X0`.

Apply `AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `UpperTheory.ConvolutionTheory.R2.rt _ = UpperTheory.ConvolutionTheory.R2.rt _`. Rewrite using `[← quadraticForm_rational_points, ← quadraticForm_rational_points, ← hρ, D.quadForm_act, nu_gl]`. Simplify using the standard rewrite rules. Set `i : Orb D.δ` to `⟨ρ X0, hq⟩`.

Establish `hi : rp i.1 = D.act (gl (ratS E c)) (rp X0)` using `(hρ X0).symm`. Establish `hfix : ∀ x : G1 ℚ, D.act (gl (jE E x)) (rp X0) = rp X0` using `fun x => (h2 (jE E x)).2 ⟨x, gl_jE x⟩`. Establish `hstab : D.act (gl (ratS E ((γ i)⁻¹ * c))) (rp X0) = rp X0`. Establish `e : ratS E ((γ i)⁻¹ * c) = (ratS E (γ i))⁻¹ * ratS E c` using `by rw [map_mul, map_inv]`. Rewrite using `[e, gl_mul, gl_inv, D.act_mul, ← hi, hγ i, D.act_inv_act]`.

Take `⟨g, hg⟩` from `(h3 _).1 hstab`. Establish `hj : ratS E ((γ i)⁻¹ * c) = jE E (ratS ℚ g)` using `gl_injective (hg.trans (gl_jE _).symm)`. Use `⟨i, ⟨ratS ℚ g, ⟨g, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hj, map_mul, map_inv, mul_inv_cancel_left]`. Introduce and unpack `i' ⟨_, ⟨g', rfl⟩, hi'⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `rp_injective` to reduce the goal to its premises. Rewrite using `[hγ i', hi, hi', gl_mul, D.act_mul, hfix]`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.reps :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Reps := by
  intro E _ _ _ D
  obtain ⟨h1, h2, h3⟩ := orbS E D
  obtain ⟨ρ1, -⟩ := orb1 E D
  choose γ hγ using fun i : Orb D.δ => h1 i.1 i.2
  refine ⟨jE E, fun i => ratS E (γ i), gl_jE, continuous_jE, injective_jE,
    fun i => ⟨⟨γ i, rfl⟩, hγ i⟩, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, (jE_ratS g).symm⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨ρ, hρ⟩ := ρ1 c
    have hq : qr D.δ (ρ X0) = qr D.δ X0 := by
      apply AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ
      change UpperTheory.ConvolutionTheory.R2.rt _ = UpperTheory.ConvolutionTheory.R2.rt _
      rw [← quadraticForm_rational_points, ← quadraticForm_rational_points, ← hρ, D.quadForm_act, nu_gl]
      simp
    let i : Orb D.δ := ⟨ρ X0, hq⟩
    have hi : rp i.1 = D.act (gl (ratS E c)) (rp X0) := (hρ X0).symm
    have hfix : ∀ x : G1 ℚ, D.act (gl (jE E x)) (rp X0) = rp X0 := fun x =>
      (h2 (jE E x)).2 ⟨x, gl_jE x⟩
    have hstab : D.act (gl (ratS E ((γ i)⁻¹ * c))) (rp X0) = rp X0 := by
      have e : ratS E ((γ i)⁻¹ * c) = (ratS E (γ i))⁻¹ * ratS E c := by rw [map_mul, map_inv]
      rw [e, gl_mul, gl_inv, D.act_mul, ← hi, hγ i, D.act_inv_act]
    obtain ⟨g, hg⟩ := (h3 _).1 hstab
    have hj : ratS E ((γ i)⁻¹ * c) = jE E (ratS ℚ g) := gl_injective (hg.trans (gl_jE _).symm)
    refine ⟨i, ⟨ratS ℚ g, ⟨g, rfl⟩, ?_⟩, ?_⟩
    · rw [← hj, map_mul, map_inv, mul_inv_cancel_left]
    · rintro i' ⟨_, ⟨g', rfl⟩, hi'⟩
      apply Subtype.ext
      apply rp_injective
      rw [hγ i', hi, hi', gl_mul, D.act_mul, hfix]
