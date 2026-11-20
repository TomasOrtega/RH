import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.MapMulInvEqOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem exHom {G V : Type} [Group G] (S : Submodule ℂ (V → ℂ)) (c : G → ℂ) (a : G → V → V)
    (c1 : c 1 = 1) (cm : ∀ g h, c (g * h) = c g * c h) (a1 : ∀ v, a 1 v = v)
    (am : ∀ g h v, a (g * h)⁻¹ v = a h⁻¹ (a g⁻¹ v))
    (hm : ∀ g, ∀ f ∈ S, (fun v => f (a g⁻¹ v)) ∈ S) :
    ∃ L : G →* Module.End ℂ S, ∀ g f v, (L g f).1 v = c g * f.1 (a g⁻¹ v) := by
  have hmem : ∀ (g : G) (f : S), (fun v => c g * f.1 (a g⁻¹ v)) ∈ S := fun g f =>
    S.smul_mem (c g) (hm g f.1 f.2)
  let T : G → Module.End ℂ S := fun g =>
    { toFun := fun f => ⟨_, hmem g f⟩
      map_add' := by
        intro f f'
        apply Subtype.ext
        funext v
        simp [mul_add]
      map_smul' := by
        intro k f
        apply Subtype.ext
        funext v
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  refine ⟨{ toFun := T, map_one' := ?_, map_mul' := ?_ }, fun g f v => rfl⟩
  · apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext v
    show c 1 * f.1 (a 1⁻¹ v) = f.1 v
    rw [c1, one_mul, inv_one, a1]
  · intro g h
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext v
    show c (g * h) * f.1 (a (g * h)⁻¹ v) = c g * (c h * f.1 (a h⁻¹ (a g⁻¹ v)))
    rw [cm, am, mul_assoc]

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private theorem abMul {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) : ab (s * t) = ab s * ab t := by
  simp only [ab, map_mul]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private theorem abOne {F : Type} [Field F] [NumberField F] : ab (1 : (A F)ˣ) = 1 := by
  simp only [ab, map_one]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem nuMul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (g h : GL (Fin 2) (A E)) : nu F (g * h) = nu F g * nu F h := by
  simp only [nu, map_mul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem nuOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    nu F (1 : GL (Fin 2) (A E)) = 1 := by
  simp only [nu, map_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.R2.D.lEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), ∃ L : GL (Fin 2) (A E) →* Module.End ℂ (S4 F),
    ∀ h φ v, (L h φ).1 v = (((ab (nu F h))⁻¹ : ℝ) : ℂ) * φ.1 (D.act h⁻¹ v) := by
  intro F E _ _ _ _ _ D
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  refine exHom (schwartzBruhatPi F (Fin 4)) (fun h => (((ab (nu F h))⁻¹ : ℝ) : ℂ)) D.act ?_ ?_ ?_ ?_ ?_
  · show (((ab (nu F (1 : GL (Fin 2) (A E))))⁻¹ : ℝ) : ℂ) = 1
    rw [nuOne, abOne]
    simp
  · intro g h
    show (((ab (nu F (g * h)))⁻¹ : ℝ) : ℂ) = (((ab (nu F g))⁻¹ : ℝ) : ℂ) * (((ab (nu F h))⁻¹ : ℝ) : ℂ)
    rw [nuMul, abMul, mul_inv]
    push_cast
    rfl
  · intro v
    rw [hρ, map_one]
    exact Matrix.one_mulVec v
  · intro g h v
    rw [hρ, hρ, hρ, _root_.mul_inv_rev, map_mul]
    exact (Matrix.mulVec_mulVec v _ _).symm
  · intro g f hf
    have h1 := UpperTheory.ConvolutionTheory.R2.D.sClos F (Fin 4) (ρ g⁻¹) f hf
    have h2 : (fun v => f (D.act g⁻¹ v)) = fun v => f ((ρ g⁻¹).val *ᵥ v) := by
      funext v
      rw [hρ]
    rw [h2]
    exact h1
