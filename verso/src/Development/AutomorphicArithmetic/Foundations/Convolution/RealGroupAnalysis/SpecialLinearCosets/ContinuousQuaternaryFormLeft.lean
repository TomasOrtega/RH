import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ColsHApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.MatLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PsiLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

/- English proof (translation)
Use `fun_prop`.
-/
private theorem continuous_form {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (a c b d e : R) :
    Continuous fun y : Fin 4 → R => 2 * (y 2 * a - c * (y 3 * b)) - y 1 * d - y 0 * e := by
  fun_prop

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp (continuous_adelicChar (K := F))`.
-/
private theorem continuous_psi {F : Type} [Field F] [NumberField F] : Continuous (ψ : A F → ℂ) :=
  continuous_subtype_val.comp (continuous_adelicChar (K := F))

/- English proof (translation)
The claim follows from `Circle.norm_coe _`.
-/
private theorem norm_psi {F : Type} [Field F] [NumberField F] (x : A F) : ‖ψ x‖ = 1 :=
  Circle.norm_coe _

/- English proof (translation)
Simplify using `[ψ, AddChar.map_add_eq_mul]`.
-/
private theorem psi_add {F : Type} [Field F] [NumberField F] (x y : A F) :
    ψ (x + y) = ψ x * ψ y := by
  simp [ψ, AddChar.map_add_eq_mul]

/- English proof (translation)
The claim follows from `continuous_form (Z 2) (rt δ) (Z 3) (Z 0) (Z 1)`.
-/
private theorem continuous_quaternaryForm_left {F : Type} [Field F] [NumberField F] (δ : F) (Z : V4 F) :
    Continuous fun y : V4 F => B4 δ y Z :=
  continuous_form (Z 2) (rt δ) (Z 3) (Z 0) (Z 1)

/- English proof (translation)
Unfold `BM`. Establish `h : ∀ i j, Continuous fun Y : M2 v => Y i j` using `fun i j => continuous_id.matrix_elem i j`. Conclude with `(((h 0 1).mul continuous_const).add ((h 1 0).mul continuous_const)).sub ((h 0 0).mul continuous_const) |>.sub ((h 1 1).mul continuous_const)`.
-/
private theorem continuous_BM {F : Type} [Field F] [NumberField F] (v : P F) (M : M2 v) :
    Continuous fun Y : M2 v => BM Y M := by
  unfold BM
  have h : ∀ i j, Continuous fun Y : M2 v => Y i j := fun i j => continuous_id.matrix_elem i j
  exact (((h 0 1).mul continuous_const).add ((h 1 0).mul continuous_const)).sub
    ((h 0 0).mul continuous_const) |>.sub ((h 1 1).mul continuous_const)

/- English proof (translation)
Assemble the required witnesses or components as `⟨hb.1.mul (hψ.comp_continuous (continuous_BM v M)), hb.2.mul_right⟩`.
-/
private theorem mul_mem_SB {F : Type} [Field F] [NumberField F] (v : P F) {b : M2 v → ℂ}
    (hb : b ∈ SB (M2 v)) (M : M2 v) (hψ : IsLocallyConstant (ψl v)) :
    (fun Y => b Y * ψl v (BM Y M)) ∈ SB (M2 v) :=
  ⟨hb.1.mul (hψ.comp_continuous (continuous_BM v M)), hb.2.mul_right⟩

/- English proof (translation)
Introduce `F _ _ _ v δ θ hθ hθ0 u hu`. Take `⟨hm1, hm2, -, -, hac, -, -⟩` from `matLaws F v δ θ hθ hθ0`. Take `⟨-, hψs, -, hψlc, -, -⟩` from `psiLaws F v`. Establish `hint : ∀ b ∈ SB (M2 v), ∀ Z : V4 F, Integrable (fun Y => ten v θ u b Y * ψ (B4 δ (away v Y) Z)) (adeleMeasurePi F)`. Introduce `b hb Z`.

Take `⟨φ, -, hφ⟩` from `hu b hb`. Rewrite using `[← hφ]`. Use `(integrable_of_mem_schwartzBruhatPi φ.2).mul_bdd (c := 1) ?_ ?_` and prove the remaining obligations. Conclude with `(continuous_psi.comp ((continuous_quaternaryForm_left δ Z).comp hac)).aestronglyMeasurable`. Conclude with `Eventually.of_forall fun y => (norm_psi _).le`.

Set `ℓ : V4 F → SB (M2 v) →ₗ[ℂ] ℂ` to `fun Z => { toFun := fun b => ∫ Y, ten v θ u b.1 Y * ψ (B4 δ (away v Y) Z) ∂(adeleMeasurePi F) map_add' := by`. Introduce `a b`. Rewrite using `[← integral_add (hint a.1 a.2 Z) (hint b.1 b.2 Z)]`. Use `congr 1`. Use function extensionality and compare the values at `Y`.

Simplify using `only [ten, Submodule.coe_add, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := by`. Introduce `c a`. Simplify using `only [RingHom.id_apply, smul_eq_mul]`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `Y`. Simplify using `only [ten, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]`. Use `ring }`.

Establish `hinv : ∀ (Z : V4 F) (y : M2 v) (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m + y)) → ℓ Z a' = ℓ Z a`. Introduce `Z y a a' h`. Take `⟨y', hy'⟩` from `hm1 y`. Express the relevant statement in the definitionally equal form `(∫ Y, ten v θ u a'.1 Y * ψ (B4 δ (away v Y) Z) ∂(adeleMeasurePi F)) = ∫ Y, ten v θ u a.1 Y * ψ (B4 δ (away v Y) Z) ∂(adeleMeasurePi F)`. Rewrite using `[← integral_add_right_eq_self (fun Y => ten v θ u a.1 Y * ψ (B4 δ (away v Y) Z)) y']`.

Use `congr 1`. Use function extensionality and compare the values at `Y`. Simplify using `only [ten, (hy' Y).1, (hy' Y).2, h]`. Use `choose c hc using fun Z => invFn F v (ℓ Z) (hinv Z)`. Use `⟨c, fun b hb => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `X`. Establish `hmem` using `mul_mem_SB v hb (mat v θ X) hψlc`. Establish `h` using `hc (away v X) ⟨_, hmem⟩`. Express the relevant statement in the definitionally equal form `(∫ Y, ten v θ u (fun Y => b Y * ψl v (BM Y (mat v θ X))) Y * ψ (B4 δ (away v Y) (away v X)) ∂(adeleMeasurePi F)) = _ at h`. Simplify using `only [ten]`.

Rewrite using `[← h]`. Unfold `ft4`. Use `congr 1`. Use function extensionality and compare the values at `Y`. Simplify using `only [ten]`.

Rewrite using `[hm2 X Y, psi_add, hψs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.ConvolutionTheory.R2.I.tenFt :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (v : P F) (δ : F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) δ → θ ≠ 0 →
      ∀ u, GoodU v δ θ u → ∃ u' : V4 F → ℂ, ∀ b ∈ SB (M2 v),
        ft4 δ (ten v θ u b) = ten v θ u' fun X => IM fun Y => b Y * ψl v (BM Y X) := by
  intro F _ _ _ v δ θ hθ hθ0 u hu
  obtain ⟨hm1, hm2, -, -, hac, -, -⟩ := matLaws F v δ θ hθ hθ0
  obtain ⟨-, hψs, -, hψlc, -, -⟩ := psiLaws F v
  have hint : ∀ b ∈ SB (M2 v), ∀ Z : V4 F,
      Integrable (fun Y => ten v θ u b Y * ψ (B4 δ (away v Y) Z)) (adeleMeasurePi F) := by
    intro b hb Z
    obtain ⟨φ, -, hφ⟩ := hu b hb
    rw [← hφ]
    refine (integrable_of_mem_schwartzBruhatPi φ.2).mul_bdd (c := 1) ?_ ?_
    · exact (continuous_psi.comp ((continuous_quaternaryForm_left δ Z).comp hac)).aestronglyMeasurable
    · exact Eventually.of_forall fun y => (norm_psi _).le
  let ℓ : V4 F → SB (M2 v) →ₗ[ℂ] ℂ := fun Z =>
    { toFun := fun b => ∫ Y, ten v θ u b.1 Y * ψ (B4 δ (away v Y) Z) ∂(adeleMeasurePi F)
      map_add' := by
        intro a b
        rw [← integral_add (hint a.1 a.2 Z) (hint b.1 b.2 Z)]
        congr 1
        funext Y
        simp only [ten, Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1
        funext Y
        simp only [ten, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring }
  have hinv : ∀ (Z : V4 F) (y : M2 v) (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m + y)) →
      ℓ Z a' = ℓ Z a := by
    intro Z y a a' h
    obtain ⟨y', hy'⟩ := hm1 y
    change (∫ Y, ten v θ u a'.1 Y * ψ (B4 δ (away v Y) Z) ∂(adeleMeasurePi F)) =
      ∫ Y, ten v θ u a.1 Y * ψ (B4 δ (away v Y) Z) ∂(adeleMeasurePi F)
    rw [← integral_add_right_eq_self
      (fun Y => ten v θ u a.1 Y * ψ (B4 δ (away v Y) Z)) y']
    congr 1
    funext Y
    simp only [ten, (hy' Y).1, (hy' Y).2, h]
  choose c hc using fun Z => invFn F v (ℓ Z) (hinv Z)
  refine ⟨c, fun b hb => ?_⟩
  funext X
  have hmem := mul_mem_SB v hb (mat v θ X) hψlc
  have h := hc (away v X) ⟨_, hmem⟩
  change (∫ Y, ten v θ u (fun Y => b Y * ψl v (BM Y (mat v θ X))) Y *
    ψ (B4 δ (away v Y) (away v X)) ∂(adeleMeasurePi F)) = _ at h
  simp only [ten]
  rw [← h]
  unfold ft4
  congr 1
  funext Y
  simp only [ten]
  rw [hm2 X Y, psi_add, hψs]
  ring
