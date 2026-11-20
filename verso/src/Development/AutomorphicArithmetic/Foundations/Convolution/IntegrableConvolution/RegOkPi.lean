import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm
import GroundTheory.AutomorphicForms.ContragredientTranspose.MatrixSimilarity

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.L1

/- English proof (translation)
Rewrite `ha`, `hb` using `[Subgroup.mem_centralizer_singleton_iff]`. Establish `hA : Commute (a : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k)`. Simplify `congrArg Units.val ha` using `[Commute, SemiconjBy]`. Establish `hB : Commute (b : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k)`. Simplify `congrArg Units.val hb` using `[Commute, SemiconjBy]`.

Conclude with `Units.ext (UpperTheory.V.Z.Tf.Orb.centComm k n _ _ _ hs hA hB)`.
-/
private theorem centComm_field {k : Type} [Field k] {n : ℕ} (γ a b : GL (Fin n) k)
    (hs : (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (ha : a ∈ Subgroup.centralizer {γ}) (hb : b ∈ Subgroup.centralizer {γ}) : a * b = b * a := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
  have hA : Commute (a : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val ha
  have hB : Commute (b : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val hb
  exact Units.ext (UpperTheory.V.Z.Tf.Orb.centComm k n _ _ _ hs hA hB)

/- English proof (translation)
Introduce `γ hs`. Use `⟨?_, fun a ha b hb => centComm_field γ a b hs ha hb⟩` and prove the remaining obligations. Establish `e : {y : GL (Fin n) k | ∃ x : GL (Fin n) k, y = x⁻¹ * γ * x} = ⋂ i : ℕ, {y : GL (Fin n) k | (y : Matrix (Fin n) (Fin n) k).charpoly.coeff i = (γ : Matrix (Fin n) (Fin n) k).charpoly.coeff i}`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩ i`. Establish `h` using `Matrix.charpoly_units_conj x⁻¹ (γ : Matrix (Fin n) (Fin n) k)`. Rewrite `h` using `[← Matrix.coe_units_inv, inv_inv]`. Rewrite using `[Units.val_mul, Units.val_mul]`.

Conclude with `congrArg (fun p => Polynomial.coeff p i) h`. Introduce `h`. Conclude with `GlobalTheory.BCT.ClsFin.conj_of_charpoly γ y hs (Polynomial.ext h).symm`. Rewrite using `[e]`. Conclude with `isClosed_iInter fun i => isClosed_eq ((GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff i).comp Units.continuous_val) continuous_const`.
-/
private theorem regOk_field (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    (n : ℕ) : RegOk k n := by
  intro γ hs
  refine ⟨?_, fun a ha b hb => centComm_field γ a b hs ha hb⟩
  have e : {y : GL (Fin n) k | ∃ x : GL (Fin n) k, y = x⁻¹ * γ * x} =
      ⋂ i : ℕ, {y : GL (Fin n) k | (y : Matrix (Fin n) (Fin n) k).charpoly.coeff i =
        (γ : Matrix (Fin n) (Fin n) k).charpoly.coeff i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨x, rfl⟩ i
      have h := Matrix.charpoly_units_conj x⁻¹ (γ : Matrix (Fin n) (Fin n) k)
      rw [← Matrix.coe_units_inv, inv_inv] at h
      rw [Units.val_mul, Units.val_mul]
      exact congrArg (fun p => Polynomial.coeff p i) h
    · intro h
      exact GlobalTheory.BCT.ClsFin.conj_of_charpoly γ y hs (Polynomial.ext h).symm
  rw [e]
  exact isClosed_iInter fun i => isClosed_eq
    ((GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff i).comp Units.continuous_val)
    continuous_const

section Pi

variable {I : Type} {k : I → Type} [∀ i, Field (k i)] {n : ℕ}

private abbrev ev (i : I) : GL (Fin n) (∀ i, k i) →* GL (Fin n) (k i) :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom k i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem ev_val (i : I) (g : GL (Fin n) (∀ i, k i)) :
    ((ev i g : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) =
      (g : Matrix (Fin n) (Fin n) (∀ i, k i)).map (Pi.evalRingHom k i) := rfl

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => funext fun i => ?_)` and prove the remaining obligations. Establish `h : ((ev i g : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b = ((ev i h : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b` using `by rw [e i]`. Conclude with `h`.
-/
private theorem ev_ext {g h : GL (Fin n) (∀ i, k i)} (e : ∀ i, ev i g = ev i h) : g = h := by
  refine Units.ext (Matrix.ext fun a b => funext fun i => ?_)
  have h : ((ev i g : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b =
      ((ev i h : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b := by rw [e i]
  exact h

private def asm (x : ∀ i, GL (Fin n) (k i)) : GL (Fin n) (∀ i, k i) where
  val := Matrix.of fun a b i => (x i : Matrix (Fin n) (Fin n) (k i)) a b
  inv := Matrix.of fun a b i => ((x i)⁻¹ : GL (Fin n) (k i)).val a b
  val_inv := by
    ext a b i
    have h := congrFun (congrFun (x i).val_inv a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [show ((x i)⁻¹ : GL (Fin n) (k i)).val = (x i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  inv_val := by
    ext a b i
    have h := congrFun (congrFun (x i).inv_val a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [show ((x i)⁻¹ : GL (Fin n) (k i)).val = (x i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Both sides reduce to the same expression.
-/
private theorem ev_asm (x : ∀ i, GL (Fin n) (k i)) (i : I) : ev i (asm x) = x i := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rfl

end Pi

/- English proof (translation)
Introduce `γ hs`. Establish `hsi : ∀ i, ((ev i γ : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)).charpoly.Separable` using `fun i => by`. Rewrite using `[ev_val, Matrix.charpoly_map]`. Conclude with `hs.map`. Establish `hc : ∀ i, Continuous (ev (n` using `n) (k := k) i) := fun i => Continuous.units_map _ ((continuous_id).matrix_map (continuous_apply i))`.

Use `⟨?_, fun a ha b hb => ev_ext fun i => ?_⟩` and prove the remaining obligations. Establish `e : {y : GL (Fin n) (∀ i, k i) | ∃ x : GL (Fin n) (∀ i, k i), y = x⁻¹ * γ * x} = ⋂ i, (ev i) ⁻¹' {y : GL (Fin n) (k i) | ∃ x : GL (Fin n) (k i), y = x⁻¹ * ev i γ * x}`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩ i`. Conclude with `⟨ev i x, by simp only [map_mul, map_inv]⟩`. Introduce `h choose x hx using h`. Use `⟨asm x, ev_ext fun i => ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_inv, ev_asm]`.

Conclude with `hx i`. Rewrite using `[e]`. Conclude with `isClosed_iInter fun i => ((regOk_field (k i) n (ev i γ) (hsi i)).1).preimage (hc i)`. Rewrite `ha`, `hb` using `[Subgroup.mem_centralizer_singleton_iff]`. Rewrite using `[map_mul, map_mul]`.

Use `centComm_field (ev i γ) _ _ (hsi i) ?_ ?_` and prove the remaining obligations. Rewrite using `[Subgroup.mem_centralizer_singleton_iff, ← map_mul, ha, map_mul]`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff, ← map_mul, hb, map_mul]`.
-/
private theorem regOk_pi (I : Type) (k : I → Type) [∀ i, Field (k i)] [∀ i, TopologicalSpace (k i)]
    [∀ i, IsTopologicalRing (k i)] [∀ i, T2Space (k i)] (n : ℕ) : RegOk (∀ i, k i) n := by
  intro γ hs
  have hsi : ∀ i, ((ev i γ : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)).charpoly.Separable := fun i => by
    rw [ev_val, Matrix.charpoly_map]
    exact hs.map
  have hc : ∀ i, Continuous (ev (n := n) (k := k) i) := fun i =>
    Continuous.units_map _ ((continuous_id).matrix_map (continuous_apply i))
  refine ⟨?_, fun a ha b hb => ev_ext fun i => ?_⟩
  · have e : {y : GL (Fin n) (∀ i, k i) | ∃ x : GL (Fin n) (∀ i, k i), y = x⁻¹ * γ * x} =
        ⋂ i, (ev i) ⁻¹' {y : GL (Fin n) (k i) | ∃ x : GL (Fin n) (k i), y = x⁻¹ * ev i γ * x} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      constructor
      · rintro ⟨x, rfl⟩ i
        exact ⟨ev i x, by simp only [map_mul, map_inv]⟩
      · intro h
        choose x hx using h
        refine ⟨asm x, ev_ext fun i => ?_⟩
        simp only [map_mul, map_inv, ev_asm]
        exact hx i
    rw [e]
    exact isClosed_iInter fun i => ((regOk_field (k i) n (ev i γ) (hsi i)).1).preimage (hc i)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    rw [map_mul, map_mul]
    refine centComm_field (ev i γ) _ _ (hsi i) ?_ ?_
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ha, map_mul]
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, hb, map_mul]

end UpperTheory.ConvolutionTheory.L1

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_field k n, fun I k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi I k n, fun F _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi (NumberField.InfinitePlace F) (fun v => v.Completion) n⟩`.
-/
theorem UpperTheory.ConvolutionTheory.L1.regOkPi :
    UpperTheory.ConvolutionTheory.L1.RegOkPi :=
  ⟨fun k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_field k n, fun I k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi I k n,
    fun F _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi (NumberField.InfinitePlace F) (fun v => v.Completion) n⟩
