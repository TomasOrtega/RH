import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

def PtsIntegralZeroLowerNE.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ),
    IsMultiHomogIdeal W → Finite (McClasses W) →
    (∀ (u : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, u k ≠ 0) → z ∈ mcPts W →
      g (fun p => u p.1 * z p) = g z) →
    (∀ z ∈ mcPts W, c ≤ g z) →
    c * degC W ≤ ptsIntegral (e := 0) W φ g

/- English proof (translation)
Establish `he : (plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 = Fin.castLEOrderEmb (Nat.le_add_right j m)`. Use `symm`. Apply `Finset.orderEmbOfFin_unique'` to reduce the goal to its premises. Introduce `x`. Simplify using `only [plAnchor, Finset.mem_map, Finset.mem_univ, true_and]`.

Conclude with `⟨x, rfl⟩`. Establish `: colsOf (onePipe Z) (plAnchor j m) = 1`. Use extensionality with `a b`. Simplify using `only [colsOf, Matrix.submatrix_apply, id, he, onePipe, Matrix.of_apply]`. Establish `: (Fin.castLEOrderEmb (Nat.le_add_right j m)) b = Fin.castAdd m b` using `rfl`.

Rewrite using `[this, Fin.append_left]`. Rewrite using `[this, Matrix.det_one]`.
-/
theorem anchor_minor {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by
  have he : (plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 = Fin.castLEOrderEmb (Nat.le_add_right j m) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro x
    simp only [plAnchor, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨x, rfl⟩
  have : colsOf (onePipe Z) (plAnchor j m) = 1 := by
    ext a b
    simp only [colsOf, Matrix.submatrix_apply, id, he, onePipe, Matrix.of_apply]
    have : (Fin.castLEOrderEmb (Nat.le_add_right j m)) b = Fin.castAdd m b := rfl
    rw [this, Fin.append_left]
  rw [this, Matrix.det_one]

/- English proof (translation)
Use `⟨fun k => ⟨plAnchor j m, ?_⟩, fun g hg => ?_⟩` and prove the remaining obligations. Simplify using `[rootCoord, anchor_minor]`. Establish `h : mConeMap (rootCoord ζ) g = 0` using `hg`. Establish `h2` using `congrArg (MvPolynomial.eval (fun _ : Fin f => (1 : ℂ))) h`. Establish `key : (MvPolynomial.eval (fun _ : Fin f => (1 : ℂ))).comp (mConeMap (rootCoord ζ) : MRing (plBlocks f j m) →+* MvPolynomial (Fin f) ℂ) = (eval (rootCoord ζ)).comp (map (Int.castRingHom ℂ))`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using the standard rewrite rules. Introduce `i`. Simplify using `[mConeMap]`.

Use `congrArg (fun φ => φ g) key` as an intermediate fact. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe, h, map_zero] at this`. Conclude with `this.symm`.
-/
theorem rootCoord_mem {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) :
    rootCoord ζ ∈ mcPts (rootPointIdeal ζ) := by
  refine ⟨fun k => ⟨plAnchor j m, ?_⟩, fun g hg => ?_⟩
  · simp [rootCoord, anchor_minor]
  · have h : mConeMap (rootCoord ζ) g = 0 := hg
    have h2 := congrArg (MvPolynomial.eval (fun _ : Fin f => (1 : ℂ))) h
    have key : (MvPolynomial.eval (fun _ : Fin f => (1 : ℂ))).comp
        (mConeMap (rootCoord ζ) : MRing (plBlocks f j m) →+* MvPolynomial (Fin f) ℂ) =
        (eval (rootCoord ζ)).comp (map (Int.castRingHom ℂ)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro i; simp [mConeMap]
    have := congrArg (fun φ => φ g) key
    simp only [RingHom.comp_apply, RingHom.coe_coe, h, map_zero] at this
    exact this.symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨∅, by simp, by simp⟩`.
-/
example : IsMultiHomogIdeal (⊥ : Ideal (MRing (fun _ : Unit => Unit))) :=
  ⟨∅, by simp, by simp⟩

/- English proof (translation)
Use `haveI : Subsingleton (McClasses (⊥ : Ideal (MRing (fun _ : Unit => Unit)))) := by`. Prove the components needed by the constructor for the conclusion. Introduce `x y`. Proceed by induction on `x using Quot.ind with | mk z => ?_`. Proceed by induction on `y using Quot.ind with | mk z' => ?_`.

Apply `Quot.sound` to reduce the goal to its premises. Take `⟨⟨⟩, hz⟩` from `z.2.1 ()`. Take `⟨⟨⟩, hz'⟩` from `z'.2.1 ()`. Use `⟨fun _ => z'.1 ⟨(), ()⟩ / z.1 ⟨(), ()⟩, fun _ => div_ne_zero hz' hz, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Break down `p with ⟨⟨⟩, ⟨⟩⟩` into its components or cases. Clear the denominators using the available nonvanishing facts. Conclude with `Finite.of_subsingleton`.
-/
theorem finite_mcClasses_bot_unit : Finite (McClasses (⊥ : Ideal (MRing (fun _ : Unit => Unit)))) := by
  haveI : Subsingleton (McClasses (⊥ : Ideal (MRing (fun _ : Unit => Unit)))) := by
    constructor
    intro x y
    induction x using Quot.ind with | mk z => ?_
    induction y using Quot.ind with | mk z' => ?_
    apply Quot.sound
    obtain ⟨⟨⟩, hz⟩ := z.2.1 ()
    obtain ⟨⟨⟩, hz'⟩ := z'.2.1 ()
    refine ⟨fun _ => z'.1 ⟨(), ()⟩ / z.1 ⟨(), ()⟩, fun _ => div_ne_zero hz' hz, ?_⟩
    funext p
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    field_simp
  exact Finite.of_subsingleton

end

end GroundTheory.Heights₂.Heights
