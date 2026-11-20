import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopBasisChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace TopDualBasisChange

/- English proof (translation)
Consider the cases of `A`. Consider the cases of `B`. Consider the cases of `ha`. Consider the cases of `hh`. Both sides reduce to the same expression.
-/
theorem hermLine_ext {ι : Unit → Type} [∀ k, Fintype (ι k)] {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

variable {T T₂ : Type} [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂]

omit [DecidableEq T₂] in

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => show intCoordSubst A (intCoordSubst B (algebraMap ℤ _ a)) = algebraMap ℤ _ a`. Rewrite using `[AlgHom.commutes, AlgHom.commutes]`. Consider the case `add f g hf hg => rw [map_add, map_add, hf, hg]`. Consider the case `mul_X f p hf`.

Rewrite using `[map_mul, map_mul, hf]`. Use `congr 1`. Take `⟨⟨⟩, t⟩` from `p`. Establish `hC : ∀ a : ℤ, (C a : MRing (dualBlocks T)) = (a : MRing (dualBlocks T))` using `fun a => map_intCast C a`. Simplify using `only [intCoordSubst, aeval_X, map_sum, map_mul, eq_intCast, hC, map_intCast, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← mul_assoc, ← Int.cast_mul, ← Finset.sum_mul, ← Int.cast_sum]`. Establish `h1 : ∀ x : T, ∑ s, B s t * A x s = (A * B) x t`. Introduce `x`. Simplify using `[Matrix.mul_apply, mul_comm]`.

Repeatedly rewrite using `[h1, hAB, Matrix.one_apply]`. Simplify using the standard rewrite rules.
-/
theorem subst_subst {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (f : MRing (dualBlocks T)) :
    intCoordSubst A (intCoordSubst B f) = f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    show intCoordSubst A (intCoordSubst B (algebraMap ℤ _ a)) = algebraMap ℤ _ a
    rw [AlgHom.commutes, AlgHom.commutes]
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | mul_X f p hf =>
    rw [map_mul, map_mul, hf]
    congr 1
    obtain ⟨⟨⟩, t⟩ := p
    have hC : ∀ a : ℤ, (C a : MRing (dualBlocks T)) = (a : MRing (dualBlocks T)) := fun a => map_intCast C a
    simp only [intCoordSubst, aeval_X, map_sum, map_mul, eq_intCast, hC, map_intCast, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Int.cast_mul, ← Finset.sum_mul, ← Int.cast_sum]
    have h1 : ∀ x : T, ∑ s, B s t * A x s = (A * B) x t := by
      intro x
      simp [Matrix.mul_apply, mul_comm]
    simp_rw [h1, hAB, Matrix.one_apply]
    simp

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in

/- English proof (translation)
Establish `h` using `congrArg (fun φ : dualLattice F => (φ : Fin i → K) j) (b.sum_toMatrix_smul_self b₂ s)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, zsmul_eq_mul] at h`. Conclude with `h.symm`.
-/
theorem basis_coe (b : Module.Basis T ℤ (dualLattice F)) (b₂ : Module.Basis T₂ ℤ (dualLattice F))
    (s : T₂) (j : Fin i) :
    (b₂ s : Fin i → K) j = ∑ t, (b.toMatrix b₂ t s : K) * (b t : Fin i → K) j := by
  have h := congrArg (fun φ : dualLattice F => (φ : Fin i → K) j) (b.sum_toMatrix_smul_self b₂ s)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, zsmul_eq_mul] at h
  exact h.symm

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in

/- English proof (translation)
Establish `h : (∑ j, C ((b₂ s : Fin i → K) j) * X j : MvPolynomial (Fin i) K) = ∑ t, (A t s : MvPolynomial (Fin i) K) * ∑ j, C ((b t : Fin i → K) j) * X j`. Simplify using `only [hA, map_sum, map_mul, map_intCast, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [dualLatticeCoord]`. Rewrite using `[h, map_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_intCast]`.
-/
theorem coord_change {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j) (s : T₂) :
    dualLatticeCoord b₂ ⟨(), s⟩ = ∑ t, (A t s : ProjField K i) * dualLatticeCoord b ⟨(), t⟩ := by
  have h : (∑ j, C ((b₂ s : Fin i → K) j) * X j : MvPolynomial (Fin i) K) =
      ∑ t, (A t s : MvPolynomial (Fin i) K) * ∑ j, C ((b t : Fin i → K) j) * X j := by
    simp only [hA, map_sum, map_mul, map_intCast, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  simp only [dualLatticeCoord]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, map_intCast]

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `hC₂ : ∀ a : ℤ, (C a : MRing (dualBlocks T₂)) = (a : MRing (dualBlocks T₂))` using `fun a => map_intCast C a`. Rewrite using `[hC₂, map_intCast, map_intCast, map_intCast]`. Consider the case `add f g hf hg => rw [map_add, map_add, map_add, hf, hg]`.

Consider the case `mul_X f p hf`. Rewrite using `[map_mul, map_mul, map_mul, hf]`. Use `congr 1`. Take `⟨⟨⟩, s⟩` from `p`. Establish `hC : ∀ a : ℤ, (C a : MRing (dualBlocks T)) = (a : MRing (dualBlocks T))` using `fun a => map_intCast C a`.

Simplify using `only [intCoordSubst, aeval_X, map_sum, map_mul, hC, map_intCast, mConeMap, coord_change hA s, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`.
-/
theorem coneMap_subst {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (f : MRing (dualBlocks T₂)) :
    mConeMap (dualLatticeCoord b) (intCoordSubst A f) = mConeMap (dualLatticeCoord b₂) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have hC₂ : ∀ a : ℤ, (C a : MRing (dualBlocks T₂)) = (a : MRing (dualBlocks T₂)) := fun a => map_intCast C a
    rw [hC₂, map_intCast, map_intCast, map_intCast]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | mul_X f p hf =>
    rw [map_mul, map_mul, map_mul, hf]
    congr 1
    obtain ⟨⟨⟩, s⟩ := p
    have hC : ∀ a : ℤ, (C a : MRing (dualBlocks T)) = (a : MRing (dualBlocks T)) := fun a => map_intCast C a
    simp only [intCoordSubst, aeval_X, map_sum, map_mul, hC, map_intCast, mConeMap, coord_change hA s,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_assoc]

omit [DecidableEq T₂] in

/- English proof (translation)
Establish `hsurj : Function.Surjective (intCoordSubst A)` using `fun f => ⟨intCoordSubst B f, subst_subst hAB f⟩`. Establish `hker : dualIdeal b₂ = (dualIdeal b).comap (intCoordSubst A)`. Use extensionality with `f`. Simplify using `only [dualIdeal, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, coneMap_subst hA]`. Rewrite using `[hker, Ideal.map_comap_of_surjective _ hsurj]`.
-/
theorem ideal_map {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1)
    {b : Module.Basis T ℤ (dualLattice F)} {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j) :
    (dualIdeal b₂).map (intCoordSubst A) = dualIdeal b := by
  have hsurj : Function.Surjective (intCoordSubst A) := fun f => ⟨intCoordSubst B f, subst_subst hAB f⟩
  have hker : dualIdeal b₂ = (dualIdeal b).comap (intCoordSubst A) := by
    ext f
    simp only [dualIdeal, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, coneMap_subst hA]
  rw [hker, Ideal.map_comap_of_surjective _ hsurj]

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in

/- English proof (translation)
Simplify using `only [dualEmbMatrix, hA, map_sum, map_mul, map_intCast]`.
-/
theorem embMatrix_apply {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (s : T₂) (p : (K →+* ℂ) × Fin i) :
    dualEmbMatrix b₂ s p = ∑ t, (A t s : ℂ) * dualEmbMatrix b t p := by
  simp only [dualEmbMatrix, hA, map_sum, map_mul, map_intCast]

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in

/- English proof (translation)
Rewrite using `[dualRecover, LinearEquiv.symm_apply_eq]`. Use `set w := dualRecover b hb (fun t => z ⟨(), t⟩)`. Establish `hw : Matrix.mulVecLin (dualEmbMatrix b) w = fun t => z ⟨(), t⟩`. Simplify using `only [w, dualRecover]`. Conclude with `LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective _ hb) _`.

Use function extensionality and compare the values at `s`. Rewrite using `[LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]`. Simplify using `only [embMatrix_apply hA, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [intCoordPt]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Establish `ht` using `congrFun hw t`. Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at ht`. Rewrite using `[← ht, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem recover_eq {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂)))
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (z : (Σ _ : Unit, T) → ℂ) :
    dualRecover b₂ hb₂ (fun s => intCoordPt A z ⟨(), s⟩) = dualRecover b hb (fun t => z ⟨(), t⟩) := by
  rw [dualRecover, LinearEquiv.symm_apply_eq]
  set w := dualRecover b hb (fun t => z ⟨(), t⟩)
  have hw : Matrix.mulVecLin (dualEmbMatrix b) w = fun t => z ⟨(), t⟩ := by
    simp only [w, dualRecover]
    exact LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective _ hb) _
  funext s
  rw [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  simp only [embMatrix_apply hA, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [intCoordPt]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht := congrFun hw t
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at ht
  rw [← ht, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

omit [DecidableEq T₂] in

/- English proof (translation)
Use `hermLine_ext rfl (funext fun z => ?_)` and prove the remaining obligations. Use `show Real.sqrt (dualNormSq b₂ hb₂ fun s => intCoordPt A z ⟨(), s⟩) = Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)`. Simplify using `only [dualNormSq, recover_eq hb hb₂ hA z]`.
-/
theorem line_eq {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂)))
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (hAB : ∃ B : Matrix T₂ T ℤ, A * B = 1) :
    intCoordLine A hAB (dualLine F b₂ hb₂) = dualLine F b hb := by
  refine hermLine_ext rfl (funext fun z => ?_)
  show Real.sqrt (dualNormSq b₂ hb₂ fun s => intCoordPt A z ⟨(), s⟩) =
    Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  simp only [dualNormSq, recover_eq hb hb₂ hA z]

end TopDualBasisChange

open TopDualBasisChange in

/- English proof (translation)
Introduce `K _ _ i F T T₂ _ _ _ _ b hb b₂ hb₂ II hi hII`. Establish `hAB : b.toMatrix b₂ * b₂.toMatrix b = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip b b₂`. Establish `hBA : b₂.toMatrix b * b.toMatrix b₂ = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip b₂ b`. Establish `h` using `hChange T T₂ (b.toMatrix b₂) (b₂.toMatrix b) hAB hBA II hII (dualIdeal b₂) i (fun _ => dualLine F b₂ hb₂) hi (DualArithVar.full K i F T₂ b₂ hi) (fun _ => (DualLineSemipositive.proof K i F T₂ b₂ hb₂).1)`. Rewrite `h` using `[ideal_map hAB (basis_coe b b₂), line_eq hb hb₂ (basis_coe b b₂)]`.

Conclude with `h.symm`.
-/
theorem DualTopBasisChange.proof (hChange : IntCoordChange.Statement) : DualTopBasisChange.Statement := by
  intro K _ _ i F T T₂ _ _ _ _ b hb b₂ hb₂ II hi hII
  have hAB : b.toMatrix b₂ * b₂.toMatrix b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b b₂
  have hBA : b₂.toMatrix b * b.toMatrix b₂ = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b₂ b
  have h := hChange T T₂ (b.toMatrix b₂) (b₂.toMatrix b) hAB hBA II hII (dualIdeal b₂) i
    (fun _ => dualLine F b₂ hb₂) hi (DualArithVar.full K i F T₂ b₂ hi)
    (fun _ => (DualLineSemipositive.proof K i F T₂ b₂ hb₂).1)
  rw [ideal_map hAB (basis_coe b b₂), line_eq hb hb₂ (basis_coe b b₂)] at h
  exact h.symm

end

end GroundTheory.Heights₂.Heights
