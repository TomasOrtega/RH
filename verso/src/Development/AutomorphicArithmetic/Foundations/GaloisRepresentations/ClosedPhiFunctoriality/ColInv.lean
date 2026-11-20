import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

/- English proof (translation)
Apply `T.eB.injective` to reduce the goal to its premises. Rewrite using `[T.actB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`.
-/
private theorem actQ_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (g : GQ l)
    (y : Per.Bcris l) : P.actQ g (T.eB.symm y) = T.eB.symm (Per.σB g y) := by
  apply T.eB.injective
  rw [T.actB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/- English proof (translation)
Apply `T.eB.injective` to reduce the goal to its premises. Rewrite using `[T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`.
-/
private theorem phiB_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (y : Per.Bcris l) : P.φB (T.eB.symm y) = T.eB.symm (Per.φB l y) := by
  apply T.eB.injective
  rw [T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/- English proof (translation)
Apply `T.eB.injective` to reduce the goal to its premises. Rewrite using `[Algebra.smul_def, map_mul, T.zB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`.
-/
private theorem smul_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l])
    (y : Per.Bcris l) : (z : ℚ_[l]) • T.eB.symm y = T.eB.symm (Per.zB l z * y) := by
  apply T.eB.injective
  rw [Algebra.smul_def, map_mul, T.zB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[← smul_symm T z y]`. Conclude with `Polynomial.smul_C (z : ℚ_[l]) (T.eB.symm y)`.
-/
private theorem smul_Cst {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l])
    (y : Per.Bcris l) : (z : ℚ_[l]) • (Polynomial.C (T.eB.symm y) : Bst P) = Polynomial.C (T.eB.symm (Per.zB l z * y)) := by
  rw [← smul_symm T z y]
  exact Polynomial.smul_C (z : ℚ_[l]) (T.eB.symm y)

/- English proof (translation)
Rewrite using `[map_sum T.eB.symm]`. Conclude with `(map_sum (Polynomial.C : P.R.B →+* Polynomial P.R.B) _ _).symm`.
-/
private theorem sum_Cst {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {ι : Type}
    (s : Finset ι) (f : ι → Per.Bcris l) :
    ∑ i ∈ s, (Polynomial.C (T.eB.symm (f i)) : Bst P) = Polynomial.C (T.eB.symm (∑ i ∈ s, f i)) := by
  rw [map_sum T.eB.symm]
  exact (map_sum (Polynomial.C : P.R.B →+* Polynomial P.R.B) _ _).symm

/- English proof (translation)
Introduce `l _ P AI T K L a d ρ R v hv U hU j`. Use `⟨?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_Dst]`. Introduce `g`. Establish `hinv : ∀ i', ∑ i, Per.zB l ((ρ g).val i' i) * Per.σB (g : GQ l) (U i j) = U i' j` using `fun i' => by`.

Establish `h` using `congrFun (congrFun (hU.inv g) i') j`. Simplify `h` using `[Matrix.mul_apply, Matrix.map_apply]`. Rewrite using `[map_sum]`. Establish `step : ∀ i, (stRep P R g) (v i ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (U i j)) : Bst P)) = ∑ i', v i' ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (Per.zB l ((ρ g).val i' i) * Per.σB (g : GQ l) (U i j))) : Bst P)` using `fun i => by`. Rewrite using `[stRep_tmul, actSt_C, actQ_symm T, hv, TensorProduct.sum_tmul]`.

Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_Cst T, TensorProduct.smul_tmul]`. Simplify using `only [step]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations.

Rewrite using `[← TensorProduct.tmul_sum, sum_Cst T, hinv]`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[phiV_tmul, phiSt_C, phiB_symm T, pow_succ', RingHom.mul_def, RingHom.comp_apply]`.
-/
theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.colInv_holds :
    ColInv := by
  intro l _ P AI T K L a d ρ R v hv U hU j
  refine ⟨?_, fun n => ?_⟩
  · rw [mem_Dst]
    intro g
    have hinv : ∀ i', ∑ i, Per.zB l ((ρ g).val i' i) * Per.σB (g : GQ l) (U i j) = U i' j := fun i' => by
      have h := congrFun (congrFun (hU.inv g) i') j
      simpa [Matrix.mul_apply, Matrix.map_apply] using h
    rw [map_sum]
    have step : ∀ i, (stRep P R g) (v i ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (U i j)) : Bst P)) =
        ∑ i', v i' ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (Per.zB l ((ρ g).val i' i) * Per.σB (g : GQ l) (U i j))) : Bst P) := fun i => by
      rw [stRep_tmul, actSt_C, actQ_symm T, hv, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [← smul_Cst T, TensorProduct.smul_tmul]
    simp only [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [← TensorProduct.tmul_sum, sum_Cst T, hinv]
  · induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [phiV_tmul, phiSt_C, phiB_symm T, pow_succ', RingHom.mul_def, RingHom.comp_apply]
