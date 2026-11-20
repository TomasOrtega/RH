import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistablePeriodMatrixOfIsSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixCrystallineModuleOverWitt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulUnramifiedEqWittBcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariants
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKurOfActStFixed
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.StU

open Polynomial

section Gen
variable {d : ℕ}

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_eq_of {S : Type} [CommRing S] (Qm Qi R A Ai : Matrix (Fin d) (Fin d) S) (h1 : Qi * Qm = 1)
    (h2 : R * A = Qm) (h3 : A * Ai = 1) : Ai = Qi * R := by
  calc Ai = (Qi * Qm) * Ai := by rw [h1, Matrix.one_mul]
    _ = Qi * R * (A * Ai) := by rw [← h2]; simp only [Matrix.mul_assoc]
    _ = Qi * R := by rw [h3, Matrix.mul_one]

/- English proof (translation)
The claim follows from `Matrix.map_mul (f := (f : S →+* S'))`.
-/
theorem mmap_mul {S S' F : Type} [CommRing S] [CommRing S'] [FunLike F S S'] [RingHomClass F S S'] (f : F)
    (A B : Matrix (Fin d) (Fin d) S) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : S →+* S'))

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero f) (map_one f)`.
-/
theorem mmap_one {S S' F : Type} [CommRing S] [CommRing S'] [FunLike F S S'] [RingHomClass F S S'] (f : F) :
    (1 : Matrix (Fin d) (Fin d) S).map f = 1 :=
  Matrix.map_one _ (map_zero f) (map_one f)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp only [pow_zero]`. Conclude with `mmap_one f`. Consider the case `succ k ih => rw [pow_succ, mmap_mul, ih, pow_succ]`.
-/
theorem mmap_pow {S S' F : Type} [CommRing S] [CommRing S'] [FunLike F S S'] [RingHomClass F S S'] (f : F)
    (A : Matrix (Fin d) (Fin d) S) (k : ℕ) : (A ^ k).map f = A.map f ^ k := by
  induction k with
  | zero => simp only [pow_zero]; exact mmap_one f
  | succ k ih => rw [pow_succ, mmap_mul, ih, pow_succ]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.sum_apply, map_sum]`.
-/
theorem mmap_sum_smul {S S' F : Type} [CommRing S] [CommRing S'] [FunLike F S S'] [RingHomClass F S S'] (f : F)
    (N : ℕ) (a : ℕ → S) (X : ℕ → Matrix (Fin d) (Fin d) S) :
    (∑ k ∈ Finset.range N, a k • X k).map f = ∑ k ∈ Finset.range N, f (a k) • (X k).map f := by
  ext i j
  simp [Matrix.sum_apply, map_sum]

/- English proof (translation)
Establish `h` using `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hx`. Establish `h2 : x.charpoly = Polynomial.X ^ Fintype.card (Fin d)` using `sub_eq_zero.1 h.eq_zero`. Establish `h3` using `Matrix.aeval_self_charpoly x`. Rewrite `h3` using `[h2, map_pow, Polynomial.aeval_X, Fintype.card_fin]`. Conclude with `h3`.
-/
theorem pow_eq_zero_field {k : Type} [Field k] (x : Matrix (Fin d) (Fin d) k) (hx : IsNilpotent x) : x ^ d = 0 := by
  have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hx
  have h2 : x.charpoly = Polynomial.X ^ Fintype.card (Fin d) := sub_eq_zero.1 h.eq_zero
  have h3 := Matrix.aeval_self_charpoly x
  rw [h2, map_pow, Polynomial.aeval_X, Fintype.card_fin] at h3
  exact h3

end Gen

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {d : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, derivative_mul, hB]`.
-/
theorem deriv_mul_const (A B : Matrix (Fin d) (Fin d) (Bst P)) (hB : ∀ i j, derivative (B i j) = 0) :
    (A * B).map derivative = A.map derivative * B := by
  ext i j
  simp [Matrix.mul_apply, derivative_mul, hB]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, derivative_mul, hB]`.
-/
theorem deriv_const_mul (A B : Matrix (Fin d) (Fin d) (Bst P)) (hB : ∀ i j, derivative (B i j) = 0) :
    (B * A).map derivative = B * A.map derivative := by
  ext i j
  simp [Matrix.mul_apply, derivative_mul, hB]

/- English proof (translation)
Rewrite using `[Polynomial.algebraMap_apply, Polynomial.derivative_C]`.
-/
theorem deriv_algebraMap (x : ℚ_[l]) : derivative (algebraMap ℚ_[l] (Bst P) x) = 0 := by
  rw [Polynomial.algebraMap_apply, Polynomial.derivative_C]

/- English proof (translation)
Rewrite using `[Polynomial.algebraMap_apply, Polynomial.derivative_C]`.
-/
theorem deriv_kur (x : ↥(MaximalUnramifiedExtension l)) : derivative (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) x) = 0 := by
  rw [Polynomial.algebraMap_apply, Polynomial.derivative_C]

/- English proof (translation)
Rewrite using `[Polynomial.algebraMap_apply, eval_C]`.
-/
theorem eval_kur (r : P.R.B) (x : ↥(MaximalUnramifiedExtension l)) : eval r (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) x) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B x := by
  rw [Polynomial.algebraMap_apply, eval_C]

/- English proof (translation)
Use `monSt_actSt P g p` as an intermediate fact. Simplify using `only [monSt_apply, map_neg] at this`. Conclude with `neg_injective this`.
-/
theorem deriv_actSt (g : GQ l) (p : Bst P) : derivative (actSt P g p) = actSt P g (derivative p) := by
  have := monSt_actSt P g p
  simp only [monSt_apply, map_neg] at this
  exact neg_injective this

section Inv
variable {K : FinExt l} (R : ↥(GK K) → Matrix (Fin d) (Fin d) ℚ_[l]) (Qm Qi : Matrix (Fin d) (Fin d) (Bst P))

/- English proof (translation)
The claim follows from `inv_eq_of Qm Qi _ _ _ (mul_eq_one_comm.1 hQQ) (hQ g) (by rw [← mmap_mul, hQQ, mmap_one])`.
-/
theorem inv_act (hQQ : Qm * Qi = 1)
    (hQ : ∀ g : ↥(GK K), (R g).map (algebraMap ℚ_[l] (Bst P)) * Qm.map (actSt P (g : GQ l)) = Qm) (g : ↥(GK K)) :
    Qi.map (actSt P (g : GQ l)) = Qi * (R g).map (algebraMap ℚ_[l] (Bst P)) :=
  inv_eq_of Qm Qi _ _ _ (mul_eq_one_comm.1 hQQ) (hQ g) (by rw [← mmap_mul, hQQ, mmap_one])

/- English proof (translation)
Establish `hD : (Qm.map derivative).map (actSt P (g : GQ l)) = (Qm.map (actSt P (g : GQ l))).map derivative`. Use extensionality with `i j`. Simplify using `[deriv_actSt]`. Establish `hRD : (R g).map (algebraMap ℚ_[l] (Bst P)) * (Qm.map (actSt P (g : GQ l))).map derivative = Qm.map derivative`. Rewrite using `[← deriv_const_mul P _ _ (fun i j => by simp only [Matrix.map_apply]; exact deriv_algebraMap P _), hQ g]`.

Rewrite using `[mmap_mul, hD, inv_act P R Qm Qi hQQ hQ g, Matrix.mul_assoc, hRD]`.
-/
theorem M_fixed (hQQ : Qm * Qi = 1)
    (hQ : ∀ g : ↥(GK K), (R g).map (algebraMap ℚ_[l] (Bst P)) * Qm.map (actSt P (g : GQ l)) = Qm) (g : ↥(GK K)) :
    (Qi * Qm.map derivative).map (actSt P (g : GQ l)) = Qi * Qm.map derivative := by
  have hD : (Qm.map derivative).map (actSt P (g : GQ l)) = (Qm.map (actSt P (g : GQ l))).map derivative := by
    ext i j; simp [deriv_actSt]
  have hRD : (R g).map (algebraMap ℚ_[l] (Bst P)) * (Qm.map (actSt P (g : GQ l))).map derivative =
      Qm.map derivative := by
    rw [← deriv_const_mul P _ _ (fun i j => by simp only [Matrix.map_apply]; exact deriv_algebraMap P _), hQ g]
  rw [mmap_mul, hD, inv_act P R Qm Qi hQQ hQ g, Matrix.mul_assoc, hRD]

/- English proof (translation)
Establish `hc : ∀ A : Matrix (Fin d) (Fin d) (Bst P), (A.map (phiSt P)).map (actSt P (g : GQ l)) = (A.map (actSt P (g : GQ l))).map (phiSt P)`. Introduce `A`. Use extensionality with `i j`. Simplify using `[phiSt_actSt]`. Establish `hRφ : ((R g).map (algebraMap ℚ_[l] (Bst P))).map (phiSt P) = (R g).map (algebraMap ℚ_[l] (Bst P))`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Rewrite using `[mmap_mul, hc, inv_act P R Qm Qi hQQ hQ g, Matrix.mul_assoc, ← hRφ, ← mmap_mul, hQ g]`. Rewrite using `[mmap_mul, hc, inv_act P R Qm Qi hQQ hQ g, mmap_mul, hRφ, Matrix.mul_assoc, hQ g]`.
-/
theorem Phi_fixed (hQQ : Qm * Qi = 1)
    (hQ : ∀ g : ↥(GK K), (R g).map (algebraMap ℚ_[l] (Bst P)) * Qm.map (actSt P (g : GQ l)) = Qm) (g : ↥(GK K)) :
    (Qi * Qm.map (phiSt P)).map (actSt P (g : GQ l)) = Qi * Qm.map (phiSt P) ∧
    (Qi.map (phiSt P) * Qm).map (actSt P (g : GQ l)) = Qi.map (phiSt P) * Qm := by
  have hc : ∀ A : Matrix (Fin d) (Fin d) (Bst P),
      (A.map (phiSt P)).map (actSt P (g : GQ l)) = (A.map (actSt P (g : GQ l))).map (phiSt P) := by
    intro A; ext i j; simp [phiSt_actSt]
  have hRφ : ((R g).map (algebraMap ℚ_[l] (Bst P))).map (phiSt P) = (R g).map (algebraMap ℚ_[l] (Bst P)) := by
    ext i j; simp
  constructor
  · rw [mmap_mul, hc, inv_act P R Qm Qi hQQ hQ g, Matrix.mul_assoc, ← hRφ, ← mmap_mul, hQ g]
  · rw [mmap_mul, hc, inv_act P R Qm Qi hQQ hQ g, mmap_mul, hRφ, Matrix.mul_assoc, hQ g]

end Inv

/- English proof (translation)
Establish `h : ∀ i j, ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c = Y i j` using `fun i j => exists_kur_of_actSt_fixed P K hK (Y i j) fun g hg => by`. Simplify using `using congrFun (congrFun (hY ⟨g, hg⟩) i) j`. Use `choose y hy using h`. Use `⟨Matrix.of y, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `[hy]`. Introduce `g`. Use extensionality with `i j`. Establish `h1` using `congrFun (congrFun (hY g) i) j`. Simplify using `only [Matrix.map_apply] at h1`.

Rewrite `h1` using `[← hy, Polynomial.algebraMap_apply, actSt_C]`. Simplify using `using Polynomial.C_injective h1`.
-/
theorem const_of_fixed {K : FinExt l}
    (hK : ∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB)
    (Y : Matrix (Fin d) (Fin d) (Bst P)) (hY : ∀ g : ↥(GK K), Y.map (actSt P (g : GQ l)) = Y) :
    ∃ y : Matrix (Fin d) (Fin d) ↥(MaximalUnramifiedExtension l), Y = y.map (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P)) ∧
      ∀ g : ↥(GK K), (y.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map (P.actQ (g : GQ l)) =
        y.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := by
  have h : ∀ i j, ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c = Y i j := fun i j =>
    exists_kur_of_actSt_fixed P K hK (Y i j) fun g hg => by
      simpa using congrFun (congrFun (hY ⟨g, hg⟩) i) j
  choose y hy using h
  refine ⟨Matrix.of y, ?_, ?_⟩
  · ext i j; simp [hy]
  · intro g; ext i j
    have h1 := congrFun (congrFun (hY g) i) j
    simp only [Matrix.map_apply] at h1
    rw [← hy, Polynomial.algebraMap_apply, actSt_C] at h1
    simpa using Polynomial.C_injective h1

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => ext i j`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Establish `hD : Qm.map derivative = Qm * y.map (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P))`.

Rewrite using `[← hM, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]`. Establish `e : Qm.map (derivative^[k+1]) = (Qm.map (derivative^[k])).map derivative`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Function.iterate_succ_apply']`. Rewrite using `[e, ih, deriv_mul_const P _ _ (fun i j => ?_), hD, pow_succ', Matrix.mul_assoc]`.

Rewrite using `[← mmap_pow, Matrix.map_apply]`. Conclude with `deriv_kur P _`.
-/
theorem iter_deriv (Qm Qi : Matrix (Fin d) (Fin d) (Bst P)) (hQQ : Qm * Qi = 1) (y : Matrix (Fin d) (Fin d) ↥(MaximalUnramifiedExtension l))
    (hM : Qi * Qm.map derivative = y.map (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P))) (k : ℕ) :
    Qm.map (derivative^[k]) = Qm * (y.map (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P))) ^ k := by
  induction k with
  | zero => ext i j; simp
  | succ k ih =>
    have hD : Qm.map derivative = Qm * y.map (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P)) := by
      rw [← hM, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    have e : Qm.map (derivative^[k+1]) = (Qm.map (derivative^[k])).map derivative := by
      ext i j; simp only [Matrix.map_apply, Function.iterate_succ_apply']
    rw [e, ih, deriv_mul_const P _ _ (fun i j => ?_), hD, pow_succ', Matrix.mul_assoc]
    rw [← mmap_pow, Matrix.map_apply]
    exact deriv_kur P _

/- English proof (translation)
Establish `hgb : P.actQ g b = b + c • P.tB - (kummer P g : ℚ_[l]) • P.tB`. Use `congrArg (Polynomial.eval 0) hb` as an intermediate fact. Simplify using `at this`. Take the linear combination `this`. Establish `h` using `Polynomial.ringHom_ext (f := (Polynomial.evalRingHom (-(c • P.tB) + -b)).comp (actSt P g).toRingHom) (g := (P.actQ g : P.R.B →+* P.R.B).comp (Polynomial.evalRingHom (-b))) (fun a => by simp) (by`.

Simplify using `[hgb]`. Use the proof step `ring)`. Conclude with `RingHom.congr_fun h p`.
-/
theorem ev_actSt (b : P.R.B) (c : ℚ_[l]) (g : GQ l)
    (hb : actSt P g (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C (c • P.tB))
    (p : Bst P) : Polynomial.eval (-(c • P.tB) + -b) (actSt P g p) = P.actQ g (Polynomial.eval (-b) p) := by
  have hgb : P.actQ g b = b + c • P.tB - (kummer P g : ℚ_[l]) • P.tB := by
    have := congrArg (Polynomial.eval 0) hb
    simp at this
    linear_combination this
  have h := Polynomial.ringHom_ext (f := (Polynomial.evalRingHom (-(c • P.tB) + -b)).comp (actSt P g).toRingHom)
    (g := (P.actQ g : P.R.B →+* P.R.B).comp (Polynomial.evalRingHom (-b))) (fun a => by simp) (by
      simp [hgb]; ring)
  exact RingHom.congr_fun h p

/- English proof (translation)
Establish `hφb : P.φB b = (l : P.R.B) * b`. Use `congrArg (Polynomial.eval 0) hb` as an intermediate fact. Simplify using `using this`. Establish `h` using `Polynomial.ringHom_ext (f := (Polynomial.evalRingHom (-b)).comp (phiSt P).toRingHom) (g := (P.φB : P.R.B →+* P.R.B).comp (Polynomial.evalRingHom (-b))) (fun a => by simp) (by`. Simplify using `[hφb])`.

Conclude with `RingHom.congr_fun h p`.
-/
theorem ev_phiSt (b : P.R.B)
    (hb : phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b))
    (p : Bst P) : Polynomial.eval (-b) (phiSt P p) = P.φB (Polynomial.eval (-b) p) := by
  have hφb : P.φB b = (l : P.R.B) * b := by
    have := congrArg (Polynomial.eval 0) hb
    simpa using this
  have h := Polynomial.ringHom_ext (f := (Polynomial.evalRingHom (-b)).comp (phiSt P).toRingHom)
    (g := (P.φB : P.R.B →+* P.R.B).comp (Polynomial.evalRingHom (-b))) (fun a => by simp) (by
      simp [hφb])
  exact RingHom.congr_fun h p

/- English proof (translation)
Rewrite using `[← Polynomial.taylor_eval, Polynomial.eval_eq_sum_range' (by rwa [Polynomial.natDegree_taylor])]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.taylor_coeff, mul_comm, mul_assoc]`. Use `congr 1`. Establish `h` using `congrFun (Polynomial.factorial_smul_hasseDeriv (R := P.R.B) k) p`.

Rewrite `h` using `[LinearMap.smul_apply]`. Rewrite using `[← h, Polynomial.eval_smul, ← Algebra.smul_def, ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ (by exact_mod_cast k.factorial_ne_zero), one_smul]`.
-/
theorem taylor_sum (r s : P.R.B) (p : Bst P) (N : ℕ) (hN : p.natDegree < N) :
    Polynomial.eval (s + r) p = ∑ k ∈ Finset.range N,
      (s ^ k * algebraMap ℚ_[l] P.R.B ((k.factorial : ℚ_[l])⁻¹)) * Polynomial.eval r (derivative^[k] p) := by
  rw [← Polynomial.taylor_eval, Polynomial.eval_eq_sum_range' (by rwa [Polynomial.natDegree_taylor])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.taylor_coeff, mul_comm, mul_assoc]
  congr 1
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := P.R.B) k) p
  rw [LinearMap.smul_apply] at h
  rw [← h, Polynomial.eval_smul, ← Algebra.smul_def, ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast k.factorial_ne_zero), one_smul]

/- English proof (translation)
Introduce `l _ K bk P AI T C hF d ρ b c ⟨hact, hphi⟩ hS`. Take `⟨Q, hQ⟩` from `GlobalTheory.PMon.exists_periodMatrix_of_isSst l P AI T (Fin d) K _ (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ) hS`. Use `set R : ↥(GK K) → Matrix (Fin d) (Fin d) ℚ_[l] := fun g => (ρ g).val.map (fun z => (z : ℚ_[l])) with hRdef`. Establish `hR : ∀ g, LinearMap.toMatrix (Pi.basisFun ℚ_[l] (Fin d)) (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ g) = R g`. Introduce `g`.

Use extensionality with `i j`. Simplify using `[qRep, R, LinearMap.toMatrix_eq_toMatrix']`. Use `set Qm : Matrix (Fin d) (Fin d) (Bst P) := (Q : Matrix (Fin d) (Fin d) (Bst P)) with hQmdef`. Use `set Qi : Matrix (Fin d) (Fin d) (Bst P) := ((Q⁻¹ : GL (Fin d) (Bst P)) : Matrix (Fin d) (Fin d) (Bst P)) with hQidef`. Establish `hQQ : Qm * Qi = 1` using `by simp [Qm, Qi]`.

Establish `hQ' : ∀ g : ↥(GK K), (R g).map (algebraMap ℚ_[l] (Bst P)) * Qm.map (actSt P (g : GQ l)) = Qm` using `fun g => by rw [← hR]; exact hQ g`. Establish `hK` using `GlobalTheory.Pst.NoLog.kummer_not_coboundary l P AI T K`. Take `⟨y, hy, hyfix⟩` from `const_of_fixed P hK _ (M_fixed P R Qm Qi hQQ hQ')`. Take `⟨yF, hyF, hyFfix⟩` from `const_of_fixed P hK _ (fun g => (Phi_fixed P R Qm Qi hQQ hQ' g).1)`. Take `⟨yF', hyF', hyF'fix⟩` from `const_of_fixed P hK _ (fun g => (Phi_fixed P R Qm Qi hQQ hQ' g).2)`.

Use `set N := max d (Finset.univ.sup (fun p : Fin d × Fin d => (Qm p.1 p.2).natDegree) + 1) with hNdef`. Establish `hN : ∀ i j, (Qm i j).natDegree < N` using `fun i j => lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := fun p : Fin d × Fin d => (Qm p.1 p.2).natDegree) (Finset.mem_univ (i, j)))) (le_max_right _ _)`. Establish `hdN : d ≤ N` using `le_max_left _ _`. Use `set ev0 : Bst P →+* P.R.B := Polynomial.evalRingHom (-b) with hev0`. Use `set U₀ := Qm.map ev0 with hU₀`.

Use `set U₀' := Qi.map ev0 with hU₀'`. Use `set m := y.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hm`. Establish `hU : U₀ * U₀' = 1` using `by rw [← mmap_mul, hQQ, mmap_one]`. Establish `hU' : U₀' * U₀ = 1` using `mul_eq_one_comm.1 hU`. Establish `hym : (y.map (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P))).map ev0 = m`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, hev0, Polynomial.coe_evalRingHom, eval_kur, hm]`. Establish `hdk : ∀ k, (Qm.map (derivative^[k])).map ev0 = U₀ * m ^ k` using `fun k => by`. Rewrite using `[iter_deriv P Qm Qi hQQ y hy k, mmap_mul, mmap_pow, hym]`. Establish `hmN : m ^ N = 0`.

Establish `h0 : Qm.map (derivative^[N]) = 0`. Use extensionality with `i j`. Simplify using `[Polynomial.iterate_derivative_eq_zero (hN i j)]`. Establish `h1` using `hdk N`. Rewrite `h1` using `[h0, Matrix.map_zero _ (map_zero _)]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hgal : ∀ g : ↥(GK K), (R g).map (algebraMap ℚ_[l] P.R.B) * U₀.map (P.actQ (g : GQ l)) = ∑ k ∈ Finset.range N, ((-((c g : ℚ_[l]) • P.tB)) ^ k * algebraMap ℚ_[l] P.R.B ((k.factorial : ℚ_[l])⁻¹)) • (U₀ * m ^ k)`. Introduce `g`. Use `set eg : Bst P →+* P.R.B := Polynomial.evalRingHom (-((c g : ℚ_[l]) • P.tB) + -b) with heg`. Establish `h1` using `congrArg (fun A => Matrix.map A eg) (hQ' g)`.

Simplify using `only [mmap_mul] at h1`. Establish `e1 : ((R g).map (algebraMap ℚ_[l] (Bst P))).map eg = (R g).map (algebraMap ℚ_[l] P.R.B)`. Use extensionality with `i j`. Simplify using `[heg]`. Establish `e2 : (Qm.map (actSt P (g : GQ l))).map eg = U₀.map (P.actQ (g : GQ l))`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, heg, Polynomial.coe_evalRingHom, hU₀, hev0]`. Conclude with `ev_actSt P b _ _ (hact g) _`. Rewrite `h1` using `[e1, e2]`. Rewrite using `[h1]`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, heg, Polynomial.coe_evalRingHom, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[taylor_sum P (-b) _ _ N (hN i j)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `congr 1`.

Use `congrFun (congrFun (hdk k) i) j` as an intermediate fact. Simplify `this` using `only [Matrix.map_apply, hev0, Polynomial.coe_evalRingHom]`. Use `set f := yF.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hf`. Use `set f' := yF'.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hf'`. Establish `hevk : ∀ z : Matrix (Fin d) (Fin d) ↥(MaximalUnramifiedExtension l), (z.map (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P))).map ev0 = z.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)`.

Introduce `z`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, hev0, Polynomial.coe_evalRingHom, eval_kur]`. Establish `hevφ : ∀ A : Matrix (Fin d) (Fin d) (Bst P), (A.map (phiSt P)).map ev0 = (A.map ev0).map P.φB`. Introduce `A`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, hev0, Polynomial.coe_evalRingHom]`. Conclude with `ev_phiSt P b hphi _`. Establish `hφ : U₀.map P.φB = U₀ * f`. Establish `e : Qm.map (phiSt P) = Qm * (Qi * Qm.map (phiSt P))` using `by rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]`.

Use `congrArg (fun A => Matrix.map A ev0) e` as an intermediate fact. Rewrite `this` using `[hevφ, hyF, mmap_mul, hevk]`. Conclude with `this`. Establish `hφ' : U₀'.map P.φB * U₀ = f'`. Use `congrArg (fun A => Matrix.map A ev0) hyF'` as an intermediate fact.

Rewrite `this` using `[mmap_mul, hevφ, hevk]`. Conclude with `this`. Establish `hff : f * f' = 1`. Establish `e : f = U₀' * U₀.map P.φB` using `by rw [hφ, ← Matrix.mul_assoc, hU', Matrix.one_mul]`. Rewrite using `[e, ← hφ']`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mmap_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hU, mmap_one, Matrix.mul_one, hU']`. Establish `hC` using `(GlobalTheory.MemLoc.fits_inv l P AI T C hF).1`.

Use `set e : P.R.B →+* Per.Bcris l := T.eB.toRingHom with he`. Use `set aw : Wq l bk.a →+* Per.Bcris l := (Per.aB l).comp (wA l bk.a).toRingHom with haw`. Establish `hent : ∀ G : Matrix (Fin d) (Fin d) P.R.B, (∀ g : ↥(GK K), G.map (P.actQ (g : GQ l)) = G) → ∀ i j, ∃ (n : ℕ) (w : Wq l bk.a), ((l : ℕ) : Per.Bcris l) ^ n * (G.map e) i j = aw w`. Introduce `G hG i j`. Take `⟨x, hxK, hx⟩` from `hC K (e (G i j)) fun g hg => by`.

Establish `h1` using `congrFun (congrFun (hG ⟨g, hg⟩) i) j`. Simplify using `only [Matrix.map_apply] at h1`. Simplify using `only [he, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]`. Rewrite using `[← T.actB, h1]`. Take `⟨n, w, hw⟩` from `GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB l K bk C x hxK`.

Conclude with `⟨n, w, by rw [Matrix.map_apply, ← hx, hw]; rfl⟩`. Take `⟨k₁, F, hF1⟩` from `GlobalTheory.SeedF.clear_den aw _ (hent f hyFfix)`. Take `⟨k₂, F', hF2⟩` from `GlobalTheory.SeedF.clear_den aw _ (hent f' hyF'fix)`. Take `⟨k, Fm, hFm⟩` from `GlobalTheory.SeedF.clear_den aw _ (hent m hyfix)`. Establish `hinj : Function.Injective (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)` using `by haveI := nontrivial_B P; exact (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective`.

Establish `hyN : y ^ N = 0`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Use `show (y ^ N).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) = (0 : Matrix (Fin d) (Fin d) ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)`. Rewrite using `[mmap_pow, Matrix.map_zero _ (map_zero _)]`. Conclude with `hmN`.

Establish `hyd : y ^ d = 0` using `pow_eq_zero_field y ⟨N, hyN⟩`. Establish `hmd : (m.map e) ^ d = 0`. Rewrite using `[← mmap_pow, hm, ← mmap_pow, hyd, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]`. Establish `hFmd : Fm ^ d = 0`. Apply `Matrix.map_injective (GlobalTheory.SeedF.aw_injective C bk.a)` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(Fm ^ d).map aw = (0 : Matrix (Fin d) (Fin d) (Wq l bk.a)).map aw`. Rewrite using `[mmap_pow, ← hFm, _root_.smul_pow, hmd, smul_zero, Matrix.map_zero _ (map_zero _)]`. Use `set Mn := -Fm with hMn`. Establish `hMnd : Mn ^ d = 0` using `by rw [hMn, neg_pow, hFmd, mul_zero]`. Use `⟨U₀.map e, U₀'.map e, k₁, k₁ + k₂, k, F, F', Mn, ?_, ?_, ?_, hMnd, ?_⟩` and prove the remaining obligations.

Rewrite using `[← mmap_mul, hU, mmap_one]`. Apply `Matrix.map_injective (GlobalTheory.SeedF.aw_injective C bk.a)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(F * F').map aw = (((l : ℕ) : Wq l bk.a) ^ (k₁ + k₂) • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))).map aw`. Rewrite using `[mmap_mul, ← hF1, ← hF2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, ← mmap_mul, hff, mmap_one]`. Use extensionality with `i j`.

Simplify using `only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hφe : (U₀.map e).map (Per.φB l) = (U₀.map P.φB).map e`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, he, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]`.

Conclude with `(T.frob _).symm`. Rewrite using `[hφe, hφ, mmap_mul, ← hF1, Matrix.mul_smul]`. Introduce `g`. Establish `hz : (ρ g).val.map (Per.zB l) = ((R g).map (algebraMap ℚ_[l] P.R.B)).map e`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, hRdef, he, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]`. Conclude with `(T.zB _).symm`. Establish `hσ : (U₀.map e).map (Per.σB (g : GQ l)) = (U₀.map (P.actQ (g : GQ l))).map e`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, he, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]`.

Conclude with `(T.actB _ _).symm`. Establish `hMa : Mn.map aw = -(((l : ℕ) : Per.Bcris l) ^ k • m.map e)`. Rewrite using `[hFm]`. Use extensionality with `i j`. Simplify using `[hMn]`.

Establish `hl0 : ((l : ℕ) : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Establish `he1 : e ((c g : ℚ_[l]) • P.tB) = Per.zB l (c g) * C.tB`. Rewrite using `[Algebra.smul_def, map_mul, ← hF.t]`. Simplify using `only [he, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]`. Rewrite using `[T.zB]`.

Establish `hterm : ∀ i : ℕ, e ((-((c g : ℚ_[l]) • P.tB)) ^ i * algebraMap ℚ_[l] P.R.B ((i.factorial : ℚ_[l])⁻¹)) • (U₀.map e * (m.map e) ^ i) = U₀.map e * ((C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map aw) ^ i)`. Introduce `i`. Establish `hn : ((i.factorial : ℕ) : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 i.factorial_ne_zero`. Establish `hinv : e (algebraMap ℚ_[l] P.R.B ((i.factorial : ℚ_[l])⁻¹)) = C.qB ((i.factorial : ℚ_[l])⁻¹)`. Establish `h1 : e (algebraMap ℚ_[l] P.R.B ((i.factorial : ℚ_[l])⁻¹)) * ((i.factorial : ℕ) : Per.Bcris l) = 1`.

Rewrite using `[← map_natCast e, ← map_natCast (algebraMap ℚ_[l] P.R.B), ← map_mul, ← map_mul, inv_mul_cancel₀ hn, map_one, map_one]`. Establish `h2 : ((i.factorial : ℕ) : Per.Bcris l) * C.qB ((i.factorial : ℚ_[l])⁻¹) = 1`. Rewrite using `[← map_natCast C.qB, ← map_mul, mul_inv_cancel₀ hn, map_one]`. Conclude with `left_inv_eq_right_inv h1 h2`. Establish `hq : C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * ((l : ℕ) : Per.Bcris l) ^ (k * i) = C.qB ((i.factorial : ℚ_[l])⁻¹)`.

Rewrite using `[← map_natCast C.qB l, ← map_pow, ← map_mul, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl0), mul_one]`. Rewrite using `[hMa, ← neg_smul (((l : ℕ) : Per.Bcris l) ^ k) (m.map e), _root_.smul_pow (-(((l : ℕ) : Per.Bcris l) ^ k)) (m.map e) i, smul_smul, Matrix.mul_smul]`. Use `congr 1`. Rewrite using `[map_mul, map_pow, map_neg, he1, hinv, ← hq, neg_pow, neg_pow (((l : ℕ) : Per.Bcris l) ^ k), ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hz, hσ, ← mmap_mul, hgal g, mmap_sum_smul]`. Simplify using `only [mmap_mul, mmap_pow]`. Rewrite using `[Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]`. Use `congr 1`. Rewrite using `[← Finset.sum_range_add_sum_Ico _ hdN, Finset.sum_eq_zero (s := Finset.Ico d N), add_zero]`.

Introduce `i hi`. Rewrite using `[← mmap_pow, pow_eq_zero_of_le (Finset.mem_Ico.1 hi).1 hMnd, Matrix.map_zero _ (map_zero _), smul_zero]`.
-/
theorem period_matrix_at_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) → IsSst P (qRep ρ) → ∃ (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (c₁ c₃ k : ℕ) (F F' Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)), U * U' = 1 ∧ F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) ∧ Mn ^ d = 0 ∧ ∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i := by
  intro l _ K bk P AI T C hF d ρ b c ⟨hact, hphi⟩ hS
  obtain ⟨Q, hQ⟩ := GlobalTheory.PMon.exists_periodMatrix_of_isSst l P AI T (Fin d) K _ (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ) hS
  set R : ↥(GK K) → Matrix (Fin d) (Fin d) ℚ_[l] := fun g => (ρ g).val.map (fun z => (z : ℚ_[l])) with hRdef
  have hR : ∀ g, LinearMap.toMatrix (Pi.basisFun ℚ_[l] (Fin d)) (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ g) = R g := by
    intro g; ext i j; simp [qRep, R, LinearMap.toMatrix_eq_toMatrix']
  set Qm : Matrix (Fin d) (Fin d) (Bst P) := (Q : Matrix (Fin d) (Fin d) (Bst P)) with hQmdef
  set Qi : Matrix (Fin d) (Fin d) (Bst P) := ((Q⁻¹ : GL (Fin d) (Bst P)) : Matrix (Fin d) (Fin d) (Bst P)) with hQidef
  have hQQ : Qm * Qi = 1 := by simp [Qm, Qi]
  have hQ' : ∀ g : ↥(GK K), (R g).map (algebraMap ℚ_[l] (Bst P)) * Qm.map (actSt P (g : GQ l)) = Qm :=
    fun g => by rw [← hR]; exact hQ g
  have hK := GlobalTheory.Pst.NoLog.kummer_not_coboundary l P AI T K
  obtain ⟨y, hy, hyfix⟩ := const_of_fixed P hK _ (M_fixed P R Qm Qi hQQ hQ')
  obtain ⟨yF, hyF, hyFfix⟩ := const_of_fixed P hK _ (fun g => (Phi_fixed P R Qm Qi hQQ hQ' g).1)
  obtain ⟨yF', hyF', hyF'fix⟩ := const_of_fixed P hK _ (fun g => (Phi_fixed P R Qm Qi hQQ hQ' g).2)
  set N := max d (Finset.univ.sup (fun p : Fin d × Fin d => (Qm p.1 p.2).natDegree) + 1) with hNdef
  have hN : ∀ i j, (Qm i j).natDegree < N := fun i j =>
    lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := fun p : Fin d × Fin d => (Qm p.1 p.2).natDegree)
      (Finset.mem_univ (i, j)))) (le_max_right _ _)
  have hdN : d ≤ N := le_max_left _ _
  set ev0 : Bst P →+* P.R.B := Polynomial.evalRingHom (-b) with hev0
  set U₀ := Qm.map ev0 with hU₀
  set U₀' := Qi.map ev0 with hU₀'
  set m := y.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hm
  have hU : U₀ * U₀' = 1 := by rw [← mmap_mul, hQQ, mmap_one]
  have hU' : U₀' * U₀ = 1 := mul_eq_one_comm.1 hU
  have hym : (y.map (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P))).map ev0 = m := by
    ext i j; simp only [Matrix.map_apply, hev0, Polynomial.coe_evalRingHom, eval_kur, hm]
  have hdk : ∀ k, (Qm.map (derivative^[k])).map ev0 = U₀ * m ^ k := fun k => by
    rw [iter_deriv P Qm Qi hQQ y hy k, mmap_mul, mmap_pow, hym]
  have hmN : m ^ N = 0 := by
    have h0 : Qm.map (derivative^[N]) = 0 := by
      ext i j; simp [Polynomial.iterate_derivative_eq_zero (hN i j)]
    have h1 := hdk N
    rw [h0, Matrix.map_zero _ (map_zero _)] at h1
    calc m ^ N = U₀' * (U₀ * m ^ N) := by rw [← Matrix.mul_assoc, hU', Matrix.one_mul]
      _ = 0 := by rw [← h1, Matrix.mul_zero]

  have hgal : ∀ g : ↥(GK K), (R g).map (algebraMap ℚ_[l] P.R.B) * U₀.map (P.actQ (g : GQ l)) =
      ∑ k ∈ Finset.range N, ((-((c g : ℚ_[l]) • P.tB)) ^ k * algebraMap ℚ_[l] P.R.B ((k.factorial : ℚ_[l])⁻¹)) •
        (U₀ * m ^ k) := by
    intro g
    set eg : Bst P →+* P.R.B := Polynomial.evalRingHom (-((c g : ℚ_[l]) • P.tB) + -b) with heg
    have h1 := congrArg (fun A => Matrix.map A eg) (hQ' g)
    simp only [mmap_mul] at h1
    have e1 : ((R g).map (algebraMap ℚ_[l] (Bst P))).map eg = (R g).map (algebraMap ℚ_[l] P.R.B) := by
      ext i j; simp [heg]
    have e2 : (Qm.map (actSt P (g : GQ l))).map eg = U₀.map (P.actQ (g : GQ l)) := by
      ext i j
      simp only [Matrix.map_apply, heg, Polynomial.coe_evalRingHom, hU₀, hev0]
      exact ev_actSt P b _ _ (hact g) _
    rw [e1, e2] at h1
    rw [h1]
    ext i j
    simp only [Matrix.map_apply, heg, Polynomial.coe_evalRingHom, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [taylor_sum P (-b) _ _ N (hN i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have := congrFun (congrFun (hdk k) i) j
    simpa only [Matrix.map_apply, hev0, Polynomial.coe_evalRingHom] using this

  set f := yF.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hf
  set f' := yF'.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) with hf'
  have hevk : ∀ z : Matrix (Fin d) (Fin d) ↥(MaximalUnramifiedExtension l),
      (z.map (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P))).map ev0 = z.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := by
    intro z; ext i j; simp only [Matrix.map_apply, hev0, Polynomial.coe_evalRingHom, eval_kur]
  have hevφ : ∀ A : Matrix (Fin d) (Fin d) (Bst P), (A.map (phiSt P)).map ev0 = (A.map ev0).map P.φB := by
    intro A; ext i j
    simp only [Matrix.map_apply, hev0, Polynomial.coe_evalRingHom]
    exact ev_phiSt P b hphi _
  have hφ : U₀.map P.φB = U₀ * f := by
    have e : Qm.map (phiSt P) = Qm * (Qi * Qm.map (phiSt P)) := by rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    have := congrArg (fun A => Matrix.map A ev0) e
    rw [hevφ, hyF, mmap_mul, hevk] at this
    exact this
  have hφ' : U₀'.map P.φB * U₀ = f' := by
    have := congrArg (fun A => Matrix.map A ev0) hyF'
    rw [mmap_mul, hevφ, hevk] at this
    exact this
  have hff : f * f' = 1 := by
    have e : f = U₀' * U₀.map P.φB := by rw [hφ, ← Matrix.mul_assoc, hU', Matrix.one_mul]
    rw [e, ← hφ']
    calc U₀' * U₀.map P.φB * (U₀'.map P.φB * U₀) = U₀' * (U₀ * U₀').map P.φB * U₀ := by
          rw [mmap_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, mmap_one, Matrix.mul_one, hU']

  have hC := (GlobalTheory.MemLoc.fits_inv l P AI T C hF).1
  set e : P.R.B →+* Per.Bcris l := T.eB.toRingHom with he
  set aw : Wq l bk.a →+* Per.Bcris l := (Per.aB l).comp (wA l bk.a).toRingHom with haw
  have hent : ∀ G : Matrix (Fin d) (Fin d) P.R.B, (∀ g : ↥(GK K), G.map (P.actQ (g : GQ l)) = G) →
      ∀ i j, ∃ (n : ℕ) (w : Wq l bk.a), ((l : ℕ) : Per.Bcris l) ^ n * (G.map e) i j = aw w := by
    intro G hG i j
    obtain ⟨x, hxK, hx⟩ := hC K (e (G i j)) fun g hg => by
      have h1 := congrFun (congrFun (hG ⟨g, hg⟩) i) j
      simp only [Matrix.map_apply] at h1
      simp only [he, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [← T.actB, h1]
    obtain ⟨n, w, hw⟩ := GlobalTheory.TeichmullerPowerUnit.exists_pow_mul_u_eq_aB l K bk C x hxK
    exact ⟨n, w, by rw [Matrix.map_apply, ← hx, hw]; rfl⟩
  obtain ⟨k₁, F, hF1⟩ := GlobalTheory.SeedF.clear_den aw _ (hent f hyFfix)
  obtain ⟨k₂, F', hF2⟩ := GlobalTheory.SeedF.clear_den aw _ (hent f' hyF'fix)
  obtain ⟨k, Fm, hFm⟩ := GlobalTheory.SeedF.clear_den aw _ (hent m hyfix)
  have hinj : Function.Injective (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := by
    haveI := nontrivial_B P; exact (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective
  have hyN : y ^ N = 0 := by
    apply Matrix.map_injective hinj
    show (y ^ N).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) = (0 : Matrix (Fin d) (Fin d) ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)
    rw [mmap_pow, Matrix.map_zero _ (map_zero _)]
    exact hmN
  have hyd : y ^ d = 0 := pow_eq_zero_field y ⟨N, hyN⟩
  have hmd : (m.map e) ^ d = 0 := by
    rw [← mmap_pow, hm, ← mmap_pow, hyd, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
  have hFmd : Fm ^ d = 0 := by
    apply Matrix.map_injective (GlobalTheory.SeedF.aw_injective C bk.a)
    change (Fm ^ d).map aw = (0 : Matrix (Fin d) (Fin d) (Wq l bk.a)).map aw
    rw [mmap_pow, ← hFm, _root_.smul_pow, hmd, smul_zero, Matrix.map_zero _ (map_zero _)]
  set Mn := -Fm with hMn
  have hMnd : Mn ^ d = 0 := by rw [hMn, neg_pow, hFmd, mul_zero]
  refine ⟨U₀.map e, U₀'.map e, k₁, k₁ + k₂, k, F, F', Mn, ?_, ?_, ?_, hMnd, ?_⟩
  · rw [← mmap_mul, hU, mmap_one]
  · apply Matrix.map_injective (GlobalTheory.SeedF.aw_injective C bk.a)
    change (F * F').map aw = (((l : ℕ) : Wq l bk.a) ^ (k₁ + k₂) • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))).map aw
    rw [mmap_mul, ← hF1, ← hF2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, ← mmap_mul, hff, mmap_one]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  · have hφe : (U₀.map e).map (Per.φB l) = (U₀.map P.φB).map e := by
      ext i j
      simp only [Matrix.map_apply, he, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      exact (T.frob _).symm
    rw [hφe, hφ, mmap_mul, ← hF1, Matrix.mul_smul]
  · intro g

    have hz : (ρ g).val.map (Per.zB l) = ((R g).map (algebraMap ℚ_[l] P.R.B)).map e := by
      ext i j
      simp only [Matrix.map_apply, hRdef, he, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      exact (T.zB _).symm
    have hσ : (U₀.map e).map (Per.σB (g : GQ l)) = (U₀.map (P.actQ (g : GQ l))).map e := by
      ext i j
      simp only [Matrix.map_apply, he, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      exact (T.actB _ _).symm
    have hMa : Mn.map aw = -(((l : ℕ) : Per.Bcris l) ^ k • m.map e) := by
      rw [hFm]; ext i j; simp [hMn]
    have hl0 : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    have he1 : e ((c g : ℚ_[l]) • P.tB) = Per.zB l (c g) * C.tB := by
      rw [Algebra.smul_def, map_mul, ← hF.t]
      simp only [he, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [T.zB]
    have hterm : ∀ i : ℕ, e ((-((c g : ℚ_[l]) • P.tB)) ^ i * algebraMap ℚ_[l] P.R.B ((i.factorial : ℚ_[l])⁻¹)) •
        (U₀.map e * (m.map e) ^ i) = U₀.map e * ((C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) *
          (Per.zB l (c g) * C.tB) ^ i) • (Mn.map aw) ^ i) := by
      intro i
      have hn : ((i.factorial : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 i.factorial_ne_zero
      have hinv : e (algebraMap ℚ_[l] P.R.B ((i.factorial : ℚ_[l])⁻¹)) = C.qB ((i.factorial : ℚ_[l])⁻¹) := by
        have h1 : e (algebraMap ℚ_[l] P.R.B ((i.factorial : ℚ_[l])⁻¹)) * ((i.factorial : ℕ) : Per.Bcris l) = 1 := by
          rw [← map_natCast e, ← map_natCast (algebraMap ℚ_[l] P.R.B), ← map_mul, ← map_mul, inv_mul_cancel₀ hn,
            map_one, map_one]
        have h2 : ((i.factorial : ℕ) : Per.Bcris l) * C.qB ((i.factorial : ℚ_[l])⁻¹) = 1 := by
          rw [← map_natCast C.qB, ← map_mul, mul_inv_cancel₀ hn, map_one]
        exact left_inv_eq_right_inv h1 h2
      have hq : C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * ((l : ℕ) : Per.Bcris l) ^ (k * i) =
          C.qB ((i.factorial : ℚ_[l])⁻¹) := by
        rw [← map_natCast C.qB l, ← map_pow, ← map_mul, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl0),
          mul_one]
      rw [hMa, ← neg_smul (((l : ℕ) : Per.Bcris l) ^ k) (m.map e), _root_.smul_pow (-(((l : ℕ) : Per.Bcris l) ^ k)) (m.map e) i,
        smul_smul, Matrix.mul_smul]
      congr 1
      rw [map_mul, map_pow, map_neg, he1, hinv, ← hq, neg_pow, neg_pow (((l : ℕ) : Per.Bcris l) ^ k), ← pow_mul]
      ring
    rw [hz, hσ, ← mmap_mul, hgal g, mmap_sum_smul]
    simp only [mmap_mul, mmap_pow]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_range_add_sum_Ico _ hdN, Finset.sum_eq_zero (s := Finset.Ico d N), add_zero]
    intro i hi
    rw [← mmap_pow, pow_eq_zero_of_le (Finset.mem_Ico.1 hi).1 hMnd, Matrix.map_zero _ (map_zero _), smul_zero]

end GlobalTheory.StU
