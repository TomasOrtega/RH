import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open Polynomial

namespace GlobalTheory.UnitLemma

noncomputable section

namespace InertUnit

variable {K : UQ} {P : K.E[X]}

/- English proof (translation)
Establish `h` using `congrArg (fun Q => Q.coeff 0) hr`. Simplify using `only [coeff_C_mul, coeff_zero_reverse] at h`. Rewrite using `[h, leadingCoeff_map_of_leadingCoeff_ne_zero _ (by simp [hP.leadingCoeff]), hP.leadingCoeff, map_one]`.
-/
theorem coeff_mul (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    K.c (P.coeff 0) * P.coeff 0 = 1 := by
  have h := congrArg (fun Q => Q.coeff 0) hr
  simp only [coeff_C_mul, coeff_zero_reverse] at h
  rw [h, leadingCoeff_map_of_leadingCoeff_ne_zero _ (by simp [hP.leadingCoeff]), hP.leadingCoeff, map_one]

def rootInv (P : K.E[X]) : AdjoinRoot P :=
  -(algebraMap K.E (AdjoinRoot P) (K.c (P.coeff 0))) * aeval (AdjoinRoot.root P) P.divX

/- English proof (translation)
Establish `h0 : aeval (AdjoinRoot.root P) P = 0` using `AdjoinRoot.aeval_eq P ▸ AdjoinRoot.mk_self`. Establish `h1` using `congrArg (aeval (AdjoinRoot.root P)) (X_mul_divX_add P)`. Rewrite `h1` using `[h0, map_add, map_mul, aeval_X, aeval_C]`. Establish `h2 : AdjoinRoot.root P * aeval (AdjoinRoot.root P) P.divX = -algebraMap K.E (AdjoinRoot P) (P.coeff 0)` using `eq_neg_of_add_eq_zero_left h1`. Unfold `rootInv`.

Rewrite using `[mul_left_comm, h2, neg_mul_neg, ← map_mul, coeff_mul hP hr, map_one]`.
-/
theorem root_mul_rootInv (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    AdjoinRoot.root P * rootInv P = 1 := by
  have h0 : aeval (AdjoinRoot.root P) P = 0 := AdjoinRoot.aeval_eq P ▸ AdjoinRoot.mk_self
  have h1 := congrArg (aeval (AdjoinRoot.root P)) (X_mul_divX_add P)
  rw [h0, map_add, map_mul, aeval_X, aeval_C] at h1
  have h2 : AdjoinRoot.root P * aeval (AdjoinRoot.root P) P.divX = -algebraMap K.E (AdjoinRoot P) (P.coeff 0) :=
    eq_neg_of_add_eq_zero_left h1
  unfold rootInv
  rw [mul_left_comm, h2, neg_mul_neg, ← map_mul, coeff_mul hP hr, map_one]

/- English proof (translation)
Establish `hu` using `root_mul_rootInv hP hr`. Use `letI : Invertible (rootInv P) := ⟨AdjoinRoot.root P, hu, by rw [mul_comm]; exact hu⟩`. Rewrite using `[← eval₂_map, ← eval₂_reverse_mul_pow]`. Establish `: ⅟(rootInv P) = AdjoinRoot.root P` using `rfl`. Rewrite using `[this, ← hr, eval₂_mul, eval₂_C]`.

Establish `h0 : P.eval₂ (algebraMap K.E (AdjoinRoot P)) (AdjoinRoot.root P) = 0` using `AdjoinRoot.eval₂_root P`. Rewrite using `[h0, mul_zero, zero_mul]`.
-/
theorem eval_rootInv (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    P.eval₂ ((algebraMap K.E (AdjoinRoot P)).comp (K.c : K.E →+* K.E)) (rootInv P) = 0 := by
  have hu := root_mul_rootInv hP hr
  letI : Invertible (rootInv P) := ⟨AdjoinRoot.root P, hu, by rw [mul_comm]; exact hu⟩
  rw [← eval₂_map, ← eval₂_reverse_mul_pow]
  have : ⅟(rootInv P) = AdjoinRoot.root P := rfl
  rw [this, ← hr, eval₂_mul, eval₂_C]
  have h0 : P.eval₂ (algebraMap K.E (AdjoinRoot P)) (AdjoinRoot.root P) = 0 := AdjoinRoot.eval₂_root P
  rw [h0, mul_zero, zero_mul]

def sig (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    AdjoinRoot P →+* AdjoinRoot P :=
  AdjoinRoot.lift ((algebraMap K.E (AdjoinRoot P)).comp (K.c : K.E →+* K.E)) (rootInv P) (eval_rootInv hP hr)

/- English proof (translation)
Rewrite using `[AdjoinRoot.algebraMap_eq, sig, AdjoinRoot.lift_of]`. Both sides reduce to the same expression.
-/
theorem sig_alg (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) (e : K.E) :
    sig hP hr (algebraMap K.E (AdjoinRoot P) e) = algebraMap K.E (AdjoinRoot P) (K.c e) := by
  rw [AdjoinRoot.algebraMap_eq, sig, AdjoinRoot.lift_of]
  rfl

/- English proof (translation)
The claim follows from `AdjoinRoot.lift_root _`.
-/
theorem sig_root (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    sig hP hr (AdjoinRoot.root P) = rootInv P := AdjoinRoot.lift_root _

/- English proof (translation)
Use `AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, RingHom.id_apply]`. Rewrite using `[← AdjoinRoot.algebraMap_eq, sig_alg, sig_alg, K.c_c]`. Simplify using `only [RingHom.comp_apply, RingHom.id_apply, sig_root]`. Establish `hu` using `root_mul_rootInv hP hr`.

Establish `h1 : sig hP hr (AdjoinRoot.root P) * sig hP hr (rootInv P) = 1` using `by rw [← map_mul, hu, map_one]`. Rewrite `h1` using `[sig_root]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sig_sig (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (sig hP hr).comp (sig hP hr) = RingHom.id _ := by
  refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [← AdjoinRoot.algebraMap_eq, sig_alg, sig_alg, K.c_c]
  · simp only [RingHom.comp_apply, RingHom.id_apply, sig_root]
    have hu := root_mul_rootInv hP hr
    have h1 : sig hP hr (AdjoinRoot.root P) * sig hP hr (rootInv P) = 1 := by rw [← map_mul, hu, map_one]
    rw [sig_root] at h1
    calc sig hP hr (rootInv P) = (AdjoinRoot.root P * rootInv P) * sig hP hr (rootInv P) := by rw [hu, one_mul]
      _ = AdjoinRoot.root P * (rootInv P * sig hP hr (rootInv P)) := by ring
      _ = AdjoinRoot.root P := by rw [h1, mul_one]

def invAlg (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) : InvAlg K where
  A := AdjoinRoot P
  fd := (AdjoinRoot.powerBasis hP.ne_zero).finite
  σ := RingEquiv.ofRingHom (sig hP hr) (sig hP hr) (sig_sig hP hr) (sig_sig hP hr)
  σ_σ := fun y => congrArg (fun f : AdjoinRoot P →+* AdjoinRoot P => f y) (sig_sig hP hr)
  σ_alg := sig_alg hP hr
  g := AdjoinRoot.root P

/- English proof (translation)
Use `haveI : Module.Finite K.E (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite`. Establish `h` using `charpoly_leftMulMatrix (AdjoinRoot.powerBasis hP.ne_zero)`. Rewrite `h` using `[Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, AdjoinRoot.powerBasis_gen, AdjoinRoot.minpoly_root hP.ne_zero, hP.leadingCoeff, inv_one, C_1, mul_one]`. Conclude with `h`.
-/
theorem charpoly_root (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (invAlg hP hr).P = P := by
  haveI : Module.Finite K.E (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis hP.ne_zero)
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, AdjoinRoot.powerBasis_gen,
    AdjoinRoot.minpoly_root hP.ne_zero, hP.leadingCoeff, inv_one, C_1, mul_one] at h
  exact h

end InertUnit

open InertUnit in
/- English proof (translation)
Introduce `K P hP hr`. Use `⟨invAlg hP hr, ?_, charpoly_root hP hr⟩` and prove the remaining obligations. Use `show AdjoinRoot.root P * sig hP hr (AdjoinRoot.root P) = 1`. Rewrite using `[sig_root]`. Conclude with `root_mul_rootInv hP hr`.
-/
theorem exists_invAlg_root : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic →
    C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse →
    ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by
  intro K P hP hr
  refine ⟨invAlg hP hr, ?_, charpoly_root hP hr⟩
  show AdjoinRoot.root P * sig hP hr (AdjoinRoot.root P) = 1
  rw [sig_root]
  exact root_mul_rootInv hP hr
end
end GlobalTheory.UnitLemma
