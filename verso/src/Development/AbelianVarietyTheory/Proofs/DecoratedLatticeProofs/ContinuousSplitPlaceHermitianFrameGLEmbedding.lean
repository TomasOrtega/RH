import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameCont
open Matrix

/- English proof (translation)
Rewrite using `[← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]`. Establish `key : ∀ v : Fin S.rank → E, S.gram *ᵥ v = 0 → v = 0`. Introduce `v hv`. Establish `h0 : ∑ j, v j • S.frame j = 0`. Apply `S.nondeg.2` to reduce the goal to its premises.

Introduce `x`. Rewrite using `[← S.frame.sum_repr x]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Establish `hi` using `congrFun hv i`. Simplify using `only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at hi`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring`. Use `_ = 0 := by rw [hi, mul_zero]`.

Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.1 S.frame.linearIndependent v h0 j`. Introduce `a b hab`. Use `key (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
theorem gram_det_isUnit {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) :
    IsUnit S.gram.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ v : Fin S.rank → E, S.gram *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h0 : ∑ j, v j • S.frame j = 0 := by
      apply S.nondeg.2
      intro x
      rw [← S.frame.sum_repr x]
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at hi
      calc _ = (starRingEnd E) (S.frame.repr x i) * ∑ j, S.hT (S.frame i) (S.frame j) * v j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hi, mul_zero]
    funext j
    exact Fintype.linearIndependent_iff.1 S.frame.linearIndependent v h0 j
  intro a b hab
  have := key (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self])
  exact sub_eq_zero.1 this

/- English proof (translation)
Establish `hc : ∀ t, σ e • M t = J⁻¹ * Formalism.UG.cT σ (e • N t) * J`. Introduce `t`. Establish `h1 : J * M t = Formalism.UG.cT σ (N t) * J`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Formalism.UG.cT σ (e • N t) = σ e • Formalism.UG.cT σ (N t)`.

Use extensionality with `a b`. Simplify using `[Formalism.UG.cT]`. Rewrite using `[h2, Matrix.mul_assoc, Matrix.smul_mul, ← h1, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]`. Establish `hC : Continuous fun t => σ e • M t`. Simplify using `only [hc]`.

Conclude with `(continuous_const.matrix_mul (hN.matrix_map hσ).matrix_transpose).matrix_mul continuous_const`. Establish `hsum : M = fun t => (1 - (e + σ e) • (1 : Matrix m m A)) + (e • M t + σ e • M t)`. Use function extensionality and compare the values at `t`. Use extensionality with `i j`. Establish `h` using `hs t i j`.

Simplify using `only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢`. Take the linear combination `-h`. Rewrite using `[hsum]`. Conclude with `continuous_const.add (hM.add hC)`.
-/
theorem continuous_of_parts {A T m : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace T] [Fintype m] [DecidableEq m] (σ : A →+* A) (hσ : Continuous σ) (e : A)
    (J : Matrix m m A) (hJ : IsUnit J.det) (M N : T → Matrix m m A)
    (hU : ∀ t, Formalism.UG.cT σ (N t) * J * N t = J) (hNM : ∀ t, N t * M t = 1)
    (hs : ∀ t i j, (e + σ e) * (M t - 1) i j = (M t - 1) i j)
    (hM : Continuous fun t => e • M t) (hN : Continuous fun t => e • N t) : Continuous M := by
  have hc : ∀ t, σ e • M t = J⁻¹ * Formalism.UG.cT σ (e • N t) * J := by
    intro t
    have h1 : J * M t = Formalism.UG.cT σ (N t) * J := by
      calc J * M t = Formalism.UG.cT σ (N t) * J * N t * M t := by rw [hU]
        _ = Formalism.UG.cT σ (N t) * J := by rw [Matrix.mul_assoc _ (N t) (M t), hNM, Matrix.mul_one]
    have h2 : Formalism.UG.cT σ (e • N t) = σ e • Formalism.UG.cT σ (N t) := by
      ext a b; simp [Formalism.UG.cT]
    rw [h2, Matrix.mul_assoc, Matrix.smul_mul, ← h1, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
  have hC : Continuous fun t => σ e • M t := by
    simp only [hc]
    exact (continuous_const.matrix_mul (hN.matrix_map hσ).matrix_transpose).matrix_mul continuous_const
  have hsum : M = fun t => (1 - (e + σ e) • (1 : Matrix m m A)) + (e • M t + σ e • M t) := by
    funext t
    ext i j
    have h := hs t i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
    linear_combination -h
  rw [hsum]
  exact continuous_const.add (hM.add hC)

/- English proof (translation)
Establish `h` using `IsModuleTopology.continuous_of_linearMap (R := R) (LinearMap.baseChange R σ.toLinearMap)`. Use `h.congr fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y => simp [LinearMap.baseChange_tmul, sigR]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem continuous_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  have h := IsModuleTopology.continuous_of_linearMap (R := R) (LinearMap.baseChange R σ.toLinearMap)
  refine h.congr fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
The claim follows from `(PI.FT.toHR x).2`.
-/
theorem unitary_mt {D : D7} {S : HSp D} (x : GA D S) :
    Formalism.UG.cT (cA D) (mt S x) * S.gram.map (incA D) * mt S x = S.gram.map (incA D) := (PI.FT.toHR x).2

/- English proof (translation)
Use `show (matHom S x⁻¹).val * (matHom S x).val = 1`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`.
-/
theorem mt_inv_mul {D : D7} {S : HSp D} (x : GA D S) : mt S x⁻¹ * mt S x = 1 := by
  show (matHom S x⁻¹).val * (matHom S x).val = 1
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

/- English proof (translation)
Establish `h0` using `(gram_det_isUnit S).map (incA D)`. Rewrite `h0` using `[RingHom.map_det]`. Conclude with `h0`.
-/
theorem gram_map_det_isUnit {D : D7} (S : HSp D) : IsUnit (S.gram.map (incA D)).det := by
  have h0 := (gram_det_isUnit S).map (incA D)
  rw [RingHom.map_det] at h0
  exact h0

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Rewrite using `[← p.sec_pr, ← β.gl_mat g]`. Both sides reduce to the same expression.
-/
theorem e_mul_entry (β : Frame p S n) (g : GL n k) (i j : Fin S.rank) :
    p.e * mt S (β.gl g) i j = p.sec ((β.b * g.val * β.b') i j) := by
  rw [← p.sec_pr, ← β.gl_mat g]; rfl

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `refine (p.cont_sec.comp (((continuous_const.matrix_mul (Units.continuous_val (M := Matrix n n k))).matrix_mul continuous_const).matrix_elem i j)).congr fun g => (e_mul_entry β g i j).symm`.
-/
theorem continuous_e_smul (β : Frame p S n) : Continuous fun g : GL n k => p.e • mt S (β.gl g) := by
  refine continuous_matrix fun i j => ?_
  refine (p.cont_sec.comp (((continuous_const.matrix_mul
    (Units.continuous_val (M := Matrix n n k))).matrix_mul continuous_const).matrix_elem i j)).congr
      fun g => (e_mul_entry β g i j).symm

/- English proof (translation)
Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) _`. Use `continuous_of_parts (cA D) (continuous_sigR _ _) p.e (S.gram.map (incA D)) (gram_map_det_isUnit S) (fun g => mt S (β.gl g)) (fun g => mt S (β.gl g⁻¹)) (fun g => unitary_mt _) (fun g => ?_) (fun g => β.gl_supp g) (continuous_e_smul β) ((continuous_e_smul β).comp continuous_inv)` and prove the remaining obligations. Use `show mt S (β.gl g⁻¹) * mt S (β.gl g) = 1`. Rewrite using `[map_inv]`. Conclude with `mt_inv_mul _`.
-/
theorem continuous_mt (β : Frame p S n) : Continuous fun g : GL n k => mt S (β.gl g) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  refine continuous_of_parts (cA D) (continuous_sigR _ _) p.e (S.gram.map (incA D)) (gram_map_det_isUnit S)
    (fun g => mt S (β.gl g)) (fun g => mt S (β.gl g⁻¹)) (fun g => unitary_mt _) (fun g => ?_)
    (fun g => β.gl_supp g) (continuous_e_smul β) ((continuous_e_smul β).comp continuous_inv)
  show mt S (β.gl g⁻¹) * mt S (β.gl g) = 1
  rw [map_inv]
  exact mt_inv_mul _

/- English proof (translation)
Introduce `D k _ _ _ _ p S n _ _ β`. Use `(PI.FT.cont_HA_iff (AF D.host.F) (fun g : GL n k => β.gl g)).2 ⟨continuous_mt β, ?_⟩` and prove the remaining obligations. Establish `h` using `(continuous_mt β).comp (continuous_inv (G := GL n k))`. Use `h.congr fun g => ?_` and prove the remaining obligations. Use `show mt S (β.gl g⁻¹) = PI.FT.mtI (β.gl g)`.

Rewrite using `[map_inv]`. Both sides reduce to the same expression.
-/
theorem continuous_gl : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), Continuous β.gl := by
  intro D k _ _ _ _ p S n _ _ β
  refine (PI.FT.cont_HA_iff (AF D.host.F) (fun g : GL n k => β.gl g)).2 ⟨continuous_mt β, ?_⟩
  have h := (continuous_mt β).comp (continuous_inv (G := GL n k))
  refine h.congr fun g => ?_
  show mt S (β.gl g⁻¹) = PI.FT.mtI (β.gl g)
  rw [map_inv]; rfl

end GlobalTheory.FrameCont
