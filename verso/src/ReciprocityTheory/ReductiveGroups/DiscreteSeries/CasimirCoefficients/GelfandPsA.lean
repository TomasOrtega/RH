import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPhi

noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace GPs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def mulL (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ X)

/- English proof (translation)
Conclude with `(hg.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)`.
-/
lemma dAt {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V) {g : Matrix (Fin n) (Fin n) ℂ → E}
    (hg : ContDiffOn ℂ ∞ g V) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ V) : DifferentiableAt ℂ g z := by
  exact (hg.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)

/- English proof (translation)
Use `show fderiv ℂ f z (X * z) = fderiv ℂ g z (X * z)`. Rewrite using `[(h.eventuallyEq_of_mem (hV.mem_nhds hz)).fderiv_eq]`.
-/
lemma lhol_congr {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V) {f g : Matrix (Fin n) (Fin n) ℂ → E}
    (h : Set.EqOn f g V) (X : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ V) :
    Lhol X f z = Lhol X g z := by
  show fderiv ℂ f z (X * z) = fderiv ℂ g z (X * z)
  rw [(h.eventuallyEq_of_mem (hV.mem_nhds hz)).fderiv_eq]

/- English proof (translation)
Use `show fderiv ℂ f z ((∑ i ∈ s, X i) * z) = ∑ i ∈ s, fderiv ℂ f z (X i * z)`. Rewrite using `[Finset.sum_mul, map_sum]`.
-/
lemma lhol_sumX {ι : Type*} (s : Finset ι) (X : ι → Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (z : Matrix (Fin n) (Fin n) ℂ) :
    Lhol (∑ i ∈ s, X i) f z = ∑ i ∈ s, Lhol (X i) f z := by
  show fderiv ℂ f z ((∑ i ∈ s, X i) * z) = ∑ i ∈ s, fderiv ℂ f z (X i * z)
  rw [Finset.sum_mul, map_sum]

/- English proof (translation)
Use `show fderiv ℂ f z ((c • X) * z) = c • fderiv ℂ f z (X * z)`. Rewrite using `[Matrix.smul_mul, map_smul]`.
-/
lemma lhol_smulX (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (z : Matrix (Fin n) (Fin n) ℂ) : Lhol (c • X) f z = c • Lhol X f z := by
  show fderiv ℂ f z ((c • X) * z) = c • fderiv ℂ f z (X * z)
  rw [Matrix.smul_mul, map_smul]

/- English proof (translation)
Use `show fderiv ℂ (fun y => ∑ i ∈ s, g i y) z (X * z) = ∑ i ∈ s, fderiv ℂ (g i) z (X * z)`. Use `erw [fderiv_fun_sum hg]`. Conclude with `map_sum ({ toFun := fun L => L (X * z), map_zero' := rfl, map_add' := fun _ _ => rfl } : (Matrix (Fin n) (Fin n) ℂ →L[ℂ] E) →+ E) _ _`.
-/
lemma lhol_fsum {ι : Type*} (s : Finset ι) (g : ι → Matrix (Fin n) (Fin n) ℂ → E)
    (X : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hg : ∀ i ∈ s, DifferentiableAt ℂ (g i) z) :
    Lhol X (fun y => ∑ i ∈ s, g i y) z = ∑ i ∈ s, Lhol X (g i) z := by
  show fderiv ℂ (fun y => ∑ i ∈ s, g i y) z (X * z) = ∑ i ∈ s, fderiv ℂ (g i) z (X * z)
  erw [fderiv_fun_sum hg]
  exact map_sum ({ toFun := fun L => L (X * z), map_zero' := rfl, map_add' := fun _ _ => rfl } :
    (Matrix (Fin n) (Fin n) ℂ →L[ℂ] E) →+ E) _ _

/- English proof (translation)
Use `show fderiv ℂ (fun y => c • g y) z (X * z) = c • fderiv ℂ g z (X * z)`. Apply the tactic sequence `erw [fderiv_fun_const_smul hg c] <;> rfl`.
-/
lemma lhol_fsmul (c : ℂ) (g : Matrix (Fin n) (Fin n) ℂ → E) (X : Matrix (Fin n) (Fin n) ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hg : DifferentiableAt ℂ g z) :
    Lhol X (fun y => c • g y) z = c • Lhol X g z := by
  show fderiv ℂ (fun y => c • g y) z (X * z) = c • fderiv ℂ g z (X * z)
  erw [fderiv_fun_const_smul hg c] <;> rfl

/- English proof (translation)
Establish `h2 : ContDiffOn ℂ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => X * y) V` using `(mulL X).contDiff.contDiffOn`. Conclude with `((contDiffOn_infty_iff_fderiv_of_isOpen hV).mp hf).2.clm_apply h2`.
-/
lemma sm_lhol {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : ContDiffOn ℂ ∞ f V) (X : Matrix (Fin n) (Fin n) ℂ) : ContDiffOn ℂ ∞ (Lhol X f) V := by
  have h2 : ContDiffOn ℂ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => X * y) V := (mulL X).contDiff.contDiffOn
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen hV).mp hf).2.clm_apply h2

/- English proof (translation)
Proceed by induction on `m generalizing a b with`. Consider the case `zero`. Simplify using `only [opPow]`. Use `split_ifs`. Conclude with `hf`.

Conclude with `contDiffOn_const (c := (0 : E))`. Consider the case `succ k ih`. Simplify using `only [opPow]`. Establish `e : (∑ c, Lhol (M a c) (opPow (fun a b => Lhol (M a b)) k c b f)) = fun x => ∑ c, Lhol (M a c) (opPow (fun a b => Lhol (M a b)) k c b f) x`. Use function extensionality and compare the values at `x`.

Conclude with `Finset.sum_apply x _ _`. Rewrite using `[e]`. Conclude with `ContDiffOn.sum fun c _ => sm_lhol hV (ih c b) (M a c)`.
-/
lemma sm_opPow {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V) (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : ContDiffOn ℂ ∞ f V) (m : ℕ) (a b : Fin n) :
    ContDiffOn ℂ ∞ (opPow (fun a b => Lhol (M a b)) m a b f) V := by
  induction m generalizing a b with
  | zero =>
    simp only [opPow]
    split_ifs
    · exact hf
    · exact contDiffOn_const (c := (0 : E))
  | succ k ih =>
    simp only [opPow]
    have e : (∑ c, Lhol (M a c) (opPow (fun a b => Lhol (M a b)) k c b f)) =
        fun x => ∑ c, Lhol (M a c) (opPow (fun a b => Lhol (M a b)) k c b f) x := by
      funext x; exact Finset.sum_apply x _ _
    rw [e]
    exact ContDiffOn.sum fun c _ => sm_lhol hV (ih c b) (M a c)

/- English proof (translation)
Establish `hq : ∀ d' c, ∑ e, Q d' e * P e c = if d' = c then 1 else 0`. Introduce `d' c`. Establish `h` using `congrFun (congrFun hQP d') c`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply]`. Then use the resulting hypothesis. Simplify using `only [Finset.smul_sum, smul_smul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d' _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `_ = ∑ c', ∑ d', ∑ c, if d' = c then ∑ d, (P a c' * Q d b) • T c' d' c d else 0 := by`. Use `Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Establish `key : ∀ d, ∑ e, (P a c' * Q d' e * (P e c * Q d b)) • T c' d' c d = (if d' = c then P a c' * Q d b else 0) • T c' d' c d`. Introduce `d`. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring`. Apply the tactic sequence `_ = _ := by rw [hq]; split_ifs <;> simp`. Simplify using `only [key]`. Apply the tactic sequence `split_ifs <;> simp`. Use `_ = ∑ c', ∑ d', ∑ d, (P a c' * Q d b) • T c' d' d' d := by`.

Use `Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d' _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules. Use `_ = ∑ c, ∑ d, ∑ e, (P a c * Q d b) • T c e e d := by`. Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`.
-/
lemma tele_alg (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (T : Fin n → Fin n → Fin n → Fin n → E)
    (a b : Fin n) :
    ∑ e, ∑ c', ∑ d', (P a c' * Q d' e) • ∑ c, ∑ d, (P e c * Q d b) • T c' d' c d =
      ∑ c, ∑ d, (P a c * Q d b) • ∑ e, T c e e d := by
  have hq : ∀ d' c, ∑ e, Q d' e * P e c = if d' = c then 1 else 0 := by
    intro d' c
    have h := congrFun (congrFun hQP d') c
    rwa [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [Finset.smul_sum, smul_smul]
  calc ∑ e, ∑ c', ∑ d', ∑ c, ∑ d, (P a c' * Q d' e * (P e c * Q d b)) • T c' d' c d
      = ∑ c', ∑ d', ∑ c, ∑ d, ∑ e, (P a c' * Q d' e * (P e c * Q d b)) • T c' d' c d := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ c', ∑ d', ∑ c, if d' = c then ∑ d, (P a c' * Q d b) • T c' d' c d else 0 := by
        refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d' _ =>
          Finset.sum_congr rfl fun c _ => ?_
        have key : ∀ d, ∑ e, (P a c' * Q d' e * (P e c * Q d b)) • T c' d' c d =
            (if d' = c then P a c' * Q d b else 0) • T c' d' c d := by
          intro d
          rw [← Finset.sum_smul]
          congr 1
          calc ∑ e, P a c' * Q d' e * (P e c * Q d b) = (P a c' * Q d b) * ∑ e, Q d' e * P e c := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
            _ = _ := by rw [hq]; split_ifs <;> simp
        simp only [key]
        split_ifs <;> simp
    _ = ∑ c', ∑ d', ∑ d, (P a c' * Q d b) • T c' d' d' d := by
        refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d' _ => ?_
        rw [Finset.sum_ite_eq]; simp
    _ = ∑ c, ∑ d, ∑ e, (P a c * Q d b) • T c e e d := by
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finset.sum_comm]

/- English proof (translation)
Establish `hq : ∀ d c, ∑ a, Q d a * P a c = if d = c then 1 else 0`. Introduce `d c`. Establish `h` using `congrFun (congrFun hQP d) c`. Rewrite `h` using `[Matrix.mul_apply, Matrix.one_apply]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `_ = ∑ c, ∑ d, (if d = c then S c d else 0) := by`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_smul]`. Establish `e : ∑ a, P a c * Q d a = if d = c then 1 else 0`. Rewrite using `[← hq]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`. Apply the tactic sequence `rw [e]; split_ifs <;> simp`.

Use `_ = ∑ c, S c c := by`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq']`. Simplify using the standard rewrite rules.
-/
lemma gel_alg (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (S : Fin n → Fin n → E) :
    ∑ a, ∑ c, ∑ d, (P a c * Q d a) • S c d = ∑ c, S c c := by
  have hq : ∀ d c, ∑ a, Q d a * P a c = if d = c then 1 else 0 := by
    intro d c
    have h := congrFun (congrFun hQP d) c
    rwa [Matrix.mul_apply, Matrix.one_apply] at h
  calc ∑ a, ∑ c, ∑ d, (P a c * Q d a) • S c d = ∑ c, ∑ d, ∑ a, (P a c * Q d a) • S c d := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_; rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, (if d = c then S c d else 0) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_smul]
        have e : ∑ a, P a c * Q d a = if d = c then 1 else 0 := by
          rw [← hq]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
        rw [e]; split_ifs <;> simp
    _ = ∑ c, S c c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_ite_eq']; simp

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `a b z _`. Simplify using `only [opPow]`. Establish `hp` using `congrFun (congrFun hPQ a) b`.

Rewrite `hp` using `[Matrix.mul_apply, Matrix.one_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_smul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single c]`.

Simplify using the standard rewrite rules. Introduce `d _ hd`. Simplify using `[Ne.symm hd]`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `a b z hz`. Establish `hsm : ∀ c d, ContDiffOn ℂ ∞ (opPow (fun a b => Lhol (M a b)) k c d f) V` using `fun c d => sm_opPow hV M hf k c d`. Establish `hd1 : ∀ c d, DifferentiableAt ℂ (opPow (fun a b => Lhol (M a b)) k c d f) z` using `fun c d => dAt hV (hsm c d) hz`. Establish `s2 : ∀ e (X : Matrix (Fin n) (Fin n) ℂ), Lhol X (opPow (fun a b => Lhol (N a b)) k e b f) z = ∑ c, ∑ d, (P e c * Q d b) • Lhol X (opPow (fun a b => Lhol (M a b)) k c d f) z`. Introduce `e X`.

Establish `hd2 : ∀ c, DifferentiableAt ℂ (fun y => ∑ d, (P e c * Q d b) • opPow (fun a b => Lhol (M a b)) k c d f y) z` using `fun c => DifferentiableAt.fun_sum fun d _ => (hd1 c d).fun_const_smul _`. Rewrite using `[lhol_congr hV (g := fun y => ∑ c, ∑ d, (P e c * Q d b) • opPow (fun a b => Lhol (M a b)) k c d f y) (fun y hy => ih e b y hy) X hz]`. Rewrite using `[lhol_fsum _ _ X (fun c _ => hd2 c)]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[lhol_fsum _ _ X (fun d _ => (hd1 c d).fun_const_smul _)]`.

Conclude with `Finset.sum_congr rfl fun d _ => lhol_fsmul _ _ X (hd1 c d)`. Simplify using `only [opPow, Finset.sum_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[hN a e, lhol_sumX]`.

Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[lhol_sumX]`. Use `Finset.sum_congr rfl fun d' _ => ?_` and prove the remaining obligations. Rewrite using `[lhol_smulX, s2]`. Use `_ = _ := tele_alg P Q hQP (fun c' d' c d => Lhol (M c' d') (opPow (fun a b => Lhol (M a b)) k c d f) z) a b`.
-/
lemma opPow_tele {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    (M N : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ a b, N a b = ∑ c, ∑ d, (P a c * Q d b) • M c d) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : ContDiffOn ℂ ∞ f V) (m : ℕ) :
    ∀ a b, ∀ z ∈ V, opPow (fun a b => Lhol (N a b)) m a b f z =
      ∑ c, ∑ d, (P a c * Q d b) • opPow (fun a b => Lhol (M a b)) m c d f z := by
  induction m with
  | zero =>
    intro a b z _
    simp only [opPow]
    have hp := congrFun (congrFun hPQ a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at hp
    calc (if a = b then f else 0) z = (if a = b then (1 : ℂ) else 0) • f z := by split_ifs <;> simp
      _ = (∑ c, P a c * Q c b) • f z := by rw [hp]
      _ = ∑ c, ∑ d, (P a c * Q d b) • (if c = d then f else 0) z := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_eq_single c]
          · simp
          · intro d _ hd; simp [Ne.symm hd]
          · simp
  | succ k ih =>
    intro a b z hz
    have hsm : ∀ c d, ContDiffOn ℂ ∞ (opPow (fun a b => Lhol (M a b)) k c d f) V :=
      fun c d => sm_opPow hV M hf k c d
    have hd1 : ∀ c d, DifferentiableAt ℂ (opPow (fun a b => Lhol (M a b)) k c d f) z :=
      fun c d => dAt hV (hsm c d) hz
    have s2 : ∀ e (X : Matrix (Fin n) (Fin n) ℂ), Lhol X (opPow (fun a b => Lhol (N a b)) k e b f) z =
        ∑ c, ∑ d, (P e c * Q d b) • Lhol X (opPow (fun a b => Lhol (M a b)) k c d f) z := by
      intro e X
      have hd2 : ∀ c, DifferentiableAt ℂ
          (fun y => ∑ d, (P e c * Q d b) • opPow (fun a b => Lhol (M a b)) k c d f y) z :=
        fun c => DifferentiableAt.fun_sum fun d _ => (hd1 c d).fun_const_smul _
      rw [lhol_congr hV (g := fun y => ∑ c, ∑ d, (P e c * Q d b) • opPow (fun a b => Lhol (M a b)) k c d f y)
        (fun y hy => ih e b y hy) X hz]
      rw [lhol_fsum _ _ X (fun c _ => hd2 c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [lhol_fsum _ _ X (fun d _ => (hd1 c d).fun_const_smul _)]
      exact Finset.sum_congr rfl fun d _ => lhol_fsmul _ _ X (hd1 c d)
    simp only [opPow, Finset.sum_apply]
    calc ∑ e, Lhol (N a e) (opPow (fun a b => Lhol (N a b)) k e b f) z
        = ∑ e, ∑ c', ∑ d', (P a c' * Q d' e) •
            ∑ c, ∑ d, (P e c * Q d b) • Lhol (M c' d') (opPow (fun a b => Lhol (M a b)) k c d f) z := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hN a e, lhol_sumX]
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [lhol_sumX]
          refine Finset.sum_congr rfl fun d' _ => ?_
          rw [lhol_smulX, s2]
      _ = _ := tele_alg P Q hQP
          (fun c' d' c d => Lhol (M c' d') (opPow (fun a b => Lhol (M a b)) k c d f) z) a b

def conjLE (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (hBA : B * A = 1) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun z := A * z * B
  invFun z := B * z * A
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by simp
  left_inv z := by
    simp only [← Matrix.mul_assoc]
    rw [hBA, Matrix.one_mul, Matrix.mul_assoc, hBA, Matrix.mul_one]
  right_inv z := by
    simp only [← Matrix.mul_assoc]
    rw [hAB, Matrix.one_mul, Matrix.mul_assoc, hAB, Matrix.mul_one]

/- English proof (translation)
Set `L : Matrix (Fin n) (Fin n) ℂ ≃L[ℂ] Matrix (Fin n) (Fin n) ℂ` to `(conjLE A B hAB hBA).toContinuousLinearEquiv`. Establish `h1 : (fun y => f (A * y * B)) = f ∘ L` using `rfl`. Use `show fderiv ℂ (fun y => f (A * y * B)) z (X * z) = fderiv ℂ f (A * z * B) (A * X * B * (A * z * B))`. Rewrite using `[h1]`. Use `erw [L.comp_right_fderiv]`.

Use `show fderiv ℂ f (A * z * B) (A * (X * z) * B) = _`. Use `congr 1`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc B A, hBA, Matrix.one_mul]`.
-/
lemma lhol_conj (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (hBA : B * A = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) (z : Matrix (Fin n) (Fin n) ℂ) :
    Lhol X (fun y => f (A * y * B)) z = Lhol (A * X * B) f (A * z * B) := by
  let L : Matrix (Fin n) (Fin n) ℂ ≃L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (conjLE A B hAB hBA).toContinuousLinearEquiv
  have h1 : (fun y => f (A * y * B)) = f ∘ L := rfl
  show fderiv ℂ (fun y => f (A * y * B)) z (X * z) = fderiv ℂ f (A * z * B) (A * X * B * (A * z * B))
  rw [h1]
  erw [L.comp_right_fderiv]
  show fderiv ℂ f (A * z * B) (A * (X * z) * B) = _
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul]

/- English proof (translation)
Proceed by induction on `m generalizing a b with`. Consider the case `zero`. Use function extensionality and compare the values at `y`. Simplify using `only [opPow]`. Apply the tactic sequence `split_ifs <;> rfl`.

Consider the case `succ k ih`. Use function extensionality and compare the values at `y`. Simplify using `only [opPow, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[ih c b]`.

Conclude with `lhol_conj A B hAB hBA (M a c) (opPow (fun a b => Lhol (A * M a b * B)) k c b f) y`.
-/
lemma opPow_conj (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (f : Matrix (Fin n) (Fin n) ℂ → E) (m : ℕ) (a b : Fin n) :
    opPow (fun a b => Lhol (M a b)) m a b (fun y => f (A * y * B)) =
      fun y => opPow (fun a b => Lhol (A * M a b * B)) m a b f (A * y * B) := by
  induction m generalizing a b with
  | zero =>
    funext y
    simp only [opPow]
    split_ifs <;> rfl
  | succ k ih =>
    funext y
    simp only [opPow, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ih c b]
    exact lhol_conj A B hAB hBA (M a c) (opPow (fun a b => Lhol (A * M a b * B)) k c b f) y

/- English proof (translation)
Unfold `opGelfand`. Simplify using `only [Finset.sum_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[opPow_conj M A B hAB hBA f m a a]`.

Use `_ = ∑ a, ∑ c, ∑ d, (P a c * Q d a) • opPow (fun a b => Lhol (M a b)) m c d f (A * z * B) := by`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Conclude with `opPow_tele hV M (fun a b => A * M a b * B) P Q hN hPQ hQP hf m a a (A * z * B) hz`. Use `_ = ∑ c, opPow (fun a b => Lhol (M a b)) m c c f (A * z * B) := gel_alg P Q hQP (fun c d => opPow (fun a b => Lhol (M a b)) m c d f (A * z * B))`.
-/
theorem gelfand_conj {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    (M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ a b, A * M a b * B = ∑ c, ∑ d, (P a c * Q d b) • M c d) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : ContDiffOn ℂ ∞ f V) (m : ℕ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : A * z * B ∈ V) :
    opGelfand (fun a b => Lhol (M a b)) m (fun y => f (A * y * B)) z =
      opGelfand (fun a b => Lhol (M a b)) m f (A * z * B) := by
  unfold opGelfand
  simp only [Finset.sum_apply]
  calc ∑ a, opPow (fun a b => Lhol (M a b)) m a a (fun y => f (A * y * B)) z
      = ∑ a, opPow (fun a b => Lhol (A * M a b * B)) m a a f (A * z * B) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [opPow_conj M A B hAB hBA f m a a]
    _ = ∑ a, ∑ c, ∑ d, (P a c * Q d a) • opPow (fun a b => Lhol (M a b)) m c d f (A * z * B) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact opPow_tele hV M (fun a b => A * M a b * B) P Q hN hPQ hQP hf m a a (A * z * B) hz
    _ = ∑ c, opPow (fun a b => Lhol (M a b)) m c c f (A * z * B) :=
        gel_alg P Q hQP (fun c d => opPow (fun a b => Lhol (M a b)) m c d f (A * z * B))

end GPs

end ReciprocityTheory.ChartRestriction.DS.S7
