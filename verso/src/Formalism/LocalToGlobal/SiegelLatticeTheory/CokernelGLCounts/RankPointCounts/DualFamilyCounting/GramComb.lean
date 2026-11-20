import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsDualGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDet

noncomputable section

open NumberField Module Formalism.MainNotions.S Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TotPosAll : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (x : D.host.E), star x = x → Formalism.MainNotions.S.LocalSplitGroups.TotPos x → Formalism.HermitianLattices.Ext.L3.TotPos x

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

/- English proof (translation)
Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]`. Use `first`. Consider the case `(refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_; ring)`. Consider the case `(rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_; ring)`.
-/
theorem gram_comb' {ι : Type} [Fintype ι] (p : ι → S.V) (A : Matrix ι ι E) (b c : ι) :
    S.hT (∑ a, A a b • p a) (∑ a, A a c • p a) =
      (A.conjTranspose * Matrix.of (fun a a' => S.hT (p a) (p a')) * A) b c := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, starRingEnd_apply, Finset.sum_mul,
    Finset.mul_sum]
  first
    | (refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_; ring)
    | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_; ring)

variable {r : ℕ}

def gv (y : Fin r → S.V) (z : S.V) (N : ℕ) : Fin (r + 1) → S.V :=
  Fin.snoc (α := fun _ => S.V) y ((-((N : E)⁻¹)) • z)

variable (E) in

def Gam (r N' : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -(N' : E) else 0

def Gam' (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  (Z⁻¹).conjTranspose * Gam E r N' * Z⁻¹

def Psi (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (d : Fin r) (a : Fin (r + 1)) : E :=
  if a = Fin.last r then Gam' N' Z (Fin.castSucc d) (Fin.last r) else Gam' N' Z (Fin.castSucc d) a / 2

def pv (e y : Fin r → S.V) (z : S.V) (N N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (w0 : S.V)
    (a : Fin (r + 1)) : S.V :=
  gv y z N a + ∑ d, Psi N' Z d a • e d + (if a = Fin.last r then (1 : E) else 0) • w0

def tv (N N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E :=
  Gam' N' Z (Fin.last r) (Fin.last r) + (N : E)⁻¹

/- English proof (translation)
Simplify using `only [Gam, Matrix.of_apply]`. Apply the tactic sequence `by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]`.
-/
theorem gam_herm (N' : ℕ) (a b : Fin (r + 1)) : star (Gam E r N' a b) = Gam E r N' b a := by
  simp only [Gam, Matrix.of_apply]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]

/- English proof (translation)
Establish `hG : (Gam E r N').conjTranspose = Gam E r N'`. Use extensionality with `a b`. Rewrite using `[Matrix.conjTranspose_apply, gam_herm]`. Establish `h1 : (Gam' N' Z).conjTranspose = Gam' N' Z`. Simplify using `only [Gam', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.mul_assoc]`.

Use `congrFun (congrFun h1 b) a` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_apply]`. Then use the resulting hypothesis.
-/
theorem gam'_herm (N' : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    star (Gam' N' Z a b) = Gam' N' Z b a := by
  have hG : (Gam E r N').conjTranspose = Gam E r N' := by
    ext a b; rw [Matrix.conjTranspose_apply, gam_herm]
  have h1 : (Gam' N' Z).conjTranspose = Gam' N' Z := by
    simp only [Gam', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.mul_assoc]
  have := congrFun (congrFun h1 b) a
  rwa [Matrix.conjTranspose_apply] at this

variable {e y : Fin r → S.V} {z : S.V} {N : ℕ} (h : Dual e y z N) (hN : 0 < N)
include h hN

/- English proof (translation)
Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Rewrite using `[if_neg (Fin.castSucc_lt_last d).ne']`. Simplify using `only [gv, Fin.snoc_last, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hsw0 S (h.ez d), smul_zero]`. Consider the case `cast a`.

Simplify using `only [gv, Fin.snoc_castSucc, Fin.castSucc_inj, h.ye]`. Distinguish the cases in `had : a = d`. Substitute `had` using the available equality. Simplify using the standard rewrite rules. Simplify using `[had, Ne.symm had]`.
-/
theorem hgv_e (a : Fin (r + 1)) (d : Fin r) :
    S.hT (gv y z N a) (e d) = if a = Fin.castSucc d then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    rw [if_neg (Fin.castSucc_lt_last d).ne']
    simp only [gv, Fin.snoc_last, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hsw0 S (h.ez d), smul_zero]
  | cast a =>
    simp only [gv, Fin.snoc_castSucc, Fin.castSucc_inj, h.ye]
    by_cases had : a = d
    · subst had; simp
    · simp [had, Ne.symm had]

/- English proof (translation)
Apply the tactic sequence `rw [hsw, hgv_e h hN]; split_ifs <;> simp`.
-/
theorem he_gv (d : Fin r) (a : Fin (r + 1)) :
    S.hT (e d) (gv y z N a) = if a = Fin.castSucc d then 1 else 0 := by
  rw [hsw, hgv_e h hN]; split_ifs <;> simp

/- English proof (translation)
Establish `hN0 : (N : E) ≠ 0` using `by exact_mod_cast hN.ne'`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Simplify using `only [gv, Fin.snoc_last, map_smul, smul_eq_mul, h.zz, if_true]`. Clear the denominators using the available nonvanishing facts.

Consider the case `cast a`. Rewrite using `[if_neg (Fin.castSucc_lt_last a).ne]`. Simplify using `only [gv, Fin.snoc_castSucc]`. Conclude with `hsw0 S (h.yz a)`.
-/
theorem hz_gv (a : Fin (r + 1)) : S.hT z (gv y z N a) = if a = Fin.last r then 1 else 0 := by
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  induction a using Fin.lastCases with
  | last =>
    simp only [gv, Fin.snoc_last, map_smul, smul_eq_mul, h.zz, if_true]
    field_simp
  | cast a =>
    rw [if_neg (Fin.castSucc_lt_last a).ne]
    simp only [gv, Fin.snoc_castSucc]
    exact hsw0 S (h.yz a)

/- English proof (translation)
Establish `hN0 : (N : E) ≠ 0` using `by exact_mod_cast hN.ne'`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `a' using Fin.lastCases with`. Consider the case `last`.

Simplify using `only [gv, Fin.snoc_last, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, h.zz, starRingEnd_apply, star_neg, star_inv₀, star_natCast, and_self, if_true]`. Clear the denominators using the available nonvanishing facts. Consider the case `cast a'`. Simplify using `only [gv, Fin.snoc_last, Fin.snoc_castSucc, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hsw0 S (h.yz a'), smul_zero]`. Simplify using `[(Fin.castSucc_lt_last a').ne]`.

Consider the case `cast a`. Proceed by induction on `a' using Fin.lastCases with`. Consider the case `last`. Simplify using `only [gv, Fin.snoc_last, Fin.snoc_castSucc, map_smul, h.yz, smul_zero]`. Simplify using `[(Fin.castSucc_lt_last a).ne]`.

Consider the case `cast a'`. Simplify using `only [gv, Fin.snoc_castSucc, h.yy]`. Simplify using `[(Fin.castSucc_lt_last a).ne]`.
-/
theorem hgv_gv (a a' : Fin (r + 1)) : S.hT (gv y z N a) (gv y z N a') =
    if a = Fin.last r ∧ a' = Fin.last r then -((N : E)⁻¹) else 0 := by
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  induction a using Fin.lastCases with
  | last =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [gv, Fin.snoc_last, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, h.zz,
        starRingEnd_apply, star_neg, star_inv₀, star_natCast, and_self, if_true]
      field_simp
    | cast a' =>
      simp only [gv, Fin.snoc_last, Fin.snoc_castSucc, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        hsw0 S (h.yz a'), smul_zero]
      simp [(Fin.castSucc_lt_last a').ne]
  | cast a =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [gv, Fin.snoc_last, Fin.snoc_castSucc, map_smul, h.yz, smul_zero]
      simp [(Fin.castSucc_lt_last a).ne]
    | cast a' =>
      simp only [gv, Fin.snoc_castSucc, h.yy]
      simp [(Fin.castSucc_lt_last a).ne]

variable {N' : ℕ} {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {w0 : S.V} (hw : IsW e y z w0)
include hw

/- English proof (translation)
Take `⟨hwe, -, hwz⟩` from `hw`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Simplify using `only [pv, Fin.snoc_last, map_add, map_sum, map_smul, smul_eq_mul, hsw0 S (h.ez _), mul_zero, Finset.sum_const_zero, add_zero, hwz, hz_gv h hN]`. Simplify using `[eq_comm]`.

Consider the case `cast a`. Simplify using `only [pv, Fin.snoc_castSucc, map_add, map_sum, map_smul, smul_eq_mul, h.ee, mul_zero, Finset.sum_const_zero, add_zero, hwe, he_gv h hN]`. Simplify using `[eq_comm]`.
-/
theorem hf_pv (a a' : Fin (r + 1)) :
    S.hT (Fin.snoc (α := fun _ => S.V) e z a) (pv e y z N N' Z w0 a') = if a = a' then 1 else 0 := by
  obtain ⟨hwe, -, hwz⟩ := hw
  induction a using Fin.lastCases with
  | last =>
    simp only [pv, Fin.snoc_last, map_add, map_sum, map_smul, smul_eq_mul, hsw0 S (h.ez _), mul_zero,
      Finset.sum_const_zero, add_zero, hwz, hz_gv h hN]
    simp [eq_comm]
  | cast a =>
    simp only [pv, Fin.snoc_castSucc, map_add, map_sum, map_smul, smul_eq_mul, h.ee, mul_zero,
      Finset.sum_const_zero, add_zero, hwe, he_gv h hN]
    simp [eq_comm]

/- English proof (translation)
Take `⟨hwe, hwy, hwz⟩` from `hw`. Establish `hgw : ∀ b, S.hT (gv y z N b) w0 = 0`. Introduce `b`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => simp [gv, hwz]`.

Consider the case `cast b => simp [gv, hwy]`. Establish `hwg : ∀ b, S.hT w0 (gv y z N b) = 0` using `fun b => hsw0 S (hgw b)`. Establish `hwe' : ∀ d, S.hT w0 (e d) = 0` using `fun d => hsw0 S (hwe d)`. Establish `key : S.hT (pv e y z N N' Z w0 a) (pv e y z N N' Z w0 a') = S.hT (gv y z N a) (gv y z N a') + ∑ d, Psi N' Z d a' * S.hT (gv y z N a) (e d) + ∑ d, star (Psi N' Z d a) * S.hT (e d) (gv y z N a') + star (if a = Fin.last r then (1 : E) else 0) * (if a' = Fin.last r then (1 : E) else …`. Simplify using `only [pv, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, h.ee, mul_zero, Finset.sum_const_zero, hgw, hwg, hwe, hwe', add_zero, zero_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, hgv_gv h hN, ht]`. Simplify using `only [hgv_e h hN, he_gv h hN, mul_ite, mul_one, mul_zero]`. Establish `hne : ∀ d : Fin r, Fin.last r ≠ Fin.castSucc d` using `fun d => (Fin.castSucc_lt_last d).ne'`. Proceed by induction on `a using Fin.lastCases with`.

Consider the case `last`. Proceed by induction on `a' using Fin.lastCases with`. Consider the case `last => simp [tv, hne]`. Consider the case `cast a' => simp [hne, Psi, gam'_herm]`. Consider the case `cast a`.

Proceed by induction on `a' using Fin.lastCases with`. Consider the case `last => simp [hne, (Fin.castSucc_lt_last a).ne, Psi]`. Consider the case `cast a'`. Simplify using `[(Fin.castSucc_lt_last a).ne, (Fin.castSucc_lt_last a').ne, Psi, star_div₀, gam'_herm]`.
-/
theorem hpv_pv (ht : S.hT w0 w0 = tv N N' Z) (a a' : Fin (r + 1)) :
    S.hT (pv e y z N N' Z w0 a) (pv e y z N N' Z w0 a') = Gam' N' Z a a' := by
  obtain ⟨hwe, hwy, hwz⟩ := hw
  have hgw : ∀ b, S.hT (gv y z N b) w0 = 0 := by
    intro b
    induction b using Fin.lastCases with
    | last => simp [gv, hwz]
    | cast b => simp [gv, hwy]
  have hwg : ∀ b, S.hT w0 (gv y z N b) = 0 := fun b => hsw0 S (hgw b)
  have hwe' : ∀ d, S.hT w0 (e d) = 0 := fun d => hsw0 S (hwe d)
  have key : S.hT (pv e y z N N' Z w0 a) (pv e y z N N' Z w0 a') =
      S.hT (gv y z N a) (gv y z N a') +
      ∑ d, Psi N' Z d a' * S.hT (gv y z N a) (e d) +
      ∑ d, star (Psi N' Z d a) * S.hT (e d) (gv y z N a') +
      star (if a = Fin.last r then (1 : E) else 0) * (if a' = Fin.last r then (1 : E) else 0) * S.hT w0 w0 := by
    simp only [pv, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, h.ee, mul_zero, Finset.sum_const_zero, hgw, hwg,
      hwe, hwe', add_zero, zero_add]
    ring
  rw [key, hgv_gv h hN, ht]
  simp only [hgv_e h hN, he_gv h hN, mul_ite, mul_one, mul_zero]
  have hne : ∀ d : Fin r, Fin.last r ≠ Fin.castSucc d := fun d => (Fin.castSucc_lt_last d).ne'
  induction a using Fin.lastCases with
  | last =>
    induction a' using Fin.lastCases with
    | last => simp [tv, hne]
    | cast a' => simp [hne, Psi, gam'_herm]
  | cast a =>
    induction a' using Fin.lastCases with
    | last => simp [hne, (Fin.castSucc_lt_last a).ne, Psi]
    | cast a' =>
      simp [(Fin.castSucc_lt_last a).ne, (Fin.castSucc_lt_last a').ne, Psi, star_div₀, gam'_herm]

end Gen

end Formalism.L2.SG.Pf.Cnt.R1
