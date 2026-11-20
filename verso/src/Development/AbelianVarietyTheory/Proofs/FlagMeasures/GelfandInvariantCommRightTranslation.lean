import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceTransposePow

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section
namespace GlobalTheory.Dec.GelfAd

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, mul_assoc, ← Algebra.commutes (Q d b) (X c d), ← mul_assoc]`.
-/
private lemma conj_apply_lemma {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) a b = ∑ c, ∑ d, (P a c * Q d b) • X c d := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Algebra.smul_def, map_mul, mul_assoc, ← Algebra.commutes (Q d b) (X c d), ← mul_assoc]

/- English proof (translation)
Simplify using `only [conj_apply_lemma]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul]`.

Establish `hd : ∀ d, ∑ a, P a c * Q d a = (1 : Matrix (Fin n) (Fin n) ℂ) d c` using `fun d => by`. Rewrite using `[← hQP, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`. Simplify using `[hd, Matrix.one_apply]`.
-/
private lemma sum_diag_conj_eq_sum_diag {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (X : Matrix (Fin n) (Fin n) A) :
    ∑ a, (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) a a = ∑ a, X a a := by
  simp only [conj_apply_lemma]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hd : ∀ d, ∑ a, P a c * Q d a = (1 : Matrix (Fin n) (Fin n) ℂ) d c := fun d => by
    rw [← hQP, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  simp [hd, Matrix.one_apply]

/- English proof (translation)
Establish `hPQ : P * Q = 1` using `mul_eq_one_comm.mp hQP`. Establish `h1 : Q.map (algebraMap ℂ A) * P.map (algebraMap ℂ A) = 1`. Rewrite using `[← Matrix.map_mul, hQP]`. Simplify using the standard rewrite rules. Establish `h2 : P.map (algebraMap ℂ A) * Q.map (algebraMap ℂ A) = 1`.

Rewrite using `[← Matrix.map_mul, hPQ]`. Simplify using the standard rewrite rules. Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero, mul_one, h2]`. Consider the case `succ m ih`.

Rewrite using `[pow_succ, ih, pow_succ]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (Q.map (algebraMap ℂ A)) (P.map (algebraMap ℂ A)), h1, one_mul]`.
-/
private lemma conj_pow_of_mul_eq_one' {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (X : Matrix (Fin n) (Fin n) A) (m : ℕ) :
    (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) ^ m =
      P.map (algebraMap ℂ A) * X ^ m * Q.map (algebraMap ℂ A) := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have h1 : Q.map (algebraMap ℂ A) * P.map (algebraMap ℂ A) = 1 := by
    rw [← Matrix.map_mul, hQP]
    simp
  have h2 : P.map (algebraMap ℂ A) * Q.map (algebraMap ℂ A) = 1 := by
    rw [← Matrix.map_mul, hPQ]
    simp
  induction m with
  | zero => rw [pow_zero, pow_zero, mul_one, h2]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc (Q.map (algebraMap ℂ A)) (P.map (algebraMap ℂ A)), h1, one_mul]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `a b`. Apply the tactic sequence `by_cases hab : a = b <;> simp [Matrix.one_apply, hab]`. Consider the case `succ m ih`.

Introduce `a b`. Rewrite using `[pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, h c b, ← mul_assoc ((M ^ m) a c), ih a c, mul_assoc]`.
-/
private lemma pow_apply_mul_eq_mul_pow_apply {A : Type} [Ring A] (M N : Matrix (Fin n) (Fin n) A) (R : A)
    (h : ∀ a b, M a b * R = R * N a b) (m : ℕ) :
    ∀ a b, (M ^ m) a b * R = R * (N ^ m) a b := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  | succ m ih =>
    intro a b
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_assoc, h c b, ← mul_assoc ((M ^ m) a c), ih a c, mul_assoc]

/- English proof (translation)
Establish `hN : ∀ a b, Matrix.of E a b * R = R * (P.map (algebraMap ℂ A) * Matrix.of E * Q.map (algebraMap ℂ A)) a b`. Introduce `a b`. Rewrite using `[conj_apply_lemma]`. Conclude with `h a b`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun c _ => pow_apply_mul_eq_mul_pow_apply _ _ R hN m c c`. Use `_ = R * ∑ c, (Matrix.of E ^ m) c c := by`. Rewrite using `[← Finset.mul_sum, conj_pow_of_mul_eq_one' P Q hQP, sum_diag_conj_eq_sum_diag P Q hQP]`.
-/
lemma trace_pow_comm {A : Type} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (R : A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (h : ∀ a b, E a b * R = R * ∑ c, ∑ d, (P a c * Q d b) • E c d) (m : ℕ) :
    (∑ c, (Matrix.of E ^ m) c c) * R = R * ∑ c, (Matrix.of E ^ m) c c := by
  have hN : ∀ a b, Matrix.of E a b * R =
      R * (P.map (algebraMap ℂ A) * Matrix.of E * Q.map (algebraMap ℂ A)) a b := by
    intro a b
    rw [conj_apply_lemma]
    exact h a b
  calc (∑ c, (Matrix.of E ^ m) c c) * R
      = ∑ c, R * ((P.map (algebraMap ℂ A) * Matrix.of E * Q.map (algebraMap ℂ A)) ^ m) c c := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => pow_apply_mul_eq_mul_pow_apply _ _ R hN m c c
    _ = R * ∑ c, (Matrix.of E ^ m) c c := by
        rw [← Finset.mul_sum, conj_pow_of_mul_eq_one' P Q hQP, sum_diag_conj_eq_sum_diag P Q hQP]

/- English proof (translation)
Unfold `inUJ at hk`. Rewrite using `[Matrix.mul_assoc (Jm ε * kᴴ), Matrix.mul_assoc (Jm ε), ← Matrix.mul_assoc kᴴ, hk, Formalism.REAL.Jm_mul_self]`.
-/
lemma inv_mul_of_UJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    Jm ε * kᴴ * Jm ε * k = 1 := by
  unfold inUJ at hk
  rw [Matrix.mul_assoc (Jm ε * kᴴ), Matrix.mul_assoc (Jm ε), ← Matrix.mul_assoc kᴴ, hk,
    Formalism.REAL.Jm_mul_self]

/- English proof (translation)
Establish `hd : IsUnit k.det` using `(Matrix.isUnit_iff_isUnit_det k).mp hk`. Simplify using `only [Rd]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Use `congr 1`.

Rewrite using `[show ((t : ℂ) • (k⁻¹ * X * k)) = k⁻¹ * ((t : ℂ) • X) * k by`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul], Matrix.exp_conj' k _ hk]`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc g k k⁻¹, Matrix.mul_nonsing_inv k hd, Matrix.mul_one]`.
-/
lemma Rd_right (X k g : Matrix (Fin n) (Fin n) ℂ) (hk : IsUnit k) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Rd X (fun x => f (x * k)) g = Rd (k⁻¹ * X * k) f (g * k) := by
  have hd : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det k).mp hk
  simp only [Rd]
  congr 1
  funext t
  congr 1
  rw [show ((t : ℂ) • (k⁻¹ * X * k)) = k⁻¹ * ((t : ℂ) • X) * k by
    rw [Matrix.mul_smul, Matrix.smul_mul], Matrix.exp_conj' k _ hk]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc g k k⁻¹, Matrix.mul_nonsing_inv k hd, Matrix.mul_one]

/- English proof (translation)
The claim follows from `(Matrix.isUnit_iff_isUnit_det k).mpr (Matrix.isUnit_det_of_left_inverse (inv_mul_of_UJ hk))`.
-/
private lemma isUnit_of_inUJ_flag_measures {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    IsUnit k :=
  (Matrix.isUnit_iff_isUnit_det k).mpr (Matrix.isUnit_det_of_left_inverse (inv_mul_of_UJ hk))

/- English proof (translation)
Establish `hinv : k⁻¹ = Jm ε * kᴴ * Jm ε` using `Matrix.inv_eq_left_inv (inv_mul_of_UJ hk)`. Establish `hL : Jm ε * kᴴ = k⁻¹ * Jm ε`. Rewrite using `[hinv]`. Simplify using `only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]`. Establish `hR : (k⁻¹)ᴴ * Jm ε = Jm ε * k`.

Rewrite using `[hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose, Matrix.conjTranspose_conjTranspose]`. Simplify using `only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hR, ← Matrix.mul_assoc (Jm ε) kᴴ, hL]`.

Simplify using `only [Matrix.mul_assoc]`.
-/
private lemma Jm_conjTranspose_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (k⁻¹ * Z * k)ᴴ * Jm ε = k⁻¹ * (Jm ε * Zᴴ * Jm ε) * k := by
  have hinv : k⁻¹ = Jm ε * kᴴ * Jm ε := Matrix.inv_eq_left_inv (inv_mul_of_UJ hk)
  have hL : Jm ε * kᴴ = k⁻¹ * Jm ε := by
    rw [hinv]
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
  have hR : (k⁻¹)ᴴ * Jm ε = Jm ε * k := by
    rw [hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [hR, ← Matrix.mul_assoc (Jm ε) kᴴ, hL]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[cpart1, cpart1, Jm_conjTranspose_conj_of_inUJ hk, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul]`.
-/
private lemma cpart1_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cpart1 ε (k⁻¹ * Z * k) = k⁻¹ * cpart1 ε Z * k := by
  rw [cpart1, cpart1, Jm_conjTranspose_conj_of_inUJ hk, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_smul,
    Matrix.smul_mul]

/- English proof (translation)
Rewrite using `[cpart2, cpart2, Jm_conjTranspose_conj_of_inUJ hk, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul]`.
-/
private lemma cpart2_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cpart2 ε (k⁻¹ * Z * k) = k⁻¹ * cpart2 ε Z * k := by
  rw [cpart2, cpart2, Jm_conjTranspose_conj_of_inUJ hk, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_smul,
    Matrix.smul_mul]

/- English proof (translation)
Establish `hu` using `isUnit_of_inUJ_flag_measures hk`. Simplify using `only [Ec]`. Rewrite using `[Rd_right _ _ _ hu f, Rd_right _ _ _ hu f, cpart1_conj_of_inUJ hk, cpart2_conj_of_inUJ hk]`.
-/
lemma Ec_right {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z g : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Ec ε Z (fun x => f (x * k)) g = Ec ε (k⁻¹ * Z * k) f (g * k) := by
  have hu := isUnit_of_inUJ_flag_measures hk
  simp only [Ec]
  rw [Rd_right _ _ _ hu f, Rd_right _ _ _ hu f, cpart1_conj_of_inUJ hk, cpart2_conj_of_inUJ hk]

/- English proof (translation)
Unfold `inUJ at *`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma inUJ_mul_flag_measures' {ε : Fin n → Bool} {g k : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (hk : inUJ ε k) : inUJ ε (g * k) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc kᴴ * gᴴ * Jm ε * (g * k) = kᴴ * (gᴴ * Jm ε * g) * k := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hk]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
/- English proof (translation)
Establish `hc : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * k)` using `(LinearMap.mulRight ℝ k).toContinuousLinearMap.contDiff`. Unfold `SmoothOnG at hf ⊢`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hmem, hF, hfF⟩` from `hf (g₀ * k) (inUJ_mul_flag_measures' hg₀ hk)`. Conclude with `⟨(fun x => x * k) ⁻¹' U, fun x => F (x * k), hU.preimage hc.continuous, hmem, hF.comp hc.contDiffOn (fun _ hx => hx), fun g hg hgJ => hfF (g * k) hg (inUJ_mul_flag_measures' hgJ hk)⟩`.
-/
lemma smooth_right {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) : SmoothOnG ε (fun x => f (x * k)) := by
  have hc : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * k) :=
    (LinearMap.mulRight ℝ k).toContinuousLinearMap.contDiff
  unfold SmoothOnG at hf ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hfF⟩ := hf (g₀ * k) (inUJ_mul_flag_measures' hg₀ hk)
  exact ⟨(fun x => x * k) ⁻¹' U, fun x => F (x * k), hU.preimage hc.continuous, hmem,
    hF.comp hc.contDiffOn (fun _ hx => hx), fun g hg hgJ => hfF (g * k) hg (inUJ_mul_flag_measures' hgJ hk)⟩

open GlobalTheory.CapelliCentral in

def rightEnd {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    Module.End ℂ (smoothSpace ε ℂ) where
  toFun F := mk (fun x => F.1 (x * k)) (smooth_right hk F.2.1)
  map_add' F F' := by
    apply ext_on
    intro g hg
    exact (mk_apply _ (smooth_right hk (F + F').2.1) hg).trans
      (congrArg₂ (· + ·) (mk_apply _ (smooth_right hk F.2.1) hg).symm
        (mk_apply _ (smooth_right hk F'.2.1) hg).symm)
  map_smul' c F := by
    apply ext_on
    intro g hg
    exact (mk_apply _ (smooth_right hk (c • F).2.1) hg).trans
      (congrArg (c • ·) (mk_apply _ (smooth_right hk F.2.1) hg).symm)

open GlobalTheory.CapelliCentral in
/- English proof (translation)
Simplify using `only [rightEnd, LinearMap.coe_mk, AddHom.coe_mk]`. Conclude with `mk_apply _ _ hg`.
-/
lemma rightEnd_apply {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (F : smoothSpace ε ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    (rightEnd hk F).1 g = F.1 (g * k) := by
  simp only [rightEnd, LinearMap.coe_mk, AddHom.coe_mk]
  exact mk_apply _ _ hg

/- English proof (translation)
Simplify using `only [Ec, EcV, rdV_eq, smul_eq_mul]`.
-/
private lemma Ec_eq_EcV (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Ec ε Z f g = EcV ε Z f g := by
  simp only [Ec, EcV, rdV_eq, smul_eq_mul]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Matrix.single_apply, ite_and]`.
-/
private lemma mul_single_mul_apply' (M N : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (M * Matrix.single a b (1 : ℂ) * N : Matrix (Fin n) (Fin n) ℂ) c d = M c a * N b d := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

open GlobalTheory.CapelliCentral in
/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `F`. Apply `ext_on` to reduce the goal to its premises. Introduce `g hg`. Establish `hgk : inUJ ε (g * k)` using `inUJ_mul_flag_measures' hg hk`.

Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, rightEnd_apply hk _ hg, eabEnd_apply (f := fun x => F.1 (x * k)) a b (rightEnd hk F) (fun x hx => rightEnd_apply hk F hx) hg, eabV_eq, Eab, Ec_right hk _ g F.1, Ec_eq_EcV, ecSumV n ε ℂ F.1 _ (g * k) F.2.1 hgk]`. Simplify using `only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, eabEnd_apply (f := F.1) _ _ F (fun _ _ => rfl) hgk, mul_single_mul_apply', Matrix.transpose_apply]`.
-/
lemma eabEnd_rightEnd {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) (a b : Fin n) :
    eabEnd ε ℂ a b * rightEnd hk =
      rightEnd hk * ∑ c, ∑ d, ((k⁻¹)ᵀ a c * kᵀ d b) • eabEnd ε ℂ c d := by
  apply LinearMap.ext
  intro F
  apply ext_on
  intro g hg
  have hgk : inUJ ε (g * k) := inUJ_mul_flag_measures' hg hk
  rw [Module.End.mul_apply, Module.End.mul_apply, rightEnd_apply hk _ hg,
    eabEnd_apply (f := fun x => F.1 (x * k)) a b (rightEnd hk F) (fun x hx => rightEnd_apply hk F hx) hg,
    eabV_eq, Eab, Ec_right hk _ g F.1, Ec_eq_EcV, ecSumV n ε ℂ F.1 _ (g * k) F.2.1 hgk]
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, Pi.smul_apply, eabEnd_apply (f := F.1) _ _ F (fun _ _ => rfl) hgk,
    mul_single_mul_apply', Matrix.transpose_apply]

/- English proof (translation)
Introduce `n ε m f k g hf hk hg`. Establish `hkU : inUJ ε k` using `hk`. Establish `hgU : inUJ ε g` using `hg`. Establish `hd : IsUnit k.det` using `(Matrix.isUnit_iff_isUnit_det k).mp (isUnit_of_inUJ_flag_measures hkU)`. Establish `hQP : kᵀ * (k⁻¹)ᵀ = 1`.

Rewrite using `[← Matrix.transpose_mul, Matrix.nonsing_inv_mul k hd, Matrix.transpose_one]`. Establish `hfV : SmoothOnGV ε f` using `(smoothOnGV_iff ε f).mpr hf`. Set `F : GlobalTheory.CapelliCentral.smoothSpace ε ℂ` to `GlobalTheory.CapelliCentral.mk f hfV`. Establish `hFf : ∀ x, inUJ ε x → F.1 x = f x` using `fun x hx => GlobalTheory.CapelliCentral.mk_apply f hfV hx`. Establish `hcomm` using `trace_pow_comm (GlobalTheory.CapelliCentral.eabEnd ε ℂ) (rightEnd hkU) (k⁻¹)ᵀ kᵀ hQP (eabEnd_rightEnd hkU) (m + 1)`.

Establish `h1` using `congrArg (fun T : Module.End ℂ (GlobalTheory.CapelliCentral.smoothSpace ε ℂ) => (T F).1 g) hcomm`. Simplify using `only [Module.End.mul_apply] at h1`. Rewrite `h1` using `[GlobalTheory.Dec.FormF.gelf_apply (f := fun x => f (x * k)) m (rightEnd hkU F) (fun x hx => (rightEnd_apply hkU F hx).trans (hFf _ (inUJ_mul_flag_measures' hx hkU))) hgU, rightEnd_apply hkU _ hgU, GlobalTheory.Dec.FormF.gelf_apply m F hFf (inUJ_mul_flag_measures' hgU hkU)]`. Conclude with `h1`.
-/
theorem gelf_right : ∀ (n : ℕ) (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (k g : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → k ∈ UJset ε → g ∈ UJset ε →
    gelf ε m (fun x => f (x * k)) g = gelf ε m f (g * k) := by
  intro n ε m f k g hf hk hg
  have hkU : inUJ ε k := hk
  have hgU : inUJ ε g := hg
  have hd : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det k).mp (isUnit_of_inUJ_flag_measures hkU)
  have hQP : kᵀ * (k⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul k hd, Matrix.transpose_one]
  have hfV : SmoothOnGV ε f := (smoothOnGV_iff ε f).mpr hf
  let F : GlobalTheory.CapelliCentral.smoothSpace ε ℂ := GlobalTheory.CapelliCentral.mk f hfV
  have hFf : ∀ x, inUJ ε x → F.1 x = f x := fun x hx => GlobalTheory.CapelliCentral.mk_apply f hfV hx
  have hcomm := trace_pow_comm (GlobalTheory.CapelliCentral.eabEnd ε ℂ) (rightEnd hkU) (k⁻¹)ᵀ kᵀ hQP
    (eabEnd_rightEnd hkU) (m + 1)
  have h1 := congrArg (fun T : Module.End ℂ (GlobalTheory.CapelliCentral.smoothSpace ε ℂ) => (T F).1 g) hcomm
  simp only [Module.End.mul_apply] at h1
  rw [GlobalTheory.Dec.FormF.gelf_apply (f := fun x => f (x * k)) m (rightEnd hkU F)
      (fun x hx => (rightEnd_apply hkU F hx).trans (hFf _ (inUJ_mul_flag_measures' hx hkU))) hgU,
    rightEnd_apply hkU _ hgU,
    GlobalTheory.Dec.FormF.gelf_apply m F hFf (inUJ_mul_flag_measures' hgU hkU)] at h1
  exact h1

end GlobalTheory.Dec.GelfAd
