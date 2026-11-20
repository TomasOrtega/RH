import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLogDerivQExpansionModPrimePowOfTranslationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionFinsetProdZpowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowUniqueStatement

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.NrmT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Apply `ε.injective` to reduce the goal to its premises. Rewrite using `[map_mul, KTExp.map_eOm, KTExp.map_eOm, KTExp.map_eOm, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eOm_add' (x y : ℚ) : eOm ε (x + y) = eOm ε x * eOm ε y := by
  apply ε.injective
  rw [map_mul, KTExp.map_eOm, KTExp.map_eOm, KTExp.map_eOm, ← Complex.exp_add]
  congr 1; push_cast; ring

/- English proof (translation)
The claim follows from `(KTExp.eOm_eq_one_iff ε 0).2 rfl`.
-/
theorem eOm_zero' : eOm ε 0 = 1 := (KTExp.eOm_eq_one_iff ε 0).2 rfl

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `zero => simp only [Nat.cast_zero, mul_zero, pow_zero]`. Conclude with `eOm_zero'`. Consider the case `succ k ih => rw [Nat.cast_succ, mul_add, mul_one, eOm_add', ih, pow_succ]`.
-/
theorem eOm_nat_mul (x : ℚ) (b : ℕ) : eOm ε (x * b) = eOm ε x ^ b := by
  induction b with
  | zero => simp only [Nat.cast_zero, mul_zero, pow_zero]; exact eOm_zero'
  | succ k ih => rw [Nat.cast_succ, mul_add, mul_one, eOm_add', ih, pow_succ]

/- English proof (translation)
Rewrite using `[← eOm_nat_mul, (KTExp.eOm_eq_one_iff ε _).2]`. Rewrite using `[Rat.mul_den_eq_num]`. Simplify using the standard rewrite rules.
-/
theorem eOm_pow_den (x : ℚ) : eOm ε x ^ x.den = 1 := by
  rw [← eOm_nat_mul, (KTExp.eOm_eq_one_iff ε _).2]
  rw [Rat.mul_den_eq_num]; simp

/- English proof (translation)
Break down `A.mem_or_inv_mem z with hz | hz` into its components or cases. Conclude with `hz`. Establish `h1 : z * z ^ (d - 1) = 1` using `by rw [← pow_succ', Nat.sub_add_cancel hd, h]`. Rewrite using `[eq_inv_of_mul_eq_one_left h1, ← inv_pow]`. Conclude with `pow_mem hz _`.
-/
theorem mem_of_pow_eq_one (A : ValuationSubring Ω) {z : Ω} {d : ℕ} (hd : 0 < d) (h : z ^ d = 1) : z ∈ A := by
  rcases A.mem_or_inv_mem z with hz | hz
  · exact hz
  · have h1 : z * z ^ (d - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hd, h]
    rw [eq_inv_of_mul_eq_one_left h1, ← inv_pow]
    exact pow_mem hz _

/- English proof (translation)
The claim follows from `mem_of_pow_eq_one A x.den_pos (eOm_pow_den x)`.
-/
theorem eOm_mem (A : ValuationSubring Ω) (x : ℚ) : eOm ε x ∈ A :=
  mem_of_pow_eq_one A x.den_pos (eOm_pow_den x)

/- English proof (translation)
Introduce `h`. Use `eOm_pow_den (ε := ε) x` as an intermediate fact. Rewrite `this` using `[h, zero_pow x.den_nz]`. Conclude with `zero_ne_one this`.
-/
theorem eOm_ne_zero (x : ℚ) : eOm ε x ≠ 0 := by
  intro h
  have := eOm_pow_den (ε := ε) x
  rw [h, zero_pow x.den_nz] at this
  exact zero_ne_one this

/- English proof (translation)
Establish `h : eOm ε (-x) * eOm ε x = 1` using `by rw [← eOm_add', neg_add_cancel, eOm_zero']`. Rewrite using `[← eq_inv_of_mul_eq_one_left h]`. Conclude with `eOm_mem A _`.
-/
theorem eOm_inv_mem (A : ValuationSubring Ω) (x : ℚ) : (eOm ε x)⁻¹ ∈ A := by
  have h : eOm ε (-x) * eOm ε x = 1 := by rw [← eOm_add', neg_add_cancel, eOm_zero']
  rw [← eq_inv_of_mul_eq_one_left h]
  exact eOm_mem A _

def trT (ε : Ω →+* ℂ) (b : ℕ) (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω where
  coeff r := eOm ε (r * b) * φ.coeff r
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trT_coeff (b : ℕ) (φ : HahnSeries ℚ Ω) (r : ℚ) : (trT ε b φ).coeff r = eOm ε (r * b) * φ.coeff r := rfl

/- English proof (translation)
Introduce `r hr h` and use `hr (by rw [trT_coeff, h, mul_zero])`.
-/
theorem trT_support (b : ℕ) (φ : HahnSeries ℚ Ω) : (trT ε b φ).support ⊆ φ.support :=
  fun r hr h => hr (by rw [trT_coeff, h, mul_zero])

/- English proof (translation)
Rewrite using `[HahnSeries.coeff_mul]`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `ij hij`. Rewrite `hij` using `[Finset.mem_addAntidiagonal]`. Conclude with `Finset.mem_addAntidiagonal.2 ⟨hxs hij.1, hyt hij.2.1, hij.2.2⟩`.

Introduce `ij hij hn`. Distinguish the cases in `h1 : x.coeff ij.1 = 0`. Rewrite using `[h1, zero_mul]`. Distinguish the cases in `h2 : y.coeff ij.2 = 0`. Rewrite using `[h2, mul_zero]`.

Conclude with `absurd (Finset.mem_addAntidiagonal.2 ⟨h1, h2, (Finset.mem_addAntidiagonal.1 hij).2.2⟩) hn`.
-/
theorem coeff_mul_sup {x y : HahnSeries ℚ Ω} {s t : Set ℚ} (hs : s.IsPWO) (ht : t.IsPWO) (hxs : x.support ⊆ s)
    (hyt : y.support ⊆ t) (a : ℚ) :
    (x * y).coeff a = ∑ ij ∈ Finset.addAntidiagonal hs ht a, x.coeff ij.1 * y.coeff ij.2 := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_subset
  · intro ij hij
    rw [Finset.mem_addAntidiagonal] at hij
    exact Finset.mem_addAntidiagonal.2 ⟨hxs hij.1, hyt hij.2.1, hij.2.2⟩
  · intro ij hij hn
    by_cases h1 : x.coeff ij.1 = 0
    · rw [h1, zero_mul]
    · by_cases h2 : y.coeff ij.2 = 0
      · rw [h2, mul_zero]
      · exact absurd (Finset.mem_addAntidiagonal.2 ⟨h1, h2, (Finset.mem_addAntidiagonal.1 hij).2.2⟩) hn

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[coeff_mul_sup x.isPWO_support y.isPWO_support (trT_support b x) (trT_support b y)]`. Simplify using `only [trT_coeff]`. Rewrite using `[HahnSeries.coeff_mul, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `ij hij`. Rewrite `hij` using `[Finset.mem_addAntidiagonal]`. Rewrite using `[← hij.2.2, add_mul, eOm_add']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trT_mul (b : ℕ) (x y : HahnSeries ℚ Ω) : trT ε b (x * y) = trT ε b x * trT ε b y := by
  ext a
  rw [coeff_mul_sup x.isPWO_support y.isPWO_support (trT_support b x) (trT_support b y)]
  simp only [trT_coeff]
  rw [HahnSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Finset.mem_addAntidiagonal] at hij
  rw [← hij.2.2, add_mul, eOm_add']
  ring

/- English proof (translation)
Use extensionality with `r`. Simplify using `only [trT_coeff, HahnSeries.coeff_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trT_sub (b : ℕ) (x y : HahnSeries ℚ Ω) : trT ε b (x - y) = trT ε b x - trT ε b y := by
  ext r
  simp only [trT_coeff, HahnSeries.coeff_sub]
  ring

/- English proof (translation)
Use extensionality with `r`. Use `show algebraMap ℚ Ω (s * r) * (eOm ε (r * b) * φ.coeff r) = eOm ε (r * b) * (algebraMap ℚ Ω (s * r) * φ.coeff r)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_trT (s : ℚ) (b : ℕ) (φ : HahnSeries ℚ Ω) : theta s (trT ε b φ) = trT ε b (theta s φ) := by
  ext r
  show algebraMap ℚ Ω (s * r) * (eOm ε (r * b) * φ.coeff r) = eOm ε (r * b) * (algebraMap ℚ Ω (s * r) * φ.coeff r)
  ring

/- English proof (translation)
Take `⟨h00, h01, h10, h11⟩` from `KTExp.ent_T_pow b`. Use extensionality with `r`. Use `X.exp_upper (ofSL (ModularGroup.T ^ b)) h10 f r` as an intermediate fact. Rewrite `this` using `[h00, h01, h11, mul_one, div_one, div_one]`. Rewrite using `[trT_coeff]`.

Conclude with `this`.
-/
theorem modularTowerExp_slAction_T_pow (X : Tower Ω ε) (b : ℕ) (f : X.K) :
    X.exp (X.sl (ofSL (ModularGroup.T ^ b)) f) = trT ε b (X.exp f) := by
  obtain ⟨h00, h01, h10, h11⟩ := KTExp.ent_T_pow b
  ext r
  have := X.exp_upper (ofSL (ModularGroup.T ^ b)) h10 f r
  rw [h00, h01, h11, mul_one, div_one, div_one] at this
  rw [trT_coeff]; exact this

/- English proof (translation)
Take `⟨z, hz, e⟩` from `h`. Conclude with `⟨c * z, mul_mem hc hz, by rw [← mul_sub, e]; ring⟩`.
-/
theorem cgA_mul (A : ValuationSubring Ω) (l n : ℕ) {c x y : Ω} (hc : c ∈ A) (h : CgA A l n x y) :
    CgA A l n (c * x) (c * y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨c * z, mul_mem hc hz, by rw [← mul_sub, e]; ring⟩

/- English proof (translation)
Take `⟨hi, r, hr0, hru⟩` from `h`. Use `⟨fun r => mul_mem (eOm_mem A _) (hi r), r, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[trT_coeff]`. Conclude with `mul_ne_zero (eOm_ne_zero _) hr0`. Rewrite using `[trT_coeff, mul_inv]`.

Conclude with `mul_mem (eOm_inv_mem A _) hru`.
-/
theorem prim_trT (A : ValuationSubring Ω) (b : ℕ) {φ : HahnSeries ℚ Ω} (h : Prim A φ) : Prim A (trT ε b φ) := by
  obtain ⟨hi, r, hr0, hru⟩ := h
  refine ⟨fun r => mul_mem (eOm_mem A _) (hi r), r, ?_, ?_⟩
  · rw [trT_coeff]; exact mul_ne_zero (eOm_ne_zero _) hr0
  · rw [trT_coeff, mul_inv]; exact mul_mem (eOm_inv_mem A _) hru

/- English proof (translation)
Take `⟨hφ, a, c, κ, hκ, he, ha, hc, hcg⟩` from `h`. Use `⟨fun r => mul_mem (eOm_mem A _) (hφ r), X.sl (ofSL (ModularGroup.T ^ b)) a, X.sl (ofSL (ModularGroup.T ^ b)) c, κ, hκ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul (X.sl (ofSL (ModularGroup.T ^ b))) f c, he, map_mul, AlgEquiv.commutes]`. Rewrite using `[modularTowerExp_slAction_T_pow]`. Conclude with `prim_trT A b ha`.

Rewrite using `[modularTowerExp_slAction_T_pow]`. Conclude with `prim_trT A b hc`. Introduce `r`. Rewrite using `[modularTowerExp_slAction_T_pow, modularTowerExp_slAction_T_pow]`. Simplify using `only [theta_trT, ← trT_mul, ← trT_sub]`.

Simplify using `only [trT_coeff]`. Conclude with `cgA_mul A l m (eOm_mem A _) (hcg r)`.
-/
theorem isLogDerivQExpansionModPrimePow_slash_T_pow (X : Tower Ω ε) (A : ValuationSubring Ω) (l m : ℕ) (s : ℚ) (f : X.K) (φ : HahnSeries ℚ Ω) (b : ℕ)
    (h : IsDl X A l m s f φ) : IsDl X A l m s (X.sl (ofSL (ModularGroup.T ^ b)) f) (trT ε b φ) := by
  obtain ⟨hφ, a, c, κ, hκ, he, ha, hc, hcg⟩ := h
  refine ⟨fun r => mul_mem (eOm_mem A _) (hφ r), X.sl (ofSL (ModularGroup.T ^ b)) a,
    X.sl (ofSL (ModularGroup.T ^ b)) c, κ, hκ, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul (X.sl (ofSL (ModularGroup.T ^ b))) f c, he, map_mul, AlgEquiv.commutes]
  · rw [modularTowerExp_slAction_T_pow]; exact prim_trT A b ha
  · rw [modularTowerExp_slAction_T_pow]; exact prim_trT A b hc
  · intro r
    rw [modularTowerExp_slAction_T_pow, modularTowerExp_slAction_T_pow]
    simp only [theta_trT, ← trT_mul, ← trT_sub]
    simp only [trT_coeff]
    exact cgA_mul A l m (eOm_mem A _) (hcg r)

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[HahnSeries.coeff_sum, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, h', smul_eq_mul]`. Simplify using `only [trT_coeff, eOm_nat_mul]`. Rewrite using `[← Finset.sum_mul]`. Distinguish the cases in `h0 : φ.coeff r = 0`.

Simplify using `[h0]`. Use `split_ifs with hr`. Establish `: eOm ε r = 1` using `(KTExp.eOm_eq_one_iff ε r).2 hr`. Simplify using `[this]`. Establish `hz1 : eOm ε r ≠ 1` using `fun e => hr ((KTExp.eOm_eq_one_iff ε r).1 e)`.

Establish `hzL : eOm ε r ^ L = 1` using `by rw [← eOm_nat_mul]; exact (KTExp.eOm_eq_one_iff ε _).2 (hφ r h0)`. Establish `hs : ∑ i ∈ Finset.range L, eOm ε r ^ i = 0`. Use `geom_sum_mul (eOm ε r) L` as an intermediate fact. Rewrite `this` using `[hzL, sub_self]`. Conclude with `(mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hz1)`.

Rewrite using `[hs, zero_mul, mul_zero]`.
-/
theorem sum_trT (L : ℕ) (φ : HahnSeries ℚ Ω) (hφ : ∀ r, φ.coeff r ≠ 0 → (r * L).den = 1) (φ' : HahnSeries ℚ Ω)
    (h' : ∀ r : ℚ, φ'.coeff r = if r.den = 1 then φ.coeff r else 0) :
    ∑ b ∈ Finset.range L, trT ε b φ = HahnSeries.C (L : Ω) * φ' := by
  ext r
  rw [HahnSeries.coeff_sum, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, h', smul_eq_mul]
  simp only [trT_coeff, eOm_nat_mul]
  rw [← Finset.sum_mul]
  by_cases h0 : φ.coeff r = 0
  · simp [h0]
  · split_ifs with hr
    · have : eOm ε r = 1 := (KTExp.eOm_eq_one_iff ε r).2 hr
      simp [this]
    · have hz1 : eOm ε r ≠ 1 := fun e => hr ((KTExp.eOm_eq_one_iff ε r).1 e)
      have hzL : eOm ε r ^ L = 1 := by rw [← eOm_nat_mul]; exact (KTExp.eOm_eq_one_iff ε _).2 (hφ r h0)
      have hs : ∑ i ∈ Finset.range L, eOm ε r ^ i = 0 := by
        have := geom_sum_mul (eOm ε r) L
        rw [hzL, sub_self] at this
        exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hz1)
      rw [hs, zero_mul, mul_zero]

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]`. Use `show algebraMap ℚ Ω (s * r) * x.coeff r = algebraMap ℚ Ω s * (algebraMap ℚ Ω (1 * r) * x.coeff r)`. Rewrite using `[one_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_eq_C_mul (s : ℚ) (x : HahnSeries ℚ Ω) : theta s x = HahnSeries.C (algebraMap ℚ Ω s) * theta 1 x := by
  ext r
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  show algebraMap ℚ Ω (s * r) * x.coeff r = algebraMap ℚ Ω s * (algebraMap ℚ Ω (1 * r) * x.coeff r)
  rw [one_mul, map_mul]; ring

/- English proof (translation)
Rewrite using `[HahnSeries.coeff_mul]`. Apply `Finset.sum_induction _ (fun u => ∃ z ∈ A, u = t * z)` to reduce the goal to its premises. Introduce and unpack `u v ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩`. Conclude with `⟨z + z', add_mem hz hz', by ring⟩`. Conclude with `⟨0, zero_mem A, by ring⟩`.

Introduce `ij _`. Take `⟨z, hz, e⟩` from `hx ij.1`. Conclude with `⟨z * y.coeff ij.2, mul_mem hz (hy ij.2), by rw [e]; ring⟩`.
-/
theorem coeff_mul_mem (A : ValuationSubring Ω) (t : Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, ∃ z ∈ A, x.coeff r = t * z)
    (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) : ∃ z ∈ A, (x * y).coeff r = t * z := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_induction _ (fun u => ∃ z ∈ A, u = t * z)
  · rintro u v ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    exact ⟨z + z', add_mem hz hz', by ring⟩
  · exact ⟨0, zero_mem A, by ring⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hx ij.1
    exact ⟨z * y.coeff ij.2, mul_mem hz (hy ij.2), by rw [e]; ring⟩

/- English proof (translation)
Take `⟨z, hz, e⟩` from `coeff_mul_mem A 1 (fun r => ⟨x.coeff r, hx r, (one_mul _).symm⟩) hy r`. Rewrite using `[e, one_mul]`. Conclude with `hz`.
-/
theorem int_mul (A : ValuationSubring Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A) (hy : ∀ r, y.coeff r ∈ A)
    (r : ℚ) : (x * y).coeff r ∈ A := by
  obtain ⟨z, hz, e⟩ := coeff_mul_mem A 1 (fun r => ⟨x.coeff r, hx r, (one_mul _).symm⟩) hy r
  rw [e, one_mul]; exact hz

/- English proof (translation)
Take `⟨-, a, c, κ, hκ, he, ha, hc', hcg⟩` from `h`. Use `⟨hψ, a, c, κ, hκ, he, ha, hc', fun r => ?_⟩` and prove the remaining obligations. Establish `hy : ∀ r, (X.exp a * X.exp c).coeff r ∈ A` using `int_mul A ha.1 hc'.1`. Establish `hx : ∀ r, ∃ z ∈ A, (ψ - φ).coeff r = (l : Ω) ^ n * z` using `fun r => by`. Take `⟨z, hz, e⟩` from `hc r`.

Conclude with `⟨z, hz, by rw [HahnSeries.coeff_sub, e]⟩`. Take `⟨z1, hz1, e1⟩` from `coeff_mul_mem A _ hx hy r`. Take `⟨z2, hz2, e2⟩` from `hcg r`. Use `⟨z1 + z2, add_mem hz1 hz2, ?_⟩` and prove the remaining obligations. Establish `: ψ * X.exp a * X.exp c = (ψ - φ) * (X.exp a * X.exp c) + φ * X.exp a * X.exp c` using `by ring`.

Rewrite using `[this, HahnSeries.coeff_add, e1, mul_add, ← e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isDl_congr (X : Tower Ω ε) (A : ValuationSubring Ω) (l n : ℕ) (s : ℚ) (F : X.K) (φ ψ : HahnSeries ℚ Ω)
    (h : IsDl X A l n s F φ) (hψ : ∀ r, ψ.coeff r ∈ A) (hc : ∀ r, CgA A l n (ψ.coeff r) (φ.coeff r)) :
    IsDl X A l n s F ψ := by
  obtain ⟨-, a, c, κ, hκ, he, ha, hc', hcg⟩ := h
  refine ⟨hψ, a, c, κ, hκ, he, ha, hc', fun r => ?_⟩
  have hy : ∀ r, (X.exp a * X.exp c).coeff r ∈ A := int_mul A ha.1 hc'.1
  have hx : ∀ r, ∃ z ∈ A, (ψ - φ).coeff r = (l : Ω) ^ n * z := fun r => by
    obtain ⟨z, hz, e⟩ := hc r
    exact ⟨z, hz, by rw [HahnSeries.coeff_sub, e]⟩
  obtain ⟨z1, hz1, e1⟩ := coeff_mul_mem A _ hx hy r
  obtain ⟨z2, hz2, e2⟩ := hcg r
  refine ⟨z1 + z2, add_mem hz1 hz2, ?_⟩
  have : ψ * X.exp a * X.exp c = (ψ - φ) * (X.exp a * X.exp c) + φ * X.exp a * X.exp c := by ring
  rw [this, HahnSeries.coeff_add, e1, mul_add, ← e2]; ring

def resZ (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω where
  coeff r := if r.den = 1 then φ.coeff r else 0
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem resZ_coeff (φ : HahnSeries ℚ Ω) (r : ℚ) : (resZ φ).coeff r = if r.den = 1 then φ.coeff r else 0 := rfl

end GlobalTheory.Glue.NrmT
