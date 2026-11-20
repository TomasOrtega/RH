import Formalism.TorsionNormIteration.LTLemma
import Formalism.TorsionNormIteration.InverseIntegralClasses.InvInt
import Formalism.TorsionNormIteration.InverseIntegralClasses.MemSpanOfNormLe

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.LTL

open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP

section Near

variable {K : Type u} [NormedField K] {ι : Type*}

def Near (k : ℕ) (A B : MvPowerSeries ι K) : Prop := Low k A ∧ Low k B ∧ Low (k + 1) (A - B)

/- English proof (translation)
The claim follows from `hk ▸ h`.
-/
theorem Near.of_eq {k k' : ℕ} {A B : MvPowerSeries ι K} (h : Near k A B) (hk : k = k') :
    Near k' A B := hk ▸ h

/- English proof (translation)
Use `⟨h1.1.mul h2.1, h1.2.1.mul h2.2.1, ?_⟩` and prove the remaining obligations. Establish `e : A * C - B * D = (A - B) * C + B * (C - D)` using `by ring`. Rewrite using `[e]`. Conclude with `((h1.2.2.mul h2.1).mono (by omega)).add ((h1.2.1.mul h2.2.2).mono (by omega))`.
-/
theorem Near.mul {k l : ℕ} {A B C D : MvPowerSeries ι K} (h1 : Near k A B) (h2 : Near l C D) :
    Near (k + l) (A * C) (B * D) := by
  refine ⟨h1.1.mul h2.1, h1.2.1.mul h2.2.1, ?_⟩
  have e : A * C - B * D = (A - B) * C + B * (C - D) := by ring
  rw [e]
  exact ((h1.2.2.mul h2.1).mono (by omega)).add ((h1.2.1.mul h2.2.2).mono (by omega))

/- English proof (translation)
Assemble the required witnesses or components as `⟨low_zero _, low_zero _, fun d _ => by simp⟩`.
-/
theorem near_one : Near 0 (1 : MvPowerSeries ι K) 1 :=
  ⟨low_zero _, low_zero _, fun d _ => by simp⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using near_one`. Consider the case `succ n ih => rw [pow_succ, pow_succ]; exact (ih.mul h).of_eq (by ring)`.
-/
theorem Near.pow {k : ℕ} {A B : MvPowerSeries ι K} (h : Near k A B) (n : ℕ) :
    Near (k * n) (A ^ n) (B ^ n) := by
  induction n with
  | zero => simpa using near_one
  | succ n ih => rw [pow_succ, pow_succ]; exact (ih.mul h).of_eq (by ring)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using near_one`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]`. Conclude with `(((hab j).pow (m j)).mul ih).of_eq (by ring)`.
-/
theorem near_prod {τ : Type*} [DecidableEq ι] {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Near 1 (a i) (b i)) (m : ι → ℕ) (s : Finset ι) :
    Near (∑ i ∈ s, m i) (∏ i ∈ s, a i ^ m i) (∏ i ∈ s, b i ^ m i) := by
  induction s using Finset.induction_on with
  | empty => simpa using near_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    exact (((hab j).pow (m j)).mul ih).of_eq (by ring)

/- English proof (translation)
Rewrite using `[Finsupp.degree_apply]`. Conclude with `near_prod hab m m.support`.
-/
theorem near_monomial {τ : Type*} {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Near 1 (a i) (b i)) (m : ι →₀ ℕ) :
    Near m.degree (m.prod fun s e => a s ^ e) (m.prod fun s e => b s ^ e) := by
  classical
  rw [Finsupp.degree_apply]
  exact near_prod hab m m.support

/- English proof (translation)
Introduce `d hd`. Establish `ha' : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Establish `hb' : MvPowerSeries.HasSubst b` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hb`. Rewrite using `[map_sub, MvPowerSeries.coeff_subst ha', MvPowerSeries.coeff_subst hb', ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite ha' δ d) (MvPowerSeries.coeff_subst_finite hb' δ d)]`. Establish `: ∀ m : ι →₀ ℕ, MvPowerSeries.coeff m δ • MvPowerSeries.coeff d (m.prod fun s e => a s ^ e) - MvPowerSeries.coeff m δ • MvPowerSeries.coeff d (m.prod fun s e => b s ^ e) = 0`.

Introduce `m`. Rewrite using `[← smul_sub]`. Distinguish the cases in `hm : m.degree < N`. Rewrite using `[hδ m hm, zero_smul]`. Use `(near_monomial hab m).2.2 d (by omega)` as an intermediate fact.

Rewrite `this` using `[map_sub]`. Rewrite using `[this, smul_zero]`. Simplify using `only [this, finsum_zero]`.
-/
theorem low_subst_sub [Finite ι] {τ : Type*} {a b : ι → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (hab : ∀ i, Near 1 (a i) (b i)) {N : ℕ} {δ : MvPowerSeries ι K} (hδ : Low N δ) :
    Low (N + 1) (MvPowerSeries.subst a δ - MvPowerSeries.subst b δ) := by
  intro d hd
  have ha' : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hb' : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [map_sub, MvPowerSeries.coeff_subst ha', MvPowerSeries.coeff_subst hb',
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite ha' δ d)
      (MvPowerSeries.coeff_subst_finite hb' δ d)]
  have : ∀ m : ι →₀ ℕ, MvPowerSeries.coeff m δ •
      MvPowerSeries.coeff d (m.prod fun s e => a s ^ e) - MvPowerSeries.coeff m δ •
      MvPowerSeries.coeff d (m.prod fun s e => b s ^ e) = 0 := by
    intro m
    rw [← smul_sub]
    by_cases hm : m.degree < N
    · rw [hδ m hm, zero_smul]
    · have := (near_monomial hab m).2.2 d (by omega)
      rw [map_sub] at this
      rw [this, smul_zero]
  simp only [this, finsum_zero]

end Near

section Master

variable {K : Type u} [NormedField K] {ι : Type*}

/- English proof (translation)
Use extensionality with `n`. Break down `n with _ | _ | n` into its components or cases. Simplify using `[h0]`. Simplify using `[PowerSeries.coeff_X_pow_mul']`. Simplify using `[tail2, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X]`.
-/
theorem decomp' (f : PowerSeries K) (h0 : constantCoeff f = 0) :
    f = coeff 1 f • X + X ^ 2 * tail2 f := by
  ext n
  rcases n with _ | _ | n
  · simp [h0]
  · simp [PowerSeries.coeff_X_pow_mul']
  · simp [tail2, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X]

/- English proof (translation)
Establish `ha : PowerSeries.HasSubst a` using `PowerSeries.HasSubst.of_constantCoeff_zero ha0`. Use `conv_lhs => rw [decomp' f h0]`. Rewrite using `[PowerSeries.subst_add ha, PowerSeries.subst_smul ha, PowerSeries.subst_mul ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]`.
-/
theorem subst_eq' (f : PowerSeries K) (h0 : constantCoeff f = 0) {a : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) :
    f.subst a = coeff 1 f • a + a ^ 2 * (tail2 f).subst a := by
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  conv_lhs => rw [decomp' f h0]
  rw [PowerSeries.subst_add ha, PowerSeries.subst_smul ha, PowerSeries.subst_mul ha,
    PowerSeries.subst_pow ha, PowerSeries.subst_X ha]

/- English proof (translation)
Rewrite using `[subst_eq' f h0 ha0, subst_eq' f h0 hb0]`. Establish `e : coeff 1 f • a + a ^ 2 * (tail2 f).subst a - (coeff 1 f • b + b ^ 2 * (tail2 f).subst b) - coeff 1 f • (a - b) = a ^ 2 * ((tail2 f).subst a - (tail2 f).subst b) + (a - b) * (a + b) * (tail2 f).subst b`. Rewrite using `[smul_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `Low.add ?_ ?_` and prove the remaining obligations. Establish `h2 : Low 2 (a ^ 2)`. Rewrite using `[pow_two]`. Conclude with `(low_one ha0).mul (low_one ha0)`. Conclude with `(h2.mul (low_of_agree (agree_psubst _ ha0 hb0 hab))).mono (by omega)`.

Establish `hs : Low 1 (a + b)` using `(low_one ha0).add (low_one hb0)`. Simplify using `using ((low_of_agree hab).mul hs).mul (low_zero ((tail2 f).subst b))`.
-/
theorem key' [Finite ι] (f : PowerSeries K) (h0 : constantCoeff f = 0)
    {N : ℕ} {a b : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (hab : Agree N a b) : Low (N + 1) (f.subst a - f.subst b - coeff 1 f • (a - b)) := by
  rw [subst_eq' f h0 ha0, subst_eq' f h0 hb0]
  have e : coeff 1 f • a + a ^ 2 * (tail2 f).subst a - (coeff 1 f • b + b ^ 2 * (tail2 f).subst b)
      - coeff 1 f • (a - b) =
      a ^ 2 * ((tail2 f).subst a - (tail2 f).subst b) + (a - b) * (a + b) * (tail2 f).subst b := by
    rw [smul_sub]; ring
  rw [e]
  refine Low.add ?_ ?_
  · have h2 : Low 2 (a ^ 2) := by
      rw [pow_two]; exact (low_one ha0).mul (low_one ha0)
    exact (h2.mul (low_of_agree (agree_psubst _ ha0 hb0 hab))).mono (by omega)
  · have hs : Low 1 (a + b) := (low_one ha0).add (low_one hb0)
    simpa using ((low_of_agree hab).mul hs).mul (low_zero ((tail2 f).subst b))

/- English proof (translation)
Establish `hX : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι K) = 0` using `by simp`. Rewrite using `[subst_eq' f h0 hX]`. Simplify using `only [Pi.smul_apply']`. Establish `hl : Low 1 (coeff 1 f • (MvPowerSeries.X i : MvPowerSeries ι K))` using `low_one (by simp)`. Use `⟨?_, hl, ?_⟩` and prove the remaining obligations.

Use `hl.add ?_` and prove the remaining obligations. Use `((low_one hX).mul (low_one hX)).mul (low_zero ((tail2 f).subst (MvPowerSeries.X i : MvPowerSeries ι K)))` as an intermediate fact. Rewrite `this` using `[← pow_two]`. Conclude with `this.mono (by omega)`. Rewrite using `[add_sub_cancel_left]`.

Use `((low_one hX).mul (low_one hX)).mul (low_zero ((tail2 f).subst (MvPowerSeries.X i : MvPowerSeries ι K)))` as an intermediate fact. Rewrite `this` using `[← pow_two]`. Conclude with `this`.
-/
theorem near_one_subst_X_coeff_one_smul_X (f : PowerSeries K) (h0 : constantCoeff f = 0) (i : ι) :
    Near 1 (f.subst (MvPowerSeries.X i : MvPowerSeries ι K))
      (((fun _ : ι => coeff 1 f) • (MvPowerSeries.X : ι → MvPowerSeries ι K)) i) := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι K) = 0 := by simp
  rw [subst_eq' f h0 hX]
  simp only [Pi.smul_apply']
  have hl : Low 1 (coeff 1 f • (MvPowerSeries.X i : MvPowerSeries ι K)) := low_one (by simp)
  refine ⟨?_, hl, ?_⟩
  · refine hl.add ?_
    have := ((low_one hX).mul (low_one hX)).mul (low_zero ((tail2 f).subst (MvPowerSeries.X i : MvPowerSeries ι K)))
    rw [← pow_two] at this
    exact this.mono (by omega)
  · rw [add_sub_cancel_left]
    have := ((low_one hX).mul (low_one hX)).mul (low_zero ((tail2 f).subst (MvPowerSeries.X i : MvPowerSeries ι K)))
    rw [← pow_two] at this
    exact this

/- English proof (translation)
Rewrite using `[Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]`.
-/
theorem prod_const_pow (c : K) (d : ι →₀ ℕ) : (d.prod fun _ m => c ^ m) = c ^ d.degree := by
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

def Ep (e' : PowerSeries K) (x : MvPowerSeries ι K) : MvPowerSeries ι K :=
  MvPowerSeries.subst (fun i => e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) x

def Ldef (e e' : PowerSeries K) (x : MvPowerSeries ι K) : MvPowerSeries ι K :=
  Ep e' x - e.subst x

/- English proof (translation)
The claim follows from `PowerSeries.constantCoeff_subst_eq_zero (by simp) _ h0`.
-/
theorem inverseIntegralClasses_cc_s_fact (e' : PowerSeries K) (h0 : constantCoeff e' = 0) (i : ι) :
    MvPowerSeries.constantCoeff (e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) _ h0

/- English proof (translation)
Unfold `Ep`. Rewrite using `[MvPowerSeries.subst_sub (MvPowerSeries.hasSubst_of_constantCoeff_zero (inverseIntegralClasses_cc_s_fact e' h0))]`.
-/
theorem Ep_sub [Finite ι] (e' : PowerSeries K) (h0 : constantCoeff e' = 0)
    (x y : MvPowerSeries ι K) : Ep e' x - Ep e' y = Ep e' (x - y) := by
  unfold Ep
  rw [MvPowerSeries.subst_sub (MvPowerSeries.hasSubst_of_constantCoeff_zero (inverseIntegralClasses_cc_s_fact e' h0))]

/- English proof (translation)
Establish `hag : Agree N ψ φ` using `fun d hd => by`. Use `hN d hd` as an intermediate fact. Rewrite `this` using `[map_sub]`. Conclude with `sub_eq_zero.mp this`. Establish `h1` using `key' e he0 hψ hφ hag d (by omega)`.

Rewrite `h1` using `[he1]`. Simplify using `only [map_sub, MvPowerSeries.coeff_smul] at h1`. Establish `h2` using `low_subst_sub (inverseIntegralClasses_cc_s_fact e' he'0) (fun i => by simp) (fun i => near_one_subst_X_coeff_one_smul_X e' he'0 i) hN d (by omega)`. Rewrite `h2` using `[he'1, ← MvPowerSeries.rescale_eq_subst, map_sub, MvPowerSeries.coeff_rescale, prod_const_pow]`. Establish `h3 : MvPowerSeries.coeff d (Ep e' ψ) - MvPowerSeries.coeff d (Ep e' φ) = MvPowerSeries.coeff d (MvPowerSeries.subst (fun i => e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) (ψ - φ))`.

Rewrite using `[← map_sub, Ep_sub e' he'0]`. Both sides reduce to the same expression. Establish `h4 : π ^ d.degree * MvPowerSeries.coeff d (ψ - φ) = π ^ N * MvPowerSeries.coeff d (ψ - φ)`. Break down `lt_or_eq_of_le hd with hlt | heq` into its components or cases. Rewrite using `[hN d hlt, mul_zero, mul_zero]`.

Rewrite using `[heq]`. Unfold `Ldef`. Simplify using `only [map_sub] at h2 h4 ⊢`. Take the linear combination `h3 + h2 + h4 - h1`.
-/
theorem master [Finite ι] (e e' : PowerSeries K) (he0 : constantCoeff e = 0)
    (he'0 : constantCoeff e' = 0) (π : K) (he1 : coeff 1 e = π) (he'1 : coeff 1 e' = π)
    {N : ℕ} {ψ φ : MvPowerSeries ι K} (hψ : MvPowerSeries.constantCoeff ψ = 0)
    (hφ : MvPowerSeries.constantCoeff φ = 0) (hN : Low N (ψ - φ)) (d : ι →₀ ℕ)
    (hd : d.degree ≤ N) :
    MvPowerSeries.coeff d (Ldef e e' ψ) - MvPowerSeries.coeff d (Ldef e e' φ) =
      (π ^ N - π) * MvPowerSeries.coeff d (ψ - φ) := by
  have hag : Agree N ψ φ := fun d hd => by
    have := hN d hd; rw [map_sub] at this; exact sub_eq_zero.mp this
  have h1 := key' e he0 hψ hφ hag d (by omega)
  rw [he1] at h1
  simp only [map_sub, MvPowerSeries.coeff_smul] at h1
  have h2 := low_subst_sub (inverseIntegralClasses_cc_s_fact e' he'0) (fun i => by simp)
    (fun i => near_one_subst_X_coeff_one_smul_X e' he'0 i) hN d (by omega)
  rw [he'1, ← MvPowerSeries.rescale_eq_subst, map_sub, MvPowerSeries.coeff_rescale,
    prod_const_pow] at h2
  have h3 : MvPowerSeries.coeff d (Ep e' ψ) - MvPowerSeries.coeff d (Ep e' φ) =
      MvPowerSeries.coeff d (MvPowerSeries.subst
        (fun i => e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) (ψ - φ)) := by
    rw [← map_sub, Ep_sub e' he'0]; rfl
  have h4 : π ^ d.degree * MvPowerSeries.coeff d (ψ - φ) =
      π ^ N * MvPowerSeries.coeff d (ψ - φ) := by
    rcases lt_or_eq_of_le hd with hlt | heq
    · rw [hN d hlt, mul_zero, mul_zero]
    · rw [heq]
  unfold Ldef
  simp only [map_sub] at h2 h4 ⊢
  linear_combination h3 + h2 + h4 - h1

end Master

section Cong

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

/- English proof (translation)
Distinguish the cases in `hfin : (Function.support g).Finite`. Rewrite using `[finsum_eq_sum g hfin]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)`. Rewrite using `[finsum_of_infinite_support hfin]`. Simplify using `using hC`.
-/
lemma norm_finsum_le' {α : Type*} {g : α → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support hfin]
    simpa using hC

/- English proof (translation)
Introduce `d` and use `by rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA d) (hB d))`.
-/
theorem dv_add {c : K} {A B : MvPowerSeries ι K} (hA : DivByMv c A) (hB : DivByMv c B) :
    DivByMv c (A + B) := fun d => by
  rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA d) (hB d))

/- English proof (translation)
Introduce `d` and use `by rw [map_neg, norm_neg]; exact hA d`.
-/
theorem dv_neg {c : K} {A : MvPowerSeries ι K} (hA : DivByMv c A) :
    DivByMv c (-A) := fun d => by rw [map_neg, norm_neg]; exact hA d

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `dv_add hA (dv_neg hB)`.
-/
theorem dv_sub {c : K} {A B : MvPowerSeries ι K} (hA : DivByMv c A) (hB : DivByMv c B) :
    DivByMv c (A - B) := by rw [sub_eq_add_neg]; exact dv_add hA (dv_neg hB)

/- English proof (translation)
Introduce `d`. Rewrite using `[MvPowerSeries.coeff_mul]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun p _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dv_mul {c : K} {A B : MvPowerSeries ι K} (hA : DivByMv c A) (hB : IntegralMv B) :
    DivByMv c (A * B) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun p _ => ?_
  rw [norm_mul]
  calc ‖MvPowerSeries.coeff p.1 A‖ * ‖MvPowerSeries.coeff p.2 B‖ ≤ ‖c‖ * 1 :=
        mul_le_mul (hA _) (hB _) (norm_nonneg _) (norm_nonneg _)
    _ = ‖c‖ := mul_one _

def Cong (c : K) (A B : MvPowerSeries ι K) : Prop :=
  IntegralMv A ∧ IntegralMv B ∧ DivByMv c (A - B)

/- English proof (translation)
Use `⟨integral_mul h1.1 h2.1, integral_mul h1.2.1 h2.2.1, ?_⟩` and prove the remaining obligations. Establish `e : A * C - B * D = (A - B) * C + (C - D) * B` using `by ring`. Rewrite using `[e]`. Conclude with `dv_add (dv_mul h1.2.2 h2.1) (dv_mul h2.2.2 h1.2.1)`.
-/
theorem Cong.mul {c : K} {A B C D : MvPowerSeries ι K} (h1 : Cong c A B) (h2 : Cong c C D) :
    Cong c (A * C) (B * D) := by
  refine ⟨integral_mul h1.1 h2.1, integral_mul h1.2.1 h2.2.1, ?_⟩
  have e : A * C - B * D = (A - B) * C + (C - D) * B := by ring
  rw [e]
  exact dv_add (dv_mul h1.2.2 h2.1) (dv_mul h2.2.2 h1.2.1)

/- English proof (translation)
Assemble the required witnesses or components as `⟨integral_one, integral_one, fun d => by simp⟩`.
-/
theorem cong_one (c : K) : Cong c (1 : MvPowerSeries ι K) 1 :=
  ⟨integral_one, integral_one, fun d => by simp⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using cong_one c`. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `ih.mul h`.
-/
theorem Cong.pow {c : K} {A B : MvPowerSeries ι K} (h : Cong c A B) (n : ℕ) :
    Cong c (A ^ n) (B ^ n) := by
  induction n with
  | zero => simpa using cong_one c
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

/- English proof (translation)
Unfold `Finsupp.prod`. Proceed by induction on `m.support using Finset.induction_on with`. Consider the case `empty => simpa using cong_one c`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.prod_insert hj]`.

Conclude with `((hab j).pow (m j)).mul ih`.
-/
theorem cong_monomial {τ : Type*} {c : K} {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Cong c (a i) (b i)) (m : ι →₀ ℕ) :
    Cong c (m.prod fun s e => a s ^ e) (m.prod fun s e => b s ^ e) := by
  classical
  unfold Finsupp.prod
  induction m.support using Finset.induction_on with
  | empty => simpa using cong_one c
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact ((hab j).pow (m j)).mul ih

/- English proof (translation)
Introduce `d`. Establish `ha' : MvPowerSeries.HasSubst a` using `MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Establish `hb' : MvPowerSeries.HasSubst b` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hb`. Rewrite using `[map_sub, MvPowerSeries.coeff_subst ha', MvPowerSeries.coeff_subst hb', ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite ha' δ d) (MvPowerSeries.coeff_subst_finite hb' δ d)]`. Use `norm_finsum_le' (norm_nonneg _) fun m => ?_` and prove the remaining obligations.

Rewrite using `[← smul_sub, smul_eq_mul, norm_mul, ← map_sub]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem divBy_subst_sub [Finite ι] {τ : Type*} {c : K} {a b : ι → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (hab : ∀ i, Cong c (a i) (b i)) {δ : MvPowerSeries ι K} (hδ : IntegralMv δ) :
    DivByMv c (MvPowerSeries.subst a δ - MvPowerSeries.subst b δ) := by
  intro d
  have ha' : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hb' : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [map_sub, MvPowerSeries.coeff_subst ha', MvPowerSeries.coeff_subst hb',
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite ha' δ d)
      (MvPowerSeries.coeff_subst_finite hb' δ d)]
  refine norm_finsum_le' (norm_nonneg _) fun m => ?_
  rw [← smul_sub, smul_eq_mul, norm_mul, ← map_sub]
  calc _ ≤ 1 * ‖c‖ := mul_le_mul (hδ m) ((cong_monomial hab m).2.2 d) (norm_nonneg _) zero_le_one
    _ = ‖c‖ := one_mul _

/- English proof (translation)
Introduce `d`. Establish `ha : PowerSeries.HasSubst P` using `PowerSeries.HasSubst.of_constantCoeff_zero hP0`. Rewrite using `[PowerSeries.coeff_subst ha f d]`. Use `norm_finsum_le' (norm_nonneg _) fun n => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, norm_mul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem divBy_psubst (c : K) (f : PowerSeries K) (P : MvPowerSeries ι K)
    (hf : DivBy c f) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv c (f.subst P) := by
  intro d
  have ha : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.coeff_subst ha f d]
  refine norm_finsum_le' (norm_nonneg _) fun n => ?_
  rw [smul_eq_mul, norm_mul]
  calc _ ≤ ‖c‖ * 1 := mul_le_mul (hf n) (integral_pow hP n d) (norm_nonneg _) (norm_nonneg _)
    _ = ‖c‖ := mul_one _

end Cong

section FrobPi

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

def piO (π : K) (hπ : ‖π‖ ≤ 1) : unitBall K := ⟨π, hπ⟩

/- English proof (translation)
Rewrite `hx` using `[Ideal.mem_span_singleton']`. Take `⟨c, rfl⟩` from `hx`. Establish `hc : ‖(c : K)‖ ≤ 1` using `c.2`. Rewrite using `[Subring.coe_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_le_of_mem_span' {π : K} (hπ : ‖π‖ ≤ 1) (x : unitBall K)
    (hx : x ∈ Ideal.span {piO π hπ}) : ‖(x : K)‖ ≤ ‖π‖ := by
  rw [Ideal.mem_span_singleton'] at hx
  obtain ⟨c, rfl⟩ := hx
  have hc : ‖(c : K)‖ ≤ 1 := c.2
  rw [Subring.coe_mul, norm_mul]
  calc ‖(c : K)‖ * ‖π‖ ≤ 1 * ‖π‖ := by gcongr
    _ = ‖π‖ := one_mul _

/- English proof (translation)
Rewrite using `[Ideal.mem_span_singleton']`. Establish `hc : ‖(x : K) / π‖ ≤ 1`. Rewrite using `[norm_div]`. Conclude with `div_le_one_of_le₀ hx (norm_nonneg _)`. Use `⟨⟨(x : K) / π, hc⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subring.coe_mul]`. Express the relevant statement in the definitionally equal form `(x : K) / π * π = x`. Clear the denominators using the available nonvanishing facts.
-/
theorem mem_span_of_norm_le' {π : K} (hπ : ‖π‖ ≤ 1) (hπ0 : π ≠ 0) (x : unitBall K)
    (hx : ‖(x : K)‖ ≤ ‖π‖) : x ∈ Ideal.span {piO π hπ} := by
  rw [Ideal.mem_span_singleton']
  have hc : ‖(x : K) / π‖ ≤ 1 := by
    rw [norm_div]
    exact div_le_one_of_le₀ hx (norm_nonneg _)
  refine ⟨⟨(x : K) / π, hc⟩, ?_⟩
  apply Subtype.ext
  rw [Subring.coe_mul]
  change (x : K) / π * π = x
  field_simp

/- English proof (translation)
Use `Fact.mk hpr` as an intermediate fact. Establish `hπ : ‖π‖ ≤ 1` using `hπ1.le`. Establish `hπne : π ≠ 0` using `norm_pos_iff.mp hπ0`. Use `set O := unitBall K`. Use `set I : Ideal O := Ideal.span {piO π hπ}`.

Establish `hI : I ≠ ⊤`. Introduce `htop`. Establish `h1 : (1 : O) ∈ I` using `htop ▸ Submodule.mem_top`. Use `norm_le_of_mem_span' hπ 1 h1` as an intermediate fact. Simplify using `at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: Nontrivial (O ⧸ I)` using `Ideal.Quotient.nontrivial_iff.mpr hI`. Establish `hpI : ((p : ℕ) : O ⧸ I) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]`. Apply `mem_span_of_norm_le' hπ hπne` to reduce the goal to its premises.

Simplify using `using hp`. Establish `: CharP (O ⧸ I) p` using `(CharP.charP_iff_prime_eq_zero hpr).mpr hpI`. Establish `: ExpChar (O ⧸ I) p` using `ExpChar.prime hpr`. Use `set mk := Ideal.Quotient.mk I`. Use `set A' := Formalism.LT.FrobP.liftO A hA`.

Use `set B' : MvPowerSeries ι O := A' ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) A'`. Establish `hB : A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) A = MvPowerSeries.map O.subtype B'`. Simplify using `only [B', map_sub, map_pow, MvPowerSeries.map_expand]`. Rewrite using `[show MvPowerSeries.map O.subtype A' = A from Formalism.LT.FrobP.map_liftO A hA]`. Establish `hcomp : (iterateFrobenius (O ⧸ I) p h).comp mk = mk`.

Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, iterateFrobenius_def, ← map_pow]`. Rewrite using `[Ideal.Quotient.eq]`. Apply `mem_span_of_norm_le' hπ hπne` to reduce the goal to its premises. Conclude with `hF a.1 a.2`.

Establish `hzero : MvPowerSeries.map mk B' = 0`. Simplify using `only [B', map_sub, map_pow, MvPowerSeries.map_expand]`. Rewrite using `[← MvPowerSeries.map_iterateFrobenius_expand _ hpr.ne_zero, ← MvPowerSeries.map_expand, MvPowerSeries.map_map, hcomp, sub_self]`. Introduce `d`. Rewrite using `[hB, MvPowerSeries.coeff_map]`.

Apply `norm_le_of_mem_span' hπ` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Use `congrArg (MvPowerSeries.coeff d) hzero` as an intermediate fact. Simplify `this` using `[MvPowerSeries.coeff_map]`.
-/
theorem frob_pi {ι : Type*} (p h : ℕ) (hpr : p.Prime) (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hp : ‖(p : K)‖ ≤ ‖π‖) (hF : ∀ a : K, ‖a‖ ≤ 1 → ‖a ^ (p ^ h) - a‖ ≤ ‖π‖)
    (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    DivByMv π (A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) A) := by
  have := Fact.mk hpr
  have hπ : ‖π‖ ≤ 1 := hπ1.le
  have hπne : π ≠ 0 := norm_pos_iff.mp hπ0
  set O := unitBall K
  set I : Ideal O := Ideal.span {piO π hπ}
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : O) ∈ I := htop ▸ Submodule.mem_top
    have := norm_le_of_mem_span' hπ 1 h1
    simp at this
    linarith
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hpI : ((p : ℕ) : O ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    apply mem_span_of_norm_le' hπ hπne
    simpa using hp
  have : CharP (O ⧸ I) p := (CharP.charP_iff_prime_eq_zero hpr).mpr hpI
  have : ExpChar (O ⧸ I) p := ExpChar.prime hpr
  set mk := Ideal.Quotient.mk I
  set A' := Formalism.LT.FrobP.liftO A hA
  set B' : MvPowerSeries ι O := A' ^ (p ^ h) - MvPowerSeries.expand (p ^ h)
    (pow_ne_zero h hpr.ne_zero) A'
  have hB : A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) A =
      MvPowerSeries.map O.subtype B' := by
    simp only [B', map_sub, map_pow, MvPowerSeries.map_expand]
    rw [show MvPowerSeries.map O.subtype A' = A from Formalism.LT.FrobP.map_liftO A hA]
  have hcomp : (iterateFrobenius (O ⧸ I) p h).comp mk = mk := by
    ext a
    simp only [RingHom.comp_apply, iterateFrobenius_def, ← map_pow]
    rw [Ideal.Quotient.eq]
    apply mem_span_of_norm_le' hπ hπne
    exact hF a.1 a.2
  have hzero : MvPowerSeries.map mk B' = 0 := by
    simp only [B', map_sub, map_pow, MvPowerSeries.map_expand]
    rw [← MvPowerSeries.map_iterateFrobenius_expand _ hpr.ne_zero, ← MvPowerSeries.map_expand,
      MvPowerSeries.map_map, hcomp, sub_self]
  intro d
  rw [hB, MvPowerSeries.coeff_map]
  apply norm_le_of_mem_span' hπ
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have := congrArg (MvPowerSeries.coeff d) hzero
  simpa [MvPowerSeries.coeff_map] using this

end FrobPi

section Defect

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

/- English proof (translation)
Introduce `d`. Rewrite using `[MvPowerSeries.coeff_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem integralMv_X' (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨hpr, ⟨h, hh, rfl⟩, hπ0, hπ1, hp, hF⟩` from `hS`. Establish `hq : p ^ h ≠ 0` using `pow_ne_zero h hpr.ne_zero`. Establish `ha : PowerSeries.HasSubst P` using `PowerSeries.HasSubst.of_constantCoeff_zero hP0`. Establish `h1 : DivByMv π (e.subst P - P ^ (p ^ h))`. Use `divBy_psubst π (e - X ^ (p ^ h)) P he.2.2.2 hP0 hP` as an intermediate fact.

Rewrite `this` using `[PowerSeries.subst_sub ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]`. Then use the resulting hypothesis. Establish `h2` using `frob_pi p h hpr π hπ0 hπ1 hp hF P hP`. Establish `hXq : ∀ i : ι, MvPowerSeries.constantCoeff ((MvPowerSeries.X i : MvPowerSeries ι K) ^ (p ^ h)) = 0` using `fun i => by`. Rewrite using `[map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]`. Establish `hcong : ∀ i : ι, Cong π (e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) ((MvPowerSeries.X i : MvPowerSeries ι K) ^ (p ^ h))`.

Introduce `i`. Establish `hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι K) = 0` using `by simp`. Establish `hXs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries ι K)` using `PowerSeries.HasSubst.of_constantCoeff_zero hX0`. Use `⟨integralSubst e' _ he'.1 hX0 (integralMv_X' i), integral_pow (integralMv_X' i) _, ?_⟩` and prove the remaining obligations. Use `divBy_psubst π (e' - X ^ (p ^ h)) (MvPowerSeries.X i : MvPowerSeries ι K) he'.2.2.2 hX0 (integralMv_X' i)` as an intermediate fact.

Rewrite `this` using `[PowerSeries.subst_sub hXs, PowerSeries.subst_pow hXs, PowerSeries.subst_X hXs]`. Then use the resulting hypothesis. Establish `h3 : DivByMv π (Ep e' P - MvPowerSeries.expand (p ^ h) hq P)`. Use `divBy_subst_sub (inverseIntegralClasses_cc_s_fact e' he'.2.1) hXq hcong hP` as an intermediate fact. Rewrite using `[MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]` and apply the resulting hypothesis. Establish `e4 : Ldef e e' P = (Ep e' P - MvPowerSeries.expand (p ^ h) hq P) - (P ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq P) - (e.subst P - P ^ (p ^ h))`.

Unfold `Ldef`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e4]`. Conclude with `dv_sub (dv_sub h3 h2) h1`.
-/
theorem defect_divBy [Finite ι] {p q : ℕ} {π : K} (hS : LTSetting K p q π)
    {e e' : PowerSeries K} (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    {P : MvPowerSeries ι K} (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv π (Ldef e e' P) := by
  obtain ⟨hpr, ⟨h, hh, rfl⟩, hπ0, hπ1, hp, hF⟩ := hS
  have hq : p ^ h ≠ 0 := pow_ne_zero h hpr.ne_zero
  have ha : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0

  have h1 : DivByMv π (e.subst P - P ^ (p ^ h)) := by
    have := divBy_psubst π (e - X ^ (p ^ h)) P he.2.2.2 hP0 hP
    rwa [PowerSeries.subst_sub ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha] at this
  have h2 := frob_pi p h hpr π hπ0 hπ1 hp hF P hP
  have hXq : ∀ i : ι, MvPowerSeries.constantCoeff
      ((MvPowerSeries.X i : MvPowerSeries ι K) ^ (p ^ h)) = 0 := fun i => by
    rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]
  have hcong : ∀ i : ι, Cong π (e'.subst (MvPowerSeries.X i : MvPowerSeries ι K))
      ((MvPowerSeries.X i : MvPowerSeries ι K) ^ (p ^ h)) := by
    intro i
    have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι K) = 0 := by simp
    have hXs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries ι K) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hX0
    refine ⟨integralSubst e' _ he'.1 hX0 (integralMv_X' i), integral_pow (integralMv_X' i) _, ?_⟩
    have := divBy_psubst π (e' - X ^ (p ^ h)) (MvPowerSeries.X i : MvPowerSeries ι K) he'.2.2.2
      hX0 (integralMv_X' i)
    rwa [PowerSeries.subst_sub hXs, PowerSeries.subst_pow hXs, PowerSeries.subst_X hXs] at this
  have h3 : DivByMv π (Ep e' P - MvPowerSeries.expand (p ^ h) hq P) := by
    have := divBy_subst_sub (inverseIntegralClasses_cc_s_fact e' he'.2.1) hXq hcong hP
    rwa [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]
  have e4 : Ldef e e' P = (Ep e' P - MvPowerSeries.expand (p ^ h) hq P) -
      (P ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq P) - (e.subst P - P ^ (p ^ h)) := by
    unfold Ldef; ring
  rw [e4]
  exact dv_sub (dv_sub h3 h2) h1

/- English proof (translation)
Establish `hlt : ‖π ^ r‖ < ‖π‖`. Rewrite using `[norm_pow]; exact pow_lt_self_of_lt_one₀ hπ0 hπ1 (by omega)`. Apply `le_antisymm` to reduce the goal to its premises. Use `IsUltrametricDist.norm_add_le_max π (-(π ^ r))` as an intermediate fact. Rewrite `this` using `[← sub_eq_add_neg, norm_neg]`.

Conclude with `this.trans (max_le le_rfl hlt.le)`. Use `IsUltrametricDist.norm_add_le_max (π - π ^ r) (π ^ r)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Break down `le_max_iff.mp this with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd h (not_le.mpr hlt)`.
-/
theorem norm_pi_sub_pow {π : K} (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) {r : ℕ} (hr : 2 ≤ r) :
    ‖π - π ^ r‖ = ‖π‖ := by
  have hlt : ‖π ^ r‖ < ‖π‖ := by
    rw [norm_pow]; exact pow_lt_self_of_lt_one₀ hπ0 hπ1 (by omega)
  apply le_antisymm
  · have := IsUltrametricDist.norm_add_le_max π (-(π ^ r))
    rw [← sub_eq_add_neg, norm_neg] at this
    exact this.trans (max_le le_rfl hlt.le)
  · have := IsUltrametricDist.norm_add_le_max (π - π ^ r) (π ^ r)
    rw [sub_add_cancel] at this
    rcases le_max_iff.mp this with h | h
    · exact h
    · exact absurd h (not_le.mpr hlt)

end Defect

section Constr

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

/- English proof (translation)
Use `Ep_sub e' he'0 (0 : MvPowerSeries ι K) 0` as an intermediate fact. Rewrite `this` using `[sub_self, sub_self]`. Conclude with `this.symm`.
-/
theorem Ep_zero [Finite ι] (e' : PowerSeries K) (he'0 : constantCoeff e' = 0) :
    Ep e' (0 : MvPowerSeries ι K) = 0 := by
  have := Ep_sub e' he'0 (0 : MvPowerSeries ι K) 0
  rw [sub_self, sub_self] at this
  exact this.symm

/- English proof (translation)
Unfold `Ldef`. Rewrite using `[Ep_zero e' he'0, PowerSeries.subst_zero_of_constantCoeff_zero he0, sub_zero]`.
-/
theorem Ldef_zero [Finite ι] (e e' : PowerSeries K) (he0 : constantCoeff e = 0)
    (he'0 : constantCoeff e' = 0) : Ldef e e' (0 : MvPowerSeries ι K) = 0 := by
  unfold Ldef
  rw [Ep_zero e' he'0, PowerSeries.subst_zero_of_constantCoeff_zero he0, sub_zero]

variable [Fintype ι] [DecidableEq ι]

def lin (a : ι → K) : MvPowerSeries ι K := ∑ i, a i • MvPowerSeries.X i

/- English proof (translation)
Simplify using `[lin]`.
-/
theorem cc_lin (a : ι → K) : MvPowerSeries.constantCoeff (lin a) = 0 := by
  simp [lin]

/- English proof (translation)
Simplify using `only [lin, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_X]`.
-/
theorem coeff_lin (a : ι → K) (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (lin a) = ∑ i, a i * (if d = Finsupp.single i 1 then 1 else 0) := by
  simp only [lin, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_X]

/- English proof (translation)
Rewrite using `[coeff_lin]`. Simplify using `[Finsupp.single_left_inj one_ne_zero]`.
-/
theorem coeff_lin_single (a : ι → K) (i : ι) :
    MvPowerSeries.coeff (Finsupp.single i 1) (lin a) = a i := by
  rw [coeff_lin]
  simp [Finsupp.single_left_inj one_ne_zero]

/- English proof (translation)
Introduce `d`. Rewrite using `[coeff_lin]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Apply the tactic sequence `split_ifs <;> simp [ha i]`.
-/
theorem integral_lin (a : ι → K) (ha : ∀ i, ‖a i‖ ≤ 1) : IntegralMv (lin a) := by
  intro d
  rw [coeff_lin]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul]
  split_ifs <;> simp [ha i]

def corr (e e' : PowerSeries K) (π : K) (N : ℕ) (P : MvPowerSeries ι K) : MvPowerSeries ι K :=
  fun d => if d.degree = N + 1 then MvPowerSeries.coeff d (Ldef e e' P) / (π - π ^ (N + 1)) else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_corr (e e' : PowerSeries K) (π : K) (N : ℕ) (P : MvPowerSeries ι K)
    (d : ι →₀ ℕ) : MvPowerSeries.coeff d (corr e e' π N P) =
      if d.degree = N + 1 then MvPowerSeries.coeff d (Ldef e e' P) / (π - π ^ (N + 1)) else 0 :=
  rfl

def seq (e e' : PowerSeries K) (π : K) (a : ι → K) : ℕ → MvPowerSeries ι K
  | 0 => 0
  | 1 => lin a
  | (N + 2) => seq e e' π a (N + 1) + corr e e' π (N + 1) (seq e e' π a (N + 1))

def Inv (e e' : PowerSeries K) (a : ι → K) (k : ℕ) (P : MvPowerSeries ι K) : Prop :=
  MvPowerSeries.constantCoeff P = 0 ∧ IntegralMv P ∧
    (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) P = a i) ∧ Low (k + 1) (Ldef e e' P)

variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}

/- English proof (translation)
Establish `hπ0 : 0 < ‖π‖` using `hS.2.2.1`. Establish `hπ1 : ‖π‖ < 1` using `hS.2.2.2.1`. Establish `hnorm` using `norm_pi_sub_pow hπ0 hπ1 (r := N + 1) (by omega)`. Establish `hne : π - π ^ (N + 1) ≠ 0`. Introduce `h0`.

Rewrite `hnorm` using `[h0, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlowc : Low (N + 1) (corr e e' π N P)`. Introduce `d hd; rw [coeff_corr, if_neg (by omega)]`. Use `⟨⟨?_, ?_, ?_, ?_⟩, hlowc⟩` and prove the remaining obligations.

Rewrite using `[map_add, h.1, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlowc 0 (by simp), add_zero]`. Introduce `d`. Rewrite using `[map_add]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.2.1 d) ?_)` and prove the remaining obligations. Rewrite using `[coeff_corr]`.

Use `split_ifs`. Rewrite using `[norm_div, hnorm]`. Conclude with `div_le_one_of_le₀ (defect_divBy hS he he' h.1 h.2.1 d) (norm_nonneg _)`. Simplify using the standard rewrite rules. Introduce `i`.

Rewrite using `[map_add, h.2.2.1 i, hlowc _ (by rw [Finsupp.degree_single]; omega), add_zero]`. Establish `hP'0 : MvPowerSeries.constantCoeff (P + corr e e' π N P) = 0`. Rewrite using `[map_add, h.1, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlowc 0 (by simp), add_zero]`. Establish `hdiff : Low (N + 1) (P + corr e e' π N P - P)`. Rewrite using `[add_sub_cancel_left]`.

Conclude with `hlowc`. Introduce `d hd`. Establish `hm` using `master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 hP'0 h.1 hdiff d (by omega)`. Rewrite `hm` using `[add_sub_cancel_left, coeff_corr]`. Break down `lt_or_eq_of_le (Nat.lt_succ_iff.mp hd) with hlt | heq` into its components or cases.

Rewrite `hm` using `[if_neg (by omega), mul_zero, h.2.2.2 d hlt, sub_zero]`. Conclude with `hm`. Rewrite `hm` using `[if_pos heq]`. Establish `: (π ^ (N + 1) - π) * (MvPowerSeries.coeff d (Ldef e e' P) / (π - π ^ (N + 1))) = -MvPowerSeries.coeff d (Ldef e e' P)` using `by field_simp; ring`. Take the linear combination `hm + this`.
-/
theorem step_inv (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    {N : ℕ} (hN : 1 ≤ N) {P : MvPowerSeries ι K} (h : Inv e e' a N P) :
    Inv e e' a (N + 1) (P + corr e e' π N P) ∧ Low (N + 1) (corr e e' π N P) := by
  have hπ0 : 0 < ‖π‖ := hS.2.2.1
  have hπ1 : ‖π‖ < 1 := hS.2.2.2.1
  have hnorm := norm_pi_sub_pow hπ0 hπ1 (r := N + 1) (by omega)
  have hne : π - π ^ (N + 1) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; linarith
  have hlowc : Low (N + 1) (corr e e' π N P) := by
    intro d hd; rw [coeff_corr, if_neg (by omega)]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hlowc⟩
  · rw [map_add, h.1, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlowc 0 (by simp),
      add_zero]
  · intro d
    rw [map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.2.1 d) ?_)
    rw [coeff_corr]
    split_ifs
    · rw [norm_div, hnorm]
      exact div_le_one_of_le₀ (defect_divBy hS he he' h.1 h.2.1 d) (norm_nonneg _)
    · simp
  · intro i
    rw [map_add, h.2.2.1 i, hlowc _ (by rw [Finsupp.degree_single]; omega), add_zero]
  · have hP'0 : MvPowerSeries.constantCoeff (P + corr e e' π N P) = 0 := by
      rw [map_add, h.1, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlowc 0 (by simp),
        add_zero]
    have hdiff : Low (N + 1) (P + corr e e' π N P - P) := by
      rw [add_sub_cancel_left]; exact hlowc
    intro d hd
    have hm := master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 hP'0 h.1 hdiff d (by omega)
    rw [add_sub_cancel_left, coeff_corr] at hm
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hd) with hlt | heq
    · rw [if_neg (by omega), mul_zero, h.2.2.2 d hlt, sub_zero] at hm
      exact hm
    · rw [if_pos heq] at hm
      have : (π ^ (N + 1) - π) * (MvPowerSeries.coeff d (Ldef e e' P) / (π - π ^ (N + 1))) =
          -MvPowerSeries.coeff d (Ldef e e' P) := by
        field_simp; ring
      linear_combination hm + this

/- English proof (translation)
Use `⟨cc_lin a, integral_lin a ha, coeff_lin_single a, ?_⟩` and prove the remaining obligations. Introduce `d hd`. Establish `hm` using `master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 (cc_lin a) (map_zero _) (by rw [sub_zero]; exact low_one (cc_lin a)) d (by omega)`. Rewrite `hm` using `[Ldef_zero e e' he.2.1 he'.2.1, map_zero, pow_one, sub_self, zero_mul, sub_zero]`. Conclude with `hm`.
-/
theorem inv_lin (_hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) : Inv e e' a 1 (lin a) := by
  refine ⟨cc_lin a, integral_lin a ha, coeff_lin_single a, ?_⟩
  intro d hd
  have hm := master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 (cc_lin a)
    (map_zero _) (by rw [sub_zero]; exact low_one (cc_lin a)) d (by omega)
  rw [Ldef_zero e e' he.2.1 he'.2.1, map_zero, pow_one, sub_self, zero_mul, sub_zero] at hm
  exact hm

/- English proof (translation)
The claim follows from `| 0 => inv_lin hS he he' ha | (k + 1) => (step_inv hS he he' (by omega) (inv_seq hS he he' ha k)).1`.
-/
theorem inv_seq (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) : ∀ k : ℕ, Inv e e' a (k + 1) (seq e e' π a (k + 1))
  | 0 => inv_lin hS he he' ha
  | (k + 1) => (step_inv hS he he' (by omega) (inv_seq hS he he' ha k)).1

/- English proof (translation)
Use `(step_inv hS he he' (by omega) (inv_seq hS he he' ha k)).2` as an intermediate fact. Express the relevant statement in the definitionally equal form `Low (k + 2) (seq e e' π a (k + 1) + corr e e' π (k + 1) (seq e e' π a (k + 1)) - seq e e' π a (k + 1))`. Rewrite using `[add_sub_cancel_left]`. Conclude with `this`.
-/
theorem seq_sub (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) (k : ℕ) :
    Low (k + 2) (seq e e' π a (k + 2) - seq e e' π a (k + 1)) := by
  have := (step_inv hS he he' (by omega) (inv_seq hS he he' ha k)).2
  change Low (k + 2) (seq e e' π a (k + 1) + corr e e' π (k + 1) (seq e e' π a (k + 1)) -
    seq e e' π a (k + 1))
  rw [add_sub_cancel_left]; exact this

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro hd; rw [show d.degree = 0 by omega]`. Consider the case `succ j ih`. Introduce `hd`.

Distinguish the cases in `h : d.degree = j + 1`. Rewrite using `[h]`. Rewrite using `[← ih (by omega)]`. Use `seq_sub hS he he' ha j d (by omega)` as an intermediate fact. Rewrite `this` using `[map_sub]`.

Conclude with `sub_eq_zero.mp this`.
-/
theorem stab (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) (d : ι →₀ ℕ) : ∀ k : ℕ, d.degree < k + 1 →
    MvPowerSeries.coeff d (seq e e' π a (k + 1)) =
      MvPowerSeries.coeff d (seq e e' π a (d.degree + 1)) := by
  intro k
  induction k with
  | zero => intro hd; rw [show d.degree = 0 by omega]
  | succ j ih =>
    intro hd
    by_cases h : d.degree = j + 1
    · rw [h]
    · rw [← ih (by omega)]
      have := seq_sub hS he he' ha j d (by omega)
      rw [map_sub] at this
      exact sub_eq_zero.mp this

def lim (e e' : PowerSeries K) (π : K) (a : ι → K) : MvPowerSeries ι K :=
  fun d => MvPowerSeries.coeff d (seq e e' π a (d.degree + 1))

/- English proof (translation)
Establish `hπ0 : 0 < ‖π‖` using `hS.2.2.1`. Establish `hπ1 : ‖π‖ < 1` using `hS.2.2.2.1`. Establish `H : ∀ N : ℕ, Low (N + 2) (ψ - φ)`. Introduce `N`. Proceed by induction on `N with`.

Consider the case `zero`. Introduce `d hd`. Rewrite using `[map_sub, sub_eq_zero]`. Break down `Nat.lt_or_ge d.degree 1 with h0 | h0` into its components or cases. Establish `: d = 0` using `(Finsupp.degree_eq_zero_iff d).mp (by omega)`.

Substitute `this` using the available equality. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hψ0, hφ0]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, d = Finsupp.single i 1 := by`. Establish `hd1 : d.degree = 1` using `by omega`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : d.support.Nonempty := by`.

Rewrite using `[Finsupp.support_nonempty_iff]`. Introduce and unpack `rfl`. Simplify using `at hd1`. Use `⟨i, ?_⟩` and prove the remaining obligations. Establish `hle : Finsupp.single i (d i) ≤ d`.

Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Ne.symm hj]`.

Establish `hdi : d i = 1`. Establish `h2` using `Finsupp.degree_mono hle`. Rewrite `h2` using `[Finsupp.degree_single]`. Establish `: d i ≠ 0` using `Finsupp.mem_support_iff.mp hi`. Use linear arithmetic over natural numbers and integers.

Take `⟨r, hr⟩` from `le_iff_exists_add.mp hle`. Establish `: r.degree = 0`. Use `congrArg Finsupp.degree hr` as an intermediate fact. Rewrite `this` using `[map_add, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers.

Rewrite `hr` using `[(Finsupp.degree_eq_zero_iff r).mp this, add_zero, hdi]`. Conclude with `hr`. Substitute `hi` using the available equality. Conclude with `h1 i`. Consider the case `succ N ih`.

Introduce `d hd`. Break down `lt_or_eq_of_le (Nat.lt_succ_iff.mp hd) with hlt | heq` into its components or cases. Conclude with `ih d hlt`. Establish `hm` using `master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 hψ0 hφ0 ih d (by omega)`. Rewrite `hm` using `[hLψ, hLφ, map_zero, sub_zero]`.

Establish `hnorm` using `norm_pi_sub_pow hπ0 hπ1 (r := N + 2) (by omega)`. Establish `hne : π ^ (N + 2) - π ≠ 0`. Introduce `h0`. Rewrite `hnorm` using `[← neg_sub, h0, neg_zero, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `(mul_eq_zero.mp hm.symm).resolve_left hne`. Use extensionality with `d`. Use `H d.degree d (by omega)` as an intermediate fact. Rewrite `this` using `[map_sub]`. Conclude with `sub_eq_zero.mp this`.
-/
theorem uniq (hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    {ψ φ : MvPowerSeries ι K} (hψ0 : MvPowerSeries.constantCoeff ψ = 0)
    (hφ0 : MvPowerSeries.constantCoeff φ = 0)
    (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) ψ =
      MvPowerSeries.coeff (Finsupp.single i 1) φ)
    (hLψ : Ldef e e' ψ = 0) (hLφ : Ldef e e' φ = 0) : ψ = φ := by
  have hπ0 : 0 < ‖π‖ := hS.2.2.1
  have hπ1 : ‖π‖ < 1 := hS.2.2.2.1
  have H : ∀ N : ℕ, Low (N + 2) (ψ - φ) := by
    intro N
    induction N with
    | zero =>
      intro d hd
      rw [map_sub, sub_eq_zero]
      rcases Nat.lt_or_ge d.degree 1 with h0 | h0
      · have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
        subst this
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hψ0, hφ0]
      · obtain ⟨i, hi⟩ : ∃ i, d = Finsupp.single i 1 := by
          have hd1 : d.degree = 1 := by omega
          obtain ⟨i, hi⟩ : d.support.Nonempty := by
            rw [Finsupp.support_nonempty_iff]
            rintro rfl
            simp at hd1
          refine ⟨i, ?_⟩
          have hle : Finsupp.single i (d i) ≤ d := by
            intro j
            by_cases hj : j = i
            · subst hj; simp
            · simp [Ne.symm hj]
          have hdi : d i = 1 := by
            have h2 := Finsupp.degree_mono hle
            rw [Finsupp.degree_single] at h2
            have : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
            omega
          obtain ⟨r, hr⟩ := le_iff_exists_add.mp hle
          have : r.degree = 0 := by
            have := congrArg Finsupp.degree hr
            rw [map_add, Finsupp.degree_single] at this
            omega
          rw [(Finsupp.degree_eq_zero_iff r).mp this, add_zero, hdi] at hr
          exact hr
        subst hi
        exact h1 i
    | succ N ih =>
      intro d hd
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hd) with hlt | heq
      · exact ih d hlt
      · have hm := master e e' he.2.1 he'.2.1 π he.2.2.1 he'.2.2.1 hψ0 hφ0 ih d (by omega)
        rw [hLψ, hLφ, map_zero, sub_zero] at hm
        have hnorm := norm_pi_sub_pow hπ0 hπ1 (r := N + 2) (by omega)
        have hne : π ^ (N + 2) - π ≠ 0 := by
          intro h0
          rw [← neg_sub, h0, neg_zero, norm_zero] at hnorm
          linarith
        exact (mul_eq_zero.mp hm.symm).resolve_left hne
  ext d
  have := H d.degree d (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.mp this

end Constr

end Formalism.LT.LTL

namespace Formalism.LT

open Formalism.G Formalism.LT.LTL

end Formalism.LT
