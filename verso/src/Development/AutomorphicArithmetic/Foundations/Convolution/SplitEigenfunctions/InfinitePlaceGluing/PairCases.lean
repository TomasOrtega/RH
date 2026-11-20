import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOneSubBound
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHecke
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PairCases

open NumberField IsDedekindDomain
open Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.ConvolutionTheory.R2
open UpperTheory.ConvolutionTheory.RankTwoDescent GroundTheory.Global

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.MultiplicativeMajorants

private def Maj (f : PowerSeries ℂ) (A : ℝ) : Prop := ∀ k, ‖PowerSeries.coeff k f‖ ≤ A ^ k

/- English proof (translation)
Introduce `k`. Rewrite using `[PowerSeries.coeff_one]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `using pow_nonneg (by linarith : (0 : ℝ) ≤ A) k`.
-/
private theorem maj_one {A : ℝ} (hA : 1 ≤ A) : Maj 1 A := by
  intro k
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simpa using pow_nonneg (by linarith : (0 : ℝ) ≤ A) k

/- English proof (translation)
Introduce `k`. Rewrite using `[PowerSeries.coeff_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun p hp => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, ← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, pow_add]`.

Conclude with `mul_le_mul (hf _) (hg _) (norm_nonneg _) (pow_nonneg hA _)`. Use `_ = ((k + 1 : ℕ) : ℝ) * A ^ k := by simp [Finset.Nat.card_antidiagonal]`. Use `_ ≤ (2 * A) ^ k := by`. Rewrite using `[mul_pow]`. Use `mul_le_mul_of_nonneg_right ?_ (pow_nonneg hA _)` and prove the remaining obligations.

Conclude with `Nat.lt_two_pow_self (n := k)` after adjusting the coercions.
-/
private theorem maj_mul {f g : PowerSeries ℂ} {A : ℝ} (hA : 0 ≤ A) (hf : Maj f A) (hg : Maj g A) :
    Maj (f * g) (2 * A) := by
  intro k
  rw [PowerSeries.coeff_mul]
  calc ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, ‖PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal k, A ^ k := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [norm_mul, ← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, pow_add]
        exact mul_le_mul (hf _) (hg _) (norm_nonneg _) (pow_nonneg hA _)
    _ = ((k + 1 : ℕ) : ℝ) * A ^ k := by simp [Finset.Nat.card_antidiagonal]
    _ ≤ (2 * A) ^ k := by
        rw [mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hA _)
        exact_mod_cast Nat.lt_two_pow_self (n := k)

private def Gs (x : ℂ) : PowerSeries ℂ := PowerSeries.mk fun k => x ^ k

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[mul_sub, mul_one, map_sub, ← mul_assoc]`. Consider the cases of `n with`. Consider the case `zero => simp [Gs]`. Consider the case `succ n`.

Rewrite using `[PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]`. Simplify using `[Gs, pow_succ, PowerSeries.coeff_one]`.
-/
private theorem gs_mul (x : ℂ) : Gs x * (1 - PowerSeries.C x * PowerSeries.X) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, ← mul_assoc]
  cases n with
  | zero => simp [Gs]
  | succ n =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
    simp [Gs, pow_succ, PowerSeries.coeff_one]

/- English proof (translation)
Introduce `k`. Simplify using `only [Gs, PowerSeries.coeff_mk, norm_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) h k`.
-/
private theorem gs_maj {x : ℂ} {R : ℝ} (h : ‖x‖ ≤ R) : Maj (Gs x) R := by
  intro k
  simp only [Gs, PowerSeries.coeff_mk, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h k

/- English proof (translation)
Establish `hR : 0 ≤ R` using `(norm_nonneg _).trans h₁`. Use `⟨(Gs x₁ * Gs x₂) * (Gs x₃ * Gs x₄), ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e₁` using `gs_mul x₁`. Establish `e₂` using `gs_mul x₂`. Establish `e₃` using `gs_mul x₃`.

Establish `e₄` using `gs_mul x₄`. Combine the equalities or inequalities in the displayed calculation. Use `maj_mul (by positivity) (maj_mul hR (gs_maj h₁) (gs_maj h₂)) (maj_mul hR (gs_maj h₃) (gs_maj h₄))` as an intermediate fact. Rewrite `this` using `[show 2 * (2 * R) = 4 * R by ring]`. Then use the resulting hypothesis. Establish `hG : ∀ x, PowerSeries.constantCoeff (Gs x) = 1` using `fun x => by`.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `[Gs]`. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `[hG]`.
-/
private theorem inv4 {x₁ x₂ x₃ x₄ : ℂ} {R : ℝ} (h₁ : ‖x₁‖ ≤ R) (h₂ : ‖x₂‖ ≤ R) (h₃ : ‖x₃‖ ≤ R) (h₄ : ‖x₄‖ ≤ R) :
    ∃ S : PowerSeries ℂ, S * ((1 - PowerSeries.C x₁ * PowerSeries.X) * (1 - PowerSeries.C x₂ * PowerSeries.X) *
      (1 - PowerSeries.C x₃ * PowerSeries.X) * (1 - PowerSeries.C x₄ * PowerSeries.X)) = 1 ∧ Maj S (4 * R) ∧
      PowerSeries.coeff 0 S = 1 := by
  have hR : 0 ≤ R := (norm_nonneg _).trans h₁
  refine ⟨(Gs x₁ * Gs x₂) * (Gs x₃ * Gs x₄), ?_, ?_, ?_⟩
  · have e₁ := gs_mul x₁
    have e₂ := gs_mul x₂
    have e₃ := gs_mul x₃
    have e₄ := gs_mul x₄
    calc _ = (Gs x₁ * (1 - PowerSeries.C x₁ * PowerSeries.X)) * (Gs x₂ * (1 - PowerSeries.C x₂ * PowerSeries.X)) *
          ((Gs x₃ * (1 - PowerSeries.C x₃ * PowerSeries.X)) * (Gs x₄ * (1 - PowerSeries.C x₄ * PowerSeries.X))) := by ring
      _ = 1 := by rw [e₁, e₂, e₃, e₄]; simp
  · have := maj_mul (by positivity) (maj_mul hR (gs_maj h₁) (gs_maj h₂)) (maj_mul hR (gs_maj h₃) (gs_maj h₄))
    rwa [show 2 * (2 * R) = 4 * R by ring] at this
  · have hG : ∀ x, PowerSeries.constantCoeff (Gs x) = 1 := fun x => by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [Gs]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [hG]

/- English proof (translation)
Set `a : ℕ → ℂ` to `fun n => if n = 0 then 0 else n.factorization.prod fun p k => PowerSeries.coeff k (T p)`. Establish `a1 : a 1 = 1` using `by simp [a]`. Establish `bound : ∀ n : ℕ, n ≠ 0 → ‖a n‖ ≤ (n : ℝ) ^ 3`. Introduce `n hn`. Establish `hprod : ((n.factorization.prod fun p k => p ^ k : ℕ) : ℝ) = n`.

Rewrite using `[Nat.prod_factorization_pow_eq_self hn]`. Simplify using `only [a, if_neg hn, Finsupp.prod]`. Rewrite using `[norm_prod, ← hprod, Finsupp.prod, Nat.cast_prod, ← Finset.prod_pow]`. Use `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => ?_` and prove the remaining obligations. Establish `pp : p.Prime` using `Nat.prime_of_mem_primeFactors (by simpa using hp)`.

Establish `h2 : (2 : ℝ) ≤ p` using `by exact_mod_cast pp.two_le`. Use `(hM p pp _).trans ?_` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← pow_mul, mul_comm _ 3, pow_mul]`. Use `pow_le_pow_left₀ (by positivity) ?_ _` and prove the remaining obligations.

Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2), mul_self_nonneg (p : ℝ)]`. Use `⟨a, a1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m n h`. Break down `eq_or_ne m 0 with rfl | hm` into its components or cases. Establish `: n = 1` using `by simpa using h`.

Substitute `this` using the available equality. Simplify using `[a1]`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Establish `: m = 1` using `by simpa using h`. Substitute `this` using the available equality.

Simplify using `[a1]`. Simplify using `only [a, if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn]`. Rewrite using `[Nat.factorization_mul_of_coprime h, Finsupp.prod_add_index_of_disjoint]`. Simplify using `using h.disjoint_primeFactors`. Introduce `p k pp`.

Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Simplify using `[a1, h0 p pp]`. Simplify using `only [a, if_neg (pow_ne_zero k pp.ne_zero), pp.factorization_pow]`. Rewrite using `[Finsupp.prod_single_index (h0 p pp)]`. Introduce `s hs`.

Use `LSeriesSummable_of_le_const_mul_rpow (x := 4) hs ⟨1, fun n hn => ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul, show (4 - 1 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Conclude with `bound n hn`.
-/
private theorem arith (T : ℕ → PowerSeries ℂ) (h0 : ∀ p : ℕ, p.Prime → PowerSeries.coeff 0 (T p) = 1)
    (hM : ∀ p : ℕ, p.Prime → Maj (T p) (4 * p)) :
    ∃ a : ℕ → ℂ, a 1 = 1 ∧ (∀ m n, m.Coprime n → a (m * n) = a m * a n) ∧
      (∀ p k : ℕ, p.Prime → a (p ^ k) = PowerSeries.coeff k (T p)) ∧ ∀ s : ℂ, 4 < s.re → LSeriesSummable a s := by
  let a : ℕ → ℂ := fun n => if n = 0 then 0 else n.factorization.prod fun p k => PowerSeries.coeff k (T p)
  have a1 : a 1 = 1 := by simp [a]
  have bound : ∀ n : ℕ, n ≠ 0 → ‖a n‖ ≤ (n : ℝ) ^ 3 := by
    intro n hn
    have hprod : ((n.factorization.prod fun p k => p ^ k : ℕ) : ℝ) = n := by
      rw [Nat.prod_factorization_pow_eq_self hn]
    simp only [a, if_neg hn, Finsupp.prod]
    rw [norm_prod, ← hprod, Finsupp.prod, Nat.cast_prod, ← Finset.prod_pow]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => ?_
    have pp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast pp.two_le
    refine (hM p pp _).trans ?_
    push_cast
    rw [← pow_mul, mul_comm _ 3, pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2), mul_self_nonneg (p : ℝ)]
  refine ⟨a, a1, ?_, ?_, ?_⟩
  · intro m n h
    rcases eq_or_ne m 0 with rfl | hm
    · have : n = 1 := by simpa using h
      subst this; simp [a1]
    rcases eq_or_ne n 0 with rfl | hn
    · have : m = 1 := by simpa using h
      subst this; simp [a1]
    simp only [a, if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn]
    rw [Nat.factorization_mul_of_coprime h, Finsupp.prod_add_index_of_disjoint]
    simpa using h.disjoint_primeFactors
  · intro p k pp
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [a1, h0 p pp]
    · simp only [a, if_neg (pow_ne_zero k pp.ne_zero), pp.factorization_pow]
      rw [Finsupp.prod_single_index (h0 p pp)]
  · intro s hs
    refine LSeriesSummable_of_le_const_mul_rpow (x := 4) hs ⟨1, fun n hn => ?_⟩
    rw [one_mul, show (4 - 1 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact bound n hn

/- English proof (translation)
Rewrite using `[normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
private theorem nv {K : Type} [Field K] [NumberField K] (v : H.P K) : normV v = Ideal.absNorm v.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Rewrite using `[nv, DirichletHecke.absNorm_asIdeal]`. Conclude with `Fact.out`.
-/
private theorem nv_prime (v : H.P ℚ) : (normV v).Prime := by
  rw [nv, DirichletHecke.absNorm_asIdeal]; exact Fact.out

/- English proof (translation)
Rewrite `h` using `[nv, nv]`. Establish `e` using `DirichletHecke.eq_span_of_absNorm_eq (I := v.asIdeal) rfl`. Establish `e'` using `DirichletHecke.eq_span_of_absNorm_eq (I := v'.asIdeal) rfl`. Conclude with `HeightOneSpectrum.ext (e.trans (by rw [h]; exact e'.symm))`.
-/
private theorem nv_inj {v v' : H.P ℚ} (h : normV v = normV v') : v = v' := by
  rw [nv, nv] at h
  have e := DirichletHecke.eq_span_of_absNorm_eq (I := v.asIdeal) rfl
  have e' := DirichletHecke.eq_span_of_absNorm_eq (I := v'.asIdeal) rfl
  exact HeightOneSpectrum.ext (e.trans (by rw [h]; exact e'.symm))

/- English proof (translation)
Establish `e` using `DirichletHecke.eq_span_of_absNorm_eq (I := v.asIdeal) (nv v).symm`. Establish `hm : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal` using `e.ge (Ideal.mem_span_singleton_self _)`. Take `⟨c, rfl⟩` from `h`. Rewrite using `[Bad]`. Use `push_cast`.

Conclude with `Ideal.mul_mem_right _ _ hm`.
-/
private theorem bad_of_dvd {N : ℕ} (v : H.P ℚ) (h : normV v ∣ N) : Bad N v := by
  have e := DirichletHecke.eq_span_of_absNorm_eq (I := v.asIdeal) (nv v).symm
  have hm : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := e.ge (Ideal.mem_span_singleton_self _)
  obtain ⟨c, rfl⟩ := h
  rw [Bad]
  push_cast
  exact Ideal.mul_mem_right _ _ hm

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hww' : w'.asIdeal ≠ w.asIdeal` using `fun e => hne (HeightOneSpectrum.ext e).symm`. Use `set p := w.under (𝓞 ℚ) with hp`. Use `haveI := w.isMaximal`. Use `haveI : w.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩`. Establish `hf` using `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal p.asIdeal p.isPrime p.ne_bot`.

Establish `hsub : ({w'.asIdeal, w.asIdeal} : Finset (Ideal (𝓞 E))) ⊆ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 E)`. Introduce `Q hQ`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hQ`. Break down `hQ with rfl | rfl` into its components or cases. Use `GlobalTheory.HenQ.Regroup.mem_fin E w'` as an intermediate fact.

Rewrite `this` using `[h]`. Then use the resulting hypothesis. Conclude with `GlobalTheory.HenQ.Regroup.mem_fin E w`. Establish `hle` using `Finset.sum_le_sum_of_subset (f := fun Q => p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q) hsub`. Rewrite `hle` using `[GlobalTheory.HenQ.Regroup.sum_eq E hE p]`. Rewrite `hle` using `[Finset.sum_insert (by simp [hww']), Finset.sum_singleton]`.

Establish `b` using `GlobalTheory.HenQ.Regroup.term_pos E w'`. Rewrite `b` using `[h]`. Establish `he` using `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal p.ne_bot`. Establish `hf0` using `Ideal.inertiaDeg'_pos (p := p.asIdeal) (P := w.asIdeal)`. Establish `hle2 : p.asIdeal.inertiaDeg' w.asIdeal ≤ p.asIdeal.ramificationIdx' w.asIdeal * p.asIdeal.inertiaDeg' w.asIdeal` using `Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero he)`.

Establish `h1 : p.asIdeal.inertiaDeg' w.asIdeal = 1` using `by omega`. Rewrite using `[nv, nv, hf, h1, pow_one]`.
-/
private theorem nv_split (hE : Module.finrank ℚ E = 2) {w w' : H.P E} (hne : w ≠ w')
    (h : w'.under (𝓞 ℚ) = w.under (𝓞 ℚ)) : normV w = normV (w.under (𝓞 ℚ)) := by
  have hww' : w'.asIdeal ≠ w.asIdeal := fun e => hne (HeightOneSpectrum.ext e).symm
  set p := w.under (𝓞 ℚ) with hp
  haveI := w.isMaximal
  haveI : w.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have hf := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal p.asIdeal p.isPrime p.ne_bot
  have hsub : ({w'.asIdeal, w.asIdeal} : Finset (Ideal (𝓞 E))) ⊆
      IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 E) := by
    intro Q hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl
    · have := GlobalTheory.HenQ.Regroup.mem_fin E w'; rwa [h] at this
    · exact GlobalTheory.HenQ.Regroup.mem_fin E w
  have hle := Finset.sum_le_sum_of_subset
    (f := fun Q => p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q) hsub
  rw [GlobalTheory.HenQ.Regroup.sum_eq E hE p] at hle
  rw [Finset.sum_insert (by simp [hww']), Finset.sum_singleton] at hle
  have b := GlobalTheory.HenQ.Regroup.term_pos E w'
  rw [h] at b
  have he := Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal p.ne_bot
  have hf0 := Ideal.inertiaDeg'_pos (p := p.asIdeal) (P := w.asIdeal)
  have hle2 : p.asIdeal.inertiaDeg' w.asIdeal ≤
      p.asIdeal.ramificationIdx' w.asIdeal * p.asIdeal.inertiaDeg' w.asIdeal :=
    Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero he)
  have h1 : p.asIdeal.inertiaDeg' w.asIdeal = 1 := by omega
  rw [nv, nv, hf, h1, pow_one]

/- English proof (translation)
Establish `h2` using `(nv_prime v).two_le`. Establish `key : normV u = normV v`. Break down `GlobalTheory.HenQ.Regroup.fiber_split E hE w w' u (hu'.trans hu.symm) (hv.trans hu.symm) hn.symm with rfl | rfl` into its components or cases. Rewrite using `[nv_split hE hn (hu'.trans hu.symm), hu]`. Rewrite using `[nv_split hE hn.symm (hu.trans hu'.symm), hu']`.

Rewrite `hr` using `[key]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem not_both (hE : Module.finrank ℚ E = 2) {w w' u : H.P E} {v : H.P ℚ} (hn : w ≠ w')
    (hu : w.under (𝓞 ℚ) = v) (hu' : w'.under (𝓞 ℚ) = v) (hv : u.under (𝓞 ℚ) = v)
    (hr : normV u = normV v ^ 2) : False := by
  have h2 := (nv_prime v).two_le
  have key : normV u = normV v := by
    rcases GlobalTheory.HenQ.Regroup.fiber_split E hE w w' u (hu'.trans hu.symm) (hv.trans hu.symm) hn.symm with rfl | rfl
    · rw [nv_split hE hn (hu'.trans hu.symm), hu]
    · rw [nv_split hE hn.symm (hu.trans hu'.symm), hu']
  rw [key] at hr
  nlinarith

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.PairCases.pair_cases h`.
-/
private theorem pair_cases {a b c d : ℂˣ} (h : ({a, b} : Multiset ℂˣ) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) :=
  _root_.UpperTheory.Reformulated.B.PairCases.pair_cases h

private noncomputable def Qs (a b a' b' c : ℂˣ) : PowerSeries ℂ :=
  (1 - PowerSeries.C ((a * a' * c : ℂˣ) : ℂ) * PowerSeries.X) *
    (1 - PowerSeries.C ((a * b' * c : ℂˣ) : ℂ) * PowerSeries.X) *
    (1 - PowerSeries.C ((b * a' * c : ℂˣ) : ℂ) * PowerSeries.X) *
    (1 - PowerSeries.C ((b * b' * c : ℂˣ) : ℂ) * PowerSeries.X)

private noncomputable def Qi (a b c : ℂˣ) : PowerSeries ℂ :=
  (1 - PowerSeries.C ((a * c : ℂˣ) : ℂ) * PowerSeries.X) *
    (1 - PowerSeries.C ((b * c : ℂˣ) : ℂ) * PowerSeries.X) * (1 - PowerSeries.X ^ 2)

variable [IsTotallyComplex E]

private def Den (P : CuspSub E 2) (χ : HChar ℚ) (v : H.P ℚ) (Q : PowerSeries ℂ) : Prop :=
  (∃ (w w' : H.P E) (α β α' β' : ℂˣ), w ≠ w' ∧ w.under (𝓞 ℚ) = v ∧ w'.under (𝓞 ℚ) = v ∧
    (CG.mk P).HasSat w {α, β} ∧ (CG.mk P).HasSat w' {α', β'} ∧ Q = Qs α β α' β' (χ.val v)) ∨
  (∃ (w : H.P E) (α β : ℂˣ), w.under (𝓞 ℚ) = v ∧ normV w = normV v ^ 2 ∧
    (CG.mk P).HasSat w {α, β} ∧ Q = Qi α β (χ.val v))

/- English proof (translation)
Break down `h with ⟨w₁, w₁', α, β, α', β', hn, hu, hu', hs, hs', rfl⟩ | ⟨w₁, α, β, hu, hq, hs, rfl⟩` into its components or cases. Break down `h' with ⟨w₂, w₂', γ, δ, γ', δ', hm, hv, hv', ht, ht', rfl⟩ | ⟨w₂, γ, δ, hv, hr, ht, rfl⟩` into its components or cases. Establish `c₁` using `GlobalTheory.HenQ.Regroup.fiber_split E hE w₁ w₁' w₂ (hu'.trans hu.symm) (hv.trans hu.symm) hn.symm`. Establish `c₂` using `GlobalTheory.HenQ.Regroup.fiber_split E hE w₁ w₁' w₂' (hu'.trans hu.symm) (hv'.trans hu.symm) hn.symm`. Apply the tactic sequence `rcases c₁ with rfl | rfl <;> rcases c₂ with rfl | rfl`.

Conclude with `absurd rfl hm`. Apply the tactic sequence `rcases pair_cases (CG.HasSat.unique hs ht) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>`. Apply the tactic sequence `rcases pair_cases (CG.HasSat.unique hs' ht') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>`. Apply the tactic sequence `simp only [Qs, Units.val_mul, map_mul] <;> ring`. Apply the tactic sequence `rcases pair_cases (CG.HasSat.unique hs ht') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>`.

Apply the tactic sequence `rcases pair_cases (CG.HasSat.unique hs' ht) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>`. Apply the tactic sequence `simp only [Qs, Units.val_mul, map_mul] <;> ring`. Conclude with `absurd rfl hm`. Conclude with `(not_both hE hn hu hu' hv hr).elim`. Break down `h' with ⟨w₂, w₂', γ, δ, γ', δ', hm, hv, hv', ht, ht', rfl⟩ | ⟨w₂, γ, δ, hv, hr, ht, rfl⟩` into its components or cases.

Conclude with `(not_both hE hm hv hv' hu hq).elim`. Establish `hN : Ideal.absNorm w₁.asIdeal = Ideal.absNorm (w₁.under (𝓞 ℚ)).asIdeal ^ 2`. Rewrite using `[← nv, ← nv, hu, hq]`. Take `rfl` from `GlobalTheory.HenQ.Regroup.fiber_inert E hE w₁ w₂ hN (hv.trans hu.symm)`. Apply the tactic sequence `rcases pair_cases (CG.HasSat.unique hs ht) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>`.

Apply the tactic sequence `simp only [Qi, Units.val_mul, map_mul] <;> ring`.
-/
private theorem den_unique (hE : Module.finrank ℚ E = 2) {P : CuspSub E 2} {χ : HChar ℚ} {v : H.P ℚ}
    {Q Q' : PowerSeries ℂ} (h : Den P χ v Q) (h' : Den P χ v Q') : Q = Q' := by
  rcases h with ⟨w₁, w₁', α, β, α', β', hn, hu, hu', hs, hs', rfl⟩ | ⟨w₁, α, β, hu, hq, hs, rfl⟩
  · rcases h' with ⟨w₂, w₂', γ, δ, γ', δ', hm, hv, hv', ht, ht', rfl⟩ | ⟨w₂, γ, δ, hv, hr, ht, rfl⟩
    · have c₁ := GlobalTheory.HenQ.Regroup.fiber_split E hE w₁ w₁' w₂ (hu'.trans hu.symm) (hv.trans hu.symm) hn.symm
      have c₂ := GlobalTheory.HenQ.Regroup.fiber_split E hE w₁ w₁' w₂' (hu'.trans hu.symm) (hv'.trans hu.symm) hn.symm
      rcases c₁ with rfl | rfl <;> rcases c₂ with rfl | rfl
      · exact absurd rfl hm
      · rcases pair_cases (CG.HasSat.unique hs ht) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases pair_cases (CG.HasSat.unique hs' ht') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [Qs, Units.val_mul, map_mul] <;> ring
      · rcases pair_cases (CG.HasSat.unique hs ht') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases pair_cases (CG.HasSat.unique hs' ht) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [Qs, Units.val_mul, map_mul] <;> ring
      · exact absurd rfl hm
    · exact (not_both hE hn hu hu' hv hr).elim
  · rcases h' with ⟨w₂, w₂', γ, δ, γ', δ', hm, hv, hv', ht, ht', rfl⟩ | ⟨w₂, γ, δ, hv, hr, ht, rfl⟩
    · exact (not_both hE hm hv hv' hu hq).elim
    · have hN : Ideal.absNorm w₁.asIdeal = Ideal.absNorm (w₁.under (𝓞 ℚ)).asIdeal ^ 2 := by
        rw [← nv, ← nv, hu, hq]
      obtain rfl := GlobalTheory.HenQ.Regroup.fiber_inert E hE w₁ w₂ hN (hv.trans hu.symm)
      rcases pair_cases (CG.HasSat.unique hs ht) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [Qi, Units.val_mul, map_mul] <;> ring

/- English proof (translation)
Establish `hs' : ∀ (w : H.P E) (α β : ℂˣ), (CG.mk P).HasSat w {α, β} → ‖(β : ℂ)‖ ^ 2 ≤ normV w` using `fun w α β hh => hs w β α (by rwa [Multiset.pair_comm])`. Establish `q1 : (1 : ℝ) ≤ normV v` using `by exact_mod_cast (nv_prime v).one_le`. Break down `h with ⟨w, w', α, β, α', β', hn, hu, hu', h₁, h₂, rfl⟩ | ⟨w, α, β, hu, hq, h₁, rfl⟩` into its components or cases. Establish `nw : normV w = normV v` using `by rw [nv_split hE hn (hu'.trans hu.symm), hu]`. Establish `nw' : normV w' = normV v` using `by rw [nv_split hE hn.symm (hu.trans hu'.symm), hu']`.

Establish `a₁` using `hs w α β h₁`. Establish `a₂` using `hs' w α β h₁`. Establish `a₃` using `hs w' α' β' h₂`. Establish `a₄` using `hs' w' α' β' h₂`. Rewrite `a₁`, `a₂` using `[nw]`.

Rewrite `a₃`, `a₄` using `[nw']`. Establish `key : ∀ x y : ℂˣ, ‖(x : ℂ)‖ ^ 2 ≤ normV v → ‖(y : ℂ)‖ ^ 2 ≤ normV v → ‖((x * y * χ.val v : ℂˣ) : ℂ)‖ ≤ normV v`. Introduce `x y hx hy`. Rewrite using `[Units.val_mul, Units.val_mul, norm_mul, norm_mul, hc, mul_one]`. Use polynomial arithmetic with `[sq_nonneg (‖(x : ℂ)‖ - ‖(y : ℂ)‖)]`.

Conclude with `inv4 (key _ _ a₁ a₃) (key _ _ a₁ a₄) (key _ _ a₂ a₃) (key _ _ a₂ a₄)`. Establish `q0 : (0 : ℝ) ≤ normV v` using `by positivity`. Establish `key : ∀ x : ℂˣ, ‖(x : ℂ)‖ ^ 2 ≤ normV w → ‖((x * χ.val v : ℂˣ) : ℂ)‖ ≤ normV v`. Introduce `x hx`. Rewrite using `[Units.val_mul, norm_mul, hc, mul_one]`.

Rewrite `hx` using `[hq]`. Move the coercions through the operations in `at hx`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) q0 two_ne_zero).1 hx`. Take `⟨S, e, m, c⟩` from `inv4 (x₃ := 1) (x₄ := -1) (key _ (hs w α β h₁)) (key _ (hs' w α β h₁)) (by simpa using q1) (by simpa using q1)`. Use `⟨S, ?_, m, c⟩` and prove the remaining obligations.

Rewrite using `[← e]`. Simplify using `only [Qi, map_one, map_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem den_inv (hE : Module.finrank ℚ E = 2) {P : CuspSub E 2} {χ : HChar ℚ} {v : H.P ℚ}
    {Q : PowerSeries ℂ}
    (hs : ∀ (w : H.P E) (α β : ℂˣ), (CG.mk P).HasSat w {α, β} → ‖(α : ℂ)‖ ^ 2 ≤ normV w)
    (hc : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1) (h : Den P χ v Q) :
    ∃ S : PowerSeries ℂ, S * Q = 1 ∧ Maj S (4 * normV v) ∧ PowerSeries.coeff 0 S = 1 := by
  have hs' : ∀ (w : H.P E) (α β : ℂˣ), (CG.mk P).HasSat w {α, β} → ‖(β : ℂ)‖ ^ 2 ≤ normV w :=
    fun w α β hh => hs w β α (by rwa [Multiset.pair_comm])
  have q1 : (1 : ℝ) ≤ normV v := by exact_mod_cast (nv_prime v).one_le
  rcases h with ⟨w, w', α, β, α', β', hn, hu, hu', h₁, h₂, rfl⟩ | ⟨w, α, β, hu, hq, h₁, rfl⟩
  · have nw : normV w = normV v := by rw [nv_split hE hn (hu'.trans hu.symm), hu]
    have nw' : normV w' = normV v := by rw [nv_split hE hn.symm (hu.trans hu'.symm), hu']
    have a₁ := hs w α β h₁
    have a₂ := hs' w α β h₁
    have a₃ := hs w' α' β' h₂
    have a₄ := hs' w' α' β' h₂
    rw [nw] at a₁ a₂
    rw [nw'] at a₃ a₄
    have key : ∀ x y : ℂˣ, ‖(x : ℂ)‖ ^ 2 ≤ normV v → ‖(y : ℂ)‖ ^ 2 ≤ normV v →
        ‖((x * y * χ.val v : ℂˣ) : ℂ)‖ ≤ normV v := by
      intro x y hx hy
      rw [Units.val_mul, Units.val_mul, norm_mul, norm_mul, hc, mul_one]
      nlinarith [sq_nonneg (‖(x : ℂ)‖ - ‖(y : ℂ)‖)]
    exact inv4 (key _ _ a₁ a₃) (key _ _ a₁ a₄) (key _ _ a₂ a₃) (key _ _ a₂ a₄)
  · have q0 : (0 : ℝ) ≤ normV v := by positivity
    have key : ∀ x : ℂˣ, ‖(x : ℂ)‖ ^ 2 ≤ normV w → ‖((x * χ.val v : ℂˣ) : ℂ)‖ ≤ normV v := by
      intro x hx
      rw [Units.val_mul, norm_mul, hc, mul_one]
      rw [hq] at hx
      push_cast at hx
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) q0 two_ne_zero).1 hx
    obtain ⟨S, e, m, c⟩ := inv4 (x₃ := 1) (x₄ := -1) (key _ (hs w α β h₁)) (key _ (hs' w α β h₁))
      (by simpa using q1) (by simpa using q1)
    refine ⟨S, ?_, m, c⟩
    rw [← e]
    simp only [Qi, map_one, map_neg]
    ring

end UpperTheory.ConvolutionTheory.RankTwoDescent.MultiplicativeMajorants

open UpperTheory.ConvolutionTheory.RankTwoDescent.MultiplicativeMajorants in
/- English proof (translation)
Introduce `hS E _ _ _ D P ω χ hc hu hq L N φ _`. Establish `hE : Module.finrank ℚ E = 2` using `by rw [Module.finrank_eq_card_basis D.b, Fintype.card_fin]`. Establish `hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1`. Introduce `a`. Establish `h1` using `congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hq a)`.

Establish `h2 : ‖((ω.1 a : ℂˣ) : ℂ)‖ = 1` using `hu a`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one, h2, mul_one] at h1`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1`. Establish `hc' : ∀ v : H.P ℚ, ‖((χ.val v : ℂˣ) : ℂ)‖ = 1` using `fun v => hχ _`. Establish `hs : ∀ (w : H.P E) (α β : ℂˣ), (CG.mk P).HasSat w {α, β} → ‖(α : ℂ)‖ ^ 2 ≤ normV w` using `fun w α β h => (hS E D P ω χ hc hu hq w α β h).2.2`.

Set `Tv : H.P ℚ → PowerSeries ℂ` to `fun v => if h : ∃ Q, Den P χ v Q then Classical.choose (den_inv hE hs (hc' v) h.choose_spec) else 1`. Establish `tv1 : ∀ v Q, Den P χ v Q → Tv v * Q = 1`. Introduce `v Q hd`. Establish `h : ∃ Q, Den P χ v Q` using `⟨Q, hd⟩`. Simplify using `only [Tv, dif_pos h]`.

Use `(Classical.choose_spec (den_inv hE hs (hc' v) h.choose_spec)).1` as an intermediate fact. Rewrite using `[← den_unique hE h.choose_spec hd]`. Conclude with `this`. Establish `tvM : ∀ v, Maj (Tv v) (4 * normV v)`. Introduce `v`.

Establish `q1 : (1 : ℝ) ≤ 4 * normV v`. Establish `: (1 : ℝ) ≤ normV v` using `by exact_mod_cast (nv_prime v).one_le`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h : ∃ Q, Den P χ v Q`. Simplify using `only [Tv, dif_pos h]`.

Conclude with `(Classical.choose_spec (den_inv hE hs (hc' v) h.choose_spec)).2.1`. Simplify using `only [Tv, dif_neg h]`. Conclude with `maj_one q1`. Establish `tv0 : ∀ v, PowerSeries.coeff 0 (Tv v) = 1`. Introduce `v`.

Distinguish the cases in `h : ∃ Q, Den P χ v Q`. Simplify using `only [Tv, dif_pos h]`. Conclude with `(Classical.choose_spec (den_inv hE hs (hc' v) h.choose_spec)).2.2`. Simplify using `[Tv, dif_neg h]`. Set `T : ℕ → PowerSeries ℂ` to `fun p => if p ∣ N then 1 else if h : ∃ v : H.P ℚ, normV v = p then Tv h.choose else 1`.

Establish `tEq : ∀ v : H.P ℚ, ¬ Bad N v → T (normV v) = Tv v`. Introduce `v hb`. Establish `h : ∃ v' : H.P ℚ, normV v' = normV v` using `⟨v, rfl⟩`. Simplify using `only [T, if_neg (fun hd => hb (bad_of_dvd v hd)), dif_pos h]`. Rewrite using `[nv_inj h.choose_spec]`.

Establish `h0 : ∀ p : ℕ, p.Prime → PowerSeries.coeff 0 (T p) = 1`. Introduce `p _`. Simplify using `only [T]`. Use `split_ifs with h₁ h₂`. Simplify using the standard rewrite rules.

Conclude with `tv0 _`. Simplify using the standard rewrite rules. Establish `hM : ∀ p : ℕ, p.Prime → Maj (T p) (4 * p)`. Introduce `p pp`. Establish `q1 : (1 : ℝ) ≤ 4 * p`.

Establish `: (1 : ℝ) ≤ p` using `by exact_mod_cast pp.one_le`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [T]`. Use `split_ifs with h₁ h₂`. Conclude with `maj_one q1`.

Use `tvM h₂.choose` as an intermediate fact. Rewrite `this` using `[h₂.choose_spec]`. Then use the resulting hypothesis. Conclude with `maj_one q1`. Take `⟨a, a1, am, ap, asum⟩` from `arith T h0 hM`. Establish `key : ∀ (v : H.P ℚ) Q, ¬ Bad N v → Den P χ v Q → (PowerSeries.mk fun k => a (normV v ^ k)) * Q = 1`.

Introduce `v Q hb hd`. Establish `e : (PowerSeries.mk fun k => a (normV v ^ k)) = T (normV v)`. Use extensionality with `k`. Rewrite using `[PowerSeries.coeff_mk, ap _ _ (nv_prime v)]`. Rewrite using `[e, tEq v hb]`.

Conclude with `tv1 v Q hd`. Use `⟨a, ⟨a1, am, ?_, ?_, ?_⟩, asum⟩` and prove the remaining obligations. Introduce `p k pp hd`. Rewrite using `[ap p _ pp]`. Simplify using `[T, hd, PowerSeries.coeff_one]`.

Introduce `v hb w w' hn hw hw' α β α' β' h₁ h₂`. Conclude with `key v _ hb (Or.inl ⟨w, w', α, β, α', β', hn, hw, hw', h₁, h₂, rfl⟩)`. Introduce `v hb w hw hn α β h₁`. Conclude with `key v _ hb (Or.inr ⟨w, α, β, hw, hn, h₁, rfl⟩)`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.asEx_of :
    SatU → AsEx := by
  intro hS E _ _ _ D P ω χ hc hu hq L N φ _
  have hE : Module.finrank ℚ E = 2 := by rw [Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  have hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
    intro a
    have h1 := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hq a)
    have h2 : ‖((ω.1 a : ℂˣ) : ℂ)‖ = 1 := hu a
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one, h2, mul_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1
  have hc' : ∀ v : H.P ℚ, ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := fun v => hχ _
  have hs : ∀ (w : H.P E) (α β : ℂˣ), (CG.mk P).HasSat w {α, β} → ‖(α : ℂ)‖ ^ 2 ≤ normV w :=
    fun w α β h => (hS E D P ω χ hc hu hq w α β h).2.2
  classical
  let Tv : H.P ℚ → PowerSeries ℂ := fun v =>
    if h : ∃ Q, Den P χ v Q then Classical.choose (den_inv hE hs (hc' v) h.choose_spec) else 1
  have tv1 : ∀ v Q, Den P χ v Q → Tv v * Q = 1 := by
    intro v Q hd
    have h : ∃ Q, Den P χ v Q := ⟨Q, hd⟩
    simp only [Tv, dif_pos h]
    have := (Classical.choose_spec (den_inv hE hs (hc' v) h.choose_spec)).1
    rw [← den_unique hE h.choose_spec hd]
    exact this
  have tvM : ∀ v, Maj (Tv v) (4 * normV v) := by
    intro v
    have q1 : (1 : ℝ) ≤ 4 * normV v := by
      have : (1 : ℝ) ≤ normV v := by exact_mod_cast (nv_prime v).one_le
      linarith
    by_cases h : ∃ Q, Den P χ v Q
    · simp only [Tv, dif_pos h]
      exact (Classical.choose_spec (den_inv hE hs (hc' v) h.choose_spec)).2.1
    · simp only [Tv, dif_neg h]
      exact maj_one q1
  have tv0 : ∀ v, PowerSeries.coeff 0 (Tv v) = 1 := by
    intro v
    by_cases h : ∃ Q, Den P χ v Q
    · simp only [Tv, dif_pos h]
      exact (Classical.choose_spec (den_inv hE hs (hc' v) h.choose_spec)).2.2
    · simp [Tv, dif_neg h]
  let T : ℕ → PowerSeries ℂ := fun p =>
    if p ∣ N then 1 else if h : ∃ v : H.P ℚ, normV v = p then Tv h.choose else 1
  have tEq : ∀ v : H.P ℚ, ¬ Bad N v → T (normV v) = Tv v := by
    intro v hb
    have h : ∃ v' : H.P ℚ, normV v' = normV v := ⟨v, rfl⟩
    simp only [T, if_neg (fun hd => hb (bad_of_dvd v hd)), dif_pos h]
    rw [nv_inj h.choose_spec]
  have h0 : ∀ p : ℕ, p.Prime → PowerSeries.coeff 0 (T p) = 1 := by
    intro p _
    simp only [T]
    split_ifs with h₁ h₂
    · simp
    · exact tv0 _
    · simp
  have hM : ∀ p : ℕ, p.Prime → Maj (T p) (4 * p) := by
    intro p pp
    have q1 : (1 : ℝ) ≤ 4 * p := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast pp.one_le
      linarith
    simp only [T]
    split_ifs with h₁ h₂
    · exact maj_one q1
    · have := tvM h₂.choose
      rwa [h₂.choose_spec] at this
    · exact maj_one q1
  obtain ⟨a, a1, am, ap, asum⟩ := arith T h0 hM
  have key : ∀ (v : H.P ℚ) Q, ¬ Bad N v → Den P χ v Q → (PowerSeries.mk fun k => a (normV v ^ k)) * Q = 1 := by
    intro v Q hb hd
    have e : (PowerSeries.mk fun k => a (normV v ^ k)) = T (normV v) := by
      ext k
      rw [PowerSeries.coeff_mk, ap _ _ (nv_prime v)]
    rw [e, tEq v hb]
    exact tv1 v Q hd
  refine ⟨a, ⟨a1, am, ?_, ?_, ?_⟩, asum⟩
  · intro p k pp hd
    rw [ap p _ pp]
    simp [T, hd, PowerSeries.coeff_one]
  · intro v hb w w' hn hw hw' α β α' β' h₁ h₂
    exact key v _ hb (Or.inl ⟨w, w', α, β, α', β', hn, hw, hw', h₁, h₂, rfl⟩)
  · intro v hb w hw hn α β h₁
    exact key v _ hb (Or.inr ⟨w, α, β, hw, hn, h₁, rfl⟩)
