import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMonicSquarefreeUnitConstPolysIffMonicSquarefrStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusCardBoundsAndMulStatement

open Polynomial Classical UniqueFactorizationMonoid
namespace GlobalTheory.BadShare

open Polynomial Classical UniqueFactorizationMonoid in
/- English proof (translation)
Unfold `_root_.GlobalTheory.BadShare.mass`. Establish `hsub : (_root_.GlobalTheory.BadShare.sqSet g N).filter (fun f => _root_.GlobalTheory.BadShare.degType g f = 0) ⊆ {1}`. Introduce `f hf`. Rewrite `hf` using `[Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]`. Take `⟨⟨hm, -, -, -⟩, h0⟩` from `hf`.

Unfold `_root_.GlobalTheory.BadShare.degType at h0`. Rewrite `h0` using `[Multiset.map_eq_zero]`. Establish `ha` using `prod_normalizedFactors hm.ne_zero`. Rewrite `ha` using `[h0, Multiset.prod_zero]`. Rewrite using `[Finset.mem_singleton]`.

Conclude with `eq_of_monic_of_associated hm monic_one ha.symm`. Establish `hmain : ∑ f ∈ (_root_.GlobalTheory.BadShare.sqSet g N).filter (fun f => _root_.GlobalTheory.BadShare.degType g f = 0), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Use `hmain using 2` and compare the differences between its conclusion and the goal. Use extensionality with `f`.

Simplify using the standard rewrite rules.
-/
private theorem mass_degType_eq_zero_le_one (g : ℕ) [Fact g.Prime] (N : ℕ) :
    _root_.GlobalTheory.BadShare.mass g N (fun f => _root_.GlobalTheory.BadShare.degType g f = 0) ≤ 1 := by
  unfold _root_.GlobalTheory.BadShare.mass
  have hsub : (_root_.GlobalTheory.BadShare.sqSet g N).filter
      (fun f => _root_.GlobalTheory.BadShare.degType g f = 0) ⊆ {1} := by
    intro f hf
    rw [Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet] at hf
    obtain ⟨⟨hm, -, -, -⟩, h0⟩ := hf
    unfold _root_.GlobalTheory.BadShare.degType at h0
    rw [Multiset.map_eq_zero] at h0
    have ha := prod_normalizedFactors hm.ne_zero
    rw [h0, Multiset.prod_zero] at ha
    rw [Finset.mem_singleton]
    exact eq_of_monic_of_associated hm monic_one ha.symm
  have hmain : ∑ f ∈ (_root_.GlobalTheory.BadShare.sqSet g N).filter
      (fun f => _root_.GlobalTheory.BadShare.degType g f = 0),
        ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ ≤ 1 :=
    calc _ ≤ ∑ f ∈ ({1} : Finset (ZMod g)[X]), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ 1 := by simp [_root_.GlobalTheory.BadShare.torusCard, _root_.GlobalTheory.BadShare.degType]
  convert hmain using 2
  ext f
  simp

open Polynomial Classical UniqueFactorizationMonoid in
/- English proof (translation)
Use `set S := (_root_.GlobalTheory.BadShare.sqSet g d).filter Irreducible with hS`. Establish `hX : (X : (ZMod g)[X]) ∉ S`. Simplify using `[hS, _root_.GlobalTheory.BadShare.mem_sqSet]`. Establish `hg : 1 < g` using `(Fact.out : g.Prime).one_lt`. Establish `hmem : ∀ P ∈ insert X S, P.Monic ∧ Irreducible P ∧ P ∣ (X ^ g ^ d - X : (ZMod g)[X])`.

Introduce `P hP`. Break down `Finset.mem_insert.1 hP with rfl | hP` into its components or cases. Use `⟨monic_X, irreducible_X, ?_⟩` and prove the remaining obligations. Conclude with `dvd_sub (dvd_pow_self _ (by positivity)) dvd_rfl`. Rewrite `hP` using `[hS, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]`.

Take `⟨⟨hm, hdeg, -, -⟩, hirr⟩` from `hP`. Use `⟨hm, hirr, ?_⟩` and prove the remaining obligations. Use `(hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := d)).1 (by rw [hdeg])` as an intermediate fact. Simplify `this` using `[Nat.card_zmod]`. Establish `hdvd : ∏ P ∈ insert X S, P ∣ (X ^ g ^ d - X : (ZMod g)[X])`.

Apply `Finset.prod_dvd_of_coprime` to reduce the goal to its premises. Introduce `P hP Q hQ hPQ`. Take `⟨hPm, hPi, -⟩` from `hmem P hP`. Take `⟨hQm, hQi, -⟩` from `hmem Q hQ`. Use `show IsCoprime P Q`.

Use `(hPi.coprime_iff_not_dvd).2 fun h => hPQ ?_` and prove the remaining obligations. Conclude with `eq_of_monic_of_associated hPm hQm (hPi.associated_of_dvd hQi h)`. Introduce `P hP`. Conclude with `(hmem P hP).2.2`. Establish `hle` using `natDegree_le_of_dvd hdvd (FiniteField.X_pow_card_pow_sub_X_ne_zero _ hd.ne' hg)`.

Rewrite `hle` using `[FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ hd.ne' hg, natDegree_prod_of_monic _ _ (fun P hP => (hmem P hP).1), Finset.sum_insert hX, natDegree_X]`. Establish `hsum : ∑ P ∈ S, P.natDegree = d * S.card`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => d), Finset.sum_const, smul_eq_mul, mul_comm]`. Introduce `P hP`. Rewrite `hP` using `[hS, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]`.

Conclude with `hP.1.2.1`. Use linear arithmetic over natural numbers and integers.
-/
private theorem mul_card_irreducible_add_one_le_pow (g : ℕ) [Fact g.Prime] {d : ℕ} (hd : 0 < d) :
    d * ((_root_.GlobalTheory.BadShare.sqSet g d).filter Irreducible).card + 1 ≤ g ^ d := by
  set S := (_root_.GlobalTheory.BadShare.sqSet g d).filter Irreducible with hS
  have hX : (X : (ZMod g)[X]) ∉ S := by
    simp [hS, _root_.GlobalTheory.BadShare.mem_sqSet]
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hmem : ∀ P ∈ insert X S,
      P.Monic ∧ Irreducible P ∧ P ∣ (X ^ g ^ d - X : (ZMod g)[X]) := by
    intro P hP
    rcases Finset.mem_insert.1 hP with rfl | hP
    · refine ⟨monic_X, irreducible_X, ?_⟩
      exact dvd_sub (dvd_pow_self _ (by positivity)) dvd_rfl
    · rw [hS, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet] at hP
      obtain ⟨⟨hm, hdeg, -, -⟩, hirr⟩ := hP
      refine ⟨hm, hirr, ?_⟩
      have := (hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := d)).1 (by rw [hdeg])
      simpa [Nat.card_zmod] using this
  have hdvd : ∏ P ∈ insert X S, P ∣ (X ^ g ^ d - X : (ZMod g)[X]) := by
    apply Finset.prod_dvd_of_coprime
    · intro P hP Q hQ hPQ
      obtain ⟨hPm, hPi, -⟩ := hmem P hP
      obtain ⟨hQm, hQi, -⟩ := hmem Q hQ
      show IsCoprime P Q
      refine (hPi.coprime_iff_not_dvd).2 fun h => hPQ ?_
      exact eq_of_monic_of_associated hPm hQm (hPi.associated_of_dvd hQi h)
    · intro P hP
      exact (hmem P hP).2.2
  have hle := natDegree_le_of_dvd hdvd (FiniteField.X_pow_card_pow_sub_X_ne_zero _ hd.ne' hg)
  rw [FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ hd.ne' hg,
    natDegree_prod_of_monic _ _ (fun P hP => (hmem P hP).1), Finset.sum_insert hX,
    natDegree_X] at hle
  have hsum : ∑ P ∈ S, P.natDegree = d * S.card := by
    rw [Finset.sum_congr rfl (g := fun _ => d), Finset.sum_const, smul_eq_mul, mul_comm]
    intro P hP
    rw [hS, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet] at hP
    exact hP.1.2.1
  omega

open Polynomial Classical UniqueFactorizationMonoid in
/- English proof (translation)
Establish `hg : 1 < g` using `(Fact.out : g.Prime).one_lt`. Establish `h1` using `mul_card_irreducible_add_one_le_pow g hd`. Establish `hpow : 1 < g ^ d` using `Nat.one_lt_pow hd.ne' hg`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => ((g ^ d - 1 : ℕ) : ℝ)⁻¹), Finset.sum_const, nsmul_eq_mul]`. Establish `hq : (0 : ℝ) < ((g ^ d - 1 : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 0 < g ^ d - 1)`.

Establish `hc : ((_root_.GlobalTheory.BadShare.sqSet g d).filter Irreducible).card * d ≤ g ^ d - 1`. Rewrite using `[Nat.mul_comm]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← div_eq_mul_inv, div_le_iff₀ hq, inv_mul_eq_div, le_div_iff₀ (by positivity)]`. Conclude with `hc` after adjusting the coercions.

Introduce `P hP`. Rewrite `hP` using `[Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]`. Rewrite using `[_root_.GlobalTheory.BadShare.torusCard_irreducible hP.2, hP.1.2.1]`.
-/
private theorem sum_inv_torusCard_irreducible_le (g : ℕ) [Fact g.Prime] {d : ℕ} (hd : 0 < d) :
    ∑ P ∈ (_root_.GlobalTheory.BadShare.sqSet g d).filter Irreducible,
      ((_root_.GlobalTheory.BadShare.torusCard g P : ℕ) : ℝ)⁻¹ ≤ (d : ℝ)⁻¹ := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have h1 := mul_card_irreducible_add_one_le_pow g hd
  have hpow : 1 < g ^ d := Nat.one_lt_pow hd.ne' hg
  rw [Finset.sum_congr rfl (g := fun _ => ((g ^ d - 1 : ℕ) : ℝ)⁻¹), Finset.sum_const,
    nsmul_eq_mul]
  · have hq : (0 : ℝ) < ((g ^ d - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < g ^ d - 1)
    have hc : ((_root_.GlobalTheory.BadShare.sqSet g d).filter Irreducible).card * d ≤ g ^ d - 1 := by
      rw [Nat.mul_comm]; omega
    rw [← div_eq_mul_inv, div_le_iff₀ hq, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    exact_mod_cast hc
  · intro P hP
    rw [Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet] at hP
    rw [_root_.GlobalTheory.BadShare.torusCard_irreducible hP.2, hP.1.2.1]

open Polynomial Classical UniqueFactorizationMonoid in
/- English proof (translation)
Unfold `_root_.GlobalTheory.BadShare.mass`. Use `set A := (_root_.GlobalTheory.BadShare.sqSet g N).filter (fun f => _root_.GlobalTheory.BadShare.degType g f = d ::ₘ ν) with hA`. Use `set B := (_root_.GlobalTheory.BadShare.sqSet g (N - d)).filter (fun f => _root_.GlobalTheory.BadShare.degType g f = ν) with hB`. Use `set S := (_root_.GlobalTheory.BadShare.sqSet g d).filter Irreducible with hS`. Establish `hbounds` using `_root_.GlobalTheory.BadShare.torusCard_bounds_mul g`.

Establish `hcount : ∀ f ∈ A, ν.count d + 1 ≤ (S.filter (· ∣ f)).card`. Introduce `f hf`. Rewrite `hf` using `[hA, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]`. Take `⟨⟨hm, -, hsq, hc0⟩, htype⟩` from `hf`. Establish `hnd` using `(squarefree_iff_nodup_normalizedFactors hm.ne_zero).1 hsq`.

Establish `hc : ((normalizedFactors f).filter (fun P => d = P.natDegree)).card = ν.count d + 1`. Rewrite using `[← Multiset.count_cons_self d ν, ← htype]`. Unfold `_root_.GlobalTheory.BadShare.degType`. Rewrite using `[Multiset.count_map]`. Rewrite using `[← hc, ← Multiset.toFinset_card_of_nodup (hnd.filter _)]`.

Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `P hP`. Rewrite `hP` using `[Multiset.mem_toFinset, Multiset.mem_filter]`. Take `⟨hP, hdeg⟩` from `hP`. Establish `hirr` using `irreducible_of_normalized_factor P hP`.

Establish `hdvd` using `dvd_of_mem_normalizedFactors hP`. Establish `hPm : P.Monic`. Rewrite using `[← normalize_normalized_factor P hP]`. Conclude with `monic_normalize hirr.ne_zero`. Rewrite using `[Finset.mem_filter, hS, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]`.

Use `⟨⟨⟨hPm, hdeg.symm, hirr.squarefree, fun h0 => hc0 ?_⟩, hirr⟩, hdvd⟩` and prove the remaining obligations. Conclude with `X_dvd_iff.1 ((X_dvd_iff.2 h0).trans hdvd)`. Establish `step1 : ((ν.count d + 1 : ℕ) : ℝ) * ∑ f ∈ A, ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ ≤ ∑ f ∈ A, ∑ P ∈ S.filter (· ∣ f), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun f hf => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Conclude with `mul_le_mul_of_nonneg_right (by exact_mod_cast hcount f hf) (by positivity)`. Establish `step2 : ∑ f ∈ A, ∑ P ∈ S.filter (· ∣ f), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ = ∑ P ∈ S, ∑ f ∈ A.filter (P ∣ ·), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹` using `Finset.sum_comm' (by intro f P; simp only [Finset.mem_filter]; tauto)`. Establish `step3 : ∀ P ∈ S, ∑ f ∈ A.filter (P ∣ ·), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ ≤ ((_root_.GlobalTheory.BadShare.torusCard g P : ℕ) : ℝ)⁻¹ * ∑ h ∈ B, ((_root_.GlobalTheory.BadShare.torusCard g h : ℕ) : ℝ)⁻¹`. Introduce `P hP`.

Rewrite `hP` using `[hS, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]`. Take `⟨⟨hPm, hPdeg, -, -⟩, hPirr⟩` from `hP`. Establish `hP0 : P ≠ 0` using `hPm.ne_zero`. Establish `hfac : ∀ f ∈ A.filter (P ∣ ·), P * (f /ₘ P) = f`. Introduce `f hf`.

Rewrite `hf` using `[Finset.mem_filter]`. Use `modByMonic_add_div f P` as an intermediate fact. Rewrite `this` using `[(modByMonic_eq_zero_iff_dvd hPm).2 hf.2, zero_add]`. Conclude with `this`. Establish `hne : ∀ f ∈ A.filter (P ∣ ·), f /ₘ P ≠ 0`.

Introduce `f hf h0`. Establish `h` using `hfac f hf`. Rewrite `h` using `[h0, mul_zero]`. Rewrite `hf` using `[Finset.mem_filter, hA, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]`. Conclude with `hf.1.1.1.ne_zero h.symm`.

Establish `himg : (A.filter (P ∣ ·)).image (· /ₘ P) ⊆ B`. Introduce `h hh`. Rewrite `hh` using `[Finset.mem_image]`. Take `⟨f, hf, rfl⟩` from `hh`. Use `show f /ₘ P ∈ B`.

Establish `hfac'` using `hfac f hf`. Establish `hh0` using `hne f hf`. Rewrite `hf` using `[Finset.mem_filter, hA, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]`. Take `⟨⟨⟨hfm, hfdeg, hfsq, hfc⟩, htype⟩, -⟩` from `hf`. Rewrite `hfm`, `hfdeg`, `hfsq`, `hfc`, `htype` using `[← hfac']`.

Rewrite using `[hB, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]`. Use `⟨⟨hPm.of_mul_monic_left hfm, ?_, hfsq.of_mul_right, fun h0 => hfc ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite `hfdeg` using `[natDegree_mul hP0 hh0, hPdeg]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[mul_coeff_zero, h0, mul_zero]`.

Rewrite `htype` using `[(hbounds.2.1 P _ hP0 hh0).1, (hbounds.2.2 P hPirr).1, hPdeg, Multiset.singleton_add]`. Conclude with `(Multiset.cons_inj_right d).1 htype`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun f hf => ?_` and prove the remaining obligations. Use `conv_lhs => rw [← hfac f hf]`.

Rewrite using `[_root_.GlobalTheory.BadShare.torusCard_mul hP0 (hne f hf), Nat.cast_mul, mul_inv]`. Use `_ = ((_root_.GlobalTheory.BadShare.torusCard g P : ℕ) : ℝ)⁻¹ * ∑ h ∈ (A.filter (P ∣ ·)).image (· /ₘ P), ((_root_.GlobalTheory.BadShare.torusCard g h : ℕ) : ℝ)⁻¹ := by`. Rewrite using `[← Finset.mul_sum, Finset.sum_image]`. Introduce `f₁ hf₁ f₂ hf₂ h₁₂`. Combine the equalities or inequalities in the displayed calculation.

Use `_ ≤ ((_root_.GlobalTheory.BadShare.torusCard g P : ℕ) : ℝ)⁻¹ * ∑ h ∈ B, ((_root_.GlobalTheory.BadShare.torusCard g h : ℕ) : ℝ)⁻¹ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)) (by positivity)`. Establish `hmain : ((ν.count d + 1 : ℕ) : ℝ) * ∑ f ∈ A, ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ ≤ (d : ℝ)⁻¹ * ∑ h ∈ B, ((_root_.GlobalTheory.BadShare.torusCard g h : ℕ) : ℝ)⁻¹` using `calc ((ν.count d + 1 : ℕ) : ℝ) * ∑ f ∈ A, ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ ≤ ∑ f ∈ A, ∑ P ∈ S.filter (· ∣ f), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ := step1 _ = ∑ P ∈ S, ∑ f ∈ A.filter (P ∣ ·), ((_root_.GlobalTheory.BadShare.torusCard g …`. Apply the tactic sequence `convert hmain using 3 <;> (ext f; simp [hA, hB])`.
-/
private theorem count_succ_mul_mass_cons_le (g : ℕ) [Fact g.Prime] (N d : ℕ) (ν : Multiset ℕ)
    (hd : 0 < d) :
    ((ν.count d + 1 : ℕ) : ℝ) *
        _root_.GlobalTheory.BadShare.mass g N (fun f => _root_.GlobalTheory.BadShare.degType g f = d ::ₘ ν) ≤
      (d : ℝ)⁻¹ *
        _root_.GlobalTheory.BadShare.mass g (N - d) (fun f => _root_.GlobalTheory.BadShare.degType g f = ν) := by
  unfold _root_.GlobalTheory.BadShare.mass
  set A := (_root_.GlobalTheory.BadShare.sqSet g N).filter
    (fun f => _root_.GlobalTheory.BadShare.degType g f = d ::ₘ ν) with hA
  set B := (_root_.GlobalTheory.BadShare.sqSet g (N - d)).filter
    (fun f => _root_.GlobalTheory.BadShare.degType g f = ν) with hB
  set S := (_root_.GlobalTheory.BadShare.sqSet g d).filter Irreducible with hS
  have hbounds := _root_.GlobalTheory.BadShare.torusCard_bounds_mul g
  have hcount : ∀ f ∈ A, ν.count d + 1 ≤ (S.filter (· ∣ f)).card := by
    intro f hf
    rw [hA, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet] at hf
    obtain ⟨⟨hm, -, hsq, hc0⟩, htype⟩ := hf
    have hnd := (squarefree_iff_nodup_normalizedFactors hm.ne_zero).1 hsq
    have hc : ((normalizedFactors f).filter (fun P => d = P.natDegree)).card = ν.count d + 1 := by
      rw [← Multiset.count_cons_self d ν, ← htype]
      unfold _root_.GlobalTheory.BadShare.degType
      rw [Multiset.count_map]
    rw [← hc, ← Multiset.toFinset_card_of_nodup (hnd.filter _)]
    apply Finset.card_le_card
    intro P hP
    rw [Multiset.mem_toFinset, Multiset.mem_filter] at hP
    obtain ⟨hP, hdeg⟩ := hP
    have hirr := irreducible_of_normalized_factor P hP
    have hdvd := dvd_of_mem_normalizedFactors hP
    have hPm : P.Monic := by
      rw [← normalize_normalized_factor P hP]
      exact monic_normalize hirr.ne_zero
    rw [Finset.mem_filter, hS, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]
    refine ⟨⟨⟨hPm, hdeg.symm, hirr.squarefree, fun h0 => hc0 ?_⟩, hirr⟩, hdvd⟩
    exact X_dvd_iff.1 ((X_dvd_iff.2 h0).trans hdvd)
  have step1 : ((ν.count d + 1 : ℕ) : ℝ) * ∑ f ∈ A, ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ ≤
      ∑ f ∈ A, ∑ P ∈ S.filter (· ∣ f), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun f hf => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount f hf) (by positivity)
  have step2 : ∑ f ∈ A, ∑ P ∈ S.filter (· ∣ f), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ =
      ∑ P ∈ S, ∑ f ∈ A.filter (P ∣ ·), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ :=
    Finset.sum_comm' (by intro f P; simp only [Finset.mem_filter]; tauto)
  have step3 : ∀ P ∈ S, ∑ f ∈ A.filter (P ∣ ·), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ ≤
      ((_root_.GlobalTheory.BadShare.torusCard g P : ℕ) : ℝ)⁻¹ *
        ∑ h ∈ B, ((_root_.GlobalTheory.BadShare.torusCard g h : ℕ) : ℝ)⁻¹ := by
    intro P hP
    rw [hS, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet] at hP
    obtain ⟨⟨hPm, hPdeg, -, -⟩, hPirr⟩ := hP
    have hP0 : P ≠ 0 := hPm.ne_zero
    have hfac : ∀ f ∈ A.filter (P ∣ ·), P * (f /ₘ P) = f := by
      intro f hf
      rw [Finset.mem_filter] at hf
      have := modByMonic_add_div f P
      rw [(modByMonic_eq_zero_iff_dvd hPm).2 hf.2, zero_add] at this
      exact this
    have hne : ∀ f ∈ A.filter (P ∣ ·), f /ₘ P ≠ 0 := by
      intro f hf h0
      have h := hfac f hf
      rw [h0, mul_zero] at h
      rw [Finset.mem_filter, hA, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet] at hf
      exact hf.1.1.1.ne_zero h.symm
    have himg : (A.filter (P ∣ ·)).image (· /ₘ P) ⊆ B := by
      intro h hh
      rw [Finset.mem_image] at hh
      obtain ⟨f, hf, rfl⟩ := hh
      show f /ₘ P ∈ B
      have hfac' := hfac f hf
      have hh0 := hne f hf
      rw [Finset.mem_filter, hA, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet] at hf
      obtain ⟨⟨⟨hfm, hfdeg, hfsq, hfc⟩, htype⟩, -⟩ := hf
      rw [← hfac'] at hfm hfdeg hfsq hfc htype
      rw [hB, Finset.mem_filter, _root_.GlobalTheory.BadShare.mem_sqSet]
      refine ⟨⟨hPm.of_mul_monic_left hfm, ?_, hfsq.of_mul_right, fun h0 => hfc ?_⟩, ?_⟩
      · rw [natDegree_mul hP0 hh0, hPdeg] at hfdeg
        omega
      · rw [mul_coeff_zero, h0, mul_zero]
      · rw [(hbounds.2.1 P _ hP0 hh0).1, (hbounds.2.2 P hPirr).1, hPdeg,
          Multiset.singleton_add] at htype
        exact (Multiset.cons_inj_right d).1 htype
    calc ∑ f ∈ A.filter (P ∣ ·), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹
        = ∑ f ∈ A.filter (P ∣ ·), ((_root_.GlobalTheory.BadShare.torusCard g P : ℕ) : ℝ)⁻¹ *
            ((_root_.GlobalTheory.BadShare.torusCard g (f /ₘ P) : ℕ) : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl fun f hf => ?_
          conv_lhs => rw [← hfac f hf]
          rw [_root_.GlobalTheory.BadShare.torusCard_mul hP0 (hne f hf), Nat.cast_mul, mul_inv]
      _ = ((_root_.GlobalTheory.BadShare.torusCard g P : ℕ) : ℝ)⁻¹ *
            ∑ h ∈ (A.filter (P ∣ ·)).image (· /ₘ P),
              ((_root_.GlobalTheory.BadShare.torusCard g h : ℕ) : ℝ)⁻¹ := by
          rw [← Finset.mul_sum, Finset.sum_image]
          intro f₁ hf₁ f₂ hf₂ h₁₂
          calc f₁ = P * (f₁ /ₘ P) := (hfac f₁ hf₁).symm
            _ = P * (f₂ /ₘ P) := by rw [show f₁ /ₘ P = f₂ /ₘ P from h₁₂]
            _ = f₂ := hfac f₂ hf₂
      _ ≤ ((_root_.GlobalTheory.BadShare.torusCard g P : ℕ) : ℝ)⁻¹ *
            ∑ h ∈ B, ((_root_.GlobalTheory.BadShare.torusCard g h : ℕ) : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity))
            (by positivity)
  have hmain : ((ν.count d + 1 : ℕ) : ℝ) * ∑ f ∈ A, ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ ≤
      (d : ℝ)⁻¹ * ∑ h ∈ B, ((_root_.GlobalTheory.BadShare.torusCard g h : ℕ) : ℝ)⁻¹ := calc
    ((ν.count d + 1 : ℕ) : ℝ) * ∑ f ∈ A, ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹
      ≤ ∑ f ∈ A, ∑ P ∈ S.filter (· ∣ f), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ := step1
    _ = ∑ P ∈ S, ∑ f ∈ A.filter (P ∣ ·), ((_root_.GlobalTheory.BadShare.torusCard g f : ℕ) : ℝ)⁻¹ := step2
    _ ≤ ∑ P ∈ S, ((_root_.GlobalTheory.BadShare.torusCard g P : ℕ) : ℝ)⁻¹ *
          ∑ h ∈ B, ((_root_.GlobalTheory.BadShare.torusCard g h : ℕ) : ℝ)⁻¹ := Finset.sum_le_sum step3
    _ = (∑ P ∈ S, ((_root_.GlobalTheory.BadShare.torusCard g P : ℕ) : ℝ)⁻¹) *
          ∑ h ∈ B, ((_root_.GlobalTheory.BadShare.torusCard g h : ℕ) : ℝ)⁻¹ := by rw [Finset.sum_mul]
    _ ≤ (d : ℝ)⁻¹ * ∑ h ∈ B, ((_root_.GlobalTheory.BadShare.torusCard g h : ℕ) : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (sum_inv_torusCard_irreducible_le g hd)
            (Finset.sum_nonneg fun _ _ => by positivity)
  convert hmain using 3 <;> (ext f; simp [hA, hB])

open Polynomial Classical UniqueFactorizationMonoid in
/- English proof (translation)
Establish `hsub : ν.toFinset ⊆ (d ::ₘ ν).toFinset` using `fun e he => by simp_all`. Rewrite using `[Finset.prod_subset hsub (fun e _ he => by`. Simplify `he)])]` using `[Multiset.count_eq_zero.2 (by simpa`. Establish `hterm : ∀ e ∈ (d ::ₘ ν).toFinset, (e : ℝ) ^ (d ::ₘ ν).count e * ((d ::ₘ ν).count e).factorial = ((e : ℝ) ^ ν.count e * (ν.count e).factorial) * (if e = d then (d : ℝ) * (ν.count d + 1) else 1)`. Introduce `e _`.

Distinguish the cases in `h : e = d`. Substitute `h` using the available equality. Simplify using `only [if_pos rfl, Multiset.count_cons_self, pow_succ, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[Multiset.count_cons_of_ne h, h]`. Rewrite using `[Finset.prod_congr rfl hterm, Finset.prod_mul_distrib]`. Simplify using the standard rewrite rules.
-/
private theorem prod_pow_count_mul_factorial_cons (d : ℕ) (ν : Multiset ℕ) :
    ∏ e ∈ (d ::ₘ ν).toFinset, ((e : ℝ) ^ (d ::ₘ ν).count e * ((d ::ₘ ν).count e).factorial) =
      (∏ e ∈ ν.toFinset, ((e : ℝ) ^ ν.count e * (ν.count e).factorial)) *
        ((d : ℝ) * (ν.count d + 1)) := by
  have hsub : ν.toFinset ⊆ (d ::ₘ ν).toFinset := fun e he => by simp_all
  rw [Finset.prod_subset hsub (fun e _ he => by
    simp [Multiset.count_eq_zero.2 (by simpa using he)])]
  have hterm : ∀ e ∈ (d ::ₘ ν).toFinset,
      (e : ℝ) ^ (d ::ₘ ν).count e * ((d ::ₘ ν).count e).factorial =
        ((e : ℝ) ^ ν.count e * (ν.count e).factorial) *
          (if e = d then (d : ℝ) * (ν.count d + 1) else 1) := by
    intro e _
    by_cases h : e = d
    · subst h
      simp only [if_pos rfl, Multiset.count_cons_self, pow_succ, Nat.factorial_succ]
      push_cast
      ring
    · simp [Multiset.count_cons_of_ne h, h]
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib]
  simp

open Polynomial Classical UniqueFactorizationMonoid in

/- English proof (translation)
Introduce `g _ N μ`. Proceed by induction on `μ using Multiset.induction_on generalizing N with`. Consider the case `empty => simpa using mass_degType_eq_zero_le_one g N`. Consider the case `cons d ν ih`. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases.

Establish `hle : _root_.GlobalTheory.BadShare.mass g N (fun f => _root_.GlobalTheory.BadShare.degType g f = 0 ::ₘ ν) ≤ _root_.GlobalTheory.BadShare.mass g N (fun _ => False)` using `_root_.GlobalTheory.BadShare.mass_mono fun f hf hμ => lt_irrefl 0 (((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).1 N f hf).2.2.2 0 (hμ ▸ Multiset.mem_cons_self 0 ν))`. Establish `h0 : _root_.GlobalTheory.BadShare.mass g N (fun _ => False) = 0`. Unfold `_root_.GlobalTheory.BadShare.mass`. Simplify using the standard rewrite rules. Use `hle.trans (h0.le.trans (inv_nonneg.2 (Finset.prod_nonneg fun _ _ => by positivity)))` and prove the remaining obligations.

Establish `key` using `count_succ_mul_mass_cons_le g N d ν hd`. Establish `hc : (0 : ℝ) < ((ν.count d + 1 : ℕ) : ℝ)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[le_div_iff₀ hc, mul_comm]`. Conclude with `key`.

Use `_ ≤ (d : ℝ)⁻¹ * (∏ e ∈ ν.toFinset, ((e : ℝ) ^ ν.count e * (ν.count e).factorial))⁻¹ / ((ν.count d + 1 : ℕ) : ℝ) := by gcongr`. Conclude with `ih (N - d)`. Use `_ = _ := by`. Rewrite using `[prod_pow_count_mul_factorial_cons]`. Use `push_cast`.

Rewrite using `[mul_inv, mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.BadShare.mass_degType_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (μ : Multiset ℕ),
    (_root_.GlobalTheory.BadShare.mass g N fun f => _root_.GlobalTheory.BadShare.degType g f = μ) ≤
      (∏ d ∈ μ.toFinset, ((d : ℝ) ^ μ.count d * (μ.count d).factorial))⁻¹ := by
  intro g _ N μ
  induction μ using Multiset.induction_on generalizing N with
  | empty => simpa using mass_degType_eq_zero_le_one g N
  | cons d ν ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have hle : _root_.GlobalTheory.BadShare.mass g N
            (fun f => _root_.GlobalTheory.BadShare.degType g f = 0 ::ₘ ν) ≤
          _root_.GlobalTheory.BadShare.mass g N (fun _ => False) :=
        _root_.GlobalTheory.BadShare.mass_mono fun f hf hμ =>
          lt_irrefl 0 (((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).1 N f hf).2.2.2 0
            (hμ ▸ Multiset.mem_cons_self 0 ν))
      have h0 : _root_.GlobalTheory.BadShare.mass g N (fun _ => False) = 0 := by
        unfold _root_.GlobalTheory.BadShare.mass
        simp
      refine hle.trans (h0.le.trans (inv_nonneg.2 (Finset.prod_nonneg fun _ _ => by positivity)))
    · have key := count_succ_mul_mass_cons_le g N d ν hd
      have hc : (0 : ℝ) < ((ν.count d + 1 : ℕ) : ℝ) := by positivity
      calc _root_.GlobalTheory.BadShare.mass g N (fun f => _root_.GlobalTheory.BadShare.degType g f = d ::ₘ ν)
          ≤ (d : ℝ)⁻¹ * _root_.GlobalTheory.BadShare.mass g (N - d)
              (fun f => _root_.GlobalTheory.BadShare.degType g f = ν) / ((ν.count d + 1 : ℕ) : ℝ) := by
            rw [le_div_iff₀ hc, mul_comm]
            exact key
        _ ≤ (d : ℝ)⁻¹ * (∏ e ∈ ν.toFinset, ((e : ℝ) ^ ν.count e * (ν.count e).factorial))⁻¹ /
              ((ν.count d + 1 : ℕ) : ℝ) := by
            gcongr
            exact ih (N - d)
        _ = _ := by
            rw [prod_pow_count_mul_factorial_cons]
            push_cast
            rw [mul_inv, mul_inv]
            ring

end GlobalTheory.BadShare
