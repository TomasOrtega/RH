import Formalism.GaussJetBounds.GaussJetProofs.AsmRDotAddRight

noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨m, rfl⟩` from `hodd`. Establish `hnat : ∀ k : ℕ, ‖(k : K)‖ ≤ 1`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Use `push_cast`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))`.

Establish `h1 : (1 : K) = ((2 * m + 1 : ℕ) : K) - 2 * (m : K)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ‖(2 : K) * (m : K)‖ < 1`. Rewrite using `[norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3 : ‖(1 : K)‖ < 1`. Rewrite using `[h1, sub_eq_add_neg]`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hpi (by rwa [norm_neg]))`. Simplify using `at h3`.
-/
theorem asmOne_one_le_norm_two {K : Type u} [NormedField K] [IsUltrametricDist K] {l : ℕ}
    (hodd : Odd l) (hpi : ‖(l : K)‖ < 1) : 1 ≤ ‖(2 : K)‖ := by
  by_contra h
  push_neg at h
  obtain ⟨m, rfl⟩ := hodd
  have hnat : ∀ k : ℕ, ‖(k : K)‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))
  have h1 : (1 : K) = ((2 * m + 1 : ℕ) : K) - 2 * (m : K) := by
    push_cast
    ring
  have h2 : ‖(2 : K) * (m : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(2 : K)‖ * ‖(m : K)‖ ≤ ‖(2 : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hnat m) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact h
  have h3 : ‖(1 : K)‖ < 1 := by
    rw [h1, sub_eq_add_neg]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hpi (by rwa [norm_neg]))
  simp at h3

/- English proof (translation)
Introduce `n`. Unfold `MonoWtGe`. Rewrite using `[map_sum]`. Simplify using `only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]`. Distinguish the cases in `hn : ∃ i, n = Finsupp.single i 1`.

Take `⟨i, rfl⟩` from `hn`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[if_pos rfl, mul_one, asmR_dot_single]`. Simplify using `only [Nat.cast_one, one_mul, sub_self, Real.rpow_zero]`. Conclude with `hc i`.

Introduce `j _ hj`. Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Conclude with `hj ((Finsupp.single_left_injective one_ne_zero) h).symm`. Simplify using the standard rewrite rules.

Use `push_neg at hn`. Rewrite using `[Finset.sum_eq_zero (fun i _ => by rw [if_neg (hn i), mul_zero]), norm_zero]`. Conclude with `Real.rpow_nonneg h0.le _`.
-/
theorem asmOne_lin_wt {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v} [Fintype ι]
    {pi : ℝ} (h0 : 0 < pi) (c : ι → K) (hc : ∀ i, ‖c i‖ ≤ 1) (t : ℝ) :
    WtGe pi (fun _ : ι => t) t (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) := by
  classical
  intro n
  unfold MonoWtGe
  rw [map_sum]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  by_cases hn : ∃ i, n = Finsupp.single i 1
  · obtain ⟨i, rfl⟩ := hn
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_one, asmR_dot_single]
      simp only [Nat.cast_one, one_mul, sub_self, Real.rpow_zero]
      exact hc i
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      exact hj ((Finsupp.single_left_injective one_ne_zero) h).symm
    · simp
  · push_neg at hn
    rw [Finset.sum_eq_zero (fun i _ => by rw [if_neg (hn i), mul_zero]), norm_zero]
    exact Real.rpow_nonneg h0.le _

/- English proof (translation)
Simplify using `[map_sum]`.
-/
theorem asmOne_lin_const {K : Type u} [NormedField K] {ι : Type v} [Fintype ι] (c : ι → K) :
    MvPowerSeries.constantCoeff (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) = 0 := by
  simp [map_sum]

/- English proof (translation)
Introduce `n`. Establish `h` using `hf n`. Unfold `MonoWtGe at h ⊢`. Rewrite using `[map_smul, smul_eq_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem asmOne_smul_wt {K : Type u} [NormedField K] {ι : Type v} {pi : ℝ} {r : ι → ℝ} {w : ℝ}
    {c : K} (hc : ‖c‖ ≤ 1) {f : MvPowerSeries ι K} (hf : WtGe pi r w f) :
    WtGe pi r w (c • f) := by
  intro n
  have h := hf n
  unfold MonoWtGe at h ⊢
  rw [map_smul, smul_eq_mul, norm_mul]
  calc ‖c‖ * ‖MvPowerSeries.coeff n f‖ ≤ 1 * ‖MvPowerSeries.coeff n f‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h

/- English proof (translation)
Use `first`. Consider the case `simp [hf]`. Consider the case `rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]`.
-/
theorem asmOne_smul_const {K : Type u} [NormedField K] {ι : Type v} (c : K)
    {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (c • f) = 0 := by
  first
    | simp [hf]
    | rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem asmOne_zmod2 : ∀ s s' a b : ZMod 2, s.val % 2 = 0 → s'.val % 2 = 1 → s + a = s' + b →
    a + b = 1 := by
  decide

/- English proof (translation)
Introduce `K _ _ _ l N0 N1 hl hodd hpi K0 hK0 ζ hζ be hbe ep hep ι _ _ M hM g hg0 hgl U hU sgn hsgn κ`. Establish `h2n : 1 ≤ ‖(2 : K)‖` using `asmOne_one_le_norm_two hodd hpi`. Use `set π : ℝ := ‖(l : K)‖ with hπdef`. Establish `hl3 : 3 ≤ l`. Take `⟨m, rfl⟩` from `hodd`.

Break down `m with _ | m` into its components or cases. Conclude with `absurd hl Nat.not_prime_one`. Use linear arithmetic over natural numbers and integers. Establish `hπ0 : 0 < π`. Rewrite using `[hπdef, norm_pos_iff]`.

Conclude with `hl.ne_zero` after adjusting the coercions. Establish `hπ1 : π ≤ 1` using `hpi.le`. Establish `hlR : (3 : ℝ) ≤ l` using `by exact_mod_cast hl3`. Establish `hl1 : (l : ℝ) - 1 ≠ 0` using `by linarith`. Establish `hl2 : (l : ℝ) ^ 2 - 1 ≠ 0` using `by nlinarith`.

Establish `hl2p : 0 < (l : ℝ) ^ 2 - 1` using `by nlinarith`. Take `⟨hOR1, hOR2⟩` from `hOR l hl3`. Establish `hrho0 : 0 ≤ rho l`. Unfold `rho`. Check the signs of the components of the expression.

Establish `hrg : rho l ≤ gam l`. Unfold `rho gam`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : 1 / ((l : ℝ) - 1) - gam l = rho l`.

Unfold `rho gam`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `wt_sum : ∀ (r : ι → ℝ) (w : ℝ) (s : Finset (Fin N0 × Fin N1)) (f : Fin N0 × Fin N1 → MvPowerSeries ι K), (∀ x ∈ s, WtGe π r w (f x)) → WtGe π r w (∑ x ∈ s, f x)`. Introduce `r w s f`.

Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_ n`. Unfold `MonoWtGe`. Rewrite using `[Finset.sum_empty, map_zero, norm_zero]`. Conclude with `Real.rpow_nonneg hπ0.le _`.

Introduce `a s ha ih hf n`. Rewrite using `[Finset.sum_insert ha]`. Establish `h1` using `hf a (Finset.mem_insert_self a s) n`. Establish `h2` using `ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)) n`. Unfold `MonoWtGe at h1 h2 ⊢`.

Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)`. Establish `cc_subst : ∀ (a : ZMod 2 → MvPowerSeries ι K), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) → ∀ f : MvPowerSeries (ZMod 2) K, MvPowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0`. Introduce `a ha f hf`. Establish `hs : MvPowerSeries.HasSubst a` using `by first`.

Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero`. Rewrite using `[MvPowerSeries.constantCoeff_subst hs]`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises.

Introduce `d`. Distinguish the cases in `hd : d = 0`. Substitute `hd` using the available equality. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hd (Finsupp.ext h)`. Establish `h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0`. Rewrite using `[Finsupp.prod, map_prod]`.

Conclude with `Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs') (by rw [map_pow, ha, zero_pow hs'])`. Rewrite using `[h0, smul_zero]`. Establish `hbe0 : MvPowerSeries.constantCoeff be = 0`. Assume the negation of the conclusion as `h`. Establish `h'` using `hbe.2.2.1 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])`.

Conclude with `absurd h'.1 (by simp [degE])`. Establish `hUw : WtGe π (fun _ => rho l) 0 U`. Introduce `n`. Unfold `MonoWtGe`. Use `(hU n).trans ?_` and prove the remaining obligations.

Conclude with `Real.one_le_rpow_of_pos_of_le_one_of_nonpos hπ0 hπ1 (by linarith [asmR_dot_nonneg n (r := fun _ => rho l) (fun _ => hrho0)])`. Establish `hlog : ∀ x, oneLog (K` using `K) l x = genLog (K := K) l id x := fun x => (hB K l 2 N0 N1).2.2 x`. Establish `hgw : ∀ x, WtGe π (fun _ => rho l) (rho l) (g x)` using `hG K l hl hpi (Fin N0 × Fin N1) id g hg0 (fun x => by rw [← hlog x]; exact hgl x)`. Establish `hGU : WtGe π (fun _ => rho l) 0 (MvPowerSeries.subst g U)` using `hW0 K π hπ0 hpi (Fin N0 × Fin N1) (Fin N0 × Fin N1) g (fun _ => rho l) (fun _ => rho l) 0 U hg0 hgw hUw`. Establish `hlinw : ∀ (t : ℝ) x, WtGe π (fun _ : ι => t) t (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i)` using `fun t x => asmOne_lin_wt hπ0 (M x) (hM x) t`.

Establish `hlinA : ∀ x, WtGe π (fun _ : ι => gam l) (rho l) (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i)` using `fun x => (hRM K π hπ0 hpi ι (fun _ => rho l) (fun _ => gam l) (rho l) (fun _ => hrg)).1 _ (hlinw (rho l) x)`. Establish `hA : WtGe π (fun _ : ι => gam l) 0 (MvPowerSeries.subst (fun x => ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) (MvPowerSeries.subst g U))` using `hW1 K π hπ0 hpi (Fin N0 × Fin N1) ι _ (fun _ => rho l) (fun _ => gam l) 0 _ (fun x => asmOne_lin_const (M x)) hlinA hGU`. Take `⟨hS1, hS2⟩` from `hS K l 2 hl hodd le_rfl even_two hpi K0 hK0 ζ hζ be hbe`. Establish `hbeW : WtGe π (fun _ : ZMod 2 => gam l) (1 / ((l : ℝ) - 1)) be`. Introduce `n`.

Distinguish the cases in `hbi : IsBiPower l n`. Take `⟨s, s', α, β, hs, hs', _, hsum, rfl⟩` from `hbi`. Establish `h1` using `hS1 (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))`. Unfold `MonoWtGe at h1 ⊢`. Establish `hodd' : Odd (α + β)`.

Establish `h` using `asmOne_zmod2 s s' α β hs hs' hsum`. Establish `h' : ((α + β : ℕ) : ZMod 2) = 1`. Use `push_cast`. Conclude with `h`. Establish `h''` using `congrArg ZMod.val h'`.

Rewrite `h''` using `[ZMod.val_natCast]`. Conclude with `Nat.odd_iff.2 (h''.trans (by decide))`. Establish `hD` using `hOR1 α β hodd'`. Establish `e1 : dot (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) (fun _ : ZMod 2 => rho l) = ((l : ℝ) ^ α + (l : ℝ) ^ β) * rho l`. Rewrite using `[show Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) = pureMon l s s' α β from rfl, asmR_dot_pureMon]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : dot (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) (fun _ : ZMod 2 => gam l) = ((l : ℝ) ^ α + (l : ℝ) ^ β) * gam l`. Rewrite using `[show Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) = pureMon l s s' α β from rfl, asmR_dot_pureMon]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e1]`.

Rewrite using `[e2]`. Use `h1.trans (Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1 ?_)` and prove the remaining obligations. Establish `hg : gam l - rho l = 1 / ((l : ℝ) + 1)` using `by linarith [hOR2]`. Establish `h3 : 1 ≤ ((l : ℝ) ^ α + (l : ℝ) ^ β) * (gam l - rho l)`. Rewrite using `[hg, mul_one_div]`.

Conclude with `hD`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `asmR_monoWtGe_rad hπ0 hπ1 (fun _ => hrg) (hS2 n hbi)`. Establish `haw : ∀ x (s : ZMod 2), WtGe π (fun _ : ι => gam l) (gam l) ((if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i)`. Introduce `x s`.

Use `asmOne_smul_wt ?_ (hlinw (gam l) x)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [hep]`. Establish `hac : ∀ x (s : ZMod 2), MvPowerSeries.constantCoeff ((if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) = 0` using `fun x s => asmOne_smul_const _ (asmOne_lin_const (M x))`. Establish `hBx : ∀ x, WtGe π (fun _ : ι => gam l) (1 / ((l : ℝ) - 1)) (MvPowerSeries.subst (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be)` using `fun x => hW1 K π hπ0 hpi (ZMod 2) ι _ (fun _ => gam l) (fun _ => gam l) _ be (hac x) (haw x) hbeW`. Apply the tactic sequence `have hsgn1 : ‖sgn‖ = 1 := by rcases hsgn with rfl | rfl <;> simp`.

Establish `hsgn2 : ‖sgn / 2‖ ≤ 1`. Rewrite using `[norm_div, hsgn1]`. Conclude with `div_le_one_of_le₀ h2n (by positivity)`. Establish `hBw` using `asmOne_smul_wt hsgn2 (wt_sum _ _ Finset.univ _ (fun x _ => hBx x))`. Establish `hBc : MvPowerSeries.constantCoeff ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be) = 0`.

Use `asmOne_smul_const _ ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun x _ => cc_subst _ (hac x) be hbe0`. Establish `hExp` using `hE K l hl hpi ι (fun _ => gam l) κ _ hBc (fun n _ => hBw n)`. Establish `hMul` using `hMW K π hπ0 ι (fun _ => gam l) 0 0 κ _ _ (fun n _ => hA n) hExp`.

Establish `hk` using `hMul κ le_rfl`. Establish `hf` using `hF K l hl hpi ι κ`. Unfold `MonoWtGe at hk`. Establish `hdeg : (κ.degree : ℝ) = ∑ i, (κ i : ℝ)`. Rewrite using `[Finsupp.degree_eq_sum]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `e : (∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - ∑ i, (κ i : ℝ) * gam l = rho l * ∑ i, (κ i : ℝ)`. Rewrite using `[← Finset.sum_sub_distrib, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← key]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[norm_mul]`. Use `(mul_le_mul hf hk (norm_nonneg _) (Real.rpow_nonneg hπ0.le _)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← Real.rpow_add hπ0, asmR_dot_fintype, hdeg]`.

Use `congr 1`. Use `beta_reduce`. Combine the linear relations using `[e]`.
-/
theorem oneLetterR_of (hS : LemmaS.{u}) (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u})
    (hW1 : SubstWt.{u, 0, v}) (hW0 : SubstWt.{u, 0, 0}) (hRM : RadMono.{u, v})
    (hMW : MulWtLe.{u, v}) (hE : ExpWtLe.{u, v}) (hF : FactVal.{u, v})
    (hOR : OneLetterRadius) : OneLetterR.{u, v} := by
  intro K _ _ _ l N0 N1 hl hodd hpi K0 hK0 ζ hζ be hbe ep hep ι _ _ M hM g hg0 hgl U hU sgn hsgn κ
  classical
  have h2n : 1 ≤ ‖(2 : K)‖ := asmOne_one_le_norm_two hodd hpi
  set π : ℝ := ‖(l : K)‖ with hπdef
  have hl3 : 3 ≤ l := by
    obtain ⟨m, rfl⟩ := hodd
    rcases m with _ | m
    · exact absurd hl Nat.not_prime_one
    · omega
  have hπ0 : 0 < π := by
    rw [hπdef, norm_pos_iff]
    exact_mod_cast hl.ne_zero
  have hπ1 : π ≤ 1 := hpi.le
  have hlR : (3 : ℝ) ≤ l := by exact_mod_cast hl3
  have hl1 : (l : ℝ) - 1 ≠ 0 := by linarith
  have hl2 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hl2p : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  obtain ⟨hOR1, hOR2⟩ := hOR l hl3
  have hrho0 : 0 ≤ rho l := by
    unfold rho
    positivity
  have hrg : rho l ≤ gam l := by
    unfold rho gam
    gcongr
    linarith
  have key : 1 / ((l : ℝ) - 1) - gam l = rho l := by
    unfold rho gam
    field_simp
    ring

  have wt_sum : ∀ (r : ι → ℝ) (w : ℝ) (s : Finset (Fin N0 × Fin N1))
      (f : Fin N0 × Fin N1 → MvPowerSeries ι K), (∀ x ∈ s, WtGe π r w (f x)) →
      WtGe π r w (∑ x ∈ s, f x) := by
    intro r w s f
    refine Finset.induction_on s ?_ ?_
    · intro _ n
      unfold MonoWtGe
      rw [Finset.sum_empty, map_zero, norm_zero]
      exact Real.rpow_nonneg hπ0.le _
    · intro a s ha ih hf n
      rw [Finset.sum_insert ha]
      have h1 := hf a (Finset.mem_insert_self a s) n
      have h2 := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)) n
      unfold MonoWtGe at h1 h2 ⊢
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

  have cc_subst : ∀ (a : ZMod 2 → MvPowerSeries ι K), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      ∀ f : MvPowerSeries (ZMod 2) K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
    intro a ha f hf
    have hs : MvPowerSeries.HasSubst a := by
      first
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
        | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
    rw [MvPowerSeries.constantCoeff_subst hs]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd : d = 0
    · subst hd
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
        by_contra h
        push_neg at h
        exact hd (Finsupp.ext h)
      have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
        rw [Finsupp.prod, map_prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs') (by rw [map_pow, ha, zero_pow hs'])
      rw [h0, smul_zero]
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    by_contra h
    have h' := hbe.2.2.1 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
    exact absurd h'.1 (by simp [degE])

  have hUw : WtGe π (fun _ => rho l) 0 U := by
    intro n
    unfold MonoWtGe
    refine (hU n).trans ?_
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hπ0 hπ1
      (by linarith [asmR_dot_nonneg n (r := fun _ => rho l) (fun _ => hrho0)])
  have hlog : ∀ x, oneLog (K := K) l x = genLog (K := K) l id x := fun x => (hB K l 2 N0 N1).2.2 x
  have hgw : ∀ x, WtGe π (fun _ => rho l) (rho l) (g x) :=
    hG K l hl hpi (Fin N0 × Fin N1) id g hg0 (fun x => by rw [← hlog x]; exact hgl x)
  have hGU : WtGe π (fun _ => rho l) 0 (MvPowerSeries.subst g U) :=
    hW0 K π hπ0 hpi (Fin N0 × Fin N1) (Fin N0 × Fin N1) g (fun _ => rho l) (fun _ => rho l) 0 U
      hg0 hgw hUw
  have hlinw : ∀ (t : ℝ) x,
      WtGe π (fun _ : ι => t) t (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) :=
    fun t x => asmOne_lin_wt hπ0 (M x) (hM x) t
  have hlinA : ∀ x, WtGe π (fun _ : ι => gam l) (rho l)
      (∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) := fun x =>
    (hRM K π hπ0 hpi ι (fun _ => rho l) (fun _ => gam l) (rho l) (fun _ => hrg)).1 _ (hlinw (rho l) x)
  have hA : WtGe π (fun _ : ι => gam l) 0
      (MvPowerSeries.subst (fun x => ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i)
        (MvPowerSeries.subst g U)) :=
    hW1 K π hπ0 hpi (Fin N0 × Fin N1) ι _ (fun _ => rho l) (fun _ => gam l) 0 _
      (fun x => asmOne_lin_const (M x)) hlinA hGU
  obtain ⟨hS1, hS2⟩ := hS K l 2 hl hodd le_rfl even_two hpi K0 hK0 ζ hζ be hbe
  have hbeW : WtGe π (fun _ : ZMod 2 => gam l) (1 / ((l : ℝ) - 1)) be := by
    intro n
    by_cases hbi : IsBiPower l n
    · obtain ⟨s, s', α, β, hs, hs', _, hsum, rfl⟩ := hbi
      have h1 := hS1 (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))
      unfold MonoWtGe at h1 ⊢
      have hodd' : Odd (α + β) := by
        have h := asmOne_zmod2 s s' α β hs hs' hsum
        have h' : ((α + β : ℕ) : ZMod 2) = 1 := by
          push_cast
          exact h
        have h'' := congrArg ZMod.val h'
        rw [ZMod.val_natCast] at h''
        exact Nat.odd_iff.2 (h''.trans (by decide))
      have hD := hOR1 α β hodd'
      have e1 : dot (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) (fun _ : ZMod 2 => rho l) =
          ((l : ℝ) ^ α + (l : ℝ) ^ β) * rho l := by
        rw [show Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) = pureMon l s s' α β from rfl,
          asmR_dot_pureMon]
        ring
      have e2 : dot (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) (fun _ : ZMod 2 => gam l) =
          ((l : ℝ) ^ α + (l : ℝ) ^ β) * gam l := by
        rw [show Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) = pureMon l s s' α β from rfl,
          asmR_dot_pureMon]
        ring
      rw [e1] at h1
      rw [e2]
      refine h1.trans (Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1 ?_)
      have hg : gam l - rho l = 1 / ((l : ℝ) + 1) := by linarith [hOR2]
      have h3 : 1 ≤ ((l : ℝ) ^ α + (l : ℝ) ^ β) * (gam l - rho l) := by
        rw [hg, mul_one_div]
        exact hD
      nlinarith
    · exact asmR_monoWtGe_rad hπ0 hπ1 (fun _ => hrg) (hS2 n hbi)
  have haw : ∀ x (s : ZMod 2), WtGe π (fun _ : ι => gam l) (gam l)
      ((if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) := by
    intro x s
    refine asmOne_smul_wt ?_ (hlinw (gam l) x)
    split_ifs <;> simp [hep]
  have hac : ∀ x (s : ZMod 2), MvPowerSeries.constantCoeff
      ((if s = 0 then (1 : K) else ep) • ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) = 0 :=
    fun x s => asmOne_smul_const _ (asmOne_lin_const (M x))
  have hBx : ∀ x, WtGe π (fun _ : ι => gam l) (1 / ((l : ℝ) - 1))
      (MvPowerSeries.subst (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
        ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be) := fun x =>
    hW1 K π hπ0 hpi (ZMod 2) ι _ (fun _ => gam l) (fun _ => gam l) _ be (hac x) (haw x) hbeW
  have hsgn1 : ‖sgn‖ = 1 := by rcases hsgn with rfl | rfl <;> simp
  have hsgn2 : ‖sgn / 2‖ ≤ 1 := by
    rw [norm_div, hsgn1]
    exact div_le_one_of_le₀ h2n (by positivity)
  have hBw := asmOne_smul_wt hsgn2 (wt_sum _ _ Finset.univ _ (fun x _ => hBx x))
  have hBc : MvPowerSeries.constantCoeff ((sgn / 2) • ∑ x : Fin N0 × Fin N1,
      MvPowerSeries.subst (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
        ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be) = 0 := by
    refine asmOne_smul_const _ ?_
    rw [map_sum]
    exact Finset.sum_eq_zero fun x _ => cc_subst _ (hac x) be hbe0
  have hExp := hE K l hl hpi ι (fun _ => gam l) κ _ hBc (fun n _ => hBw n)
  have hMul := hMW K π hπ0 ι (fun _ => gam l) 0 0 κ _ _ (fun n _ => hA n) hExp
  have hk := hMul κ le_rfl
  have hf := hF K l hl hpi ι κ
  unfold MonoWtGe at hk
  have hdeg : (κ.degree : ℝ) = ∑ i, (κ i : ℝ) := by
    rw [Finsupp.degree_eq_sum]
    push_cast
    rfl
  have e : (∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - ∑ i, (κ i : ℝ) * gam l = rho l * ∑ i, (κ i : ℝ) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← key]
    ring
  rw [norm_mul]
  refine (mul_le_mul hf hk (norm_nonneg _) (Real.rpow_nonneg hπ0.le _)).trans (le_of_eq ?_)
  rw [← Real.rpow_add hπ0, asmR_dot_fintype, hdeg]
  congr 1
  beta_reduce
  linarith [e]

end Formalism.DworkPowerSeriesWeights
