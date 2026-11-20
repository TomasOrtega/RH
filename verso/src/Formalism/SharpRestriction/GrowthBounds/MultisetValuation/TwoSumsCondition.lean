import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ExistsAtPiG1EqCPowMulIntegralSeries

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser Aser Aser' AA leadT G1)

abbrev wK' (p : ℕ) [Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K'] (c : WW p) : K' :=
  algebraMap (K0 p) K' (algebraMap (WW p) (K0 p) c)

def sOf {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K']
    (μ : PowerSeries K') (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : MvPowerSeries (Zidx n' r0 r1) K' :=
  PowerSeries.subst (coordZ B K' 1 x) μ

def TwoSumsCondition (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → ∀ c : WW p, (sigW p)^[2] c = c → ∀ (n' r0 r1 : ℕ), 2 ≤ n' → Even n' → ∀ (B : OmBasis p n')
    (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∀ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X →
    ∃ u : Fin n' → K', (∀ s, u s ∈ Rp p K' vp) ∧ ∃ Y : MvPowerSeries (Zidx n' r0 r1) K', IntR (Rp p K' vp) Y ∧
      ∑ e : Eidx n' r0 r1, (MvPowerSeries.C (wK' p K' c) * (sOf B K' μ (Sum.inl e) * sOf B K' μ (Sum.inr e) ^ p) -
          MvPowerSeries.C (wK' p K' (sigW p c)) * (sOf B K' μ (Sum.inr e) * sOf B K' μ (Sum.inl e) ^ p)) =
        hhS p K' u + MvPowerSeries.C (p : K') * Y

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Introduce `n` and use `by rw [map_neg]; exact R.neg_mem (hf n)`.
-/
theorem IntR_neg {ι K : Type} [Field K] {R : Subring K} {f : MvPowerSeries ι K} (hf : IntR R f) : IntR R (-f) :=
  fun n => by rw [map_neg]; exact R.neg_mem (hf n)

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_pow]`. Use `Subring.sum_mem _ fun l hl => ?_` and prove the remaining obligations. Rewrite `hl` using `[Finset.mem_finsuppAntidiag]`. Take `⟨hsum, -⟩` from `hl`. Distinguish the cases in `hz : ∃ i ∈ range k, l i = 0`.

Take `⟨i, hi, hli⟩` from `hz`. Rewrite using `[Finset.prod_eq_zero hi (by rw [hli, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0])]`. Conclude with `Subring.zero_mem _`. Use `push_neg at hz`. Use `Subring.prod_mem _ fun i hi => ih _ ?_` and prove the remaining obligations.

Establish `hik : i < k` using `Finset.mem_range.mp hi`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj, hji⟩ : ∃ j ∈ range k, j ≠ i := by`. Distinguish the cases in `h : i = 0`. Conclude with `⟨1, Finset.mem_range.mpr (by omega), by omega⟩`. Conclude with `⟨0, Finset.mem_range.mpr (by omega), by omega⟩`.

Establish `hsub : ({i, j} : Finset ℕ) ⊆ range k`. Introduce `x hx`. Rewrite `hx` using `[Finset.mem_insert, Finset.mem_singleton]`. Break down `hx with rfl | rfl` into its components or cases. Conclude with `hi`.

Conclude with `hj`. Establish `hle` using `Finset.sum_le_sum_of_subset (f := l) hsub`. Rewrite `hle` using `[Finset.sum_pair hji.symm, hsum]`. Use `hz j hj` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem coeff_pow_mem_of_lower_coeff_mem {K : Type} [Field K] (R : Subring K) (μ : PowerSeries K)
    (h0 : PowerSeries.constantCoeff μ = 0) (n : ℕ) (ih : ∀ m < n, PowerSeries.coeff m μ ∈ R)
    (k : ℕ) (hk : 2 ≤ k) : PowerSeries.coeff n (μ ^ k) ∈ R := by
  rw [PowerSeries.coeff_pow]
  refine Subring.sum_mem _ fun l hl => ?_
  rw [Finset.mem_finsuppAntidiag] at hl
  obtain ⟨hsum, -⟩ := hl
  by_cases hz : ∃ i ∈ range k, l i = 0
  · obtain ⟨i, hi, hli⟩ := hz
    rw [Finset.prod_eq_zero hi (by rw [hli, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0])]
    exact Subring.zero_mem _
  · push_neg at hz
    refine Subring.prod_mem _ fun i hi => ih _ ?_
    have hik : i < k := Finset.mem_range.mp hi
    obtain ⟨j, hj, hji⟩ : ∃ j ∈ range k, j ≠ i := by
      by_cases h : i = 0
      · exact ⟨1, Finset.mem_range.mpr (by omega), by omega⟩
      · exact ⟨0, Finset.mem_range.mpr (by omega), by omega⟩
    have hsub : ({i, j} : Finset ℕ) ⊆ range k := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hj
    have hle := Finset.sum_le_sum_of_subset (f := l) hsub
    rw [Finset.sum_pair hji.symm, hsum] at hle
    have := hz j hj
    omega

/- English proof (translation)
Establish `hp1 : (1 : ℕ) ≠ p ^ 2`. Use `hp.out.two_le` as an intermediate fact. Introduce `h`. Use the polynomial consequences of the given equalities and inequalities. Establish `hl0 : PowerSeries.coeff 0 (lamF p vp) = 0` using `by simp [lamF, lgF]`.

Establish `hl1 : PowerSeries.coeff 1 (lamF p vp) = 1` using `by simp [lamF, lgF, Finset.sum_range_succ, hp1]`. Establish `hlm` using `lamF_mem p K' vp hvp`. Establish `hS` using `PowerSeries.HasSubst.of_constantCoeff_zero' h0`. Use `Nat.strong_induction_on n ?_` and prove the remaining obligations. Introduce `n ih`.

Establish `hX` using `congrArg (PowerSeries.coeff n) h1`. Rewrite `hX` using `[PowerSeries.coeff_subst' hS]`. Establish `hfin` using `PowerSeries.coeff_subst_finite' hS (lamF p vp) n`. Use `set f : ℕ → K' := fun d => PowerSeries.coeff d (lamF p vp) • PowerSeries.coeff n (μ ^ d) with hf`. Establish `hfin' : (Function.support f).Finite` using `hfin`.

Establish `hsub : Function.support f ⊆ ↑(Set.Finite.toFinset hfin' ∪ {1})`. Introduce `d hd`. Rewrite using `[Finset.coe_union, Set.Finite.coe_toFinset]`. Conclude with `Or.inl hd`. Rewrite `hX` using `[finsum_eq_sum_of_support_subset f hsub, ← Finset.add_sum_erase _ _ (Finset.mem_union_right _ (Finset.mem_singleton_self 1))]`.

Establish `hf1 : f 1 = PowerSeries.coeff n μ` using `by simp [hf, hl1]`. Establish `hrest : ∑ d ∈ (Set.Finite.toFinset hfin' ∪ {1}).erase 1, f d ∈ Rp p K' vp`. Use `Subring.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Establish `hd1 : d ≠ 1` using `Finset.ne_of_mem_erase hd`. Simplify using `only [hf, smul_eq_mul]`.

Break down `Nat.lt_or_ge d 2 with h | h` into its components or cases. Establish `: d = 0` using `by omega`. Substitute `this` using the available equality. Rewrite using `[hl0, zero_mul]`. Conclude with `Subring.zero_mem _`.

Conclude with `Subring.mul_mem _ (hlm d) (coeff_pow_mem_of_lower_coeff_mem _ μ h0 n ih d h)`. Establish `hXn : PowerSeries.coeff n (PowerSeries.X : PowerSeries K') ∈ Rp p K' vp`. Rewrite using `[PowerSeries.coeff_X]`. Use `split_ifs`. Conclude with `Subring.one_mem _`.

Conclude with `Subring.zero_mem _`. Rewrite `hX` using `[hf1]`. Establish `hμ : PowerSeries.coeff n μ = PowerSeries.coeff n (PowerSeries.X : PowerSeries K') - ∑ d ∈ (Set.Finite.toFinset hfin' ∪ {1}).erase 1, f d`. Rewrite using `[← hX]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hμ]`. Conclude with `Subring.sub_mem _ hXn hrest`.
-/
theorem th_mu_int (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K'))
    (μ : PowerSeries K') (h0 : PowerSeries.constantCoeff μ = 0)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X) (n : ℕ) :
    PowerSeries.coeff n μ ∈ Rp p K' vp := by
  have hp1 : (1 : ℕ) ≠ p ^ 2 := by
    have := hp.out.two_le
    intro h
    nlinarith
  have hl0 : PowerSeries.coeff 0 (lamF p vp) = 0 := by simp [lamF, lgF]
  have hl1 : PowerSeries.coeff 1 (lamF p vp) = 1 := by simp [lamF, lgF, Finset.sum_range_succ, hp1]
  have hlm := lamF_mem p K' vp hvp
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  refine Nat.strong_induction_on n ?_
  intro n ih
  have hX := congrArg (PowerSeries.coeff n) h1
  rw [PowerSeries.coeff_subst' hS] at hX
  have hfin := PowerSeries.coeff_subst_finite' hS (lamF p vp) n
  set f : ℕ → K' := fun d => PowerSeries.coeff d (lamF p vp) • PowerSeries.coeff n (μ ^ d) with hf
  have hfin' : (Function.support f).Finite := hfin
  have hsub : Function.support f ⊆ ↑(Set.Finite.toFinset hfin' ∪ {1}) := by
    intro d hd
    rw [Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl hd
  rw [finsum_eq_sum_of_support_subset f hsub,
    ← Finset.add_sum_erase _ _ (Finset.mem_union_right _ (Finset.mem_singleton_self 1))] at hX
  have hf1 : f 1 = PowerSeries.coeff n μ := by simp [hf, hl1]
  have hrest : ∑ d ∈ (Set.Finite.toFinset hfin' ∪ {1}).erase 1, f d ∈ Rp p K' vp := by
    refine Subring.sum_mem _ fun d hd => ?_
    have hd1 : d ≠ 1 := Finset.ne_of_mem_erase hd
    simp only [hf, smul_eq_mul]
    rcases Nat.lt_or_ge d 2 with h | h
    · have : d = 0 := by omega
      subst this
      rw [hl0, zero_mul]
      exact Subring.zero_mem _
    · exact Subring.mul_mem _ (hlm d) (coeff_pow_mem_of_lower_coeff_mem _ μ h0 n ih d h)
  have hXn : PowerSeries.coeff n (PowerSeries.X : PowerSeries K') ∈ Rp p K' vp := by
    rw [PowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  rw [hf1] at hX
  have hμ : PowerSeries.coeff n μ = PowerSeries.coeff n (PowerSeries.X : PowerSeries K') -
      ∑ d ∈ (Set.Finite.toFinset hfin' ∪ {1}).erase 1, f d := by
    rw [← hX]
    ring
  rw [hμ]
  exact Subring.sub_mem _ hXn hrest

/- English proof (translation)
Use `haveI := charZero_K' p K'`. Establish `hpK : (p : K') ≠ 0` using `Nat.cast_ne_zero.mpr hp.out.ne_zero`. Establish `hvR : vp ∈ Rp p K' vp` using `Subring.subset_closure (Or.inr rfl)`. Establish `hv : (p - 1) * padicValNat p k.factorial ≤ k`. Rewrite using `[sub_one_mul_padicValNat_factorial]`.

Use linear arithmetic over natural numbers and integers. Establish `hdec : k.factorial = p ^ padicValNat p k.factorial * ordCompl[p] k.factorial`. Rewrite using `[← Nat.factorization_def _ hp.out]`. Conclude with `(Nat.ordProj_mul_ordCompl_eq_self _ _).symm`. Establish `hnd : ¬ p ∣ ordCompl[p] k.factorial` using `Nat.not_dvd_ordCompl hp.out (Nat.factorial_ne_zero k)`.

Establish `hm0 : ((ordCompl[p] k.factorial : ℕ) : K') ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.ordCompl_pos p (Nat.factorial_ne_zero k)).ne'`. Establish `h2 : p ^ 2 - 1 = (p + 1) * (p - 1)`. Establish `h1` using `hp.out.one_le`. Establish `h3 : 1 ≤ p ^ 2` using `Nat.one_le_pow 2 p (by omega)`. Use `zify [h1, h3]`.

Expand and normalize the polynomial expressions, which then agree. Use `set v := padicValNat p k.factorial with hvdef`. Use `set m := ordCompl[p] k.factorial with hmdef`. Establish `hle : (p ^ 2 - 1) * v ≤ (p + 1) * k`. Rewrite using `[h2, mul_assoc]`.

Conclude with `Nat.mul_le_mul_left _ hv`. Establish `hsplit : (vp ^ (p + 1)) ^ k = (vp ^ (p ^ 2 - 1)) ^ v * vp ^ ((p + 1) * k - (p ^ 2 - 1) * v)`. Rewrite using `[← pow_mul, ← pow_mul, ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hsplit, hvp, hdec, Nat.cast_mul, Nat.cast_pow]`. Establish `hre : (p : K') ^ v * vp ^ ((p + 1) * k - (p ^ 2 - 1) * v) * ((p : K') ^ v * (m : K'))⁻¹ = vp ^ ((p + 1) * k - (p ^ 2 - 1) * v) * (m : K')⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hre]`. Conclude with `Subring.mul_mem _ (Subring.pow_mem _ hvR _) (natCast_inv_mem_Rp p K' vp _ hnd)`.
-/
private theorem pow_mul_inv_factorial_mem_Rp (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (hvp : vp ^ (p ^ 2 - 1) = (p : K')) (k : ℕ) :
    (vp ^ (p + 1)) ^ k * ((k.factorial : ℕ) : K')⁻¹ ∈ Rp p K' vp := by
  haveI := charZero_K' p K'
  have hpK : (p : K') ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hvR : vp ∈ Rp p K' vp := Subring.subset_closure (Or.inr rfl)
  have hv : (p - 1) * padicValNat p k.factorial ≤ k := by
    rw [sub_one_mul_padicValNat_factorial]
    omega
  have hdec : k.factorial = p ^ padicValNat p k.factorial * ordCompl[p] k.factorial := by
    rw [← Nat.factorization_def _ hp.out]
    exact (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
  have hnd : ¬ p ∣ ordCompl[p] k.factorial := Nat.not_dvd_ordCompl hp.out (Nat.factorial_ne_zero k)
  have hm0 : ((ordCompl[p] k.factorial : ℕ) : K') ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ordCompl_pos p (Nat.factorial_ne_zero k)).ne'
  have h2 : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have h1 := hp.out.one_le
    have h3 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p (by omega)
    zify [h1, h3]
    ring
  set v := padicValNat p k.factorial with hvdef
  set m := ordCompl[p] k.factorial with hmdef
  have hle : (p ^ 2 - 1) * v ≤ (p + 1) * k := by
    rw [h2, mul_assoc]
    exact Nat.mul_le_mul_left _ hv
  have hsplit : (vp ^ (p + 1)) ^ k = (vp ^ (p ^ 2 - 1)) ^ v * vp ^ ((p + 1) * k - (p ^ 2 - 1) * v) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hsplit, hvp, hdec, Nat.cast_mul, Nat.cast_pow]
  have hre : (p : K') ^ v * vp ^ ((p + 1) * k - (p ^ 2 - 1) * v) * ((p : K') ^ v * (m : K'))⁻¹ =
      vp ^ ((p + 1) * k - (p ^ 2 - 1) * v) * (m : K')⁻¹ := by
    field_simp
  rw [hre]
  exact Subring.mul_mem _ (Subring.pow_mem _ hvR _) (natCast_inv_mem_Rp p K' vp _ hnd)

/- English proof (translation)
Use extensionality with `n`. Express the relevant statement in the definitionally equal form `vp ^ n.degree * _ = _`. Rewrite using `[MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, MvPowerSeries.X_pow_eq, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial]`. Use `split_ifs with h`. Rewrite using `[h, map_add, Finsupp.degree_single, Finsupp.degree_single]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
private theorem atPi_C_mul_X_mul_X_pow {K : Type} [Field K] (vp k : K) (x y : Fin 2) (q : ℕ) :
    atPi vp (MvPowerSeries.C k * (MvPowerSeries.X x * MvPowerSeries.X y ^ q)) =
      MvPowerSeries.C (k * vp ^ (q + 1)) * (MvPowerSeries.X x * MvPowerSeries.X y ^ q) := by
  ext n
  change vp ^ n.degree * _ = _
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, MvPowerSeries.X_pow_eq, MvPowerSeries.X,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial]
  split_ifs with h
  · rw [h, map_add, Finsupp.degree_single, Finsupp.degree_single]
    ring
  · simp

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[map_add]`. Express the relevant statement in the definitionally equal form `vp ^ n.degree * MvPowerSeries.coeff n (f + g) = vp ^ n.degree * MvPowerSeries.coeff n f + vp ^ n.degree * MvPowerSeries.coeff n g`. Rewrite using `[map_add, mul_add]`.
-/
private theorem atPi_add {σ K : Type} [Field K] (vp : K) (f g : MvPowerSeries σ K) :
    atPi vp (f + g) = atPi vp f + atPi vp g := by
  ext n
  rw [map_add]
  change vp ^ n.degree * MvPowerSeries.coeff n (f + g) =
    vp ^ n.degree * MvPowerSeries.coeff n f + vp ^ n.degree * MvPowerSeries.coeff n g
  rw [map_add, mul_add]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[map_sub]`. Express the relevant statement in the definitionally equal form `vp ^ n.degree * MvPowerSeries.coeff n (f - g) = vp ^ n.degree * MvPowerSeries.coeff n f - vp ^ n.degree * MvPowerSeries.coeff n g`. Rewrite using `[map_sub, mul_sub]`.
-/
private theorem atPi_sub {σ K : Type} [Field K] (vp : K) (f g : MvPowerSeries σ K) :
    atPi vp (f - g) = atPi vp f - atPi vp g := by
  ext n
  rw [map_sub]
  change vp ^ n.degree * MvPowerSeries.coeff n (f - g) =
    vp ^ n.degree * MvPowerSeries.coeff n f - vp ^ n.degree * MvPowerSeries.coeff n g
  rw [map_sub, mul_sub]

/- English proof (translation)
Introduce `hp5 c hc n' r0 r1 hn hev B K' _ _ vp hvp μ h0 h1`. Use `haveI := charZero_K' p K'`. Take `⟨u, hu, Y, hY, hsum⟩` from `hT hp5 c hc n' r0 r1 hn hev B K' vp hvp μ h0 h1`. Establish `hpK : (p : K') ≠ 0` using `Nat.cast_ne_zero.mpr hp.out.ne_zero`. Establish `hwR : ∀ w : WW p, wK' p K' w ∈ Rp p K' vp` using `fun w => Subring.subset_closure (Or.inl ⟨w, rfl⟩)`.

Establish `hL0 : ∀ x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.constantCoeff (coordZ B K' (1 : K') x) = 0` using `coordZ_const B K' 1`. Establish `hLs : ∀ x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, PowerSeries.HasSubst (coordZ B K' (1 : K') x)` using `fun x => PowerSeries.HasSubst.of_constantCoeff_zero (hL0 x)`. Establish `hS0 : ∀ x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.constantCoeff (sOf B K' μ x) = 0`. Introduce `x`. Rewrite using `[sOf, PowerSeries.constantCoeff_subst (hLs x)]`.

Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `d`. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, zero_smul]`. Rewrite using `[map_pow, hL0, zero_pow hd.ne', smul_zero]`.

Establish `hSI : ∀ x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, IntR (Rp p K' vp) (sOf B K' μ x)` using `fun x => IntR_psubst (hL0 x) (th_coordZ_int B K' vp x) (th_mu_int K' vp hvp μ h0 h1)`. Establish `ht : tOf vp μ (coordZ B K' 1) = fun x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1 => MvPowerSeries.C vp * sOf B K' μ x`. Use function extensionality and compare the values at `x`. Use `show PowerSeries.subst (coordZ B K' 1 x) (PowerSeries.C vp * μ) = _`. Rewrite using `[← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul (hLs x), MvPowerSeries.smul_eq_C_mul]`.

Both sides reduce to the same expression. Establish `ht0 : ∀ x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.constantCoeff (tOf vp μ (coordZ B K' 1) x) = 0`. Introduce `x`. Rewrite using `[ht, map_mul, hS0, mul_zero]`. Establish `htS : MvPowerSeries.HasSubst (tOf vp μ (coordZ B K' (r0` using `r0) (r1 := r1) 1)) := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0`.

Take `⟨Rr, hRrI, hRr0, hRr⟩` from `exists_atPi_G1_eq_C_pow_mul_integral_series p K' vp hvp (hwR c) (hwR (sigW p c))`. Set `P : Eidx n' r0 r1 → Fin 2 → MvPowerSeries (Zidx n' r0 r1) K'` to `fun e => ![sOf B K' μ (Sum.inl e), sOf B K' μ (Sum.inr e)]`. Establish `hP0 : ∀ e i, MvPowerSeries.constantCoeff (P e i) = 0`. Introduce `e i`. Use `fin_cases i`.

Conclude with `hS0 _`. Conclude with `hS0 _`. Establish `hPs : ∀ e, MvPowerSeries.HasSubst (P e)` using `fun e => MvPowerSeries.hasSubst_of_constantCoeff_zero (hP0 e)`. Establish `hPI : ∀ e i, IntR (Rp p K' vp) (P e i)`. Introduce `e i`.

Use `fin_cases i`. Conclude with `hSI _`. Conclude with `hSI _`. Establish `hA1 : Aser K' p = AA K' p 0 1` using `rfl`. Establish `hA2 : Aser' K' p = AA K' p 1 0` using `rfl`.

Establish `hper : ∀ e, MvPowerSeries.subst (fun k => MvPowerSeries.C vp * P e k) (Gser p (wK' p K' c) (wK' p K' (sigW p c))) = MvPowerSeries.C (vp ^ (p + 1)) * MvPowerSeries.subst (P e) Rr + MvPowerSeries.C (vp ^ (p + 1) / p) * (MvPowerSeries.C (wK' p K' c) * (sOf B K' μ (Sum.inl e) * sOf B …`. Introduce `e`. Rewrite using `[th_subst_scale vp (P e) (hPs e)]`. Establish `hG : Gser p (wK' p K' c) (wK' p K' (sigW p c)) = G1 p (wK' p K' c) (wK' p K' (sigW p c)) + (MvPowerSeries.C (wK' p K' c * (p : K')⁻¹) * (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ p) - MvPowerSeries.C (wK' p K' (sigW p c) * (p : K')⁻¹) * (MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ p))`. Simplify using `only [Gser, G1, leadT, hA1, hA2, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hG, atPi_add, atPi_sub, hRr, atPi_C_mul_X_mul_X_pow, atPi_C_mul_X_mul_X_pow, ← MvPowerSeries.coe_substAlgHom (hPs e)]`. Simplify using `only [map_add, map_sub, map_mul, map_pow]`. Simplify using `only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_C, MvPowerSeries.subst_X (hPs e)]`. Simplify using `only [P, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, div_eq_mul_inv, map_mul, map_pow]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hGt0 : MvPowerSeries.constantCoeff (-(MvPowerSeries.map (algebraMap (K0 p) K') (Gt p (Eidx n' r0 r1) (wK p c) (wK p (sigW p c))))) = 0`. Rewrite using `[map_neg, MvPowerSeries.constantCoeff_map, th_Gt_const, map_zero, neg_zero]`. Rewrite using `[th_subst_expK _ ht0 hGt0]`. Use `set W : MvPowerSeries (Zidx n' r0 r1) K' := ∑ e : Eidx n' r0 r1, MvPowerSeries.subst (P e) Rr with hW`.

Establish `hexp : MvPowerSeries.subst (tOf vp μ (coordZ B K' 1)) (-(MvPowerSeries.map (algebraMap (K0 p) K') (Gt p (Eidx n' r0 r1) (wK p c) (wK p (sigW p c))))) = -(MvPowerSeries.C (vp ^ (p + 1) / p) * hhS p K' u) + MvPowerSeries.C (vp ^ (p + 1)) * (-(Y + W))`. Rewrite using `[← MvPowerSeries.coe_substAlgHom htS, map_neg, Gt, map_sum, map_sum]`. Establish `hterm : ∀ e : Eidx n' r0 r1, MvPowerSeries.substAlgHom htS (MvPowerSeries.map (algebraMap (K0 p) K') (ren ![Sum.inl e, Sum.inr e] (Gser p (wK p c) (wK p (sigW p c))))) = MvPowerSeries.C (vp ^ (p + 1)) * MvPowerSeries.subst (P e) Rr + MvPowerSeries.C (vp ^ (p + 1) / p) * (MvPowerS …`. Introduce `e`. Rewrite using `[MvPowerSeries.coe_substAlgHom, th_map_ren, th_map_Gser, th_subst_ren _ htS, ← hper e]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Use `fin_cases k`. Simplify using `[ht, P]`. Simplify using `[ht, P]`.

Rewrite using `[Finset.sum_congr rfl (fun e _ => hterm e), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]`. Establish `hBA : MvPowerSeries.C (vp ^ (p + 1) / p) * MvPowerSeries.C (p : K') = (MvPowerSeries.C (vp ^ (p + 1)) : MvPowerSeries (Zidx n' r0 r1) K')`. Rewrite using `[← map_mul, div_mul_cancel₀ _ hpK]`. Take the linear combination `(-Y) * hBA`. Establish `hY0 : MvPowerSeries.constantCoeff Y = 0`.

Establish `hc0` using `congrArg MvPowerSeries.constantCoeff hsum`. Simplify using `[hS0, hhS_const, zero_pow hp.out.ne_zero, hpK] at hc0`. Conclude with `hc0`. Establish `hW0 : MvPowerSeries.constantCoeff W = 0`. Rewrite using `[hW, map_sum]`.

Conclude with `Finset.sum_eq_zero fun e _ => MvPowerSeries.constantCoeff_subst_eq_zero (hPs e) (hP0 e) hRr0`. Establish `hWI : IntR (Rp p K' vp) W` using `IntR_sum _ _ fun e _ => IntR_subst (P e) (hP0 e) (hPI e) hRrI`. Rewrite using `[hexp, expK_add]`. Conclude with `⟨u, hu, _, IntR_expK (pow_mul_inv_factorial_mem_Rp K' vp hvp) (IntR_neg (IntR_add hY hWI)), rfl⟩`. Rewrite using `[map_neg, map_mul, hhS_const, mul_zero, neg_zero]`.

Rewrite using `[map_mul, map_neg, map_add, hY0, hW0, add_zero, neg_zero, mul_zero]`.
-/
theorem gcCondition_of_twoSums (hT : TwoSumsCondition p) : RestGc p := by
  intro hp5 c hc n' r0 r1 hn hev B K' _ _ vp hvp μ h0 h1
  haveI := charZero_K' p K'
  obtain ⟨u, hu, Y, hY, hsum⟩ := hT hp5 c hc n' r0 r1 hn hev B K' vp hvp μ h0 h1
  have hpK : (p : K') ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hwR : ∀ w : WW p, wK' p K' w ∈ Rp p K' vp := fun w => Subring.subset_closure (Or.inl ⟨w, rfl⟩)
  have hL0 : ∀ x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.constantCoeff (coordZ B K' (1 : K') x) = 0 := coordZ_const B K' 1
  have hLs : ∀ x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, PowerSeries.HasSubst (coordZ B K' (1 : K') x) := fun x =>
    PowerSeries.HasSubst.of_constantCoeff_zero (hL0 x)
  have hS0 : ∀ x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.constantCoeff (sOf B K' μ x) = 0 := by
    intro x
    rw [sOf, PowerSeries.constantCoeff_subst (hLs x)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, zero_smul]
    · rw [map_pow, hL0, zero_pow hd.ne', smul_zero]
  have hSI : ∀ x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, IntR (Rp p K' vp) (sOf B K' μ x) := fun x =>
    IntR_psubst (hL0 x) (th_coordZ_int B K' vp x) (th_mu_int K' vp hvp μ h0 h1)
  have ht : tOf vp μ (coordZ B K' 1) = fun x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1 => MvPowerSeries.C vp * sOf B K' μ x := by
    funext x
    show PowerSeries.subst (coordZ B K' 1 x) (PowerSeries.C vp * μ) = _
    rw [← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul (hLs x), MvPowerSeries.smul_eq_C_mul]
    rfl
  have ht0 : ∀ x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.constantCoeff (tOf vp μ (coordZ B K' 1) x) = 0 := by
    intro x
    rw [ht, map_mul, hS0, mul_zero]
  have htS : MvPowerSeries.HasSubst (tOf vp μ (coordZ B K' (r0 := r0) (r1 := r1) 1)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  obtain ⟨Rr, hRrI, hRr0, hRr⟩ := exists_atPi_G1_eq_C_pow_mul_integral_series p K' vp hvp (hwR c) (hwR (sigW p c))
  let P : Eidx n' r0 r1 → Fin 2 → MvPowerSeries (Zidx n' r0 r1) K' :=
    fun e => ![sOf B K' μ (Sum.inl e), sOf B K' μ (Sum.inr e)]
  have hP0 : ∀ e i, MvPowerSeries.constantCoeff (P e i) = 0 := by
    intro e i
    fin_cases i
    · exact hS0 _
    · exact hS0 _
  have hPs : ∀ e, MvPowerSeries.HasSubst (P e) := fun e =>
    MvPowerSeries.hasSubst_of_constantCoeff_zero (hP0 e)
  have hPI : ∀ e i, IntR (Rp p K' vp) (P e i) := by
    intro e i
    fin_cases i
    · exact hSI _
    · exact hSI _
  have hA1 : Aser K' p = AA K' p 0 1 := rfl
  have hA2 : Aser' K' p = AA K' p 1 0 := rfl
  have hper : ∀ e, MvPowerSeries.subst (fun k => MvPowerSeries.C vp * P e k)
      (Gser p (wK' p K' c) (wK' p K' (sigW p c))) =
      MvPowerSeries.C (vp ^ (p + 1)) * MvPowerSeries.subst (P e) Rr +
      MvPowerSeries.C (vp ^ (p + 1) / p) *
        (MvPowerSeries.C (wK' p K' c) * (sOf B K' μ (Sum.inl e) * sOf B K' μ (Sum.inr e) ^ p) -
          MvPowerSeries.C (wK' p K' (sigW p c)) * (sOf B K' μ (Sum.inr e) * sOf B K' μ (Sum.inl e) ^ p)) := by
    intro e
    rw [th_subst_scale vp (P e) (hPs e)]
    have hG : Gser p (wK' p K' c) (wK' p K' (sigW p c)) = G1 p (wK' p K' c) (wK' p K' (sigW p c)) +
        (MvPowerSeries.C (wK' p K' c * (p : K')⁻¹) * (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ p) -
          MvPowerSeries.C (wK' p K' (sigW p c) * (p : K')⁻¹) * (MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ p)) := by
      simp only [Gser, G1, leadT, hA1, hA2, map_mul]
      ring
    rw [hG, atPi_add, atPi_sub, hRr, atPi_C_mul_X_mul_X_pow, atPi_C_mul_X_mul_X_pow,
      ← MvPowerSeries.coe_substAlgHom (hPs e)]
    simp only [map_add, map_sub, map_mul, map_pow]
    simp only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_C, MvPowerSeries.subst_X (hPs e)]
    simp only [P, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, div_eq_mul_inv, map_mul, map_pow]
    ring
  have hGt0 : MvPowerSeries.constantCoeff (-(MvPowerSeries.map (algebraMap (K0 p) K')
      (Gt p (Eidx n' r0 r1) (wK p c) (wK p (sigW p c))))) = 0 := by
    rw [map_neg, MvPowerSeries.constantCoeff_map, th_Gt_const, map_zero, neg_zero]
  rw [th_subst_expK _ ht0 hGt0]
  set W : MvPowerSeries (Zidx n' r0 r1) K' := ∑ e : Eidx n' r0 r1, MvPowerSeries.subst (P e) Rr with hW
  have hexp : MvPowerSeries.subst (tOf vp μ (coordZ B K' 1)) (-(MvPowerSeries.map (algebraMap (K0 p) K')
      (Gt p (Eidx n' r0 r1) (wK p c) (wK p (sigW p c))))) =
      -(MvPowerSeries.C (vp ^ (p + 1) / p) * hhS p K' u) + MvPowerSeries.C (vp ^ (p + 1)) * (-(Y + W)) := by
    rw [← MvPowerSeries.coe_substAlgHom htS, map_neg, Gt, map_sum, map_sum]
    have hterm : ∀ e : Eidx n' r0 r1, MvPowerSeries.substAlgHom htS (MvPowerSeries.map (algebraMap (K0 p) K')
        (ren ![Sum.inl e, Sum.inr e] (Gser p (wK p c) (wK p (sigW p c))))) =
        MvPowerSeries.C (vp ^ (p + 1)) * MvPowerSeries.subst (P e) Rr +
        MvPowerSeries.C (vp ^ (p + 1) / p) *
          (MvPowerSeries.C (wK' p K' c) * (sOf B K' μ (Sum.inl e) * sOf B K' μ (Sum.inr e) ^ p) -
            MvPowerSeries.C (wK' p K' (sigW p c)) * (sOf B K' μ (Sum.inr e) * sOf B K' μ (Sum.inl e) ^ p)) := by
      intro e
      rw [MvPowerSeries.coe_substAlgHom, th_map_ren, th_map_Gser, th_subst_ren _ htS, ← hper e]
      congr 1
      funext k
      fin_cases k
      · simp [ht, P]
      · simp [ht, P]
    rw [Finset.sum_congr rfl (fun e _ => hterm e), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hsum]
    have hBA : MvPowerSeries.C (vp ^ (p + 1) / p) * MvPowerSeries.C (p : K') =
        (MvPowerSeries.C (vp ^ (p + 1)) : MvPowerSeries (Zidx n' r0 r1) K') := by
      rw [← map_mul, div_mul_cancel₀ _ hpK]
    linear_combination (-Y) * hBA
  have hY0 : MvPowerSeries.constantCoeff Y = 0 := by
    have hc0 := congrArg MvPowerSeries.constantCoeff hsum
    simp [hS0, hhS_const, zero_pow hp.out.ne_zero, hpK] at hc0
    exact hc0
  have hW0 : MvPowerSeries.constantCoeff W = 0 := by
    rw [hW, map_sum]
    exact Finset.sum_eq_zero fun e _ => MvPowerSeries.constantCoeff_subst_eq_zero (hPs e) (hP0 e) hRr0
  have hWI : IntR (Rp p K' vp) W := IntR_sum _ _ fun e _ => IntR_subst (P e) (hP0 e) (hPI e) hRrI
  rw [hexp, expK_add]
  · exact ⟨u, hu, _, IntR_expK (pow_mul_inv_factorial_mem_Rp K' vp hvp) (IntR_neg (IntR_add hY hWI)), rfl⟩
  · rw [map_neg, map_mul, hhS_const, mul_zero, neg_zero]
  · rw [map_mul, map_neg, map_add, hY0, hW0, add_zero, neg_zero, mul_zero]

end Formalism.MainNotions.FormalGroupSystem.Pf
