import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.TsumNormEisensteinTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisSlash
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisVan
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EulerianNumeratorThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LevelOne

noncomputable section

open Formalism.ConjugateSelfDual Polynomial CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

section
variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N]

private structure Good (k : ℤ) (f : (ZMod N)ˣ → ℍ → ℂ) : Prop where
  mf : ∀ a, ∃ F : ModularForm (Gamma1 N) k, (F : ℍ → ℂ) = f a
  fam : ∀ (a b : (ZMod N)ˣ) (γ : SL(2, ℤ)), γ ∈ Gamma0 N → (b : ZMod N) = a * ((γ 1 1 : ℤ) : ZMod N) →
    f a ∣[k] γ = f b
  int : ∀ a, IntQ ι (f a)

omit [NeZero N] in
/- English proof (translation)
Rewrite using `[strictPeriods_Gamma1]`. Conclude with `AddSubgroup.mem_zmultiples 1`.
-/
private lemma one_mem_per :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

variable {ι}

/- English proof (translation)
Take `⟨F, hF⟩` from `hf.mf a`. Take `⟨G, hG⟩` from `hg.mf a`. Rewrite using `[← hF, ← hG]`. Conclude with `ModularForm.qExpansion_mul_coe one_pos one_mem_per F G`.
-/
private lemma Good.q_mul {k k' : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k' g) (a) :
    qExpansion 1 (f a * g a) = qExpansion 1 (f a) * qExpansion 1 (g a) := by
  obtain ⟨F, hF⟩ := hf.mf a
  obtain ⟨G, hG⟩ := hg.mf a
  rw [← hF, ← hG]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_per F G

/- English proof (translation)
Unfold `coef`. Rewrite using `[hf.q_mul hg]`. Simplify using `[PowerSeries.coeff_zero_eq_constantCoeff]`.
-/
private lemma Good.coef_mul {k k' : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k' g) (a) :
    coef (f a * g a) 0 = coef (f a) 0 * coef (g a) 0 := by
  unfold coef
  rw [hf.q_mul hg]
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

/- English proof (translation)
Take `⟨F, hF⟩` from `hf.mf a`. Take `⟨G, hG⟩` from `hg.mf a`. Conclude with `⟨F.mul G, by rw [ModularForm.coe_mul, hF, hG]⟩`. Use `fam a b γ hγ h := by`. Rewrite using `[ModularForm.mul_slash_SL2, hf.fam a b γ hγ h, hg.fam a b γ hγ h]`.

Use `int a n := by`. Unfold `coef`. Rewrite using `[hf.q_mul hg, PowerSeries.coeff_mul, map_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, norm_mul]`.

Conclude with `mul_le_one₀ (hf.int a p.1) (norm_nonneg _) (hg.int a p.2)`.
-/
private lemma Good.mul {k k' : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k' g) :
    Good ι (k + k') (fun a => f a * g a) where
  mf a := by
    obtain ⟨F, hF⟩ := hf.mf a
    obtain ⟨G, hG⟩ := hg.mf a
    exact ⟨F.mul G, by rw [ModularForm.coe_mul, hF, hG]⟩
  fam a b γ hγ h := by
    rw [ModularForm.mul_slash_SL2, hf.fam a b γ hγ h, hg.fam a b γ hγ h]
  int a n := by
    unfold coef
    rw [hf.q_mul hg, PowerSeries.coeff_mul, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
    rw [map_mul, norm_mul]
    exact mul_le_one₀ (hf.int a p.1) (norm_nonneg _) (hg.int a p.2)

/- English proof (translation)
Take `⟨F, hF⟩` from `hf.mf a`. Take `⟨G, hG⟩` from `hg.mf a`. Unfold `coef`. Rewrite using `[← hF, ← hG]`. Establish `h1` using `ModularForm.qExpansion_add one_pos one_mem_per F (c • G)`.

Establish `h2` using `ModularForm.qExpansion_smul one_pos one_mem_per c G`. Rewrite `h1` using `[FunLike.coe_smul]`. Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules.
-/
private lemma Good.coef_comb {k : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k g) (c : ℂ) (a) (n : ℕ) :
    coef (f a + c • g a) n = coef (f a) n + c * coef (g a) n := by
  obtain ⟨F, hF⟩ := hf.mf a
  obtain ⟨G, hG⟩ := hg.mf a
  unfold coef
  rw [← hF, ← hG]
  have h1 := ModularForm.qExpansion_add one_pos one_mem_per F (c • G)
  have h2 := ModularForm.qExpansion_smul one_pos one_mem_per c G
  rw [FunLike.coe_smul] at h1
  rw [h1, h2]
  simp

/- English proof (translation)
Take `⟨F, hF⟩` from `hf.mf a`. Take `⟨G, hG⟩` from `hg.mf a`. Conclude with `⟨F + c • G, by rw [FunLike.coe_add, FunLike.coe_smul, hF, hG]⟩`. Use `fam a b γ hγ h := by`. Rewrite using `[SlashAction.add_slash, ModularForm.SL_smul_slash, hf.fam a b γ hγ h, hg.fam a b γ hγ h]`.

Use `int a n := by`. Rewrite using `[hf.coef_comb hg, map_add, map_mul]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf.int a n) ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ hc (norm_nonneg _) (hg.int a n)`.
-/
private lemma Good.comb {k : ℤ} {f g : (ZMod N)ˣ → ℍ → ℂ} (hf : Good ι k f) (hg : Good ι k g) (c : ℂ)
    (hc : ‖ι.symm c‖ ≤ 1) : Good ι k (fun a => f a + c • g a) where
  mf a := by
    obtain ⟨F, hF⟩ := hf.mf a
    obtain ⟨G, hG⟩ := hg.mf a
    exact ⟨F + c • G, by rw [FunLike.coe_add, FunLike.coe_smul, hF, hG]⟩
  fam a b γ hγ h := by
    rw [SlashAction.add_slash, ModularForm.SL_smul_slash, hf.fam a b γ hγ h, hg.fam a b γ hγ h]
  int a n := by
    rw [hf.coef_comb hg, map_add, map_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf.int a n) ?_)
    rw [norm_mul]
    exact mul_le_one₀ hc (norm_nonneg _) (hg.int a n)

/- English proof (translation)
Take `⟨f, h1, h0, hi⟩` from `levelOne N k hk h2`. Use `⟨fun _ => f, ⟨fun _ => ⟨f, rfl⟩, fun _ _ γ _ _ => h1 γ, fun _ n => ?_⟩, fun _ => h0⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hi n`. Rewrite using `[hc, map_intCast]`. Conclude with `IsUltrametricDist.norm_intCast_le_one _ c`.
-/
private lemma good_one (k : ℕ) (hk : Even k) (h2 : k ≠ 2) :
    ∃ E : (ZMod N)ˣ → ℍ → ℂ, Good ι (k : ℤ) E ∧ ∀ a, coef (E a) 0 = 1 := by
  obtain ⟨f, h1, h0, hi⟩ := levelOne N k hk h2
  refine ⟨fun _ => f, ⟨fun _ => ⟨f, rfl⟩, fun _ _ γ _ _ => h1 γ, fun _ n => ?_⟩, fun _ => h0⟩
  obtain ⟨c, hc⟩ := hi n
  rw [hc, map_intCast]
  exact IsUltrametricDist.norm_intCast_le_one _ c

omit [NeZero N] in
/- English proof (translation)
Unfold `Lk`. Rewrite using `[map_div₀, map_pow, map_sub, map_one]`. Use `congr 1`. Conclude with `(Polynomial.aeval_algHom_apply (ι.symm.toRingHom.toIntAlgHom) x (numL k)).symm`.
-/
private lemma symm_Lk (k : ℕ) (x : ℂ) : ι.symm (Lk k x) = Lk k (ι.symm x) := by
  unfold Lk
  rw [map_div₀, map_pow, map_sub, map_one]
  congr 1
  exact (Polynomial.aeval_algHom_apply (ι.symm.toRingHom.toIntAlgHom) x (numL k)).symm

private def rt (ι : Qbar l ≃+* ℂ) (a : ZMod N) : Qbar l := ι.symm (ZMod.stdAddChar a : ℂ)

/- English proof (translation)
Unfold `rt`. Rewrite using `[AddChar.map_nsmul_eq_pow, map_pow]`.
-/
private lemma rt_pow (a : ZMod N) (n : ℕ) : rt ι a ^ n = rt ι (n • a) := by
  unfold rt
  rw [AddChar.map_nsmul_eq_pow, map_pow]

/- English proof (translation)
Simplify using `[rt]`.
-/
private lemma rt_zero : rt ι (0 : ZMod N) = 1 := by simp [rt]

/- English proof (translation)
The claim follows from `ι.symm.injective.comp ZMod.injective_stdAddChar`.
-/
private lemma rt_inj : Function.Injective (rt ι : ZMod N → Qbar l) :=
  ι.symm.injective.comp ZMod.injective_stdAddChar

/- English proof (translation)
Rewrite using `[rt_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, rt_zero]`.
-/
private lemma rt_powN (a : ZMod N) : rt ι a ^ N = 1 := by
  rw [rt_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, rt_zero]

/- English proof (translation)
Establish `h` using `congrArg norm (rt_powN (ι := ι) a)`. Rewrite `h` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne N)).1 h`.
-/
private lemma rt_norm (a : ZMod N) : ‖rt ι a‖ = 1 := by
  have h := congrArg norm (rt_powN (ι := ι) a)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne N)).1 h

/- English proof (translation)
Unfold `rt`. Rewrite using `[AddChar.map_neg_eq_inv, map_inv₀]`.
-/
private lemma rt_neg (a : ZMod N) : rt ι (-a) = (rt ι a)⁻¹ := by
  unfold rt
  rw [AddChar.map_neg_eq_inv, map_inv₀]

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[rt_pow, ← rt_zero (ι := ι) (N := N)]`. Establish `h1` using `rt_inj h`. Rewrite `h1` using `[nsmul_eq_mul, Units.mul_left_eq_zero, ZMod.natCast_eq_zero_iff]`. Use `Nat.le_of_dvd (by norm_num) h1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
private lemma rt_sq (hN : 3 ≤ N) (a : (ZMod N)ˣ) : rt ι (a : ZMod N) ^ 2 ≠ 1 := by
  intro h
  rw [rt_pow, ← rt_zero (ι := ι) (N := N)] at h
  have h1 := rt_inj h
  rw [nsmul_eq_mul, Units.mul_left_eq_zero, ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

/- English proof (translation)
Use `haveI : Fact (1 < N) := ⟨by omega⟩`. Conclude with `a.ne_zero`.
-/
private lemma unit_ne_zero (hN : 3 ≤ N) (a : (ZMod N)ˣ) : (a : ZMod N) ≠ 0 := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  exact a.ne_zero

/- English proof (translation)
Rewrite using `[(eisCoef N k hk a (unit_ne_zero hN a)).1, symm_Lk]`. Both sides reduce to the same expression.
-/
private lemma eis_coef0 (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (a : (ZMod N)ˣ) :
    ι.symm (coef (eisFun N k a) 0) = Lk k (rt ι (a : ZMod N)) := by
  rw [(eisCoef N k hk a (unit_ne_zero hN a)).1, symm_Lk]
  rfl

/- English proof (translation)
The claim follows from `eisMF N k hk a fam a b γ hγ h := by rw [h]; exact eisSlash N k hk a γ hγ int a n := by rcases Nat.eq_zero_or_pos n with rfl | hn · rw [eis_coef0 hN k hk] refine (lkSep l hl N (by omega) hlN).1 k _ (rt_powN _) fun h => rt_sq (ι := ι) hN a ?_ rw [h, one_pow] · rw [(eisCoef N k hk a …`.
-/
private lemma good_eis (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (k : ℕ) (hk : 3 ≤ k) :
    Good ι (k : ℤ) (fun a : (ZMod N)ˣ => eisFun N k a) where
  mf a := eisMF N k hk a
  fam a b γ hγ h := by
    rw [h]; exact eisSlash N k hk a γ hγ
  int a n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [eis_coef0 hN k hk]
      refine (lkSep l hl N (by omega) hlN).1 k _ (rt_powN _) fun h => rt_sq (ι := ι) hN a ?_
      rw [h, one_pow]
    · rw [(eisCoef N k hk a (unit_ne_zero hN a)).2 n hn, map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun e _ => ?_
      have hr : ∀ b : ZMod N, ‖ι.symm (ZMod.stdAddChar b : ℂ)‖ = 1 := fun b => rt_norm (ι := ι) b
      rw [map_mul ι.symm, norm_mul, map_pow ι.symm, map_natCast ι.symm, norm_pow, map_add ι.symm, map_mul ι.symm]
      refine mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ e))
        (norm_nonneg _) ?_
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_mul, hr, hr, map_pow ι.symm, map_neg ι.symm, map_one ι.symm, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        max_self]

/- English proof (translation)
Take `⟨E, hE, hE0⟩` from `good_one (ι := ι) (N := N) m hm h2`. Use `⟨m, _, hm, hH.comb hE (-coef (H d) 0) (by rw [map_neg, norm_neg]; exact hH.int d 0), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hH.coef_comb hE, hE0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hH.coef_comb hE, hE0, mul_one, ← sub_eq_add_neg, map_sub, hd]`.
-/
private lemma factor_of {m : ℕ} (hm : Even m) (h2 : m ≠ 2) {H : (ZMod N)ˣ → ℍ → ℂ} (hH : Good ι (m : ℤ) H)
    (d : (ZMod N)ˣ) (hd : ‖ι.symm (coef (H 1) 0) - ι.symm (coef (H d) 0)‖ = 1) :
    ∃ (m : ℕ) (h : (ZMod N)ˣ → ℍ → ℂ), Even m ∧ Good ι (m : ℤ) h ∧ coef (h d) 0 = 0 ∧
      ‖ι.symm (coef (h 1) 0)‖ = 1 := by
  obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) m hm h2
  refine ⟨m, _, hm, hH.comb hE (-coef (H d) 0) (by rw [map_neg, norm_neg]; exact hH.int d 0), ?_, ?_⟩
  · rw [hH.coef_comb hE, hE0]; ring
  · rw [hH.coef_comb hE, hE0, mul_one, ← sub_eq_add_neg, map_sub, hd]

/- English proof (translation)
Establish `g3` using `good_eis (ι := ι) hl hN hlN 3 le_rfl`. Establish `g4` using `good_eis (ι := ι) hl hN hlN 4 (by norm_num)`. Establish `g5` using `good_eis (ι := ι) hl hN hlN 5 (by norm_num)`. Establish `hx : rt ι (d : ZMod N) ≠ rt ι ((1 : (ZMod N)ˣ) : ZMod N)` using `fun h => h1 (Units.ext (rt_inj h))`. Establish `hy : rt ι (d : ZMod N) ≠ (rt ι ((1 : (ZMod N)ˣ) : ZMod N))⁻¹` using `fun h => by`.

Rewrite `h` using `[← rt_neg]`. Conclude with `h2 (Units.ext (rt_inj h))`. Break down `(lkSep l hl N (by omega) hlN).2.2 _ _ (rt_powN _) (rt_powN _) (rt_sq hN 1) (rt_sq hN d) hx hy with h | h | h` into its components or cases. Use `factor_of (m := 4) (by decide) (by decide) g4 d ?_` and prove the remaining obligations. Rewrite using `[eis_coef0 hN 4 (by norm_num), eis_coef0 hN 4 (by norm_num), h]`.

Use `factor_of (m := 6) (by decide) (by decide) (g3.mul g3) d ?_` and prove the remaining obligations. Rewrite using `[g3.coef_mul g3, g3.coef_mul g3, map_mul, map_mul, eis_coef0 hN 3 le_rfl, eis_coef0 hN 3 le_rfl, ← sq, ← sq, h]`. Use `factor_of (m := 8) (by decide) (by decide) (g3.mul g5) d ?_` and prove the remaining obligations. Rewrite using `[g3.coef_mul g5, g3.coef_mul g5, map_mul, map_mul, eis_coef0 hN 3 le_rfl, eis_coef0 hN 3 le_rfl, eis_coef0 hN 5 (by norm_num), eis_coef0 hN 5 (by norm_num), h]`.
-/
private lemma factor (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (d : (ZMod N)ˣ) (h1 : d ≠ 1) (h2 : d ≠ -1) :
    ∃ (m : ℕ) (h : (ZMod N)ˣ → ℍ → ℂ), Even m ∧ Good ι (m : ℤ) h ∧ coef (h d) 0 = 0 ∧
      ‖ι.symm (coef (h 1) 0)‖ = 1 := by
  have g3 := good_eis (ι := ι) hl hN hlN 3 le_rfl
  have g4 := good_eis (ι := ι) hl hN hlN 4 (by norm_num)
  have g5 := good_eis (ι := ι) hl hN hlN 5 (by norm_num)
  have hx : rt ι (d : ZMod N) ≠ rt ι ((1 : (ZMod N)ˣ) : ZMod N) := fun h => h1 (Units.ext (rt_inj h))
  have hy : rt ι (d : ZMod N) ≠ (rt ι ((1 : (ZMod N)ˣ) : ZMod N))⁻¹ := fun h => by
    rw [← rt_neg] at h
    exact h2 (Units.ext (rt_inj h))
  rcases (lkSep l hl N (by omega) hlN).2.2 _ _ (rt_powN _) (rt_powN _) (rt_sq hN 1) (rt_sq hN d) hx hy with h | h | h
  · refine factor_of (m := 4) (by decide) (by decide) g4 d ?_
    rw [eis_coef0 hN 4 (by norm_num), eis_coef0 hN 4 (by norm_num), h]
  · refine factor_of (m := 6) (by decide) (by decide) (g3.mul g3) d ?_
    rw [g3.coef_mul g3, g3.coef_mul g3, map_mul, map_mul, eis_coef0 hN 3 le_rfl, eis_coef0 hN 3 le_rfl, ← sq, ← sq, h]
  · refine factor_of (m := 8) (by decide) (by decide) (g3.mul g5) d ?_
    rw [g3.coef_mul g5, g3.coef_mul g5, map_mul, map_mul, eis_coef0 hN 3 le_rfl, eis_coef0 hN 3 le_rfl,
      eis_coef0 hN 5 (by norm_num), eis_coef0 hN 5 (by norm_num), h]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Take `⟨E, hE, hE0⟩` from `good_one (ι := ι) (N := N) 0 (by decide) (by decide)`. Conclude with `⟨0, E, by decide, hE, by simp, by rw [hE0, map_one, norm_one]⟩`. Consider the case `insert d S _ ih`.

Take `⟨m, h, hm, hg, h0, hu⟩` from `ih`. Distinguish the cases in `hd : d ≠ 1 ∧ d ≠ -1`. Take `⟨m', h', hm', hg', h0', hu'⟩` from `factor (ι := ι) hl hN hlN d hd.1 hd.2`. Use `⟨m + m', fun a => h a * h' a, hm.add hm', by exact_mod_cast hg.mul hg', fun e he e1 e2 => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg.coef_mul hg']`.

Break down `Finset.mem_insert.1 he with rfl | he` into its components or cases. Rewrite using `[h0', mul_zero]`. Rewrite using `[h0 e he e1 e2, zero_mul]`. Rewrite using `[hg.coef_mul hg', map_mul, norm_mul, hu, hu', mul_one]`. Use `⟨m, h, hm, hg, fun e he e1 e2 => ?_, hu⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.1 he with rfl | he` into its components or cases. Conclude with `absurd ⟨e1, e2⟩ hd`. Conclude with `h0 e he e1 e2`.
-/
private lemma killer (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (S : Finset (ZMod N)ˣ) :
    ∃ (m : ℕ) (h : (ZMod N)ˣ → ℍ → ℂ), Even m ∧ Good ι (m : ℤ) h ∧ (∀ d ∈ S, d ≠ 1 → d ≠ -1 → coef (h d) 0 = 0) ∧
      ‖ι.symm (coef (h 1) 0)‖ = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) 0 (by decide) (by decide)
    exact ⟨0, E, by decide, hE, by simp, by rw [hE0, map_one, norm_one]⟩
  | insert d S _ ih =>
    obtain ⟨m, h, hm, hg, h0, hu⟩ := ih
    by_cases hd : d ≠ 1 ∧ d ≠ -1
    · obtain ⟨m', h', hm', hg', h0', hu'⟩ := factor (ι := ι) hl hN hlN d hd.1 hd.2
      refine ⟨m + m', fun a => h a * h' a, hm.add hm', by exact_mod_cast hg.mul hg', fun e he e1 e2 => ?_, ?_⟩
      · rw [hg.coef_mul hg']
        rcases Finset.mem_insert.1 he with rfl | he
        · rw [h0', mul_zero]
        · rw [h0 e he e1 e2, zero_mul]
      · rw [hg.coef_mul hg', map_mul, norm_mul, hu, hu', mul_one]
    · refine ⟨m, h, hm, hg, fun e he e1 e2 => ?_, hu⟩
      rcases Finset.mem_insert.1 he with rfl | he
      · exact absurd ⟨e1, e2⟩ hd
      · exact h0 e he e1 e2

/- English proof (translation)
Introduce `γ hγ`. Take `⟨G, hG⟩` from `hg.mf a`. Rewrite using `[Nat.cast_add, ModularForm.mul_slash_SL2, ← hG]`. Conclude with `Filter.ZeroAtFilter.mul_boundedAtFilter (hf γ hγ) (ModularFormClass.bdd_at_infty_slash G γ)`.
-/
private lemma van_mul {k k' : ℕ} {f : ℍ → ℂ} (hf : VanOff N k f) {g : (ZMod N)ˣ → ℍ → ℂ} (hg : Good ι (k' : ℤ) g) (a) :
    VanOff N (k + k') (f * g a) := by
  intro γ hγ
  obtain ⟨G, hG⟩ := hg.mf a
  rw [Nat.cast_add, ModularForm.mul_slash_SL2, ← hG]
  exact Filter.ZeroAtFilter.mul_boundedAtFilter (hf γ hγ) (ModularFormClass.bdd_at_infty_slash G γ)

/- English proof (translation)
Establish `g3` using `good_eis (ι := ι) hl hN hlN 3 le_rfl`. Establish `v3 : ∀ a : (ZMod N)ˣ, VanOff N 3 (eisFun N 3 a)` using `fun a => eisVan N 3 le_rfl a a.isUnit (by omega)`. Establish `u3 : ‖ι.symm (coef (eisFun N 3 ((1 : (ZMod N)ˣ) : ZMod N)) 0)‖ = 1`. Rewrite using `[eis_coef0 hN 3 le_rfl]`. Conclude with `(lkSep l hl N (by omega) hlN).2.1 _ (rt_powN _) (rt_sq hN 1)`.

Establish `step : ∀ (j : ℕ) (g : (ZMod N)ˣ → ℍ → ℂ), Good ι (j : ℤ) g → ‖ι.symm (coef (g 1) 0)‖ = 1 → Good ι ((3 + j : ℕ) : ℤ) (fun a : (ZMod N)ˣ => eisFun N 3 a * g a) ∧ (∀ a : (ZMod N)ˣ, VanOff N (3 + j) (eisFun N 3 a * g a)) ∧ ‖ι.symm (coef (eisFun N 3 ((1 : (ZMod N)ˣ) : ZMod N) * g 1) 0 …` using `fun j g hg hu => ⟨by rw [Nat.cast_add]; exact g3.mul hg, fun a => van_mul (v3 a) hg a, by`. Rewrite using `[g3.coef_mul hg, map_mul, norm_mul, u3, hu, mul_one]⟩`. Break down `Nat.even_or_odd' k with ⟨t, rfl | rfl⟩` into its components or cases. Take `⟨E, hE, hE0⟩` from `good_one (ι := ι) (N := N) (2 * t - 6) ⟨t - 3, by omega⟩ (by omega)`. Take `⟨a1, -, a3⟩` from `step _ E hE (by rw [hE0, map_one, norm_one])`.

Use `step _ _ a1 a3` as an intermediate fact. Rewrite `this` using `[show 3 + (3 + (2 * t - 6)) = 2 * t by omega]`. Conclude with `⟨_, this⟩`. Take `⟨E, hE, hE0⟩` from `good_one (ι := ι) (N := N) (2 * t - 2) ⟨t - 1, by omega⟩ (by omega)`. Use `step _ E hE (by rw [hE0, map_one, norm_one])` as an intermediate fact.

Rewrite `this` using `[show 3 + (2 * t - 2) = 2 * t + 1 by omega]`. Conclude with `⟨_, this⟩`.
-/
private lemma base (hl : l ≠ 2) (hN : 3 ≤ N) (hlN : ¬ l ∣ N) (k : ℕ) (hk : 10 ≤ k) :
    ∃ f : (ZMod N)ˣ → ℍ → ℂ, Good ι (k : ℤ) f ∧ (∀ a, VanOff N k (f a)) ∧ ‖ι.symm (coef (f 1) 0)‖ = 1 := by
  have g3 := good_eis (ι := ι) hl hN hlN 3 le_rfl
  have v3 : ∀ a : (ZMod N)ˣ, VanOff N 3 (eisFun N 3 a) := fun a => eisVan N 3 le_rfl a a.isUnit (by omega)
  have u3 : ‖ι.symm (coef (eisFun N 3 ((1 : (ZMod N)ˣ) : ZMod N)) 0)‖ = 1 := by
    rw [eis_coef0 hN 3 le_rfl]
    exact (lkSep l hl N (by omega) hlN).2.1 _ (rt_powN _) (rt_sq hN 1)
  have step : ∀ (j : ℕ) (g : (ZMod N)ˣ → ℍ → ℂ), Good ι (j : ℤ) g → ‖ι.symm (coef (g 1) 0)‖ = 1 →
      Good ι ((3 + j : ℕ) : ℤ) (fun a : (ZMod N)ˣ => eisFun N 3 a * g a) ∧
      (∀ a : (ZMod N)ˣ, VanOff N (3 + j) (eisFun N 3 a * g a)) ∧
      ‖ι.symm (coef (eisFun N 3 ((1 : (ZMod N)ˣ) : ZMod N) * g 1) 0)‖ = 1 := fun j g hg hu =>
    ⟨by rw [Nat.cast_add]; exact g3.mul hg, fun a => van_mul (v3 a) hg a, by
      rw [g3.coef_mul hg, map_mul, norm_mul, u3, hu, mul_one]⟩
  rcases Nat.even_or_odd' k with ⟨t, rfl | rfl⟩
  · obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) (2 * t - 6) ⟨t - 3, by omega⟩ (by omega)
    obtain ⟨a1, -, a3⟩ := step _ E hE (by rw [hE0, map_one, norm_one])
    have := step _ _ a1 a3
    rw [show 3 + (3 + (2 * t - 6)) = 2 * t by omega] at this
    exact ⟨_, this⟩
  · obtain ⟨E, hE, hE0⟩ := good_one (ι := ι) (N := N) (2 * t - 2) ⟨t - 1, by omega⟩ (by omega)
    have := step _ E hE (by rw [hE0, map_one, norm_one])
    rw [show 3 + (2 * t - 2) = 2 * t + 1 by omega] at this
    exact ⟨_, this⟩

end

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
/- English proof (translation)
Introduce `l _ hl ι N _ hN hlN`. Take `⟨m, h, -, hg, h0, hu⟩` from `killer (ι := ι) hl hN hlN Finset.univ`. Use `⟨10 + m, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨j, rfl⟩ : ∃ j, k = j + m` from `⟨k - m, by omega⟩`. Take `⟨f, hf, hv, hfu⟩` from `base (ι := ι) hl hN hlN j (by omega)`.

Establish `hG : Good ι ((j + m : ℕ) : ℤ) (fun a => f a * h a)`. Rewrite using `[Nat.cast_add]`. Conclude with `hf.mul hg`. Use `choose F hF using hG.mf`. Use `⟨F, fun a b γ hγ hab => ?_, fun a => ?_, fun a => ?_, ?_, fun a a1 a2 => ?_⟩` and prove the remaining obligations.

Rewrite using `[hF, hF]`. Conclude with `hG.fam a b γ hγ hab`. Rewrite using `[hF]`. Conclude with `hG.int a`. Rewrite using `[hF]`.

Conclude with `van_mul (hv a) hg a`. Rewrite using `[hF, hf.coef_mul hg, map_mul, norm_mul, hfu, hu, mul_one]`. Rewrite using `[hF, hf.coef_mul hg, h0 a (Finset.mem_univ a) a1 a2, mul_zero]`.
-/
theorem UpperTheory.V.Sd.unitFam :
    UpperTheory.V.Sd.UnitFam := by
  intro l _ hl ι N _ hN hlN
  obtain ⟨m, h, -, hg, h0, hu⟩ := killer (ι := ι) hl hN hlN Finset.univ
  refine ⟨10 + m, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + m := ⟨k - m, by omega⟩
  obtain ⟨f, hf, hv, hfu⟩ := base (ι := ι) hl hN hlN j (by omega)
  have hG : Good ι ((j + m : ℕ) : ℤ) (fun a => f a * h a) := by
    rw [Nat.cast_add]; exact hf.mul hg
  choose F hF using hG.mf
  refine ⟨F, fun a b γ hγ hab => ?_, fun a => ?_, fun a => ?_, ?_, fun a a1 a2 => ?_⟩
  · rw [hF, hF]; exact hG.fam a b γ hγ hab
  · rw [hF]; exact hG.int a
  · rw [hF]; exact van_mul (hv a) hg a
  · rw [hF, hf.coef_mul hg, map_mul, norm_mul, hfu, hu, mul_one]
  · rw [hF, hf.coef_mul hg, h0 a (Finset.mem_univ a) a1 a2, mul_zero]
