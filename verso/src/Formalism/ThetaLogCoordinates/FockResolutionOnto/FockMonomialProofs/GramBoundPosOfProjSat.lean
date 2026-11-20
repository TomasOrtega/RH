import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementH
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundUnconditionalOfSat
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.Vanish

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset

/- English proof (translation)
Take `⟨Pr', hPr'⟩` from `hX p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) e1 hK hr hρ hv hP hE`. Establish `hSp` using `grSpan_eq LLw J M ρ w e e1 hr hρ hv he hP hE hO`. Use `⟨(LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) ∘ₗ Pr' ∘ₗ strip p (Fin.last K, ρ) e, ?_⟩` and prove the remaining obligations. Introduce `m hm`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply]`.

Distinguish the cases in `hme : m (Fin.last K, ρ) = e`. Take `⟨m', rfl⟩ : ∃ m', m = Finsupp.single (Fin.last K, ρ) e + m'` from `⟨m - Finsupp.single (Fin.last K, ρ) e, (add_tsub_cancel_of_le (by`. Rewrite using `[Finsupp.single_le_iff]`. Conclude with `hme.ge)).symm⟩`. Establish `hm0 : m' (Fin.last K, ρ) = 0` using `by simpa using hme`.

Establish `hmD` using `(multiDeg_pow LLw ρ e he m').mp hm`. Take `⟨h1, h2, h3⟩` from `hPr' m' hmD hm0`. Rewrite using `[strip_monomial_eq _ _ _ hm0]`. Use `⟨(hSp _).mpr ⟨_, h1, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_smul_comm, pow_mul_int_iff]`.

Conclude with `h2`. Introduce `g hg`. Take `⟨y, hy, rfl⟩` from `(hSp g).mp hg`. Rewrite using `[monomial_single_add, fock_pow_mul _ _ _ _ (xH_le_free _ J _ ρ _ y hy), fock_pow_mul _ _ _ _ (xH_le_free _ J _ ρ _ y hy), h3 y hy]`. Rewrite using `[strip_monomial_ne _ _ _ hme, map_zero, mul_zero]`.

Use `⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Take `⟨y, hy, rfl⟩` from `(hSp g).mp hg`. Rewrite using `[fock_eq_zero_of _ 0 (fun _ => Or.inr (coeff_zero _)), fock_eq_zero_of]`. Introduce `n`.

Distinguish the cases in `hn : n = m`. Use `left`. Rewrite using `[hn]`. Conclude with `coeff_pow_mul_ne _ _ y (xH_le_free _ J _ ρ _ y hy) m hme`. Use `right`.

Rewrite using `[coeff_monomial, if_neg (Ne.symm hn)]`.
-/
theorem projAt2_of (hX : HighestVectorProjectionPos) (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e e1 : ℕ) (hK : 1 ≤ K) (hr : 2 ≤ r)
    (hρ : (ρ : ℕ) = r - 1) (hv : LLw.vec (Fin.last K) = true) (he : e ≤ LLw.deg (Fin.last K))
    (hP : HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hE : HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hO : ResOntoK p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ) :
    ProjAt p LLw J M ρ w e ((K + 1) * e1) := by
  classical
  obtain ⟨Pr', hPr'⟩ := hX p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) e1
    hK hr hρ hv hP hE
  have hSp := grSpan_eq LLw J M ρ w e e1 hr hρ hv he hP hE hO
  refine ⟨(LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) ∘ₗ Pr' ∘ₗ
    strip p (Fin.last K, ρ) e, ?_⟩
  intro m hm
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  by_cases hme : m (Fin.last K, ρ) = e
  · obtain ⟨m', rfl⟩ : ∃ m', m = Finsupp.single (Fin.last K, ρ) e + m' :=
      ⟨m - Finsupp.single (Fin.last K, ρ) e, (add_tsub_cancel_of_le (by
        rw [Finsupp.single_le_iff]; exact hme.ge)).symm⟩
    have hm0 : m' (Fin.last K, ρ) = 0 := by simpa using hme
    have hmD := (multiDeg_pow LLw ρ e he m').mp hm
    obtain ⟨h1, h2, h3⟩ := hPr' m' hmD hm0
    rw [strip_monomial_eq _ _ _ hm0]
    refine ⟨(hSp _).mpr ⟨_, h1, rfl⟩, ?_, ?_⟩
    · rw [← mul_smul_comm, pow_mul_int_iff]; exact h2
    · intro g hg
      obtain ⟨y, hy, rfl⟩ := (hSp g).mp hg
      rw [monomial_single_add, fock_pow_mul _ _ _ _ (xH_le_free _ J _ ρ _ y hy),
        fock_pow_mul _ _ _ _ (xH_le_free _ J _ ρ _ y hy), h3 y hy]
  · rw [strip_monomial_ne _ _ _ hme, map_zero, mul_zero]
    refine ⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, ?_⟩
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (hSp g).mp hg
    rw [fock_eq_zero_of _ 0 (fun _ => Or.inr (coeff_zero _)), fock_eq_zero_of]
    intro n
    by_cases hn : n = m
    · left
      rw [hn]
      exact coeff_pow_mul_ne _ _ y (xH_le_free _ J _ ρ _ y hy) m hme
    · right
      rw [coeff_monomial, if_neg (Ne.symm hn)]

/- English proof (translation)
Introduce `p _ K r _ LLw q J M ρ e1 c0 κ hK hr hρ hv hPE hS hκ w e k g hli hspan`. Distinguish the cases in `he : e ≤ LLw.deg (Fin.last K)`. Take `⟨hP, hE⟩` from `hPE (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)`. Use `graded_piece_bound_holds p K r LLw J M ρ w e ((K + 1) * e1) (e1 + c0) κ (projAt2_of hX p K r LLw J M ρ w e e1 hK hr hρ hv he hP hE (resOntoK_of_resSatL _ J _ ρ c0 (hS e he))) (satAtL LLw J M ρ w e e1 c0 hr hρ hv he hP hE (hS e he)) ?_ k g hli hspan` and prove the remaining obligations. Establish `: (K + 1) * e1 + 2 * (e1 + c0) = (K + 3) * e1 + 2 * c0` using `by ring`.

Rewrite using `[this]`. Conclude with `hκ`. Rewrite `hspan` using `[graded_bot_holds p K r LLw J M ρ w e (not_le.mp he)]`. Establish `hk : k = 0`. Assume the negation of the conclusion as `hk`.

Establish `h0 : g ⟨0, Nat.pos_of_ne_zero hk⟩ ∈ Submodule.span ℤ_[p] (Set.range g)` using `Submodule.subset_span ⟨_, rfl⟩`. Rewrite `h0` using `[hspan, Submodule.mem_bot]`. Conclude with `hli.ne_zero _ h0`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.
-/
theorem graded_bound_pos_of_proj (hX : HighestVectorProjectionPos) : GradedBoundOfSaturationPos := by
  intro p _ K r _ LLw q J M ρ e1 c0 κ hK hr hρ hv hPE hS hκ w e k g hli hspan
  by_cases he : e ≤ LLw.deg (Fin.last K)
  · obtain ⟨hP, hE⟩ := hPE (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
    refine graded_piece_bound_holds p K r LLw J M ρ w e ((K + 1) * e1) (e1 + c0) κ
      (projAt2_of hX p K r LLw J M ρ w e e1 hK hr hρ hv he hP hE (resOntoK_of_resSatL _ J _ ρ c0 (hS e he)))
      (satAtL LLw J M ρ w e e1 c0 hr hρ hv he hP hE (hS e he)) ?_ k g hli hspan
    have : (K + 1) * e1 + 2 * (e1 + c0) = (K + 3) * e1 + 2 * c0 := by ring
    rw [this]; exact hκ
  · rw [graded_bot_holds p K r LLw J M ρ w e (not_le.mp he)] at hspan
    have hk : k = 0 := by
      by_contra hk
      have h0 : g ⟨0, Nat.pos_of_ne_zero hk⟩ ∈ Submodule.span ℤ_[p] (Set.range g) :=
        Submodule.subset_span ⟨_, rfl⟩
      rw [hspan, Submodule.mem_bot] at h0
      exact hli.ne_zero _ h0
    subst hk
    simp

section Zero

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use `⟨x, hY, hi, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, one_smul, ← resL_apply, resL_of_free _ x hF]`.
-/
theorem self_lift {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hF : x ∈ FreeOf p (Fin.last K, ρ))
    (hY : x ∈ Y p LL J M) (hi : x ∈ IntPol p (Fin (K + 1) × Fin r)) :
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧
      initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ 0) • x := by
  refine ⟨x, hY, hi, ?_⟩
  rw [pow_zero, one_smul, ← resL_apply, resL_of_free _ x hF]

/- English proof (translation)
Use `le_ycond LL j _ _ ?_ (fun a b x hx => Formalism.CountingSumsFrames.glAct_pol LL j a b x hx)` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Pol, mem_restrictSupport_iff]`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `m hm`.

Establish `h1 : MultiDeg LL m` using `hx hm`. Establish `h2` using `abs_wt_le LL j (0 : Fin r) m`. Establish `h3 : (∑ v, m v) = LL.total`. Rewrite using `[Fintype.sum_prod_type]`. Unfold `Letters.total`.

Conclude with `Finset.sum_congr rfl fun i _ => h1 i`. Use `show ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((c : ℤ) : WithTop ℤ)`. Rewrite using `[WithTop.coe_le_coe]`. Establish `h4` using `le_abs_self (wt LL j (0 : Fin r) m)`. Rewrite `h2` using `[h3]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem pol_le_ycond_total {r N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (c : ℤ) (hc : (LL.total : ℤ) ≤ c) :
    Pol p r LL ≤ YCond p LL j ((c : ℤ) : WithTop ℤ) := by
  refine le_ycond LL j _ _ ?_ (fun a b x hx => Formalism.CountingSumsFrames.glAct_pol LL j a b x hx)
  intro x hx
  rw [Pol, mem_restrictSupport_iff] at hx
  rw [mem_restrictSupport_iff]
  intro m hm
  have h1 : MultiDeg LL m := hx hm
  have h2 := abs_wt_le LL j (0 : Fin r) m
  have h3 : (∑ v, m v) = LL.total := by
    rw [Fintype.sum_prod_type]
    unfold Letters.total
    exact Finset.sum_congr rfl fun i _ => h1 i
  show ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((c : ℤ) : WithTop ℤ)
  rw [WithTop.coe_le_coe]
  have h4 := le_abs_self (wt LL j (0 : Fin r) m)
  rw [h3] at h2
  omega

end Zero

/- English proof (translation)
Introduce `p _ r _ LL q J M ρ hr hρ hv x hx hxi`. Take `⟨hxP, hxF, hxk⟩` from `(mem_xsp LL J M ρ x).mp hx`. Distinguish the cases in `hfin : ∃ k, 0 + 1 ≤ J k ∧ M k ≠ ⊤`. Take `⟨k1, hk1, hM1⟩` from `hfin`. Establish `hne : (univ.filter fun k => 0 + 1 ≤ J k).Nonempty` using `⟨k1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk1⟩⟩`.

Take `⟨k0, hk0, hmin⟩` from `Finset.exists_min_image _ M hne`. Establish `hk0' : 0 + 1 ≤ J k0` using `(Finset.mem_filter.mp hk0).2`. Establish `hmin' : ∀ k, 0 + 1 ≤ J k → M k0 ≤ M k` using `fun k hk => hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)`. Establish `hM0 : M k0 ≠ ⊤` using `fun h => hM1 (top_le_iff.mp (h ▸ hmin' k1 hk1))`. Take `⟨c, hc⟩` from `WithTop.ne_top_iff_exists.mp hM0`.

Distinguish the cases in `hcd : c < LL.total`. Establish `hT : x ∈ TypesLE p LL (0 + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ)`. Rewrite using `[hc]`. Conclude with `((hxk k0).1 hk0').2`. Establish `htot : LL.total = LL.deg (Fin.last 0)`.

Unfold `Letters.total`. Simplify using the standard rewrite rules. Establish `hV` using `space_vanishing_holds p 0 r LL ρ c (LL.deg (Fin.last 0)) hr hρ hv (by`. Rewrite `hcd` using `[htot]`. Simplify using `using hcd)`.

Rewrite `hV` using `[setLast_self]`. Establish `hx0 : x = 0`. Establish `: x ∈ Pol p r LL ⊓ FreeOf p (Fin.last 0, ρ) ⊓ TypesLE p LL (0 + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ)` using `Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hxP, hxF⟩, hT⟩`. Rewrite `this` using `[hV]`. Conclude with `(Submodule.mem_bot _).mp this`.

Substitute `hx0` using the available equality. Conclude with `self_lift LL J M ρ 0 hxF (Submodule.zero_mem _) hxi`. Use `self_lift LL J M ρ x hxF ((mem_y LL J M x).mpr ⟨hxP, fun k => ?_⟩) hxi` and prove the remaining obligations. Distinguish the cases in `hk : 0 + 1 ≤ J k`. Conclude with `ycond_mono LL (J k) _ _ (hc ▸ hmin' k hk) (pol_le_ycond_total LL (J k) c (not_lt.mp hcd) hxP)`.

Conclude with `(hxk k).2 hk`. Use `self_lift LL J M ρ x hxF ((mem_y LL J M x).mpr ⟨hxP, fun k => ?_⟩) hxi` and prove the remaining obligations. Distinguish the cases in `hk : 0 + 1 ≤ J k`. Establish `: M k = ⊤`. Assume the negation of the conclusion as `hne`.

Conclude with `hfin ⟨k, hk, hne⟩`. Rewrite using `[this, Formalism.CountingSumsFrames.ycond_top]`. Conclude with `Submodule.mem_top`. Conclude with `(hxk k).2 hk`.
-/
theorem restricted_saturation_zero : ResSatLZero := by
  intro p _ r _ LL q J M ρ hr hρ hv x hx hxi
  obtain ⟨hxP, hxF, hxk⟩ := (mem_xsp LL J M ρ x).mp hx
  by_cases hfin : ∃ k, 0 + 1 ≤ J k ∧ M k ≠ ⊤
  · obtain ⟨k1, hk1, hM1⟩ := hfin
    have hne : (univ.filter fun k => 0 + 1 ≤ J k).Nonempty := ⟨k1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk1⟩⟩
    obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image _ M hne
    have hk0' : 0 + 1 ≤ J k0 := (Finset.mem_filter.mp hk0).2
    have hmin' : ∀ k, 0 + 1 ≤ J k → M k0 ≤ M k := fun k hk =>
      hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
    have hM0 : M k0 ≠ ⊤ := fun h => hM1 (top_le_iff.mp (h ▸ hmin' k1 hk1))
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hM0
    by_cases hcd : c < LL.total
    · have hT : x ∈ TypesLE p LL (0 + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) := by
        rw [hc]; exact ((hxk k0).1 hk0').2
      have htot : LL.total = LL.deg (Fin.last 0) := by
        unfold Letters.total
        simp
      have hV := space_vanishing_holds p 0 r LL ρ c (LL.deg (Fin.last 0)) hr hρ hv (by
        rw [htot] at hcd
        simpa using hcd)
      rw [setLast_self] at hV
      have hx0 : x = 0 := by
        have : x ∈ Pol p r LL ⊓ FreeOf p (Fin.last 0, ρ) ⊓
            TypesLE p LL (0 + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) :=
          Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hxP, hxF⟩, hT⟩
        rw [hV] at this
        exact (Submodule.mem_bot _).mp this
      subst hx0
      exact self_lift LL J M ρ 0 hxF (Submodule.zero_mem _) hxi
    · refine self_lift LL J M ρ x hxF ((mem_y LL J M x).mpr ⟨hxP, fun k => ?_⟩) hxi
      by_cases hk : 0 + 1 ≤ J k
      · exact ycond_mono LL (J k) _ _ (hc ▸ hmin' k hk) (pol_le_ycond_total LL (J k) c (not_lt.mp hcd) hxP)
      · exact (hxk k).2 hk
  · refine self_lift LL J M ρ x hxF ((mem_y LL J M x).mpr ⟨hxP, fun k => ?_⟩) hxi
    by_cases hk : 0 + 1 ≤ J k
    · have : M k = ⊤ := by
        by_contra hne
        exact hfin ⟨k, hk, hne⟩
      rw [this, Formalism.CountingSumsFrames.ycond_top]
      exact Submodule.mem_top
    · exact (hxk k).2 hk

/- English proof (translation)
Introduce `p _ K r _ LLw q J M ρ a κ hr hρ hv ht hκ`. Break down `Nat.eq_zero_or_pos K with rfl | hK` into its components or cases. Use `graded_bound_saturation_holds p 0 r LLw J M ρ (kapC p r LLw.total) 0 κ hr hρ hv (hypPE_setLast LLw ρ) (fun e _ => restricted_saturation_zero p r _ J _ ρ hr hρ hv) ?_` and prove the remaining obligations. Rewrite using `[Nat.mul_zero, Nat.add_zero]`. Conclude with `(kappa_numeric_holds p 0 r a LLw.total hr ht).trans hκ`.

Use `graded_bound_pos_of_proj hX p K r LLw J M ρ (kapC p r LLw.total) (2 * (r.choose 2 * Nat.log p (4 * LLw.total + r - 1))) κ hK hr hρ hv (hypPE_setLast LLw ρ) ?_ (le_trans ?_ hκ)` and prove the remaining obligations. Introduce `e _`. Establish `ht'` using `setLast_total_le LLw (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)`. Conclude with `resSatL_mono _ J _ ρ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega)))) (hS p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ hr hρ hv)`. Establish `h1` using `numeric_product_inequality p a r (LLw.total + r - 1) (by omega)`.

Establish `h2` using `numeric_product_inequality p a r (4 * LLw.total + r - 1) (by omega)`. Establish `hQ` using `lg_nonneg p a r`. Establish `hK1 : (1 : ℝ) ≤ K` using `by exact_mod_cast hK`. Establish `hKQ` using `mul_nonneg (sub_nonneg.mpr hK1) hQ`. Establish `h3 : ((K : ℝ) + 3) * ((kapC p r LLw.total : ℕ) : ℝ) ≤ ((K : ℝ) + 3) * ((r : ℝ) ^ 2 / 2 * lgV2 p a r)` using `mul_le_mul_of_nonneg_left h1 (by positivity)`.

Rewrite using `[Nat.cast_add, Nat.cast_mul, Nat.cast_mul (2 : ℕ), Nat.cast_mul (2 : ℕ)]`. Move the coercions through the operations in `at h2 h3 ⊢`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gram_bound_pos_of_proj_sat (hX : HighestVectorProjectionPos) (hS : ResSatLThm) : GramBoundUnconditionalPos := by
  intro p _ K r _ LLw q J M ρ a κ hr hρ hv ht hκ
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · refine graded_bound_saturation_holds p 0 r LLw J M ρ (kapC p r LLw.total) 0 κ hr hρ hv (hypPE_setLast LLw ρ)
      (fun e _ => restricted_saturation_zero p r _ J _ ρ hr hρ hv) ?_
    rw [Nat.mul_zero, Nat.add_zero]
    exact (kappa_numeric_holds p 0 r a LLw.total hr ht).trans hκ
  · refine graded_bound_pos_of_proj hX p K r LLw J M ρ (kapC p r LLw.total)
      (2 * (r.choose 2 * Nat.log p (4 * LLw.total + r - 1))) κ hK hr hρ hv (hypPE_setLast LLw ρ) ?_ (le_trans ?_ hκ)
    · intro e _
      have ht' := setLast_total_le LLw (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
      exact resSatL_mono _ J _ ρ
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))))
        (hS p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ hr hρ hv)
    · have h1 := numeric_product_inequality p a r (LLw.total + r - 1) (by omega)
      have h2 := numeric_product_inequality p a r (4 * LLw.total + r - 1) (by omega)
      have hQ := lg_nonneg p a r
      have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have hKQ := mul_nonneg (sub_nonneg.mpr hK1) hQ
      have h3 : ((K : ℝ) + 3) * ((kapC p r LLw.total : ℕ) : ℝ) ≤ ((K : ℝ) + 3) * ((r : ℝ) ^ 2 / 2 * lgV2 p a r) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul (2 : ℕ), Nat.cast_mul (2 : ℕ)]
      push_cast at h2 h3 ⊢
      nlinarith

/- English proof (translation)
Take `⟨C₀, hC₀, hM⟩` from `Formalism.InvariantFactorPaths.PW.Top.lattice_theorem_height_bound`. Use `⟨C₀, hC₀, ?_⟩` and prove the remaining obligations. Introduce `p _ N r _ _ LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS' hdeg hz hκ hineq`. Use `hM p N r LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS' hdeg hz hκ hineq ?_` and prove the remaining obligations. Introduce `n hn i`.

Conclude with `gram_bound_pos_of_proj_sat hX hS p (T.pos i) r _ T.J (T.thrUpTo i) ρ a κ hr hρ (takeD_vec_last LL T hadm n i) (takeD_total_le LL T hadm a Yl n₀ dd hS' hdeg n (grid_le T Yl n₀ dd n hn) i) ((pos_num LL T hadm p a r i).trans hκ)`.
-/
theorem theoremMFree0_of (hX : HighestVectorProjectionPos) (hS : ResSatLThm) : TheoremMFree0 := by
  obtain ⟨C₀, hC₀, hM⟩ := Formalism.InvariantFactorPaths.PW.Top.lattice_theorem_height_bound
  refine ⟨C₀, hC₀, ?_⟩
  intro p _ N r _ _ LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS' hdeg hz hκ hineq
  refine hM p N r LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS' hdeg hz hκ hineq ?_
  intro n hn i
  exact gram_bound_pos_of_proj_sat hX hS p (T.pos i) r _ T.J (T.thrUpTo i) ρ a κ hr hρ (takeD_vec_last LL T hadm n i)
    (takeD_total_le LL T hadm a Yl n₀ dd hS' hdeg n (grid_le T Yl n₀ dd n hn) i)
    ((pos_num LL T hadm p a r i).trans hκ)

end Formalism.InvariantFactorPaths.L4
