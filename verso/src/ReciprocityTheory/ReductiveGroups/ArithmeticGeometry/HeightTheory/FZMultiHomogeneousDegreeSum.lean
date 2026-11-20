import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ProdZpowEqZpowSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KerPLeOfPlace

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section Swap

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

def swapT : TVar D N ≃ TVar D N := Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl _)

def swapS : (Fin (D + 1) × Fin N) ≃ (Fin (D + 1) × Fin N) :=
  Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl _)

/- English proof (translation)
Establish `key : ∀ p : TVar D N, chiImg j₀ x (swapT p) = rename swapS (chiImg j₀ x p)`. Introduce and unpack `⟨b, j⟩`. Break down `Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩` into its components or cases. Simplify using `[chiImg, swapT, swapS, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same, map_sum, map_neg]`. Simplify using `[chiImg, swapT, swapS, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]`.

Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp [chiP]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, rename_X]`.

Simplify using `only [chiP, aeval_X, key]`.
-/
theorem chiP_rename_swap (j₀ : Fin (N + 1)) (x : Fin N → Ω) (g : MvPolynomial (TVar D N) K) :
    chiP (K := K) j₀ x (rename swapT g) = rename swapS (chiP (K := K) j₀ x g) := by
  have key : ∀ p : TVar D N, chiImg j₀ x (swapT p) = rename swapS (chiImg j₀ x p) := by
    rintro ⟨b, j⟩
    rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩
    · simp [chiImg, swapT, swapS, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same, map_sum, map_neg]
    · simp [chiImg, swapT, swapS, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
  induction g using MvPolynomial.induction_on with
  | C a => simp [chiP]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    simp only [chiP, aeval_X, key]

/- English proof (translation)
Rewrite `hg`, the goal using `[kerP, RingHom.mem_ker]`. Establish `hg' : chiP (K` using `K) j₀ x g = 0 := hg`. Use `show chiP (K := K) j₀ x (rename swapT g) = 0`. Rewrite using `[chiP_rename_swap, hg', map_zero]`.
-/
theorem rename_swap_mem_ker_eval (j₀ : Fin (N + 1)) (x : Fin N → Ω) (g : MvPolynomial (TVar D N) K)
    (hg : g ∈ kerP (K := K) (D := D) j₀ x) : rename swapT g ∈ kerP (K := K) (D := D) j₀ x := by
  rw [kerP, RingHom.mem_ker] at hg ⊢
  have hg' : chiP (K := K) j₀ x g = 0 := hg
  show chiP (K := K) j₀ x (rename swapT g) = 0
  rw [chiP_rename_swap, hg', map_zero]

end Swap

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Establish `hy : d.rationalBaseRow c ≠ 0` using `d.lineRatio_ne_zero hd c`. Take `⟨hfin, hall⟩` from `d.norm_by_places hd h c`. Take `⟨hSy, κ, hκ, hN⟩` from `hall _ hy`. Use `set T := hSy.toFinset with hT`. Use `set Gm : Ideal (KTp K d.D d.N) → KTf K d.D d.N := fun p => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hGm`.

Use `set a : Ideal (KTp K d.D d.N) → ℤ := fun p => ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p), (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) with ha`. Use `set b : Ideal (KTp K d.D d.N) → ℤ := fun p => d.nPMM h c (d.w (d.jc c) c) p with hb`. Establish `hmemT : ∀ p, p ∈ T ↔ p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0` using `fun p => Set.Finite.mem_toFinset hSy`. Establish `hGne : ∀ p ∈ d.HtOne, Gm p ≠ 0` using `fun p hp => by`. Simplify using `only [hGm]`.

Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).mpr (d.generator_ne_zero_of_height p hp)`. Establish `hoff : ∀ p ∈ d.HtOne, p ∉ T → ∀ w ∈ d.OverP c p, w (d.rationalBaseRow c) = 0`. Introduce `p hp hpT w hw`. Assume the negation of the conclusion as `hne`. Conclude with `hpT ((hmemT p).mpr ⟨hp, w, hw, hne⟩)`.

Establish `ha0 : ∀ p ∈ d.HtOne, p ∉ T → a p = 0`. Introduce `p hp hpT`. Simplify using `only [ha]`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)]`. Use `Finset.sum_eq_zero fun w hw => ?_` and prove the remaining obligations.

Rewrite using `[hoff p hp hpT w ((Set.Finite.mem_toFinset _).mp hw)]`. Simplify using the standard rewrite rules. Establish `hb0 : ∀ p ∈ d.HtOne, p ∉ T → b p = 0`. Introduce `p hp hpT`. Simplify using `only [hb, Data.nPMM]`.

Establish `hGf : (d.GoodP c p).Finite` using `(hfin p hp).subset fun w hw => hw.1`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hGf]`. Use `Finset.sum_eq_zero fun w hw => ?_` and prove the remaining obligations. Establish `hw'` using `(Set.Finite.mem_toFinset _).mp hw`. Use `d.good_valuation_balance hd h c p hp w hw'` as an intermediate fact.

Rewrite `this` using `[hoff p hp hpT w hw'.1]`. Simplify using `at this`. Rewrite using `[this, mul_zero]`. Establish `hab : ∀ p ∈ d.HtOne, 0 ≤ a p + b p`. Introduce `p hp`.

Establish `hGf : (d.GoodP c p).Finite` using `(hfin p hp).subset fun w hw => hw.1`. Establish `e1 : a p = ∑ w ∈ (hfin p hp).toFinset, (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c))` using `finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)`. Establish `e2 : b p = ∑ w ∈ (hfin p hp).toFinset, if w ∈ d.GoodP c p then (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c) else 0`. Rewrite using `[← Finset.sum_filter]`. Simplify using `only [hb, Data.nPMM]`.

Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hGf]`. Use `congr 1`. Use extensionality with `w`. Simplify using `only [Set.Finite.mem_toFinset, Finset.mem_filter]`. Conclude with `⟨fun hw => ⟨hw.1, hw⟩, fun hw => hw.2⟩`.

Rewrite using `[e1, e2, ← Finset.sum_add_distrib]`. Use `Finset.sum_nonneg fun w hw => ?_` and prove the remaining obligations. Establish `hwO` using `(Set.Finite.mem_toFinset _).mp hw`. Distinguish the cases in `hg : w ∈ d.GoodP c p`. Rewrite using `[if_pos hg, ← mul_add, d.good_valuation_balance hd h c p hp w hg, mul_zero]`.

Rewrite using `[if_neg hg, add_zero]`. Use `mul_nonneg (by positivity) (untopD_nonneg ?_)` and prove the remaining obligations. Use `d.lineRatio_val_nonneg c p w hwO fun a0 ha0' => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hg ⟨hwO, a0, ha0', hne⟩`.

Establish `hTsub : (T : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne` using `fun p hp => ((hmemT p).mp hp).1`. Establish `e1 : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), Gm p ^ a p) = ∏ p ∈ T, Gm p ^ a p`. Use `finprod_mem_eq_prod_of_subset _ ?_ hTsub` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hne⟩`. Assume the negation of the conclusion as `hpT`.

Conclude with `hne (by simp only [ha0 p hp hpT, zpow_zero])`. Establish `e2 : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), Gm p ^ b p) = ∏ p ∈ T, Gm p ^ b p`. Use `finprod_mem_eq_prod_of_subset _ ?_ hTsub` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hne⟩`. Assume the negation of the conclusion as `hpT`.

Conclude with `hne (by simp only [hb0 p hp hpT, zpow_zero])`. Establish `hfZ : d.fZ h c = algebraMap K (KTf K d.D d.N) κ * ∏ p ∈ T, Gm p ^ (a p + b p)`. Establish `hN'` using `hN`. Unfold `Data.fZ`. Rewrite using `[hN', e1, e2, mul_assoc, ← Finset.prod_mul_distrib]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun p hp => (zpow_add₀ (hGne p (hTsub hp)) _ _).symm` and prove the remaining obligations. Use `⟨κ, hκ, T, fun p => (a p + b p).toNat, fun p hp => hTsub hp, ?_, ?_⟩` and prove the remaining obligations. Apply `IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)` to reduce the goal to its premises. Rewrite using `[hF, hfZ, map_mul, map_prod, ← d.algebraMap_K_KTf]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hab p (hTsub hp))]`. Introduce `p hpT he`. Establish `hp` using `hTsub hpT`.

Establish `hne : a p + b p ≠ 0` using `fun h0 => he (by simp only [h0, Int.toNat_zero])`. Establish `hGf : (d.GoodP c p).Finite` using `(hfin p hp).subset fun w hw => hw.1`. Establish `e1 : a p = ∑ w ∈ (hfin p hp).toFinset, (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c))` using `finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)`. Establish `e2 : b p = ∑ w ∈ (hfin p hp).toFinset, if w ∈ d.GoodP c p then (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c) else 0`. Rewrite using `[← Finset.sum_filter]`.

Simplify using `only [hb, Data.nPMM]`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hGf]`. Use `congr 1`. Use extensionality with `w`. Simplify using `only [Set.Finite.mem_toFinset, Finset.mem_filter]`.

Conclude with `⟨fun hw => ⟨hw.1, hw⟩, fun hw => hw.2⟩`. Rewrite `hne` using `[e1, e2, ← Finset.sum_add_distrib]`. Take `⟨w, hwF, hw0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hne`. Establish `hwO` using `(Set.Finite.mem_toFinset _).mp hwF`. Distinguish the cases in `hg : w ∈ d.GoodP c p`.

Rewrite `hw0` using `[if_pos hg, ← mul_add, d.good_valuation_balance hd h c p hp w hg, mul_zero]`. Conclude with `absurd rfl hw0`. Rewrite `hw0` using `[if_neg hg, add_zero]`. Establish `htriv : ∀ a0 : Ω c, a0 ≠ 0 → d.Wres c w a0 = 0` using `fun a0 ha0 => by`. Assume the negation of the conclusion as `hne'`.

Conclude with `hg ⟨hwO, a0, ha0, hne'⟩`. Establish `hnn` using `d.lineRatio_val_nonneg c p w hwO htriv`. Establish `hu : WithTop.untopD 0 (w (d.rationalBaseRow c)) ≠ 0` using `right_ne_zero_of_mul hw0`. Conclude with `⟨w, hwO, htriv, lt_of_le_of_ne hnn fun h0 => hu (by rw [← h0]; rfl)⟩`.
-/
theorem fZ_factor_height_one_primes (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ κ : K, κ ≠ 0 ∧ ∃ T : Finset (Ideal (KTp K d.D d.N)), ∃ e : Ideal (KTp K d.D d.N) → ℕ,
      (∀ p ∈ T, p ∈ d.HtOne) ∧ F = C κ * ∏ p ∈ T, d.gen p ^ e p ∧
      ∀ p ∈ T, e p ≠ 0 → ∃ w ∈ d.OverP c p, (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∧
        0 < w (d.rationalBaseRow c) := by
  classical
  have hy : d.rationalBaseRow c ≠ 0 := d.lineRatio_ne_zero hd c
  obtain ⟨hfin, hall⟩ := d.norm_by_places hd h c
  obtain ⟨hSy, κ, hκ, hN⟩ := hall _ hy
  set T := hSy.toFinset with hT
  set Gm : Ideal (KTp K d.D d.N) → KTf K d.D d.N :=
    fun p => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hGm
  set a : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) with ha
  set b : Ideal (KTp K d.D d.N) → ℤ := fun p => d.nPMM h c (d.w (d.jc c) c) p with hb
  have hmemT : ∀ p, p ∈ T ↔ p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0 := fun p =>
    Set.Finite.mem_toFinset hSy
  have hGne : ∀ p ∈ d.HtOne, Gm p ≠ 0 := fun p hp => by
    simp only [hGm]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).mpr
      (d.generator_ne_zero_of_height p hp)

  have hoff : ∀ p ∈ d.HtOne, p ∉ T → ∀ w ∈ d.OverP c p, w (d.rationalBaseRow c) = 0 := by
    intro p hp hpT w hw
    by_contra hne
    exact hpT ((hmemT p).mpr ⟨hp, w, hw, hne⟩)
  have ha0 : ∀ p ∈ d.HtOne, p ∉ T → a p = 0 := by
    intro p hp hpT
    simp only [ha]
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)]
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [hoff p hp hpT w ((Set.Finite.mem_toFinset _).mp hw)]
    simp
  have hb0 : ∀ p ∈ d.HtOne, p ∉ T → b p = 0 := by
    intro p hp hpT
    simp only [hb, Data.nPMM]
    have hGf : (d.GoodP c p).Finite := (hfin p hp).subset fun w hw => hw.1
    rw [finsum_mem_eq_finite_toFinset_sum _ hGf]
    refine Finset.sum_eq_zero fun w hw => ?_
    have hw' := (Set.Finite.mem_toFinset _).mp hw
    have := d.good_valuation_balance hd h c p hp w hw'
    rw [hoff p hp hpT w hw'.1] at this
    simp at this
    rw [this, mul_zero]
  have hab : ∀ p ∈ d.HtOne, 0 ≤ a p + b p := by
    intro p hp
    have hGf : (d.GoodP c p).Finite := (hfin p hp).subset fun w hw => hw.1
    have e1 : a p = ∑ w ∈ (hfin p hp).toFinset,
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) :=
      finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)
    have e2 : b p = ∑ w ∈ (hfin p hp).toFinset,
        if w ∈ d.GoodP c p then (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c) else 0 := by
      rw [← Finset.sum_filter]
      simp only [hb, Data.nPMM]
      rw [finsum_mem_eq_finite_toFinset_sum _ hGf]
      congr 1
      ext w
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
      exact ⟨fun hw => ⟨hw.1, hw⟩, fun hw => hw.2⟩
    rw [e1, e2, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun w hw => ?_
    have hwO := (Set.Finite.mem_toFinset _).mp hw
    by_cases hg : w ∈ d.GoodP c p
    · rw [if_pos hg, ← mul_add, d.good_valuation_balance hd h c p hp w hg, mul_zero]
    · rw [if_neg hg, add_zero]
      refine mul_nonneg (by positivity) (untopD_nonneg ?_)
      refine d.lineRatio_val_nonneg c p w hwO fun a0 ha0' => ?_
      by_contra hne
      exact hg ⟨hwO, a0, ha0', hne⟩
  have hTsub : (T : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne := fun p hp => ((hmemT p).mp hp).1
  have e1 : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), Gm p ^ a p) = ∏ p ∈ T, Gm p ^ a p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTsub
    rintro p ⟨hp, hne⟩
    by_contra hpT
    exact hne (by simp only [ha0 p hp hpT, zpow_zero])
  have e2 : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), Gm p ^ b p) = ∏ p ∈ T, Gm p ^ b p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTsub
    rintro p ⟨hp, hne⟩
    by_contra hpT
    exact hne (by simp only [hb0 p hp hpT, zpow_zero])
  have hfZ : d.fZ h c = algebraMap K (KTf K d.D d.N) κ * ∏ p ∈ T, Gm p ^ (a p + b p) := by
    have hN' := hN
    unfold Data.fZ
    rw [hN', e1, e2, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p hp => (zpow_add₀ (hGne p (hTsub hp)) _ _).symm
  refine ⟨κ, hκ, T, fun p => (a p + b p).toNat, fun p hp => hTsub hp, ?_, ?_⟩
  · apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
    rw [hF, hfZ, map_mul, map_prod, ← d.algebraMap_K_KTf]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hab p (hTsub hp))]
  · intro p hpT he
    have hp := hTsub hpT
    have hne : a p + b p ≠ 0 := fun h0 => he (by simp only [h0, Int.toNat_zero])
    have hGf : (d.GoodP c p).Finite := (hfin p hp).subset fun w hw => hw.1
    have e1 : a p = ∑ w ∈ (hfin p hp).toFinset,
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) :=
      finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)
    have e2 : b p = ∑ w ∈ (hfin p hp).toFinset,
        if w ∈ d.GoodP c p then (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c) else 0 := by
      rw [← Finset.sum_filter]
      simp only [hb, Data.nPMM]
      rw [finsum_mem_eq_finite_toFinset_sum _ hGf]
      congr 1
      ext w
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
      exact ⟨fun hw => ⟨hw.1, hw⟩, fun hw => hw.2⟩
    rw [e1, e2, ← Finset.sum_add_distrib] at hne
    obtain ⟨w, hwF, hw0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hwO := (Set.Finite.mem_toFinset _).mp hwF
    by_cases hg : w ∈ d.GoodP c p
    · rw [if_pos hg, ← mul_add, d.good_valuation_balance hd h c p hp w hg, mul_zero] at hw0
      exact absurd rfl hw0
    · rw [if_neg hg, add_zero] at hw0
      have htriv : ∀ a0 : Ω c, a0 ≠ 0 → d.Wres c w a0 = 0 := fun a0 ha0 => by
        by_contra hne'
        exact hg ⟨hwO, a0, ha0, hne'⟩
      have hnn := d.lineRatio_val_nonneg c p w hwO htriv
      have hu : WithTop.untopD 0 (w (d.rationalBaseRow c)) ≠ 0 := right_ne_zero_of_mul hw0
      exact ⟨w, hwO, htriv, lt_of_le_of_ne hnn fun h0 => hu (by rw [← h0]; rfl)⟩

/- English proof (translation)
Take `⟨κ, hκ, T, e, hT, hFeq, hplace⟩` from `d.fZ_factor_height_one_primes hd h c F hF`. Use `set P := kerP (K := K) (D := d.D) (d.jc c) (d.x c) with hP`. Establish `hker : ∀ p ∈ T, e p ≠ 0 → p = P`. Introduce `p hp hep`. Take `⟨w, hw, htriv, hy⟩` from `hplace p hp hep`.

Conclude with `(d.ker_eval_eq_of_place hd c (hT p hp) hw htriv hy).symm`. Distinguish the cases in `hex : ∃ p ∈ T, e p ≠ 0`. Take `⟨p0, hp0, hep0⟩` from `hex`. Establish `hPone : P ∈ d.HtOne`. Rewrite using `[← hker p0 hp0 hep0]`.

Conclude with `hT p0 hp0`. Establish `hg0 : d.gen P ≠ 0` using `d.generator_ne_zero_of_height P hPone`. Establish `hprin : P.IsPrincipal`. Assume the negation of the conclusion as `hnp`. Apply `hg0` to reduce the goal to its premises.

Unfold `Data.gen`. Rewrite using `[dif_neg hnp]`. Establish `hgspan : Ideal.span {d.gen P} = P`. Unfold `Data.gen`. Rewrite using `[dif_pos hprin]`.

Conclude with `Ideal.span_singleton_generator P`. Establish `hFg : F = C κ * d.gen P ^ (∑ p ∈ T, e p)`. Rewrite using `[hFeq, ← Finset.prod_pow_eq_pow_sum]`. Use `congr 1`. Use `Finset.prod_congr rfl fun p hp => ?_` and prove the remaining obligations.

Distinguish the cases in `hep : e p = 0`. Rewrite using `[hep, pow_zero, pow_zero]`. Rewrite using `[hker p hp hep]`. Establish `hren : ∃ r : K, rename swapT (d.gen P) = C r * d.gen P`. Establish `hmem0 : d.gen P ∈ P`.

Establish `h1` using `Ideal.mem_span_singleton_self (d.gen P)`. Rewrite `h1` using `[hgspan]`. Then use the resulting hypothesis. Establish `hmem : rename swapT (d.gen P) ∈ P` using `rename_swap_mem_ker_eval (K := K) (D := d.D) (d.jc c) (d.x c) _ hmem0`. Establish `hmem' : rename swapT (d.gen P) ∈ Ideal.span {d.gen P}`. Rewrite using `[hgspan]`.

Conclude with `hmem`. Rewrite `hmem'` using `[Ideal.mem_span_singleton]`. Take `⟨q, hq⟩` from `hmem'`. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hq` using `[mul_zero]`. Apply `hg0` to reduce the goal to its premises. Apply `MvPolynomial.rename_injective _ (swapT (D := d.D) (N := d.N)).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `hq`.

Establish `hdeg` using `MvPolynomial.totalDegree_rename_le (swapT (D := d.D) (N := d.N)) (d.gen P)`. Rewrite `hdeg` using `[hq, MvPolynomial.totalDegree_mul_of_isDomain hg0 hq0]`. Establish `hq' : q.totalDegree = 0` using `by omega`. Rewrite `hq'` using `[MvPolynomial.totalDegree_eq_zero_iff_eq_C]`. Take `⟨a, ha⟩ : ∃ a : K, q = C a` from `⟨_, hq'⟩`.

Conclude with `⟨a, by rw [hq, ha, mul_comm]⟩`. Take `⟨r, hr⟩` from `hren`. Use `⟨r ^ (∑ p ∈ T, e p), ?_⟩` and prove the remaining obligations. Rewrite using `[hFg, map_mul, MvPolynomial.rename_C, map_pow, hr, mul_pow, ← map_pow]`. Expand and normalize the polynomial expressions, which then agree.

Use `push_neg at hex`. Establish `hF1 : F = C κ`. Rewrite using `[hFeq]`. Establish `h1 : ∏ p ∈ T, d.gen p ^ e p = 1` using `Finset.prod_eq_one fun p hp => by rw [hex p hp, pow_zero]`. Rewrite using `[h1, mul_one]`.

Conclude with `⟨1, by rw [hF1, MvPolynomial.rename_C, map_one, one_mul]⟩`.
-/
theorem rename_swap_F (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ ρ : K, rename swapT F = C ρ * F := by
  classical
  obtain ⟨κ, hκ, T, e, hT, hFeq, hplace⟩ := d.fZ_factor_height_one_primes hd h c F hF
  set P := kerP (K := K) (D := d.D) (d.jc c) (d.x c) with hP
  have hker : ∀ p ∈ T, e p ≠ 0 → p = P := by
    intro p hp hep
    obtain ⟨w, hw, htriv, hy⟩ := hplace p hp hep
    exact (d.ker_eval_eq_of_place hd c (hT p hp) hw htriv hy).symm
  by_cases hex : ∃ p ∈ T, e p ≠ 0
  · obtain ⟨p0, hp0, hep0⟩ := hex
    have hPone : P ∈ d.HtOne := by
      rw [← hker p0 hp0 hep0]
      exact hT p0 hp0
    have hg0 : d.gen P ≠ 0 := d.generator_ne_zero_of_height P hPone
    have hprin : P.IsPrincipal := by
      by_contra hnp
      apply hg0
      unfold Data.gen
      rw [dif_neg hnp]
    have hgspan : Ideal.span {d.gen P} = P := by
      unfold Data.gen
      rw [dif_pos hprin]
      exact Ideal.span_singleton_generator P
    have hFg : F = C κ * d.gen P ^ (∑ p ∈ T, e p) := by
      rw [hFeq, ← Finset.prod_pow_eq_pow_sum]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      by_cases hep : e p = 0
      · rw [hep, pow_zero, pow_zero]
      · rw [hker p hp hep]
    have hren : ∃ r : K, rename swapT (d.gen P) = C r * d.gen P := by
      have hmem0 : d.gen P ∈ P := by
        have h1 := Ideal.mem_span_singleton_self (d.gen P)
        rwa [hgspan] at h1
      have hmem : rename swapT (d.gen P) ∈ P := rename_swap_mem_ker_eval (K := K) (D := d.D) (d.jc c) (d.x c) _ hmem0
      have hmem' : rename swapT (d.gen P) ∈ Ideal.span {d.gen P} := by
        rw [hgspan]
        exact hmem
      rw [Ideal.mem_span_singleton] at hmem'
      obtain ⟨q, hq⟩ := hmem'
      have hq0 : q ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hq
        apply hg0
        apply MvPolynomial.rename_injective _ (swapT (D := d.D) (N := d.N)).injective
        rw [map_zero]
        exact hq
      have hdeg := MvPolynomial.totalDegree_rename_le (swapT (D := d.D) (N := d.N)) (d.gen P)
      rw [hq, MvPolynomial.totalDegree_mul_of_isDomain hg0 hq0] at hdeg
      have hq' : q.totalDegree = 0 := by omega
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq'
      obtain ⟨a, ha⟩ : ∃ a : K, q = C a := ⟨_, hq'⟩
      exact ⟨a, by rw [hq, ha, mul_comm]⟩
    obtain ⟨r, hr⟩ := hren
    refine ⟨r ^ (∑ p ∈ T, e p), ?_⟩
    rw [hFg, map_mul, MvPolynomial.rename_C, map_pow, hr, mul_pow, ← map_pow]
    ring
  · push_neg at hex
    have hF1 : F = C κ := by
      rw [hFeq]
      have h1 : ∏ p ∈ T, d.gen p ^ e p = 1 := Finset.prod_eq_one fun p hp => by rw [hex p hp, pow_zero]
      rw [h1, mul_one]
    exact ⟨1, by rw [hF1, MvPolynomial.rename_C, map_one, one_mul]⟩

/- English proof (translation)
Take `⟨F', hF', hF'0⟩` from `d.componentForm_poly hd h c`. Establish `hFF : F = F'` using `IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) (hF.trans hF'.symm)`. Establish `hF0 : F ≠ 0` using `hFF ▸ hF'0`. Take `⟨hdeg0, hdegb⟩` from `d.F_degrees hd h c F hF`. Take `⟨ρ, hρ⟩` from `d.rename_swap_F hd h c F hF`.

Establish `h10 : (1 : Fin (d.D + 1)) ≠ 0`. Establish `hD` using `hd.D_ge`. Introduce `h1`. Establish `h2` using `congrArg (fun i : Fin (d.D + 1) => (i : ℕ)) h1`. Use `first`.

Consider the case `(simp only [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (show 1 < d.D + 1 by omega)] at h2; omega)`. Consider the case `(simp at h2; omega)`. Consider the case `(simp [Fin.val_one'] at h2; omega)`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : F.support.Nonempty := by`. Rewrite using `[Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]`.

Conclude with `hF0`. Establish `ht : s.mapDomain swapT ∈ F.support`. Establish `h1 : (rename swapT F).coeff (s.mapDomain swapT) = F.coeff s` using `MvPolynomial.coeff_rename_mapDomain _ (swapT (D := d.D) (N := d.N)).injective F s`. Rewrite `h1` using `[hρ, MvPolynomial.coeff_C_mul]`. Rewrite `hs`, the goal using `[MvPolynomial.mem_support_iff]`.

Introduce `h0`. Rewrite `h1` using `[h0, mul_zero]`. Conclude with `hs h1.symm`. Establish `key : (d.aMM h c).toNat = d.delc c`. Rewrite using `[← hdegb 1 h10 s hs, ← hdeg0 _ ht]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hsw : (swapT (D` using `d.D) (N := d.N)) (1, j) = (0, j) := by`. Simplify using `[swapT, Equiv.swap_apply_right]`. Rewrite using `[← hsw, Finsupp.mapDomain_apply (swapT (D := d.D) (N := d.N)).injective]`. Establish `hA : d.aMM h c = d.delc c`.

Establish `h1` using `d.aMM_nonneg hd h c`. Use linear arithmetic over natural numbers and integers. Use `⟨?_, hA⟩` and prove the remaining obligations. Introduce `s' hs' b`. Distinguish the cases in `hb : b = 0`.

Substitute `hb` using the available equality. Conclude with `hdeg0 s' hs'`. Rewrite using `[hdegb b hb s' hs', key]`.
-/
theorem fZ_multiHomogeneous_degree_sum (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) F ∧
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)) = d.delc c := by
  classical
  obtain ⟨F', hF', hF'0⟩ := d.componentForm_poly hd h c
  have hFF : F = F' := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) (hF.trans hF'.symm)
  have hF0 : F ≠ 0 := hFF ▸ hF'0
  obtain ⟨hdeg0, hdegb⟩ := d.F_degrees hd h c F hF
  obtain ⟨ρ, hρ⟩ := d.rename_swap_F hd h c F hF
  have h10 : (1 : Fin (d.D + 1)) ≠ 0 := by
    have hD := hd.D_ge
    intro h1
    have h2 := congrArg (fun i : Fin (d.D + 1) => (i : ℕ)) h1
    first
    | (simp only [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (show 1 < d.D + 1 by omega)] at h2; omega)
    | (simp at h2; omega)
    | (simp [Fin.val_one'] at h2; omega)
  obtain ⟨s, hs⟩ : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hF0
  have ht : s.mapDomain swapT ∈ F.support := by
    have h1 : (rename swapT F).coeff (s.mapDomain swapT) = F.coeff s :=
      MvPolynomial.coeff_rename_mapDomain _ (swapT (D := d.D) (N := d.N)).injective F s
    rw [hρ, MvPolynomial.coeff_C_mul] at h1
    rw [MvPolynomial.mem_support_iff] at hs ⊢
    intro h0
    rw [h0, mul_zero] at h1
    exact hs h1.symm
  have key : (d.aMM h c).toNat = d.delc c := by
    rw [← hdegb 1 h10 s hs, ← hdeg0 _ ht]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsw : (swapT (D := d.D) (N := d.N)) (1, j) = (0, j) := by
      simp [swapT, Equiv.swap_apply_right]
    rw [← hsw, Finsupp.mapDomain_apply (swapT (D := d.D) (N := d.N)).injective]
  have hA : d.aMM h c = d.delc c := by
    have h1 := d.aMM_nonneg hd h c
    omega
  refine ⟨?_, hA⟩
  intro s' hs' b
  by_cases hb : b = 0
  · subst hb
    exact hdeg0 s' hs'
  · rw [hdegb b hb s' hs', key]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
