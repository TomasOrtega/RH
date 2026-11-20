import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNmSectionsRational
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsRationalProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]`.

Establish `hsub : ∀ f : (Σ k, ι k) → Ω, ∏ p ∈ m.support, f p ^ m p = ∏ p, f p ^ m p` using `fun f => Finset.prod_subset (Finset.subset_univ _) (fun p _ hp => by simp [Finsupp.notMem_support_iff.mp hp])`. Establish `hden : ∏ p, y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ d k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = _`.

Rewrite using `[Finset.prod_pow_eq_pow_sum, hg m hm k]`. Simplify using `only [hsub, div_pow, Finset.prod_div_distrib, hden, zpow_neg, zpow_natCast, Finset.prod_inv_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_mul_prod_zpow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {d : K → ℕ} {g : MRing ι}
    (hg : IsMultiHomog g d) :
    aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  have hsub : ∀ f : (Σ k, ι k) → Ω, ∏ p ∈ m.support, f p ^ m p = ∏ p, f p ^ m p := fun f =>
    Finset.prod_subset (Finset.subset_univ _) (fun p _ hp => by simp [Finsupp.notMem_support_iff.mp hp])
  have hden : ∏ p, y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  simp only [hsub, div_pow, Finset.prod_div_distrib, hden, zpow_neg, zpow_natCast, Finset.prod_inv_distrib]
  ring

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `x hx`. Establish `hle : chartRingZ y c ≤ (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)).restrictScalars ℤ` using `Algebra.adjoin_le Algebra.subset_adjoin`. Conclude with `hle hx`.
-/
theorem chartRingZ_le [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    (chartRingZ y c : Set Ω) ⊆
      Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) := by
  intro x hx
  have hle : chartRingZ y c ≤
      (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)).restrictScalars ℤ :=
    Algebra.adjoin_le Algebra.subset_adjoin
  exact hle hx

/- English proof (translation)
Use `set A := Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)`. Establish `hmem : ∀ {d : K → ℕ} {g : MRing ι}, IsMultiHomog g d → aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) ∈ A`. Introduce `d g hg`. Rewrite using `[aeval_mul_prod_zpow y c hg]`. Use `chartRingZ_le y c ?_` and prove the remaining obligations.

Rewrite using `[chartRingZ, Algebra.adjoin_range_eq_range_aeval]`. Conclude with `⟨g, rfl⟩`. Use `IsFractionRing.of_field A Ω fun z => ?_` and prove the remaining obligations. Take `⟨d, g, h, hg, hh, hh0, hgh⟩` from `hbir z`. Establish `hP : (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)`.

Use `⟨⟨_, hmem hg⟩, ⟨_, hmem hh⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z = aeval y g * _ / (aeval y h * _)`. Rewrite using `[hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]`.
-/
theorem isFractionRing_chart [CharZero Ω] (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    IsFractionRing (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) Ω := by
  set A := Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
  have hmem : ∀ {d : K → ℕ} {g : MRing ι}, IsMultiHomog g d →
      aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) ∈ A := by
    intro d g hg
    rw [aeval_mul_prod_zpow y c hg]
    refine chartRingZ_le y c ?_
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨g, rfl⟩
  refine IsFractionRing.of_field A Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  refine ⟨⟨_, hmem hg⟩, ⟨_, hmem hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]

/- English proof (translation)
Establish `hnat : ∀ (n : ℕ) {z : Ω}, z ∈ Algebra.adjoin ℤ S → (n : Ω) * z ∈ Algebra.adjoin ℤ S` using `fun n z hz => Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ n) hz`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem z hz => exact ⟨1, le_rfl, by simpa using Algebra.subset_adjoin hz⟩`. Consider the case `algebraMap q`. Use `⟨q.den, q.den_pos, ?_⟩` and prove the remaining obligations.

Establish `hq : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω)`. Rewrite using `[eq_ratCast, Rat.cast_def, mul_div_cancel₀ _ (by exact_mod_cast q.den_ne_zero)]`. Rewrite using `[hq]`. Conclude with `Subalgebra.intCast_mem _ _`. Consider the case `add u v _ _ hu hv`.

Take `⟨n₁, h₁, hu⟩` from `hu`. Take `⟨n₂, h₂, hv⟩` from `hv`. Use `⟨n₁ * n₂, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩` and prove the remaining obligations. Establish `: ((n₁ * n₂ : ℕ) : Ω) * (u + v) = (n₂ : Ω) * ((n₁ : Ω) * u) + (n₁ : Ω) * ((n₂ : Ω) * v)` using `by push_cast; ring`. Rewrite using `[this]`.

Conclude with `add_mem (hnat _ hu) (hnat _ hv)`. Consider the case `mul u v _ _ hu hv`. Take `⟨n₁, h₁, hu⟩` from `hu`. Take `⟨n₂, h₂, hv⟩` from `hv`. Use `⟨n₁ * n₂, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩` and prove the remaining obligations.

Establish `: ((n₁ * n₂ : ℕ) : Ω) * (u * v) = ((n₁ : Ω) * u) * ((n₂ : Ω) * v)` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `Subalgebra.mul_mem _ hu hv`.
-/
theorem exists_nat_mul_mem_adjoin_int [CharZero Ω] {S : Set Ω} {x : Ω} (hx : x ∈ Algebra.adjoin ℚ S) :
    ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * x ∈ Algebra.adjoin ℤ S := by
  have hnat : ∀ (n : ℕ) {z : Ω}, z ∈ Algebra.adjoin ℤ S → (n : Ω) * z ∈ Algebra.adjoin ℤ S :=
    fun n z hz => Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ n) hz
  induction hx using Algebra.adjoin_induction with
  | mem z hz => exact ⟨1, le_rfl, by simpa using Algebra.subset_adjoin hz⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_pos, ?_⟩
    have hq : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      rw [eq_ratCast, Rat.cast_def, mul_div_cancel₀ _ (by exact_mod_cast q.den_ne_zero)]
    rw [hq]
    exact Subalgebra.intCast_mem _ _
  | add u v _ _ hu hv =>
    obtain ⟨n₁, h₁, hu⟩ := hu
    obtain ⟨n₂, h₂, hv⟩ := hv
    refine ⟨n₁ * n₂, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    have : ((n₁ * n₂ : ℕ) : Ω) * (u + v) = (n₂ : Ω) * ((n₁ : Ω) * u) + (n₁ : Ω) * ((n₂ : Ω) * v) := by
      push_cast; ring
    rw [this]
    exact add_mem (hnat _ hu) (hnat _ hv)
  | mul u v _ _ hu hv =>
    obtain ⟨n₁, h₁, hu⟩ := hu
    obtain ⟨n₂, h₂, hv⟩ := hv
    refine ⟨n₁ * n₂, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    have : ((n₁ * n₂ : ℕ) : Ω) * (u * v) = ((n₁ : Ω) * u) * ((n₂ : Ω) * v) := by
      push_cast; ring
    rw [this]
    exact Subalgebra.mul_mem _ hu hv

/- English proof (translation)
Use `set A := Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)`. Use `isFractionRing_chart y hbir c hc` as an intermediate fact. Establish `: IsIntegrallyClosed A` using `hnorm c hc`. Set `φ : chartRingZ y c →+* A` to `(Subring.inclusion fun z hz => chartRingZ_le y c hz : (chartRingZ y c).toSubring →+* A.toSubring)`. Establish `hxA : IsIntegral A x` using `IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (by ext; rfl) (hx : IsIntegral _ x)`.

Take `⟨z, hz⟩` from `(IsIntegrallyClosed.isIntegral_iff (K := Ω)).mp hxA`. Establish `hxm : x ∈ A` using `hz ▸ z.2`. Conclude with `exists_nat_mul_mem_adjoin_int hxm`.
-/
theorem exists_nat_mul_mem_chartRingZ [CharZero Ω] (y : (Σ k, ι k) → Ω) (hbir : Birational y)
    (hnorm : KH.NormalGenericFibre y) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * x ∈ chartRingZ y c := by
  set A := Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
  have := isFractionRing_chart y hbir c hc
  have : IsIntegrallyClosed A := hnorm c hc
  let φ : chartRingZ y c →+* A := (Subring.inclusion fun z hz => chartRingZ_le y c hz :
    (chartRingZ y c).toSubring →+* A.toSubring)
  have hxA : IsIntegral A x :=
    IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (by ext; rfl) (hx : IsIntegral _ x)
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (K := Ω)).mp hxA
  have hxm : x ∈ A := hz ▸ z.2
  exact exists_nat_mul_mem_adjoin_int hxm

end NmSectionsRationalProof

open NmSectionsRationalProof in

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y a ha hy hbir hnorm`. Take `⟨τ₀, hτ₀⟩` from `h K ι Ω y a ha hy`. Use `⟨τ₀, fun τ hτ s hs => ?_⟩` and prove the remaining obligations. Establish `hchart : ∀ c : ∀ k, ι k, ∃ m : ℕ, 1 ≤ m ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) → (m : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ)))) ∈ chartRingZ y c)`. Introduce `c`.

Distinguish the cases in `hc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Take `⟨m, hm, hmem⟩` from `exists_nat_mul_mem_chartRingZ y hbir hnorm c hc (hs c hc)`. Conclude with `⟨m, hm, fun _ => hmem⟩`. Conclude with `⟨1, le_rfl, fun h' => absurd h' hc⟩`. Use `choose m hm1 hm using hchart`.

Use `⟨∏ c, m c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_pos fun c _ => hm1 c).ne', ?_⟩` and prove the remaining obligations. Rewrite using `[← hτ₀ τ hτ]`. Introduce `c hc`. Establish `hsplit : (∏ c', m c' : ℕ) = (∏ c' ∈ Finset.univ.erase c, m c') * m c` using `(Finset.prod_erase_mul _ _ (Finset.mem_univ c)).symm`. Establish `hval : ((∏ c', m c' : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ))) = ((∏ c' ∈ Finset.univ.erase c, m c' : ℕ) : Ω) * ((m c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ)))))`.

Rewrite using `[hsplit]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hval]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hm c hc)`.
-/
theorem NmSectionsRational.proof (h : KH.SecEqStatement) : NmSectionsRational.Statement := by
  intro K _ ι _ Ω _ _ y a ha hy hbir hnorm
  obtain ⟨τ₀, hτ₀⟩ := h K ι Ω y a ha hy
  refine ⟨τ₀, fun τ hτ s hs => ?_⟩
  classical
  have hchart : ∀ c : ∀ k, ι k, ∃ m : ℕ, 1 ≤ m ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (m : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ)))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨m, hm, hmem⟩ := exists_nat_mul_mem_chartRingZ y hbir hnorm c hc (hs c hc)
      exact ⟨m, hm, fun _ => hmem⟩
    · exact ⟨1, le_rfl, fun h' => absurd h' hc⟩
  choose m hm1 hm using hchart
  refine ⟨∏ c, m c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_pos fun c _ => hm1 c).ne', ?_⟩
  rw [← hτ₀ τ hτ]
  intro c hc
  have hsplit : (∏ c', m c' : ℕ) = (∏ c' ∈ Finset.univ.erase c, m c') * m c :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ c)).symm
  have hval : ((∏ c', m c' : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ))) =
      ((∏ c' ∈ Finset.univ.erase c, m c' : ℕ) : Ω) *
        ((m c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ))))) := by
    rw [hsplit]; push_cast; ring
  rw [hval]
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hm c hc)

end GroundTheory.Heights₂.Heights.HilbertSamuel
