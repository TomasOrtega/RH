import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCodimOneCompleteIntersection
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RegularQuotientGenerators
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalizationAtPrimeQuotient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAC
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

noncomputable section

/- English proof (translation)
Establish `: FiniteRingKrullDim A` using `finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h => by`. Establish `h0` using `ringKrullDim_nonneg_of_nontrivial (R := A)`. Rewrite `h0` using `[h]`. Conclude with `absurd h0 (by simp), hfin⟩`. Take `⟨s, hs⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ A`.

Conclude with `ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (fun M N hM hN => (hs M hM).trans (hs N hN).symm) q`.
-/
theorem ringKrullDim_quotient_add_height_of_finiteType {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsJacobsonRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (hfin : ringKrullDim A ≠ ⊤) (q : Ideal A)
    [q.IsPrime] : ringKrullDim (A ⧸ q) + (q.height : WithBot ℕ∞) = ringKrullDim A := by
  have : FiniteRingKrullDim A :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h => by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := A)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ A
  exact ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (fun M N hM hN => (hs M hM).trans (hs N hN).symm) q

/- English proof (translation)
Establish `: IsDomain (Localization.AtPrime q)` using `IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors q)`. Establish `: IsIntegrallyClosed (Localization.AtPrime q)` using `isIntegrallyClosed_of_isLocalization _ q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors q)`. Establish `hdB : ringKrullDim (Localization.AtPrime q) = 1`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]`. Both sides reduce to the same expression.

Establish `: Ring.KrullDimLE 1 (Localization.AtPrime q)` using `Ring.krullDimLE_iff.mpr (by rw [hdB]; rfl)`. Establish `h3 : IsIntegrallyClosed (Localization.AtPrime q) ∧ ∀ p : Ideal (Localization.AtPrime q), p ≠ ⊥ → p.IsPrime → p = maximalIdeal (Localization.AtPrime q)` using `⟨inferInstance, fun p hp0 hpp => eq_maximalIdeal (hpp.isMaximal_of_ne_bot hp0)⟩`. Establish `: IsDedekindDomain (Localization.AtPrime q)` using `((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)).out 3 2).mp h3`. Use `⟨IsRegularLocalRing.of_ringEquiv eqv, ?_⟩` and prove the remaining obligations. Rewrite using `[← ringKrullDim_eq_of_ringEquiv eqv, IsLocalization.AtPrime.ringKrullDim_eq_height (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime (maximalIdeal (Localization.AtPrime q))), IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdB]`.
-/
theorem isRegularLocalRing_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1) {C : Type*} [CommRing C]
    (eqv : Localization.AtPrime (maximalIdeal (Localization.AtPrime q)) ≃+* C) :
    IsRegularLocalRing C ∧ ringKrullDim C = 1 := by
  have : IsDomain (Localization.AtPrime q) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors q)
  have : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors q)
  have hdB : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
    rfl
  have : Ring.KrullDimLE 1 (Localization.AtPrime q) := Ring.krullDimLE_iff.mpr (by rw [hdB]; rfl)
  have h3 : IsIntegrallyClosed (Localization.AtPrime q) ∧
      ∀ p : Ideal (Localization.AtPrime q), p ≠ ⊥ → p.IsPrime → p = maximalIdeal (Localization.AtPrime q) :=
    ⟨inferInstance, fun p hp0 hpp => eq_maximalIdeal (hpp.isMaximal_of_ne_bot hp0)⟩
  have : IsDedekindDomain (Localization.AtPrime q) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)).out 3 2).mp h3
  refine ⟨IsRegularLocalRing.of_ringEquiv eqv, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv eqv,
    IsLocalization.AtPrime.ringKrullDim_eq_height (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime (maximalIdeal (Localization.AtPrime q))),
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdB]

/- English proof (translation)
Introduce `σ _ P Q e hP hQ hPQ hint hdP hdQ`. Establish `hdS : ringKrullDim (MvPolynomial σ ℂ) = (Fintype.card σ : ℕ)`. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, zero_add]`. Take `⟨hgt, hhgt⟩ : ∃ k : ℕ, Q.height = k` from `ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ h => h.symm`. Establish `hQh : hgt + e = Fintype.card σ`.

Establish `h` using `ringKrullDim_quotient_add_height_of_finiteType (A := MvPolynomial σ ℂ) (by rw [hdS]; exact ne_of_beq_false rfl) Q`. Rewrite `h` using `[hdQ, hdS, hhgt]`. Establish `h' : e + hgt = Fintype.card σ` using `by exact_mod_cast h`. Use linear arithmetic over natural numbers and integers. Take `⟨Qb, hQb_def⟩ : ∃ Qb, Qb = Q.map (Ideal.Quotient.mk P)` from `⟨_, rfl⟩`.

Establish `hQbp : Qb.IsPrime` using `hQb_def ▸ Ideal.isPrime_map_quotientMk_of_isPrime hPQ`. Establish `: Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ P)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)`. Establish `: IsDomain (MvPolynomial σ ℂ ⧸ P)` using `Ideal.Quotient.isDomain P`. Establish `hQb : Qb.height = 1`. Take `⟨k, hk⟩ : ∃ k : ℕ, Qb.height = k` from `ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ h => h.symm`.

Establish `h` using `ringKrullDim_quotient_add_height_of_finiteType (A := MvPolynomial σ ℂ ⧸ P) (by rw [hdP]; exact ne_of_beq_false rfl) Qb`. Establish `hq : ringKrullDim ((MvPolynomial σ ℂ ⧸ P) ⧸ Qb) = ringKrullDim (MvPolynomial σ ℂ ⧸ Q)`. Rewrite using `[hQb_def]`. Conclude with `ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ)`. Rewrite `h` using `[hq, hdQ, hdP, hk]`.

Establish `h' : e + k = e + 1` using `by exact_mod_cast h`. Rewrite using `[hk]`. Conclude with `(by omega : k = 1)` after adjusting the coercions. Establish `hdR : ringKrullDim (Localization.AtPrime Q) = (hgt : WithBot ℕ∞)`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q), hhgt]`.

Both sides reduce to the same expression. Establish `hcomap : (maximalIdeal (Localization.AtPrime Qb)).comap ((algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime Qb)).comp (Ideal.Quotient.mk P)) = Q`. Rewrite using `[← Ideal.comap_comap]`. Express the relevant statement in the definitionally equal form `(Ideal.under _ (maximalIdeal (Localization.AtPrime Qb))).comap (Ideal.Quotient.mk P) = Q`. Rewrite using `[Localization.AtPrime.under_maximalIdeal, hQb_def, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.mpr hPQ]`.

Take `⟨eqv, -⟩` from `LocalizationAtPrimeQuotient.proof (MvPolynomial σ ℂ) P Qb.primeCompl (maximalIdeal (Localization.AtPrime Qb)) Q hcomap`. Take `⟨hregRI, hdRI⟩` from `isRegularLocalRing_of_height_eq_one Qb hQb eqv`. Establish `hgt1 : 1 ≤ hgt`. Establish `h` using `ringKrullDim_quotient_le (P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)))`. Rewrite `h` using `[hdRI, hdR]`.

Conclude with `h` after adjusting the coercions. Take `⟨f, hfI, hfspan⟩` from `exists_span_eq_of_isRegularLocalRing_quotient (hgt - 1) (Localization.AtPrime Q) (P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q))) (by`. Rewrite using `[hdR, hdRI]`. Establish `: hgt = 1 + (hgt - 1)` using `by omega`. Conclude with `this)` after adjusting the coercions.

Establish `hnum : ∀ j, ∃ a ∈ P, ∃ s ∈ Q.primeCompl, f j * algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) s = algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) a`. Introduce `j`. Take `⟨⟨a, s⟩, h⟩` from `(IsLocalization.mem_map_algebraMap_iff (M := Q.primeCompl) (S := Localization.AtPrime Q)).mp (hfI j)`. Conclude with `⟨a, a.2, s, s.2, h⟩`. Use `choose a haP s hsQ hfa using hnum`.

Establish `hIa : P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)) = (Ideal.span (Set.range a)).map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q))`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[hfspan, Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Establish `hu : IsUnit (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) (s j))` using `IsLocalization.map_units (Localization.AtPrime Q) ⟨s j, hsQ j⟩`.

Establish `hf : f j = algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) (a j) * ↑hu.unit⁻¹`. Rewrite using `[← hfa j, mul_assoc, IsUnit.mul_val_inv, mul_one]`. Rewrite using `[hf]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩))`. Conclude with `Ideal.map_mono (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact haP j))`.

Take `⟨t, ht⟩` from `(IsNoetherian.noetherian P : P.FG)`. Establish `hgen : ∀ p ∈ t, ∃ u ∈ Q.primeCompl, u * p ∈ Ideal.span (Set.range a)`. Introduce `p hp`. Establish `hp' : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) p ∈ (Ideal.span (Set.range a)).map (algebraMap _ (Localization.AtPrime Q))` using `hIa ▸ Ideal.mem_map_of_mem _ (ht ▸ Ideal.subset_span hp)`. Conclude with `(IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl) (S := Localization.AtPrime Q) _ p).mp hp'`.

Use `choose! u hu hup using hgen`. Use `⟨hgt - 1, a, ∏ p ∈ t, u p, by omega, haP, ?_, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Take `⟨p, hp, hpQ⟩` from `Ideal.IsPrime.prod_mem_iff.mp hmem`. Conclude with `hu p hp hpQ`.

Introduce `p hp`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one]`. Rewrite `hp` using `[← ht]`. Proceed by induction on `hp using Submodule.span_induction with`.

Consider the case `mem x hx`. Rewrite using `[← Finset.mul_prod_erase t u hx, mul_comm (u x), mul_assoc]`. Conclude with `Ideal.mul_mem_left _ _ (hup x hx)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Rewrite using `[mul_add]`. Conclude with `Ideal.add_mem _ hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[smul_eq_mul, mul_left_comm]`. Conclude with `Ideal.mul_mem_left _ _ hx`.
-/
theorem NormalCodimOneCompleteIntersection.proof : NormalCodimOneCompleteIntersection.Statement := by
  classical
  intro σ _ P Q e hP hQ hPQ hint hdP hdQ
  have hdS : ringKrullDim (MvPolynomial σ ℂ) = (Fintype.card σ : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
      zero_add]

  obtain ⟨hgt, hhgt⟩ : ∃ k : ℕ, Q.height = k :=
    ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ h => h.symm
  have hQh : hgt + e = Fintype.card σ := by
    have h := ringKrullDim_quotient_add_height_of_finiteType (A := MvPolynomial σ ℂ)
      (by rw [hdS]; exact ne_of_beq_false rfl) Q
    rw [hdQ, hdS, hhgt] at h
    have h' : e + hgt = Fintype.card σ := by exact_mod_cast h
    omega

  obtain ⟨Qb, hQb_def⟩ : ∃ Qb, Qb = Q.map (Ideal.Quotient.mk P) := ⟨_, rfl⟩
  have hQbp : Qb.IsPrime := hQb_def ▸ Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  have : IsDomain (MvPolynomial σ ℂ ⧸ P) := Ideal.Quotient.isDomain P
  have hQb : Qb.height = 1 := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Qb.height = k :=
      ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ h => h.symm
    have h := ringKrullDim_quotient_add_height_of_finiteType (A := MvPolynomial σ ℂ ⧸ P)
      (by rw [hdP]; exact ne_of_beq_false rfl) Qb
    have hq : ringKrullDim ((MvPolynomial σ ℂ ⧸ P) ⧸ Qb) = ringKrullDim (MvPolynomial σ ℂ ⧸ Q) := by
      rw [hQb_def]
      exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ)
    rw [hq, hdQ, hdP, hk] at h
    have h' : e + k = e + 1 := by exact_mod_cast h
    rw [hk]
    exact_mod_cast (by omega : k = 1)

  have hdR : ringKrullDim (Localization.AtPrime Q) = (hgt : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q), hhgt]
    rfl

  have hcomap : (maximalIdeal (Localization.AtPrime Qb)).comap
      ((algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime Qb)).comp (Ideal.Quotient.mk P)) = Q := by
    rw [← Ideal.comap_comap]
    change (Ideal.under _ (maximalIdeal (Localization.AtPrime Qb))).comap (Ideal.Quotient.mk P) = Q
    rw [Localization.AtPrime.under_maximalIdeal, hQb_def,
      Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.mpr hPQ]
  obtain ⟨eqv, -⟩ := LocalizationAtPrimeQuotient.proof (MvPolynomial σ ℂ) P Qb.primeCompl
    (maximalIdeal (Localization.AtPrime Qb)) Q hcomap
  obtain ⟨hregRI, hdRI⟩ := isRegularLocalRing_of_height_eq_one Qb hQb eqv
  have hgt1 : 1 ≤ hgt := by
    have h := ringKrullDim_quotient_le (P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)))
    rw [hdRI, hdR] at h
    exact_mod_cast h
  obtain ⟨f, hfI, hfspan⟩ := exists_span_eq_of_isRegularLocalRing_quotient (hgt - 1) (Localization.AtPrime Q)
    (P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q))) (by
      rw [hdR, hdRI]
      have : hgt = 1 + (hgt - 1) := by omega
      exact_mod_cast this)

  have hnum : ∀ j, ∃ a ∈ P, ∃ s ∈ Q.primeCompl,
      f j * algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) s =
        algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) a := by
    intro j
    obtain ⟨⟨a, s⟩, h⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (M := Q.primeCompl) (S := Localization.AtPrime Q)).mp (hfI j)
    exact ⟨a, a.2, s, s.2, h⟩
  choose a haP s hsQ hfa using hnum
  have hIa : P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)) =
      (Ideal.span (Set.range a)).map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)) := by
    apply le_antisymm
    · rw [hfspan, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have hu : IsUnit (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) (s j)) :=
        IsLocalization.map_units (Localization.AtPrime Q) ⟨s j, hsQ j⟩
      have hf : f j = algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) (a j) * ↑hu.unit⁻¹ := by
        rw [← hfa j, mul_assoc, IsUnit.mul_val_inv, mul_one]
      rw [hf]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩))
    · exact Ideal.map_mono (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact haP j))
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian P : P.FG)
  have hgen : ∀ p ∈ t, ∃ u ∈ Q.primeCompl, u * p ∈ Ideal.span (Set.range a) := by
    intro p hp
    have hp' : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) p ∈
        (Ideal.span (Set.range a)).map (algebraMap _ (Localization.AtPrime Q)) :=
      hIa ▸ Ideal.mem_map_of_mem _ (ht ▸ Ideal.subset_span hp)
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl) (S := Localization.AtPrime Q) _ p).mp
      hp'
  choose! u hu hup using hgen
  refine ⟨hgt - 1, a, ∏ p ∈ t, u p, by omega, haP, ?_, ?_⟩
  · intro hmem
    obtain ⟨p, hp, hpQ⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hu p hp hpQ
  · intro p hp
    refine ⟨1, ?_⟩
    rw [pow_one]
    rw [← ht] at hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase t u hx, mul_comm (u x), mul_assoc]
      exact Ideal.mul_mem_left _ _ (hup x hx)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add]
      exact Ideal.add_mem _ hx hy
    | smul r x _ hx =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ hx

end

end GroundTheory.Heights₂.Heights
