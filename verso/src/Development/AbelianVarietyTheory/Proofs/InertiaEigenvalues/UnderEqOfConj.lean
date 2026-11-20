import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Small

/- English proof (translation)
Take `⟨Q, hQ, hQv⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 D.host.E) v.asIdeal (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))]`. Conclude with `bot_le)`. Use `⟨⟨Q, hQ, fun h => v.ne_bot ?_⟩, HeightOneSpectrum.ext hQv⟩` and prove the remaining obligations. Rewrite using `[← hQv, h]`.

Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)`.
-/
theorem exists_under (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v := by
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 D.host.E) v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))]
      exact bot_le)
  refine ⟨⟨Q, hQ, fun h => v.ne_bot ?_⟩, HeightOneSpectrum.ext hQv⟩
  rw [← hQv, h]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

/- English proof (translation)
Use `HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top fun a ha => ?_)` and prove the remaining obligations. Take `⟨c', h1, h2⟩` from `h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha`. Establish `hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F)` using `(D.sp.cm.fixed _).2 ⟨_, rfl⟩`. Establish `e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c'` using `RingOfIntegers.ext (h2.trans hfix).symm`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal`.

Rewrite using `[e]` and apply the resulting hypothesis.
-/
theorem under_eq_of_conj {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

end GlobalTheory.RawLift.Small

namespace GlobalTheory.RawLift.Small

/- English proof (translation)
Establish `hL : (0 : ℝ) ≤ L` using `Nat.cast_nonneg L`. Establish `hLn : (L : ℝ) ^ n ≠ 0` using `fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h`. Establish `h1 : ((L : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 = ((L : ℝ) ^ n)⁻¹`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hL, show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring, Real.rpow_neg hL, Real.rpow_natCast]`. Establish `h2 : ‖z‖ ^ 2 = ((L : ℝ) ^ n)⁻¹` using `eq_inv_of_mul_eq_one_left h`.

Conclude with `(pow_left_inj₀ (norm_nonneg z) (Real.rpow_nonneg hL _) two_ne_zero).1 (h2.trans h1.symm)`.
-/
theorem norm_eq_rpow {z : ℂ} {L n : ℕ} (h : ‖z‖ ^ 2 * (L : ℝ) ^ n = 1) : ‖z‖ = (L : ℝ) ^ (-(n : ℝ) / 2) := by
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hLn : (L : ℝ) ^ n ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
  have h1 : ((L : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 = ((L : ℝ) ^ n)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL, show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring,
      Real.rpow_neg hL, Real.rpow_natCast]
  have h2 : ‖z‖ ^ 2 = ((L : ℝ) ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h
  exact (pow_left_inj₀ (norm_nonneg z) (Real.rpow_nonneg hL _) two_ne_zero).1 (h2.trans h1.symm)

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t hB hG hI μ 𝓕 hμ`. Take `⟨s, hs, hs1, hsC⟩` from `hI`. Use `⟨fun v => max (s v) 0, ?_, fun v => max_lt (hs1 v) one_pos, ?_⟩` and prove the remaining obligations. Conclude with `Summable.of_nonneg_of_le (fun v => le_max_right _ _) (fun v => max_le (le_abs_self _) (abs_nonneg _)) hs.abs`. Introduce `v f hf C hC hCd`.

Distinguish the cases in `hbad : ∃ P, (P ∈ R.Pg ∨ P ∈ R.Q t) ∧ ∃ e f', IsPrimeIdem P e f' ∧ f' = f`. Take `⟨P, hP, e, f', hPI, rfl⟩` from `hbad`. Rewrite using `[Finset.sum_eq_zero fun g hg => by rw [hB μ 𝓕 hμ P hP e f' hPI g (hC g hg).1 (hC g hg).2, norm_zero]]`. Conclude with `le_max_right _ _`. Use `push_neg at hbad`.

Take `⟨ε, hε, hfε⟩` from `hf`. Establish `hI0` using `GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)`. Take `⟨P, hPv⟩` from `exists_under D v`. Take `⟨e, fP, hPI⟩` from `hI0.2.1 P`. Establish `hfP : fP = f`.

Rewrite using `[GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hPI hPv, hfε, GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hε]`. Substitute `hfP` using the available equality. Take `⟨c, hβ⟩` from `hL.lev.βW i`. Establish `hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal`. Rewrite using `[one_pow, Nat.cast_one]`.

Conclude with `(Ideal.ne_top_iff_one _).1 P.isPrime.ne_top`. Establish `hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P`. Introduce `PP hPP`. Establish `hPP' : PP ∈ R.Pg` using `hPP.elim id fun h => absurd h (Finset.notMem_empty _)`. Take `⟨e', f', h'⟩` from `hI0.2.1 PP`.

Establish `hne` using `hbad PP (Or.inl hPP') e' f' h'`. Use `⟨fun h => hne ?_, fun h => hne ?_⟩` and prove the remaining obligations. Substitute `h` using the available equality. Conclude with `((hI0.2.2.1 PP e fP hPI).2.2.2.1 e' f' h').2`. Rewrite using `[GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem h' ((under_eq_of_conj h).trans hPv), GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hPI hPv]`.

Take `⟨hJ, -, -⟩` from `(GlobalTheory.LevSplit.lev_split (Wc D i) (R.βW i) (R.ΛW i) (1 ^ c) (R.datWp i R.triv) hβ).2 P e fP hPI hN hoff`. Establish `hPI'` using `hI0.2.2.1 P e fP hPI`. Take `⟨L, hL'⟩` from `(hI0.1 fP hPI'.1 hPI'.2.1).1`. Establish `hsupp : ∀ g ∈ C, ∀ g' ∈ C, SuppF (Wc D i) fP (g⁻¹ * g')` using `fun g hg g' hg' => (hL' _).1 (L.mul_mem (L.inv_mem ((hL' g).2 (hC g hg).1)) ((hL' g').2 (hC g' hg').1))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem locSmall : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t → GoodMod R i t → IndexSum (Wc D i) (Vc D i).rank → LocSmall R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t hB hG hI μ 𝓕 hμ
  obtain ⟨s, hs, hs1, hsC⟩ := hI
  refine ⟨fun v => max (s v) 0, ?_, fun v => max_lt (hs1 v) one_pos, ?_⟩
  · exact Summable.of_nonneg_of_le (fun v => le_max_right _ _) (fun v => max_le (le_abs_self _) (abs_nonneg _)) hs.abs
  intro v f hf C hC hCd
  by_cases hbad : ∃ P, (P ∈ R.Pg ∨ P ∈ R.Q t) ∧ ∃ e f', IsPrimeIdem P e f' ∧ f' = f
  · obtain ⟨P, hP, e, f', hPI, rfl⟩ := hbad
    rw [Finset.sum_eq_zero fun g hg => by rw [hB μ 𝓕 hμ P hP e f' hPI g (hC g hg).1 (hC g hg).2, norm_zero]]
    exact le_max_right _ _
  push_neg at hbad
  obtain ⟨ε, hε, hfε⟩ := hf
  have hI0 := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)
  obtain ⟨P, hPv⟩ := exists_under D v
  obtain ⟨e, fP, hPI⟩ := hI0.2.1 P
  have hfP : fP = f := by
    rw [GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hPI hPv, hfε, GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hε]
  subst hfP
  obtain ⟨c, hβ⟩ := hL.lev.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    obtain ⟨e', f', h'⟩ := hI0.2.1 PP
    have hne := hbad PP (Or.inl hPP') e' f' h'
    refine ⟨fun h => hne ?_, fun h => hne ?_⟩
    · subst h
      exact ((hI0.2.2.1 PP e fP hPI).2.2.2.1 e' f' h').2
    · rw [GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem h' ((under_eq_of_conj h).trans hPv),
        GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hPI hPv]
  obtain ⟨hJ, -, -⟩ := (GlobalTheory.LevSplit.lev_split (Wc D i) (R.βW i) (R.ΛW i) (1 ^ c) (R.datWp i R.triv) hβ).2 P e fP hPI hN hoff
  have hPI' := hI0.2.2.1 P e fP hPI
  obtain ⟨L, hL'⟩ := (hI0.1 fP hPI'.1 hPI'.2.1).1
  have hsupp : ∀ g ∈ C, ∀ g' ∈ C, SuppF (Wc D i) fP (g⁻¹ * g') := fun g hg g' hg' =>
    (hL' _).1 (L.mul_mem (L.inv_mem ((hL' g).2 (hC g hg).1)) ((hL' g').2 (hC g' hg').1))
  calc ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ = ∑ g ∈ C, (latIndex (Wc D i) g : ℝ) ^ (-((Vc D i).rank : ℝ) / 2) :=
        Finset.sum_congr rfl fun g hg => norm_eq_rpow (hG μ 𝓕 hμ v fP ⟨ε, hε, hfε⟩ hbad g (hC g hg).1)
    _ ≤ s v := hsC v fP ⟨ε, hε, hfε⟩ C (fun g hg => ⟨(hC g hg).1, fun hk => (hC g hg).2 ((hJ g (hC g hg).1).2 hk)⟩)
        fun g hg g' hg' hk => hCd g hg g' hg' ((hJ _ (hsupp g hg g' hg')).2 hk)
    _ ≤ max (s v) 0 := le_max_left _ _

end GlobalTheory.RawLift.Small

end
