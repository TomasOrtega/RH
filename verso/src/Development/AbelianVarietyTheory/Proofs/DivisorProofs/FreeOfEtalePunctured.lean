import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorQuotientSmulTopOfFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoOfIsIntegrallyClosedOfIsRegularLocaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFreeOfCompleteRegularLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthGeThreeFiniteEtalePuncturedRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfEtalePuncturedOfDepthPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEQuotientMapSpanSingletonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleQuotientOfEtalePuncturedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFreeOfRegularOfFreeQuotientLocalStatement

open IsLocalRing

namespace GlobalTheory.PurityStep

/- English proof (translation)
The claim follows from `Module.Finite.of_restrictScalars_finite R _ _`.
-/
theorem finite_quot (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R) : Module.Finite (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
  Module.Finite.of_restrictScalars_finite R _ _

/- English proof (translation)
Introduce `A _ _ _ hA _`. Use `GlobalTheory.AnnRegSeq.free_of_modDepthGE 2 R A hA ?_` and prove the remaining obligations. Establish `h1 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R` using `IsRegularLocalRing.spanFinrank_maximalIdeal`. Establish `: ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ((2 : ℕ) : WithBot ℕ∞)`. Rewrite using `[h1]`.

Conclude with `h` after adjusting the coercions. Conclude with `this` after adjusting the coercions.
-/
theorem lowDim (R : Type) [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 2) :
    PurityFree R := by
  intro A _ _ _ hA _
  refine GlobalTheory.AnnRegSeq.free_of_modDepthGE 2 R A hA ?_
  have h1 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
    rw [h1]; exact_mod_cast h
  exact_mod_cast this

/- English proof (translation)
Introduce `A _ _ _ hA het`. Establish `h3` using `GlobalTheory.T.depth_ge_three_finite_etale_punctured_regular R hc hd f hf hf2 hP A hA het`. Establish `hf0 : f ≠ 0`. Introduce and unpack `rfl`. Conclude with `hf2 (zero_mem _)`.

Establish `hreg` using `GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' R A (ReciprocityTheory.CA.ModDepthGE.mono (by norm_num) hA) het f hf0`. Use `haveI := finite_quot R A f`. Conclude with `GlobalTheory.T.moduleFree_of_regular_of_free_quotient_local R A f hf hreg (hP _ (GlobalTheory.T.modDepthGE_quotient_span_of_isSMulRegular R A f hf hreg 2 h3) (GlobalTheory.T.etale_quotient_of_etale_punctured' R A f het))`.
-/
theorem hyperplane (R : Type) [CommRing R] [IsRegularLocalRing R]
    (hc : IsAdicComplete (maximalIdeal R) R) (hd : 3 ≤ ringKrullDim R) (f : R)
    (hf : f ∈ maximalIdeal R) (hf2 : f ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span {f})]
    (hP : PurityFree (R ⧸ Ideal.span {f})) : PurityFree R := by
  intro A _ _ _ hA het
  have h3 := GlobalTheory.T.depth_ge_three_finite_etale_punctured_regular R hc hd f hf hf2 hP A hA het
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf2 (zero_mem _)
  have hreg := GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' R A (ReciprocityTheory.CA.ModDepthGE.mono (by norm_num) hA) het f hf0
  haveI := finite_quot R A f
  exact GlobalTheory.T.moduleFree_of_regular_of_free_quotient_local R A f hf hreg (hP _ (GlobalTheory.T.modDepthGE_quotient_span_of_isSMulRegular R A f hf hreg 2 h3) (GlobalTheory.T.etale_quotient_of_etale_punctured' R A f het))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `S _ _ hS`. Conclude with `lowDim S (by rw [hS]; norm_num)`. Consider the case `succ n ih`.

Introduce `S _ _ hS`. Distinguish the cases in `h2 : n + 1 ≤ 2`. Conclude with `lowDim S (by rw [hS]; exact_mod_cast h2)`. Use `GlobalTheory.T.purityFree_of_complete_regularLocal S fun S' _ _ hc hd' => ?_` and prove the remaining obligations. Rewrite `hd'` using `[hS]`.

Establish `hsq : ¬ maximalIdeal S' ≤ maximalIdeal S' ^ 2`. Introduce `h`. Establish `h0` using `GlobalTheory.AnnRegSeq.maximalIdeal_eq_bot_of_le_sq h`. Use `ringKrullDim_eq_zero_of_isField ((IsLocalRing.isField_iff_maximalIdeal_eq (R := S')).mpr h0)` as an intermediate fact. Rewrite `hd'` using `[this]`.

Conclude with `absurd hd' (by norm_cast)`. Take `⟨f, hf, hf2⟩` from `Set.not_subset.mp hsq`. Use `haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hf`. Use `haveI hQ := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hf hf2`. Establish `hdim` using `ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hf hf2`.

Establish `hsp : ((maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank : WithBot ℕ∞) = ringKrullDim (S' ⧸ Ideal.span {f})` using `IsRegularLocalRing.spanFinrank_maximalIdeal`. Rewrite `hdim` using `[← hsp, hd']`. Establish `hk : (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank = n`. Establish `: (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank + 1 = n + 1`. Conclude with `hdim` after adjusting the coercions.

Use linear arithmetic over natural numbers and integers. Use `hyperplane S' hc ?_ f hf hf2 (ih _ ?_)` and prove the remaining obligations. Rewrite using `[hd']; exact_mod_cast (by omega : 3 ≤ n + 1)`. Rewrite using `[← hsp, hk]`.
-/
theorem purityFree_of_ringKrullDim (n : ℕ) : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S],
    ringKrullDim S = n → PurityFree S := by
  induction n with
  | zero =>
    intro S _ _ hS
    exact lowDim S (by rw [hS]; norm_num)
  | succ n ih =>
    intro S _ _ hS
    by_cases h2 : n + 1 ≤ 2
    · exact lowDim S (by rw [hS]; exact_mod_cast h2)
    refine GlobalTheory.T.purityFree_of_complete_regularLocal S fun S' _ _ hc hd' => ?_
    rw [hS] at hd'
    have hsq : ¬ maximalIdeal S' ≤ maximalIdeal S' ^ 2 := by
      intro h
      have h0 := GlobalTheory.AnnRegSeq.maximalIdeal_eq_bot_of_le_sq h
      have := ringKrullDim_eq_zero_of_isField ((IsLocalRing.isField_iff_maximalIdeal_eq (R := S')).mpr h0)
      rw [this] at hd'
      exact absurd hd' (by norm_cast)
    obtain ⟨f, hf, hf2⟩ := Set.not_subset.mp hsq
    haveI := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hf
    haveI hQ := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hf hf2
    have hdim := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hf hf2
    have hsp : ((maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (S' ⧸ Ideal.span {f}) := IsRegularLocalRing.spanFinrank_maximalIdeal
    rw [← hsp, hd'] at hdim
    have hk : (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank = n := by
      have : (maximalIdeal (S' ⧸ Ideal.span {f})).spanFinrank + 1 = n + 1 := by
        exact_mod_cast hdim
      omega
    refine hyperplane S' hc ?_ f hf hf2 (ih _ ?_)
    · rw [hd']; exact_mod_cast (by omega : 3 ≤ n + 1)
    · rw [← hsp, hk]

/- English proof (translation)
Introduce `R A _ _ _ _ _ _ _ _ _ _ hreg hd het`. Use `haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hreg`. Use `purityFree_of_ringKrullDim _ R hreg.symm A (GlobalTheory.T.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing' R A (le_trans (by norm_num) hd)) het` and prove the remaining obligations.
-/
theorem free_of_etale_punctured : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 3 ≤ ringKrullDim R → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Module.Free R A := by
  intro R A _ _ _ _ _ _ _ _ _ _ hreg hd het
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hreg
  refine purityFree_of_ringKrullDim _ R hreg.symm A (GlobalTheory.T.modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing' R A (le_trans (by norm_num) hd)) het

end GlobalTheory.PurityStep
