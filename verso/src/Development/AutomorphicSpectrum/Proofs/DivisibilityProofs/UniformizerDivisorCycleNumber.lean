import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ConsPoly

/- English proof (translation)
Establish `h` using `hH (mem_support_iff.mp hμ)`. Rewrite using `[← h]`. Simplify using `[classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset, Finsupp.weight_apply, Finsupp.sum]`.
-/
theorem length_classList {K σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ}
    (hH : H.IsHomogeneous m) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = m := by
  have h := hH (mem_support_iff.mp hμ)
  rw [← h]
  simp [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset,
    Finsupp.weight_apply, Finsupp.sum]

/- English proof (translation)
Use `haveI : P.IsPrime := hM.multiProj.isPrime`. Establish `hC : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P`. Introduce `a ha hmem`. Apply `ha` to reduce the goal to its premises. Establish `ha' : a ∈ P.comap (C : O →+* MRing ι O)` using `Ideal.mem_comap.2 hmem`.

Rewrite `ha'` using `[hM.noTorsion]`. Conclude with `Ideal.mem_bot.1 ha'`. Establish `hfin` using `ScalarQuotient.divCycle_support_finite P (C ϖ)`. Establish `key : cycEval (fun W => vNumL W l) (divCycle P (C ϖ)) = intNumL (FractionRing O) (genFib P) l` using `ConservationOfNumber.full O ϖ hϖ K ι P l.length hM l.get`. Unfold `cycList`.

Rewrite using `[ScalarQuotient.divCycle_const P hC hϖ.ne_zero u e, ← key]`. Unfold `cycEval`. Use `show ∑ᶠ W, ((e : ℤ) * divCycle P (C ϖ) W) * vNumL W l = (e : ℤ) * ∑ᶠ W, divCycle P (C ϖ) W * vNumL W l`. Rewrite using `[mul_finsum]`. Conclude with `finsum_congr fun W => by ring`.

Apply the tactic sequence `all_goals exact hfin.subset (Function.support_mul_subset_left _ _)`.
-/
theorem cycList_const {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (l : List (K → ℤ))
    (hM : IsModelOver P l.length) (u : Oˣ) (e : ℕ) :
    cycList (divCycle P (C ((u : O) * ϖ ^ e))) l =
      (e : ℤ) * intNumL (FractionRing O) (genFib P) l := by
  haveI : P.IsPrime := hM.multiProj.isPrime
  have hC : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P := by
    intro a ha hmem
    apply ha
    have ha' : a ∈ P.comap (C : O →+* MRing ι O) := Ideal.mem_comap.2 hmem
    rw [hM.noTorsion] at ha'
    exact Ideal.mem_bot.1 ha'
  have hfin := ScalarQuotient.divCycle_support_finite P (C ϖ)
  have key : cycEval (fun W => vNumL W l) (divCycle P (C ϖ)) =
      intNumL (FractionRing O) (genFib P) l :=
    ConservationOfNumber.full O ϖ hϖ K ι P l.length hM l.get
  unfold cycList
  rw [ScalarQuotient.divCycle_const P hC hϖ.ne_zero u e, ← key]
  unfold cycEval
  show ∑ᶠ W, ((e : ℤ) * divCycle P (C ϖ) W) * vNumL W l =
    (e : ℤ) * ∑ᶠ W, divCycle P (C ϖ) W * vNumL W l
  rw [mul_finsum]
  · exact finsum_congr fun W => by ring
  all_goals exact hfin.subset (Function.support_mul_subset_left _ _)

end GlobalTheory.CompanionTheory.Ar.Num.ConsPoly

open GlobalTheory.CompanionTheory.Ar.Num.ConsPoly in

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hM u e σ cls H m hH Q hd`. Unfold `cycNum genNum`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Establish `hlen : (classList cls μ ++ Q).length = d`.

Rewrite using `[List.length_append, length_classList cls hH hμ, hd]`. Establish `hM' : IsModelOver P (classList cls μ ++ Q).length`. Rewrite using `[hlen]`. Conclude with `hM`. Rewrite using `[cycList_const hϖ _ hM' u e]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (u : Oˣ) (e : ℕ) (σ : Type) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (divCycle P (C ((u : O) * ϖ ^ e))) cls H Q = (e : ℝ) * genNum (FractionRing O) (genFib P) cls H Q := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hM u e σ cls H m hH Q hd
  unfold cycNum genNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hlen : (classList cls μ ++ Q).length = d := by
    rw [List.length_append, length_classList cls hH hμ, hd]
  have hM' : IsModelOver P (classList cls μ ++ Q).length := by
    rw [hlen]
    exact hM
  rw [cycList_const hϖ _ hM' u e]
  push_cast
  ring
