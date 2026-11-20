import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EmbedsOfTie

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Unfold `regAt`. Conclude with `IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective`.
-/
theorem isLocalRing_regAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  unfold regAt
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, -, hinv⟩`. Use `isUnit_iff_exists_inv.mpr ⟨⟨(s : Ω)⁻¹, hinv⟩, ?_⟩` and prove the remaining obligations. Conclude with `Subtype.ext (mul_inv_cancel₀ h0)`. Introduce `hs`.

Take `⟨t, ht⟩` from `isUnit_iff_exists_inv.mp hs`. Establish `ht' : (s : Ω) * (t : Ω) = 1` using `by simpa using congrArg Subtype.val ht`. Establish `h0 : (s : Ω) ≠ 0` using `left_ne_zero_of_mul_eq_one ht'`. Use `⟨h0, s.2, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_eq_of_mul_eq_one_right ht']`.

Conclude with `t.2`.
-/
theorem unitAt_iff_isUnit {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ) (s : regAt ξ p) :
    unitAt ξ p (s : Ω) ↔ IsUnit s := by
  constructor
  · rintro ⟨h0, -, hinv⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨(s : Ω)⁻¹, hinv⟩, ?_⟩
    exact Subtype.ext (mul_inv_cancel₀ h0)
  · intro hs
    obtain ⟨t, ht⟩ := isUnit_iff_exists_inv.mp hs
    have ht' : (s : Ω) * (t : Ω) = 1 := by simpa using congrArg Subtype.val ht
    have h0 : (s : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one ht'
    refine ⟨h0, s.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right ht']
    exact t.2

/- English proof (translation)
Proceed by induction on `h using Algebra.adjoin_induction with`. Consider the case `mem y hy => exact Algebra.subset_adjoin hy`. Consider the case `algebraMap r`. Rewrite using `[eq_intCast (algebraMap ℤ Ω) r]`. Conclude with `intCast_mem _ r`.

Consider the case `add y z _ _ hy hz => exact add_mem hy hz`. Consider the case `mul y z _ _ hy hz => exact mul_mem hy hz`.
-/
theorem mem_adjoin_rat_of_int [CharZero Ω] {S : Set Ω} {a : Ω} (h : a ∈ Algebra.adjoin ℤ S) :
    a ∈ Algebra.adjoin ℚ S := by
  induction h using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap r =>
    rw [eq_intCast (algebraMap ℤ Ω) r]
    exact intCast_mem _ r
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

/- English proof (translation)
Introduce `X Ω _ _ ξ κ x h`. Unfold `EmbedsGeneric`. Introduce `p _`. Use `⟨h.cover p, fun i hi => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `a ha`.

Take `⟨s, hs, hu, hsa⟩` from `(GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h i p hi a).mp ha`. Conclude with `⟨s, mem_adjoin_rat_of_int hs, hu, mem_adjoin_rat_of_int hsa⟩`. Introduce `q _ hq hpq haveI := isLocalRing_regAt h.gen p`. Establish `hmem : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x i), a ∈ regAt ξ p` using `fun a ha => (h.ring i hi.1 a).mp ha p hi`. Set `φ : Algebra.adjoin ℤ (Set.range fun j => x j / x i) →+* regAt ξ p` to `{ toFun := fun s => ⟨s, hmem s s.2⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`.

Set `I : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x i))` to `Ideal.comap φ (IsLocalRing.maximalIdeal (regAt ξ p))`. Establish `hI : I.IsPrime` using `Ideal.comap_isPrime φ _`. Establish `key : ∀ s : Algebra.adjoin ℤ (Set.range fun j => x j / x i), s ∉ I ↔ unitAt ξ p (s : Ω)`. Introduce `s`. Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`.

Conclude with `(unitAt_iff_isUnit p (φ s)).symm`. Take `⟨p', -, huniq⟩` from `GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x h i hi.1 I hI`. Establish `e1` using `huniq p ⟨hi, key⟩`. Establish `e2` using `huniq q ⟨hq, fun s => (key s).trans (hpq s (mem_adjoin_rat_of_int s.2))⟩`. Conclude with `e1.trans e2.symm`.
-/
theorem embedsGeneric_of_coordTie : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → EmbedsGeneric ξ x := by
  intro X Ω _ _ ξ κ x h
  unfold EmbedsGeneric
  intro p _
  refine ⟨h.cover p, fun i hi => ⟨?_, ?_⟩⟩
  · intro a ha
    obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h i p hi a).mp ha
    exact ⟨s, mem_adjoin_rat_of_int hs, hu, mem_adjoin_rat_of_int hsa⟩
  · intro q _ hq hpq
    haveI := isLocalRing_regAt h.gen p
    have hmem : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x i), a ∈ regAt ξ p :=
      fun a ha => (h.ring i hi.1 a).mp ha p hi
    let φ : Algebra.adjoin ℤ (Set.range fun j => x j / x i) →+* regAt ξ p :=
      { toFun := fun s => ⟨s, hmem s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let I : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x i)) :=
      Ideal.comap φ (IsLocalRing.maximalIdeal (regAt ξ p))
    have hI : I.IsPrime := Ideal.comap_isPrime φ _
    have key : ∀ s : Algebra.adjoin ℤ (Set.range fun j => x j / x i), s ∉ I ↔ unitAt ξ p (s : Ω) := by
      intro s
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact (unitAt_iff_isUnit p (φ s)).symm
    obtain ⟨p', -, huniq⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x h i hi.1 I hI
    have e1 := huniq p ⟨hi, key⟩
    have e2 := huniq q ⟨hq, fun s => (key s).trans (hpq s (mem_adjoin_rat_of_int s.2))⟩
    exact e1.trans e2.symm

end GlobalTheory.CompanionTheory.Ar.EmbedsOfTie
