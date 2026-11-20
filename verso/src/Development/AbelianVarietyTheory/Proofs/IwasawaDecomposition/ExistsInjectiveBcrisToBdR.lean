import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjectiveStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

/- English proof (translation)
Establish `hu : ∀ y : M, IsUnit (g y)`. Introduce `y`. Establish `h : g y ≠ 0` using `fun h => hM y y.2 (hg (by rw [h, map_zero]))`. Take `⟨b, hb⟩` from `hK.mul_inv_cancel h`. Conclude with `IsUnit.of_mul_eq_one b hb`.

Use `⟨IsLocalization.lift hu, fun x => IsLocalization.lift_eq hu x, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalization.lift_injective_iff]`. Introduce `x y`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[← IsLocalization.lift_eq (S := S) hu x, h, IsLocalization.lift_eq]`. Introduce `h`. Rewrite using `[hg h]`.
-/
theorem exists_injective_lift_field {R S K : Type} [CommRing R] [CommRing S] [CommRing K] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hK : IsField K) (g : R →+* K) (hg : Function.Injective g)
    (hM : ∀ y ∈ M, y ≠ 0) :
    ∃ ι : S →+* K, (∀ x : R, ι (algebraMap R S x) = g x) ∧ Function.Injective ι := by
  have hu : ∀ y : M, IsUnit (g y) := by
    intro y
    have h : g y ≠ 0 := fun h => hM y y.2 (hg (by rw [h, map_zero]))
    obtain ⟨b, hb⟩ := hK.mul_inv_cancel h
    exact IsUnit.of_mul_eq_one b hb
  refine ⟨IsLocalization.lift hu, fun x => IsLocalization.lift_eq hu x, ?_⟩
  rw [IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    rw [← IsLocalization.lift_eq (S := S) hu x, h, IsLocalization.lift_eq]
  · intro h
    rw [hg h]

/- English proof (translation)
The claim follows from `GlobalTheory.RingIface.tower l x`.
-/
theorem algebraMap_ainf_acris_eq {l : ℕ} [Fact l.Prime] (x : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) x =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
  GlobalTheory.RingIface.tower l x

/- English proof (translation)
Take `⟨hd, -, hi⟩` from `GlobalTheory.T.usage l`. Introduce `h'`. Apply `hx0` to reduce the goal to its premises. Establish `h1` using `hj.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)`. Rewrite `h1` using `[← algebraMap_ainf_acris_eq]`.

Rewrite `h1` using `[h', map_zero]`. Establish `h2 : ((algebraMap (Per.Ainf l) (Per.Acris0 l) x : Per.Acris0 l) : Per.AinfP l) = 0` using `GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective l (by rw [map_zero]; exact h1.symm)`. Conclude with `hi (by rw [map_zero]; exact h2)`.
-/
theorem algebraMap_ainf_acris_ne_zero_pt {l : ℕ} [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l)
    (hj : IsCrisP j) (x : Per.Ainf l) (hx0 : x ≠ 0) : algebraMap (Per.Ainf l) (Per.Acris l) x ≠ 0 := by
  obtain ⟨hd, -, hi⟩ := GlobalTheory.T.usage l
  intro h'
  apply hx0
  have h1 := hj.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)
  rw [← algebraMap_ainf_acris_eq] at h1
  rw [h', map_zero] at h1
  have h2 : ((algebraMap (Per.Ainf l) (Per.Acris0 l) x : Per.Acris0 l) : Per.AinfP l) = 0 :=
    GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective l (by rw [map_zero]; exact h1.symm)
  exact hi (by rw [map_zero]; exact h2)

/- English proof (translation)
Take `⟨hd, -, -⟩` from `GlobalTheory.T.usage l`. Rewrite using `[← map_pow]`. Use `algebraMap_ainf_acris_ne_zero_pt j hj _ (pow_ne_zero n fun h => ?_)` and prove the remaining obligations. Conclude with `GlobalTheory.CrisLoc.constantCoeff_root_ne_zero l e hne (by rw [h, map_zero])`.
-/
theorem pow_root_ne_zero {l : ℕ} [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j)
    (e : Per.Fl l) (hne : e ≠ 1) (n : ℕ) :
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ^ n ≠ 0 := by
  obtain ⟨hd, -, -⟩ := GlobalTheory.T.usage l
  rw [← map_pow]
  refine algebraMap_ainf_acris_ne_zero_pt j hj _ (pow_ne_zero n fun h => ?_)
  exact GlobalTheory.CrisLoc.constantCoeff_root_ne_zero l e hne (by rw [h, map_zero])

/- English proof (translation)
Introduce `l _ j hj`. Take `⟨-, hi, hK, -⟩` from `GlobalTheory.T.bdRPlus_isDomain_bdR_isField l`. Take `⟨e, he, hne⟩` from `GlobalTheory.CrisLoc.exists_root_ne_one l`. Use `haveI := GlobalTheory.CrisLoc.bcris_away l e he hne`. Use `exists_injective_lift_field (Submonoid.powers (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1))) hK ((algebraMap (Per.BdRp l) (Per.BdR l)).comp j) (hi.comp (GlobalTheory.T.acrisToBdRPlus_injective l j hj)) ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨n, rfl⟩`. Conclude with `pow_root_ne_zero j hj e hne n`.
-/
theorem exists_iota_cris_dR : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j →
    ∃ ι : Per.Bcris l →+* Per.BdR l, (∀ x : Per.Acris l, ι (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.BdRp l) (Per.BdR l) (j x)) ∧ Function.Injective ι := by
  intro l _ j hj
  obtain ⟨-, hi, hK, -⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  haveI := GlobalTheory.CrisLoc.bcris_away l e he hne
  refine exists_injective_lift_field
    (Submonoid.powers (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1))) hK
    ((algebraMap (Per.BdRp l) (Per.BdR l)).comp j) (hi.comp (GlobalTheory.T.acrisToBdRPlus_injective l j hj)) ?_
  rintro _ ⟨n, rfl⟩
  exact pow_root_ne_zero j hj e hne n

end GlobalTheory.MemLoc
