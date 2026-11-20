import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDegreeOnePrimeNotSplitsCompletely

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert

namespace ExistsNonSplitPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Take `⟨u, ⟨hu, hue⟩, -⟩` from `hS w`. Distinguish the cases in `h : u = w`. Conclude with `h ▸ hu`. Conclude with `absurd ⟨u, h, hue⟩ hw`.
-/
theorem mem_of_not_isSplitAt {Sec : Set (Pl E)} (hS : IsSection Sec) {w : Pl E} (hw : ¬ IsSplitAt w) :
    w ∈ Sec := by
  obtain ⟨u, ⟨hu, hue⟩, -⟩ := hS w
  by_cases h : u = w
  · exact h ▸ hu
  · exact absurd ⟨u, h, hue⟩ hw

/- English proof (translation)
Use `set F := maximalRealSubfield E`. Establish `h2 : Module.finrank F E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two F E`. Take `⟨v, -, hvB, hv⟩` from `GlobalTheory.CompanionTheory.Density.exists_degreeOnePrime_not_splitsCompletely F F E (by omega) ((fun w : Pl E => w.under (𝓞 F)) '' B) (hB.image _)`. Use `haveI := v.isMaximal`. Take `⟨⟨P, hP⟩⟩` from `v.asIdeal.nonempty_primesOver (S := 𝓞 E)`.

Establish `hP0 : P ≠ ⊥` using `Ideal.ne_bot_of_mem_primesOver v.ne_bot hP`. Set `w : Pl E` to `⟨P, hP.1, hP0⟩`. Establish `hwv : w.under (𝓞 F) = v` using `HeightOneSpectrum.ext (hP.2.over).symm`. Use `⟨w, fun hw => hvB ⟨w, hw, hwv⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨u, hu, hue⟩`.

Apply `hv` to reduce the goal to its premises. Rewrite using `[GroundTheory.Global.splitsCompletely_iff_ncard_primesOver, h2]`. Use `haveI : NoZeroSMulDivisors (𝓞 F) (𝓞 E) := ⟨fun {c x} e => by`. Rewrite `e` using `[Algebra.smul_def, mul_eq_zero, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]`. Conclude with `e⟩`.

Establish `hle : (v.asIdeal.primesOver (𝓞 E)).ncard ≤ 2`. Establish `h` using `Ideal.card_primesOverFinset_le_finrank (𝓞 E) F E v.ne_bot`. Rewrite `h` using `[← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset v.ne_bot, h2]`. Conclude with `h`. Establish `hmem : ∀ x : Pl E, x.under (𝓞 F) = v → x.asIdeal ∈ v.asIdeal.primesOver (𝓞 E)` using `fun x hx => ⟨x.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hx).symm⟩⟩`.

Establish `hge : 2 ≤ (v.asIdeal.primesOver (𝓞 E)).ncard`. Establish `hne : u.asIdeal ≠ w.asIdeal` using `fun e => hu (HeightOneSpectrum.ext e)`. Rewrite using `[← Set.ncard_pair hne]`. Use `Set.ncard_le_ncard ?_ (IsDedekindDomain.primesOver_finite _ _)` and prove the remaining obligations. Introduce and unpack `x (rfl | rfl)`.

Conclude with `hmem u (hue.trans hwv)`. Conclude with `hmem w hwv`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_not_isSplitAt (B : Set (Pl E)) (hB : B.Finite) : ∃ w : Pl E, w ∉ B ∧ ¬ IsSplitAt w := by
  set F := maximalRealSubfield E
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  obtain ⟨v, -, hvB, hv⟩ := GlobalTheory.CompanionTheory.Density.exists_degreeOnePrime_not_splitsCompletely F F E
    (by omega) ((fun w : Pl E => w.under (𝓞 F)) '' B) (hB.image _)
  haveI := v.isMaximal
  obtain ⟨⟨P, hP⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 E)
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot hP
  let w : Pl E := ⟨P, hP.1, hP0⟩
  have hwv : w.under (𝓞 F) = v := HeightOneSpectrum.ext (hP.2.over).symm
  refine ⟨w, fun hw => hvB ⟨w, hw, hwv⟩, ?_⟩
  rintro ⟨u, hu, hue⟩
  apply hv
  rw [GroundTheory.Global.splitsCompletely_iff_ncard_primesOver, h2]
  haveI : NoZeroSMulDivisors (𝓞 F) (𝓞 E) := ⟨fun {c x} e => by
    rw [Algebra.smul_def, mul_eq_zero, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))] at e
    exact e⟩
  have hle : (v.asIdeal.primesOver (𝓞 E)).ncard ≤ 2 := by
    have h := Ideal.card_primesOverFinset_le_finrank (𝓞 E) F E v.ne_bot
    rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset v.ne_bot, h2] at h
    exact h
  have hmem : ∀ x : Pl E, x.under (𝓞 F) = v → x.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := fun x hx =>
    ⟨x.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hx).symm⟩⟩
  have hge : 2 ≤ (v.asIdeal.primesOver (𝓞 E)).ncard := by
    have hne : u.asIdeal ≠ w.asIdeal := fun e => hu (HeightOneSpectrum.ext e)
    rw [← Set.ncard_pair hne]
    refine Set.ncard_le_ncard ?_ (IsDedekindDomain.primesOver_finite _ _)
    rintro x (rfl | rfl)
    · exact hmem u (hue.trans hwv)
    · exact hmem w hwv
  omega

end ExistsNonSplitPlace

/- English proof (translation)
Introduce `E _ _ _ _ n π hπ Sec hS X`. Establish `hfin : {w : Pl E | ¬ IsUnramU π w}.Finite` using `Filter.eventually_cofinite.1 (PositivityTheory.Rg.BcB.F.Rig.eventually_isUnramU hπ)`. Take `⟨w, hwB, hw⟩` from `ExistsNonSplitPlace.exists_not_isSplitAt ((X : Set (Pl E)) ∪ {w | ¬ IsUnramU π w}) (X.finite_toSet.union hfin)`. Use `⟨w, ExistsNonSplitPlace.mem_of_not_isSplitAt hS hw, fun h => hwB (Or.inl h), hw, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `hwB (Or.inr h)`.
-/
theorem inertPlaceEx : InertPlaceEx := by
  intro E _ _ _ _ n π hπ Sec hS X
  have hfin : {w : Pl E | ¬ IsUnramU π w}.Finite :=
    Filter.eventually_cofinite.1 (PositivityTheory.Rg.BcB.F.Rig.eventually_isUnramU hπ)
  obtain ⟨w, hwB, hw⟩ := ExistsNonSplitPlace.exists_not_isSplitAt ((X : Set (Pl E)) ∪ {w | ¬ IsUnramU π w})
    (X.finite_toSet.union hfin)
  refine ⟨w, ExistsNonSplitPlace.mem_of_not_isSplitAt hS hw, fun h => hwB (Or.inl h), hw, ?_⟩
  by_contra h
  exact hwB (Or.inr h)

end PositivityTheory.Rg.BcB.F.Inert

end
