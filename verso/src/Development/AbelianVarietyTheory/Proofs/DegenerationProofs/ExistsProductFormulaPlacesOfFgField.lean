import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProductFormulaPlacesFunctionFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS

def Places.sigma {k K : Type} [Field k] [Field K] [Algebra k K] {J : Type} [Finite J]
    (F : J → IntermediateField k K) (P : ∀ j, Places (F j) K) : Places k K where
  I := Σ j, (P j).I
  O := fun i => (P i.1).O i.2
  v := fun i => (P i.1).v i.2
  v_mul := fun i => (P i.1).v_mul i.2
  mem := fun i => (P i.1).mem i.2
  const := fun i c => (P i.1).const i.2 (algebraMap k (F i.1) c)
  fin := fun x => by
    refine (Set.finite_iUnion fun j => ((P j).fin x).image (Sigma.mk (β := fun j => (P j).I) j)).subset ?_
    rintro ⟨j, i⟩ hi
    exact Set.mem_iUnion.2 ⟨j, i, hi, rfl⟩
  sum := fun x => by
    classical
    have := Fintype.ofFinite J
    rw [finsum_eq_sum_of_support_subset (s := Finset.univ.sigma fun j => ((P j).fin x).toFinset),
      Finset.sum_sigma]
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [← (P j).sum x, finsum_eq_sum _ ((P j).fin x)]
    · rintro ⟨j, i⟩ hi
      simpa using hi

/- English proof (translation)
Establish `key : x ∈ (AlgebraicIndependent.matroid k K).closure ∅`. Establish `hB` using `AlgebraicIndependent.matroid_isBase_iff.2 hs`. Break down `s.eq_empty_or_nonempty with rfl | hne` into its components or cases. Rewrite using `[hB.closure_eq]`. Discharge the goal by the elementary cases of `trivial`.

Use `hne.coe_sort` as an intermediate fact. Establish `e : (⋂ t : s, s \ {(t : K)}) = ∅`. Use `Set.eq_empty_of_forall_notMem fun y hy => ?_` and prove the remaining obligations. Rewrite `hy` using `[Set.mem_iInter]`. Conclude with `(hy ⟨y, (hy this.some).1⟩).2 rfl`.

Rewrite using `[← e, hB.indep.closure_iInter_eq_biInter_closure_of_forall_subset fun _ => Set.diff_subset]`. Use `Set.mem_iInter.2 fun t => ?_` and prove the remaining obligations. Rewrite using `[AlgebraicIndependent.matroid_closure_eq]`. Conclude with `IntermediateField.isAlgebraic_adjoin_iff.1 (h t)`. Rewrite `key` using `[AlgebraicIndependent.matroid_closure_eq]`.

Establish `h2 : IsAlgebraic (IntermediateField.adjoin k (∅ : Set K)) x` using `IntermediateField.isAlgebraic_adjoin_iff.2 key`. Establish `: Algebra.IsAlgebraic k (IntermediateField.adjoin k (∅ : Set K))` using `(IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic k K).2 (by simp)`. Conclude with `h2.restrictScalars k`.
-/
theorem isAlgebraic_of_forall_erase {k K : Type} [Field k] [Field K] [Algebra k K] {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K)) {x : K}
    (h : ∀ t : s, IsAlgebraic (IntermediateField.adjoin k (s \ {(t : K)})) x) : IsAlgebraic k x := by
  have key : x ∈ (AlgebraicIndependent.matroid k K).closure ∅ := by
    have hB := AlgebraicIndependent.matroid_isBase_iff.2 hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · rw [hB.closure_eq]; trivial
    · have := hne.coe_sort
      have e : (⋂ t : s, s \ {(t : K)}) = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun y hy => ?_
        rw [Set.mem_iInter] at hy
        exact (hy ⟨y, (hy this.some).1⟩).2 rfl
      rw [← e, hB.indep.closure_iInter_eq_biInter_closure_of_forall_subset fun _ => Set.diff_subset]
      refine Set.mem_iInter.2 fun t => ?_
      rw [AlgebraicIndependent.matroid_closure_eq]
      exact IntermediateField.isAlgebraic_adjoin_iff.1 (h t)
  rw [AlgebraicIndependent.matroid_closure_eq] at key
  have h2 : IsAlgebraic (IntermediateField.adjoin k (∅ : Set K)) x :=
    IntermediateField.isAlgebraic_adjoin_iff.2 key
  have : Algebra.IsAlgebraic k (IntermediateField.adjoin k (∅ : Set K)) :=
    (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic k K).2 (by simp)
  exact h2.restrictScalars k

/- English proof (translation)
Establish `hB` using `AlgebraicIndependent.matroid_isBase_iff.2 hs`. Introduce `h`. Use `hB.indep.notMem_closure_diff_of_mem t.2 ?_` and prove the remaining obligations. Rewrite using `[AlgebraicIndependent.matroid_closure_eq]`. Conclude with `IntermediateField.isAlgebraic_adjoin_iff.1 h`.
-/
theorem transcendental_erase {k K : Type} [Field k] [Field K] [Algebra k K] {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K)) (t : s) :
    Transcendental (IntermediateField.adjoin k (s \ {(t : K)})) (t : K) := by
  have hB := AlgebraicIndependent.matroid_isBase_iff.2 hs
  intro h
  refine hB.indep.notMem_closure_diff_of_mem t.2 ?_
  rw [AlgebraicIndependent.matroid_closure_eq]
  exact IntermediateField.isAlgebraic_adjoin_iff.1 h

/- English proof (translation)
Establish `: Algebra.EssFiniteType k K` using `IntermediateField.fg_top_iff.mp hfg`. Take `⟨s, hs, hsep⟩` from `exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K`. Establish `: Algebra.EssFiniteType (IntermediateField.adjoin k (s : Set K)) K` using `Algebra.EssFiniteType.of_comp k _ K`. Establish `hfin : FiniteDimensional (IntermediateField.adjoin k (s : Set K)) K` using `Algebra.finite_of_essFiniteType_of_isAlgebraic`. Establish `H : ∀ t : (s : Set K), ∃ Pl : Places (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) K, ∀ x : K, (∀ i, x ∈ Pl.O i) → IsAlgebraic (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) x`.

Introduce `t`. Establish `e : IntermediateField.adjoin k (s : Set K) = (IntermediateField.adjoin (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) {(t : K)}).restrictScalars k`. Rewrite using `[IntermediateField.adjoin_adjoin_left, Set.diff_union_of_subset (by simpa using t.2)]`. Rewrite `hsep`, `hfin` using `[e]`. Conclude with `GlobalTheory.T.exists_productFormulaPlaces_function_field _ K t (transcendental_erase hs t) hfin hsep`.

Use `choose P hP using H`. Use `⟨Places.sigma _ P, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : IsAlgebraic k x` using `isAlgebraic_of_forall_erase hs fun t => hP t x fun i => hx ⟨t, i⟩`. Conclude with `minpoly.mem_range_of_degree_eq_one k x (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx'.isIntegral))`.
-/
theorem exists_places_of_fg (k : Type) [Field k] [IsAlgClosed k] (K : Type) [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
    ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → x ∈ Set.range (algebraMap k K) := by
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have : Algebra.EssFiniteType (IntermediateField.adjoin k (s : Set K)) K :=
    Algebra.EssFiniteType.of_comp k _ K
  have hfin : FiniteDimensional (IntermediateField.adjoin k (s : Set K)) K :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have H : ∀ t : (s : Set K), ∃ Pl : Places (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) K,
      ∀ x : K, (∀ i, x ∈ Pl.O i) →
        IsAlgebraic (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) x := by
    intro t
    have e : IntermediateField.adjoin k (s : Set K) = (IntermediateField.adjoin
        (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) {(t : K)}).restrictScalars k := by
      rw [IntermediateField.adjoin_adjoin_left, Set.diff_union_of_subset (by simpa using t.2)]
    rw [e] at hsep hfin
    exact GlobalTheory.T.exists_productFormulaPlaces_function_field _ K t (transcendental_erase hs t) hfin hsep
  choose P hP using H
  refine ⟨Places.sigma _ P, fun x hx => ?_⟩
  have hx' : IsAlgebraic k x := isAlgebraic_of_forall_erase hs fun t => hP t x fun i => hx ⟨t, i⟩
  exact minpoly.mem_range_of_degree_eq_one k x
    (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx'.isIntegral))

end GlobalTheory.SS
end
