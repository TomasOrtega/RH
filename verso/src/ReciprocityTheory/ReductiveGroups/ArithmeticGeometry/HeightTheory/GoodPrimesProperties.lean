import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AdmissibleValuationPrimeUnique

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Establish `hgoodI : ∀ {p : Ideal (KTp K d.D d.N)}, p ∈ d.HtOne → ∀ {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)}, w ∈ d.GoodP c p → d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w)`. Introduce `p hp w hw`. Break down `d.PlaceTrivialOrPositive hd h c p hp w hw.1 with h1 | ⟨hadm, htriv, -⟩` into its components or cases. Take `⟨a, ha, hne⟩` from `hw.2`. Conclude with `absurd (h1 a ha) hne`.

Conclude with `⟨hadm, htriv⟩`. Establish `hcover : ∀ (V : Set (AddValuation (Ω c) (WithTop ℤ))), V.Finite → ∀ S : Set (Ideal (KTp K d.D d.N)), (∀ p ∈ S, p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w ∈ V) → S.Finite`. Introduce `V hV S hS`. Establish `hfin : (⋃ v ∈ V, {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}).Finite`. Use `hV.biUnion fun v _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hv' : d.admitted c v ∧ IsTrivOn K v`. Conclude with `(d.AdmissibleValuationPrimeUnique hd h c v hv'.1 hv'.2).finite`. Use `Set.Subsingleton.finite ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, w, hw, rfl⟩`. Conclude with `absurd (hgoodI hp hw) hv'`.

Use `hfin.subset ?_` and prove the remaining obligations. Introduce `p hpS`. Take `⟨hp, w, hw, hwV⟩` from `hS p hpS`. Conclude with `Set.mem_biUnion hwV ⟨hp, w, hw, rfl⟩`. Use `⟨d.AdmissibleValuationPrimeUnique hd h c, d.GeneratorMultiHomogeneous hd h c, ?_, ?_⟩` and prove the remaining obligations.

Introduce `G ta hta hta0`. Use `hcover {v | d.admitted c v ∧ d.ord c v G ta ≠ 0} (hd.a3' c hta hta0) _ ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hne⟩`. Use `⟨hp, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Apply `hne` to reduce the goal to its premises. Use `finsum_mem_eq_zero_of_forall_eq_zero fun w hw => ?_` and prove the remaining obligations. Use `hcon w hw` as an intermediate fact. Simplify using `only [Set.mem_setOf_eq, not_and, not_not] at this`.

Rewrite using `[this (hgoodI hp hw).1, mul_zero]`. Introduce `ta hta hta0`. Set `V : Set (AddValuation (Ω c) (WithTop ℤ))` to `{v | d.admitted c v ∧ d.ord c v d.wL ta ≠ 0} ∪ ⋃ j : {j // d.w j c ≠ 0}, {v | d.admitted c v ∧ d.ord c v d.wL (d.w j c) ≠ 0}`. Establish `hV : V.Finite` using `(hd.a3' c hta hta0).union (Set.finite_iUnion fun j => hd.a3' c (hd.w_mem j c) j.2)`. Use `hcover V hV _ ?_` and prove the remaining obligations.

Introduce and unpack `p ⟨hp, hne⟩`. Use `⟨hp, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hne` to reduce the goal to its premises.

Use `finsum_mem_eq_zero_of_forall_eq_zero fun w hw => ?_` and prove the remaining obligations. Establish `hnot` using `hcon w hw`. Establish `hadm` using `(hgoodI hp hw).1`. Establish `h1 : d.ord c (d.Wres c w) d.wL ta = 0`. Assume the negation of the conclusion as `h0`.

Conclude with `hnot (Or.inl ⟨hadm, h0⟩)`. Establish `h2 : ∀ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c) = 0`. Introduce `j`. Assume the negation of the conclusion as `h0`. Conclude with `hnot (Or.inr (Set.mem_iUnion.mpr ⟨j, hadm, h0⟩))`.

Use `haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨d.jc c, hd.w_base c⟩⟩`. Unfold `ordMM`. Rewrite using `[h1, show (⨅ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c)) = 0 by`. Simplify using `only [h2, ciInf_const]]`. Simplify using the standard rewrite rules.
-/
theorem good_primes_properties (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    (∀ v : AddValuation (Ω c) (WithTop ℤ), d.admitted c v → IsTrivOn K v →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}.Subsingleton) ∧
    (∀ p ∈ d.HtOne, (∃ w, w ∈ d.GoodP c p) →
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen p))
        (d.gen p)) ∧
    (∀ (G : WT) (ta : A c), ta ∈ 𝒜 c G → ta ≠ 0 →
      {p | p ∈ d.HtOne ∧ d.nP h c G ta p ≠ 0}.Finite) ∧
    (∀ ta : A c, ta ∈ 𝒜 c d.wL → ta ≠ 0 → {p | p ∈ d.HtOne ∧ d.nPMM h c ta p ≠ 0}.Finite) := by
  classical
  have hgoodI : ∀ {p : Ideal (KTp K d.D d.N)}, p ∈ d.HtOne →
      ∀ {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)}, w ∈ d.GoodP c p →
        d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w) := by
    intro p hp w hw
    rcases d.PlaceTrivialOrPositive hd h c p hp w hw.1 with h1 | ⟨hadm, htriv, -⟩
    · obtain ⟨a, ha, hne⟩ := hw.2
      exact absurd (h1 a ha) hne
    · exact ⟨hadm, htriv⟩

  have hcover : ∀ (V : Set (AddValuation (Ω c) (WithTop ℤ))), V.Finite →
      ∀ S : Set (Ideal (KTp K d.D d.N)),
        (∀ p ∈ S, p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w ∈ V) → S.Finite := by
    intro V hV S hS
    have hfin : (⋃ v ∈ V, {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}).Finite := by
      refine hV.biUnion fun v _ => ?_
      by_cases hv' : d.admitted c v ∧ IsTrivOn K v
      · exact (d.AdmissibleValuationPrimeUnique hd h c v hv'.1 hv'.2).finite
      · refine Set.Subsingleton.finite ?_
        rintro p ⟨hp, w, hw, rfl⟩
        exact absurd (hgoodI hp hw) hv'
    refine hfin.subset ?_
    intro p hpS
    obtain ⟨hp, w, hw, hwV⟩ := hS p hpS
    exact Set.mem_biUnion hwV ⟨hp, w, hw, rfl⟩
  refine ⟨d.AdmissibleValuationPrimeUnique hd h c, d.GeneratorMultiHomogeneous hd h c, ?_, ?_⟩
  · intro G ta hta hta0
    refine hcover {v | d.admitted c v ∧ d.ord c v G ta ≠ 0} (hd.a3' c hta hta0) _ ?_
    rintro p ⟨hp, hne⟩
    refine ⟨hp, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hne
    refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw => ?_
    have := hcon w hw
    simp only [Set.mem_setOf_eq, not_and, not_not] at this
    rw [this (hgoodI hp hw).1, mul_zero]
  · intro ta hta hta0
    let V : Set (AddValuation (Ω c) (WithTop ℤ)) :=
      {v | d.admitted c v ∧ d.ord c v d.wL ta ≠ 0} ∪
        ⋃ j : {j // d.w j c ≠ 0}, {v | d.admitted c v ∧ d.ord c v d.wL (d.w j c) ≠ 0}
    have hV : V.Finite := (hd.a3' c hta hta0).union
      (Set.finite_iUnion fun j => hd.a3' c (hd.w_mem j c) j.2)
    refine hcover V hV _ ?_
    rintro p ⟨hp, hne⟩
    refine ⟨hp, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hne
    refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw => ?_
    have hnot := hcon w hw
    have hadm := (hgoodI hp hw).1
    have h1 : d.ord c (d.Wres c w) d.wL ta = 0 := by
      by_contra h0
      exact hnot (Or.inl ⟨hadm, h0⟩)
    have h2 : ∀ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c) = 0 := by
      intro j
      by_contra h0
      exact hnot (Or.inr (Set.mem_iUnion.mpr ⟨j, hadm, h0⟩))
    haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨d.jc c, hd.w_base c⟩⟩
    unfold ordMM
    rw [h1, show (⨅ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c)) = 0 by
      simp only [h2, ciInf_const]]
    simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0
