import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces

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
Rewrite using `[finsum_mem_def]`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [Function.mem_support, ne_eq, Set.indicator_apply_eq_zero, _root_.not_imp] at hx`. Conclude with `hS x hx.1 hx.2`.
-/
theorem fsum_eq_sum {α M : Type*} [AddCommMonoid M] (s : Set α) (S : Finset α) (f : α → M)
    (hS : ∀ x ∈ s, f x ≠ 0 → x ∈ S) :
    ∑ᶠ x ∈ s, f x = ∑ x ∈ S, s.indicator f x := by
  rw [finsum_mem_def]
  apply finsum_eq_sum_of_support_subset
  intro x hx
  simp only [Function.mem_support, ne_eq, Set.indicator_apply_eq_zero, _root_.not_imp] at hx
  exact hS x hx.1 hx.2

noncomputable def Emin (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) : ℤ :=
  ⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)

noncomputable def Ep (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) : ℤ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
    (d.fze h c w : ℤ) * d.Emin c (d.Wres c w)

/- English proof (translation)
Break down `d.PlaceTrivialOrPositive hd h c p hp w hw.1 with h1 | h2` into its components or cases. Take `⟨a, ha, hne⟩` from `hw.2`. Conclude with `absurd (h1 a ha) hne`. Conclude with `⟨h2.1, h2.2.1⟩`.
-/
theorem hh_good_adm (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) :
    d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w) := by
  rcases d.PlaceTrivialOrPositive hd h c p hp w hw.1 with h1 | h2
  · obtain ⟨a, ha, hne⟩ := hw.2
    exact absurd (h1 a ha) hne
  · exact ⟨h2.1, h2.2.1⟩

/- English proof (translation)
The claim follows from `((d.norm_by_places hd h c).1 p hp).subset (fun _ hw => hw.1)`.
-/
theorem good_finite (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) : (d.GoodP c p).Finite :=
  ((d.norm_by_places hd h c).1 p hp).subset (fun _ hw => hw.1)

/- English proof (translation)
Rewrite using `[hd.WW_span]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`.
-/
theorem w_mem_WW (hd : d.AxH 𝒜) (j : Fin (d.N + 1)) : d.w j ∈ d.WW := by
  rw [hd.WW_span]
  exact Submodule.subset_span ⟨j, rfl⟩

/- English proof (translation)
Use `haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨d.jc c, hd.w_base c⟩⟩`. Unfold `Emin`. Conclude with `le_ciInf fun j => hd.ord_nonneg_WW c v hv (d.w j.1) (w_mem_WW d hd j.1) j.2`.
-/
theorem Emin_nonneg (hd : d.AxH 𝒜) (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (hv : d.admitted c v) :
    0 ≤ d.Emin c v := by
  haveI : Nonempty {j // d.w j c ≠ 0} := ⟨⟨d.jc c, hd.w_base c⟩⟩
  unfold Emin
  exact le_ciInf fun j => hd.ord_nonneg_WW c v hv (d.w j.1) (w_mem_WW d hd j.1) j.2

/- English proof (translation)
Unfold `nP nPMM Ep`. Rewrite using `[← finsum_mem_add_distrib (good_finite d hd h c hp)]`. Use `finsum_congr fun w => finsum_congr fun _ => ?_` and prove the remaining obligations. Simplify using `only [ordMM, Emin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nP_split (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (f : A c) : d.nP h c d.wL f p = d.nPMM h c f p + d.Ep h c p := by
  unfold nP nPMM Ep
  rw [← finsum_mem_add_distrib (good_finite d hd h c hp)]
  refine finsum_congr fun w => finsum_congr fun _ => ?_
  simp only [ordMM, Emin]
  ring

/- English proof (translation)
Unfold `Ep`. Conclude with `finsum_nonneg fun w => finsum_nonneg fun hw => mul_nonneg (Nat.cast_nonneg _) (Emin_nonneg d hd c _ (hh_good_adm d hd h hp hw).1)`.
-/
theorem Ep_nonneg (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    0 ≤ d.Ep h c p := by
  unfold Ep
  exact finsum_nonneg fun w => finsum_nonneg fun hw =>
    mul_nonneg (Nat.cast_nonneg _) (Emin_nonneg d hd c _ (hh_good_adm d hd h hp hw).1)

/- English proof (translation)
Unfold `nP`. Conclude with `finsum_nonneg fun w => finsum_nonneg fun hw => mul_nonneg (Nat.cast_nonneg _) (hf _ (hh_good_adm d hd h hp hw).1)`.
-/
theorem nP_nonneg (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (G : WT) (f : A c) (hf : ∀ v, d.admitted c v → 0 ≤ d.ord c v G f) : 0 ≤ d.nP h c G f p := by
  unfold nP
  exact finsum_nonneg fun w => finsum_nonneg fun hw =>
    mul_nonneg (Nat.cast_nonneg _) (hf _ (hh_good_adm d hd h hp hw).1)

/- English proof (translation)
Establish `hs` using `d.good_finite hd h c hp`. Unfold `Ep nP`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_le_sum fun w hw => ?_` and prove the remaining obligations. Rewrite `hw` using `[Set.Finite.mem_toFinset]`. Establish `ha` using `d.hh_good_adm hd h hp hw`. Use `hF1d c _ ha.1 ha.2` as an intermediate fact. Establish `hf : (0 : ℝ) ≤ d.fze h c w` using `Nat.cast_nonneg _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem Ep_le (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) :
    (d.Ep h c p : ℝ) ≤ d.cc / (2 * d.i) * d.nP h c (d.n1 • d.wde) (d.et c) p := by
  have hs := d.good_finite hd h c hp
  unfold Ep nP
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  have ha := d.hh_good_adm hd h hp hw
  have := hF1d c _ ha.1 ha.2
  have hf : (0 : ℝ) ≤ d.fze h c w := Nat.cast_nonneg _
  calc (d.fze h c w : ℝ) * (d.Emin c (d.Wres c w) : ℝ)
      ≤ (d.fze h c w : ℝ) * (d.cc / (2 * d.i) * d.ord c (d.Wres c w) (d.n1 • d.wde) (d.et c)) :=
        mul_le_mul_of_nonneg_left this hf
    _ = _ := by ring

/- English proof (translation)
Use `((d.good_primes_properties hd h c).2.2.1 d.wL f hf hf0).union ((d.good_primes_properties hd h c).2.2.2 f hf hf0) |>.subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hE⟩`. Assume the negation of the conclusion as `hno`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_not] at hno`. Use `d.nP_split hd h c hp f` as an intermediate fact.

Rewrite `this` using `[hno.1 hp, hno.2 hp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Ep_ne (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (f : A c) (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    {p | p ∈ d.HtOne ∧ d.Ep h c p ≠ 0}.Finite := by
  refine ((d.good_primes_properties hd h c).2.2.1 d.wL f hf hf0).union ((d.good_primes_properties hd h c).2.2.2 f hf hf0)
    |>.subset ?_
  rintro p ⟨hp, hE⟩
  by_contra hno
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_not] at hno
  have := d.nP_split hd h c hp f
  rw [hno.1 hp, hno.2 hp] at this
  omega

end Data

end ReciprocityTheory.ChartRestriction.G.T0
