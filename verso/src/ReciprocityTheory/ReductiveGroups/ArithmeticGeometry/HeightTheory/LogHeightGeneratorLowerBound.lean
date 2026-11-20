import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FsumEqSum

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
Simplify using `[ReciprocityTheory.MultiplicativeHeights.h0, ReciprocityTheory.MultiplicativeHeights.gaussAbs, ReciprocityTheory.MultiplicativeHeights.blockSphereMean]`.
-/
theorem h0_zero : ReciprocityTheory.MultiplicativeHeights.h0 (0 : KTp K d.D d.N) = 0 := by
  simp [ReciprocityTheory.MultiplicativeHeights.h0, ReciprocityTheory.MultiplicativeHeights.gaussAbs, ReciprocityTheory.MultiplicativeHeights.blockSphereMean]

/- English proof (translation)
Establish `h` using `Real.log_natCast_nonneg (d.N + 1)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lr_nonneg : (0 : ℝ) ≤ Real.log (d.N + 1 : ℕ) + 1 / 2 := by
  have h := Real.log_natCast_nonneg (d.N + 1)
  linarith

/- English proof (translation)
Distinguish the cases in `h0 : d.gen p = 0`. Rewrite using `[h0, d.h0_zero]`. Establish `: d.dg 0 = 0` using `by simp [dg]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Establish `hm` using `(d.good_primes_properties hd h c).2.1 p hp hg`. Use `ReciprocityTheory.MultiplicativeHeights.Closed.sphere_height_lower_bound K (d.D + 1) (d.N + 1) _ (d.gen p) (Nat.succ_pos _) h0 hm` as an intermediate fact. Rewrite `this` using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.succ_ne_zero, if_false, if_true, Nat.cast_zero, zero_mul, zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this`. Use `this using 2` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem logHeight_generator_lower_bound (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (hg : ∃ w, w ∈ d.GoodP c p) :
    -((d.D : ℝ) * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤ ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) := by
  by_cases h0 : d.gen p = 0
  · rw [h0, d.h0_zero]
    have : d.dg 0 = 0 := by simp [dg]
    rw [this]; simp
  · have hm := (d.good_primes_properties hd h c).2.1 p hp hg
    have := ReciprocityTheory.MultiplicativeHeights.Closed.sphere_height_lower_bound K (d.D + 1) (d.N + 1) _ (d.gen p) (Nat.succ_pos _) h0 hm
    rw [Fin.sum_univ_succ] at this
    simp only [Fin.succ_ne_zero, if_false, if_true, Nat.cast_zero, zero_mul, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    convert this using 2
    ring

/- English proof (translation)
Distinguish the cases in `hg : ∃ w, w ∈ d.GoodP c p`. Establish `hL` using `d.logHeight_generator_lower_bound hd h c hp hg`. Establish `hE0 : (0 : ℝ) ≤ d.Ep h c p` using `by exact_mod_cast d.Ep_nonneg hd h c hp`. Establish `hE` using `d.Ep_le hd h hF1d c hp`. Establish `hn0 : (0 : ℝ) ≤ d.nP h c (d.n1 • d.wde) (d.et c) p`.

Conclude with `d.nP_nonneg hd h c hp _ _ fun v hv => hd.ord_nonneg_et c v hv` after adjusting the coercions. Establish `hi : (0 : ℝ) ≤ d.cc / d.i` using `div_nonneg hd.cc_nonneg (Nat.cast_nonneg _)`. Establish `hE' : (d.Ep h c p : ℝ) ≤ d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p`. Establish `: d.cc / (2 * d.i) = (d.cc / d.i) / 2` using `by ring`. Rewrite `hE` using `[this]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hlr` using `d.lr_nonneg`. Establish `hX : (0 : ℝ) ≤ d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)` using `by positivity`. Use `set r := d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) - d.Ep h c p`. Establish `hr0 : 0 ≤ r` using `by linarith`.

Establish `hrle : r ≤ d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ)` using `by linarith`. Establish `k1 : -(r * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p)) ≤ r * (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2))`. Use the polynomial consequences of the given equalities and inequalities. Establish `k2 : r * (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤ d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) * (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2))` using `mul_le_mul_of_nonneg_right hrle hX`. Establish `: (d.Ep h c p : ℝ) = d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p - r` using `by ring`.

Rewrite using `[this]`. Use the polynomial consequences of the given equalities and inequalities. Use `push_neg at hg`. Establish `hG : d.GoodP c p = ∅` using `Set.eq_empty_iff_forall_notMem.mpr hg`. Establish `e1 : d.Ep h c p = 0` using `by unfold Ep; rw [hG]; simp`.

Establish `e2 : d.nP h c (d.n1 • d.wde) (d.et c) p = 0` using `by unfold nP; rw [hG]; simp`. Rewrite using `[e1, e2]`. Simplify using the standard rewrite rules.
-/
theorem multiplicity_mul_logHeight_le (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) :
    (d.Ep h c p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) ≤
      d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) +
        d.D * (Real.log (d.N + 1 : ℕ) + 1 / 2) * (d.cc / d.i) *
          (d.nP h c (d.n1 • d.wde) (d.et c) p * d.dg (d.gen p)) := by
  by_cases hg : ∃ w, w ∈ d.GoodP c p
  · have hL := d.logHeight_generator_lower_bound hd h c hp hg
    have hE0 : (0 : ℝ) ≤ d.Ep h c p := by exact_mod_cast d.Ep_nonneg hd h c hp
    have hE := d.Ep_le hd h hF1d c hp
    have hn0 : (0 : ℝ) ≤ d.nP h c (d.n1 • d.wde) (d.et c) p := by
      exact_mod_cast d.nP_nonneg hd h c hp _ _ fun v hv => hd.ord_nonneg_et c v hv
    have hi : (0 : ℝ) ≤ d.cc / d.i := div_nonneg hd.cc_nonneg (Nat.cast_nonneg _)
    have hE' : (d.Ep h c p : ℝ) ≤ d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p := by
      have : d.cc / (2 * d.i) = (d.cc / d.i) / 2 := by ring
      rw [this] at hE; nlinarith
    have hlr := d.lr_nonneg
    have hX : (0 : ℝ) ≤ d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by positivity
    set r := d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) - d.Ep h c p
    have hr0 : 0 ≤ r := by linarith
    have hrle : r ≤ d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) := by linarith
    have k1 : -(r * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p)) ≤ r * (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) := by
      nlinarith
    have k2 : r * (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤
        d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) *
          (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) :=
      mul_le_mul_of_nonneg_right hrle hX
    have : (d.Ep h c p : ℝ) = d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p - r := by ring
    rw [this]
    nlinarith
  · push_neg at hg
    have hG : d.GoodP c p = ∅ := Set.eq_empty_iff_forall_notMem.mpr hg
    have e1 : d.Ep h c p = 0 := by unfold Ep; rw [hG]; simp
    have e2 : d.nP h c (d.n1 • d.wde) (d.et c) p = 0 := by unfold nP; rw [hG]; simp
    rw [e1, e2]; simp

/- English proof (translation)
Unfold `h0f mahlerMeasureHeight aG`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun c _ => ?_` and prove the remaining obligations. Establish `x2` using `d.good_primes_properties hd h c`.

Establish `hfin : {p | p ∈ d.HtOne ∧ (d.nP h c d.wL (f c) p ≠ 0 ∨ d.nPMM h c (f c) p ≠ 0 ∨ d.Ep h c p ≠ 0 ∨ d.nP h c (d.n1 • d.wde) (d.et c) p ≠ 0)}.Finite`. Use `(((x2.2.2.1 _ _ (hf c).1 (hf c).2).union (x2.2.2.2 _ (hf c).1 (hf c).2)).union ((d.Ep_ne hd h c _ (hf c).1 (hf c).2).union (x2.2.2.1 _ _ (hd.et_mem c) (hd.et_ne c)))).subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hp, h1 | h1 | h1 | h1⟩`. Conclude with `Or.inl (Or.inl ⟨hp, h1⟩)`. Conclude with `Or.inl (Or.inr ⟨hp, h1⟩)`.

Conclude with `Or.inr (Or.inl ⟨hp, h1⟩)`. Conclude with `Or.inr (Or.inr ⟨hp, h1⟩)`. Use `set S := hfin.toFinset`. Establish `mem : ∀ p, p ∈ d.HtOne → (d.nP h c d.wL (f c) p ≠ 0 ∨ d.nPMM h c (f c) p ≠ 0 ∨ d.Ep h c p ≠ 0 ∨ d.nP h c (d.n1 • d.wde) (d.et c) p ≠ 0) → p ∈ S` using `fun p hp h1 => by`. Simplify using `only [S, Set.Finite.mem_toFinset]`.

Conclude with `⟨hp, h1⟩`. Rewrite using `[fsum_eq_sum _ S (fun p => (d.nP h c d.wL (f c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p)) (fun p hp h0 => mem p hp (Or.inl fun e => h0 (by simp [e]))), fsum_eq_sum _ S (fun p => (d.nPMM h c (f c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p)) …`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun p _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hp : p ∈ d.HtOne`. Simplify using `only [Set.indicator_of_mem hp]`. Establish `e` using `d.nP_split hd h c hp (f c)`. Establish `k` using `d.multiplicity_mul_logHeight_le hd h hF1d c hp`. Rewrite using `[e]`.

Use `push_cast`. Move the coercions through the operations in `at k`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[Set.indicator_of_notMem hp]`.
-/
theorem logHeight_section_bound (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) :
    d.h0f h d.wL f ≤ d.mahlerMeasureHeight h f + d.cc / d.i * d.h0f h (d.n1 • d.wde) d.et +
      d.D * (Real.log (d.N + 1 : ℕ) + 1 / 2) * (d.cc / d.i) * (d.aG h (d.n1 • d.wde) d.et : ℝ) := by
  classical
  unfold h0f mahlerMeasureHeight aG
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  have x2 := d.good_primes_properties hd h c
  have hfin : {p | p ∈ d.HtOne ∧ (d.nP h c d.wL (f c) p ≠ 0 ∨ d.nPMM h c (f c) p ≠ 0 ∨
      d.Ep h c p ≠ 0 ∨ d.nP h c (d.n1 • d.wde) (d.et c) p ≠ 0)}.Finite := by
    refine (((x2.2.2.1 _ _ (hf c).1 (hf c).2).union (x2.2.2.2 _ (hf c).1 (hf c).2)).union
      ((d.Ep_ne hd h c _ (hf c).1 (hf c).2).union
        (x2.2.2.1 _ _ (hd.et_mem c) (hd.et_ne c)))).subset ?_
    rintro p ⟨hp, h1 | h1 | h1 | h1⟩
    · exact Or.inl (Or.inl ⟨hp, h1⟩)
    · exact Or.inl (Or.inr ⟨hp, h1⟩)
    · exact Or.inr (Or.inl ⟨hp, h1⟩)
    · exact Or.inr (Or.inr ⟨hp, h1⟩)
  set S := hfin.toFinset
  have mem : ∀ p, p ∈ d.HtOne → (d.nP h c d.wL (f c) p ≠ 0 ∨ d.nPMM h c (f c) p ≠ 0 ∨
      d.Ep h c p ≠ 0 ∨ d.nP h c (d.n1 • d.wde) (d.et c) p ≠ 0) → p ∈ S := fun p hp h1 => by
    simp only [S, Set.Finite.mem_toFinset]; exact ⟨hp, h1⟩
  rw [fsum_eq_sum _ S (fun p => (d.nP h c d.wL (f c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p))
      (fun p hp h0 => mem p hp (Or.inl fun e => h0 (by simp [e]))),
    fsum_eq_sum _ S (fun p => (d.nPMM h c (f c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p))
      (fun p hp h0 => mem p hp (Or.inr (Or.inl fun e => h0 (by simp [e])))),
    fsum_eq_sum _ S (fun p => (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p))
      (fun p hp h0 => mem p hp (Or.inr (Or.inr (Or.inr fun e => h0 (by simp [e]))))),
    fsum_eq_sum _ S (fun p => d.nP h c (d.n1 • d.wde) (d.et c) p * (d.dg (d.gen p) : ℤ))
      (fun p hp h0 => mem p hp (Or.inr (Or.inr (Or.inr fun e => h0 (by simp [e])))))]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : p ∈ d.HtOne
  · simp only [Set.indicator_of_mem hp]
    have e := d.nP_split hd h c hp (f c)
    have k := d.multiplicity_mul_logHeight_le hd h hF1d c hp
    rw [e]; push_cast
    push_cast at k
    linarith
  · simp [Set.indicator_of_notMem hp]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
