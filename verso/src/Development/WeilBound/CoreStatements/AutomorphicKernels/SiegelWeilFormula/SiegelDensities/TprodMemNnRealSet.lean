import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.SWMeasCAll

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open NumberField IsDedekindDomain Topology Filter

def nnRealSet : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}

/- English proof (translation)
The claim follows from `(isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)`.
-/
theorem isClosed_nnRealSet : IsClosed nnRealSet :=
  (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)

/- English proof (translation)
Take `⟨ha1, ha2⟩` from `ha`. Take `⟨hb1, hb2⟩` from `hb`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `[Complex.mul_im, ha1, hb1]`. Simplify using `only [Complex.mul_re, ha1, hb1, mul_zero, sub_zero]`.

Conclude with `mul_nonneg ha2 hb2`.
-/
theorem mul_mem_nnRealSet {a b : ℂ} (ha : a ∈ nnRealSet) (hb : b ∈ nnRealSet) : a * b ∈ nnRealSet := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, ?_⟩
  · simp [Complex.mul_im, ha1, hb1]
  · simp only [Complex.mul_re, ha1, hb1, mul_zero, sub_zero]
    exact mul_nonneg ha2 hb2

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simp, by simp⟩`.
-/
theorem one_mem_nnRealSet : (1 : ℂ) ∈ nnRealSet := ⟨by simp, by simp⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using one_mem_nnRealSet`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `mul_mem_nnRealSet (hf a) ih`.
-/
theorem prod_mem_nnRealSet {ι : Type} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i, f i ∈ nnRealSet) :
    ∏ i ∈ s, f i ∈ nnRealSet := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_nnRealSet
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact mul_mem_nnRealSet (hf a) ih

/- English proof (translation)
Distinguish the cases in `h : Multipliable f`. Conclude with `isClosed_nnRealSet.mem_of_tendsto h.hasProd (Eventually.of_forall fun s => prod_mem_nnRealSet s f hf)`. Rewrite using `[tprod_eq_one_of_not_multipliable h]`. Conclude with `one_mem_nnRealSet`.
-/
theorem tprod_mem_nnRealSet {ι : Type} (f : ι → ℂ) (hf : ∀ i, f i ∈ nnRealSet) : ∏' i, f i ∈ nnRealSet := by
  by_cases h : Multipliable f
  · exact isClosed_nnRealSet.mem_of_tendsto h.hasProd (Eventually.of_forall fun s => prod_mem_nnRealSet s f hf)
  · rw [tprod_eq_one_of_not_multipliable h]
    exact one_mem_nnRealSet

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ)`. Establish `h : Ideal.absNorm v.asIdeal ≠ 0` using `fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`. Conclude with `Nat.one_le_iff_ne_zero.2 h` after adjusting the coercions. Establish `hq0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ)` using `by linarith`. Establish `hp : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)) = (((Ideal.absNorm v.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)`.

Rewrite using `[Complex.ofReal_cpow hq0]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hle : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith)`. Establish `hpos : 0 ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)` using `Real.rpow_nonneg hq0 _`.

Rewrite using `[hp]`. Unfold `PositivityTheory.SiegelWeilFormula.Gen.eSp`. Use `split_ifs`. Use `⟨by simp, ?_⟩` and prove the remaining obligations. Simplify using `only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.one_im, Complex.ofReal_im]`.

Use the polynomial consequences of the given equalities and inequalities. Use `⟨by simp, ?_⟩` and prove the remaining obligations. Simplify using `only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.one_im, Complex.ofReal_im]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem factor_mem (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) (hs : 0 ≤ s) :
    (1 - PositivityTheory.SiegelWeilFormula.Gen.eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) ∈ nnRealSet := by
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    have h : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 h
  have hq0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  have hp : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)) = (((Ideal.absNorm v.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hq0]
    push_cast
    rfl
  have hle : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith)
  have hpos : 0 ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) := Real.rpow_nonneg hq0 _
  rw [hp]
  unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs
  · refine ⟨by simp, ?_⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.one_im, Complex.ofReal_im]
    nlinarith
  · refine ⟨by simp, ?_⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.one_im,
      Complex.ofReal_im]
    nlinarith

/- English proof (translation)
Establish `hmem : Λ ∈ nnRealSet`. Use `isClosed_nnRealSet.mem_of_tendsto h ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Conclude with `tprod_mem_nnRealSet _ fun v => factor_mem v s (by linarith [Set.mem_Ioi.1 hs])`. Use `⟨?_, hmem.2⟩` and prove the remaining obligations.

Apply the tactic sequence `apply Complex.ext <;> simp [hmem.1]`.
-/
theorem lamLim_real {Λ : ℂ} (h : IsLamLim F E Λ) : Λ = ((Λ.re : ℝ) : ℂ) ∧ 0 ≤ Λ.re := by
  have hmem : Λ ∈ nnRealSet := by
    refine isClosed_nnRealSet.mem_of_tendsto h ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact tprod_mem_nnRealSet _ fun v => factor_mem v s (by linarith [Set.mem_Ioi.1 hs])
  refine ⟨?_, hmem.2⟩
  apply Complex.ext <;> simp [hmem.1]

/- English proof (translation)
The claim follows from `tendsto_nhds_unique h h'`.
-/
theorem lamLim_unique {Λ Λ' : ℂ} (h : IsLamLim F E Λ) (h' : IsLamLim F E Λ') : Λ = Λ' :=
  tendsto_nhds_unique h h'

end PositivityTheory.SiegelWeilFormula.Densx

end
