import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelColumns

/- English proof (translation)
Simplify using `[ker]`.
-/
theorem ker_zero (X : Ctx) (x y : X.G) : ker X.Γ (0 : X.G → ℂ) x y = 0 := by
  simp [ker]

/- English proof (translation)
Introduce `l`. Establish `h : (((0 : X.Hs ι) l : Lp ℂ 2 X.ν) : X.G → ℂ) =ᵐ[X.ν] 0` using `Lp.coeFn_zero ℂ 2 X.ν`. Use `h.trans (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Conclude with `(ker_zero X z y).symm`.
-/
theorem isVec_zero (X : Ctx) {ι : Type} [Fintype ι] (y : X.G) (j : ι) :
    X.IsVec (0 : Matrix ι ι (X.G → ℂ)) y j (0 : X.Hs ι) := by
  intro l
  have h : (((0 : X.Hs ι) l : Lp ℂ 2 X.ν) : X.G → ℂ) =ᵐ[X.ν] 0 := Lp.coeFn_zero ℂ 2 X.ν
  refine h.trans (Filter.Eventually.of_forall fun z => ?_)
  exact (ker_zero X z y).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨continuous_const, HasCompactSupport.zero⟩`.
-/
theorem tst_zero (X : Ctx) : Tst (0 : X.G → ℂ) :=
  ⟨continuous_const, HasCompactSupport.zero⟩

/- English proof (translation)
Establish `h : ∀ i j, ∃ B : ℝ, ∀ z, ‖Φ i j z‖ ≤ B` using `fun i j => by`. Take `⟨B, hB⟩` from `((hΦ i j).1.norm).bddAbove_range_of_hasCompactSupport (hΦ i j).2.norm`. Conclude with `⟨B, fun z => hB ⟨z, rfl⟩⟩`. Use `choose B hB using h`. Establish `hB0 : ∀ i j, 0 ≤ B i j` using `fun i j => (norm_nonneg _).trans (hB i j 1)`.

Use `⟨∑ i, ∑ j, B i j, fun l j z => (hB l j z).trans ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_bound (X : Ctx) {ι : Type} [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ))
    (hΦ : ∀ i j, Tst (Φ i j)) : ∃ ε : ℝ, ∀ l j z, ‖Φ l j z‖ ≤ ε := by
  have h : ∀ i j, ∃ B : ℝ, ∀ z, ‖Φ i j z‖ ≤ B := fun i j => by
    obtain ⟨B, hB⟩ := ((hΦ i j).1.norm).bddAbove_range_of_hasCompactSupport (hΦ i j).2.norm
    exact ⟨B, fun z => hB ⟨z, rfl⟩⟩
  choose B hB using h
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j => (norm_nonneg _).trans (hB i j 1)
  refine ⟨∑ i, ∑ j, B i j, fun l j z => (hB l j z).trans ?_⟩
  calc B l j ≤ ∑ j, B l j :=
        Finset.single_le_sum (f := fun j => B l j) (fun j _ => hB0 l j) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, B i j :=
        Finset.single_le_sum (f := fun i => ∑ j, B i j)
          (fun i _ => Finset.sum_nonneg fun j _ => hB0 i j) (Finset.mem_univ l)

/- English proof (translation)
Introduce `hV X ι _ Φ hΦ`. Take `⟨ε, hε⟩` from `exists_bound X Φ hΦ`. Use `set Ω₀ : Set X.G := ⋃ i, ⋃ j, tsupport (Φ i j) with hΩ₀`. Establish `hc : IsCompact Ω₀` using `isCompact_iUnion fun i => isCompact_iUnion fun j => (hΦ i j).2`. Establish `hci : IsCompact Ω₀⁻¹` using `hc.inv`.

Use `⟨(Fintype.card ι : ℝ≥0∞) * (ENNReal.ofReal ε ^ 2 * X.μ Ω₀⁻¹), Ω₀⁻¹ * Ω₀, ?_, hci.mul hc, ?_⟩` and prove the remaining obligations. Conclude with `ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hci.measure_lt_top.ne)`. Introduce `y j k hk`. Establish `h` using `hV X ι Φ 0 Ω₀ ε y j k 0 hc (fun l => ⟨hΦ l j, tst_zero X, ?_, ?_, ?_⟩) hk (isVec_zero X y j)`. Simplify `h` using `[mul_assoc]`.

Conclude with `(subset_tsupport _).trans (Set.subset_iUnion_of_subset l (Set.subset_iUnion_of_subset j subset_rfl))`. Simplify using the standard rewrite rules. Introduce `z`. Simplify using `using hε l j z`.
-/
theorem vecNorm_of_vecClose : VecClose → VecNorm := by
  intro hV X ι _ Φ hΦ
  obtain ⟨ε, hε⟩ := exists_bound X Φ hΦ
  set Ω₀ : Set X.G := ⋃ i, ⋃ j, tsupport (Φ i j) with hΩ₀
  have hc : IsCompact Ω₀ := isCompact_iUnion fun i => isCompact_iUnion fun j => (hΦ i j).2
  have hci : IsCompact Ω₀⁻¹ := hc.inv
  refine ⟨(Fintype.card ι : ℝ≥0∞) * (ENNReal.ofReal ε ^ 2 * X.μ Ω₀⁻¹), Ω₀⁻¹ * Ω₀, ?_,
    hci.mul hc, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hci.measure_lt_top.ne)
  · intro y j k hk
    have h := hV X ι Φ 0 Ω₀ ε y j k 0 hc (fun l => ⟨hΦ l j, tst_zero X, ?_, ?_, ?_⟩) hk
      (isVec_zero X y j)
    · simpa [mul_assoc] using h
    · exact (subset_tsupport _).trans
        (Set.subset_iUnion_of_subset l (Set.subset_iUnion_of_subset j subset_rfl))
    · simp
    · intro z
      simpa using hε l j z

end GlobalTheory.CompanionTheory.KernelColumns

end
