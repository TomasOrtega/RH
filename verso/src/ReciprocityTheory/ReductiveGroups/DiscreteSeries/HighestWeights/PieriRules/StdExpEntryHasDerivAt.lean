import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.StTest
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.CountNotTwoOfFinrankLeOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensHW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylSum
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.InnerLowerSelf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def stdRho (ε : Fin n → Bool) : KG ε →* unitary (Matrix (Fin n) (Fin n) ℂ) where
  toFun k := ⟨toMK k, k.2.1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem stdRho_apply (ε : Fin n → Bool) (k : KG ε) :
    ((stdRho ε k : unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ) = toMK k := rfl

/- English proof (translation)
The claim follows from `(continuous_toM ε).comp continuous_subtype_val`.
-/
theorem stdRho_cont (ε : Fin n → Bool) :
    Continuous (fun k : KG ε => ((stdRho ε k : unitary (Matrix (Fin n) (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ)) :=
  (continuous_toM ε).comp continuous_subtype_val

/- English proof (translation)
Set `_ : NormedRing (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedRing`. Set `_ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedAlgebra`. Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ)`. Establish `h2` using `(LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).hasFDerivAt.comp_hasDerivAt _ h`. Establish `h3` using `hasDerivAt_real_of_complex' (z := 0) h2`.

Establish `h4 : (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)) (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X) = X i j`. Simplify using the standard rewrite rules. Conclude with `h3.congr_deriv h4`.
-/
theorem std_exp_entry_hasDerivAt (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ)
  have h2 := (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).hasFDerivAt.comp_hasDerivAt
    _ h
  have h3 := hasDerivAt_real_of_complex' (z := 0) h2
  have h4 : (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X) = X i j := by
    simp
  exact h3.congr_deriv h4

/- English proof (translation)
Introduce `X _ γ hγ i j`. Establish `e : (fun t : ℝ => ((stdRho ε (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ) i j) = fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j`. Use function extensionality and compare the values at `t`. Rewrite using `[stdRho_apply, hγ t]`. Rewrite using `[e]`.

Conclude with `std_exp_entry_hasDerivAt X i j`.
-/
theorem stdRho_hasDeriv (ε : Fin n → Bool) :
    ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((stdRho ε (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) i j)
        ((LinearMap.id : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) X i j) 0 := by
  intro X _ γ hγ i j
  have e : (fun t : ℝ => ((stdRho ε (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ) i j) = fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j := by
    funext t
    rw [stdRho_apply, hγ t]
  rw [e]
  exact std_exp_entry_hasDerivAt X i j

/- English proof (translation)
Introduce `i j h`. Establish `h1` using `congrFun h i`. Simplify using `only [stdWt, Pi.single_eq_same] at h1`. Assume the negation of the conclusion as `hij`. Rewrite `h1` using `[Pi.single_eq_of_ne hij]`.

Conclude with `one_ne_zero h1`.
-/
theorem stdWt_injective (n : ℕ) : Function.Injective (stdWt n) := by
  intro i j h
  have h1 := congrFun h i
  simp only [stdWt, Pi.single_eq_same] at h1
  by_contra hij
  rw [Pi.single_eq_of_ne hij] at h1
  exact one_ne_zero h1

/- English proof (translation)
Rewrite using `[Nat.card_eq_one_iff_exists]`. Use `⟨⟨s, rfl⟩, fun x => Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `(stdWt_injective n (add_left_cancel x.2)).symm`.
-/
theorem stdWt_card (Λ : Fin n → ℝ) (s : Fin n) :
    Nat.card {i : Fin n // Λ + stdWt n s = Λ + stdWt n i} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨s, rfl⟩, fun x => Subtype.ext ?_⟩
  exact (stdWt_injective n (add_left_cancel x.2)).symm

/- English proof (translation)
Introduce `n ε Λ T`. Take `⟨hint, hkd⟩` from `hdom n ε Λ T`. Take `⟨hs, hvan⟩` from `hsum n ε Λ hint hkd`. Establish `hs' : ∑ i, weylK ε (Λ + stdWt n i) = (Fintype.card (Fin n) : ℝ) * weylK ε Λ`. Rewrite using `[Fintype.card_fin]`.

Conclude with `hs`. Establish `hc` using `hcount n ε Λ T (Fin n) (stdRho ε) LinearMap.id (stdWt n) (stdRho_cont ε) (stdRho_hasDeriv ε) (pieriSt_kRel_stdM ε) pieriSt_stdM_diag (stdWt_injective n) hs' hvan`. Establish `ht` using `htens T.V n ε (kunits T) Λ T.w (Fin n) (stdM n) (stdWt n) (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) (KType.kSpan_eq_top T) (pieriSt_kRel_stdM ε) pieriSt_stdM_diag`. Use `⟨hc.2, fun s => ?_, hc.1⟩` and prove the remaining obligations. Establish `h` using `(ht.2 (Λ + stdWt n s)).2`.

Rewrite `h` using `[stdWt_card Λ s]`. Conclude with `h`.
-/
theorem pieriStd_of_props (hcount : PieriCountStatement) (htens : TensHWStatement)
    (hsum : WeylSumStdStatement) (hdom : KTypeIntDomStatement) : PieriStdStatement := by
  intro n ε Λ T
  obtain ⟨hint, hkd⟩ := hdom n ε Λ T
  obtain ⟨hs, hvan⟩ := hsum n ε Λ hint hkd
  have hs' : ∑ i, weylK ε (Λ + stdWt n i) = (Fintype.card (Fin n) : ℝ) * weylK ε Λ := by
    rw [Fintype.card_fin]; exact hs
  have hc := hcount n ε Λ T (Fin n) (stdRho ε) LinearMap.id (stdWt n) (stdRho_cont ε)
    (stdRho_hasDeriv ε) (pieriSt_kRel_stdM ε) pieriSt_stdM_diag (stdWt_injective n) hs' hvan
  have ht := htens T.V n ε (kunits T) Λ T.w (Fin n) (stdM n) (stdWt n) (KType.kRel T) (KType.kUnit T)
    (KType.kHighest_w T) (KType.kSpan_eq_top T) (pieriSt_kRel_stdM ε) pieriSt_stdM_diag
  refine ⟨hc.2, fun s => ?_, hc.1⟩
  have h := (ht.2 (Λ + stdWt n s)).2
  rw [stdWt_card Λ s] at h
  exact h

/- English proof (translation)
The claim follows from `pieriStd_of_props (pieriCount_of hc hr) tensHW weylSumStd kTypeIntDom`.
-/
theorem pieriStd_of (hc : CompRedStatement) (hr : KRepRelStatement) : PieriStdStatement :=
  pieriStd_of_props (pieriCount_of hc hr) tensHW weylSumStd kTypeIntDom

end ReciprocityTheory.ChartRestriction.DS.HW
