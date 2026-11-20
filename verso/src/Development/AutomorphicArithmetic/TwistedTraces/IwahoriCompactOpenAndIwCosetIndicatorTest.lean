import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Pointwise

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `Set.mul_mem_mul (Set.mul_mem_mul ha rfl) hb`. Introduce and unpack `⟨x, ⟨a, ha, d, rfl, rfl⟩, b, hb, rfl⟩`.

Conclude with `⟨a, ha, b, hb, rfl⟩`.
-/
private theorem iwCoset_eq_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    iwCoset w ν = ((GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) *
        ({Cartan.diagPow (w.adicCompletion K) n ν} : Set (Gw n w))) *
      (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Set.mul_mem_mul (Set.mul_mem_mul ha rfl) hb
  · rintro ⟨x, ⟨a, ha, d, rfl, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

/- English proof (translation)
Rewrite using `[iwCoset_eq_mul]`. Conclude with `(GLnLocal.isOpen_iwahori (w.adicCompletion K) n).mul_left`.
-/
private theorem isOpen_iwCoset {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    IsOpen (iwCoset w ν) := by
  rw [iwCoset_eq_mul]
  exact (GLnLocal.isOpen_iwahori (w.adicCompletion K) n).mul_left

/- English proof (translation)
Rewrite using `[iwCoset_eq_mul]`. Establish `hI` using `GLnLocal.isCompact_iwahori (w.adicCompletion K) n`. Conclude with `(hI.mul isCompact_singleton).mul hI`.
-/
private theorem isCompact_iwCoset {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    IsCompact (iwCoset w ν) := by
  rw [iwCoset_eq_mul]
  have hI := GLnLocal.isCompact_iwahori (w.adicCompletion K) n
  exact (hI.mul isCompact_singleton).mul hI

/- English proof (translation)
Introduce `K _ _ n w`. Use `⟨⟨GLnLocal.isCompact_iwahori _ n, GLnLocal.isOpen_iwahori _ n⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `U ho hle`. Conclude with `⟨(GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) hle, ho⟩`. Introduce `ν`.

Establish `hc` using `isCompact_iwCoset w ν`. Establish `hclopen : IsClopen (iwCoset w ν)` using `⟨hc.isClosed, isOpen_iwCoset w ν⟩`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`.

Distinguish the cases in `hx : x ∈ iwCoset w ν`. Use `filter_upwards [hclopen.isOpen.mem_nhds hx] with y hy`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`. Both sides reduce to the same expression. Use `filter_upwards [hclopen.compl.isOpen.mem_nhds hx] with y hy`.

Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`. Conclude with `HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _`. Introduce `u hu g`. Establish `hiff : u * g ∈ iwCoset w ν ↔ g ∈ iwCoset w ν`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, b, hb, h⟩`. Use `⟨u⁻¹ * a, mul_mem (inv_mem hu) ha, b, hb, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `⟨u * a, mul_mem hu ha, b, hb, by simp only [mul_assoc]⟩`.

Distinguish the cases in `hg : g ∈ iwCoset w ν`. Rewrite using `[Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hiff.1 h))]`.
-/
theorem UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (w : Pl K),
        CO (GLnLocal.iwahori (w.adicCompletion K) n) ∧
        (∀ U : Subgroup (Gw n w), IsOpen (U : Set (Gw n w)) → U ≤ GLnLocal.integralGL (w.adicCompletion K) n → CO U) ∧
        ∀ ν : Fin n → ℤ, Test ((iwCoset w ν).indicator 1 : Gw n w → ℂ) ∧
          ∀ u ∈ GLnLocal.iwahori (w.adicCompletion K) n, ∀ g : Gw n w,
            (iwCoset w ν).indicator (1 : Gw n w → ℂ) (u * g) = (iwCoset w ν).indicator (1 : Gw n w → ℂ) g := by
  intro K _ _ n w
  refine ⟨⟨GLnLocal.isCompact_iwahori _ n, GLnLocal.isOpen_iwahori _ n⟩, ?_, ?_⟩
  · intro U ho hle
    exact ⟨(GLnLocal.isCompact_integralGL _ n).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ ho) hle, ho⟩
  · intro ν
    have hc := isCompact_iwCoset w ν
    have hclopen : IsClopen (iwCoset w ν) := ⟨hc.isClosed, isOpen_iwCoset w ν⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      by_cases hx : x ∈ iwCoset w ν
      · filter_upwards [hclopen.isOpen.mem_nhds hx] with y hy
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
        rfl
      · filter_upwards [hclopen.compl.isOpen.mem_nhds hx] with y hy
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _
    · intro u hu g
      have hiff : u * g ∈ iwCoset w ν ↔ g ∈ iwCoset w ν := by
        constructor
        · rintro ⟨a, ha, b, hb, h⟩
          refine ⟨u⁻¹ * a, mul_mem (inv_mem hu) ha, b, hb, ?_⟩
          calc g = u⁻¹ * (u * g) := (inv_mul_cancel_left u g).symm
            _ = _ := by rw [h]; simp only [mul_assoc]
        · rintro ⟨a, ha, b, hb, rfl⟩
          exact ⟨u * a, mul_mem hu ha, b, hb, by simp only [mul_assoc]⟩
      by_cases hg : g ∈ iwCoset w ν
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg)]
        rfl
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hiff.1 h))]
