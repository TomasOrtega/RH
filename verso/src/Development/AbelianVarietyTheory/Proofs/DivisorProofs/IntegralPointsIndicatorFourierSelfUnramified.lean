import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.RatWeilOp

/- English proof (translation)
Introduce `F _ _ v ψ hψ κ _ _ _ μ _ hμ`. Establish `hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v))` using `Valued.isOpen_valuationSubring _`. Establish `hSo : IsOpen {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}`. Establish `e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} = ⋂ i, (fun x : κ → Fv F v => x i) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))` using `by ext; simp`. Rewrite using `[e]`.

Conclude with `isOpen_iInter_of_finite fun i => hO.preimage (continuous_apply i)`. Establish `hSm` using `hSo.measurableSet`. Establish `hψO : ∀ z ∈ v.adicCompletionIntegers F, ψ z = 1` using `fun z hz => by`. Simplify using `using (hψ 1).2 (v.adicCompletionIntegers F).one_mem z hz`. Establish `hdot : ∀ x y : κ → Fv F v, (∀ i, x i ∈ v.adicCompletionIntegers F) → (∀ i, y i ∈ v.adicCompletionIntegers F) → x ⬝ᵥ y ∈ v.adicCompletionIntegers F` using `fun x y hx hy => (v.adicCompletionIntegers F).sum_mem fun i _ => mul_mem (hx i) (hy i)`.

Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : ∀ i, y i ∈ v.adicCompletionIntegers F`. Establish `e : (fun x => ind κ v x * ψ (x ⬝ᵥ y)) = Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : ∀ i, x i ∈ v.adicCompletionIntegers F`.

Establish `hx' : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}` using `hx`. Simplify using `only [ind, Set.indicator_of_mem hx', Pi.one_apply, one_mul, hψO _ (hdot x y hx hy)]`. Establish `hx' : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}` using `hx`. Simplify using `only [ind, Set.indicator_of_notMem hx', zero_mul]`. Establish `hy' : y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}` using `hy`.

Rewrite using `[e, integral_indicator hSm, setIntegral_const, Measure.real, hμ]`. Simplify using `[ind, Set.indicator_of_mem hy']`. Establish `hy' : y ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}` using `hy`. Establish `h0 : ind κ v y = 0` using `by simp only [ind, Set.indicator_of_notMem hy']`. Rewrite using `[h0]`.

Use `push_neg at hy`. Take `⟨i, hi⟩` from `hy`. Establish `: ¬ ∀ t ∈ v.adicCompletionIntegers F, ψ (y i * t) = 1` using `fun h => hi ((hψ (y i)).1 h)`. Use `push_neg at this`. Take `⟨t, ht, hne⟩` from `this`.

Establish `hs : ∀ j, (Pi.single i t : κ → Fv F v) j ∈ v.adicCompletionIntegers F` using `fun j => by`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using ht`. Simplify using `[Pi.single_apply, hj]`.

Establish `hind : ∀ x, ind κ v (Pi.single i t + x) = ind κ v x` using `fun x => by`. Establish `: (∀ j, ((Pi.single i t : κ → Fv F v) + x) j ∈ v.adicCompletionIntegers F) ↔ ∀ j, x j ∈ v.adicCompletionIntegers F`. Prove the components needed by the constructor for the conclusion. Introduce `h j`. Use `sub_mem (h j) (hs j)` as an intermediate fact.

Simplify using `using this`. Introduce `h j`. Conclude with `add_mem (hs j) (h j)`. Distinguish the cases in `hx : ∀ j, x j ∈ v.adicCompletionIntegers F`. Establish `h1 : Pi.single i t + x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}` using `this.2 hx`.

Establish `h2 : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}` using `hx`. Simplify using `only [ind, Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply]`. Establish `h1 : Pi.single i t + x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}` using `fun h => hx (this.1 h)`. Establish `h2 : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}` using `hx`. Simplify using `only [ind, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]`.

Establish `key : ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = ψ (y i * t) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ`. Rewrite using `[← integral_const_mul]`. Use `conv_lhs => rw [← integral_add_left_eq_self (μ := μ) (fun x => ind κ v x * ψ (x ⬝ᵥ y)) (Pi.single i t)]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Rewrite using `[hind, add_dotProduct, single_dotProduct, AddChar.map_add_eq_mul, mul_comm t (y i)]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (1 - ψ (y i * t)) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = 0`. Rewrite using `[sub_mul, one_mul, ← key, sub_self]`. Conclude with `(mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm hne))`.
-/
theorem ind_fourier_self : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    μ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 → (fun y : κ → Fv F v => ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ) = ind κ v := by
  intro F _ _ v ψ hψ κ _ _ _ μ _ hμ
  classical
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hSo : IsOpen {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
        ⋂ i, (fun x : κ → Fv F v => x i) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext; simp
    rw [e]; exact isOpen_iInter_of_finite fun i => hO.preimage (continuous_apply i)
  have hSm := hSo.measurableSet
  have hψO : ∀ z ∈ v.adicCompletionIntegers F, ψ z = 1 := fun z hz => by
    simpa using (hψ 1).2 (v.adicCompletionIntegers F).one_mem z hz
  have hdot : ∀ x y : κ → Fv F v, (∀ i, x i ∈ v.adicCompletionIntegers F) → (∀ i, y i ∈ v.adicCompletionIntegers F) →
      x ⬝ᵥ y ∈ v.adicCompletionIntegers F := fun x y hx hy =>
    (v.adicCompletionIntegers F).sum_mem fun i _ => mul_mem (hx i) (hy i)
  funext y
  by_cases hy : ∀ i, y i ∈ v.adicCompletionIntegers F
  · have e : (fun x => ind κ v x * ψ (x ⬝ᵥ y)) =
        Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
      · have hx' : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_mem hx', Pi.one_apply, one_mul, hψO _ (hdot x y hx hy)]
      · have hx' : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_notMem hx', zero_mul]
    have hy' : y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hy
    rw [e, integral_indicator hSm, setIntegral_const, Measure.real, hμ]
    simp [ind, Set.indicator_of_mem hy']
  · have hy' : y ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hy
    have h0 : ind κ v y = 0 := by simp only [ind, Set.indicator_of_notMem hy']
    rw [h0]
    push_neg at hy
    obtain ⟨i, hi⟩ := hy
    have : ¬ ∀ t ∈ v.adicCompletionIntegers F, ψ (y i * t) = 1 := fun h => hi ((hψ (y i)).1 h)
    push_neg at this
    obtain ⟨t, ht, hne⟩ := this
    have hs : ∀ j, (Pi.single i t : κ → Fv F v) j ∈ v.adicCompletionIntegers F := fun j => by
      by_cases hj : j = i
      · subst hj; simpa using ht
      · simp [Pi.single_apply, hj]
    have hind : ∀ x, ind κ v (Pi.single i t + x) = ind κ v x := fun x => by
      have : (∀ j, ((Pi.single i t : κ → Fv F v) + x) j ∈ v.adicCompletionIntegers F) ↔ ∀ j, x j ∈ v.adicCompletionIntegers F := by
        constructor
        · intro h j
          have := sub_mem (h j) (hs j)
          simpa using this
        · intro h j
          exact add_mem (hs j) (h j)
      by_cases hx : ∀ j, x j ∈ v.adicCompletionIntegers F
      · have h1 : Pi.single i t + x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := this.2 hx
        have h2 : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply]
      · have h1 : Pi.single i t + x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := fun h => hx (this.1 h)
        have h2 : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    have key : ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = ψ (y i * t) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ := by
      rw [← integral_const_mul]
      conv_lhs => rw [← integral_add_left_eq_self (μ := μ) (fun x => ind κ v x * ψ (x ⬝ᵥ y)) (Pi.single i t)]
      congr 1
      funext x
      rw [hind, add_dotProduct, single_dotProduct, AddChar.map_add_eq_mul, mul_comm t (y i)]
      ring
    have h1 : (1 - ψ (y i * t)) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm hne))

end GlobalTheory.RatWeilOp
