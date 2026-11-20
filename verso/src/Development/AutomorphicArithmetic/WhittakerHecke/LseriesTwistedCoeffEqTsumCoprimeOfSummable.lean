import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Introduce `N χ μ s hS`. Establish `hterm : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, LSeries.term (bN N χ μ) s (n : ℕ) = μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s)`. Introduce and unpack `⟨n, hn, hc⟩`. Establish `hn0 : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Rewrite using `[LSeries.term_of_ne_zero hn.ne']`.

Simplify using `only [bN, if_pos hc]`. Rewrite using `[Complex.cpow_sub _ _ hn0, Complex.cpow_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hzero : ∀ x ∉ Set.range (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ), LSeries.term (bN N χ μ) s x = 0`. Introduce `x hx`.

Distinguish the cases in `h0 : x = 0`. Rewrite using `[h0, LSeries.term_zero]`. Rewrite using `[LSeries.term_of_ne_zero h0]`. Establish `hc : ¬ x.Coprime N` using `fun hc => hx ⟨⟨x, Nat.pos_of_ne_zero h0, hc⟩, rfl⟩`. Simplify using `only [bN, if_neg hc, zero_div]`.

Establish `heq : (LSeries.term (bN N χ μ) s) ∘ (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ) = fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s)`. Use function extensionality and compare the values at `hterm`. Use `⟨(Subtype.val_injective.summable_iff hzero).1 (heq ▸ hS), ?_⟩` and prove the remaining obligations. Establish `hsupp : Function.support (LSeries.term (bN N χ μ) s) ⊆ Set.range (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ)`. Introduce `x hx`.

Assume the negation of the conclusion as `h`. Conclude with `hx (hzero x h)`. Rewrite using `[LSeries, ← Subtype.val_injective.tsum_eq hsupp]`. Conclude with `tsum_congr hterm`.
-/
theorem UpperTheory.lseries_twisted_coeff_eq_tsum_coprime_of_summable :
    ∀ (N : ℕ) (χ : HChar ℚ) (μ : ℕ → ℂ) (s : ℂ),
        Summable (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s)) →
        LSeriesSummable (bN N χ μ) s ∧
          LSeries (bN N χ μ) s = ∑' n : {n : ℕ // 0 < n ∧ n.Coprime N}, μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) := by
  intro N χ μ s hS
  have hterm : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, LSeries.term (bN N χ μ) s (n : ℕ) =
      μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) := by
    rintro ⟨n, hn, hc⟩
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne']
    simp only [bN, if_pos hc]
    rw [Complex.cpow_sub _ _ hn0, Complex.cpow_one]
    ring
  have hzero : ∀ x ∉ Set.range (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ),
      LSeries.term (bN N χ μ) s x = 0 := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero h0]
      have hc : ¬ x.Coprime N := fun hc => hx ⟨⟨x, Nat.pos_of_ne_zero h0, hc⟩, rfl⟩
      simp only [bN, if_neg hc, zero_div]
  have heq : (LSeries.term (bN N χ μ) s) ∘ (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ) =
      fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s) :=
    funext hterm
  refine ⟨(Subtype.val_injective.summable_iff hzero).1 (heq ▸ hS), ?_⟩
  have hsupp : Function.support (LSeries.term (bN N χ μ) s) ⊆
      Set.range (Subtype.val : {n : ℕ // 0 < n ∧ n.Coprime N} → ℕ) := by
    intro x hx
    by_contra h
    exact hx (hzero x h)
  rw [LSeries, ← Subtype.val_injective.tsum_eq hsupp]
  exact tsum_congr hterm
