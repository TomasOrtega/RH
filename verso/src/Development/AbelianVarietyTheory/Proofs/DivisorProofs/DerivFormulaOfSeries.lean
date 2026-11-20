import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DerivAtOrigin

/- English proof (translation)
Establish `: polydisc I = ⋂ i : I, {z : I → ℂ | ‖z i‖ < 1}`. Use extensionality with `z`. Simplify using `[polydisc]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const`.
-/
theorem isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  have : polydisc I = ⋂ i : I, {z : I → ℂ | ‖z i‖ < 1} := by
    ext z; simp [polydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

/- English proof (translation)
Introduce `i`. Simplify using the standard rewrite rules.
-/
theorem zero_mem_polydisc (I : Type) : (0 : I → ℂ) ∈ polydisc I := by
  intro i; simp

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[List.count_cons]`. Simplify using `[List.count_cons, Pi.single_apply, h, Ne.symm h]`.
-/
theorem count_cons_eq {I : Type} [DecidableEq I] (i : I) (l : List I) :
    (fun j => (i :: l).count j) = (fun j => l.count j) + Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [List.count_cons]
  · simp [List.count_cons, Pi.single_apply, h, Ne.symm h]

/- English proof (translation)
Unfold `risingFactor`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i _`. Use `mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_ne_zero_iff]`.

Introduce `j _`. Establish `: ((k : ℂ) + j) = ((k + j : ℕ) : ℂ)` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `(by omega : k + j ≠ 0)` after adjusting the coercions.
-/
theorem risingFactor_ne_zero {I : Type} [Fintype I] (k : ℕ) (hk : 1 ≤ k) (κ : I → ℕ) :
    risingFactor k κ ≠ 0 := by
  unfold risingFactor
  rw [Finset.prod_ne_zero_iff]
  intro i _
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro j _
  have : ((k : ℂ) + j) = ((k + j : ℕ) : ℂ) := by push_cast; ring
  rw [this]
  exact_mod_cast (by omega : k + j ≠ 0)

/- English proof (translation)
Unfold `term`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem term_origin {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (x : E) :
    term φ k κ 0 x = ∏ i, ((φ i x)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i x)) ^ κ i) := by
  unfold term
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

/- English proof (translation)
Introduce `E _ _ I _ _ φ k L hk H`. Use `set T : (I → ℕ) → (I → ℂ) → ℂ := fun m w => ∑' q : modUnits L, dTerm φ k m w q.1.out with hT`. Establish `hT0 : ∀ z ∈ polydisc I, HasSum (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) (T 0 z)`. Introduce `z hz`. Establish `e : (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) = fun q : modUnits L => dTerm φ k 0 z q.1.out`.

Use function extensionality and compare the values at `fun q => (dTerm_zero φ k z q.1.out).symm`. Rewrite using `[e]`. Conclude with `(H 0 z hz).1.hasSum`. Establish `hagree : ∀ g, IsDefSum φ k L g → ∀ z ∈ polydisc I, g z = (cWt E k : ℂ) * T 0 z`. Introduce `g hg z hz`.

Take `⟨G, hG, hgz⟩` from `hg z hz`. Rewrite using `[hgz, (hG.1 (by omega)).unique (hT0 z hz)]`. Establish `hiter : ∀ g, IsDefSum φ k L g → ∀ l : List I, ∀ z ∈ polydisc I, iterD l g z = (cWt E k : ℂ) * T (fun j => l.count j) z`. Introduce `g hg l`. Proceed by induction on `l with`.

Consider the case `nil`. Introduce `z hz`. Establish `: (fun j : I => ([] : List I).count j) = 0` using `by funext j; simp`. Rewrite using `[this]`. Conclude with `hagree g hg z hz`.

Consider the case `cons i l ih`. Introduce `z hz`. Establish `hev : iterD l g =ᶠ[nhds z] fun w => (cWt E k : ℂ) * T (fun j => l.count j) w` using `by filter_upwards [(isOpen_polydisc I).mem_nhds hz] with w hw using ih w hw`. Establish `hd : HasLineDerivAt ℂ (fun w => (cWt E k : ℂ) * T (fun j => l.count j) w) ((cWt E k : ℂ) * T ((fun j => l.count j) + Pi.single i 1) z) z (Pi.single i 1)`. Establish `h1` using `(H (fun j => l.count j) z hz).2.2 i`.

Unfold `HasLineDerivAt at h1 ⊢`. Conclude with `h1.const_mul _`. Establish `h2 : iterD (i :: l) g z = lineDeriv ℂ (iterD l g) z (Pi.single i 1)` using `rfl`. Rewrite using `[h2, hev.lineDeriv_eq, hd.lineDeriv, count_cons_eq]`. Use `⟨⟨fun z => (cWt E k : ℂ) * T 0 z, fun z hz => ⟨T 0 z, ⟨fun _ => hT0 z hz, fun h => by omega⟩, rfl⟩⟩, ?_⟩` and prove the remaining obligations.

Introduce `g hg`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Establish `hev : g =ᶠ[nhds z] fun w => (cWt E k : ℂ) * T 0 w` using `by filter_upwards [(isOpen_polydisc I).mem_nhds hz] with w hw using hagree g hg w hw`. Establish `hda : DifferentiableAt ℂ (fun w => (cWt E k : ℂ) * T 0 w) z` using `((H 0 z hz).2.1).const_mul _`.

Conclude with `(hda.congr_of_eventuallyEq hev).differentiableWithinAt`. Introduce `κ l hl`. Establish `hκ : (fun j => l.count j) = κ` using `funext hl`. Establish `h0 : iterD l g 0 = (cWt E k : ℂ) * T κ 0`. Rewrite using `[hiter g hg l 0 (zero_mem_polydisc I), hκ]`.

Establish `hTκ : T κ 0 = risingFactor k κ * ∑' q : modUnits L, ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i)`. Simplify using `only [hT, dTerm_origin]`. Conclude with `tsum_mul_left`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `S hS`.

Establish `hS0` using `hS.2 0 (by`. Establish `: (4 : ℝ) ≤ k` using `by exact_mod_cast hk`. Simplify using the standard rewrite rules. Use the proof step `linarith)`. Simplify using `only [term_origin] at hS0`.

Rewrite using `[h0, hTκ, hS0.tsum_eq]`. Expand and normalize the polynomial expressions, which then agree. Introduce `_`. Establish `hsum : Summable (fun q : modUnits L => ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i))`. Establish `h` using `(H κ 0 (zero_mem_polydisc I)).1`.

Simplify using `only [dTerm_origin] at h`. Conclude with `(summable_mul_left_iff (risingFactor_ne_zero k (by omega) κ)).1 h`. Use `⟨_, hsum.hasSum, ?_⟩` and prove the remaining obligations. Rewrite using `[h0, hTκ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivFormula_of_series : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (k : ℕ) (L : Set E), 4 ≤ k → (∀ (m : I → ℕ) (z : I → ℂ), z ∈ polydisc I → Summable (fun q : modUnits L => dTerm φ k m z q.1.out) ∧ DifferentiableAt ℂ (fun w : I → ℂ => ∑' q : modUnits L, dTerm φ k m w q.1.out) z ∧ ∀ i : I, HasLineDerivAt ℂ (fun w : I → ℂ => ∑' q : modUnits L, dTerm φ k m w q.1.out) (∑' q : modUnits L, dTerm φ k (m + Pi.single i 1) z q.1.out) z (Pi.single i 1)) → DerivFormula φ k L := by
  intro E _ _ I _ _ φ k L hk H
  set T : (I → ℕ) → (I → ℂ) → ℂ := fun m w => ∑' q : modUnits L, dTerm φ k m w q.1.out with hT
  have hT0 : ∀ z ∈ polydisc I, HasSum (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) (T 0 z) := by
    intro z hz
    have e : (fun q : modUnits L => ∏ i, (defCoord φ z q.1.out i)⁻¹ ^ k) = fun q : modUnits L => dTerm φ k 0 z q.1.out :=
      funext fun q => (dTerm_zero φ k z q.1.out).symm
    rw [e]
    exact (H 0 z hz).1.hasSum

  have hagree : ∀ g, IsDefSum φ k L g → ∀ z ∈ polydisc I, g z = (cWt E k : ℂ) * T 0 z := by
    intro g hg z hz
    obtain ⟨G, hG, hgz⟩ := hg z hz
    rw [hgz, (hG.1 (by omega)).unique (hT0 z hz)]

  have hiter : ∀ g, IsDefSum φ k L g → ∀ l : List I, ∀ z ∈ polydisc I,
      iterD l g z = (cWt E k : ℂ) * T (fun j => l.count j) z := by
    intro g hg l
    induction l with
    | nil =>
      intro z hz
      have : (fun j : I => ([] : List I).count j) = 0 := by funext j; simp
      rw [this]
      exact hagree g hg z hz
    | cons i l ih =>
      intro z hz
      have hev : iterD l g =ᶠ[nhds z] fun w => (cWt E k : ℂ) * T (fun j => l.count j) w := by
        filter_upwards [(isOpen_polydisc I).mem_nhds hz] with w hw using ih w hw
      have hd : HasLineDerivAt ℂ (fun w => (cWt E k : ℂ) * T (fun j => l.count j) w)
          ((cWt E k : ℂ) * T ((fun j => l.count j) + Pi.single i 1) z) z (Pi.single i 1) := by
        have h1 := (H (fun j => l.count j) z hz).2.2 i
        unfold HasLineDerivAt at h1 ⊢
        exact h1.const_mul _
      have h2 : iterD (i :: l) g z = lineDeriv ℂ (iterD l g) z (Pi.single i 1) := rfl
      rw [h2, hev.lineDeriv_eq, hd.lineDeriv, count_cons_eq]
  refine ⟨⟨fun z => (cWt E k : ℂ) * T 0 z, fun z hz => ⟨T 0 z, ⟨fun _ => hT0 z hz, fun h => by omega⟩, rfl⟩⟩, ?_⟩
  intro g hg
  refine ⟨?_, ?_⟩
  · intro z hz
    have hev : g =ᶠ[nhds z] fun w => (cWt E k : ℂ) * T 0 w := by
      filter_upwards [(isOpen_polydisc I).mem_nhds hz] with w hw using hagree g hg w hw
    have hda : DifferentiableAt ℂ (fun w => (cWt E k : ℂ) * T 0 w) z :=
      ((H 0 z hz).2.1).const_mul _
    exact (hda.congr_of_eventuallyEq hev).differentiableWithinAt
  · intro κ l hl
    have hκ : (fun j => l.count j) = κ := funext hl
    have h0 : iterD l g 0 = (cWt E k : ℂ) * T κ 0 := by
      rw [hiter g hg l 0 (zero_mem_polydisc I), hκ]
    have hTκ : T κ 0 = risingFactor k κ *
        ∑' q : modUnits L, ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i) := by
      simp only [hT, dTerm_origin]
      exact tsum_mul_left
    refine ⟨?_, ?_⟩
    · intro S hS
      have hS0 := hS.2 0 (by
        have : (4 : ℝ) ≤ k := by exact_mod_cast hk
        simp; linarith)
      simp only [term_origin] at hS0
      rw [h0, hTκ, hS0.tsum_eq]; ring
    · intro _
      have hsum : Summable (fun q : modUnits L =>
          ∏ i, ((φ i q.1.out)⁻¹ ^ (k + κ i) * (starRingEnd ℂ (φ i q.1.out)) ^ κ i)) := by
        have h := (H κ 0 (zero_mem_polydisc I)).1
        simp only [dTerm_origin] at h
        exact (summable_mul_left_iff (risingFactor_ne_zero k (by omega) κ)).1 h
      refine ⟨_, hsum.hasSum, ?_⟩
      rw [h0, hTκ]; ring

end GlobalTheory.DerivAtOrigin
