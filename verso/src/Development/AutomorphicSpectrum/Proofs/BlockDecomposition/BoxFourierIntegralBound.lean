import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CutOff.FinFT

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

/- English proof (translation)
Establish `e : boxL (L : Set (Af E)) c = Set.pi Set.univ fun i => (fun x : Af E => x - c i) ⁻¹' (L : Set (Af E))`. Use extensionality with `f`. Simplify using `[boxL, Set.mem_pi]`. Rewrite using `[e]`. Conclude with `MeasurableSet.univ_pi fun i => (hLo.preimage (continuous_id.sub continuous_const)).measurableSet`.
-/
theorem measurableSet_boxL (L : AddSubgroup (Af E)) (hLo : IsOpen (L : Set (Af E)))
    (c : Fin k → Af E) : MeasurableSet (boxL (L : Set (Af E)) c) := by
  have e : boxL (L : Set (Af E)) c =
      Set.pi Set.univ fun i => (fun x : Af E => x - c i) ⁻¹' (L : Set (Af E)) := by
    ext f; simp [boxL, Set.mem_pi]
  rw [e]
  exact MeasurableSet.univ_pi fun i =>
    (hLo.preimage (continuous_id.sub continuous_const)).measurableSet

/- English proof (translation)
Establish `hl : ∀ j, (Pi.single i a : Fin k → Af E) j ∈ L` using `fun j => by`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `using ha`. Simplify using `[Pi.single_eq_of_ne h]`.

Establish `e : ∀ j, (f + Pi.single i a : Fin k → Af E) j - c j = (f j - c j) + (Pi.single i a : Fin k → Af E) j` using `fun j => by simp only [Pi.add_apply]; ring`. Prove the components needed by the constructor for the conclusion. Introduce `h j`. Establish `h1 : (f + Pi.single i a : Fin k → Af E) j - c j ∈ L` using `h j`. Rewrite `h1` using `[e]`.

Conclude with `(L.add_mem_cancel_right (hl j)).1 h1`. Introduce `h j`. Express the relevant statement in the definitionally equal form `(f + Pi.single i a : Fin k → Af E) j - c j ∈ L`. Rewrite using `[e]`. Conclude with `L.add_mem (h j) (hl j)`.
-/
theorem boxL_add_single (L : AddSubgroup (Af E)) (c f : Fin k → Af E) (i : Fin k) {a : Af E}
    (ha : a ∈ L) : f + Pi.single i a ∈ boxL (L : Set (Af E)) c ↔ f ∈ boxL (L : Set (Af E)) c := by
  have hl : ∀ j, (Pi.single i a : Fin k → Af E) j ∈ L := fun j => by
    by_cases h : j = i
    · subst h; simpa using ha
    · simp [Pi.single_eq_of_ne h]
  have e : ∀ j, (f + Pi.single i a : Fin k → Af E) j - c j = (f j - c j) + (Pi.single i a : Fin k → Af E) j :=
    fun j => by simp only [Pi.add_apply]; ring
  constructor
  · intro h j
    have h1 : (f + Pi.single i a : Fin k → Af E) j - c j ∈ L := h j
    rw [e] at h1
    exact (L.add_mem_cancel_right (hl j)).1 h1
  · intro h j
    change (f + Pi.single i a : Fin k → Af E) j - c j ∈ L
    rw [e]
    exact L.add_mem (h j) (hl j)

/- English proof (translation)
Simplify using `only [Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `[Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules.
-/
theorem sum_add_single (f z : Fin k → Af E) (i : Fin k) (a : Af E) :
    ∑ j, (f + Pi.single i a : Fin k → Af E) j * z j = ∑ j, f j * z j + a * z i := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · simp

variable [IsTotallyComplex E]

/- English proof (translation)
Establish `hm` using `measurableSet_boxL L hLo c`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Establish `e : (fun f : Fin k → Af E => ‖(((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i))‖) = (boxL (L : Set (Af E)) c).indicator 1`. Use function extensionality and compare the values at `f`.

Apply the tactic sequence `by_cases hf : f ∈ boxL (L : Set (Af E)) c <;> simp [hf, hψ]`. Rewrite using `[e, integral_indicator_one hm]`. Introduce `hI i a ha`. Establish `hinv : (nuFin E k).IsAddRightInvariant`. Unfold `nuFin`.

Use `infer_instance`. Establish `key` using `integral_add_right_eq_self (μ := nuFin E k) (fun f => (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i))) (Pi.single i a : Fin k → Af E)`. Establish `e : ∀ f : Fin k → Af E, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) (f + Pi.single i a) : ℝ) : ℂ) * ψ (sFin E (∑ j, (f + Pi.single i a : Fin k → Af E) j * z j)) = ψ (sFin E (a * z i)) * ((((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E …` using `fun f => by`. Rewrite using `[sum_add_single, map_add, AddChar.map_add_eq_mul]`. Distinguish the cases in `hf : f ∈ boxL (L : Set (Af E)) c`.

Rewrite using `[Set.indicator_of_mem ((boxL_add_single L c f i ha).2 hf), Set.indicator_of_mem hf]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Set.indicator_of_notMem (fun h => hf ((boxL_add_single L c f i ha).1 h)), Set.indicator_of_notMem hf]`. Simplify using the standard rewrite rules. Simplify using `only [e] at key`.

Rewrite `key` using `[integral_const_mul]`. Conclude with `mul_right_cancel₀ hI (key.trans (one_mul _).symm)`.
-/
theorem box_fourier {ψ : AddChar (Ad E) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (_hc : Continuous ψ)
    (L : AddSubgroup (Af E)) (_hLc : IsCompact (L : Set (Af E))) (hLo : IsOpen (L : Set (Af E)))
    (c z : Fin k → Af E) :
    ‖∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k‖ ≤ (nuFin E k).real (boxL (L : Set (Af E)) c) ∧
    (∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k ≠ 0 →
      ∀ i, ∀ a ∈ L, ψ (sFin E (a * z i)) = 1) := by
  have hm := measurableSet_boxL L hLo c
  refine ⟨?_, ?_⟩
  · refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    have e : (fun f : Fin k → Af E => ‖(((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i))‖) = (boxL (L : Set (Af E)) c).indicator 1 := by
      funext f
      by_cases hf : f ∈ boxL (L : Set (Af E)) c <;> simp [hf, hψ]
    rw [e, integral_indicator_one hm]
  · intro hI i a ha
    have hinv : (nuFin E k).IsAddRightInvariant := by
      unfold nuFin; infer_instance
    have key := integral_add_right_eq_self (μ := nuFin E k)
      (fun f => (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * z i))) (Pi.single i a : Fin k → Af E)
    have e : ∀ f : Fin k → Af E,
        (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) (f + Pi.single i a) : ℝ) : ℂ) *
          ψ (sFin E (∑ j, (f + Pi.single i a : Fin k → Af E) j * z j)) =
        ψ (sFin E (a * z i)) * ((((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
          ψ (sFin E (∑ j, f j * z j))) := fun f => by
      rw [sum_add_single, map_add, AddChar.map_add_eq_mul]
      by_cases hf : f ∈ boxL (L : Set (Af E)) c
      · rw [Set.indicator_of_mem ((boxL_add_single L c f i ha).2 hf), Set.indicator_of_mem hf]
        ring
      · rw [Set.indicator_of_notMem (fun h => hf ((boxL_add_single L c f i ha).1 h)),
          Set.indicator_of_notMem hf]
        simp
    simp only [e] at key
    rw [integral_const_mul] at key
    exact mul_right_cancel₀ hI (key.trans (one_mul _).symm)

/- English proof (translation)
Introduce `h1 h2 L h3 h4 c z` and use `box_fourier h1 h2 L h3 h4 c z`.
-/
theorem box_fourier_main : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, (∀ x, ‖ψ x‖ = 1) → Continuous ψ → ∀ (L : AddSubgroup (Af E)), IsCompact (L : Set (Af E)) → IsOpen (L : Set (Af E)) → ∀ (c z : Fin k → Af E), ‖∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k‖ ≤ (nuFin E k).real (boxL (L : Set (Af E)) c) ∧ (∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k ≠ 0 → ∀ i, ∀ a ∈ L, ψ (sFin E (a * z i)) = 1) :=
  fun h1 h2 L h3 h4 c z => box_fourier h1 h2 L h3 h4 c z

end GlobalTheory.CompanionTheory.CutOff.FinFT
end
