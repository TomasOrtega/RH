import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDCCLower

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutBP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

/- English proof (translation)
Take `⟨g, hg⟩ : ∃ g, g ∈ B.GV k r` from `⟨1, by simp [B.GV, Formalism.QuantumDeterminants.UH]⟩`. Establish `h1` using `h.2 [] [] (by simp) (by simp) (by simp) g hg`. Establish `h2 : 0 ≤ B.gN g ^ A * ‖B.dLR [] [] F g‖` using `mul_nonneg (Real.rpow_nonneg (gN_pos hg).le _) (norm_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ccleQ_nonneg {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F : B.Mat k r → E} {b : ℝ} (h : B.CCle A m F b) : 0 ≤ b := by
  obtain ⟨g, hg⟩ : ∃ g, g ∈ B.GV k r := ⟨1, by simp [B.GV, Formalism.QuantumDeterminants.UH]⟩
  have h1 := h.2 [] [] (by simp) (by simp) (by simp) g hg
  have h2 : 0 ≤ B.gN g ^ A * ‖B.dLR [] [] F g‖ :=
    mul_nonneg (Real.rpow_nonneg (gN_pos hg).le _) (norm_nonneg _)
  linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, fun u v hu hv hl g hg => (h.2 u v hu hv hl g hg).trans hb⟩`.
-/
theorem ccleQ_mono_c {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F : B.Mat k r → E} {b b' : ℝ} (h : B.CCle A m F b) (hb : b ≤ b') : B.CCle A m F b' := ⟨h.1, fun u v hu hv hl g hg => (h.2 u v hu hv hl g hg).trans hb⟩

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro x hx`. Simplify using `at hx`. Consider the case `cons y t ih`.

Introduce `x hx`. Simplify using `only [List.foldr_cons]`. Break down `List.mem_cons.mp hx with h | h` into its components or cases. Substitute `h` using the available equality. Conclude with `le_max_left _ _`.

Conclude with `le_trans (ih x h) (le_max_right _ _)`.
-/
private theorem le_foldr_max_zero_of_mem : ∀ (l : List ℕ), ∀ x ∈ l, x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons y t ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih x h) (le_max_right _ _)

/- English proof (translation)
Introduce `T hT`. Unfold `B.opOrder`. Conclude with `le_foldr_max_zero_of_mem _ _ (List.mem_map_of_mem hT)`.
-/
theorem word_le_opOrder {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) :
    ∀ T ∈ Θ, T.word.length ≤ B.opOrder Θ := by
  intro T hT
  unfold B.opOrder
  exact le_foldr_max_zero_of_mem _ _ (List.mem_map_of_mem hT)

/- English proof (translation)
Establish `_hd` using `hd`. Use `set o := B.opOrder Θ with ho`. Establish `hO : IsOpen (∅ : Set (B.Mat k r))` using `isOpen_empty`. Establish `hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r` using `fun g hg => Or.inr hg`. Establish `hterm : ∀ T ∈ Θ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), B.CCle A (m + o) F b → B.CCle (A - d) m (ap T.coef (B.Rw T.word F)) (K * b)`.

Introduce `T hT`. Take `⟨hc1, -, hcb⟩` from `hG T hT`. Take `⟨C, hC⟩` from `hcb m`. Use `set s : ℂ := (((T.word.map nz).prod : ℝ) : ℂ) with hs`. Use `⟨2 ^ m * (|C| * ‖s‖), by positivity, fun F b hF => ?_⟩` and prove the remaining obligations.

Establish `hb0 : 0 ≤ b` using `ccleQ_nonneg hF`. Establish `hlen : T.word.length ≤ o` using `word_le_opOrder Θ T hT`. Establish `hF1 : B.CCle A (m + (T.word.map nrm).length) F b` using `CCle_mono_m (by simp; omega) hF`. Establish `hunit : ∀ X ∈ T.word.map nrm, unitLie k r X`. Introduce `X hX`.

Take `⟨Y, hY, rfl⟩` from `List.mem_map.mp hX`. Conclude with `nrm_unit (T.word_lie Y hY)`. Establish `hR : B.CCle A m (B.Rw T.word F) (‖s‖ * b)`. Rewrite using `[Rw_scale]`. Conclude with `CCle_smul s (CCle_Rw hunit hF1)`.

Establish `hR' : B.CCle (A - d + d) m (B.Rw T.word F) (‖s‖ * b)` using `by rw [sub_add_cancel]; exact hR`. Establish `hP` using `prodBound hO hcov (sCkOn_mono le_top hc1) (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).1) hR' (fun g _ hg => by simp at hg)`. Use `ccleQ_mono_c hP (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[abs_of_nonneg (mul_nonneg (norm_nonneg _) hb0)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsum : ∀ L : List (B.DTerm k r Wp Wq), (∀ T ∈ L, T ∈ Θ) → ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), B.CCle A (m + o) F b → B.CCle (A - d) m (fun g => (L.map fun T => ap T.coef (B.Rw T.word F) g).sum) (K * b)`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `_`.

Use `⟨0, le_rfl, fun F b _ => ?_⟩` and prove the remaining obligations. Simplify using `using (CCle_zero : B.CCle (A - d) m (fun _ : B.Mat k r => (0 : Wq →L[ℂ] Wp)) 0)`. Consider the case `cons T L ih`. Introduce `hL`. Take `⟨K₁, hK₁, h₁⟩` from `hterm T (hL T (by simp))`.

Take `⟨K₂, hK₂, h₂⟩` from `ih fun S hS => hL S (by simp [hS])`. Use `⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun F b hF => ?_⟩` and prove the remaining obligations. Establish `h` using `CCle_add (h₁ F b hF) (h₂ F b hF)`. Establish `e : (K₁ + K₂) * b = K₁ * b + K₂ * b` using `by ring`. Rewrite using `[e]`.

Simplify using `using h`. Take `⟨K, hK, hKb⟩` from `hsum Θ fun T hT => hT`. Use `⟨K, hK, fun F b _ hF => ?_⟩` and prove the remaining obligations. Establish `hop : B.opApply Θ F = fun g => (Θ.map fun T => ap T.coef (B.Rw T.word F) g).sum` using `rfl`. Rewrite using `[hop]`.

Conclude with `hKb F b hF`.
-/
theorem jdCCLowerQ {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d A : ℝ)
    (hd : 0 ≤ d) (hG : CutMP.GlobCoef Θ d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), B.CkOn ⊤ (B.GV k r) F →
      B.CCle A (m + B.opOrder Θ) F b → B.CCle (A - d) m (B.opApply Θ F) (K * b) := by
  have _hd := hd
  set o := B.opOrder Θ with ho
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg

  have hterm : ∀ T ∈ Θ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ),
      B.CCle A (m + o) F b → B.CCle (A - d) m (ap T.coef (B.Rw T.word F)) (K * b) := by
    intro T hT
    obtain ⟨hc1, -, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    set s : ℂ := (((T.word.map nz).prod : ℝ) : ℂ) with hs
    refine ⟨2 ^ m * (|C| * ‖s‖), by positivity, fun F b hF => ?_⟩
    have hb0 : 0 ≤ b := ccleQ_nonneg hF
    have hlen : T.word.length ≤ o := word_le_opOrder Θ T hT
    have hF1 : B.CCle A (m + (T.word.map nrm).length) F b :=
      CCle_mono_m (by simp; omega) hF
    have hunit : ∀ X ∈ T.word.map nrm, unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
      exact nrm_unit (T.word_lie Y hY)
    have hR : B.CCle A m (B.Rw T.word F) (‖s‖ * b) := by
      rw [Rw_scale]
      exact CCle_smul s (CCle_Rw hunit hF1)
    have hR' : B.CCle (A - d + d) m (B.Rw T.word F) (‖s‖ * b) := by rw [sub_add_cancel]; exact hR
    have hP := prodBound hO hcov (sCkOn_mono le_top hc1)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).1) hR' (fun g _ hg => by simp at hg)
    refine ccleQ_mono_c hP (le_of_eq ?_)
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) hb0)]
    ring

  have hsum : ∀ L : List (B.DTerm k r Wp Wq), (∀ T ∈ L, T ∈ Θ) → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), B.CCle A (m + o) F b →
        B.CCle (A - d) m (fun g => (L.map fun T => ap T.coef (B.Rw T.word F) g).sum) (K * b) := by
    intro L
    induction L with
    | nil =>
      intro _
      refine ⟨0, le_rfl, fun F b _ => ?_⟩
      simpa using (CCle_zero : B.CCle (A - d) m (fun _ : B.Mat k r => (0 : Wq →L[ℂ] Wp)) 0)
    | cons T L ih =>
      intro hL
      obtain ⟨K₁, hK₁, h₁⟩ := hterm T (hL T (by simp))
      obtain ⟨K₂, hK₂, h₂⟩ := ih fun S hS => hL S (by simp [hS])
      refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun F b hF => ?_⟩
      have h := CCle_add (h₁ F b hF) (h₂ F b hF)
      have e : (K₁ + K₂) * b = K₁ * b + K₂ * b := by ring
      rw [e]
      simpa using h
  obtain ⟨K, hK, hKb⟩ := hsum Θ fun T hT => hT
  refine ⟨K, hK, fun F b _ hF => ?_⟩
  have hop : B.opApply Θ F = fun g => (Θ.map fun T => ap T.coef (B.Rw T.word F) g).sum := rfl
  rw [hop]
  exact hKb F b hF

end

end Formalism.FourierDecayAlt.P.CutBP
