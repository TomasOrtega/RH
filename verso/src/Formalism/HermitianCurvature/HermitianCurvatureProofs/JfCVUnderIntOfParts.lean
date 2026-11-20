import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section WS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def wsum (L : List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) : E :=
  (L.map fun cw => cw.1 • Rw cw.2 f g).sum

/- English proof (translation)
Simplify using `[wsum]`.
-/
theorem wsum_nil (f : Mat k r → E) (g : Mat k r) : wsum [] f g = 0 := by
  simp [wsum]

/- English proof (translation)
Simplify using `[wsum]`.
-/
theorem wsum_cons (cw : ℂ × List (Mat k r)) (L : List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (cw :: L) f g = cw.1 • Rw cw.2 f g + wsum L f g := by
  simp [wsum]

/- English proof (translation)
Simplify using `[wsum, List.map_append, List.sum_append]`.
-/
theorem wsum_append (L₁ L₂ : List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (L₁ ++ L₂) f g = wsum L₁ f g + wsum L₂ f g := by
  simp [wsum, List.map_append, List.sum_append]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp [wsum]`. Consider the case `cons cw L ih`. Simplify using `only [List.map_cons, wsum_cons, ih, smul_add, mul_smul]`.
-/
theorem wsum_scale (c : ℂ) (L : List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (L.map fun cw => (c * cw.1, cw.2)) f g = c • wsum L f g := by
  induction L with
  | nil => simp [wsum]
  | cons cw L ih =>
    simp only [List.map_cons, wsum_cons, ih, smul_add, mul_smul]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [wsum]`. Consider the case `cons i l ih => simp [List.flatMap_cons, wsum_append, ih]`.
-/
theorem wsum_flatMap {ι : Type*} (l : List ι) (F : ι → List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (l.flatMap F) f g = (l.map fun i => wsum (F i) f g).sum := by
  induction l with
  | nil => simp [wsum]
  | cons i l ih => simp [List.flatMap_cons, wsum_append, ih]

def WOK (L : List (ℂ × List (Mat k r))) (j : ℕ) : Prop :=
  ∀ cw ∈ L, (∀ X ∈ cw.2, inLie k r X) ∧ cw.2.length ≤ j

/- English proof (translation)
Rewrite using `[← Dw_wR]`. Apply `CkOn_Dw` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [wR, List.mem_map] at hx`. Take `⟨X, hX, rfl⟩` from `hx`.

Conclude with `hw X hX`. Apply `sCkOn_mono _ hf` to reduce the goal to its premises. Establish `h1 : (wR w).length = w.length` using `by simp [wR]`. Rewrite using `[h1]`. Conclude with `(by omega : 1 + w.length ≤ j + 1)` after adjusting the coercions.
-/
theorem ckOn_Rw_loc {UU : Set (Mat k r)} {w : List (Mat k r)} (hw : ∀ X ∈ w, inLie k r X) {j : ℕ}
    (hj : w.length + 1 ≤ j + 1) {f : Mat k r → E} (hf : CkOn ((j + 1 : ℕ) : ℕ∞) UU f) :
    CkOn 1 UU (Rw w f) := by
  rw [← Dw_wR]
  apply CkOn_Dw
  · intro x hx
    simp only [wR, List.mem_map] at hx
    obtain ⟨X, hX, rfl⟩ := hx
    exact hw X hX
  · apply sCkOn_mono _ hf
    have h1 : (wR w).length = w.length := by simp [wR]
    rw [h1]
    exact_mod_cast (by omega : 1 + w.length ≤ j + 1)

/- English proof (translation)
Establish `hgU : g ∈ O ∩ GV k r` using `⟨hgO, hgG⟩`. Establish `hword : ∀ cw ∈ L, HasDerivAt (fun t : ℝ => Rw cw.2 f (g * NormedSpace.exp ((t : ℂ) • X))) (Rw (X :: cw.2) f g) 0`. Introduce `cw hcw`. Take `⟨h1, h2⟩` from `hL cw hcw`. Take `⟨U, f', hU, hgU', hf', he⟩` from `ckOn_Rw_loc h1 (by omega) hf g hgU`.

Establish `hγ` using `Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g X 0`. Establish `hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g` using `by simp`. Establish `hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ U` using `hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU')`. Establish `hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), Rw cw.2 f (g * NormedSpace.exp ((t : ℂ) • X)) = f' (g * NormedSpace.exp ((t : ℂ) • X))` using `by filter_upwards [hmem] with t ht`. Conclude with `he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)`.

Establish `hf'd : DifferentiableAt ℝ f' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))`. Rewrite using `[hγ0]`. Conclude with `(hf'.contDiffAt (hU.mem_nhds hgU')).differentiableAt (by simp)`. Conclude with `((hf'd.comp (0 : ℝ) hγ.differentiableAt).congr_of_eventuallyEq hev).hasDerivAt`. Establish `key : ∀ L' : List (ℂ × List (Mat k r)), (∀ cw ∈ L', cw ∈ L) → HasDerivAt (fun t : ℝ => wsum L' f (g * NormedSpace.exp ((t : ℂ) • X))) (wsum (L'.map fun cw => (cw.1, X :: cw.2)) f g) 0`.

Introduce `L'`. Proceed by induction on `L' with`. Consider the case `nil => intro _`. Simplify `hasDerivAt_const (0 : ℝ) (0 : E)` using `[wsum]`. Consider the case `cons cw L' ih`.

Introduce `hsub`. Simplify using `only [List.map_cons, wsum_cons]`. Conclude with `((hword cw (hsub cw (by simp))).const_smul cw.1).add (ih (fun c hc => hsub c (by simp [hc])))`. Establish `hcrv : ∀ t : ℝ, crv (false, X) g t = g * NormedSpace.exp ((t : ℂ) • X)` using `fun t => by simp [crv]`. Simplify using `only [hcrv]`.

Conclude with `key L (fun _ h => h)`.
-/
theorem wsum_hasDeriv {O : Set (Mat k r)} {L : List (ℂ × List (Mat k r))} {j : ℕ} (hL : WOK L j)
    {f : Mat k r → E} (hf : CkOn ((j + 1 : ℕ) : ℕ∞) (O ∩ GV k r) f) {X : Mat k r} (hX : inLie k r X)
    {g : Mat k r} (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    HasDerivAt (fun t : ℝ => wsum L f (crv (false, X) g t)) (wsum (L.map fun cw => (cw.1, X :: cw.2)) f g) 0 := by
  have hgU : g ∈ O ∩ GV k r := ⟨hgO, hgG⟩
  have hword : ∀ cw ∈ L, HasDerivAt (fun t : ℝ => Rw cw.2 f (g * NormedSpace.exp ((t : ℂ) • X)))
      (Rw (X :: cw.2) f g) 0 := by
    intro cw hcw
    obtain ⟨h1, h2⟩ := hL cw hcw
    obtain ⟨U, f', hU, hgU', hf', he⟩ := ckOn_Rw_loc h1 (by omega) hf g hgU
    have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g X 0
    have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
    have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU')
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
        Rw cw.2 f (g * NormedSpace.exp ((t : ℂ) • X)) = f' (g * NormedSpace.exp ((t : ℂ) • X)) := by
      filter_upwards [hmem] with t ht
      exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)
    have hf'd : DifferentiableAt ℝ f' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
      rw [hγ0]
      exact (hf'.contDiffAt (hU.mem_nhds hgU')).differentiableAt (by simp)
    exact ((hf'd.comp (0 : ℝ) hγ.differentiableAt).congr_of_eventuallyEq hev).hasDerivAt
  have key : ∀ L' : List (ℂ × List (Mat k r)), (∀ cw ∈ L', cw ∈ L) →
      HasDerivAt (fun t : ℝ => wsum L' f (g * NormedSpace.exp ((t : ℂ) • X)))
        (wsum (L'.map fun cw => (cw.1, X :: cw.2)) f g) 0 := by
    intro L'
    induction L' with
    | nil => intro _; simpa [wsum] using hasDerivAt_const (0 : ℝ) (0 : E)
    | cons cw L' ih =>
      intro hsub
      simp only [List.map_cons, wsum_cons]
      exact ((hword cw (hsub cw (by simp))).const_smul cw.1).add (ih (fun c hc => hsub c (by simp [hc])))
  have hcrv : ∀ t : ℝ, crv (false, X) g t = g * NormedSpace.exp ((t : ℂ) • X) := fun t => by simp [crv]
  simp only [hcrv]
  exact key L (fun _ h => h)

def stepL (k r : ℕ) (u : ℂ) (c d : Fin (2 * r + k + 1)) (L : List (ℂ × List (Mat k r))) :
    List (ℂ × List (Mat k r)) :=
  (if c = d then L.map (fun cw => (u * cw.1, cw.2)) else []) ++
    ((L.map fun cw => (cw.1, Xa k r c d :: cw.2)) ++
      (L.map fun cw => (cw.1, Xb k r c d :: cw.2)).map fun cw => (Complex.I * cw.1, cw.2))

/- English proof (translation)
Introduce `cw hcw`. Establish `hmem : cw ∈ (if c = d then L.map (fun cw => (u * cw.1, cw.2)) else []) ∨ cw ∈ L.map (fun cw => (cw.1, Xa k r c d :: cw.2)) ∨ cw ∈ (L.map fun cw => (cw.1, Xb k r c d :: cw.2)).map fun cw => (Complex.I * cw.1, cw.2)`. Simplify `hcw` using `only [stepL, List.mem_append, or_assoc]`. Break down `hmem with h | h | h` into its components or cases. Distinguish the cases in `hcd : c = d`.

Rewrite `h` using `[if_pos hcd]`. Take `⟨cw', hcw', rfl⟩` from `List.mem_map.1 h`. Take `⟨h1, h2⟩` from `hL cw' hcw'`. Conclude with `⟨h1, Nat.le_succ_of_le h2⟩`. Rewrite `h` using `[if_neg hcd]`.

Simplify using `at h`. Take `⟨cw', hcw', rfl⟩` from `List.mem_map.1 h`. Take `⟨h1, h2⟩` from `hL cw' hcw'`. Use `⟨?_, by simpa using h2⟩` and prove the remaining obligations. Introduce `X hX`.

Break down `List.mem_cons.1 hX with rfl | hX` into its components or cases. Conclude with `Xa_lie c d`. Conclude with `h1 X hX`. Take `⟨x, hx, rfl⟩` from `List.mem_map.1 h`. Take `⟨cw', hcw', rfl⟩` from `List.mem_map.1 hx`.

Take `⟨h1, h2⟩` from `hL cw' hcw'`. Use `⟨?_, by simpa using h2⟩` and prove the remaining obligations. Introduce `X hX`. Break down `List.mem_cons.1 hX with rfl | hX` into its components or cases. Conclude with `Xb_lie c d`.

Conclude with `h1 X hX`.
-/
theorem stepL_ok {u : ℂ} {c d : Fin (2 * r + k + 1)} {L : List (ℂ × List (Mat k r))} {j : ℕ} (hL : WOK L j) :
    WOK (stepL k r u c d L) (j + 1) := by
  intro cw hcw
  have hmem : cw ∈ (if c = d then L.map (fun cw => (u * cw.1, cw.2)) else []) ∨
      cw ∈ L.map (fun cw => (cw.1, Xa k r c d :: cw.2)) ∨
      cw ∈ (L.map fun cw => (cw.1, Xb k r c d :: cw.2)).map fun cw => (Complex.I * cw.1, cw.2) := by
    simpa only [stepL, List.mem_append, or_assoc] using hcw
  rcases hmem with h | h | h
  · by_cases hcd : c = d
    · rw [if_pos hcd] at h
      obtain ⟨cw', hcw', rfl⟩ := List.mem_map.1 h
      obtain ⟨h1, h2⟩ := hL cw' hcw'
      exact ⟨h1, Nat.le_succ_of_le h2⟩
    · rw [if_neg hcd] at h
      simp at h
  · obtain ⟨cw', hcw', rfl⟩ := List.mem_map.1 h
    obtain ⟨h1, h2⟩ := hL cw' hcw'
    refine ⟨?_, by simpa using h2⟩
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact Xa_lie c d
    · exact h1 X hX
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    obtain ⟨cw', hcw', rfl⟩ := List.mem_map.1 hx
    obtain ⟨h1, h2⟩ := hL cw' hcw'
    refine ⟨?_, by simpa using h2⟩
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact Xb_lie c d
    · exact h1 X hX

/- English proof (translation)
Establish `hf' : CkOn ((j + 1 : ℕ) : ℕ∞) (O ∩ GV k r) f`. Introduce `g₀ hg₀`. Take `⟨U, f', hU, hgU, hf'', he⟩` from `hf g₀ hg₀`. Conclude with `⟨U, f', hU, hgU, hf''.of_le (WithTop.coe_le_coe.2 (by exact_mod_cast hjN)), he⟩`. Establish `hcong : ∀ Y, inLie k r Y → RdV Y (op f) g = RdV Y (wsum L f) g`.

Introduce `Y hY`. Establish `hγ` using `Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g Y 0`. Establish `hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = g` using `by simp`. Establish `hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • Y) ∈ O` using `hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hO.mem_nhds hgO)`. Use `show deriv (fun t : ℝ => op f (g * NormedSpace.exp ((t : ℂ) • Y))) 0 = deriv (fun t : ℝ => wsum L f (g * NormedSpace.exp ((t : ℂ) • Y))) 0`.

Apply `Filter.EventuallyEq.deriv_eq` to reduce the goal to its premises. Use `filter_upwards [hmem] with t ht`. Conclude with `hop f hf _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hY t)`. Establish `hder : ∀ Y, inLie k r Y → RdV Y (wsum L f) g = wsum (L.map fun cw => (cw.1, Y :: cw.2)) f g`. Introduce `Y hY`.

Establish `h` using `wsum_hasDeriv (O := O) hL hf' hY hgO hgG`. Establish `hcrv : (fun t : ℝ => wsum L f (crv (false, Y) g t)) = fun t : ℝ => wsum L f (g * NormedSpace.exp ((t : ℂ) • Y))`. Use function extensionality and compare the values at `t`. Simplify using `[crv]`. Rewrite `h` using `[hcrv]`.

Conclude with `h.deriv`. Use `show (if c = d then u • op f g else 0) + Q.EH k r c d (op f) g = wsum (stepL k r u c d L) f g`. Establish `hEH : Q.EH k r c d (op f) g = RdV (Xa k r c d) (op f) g + Complex.I • RdV (Xb k r c d) (op f) g` using `rfl`. Rewrite using `[hEH, hcong _ (Xa_lie c d), hcong _ (Xb_lie c d), hder _ (Xa_lie c d), hder _ (Xb_lie c d), hop f hf g hgO hgG]`. Simplify using `only [stepL, wsum_append, wsum_scale]`.

Use `split_ifs with hcd`. Rewrite using `[wsum_scale]`. Rewrite using `[wsum_nil]`.
-/
theorem top_rep {O : Set (Mat k r)} (hO : IsOpen O) {L : List (ℂ × List (Mat k r))} {j N : ℕ} (hL : WOK L j)
    (hjN : j + 1 ≤ N) (op : (Mat k r → E) → (Mat k r → E))
    (hop : ∀ f : Mat k r → E, CkOn (N : ℕ∞) (O ∩ GV k r) f → ∀ g ∈ O, g ∈ GV k r → op f g = wsum L f g)
    (u : ℂ) (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) (hf : CkOn (N : ℕ∞) (O ∩ GV k r) f)
    (g : Mat k r) (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    Top (Q.EH k r) u c d (op f) g = wsum (stepL k r u c d L) f g := by
  have hf' : CkOn ((j + 1 : ℕ) : ℕ∞) (O ∩ GV k r) f := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf'', he⟩ := hf g₀ hg₀
    exact ⟨U, f', hU, hgU, hf''.of_le (WithTop.coe_le_coe.2 (by exact_mod_cast hjN)), he⟩
  have hcong : ∀ Y, inLie k r Y → RdV Y (op f) g = RdV Y (wsum L f) g := by
    intro Y hY
    have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g Y 0
    have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = g := by simp
    have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • Y) ∈ O :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hO.mem_nhds hgO)
    show deriv (fun t : ℝ => op f (g * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      deriv (fun t : ℝ => wsum L f (g * NormedSpace.exp ((t : ℂ) • Y))) 0
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hmem] with t ht
    exact hop f hf _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hY t)
  have hder : ∀ Y, inLie k r Y → RdV Y (wsum L f) g = wsum (L.map fun cw => (cw.1, Y :: cw.2)) f g := by
    intro Y hY
    have h := wsum_hasDeriv (O := O) hL hf' hY hgO hgG
    have hcrv : (fun t : ℝ => wsum L f (crv (false, Y) g t)) =
        fun t : ℝ => wsum L f (g * NormedSpace.exp ((t : ℂ) • Y)) := by
      funext t
      simp [crv]
    rw [hcrv] at h
    exact h.deriv
  show (if c = d then u • op f g else 0) + Q.EH k r c d (op f) g = wsum (stepL k r u c d L) f g
  have hEH : Q.EH k r c d (op f) g =
      RdV (Xa k r c d) (op f) g + Complex.I • RdV (Xb k r c d) (op f) g := rfl
  rw [hEH, hcong _ (Xa_lie c d), hcong _ (Xb_lie c d), hder _ (Xa_lie c d), hder _ (Xb_lie c d),
    hop f hf g hgO hgG]
  simp only [stepL, wsum_append, wsum_scale]
  split_ifs with hcd
  · rw [wsum_scale]
  · rw [wsum_nil]

def foldL (k r : ℕ) (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) : List (ℂ × List (Mat k r)) :=
  ts.foldr (fun t L => stepL k r t.1 t.2.1 t.2.2 L) [(1, [])]

/- English proof (translation)
Proceed by induction on `ts with`. Consider the case `nil`. Introduce `cw hcw`. Simplify using `[foldL] at hcw`. Substitute `hcw` using the available equality.

Simplify using the standard rewrite rules. Consider the case `cons t ts ih`. Simplify `stepL_ok (u := t.1) (c := t.2.1) (d := t.2.2) ih` using `[foldL, List.foldr_cons]`.
-/
theorem foldL_ok (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) : WOK (foldL k r ts) ts.length := by
  induction ts with
  | nil =>
    intro cw hcw
    simp [foldL] at hcw
    subst hcw
    simp
  | cons t ts ih =>
    simpa [foldL, List.foldr_cons] using stepL_ok (u := t.1) (c := t.2.1) (d := t.2.2) ih

/- English proof (translation)
Proceed by induction on `ts with`. Consider the case `nil`. Introduce `N _ f _ g _ _`. Simplify using `[foldL, wsum, Rw]`. Consider the case `cons t ts ih`.

Introduce `N hN f hf g hgO hgG`. Establish `hN' : ts.length ≤ N` using `le_trans (Nat.le_succ _) hN`. Establish `key` using `top_rep hO (foldL_ok (k := k) (r := r) ts) (by simpa using hN) (fun f => (ts.map fun t => Top (Q.EH k r) t.1 t.2.1 t.2.2).foldr (fun T h => T h) f) (fun f hf g hgO hgG => ih hN' f hf g hgO hgG) t.1 t.2.1 t.2.2 f hf g hgO hgG`. Conclude with `key`.
-/
theorem fold_rep {O : Set (Mat k r)} (hO : IsOpen O) (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ {N : ℕ}, ts.length ≤ N → ∀ f : Mat k r → E, CkOn (N : ℕ∞) (O ∩ GV k r) f → ∀ g ∈ O, g ∈ GV k r →
      (ts.map fun t => Top (Q.EH k r) t.1 t.2.1 t.2.2).foldr (fun T h => T h) f g = wsum (foldL k r ts) f g := by
  induction ts with
  | nil =>
    intro N _ f _ g _ _
    simp [foldL, wsum, Rw]
  | cons t ts ih =>
    intro N hN f hf g hgO hgG
    have hN' : ts.length ≤ N := le_trans (Nat.le_succ _) hN
    have key := top_rep hO (foldL_ok (k := k) (r := r) ts) (by simpa using hN)
      (fun f => (ts.map fun t => Top (Q.EH k r) t.1 t.2.1 t.2.2).foldr (fun T h => T h) f)
      (fun f hf g hgO hgG => ih hN' f hf g hgO hgG) t.1 t.2.1 t.2.2 f hf g hgO hgG
    exact key

def tsOf {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (σ : Equiv.Perm (Fin t)) :
    List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
  List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), p (σ j), q j)

def qmL (k r : ℕ) {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) : List (ℂ × List (Mat k r)) :=
  (Finset.univ.toList : List (Equiv.Perm (Fin t))).flatMap fun σ =>
    (foldL k r (tsOf p q u σ)).map fun cw => ((((Equiv.Perm.sign σ : ℤ) : ℂ)) * cw.1, cw.2)

/- English proof (translation)
Introduce `cw hcw`. Simplify using `only [qmL, List.mem_flatMap, List.mem_map] at hcw`. Take `⟨σ, -, cw', hcw', rfl⟩` from `hcw`. Take `⟨h1, h2⟩` from `foldL_ok (k := k) (r := r) (tsOf p q u σ) cw' hcw'`. Conclude with `⟨h1, by simpa [tsOf] using h2⟩`.
-/
theorem qmL_ok {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) : WOK (qmL k r p q u) t := by
  intro cw hcw
  simp only [qmL, List.mem_flatMap, List.mem_map] at hcw
  obtain ⟨σ, -, cw', hcw', rfl⟩ := hcw
  obtain ⟨h1, h2⟩ := foldL_ok (k := k) (r := r) (tsOf p q u σ) cw' hcw'
  exact ⟨h1, by simpa [tsOf] using h2⟩

/- English proof (translation)
Establish `hfold : ∀ σ : Equiv.Perm (Fin t), (List.ofFn fun j : Fin t => Top (Q.EH k r) (u - ((j : ℕ) : ℂ)) (p (σ j)) (q j)).foldr (fun T h => T h) f g = wsum (foldL k r (tsOf p q u σ)) f g`. Introduce `σ`. Use `fold_rep hO (tsOf p q u σ) (N := t) (by simp [tsOf]) f hf g hgO hgG` as an intermediate fact. Simplify `this` using `[tsOf, List.map_ofFn, Function.comp_def]`. Simplify using `only [qminorOp, Finset.sum_apply, Pi.smul_apply, hfold, qmL, wsum_flatMap, wsum_scale, Finset.sum_toList]`.

Use `first`. Consider the case `exact (Finset.sum_toList _ _).symm`. Consider the case `exact (Finset.sum_map_toList _ _).symm`. Consider the case `simp [Finset.sum_toList]`.
-/
theorem qminor_rep {O : Set (Mat k r)} (hO : IsOpen O) {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (hf : CkOn (t : ℕ∞) (O ∩ GV k r) f) (g : Mat k r) (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    qminorOp (Q.EH k r) p q u f g = wsum (qmL k r p q u) f g := by
  have hfold : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun j : Fin t => Top (Q.EH k r) (u - ((j : ℕ) : ℂ)) (p (σ j)) (q j)).foldr (fun T h => T h) f g =
        wsum (foldL k r (tsOf p q u σ)) f g := by
    intro σ
    have := fold_rep hO (tsOf p q u σ) (N := t) (by simp [tsOf]) f hf g hgO hgG
    simpa [tsOf, List.map_ofFn, Function.comp_def] using this
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply, hfold, qmL, wsum_flatMap, wsum_scale, Finset.sum_toList]
  first
  | exact (Finset.sum_toList _ _).symm
  | exact (Finset.sum_map_toList _ _).symm
  | simp [Finset.sum_toList]

def unitL (L : List (ℂ × List (Mat k r))) : List (ℂ × List (Mat k r)) :=
  L.map fun cw => ((((cw.2.map nz).prod : ℝ) : ℂ) * cw.1, cw.2.map nrm)

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp [unitL, wsum]`. Consider the case `cons cw L ih`. Simplify using `only [unitL, List.map_cons] at ih ⊢`. Rewrite using `[wsum_cons, wsum_cons, ih, Rw_scale cw.2 f, mul_smul, smul_comm]`.
-/
theorem wsum_unitL (L : List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (unitL L) f g = wsum L f g := by
  induction L with
  | nil => simp [unitL, wsum]
  | cons cw L ih =>
    simp only [unitL, List.map_cons] at ih ⊢
    rw [wsum_cons, wsum_cons, ih, Rw_scale cw.2 f, mul_smul, smul_comm]

/- English proof (translation)
Introduce `cw hcw`. Simplify using `only [unitL, List.mem_map] at hcw`. Take `⟨cw', hcw', rfl⟩` from `hcw`. Take `⟨h1, h2⟩` from `hL cw' hcw'`. Use `⟨?_, by simpa using h2⟩` and prove the remaining obligations.

Introduce `X hX`. Simplify using `only [List.mem_map] at hX`. Take `⟨Y, hY, rfl⟩` from `hX`. Conclude with `nrm_unit (h1 Y hY)`.
-/
theorem unitL_ok {L : List (ℂ × List (Mat k r))} {j : ℕ} (hL : WOK L j) :
    ∀ cw ∈ unitL L, (∀ X ∈ cw.2, unitLie k r X) ∧ cw.2.length ≤ j := by
  intro cw hcw
  simp only [unitL, List.mem_map] at hcw
  obtain ⟨cw', hcw', rfl⟩ := hcw
  obtain ⟨h1, h2⟩ := hL cw' hcw'
  refine ⟨?_, by simpa using h2⟩
  intro X hX
  simp only [List.mem_map] at hX
  obtain ⟨Y, hY, rfl⟩ := hX
  exact nrm_unit (h1 Y hY)

end WS

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mdim0 : Q.mdim k r 0 = 2 * r + k + 1 := by
  rfl

/- English proof (translation)
Introduce `k r Y`. Use `⟨unitL (qmL k r (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y)), ?_, ?_⟩` and prove the remaining obligations. Introduce `cw hcw`. Use `unitL_ok (qmL_ok (k := k) (r := r) (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y)) cw hcw` as an intermediate fact. Conclude with `⟨this.1, this.2.trans (le_of_eq mdim0)⟩`.

Introduce `E _ _ UU f hf g hgU hgG`. Take `⟨U, f', hU, hgU', hc, hff⟩` from `hf g hgU`. Establish `hf2 : CkOn ((Q.mdim k r 0 : ℕ) : ℕ∞) (U ∩ GV k r) f`. Introduce `g₁ hg₁`. Conclude with `⟨U, f', hU, hg₁.1, by rw [mdim0]; exact hc, hff⟩`.

Use `qminor_rep hU (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f hf2 g hgU' hgG` as an intermediate fact. Use `show qminorOp (Q.EH k r) (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f g = _`. Rewrite using `[this, ← wsum_unitL]`. Both sides reduce to the same expression.
-/
theorem cvWordSum : JF.CVWordSum := by
  intro k r Y
  refine ⟨unitL (qmL k r (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y)), ?_, ?_⟩
  · intro cw hcw
    have := unitL_ok (qmL_ok (k := k) (r := r) (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y)) cw hcw
    exact ⟨this.1, this.2.trans (le_of_eq mdim0)⟩
  · intro E _ _ UU f hf g hgU hgG
    obtain ⟨U, f', hU, hgU', hc, hff⟩ := hf g hgU
    have hf2 : CkOn ((Q.mdim k r 0 : ℕ) : ℕ∞) (U ∩ GV k r) f := by
      intro g₁ hg₁
      exact ⟨U, f', hU, hg₁.1, by rw [mdim0]; exact hc, hff⟩
    have := qminor_rep hU (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f hf2 g hgU' hgG
    show qminorOp (Q.EH k r) (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f g = _
    rw [this, ← wsum_unitL]
    rfl

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons i l ih`. Establish `hi : Integrable (φ i) μ` using `h i (by simp)`. Take `⟨hl1, hl2⟩` from `ih (fun j hj => h j (by simp [hj]))`.

Establish `hadd` using `integral_add (hi.smul (c i)) hl1`. Simplify using `only [Pi.smul_apply] at hadd`. Simplify using `only [List.map_cons, List.sum_cons]`. Use `⟨(hi.smul (c i)).add hl1, ?_⟩` and prove the remaining obligations. Rewrite using `[hadd, integral_smul, hl2]`.
-/
theorem integral_list_smul {α V : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] {ι : Type*} (l : List ι) (c : ι → ℂ) (φ : ι → α → V)
    (h : ∀ i ∈ l, Integrable (φ i) μ) :
    Integrable (fun p => (l.map fun i => c i • φ i p).sum) μ ∧
      (∫ p, (l.map fun i => c i • φ i p).sum ∂μ) = (l.map fun i => c i • ∫ p, φ i p ∂μ).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : Integrable (φ i) μ := h i (by simp)
    obtain ⟨hl1, hl2⟩ := ih (fun j hj => h j (by simp [hj]))
    have hadd := integral_add (hi.smul (c i)) hl1
    simp only [Pi.smul_apply] at hadd
    simp only [List.map_cons, List.sum_cons]
    refine ⟨(hi.smul (c i)).add hl1, ?_⟩
    rw [hadd, integral_smul, hl2]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons i l ih => simp [smul_add, ih, smul_comm a (c i)]`.
-/
theorem list_smul_sum {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} (a : ℂ) (l : List ι)
    (c : ι → ℂ) (φ : ι → V) :
    a • (l.map fun i => c i • φ i).sum = (l.map fun i => c i • (a • φ i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [smul_add, ih, smul_comm a (c i)]

/- English proof (translation)
Conclude with `⟨hg, fun a ha => by simp at ha⟩`.
-/
theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 := by
  exact ⟨hg, fun a ha => by simp at ha⟩

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D A m F Y hnm hThr hCC g hg`. Take `⟨hCk, hJW⟩` from `hJ k r Wp Wq D A m F hThr hCC`. Take `⟨L, hLw, hL⟩` from `hW k r Y`. Establish `hgG : g ∈ GV k r` using `hg.1`. Take `⟨c0, hc0⟩` from `hCC`.

Establish `hFm : CkOn ((m : ℕ) : ℕ∞) (GV k r) F` using `hc0.1`. Establish `hFn : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) F` using `sCkOn_mono (by exact_mod_cast hnm) hFm`. Establish `hJck : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (JF.Om k r D.z D.z') (B.JF D F)`. Introduce `g₀ hg₀`. Take `⟨U, F', hU, hg₀U, hc, hff⟩` from `hCk g₀ ⟨glev0 hg₀.1, hg₀.2⟩`.

Use `⟨U, F', hU, hg₀U, hc.of_le ?_, fun g hgU hgG => hff g hgU (glev0 hgG)⟩` and prove the remaining obligations. Conclude with `hnm` after adjusting the coercions. Establish `hcw : ∀ cw ∈ L, Integrable (fun p => JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g) D.μSS ∧ Rw cw.2 (B.JF D F) g = ∫ p, JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g ∂D.μSS`. Introduce `cw hcw`. Use `hJW [] cw.2 (by simp) (hLw cw hcw).1 (by simpa using (hLw cw hcw).2.trans hnm) g hg` as an intermediate fact.

Simplify `this` using `[B.dLR]`. Rewrite using `[hL _ _ _ hJck g hg hgG]`. Establish `e1 : (L.map fun cw => cw.1 • Rw cw.2 (B.JF D F) g).sum = (L.map fun cw => cw.1 • ∫ p, JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g ∂D.μSS).sum`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises.

Introduce `cw h`. Rewrite using `[(hcw cw h).2]`. Rewrite using `[e1, ← (integral_list_smul L (fun cw => cw.1) (fun cw p => JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g) (fun cw h => (hcw cw h).1)).2]`. Apply `integral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp`.

Establish `hrho : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) (B.rho D p F)` using `Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hFn`. Rewrite using `[hL _ (GV k r) _ hrho g hgG hgG, list_smul_sum]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `cw h`.

Establish `this : Rw cw.2 (B.rho D p F) g = B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g` using `hR k r Wp Wq D m F p hp hFm [] cw.2 (by simp) (fun X hX => ((hLw cw h).1 X hX).1) (by simpa using (hLw cw h).2.trans hnm) g hgG`. Rewrite using `[this]`.
-/
theorem cvUnderInt_of (hJ : JF.JWords) (hW : JF.CVWordSum) (hR : JF.RwRho) : JF.CVUnderInt := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F Y hnm hThr hCC g hg
  obtain ⟨hCk, hJW⟩ := hJ k r Wp Wq D A m F hThr hCC
  obtain ⟨L, hLw, hL⟩ := hW k r Y
  have hgG : g ∈ GV k r := hg.1
  obtain ⟨c0, hc0⟩ := hCC
  have hFm : CkOn ((m : ℕ) : ℕ∞) (GV k r) F := hc0.1
  have hFn : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) F := sCkOn_mono (by exact_mod_cast hnm) hFm
  have hJck : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (JF.Om k r D.z D.z') (B.JF D F) := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hg₀U, hc, hff⟩ := hCk g₀ ⟨glev0 hg₀.1, hg₀.2⟩
    refine ⟨U, F', hU, hg₀U, hc.of_le ?_, fun g hgU hgG => hff g hgU (glev0 hgG)⟩
    exact_mod_cast hnm
  have hcw : ∀ cw ∈ L,
      Integrable (fun p => JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g) D.μSS ∧
        Rw cw.2 (B.JF D F) g = ∫ p, JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g ∂D.μSS := by
    intro cw hcw
    have := hJW [] cw.2 (by simp) (hLw cw hcw).1 (by simpa using (hLw cw hcw).2.trans hnm) g hg
    simpa [B.dLR] using this
  rw [hL _ _ _ hJck g hg hgG]
  have e1 : (L.map fun cw => cw.1 • Rw cw.2 (B.JF D F) g).sum =
      (L.map fun cw => cw.1 • ∫ p, JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g ∂D.μSS).sum := by
    congr 1
    apply List.map_congr_left
    intro cw h
    rw [(hcw cw h).2]
  rw [e1, ← (integral_list_smul L (fun cw => cw.1)
    (fun cw p => JF.xiP D p • B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g) (fun cw h => (hcw cw h).1)).2]
  apply integral_congr_ae
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  have hrho : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) (B.rho D p F) := Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hFn
  rw [hL _ (GV k r) _ hrho g hgG hgG, list_smul_sum]
  congr 1
  apply List.map_congr_left
  intro cw h
  have this : Rw cw.2 (B.rho D p F) g = B.rho D p (Rw (cw.2.map (JF.AdR p)) F) g :=
    hR k r Wp Wq D m F p hp hFm [] cw.2 (by simp) (fun X hX => ((hLw cw h).1 X hX).1)
      (by simpa using (hLw cw h).2.trans hnm) g hgG
  rw [this]

end Formalism.FourierDecayAlt.P.JFxB

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.JFxB.cvLeft`.
-/
theorem Formalism.FourierDecayAlt.P.capelli_left_translation : Formalism.FourierDecayAlt.JF.CVLeft := Formalism.FourierDecayAlt.P.JFxB.cvLeft

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.JFxB.cvPost`.
-/
theorem Formalism.FourierDecayAlt.P.capelli_post_composition : Formalism.FourierDecayAlt.JF.CVPost := Formalism.FourierDecayAlt.P.JFxB.cvPost

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.JFxB.cvRhoOfParts`.
-/
theorem Formalism.FourierDecayAlt.P.capelli_rho_of_parts : Formalism.FourierDecayAlt.JF.CVRhoOfParts := Formalism.FourierDecayAlt.P.JFxB.cvRhoOfParts

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.JFxB.cvWordSum`.
-/
theorem Formalism.FourierDecayAlt.P.JFxB.jf_cVWordSum_alt : Formalism.FourierDecayAlt.JF.CVWordSum := Formalism.FourierDecayAlt.P.JFxB.cvWordSum

/- English proof (translation)
Introduce `hJ hW hR`. Conclude with `Formalism.FourierDecayAlt.P.JFxB.cvUnderInt_of hJ hW hR`.
-/
theorem Formalism.FourierDecayAlt.P.JFxB.jf_cVUnderIntOfParts_alt : Formalism.FourierDecayAlt.JF.CVUnderIntOfParts := by
  intro hJ hW hR
  exact Formalism.FourierDecayAlt.P.JFxB.cvUnderInt_of hJ hW hR

/- English proof (translation)
Introduce `hJ hR` and use `Formalism.FourierDecayAlt.P.JFxB.cvUnderInt_of hJ Formalism.FourierDecayAlt.P.JFxB.cvWordSum hR`.
-/
theorem Formalism.FourierDecayAlt.P.jf_cVUnderInt_of : Formalism.FourierDecayAlt.JF.JWords → Formalism.FourierDecayAlt.JF.RwRho → Formalism.FourierDecayAlt.JF.CVUnderInt :=
  fun hJ hR => Formalism.FourierDecayAlt.P.JFxB.cvUnderInt_of hJ Formalism.FourierDecayAlt.P.JFxB.cvWordSum hR

/- English proof (translation)
Introduce `hA` and use `Formalism.FourierDecayAlt.P.JFxB.cvRight_of hA`.
-/
theorem Formalism.FourierDecayAlt.P.jf_cVRight_of : Formalism.FourierDecayAlt.P.JFxB.CapAdInv → Formalism.FourierDecayAlt.JF.CVRight :=
  fun hA => Formalism.FourierDecayAlt.P.JFxB.cvRight_of hA

/- English proof (translation)
Introduce `hA` and use `Formalism.FourierDecayAlt.P.JFxB.cvRho_of hA`.
-/
theorem Formalism.FourierDecayAlt.P.jf_cVRho_of : Formalism.FourierDecayAlt.P.JFxB.CapAdInv → Formalism.FourierDecayAlt.JF.CVRho :=
  fun hA => Formalism.FourierDecayAlt.P.JFxB.cvRho_of hA
