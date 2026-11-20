import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PoincareAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Take `⟨n, hn, hpow⟩` from `X.χ_fin la`. Establish `h` using `congrArg norm (hpow γ hγ)`. Rewrite `h` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h`.
-/
theorem norm_chi {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := X.χ_fin la
  have h := congrArg norm (hpow γ hγ)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show (mat (lact γ x) τ * mat (nmat X z) τ : Matrix (Fin r) (Fin r) ℂ) = ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x z) τ : Matrix (Fin r) (Fin r) ℂ)`. Simplify using `only [mat, lact, cpt, rmul]`. Conclude with `Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (x τ)) (Matrix.of (nmat X z τ))`.
-/
theorem cpt_lact {r : ℕ} (X : Data E r) (γ : GL (Fin r) E) (x : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ x) z = lact γ (cpt X x z) := by
  funext τ
  show (mat (lact γ x) τ * mat (nmat X z) τ : Matrix (Fin r) (Fin r) ℂ) =
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x z) τ : Matrix (Fin r) (Fin r) ℂ)
  simp only [mat, lact, cpt, rmul]
  exact Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (x τ))
    (Matrix.of (nmat X z τ))

/- English proof (translation)
Introduce `τ`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Establish `e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ` using `rfl`. Establish `h` using `(hx τ).1`. Rewrite `h` using `[e1, Matrix.det_mul]`.

Conclude with `right_ne_zero_of_mul h`. Use `(hx τ).2 i` as an intermediate fact. Unfold `dmin at this ⊢`. Rewrite `this` using `[OntoS.gram_lact X hγ]`. Then use the resulting hypothesis.
-/
theorem dom_of_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : lact γ x ∈ X.dom) : x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    have h := (hx τ).1
    rw [e1, Matrix.det_mul] at h
    exact right_ne_zero_of_mul h
  · have := (hx τ).2 i
    unfold dmin at this ⊢
    rwa [OntoS.gram_lact X hγ] at this

/- English proof (translation)
Introduce `τ` and use `by rw [OntoS.gram_lact X hγ, hx τ]`.
-/
theorem isOrth_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : IsOrth X (lact γ x) := fun τ => by
  rw [OntoS.gram_lact X hγ, hx τ]

/- English proof (translation)
Unfold `phla Data.nfac dmin`. Simplify using `only [OntoS.gram_lact X hγ]`.
-/
theorem phla_lact {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (x : Frame X.Ψ r) : phla X la (lact γ x) = phla X la x := by
  unfold phla Data.nfac dmin
  simp only [OntoS.gram_lact X hγ]

/- English proof (translation)
Unfold `poin`. Rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Establish `h1 : X.χ la' γ.1 ≠ 0`. Rewrite using `[← norm_ne_zero_iff, norm_chi X la' γ.2]`.

Conclude with `one_ne_zero`. Establish `h2 : X.χ la γ.1 ≠ 0`. Rewrite using `[← norm_ne_zero_iff, norm_chi X la γ.2]`. Conclude with `one_ne_zero`. Simplify using `only [X.χ_add la la' γ.1 γ.2, hg.2.2 γ.1 γ.2 x hx]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem poin_mul {r : ℕ} (X : Data E r) (la la' : Wt X.Ψ r) (P g : Frame X.Ψ r → ℂ)
    (hg : X.IsSec la' g) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  have h1 : X.χ la' γ.1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_chi X la' γ.2]; exact one_ne_zero
  have h2 : X.χ la γ.1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_chi X la γ.2]; exact one_ne_zero
  simp only [X.χ_add la la' γ.1 γ.2, hg.2.2 γ.1 γ.2 x hx]
  field_simp

/- English proof (translation)
Introduce `hκ hball hloc hbdd hFF r X x0 ho hPD la W bb hW hWl hbb F P _ hF hP hPF`. Take `⟨κ, hκ⟩` from `hκ r X x0 ho hPD bb hbb`. Take `⟨hs, hb⟩` from `hbdd r X la κ P hP hκ.2.2.2.2.1 (hloc r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF)`. Use `⟨hs, hb, hFF r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF hs, fun ρ hρ hρ1 => ?_, fun la' g hg x hx => poin_mul X la la' P g hg hx⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `hball r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF ρ hρ hρ1`.

Take `⟨K, hK, hKs⟩` from `hκ.2.2.2.2.1`. Use `⟨C * K.toReal, fun x hx hxo => ?_⟩` and prove the remaining obligations. Use `set S : ℝ≥0∞ := ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom), (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ) with hS`. Establish `hterm : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ ≤ ENNReal.ofReal C * S * ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x)))`. Introduce `γ`.

Rewrite using `[← ofReal_norm, norm_mul, norm_inv, norm_chi X la γ.2, inv_one, one_mul]`. Use `(hC _ (isOrth_lact X γ.2 hxo)).trans ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_mul' (Real.sqrt_nonneg _), mul_right_comm]`. Use `gcongr`. Use `iSup_le fun z => iSup_le fun hz => iSup_le fun hd => ?_` and prove the remaining obligations.

Rewrite `hd`, the goal using `[cpt_lact]`. Establish `hd'` using `dom_of_lact X γ.2 hd`. Rewrite using `[phla_lact X la γ.2, hW.2.2 γ.1 γ.2 _ hd']`. Conclude with `le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le hd' le_rfl))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[ENNReal.tsum_mul_left]`. Use `gcongr`. Conclude with `hKs x hx`. Use `_ = ENNReal.ofReal (C * K.toReal) * S := by`. Rewrite using `[ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK.ne, mul_right_comm]`.
-/
theorem poinStatement_of :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x, IsOrth X x → ENNReal.ofReal ‖P x‖ ≤ ENNReal.ofReal (C * Real.sqrt (κ x)) * ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom), (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ‖P (cpt X x z)‖ ≤ C * Real.sqrt (κ x)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (κ : Frame X.Ψ r → ℝ) (P : Frame X.Ψ r → ℂ), IsBEq X la P → (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) → (∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ‖P (cpt X x z)‖ ≤ C * Real.sqrt (κ x)) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) ∧ X.IsBddSec la (poin X la P)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) → ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) → (PoinStatement (E := E)) := by
  intro hκ hball hloc hbdd hFF r X x0 ho hPD la W bb hW hWl hbb F P _ hF hP hPF
  obtain ⟨κ, hκ⟩ := hκ r X x0 ho hPD bb hbb
  obtain ⟨hs, hb⟩ := hbdd r X la κ P hP hκ.2.2.2.2.1
    (hloc r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF)
  refine ⟨hs, hb, hFF r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF hs, fun ρ hρ hρ1 => ?_,
    fun la' g hg x hx => poin_mul X la la' P g hg hx⟩
  obtain ⟨C, hC⟩ := hball r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF ρ hρ hρ1
  obtain ⟨K, hK, hKs⟩ := hκ.2.2.2.2.1
  refine ⟨C * K.toReal, fun x hx hxo => ?_⟩
  set S : ℝ≥0∞ := ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
    (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ) with hS
  have hterm : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ ≤
      ENNReal.ofReal C * S * ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) := by
    intro γ
    rw [← ofReal_norm, norm_mul, norm_inv, norm_chi X la γ.2, inv_one, one_mul]
    refine (hC _ (isOrth_lact X γ.2 hxo)).trans ?_
    rw [ENNReal.ofReal_mul' (Real.sqrt_nonneg _), mul_right_comm]
    gcongr
    refine iSup_le fun z => iSup_le fun hz => iSup_le fun hd => ?_
    rw [cpt_lact] at hd ⊢
    have hd' := dom_of_lact X γ.2 hd
    rw [phla_lact X la γ.2, hW.2.2 γ.1 γ.2 _ hd']
    exact le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le hd' le_rfl))
  calc ENNReal.ofReal ‖poin X la P x‖
      = ‖∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ := ofReal_norm _
    _ ≤ ∑' γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ := enorm_tsum_le_tsum_enorm
    _ ≤ ∑' γ : X.Γ, ENNReal.ofReal C * S * ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) :=
        ENNReal.tsum_le_tsum hterm
    _ ≤ ENNReal.ofReal C * S * K := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact hKs x hx
    _ = ENNReal.ofReal (C * K.toReal) * S := by
        rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK.ne, mul_right_comm]

end GlobalTheory.PoincareAssembly
