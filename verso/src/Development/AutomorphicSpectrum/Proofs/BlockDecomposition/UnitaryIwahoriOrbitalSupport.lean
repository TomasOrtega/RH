import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitone
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.DiagCoset

/- English proof (translation)
Establish `h0 : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Unfold `ordL`. Rewrite using `[dif_neg h0]`. Simplify using the standard rewrite rules.
-/
theorem v_eq_of_ne {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dif_neg h0]
  simp

/- English proof (translation)
Establish `hinv : ∀ i, Valued.v ((τ⁻¹) i : w.adicCompletion E) = 1`. Introduce `i`. Establish `: (((τ⁻¹) i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = (τ i : w.adicCompletion E)⁻¹`. Simplify using the standard rewrite rules. Rewrite using `[this, map_inv₀, hτ, inv_one]`.

Establish `hle : ∀ (ρ : Fin n → (w.adicCompletion E)ˣ), (∀ i, Valued.v (ρ i : w.adicCompletion E) = 1) → ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) ρ).val i j) ≤ 1`. Introduce `ρ hρ i j`. Rewrite using `[GlobalTheory.SmGL.val_diagT]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq, hρ]`. Rewrite using `[Matrix.diagonal_apply_ne _ h, map_zero]`. Conclude with `zero_le'`. Use `((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1).2 ⟨hle τ hτ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`.

Conclude with `hle _ hinv`. Introduce `i j hij`. Rewrite using `[GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]`. Conclude with `zero_lt_one`.
-/
theorem diagT_mem_iwGL {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ)
    (τ : Fin n → (w.adicCompletion E)ˣ) (hτ : ∀ i, Valued.v (τ i : w.adicCompletion E) = 1) :
    GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ ∈ iwGL n w := by
  have hinv : ∀ i, Valued.v ((τ⁻¹) i : w.adicCompletion E) = 1 := by
    intro i
    have : (((τ⁻¹) i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = (τ i : w.adicCompletion E)⁻¹ := by
      simp
    rw [this, map_inv₀, hτ, inv_one]
  have hle : ∀ (ρ : Fin n → (w.adicCompletion E)ˣ), (∀ i, Valued.v (ρ i : w.adicCompletion E) = 1) →
      ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) ρ).val i j) ≤ 1 := by
    intro ρ hρ i j
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, hρ]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]
      exact zero_le'
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1).2 ⟨hle τ hτ, ?_, ?_⟩
  · rw [← map_inv]
    exact hle _ hinv
  · intro i j hij
    rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]
    exact zero_lt_one

/- English proof (translation)
Introduce `E _ _ _ hU w hw n b hb ϖ hϖ l hl γ u hu hγ x hx z hz`. Take `⟨hUL, hiw, -, hdiag⟩` from `GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb`. Establish `hrev` using `(GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).2`. Use `set τ : Fin n → (w.adicCompletion E)ˣ := fun i => u i * (ϖ ^ wexp n l i)⁻¹ with hτdef`. Establish `hvϖ : Valued.v (ϖ : w.adicCompletion E) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`.

Rewrite using `[v_eq_of_ne ϖ.ne_zero, hϖ.1]`. Establish `hvpow : ∀ d : ℤ, Valued.v (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = ((Multiplicative.ofAdd (-d) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Introduce `d`. Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀, hvϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul]`. Simplify using the standard rewrite rules.

Establish `hτ : ∀ i, Valued.v (τ i : w.adicCompletion E) = 1`. Introduce `i`. Establish `e : ((τ i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = (u i : w.adicCompletion E) * (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹`. Simplify using `[hτdef]`. Rewrite using `[e, map_mul, map_inv₀, hvpow, v_eq_of_ne (u i).ne_zero, hu i]`.

Conclude with `mul_inv_cancel₀ WithZero.coe_ne_zero`. Establish `hfac : GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u = tdiag ϖ (wexp n l) * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ`. Rewrite using `[tdiag, ← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[hτdef]`. Establish `hu1 : ∀ i, cj w (u i : w.adicCompletion E) * (u (Fin.rev i) : w.adicCompletion E) = 1`. Establish `h1 : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∈ UL n w` using `hγ ▸ γ.2`. Conclude with `(hdiag u).1 ((hUL _).1 h1)`. Establish `hcjϖ : ∀ d : ℤ, cj w (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = ((ϖ ^ d : (w.adicCompletion E)ˣ) : w.adicCompletion E)`.

Introduce `d`. Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ.2]`. Establish `hτ1 : ∀ i, cj w (τ i : w.adicCompletion E) * (τ (Fin.rev i) : w.adicCompletion E) = 1`. Introduce `i`. Establish `e : ∀ j, ((τ j : (w.adicCompletion E)ˣ) : w.adicCompletion E) = (u j : w.adicCompletion E) * (((ϖ ^ wexp n l j : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹`.

Introduce `j`. Simplify using `[hτdef]`. Rewrite using `[e, e, map_mul, map_inv₀, hcjϖ, hrev i, _root_.zpow_neg]`. Establish `h2` using `hu1 i`. Establish `hp : (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E) ≠ 0` using `Units.ne_zero _`.

Simplify using `only [Units.val_inv_eq_inv_val, inv_inv]`. Combine the equalities or inequalities in the displayed calculation. Establish `hκU : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹ ∈ UL n w` using `(hUL _).2 ((hdiag τ).2 hτ1)`. Set `κ : UL n w` to `⟨_, hκU⟩`. Establish `hκ : κ ∈ iwU n w b`.

Rewrite using `[hiw]`. Establish `: b⁻¹ * κ.1 * b = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ`. Express the relevant statement in the definitionally equal form `b⁻¹ * (b * _ * b⁻¹) * b = _`. Use `group`. Rewrite using `[this]`.

Conclude with `diagT_mem_iwGL w n τ hτ`. Unfold `fU`. Use `if_pos ⟨x, hx, κ * z, mul_mem hκ hz, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x.1 * γ.1 * z.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * ((b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹) * z.1)`. Rewrite using `[hγ, hfac]`.

Use `group`.
-/
theorem fU_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → ∀ (γ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) → γ.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ → ∀ x ∈ iwU n w b, ∀ z ∈ iwU n w b, fU n w b ϖ l (x * γ * z) = 1 := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl γ u hu hγ x hx z hz
  obtain ⟨hUL, hiw, -, hdiag⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hrev := (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).2

  set τ : Fin n → (w.adicCompletion E)ˣ := fun i => u i * (ϖ ^ wexp n l i)⁻¹ with hτdef
  have hvϖ : Valued.v (ϖ : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [v_eq_of_ne ϖ.ne_zero, hϖ.1]
  have hvpow : ∀ d : ℤ, Valued.v (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-d) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro d
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hvϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul]
    simp
  have hτ : ∀ i, Valued.v (τ i : w.adicCompletion E) = 1 := by
    intro i
    have e : ((τ i : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (u i : w.adicCompletion E) * (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ := by
      simp [hτdef]
    rw [e, map_mul, map_inv₀, hvpow, v_eq_of_ne (u i).ne_zero, hu i]
    exact mul_inv_cancel₀ WithZero.coe_ne_zero
  have hfac : GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u =
      tdiag ϖ (wexp n l) * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ := by
    rw [tdiag, ← map_mul]
    congr 1
    funext i
    simp [hτdef]

  have hu1 : ∀ i, cj w (u i : w.adicCompletion E) * (u (Fin.rev i) : w.adicCompletion E) = 1 := by
    have h1 : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∈ UL n w := hγ ▸ γ.2
    exact (hdiag u).1 ((hUL _).1 h1)
  have hcjϖ : ∀ d : ℤ, cj w (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) =
      ((ϖ ^ d : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    intro d
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ.2]
  have hτ1 : ∀ i, cj w (τ i : w.adicCompletion E) * (τ (Fin.rev i) : w.adicCompletion E) = 1 := by
    intro i
    have e : ∀ j, ((τ j : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (u j : w.adicCompletion E) * (((ϖ ^ wexp n l j : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ := by
      intro j
      simp [hτdef]
    rw [e, e, map_mul, map_inv₀, hcjϖ, hrev i, _root_.zpow_neg]
    have h2 := hu1 i
    have hp : (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E) ≠ 0 := Units.ne_zero _
    simp only [Units.val_inv_eq_inv_val, inv_inv]
    calc _ = (cj w (u i : w.adicCompletion E) * (u (Fin.rev i) : w.adicCompletion E)) *
          ((((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ *
            (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)) := by ring
      _ = 1 := by rw [h2, inv_mul_cancel₀ hp, one_mul]
  have hκU : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹ ∈ UL n w :=
    (hUL _).2 ((hdiag τ).2 hτ1)
  let κ : UL n w := ⟨_, hκU⟩
  have hκ : κ ∈ iwU n w b := by
    rw [hiw]
    have : b⁻¹ * κ.1 * b = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ := by
      change b⁻¹ * (b * _ * b⁻¹) * b = _
      group
    rw [this]
    exact diagT_mem_iwGL w n τ hτ
  unfold fU
  refine if_pos ⟨x, hx, κ * z, mul_mem hκ hz, ?_⟩
  change x.1 * γ.1 * z.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * ((b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹) * z.1)
  rw [hγ, hfac]
  group

end GlobalTheory.CompanionTheory.DiagCoset
