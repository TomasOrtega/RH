import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneUnitHilbertNinetyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitone
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.UnitaryContraction

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Establish `h0 : Valued.v (x : L) ≠ 0` using `(Valuation.ne_zero_iff _).2 x.ne_zero`. Take `⟨a, ha⟩` from `WithZero.ne_zero_iff_exists.1 h0`. Establish `hk : Valued.v ((x ^ k : Lˣ) : L) = ((a ^ k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, WithZero.coe_zpow]`. Rewrite using `[UnitaryCorrection.ordL_of_eq hk, UnitaryCorrection.ordL_of_eq ha.symm, toAdd_zpow]`.

Simplify using the standard rewrite rules.
-/
theorem ordL_zpow (x : Lˣ) (k : ℤ) : ordL ((x ^ k : Lˣ) : L) = k * ordL (x : L) := by
  have h0 : Valued.v (x : L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 h0
  have hk : Valued.v ((x ^ k : Lˣ) : L) = ((a ^ k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, WithZero.coe_zpow]
  rw [UnitaryCorrection.ordL_of_eq hk, UnitaryCorrection.ordL_of_eq ha.symm, toAdd_zpow]
  simp

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hle : ∀ t : Fin n → (w.adicCompletion E)ˣ, (∀ i, Valued.v (t i : w.adicCompletion E) = 1) → ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) t).val i j) ≤ 1`. Introduce `t ht i j`. Rewrite using `[GlobalTheory.SmGL.val_diagT]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq, ht]`. Rewrite using `[Matrix.diagonal_apply_ne _ h, map_zero]`. Conclude with `zero_le_one`. Rewrite using `[(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1]`. Use `⟨hle s hs, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_inv]`. Use `hle _ fun i => ?_` and prove the remaining obligations. Rewrite using `[Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hs, inv_one]`. Introduce `i j hij`. Rewrite using `[GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]`.

Conclude with `zero_lt_one`.
-/
theorem diagT_mem_iwGL (w : Pl E) (n : ℕ) (s : Fin n → (w.adicCompletion E)ˣ)
    (hs : ∀ i, Valued.v (s i : w.adicCompletion E) = 1) :
    GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s ∈ iwGL n w := by
  have hle : ∀ t : Fin n → (w.adicCompletion E)ˣ, (∀ i, Valued.v (t i : w.adicCompletion E) = 1) →
      ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) t).val i j) ≤ 1 := by
    intro t ht i j
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, ht]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]
      exact zero_le_one
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1]
  refine ⟨hle s hs, ?_, ?_⟩
  · rw [← map_inv]
    refine hle _ fun i => ?_
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hs, inv_one]
  · intro i j hij
    rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]
    exact zero_lt_one

/- English proof (translation)
Introduce `E _ _ _ hU w hw n b hb ϖ hϖ l hl hyp γ hγ`. Take `⟨-, hcc, hcv, -⟩` from `GlobalTheory.T.placeConjugation_properties_cmField E hU w`. Take `⟨hW1, hW2, -, -⟩` from `GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb`. Take `⟨hanti, hrev⟩` from `GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl`. Establish `hγ' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1`.

Assume the negation of the conclusion as `h`. Conclude with `hγ (if_neg h)`. Take `⟨x, hx, z, hz, e⟩` from `hγ'`. Take `⟨δ, hδ⟩ : ∃ δ : GLw n w, δ = b⁻¹ * γ.1 * b` from `⟨_, rfl⟩`. Establish `hγδ : γ.1 = b * δ * b⁻¹` using `by rw [hδ]; group`.

Establish `hδd : dcos n w (tdiag ϖ (wexp n l)) δ ≠ 0`. Establish `h : ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, δ = x * tdiag ϖ (wexp n l) * z` using `⟨_, (hW2 x).1 hx, _, (hW2 z).1 hz, by rw [hδ, e]; group⟩`. Simplify using `only [dcos, if_pos h]`. Conclude with `one_ne_zero`. Establish `hδU : δ ∈ UJ (cj w) (antiJ (w.adicCompletion E) n)` using `(hW1 δ).1 (by rw [← hγδ]; exact γ.2)`.

Take `⟨m0, hm0, τ, ⟨hτ0, hτ1⟩, hmτ⟩` from `hyp (wexp n l) hanti δ hδd`. Establish `hne : ∀ i, τ.val i i ≠ 0` using `fun i h => by`. Use `hτ1 i` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`.

Take `⟨v, hv⟩ : ∃ v : Fin n → (w.adicCompletion E)ˣ, ∀ i, (v i : w.adicCompletion E) = τ.val i i` from `⟨fun i => Units.mk0 _ (hne i), fun i => rfl⟩`. Establish `hτv : τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) v`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.SmGL.val_diagT]`. Use extensionality with `i j`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, hv]`. Rewrite using `[Matrix.diagonal_apply_ne _ h, hτ0 i j h]`. Take `⟨u, hu⟩ : ∃ u : Fin n → (w.adicCompletion E)ˣ, u = fun i => ϖ ^ wexp n l i * v i` from `⟨_, rfl⟩`.

Establish `htu : tdiag ϖ (wexp n l) * τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u`. Rewrite using `[hτv, hu, tdiag, ← map_mul]`. Both sides reduce to the same expression. Establish `hord : ∀ i, ordL (u i : w.adicCompletion E) = wexp n l i`. Introduce `i`.

Rewrite using `[hu]`. Simplify using `only [Units.val_mul]`. Rewrite using `[UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _), ordL_zpow, hϖ.1, UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hv, hτ1, map_one]), UnitaryCorrection.ordL_one]`. Simplify using the standard rewrite rules. Establish `hm0e` using `(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n m0).1.1 hm0`.

Establish `hδe : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * m0⁻¹ = δ`. Rewrite using `[← htu, ← hmτ]`. Use `group`. Take `⟨s, hs1, hs2⟩` from `GlobalTheory.CompanionTheory.UnitaryCorrection.main (w.adicCompletion E) (cj w) hcc hcv (GlobalTheory.T.norm_one_unit_hilbert_ninety E hU w hw) n (wexp n l) hanti.injective hrev u hord m0 hm0e.1 hm0e.2.1 (by rw [hδe]; exact hδU)`. Establish `hm1 : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s ∈ iwGL n w` using `mul_mem hm0 (diagT_mem_iwGL w n s hs1)`.

Establish `hcomm : (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s)⁻¹ * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u`. Rewrite using `[← map_inv, ← map_mul, ← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[mul_comm]`.

Use `⟨⟨b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹, (hW1 _).2 hs2⟩, (hW2 _).2 ?_, u, hord, ?_⟩` and prove the remaining obligations. Establish `: b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b = m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s` using `by group`. Express the relevant statement in the definitionally equal form `b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b ∈ iwGL n w`. Rewrite using `[this]`. Conclude with `hm1`.

Express the relevant statement in the definitionally equal form `(b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹)⁻¹ * γ.1 * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) = _`. Rewrite using `[hγδ]`. Establish `hd : m0⁻¹ * δ * m0 = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u` using `by rw [hmτ, htu]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → (∀ (y : Fin n → ℤ), StrictAnti y → ∀ δ : GLw n w, dcos n w (tdiag ϖ y) δ ≠ 0 → ∃ m ∈ iwGL n w, ∃ τ : GLw n w, ((∀ i j : Fin n, i ≠ j → τ.val i j = 0) ∧ ∀ i, Valued.v (τ.val i i) = 1) ∧ m⁻¹ * δ * m = tdiag ϖ y * τ) → ∀ γ : UL n w, fU n w b ϖ l γ ≠ 0 → ∃ m ∈ iwU n w b, ∃ u : Fin n → (w.adicCompletion E)ˣ, (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) ∧ (m⁻¹ * γ * m).1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl hyp γ hγ
  obtain ⟨-, hcc, hcv, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨hW1, hW2, -, -⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  obtain ⟨hanti, hrev⟩ := GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl
  have hγ' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b,
      γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := by
    by_contra h
    exact hγ (if_neg h)
  obtain ⟨x, hx, z, hz, e⟩ := hγ'
  obtain ⟨δ, hδ⟩ : ∃ δ : GLw n w, δ = b⁻¹ * γ.1 * b := ⟨_, rfl⟩
  have hγδ : γ.1 = b * δ * b⁻¹ := by rw [hδ]; group
  have hδd : dcos n w (tdiag ϖ (wexp n l)) δ ≠ 0 := by
    have h : ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, δ = x * tdiag ϖ (wexp n l) * z :=
      ⟨_, (hW2 x).1 hx, _, (hW2 z).1 hz, by rw [hδ, e]; group⟩
    simp only [dcos, if_pos h]
    exact one_ne_zero
  have hδU : δ ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) :=
    (hW1 δ).1 (by rw [← hγδ]; exact γ.2)
  obtain ⟨m0, hm0, τ, ⟨hτ0, hτ1⟩, hmτ⟩ := hyp (wexp n l) hanti δ hδd
  have hne : ∀ i, τ.val i i ≠ 0 := fun i h => by
    have := hτ1 i
    rw [h, map_zero] at this
    exact zero_ne_one this
  obtain ⟨v, hv⟩ : ∃ v : Fin n → (w.adicCompletion E)ˣ, ∀ i, (v i : w.adicCompletion E) = τ.val i i :=
    ⟨fun i => Units.mk0 _ (hne i), fun i => rfl⟩
  have hτv : τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) v := by
    apply Units.ext
    rw [GlobalTheory.SmGL.val_diagT]
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, hv]
    · rw [Matrix.diagonal_apply_ne _ h, hτ0 i j h]
  obtain ⟨u, hu⟩ : ∃ u : Fin n → (w.adicCompletion E)ˣ, u = fun i => ϖ ^ wexp n l i * v i := ⟨_, rfl⟩
  have htu : tdiag ϖ (wexp n l) * τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by
    rw [hτv, hu, tdiag, ← map_mul]
    rfl
  have hord : ∀ i, ordL (u i : w.adicCompletion E) = wexp n l i := by
    intro i
    rw [hu]
    simp only [Units.val_mul]
    rw [UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _), ordL_zpow, hϖ.1,
      UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hv, hτ1, map_one]),
      UnitaryCorrection.ordL_one]
    simp
  have hm0e := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n m0).1.1 hm0
  have hδe : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * m0⁻¹ = δ := by
    rw [← htu, ← hmτ]
    group
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.CompanionTheory.UnitaryCorrection.main (w.adicCompletion E) (cj w) hcc hcv
    (GlobalTheory.T.norm_one_unit_hilbert_ninety E hU w hw) n (wexp n l) hanti.injective hrev u hord m0 hm0e.1 hm0e.2.1
    (by rw [hδe]; exact hδU)
  have hm1 : m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s ∈ iwGL n w :=
    mul_mem hm0 (diagT_mem_iwGL w n s hs1)
  have hcomm : (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s)⁻¹ *
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp [mul_comm]
  refine ⟨⟨b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹, (hW1 _).2 hs2⟩,
    (hW2 _).2 ?_, u, hord, ?_⟩
  · have : b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b =
        m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s := by group
    change b⁻¹ * (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) * b ∈ iwGL n w
    rw [this]
    exact hm1
  · change (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹)⁻¹ * γ.1 *
      (b * (m0 * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹) = _
    rw [hγδ]
    have hd : m0⁻¹ * δ * m0 = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u := by rw [hmτ, htu]
    calc _ = b * ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s)⁻¹ * (m0⁻¹ * δ * m0) *
          GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) * b⁻¹ := by group
      _ = _ := by rw [hd, hcomm]

end GlobalTheory.CompanionTheory.UnitaryContraction
