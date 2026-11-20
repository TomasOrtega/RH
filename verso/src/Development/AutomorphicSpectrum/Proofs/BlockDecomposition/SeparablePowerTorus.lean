import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSecondBlockOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VLtOneOfOrdLEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitone
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharpolyConjDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealWeight

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MLM Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SepPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `e` using `congrArg Valued.v h`. Rewrite `e` using `[map_mul, map_mul, hu, hv, mul_one, mul_one]`. Establish `h1 : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ)`. Rewrite using `[GlobalTheory.BorelUMod.v_eq_exp ϖ.ne_zero, hϖ.1]`. Establish `h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0`.

Rewrite using `[h1]`. Conclude with `WithZero.exp_ne_zero`. Establish `hne : Valued.v (ϖ : w.adicCompletion E) ≠ 1`. Rewrite using `[h1, ← WithZero.exp_zero]`. Introduce `h2`.

Use `WithZero.exp_injective h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `e` using `[Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀]`. Conclude with `zpow_right_injective₀ (zero_lt_iff.2 h0) hne e`.
-/
theorem zpow_mul_inj {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {a c : ℤ} {u v : w.adicCompletion E}
    (hu : Valued.v u = 1) (hv : Valued.v v = 1)
    (h : ((ϖ ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * u = ((ϖ ^ c : (w.adicCompletion E)ˣ) : w.adicCompletion E) * v) :
    a = c := by
  have e := congrArg Valued.v h
  rw [map_mul, map_mul, hu, hv, mul_one, mul_one] at e
  have h1 : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [GlobalTheory.BorelUMod.v_eq_exp ϖ.ne_zero, hϖ.1]
  have h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0 := by
    rw [h1]; exact WithZero.exp_ne_zero
  have hne : Valued.v (ϖ : w.adicCompletion E) ≠ 1 := by
    rw [h1, ← WithZero.exp_zero]
    intro h2
    have := WithZero.exp_injective h2
    omega
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀] at e
  exact zpow_right_injective₀ (zero_lt_iff.2 h0) hne e

/- English proof (translation)
Establish `hy` using `(GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).1`. Establish `h' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1`. Assume the negation of the conclusion as `hc`. Conclude with `h (if_neg hc)`. Take `⟨x, hx, z, hz, e⟩` from `h'`.

Take `⟨x', hx', ex⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)`. Take `⟨z', hz', ez⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hz)`. Establish `ex' : x.1 = b * x' * b⁻¹` using `ex.symm`. Establish `ez' : z.1 = b * z' * b⁻¹` using `ez.symm`. Establish `hδ : dcos n w (tdiag ϖ (wexp n l)) (b⁻¹ * γ.1 * b) ≠ 0`.

Establish `: ∃ p ∈ iwGL n w, ∃ q ∈ iwGL n w, b⁻¹ * γ.1 * b = p * tdiag ϖ (wexp n l) * q` using `⟨x', hx', z', hz', by rw [e, ex', ez']; group⟩`. Simplify using `[dcos, this]`. Take `⟨m, -, τ, hτ, em⟩` from `GlobalTheory.CompanionTheory.IwahoriContraction.contr_id w ϖ hϖ n (wexp n l) hy _ hδ`. Establish `hval : (tdiag ϖ (wexp n l) * τ).val = Matrix.diagonal fun i => ((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * τ.val i i`. Establish `hτd : τ.val = Matrix.diagonal fun i => τ.val i i`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[hτ.1 i j hij, Matrix.diagonal_apply_ne _ hij]`.

Rewrite using `[Units.val_mul, GlobalTheory.CompanionTheory.FUMulPf.tdiag_val, hτd, Matrix.diagonal_mul_diagonal]`. Simplify using the standard rewrite rules. Establish `hg : γ.1 = (b * m) * (tdiag ϖ (wexp n l) * τ) * (b * m)⁻¹`. Rewrite using `[← em]`. Use `group`.

Rewrite using `[GlobalTheory.CompanionTheory.UnitarySide.charpoly_conj_diagonal (b * m) _ γ.1 _ hval hg, Polynomial.separable_prod_X_sub_C_iff]`. Introduce `i j hij`. Conclude with `hy.injective (zpow_mul_inj hϖ (hτ.2 i) (hτ.2 j) hij)`.
-/
theorem separable_of_fU {w : Pl E} {b : GLw n w} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {l : Fin (n / 2) → ℤ}
    (hl : Cone l) {γ : UL n w} (h : fU n w b ϖ l γ ≠ 0) : γ.1.val.charpoly.Separable := by
  have hy := (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).1
  have h' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := by
    by_contra hc
    exact h (if_neg hc)
  obtain ⟨x, hx, z, hz, e⟩ := h'
  obtain ⟨x', hx', ex⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
  obtain ⟨z', hz', ez⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hz)
  have ex' : x.1 = b * x' * b⁻¹ := ex.symm
  have ez' : z.1 = b * z' * b⁻¹ := ez.symm
  have hδ : dcos n w (tdiag ϖ (wexp n l)) (b⁻¹ * γ.1 * b) ≠ 0 := by
    have : ∃ p ∈ iwGL n w, ∃ q ∈ iwGL n w, b⁻¹ * γ.1 * b = p * tdiag ϖ (wexp n l) * q :=
      ⟨x', hx', z', hz', by rw [e, ex', ez']; group⟩
    simp [dcos, this]
  obtain ⟨m, -, τ, hτ, em⟩ := GlobalTheory.CompanionTheory.IwahoriContraction.contr_id w ϖ hϖ n (wexp n l) hy _ hδ
  have hval : (tdiag ϖ (wexp n l) * τ).val = Matrix.diagonal fun i =>
      ((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * τ.val i i := by
    have hτd : τ.val = Matrix.diagonal fun i => τ.val i i := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · rw [hτ.1 i j hij, Matrix.diagonal_apply_ne _ hij]
    rw [Units.val_mul, GlobalTheory.CompanionTheory.FUMulPf.tdiag_val, hτd, Matrix.diagonal_mul_diagonal]
    simp
  have hg : γ.1 = (b * m) * (tdiag ϖ (wexp n l) * τ) * (b * m)⁻¹ := by
    rw [← em]; group
  rw [GlobalTheory.CompanionTheory.UnitarySide.charpoly_conj_diagonal (b * m) _ γ.1 _ hval hg, Polynomial.separable_prod_X_sub_C_iff]
  intro i j hij
  exact hy.injective (zpow_mul_inj hϖ (hτ.2 i) (hτ.2 j) hij)

/- English proof (translation)
Introduce `E _ _ _ hU n d hd hm m w hT y hy`. Take `⟨hs, hb, hϖ, hx⟩` from `hm.T w hT`. Establish `hx' : ∀ j, StrictAnti (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j) ∧ Cone (lOf (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j))` using `fun j => hx j.1 j.2`. Take `⟨J', _, c', x', hx'', e1, -⟩` from `GlobalTheory.CompanionTheory.MatchPow.pow_claim GlobalTheory.CompanionTheory.FUMulPf.fuMul GlobalTheory.CompanionTheory.DcosProduct.dcosMul hU hs 0 hb hϖ (GlobalTheory.CompanionTheory.MatchLMPlaces.cc d w) (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w) hx' m`. Establish `hKU : d.KU w = iwU n w (d.b w)` using `by simp [LocData.KU, hT]`.

Establish `hG : d.gU (m + 1) w y = (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1) * (GlobalTheory.CompanionTheory.MatchPow.alpha n w (d.b w) ^ m * ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y)`. Unfold `LocData.gU`. Rewrite using `[hKU, GlobalTheory.CompanionTheory.MatchLMPlaces.unitary_function_at_T d hT, GlobalTheory.CompanionTheory.MatchLMPlaces.lpow_scale, e1]`. Rewrite `hy` using `[hG]`. Establish `hsum : ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y ≠ 0` using `fun h0 => hy (by rw [h0]; simp)`.

Take `⟨j, -, hj⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hsum`. Conclude with `separable_of_fU hϖ (hx'' j).2 (right_ne_zero_of_mul hj)`.
-/
theorem sepPowT : SepPowT := by
  intro E _ _ _ hU n d hd hm m w hT y hy
  obtain ⟨hs, hb, hϖ, hx⟩ := hm.T w hT
  have hx' : ∀ j, StrictAnti (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j) ∧ Cone (lOf (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j)) :=
    fun j => hx j.1 j.2
  obtain ⟨J', _, c', x', hx'', e1, -⟩ := GlobalTheory.CompanionTheory.MatchPow.pow_claim GlobalTheory.CompanionTheory.FUMulPf.fuMul GlobalTheory.CompanionTheory.DcosProduct.dcosMul hU hs 0
    hb hϖ (GlobalTheory.CompanionTheory.MatchLMPlaces.cc d w) (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w) hx' m
  have hKU : d.KU w = iwU n w (d.b w) := by simp [LocData.KU, hT]
  have hG : d.gU (m + 1) w y = (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1) *
      (GlobalTheory.CompanionTheory.MatchPow.alpha n w (d.b w) ^ m * ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y) := by
    unfold LocData.gU
    rw [hKU, GlobalTheory.CompanionTheory.MatchLMPlaces.unitary_function_at_T d hT, GlobalTheory.CompanionTheory.MatchLMPlaces.lpow_scale, e1]
  rw [hG] at hy
  have hsum : ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y ≠ 0 := fun h0 => hy (by rw [h0]; simp)
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact separable_of_fU hϖ (hx'' j).2 (right_ne_zero_of_mul hj)

end GlobalTheory.CompanionTheory.SepPow

end
