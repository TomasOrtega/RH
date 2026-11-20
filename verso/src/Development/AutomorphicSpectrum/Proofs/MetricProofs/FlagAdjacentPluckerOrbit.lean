import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mul_one_add_single_apply {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (ca cb : Fin N) (t : ℂ) (r c : Fin N) :
    (h * (1 + Matrix.single cb ca t)) r c = h r c + if c = ca then t * h r cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  simp only [Matrix.single_apply]
  split_ifs with hc
  · subst hc
    simp [mul_comm]
  · simp [Ne.symm hc]

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem minorIJ_mul_transvection {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N)) {ca cb : Fin N}
    (hne : ca ≠ cb) (t : ℂ) (hJ : ca ∈ J ↔ cb ∈ J) :
    minorIJ (h * (1 + Matrix.single cb ca t)) I J = minorIJ h I J := by
  unfold minorIJ
  split_ifs with e
  · by_cases hca : ca ∈ J
    · have hcb := hJ.1 hca
      obtain ⟨p, hp⟩ : ca ∈ Set.range (J.orderEmbOfFin (rfl : J.card = J.card)) := by
        rw [Finset.range_orderEmbOfFin]; exact hca
      obtain ⟨q, hq⟩ : cb ∈ Set.range (J.orderEmbOfFin (rfl : J.card = J.card)) := by
        rw [Finset.range_orderEmbOfFin]; exact hcb
      have hpq : p ≠ q := fun h' => hne (by rw [← hp, ← hq, h'])
      refine (congrArg Matrix.det ?_).trans
        (Matrix.det_updateCol_add_smul_self (h.submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl)) hpq t)
      ext a b
      rw [Matrix.submatrix_apply, mul_one_add_single_apply]
      by_cases hb : b = p
      · rw [hb, Matrix.updateCol_self]
        simp [hp, hq]
      · have hbc : J.orderEmbOfFin rfl b ≠ ca := fun h' =>
          hb ((J.orderEmbOfFin rfl).injective (h'.trans hp.symm))
        rw [Matrix.updateCol_ne hb]
        simp [hbc]
    · congr 1
      ext a b
      have hbc : J.orderEmbOfFin rfl b ≠ ca := fun h' => hca (h' ▸ Finset.orderEmbOfFin_mem J rfl b)
      simp [mul_one_add_single_apply, hbc]
  · rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem mem_stepCols_iff {N j : ℕ} {a b i ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hi : i ≠ a) :
    ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i := by
  have hi' : (i : ℕ) ≠ a := fun h => hi (Fin.ext h)
  have := a.isLt
  have := b.isLt
  have := i.isLt
  have := ca.isLt
  have := cb.isLt
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold lastCol at hca
  split_ifs at hca ⊢ <;> omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Both sides reduce to the same expression. Apply function extensionality and compare values at an arbitrary argument.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify by unfolding definitions. Reduce the equality to equality of the corresponding arguments.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fstPt_sndPt_wVec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), fstPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b h ∧ sndPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hab hblk hca hcb F bv h t
  have hne : ca ≠ cb := by
    intro e
    have := congrArg Fin.val e
    omega
  refine ⟨?_, ?_⟩
  · funext p
    obtain ⟨k, m⟩ := p
    rfl
  · funext p
    obtain ⟨k, m⟩ := p
    simp only [sndPt, Function.comp_apply]
    by_cases hk : k = k₀
    · subst hk
      rw [v₁_self]
      show (∑ I, valAt M.x (F.u ⟨k, m⟩ I) bv * minorIJ (h τ * (1 + Matrix.single cb ca t)) I (stepCols N j a)) = _
      rw [flagPt_step M F bv _ hblk m]
      simp [Function.update_self]
    · rw [v₁_ne (p := ⟨k, m⟩) hk]
      show FC.flagPt M F bv h ⟨k, m⟩ = _
      by_cases hbase : ∀ p, M.blk p ≠ some k
      · simp [FC.flagPt, hbase]
      · push Not at hbase
        obtain ⟨⟨τ', i⟩, hp⟩ := hbase
        rw [flagPt_step M F bv h hp m, flagPt_step M F bv _ hp m]
        refine Finset.sum_congr rfl fun I _ => ?_
        dsimp only
        congr 1
        by_cases hτ : τ' = τ
        · subst hτ
          have hia : i ≠ a := by
            rintro rfl
            exact hk (Option.some_injective _ (hp.symm.trans hblk))
          rw [Function.update_self, minorIJ_mul_transvection _ _ _ hne t (mem_stepCols_iff hb hab hca hcb hia)]
        · rw [Function.update_of_ne hτ]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
