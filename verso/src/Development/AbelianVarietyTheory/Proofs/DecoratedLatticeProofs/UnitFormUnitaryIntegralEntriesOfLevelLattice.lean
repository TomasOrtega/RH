import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.Columns.RecLevelLocT
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLastRowCongrOneMemLocalLevelLevelPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitLevelInt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Separate the alternatives or extract the components of the hypothesis. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem entry_mem_of_levelVL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J = 1 → ∀ (t : 𝓞 E), (t : E) ≠ 0 → ∀ (Λ : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ Λ ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ Formalism.UG.levelVL σ J v Λ → ∀ i j, g.1 i j ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring := by
  intro F E _ _ _ _ _ σ hσ n J hJ t ht Λ hΛ v g hg
  subst hJ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro i; exact i.elim0
  haveI : NeZero n := ⟨by omega⟩
  have hlast : ∀ j : Fin n, j.1 + 1 = n ↔ j = Formalism.L2.Col.lastIdx n := by
    intro j
    constructor
    · intro h; ext; simp [Formalism.L2.Col.lastIdx]; omega
    · rintro rfl; simp [Formalism.L2.Col.lastIdx]; omega
  have hΛeq : Λ = Formalism.L2.Col.rll_dLat n ((t : E)⁻¹) := by
    ext x
    rw [hΛ, Formalism.L2.Col.rll_mem_dLat]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · obtain ⟨r, hr, -⟩ := h i
        exact ⟨r, hr.symm⟩
      · obtain ⟨r, hr, hd⟩ := h (Formalism.L2.Col.lastIdx n)
        obtain ⟨q, rfl⟩ := hd ((hlast _).2 rfl)
        refine ⟨q, ?_⟩
        rw [hr]
        show (q : E) = (t : E)⁻¹ * ((t * q : 𝓞 E) : E)
        rw [show ((t * q : 𝓞 E) : E) = (t : E) * q from rfl, inv_mul_cancel_left₀ ht]
    · rintro ⟨h1, q, hq⟩
      intro j
      by_cases hj : j = Formalism.L2.Col.lastIdx n
      · subst hj
        refine ⟨t * q, ?_, fun _ => dvd_mul_right t q⟩
        have hq' : (q : E) = (t : E)⁻¹ * x (Formalism.L2.Col.lastIdx n) := hq
        rw [show ((t * q : 𝓞 E) : E) = (t : E) * q from rfl, hq', mul_inv_cancel_left₀ ht]
      · obtain ⟨r, hr⟩ := h1 j hj
        exact ⟨r, hr.symm, fun h => absurd ((hlast j).1 h) hj⟩
  set S := Formalism.BasicNotions.intV E v with hSdef
  let ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F)
  have hmem : ∀ z : Fin n → E ⊗[F] v.adicCompletion F,
      z ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ ↔
        (∀ i, i ≠ Formalism.L2.Col.lastIdx n → z i ∈ S) ∧ ι (t : E)⁻¹ * z (Formalism.L2.Col.lastIdx n) ∈ S := by
    intro z
    rw [hΛeq]
    exact Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v _ (inv_ne_zero ht) z
  have htS : ι (t : E) ∈ S := GlobalTheory.UnitLocLastRow.inclE_int v t
  have hcols : ∀ h : GL (Fin n) (E ⊗[F] v.adicCompletion F),
      h ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ) →
      ∀ i j, j ≠ Formalism.L2.Col.lastIdx n → (i ≠ Formalism.L2.Col.lastIdx n → h.1 i j ∈ S) ∧
        ι (t : E)⁻¹ * h.1 (Formalism.L2.Col.lastIdx n) j ∈ S := by
    intro h hh i j hj
    have he : (Pi.single j 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ := by
      rw [hmem]
      refine ⟨fun k _ => ?_, ?_⟩
      · by_cases hk : k = j
        · subst hk; rw [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne hk]; exact zero_mem _
      · rw [Pi.single_eq_of_ne (Ne.symm hj), mul_zero]; exact zero_mem _
    have h2 := (hmem _).1 ((hh _).1 he)
    rw [Matrix.mulVec_single_one] at h2
    exact ⟨fun hi => h2.1 i hi, h2.2⟩
  have hlastcol : ∀ i, ι (t : E) * g.1 i (Formalism.L2.Col.lastIdx n) ∈ S ∧
      (i = Formalism.L2.Col.lastIdx n → g.1 i (Formalism.L2.Col.lastIdx n) ∈ S) := by
    intro i
    have he : (Pi.single (Formalism.L2.Col.lastIdx n) (ι (t : E)) : Fin n → E ⊗[F] v.adicCompletion F) ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ := by
      rw [hmem]
      refine ⟨fun k hk => ?_, ?_⟩
      · rw [Pi.single_eq_of_ne hk]; exact zero_mem _
      · rw [Pi.single_eq_same, ← map_mul, inv_mul_cancel₀ ht, map_one]; exact one_mem _
    have h2 := (hmem _).1 ((hg.2 _).1 he)
    have e : ∀ k, ((g.1 : Matrix (Fin n) (Fin n) _) *ᵥ
        (Pi.single (Formalism.L2.Col.lastIdx n) (ι (t : E)) : Fin n → E ⊗[F] v.adicCompletion F)) k =
          g.1 k (Formalism.L2.Col.lastIdx n) * ι (t : E) := by
      intro k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    refine ⟨?_, fun hi => ?_⟩
    · by_cases hi : i = Formalism.L2.Col.lastIdx n
      · subst hi
        have := h2.2
        rw [e, mul_comm (g.1 _ _), ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] at this
        exact mul_mem htS this
      · have := h2.1 i hi
        rw [e, mul_comm] at this
        exact this
    · subst hi
      have := h2.2
      rw [e, mul_comm (g.1 _ _), ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] at this
      exact this

  have hU : Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) g.1 * g.1 = 1 := by
    have h1 := hg.1
    change Formalism.UG.cT _ g.1 * ((1 : Matrix (Fin n) (Fin n) E).map ι) * g.1 = (1 : Matrix (Fin n) (Fin n) E).map ι at h1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h1
    exact h1
  have hinv : ((g⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) = Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) g.1 :=
    Units.inv_eq_of_mul_eq_one_left hU
  have hginv := hcols g⁻¹ (inv_mem hg.2)
  intro i j
  by_cases hj : j = Formalism.L2.Col.lastIdx n
  · subst hj
    by_cases hi : i = Formalism.L2.Col.lastIdx n
    · exact (hlastcol i).2 hi
    · have h3 := (hginv (Formalism.L2.Col.lastIdx n) i hi).2
      rw [hinv] at h3
      change ι (t : E)⁻¹ * Formalism.UG.sigR σ (v.adicCompletion F) (g.1 i (Formalism.L2.Col.lastIdx n)) ∈ S at h3
      have h4 := GlobalTheory.UnitLocLastRow.sigR_mem_intV σ v h3
      rw [map_mul, GlobalTheory.UnitLocLastRow.sigR_sigR σ hσ, GlobalTheory.UnitLocLastRow.sigR_inclE] at h4
      have hs : ι (σ (t : E)) ∈ S := by
        have := GlobalTheory.UnitLocLastRow.sigR_mem_intV σ v htS
        rwa [GlobalTheory.UnitLocLastRow.sigR_inclE] at this
      have hst : σ (t : E) ≠ 0 := by
        intro h0; apply ht
        have := congrArg σ h0
        rwa [hσ, map_zero] at this
      have e : g.1 i (Formalism.L2.Col.lastIdx n) = ι (σ (t : E)) * (ι (σ (t : E)⁻¹) * g.1 i (Formalism.L2.Col.lastIdx n)) := by
        rw [← mul_assoc, ← map_mul, map_inv₀, mul_inv_cancel₀ hst, map_one, one_mul]
      rw [e]
      exact mul_mem hs h4
  · have h2 := hcols g hg.2 i j hj
    by_cases hi : i = Formalism.L2.Col.lastIdx n
    · subst hi
      have e : g.1 (Formalism.L2.Col.lastIdx n) j = ι (t : E) * (ι (t : E)⁻¹ * g.1 (Formalism.L2.Col.lastIdx n) j) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
      rw [e]; exact mul_mem htS h2.2
    · exact h2.1 hi

end GlobalTheory.UnitLevelInt
