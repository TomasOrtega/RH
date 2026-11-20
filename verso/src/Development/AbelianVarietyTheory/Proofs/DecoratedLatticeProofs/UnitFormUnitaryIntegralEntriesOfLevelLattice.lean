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
Introduce `F E _ _ _ _ _ σ hσ n J hJ t ht Λ hΛ v g hg`. Substitute `hJ` using the available equality. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Introduce `i`. Conclude with `i.elim0`.

Use `haveI : NeZero n := ⟨by omega⟩`. Establish `hlast : ∀ j : Fin n, j.1 + 1 = n ↔ j = Formalism.L2.Col.lastIdx n`. Introduce `j`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `ext`. Simplify using `[Formalism.L2.Col.lastIdx]`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `rfl`. Simplify using `[Formalism.L2.Col.lastIdx]`.

Use linear arithmetic over natural numbers and integers. Establish `hΛeq : Λ = Formalism.L2.Col.rll_dLat n ((t : E)⁻¹)`. Use extensionality with `x`. Rewrite using `[hΛ, Formalism.L2.Col.rll_mem_dLat]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨fun i hi => ?_, ?_⟩` and prove the remaining obligations. Take `⟨r, hr, -⟩` from `h i`. Conclude with `⟨r, hr.symm⟩`. Take `⟨r, hr, hd⟩` from `h (Formalism.L2.Col.lastIdx n)`.

Take `⟨q, rfl⟩` from `hd ((hlast _).2 rfl)`. Use `⟨q, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`. Use `show (q : E) = (t : E)⁻¹ * ((t * q : 𝓞 E) : E)`. Rewrite using `[show ((t * q : 𝓞 E) : E) = (t : E) * q from rfl, inv_mul_cancel_left₀ ht]`.

Introduce and unpack `⟨h1, q, hq⟩`. Introduce `j`. Distinguish the cases in `hj : j = Formalism.L2.Col.lastIdx n`. Substitute `hj` using the available equality. Use `⟨t * q, ?_, fun _ => dvd_mul_right t q⟩` and prove the remaining obligations.

Establish `hq' : (q : E) = (t : E)⁻¹ * x (Formalism.L2.Col.lastIdx n)` using `hq`. Rewrite using `[show ((t * q : 𝓞 E) : E) = (t : E) * q from rfl, hq', mul_inv_cancel_left₀ ht]`. Take `⟨r, hr⟩` from `h1 j hj`. Conclude with `⟨r, hr.symm, fun h => absurd ((hlast j).1 h) hj⟩`. Use `set S := Formalism.BasicNotions.intV E v with hSdef`.

Set `ι` to `Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F)`. Establish `hmem : ∀ z : Fin n → E ⊗[F] v.adicCompletion F, z ∈ Formalism.UG.latS (F` using `F) (v.adicCompletion F) S Λ ↔ (∀ i, i ≠ Formalism.L2.Col.lastIdx n → z i ∈ S) ∧ ι (t : E)⁻¹ * z (Formalism.L2.Col.lastIdx n) ∈ S := by`. Introduce `z`. Rewrite using `[hΛeq]`. Conclude with `Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v _ (inv_ne_zero ht) z`.

Establish `htS : ι (t : E) ∈ S` using `GlobalTheory.UnitLocLastRow.inclE_int v t`. Establish `hcols : ∀ h : GL (Fin n) (E ⊗[F] v.adicCompletion F), h ∈ Formalism.UG.stabGL (Formalism.UG.latS (F` using `F) (v.adicCompletion F) S Λ) → ∀ i j, j ≠ Formalism.L2.Col.lastIdx n → (i ≠ Formalism.L2.Col.lastIdx n → h.1 i j ∈ S) ∧ ι (t : E)⁻¹ * h.1 (Formalism.L2.Col.lastIdx n) j ∈ S := by`. Introduce `h hh i j hj`. Establish `he : (Pi.single j 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈ Formalism.UG.latS (F` using `F) (v.adicCompletion F) S Λ := by`. Rewrite using `[hmem]`.

Use `⟨fun k _ => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`.

Rewrite using `[Pi.single_eq_of_ne hk]`. Conclude with `zero_mem _`. Rewrite using `[Pi.single_eq_of_ne (Ne.symm hj), mul_zero]`. Conclude with `zero_mem _`. Establish `h2` using `(hmem _).1 ((hh _).1 he)`.

Rewrite `h2` using `[Matrix.mulVec_single_one]`. Conclude with `⟨fun hi => h2.1 i hi, h2.2⟩`. Establish `hlastcol : ∀ i, ι (t : E) * g.1 i (Formalism.L2.Col.lastIdx n) ∈ S ∧ (i = Formalism.L2.Col.lastIdx n → g.1 i (Formalism.L2.Col.lastIdx n) ∈ S)`. Introduce `i`. Establish `he : (Pi.single (Formalism.L2.Col.lastIdx n) (ι (t : E)) : Fin n → E ⊗[F] v.adicCompletion F) ∈ Formalism.UG.latS (F` using `F) (v.adicCompletion F) S Λ := by`.

Rewrite using `[hmem]`. Use `⟨fun k hk => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.single_eq_of_ne hk]`. Conclude with `zero_mem _`. Rewrite using `[Pi.single_eq_same, ← map_mul, inv_mul_cancel₀ ht, map_one]`.

Conclude with `one_mem _`. Establish `h2` using `(hmem _).1 ((hg.2 _).1 he)`. Establish `e : ∀ k, ((g.1 : Matrix (Fin n) (Fin n) _) *ᵥ (Pi.single (Formalism.L2.Col.lastIdx n) (ι (t : E)) : Fin n → E ⊗[F] v.adicCompletion F)) k = g.1 k (Formalism.L2.Col.lastIdx n) * ι (t : E)`. Introduce `k`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Use `⟨?_, fun hi => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hi : i = Formalism.L2.Col.lastIdx n`. Substitute `hi` using the available equality. Use `h2.2` as an intermediate fact. Rewrite `this` using `[e, mul_comm (g.1 _ _), ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul]`.

Conclude with `mul_mem htS this`. Use `h2.1 i hi` as an intermediate fact. Rewrite `this` using `[e, mul_comm]`. Conclude with `this`. Substitute `hi` using the available equality.

Use `h2.2` as an intermediate fact. Rewrite `this` using `[e, mul_comm (g.1 _ _), ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul]`. Conclude with `this`. Establish `hU : Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) g.1 * g.1 = 1`. Establish `h1` using `hg.1`.

Express the relevant statement in the definitionally equal form `Formalism.UG.cT _ g.1 * ((1 : Matrix (Fin n) (Fin n) E).map ι) * g.1 = (1 : Matrix (Fin n) (Fin n) E).map ι at h1`. Rewrite `h1` using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`. Conclude with `h1`. Establish `hinv : ((g⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) = Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) g.1` using `Units.inv_eq_of_mul_eq_one_left hU`. Establish `hginv` using `hcols g⁻¹ (inv_mem hg.2)`.

Introduce `i j`. Distinguish the cases in `hj : j = Formalism.L2.Col.lastIdx n`. Substitute `hj` using the available equality. Distinguish the cases in `hi : i = Formalism.L2.Col.lastIdx n`. Conclude with `(hlastcol i).2 hi`.

Establish `h3` using `(hginv (Formalism.L2.Col.lastIdx n) i hi).2`. Rewrite `h3` using `[hinv]`. Express the relevant statement in the definitionally equal form `ι (t : E)⁻¹ * Formalism.UG.sigR σ (v.adicCompletion F) (g.1 i (Formalism.L2.Col.lastIdx n)) ∈ S at h3`. Establish `h4` using `GlobalTheory.UnitLocLastRow.sigR_mem_intV σ v h3`. Rewrite `h4` using `[map_mul, GlobalTheory.UnitLocLastRow.sigR_sigR σ hσ, GlobalTheory.UnitLocLastRow.sigR_inclE]`.

Establish `hs : ι (σ (t : E)) ∈ S`. Use `GlobalTheory.UnitLocLastRow.sigR_mem_intV σ v htS` as an intermediate fact. Rewrite `this` using `[GlobalTheory.UnitLocLastRow.sigR_inclE]`. Then use the resulting hypothesis. Establish `hst : σ (t : E) ≠ 0`. Introduce `h0`.

Apply `ht` to reduce the goal to its premises. Use `congrArg σ h0` as an intermediate fact. Rewrite `this` using `[hσ, map_zero]`. Then use the resulting hypothesis. Establish `e : g.1 i (Formalism.L2.Col.lastIdx n) = ι (σ (t : E)) * (ι (σ (t : E)⁻¹) * g.1 i (Formalism.L2.Col.lastIdx n))`. Rewrite using `[← mul_assoc, ← map_mul, map_inv₀, mul_inv_cancel₀ hst, map_one, one_mul]`.

Rewrite using `[e]`. Conclude with `mul_mem hs h4`. Establish `h2` using `hcols g hg.2 i j hj`. Distinguish the cases in `hi : i = Formalism.L2.Col.lastIdx n`. Substitute `hi` using the available equality.

Establish `e : g.1 (Formalism.L2.Col.lastIdx n) j = ι (t : E) * (ι (t : E)⁻¹ * g.1 (Formalism.L2.Col.lastIdx n) j)`. Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]`. Rewrite using `[e]`. Conclude with `mul_mem htS h2.2`. Conclude with `h2.1 hi`.
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
