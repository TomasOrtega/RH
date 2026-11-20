import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup

open Matrix

noncomputable section

namespace GlobalTheory.KFinLinkPort

open GlobalTheory.KFinVec
open ReciprocityTheory.ChartRestriction.DS (smD smE smE_apply isDerivedOn_smE dS dS_eq_actM actM)
open CompanionTheory.D.gk.HC (KF)

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Unfold `Formalism.L2.Theta.dRep dS`. Use `congr 1`.
-/
theorem dRep_eq_dS (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    Formalism.L2.Theta.dRep σ X w = dS σ X w := by
  unfold Formalism.L2.Theta.dRep dS
  congr 1

/- English proof (translation)
Introduce and unpack `S ⟨hf, -, hK, -⟩`. Establish `hfin : FiniteDimensional ℂ (Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S)` using `(CompanionTheory.HCMult.harish_chandra_multiplicity : Formalism.MainNotions.BridgeCPX.HCMult) n ε H σ hσ hirr S hf hK`. Establish `hle : kIsotypic ε σ S ≤ Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S` using `iSup_le fun T => le_sSup ⟨T.1, fun a v w h => T.2 _ a.2 v w h, rfl⟩`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem isAdmissible_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsAdmissible ε σ := by
  rintro S ⟨hf, -, hK, -⟩
  have hfin : FiniteDimensional ℂ (Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S) :=
    (CompanionTheory.HCMult.harish_chandra_multiplicity : Formalism.MainNotions.BridgeCPX.HCMult) n ε H σ hσ hirr S hf hK
  have hle : kIsotypic ε σ S ≤ Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S :=
    iSup_le fun T => le_sSup ⟨T.1, fun a v w h => T.2 _ a.2 v w h, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

/- English proof (translation)
Introduce `X hX v hv`. Take `⟨h1, h2⟩` from `CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr`. Establish `hvS : v ∈ smD ε σ` using `h1 v hv`. Rewrite using `[dRep_eq_dS]`. Establish `e` using `dS_eq_actM (isDerivedOn_smE hσ) hX ⟨v, hvS⟩`.

Simplify using `only [] at e`. Rewrite using `[e]`. Simplify using `only [actM, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (h2 a b ⟨v, hvS⟩ hv)`.
-/
theorem isLieStable_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsLieStable ε σ (kFinSub ε σ) := by
  intro X hX v hv
  obtain ⟨h1, h2⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  have hvS : v ∈ smD ε σ := h1 v hv
  rw [dRep_eq_dS]
  have e := dS_eq_actM (isDerivedOn_smE hσ) hX ⟨v, hvS⟩
  simp only [] at e
  rw [e]
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (h2 a b ⟨v, hvS⟩ hv)

/- English proof (translation)
Take `⟨h1, -⟩` from `CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr`. Set `N : Submodule ℂ (smD ε σ)` to `S.comap (smD ε σ).subtype`. Establish `hNK : (N : Set (smD ε σ)) ⊆ KF ε σ` using `fun v hv => hS hv`. Establish `hst : ∀ a b, ∀ v ∈ N, smE ε σ a b v ∈ N`. Introduce `a b v hv`.

Use `show ((smE ε σ a b v : smD ε σ) : H) ∈ S`. Rewrite using `[smE_apply hσ]`. Establish `e1` using `hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε (Matrix.single a b 1)) (v : H) hv`. Establish `e2` using `hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε (Matrix.single a b 1)) (v : H) hv`. Rewrite `e1`, `e2` using `[dRep_eq_dS]`.

Conclude with `S.add_mem e1 (S.smul_mem _ e2)`. Break down `GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N hNK hst with h | h` into its components or cases. Use `left`. Use `eq_bot_iff.2 fun v hv => ?_` and prove the remaining obligations. Establish `hvN : (⟨v, h1 v (hS hv)⟩ : smD ε σ) ∈ N` using `hv`.

Rewrite `hvN` using `[h]`. Use `(Submodule.mem_bot ℂ).1 hvN` as an intermediate fact. Conclude with `(Submodule.mem_bot ℂ).2 (congrArg Subtype.val this)`. Use `right`. Use `le_antisymm hS fun v hv => ?_` and prove the remaining obligations.

Establish `hvK : (⟨v, h1 v hv⟩ : smD ε σ) ∈ KF ε σ` using `hv`. Rewrite `hvK` using `[← h]`. Conclude with `hvK`.
-/
theorem lieIrr_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (S : Submodule ℂ H) (hS : S ≤ kFinSub ε σ)
    (hL : IsLieStable ε σ S) : S = ⊥ ∨ S = kFinSub ε σ := by
  obtain ⟨h1, -⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  let N : Submodule ℂ (smD ε σ) := S.comap (smD ε σ).subtype
  have hNK : (N : Set (smD ε σ)) ⊆ KF ε σ := fun v hv => hS hv
  have hst : ∀ a b, ∀ v ∈ N, smE ε σ a b v ∈ N := by
    intro a b v hv
    show ((smE ε σ a b v : smD ε σ) : H) ∈ S
    rw [smE_apply hσ]
    have e1 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε (Matrix.single a b 1)) (v : H) hv
    have e2 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε (Matrix.single a b 1)) (v : H) hv
    rw [dRep_eq_dS] at e1 e2
    exact S.add_mem e1 (S.smul_mem _ e2)
  rcases GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N hNK hst with h | h
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hvN : (⟨v, h1 v (hS hv)⟩ : smD ε σ) ∈ N := hv
    rw [h] at hvN
    have := (Submodule.mem_bot ℂ).1 hvN
    exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val this)
  · right
    refine le_antisymm hS fun v hv => ?_
    have hvK : (⟨v, h1 v hv⟩ : smD ε σ) ∈ KF ε σ := hv
    rw [← h] at hvK
    exact hvK

end GlobalTheory.KFinLinkPort

namespace GlobalTheory.KFinLinkPort

/- English proof (translation)
Introduce `n ε H _ _ _ _ σ hσ hirr`. Conclude with `⟨GlobalTheory.KFinLinkPort.isAdmissible_of hσ hirr, GlobalTheory.HcPort.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hσ hirr, GlobalTheory.T.dense_kFinite_vectors_unitaryGroupRep n ε H σ hσ, GlobalTheory.KFinLinkPort.isLieStable_of hσ hirr, fun S hS hL => GlobalTheory.KFinLi …`.
-/
theorem kFiniteVectors_irreducibleUnitary_unitaryGroupPQ : GlobalTheory.Published.KFiniteVectorsUnitary := by
  intro n ε H _ _ _ _ σ hσ hirr
  exact ⟨GlobalTheory.KFinLinkPort.isAdmissible_of hσ hirr,
    GlobalTheory.HcPort.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hσ hirr,
    GlobalTheory.T.dense_kFinite_vectors_unitaryGroupRep n ε H σ hσ,
    GlobalTheory.KFinLinkPort.isLieStable_of hσ hirr,
    fun S hS hL => GlobalTheory.KFinLinkPort.lieIrr_of hσ hirr S hS hL⟩

end GlobalTheory.KFinLinkPort

end
