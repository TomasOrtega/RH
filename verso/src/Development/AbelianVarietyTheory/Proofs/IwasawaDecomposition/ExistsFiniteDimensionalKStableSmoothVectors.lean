import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

/- English proof (translation)
Introduce and unpack `n ε H _ _ _ σ P G hP h hU ⟨Λ, S, hS⟩`. Take `⟨w, hwS, hw, -⟩` from `hS.2.2.2.1`. Establish `hwpos : 0 < ‖w‖` using `norm_pos_iff.2 hw`. Establish `hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε` using `(1 : Formalism.REAL.UJ ε).2`. Establish `hnb : {g | ‖σ g w - w‖ < ‖w‖ / 2} ∈ 𝓝[UJset ε] (1 : Matrix (Fin n) (Fin n) ℂ)`.

Establish `h` using `(hU.2.2 w 1 hone) (Metric.ball_mem_nhds _ (half_pos hwpos))`. Simplify `h` using `[hU.1.1, Set.preimage, dist_eq_norm]`. Take `⟨U, hUn, hUs⟩` from `mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb`. Take `⟨φ, hφ, hφc, hφU, hφ0, hφ1, hinv⟩` from `GlobalTheory.LowTypeRestriction.exists_bump hUn`. Establish `hT : IsTest φ` using `⟨hφ, hφc⟩`.

Establish `hne` using `GlobalTheory.LowTypeRestriction.garding_ne_zero hU hT.continuous hφc hφ0 hφ1 hw fun g hg h0 => hUs ⟨hφU g h0, hg⟩`. Establish `hK` using `GlobalTheory.LowTypeRestriction.isKTypeOf_map hS (GlobalTheory.LowTypeRestriction.garding hU hT.continuous hφc) (fun k hk w => GlobalTheory.LowTypeRestriction.garding_comm hU hT.continuous hφc hinv hk w) hwS hne`. Use `⟨S.map (GlobalTheory.LowTypeRestriction.garding hU hT.continuous hφc), hK.1, (Submodule.ne_bot_iff _).2 ⟨_, ⟨w, hwS, rfl⟩, hne⟩, ?_, fun k hk v hv => hK.2.1 k hk v hv⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨v, -, rfl⟩`. Conclude with `gard_mem hP h hU hT v`.
-/
theorem exists_finiteDimensional_kStable_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → (∃ Λ S, IsKTypeOf ε σ Λ S) → ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ W ≠ ⊥ ∧ W ≤ smSub G (trRep σ P) ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W := by
  rintro n ε H _ _ _ σ P G hP h hU ⟨Λ, S, hS⟩
  obtain ⟨w, hwS, hw, -⟩ := hS.2.2.2.1
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := (1 : Formalism.REAL.UJ ε).2
  have hnb : {g | ‖σ g w - w‖ < ‖w‖ / 2} ∈ 𝓝[UJset ε] (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := (hU.2.2 w 1 hone) (Metric.ball_mem_nhds _ (half_pos hwpos))
    simpa [hU.1.1, Set.preimage, dist_eq_norm] using h
  obtain ⟨U, hUn, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb
  obtain ⟨φ, hφ, hφc, hφU, hφ0, hφ1, hinv⟩ := GlobalTheory.LowTypeRestriction.exists_bump hUn
  have hT : IsTest φ := ⟨hφ, hφc⟩
  have hne := GlobalTheory.LowTypeRestriction.garding_ne_zero hU hT.continuous hφc hφ0 hφ1 hw
    fun g hg h0 => hUs ⟨hφU g h0, hg⟩
  have hK := GlobalTheory.LowTypeRestriction.isKTypeOf_map hS (GlobalTheory.LowTypeRestriction.garding hU hT.continuous hφc)
    (fun k hk w => GlobalTheory.LowTypeRestriction.garding_comm hU hT.continuous hφc hinv hk w) hwS hne
  refine ⟨S.map (GlobalTheory.LowTypeRestriction.garding hU hT.continuous hφc), hK.1,
    (Submodule.ne_bot_iff _).2 ⟨_, ⟨w, hwS, rfl⟩, hne⟩, ?_, fun k hk v hv => hK.2.1 k hk v hv⟩
  rintro _ ⟨v, -, rfl⟩
  exact gard_mem hP h hU hT v

end GlobalTheory.SmVec
