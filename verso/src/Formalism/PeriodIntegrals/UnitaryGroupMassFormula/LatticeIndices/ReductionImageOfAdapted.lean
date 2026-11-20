import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocCongIffEnt

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Pos

variable {r k : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem frA_condE (a : Fin r) (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.castSucc a → i ≠ pe a') ↔ i ∉ (Sum.inl '' {b : Fin r | b.1 < a.1}) := by
  constructor
  · rintro h ⟨b, hb, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_castSucc_iff.mpr hb) (by rw [pe_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    have ha2 : (a' : ℕ) < a.1 := ha'
    refine ⟨⟨a', by omega⟩, ha2, ?_⟩
    rw [hi, pe_inl_of_lt ha']

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem frA_condZ (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.last r → i ≠ pe a') ↔ i ∉ (Sum.inl '' Set.univ) := by
  constructor
  · rintro h ⟨b, -, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_last b) (by rw [pe_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    refine ⟨⟨a', ha'⟩, trivial, ?_⟩
    rw [hi, pe_inl_of_lt ha']

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem frA_condF (a : Fin r) (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.castSucc a → i ≠ pf a') ↔
      i ∉ ((fun b : Fin r => (Sum.inr (Sum.inr (Fin.rev b)) : Formalism.FourierDecayAlt.S3.Idx r k)) '' {b : Fin r | b.1 < a.1}) := by
  constructor
  · rintro h ⟨b, hb, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_castSucc_iff.mpr hb) (by rw [pf_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    have ha2 : (a' : ℕ) < a.1 := ha'
    refine ⟨⟨a', by omega⟩, ha2, ?_⟩
    rw [hi, pf_of_lt ha']

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem frA_condFZ (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.last r → i ≠ pf a') ↔
      i ∉ ((fun b : Fin r => (Sum.inr (Sum.inr (Fin.rev b)) : Formalism.FourierDecayAlt.S3.Idx r k)) '' Set.univ) := by
  constructor
  · rintro h ⟨b, -, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_last b) (by rw [pf_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    refine ⟨⟨a', ha'⟩, trivial, ?_⟩
    rw [hi, pf_of_lt ha']

end Pos

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem ent_iff_nuG (π : Op X p →+* ZMod (gOf p)) (Y : GL (IdxD D) (Op X p)) :
    EntA X p π Y ↔ glRed π Y ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k := by
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  rw [mem_nuG_iff_flags, colFlag_iff', colW_iff, rowFlag_iff', ← map_inv, Fin.forall_fin_succ',
    Fin.forall_fin_succ']
  simp only [pe_castSucc, pe_last, pf_castSucc, pf_last]
  simp only [frA_condE, frA_condZ, frA_condF, frA_condFZ]
  unfold EntA
  constructor
  · rintro ⟨hP, hR, hT, hQ, hS⟩
    exact ⟨⟨hP, hR⟩, hT, ⟨hQ, hS⟩⟩
  · rintro ⟨⟨hP, hR⟩, hT, ⟨hQ, hS⟩⟩
    exact ⟨hP, hR, hT, hQ, hS⟩

variable (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (IdxD D) (FpX X p))

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem transA_of (hθ : IsSplitEquiv X p θ) (π : Op X p →+* ZMod (gOf p))
    (hker : RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)}) (hS : SplitA X p θ Q) (hA : AdaptA X p θ Q) :
    TransA X p θ Q π := fun x _ Y hY =>
  (locCong_iff_ent X p θ Q hθ π hker hS hA x Y hY).trans (ent_iff_nuG X p π Y)

def StAdaptA : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ SplitA X p θ Q ∧ AdaptA X p θ Q

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem stFrameA_of_adapt (hC : LatCoreX) (h : StAdaptA X p) : StFrameA X p := by
  obtain ⟨θ, hθ, Q, hL, hS, hA⟩ := h
  obtain ⟨π, hπ, hker⟩ := stResZ_holds X p
  exact stFrameA_of_trans X hC p ⟨θ, hθ, Q, hL, π, hπ, hker, transA_of X p θ Q hθ π hker hS hA⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem reduction_image_of_adapted (hb : AdBridgeIso X.B.I) (hC : LatCoreX) (h : StAdaptA X p) : LevelReductionImage X hb p :=
  reduction_image_of_frame X hb p (stFrameA_of_adapt X p hC h)

end Loc

end MassDataIdxSteps
