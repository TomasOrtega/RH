import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLocJacHyp
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.SG.LocVol.LJP

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem hE_crdOf {D : D7} (X : HidaSetting D) (x y : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.HidaSetting.crdOf X.B.I X.ιE X.bas x) (Formalism.L2.SG.HidaSetting.crdOf X.B.I X.ιE X.bas y) =
      X.ιE.symm ((VS D).hT x y) := by
  apply X.ιE.injective
  rw [RingEquiv.apply_symm_apply, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Proceed by induction. Treat this case separately.

Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately.
-/
theorem diag : DiagProp := by
  intro D X w v
  have hze : ∀ a, (VS D).hT (X.zu w) (X.eX a) = 0 := by
    intro a
    have h := (VS D).herm.eq (X.eX a) (X.zu w)
    rw [(X.zu_orth w a).1] at h
    simpa using h.symm
  ext a b
  simp only [TFv, Matrix.map_apply, Matrix.diagonal_apply, gramE]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, hE_crdOf, X.zu_norm, Tw]
    | cast j => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, Fin.snoc_castSucc, hE_crdOf, hze, Ne.symm (Fin.castSucc_ne_last j)]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, Fin.snoc_castSucc, hE_crdOf, (X.zu_orth w i).1, Fin.castSucc_ne_last]
    | cast j => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_castSucc, hE_crdOf, X.ee, Fin.castSucc_ne_last]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem herm : HermProp := by
  intro D X w v
  rw [diag X w v]
  intro a b
  by_cases h : a = b
  · subst h
    simp only [Matrix.diagonal_apply_eq]
    split_ifs <;> simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

A detailed English derivation is pending.
-/
theorem integral : IntProp := by
  intro D X u u' v _ hdiv i j
  rw [diag X u' v, diag X u v]
  by_cases h : i = j ∧ i = Fin.last D.R.rS
  · obtain ⟨rfl, rfl⟩ := h
    obtain ⟨k, hk⟩ := hdiv
    simp only [Matrix.diagonal_apply_eq, if_true]
    letI : CharZero (Fv X.B.I.F v) := charZero_of_injective_algebraMap (algebraMap X.B.I.F (Fv X.B.I.F v)).injective
    have hg : ((gAt X v : ℕ) : Fv X.B.I.F v) ≠ 0 := Nat.cast_ne_zero.2 (gAt_prime X v).ne_zero
    have hA : ((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - ((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) =
        ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * (k : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := by
      have := congrArg (Int.cast : ℤ → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) hk
      push_cast at this
      exact this
    have hs : ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) *
        sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ = 1 := by
      rw [show sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ =
          Algebra.TensorProduct.includeLeftRingHom (R := X.B.I.F) (B := X.B.I.E) ((gAt X v : Fv X.B.I.F v))⁻¹ from rfl,
        ← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := X.B.I.F) (A := Fv X.B.I.F v) (B := X.B.I.E)),
        ← map_mul, mul_inv_cancel₀ hg, map_one]
    have e1 : (-((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - -((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) *
        sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ = inclR (Fv X.B.I.F v) ((k : 𝓞 X.B.I.E) : X.B.I.E) := by
      rw [show -((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - -((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) =
          ((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - ((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) by ring,
        hA, mul_comm ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E), mul_assoc, hs, mul_one]
      simp
    rw [e1]
    unfold OEv
    exact Submodule.subset_span ⟨(k : 𝓞 X.B.I.E), Set.mem_univ _, rfl⟩
  · have h0 : ∀ d : Fin (D.R.rS + 1) → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, (∀ l, l ≠ Fin.last D.R.rS → d l = 0) →
        Matrix.diagonal d i j = 0 := by
      intro d hd
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq]; exact hd _ (fun h' => h ⟨rfl, h'⟩)
      · exact Matrix.diagonal_apply_ne _ hij
    rw [h0 _ (fun l hl => if_neg hl), h0 _ (fun l hl => if_neg hl), sub_zero, zero_mul]
    unfold OEv
    exact Submodule.zero_mem _

end Formalism.L2.SG.LocVol.LJP
