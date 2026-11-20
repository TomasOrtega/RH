import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfStmt

namespace Formalism.L2.SG.Pf.RCoc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem kerBaseChange_holds : KerBaseChange := by
  intro K L _ _ f m p _ _ _ A
  classical
  set T : (p → K) →ₗ[K] (m → K) := Matrix.toLin' A with hT
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker T)
  have hinj : LinearMap.ker (T ∘ₗ C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have hk : (c : p → K) ∈ LinearMap.ker T := hc
    have hm : (c : p → K) ∈ LinearMap.ker T ⊓ C := ⟨hk, c.2⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hm
    exact Subtype.ext hm
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (T ∘ₗ C.subtype) hinj
  have hTQT : ∀ v : p → K, T (C.subtype (g (T v))) = T v := by
    intro v
    have hv : v ∈ LinearMap.ker T ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨k, hk, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    have hk0 : T k = 0 := hk
    have e : g (T (k + c)) = ⟨c, hc⟩ := by
      rw [map_add, hk0, zero_add]
      exact LinearMap.congr_fun hg ⟨c, hc⟩
    rw [e, map_add, hk0, zero_add]
    rfl
  set Q : Matrix p m K := LinearMap.toMatrix' (C.subtype ∘ₗ g) with hQ
  have hAQA : A * Q * A = A := by
    have hcomp : T ∘ₗ (C.subtype ∘ₗ g) ∘ₗ T = T := LinearMap.ext hTQT
    have h := congrArg LinearMap.toMatrix' hcomp
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hT, LinearMap.toMatrix'_toLin', ← hQ,
      ← Matrix.mul_assoc] at h
  refine ⟨1 - Q * A, ?_, ?_⟩
  · rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hAQA, sub_self]
  · intro z hz
    have e : (1 - Q * A).map f = 1 - Q.map f * A.map f := by
      have h := (f.mapMatrix (m := p)).map_sub 1 (Q * A)
      rw [map_one] at h
      simp only [RingHom.mapMatrix_apply] at h
      rw [h, Matrix.map_mul]
    rw [e, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, sub_zero]

end Formalism.L2.SG.Pf.RCoc
