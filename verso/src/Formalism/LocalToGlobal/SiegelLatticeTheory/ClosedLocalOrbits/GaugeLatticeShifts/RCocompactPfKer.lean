import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfStmt

namespace Formalism.L2.SG.Pf.RCoc

/- English proof (translation)
Introduce `K L _ _ f m p _ _ _ A`. Use `set T : (p → K) →ₗ[K] (m → K) := Matrix.toLin' A with hT`. Take `⟨C, hC⟩` from `Submodule.exists_isCompl (LinearMap.ker T)`. Establish `hinj : LinearMap.ker (T ∘ₗ C.subtype) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`.

Introduce `c hc`. Establish `hk : (c : p → K) ∈ LinearMap.ker T` using `hc`. Establish `hm : (c : p → K) ∈ LinearMap.ker T ⊓ C` using `⟨hk, c.2⟩`. Rewrite `hm` using `[hC.inf_eq_bot, Submodule.mem_bot]`. Conclude with `Subtype.ext hm`.

Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (T ∘ₗ C.subtype) hinj`. Establish `hTQT : ∀ v : p → K, T (C.subtype (g (T v))) = T v`. Introduce `v`. Establish `hv : v ∈ LinearMap.ker T ⊔ C` using `by rw [hC.sup_eq_top]; trivial`. Take `⟨k, hk, c, hc, rfl⟩` from `Submodule.mem_sup.1 hv`.

Establish `hk0 : T k = 0` using `hk`. Establish `e : g (T (k + c)) = ⟨c, hc⟩`. Rewrite using `[map_add, hk0, zero_add]`. Conclude with `LinearMap.congr_fun hg ⟨c, hc⟩`. Rewrite using `[e, map_add, hk0, zero_add]`.

Both sides reduce to the same expression. Use `set Q : Matrix p m K := LinearMap.toMatrix' (C.subtype ∘ₗ g) with hQ`. Establish `hAQA : A * Q * A = A`. Establish `hcomp : T ∘ₗ (C.subtype ∘ₗ g) ∘ₗ T = T` using `LinearMap.ext hTQT`. Establish `h` using `congrArg LinearMap.toMatrix' hcomp`.

Rewrite `h` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hT, LinearMap.toMatrix'_toLin', ← hQ, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Use `⟨1 - Q * A, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hAQA, sub_self]`. Introduce `z hz`. Establish `e : (1 - Q * A).map f = 1 - Q.map f * A.map f`.

Establish `h` using `(f.mapMatrix (m := p)).map_sub 1 (Q * A)`. Rewrite `h` using `[map_one]`. Simplify using `only [RingHom.mapMatrix_apply] at h`. Rewrite using `[h, Matrix.map_mul]`. Rewrite using `[e, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, sub_zero]`.
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
