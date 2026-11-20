import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalleyStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleToMatrixIffIsSemisimpleRepresStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGroupHomRangeEqOfAutStableStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleMatrixSetTransposeImageStatement

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `hm : ∀ g : G, LinearMap.toMatrix (Pi.basisFun ℂ (Fin 0 → ι)) (Pi.basisFun ℂ (Fin 0 → ι)) (Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g) = 1`. Introduce `g`. Establish `: Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g = LinearMap.id`.

Use extensionality with `v`. Simplify using the standard rewrite rules. Rewrite using `[this, LinearMap.toMatrix_id]`. Use `⟨(Fin 0 → ι) → ℂ, inferInstance, inferInstance, Representation.trivial ℂ G _, Pi.basisFun ℂ _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation (Fin 0 → ι) G _ _ (Pi.basisFun ℂ _)]`.

Introduce `W _`. Take `⟨W', hW'⟩` from `Submodule.exists_isCompl W`. Use `⟨W', ?_, hW'⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩ v hv`. Simplify `hv` using `only [hm, Matrix.one_mulVec]`.

Introduce `g`. Rewrite using `[hm]`. Use extensionality with `a b`. Establish `: a = b` using `Subsingleton.elim _ _`. Substitute `this` using the available equality.

Simplify using `[tpow]`. Consider the case `succ n ih`. Take `⟨V, _, _, r, b, hr, hb⟩` from `ih`. Set `r₁ : Representation ℂ G (ι → ℂ)` to `(Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)).toAlgHom.toMonoidHom.comp ρ`. Establish `h₁ : ∀ g, LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (r₁ g) = ρ g`.

Introduce `g`. Express the relevant statement in the definitionally equal form `LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (Matrix.toLin' (ρ g)) = ρ g`. Rewrite using `[LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']`. Establish `hs₁ : r₁.IsSemisimpleRepresentation`. Rewrite using `[← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation ι G _ _ (Pi.basisFun ℂ _)]`.

Simplify `h` using `only [h₁]`. Use `haveI : FiniteDimensional ℂ V := Module.Finite.of_basis b`. Set `e : ι × (Fin n → ι) ≃ (Fin (n + 1) → ι)` to `Fin.consEquiv fun _ => ι`. Use `⟨(ι → ℂ) ⊗[ℂ] V, inferInstance, inferInstance, r₁.tprod r, ((Pi.basisFun ℂ ι).tensorProduct b).reindex e, GlobalTheory.T.isSemisimpleRepresentation_tprod_chevalley G _ r₁ V r hs₁ hr, ?_⟩` and prove the remaining obligations. Introduce `g`.

Establish `ht : LinearMap.toMatrix ((Pi.basisFun ℂ ι).tensorProduct b) ((Pi.basisFun ℂ ι).tensorProduct b) ((r₁.tprod r) g) = ρ g ⊗ₖ tpow n (ρ g)`. Rewrite using `[Representation.tprod_apply, TensorProduct.toMatrix_map, h₁, hb]`. Use extensionality with `a c`. Use `congrFun (congrFun ht (e.symm a)) (e.symm c)` as an intermediate fact. Rewrite `this`, the goal using `[LinearMap.toMatrix_apply]`.

Rewrite using `[Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, this]`. Simplify using `[e, tpow, Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]`.
-/
theorem exists_semisimple_rep_tpow {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]
    (ρ : G →* Matrix ι ι ℂ) (h : SS (Set.range ρ)) (n : ℕ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (r : Representation ℂ G V)
      (b : Module.Basis (Fin n → ι) ℂ V),
      r.IsSemisimpleRepresentation ∧ ∀ g, LinearMap.toMatrix b b (r g) = tpow n (ρ g) := by
  induction n with
  | zero =>
    have hm : ∀ g : G, LinearMap.toMatrix (Pi.basisFun ℂ (Fin 0 → ι)) (Pi.basisFun ℂ (Fin 0 → ι))
        (Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g) = 1 := by
      intro g
      have : Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g = LinearMap.id := by
        ext v; simp
      rw [this, LinearMap.toMatrix_id]
    refine ⟨(Fin 0 → ι) → ℂ, inferInstance, inferInstance, Representation.trivial ℂ G _,
      Pi.basisFun ℂ _, ?_, ?_⟩
    · rw [← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation (Fin 0 → ι) G _ _ (Pi.basisFun ℂ _)]
      intro W _
      obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
      refine ⟨W', ?_, hW'⟩
      rintro _ ⟨g, rfl⟩ v hv
      simpa only [hm, Matrix.one_mulVec] using hv
    · intro g
      rw [hm]
      ext a b
      have : a = b := Subsingleton.elim _ _
      subst this
      simp [tpow]
  | succ n ih =>
    obtain ⟨V, _, _, r, b, hr, hb⟩ := ih
    let r₁ : Representation ℂ G (ι → ℂ) :=
      (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)).toAlgHom.toMonoidHom.comp ρ
    have h₁ : ∀ g, LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (r₁ g) = ρ g := by
      intro g
      change LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (Matrix.toLin' (ρ g)) = ρ g
      rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    have hs₁ : r₁.IsSemisimpleRepresentation := by
      rw [← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation ι G _ _ (Pi.basisFun ℂ _)]
      simpa only [h₁] using h
    haveI : FiniteDimensional ℂ V := Module.Finite.of_basis b
    let e : ι × (Fin n → ι) ≃ (Fin (n + 1) → ι) := Fin.consEquiv fun _ => ι
    refine ⟨(ι → ℂ) ⊗[ℂ] V, inferInstance, inferInstance, r₁.tprod r,
      ((Pi.basisFun ℂ ι).tensorProduct b).reindex e,
      GlobalTheory.T.isSemisimpleRepresentation_tprod_chevalley G _ r₁ V r hs₁ hr, ?_⟩
    intro g
    have ht : LinearMap.toMatrix ((Pi.basisFun ℂ ι).tensorProduct b) ((Pi.basisFun ℂ ι).tensorProduct b)
        ((r₁.tprod r) g) = ρ g ⊗ₖ tpow n (ρ g) := by
      rw [Representation.tprod_apply, TensorProduct.toMatrix_map, h₁, hb]
    ext a c
    have := congrFun (congrFun ht (e.symm a)) (e.symm c)
    rw [LinearMap.toMatrix_apply] at this ⊢
    rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, this]
    simp [e, tpow, Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]

/- English proof (translation)
Introduce `ι _ _ Γ hΓ hs n`. Take `⟨G, _, ρ, rfl⟩` from `GlobalTheory.T.exists_group_hom_range_eq_of_isPre ι Γ hΓ`. Take `⟨V, _, _, r, b, hr, hb⟩` from `exists_semisimple_rep_tpow ρ hs n`. Establish `h` using `GlobalTheory.T.isCompletelyReducibleMatrixSet_transpose_image _ _ ((GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation _ G V r b).2 hr)`. Simplify using `only [hb] at h`.

Rewrite `h`, the goal using `[← Set.range_comp]`. Conclude with `h`.
-/
theorem ss_tpow_transpose : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)),
    IsPre Γ → SS Γ → ∀ n : ℕ, SS ((fun g => (tpow n g)ᵀ) '' Γ) := by
  intro ι _ _ Γ hΓ hs n
  obtain ⟨G, _, ρ, rfl⟩ := GlobalTheory.T.exists_group_hom_range_eq_of_isPre ι Γ hΓ
  obtain ⟨V, _, _, r, b, hr, hb⟩ := exists_semisimple_rep_tpow ρ hs n
  have h := GlobalTheory.T.isCompletelyReducibleMatrixSet_transpose_image _ _ ((GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation _ G V r b).2 hr)
  simp only [hb] at h
  rw [← Set.range_comp] at h ⊢
  exact h

end GlobalTheory.ClassFin
