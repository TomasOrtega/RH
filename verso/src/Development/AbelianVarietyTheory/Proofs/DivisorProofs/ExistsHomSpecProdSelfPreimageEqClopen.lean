import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEqOfBasicOpenEq
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn

namespace GlobalTheory

/- English proof (translation)
Introduce `O _ T p U hU`. Take `⟨ε, he, hεU⟩` from `exists_idempotent_basicOpen_eq_of_isClopen T U hU`. Set `φ : O →+* Γ(T, ⊤)` to `((Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop).hom`. Set `ψ : O × O →+* Γ(T, ⊤)` to `{ toFun := fun x => φ x.1 * ε + φ x.2 * (1 - ε) map_one' := by simp map_mul' := fun x y => by`. Simplify using `only [Prod.fst_mul, Prod.snd_mul, map_mul]`.

Take the linear combination `-(φ x.1 * φ y.1 - φ x.1 * φ y.2 - φ x.2 * φ y.1 + φ x.2 * φ y.2) * he`. Use the proof step `map_zero' := by simp`. Use the proof step `map_add' := fun x y => by`. Simplify using `only [Prod.fst_add, Prod.snd_add, map_add]`. Use `ring }`.

Establish `hψ : ψ.comp (algebraMap O (O × O)) = φ`. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `φ a * ε + φ a * (1 - ε) = φ a`. Expand and normalize the polynomial expressions, which then agree. Use `⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩` and prove the remaining obligations.

Establish `: CommRingCat.ofHom φ = (Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop` using `rfl`. Rewrite using `[Category.assoc, twoπ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, this, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]`. Rewrite using `[Scheme.preimage_basicOpen_top, ← hεU]`. Use `congr 2`. Establish `h1 : (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)).appTop (fst1 O) = ψ ((1, 0) : O × O)`.

Rewrite using `[Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.toSpecΓ_appTop]`. Use `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)` as an intermediate fact. Establish `h2` using `congrArg (fun f => f.hom (fst1 O)) this`. Simplify using `only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h2`. Use `h2.trans ?_` and prove the remaining obligations.

Simplify using `[fst1]`. Rewrite using `[h1]`. Express the relevant statement in the definitionally equal form `φ 1 * ε + φ 0 * (1 - ε) = ε`. Simplify using the standard rewrite rules.
-/
theorem exists_hom_spec_prod_self_preimage_eq_clopen :
    ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (p : T ⟶ Spec (.of O)) (U : Set T), IsClopen U →
      ∃ h : T ⟶ Spec (.of (O × O)), h ≫ twoπ O = p ∧
        ((h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : T.Opens) : Set T) = U := by
  intro O _ T p U hU
  obtain ⟨ε, he, hεU⟩ := exists_idempotent_basicOpen_eq_of_isClopen T U hU
  let φ : O →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop).hom
  let ψ : O × O →+* Γ(T, ⊤) :=
    { toFun := fun x => φ x.1 * ε + φ x.2 * (1 - ε)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination -(φ x.1 * φ y.1 - φ x.1 * φ y.2 - φ x.2 * φ y.1 + φ x.2 * φ y.2) * he
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        ring }
  have hψ : ψ.comp (algebraMap O (O × O)) = φ := by
    ext a
    change φ a * ε + φ a * (1 - ε) = φ a
    ring
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · have : CommRingCat.ofHom φ = (Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop := rfl
    rw [Category.assoc, twoπ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, this, Spec.map_comp,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  · rw [Scheme.preimage_basicOpen_top, ← hεU]
    congr 2
    have h1 : (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)).appTop (fst1 O) = ψ ((1, 0) : O × O) := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.toSpecΓ_appTop]
      have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
      have h2 := congrArg (fun f => f.hom (fst1 O)) this
      simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h2
      refine h2.trans ?_
      simp [fst1]
    rw [h1]
    change φ 1 * ε + φ 0 * (1 - ε) = ε
    simp

end GlobalTheory
