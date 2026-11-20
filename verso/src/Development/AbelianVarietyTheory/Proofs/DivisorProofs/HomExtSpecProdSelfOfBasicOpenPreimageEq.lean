import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEqOfBasicOpenEq
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlgConn

/- English proof (translation)
Rewrite using `[Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]`.
-/
theorem hom_eq_toSpecΓ_comp {T : Scheme.{0}} {A : CommRingCat.{0}} (h : T ⟶ Spec A) :
    h = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ h.appTop) := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/- English proof (translation)
Introduce `O _ T h h' hπ hb`. Rewrite using `[hom_eq_toSpecΓ_comp h, hom_eq_toSpecΓ_comp h']`. Use `congr 2`. Establish `h1 : ∀ a : O, ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom (algebraMap O (O × O) a) = ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom (algebraMap O (O × O) a)`. Introduce `a`.

Establish `key : ∀ g : T ⟶ Spec (.of (O × O)), ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ g.appTop).hom (algebraMap O (O × O) a) = ((Scheme.ΓSpecIso (.of O)).inv ≫ (g ≫ twoπ O).appTop).hom a`. Introduce `g`. Rewrite using `[Scheme.Hom.comp_appTop, ← Category.assoc]`. Establish `n` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O (O × O)))`. Establish `n' : CommRingCat.ofHom (algebraMap O (O × O)) ≫ (Scheme.ΓSpecIso (.of (O × O))).inv = (Scheme.ΓSpecIso (.of O)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap O (O × O)))).appTop`.

Rewrite using `[Iso.eq_inv_comp, ← Category.assoc, ← n, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Rewrite using `[← n']`. Both sides reduce to the same expression. Rewrite using `[key h, key h', hπ]`. Establish `h2 : ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom ((1, 0) : O × O) = ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom ((1, 0) : O × O)`.

Express the relevant statement in the definitionally equal form `h.appTop (fst1 O) = h'.appTop (fst1 O)`. Establish `hid : fst1 O * fst1 O = fst1 O`. Apply the tactic sequence `rw [fst1, ← map_mul]; congr 1; ext <;> simp`. Apply `GlobalTheory.idempotent_eq_of_basicOpen_eq T` to reduce the goal to its premises. Rewrite using `[← map_mul, hid]`.

Rewrite using `[← map_mul, hid]`. Rewrite using `[← Scheme.preimage_basicOpen_top, ← Scheme.preimage_basicOpen_top, hb]`. Use `ext1`. Use extensionality with `x`. Take `⟨a, b⟩` from `x`.

Establish `hx : ((a, b) : O × O) = algebraMap O (O × O) a * (1, 0) + algebraMap O (O × O) b * (1 - (1, 0))`. Apply the tactic sequence `ext <;> simp`. Rewrite using `[hx, map_add, map_mul, map_mul, map_sub, map_one, map_add, map_mul, map_mul, map_sub, map_one, h1 a, h1 b, h2]`.
-/
theorem hom_ext_of_twoπ_of_basicOpen : ∀ (O : Type) [CommRing O] (T : Scheme.{0})
    (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O →
    h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) →
    h = h' := by
  intro O _ T h h' hπ hb
  rw [hom_eq_toSpecΓ_comp h, hom_eq_toSpecΓ_comp h']
  congr 2

  have h1 : ∀ a : O, ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom (algebraMap O (O × O) a) =
      ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom (algebraMap O (O × O) a) := by
    intro a
    have key : ∀ g : T ⟶ Spec (.of (O × O)),
        ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ g.appTop).hom (algebraMap O (O × O) a) =
          ((Scheme.ΓSpecIso (.of O)).inv ≫ (g ≫ twoπ O).appTop).hom a := by
      intro g
      rw [Scheme.Hom.comp_appTop, ← Category.assoc]
      have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O (O × O)))
      have n' : CommRingCat.ofHom (algebraMap O (O × O)) ≫ (Scheme.ΓSpecIso (.of (O × O))).inv =
          (Scheme.ΓSpecIso (.of O)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap O (O × O)))).appTop := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← n']
      rfl
    rw [key h, key h', hπ]

  have h2 : ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom ((1, 0) : O × O) =
      ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom ((1, 0) : O × O) := by
    change h.appTop (fst1 O) = h'.appTop (fst1 O)
    have hid : fst1 O * fst1 O = fst1 O := by
      rw [fst1, ← map_mul]; congr 1; ext <;> simp
    apply GlobalTheory.idempotent_eq_of_basicOpen_eq T
    · rw [← map_mul, hid]
    · rw [← map_mul, hid]
    · rw [← Scheme.preimage_basicOpen_top, ← Scheme.preimage_basicOpen_top, hb]

  ext1
  ext x
  obtain ⟨a, b⟩ := x
  have hx : ((a, b) : O × O) = algebraMap O (O × O) a * (1, 0) + algebraMap O (O × O) b * (1 - (1, 0)) := by
    ext <;> simp
  rw [hx, map_add, map_mul, map_mul, map_sub, map_one, map_add, map_mul, map_mul, map_sub, map_one, h1 a, h1 b, h2]

end GlobalTheory.AlgConn
