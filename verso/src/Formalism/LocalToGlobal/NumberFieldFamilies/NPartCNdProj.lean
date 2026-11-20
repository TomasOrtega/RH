import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNdTie

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Module Module.End Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace Formalism.L2.Fam.NPC

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

section Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂)

/- English proof (translation)
Apply `(mtEquiv B hC hL i).injective` to reduce the goal to its premises. Establish `e1 : mtEquiv B hC hL i (prMtC B hC hL i x) = projOf B hC i (B.iV (jOf B i) (wOf B i) x)`. Simplify using `[prMtC]`. Rewrite using `[e1, TensorProduct.mk_apply]`. Unfold `mtEquiv`.

Rewrite using `[IsBaseChange.equiv_tmul, one_smul]`. Both sides reduce to the same expression.
-/
theorem prMtC_lat (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) (x : what₂.MtL (what₂.muTw (wOf B i)) (jOf B i))
    (hx : x ∈ latL B i) :
    prMtC B hC hL i x = TensorProduct.mk (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) 1
      ⟨projOf B hC i (B.iV (jOf B i) (wOf B i) x), Submodule.subset_span ⟨x, hx, rfl⟩⟩ := by
  apply (mtEquiv B hC hL i).injective
  have e1 : mtEquiv B hC hL i (prMtC B hC hL i x) = projOf B hC i (B.iV (jOf B i) (wOf B i) x) := by
    simp [prMtC]
  rw [e1, TensorProduct.mk_apply]
  unfold mtEquiv
  rw [IsBaseChange.equiv_tmul, one_smul]
  rfl

/- English proof (translation)
Use `set G : Set (partOf B i) := (fun x => projOf B hC i (B.iV (jOf B i) (wOf B i) x)) '' latL B i with hG`. Establish `e : prMtC B hC hL i '' latL B i = (TensorProduct.mk (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) 1) '' ((↑) ⁻¹' G : Set (MtSub B hC i))`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Conclude with `⟨_, ⟨x, hx, rfl⟩, (prMtC_lat B hC hL i x hx).symm⟩`. Introduce and unpack `⟨m, ⟨x, hx, hmx⟩, rfl⟩`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[prMtC_lat B hC hL i x hx]`. Use `congr 1`.

Conclude with `Subtype.ext hmx`. Establish `htop : Submodule.span (OOf B i) ((↑) ⁻¹' G : Set (MtSub B hC i)) = ⊤` using `Submodule.span_span_coe_preimage`. Rewrite using `[e, Submodule.span_image, htop, Submodule.map_top]`.
-/
theorem prMtC_latSpan (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) :
    Submodule.span (OOf B i) (prMtC B hC hL i '' latL B i) =
      LinearMap.range (TensorProduct.mk (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) 1) := by
  set G : Set (partOf B i) := (fun x => projOf B hC i (B.iV (jOf B i) (wOf B i) x)) '' latL B i with hG
  have e : prMtC B hC hL i '' latL B i =
      (TensorProduct.mk (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) 1) '' ((↑) ⁻¹' G : Set (MtSub B hC i)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, (prMtC_lat B hC hL i x hx).symm⟩
    · rintro ⟨m, ⟨x, hx, hmx⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      rw [prMtC_lat B hC hL i x hx]
      congr 1
      exact Subtype.ext hmx
  have htop : Submodule.span (OOf B i) ((↑) ⁻¹' G : Set (MtSub B hC i)) = ⊤ := Submodule.span_span_coe_preimage
  rw [e, Submodule.span_image, htop, Submodule.map_top]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis what₂.LL (what₂.MtL (what₂.muTw (wOf B i)) (jOf B i))`. Establish `hb` using `(B.iV_basis (jOf B i) (wOf B i) b).2`. Establish `h1 : Submodule.span (FractionRing (OOf B i)) (Set.range (B.iV (jOf B i) (wOf B i))) = ⊤` using `eq_top_iff.2 (hb ▸ Submodule.span_mono (Set.range_comp_subset_range b (B.iV (jOf B i) (wOf B i))))`. Establish `h2 : Set.range (prMtC B hC hL i) = (mtEquiv B hC hL i).symm.toLinearMap '' (projOf B hC i '' Set.range (B.iV (jOf B i) (wOf B i)))`. Use extensionality with `z`.

Simplify using `[prMtC]`. Establish `h3 : LinearMap.range (projOf B hC i) = ⊤` using `Submodule.linearProjOfIsCompl_range (hC i)`. Rewrite using `[h2, Submodule.span_image, Submodule.span_image, h1, Submodule.map_top, h3, Submodule.map_top, LinearMap.range_eq_top.2 (mtEquiv B hC hL i).symm.surjective]`.
-/
theorem prMtC_span (hC : PartCompl B) (hL : MtLoc B hC) (i : LocT B) :
    Submodule.span (FractionRing (OOf B i)) (Set.range (prMtC B hC hL i)) = ⊤ := by
  let b := Module.Free.chooseBasis what₂.LL (what₂.MtL (what₂.muTw (wOf B i)) (jOf B i))
  have hb := (B.iV_basis (jOf B i) (wOf B i) b).2
  have h1 : Submodule.span (FractionRing (OOf B i)) (Set.range (B.iV (jOf B i) (wOf B i))) = ⊤ :=
    eq_top_iff.2 (hb ▸ Submodule.span_mono (Set.range_comp_subset_range b (B.iV (jOf B i) (wOf B i))))
  have h2 : Set.range (prMtC B hC hL i) =
      (mtEquiv B hC hL i).symm.toLinearMap '' (projOf B hC i '' Set.range (B.iV (jOf B i) (wOf B i))) := by
    ext z
    simp [prMtC]
  have h3 : LinearMap.range (projOf B hC i) = ⊤ := Submodule.linearProjOfIsCompl_range (hC i)
  rw [h2, Submodule.span_image, Submodule.span_image, h1, Submodule.map_top, h3, Submodule.map_top,
    LinearMap.range_eq_top.2 (mtEquiv B hC hL i).symm.surjective]

end Gen

end Formalism.L2.Fam.NPC
