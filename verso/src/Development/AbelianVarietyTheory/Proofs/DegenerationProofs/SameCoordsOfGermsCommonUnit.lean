import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem toStk_valR_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valR x U a) = gs x z U a := by
  rw [valR, dif_pos ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem toStk_surjective {F : Type} [Field F] (y : Sp F) : Function.Surjective (toStk y) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp F).presheaf.exists_germ_eq s
  obtain rfl : U = ⊤ := top_le_iff.1 ((top_le_iff_mem (𝟙 (Sp F)) U y).2 hU)
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom a, by simp [toStk]⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem crd_of_germs_unit : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (H : LB X) (H' : LB Y), H'.IsLB → ∀ (J : Type) (F : J → H.Sec) (σ : J → H'.Sec) (x : Sp k ⟶ X) (y : Sp k ⟶ Y), (∀ (z : Sp k) (l : H.ι) (l' : H'.ι), x z ∈ H.U l → y z ∈ H'.U l' → ∃ u : ((Sp k).presheaf.stalk z)ˣ, ∀ i, gs x z (H.U l) ((F i).f l) = u.val * gs y z (H'.U l') ((σ i).f l')) → ∀ v : J → k, GlobalTheory.ZH.Crd H F x v → GlobalTheory.ZH.Crd H' σ y v := by
  intro k _ X Y H H' hH' J F σ x y h v ⟨l, c, hl, hv⟩
  let z : Sp k := (⊥ : PrimeSpectrum k)
  obtain ⟨l', hl'⟩ := exists_chart hH' (y z)
  have hx := (top_le_iff_mem x _ z).1 hl
  obtain ⟨u, hu⟩ := h z l l' hx hl'
  obtain ⟨f, hf⟩ := toStk_surjective z u.val
  have f0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact u.ne_zero hf.symm
  refine ⟨l', c * Units.mk0 f f0, (top_le_iff_mem y _ z).2 hl', fun j => ?_⟩
  rw [hv j, Units.val_mul, Units.val_mk0, _root_.mul_assoc]
  congr 1
  apply (toStk z).injective
  rw [map_mul, toStk_valR_gs x _ z hx, toStk_valR_gs y _ z hl', hf, hu j]

end GlobalTheory.ZH.UFib
end
