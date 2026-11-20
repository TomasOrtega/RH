import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FlatMul

variable {T : Scheme.{0}}

/- English proof (translation)
Use `(IsPullback.of_right (h₁₁ := (q ▷ Y).left) (v₁₁ := pullback.fst V.hom Y.hom) (h₂₁ := q.left) (v₁₂ := pullback.fst H.hom Y.hom) ?_ (Over.whiskerRight_left_fst q) (IsPullback.of_hasPullback H.hom Y.hom).flip).flip` and prove the remaining obligations. Rewrite using `[Over.whiskerRight_left_snd, Over.w]`. Conclude with `(IsPullback.of_hasPullback V.hom Y.hom).flip`.
-/
theorem whiskerRight_pb {H V : Over T} (q : V ⟶ H) (Y : Over T) :
    IsPullback (pullback.fst V.hom Y.hom) (q ▷ Y).left q.left (pullback.fst H.hom Y.hom) := by
  refine (IsPullback.of_right (h₁₁ := (q ▷ Y).left) (v₁₁ := pullback.fst V.hom Y.hom)
    (h₂₁ := q.left) (v₁₂ := pullback.fst H.hom Y.hom) ?_ (Over.whiskerRight_left_fst q)
    (IsPullback.of_hasPullback H.hom Y.hom).flip).flip
  rw [Over.whiskerRight_left_snd, Over.w]
  exact (IsPullback.of_hasPullback V.hom Y.hom).flip

/- English proof (translation)
Establish `: IsPullback (snd X A) (X ◁ q) q (snd X B)`. Use `⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst X B) s.fst) (fun s => by simp) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩` and prove the remaining obligations. Use `ext1`. Simplify using the standard rewrite rules. Simplify using `[s.condition]`.

Use `ext1`. Simplify using `[← h₂]`. Simplify using `[← h₁]`. Conclude with `this.map (Over.forget T)`.
-/
theorem whiskerLeft_pb (X : Over T) {A B : Over T} (q : A ⟶ B) :
    IsPullback (snd X A).left (X ◁ q).left q.left (snd X B).left := by
  have : IsPullback (snd X A) (X ◁ q) q (snd X B) := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst X B) s.fst)
      (fun s => by simp) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩
    · ext1
      · simp
      · simp [s.condition]
    · ext1
      · simp [← h₂]
      · simp [← h₁]
  exact this.map (Over.forget T)

/- English proof (translation)
Use `⟨⟨lift (fst H H * (snd H H)⁻¹) (snd H H), ?_, ?_⟩⟩` and prove the remaining obligations. Establish `hμ : μ[H] = fst H H * snd H H` using `by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]`. Apply `hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, lift_fst, comp_mul, lift_fst, GrpObj.comp_inv, lift_snd, hμ, mul_inv_cancel_right, Category.id_comp]`. Rewrite using `[Category.assoc, lift_snd, lift_snd, Category.id_comp]`.

Establish `hμ : μ[H] = fst H H * snd H H` using `by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]`. Apply `hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, lift_fst, hμ, comp_mul, lift_fst, lift_snd, inv_mul_cancel_right, Category.id_comp]`. Rewrite using `[Category.assoc, lift_snd, lift_snd, Category.id_comp]`.
-/
theorem isIso_shear (H : Over T) [GrpObj H] : IsIso (lift μ[H] (snd H H)) := by
  refine ⟨⟨lift (fst H H * (snd H H)⁻¹) (snd H H), ?_, ?_⟩⟩
  · have hμ : μ[H] = fst H H * snd H H := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    apply hom_ext
    · rw [Category.assoc, lift_fst, comp_mul, lift_fst, GrpObj.comp_inv, lift_snd, hμ, mul_inv_cancel_right,
        Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]
  · have hμ : μ[H] = fst H H * snd H H := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    apply hom_ext
    · rw [Category.assoc, lift_fst, hμ, comp_mul, lift_fst, lift_snd, inv_mul_cancel_right, Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]

/- English proof (translation)
Establish `e : μ[H] = lift μ[H] (snd H H) ≫ fst H H` using `by rw [lift_fst]`. Use `isIso_shear H` as an intermediate fact. Establish `: IsIso (lift μ[H] (snd H H)).left` using `(Over.forget T).map_isIso (lift μ[H] (snd H H))`. Establish `hfst : Flat (fst H H).left`. Establish `h1 : (fst H H).left = pullback.fst H.hom H.hom` using `by simp`.

Rewrite using `[h1]`. Conclude with `MorphismProperty.of_isPullback (IsPullback.of_hasPullback H.hom H.hom).flip hH`. Rewrite using `[e, Over.comp_left]`. Use `infer_instance`.
-/
theorem flat_mu (H : Over T) [GrpObj H] (hH : Flat H.hom) : Flat μ[H].left := by
  have e : μ[H] = lift μ[H] (snd H H) ≫ fst H H := by rw [lift_fst]
  have := isIso_shear H
  have : IsIso (lift μ[H] (snd H H)).left := (Over.forget T).map_isIso (lift μ[H] (snd H H))
  have hfst : Flat (fst H H).left := by
    have h1 : (fst H H).left = pullback.fst H.hom H.hom := by simp
    rw [h1]
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback H.hom H.hom).flip hH
  rw [e, Over.comp_left]
  infer_instance

/- English proof (translation)
Introduce `T H V _ e he hH`. Establish `h1 : Flat (e ▷ V).left` using `MorphismProperty.of_isPullback (whiskerRight_pb e V) (inferInstance : Flat e.left)`. Establish `h2 : Flat (H ◁ e).left` using `MorphismProperty.of_isPullback (whiskerLeft_pb H e) (inferInstance : Flat e.left)`. Establish `h3` using `flat_mu H hH`. Establish `k : (fst V V ≫ e) * (snd V V ≫ e) = ((e ▷ V) ≫ (H ◁ e)) ≫ μ[H]`.

Rewrite using `[Hom.mul_def]`. Use `congr 1`. Apply the tactic sequence `apply hom_ext <;> simp`. Rewrite using `[k, Over.comp_left, Over.comp_left]`. Use `infer_instance`.
-/
theorem main : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Flat H.hom →
    Flat ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  intro T H V _ e he hH
  have h1 : Flat (e ▷ V).left := MorphismProperty.of_isPullback (whiskerRight_pb e V)
    (inferInstance : Flat e.left)
  have h2 : Flat (H ◁ e).left := MorphismProperty.of_isPullback (whiskerLeft_pb H e)
    (inferInstance : Flat e.left)
  have h3 := flat_mu H hH
  have k : (fst V V ≫ e) * (snd V V ≫ e) = ((e ▷ V) ≫ (H ◁ e)) ≫ μ[H] := by
    rw [Hom.mul_def]
    congr 1
    apply hom_ext <;> simp
  rw [k, Over.comp_left, Over.comp_left]
  infer_instance

end GlobalTheory.Mum.FlatMul
