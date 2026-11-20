import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelSum

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo Ω _ _ x x' Ψ p n s s' β s₁ e hΨ _ hs' hβ hs Z r z J hJ`. Establish `hG` using `abelianSchemeLaws_all.1.globalFns`. Establish `hA` using `GlobalTheory.HeckePoint.isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper`. Take `⟨β', s₂, n', c, hβ', hs₂, hc, hv⟩` from `isThetaTrace_iff.1 hs'`. Take `rfl` from `hs.unique hG hA hs₂`.

Establish `hst : ∀ a ∈ transKer Xo.univ.t.G Ψ, a ≫ Xo.univ.t.act.act H.w0 ∈ transKer Xo.univ.t.G Ψ`. Introduce `a ha`. Use `Xo.univ.t.act.hom H.w0` as an intermediate fact. Use `(hΨ.2.2.2.1 _).1 ?_` and prove the remaining obligations. Establish `h1 : (lift (𝟙 (Over.mk x)) a).left ≫ Ψ = (lift (𝟙 (Over.mk x')) (1 : Over.mk x' ⟶ Xo.univ.t.G)).left` using `(hΨ.2.2.2.1 a).2 ha`.

Use `show (lift (𝟙 (Over.mk x)) (a ≫ Xo.univ.t.act.act H.w0)).left ≫ Ψ = (lift (𝟙 (Over.mk x')) (1 : Over.mk x' ⟶ Xo.univ.t.G)).left`. Rewrite using `[← lift_whiskerLeft, Over.comp_left, Category.assoc, hΨ.2.1.2.2 H.w0, reassoc_of% h1, ← Over.comp_left, lift_whiskerLeft, MonObj.one_comp]`. Set `Φ : (Over.mk x ⟶ Xo.univ.t.G) → Z.presheaf.stalk z` to `fun b => ((val β (r ≫ (translT Xo.univ.t.G b).left) z J)⁻¹).val * sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G b).left) z J`. Establish `hΦ : ∀ a ∈ transKer Xo.univ.t.G Ψ, a ^ p = 1 → ∀ b, Φ (a * b) = Φ b` using `fun a ha hp b => GlobalTheory.ThetaTransport.term_transl hΨ.2.1 hβ.2.1 hs hst r z hJ a ha hp b`. Establish `h1 : sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ i, Φ (c i)` using `(hv Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => by`.

Simplify using `only [Φ]`. Rewrite using `[hβ'.val_unique hG hA hβ _ z hJ])`. Establish `: Finite (transKer Xo.univ.t.G Ψ)` using `Finite.of_equiv _ e`. Use `letI := Fintype.ofFinite (transKer Xo.univ.t.G Ψ)`. Set `T` to `{a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1}`.

Establish `: Finite T` using `Finite.of_injective (fun q : T => (⟨q.1, q.2.1⟩ : transKer Xo.univ.t.G Ψ)) (fun a b h => Subtype.ext (congrArg (fun q : transKer Xo.univ.t.G Ψ => q.1) h))`. Use `letI := Fintype.ofFinite T`. Establish `bij : Function.Bijective fun q : T × Fin n' => (⟨q.1.1 * c q.2, (transKer Xo.univ.t.G Ψ).mul_mem q.1.2.1 (hc.1 _)⟩ : transKer Xo.univ.t.G Ψ)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, i⟩ ⟨b, j⟩ h`.

Establish `h' : a.1 * c i = b.1 * c j` using `congrArg Subtype.val h`. Take `rfl : i = j` from `(hc.2 _ ((transKer Xo.univ.t.G Ψ).mul_mem a.2.1 (hc.1 i))).unique (by simpa using a.2.2) (by rw [h']; simpa using b.2.2)`. Conclude with `Prod.ext (Subtype.ext (mul_right_cancel h')) rfl`. Introduce `d`. Take `⟨i, hi, -⟩` from `hc.2 d d.2`.

Conclude with `⟨(⟨d * (c i)⁻¹, (transKer Xo.univ.t.G Ψ).mul_mem d.2 ((transKer Xo.univ.t.G Ψ).inv_mem (hc.1 i)), hi⟩, i), Subtype.ext (by simp)⟩`. Establish `h2 : ∑ j, Φ (e j).1 = ∑ d : transKer Xo.univ.t.G Ψ, Φ d.1` using `Equiv.sum_comp e (fun d => Φ d.1)`. Establish `h3 : ∑ d : transKer Xo.univ.t.G Ψ, Φ d.1 = ∑ q : T × Fin n', Φ (q.1.1 * c q.2)` using `(Fintype.sum_bijective _ bij _ _ fun q => rfl).symm`. Establish `h4 : ∑ q : T × Fin n', Φ (q.1.1 * c q.2) = ∑ q : T × Fin n', Φ (c q.2)` using `Finset.sum_congr rfl fun q _ => hΦ _ q.1.2.1 q.1.2.2 _`. Use `show _ = ∑ j, Φ (e j).1`.

Rewrite using `[h2, h3, h4, Fintype.sum_prod_type]`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[h1, Nat.card_eq_fintype_card]`.
-/
theorem sum_ker_eq_card_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (p n : ℕ) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))) (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))) (e : Fin n ≃ transKer Xo.univ.t.G Ψ), IsHeckeIsog p (transKer Xo.univ.t.G Ψ) Ψ → IsThGen x' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s' → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ _ β → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → (Nat.card {a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1} : Z.presheaf.stalk z) * sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ j, ((val β (r ≫ (translT Xo.univ.t.G (e j).1).left) z J)⁻¹).val * sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G (e j).1).left) z J := by
  intro E _ _ _ H Dw l Xo Ω _ _ x x' Ψ p n s s' β s₁ e hΨ _ hs' hβ hs Z r z J hJ
  have hG := abelianSchemeLaws_all.1.globalFns
  have hA := GlobalTheory.HeckePoint.isAbelianScheme_of_proper Xo.univ.t Xo.univ.proper
  obtain ⟨β', s₂, n', c, hβ', hs₂, hc, hv⟩ := isThetaTrace_iff.1 hs'
  obtain rfl := hs.unique hG hA hs₂
  have hst : ∀ a ∈ transKer Xo.univ.t.G Ψ, a ≫ Xo.univ.t.act.act H.w0 ∈ transKer Xo.univ.t.G Ψ := by
    intro a ha
    have := Xo.univ.t.act.hom H.w0
    refine (hΨ.2.2.2.1 _).1 ?_
    have h1 : (lift (𝟙 (Over.mk x)) a).left ≫ Ψ =
        (lift (𝟙 (Over.mk x')) (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := (hΨ.2.2.2.1 a).2 ha
    show (lift (𝟙 (Over.mk x)) (a ≫ Xo.univ.t.act.act H.w0)).left ≫ Ψ =
      (lift (𝟙 (Over.mk x')) (1 : Over.mk x' ⟶ Xo.univ.t.G)).left
    rw [← lift_whiskerLeft, Over.comp_left, Category.assoc, hΨ.2.1.2.2 H.w0, reassoc_of% h1, ← Over.comp_left,
      lift_whiskerLeft, MonObj.one_comp]
  let Φ : (Over.mk x ⟶ Xo.univ.t.G) → Z.presheaf.stalk z := fun b =>
    ((val β (r ≫ (translT Xo.univ.t.G b).left) z J)⁻¹).val *
      sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G b).left) z J
  have hΦ : ∀ a ∈ transKer Xo.univ.t.G Ψ, a ^ p = 1 → ∀ b, Φ (a * b) = Φ b := fun a ha hp b =>
    GlobalTheory.ThetaTransport.term_transl hΨ.2.1 hβ.2.1 hs hst r z hJ a ha hp b
  have h1 : sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ i, Φ (c i) :=
    (hv Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => by
      simp only [Φ]; rw [hβ'.val_unique hG hA hβ _ z hJ])
  have : Finite (transKer Xo.univ.t.G Ψ) := Finite.of_equiv _ e
  letI := Fintype.ofFinite (transKer Xo.univ.t.G Ψ)
  let T := {a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1}
  have : Finite T := Finite.of_injective (fun q : T => (⟨q.1, q.2.1⟩ : transKer Xo.univ.t.G Ψ))
    (fun a b h => Subtype.ext (congrArg (fun q : transKer Xo.univ.t.G Ψ => q.1) h))
  letI := Fintype.ofFinite T
  have bij : Function.Bijective fun q : T × Fin n' =>
      (⟨q.1.1 * c q.2, (transKer Xo.univ.t.G Ψ).mul_mem q.1.2.1 (hc.1 _)⟩ : transKer Xo.univ.t.G Ψ) := by
    constructor
    · rintro ⟨a, i⟩ ⟨b, j⟩ h
      have h' : a.1 * c i = b.1 * c j := congrArg Subtype.val h
      obtain rfl : i = j := (hc.2 _ ((transKer Xo.univ.t.G Ψ).mul_mem a.2.1 (hc.1 i))).unique
        (by simpa using a.2.2) (by rw [h']; simpa using b.2.2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h')) rfl
    · intro d
      obtain ⟨i, hi, -⟩ := hc.2 d d.2
      exact ⟨(⟨d * (c i)⁻¹, (transKer Xo.univ.t.G Ψ).mul_mem d.2 ((transKer Xo.univ.t.G Ψ).inv_mem (hc.1 i)), hi⟩, i),
        Subtype.ext (by simp)⟩
  have h2 : ∑ j, Φ (e j).1 = ∑ d : transKer Xo.univ.t.G Ψ, Φ d.1 := Equiv.sum_comp e (fun d => Φ d.1)
  have h3 : ∑ d : transKer Xo.univ.t.G Ψ, Φ d.1 = ∑ q : T × Fin n', Φ (q.1.1 * c q.2) :=
    (Fintype.sum_bijective _ bij _ _ fun q => rfl).symm
  have h4 : ∑ q : T × Fin n', Φ (q.1.1 * c q.2) = ∑ q : T × Fin n', Φ (c q.2) :=
    Finset.sum_congr rfl fun q _ => hΦ _ q.1.2.1 q.1.2.2 _
  show _ = ∑ j, Φ (e j).1
  rw [h2, h3, h4, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h1, Nat.card_eq_fintype_card]

end GlobalTheory.KernelSum
