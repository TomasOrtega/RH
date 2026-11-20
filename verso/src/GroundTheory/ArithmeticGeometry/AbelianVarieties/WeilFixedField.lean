import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilTranslate

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
  [W.IsElliptic]

/- English proof (translation)
Establish `e` using `congrArg (fun ψ => Point.map ψ (genericPoint W)) h`. Simplify using `only [map_translate_genericPoint, add_right_inj] at e`. Conclude with `Point.map_injective (W' := W) (f := Algebra.ofId F W.toAffine.FunctionField) e`.
-/
theorem translate_inj {S S' : W.toAffine.Point} (h : translate W S = translate W S') : S = S' := by
  have e := congrArg (fun ψ => Point.map ψ (genericPoint W)) h
  simp only [map_translate_genericPoint, add_right_inj] at e
  exact Point.map_injective (W' := W) (f := Algebra.ofId F W.toAffine.FunctionField) e

noncomputable abbrev mulPullbackField {n : ℤ} (hn0 : n ≠ 0) :
    IntermediateField F W.toAffine.FunctionField :=
  (mulPullback W n hn0).fieldRange

noncomputable def translateEquiv {n : ℤ} (hn0 : n ≠ 0) (S : W.toAffine.Point) (hS : n • S = 0) :
    W.toAffine.FunctionField ≃ₐ[mulPullbackField W hn0] W.toAffine.FunctionField :=
  AlgEquiv.ofRingEquiv (f := {
      toFun := translate W S
      invFun := translate W (-S)
      left_inv := fun f => by rw [translate_translate, neg_add_cancel, translate_zero]; rfl
      right_inv := fun f => by rw [translate_translate, add_neg_cancel, translate_zero]; rfl
      map_mul' := map_mul (translate W S)
      map_add' := map_add (translate W S) }) (by
    rintro ⟨m, hm⟩
    obtain ⟨f, rfl⟩ := AlgHom.mem_fieldRange.mp hm
    exact translate_mulPullback_of_zsmul_eq_zero W hn0 hS f)

noncomputable def torsionTranslations {n : ℤ} (hn0 : n ≠ 0) :
    Subgroup (W.toAffine.FunctionField ≃ₐ[mulPullbackField W hn0] W.toAffine.FunctionField) where
  carrier := {σ | ∃ S : W.toAffine.Point, n • S = 0 ∧ ∀ f, σ f = translate W S f}
  mul_mem' := by
    rintro σ τ ⟨S, hS, hσ⟩ ⟨T, hT, hτ⟩
    refine ⟨S + T, by rw [smul_add, hS, hT, add_zero], fun f => ?_⟩
    rw [AlgEquiv.mul_apply, hτ, hσ, translate_translate]
  one_mem' := ⟨0, smul_zero n, fun f => by rw [translate_zero]; rfl⟩
  inv_mem' := by
    rintro σ ⟨S, hS, hσ⟩
    refine ⟨-S, by rw [smul_neg, hS, neg_zero], fun f => ?_⟩
    apply (translate_injective W S)
    rw [← hσ, translate_translate, add_neg_cancel, translate_zero, AlgHom.id_apply]
    exact σ.apply_symm_apply f

/- English proof (translation)
Rewrite using `[← card_zsmul_eq_zero W hn]`. Use `symm`. Use `Nat.card_congr (Equiv.ofBijective (fun S => ⟨translateEquiv W hn0 S.1 S.2, S.1, S.2, fun _ => rfl⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce and unpack `⟨S, hS⟩ ⟨S', hS'⟩ h`. Establish `h' : translate W S = translate W S'` using `AlgHom.ext fun f => DFunLike.congr_fun (congrArg Subtype.val h) f`.

Conclude with `Subtype.ext (translate_inj W h')`. Introduce and unpack `⟨σ, S, hS, hσ⟩`. Conclude with `⟨⟨S, hS⟩, Subtype.ext (AlgEquiv.ext fun f => (hσ f).symm)⟩`.
-/
theorem card_torsionTranslations {n : ℤ} (hn : (n : F) ≠ 0) (hn0 : n ≠ 0) :
    Nat.card (torsionTranslations W hn0) = n.natAbs ^ 2 := by
  rw [← card_zsmul_eq_zero W hn]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun S => ⟨translateEquiv W hn0 S.1 S.2, S.1, S.2, fun _ => rfl⟩) ⟨?_, ?_⟩)
  · rintro ⟨S, hS⟩ ⟨S', hS'⟩ h
    have h' : translate W S = translate W S' := AlgHom.ext fun f =>
      DFunLike.congr_fun (congrArg Subtype.val h) f
    exact Subtype.ext (translate_inj W h')
  · rintro ⟨σ, S, hS, hσ⟩
    exact ⟨⟨S, hS⟩, Subtype.ext (AlgEquiv.ext fun f => (hσ f).symm)⟩

/- English proof (translation)
Use `set M := mulPullbackField W hn0`. Use `set H := torsionTranslations W hn0`. Establish `hdeg : Module.finrank M W.toAffine.FunctionField = n.natAbs ^ 2` using `degree_mulIsogeny W hn0`. Establish `hpos : 0 < n.natAbs ^ 2` using `pow_pos (Int.natAbs_pos.mpr hn0) 2`. Establish `: FiniteDimensional M W.toAffine.FunctionField` using `Module.finite_of_finrank_pos (by rw [hdeg]; exact hpos)`.

Establish `hfix : Module.finrank (IntermediateField.fixedField H) W.toAffine.FunctionField = n.natAbs ^ 2`. Rewrite using `[IntermediateField.finrank_fixedField_eq_card, card_torsionTranslations W hn hn0]`. Establish `hone : Module.finrank M (IntermediateField.fixedField H) = 1`. Establish `: Module.Free M (IntermediateField.fixedField H)` using `Module.Free.of_divisionRing _ _`. Establish `: Module.Free (IntermediateField.fixedField H) W.toAffine.FunctionField` using `Module.Free.of_divisionRing _ _`.

Use `Module.finrank_mul_finrank M (IntermediateField.fixedField H) W.toAffine.FunctionField` as an intermediate fact. Rewrite `this` using `[hfix, hdeg]`. Conclude with `(Nat.mul_eq_right hpos.ne').mp this`. Establish `hbot : IntermediateField.fixedField H = ⊥` using `IntermediateField.finrank_eq_one_iff.mp hone`. Establish `hg : g ∈ IntermediateField.fixedField H`.

Introduce and unpack `⟨σ, S, hS, hσ⟩`. Conclude with `(hσ g).trans (h S hS)`. Rewrite `hg` using `[hbot, IntermediateField.mem_bot]`. Take `⟨⟨m, hm⟩, rfl⟩` from `hg`. Take `⟨f, rfl⟩` from `AlgHom.mem_fieldRange.mp hm`.

Conclude with `⟨f, rfl⟩`.
-/
theorem exists_mulPullback_eq_of_forall_translate_eq {n : ℤ} (hn : (n : F) ≠ 0) (hn0 : n ≠ 0)
    {g : W.toAffine.FunctionField} (h : ∀ S : W.toAffine.Point, n • S = 0 → translate W S g = g) :
    ∃ f, mulPullback W n hn0 f = g := by
  set M := mulPullbackField W hn0
  set H := torsionTranslations W hn0
  have hdeg : Module.finrank M W.toAffine.FunctionField = n.natAbs ^ 2 :=
    degree_mulIsogeny W hn0
  have hpos : 0 < n.natAbs ^ 2 := pow_pos (Int.natAbs_pos.mpr hn0) 2
  have : FiniteDimensional M W.toAffine.FunctionField :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact hpos)
  have hfix : Module.finrank (IntermediateField.fixedField H) W.toAffine.FunctionField =
      n.natAbs ^ 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card, card_torsionTranslations W hn hn0]
  have hone : Module.finrank M (IntermediateField.fixedField H) = 1 := by
    have : Module.Free M (IntermediateField.fixedField H) := Module.Free.of_divisionRing _ _
    have : Module.Free (IntermediateField.fixedField H) W.toAffine.FunctionField :=
      Module.Free.of_divisionRing _ _
    have := Module.finrank_mul_finrank M (IntermediateField.fixedField H) W.toAffine.FunctionField
    rw [hfix, hdeg] at this
    exact (Nat.mul_eq_right hpos.ne').mp this
  have hbot : IntermediateField.fixedField H = ⊥ := IntermediateField.finrank_eq_one_iff.mp hone
  have hg : g ∈ IntermediateField.fixedField H := by
    rintro ⟨σ, S, hS, hσ⟩
    exact (hσ g).trans (h S hS)
  rw [hbot, IntermediateField.mem_bot] at hg
  obtain ⟨⟨m, hm⟩, rfl⟩ := hg
  obtain ⟨f, rfl⟩ := AlgHom.mem_fieldRange.mp hm
  exact ⟨f, rfl⟩

end GroundTheory.Arith.Abelian
