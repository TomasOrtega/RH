import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModulesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameComplementRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapFnOfEqValC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcParamEqWeightStepZeroAddRho
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

/- English proof (translation)
Introduce `D X u F wt hw`. Take `⟨o, ho, hfr⟩` from `GlobalTheory.T.exists_orthonormalFrame_complement_realPlaces D X u wt hw`. Set `e` to `Equiv.piCongrLeft (X.Vloc u) X.pl.symm`. Establish `he : ∀ (x : ∀ τ, X.Vloc u (X.pl.symm τ)) τ, e x (X.pl.symm τ) = x τ` using `fun x τ => Equiv.piCongrLeft_apply_apply (X.Vloc u) X.pl.symm x τ`. Set `tens : (∀ τ, X.Vloc u (X.pl.symm τ)) → X.Vpi u` to `fun x => X.tensU u (e x)`.

Establish `hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ`. Introduce `x y`. Use `show ⟪X.tensU u (e x), X.tensU u (e y)⟫_ℂ = _`. Rewrite using `[X.tensU_inner, ← Equiv.prod_comp X.pl.symm]`. Conclude with `Finset.prod_congr rfl fun τ _ => by rw [he, he]`.

Establish `hsp : Submodule.span ℂ (Set.range tens) = ⊤`. Establish `: Set.range tens = Set.range (X.tensU u)` using `e.surjective.range_comp _`. Rewrite using `[this]`. Conclude with `X.tensU_span u`. Establish `hty : ∀ τ, IsHCTypeU D.R.k (fun i => (((D.hcW u τ).u i : ℚ) : ℝ)) (X.piLoc u (X.pl.symm τ))`.

Introduce `τ`. Establish `h` using `X.piLoc_type u (X.pl.symm τ)`. Rewrite `h` using `[X.pl.apply_symm_apply]`. Then use the resulting hypothesis. Take `⟨Jp, hJv, hJs, hJi, hJe⟩` from `GlobalTheory.T.tensor_types_realPlaces_equiv_span_weylModules D.what₂.Tau D.R.k (D.R.N 0) D.R.N_zero.symm (Formalism.L2.Forms.lamT u 0) (fun τ i => (((D.hcW u τ).u i : ℚ) : ℝ)) (fun τ i => GlobalTheory.hcParam_eq_weight_step_zero_add_rho D u τ i) (fun τ => X.Vloc u (X.pl.symm τ)) …`. Establish `hoinv : ∀ τ, IsUnit ((o.1 τ)⁻¹).det` using `fun τ => by`.

Establish `h` using `o.2 τ`. Rewrite using `[Matrix.det_nonsing_inv]`. Conclude with `(Ring.inverse_unit h.unit ▸ (h.unit⁻¹).isUnit)`. Establish `hmap` using `GlobalTheory.ValueSpaceCoordinates.map_fnOf_eq_ValC D.what₂.Tau (D.R.N 0) (Formalism.L2.Forms.lamT u 0) (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (fun τ => (o.1 τ)⁻¹) hoinv`. Set `fo` to `Formalism.L2.Forms.fnOf (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0)) (fun τ => (o.1 τ)⁻¹)`.

Use `⟨fo.comp Jp, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `s hs ξ y y' hyy`. Take `⟨m, hm⟩` from `hfr s hs`. Establish `hA : ∀ x, X.piU u s (tens x) = tens (fun τ => X.piLoc u (X.pl.symm τ) ((m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm)) (x τ))`. Introduce `x`.

Use `show X.piU u s (X.tensU u (e x)) = X.tensU u (e _)`. Rewrite using `[X.tensU_equiv u s hs (e x)]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Take `⟨τ, rfl⟩` from `X.pl.symm.surjective v`.

Rewrite using `[he, he, (hm τ).2.1]`. Establish `hy : Formalism.L2.Forms.IsTr (fun τ => o.1 τ * m τ * (o.1 τ)⁻¹) y' y` using `fun τ => by`. Rewrite using `[hyy τ, (hm τ).2.2]`. Conclude with `hJe m (fun τ => (hm τ).1) (X.piU u s) hA _ o.1 (fun τ => o.2 τ) ξ y y' hy`. Introduce `ξ`.

Rewrite using `[← hmap]`. Conclude with `⟨Jp ξ, hJv ξ, rfl⟩`. Introduce `c ξ η`. Establish `hon : o.IsON` using `fun τ => Or.inl (ho τ)`. Establish `hP : ∀ ζ, Jp ζ ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam 0)` using `fun ζ => by`.

Rewrite using `[← Formalism.L2.Forms.lamT_zero]`. Conclude with `hJv ζ`. Establish `h` using `F.val0.ipV c o hon (Jp ξ) (hP ξ) (Jp η) (hP η)`. Rewrite `h` using `[← Formalism.L2.Forms.lamT_zero]`. Conclude with `h.trans (hJi ξ η)`.

Introduce `p hp`. Rewrite `hp` using `[← hmap]`. Take `⟨P, hP, rfl⟩` from `hp`. Take `⟨ξ, rfl⟩` from `hJs P hP`. Conclude with `⟨ξ, rfl⟩`.
-/
theorem coefficient_map_exists_onto : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ), JOK X u F wt J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, J ξ = p := by
  intro D X u F wt hw
  obtain ⟨o, ho, hfr⟩ := GlobalTheory.T.exists_orthonormalFrame_complement_realPlaces D X u wt hw
  let e := Equiv.piCongrLeft (X.Vloc u) X.pl.symm
  have he : ∀ (x : ∀ τ, X.Vloc u (X.pl.symm τ)) τ, e x (X.pl.symm τ) = x τ := fun x τ =>
    Equiv.piCongrLeft_apply_apply (X.Vloc u) X.pl.symm x τ
  let tens : (∀ τ, X.Vloc u (X.pl.symm τ)) → X.Vpi u := fun x => X.tensU u (e x)
  have hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ := by
    intro x y
    show ⟪X.tensU u (e x), X.tensU u (e y)⟫_ℂ = _
    rw [X.tensU_inner, ← Equiv.prod_comp X.pl.symm]
    exact Finset.prod_congr rfl fun τ _ => by rw [he, he]
  have hsp : Submodule.span ℂ (Set.range tens) = ⊤ := by
    have : Set.range tens = Set.range (X.tensU u) := e.surjective.range_comp _
    rw [this]; exact X.tensU_span u
  have hty : ∀ τ, IsHCTypeU D.R.k (fun i => (((D.hcW u τ).u i : ℚ) : ℝ)) (X.piLoc u (X.pl.symm τ)) := by
    intro τ
    have h := X.piLoc_type u (X.pl.symm τ)
    rwa [X.pl.apply_symm_apply] at h
  obtain ⟨Jp, hJv, hJs, hJi, hJe⟩ := GlobalTheory.T.tensor_types_realPlaces_equiv_span_weylModules D.what₂.Tau D.R.k (D.R.N 0) D.R.N_zero.symm
    (Formalism.L2.Forms.lamT u 0) (fun τ i => (((D.hcW u τ).u i : ℚ) : ℝ))
    (fun τ i => GlobalTheory.hcParam_eq_weight_step_zero_add_rho D u τ i)
    (fun τ => X.Vloc u (X.pl.symm τ)) (fun τ => X.piLoc u (X.pl.symm τ)) hty (X.Vpi u) tens hin hsp
  have hoinv : ∀ τ, IsUnit ((o.1 τ)⁻¹).det := fun τ => by
    have h := o.2 τ
    rw [Matrix.det_nonsing_inv]
    exact (Ring.inverse_unit h.unit ▸ (h.unit⁻¹).isUnit)
  have hmap := GlobalTheory.ValueSpaceCoordinates.map_fnOf_eq_ValC D.what₂.Tau (D.R.N 0) (Formalism.L2.Forms.lamT u 0)
    (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D))
    (fun τ => (o.1 τ)⁻¹) hoinv
  let fo := Formalism.L2.Forms.fnOf (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D))
    (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0)) (fun τ => (o.1 τ)⁻¹)
  refine ⟨fo.comp Jp, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro s hs ξ y y' hyy
    obtain ⟨m, hm⟩ := hfr s hs
    have hA : ∀ x, X.piU u s (tens x) = tens (fun τ =>
        X.piLoc u (X.pl.symm τ) ((m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm)) (x τ)) := by
      intro x
      show X.piU u s (X.tensU u (e x)) = X.tensU u (e _)
      rw [X.tensU_equiv u s hs (e x)]
      congr 1
      funext v
      obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
      rw [he, he, (hm τ).2.1]
    have hy : Formalism.L2.Forms.IsTr (fun τ => o.1 τ * m τ * (o.1 τ)⁻¹) y' y := fun τ => by
      rw [hyy τ, (hm τ).2.2]
    exact hJe m (fun τ => (hm τ).1) (X.piU u s) hA _ o.1 (fun τ => o.2 τ) ξ y y' hy
  · intro ξ
    rw [← hmap]
    exact ⟨Jp ξ, hJv ξ, rfl⟩
  · intro c ξ η
    have hon : o.IsON := fun τ => Or.inl (ho τ)
    have hP : ∀ ζ, Jp ζ ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam 0) := fun ζ => by
      rw [← Formalism.L2.Forms.lamT_zero]; exact hJv ζ
    have h := F.val0.ipV c o hon (Jp ξ) (hP ξ) (Jp η) (hP η)
    rw [← Formalism.L2.Forms.lamT_zero] at h
    exact h.trans (hJi ξ η)
  · intro p hp
    rw [← hmap] at hp
    obtain ⟨P, hP, rfl⟩ := hp
    obtain ⟨ξ, rfl⟩ := hJs P hP
    exact ⟨ξ, rfl⟩

end GlobalTheory.St
