import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

/- English proof (translation)
Take `⟨U, hU⟩` from `W.exists_isCompl`. Take `⟨U', hU'⟩` from `W'.exists_isCompl`. Establish `h1` using `Submodule.finrank_add_eq_of_isCompl hU`. Establish `h2` using `Submodule.finrank_add_eq_of_isCompl hU'`. Establish `h3 : Module.finrank k U = Module.finrank k U'` using `by omega`.

Set `a : W ≃ₗ[k] W'` to `LinearEquiv.ofFinrankEq _ _ h`. Set `b : U ≃ₗ[k] U'` to `LinearEquiv.ofFinrankEq _ _ h3`. Set `e : V ≃ₗ[k] V` to `(Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ Submodule.prodEquivOfIsCompl W' U' hU'`. Establish `he : ∀ w : W, e w = a w`. Introduce `w`.

Simplify using `[e]`. Use `⟨e, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Use `he ⟨w, hw⟩` as an intermediate fact.

Express the relevant statement in the definitionally equal form `e w ∈ W'`. Simplify using `only at this`. Rewrite using `[this]`. Conclude with `(a ⟨w, hw⟩).2`. Introduce `w hw`.

Use `⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e _ = w`. Rewrite using `[he]`. Simplify using the standard rewrite rules.
-/
theorem exists_linearEquiv_map_eq_of_finrank_eq {k V : Type} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (W W' : Submodule k V)
    (h : Module.finrank k W = Module.finrank k W') :
    ∃ e : V ≃ₗ[k] V, W.map e.toLinearMap = W' := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  obtain ⟨U', hU'⟩ := W'.exists_isCompl
  have h1 := Submodule.finrank_add_eq_of_isCompl hU
  have h2 := Submodule.finrank_add_eq_of_isCompl hU'
  have h3 : Module.finrank k U = Module.finrank k U' := by omega
  let a : W ≃ₗ[k] W' := LinearEquiv.ofFinrankEq _ _ h
  let b : U ≃ₗ[k] U' := LinearEquiv.ofFinrankEq _ _ h3
  let e : V ≃ₗ[k] V := (Submodule.prodEquivOfIsCompl W U hU).symm ≪≫ₗ (a.prodCongr b) ≪≫ₗ
    Submodule.prodEquivOfIsCompl W' U' hU'
  have he : ∀ w : W, e w = a w := by
    intro w
    simp [e]
  refine ⟨e, ?_⟩
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have := he ⟨w, hw⟩
    change e w ∈ W'
    simp only at this
    rw [this]
    exact (a ⟨w, hw⟩).2
  · intro w hw
    refine ⟨a.symm ⟨w, hw⟩, (a.symm ⟨w, hw⟩).2, ?_⟩
    change e _ = w
    rw [he]
    simp

/- English proof (translation)
Take `⟨e, he⟩` from `exists_linearEquiv_map_eq_of_finrank_eq W W' h`. Set `M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)` to `LinearMap.toMatrix' e.toLinearMap`. Use `choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)`. Establish `hAM : (Matrix.of A).map (IsLocalRing.residue O) = M`. Use extensionality with `i j`.

Conclude with `hA i j`. Establish `hM : M.det ≠ 0`. Establish `: M.det = LinearMap.det e.toLinearMap` using `LinearMap.det_toMatrix' _`. Rewrite using `[this]`. Conclude with `(LinearEquiv.isUnit_det' e).ne_zero`.

Establish `hu : IsUnit (Matrix.of A).det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]`. Express the relevant statement in the definitionally equal form `((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0`. Rewrite using `[hAM]`. Conclude with `hM`.

Take `⟨g, hg⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 hu`. Use `⟨g, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, hAM, ← he]`. Use `congr 1`. Conclude with `Matrix.toLin'_toMatrix' e.toLinearMap`.
-/
theorem exists_gl_map_residue_eq (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ)
    (W W' : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O))
    (h : Module.finrank (IsLocalRing.ResidueField O) W =
      Module.finrank (IsLocalRing.ResidueField O) W') :
    ∃ g : GL (Fin n) O, W.map (g.1.map (IsLocalRing.residue O)).mulVecLin = W' := by
  obtain ⟨e, he⟩ := exists_linearEquiv_map_eq_of_finrank_eq W W' h
  let M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O) := LinearMap.toMatrix' e.toLinearMap
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := O) (M i j)
  have hAM : (Matrix.of A).map (IsLocalRing.residue O) = M := by
    ext i j
    exact hA i j
  have hM : M.det ≠ 0 := by
    have : M.det = LinearMap.det e.toLinearMap := LinearMap.det_toMatrix' _
    rw [this]
    exact (LinearEquiv.isUnit_det' e).ne_zero
  have hu : IsUnit (Matrix.of A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    change ((Matrix.of A).map (IsLocalRing.residue O)).det ≠ 0
    rw [hAM]
    exact hM
  obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨g, ?_⟩
  rw [hg, hAM, ← he]
  congr 1
  exact Matrix.toLin'_toMatrix' e.toLinearMap

end GlobalTheory.SplitHecke
