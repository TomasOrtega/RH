import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrankStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Establish `: IsIso ((Over.forget _).map f.hom)` using `by simpa using (inferInstance : IsIso f.hom.left)`. Establish `: IsIso f.hom` using `isIso_of_reflects_iso f.hom (Over.forget _)`. Establish `: IsMonHom (inv f.hom)` using `inferInstanceAs (IsMonHom (asIso f.hom).inv)`. Set `g : B ⟶ A` to `Hom.mk (A := B) (B := A) (inv f.hom)`. Conclude with `⟨g, hom_ext (by simp [g]), hom_ext (by simp [g])⟩`.
-/
theorem isIso_of_isIso_left {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) [IsIso f.hom.left] : IsIso f := by
  have : IsIso ((Over.forget _).map f.hom) := by simpa using (inferInstance : IsIso f.hom.left)
  have : IsIso f.hom := isIso_of_reflects_iso f.hom (Over.forget _)
  have : IsMonHom (inv f.hom) := inferInstanceAs (IsMonHom (asIso f.hom).inv)
  let g : B ⟶ A := Hom.mk (A := B) (B := A) (inv f.hom)
  exact ⟨g, hom_ext (by simp [g]), hom_ext (by simp [g])⟩

instance isIso_left_of_isIso {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) [IsIso f] : IsIso f.hom.left := by
  have : IsIso f.hom := ⟨(inv f).hom, by rw [← comp_hom, IsIso.hom_inv_id, id_hom], by rw [← comp_hom, IsIso.inv_hom_id, id_hom]⟩
  exact (inferInstance : IsIso ((Over.forget _).map f.hom))

/- English proof (translation)
Introduce `K _ A B f`. Use `⟨fun hf => ?_, fun hd => ?_⟩` and prove the remaining obligations. Establish `hI : IsIsogeny f` using `⟨inferInstance, inferInstance⟩`. Use `⟨hI, ?_⟩` and prove the remaining obligations. Rewrite using `[deg, if_pos hI, Scheme.Hom.finrank_eq_one_of_isIso]`.

Both sides reduce to the same expression. Establish `hI : IsIsogeny f`. Assume the negation of the conclusion as `h`. Rewrite `hd` using `[deg, if_neg h]`. Conclude with `zero_ne_one hd`.

Take `⟨-, hfl, -, hr⟩` from `GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hI`. Establish `: IsFinite f.hom.left` using `hI.1`. Establish `: IsIso f.hom.left`. Rewrite using `[Scheme.Hom.isIso_iff_finrank_eq]`. Use function extensionality and compare the values at `y`.

Rewrite using `[hr y, hd]`. Both sides reduce to the same expression. Conclude with `isIso_of_isIso_left f`.
-/
theorem isIso_iff_deg_eq_one : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    (IsIso f → IsIsogeny f ∧ deg f = 1) ∧ (deg f = 1 → IsIso f) := by
  intro K _ A B f
  refine ⟨fun hf => ?_, fun hd => ?_⟩
  · have hI : IsIsogeny f := ⟨inferInstance, inferInstance⟩
    refine ⟨hI, ?_⟩
    rw [deg, if_pos hI, Scheme.Hom.finrank_eq_one_of_isIso]
    rfl
  · have hI : IsIsogeny f := by
      by_contra h
      rw [deg, if_neg h] at hd
      exact zero_ne_one hd
    obtain ⟨-, hfl, -, hr⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hI
    have : IsFinite f.hom.left := hI.1
    have : IsIso f.hom.left := by
      rw [Scheme.Hom.isIso_iff_finrank_eq]
      funext y
      rw [hr y, hd]
      rfl
    exact isIso_of_isIso_left f

end GlobalTheory.AV.AbVar
