import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

def transferMap {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    pullback z' g' ⟶ pullback z g :=
  pullback.map z' g' z g eZ.hom (𝟙 T) eS.hom hsq.symm (by rw [Category.id_comp, hg])

instance {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    IsIso (transferMap z z' eS eZ hsq g' g hg) := by
  unfold transferMap; infer_instance

def transferIso {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    pullback z' g' ≅ pullback z g :=
  asIso (transferMap z z' eS eZ hsq g' g hg)

/- English proof (translation)
Simplify using `only [transferIso, asIso_hom, transferMap]`. Conclude with `(pullback.lift_snd _ _ _).trans (Category.comp_id _)`.
-/
lemma transferIso_hom_snd {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    (transferIso z z' eS eZ hsq g' g hg).hom ≫ pullback.snd z g = pullback.snd z' g' := by
  simp only [transferIso, asIso_hom, transferMap]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/- English proof (translation)
Rewrite using `[Iso.inv_comp_eq, transferIso_hom_snd]`.
-/
lemma transferIso_inv_snd {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    (transferIso z z' eS eZ hsq g' g hg).inv ≫ pullback.snd z' g' = pullback.snd z g := by
  rw [Iso.inv_comp_eq, transferIso_hom_snd]

/- English proof (translation)
Simplify using `only [transferIso, asIso_hom, transferMap, pullback.map]`. Apply the tactic sequence `apply pullback.hom_ext <;>`. Simplify using `only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]`.
-/
lemma transferIso_map {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T H : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g)
    (h' : H ⟶ S') (f : T ⟶ H) (hf' : f ≫ h' = g') (hf : f ≫ (h' ≫ eS.hom) = g) :
    pullback.map z' g' z' h' (𝟙 Z') f (𝟙 S') (by simp) (by rw [Category.comp_id, hf'])
        ≫ (transferIso z z' eS eZ hsq h' (h' ≫ eS.hom) rfl).hom =
      (transferIso z z' eS eZ hsq g' g hg).hom ≫
        pullback.map z g z (h' ≫ eS.hom) (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf]) := by
  simp only [transferIso, asIso_hom, transferMap, pullback.map]
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

/- English proof (translation)
Introduce `S Z S' Z' z z' eS eZ hsq r hrep`. Take `⟨H, h', U, u', hP, hC, hF, hFl, hR, hU⟩` from `hrep`. Use `set ΦH := transferIso z z' eS eZ hsq h' (h' ≫ eS.hom) rfl with hΦH`. Establish `eu : (u' ≫ ΦH.hom) ≫ pullback.snd z (h' ≫ eS.hom) = u' ≫ pullback.snd z' h'`. Rewrite using `[Category.assoc, transferIso_hom_snd]`.

Use `⟨H, h' ≫ eS.hom, U, u' ≫ ΦH.hom, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eu]`. Conclude with `hF`. Rewrite using `[eu]`. Conclude with `hFl`.

Rewrite using `[eu]`. Conclude with `hR`. Introduce `T g V v hv hvF hvFl hvR`. Establish `hg : (g ≫ eS.inv) ≫ eS.hom = g` using `by simp`. Use `set ΦT := transferIso z z' eS eZ hsq (g ≫ eS.inv) g hg with hΦT`.

Establish `ev : (v ≫ ΦT.inv) ≫ pullback.snd z' (g ≫ eS.inv) = v ≫ pullback.snd z g`. Rewrite using `[Category.assoc, transferIso_inv_snd]`. Establish `hv' : IsClosedImmersion (v ≫ ΦT.inv)` using `inferInstance`. Take `⟨f, ⟨hf', w, hpb⟩, huniq⟩` from `hU T (g ≫ eS.inv) V (v ≫ ΦT.inv) hv' (by rw [ev]; exact hvF) (by rw [ev]; exact hvFl) (by rw [ev]; exact hvR)`. Establish `hf : f ≫ (h' ≫ eS.hom) = g` using `by rw [← Category.assoc, hf', hg]`.

Use `⟨f, ⟨hf, w, ?_⟩, ?_⟩` and prove the remaining obligations. Use `hpb.of_iso (Iso.refl _) ΦT (Iso.refl _) ΦH ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Conclude with `transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f hf' hf`.

Simplify using the standard rewrite rules. Introduce and unpack `f₂ ⟨hf₂, w₂, hpb₂⟩`. Establish `hf₂' : f₂ ≫ h' = g ≫ eS.inv` using `by rw [← hf₂]; simp`. Apply `huniq f₂ ⟨hf₂', w₂, ?_⟩` to reduce the goal to its premises. Use `hpb₂.of_iso (Iso.refl _) ΦT.symm (Iso.refl _) ΦH.symm ?_ ?_ ?_ ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f₂ hf₂' hf₂, Iso.inv_hom_id_assoc]`. Simplify using `[hΦH]`.
-/
theorem isHilbRep_transfer : ∀ {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z),
    eZ.hom ≫ z = z' ≫ eS.hom → ∀ r : ℕ, IsHilbRep z' r → IsHilbRep z r := by
  intro S Z S' Z' z z' eS eZ hsq r hrep
  obtain ⟨H, h', U, u', hP, hC, hF, hFl, hR, hU⟩ := hrep
  set ΦH := transferIso z z' eS eZ hsq h' (h' ≫ eS.hom) rfl with hΦH
  have eu : (u' ≫ ΦH.hom) ≫ pullback.snd z (h' ≫ eS.hom) = u' ≫ pullback.snd z' h' := by
    rw [Category.assoc, transferIso_hom_snd]
  refine ⟨H, h' ≫ eS.hom, U, u' ≫ ΦH.hom, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [eu]; exact hF
  · rw [eu]; exact hFl
  · rw [eu]; exact hR
  intro T g V v hv hvF hvFl hvR
  have hg : (g ≫ eS.inv) ≫ eS.hom = g := by simp
  set ΦT := transferIso z z' eS eZ hsq (g ≫ eS.inv) g hg with hΦT
  have ev : (v ≫ ΦT.inv) ≫ pullback.snd z' (g ≫ eS.inv) = v ≫ pullback.snd z g := by
    rw [Category.assoc, transferIso_inv_snd]
  have hv' : IsClosedImmersion (v ≫ ΦT.inv) := inferInstance
  obtain ⟨f, ⟨hf', w, hpb⟩, huniq⟩ := hU T (g ≫ eS.inv) V (v ≫ ΦT.inv) hv' (by rw [ev]; exact hvF)
    (by rw [ev]; exact hvFl) (by rw [ev]; exact hvR)
  have hf : f ≫ (h' ≫ eS.hom) = g := by rw [← Category.assoc, hf', hg]
  refine ⟨f, ⟨hf, w, ?_⟩, ?_⟩
  · refine hpb.of_iso (Iso.refl _) ΦT (Iso.refl _) ΦH ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f hf' hf
    · simp
  · rintro f₂ ⟨hf₂, w₂, hpb₂⟩
    have hf₂' : f₂ ≫ h' = g ≫ eS.inv := by rw [← hf₂]; simp
    apply huniq f₂ ⟨hf₂', w₂, ?_⟩
    refine hpb₂.of_iso (Iso.refl _) ΦT.symm (Iso.refl _) ΦH.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc,
        transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f₂ hf₂' hf₂, Iso.inv_hom_id_assoc]
    · simp [hΦH]

end GlobalTheory.HilbertSch
