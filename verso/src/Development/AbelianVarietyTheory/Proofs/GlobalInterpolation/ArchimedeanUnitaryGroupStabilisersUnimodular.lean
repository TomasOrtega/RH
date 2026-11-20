import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt

open MeasureTheory NumberField IsDedekindDomain Matrix Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicUnimod
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
open Formalism.UG (UJ cT cT_mul)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.ArchUnitaryUnimod

section Blocks

variable {A : Type} [CommRing A] {n m k : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype k] [DecidableEq k] {σ : A →+* A} {J : Matrix n n A}
  {B : Matrix n m A} {C : Matrix m n A} {X : Matrix n k A} {Y : Matrix k n A}

def OrthSplit (σ : A →+* A) (J : Matrix n n A) (B : Matrix n m A) (C : Matrix m n A) (X : Matrix n k A)
    (Y : Matrix k n A) : Prop :=
  C * B = 1 ∧ B * C + X * Y = 1 ∧ C * X = 0 ∧ Y * B = 0 ∧ Y * X = 1 ∧ cT σ B * J * X = 0 ∧
    cT σ X * J * B = 0 ∧ IsUnit J

omit [Fintype n] [DecidableEq n] in
/- English proof (translation)
Unfold `Formalism.UG.cT`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem cT_add' (P Q : Matrix n n A) : cT σ (P + Q) = cT σ P + cT σ Q := by
  unfold Formalism.UG.cT
  ext i j
  simp

/- English proof (translation)
Unfold `Formalism.UG.cT`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]`.
-/
private theorem cT_one_global_interpolation {p : Type} [Fintype p] [DecidableEq p] : cT σ (1 : Matrix p p A) = 1 := by
  unfold Formalism.UG.cT
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_UJ_iff' {p : Type} [Fintype p] [DecidableEq p] {K : Matrix p p A} {g : GL p A} :
    g ∈ UJ σ K ↔ cT σ (g : Matrix p p A) * K * g = K := Iff.rfl

def OrthSplit.ext (h : OrthSplit σ J B C X Y) : Matrix m m A →* Matrix n n A where
  toFun g := B * g * C + X * Y
  map_one' := by rw [Matrix.mul_one, h.2.1]
  map_mul' g g' := by
    obtain ⟨h1, -, h3, h4, h5, -⟩ := h
    have e1 : ∀ Z : Matrix m n A, C * (B * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    have e3 : ∀ Z : Matrix k n A, C * (X * Z) = 0 := fun Z => by rw [← Matrix.mul_assoc, h3, Matrix.zero_mul]
    have e4 : ∀ Z : Matrix m n A, Y * (B * Z) = 0 := fun Z => by rw [← Matrix.mul_assoc, h4, Matrix.zero_mul]
    have e5 : ∀ Z : Matrix k n A, Y * (X * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, h5, Matrix.one_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, e1, e3, e4, e5, Matrix.mul_zero, add_zero,
      zero_add]

/- English proof (translation)
Use `show cT σ (B * g * C + X * Y) * J * (B * g * C + X * Y) = _`. Take `⟨-, -, -, -, -, h6, h7, -⟩` from `id h`. Establish `e6 : ∀ Z : Matrix k n A, cT σ B * (J * (X * Z)) = 0` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h6, Matrix.zero_mul]`. Establish `e7 : ∀ Z : Matrix m n A, cT σ X * (J * (B * Z)) = 0` using `fun Z => by`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h7, Matrix.zero_mul]`. Simplify using `only [cT_add', cT_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, e6, e7, Matrix.mul_zero, add_zero, zero_add]`.
-/
theorem OrthSplit.form_ext (h : OrthSplit σ J B C X Y) (g : Matrix m m A) :
    cT σ (h.ext g) * J * h.ext g =
      cT σ C * (cT σ g * (cT σ B * J * B) * g) * C + cT σ Y * (cT σ X * J * X) * Y := by
  show cT σ (B * g * C + X * Y) * J * (B * g * C + X * Y) = _
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := id h
  have e6 : ∀ Z : Matrix k n A, cT σ B * (J * (X * Z)) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h6, Matrix.zero_mul]
  have e7 : ∀ Z : Matrix m n A, cT σ X * (J * (B * Z)) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h7, Matrix.zero_mul]
  simp only [cT_add', cT_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, e6, e7, Matrix.mul_zero,
    add_zero, zero_add]

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7, hJ⟩` from `h`. Establish `hJJ : J⁻¹ * J = 1` using `Matrix.nonsing_inv_mul J ((Matrix.isUnit_iff_isUnit_det J).mp hJ)`. Establish `hc : cT σ C * cT σ B + cT σ Y * cT σ X = 1`. Rewrite using `[← cT_mul, ← cT_mul, ← cT_add', h2, cT_one_global_interpolation]`. Establish `key : (Y * J⁻¹ * cT σ Y) * (cT σ X * J * X) = 1`.

Establish `e1 : cT σ Y * cT σ X = 1 - cT σ C * cT σ B` using `eq_sub_of_add_eq' hc`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Y * (J⁻¹ * J) * X - Y * J⁻¹ * cT σ C * (cT σ B * J * X) := by`. Rewrite using `[e1]`.

Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = 1 := by rw [hJJ, h6, Matrix.mul_one, h5, Matrix.mul_zero, sub_zero]`. Establish `hW : cT σ X * J * (g * B) = 0`. Combine the equalities or inequalities in the displayed calculation. Establish `hYW : Y * (g * B) = 0`.

Establish `e : cT σ X * J * (X * Y * (g * B)) = cT σ X * J * (g * B)`. Rewrite using `[show X * Y = 1 - B * C from eq_sub_of_add_eq' h2, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_assoc B C, ← Matrix.mul_assoc (cT σ X * J) B, h7, Matrix.zero_mul, sub_zero]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem OrthSplit.preserves (h : OrthSplit σ J B C X Y) {g : Matrix n n A} (hg : cT σ g * J * g = J)
    (hX : g * X = X) : B * (C * g * B) = g * B := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hJ⟩ := h
  have hJJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J ((Matrix.isUnit_iff_isUnit_det J).mp hJ)
  have hc : cT σ C * cT σ B + cT σ Y * cT σ X = 1 := by
    rw [← cT_mul, ← cT_mul, ← cT_add', h2, cT_one_global_interpolation]
  have key : (Y * J⁻¹ * cT σ Y) * (cT σ X * J * X) = 1 := by
    have e1 : cT σ Y * cT σ X = 1 - cT σ C * cT σ B := eq_sub_of_add_eq' hc
    calc (Y * J⁻¹ * cT σ Y) * (cT σ X * J * X) = Y * J⁻¹ * (cT σ Y * cT σ X) * J * X := by
          simp only [Matrix.mul_assoc]
      _ = Y * (J⁻¹ * J) * X - Y * J⁻¹ * cT σ C * (cT σ B * J * X) := by
          rw [e1]
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hJJ, h6, Matrix.mul_one, h5, Matrix.mul_zero, sub_zero]
  have hW : cT σ X * J * (g * B) = 0 := by
    calc cT σ X * J * (g * B) = cT σ (g * X) * J * (g * B) := by rw [hX]
      _ = cT σ X * (cT σ g * J * g) * B := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hg, h7]
  have hYW : Y * (g * B) = 0 := by
    have e : cT σ X * J * (X * Y * (g * B)) = cT σ X * J * (g * B) := by
      rw [show X * Y = 1 - B * C from eq_sub_of_add_eq' h2, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
        Matrix.mul_assoc B C, ← Matrix.mul_assoc (cT σ X * J) B, h7, Matrix.zero_mul, sub_zero]
    calc Y * (g * B) = (Y * J⁻¹ * cT σ Y) * (cT σ X * J * X) * (Y * (g * B)) := by rw [key, Matrix.one_mul]
      _ = (Y * J⁻¹ * cT σ Y) * (cT σ X * J * (X * Y * (g * B))) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [e, hW, Matrix.mul_zero]
  calc B * (C * g * B) = (B * C) * (g * B) := by simp only [Matrix.mul_assoc]
    _ = (B * C + X * Y) * (g * B) := by rw [Matrix.add_mul, Matrix.mul_assoc X Y, hYW, Matrix.mul_zero, add_zero]
    _ = g * B := by rw [h2, Matrix.one_mul]

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7, hJ⟩` from `id h`. Establish `e1 : ∀ {p : Type} (Z : Matrix m p A), C * (B * Z) = Z` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, h1, Matrix.one_mul]`. Establish `e3 : ∀ {p : Type} (Z : Matrix k p A), C * (X * Z) = 0` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, h3, Matrix.zero_mul]`.

Establish `hext : ∀ g : Matrix m m A, h.ext g = B * g * C + X * Y` using `fun _ => rfl`. Establish `memU : ∀ g : Matrix m m A, cT σ g * (cT σ B * J * B) * g = cT σ B * J * B → cT σ (h.ext g) * J * h.ext g = J`. Introduce `g hg`. Establish `e0` using `h.form_ext 1`. Rewrite `e0` using `[map_one]`.

Simplify using `only [cT_one_global_interpolation, Matrix.one_mul, Matrix.mul_one] at e0`. Rewrite using `[h.form_ext g, hg, ← e0]`. Establish `fixX : ∀ g : Matrix m m A, h.ext g * X = X`. Introduce `g`. Rewrite using `[hext, Matrix.add_mul, Matrix.mul_assoc (B * g) C X, h3, Matrix.mul_zero, zero_add, Matrix.mul_assoc, h5, Matrix.mul_one]`.

Establish `memU' : ∀ g : Matrix n n A, cT σ g * J * g = J → g * X = X → cT σ (C * g * B) * (cT σ B * J * B) * (C * g * B) = cT σ B * J * B`. Introduce `g hg hgX`. Establish `e` using `h.preserves hg hgX`. Combine the equalities or inequalities in the displayed calculation. Establish `presU : ∀ s : S, B * (C * mat (s : UJ σ J) * B) = mat (s : UJ σ J) * B` using `fun s => h.preserves (mem_UJ_iff'.1 (s : UJ σ J).2) ((hS _).1 s.2)`.

Establish `hsi : ∀ s : S, mat (s : UJ σ J) * mat ((s⁻¹ : S) : UJ σ J) = 1` using `fun s => ((s : UJ σ J) : GL n A).mul_inv`. Establish `his : ∀ s : S, mat ((s⁻¹ : S) : UJ σ J) * mat (s : UJ σ J) = 1` using `fun s => ((s : UJ σ J) : GL n A).inv_mul`. Set `gm : S → GL m A` to `fun s => ⟨C * mat (s : UJ σ J) * B, C * mat ((s⁻¹ : S) : UJ σ J) * B, by`. Rewrite using `[Matrix.mul_assoc (C * mat (s : UJ σ J)) B, presU s⁻¹, ← Matrix.mul_assoc, Matrix.mul_assoc C, hsi, Matrix.mul_one, h1], by`. Rewrite using `[Matrix.mul_assoc (C * mat ((s⁻¹ : S) : UJ σ J)) B, presU s, ← Matrix.mul_assoc, Matrix.mul_assoc C, his, Matrix.mul_one, h1]⟩`.

Use `⟨{ toFun := fun u => ⟨⟨Units.map h.ext (u : GL m A), mem_UJ_iff'.2 (by` and prove the remaining obligations. Rewrite using `[Units.coe_map]; exact memU _ (mem_UJ_iff'.1 u.2))⟩, (hS _).2 (by`. Use `show (Units.map h.ext (u : GL m A) : Matrix n n A) * X = X`. Rewrite using `[Units.coe_map]`. Conclude with `fixX _)⟩`.

Use `invFun := fun s => ⟨gm s, mem_UJ_iff'.2 (memU' _ (mem_UJ_iff'.1 (s : UJ σ J).2) ((hS _).1 s.2))⟩`. Use `left_inv := ?_, right_inv := ?_, map_mul' := ?_, continuous_toFun := ?_, continuous_invFun := ?_ }⟩`. Introduce `u`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Use `show C * (B * ((u : GL m A) : Matrix m m A) * C + X * Y) * B = ((u : GL m A) : Matrix m m A)`. Simplify using `only [Matrix.mul_add, Matrix.mul_assoc, e1, e3, h1, Matrix.mul_one, add_zero]`. Introduce `s`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Use `show B * (C * mat (s : UJ σ J) * B) * C + X * Y = mat (s : UJ σ J)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[presU s, (hS _).1 s.2]`. Use `_ = mat (s : UJ σ J) * (B * C + X * Y) := by simp only [Matrix.mul_add, Matrix.mul_assoc]`.

Use `_ = mat (s : UJ σ J) := by rw [h2, Matrix.mul_one]`. Introduce `u v`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `map_mul h.ext ((u : GL m A) : Matrix m m A) ((v : GL m A) : Matrix m m A)`. Use `Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _` and prove the remaining obligations. Rewrite using `[Units.continuous_iff]`. Establish `hu : Continuous fun u : UJ σ (cT σ B * J * B) => ((u : GL m A) : Matrix m m A)` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hui : Continuous fun u : UJ σ (cT σ B * J * B) => (((u : GL m A)⁻¹ : GL m A) : Matrix m m A)` using `Units.continuous_coe_inv.comp continuous_subtype_val`.

Conclude with `⟨((continuous_const.matrix_mul hu).matrix_mul continuous_const).add continuous_const, ((continuous_const.matrix_mul hui).matrix_mul continuous_const).add continuous_const⟩`. Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Rewrite using `[Units.continuous_iff]`. Establish `hs : Continuous fun s : S => (((s : UJ σ J) : GL n A) : Matrix n n A)` using `Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)`. Establish `hsi' : Continuous fun s : S => ((((s : UJ σ J) : GL n A)⁻¹ : GL n A) : Matrix n n A)` using `Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)`.

Conclude with `⟨(continuous_const.matrix_mul hs).matrix_mul continuous_const, (continuous_const.matrix_mul hsi').matrix_mul continuous_const⟩`.
-/
theorem OrthSplit.exists_equiv [TopologicalSpace A] [IsTopologicalRing A] (h : OrthSplit σ J B C X Y)
    (S : Subgroup (UJ σ J)) (hS : ∀ g, g ∈ S ↔ mat g * X = X) :
    Nonempty (UJ σ (cT σ B * J * B) ≃ₜ* S) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hJ⟩ := id h
  have e1 : ∀ {p : Type} (Z : Matrix m p A), C * (B * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e3 : ∀ {p : Type} (Z : Matrix k p A), C * (X * Z) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, h3, Matrix.zero_mul]
  have hext : ∀ g : Matrix m m A, h.ext g = B * g * C + X * Y := fun _ => rfl
  have memU : ∀ g : Matrix m m A, cT σ g * (cT σ B * J * B) * g = cT σ B * J * B →
      cT σ (h.ext g) * J * h.ext g = J := by
    intro g hg
    have e0 := h.form_ext 1
    rw [map_one] at e0
    simp only [cT_one_global_interpolation, Matrix.one_mul, Matrix.mul_one] at e0
    rw [h.form_ext g, hg, ← e0]
  have fixX : ∀ g : Matrix m m A, h.ext g * X = X := by
    intro g
    rw [hext, Matrix.add_mul, Matrix.mul_assoc (B * g) C X, h3, Matrix.mul_zero, zero_add, Matrix.mul_assoc, h5,
      Matrix.mul_one]
  have memU' : ∀ g : Matrix n n A, cT σ g * J * g = J → g * X = X →
      cT σ (C * g * B) * (cT σ B * J * B) * (C * g * B) = cT σ B * J * B := by
    intro g hg hgX
    have e := h.preserves hg hgX
    calc cT σ (C * g * B) * (cT σ B * J * B) * (C * g * B)
        = cT σ (B * (C * g * B)) * J * (B * (C * g * B)) := by rw [cT_mul σ B (C * g * B)]; simp only [Matrix.mul_assoc]
      _ = cT σ B * (cT σ g * J * g) * B := by rw [e, cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ B * J * B := by rw [hg]
  have presU : ∀ s : S, B * (C * mat (s : UJ σ J) * B) = mat (s : UJ σ J) * B := fun s =>
    h.preserves (mem_UJ_iff'.1 (s : UJ σ J).2) ((hS _).1 s.2)
  have hsi : ∀ s : S, mat (s : UJ σ J) * mat ((s⁻¹ : S) : UJ σ J) = 1 := fun s =>
    ((s : UJ σ J) : GL n A).mul_inv
  have his : ∀ s : S, mat ((s⁻¹ : S) : UJ σ J) * mat (s : UJ σ J) = 1 := fun s =>
    ((s : UJ σ J) : GL n A).inv_mul
  let gm : S → GL m A := fun s => ⟨C * mat (s : UJ σ J) * B, C * mat ((s⁻¹ : S) : UJ σ J) * B, by
      rw [Matrix.mul_assoc (C * mat (s : UJ σ J)) B, presU s⁻¹, ← Matrix.mul_assoc, Matrix.mul_assoc C, hsi,
        Matrix.mul_one, h1], by
      rw [Matrix.mul_assoc (C * mat ((s⁻¹ : S) : UJ σ J)) B, presU s, ← Matrix.mul_assoc, Matrix.mul_assoc C, his,
        Matrix.mul_one, h1]⟩
  refine ⟨{ toFun := fun u => ⟨⟨Units.map h.ext (u : GL m A), mem_UJ_iff'.2 (by
                rw [Units.coe_map]; exact memU _ (mem_UJ_iff'.1 u.2))⟩, (hS _).2 (by
                show (Units.map h.ext (u : GL m A) : Matrix n n A) * X = X
                rw [Units.coe_map]; exact fixX _)⟩
            invFun := fun s => ⟨gm s, mem_UJ_iff'.2 (memU' _ (mem_UJ_iff'.1 (s : UJ σ J).2) ((hS _).1 s.2))⟩
            left_inv := ?_, right_inv := ?_, map_mul' := ?_, continuous_toFun := ?_, continuous_invFun := ?_ }⟩
  · intro u
    apply Subtype.ext
    apply Units.ext
    show C * (B * ((u : GL m A) : Matrix m m A) * C + X * Y) * B = ((u : GL m A) : Matrix m m A)
    simp only [Matrix.mul_add, Matrix.mul_assoc, e1, e3, h1, Matrix.mul_one, add_zero]
  · intro s
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    show B * (C * mat (s : UJ σ J) * B) * C + X * Y = mat (s : UJ σ J)
    calc B * (C * mat (s : UJ σ J) * B) * C + X * Y = mat (s : UJ σ J) * B * C + mat (s : UJ σ J) * X * Y := by
          rw [presU s, (hS _).1 s.2]
      _ = mat (s : UJ σ J) * (B * C + X * Y) := by simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = mat (s : UJ σ J) := by rw [h2, Matrix.mul_one]
  · intro u v
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact map_mul h.ext ((u : GL m A) : Matrix m m A) ((v : GL m A) : Matrix m m A)
  · refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    rw [Units.continuous_iff]
    have hu : Continuous fun u : UJ σ (cT σ B * J * B) => ((u : GL m A) : Matrix m m A) :=
      Units.continuous_val.comp continuous_subtype_val
    have hui : Continuous fun u : UJ σ (cT σ B * J * B) => (((u : GL m A)⁻¹ : GL m A) : Matrix m m A) :=
      Units.continuous_coe_inv.comp continuous_subtype_val
    exact ⟨((continuous_const.matrix_mul hu).matrix_mul continuous_const).add continuous_const,
      ((continuous_const.matrix_mul hui).matrix_mul continuous_const).add continuous_const⟩
  · refine Continuous.subtype_mk ?_ _
    rw [Units.continuous_iff]
    have hs : Continuous fun s : S => (((s : UJ σ J) : GL n A) : Matrix n n A) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hsi' : Continuous fun s : S => ((((s : UJ σ J) : GL n A)⁻¹ : GL n A) : Matrix n n A) :=
      Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact ⟨(continuous_const.matrix_mul hs).matrix_mul continuous_const,
      (continuous_const.matrix_mul hsi').matrix_mul continuous_const⟩

end Blocks

/- English proof (translation)
Take `⟨hTG, hT2, hLC, hSC, hB, ⟨μ, hμ⟩, hR⟩` from `hG`. Use `hμ` as an intermediate fact. Establish `hT2H : T2Space H` using `e.symm.toHomeomorph.isEmbedding.t2Space`. Establish `hLCH : LocallyCompactSpace H` using `e.symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace`. Establish `hSCH : SecondCountableTopology H` using `e.symm.toHomeomorph.isEmbedding.secondCountableTopology`.

Use `⟨inferInstance, hT2H, hLCH, hSCH, inferInstance, ⟨μ.map e, ContinuousMulEquiv.isHaarMeasure_map μ e⟩, ?_⟩` and prove the remaining obligations. Introduce `ν hν`. Use `hν` as an intermediate fact. Establish `hν' : (ν.map e.symm).IsHaarMeasure` using `ContinuousMulEquiv.isHaarMeasure_map ν e.symm`. Use `hR _ hν'` as an intermediate fact.

Establish `hme : Measurable e` using `e.continuous.measurable`. Establish `hmes : Measurable e.symm` using `e.symm.continuous.measurable`. Establish `hid : (e ∘ e.symm : H → H) = id` using `funext fun x => e.apply_symm_apply x`. Establish `hνeq : ν = (ν.map e.symm).map e`. Rewrite using `[Measure.map_map hme hmes, hid, Measure.map_id]`.

Use `⟨fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[hνeq, Measure.map_map (measurable_mul_const h) hme]`. Establish `hc : (fun x => x * h) ∘ e = e ∘ (fun x => x * e.symm h)`. Use function extensionality and compare the values at `x`. Simplify using `[map_mul]`.

Rewrite using `[hc, ← Measure.map_map hme (measurable_mul_const _), Measure.IsMulRightInvariant.map_mul_right_eq_self]`.
-/
theorem isUnimodularLC_of_equiv {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (hG : IsUnimodularLC G) (e : G ≃ₜ* H) : IsUnimodularLC H := by
  obtain ⟨hTG, hT2, hLC, hSC, hB, ⟨μ, hμ⟩, hR⟩ := hG
  have := hμ
  have hT2H : T2Space H := e.symm.toHomeomorph.isEmbedding.t2Space
  have hLCH : LocallyCompactSpace H := e.symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hSCH : SecondCountableTopology H := e.symm.toHomeomorph.isEmbedding.secondCountableTopology
  refine ⟨inferInstance, hT2H, hLCH, hSCH, inferInstance, ⟨μ.map e, ContinuousMulEquiv.isHaarMeasure_map μ e⟩, ?_⟩
  intro ν hν
  have := hν
  have hν' : (ν.map e.symm).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν e.symm
  have := hR _ hν'
  have hme : Measurable e := e.continuous.measurable
  have hmes : Measurable e.symm := e.symm.continuous.measurable
  have hid : (e ∘ e.symm : H → H) = id := funext fun x => e.apply_symm_apply x
  have hνeq : ν = (ν.map e.symm).map e := by
    rw [Measure.map_map hme hmes, hid, Measure.map_id]
  refine ⟨fun h => ?_⟩
  rw [hνeq, Measure.map_map (measurable_mul_const h) hme]
  have hc : (fun x => x * h) ∘ e = e ∘ (fun x => x * e.symm h) := by
    funext x
    simp [map_mul]
  rw [hc, ← Measure.map_map hme (measurable_mul_const _), Measure.IsMulRightInvariant.map_mul_right_eq_self]

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `: IsModuleTopology R (R ⊗[F] E)` using `⟨rfl⟩`. Conclude with `IsModuleTopology.isTopologicalRing R (R ⊗[F] E)`.
-/
private theorem isTopologicalRing_tensorProduct {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalRing (R ⊗[F] E) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

/- English proof (translation)
Establish `hPQ : P * Q = 1`. Rewrite using `[← Matrix.inv_eq_left_inv hQ]`. Conclude with `Matrix.mul_nonsing_inv P (Matrix.isUnit_det_of_left_inverse hQ)`. Establish `hs : ∀ {s t : Type} (U V : Matrix (Fin (M + 1)) (Fin (M + 1)) A) (e : s → Fin (M + 1)) (f : t → Fin (M + 1)), U.submatrix e id * V.submatrix id f = (U * V).submatrix e f` using `fun U V e f => by`. Use extensionality with `i j`.

Simplify using `[Matrix.mul_apply]`. Establish `hs1 : ∀ {s : Type} (U V : Matrix (Fin (M + 1)) (Fin (M + 1)) A) (e : s → Fin (M + 1)), U.submatrix e id * V = (U * V).submatrix e id` using `fun U V e => by`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`. Establish `hcT : ∀ {s t : Type} (e : s → Fin (M + 1)) (f : t → Fin (M + 1)), cT σ (P.submatrix e f) = (cT σ P).submatrix f e` using `fun e f => by`.

Use extensionality with `i j`. Both sides reduce to the same expression. Unfold `OrthSplit`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hJ⟩` and prove the remaining obligations. Rewrite using `[hs, hQ]`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.submatrix_apply, Matrix.one_apply_ne (fun h => hij (Fin.succ_injective _ h)), Matrix.one_apply_ne hij]`.

Use extensionality with `i j`. Establish `e` using `congrFun (congrFun hPQ i) j`. Rewrite `e` using `[Matrix.mul_apply, Fin.sum_univ_succ]`. Rewrite using `[← e, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, add_comm]`. Both sides reduce to the same expression.

Rewrite using `[hs, hQ]`. Use extensionality with `i j`. Rewrite using `[Matrix.submatrix_apply, Matrix.one_apply_ne (Fin.succ_ne_zero i), Matrix.zero_apply]`. Rewrite using `[hs, hQ]`. Use extensionality with `i j`.

Rewrite using `[Matrix.submatrix_apply, Matrix.one_apply_ne (Fin.succ_ne_zero j).symm, Matrix.zero_apply]`. Rewrite using `[hs, hQ]`. Use extensionality with `i j`. Rewrite using `[Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]`. Simplify using the standard rewrite rules.

Rewrite using `[hcT, hs1, hs]`. Use extensionality with `i j`. Conclude with `h10 i`. Rewrite using `[hcT, hs1, hs]`. Use extensionality with `i j`.

Conclude with `h01 j`.
-/
private theorem orthSplit_submatrix_succ_of_zero_entries {A : Type} [CommRing A] {σ : A →+* A} {M : ℕ}
    {J P Q : Matrix (Fin (M + 1)) (Fin (M + 1)) A} (hQ : Q * P = 1)
    (h01 : ∀ j : Fin M, (cT σ P * J * P) 0 j.succ = 0) (h10 : ∀ j : Fin M, (cT σ P * J * P) j.succ 0 = 0) (hJ : IsUnit J) :
    OrthSplit σ J (P.submatrix id Fin.succ) (Q.submatrix Fin.succ id) (P.submatrix id fun _ : Fin 1 => 0)
      (Q.submatrix (fun _ : Fin 1 => 0) id) := by
  have hPQ : P * Q = 1 := by
    rw [← Matrix.inv_eq_left_inv hQ]
    exact Matrix.mul_nonsing_inv P (Matrix.isUnit_det_of_left_inverse hQ)
  have hs : ∀ {s t : Type} (U V : Matrix (Fin (M + 1)) (Fin (M + 1)) A) (e : s → Fin (M + 1)) (f : t → Fin (M + 1)),
      U.submatrix e id * V.submatrix id f = (U * V).submatrix e f := fun U V e f => by
    ext i j
    simp [Matrix.mul_apply]
  have hs1 : ∀ {s : Type} (U V : Matrix (Fin (M + 1)) (Fin (M + 1)) A) (e : s → Fin (M + 1)),
      U.submatrix e id * V = (U * V).submatrix e id := fun U V e => by
    ext i j
    simp [Matrix.mul_apply]
  have hcT : ∀ {s t : Type} (e : s → Fin (M + 1)) (f : t → Fin (M + 1)),
      cT σ (P.submatrix e f) = (cT σ P).submatrix f e := fun e f => by
    ext i j
    rfl
  unfold OrthSplit
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hJ⟩
  · rw [hs, hQ]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.submatrix_apply, Matrix.one_apply_ne (fun h => hij (Fin.succ_injective _ h)), Matrix.one_apply_ne hij]
  · ext i j
    have e := congrFun (congrFun hPQ i) j
    rw [Matrix.mul_apply, Fin.sum_univ_succ] at e
    rw [← e, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, add_comm]
    rfl
  · rw [hs, hQ]
    ext i j
    rw [Matrix.submatrix_apply, Matrix.one_apply_ne (Fin.succ_ne_zero i), Matrix.zero_apply]
  · rw [hs, hQ]
    ext i j
    rw [Matrix.submatrix_apply, Matrix.one_apply_ne (Fin.succ_ne_zero j).symm, Matrix.zero_apply]
  · rw [hs, hQ]
    ext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simp
  · rw [hcT, hs1, hs]
    ext i j
    exact h10 i
  · rw [hcT, hs1, hs]
    ext i j
    exact h01 j

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7, hJ⟩` from `h`. Establish `m0 : ∀ {p q : Type}, (0 : Matrix p q A).map π = 0` using `Matrix.map_zero _ (map_zero π)`. Establish `m1 : ∀ {p : Type} [DecidableEq p], (1 : Matrix p p A).map π = 1` using `Matrix.map_one _ (map_zero π) (map_one π)`. Establish `hc : ∀ {p q : Type} (Z : Matrix p q A), (cT σ Z).map π = cT σ' (Z.map π)` using `fun Z => by`. Use extensionality with `i j`.

Conclude with `hπ (Z j i)`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hJ.map π.mapMatrix⟩` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, h1, m1]`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π), h2, m1]`. Rewrite using `[← Matrix.map_mul, h3, m0]`.

Rewrite using `[← Matrix.map_mul, h4, m0]`. Rewrite using `[← Matrix.map_mul, h5, m1]`. Rewrite using `[← hc, ← Matrix.map_mul, ← Matrix.map_mul, h6, m0]`. Rewrite using `[← hc, ← Matrix.map_mul, ← Matrix.map_mul, h7, m0]`.
-/
private theorem orthSplit_map {A A' : Type} [CommRing A] [CommRing A'] {n m k : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k] {σ : A →+* A} {σ' : A' →+* A'} {π : A →+* A'}
    (hπ : ∀ x, π (σ x) = σ' (π x)) {J : Matrix n n A} {B : Matrix n m A} {C : Matrix m n A} {X : Matrix n k A}
    {Y : Matrix k n A} (h : OrthSplit σ J B C X Y) :
    OrthSplit σ' (J.map π) (B.map π) (C.map π) (X.map π) (Y.map π) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hJ⟩ := h
  have m0 : ∀ {p q : Type}, (0 : Matrix p q A).map π = 0 := Matrix.map_zero _ (map_zero π)
  have m1 : ∀ {p : Type} [DecidableEq p], (1 : Matrix p p A).map π = 1 := Matrix.map_one _ (map_zero π) (map_one π)
  have hc : ∀ {p q : Type} (Z : Matrix p q A), (cT σ Z).map π = cT σ' (Z.map π) := fun Z => by
    ext i j
    exact hπ (Z j i)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hJ.map π.mapMatrix⟩
  · rw [← Matrix.map_mul, h1, m1]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π), h2, m1]
  · rw [← Matrix.map_mul, h3, m0]
  · rw [← Matrix.map_mul, h4, m0]
  · rw [← Matrix.map_mul, h5, m1]
  · rw [← hc, ← Matrix.map_mul, ← Matrix.map_mul, h6, m0]
  · rw [← hc, ← Matrix.map_mul, ← Matrix.map_mul, h7, m0]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Formalism.UG.hform, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
private theorem cT_mul_mul_apply_eq_hform {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (J P : Matrix n n A)
    (a c : n) : (cT s P * J * P) a c = Formalism.UG.hform s J (fun i => P i a) (fun j => P j c) := by
  simp only [Matrix.mul_apply, Formalism.UG.hform, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

section Points

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

/- English proof (translation)
Use `isTopologicalRing_tensorProduct (F := F) (E := E) R` as an intermediate fact. Establish `hss' : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e` using `hss`. Establish `hJJ : cT (σ : E →+* E) J = J`. Use extensionality with `i j`. Conclude with `hJ.1 i j`.

Choose the witnesses or unpack the hypotheses as in `⟨M', rfl⟩ : ∃ M', M = M' + 1 := by`. Break down `M with _ | M'` into its components or cases. It suffices to derive a contradiction. Apply `hx` to reduce the goal to its premises. Simplify using `[hE, Formalism.UG.hform]`.

Conclude with `⟨M', rfl⟩`. Set `φ : (Fin (M' + 1) → E) →ₗ[E] E` to `{ toFun := fun v => hE σ J (x 0) v map_add' := fun v w => by simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib] map_smul' := fun c v => by`. Simplify using `only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `ring }`.

Establish `hφ : ∀ v, φ v = hE σ J (x 0) v` using `fun v => rfl`. Establish `hsurj : LinearMap.range φ = ⊤`. Use `LinearMap.range_eq_top.mpr fun c => ⟨(c / hE σ J (x 0) (x 0)) • x 0, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, hφ, smul_eq_mul, div_mul_cancel₀ _ hx]`. Establish `hK : Module.finrank E (LinearMap.ker φ) = M'`.

Establish `h1` using `LinearMap.finrank_range_add_finrank_ker φ`. Rewrite `h1` using `[hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Set `b` to `Module.finBasisOfFinrankEq E (LinearMap.ker φ) hK`. Set `v : Fin (M' + 1) → (Fin (M' + 1) → E)` to `Fin.cons (x 0) fun j => (b j : Fin (M' + 1) → E)`.

Establish `hli : LinearIndependent E v`. Use `linearIndependent_finCons.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `b.linearIndependent.map' (LinearMap.ker φ).subtype (Submodule.ker_subtype _)`. Introduce `hmem`. Establish `hle : Submodule.span E (Set.range fun j => (b j : Fin (M' + 1) → E)) ≤ LinearMap.ker φ` using `Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact (b j).2)`.

Conclude with `hx (LinearMap.mem_ker.mp (hle hmem))`. Set `P : Matrix (Fin (M' + 1)) (Fin (M' + 1)) E` to `(Matrix.of v)ᵀ`. Establish `hPu : IsUnit P` using `Matrix.linearIndependent_cols_iff_isUnit.mp (by simpa [P] using hli)`. Establish `hQ : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hPu)`. Establish `hP0 : (fun i => P i 0) = x 0`.

Use function extensionality and compare the values at `i`. Simplify using `[P, v]`. Establish `hPs : ∀ j : Fin M', (fun i => P i j.succ) = (b j : Fin (M' + 1) → E)` using `fun j => by`. Use function extensionality and compare the values at `i`. Simplify using `[P, v]`.

Establish `h01 : ∀ j : Fin M', (cT (σ : E →+* E) P * J * P) 0 j.succ = 0` using `fun j => by`. Rewrite using `[cT_mul_mul_apply_eq_hform, hP0, hPs]`. Conclude with `LinearMap.mem_ker.mp (b j).2`. Establish `h10 : ∀ j : Fin M', (cT (σ : E →+* E) P * J * P) j.succ 0 = 0` using `fun j => by`. Rewrite using `[cT_mul_mul_apply_eq_hform, ← GlobalTheory.AdelicUnimod.hform_symm (σ := (σ : E →+* E)) hss' hJJ, ← cT_mul_mul_apply_eq_hform, h01, map_zero]`.

Establish `hJu : IsUnit J` using `(Matrix.isUnit_iff_isUnit_det J).mpr (isUnit_iff_ne_zero.mpr hJ.2)`. Establish `hπ : ∀ e : E, inclR (F` using `F) R ((σ : E →+* E) e) = sigR R σ (inclR (F := F) R e) := fun e => by`. Simplify using `[inclR, sigR]`. Establish `hOSR` using `orthSplit_map hπ (orthSplit_submatrix_succ_of_zero_entries hQ h01 h10 hJu)`. Establish `hP0' : ∀ k, P k 0 = x 0 k` using `fun k => congrFun hP0 k`.

Establish `hS : ∀ g : ↥(Formalism.UG.UJ (sigR R σ) (JR (F` using `F) R J)), (show HA R σ J from g) ∈ Hstab R σ J x ↔ mat g * (P.submatrix id fun _ : Fin 1 => 0).map (inclR (F := F) R) = (P.submatrix id fun _ : Fin 1 => 0).map (inclR (F := F) R) := by`. Introduce `g`. Establish `e1 : ∀ a i, ((show HA R σ J from g) • ratTup (F` using `F) R x) a i = (mat g * (P.submatrix id fun _ : Fin 1 => 0).map (inclR (F := F) R)) i a := by`. Introduce `a i`. Rewrite using `[Fin.fin_one_eq_zero a]`.

Use `show ∑ k, (mat g) i k * inclR (F := F) R (x 0 k) = ∑ k, (mat g) i k * inclR (F := F) R (P k 0)`. Simplify using `only [hP0']`. Establish `e2 : ∀ a i, ratTup (F` using `F) R x a i = (P.submatrix id fun _ : Fin 1 => 0).map (inclR (F := F) R) i a := by`. Introduce `a i`. Rewrite using `[Fin.fin_one_eq_zero a]`.

Use `show inclR (F := F) R (x 0 i) = inclR (F := F) R (P i 0)`. Rewrite using `[hP0']`. Rewrite using `[Hstab, MulAction.mem_stabilizer_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hg`.

Use extensionality with `i a`. Rewrite using `[← e1, ← e2, hg]`. Introduce `hg`. Use function extensionality and compare the values at `a i`. Rewrite using `[e1, e2, hg]`.

Take `⟨φe⟩` from `hOSR.exists_equiv (Hstab R σ J x) hS`. Establish `hsub : cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ = (cT (σ : E →+* E) P * J * P).submatrix Fin.succ Fin.succ`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.submatrix_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, id]`. Establish `hdetN : (cT (σ : E →+* E) P * J * P).det = (cT (σ : E →+* E) P * J * P) 0 0 * (cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ).det`.

Rewrite using `[Matrix.det_succ_row_zero, Fin.sum_univ_succ, hsub]`. Simplify using `only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, h01, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]`. Establish `hdetP : P.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det P).mp hPu).ne_zero`. Establish `hmd : (P.map (σ : E →+* E)).det = (σ : E →+* E) P.det` using `((σ : E →+* E).map_det P).symm`. Establish `hdetNne : (cT (σ : E →+* E) P * J * P).det ≠ 0`.

Rewrite using `[Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, hmd]`. Conclude with `mul_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hdetP) hJ.2) hdetP`. Establish `hherm : ∀ i j, σ ((cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ) j i) = (cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ) i j`. Introduce `i j`. Use `show (σ : E →+* E) _ = _`.

Rewrite using `[hsub, Matrix.submatrix_apply, Matrix.submatrix_apply, cT_mul_mul_apply_eq_hform, cT_mul_mul_apply_eq_hform, GlobalTheory.AdelicUnimod.hform_symm (σ := (σ : E →+* E)) hss' hJJ]`. Use `⟨M', cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ, ⟨hherm, fun h0 => hdetNne (by rw [hdetN, h0, mul_zero])⟩, ?_⟩` and prove the remaining obligations. Establish `hcm : ∀ {p q : Type} (Z : Matrix p q E), (cT (σ : E →+* E) Z).map (inclR (F` using `F) R) = cT (sigR R σ) (Z.map (inclR (F := F) R)) := fun Z => by`. Use extensionality with `i j`. Conclude with `hπ (Z j i)`.

Establish `hJ'R : JR R (cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ) = cT (sigR R σ) ((P.submatrix id Fin.succ).map (inclR (F` using `F) R)) * J.map (inclR (F := F) R) * (P.submatrix id Fin.succ).map (inclR (F := F) R) := by`. Rewrite using `[JR, Matrix.map_mul, Matrix.map_mul, hcm]`. Express the relevant statement in the definitionally equal form `Nonempty (↥(Formalism.UG.UJ (sigR R σ) (JR R _)) ≃ₜ* _)`. Rewrite using `[hJ'R]`. Conclude with `⟨φe⟩`.
-/
theorem exists_stab_equiv (hss : ∀ x, σ (σ x) = x) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (x : Fin 1 → Fin M → E) (hx : hE σ J (x 0) (x 0) ≠ 0) :
    ∃ (M' : ℕ) (J' : Matrix (Fin M') (Fin M') E), IsHermND σ J' ∧ Nonempty (HA R σ J' ≃ₜ* Hstab R σ J x) := by
  classical
  have := isTopologicalRing_tensorProduct (F := F) (E := E) R
  have hss' : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e := hss
  have hJJ : cT (σ : E →+* E) J = J := by
    ext i j
    exact hJ.1 i j
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := by
    rcases M with _ | M'
    · exfalso
      apply hx
      simp [hE, Formalism.UG.hform]
    · exact ⟨M', rfl⟩
  let φ : (Fin (M' + 1) → E) →ₗ[E] E :=
    { toFun := fun v => hE σ J (x 0) v
      map_add' := fun v w => by simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring }
  have hφ : ∀ v, φ v = hE σ J (x 0) v := fun v => rfl
  have hsurj : LinearMap.range φ = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun c => ⟨(c / hE σ J (x 0) (x 0)) • x 0, ?_⟩
    rw [LinearMap.map_smul, hφ, smul_eq_mul, div_mul_cancel₀ _ hx]
  have hK : Module.finrank E (LinearMap.ker φ) = M' := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker φ) hK
  let v : Fin (M' + 1) → (Fin (M' + 1) → E) := Fin.cons (x 0) fun j => (b j : Fin (M' + 1) → E)
  have hli : LinearIndependent E v := by
    refine linearIndependent_finCons.mpr ⟨?_, ?_⟩
    · exact b.linearIndependent.map' (LinearMap.ker φ).subtype (Submodule.ker_subtype _)
    · intro hmem
      have hle : Submodule.span E (Set.range fun j => (b j : Fin (M' + 1) → E)) ≤ LinearMap.ker φ :=
        Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact (b j).2)
      exact hx (LinearMap.mem_ker.mp (hle hmem))
  let P : Matrix (Fin (M' + 1)) (Fin (M' + 1)) E := (Matrix.of v)ᵀ
  have hPu : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp (by simpa [P] using hli)
  have hQ : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hPu)
  have hP0 : (fun i => P i 0) = x 0 := by
    funext i
    simp [P, v]
  have hPs : ∀ j : Fin M', (fun i => P i j.succ) = (b j : Fin (M' + 1) → E) := fun j => by
    funext i
    simp [P, v]
  have h01 : ∀ j : Fin M', (cT (σ : E →+* E) P * J * P) 0 j.succ = 0 := fun j => by
    rw [cT_mul_mul_apply_eq_hform, hP0, hPs]
    exact LinearMap.mem_ker.mp (b j).2
  have h10 : ∀ j : Fin M', (cT (σ : E →+* E) P * J * P) j.succ 0 = 0 := fun j => by
    rw [cT_mul_mul_apply_eq_hform, ← GlobalTheory.AdelicUnimod.hform_symm (σ := (σ : E →+* E)) hss' hJJ, ← cT_mul_mul_apply_eq_hform, h01, map_zero]
  have hJu : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).mpr (isUnit_iff_ne_zero.mpr hJ.2)
  have hπ : ∀ e : E, inclR (F := F) R ((σ : E →+* E) e) = sigR R σ (inclR (F := F) R e) := fun e => by
    simp [inclR, sigR]
  have hOSR := orthSplit_map hπ (orthSplit_submatrix_succ_of_zero_entries hQ h01 h10 hJu)
  have hP0' : ∀ k, P k 0 = x 0 k := fun k => congrFun hP0 k
  have hS : ∀ g : ↥(Formalism.UG.UJ (sigR R σ) (JR (F := F) R J)), (show HA R σ J from g) ∈ Hstab R σ J x ↔
      mat g * (P.submatrix id fun _ : Fin 1 => 0).map (inclR (F := F) R) =
        (P.submatrix id fun _ : Fin 1 => 0).map (inclR (F := F) R) := by
    intro g
    have e1 : ∀ a i, ((show HA R σ J from g) • ratTup (F := F) R x) a i =
        (mat g * (P.submatrix id fun _ : Fin 1 => 0).map (inclR (F := F) R)) i a := by
      intro a i
      rw [Fin.fin_one_eq_zero a]
      show ∑ k, (mat g) i k * inclR (F := F) R (x 0 k) = ∑ k, (mat g) i k * inclR (F := F) R (P k 0)
      simp only [hP0']
    have e2 : ∀ a i, ratTup (F := F) R x a i = (P.submatrix id fun _ : Fin 1 => 0).map (inclR (F := F) R) i a := by
      intro a i
      rw [Fin.fin_one_eq_zero a]
      show inclR (F := F) R (x 0 i) = inclR (F := F) R (P i 0)
      rw [hP0']
    rw [Hstab, MulAction.mem_stabilizer_iff]
    constructor
    · intro hg
      ext i a
      rw [← e1, ← e2, hg]
    · intro hg
      funext a i
      rw [e1, e2, hg]
  obtain ⟨φe⟩ := hOSR.exists_equiv (Hstab R σ J x) hS
  have hsub : cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ
      = (cT (σ : E →+* E) P * J * P).submatrix Fin.succ Fin.succ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, id]
  have hdetN : (cT (σ : E →+* E) P * J * P).det =
      (cT (σ : E →+* E) P * J * P) 0 0 * (cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, hsub]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, h01, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
  have hdetP : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp hPu).ne_zero
  have hmd : (P.map (σ : E →+* E)).det = (σ : E →+* E) P.det := ((σ : E →+* E).map_det P).symm
  have hdetNne : (cT (σ : E →+* E) P * J * P).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, hmd]
    exact mul_ne_zero (mul_ne_zero ((map_ne_zero _).mpr hdetP) hJ.2) hdetP
  have hherm : ∀ i j, σ ((cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ) j i) =
      (cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ) i j := by
    intro i j
    show (σ : E →+* E) _ = _
    rw [hsub, Matrix.submatrix_apply, Matrix.submatrix_apply, cT_mul_mul_apply_eq_hform, cT_mul_mul_apply_eq_hform,
      GlobalTheory.AdelicUnimod.hform_symm (σ := (σ : E →+* E)) hss' hJJ]
  refine ⟨M', cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ,
    ⟨hherm, fun h0 => hdetNne (by rw [hdetN, h0, mul_zero])⟩, ?_⟩
  have hcm : ∀ {p q : Type} (Z : Matrix p q E), (cT (σ : E →+* E) Z).map (inclR (F := F) R) = cT (sigR R σ) (Z.map (inclR (F := F) R)) :=
    fun Z => by
      ext i j
      exact hπ (Z j i)
  have hJ'R : JR R (cT (σ : E →+* E) (P.submatrix id Fin.succ) * J * P.submatrix id Fin.succ) =
      cT (sigR R σ) ((P.submatrix id Fin.succ).map (inclR (F := F) R)) * J.map (inclR (F := F) R) *
        (P.submatrix id Fin.succ).map (inclR (F := F) R) := by
    rw [JR, Matrix.map_mul, Matrix.map_mul, hcm]
  change Nonempty (↥(Formalism.UG.UJ (sigR R σ) (JR R _)) ≃ₜ* _)
  rw [hJ'R]
  exact ⟨φe⟩

/- English proof (translation)
Use `⟨h M J hJ, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨M', J', hJ', ⟨e⟩⟩` from `exists_stab_equiv R hss hJ x hx`. Use `isTopologicalRing_tensorProduct (F := F) (E := E) R` as an intermediate fact. Establish `: IsTopologicalGroup (HA R σ J)` using `inferInstanceAs (IsTopologicalGroup ↥(Formalism.UG.UJ (sigR R σ) (JR R J)))`. Establish `: BorelSpace (HA R σ J)` using `⟨rfl⟩`.

Conclude with `isUnimodularLC_of_equiv (h M' J' hJ') e`.
-/
theorem unimodularOver_of_forall (hss : ∀ x, σ (σ x) = x)
    (h : ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsUnimodularLC (HA R σ J))
    {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : UnimodularOver R σ J := by
  refine ⟨h M J hJ, fun x hx => ?_⟩
  obtain ⟨M', J', hJ', ⟨e⟩⟩ := exists_stab_equiv R hss hJ x hx
  have := isTopologicalRing_tensorProduct (F := F) (E := E) R
  have : IsTopologicalGroup (HA R σ J) :=
    inferInstanceAs (IsTopologicalGroup ↥(Formalism.UG.UJ (sigR R σ) (JR R J)))
  have : BorelSpace (HA R σ J) := ⟨rfl⟩
  exact isUnimodularLC_of_equiv (h M' J' hJ') e

/- English proof (translation)
Use `isTopologicalRing_tensorProduct (F := F) (E := E) R` as an intermediate fact. Establish `hFD : FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `: IsModuleTopology R (R ⊗[F] E)` using `⟨rfl⟩`. Set `eL` to `(Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun`. Establish `hc1 : Continuous eL` using `IsModuleTopology.continuous_of_linearMap eL.toLinearMap`.

Establish `hc2 : Continuous eL.symm` using `IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap`. Set `eH : (R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R)` to `{ toEquiv := eL.toEquiv, continuous_toFun := hc1, continuous_invFun := hc2 }`. Establish `: T2Space (R ⊗[F] E)` using `eH.isEmbedding.t2Space`. Establish `: LocallyCompactSpace (R ⊗[F] E)` using `eH.isClosedEmbedding.locallyCompactSpace`. Establish `: SecondCountableTopology (R ⊗[F] E)` using `eH.isEmbedding.secondCountableTopology`.

Establish `: LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E))` using `inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))`. Establish `: SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))` using `inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))`. Establish `: T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E))` using `inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))`. Establish `: LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ` using `MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace`. Establish `: SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ` using `MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`.

Establish `: T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ` using `MulOpposite.opHomeomorph.symm.isEmbedding.t2Space`. Establish `hemb` using `Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (R ⊗[F] E))`. Establish `: LocallyCompactSpace (GL (Fin M) (R ⊗[F] E))` using `hemb.locallyCompactSpace`. Establish `: SecondCountableTopology (GL (Fin M) (R ⊗[F] E))` using `hemb.isEmbedding.secondCountableTopology`. Establish `: T2Space (GL (Fin M) (R ⊗[F] E))` using `hemb.isEmbedding.t2Space`.

Establish `hsig : ⇑(sigR R σ) = ⇑((σ.toLinearMap : E →ₗ[F] E).baseChange R)`. Use function extensionality and compare the values at `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [sigR]`.

Consider the case `add y z hy hz => simp only [map_add, hy, hz]`. Establish `hs'c : Continuous (sigR R σ)`. Rewrite using `[hsig]`. Conclude with `IsModuleTopology.continuous_of_linearMap _`. Establish `hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))` using `Units.continuous_val`.

Establish `hclosed : IsClosed (Formalism.UG.UJ (sigR R σ) (JR R J) : Set (GL (Fin M) (R ⊗[F] E)))` using `isClosed_eq (((hv.matrix_map hs'c).matrix_transpose.matrix_mul continuous_const).matrix_mul hv) continuous_const`. Establish `: LocallyCompactSpace (HA R σ J)` using `hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: SecondCountableTopology (HA R σ J)` using `hclosed.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology`. Establish `: T2Space (HA R σ J)` using `inferInstanceAs (T2Space ↥(Formalism.UG.UJ (sigR R σ) (JR R J)))`. Establish `: IsTopologicalGroup (HA R σ J)` using `inferInstanceAs (IsTopologicalGroup ↥(Formalism.UG.UJ (sigR R σ) (JR R J)))`.

Establish `: BorelSpace (HA R σ J)` using `⟨rfl⟩`. Use `⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ⟨Measure.haar, inferInstance⟩, fun μ hμ => ?_⟩` and prove the remaining obligations. Use `hμ` as an intermediate fact. Establish `hJJ : cT (σ : E →+* E) J = J`. Use extensionality with `i j`.

Conclude with `hJ.1 i j`. Establish `hπ : ∀ e : E, inclR (F` using `F) R ((σ : E →+* E) e) = sigR R σ (inclR (F := F) R e) := fun e => by`. Simplify using `[inclR, sigR]`. Take `⟨Mm, hFr⟩` from `GlobalTheory.AdelicUnimod.exists_framed (σ := (σ : E →+* E)) hss hJJ hJ.2`. Establish `hFrR` using `hFr.map hπ`.

Take `⟨T, hTc, hTT, hT⟩` from `GlobalTheory.AdelicUnimod.exists_involution hs'c (GlobalTheory.AdelicPointsUnimod.sigR_sigR hss) hFrR`. Set `T' : HA R σ J →* HA R σ J` to `T`. Establish `hmod : ∀ g : HA R σ J, Measure.modularCharacter (T' g) = Measure.modularCharacter g` using `GlobalTheory.AdelicUnimod.modular_involution (G := HA R σ J) T' hTc hTT`. Establish `hArt : IsArtinianRing (R ⊗[F] E)` using `IsArtinianRing.of_finite R (R ⊗[F] E)`. Set `_ : Algebra ℚ (R ⊗[F] E)` to `((algebraMap F (R ⊗[F] E)).comp (algebraMap ℚ F)).toAlgebra`.

Establish `hgen : GlobalTheory.AdelicUnimod.Generic (sigR R σ)` using `GlobalTheory.AdelicUnimod.generic_of_semilocal ((isUnit_iff_ne_zero.mpr hδ).map (inclR (F := F) R)) (by rw [← hπ]; simp [hσδ])`. Establish `hχ : ∀ g : HA R σ J, Measure.modularCharacter g = 1` using `fun g => GlobalTheory.AdelicUnimod.char_eq_one (GlobalTheory.AdelicPointsUnimod.sigR_sigR hss) hFrR hgen (Measure.modularCharacter : HA R σ J →* NNReal) (fun g g' hg => by`. Rewrite using `[hT g g' hg]`. Conclude with `hmod g) g`. Conclude with `⟨fun g => by rw [GlobalTheory.AdelicUnimod.map_mul_right_eq μ g, hχ g, one_smul]⟩`.
-/
theorem isUnimodularLC_of_artinian [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [IsArtinianRing R] (hss : ∀ x, σ (σ x) = x) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : IsUnimodularLC (HA R σ J) := by
  classical
  have := isTopologicalRing_tensorProduct (F := F) (E := E) R
  have hFD : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let eL := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  have hc1 : Continuous eL := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
  have hc2 : Continuous eL.symm := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap
  let eH : (R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R) :=
    { toEquiv := eL.toEquiv, continuous_toFun := hc1, continuous_invFun := hc2 }
  have : T2Space (R ⊗[F] E) := eH.isEmbedding.t2Space
  have : LocallyCompactSpace (R ⊗[F] E) := eH.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (R ⊗[F] E) := eH.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))
  have : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E)) := inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))
  have : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.t2Space
  have hemb := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (R ⊗[F] E))
  have : LocallyCompactSpace (GL (Fin M) (R ⊗[F] E)) := hemb.locallyCompactSpace
  have : SecondCountableTopology (GL (Fin M) (R ⊗[F] E)) := hemb.isEmbedding.secondCountableTopology
  have : T2Space (GL (Fin M) (R ⊗[F] E)) := hemb.isEmbedding.t2Space
  have hsig : ⇑(sigR R σ) = ⇑((σ.toLinearMap : E →ₗ[F] E).baseChange R) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hs'c : Continuous (sigR R σ) := by
    rw [hsig]
    exact IsModuleTopology.continuous_of_linearMap _
  have hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val
  have hclosed : IsClosed (Formalism.UG.UJ (sigR R σ) (JR R J) : Set (GL (Fin M) (R ⊗[F] E))) :=
    isClosed_eq (((hv.matrix_map hs'c).matrix_transpose.matrix_mul continuous_const).matrix_mul hv)
      continuous_const
  have : LocallyCompactSpace (HA R σ J) := hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HA R σ J) :=
    hclosed.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have : T2Space (HA R σ J) := inferInstanceAs (T2Space ↥(Formalism.UG.UJ (sigR R σ) (JR R J)))
  have : IsTopologicalGroup (HA R σ J) :=
    inferInstanceAs (IsTopologicalGroup ↥(Formalism.UG.UJ (sigR R σ) (JR R J)))
  have : BorelSpace (HA R σ J) := ⟨rfl⟩
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun μ hμ => ?_⟩
  have := hμ
  have hJJ : cT (σ : E →+* E) J = J := by
    ext i j
    exact hJ.1 i j
  have hπ : ∀ e : E, inclR (F := F) R ((σ : E →+* E) e) = sigR R σ (inclR (F := F) R e) := fun e => by
    simp [inclR, sigR]
  obtain ⟨Mm, hFr⟩ := GlobalTheory.AdelicUnimod.exists_framed (σ := (σ : E →+* E)) hss hJJ hJ.2
  have hFrR := hFr.map hπ
  obtain ⟨T, hTc, hTT, hT⟩ := GlobalTheory.AdelicUnimod.exists_involution hs'c (GlobalTheory.AdelicPointsUnimod.sigR_sigR hss) hFrR
  let T' : HA R σ J →* HA R σ J := T
  have hmod : ∀ g : HA R σ J, Measure.modularCharacter (T' g) = Measure.modularCharacter g :=
    GlobalTheory.AdelicUnimod.modular_involution (G := HA R σ J) T' hTc hTT
  have hArt : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R (R ⊗[F] E)
  let _ : Algebra ℚ (R ⊗[F] E) := ((algebraMap F (R ⊗[F] E)).comp (algebraMap ℚ F)).toAlgebra
  have hgen : GlobalTheory.AdelicUnimod.Generic (sigR R σ) :=
    GlobalTheory.AdelicUnimod.generic_of_semilocal ((isUnit_iff_ne_zero.mpr hδ).map (inclR (F := F) R)) (by rw [← hπ]; simp [hσδ])
  have hχ : ∀ g : HA R σ J, Measure.modularCharacter g = 1 := fun g =>
    GlobalTheory.AdelicUnimod.char_eq_one (GlobalTheory.AdelicPointsUnimod.sigR_sigR hss) hFrR hgen
      (Measure.modularCharacter : HA R σ J →* NNReal) (fun g g' hg => by
        rw [hT g g' hg]
        exact hmod g) g
  exact ⟨fun g => by rw [GlobalTheory.AdelicUnimod.map_mul_right_eq μ g, hχ g, one_smul]⟩

/- English proof (translation)
Establish `hss : ∀ e, σ (σ e) = e` using `GlobalTheory.HermLineZeros.conj_invol hσ`. Take `⟨d, hd⟩` from `GlobalTheory.HermLineZeros.exists_conj_ne hσ`. Conclude with `unimodularOver_of_forall R hss (fun M' J' hJ' => isUnimodularLC_of_artinian R hss (δ := d - σ d) (sub_ne_zero.mpr (Ne.symm hd)) (by rw [map_sub, hss]; ring) hJ') hJ`.
-/
theorem unimodularOver_of_artinian [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [IsArtinianRing R] (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) :
    UnimodularOver R σ J := by
  have hss : ∀ e, σ (σ e) = e := GlobalTheory.HermLineZeros.conj_invol hσ
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hσ
  exact unimodularOver_of_forall R hss (fun M' J' hJ' => isUnimodularLC_of_artinian R hss (δ := d - σ d)
    (sub_ne_zero.mpr (Ne.symm hd)) (by rw [map_sub, hss]; ring) hJ') hJ

end Points

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ`. Establish `: T2Space (Ainf F)` using `inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))`. Establish `hsc : ∀ v : NumberField.InfinitePlace F, SecondCountableTopology v.Completion` using `fun v => (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology`. Establish `: SecondCountableTopology (Ainf F)` using `inferInstanceAs (SecondCountableTopology ((v : NumberField.InfinitePlace F) → v.Completion))`. Establish `: IsArtinianRing (Ainf F)` using `inferInstanceAs (IsArtinianRing ((v : NumberField.InfinitePlace F) → v.Completion))`.

Conclude with `unimodularOver_of_artinian (Ainf F) hσ hJ`.
-/
theorem unimodularOver_infinite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (Ainf F) σ J := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : T2Space (Ainf F) := inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  have hsc : ∀ v : NumberField.InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  have : SecondCountableTopology (Ainf F) :=
    inferInstanceAs (SecondCountableTopology ((v : NumberField.InfinitePlace F) → v.Completion))
  have : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing ((v : NumberField.InfinitePlace F) → v.Completion))
  exact unimodularOver_of_artinian (Ainf F) hσ hJ

end GlobalTheory.ArchUnitaryUnimod
