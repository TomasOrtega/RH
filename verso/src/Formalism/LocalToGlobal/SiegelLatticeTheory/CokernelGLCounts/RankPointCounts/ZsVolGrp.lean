import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolCut
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntLowMul

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolGrp

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular l (fun i j hij => h2 i j hij)]`. Conclude with `Finset.prod_eq_one fun i _ => h1 i`.
-/
theorem det_lo {l : Matrix (Fin n) (Fin n) R} (h1 : ∀ a, l a a = 1) (h2 : ∀ a b, a < b → l a b = 0) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j hij => h2 i j hij)]
  exact Finset.prod_eq_one fun i _ => h1 i

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => h2 i j hij)]`. Conclude with `Finset.prod_eq_one fun i _ => h1 i`.
-/
theorem det_up {l : Matrix (Fin n) (Fin n) R} (h1 : ∀ a, l a a = 1) (h2 : ∀ a b, b < a → l a b = 0) : l.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h2 i j hij)]
  exact Finset.prod_eq_one fun i _ => h1 i

/- English proof (translation)
Rewrite using `[Matrix.inv_def, h, Ring.inverse_one, one_smul]`.
-/
theorem inv_eq_adj {l : Matrix (Fin n) (Fin n) R} (h : l.det = 1) : l⁻¹ = l.adjugate := by
  rw [Matrix.inv_def, h, Ring.inverse_one, one_smul]

/- English proof (translation)
Set `lS : Matrix (Fin n) (Fin n) S` to `fun a b => ⟨l a b, h a b⟩`. Establish `e : l = S.subtype.mapMatrix lS`. Use extensionality with `a b`. Both sides reduce to the same expression. Rewrite using `[e, ← RingHom.map_adjugate]`.

Conclude with `(lS.adjugate i j).2`.
-/
theorem adj_mem (S : Subring R) {l : Matrix (Fin n) (Fin n) R} (h : ∀ a b, l a b ∈ S) (i j : Fin n) :
    l.adjugate i j ∈ S := by
  let lS : Matrix (Fin n) (Fin n) S := fun a b => ⟨l a b, h a b⟩
  have e : l = S.subtype.mapMatrix lS := by
    ext a b
    rfl
  rw [e, ← RingHom.map_adjugate]
  exact (lS.adjugate i j).2

end Uni

section Int

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
  [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne], fun a b => by rw [Matrix.one_apply]; split_ifs · exact one_mem _ · exact zero_mem _⟩`.
-/
theorem intLow_one : Formalism.MainNotions.S.TieN.IntLow Mp (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne], fun a b => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne'], fun a b => by rw [Matrix.one_apply]; split_ifs · exact one_mem _ · exact zero_mem _⟩`.
-/
theorem intUp_one : Formalism.MainNotions.S.TieN.IntUp Mp (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne'], fun a b => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

/- English proof (translation)
Apply the tactic sequence `first | exact GlobalTheory.LowerIntegralMul.intLow_mul .. | (apply GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (intros; apply GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (intros; appl …`.
-/
theorem intLow_mul {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l)
    (h' : Formalism.MainNotions.S.TieN.IntLow Mp l') : Formalism.MainNotions.S.TieN.IntLow Mp (l * l') := by
  first | exact GlobalTheory.LowerIntegralMul.intLow_mul .. | (apply GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (intros; apply GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (intros; apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' h h' | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' h | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E | exact @GlobalTheory.LowerIntegralMul.intLow_mul F

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Take `⟨h1', h2', h3'⟩` from `h'`. Use `⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[h1, h1', mul_one]`.

Introduce `c _ hc`. Break down `lt_or_gt_of_ne hc with h | h` into its components or cases. Rewrite using `[h2 a c h, zero_mul]`. Rewrite using `[h2' c a h, mul_zero]`. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Break down `lt_or_ge c a with h | h` into its components or cases. Rewrite using `[h2 a c h, zero_mul]`. Rewrite using `[h2' c b (lt_of_lt_of_le hab h), mul_zero]`.

Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun c _ => mul_mem (h3 a c) (h3' c b)`.
-/
theorem intUp_mul {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp l)
    (h' : Formalism.MainNotions.S.TieN.IntUp Mp l') : Formalism.MainNotions.S.TieN.IntUp Mp (l * l') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [h1, h1', mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [h2 a c h, zero_mul]
      · rw [h2' c a h, mul_zero]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [h2 a c h, zero_mul]
    · rw [h2' c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply]
    exact sum_mem fun c _ => mul_mem (h3 a c) (h3' c b)

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `hd` using `det_lo h1 h2`. Establish `hu : IsUnit l.det` using `by rw [hd]; exact isUnit_one`. Establish `hli : l⁻¹ * l = 1` using `Matrix.nonsing_inv_mul l hu`. Establish `hil : l * l⁻¹ = 1` using `Matrix.mul_nonsing_inv l hu`.

Use `Matrix.invertibleOfIsUnitDet l hu` as an intermediate fact. Establish `hb : l⁻¹.BlockTriangular OrderDual.toDual` using `Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h2 i j hij)`. Establish `hz : ∀ a b, a < b → l⁻¹ a b = 0` using `fun a b hab => hb hab`. Use `⟨⟨fun a => ?_, hz, fun a b => ?_⟩, hli, hil⟩` and prove the remaining obligations. Establish `e` using `congrFun (congrFun hil a) a`.

Rewrite `e` using `[Matrix.mul_apply, Finset.sum_eq_single a, h1, one_mul]`. Simplify using `using e`. Introduce `c _ hc`. Break down `lt_or_gt_of_ne hc with h | h` into its components or cases. Rewrite using `[hz c a h, mul_zero]`.

Rewrite using `[h2 a c h, zero_mul]`. Simplify using the standard rewrite rules. Rewrite using `[inv_eq_adj hd]`. Conclude with `adj_mem Mp.R h3 a b`.
-/
theorem intLow_inv {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l) :
    Formalism.MainNotions.S.TieN.IntLow Mp l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := det_lo h1 h2
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h2 i j hij)
  have hz : ∀ a b, a < b → l⁻¹ a b = 0 := fun a b hab => hb hab
  refine ⟨⟨fun a => ?_, hz, fun a b => ?_⟩, hli, hil⟩
  · have e := congrFun (congrFun hil a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, h1, one_mul] at e
    · simpa using e
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hz c a h, mul_zero]
      · rw [h2 a c h, zero_mul]
    · simp
  · rw [inv_eq_adj hd]
    exact adj_mem Mp.R h3 a b

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `hd` using `det_up h1 h2`. Establish `hu : IsUnit l.det` using `by rw [hd]; exact isUnit_one`. Establish `hli : l⁻¹ * l = 1` using `Matrix.nonsing_inv_mul l hu`. Establish `hil : l * l⁻¹ = 1` using `Matrix.mul_nonsing_inv l hu`.

Use `Matrix.invertibleOfIsUnitDet l hu` as an intermediate fact. Establish `hb : l⁻¹.BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h2 i j hij)`. Establish `hz : ∀ a b, b < a → l⁻¹ a b = 0` using `fun a b hab => hb hab`. Use `⟨⟨fun a => ?_, hz, fun a b => ?_⟩, hli, hil⟩` and prove the remaining obligations. Establish `e` using `congrFun (congrFun hil a) a`.

Rewrite `e` using `[Matrix.mul_apply, Finset.sum_eq_single a, h1, one_mul]`. Simplify using `using e`. Introduce `c _ hc`. Break down `lt_or_gt_of_ne hc with h | h` into its components or cases. Rewrite using `[h2 a c h, zero_mul]`.

Rewrite using `[hz c a h, mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[inv_eq_adj hd]`. Conclude with `adj_mem Mp.R h3 a b`.
-/
theorem intUp_inv {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp l) :
    Formalism.MainNotions.S.TieN.IntUp Mp l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := det_up h1 h2
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h2 i j hij)
  have hz : ∀ a b, b < a → l⁻¹ a b = 0 := fun a b hab => hb hab
  refine ⟨⟨fun a => ?_, hz, fun a b => ?_⟩, hli, hil⟩
  · have e := congrFun (congrFun hil a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, h1, one_mul] at e
    · simpa using e
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [h2 a c h, zero_mul]
      · rw [hz c a h, mul_zero]
    · simp
  · rw [inv_eq_adj hd]
    exact adj_mem Mp.R h3 a b

end Int

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [ZhatOM]`. Rewrite using `[← mul_assoc, ← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem zhatOM_zhatOM {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM (ZhatOM Z) = Z := by
  ext a b
  simp only [ZhatOM]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

end Formalism.L2.SG.Pf.ZsVolGrp

end
