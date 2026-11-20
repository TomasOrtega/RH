import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivFinExtIntegersPadicIntOf
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
open Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.IntegralConjFinExt

open Matrix

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(PadicAlgCl.isNonarchimedean l _ _).trans (max_le (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))`.
-/
theorem norm_sum_le_one (l : ℕ) [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → PadicAlgCl l)
    (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (PadicAlgCl.isNonarchimedean l _ _).trans
      (max_le (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

/- English proof (translation)
Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem norm_one_apply_le (l : ℕ) [Fact l.Prime] (a : ℕ) (i j : Fin a) :
    ‖(1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

def intSubgroup (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}
    (ρ : Γ →* GL (Fin a) (PadicAlgCl l)) : Subgroup Γ where
  carrier := {g | ∀ i j, ‖(ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1 ∧
    ‖(ρ g⁻¹ : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1}
  one_mem' := fun i j => by
    simp only [inv_one, map_one, Units.val_one]
    exact ⟨norm_one_apply_le l a i j, norm_one_apply_le l a i j⟩
  mul_mem' := fun {g h} hg hh i j => by
    rw [_root_.mul_inv_rev, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
      Matrix.mul_apply]
    exact ⟨norm_sum_le_one l _ _ fun k _ => by
        rw [norm_mul]; exact mul_le_one₀ (hg i k).1 (norm_nonneg _) (hh k j).1,
      norm_sum_le_one l _ _ fun k _ => by
        rw [norm_mul]; exact mul_le_one₀ (hh i k).2 (norm_nonneg _) (hg k j).2⟩
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

/- English proof (translation)
Set `V : Set Γ` to `⋂ i, ⋂ j, ({g | ‖(ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j - (1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ < 1} ∩ {g | ‖(ρ g⁻¹ : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j - (1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ < 1})`. Establish `hVo : IsOpen V` using `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_lt (((hρ.matrix_elem i j).sub continuous_const).norm) continuous_const).inter (isOpen_lt ((((hρ.matrix_elem i j).comp continuous_inv).sub continuous_const).norm) continuous_const)`. Establish `hV1 : (1 : Γ) ∈ V`. Simplify using `only [V, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, inv_one, map_one, Units.val_one, sub_self, norm_zero, zero_lt_one, and_self, implies_true]`. Establish `hle : ∀ x y : PadicAlgCl l, ‖x - y‖ < 1 → ‖y‖ ≤ 1 → ‖x‖ ≤ 1` using `fun x y hxy hy => by`.

Use `PadicAlgCl.isNonarchimedean l (x - y) y` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Conclude with `this.trans (max_le hxy.le hy)`. Establish `hVU : V ⊆ (intSubgroup l ρ : Set Γ)` using `fun g hg i j => by`. Simplify using `only [V, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hg`.

Conclude with `⟨hle _ _ (hg i j).1 (norm_one_apply_le l a i j), hle _ _ (hg i j).2 (norm_one_apply_le l a i j)⟩`. Conclude with `Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hVo.mem_nhds hV1) hVU)`.
-/
theorem isOpen_intSubgroup (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) (PadicAlgCl l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))) :
    IsOpen (intSubgroup l ρ : Set Γ) := by
  let V : Set Γ := ⋂ i, ⋂ j,
    ({g | ‖(ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j - (1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ < 1} ∩
     {g | ‖(ρ g⁻¹ : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j - (1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ < 1})
  have hVo : IsOpen V :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_lt (((hρ.matrix_elem i j).sub continuous_const).norm) continuous_const).inter
        (isOpen_lt ((((hρ.matrix_elem i j).comp continuous_inv).sub continuous_const).norm) continuous_const)
  have hV1 : (1 : Γ) ∈ V := by
    simp only [V, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, inv_one, map_one, Units.val_one,
      sub_self, norm_zero, zero_lt_one, and_self, implies_true]
  have hle : ∀ x y : PadicAlgCl l, ‖x - y‖ < 1 → ‖y‖ ≤ 1 → ‖x‖ ≤ 1 := fun x y hxy hy => by
    have := PadicAlgCl.isNonarchimedean l (x - y) y
    rw [sub_add_cancel] at this
    exact this.trans (max_le hxy.le hy)
  have hVU : V ⊆ (intSubgroup l ρ : Set Γ) := fun g hg i j => by
    simp only [V, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hg
    exact ⟨hle _ _ (hg i j).1 (norm_one_apply_le l a i j), hle _ _ (hg i j).2 (norm_one_apply_le l a i j)⟩
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hVo.mem_nhds hV1) hVU)

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `l _ Γ _ _ _ _ _ a ρ hρ`. Use `letI : DecidableEq Γ := Classical.decEq Γ`. Take `⟨L, -, hL⟩` from `GlobalTheory.CompactRepField.exists_finExt_entries_mem l Γ a ρ hρ ⟨⊥, inferInstance⟩`. Use `haveI : FiniteDimensional ℚ_[l] L.1 := L.2`. Set `U` to `intSubgroup l ρ`.

Use `haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen _ (isOpen_intSubgroup l ρ hρ)`. Use `haveI : Fintype (Γ ⧸ U) := Fintype.ofFinite _`. Set `T : Finset Γ` to `Finset.univ.image (fun q : Γ ⧸ U => q.out)`. Establish `hTU : ∀ x : Γ, ∃ t ∈ T, t⁻¹ * x ∈ U`. Introduce `x`.

Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul U x`. Use `⟨(x : Γ ⧸ U).out, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hh, _root_.mul_inv_rev, inv_mul_cancel_right]`. Conclude with `U.inv_mem h.2`. Take `⟨r, hr⟩` from `GlobalTheory.StableLattice.lift_of_integral (O := L.1) (K := PadicAlgCl l) Subtype.val_injective ρ (fun g i j => ⟨⟨_, hL g i j⟩, rfl⟩)`.

Establish `hre : ∀ g i j, (((r g : GL (Fin a) L.1) : Matrix (Fin a) (Fin a) L.1) i j : PadicAlgCl l) = ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j`. Introduce `g i j`. Rewrite using `[← hr g, Matrix.GeneralLinearGroup.map_apply]`. Both sides reduce to the same expression. Set `e : L.1 ≃ₐ[Loc.OL L] FractionRing (Loc.OL L)` to `IsLocalization.algEquiv (nonZeroDivisors (Loc.OL L)) L.1 (FractionRing (Loc.OL L))`.

Set `σ : Γ →* GL (Fin a) (FractionRing (Loc.OL L))` to `(Matrix.GeneralLinearGroup.map e.toRingEquiv.toRingHom).comp r`. Establish `hσ : ∀ x : Γ, ∃ t ∈ T, ∀ i j, (σ (t⁻¹ * x)).val i j ∈ (algebraMap (Loc.OL L) (FractionRing (Loc.OL L))).range`. Introduce `x`. Take `⟨t, ht, hu⟩` from `hTU x`. Use `⟨t, ht, fun i j => ?_⟩` and prove the remaining obligations.

Establish `hmem : ((r (t⁻¹ * x) : GL (Fin a) L.1) : Matrix (Fin a) (Fin a) L.1) i j ∈ Loc.OL L`. Rewrite using `[Formalism.BasicNotions.Examples₂.LB.mem_OL, hre]`. Conclude with `(hu i j).1`. Use `⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [σ, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply]`.

Rewrite using `[← e.commutes]`. Both sides reduce to the same expression. Take `⟨P', hP'⟩` from `GlobalTheory.StableLattice.exists_conj_integral σ T hσ`. Set `φ : FractionRing (Loc.OL L) →+* PadicAlgCl l` to `(algebraMap L.1 (PadicAlgCl l)).comp e.symm.toRingEquiv.toRingHom`. Establish `hφσ : ∀ g, Matrix.GeneralLinearGroup.map φ (σ g) = ρ g`.

Introduce `g`. Rewrite using `[← hr g]`. Use extensionality with `i j`. Simplify using `only [σ, φ, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.comp_apply]`. Use `congr 1`.

Conclude with `e.symm_apply_apply _`. Use `⟨L, Matrix.GeneralLinearGroup.map φ P', fun g i k => ?_⟩` and prove the remaining obligations. Establish `h1 : (Matrix.GeneralLinearGroup.map φ P')⁻¹ * ρ g * Matrix.GeneralLinearGroup.map φ P' = Matrix.GeneralLinearGroup.map φ (P'⁻¹ * σ g * P')`. Rewrite using `[MonoidHom.map_mul (Matrix.GeneralLinearGroup.map φ), MonoidHom.map_mul (Matrix.GeneralLinearGroup.map φ), MonoidHom.map_inv (Matrix.GeneralLinearGroup.map φ), hφσ]`. It suffices to establish `key : ((Matrix.GeneralLinearGroup.map φ (P'⁻¹ * σ g * P') : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 by`.

Rewrite `key` using `[← h1]`. Conclude with `key`. Take `⟨z, hz⟩` from `hP' g i k`. Rewrite using `[Matrix.GeneralLinearGroup.map_apply, ← hz]`. Establish `h2 : φ (algebraMap (Loc.OL L) (FractionRing (Loc.OL L)) z) = (((z : L.1)) : PadicAlgCl l)`.

Simplify using `only [φ, RingHom.comp_apply]`. Rewrite using `[← e.commutes z]`. Use `show algebraMap L.1 (PadicAlgCl l) (e.symm (e _)) = _`. Rewrite using `[e.symm_apply_apply]`. Both sides reduce to the same expression.

Rewrite using `[h2, GlobalTheory.IntOfFinExt.mem_intOf_iff]`. Conclude with `⟨(z : L.1).2, (Formalism.BasicNotions.Examples₂.LB.mem_OL L _).1 z.2⟩`.
-/
theorem exists_finExt_conj_intOf : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) → ∃ (L : Loc.FinExt l) (P : GL (Fin a) (PadicAlgCl l)), ∀ g i k, ((P⁻¹ * ρ g * P : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 := by
  intro l _ Γ _ _ _ _ _ a ρ hρ
  letI : DecidableEq Γ := Classical.decEq Γ
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l Γ a ρ hρ ⟨⊥, inferInstance⟩
  haveI : FiniteDimensional ℚ_[l] L.1 := L.2
  let U := intSubgroup l ρ
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen _ (isOpen_intSubgroup l ρ hρ)
  haveI : Fintype (Γ ⧸ U) := Fintype.ofFinite _
  let T : Finset Γ := Finset.univ.image (fun q : Γ ⧸ U => q.out)
  have hTU : ∀ x : Γ, ∃ t ∈ T, t⁻¹ * x ∈ U := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U x
    refine ⟨(x : Γ ⧸ U).out, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [hh, _root_.mul_inv_rev, inv_mul_cancel_right]
    exact U.inv_mem h.2
  obtain ⟨r, hr⟩ := GlobalTheory.StableLattice.lift_of_integral (O := L.1) (K := PadicAlgCl l)
    Subtype.val_injective ρ (fun g i j => ⟨⟨_, hL g i j⟩, rfl⟩)
  have hre : ∀ g i j, (((r g : GL (Fin a) L.1) : Matrix (Fin a) (Fin a) L.1) i j : PadicAlgCl l) =
      ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j := by
    intro g i j
    rw [← hr g, Matrix.GeneralLinearGroup.map_apply]
    rfl
  let e : L.1 ≃ₐ[Loc.OL L] FractionRing (Loc.OL L) :=
    IsLocalization.algEquiv (nonZeroDivisors (Loc.OL L)) L.1 (FractionRing (Loc.OL L))
  let σ : Γ →* GL (Fin a) (FractionRing (Loc.OL L)) :=
    (Matrix.GeneralLinearGroup.map e.toRingEquiv.toRingHom).comp r
  have hσ : ∀ x : Γ, ∃ t ∈ T, ∀ i j, (σ (t⁻¹ * x)).val i j ∈
        (algebraMap (Loc.OL L) (FractionRing (Loc.OL L))).range := by
    intro x
    obtain ⟨t, ht, hu⟩ := hTU x
    refine ⟨t, ht, fun i j => ?_⟩
    have hmem : ((r (t⁻¹ * x) : GL (Fin a) L.1) : Matrix (Fin a) (Fin a) L.1) i j ∈ Loc.OL L := by
      rw [Formalism.BasicNotions.Examples₂.LB.mem_OL, hre]
      exact (hu i j).1
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only [σ, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply]
    rw [← e.commutes]
    rfl
  obtain ⟨P', hP'⟩ := GlobalTheory.StableLattice.exists_conj_integral σ T hσ
  let φ : FractionRing (Loc.OL L) →+* PadicAlgCl l :=
    (algebraMap L.1 (PadicAlgCl l)).comp e.symm.toRingEquiv.toRingHom
  have hφσ : ∀ g, Matrix.GeneralLinearGroup.map φ (σ g) = ρ g := by
    intro g
    rw [← hr g]
    ext i j
    simp only [σ, φ, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.comp_apply]
    congr 1
    exact e.symm_apply_apply _
  refine ⟨L, Matrix.GeneralLinearGroup.map φ P', fun g i k => ?_⟩
  have h1 : (Matrix.GeneralLinearGroup.map φ P')⁻¹ * ρ g * Matrix.GeneralLinearGroup.map φ P' =
      Matrix.GeneralLinearGroup.map φ (P'⁻¹ * σ g * P') := by
    rw [MonoidHom.map_mul (Matrix.GeneralLinearGroup.map φ), MonoidHom.map_mul (Matrix.GeneralLinearGroup.map φ),
      MonoidHom.map_inv (Matrix.GeneralLinearGroup.map φ), hφσ]
  suffices key : ((Matrix.GeneralLinearGroup.map φ (P'⁻¹ * σ g * P') : GL (Fin a) (PadicAlgCl l)) :
      Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 by
    rw [← h1] at key
    exact key
  obtain ⟨z, hz⟩ := hP' g i k
  rw [Matrix.GeneralLinearGroup.map_apply, ← hz]
  have h2 : φ (algebraMap (Loc.OL L) (FractionRing (Loc.OL L)) z) = (((z : L.1)) : PadicAlgCl l) := by
    simp only [φ, RingHom.comp_apply]
    rw [← e.commutes z]
    show algebraMap L.1 (PadicAlgCl l) (e.symm (e _)) = _
    rw [e.symm_apply_apply]
    rfl
  rw [h2, GlobalTheory.IntOfFinExt.mem_intOf_iff]
  exact ⟨(z : L.1).2, (Formalism.BasicNotions.Examples₂.LB.mem_OL L _).1 z.2⟩

end GlobalTheory.IntegralConjFinExt
