import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EqAdeleSupportedAtFinitePlaceOfSupportedAt

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace Tw.LatParam
open _root_.GlobalTheory

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.vecMulVec_apply, Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply, zsmul_eq_mul]`. Rewrite using `[Finset.sum_mul_sum, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply, Pi.intCast_apply]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vecMulVec_sum_zsmul {E : Type} [Field E] {n d kx ky : ℕ} (ex : Fin kx → Fin n → E) (fy : Fin ky → Fin d → E)
    (c : Fin kx → ℤ) (c' : Fin ky → ℤ) :
    Matrix.vecMulVec (∑ i, c i • ex i) (∑ j, c' j • fy j) =
      ∑ m : Fin kx × Fin ky, (c m.1 * c' m.2) • Matrix.vecMulVec (ex m.1) (fy m.2) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply,
    zsmul_eq_mul]
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.mul_apply, Pi.intCast_apply]
  push_cast
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ n d X Y hX hY v`. Take `⟨kx, ex, hex⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 (hX.fg.restrictScalars (R := ℤ))`. Take `⟨ky, fy, hfy⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 (hY.fg.restrictScalars (R := ℤ))`. Establish `memX : ∀ x, x ∈ X.L ↔ ∃ c : Fin kx → ℤ, ∑ i, c i • ex i = x`. Introduce `x`.

Rewrite using `[← Submodule.restrictScalars_mem ℤ, ← hex, Submodule.mem_span_range_iff_exists_fun]`. Establish `memY : ∀ y, y ∈ Y.L ↔ ∃ c : Fin ky → ℤ, ∑ j, c j • fy j = y`. Introduce `y`. Rewrite using `[← Submodule.restrictScalars_mem ℤ, ← hfy, Submodule.mem_span_range_iff_exists_fun]`. Establish `exX : ∀ i, ex i ∈ X.L`.

Introduce `i`. Establish `h` using `Submodule.subset_span (R := ℤ) (Set.mem_range_self (f := ex) i)`. Rewrite `h` using `[hex]`. Conclude with `(Submodule.restrictScalars_mem ℤ _ _).1 h`. Establish `exY : ∀ j, fy j ∈ Y.L`.

Introduce `j`. Establish `h` using `Submodule.subset_span (R := ℤ) (Set.mem_range_self (f := fy) j)`. Rewrite `h` using `[hfy]`. Conclude with `(Submodule.restrictScalars_mem ℤ _ _).1 h`. Use `⟨Fin kx × Fin ky, inferInstance, fun m => Matrix.vecMulVec (ex m.1) (fy m.2), ?_⟩` and prove the remaining obligations.

Introduce `γ`. Set `φ : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)` to `(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).toAddMonoidHom.mapMatrix`. Establish `hφ : ∀ J, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J = φ J` using `fun J => rfl`. Establish `hsupp : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (⇑(GlobalTheory.AdelicU.evFin F v)) a → a = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a)`. Introduce `a ha`.

Establish `h1 : GlobalTheory.AdelicU.evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0`. Rewrite using `[map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]`. Establish `h2` using `ha _ h1`. Rewrite `h2` using `[smul_eq_mul, sub_mul, one_mul, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hdef : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v = AddSubgroup.closure {z | ∃ a, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (⇑(GlobalTheory.AdelicU.evFin F v)) a ∧ (GlobalTheory.AdelicU.evFin F v) a ∈ IsDedekindDomain.HeightOneSpectrum …` using `rfl`. Rewrite using `[hdef]`. Prove the components needed by the constructor for the conclusion. Introduce `hγ`. Proceed by induction on `hγ using AddSubgroup.closure_induction with`.

Consider the case `mem z hz`. Take `⟨a, ha, hav, x, hx, y, hy, rfl⟩` from `hz`. Take `⟨c, rfl⟩` from `(memX x).1 hx`. Take `⟨c', rfl⟩` from `(memY y).1 hy`. Use `⟨fun m => (c m.1 * c' m.2) • ⟨_, hav⟩, ?_⟩` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[vecMulVec_sum_zsmul, hφ, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, smul_comm, AddSubgroupClass.coe_zsmul, map_zsmul, smul_assoc, ← hsupp a ha, hφ]`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, by simp [Finset.sum_add_distrib, add_smul]⟩`. Consider the case `neg x _ hx`.

Take `⟨a, rfl⟩` from `hx`. Conclude with `⟨-a, by simp [neg_smul]⟩`. Introduce and unpack `⟨a, rfl⟩`. Use `AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ?_` and prove the remaining obligations. Use `⟨GlobalTheory.EmbChart.atPlace v (a m), GlobalTheory.VacAny.at_atPlace _, ?_, ex m.1, exX _, fy m.2, exY _, rfl⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.EmbChart.evFin_atPlace]`. Conclude with `(a m).2`.
-/
theorem latAtV_param : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    ∃ (M : Type) (_ : Fintype M) (g : M → Matrix (Fin n) (Fin d) E), ∀ γ,
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v ↔ ∃ a : M → v.adicCompletionIntegers F,
        γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m) := by
  intro F E _ _ _ _ _ n d X Y hX hY v
  classical
  obtain ⟨kx, ex, hex⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hX.fg.restrictScalars (R := ℤ))
  obtain ⟨ky, fy, hfy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hY.fg.restrictScalars (R := ℤ))
  have memX : ∀ x, x ∈ X.L ↔ ∃ c : Fin kx → ℤ, ∑ i, c i • ex i = x := by
    intro x
    rw [← Submodule.restrictScalars_mem ℤ, ← hex, Submodule.mem_span_range_iff_exists_fun]
  have memY : ∀ y, y ∈ Y.L ↔ ∃ c : Fin ky → ℤ, ∑ j, c j • fy j = y := by
    intro y
    rw [← Submodule.restrictScalars_mem ℤ, ← hfy, Submodule.mem_span_range_iff_exists_fun]
  have exX : ∀ i, ex i ∈ X.L := by
    intro i
    have h := Submodule.subset_span (R := ℤ) (Set.mem_range_self (f := ex) i)
    rw [hex] at h
    exact (Submodule.restrictScalars_mem ℤ _ _).1 h
  have exY : ∀ j, fy j ∈ Y.L := by
    intro j
    have h := Submodule.subset_span (R := ℤ) (Set.mem_range_self (f := fy) j)
    rw [hfy] at h
    exact (Submodule.restrictScalars_mem ℤ _ _).1 h
  refine ⟨Fin kx × Fin ky, inferInstance, fun m => Matrix.vecMulVec (ex m.1) (fy m.2), ?_⟩
  intro γ
  let φ : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :=
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).toAddMonoidHom.mapMatrix
  have hφ : ∀ J, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J = φ J := fun J => rfl
  have hsupp : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (⇑(GlobalTheory.AdelicU.evFin F v)) a →
      a = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by
    intro a ha
    have h1 : GlobalTheory.AdelicU.evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
      rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
    have h2 := ha _ h1
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h2
    calc a = GlobalTheory.EmbChart.atPlace v 1 * a := h2
      _ = GlobalTheory.EmbChart.atPlace v (1 * GlobalTheory.AdelicU.evFin F v a) := GlobalTheory.EmbChart.atPlace_mul_right v 1 a
      _ = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by rw [one_mul]
  have hdef : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v = AddSubgroup.closure {z |
      ∃ a, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (⇑(GlobalTheory.AdelicU.evFin F v)) a ∧
        (GlobalTheory.AdelicU.evFin F v) a ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v ∧
          ∃ x ∈ X.L, ∃ y ∈ Y.L, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (Matrix.vecMulVec x y)} := rfl
  rw [hdef]
  constructor
  · intro hγ
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
      obtain ⟨c, rfl⟩ := (memX x).1 hx
      obtain ⟨c', rfl⟩ := (memY y).1 hy
      refine ⟨fun m => (c m.1 * c' m.2) • ⟨_, hav⟩, ?_⟩
      beta_reduce
      rw [vecMulVec_sum_zsmul, hφ, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_zsmul, smul_comm, AddSubgroupClass.coe_zsmul, map_zsmul, smul_assoc, ← hsupp a ha, hφ]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [Finset.sum_add_distrib, add_smul]⟩
    | neg x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨-a, by simp [neg_smul]⟩
  · rintro ⟨a, rfl⟩
    refine AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ?_
    refine ⟨GlobalTheory.EmbChart.atPlace v (a m), GlobalTheory.VacAny.at_atPlace _, ?_, ex m.1, exX _, fy m.2, exY _, rfl⟩
    rw [GlobalTheory.EmbChart.evFin_atPlace]
    exact (a m).2

end Tw.LatParam
