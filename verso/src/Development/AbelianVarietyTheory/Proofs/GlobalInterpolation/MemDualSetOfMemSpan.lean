import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingSemiLoc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MulVecMemLocLatIffOfFrame

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.DualFrame

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
/- English proof (translation)
Simplify using `[_root_.Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem _root_.GlobalTheory.DualFrame.hform_eq_dot {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y : n → A) : _root_.Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [_root_.Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.DualFrame.hform_eq_dot, ← mulVec_mulVec, _root_.Formalism.UG.cT, dotProduct_mulVec (fun i => σ (u i)) (B.map σ)ᵀ, vecMul_transpose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.DualFrame.hform_mulVec {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J B : Matrix n n A)
    (u y : n → A) : _root_.Formalism.UG.hform σ J (B *ᵥ u) y = (fun i => σ (u i)) ⬝ᵥ ((_root_.Formalism.UG.cT σ B * J) *ᵥ y) := by
  rw [_root_.GlobalTheory.DualFrame.hform_eq_dot, ← mulVec_mulVec, _root_.Formalism.UG.cT,
    dotProduct_mulVec (fun i => σ (u i)) (B.map σ)ᵀ, vecMul_transpose]
  congr 1
  funext i
  rw [RingHom.map_mulVec]
  rfl

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz => exact hz`. Consider the case `zero`. Introduce `x _`. Rewrite using `[_root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_zero, dotProduct_zero]`.

Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb`. Introduce `x hx`. Rewrite using `[_root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_add, dotProduct_add, ← _root_.GlobalTheory.DualFrame.hform_eq_dot, ← _root_.GlobalTheory.DualFrame.hform_eq_dot]`. Conclude with `add_mem (ha x hx) (hb x hx)`.

Consider the case `smul a z _ hz`. Introduce `x hx`. Establish `hsm : a • z = algebraMap (𝓞 E) E a • z` using `(algebraMap_smul E a z).symm`. Rewrite using `[hsm, _root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_smul, dotProduct_smul, ← _root_.GlobalTheory.DualFrame.hform_eq_dot, smul_eq_mul]`. Conclude with `mul_mem ⟨a, rfl⟩ (hz x hx)`.
-/
theorem _root_.GlobalTheory.DualFrame.mem_dualSet_of_mem_span {E n : Type} [Field E] [NumberField E] [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (L : Submodule (𝓞 E) (n → E)) {y : n → E}
    (hy : y ∈ Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet σ J L)) : y ∈ _root_.Formalism.BasicNotions.dualSet σ J L := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact hz
  | zero =>
    intro x _
    rw [_root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_zero, dotProduct_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    intro x hx
    rw [_root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_add, dotProduct_add,
      ← _root_.GlobalTheory.DualFrame.hform_eq_dot, ← _root_.GlobalTheory.DualFrame.hform_eq_dot]
    exact add_mem (ha x hx) (hb x hx)
  | smul a z _ hz =>
    intro x hx
    have hsm : a • z = algebraMap (𝓞 E) E a • z := (algebraMap_smul E a z).symm
    rw [hsm, _root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_smul, dotProduct_smul,
      ← _root_.GlobalTheory.DualFrame.hform_eq_dot, smul_eq_mul]
    exact mul_mem ⟨a, rfl⟩ (hz x hx)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
/- English proof (translation)
Take `⟨u, hu, huc⟩` from `_root_.GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one (E := E) v c hc`. Establish `hgen : ∀ x ∈ L, (fun i => _root_.Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (x i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L := by`. Introduce `x hx`. Unfold `_root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat _root_.Formalism.UG.latS`. Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`.

Establish `hsmul : ∀ s ∈ _root_.Formalism.BasicNotions.intV E v, ∀ z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L, (fun i => s * z i) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L` using `fun s hs z hz => Submodule.smul_mem _ (⟨s, hs⟩ : _root_.Formalism.BasicNotions.intV E v) hz`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `key : ∀ z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L, ∀ i, (((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F` using `F) (v.adicCompletion F)) *ᵥ z) i ∈ _root_.Formalism.BasicNotions.intV E v := by`. Introduce `z hz`.

Unfold `_root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat _root_.Formalism.UG.latS at hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨x, hx, rfl⟩` from `hw`. Introduce `i`.

Take `⟨a, ha⟩` from `hint x hx i`. Establish `hmap` using `RingHom.map_mulVec (_root_.Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F)) ((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) x i`. Simplify using `only [Function.comp_def] at hmap`. Rewrite using `[← hmap]`. Establish `: _root_.Formalism.UG.inclE (F` using `F) (v.adicCompletion F) ((((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i) = u * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a) := by`.

Rewrite using `[ha, map_mul]`. Take the linear combination `(-(_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) ((((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i))) * huc`. Rewrite using `[this]`. Use `mul_mem hu ?_` and prove the remaining obligations. Unfold `_root_.Formalism.UG.inclE`.

Rewrite using `[Algebra.TensorProduct.includeLeftRingHom_apply]`. Conclude with `_root_.GlobalTheory.OverCompare.tmul_mem_intV a`. Consider the case `zero`. Introduce `i`. Rewrite using `[mulVec_zero]`.

Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb`. Introduce `i`. Rewrite using `[mulVec_add]`. Conclude with `add_mem (ha i) (hb i)`.

Consider the case `smul s z _ hz`. Introduce `i`. Rewrite using `[mulVec_smul]`. Conclude with `mul_mem s.2 (hz i)`. Introduce `i`.

Establish `hy : y = ((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F` using `F) (v.adicCompletion F)) *ᵥ ((P : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ y) := by`. Rewrite using `[mulVec_mulVec, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]`. Rewrite using `[hy]`. Conclude with `key _ h i`. Introduce `hy`.

Establish `hsum : (P : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F` using `F) (v.adicCompletion F)) *ᵥ y = ∑ j, fun i => (y j * u) * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap F E c * (P : Matrix (Fin k) (Fin k) E) i j) := by`. Use function extensionality and compare the values at `i`. Simplify using `only [mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, map_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Take the linear combination `(-(y j * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) ((P : Matrix (Fin k) (Fin k) E) i j))) * huc`.

Rewrite using `[hsum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Conclude with `hsmul _ (mul_mem (hy j) hu) _ (hgen _ (hcol j))`.
-/
private theorem mulVec_mem_latticeCompletion_iff {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) {k : ℕ}
    (L : Submodule (𝓞 E) (Fin k → E)) (P : GL (Fin k) E) (c : 𝓞 F) (hc : c ∉ v.asIdeal)
    (hint : ∀ x ∈ L, ∀ i, algebraMap F E c * (((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈
      (algebraMap (𝓞 E) E).range)
    (hcol : ∀ j, (fun i => algebraMap F E c * (P : Matrix (Fin k) (Fin k) E) i j) ∈ L)
    (y : Fin k → E ⊗[F] v.adicCompletion F) :
    (P : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ y ∈
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L ↔ ∀ i, y i ∈ _root_.Formalism.BasicNotions.intV E v := by
  obtain ⟨u, hu, huc⟩ := _root_.GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one (E := E) v c hc
  have hgen : ∀ x ∈ L, (fun i => _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (x i)) ∈
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L := by
    intro x hx
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat _root_.Formalism.UG.latS
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  have hsmul : ∀ s ∈ _root_.Formalism.BasicNotions.intV E v, ∀ z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L,
      (fun i => s * z i) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L :=
    fun s hs z hz => Submodule.smul_mem _ (⟨s, hs⟩ : _root_.Formalism.BasicNotions.intV E v) hz
  constructor
  · intro h
    have key : ∀ z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L, ∀ i,
        (((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map
          (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ z) i ∈ _root_.Formalism.BasicNotions.intV E v := by
      intro z hz
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat _root_.Formalism.UG.latS at hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x, hx, rfl⟩ := hw
        intro i
        obtain ⟨a, ha⟩ := hint x hx i
        have hmap := RingHom.map_mulVec (_root_.Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F))
          ((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) x i
        simp only [Function.comp_def] at hmap
        rw [← hmap]
        have : _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
            ((((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i) =
            u * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a) := by
          rw [ha, map_mul]
          linear_combination (-(_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
            ((((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i))) * huc
        rw [this]
        refine mul_mem hu ?_
        unfold _root_.Formalism.UG.inclE
        rw [Algebra.TensorProduct.includeLeftRingHom_apply]
        exact _root_.GlobalTheory.OverCompare.tmul_mem_intV a
      | zero =>
        intro i
        rw [mulVec_zero]
        exact zero_mem _
      | add a b _ _ ha hb =>
        intro i
        rw [mulVec_add]
        exact add_mem (ha i) (hb i)
      | smul s z _ hz =>
        intro i
        rw [mulVec_smul]
        exact mul_mem s.2 (hz i)
    intro i
    have hy : y = ((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map
        (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ
        ((P : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ y) := by
      rw [mulVec_mulVec, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _),
        one_mulVec]
    rw [hy]
    exact key _ h i
  · intro hy
    have hsum : (P : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ y =
        ∑ j, fun i => (y j * u) * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
          (algebraMap F E c * (P : Matrix (Fin k) (Fin k) E) i j) := by
      funext i
      simp only [mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, map_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination (-(y j * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
        ((P : Matrix (Fin k) (Fin k) E) i j))) * huc
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact hsmul _ (mul_mem (hy j) hu) _ (hgen _ (hcol j))

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

/- English proof (translation)
Take `⟨B₀, c, hc, hint, hcol⟩` from `_root_.GlobalTheory.SemiLocalFrame.exists_frame_denominator F E k Λ hfin hsp v`. Use `set σ' : E →+* E := (σ : E →+* E) with hσ'`. Establish `hσc : σ' (algebraMap F E c) = algebraMap F E c` using `σ.commutes _`. Establish `hdet : (_root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E) * J).det ≠ 0`. Rewrite using `[det_mul, _root_.Formalism.UG.cT, det_transpose, show ((B₀ : Matrix (Fin k) (Fin k) E).map σ').det = σ' (B₀ : Matrix (Fin k) (Fin k) E).det from (RingHom.map_det σ' _).symm]`.

Conclude with `mul_ne_zero ((map_ne_zero σ').mpr (B₀.isUnit.map Matrix.detMonoidHom).ne_zero) hJ.ne_zero`. Use `set M : GL (Fin k) E := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hM`. Establish `hMcoe : (M : Matrix (Fin k) (Fin k) E) = _root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E) * J` using `rfl`. Establish `hconj : ∀ e : E, _root_.Formalism.UG.sigR σ (v.adicCompletion F) (_root_.Formalism.UG.inclE (F` using `F) (v.adicCompletion F) e) = _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (σ' e) := by`. Introduce `e`.

Simplify using `[_root_.Formalism.UG.sigR, _root_.Formalism.UG.inclE, hσ']`. Use `⟨Matrix.GeneralLinearGroup.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) B₀, Matrix.GeneralLinearGroup.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) M⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (v.adicCompletion F)) ((B₀ : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F))) * J.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) * (((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fi …`. Establish `hT : _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (v.adicCompletion F)) ((B₀ : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F` using `F) (v.adicCompletion F))) = (_root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E)).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) := by`. Simplify using `only [_root_.Formalism.UG.cT, transpose_map, Matrix.map_map]`.

Use `congr 2`. Rewrite using `[hT, ← Matrix.map_mul, ← Matrix.map_mul, ← hMcoe, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `mulVec_mem_latticeCompletion_iff v Λ B₀ c hc hint hcol`. Use `mulVec_mem_latticeCompletion_iff v _ M⁻¹ c hc ?_ ?_` and prove the remaining obligations. Introduce `y hy i`.

Establish `hyd` using `_root_.GlobalTheory.DualFrame.mem_dualSet_of_mem_span σ' J Λ hy`. Establish `hx : (fun l => algebraMap F E c * (B₀ : Matrix (Fin k) (Fin k) E) l i) = (B₀ : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i (algebraMap F E c)`. Use function extensionality and compare the values at `l`. Simplify using `[mulVec_single, mul_comm]`. Establish `hval` using `hyd _ (hcol i)`.

Rewrite `hval` using `[hx, _root_.GlobalTheory.DualFrame.hform_mulVec]`. Establish `hfun : (fun l => σ' ((Pi.single i (algebraMap F E c) : Fin k → E) l)) = (Pi.single i (algebraMap F E c) : Fin k → E)`. Use function extensionality and compare the values at `l`. Distinguish the cases in `hl : l = i`. Substitute `hl` using the available equality.

Simplify using `[hσc]`. Simplify using `[hl]`. Rewrite `hval` using `[hfun, single_dotProduct, ← hMcoe]`. Rewrite using `[inv_inv]` and apply the resulting hypothesis. Introduce `j`.

Use `Submodule.subset_span ?_` and prove the remaining obligations. Introduce `x hx`. Use `set u := ((B₀⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x with hu`. Establish `hxu : x = (B₀ : Matrix (Fin k) (Fin k) E) *ᵥ u`. Rewrite using `[hu, mulVec_mulVec, Units.mul_inv, one_mulVec]`.

Establish `hw : (fun i => algebraMap F E c * ((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) i j) = ((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single j (algebraMap F E c)`. Use function extensionality and compare the values at `l`. Simplify using `[mulVec_single, mul_comm]`. Take `⟨a, ha⟩` from `hint x hx j`. Rewrite using `[hxu, hw, _root_.GlobalTheory.DualFrame.hform_mulVec, ← hMcoe, mulVec_mulVec, Units.mul_inv, one_mulVec, dotProduct_single, ← hσc, ← map_mul, mul_comm, ← ha]`.

Conclude with `⟨⟨σ' a, (RingOfIntegers.isIntegral_coe a).map σ'.toIntAlgHom⟩, rfl⟩`.
-/
theorem _root_.GlobalTheory.DualFrame.exists_dual_frames (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E) (hJ : IsUnit J.det)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hsp : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ B C : GL (Fin k) (E ⊗[F] v.adicCompletion F),
      _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (v.adicCompletion F)) (B : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *
        J.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *
        (C : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) = 1 ∧
      (∀ y : Fin k → E ⊗[F] v.adicCompletion F,
        (B : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v Λ ↔
          ∀ i, y i ∈ _root_.Formalism.BasicNotions.intV E v) ∧
      ∀ y : Fin k → E ⊗[F] v.adicCompletion F,
        (C : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈
          _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v (Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet (σ : E →+* E) J Λ)) ↔ ∀ i, y i ∈ _root_.Formalism.BasicNotions.intV E v := by
  obtain ⟨B₀, c, hc, hint, hcol⟩ := _root_.GlobalTheory.SemiLocalFrame.exists_frame_denominator F E k Λ hfin hsp v
  set σ' : E →+* E := (σ : E →+* E) with hσ'
  have hσc : σ' (algebraMap F E c) = algebraMap F E c := σ.commutes _
  have hdet : (_root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E) * J).det ≠ 0 := by
    rw [det_mul, _root_.Formalism.UG.cT, det_transpose,
      show ((B₀ : Matrix (Fin k) (Fin k) E).map σ').det = σ' (B₀ : Matrix (Fin k) (Fin k) E).det from
        (RingHom.map_det σ' _).symm]
    exact mul_ne_zero ((map_ne_zero σ').mpr (B₀.isUnit.map Matrix.detMonoidHom).ne_zero) hJ.ne_zero
  set M : GL (Fin k) E := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hM
  have hMcoe : (M : Matrix (Fin k) (Fin k) E) = _root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E) * J := rfl
  have hconj : ∀ e : E, _root_.Formalism.UG.sigR σ (v.adicCompletion F) (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) e) =
      _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (σ' e) := by
    intro e
    simp [_root_.Formalism.UG.sigR, _root_.Formalism.UG.inclE, hσ']
  refine ⟨Matrix.GeneralLinearGroup.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) B₀,
    Matrix.GeneralLinearGroup.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) M⁻¹, ?_, ?_, ?_⟩
  · change _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (v.adicCompletion F))
        ((B₀ : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F))) *
        J.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *
        (((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E)).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) = 1
    have hT : _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (v.adicCompletion F))
        ((B₀ : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F))) =
        (_root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E)).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) := by
      simp only [_root_.Formalism.UG.cT, transpose_map, Matrix.map_map]
      congr 2
    rw [hT, ← Matrix.map_mul, ← Matrix.map_mul, ← hMcoe, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · exact mulVec_mem_latticeCompletion_iff v Λ B₀ c hc hint hcol
  · refine mulVec_mem_latticeCompletion_iff v _ M⁻¹ c hc ?_ ?_
    · intro y hy i
      have hyd := _root_.GlobalTheory.DualFrame.mem_dualSet_of_mem_span σ' J Λ hy
      have hx : (fun l => algebraMap F E c * (B₀ : Matrix (Fin k) (Fin k) E) l i) =
          (B₀ : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i (algebraMap F E c) := by
        funext l
        simp [mulVec_single, mul_comm]
      have hval := hyd _ (hcol i)
      rw [hx, _root_.GlobalTheory.DualFrame.hform_mulVec] at hval
      have hfun : (fun l => σ' ((Pi.single i (algebraMap F E c) : Fin k → E) l)) =
          (Pi.single i (algebraMap F E c) : Fin k → E) := by
        funext l
        by_cases hl : l = i
        · subst hl
          simp [hσc]
        · simp [hl]
      rw [hfun, single_dotProduct, ← hMcoe] at hval
      rwa [inv_inv]
    · intro j
      refine Submodule.subset_span ?_
      intro x hx
      set u := ((B₀⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x with hu
      have hxu : x = (B₀ : Matrix (Fin k) (Fin k) E) *ᵥ u := by
        rw [hu, mulVec_mulVec, Units.mul_inv, one_mulVec]
      have hw : (fun i => algebraMap F E c * ((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) i j) =
          ((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single j (algebraMap F E c) := by
        funext l
        simp [mulVec_single, mul_comm]
      obtain ⟨a, ha⟩ := hint x hx j
      rw [hxu, hw, _root_.GlobalTheory.DualFrame.hform_mulVec, ← hMcoe, mulVec_mulVec, Units.mul_inv, one_mulVec,
        dotProduct_single, ← hσc, ← map_mul, mul_comm, ← ha]
      exact ⟨⟨σ' a, (RingOfIntegers.isIntegral_coe a).map σ'.toIntAlgHom⟩, rfl⟩

end GlobalTheory.DualFrame
