import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumATop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.ExistsIntegralMultiple

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Tools

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Set `φ : V →+ E` to `AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)`. Establish `h1` using `map_sum φ (fun i => c i • x i) Finset.univ`. Simplify using `only [φ, AddMonoidHom.mk'_apply, H.h_smul_left] at h1`. Conclude with `h1`.
-/
private theorem hermSp_h_sum_smul_left {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {ι : Type} [Fintype ι] (c : ι → E) (x : ι → V) (y : V) : H.h (∑ i, c i • x i) y = ∑ i, c i * H.h (x i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)
  have h1 := map_sum φ (fun i => c i • x i) Finset.univ
  simp only [φ, AddMonoidHom.mk'_apply, H.h_smul_left] at h1
  exact h1

/- English proof (translation)
Rewrite using `[H.h_herm (∑ i, c i • x i) y, hermSp_h_sum_smul_left, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← H.h_herm]`.
-/
private theorem hermSp_h_sum_smul_right {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {ι : Type} [Fintype ι] (y : V) (c : ι → E) (x : ι → V) :
    H.h y (∑ i, c i • x i) = ∑ i, M.L.cj (c i) * H.h y (x i) := by
  rw [H.h_herm (∑ i, c i • x i) y, hermSp_h_sum_smul_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← H.h_herm]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [HermSp.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[hermSp_h_sum_smul_left]`. Simplify using `only [hermSp_h_sum_smul_right, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_recomb {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type}
    [Fintype ι] (v : ι → V) (A : Matrix ι ι E) :
    H.gram (fun j => ∑ i, A i j • v i) = (A.map M.L.cj)ᵀ * H.gram v * A := by
  ext a b
  simp only [HermSp.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hermSp_h_sum_smul_left]
  simp only [hermSp_h_sum_smul_right, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Introduce `V _ _ H t hg`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `(Submodule.span_le (R := E)).2 fun v hv => hv.2`. Introduce `w hw`. Establish `hwΛ : w ∈ Submodule.span E (t.abelian₂ : Set V)`.

Rewrite using `[hg.1.1.2.1]`. Conclude with `Submodule.mem_top`. Take `⟨c, hc0, hc⟩` from `PI.LocHerm.Glue.existsIntegralMultiple M hM V t.abelian₂ w hwΛ`. Establish `hcW : algebraMap F E (c : F) • w ∈ ThL H t` using `⟨hc, Submodule.smul_mem _ _ hw⟩`. Establish `hunit : IsUnit (algebraMap F E (c : F))` using `(Units.mk0 (c : F) hc0).isUnit.map _`.

Establish `e : w = (hunit.unit⁻¹ : Eˣ) • (algebraMap F E (c : F) • w)`. Rewrite using `[Units.smul_def, smul_smul, IsUnit.val_inv_mul, one_smul]`. Rewrite using `[e, Units.smul_def]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hcW)`.
-/
theorem thSpan_at (M : Model F E) (r : ℕ) (hM : M.OK) : ThSpan M r := by
  intro V _ _ H t hg
  apply le_antisymm
  · exact (Submodule.span_le (R := E)).2 fun v hv => hv.2
  · intro w hw
    have hwΛ : w ∈ Submodule.span E (t.abelian₂ : Set V) := by
      rw [hg.1.1.2.1]
      exact Submodule.mem_top
    obtain ⟨c, hc0, hc⟩ := PI.LocHerm.Glue.existsIntegralMultiple M hM V t.abelian₂ w hwΛ
    have hcW : algebraMap F E (c : F) • w ∈ ThL H t := ⟨hc, Submodule.smul_mem _ _ hw⟩
    have hunit : IsUnit (algebraMap F E (c : F)) := (Units.mk0 (c : F) hc0).isUnit.map _
    have e : w = (hunit.unit⁻¹ : Eˣ) • (algebraMap F E (c : F) • w) := by
      rw [Units.smul_def, smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [e, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hcW)

/- English proof (translation)
Introduce `V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂`. Take `⟨hg₁, hF₂, hF₂', hI, -, -⟩` from `hyp`. Establish `hT1` using `hg₁.1`. Establish `hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1))` using `hT1.2.2.2.1`. Establish `hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T')` using `isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1`.

Establish `hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T')`. Establish `e` using `Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hI.2.2.2.2.2`. Establish `hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1)))` using `hD₂.mul (hD₂.map M.L.cj)`. Establish `h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1)))`. Rewrite using `[e]`.

Conclude with `hN₂.mul hG₁`. Conclude with `isUnit_of_mul_isUnit_left h3`. Take `⟨s, hs, hdet⟩` from `gram_det H f₂ f₂' t₁.T t₁.T' hF₂ hF₂' hD₂`. Establish `hgu : IsUnit (H.gram (Sum.elim f₂ f₂')).det`. Establish `hsu : IsUnit s` using `⟨⟨s, s, hs, hs⟩, rfl⟩`.

Establish `: (H.gram (Sum.elim f₂ f₂')).det = H.Gdet f₂ f₂' t₁.T t₁.T' * s`. Rewrite using `[← hdet, mul_assoc, hs, mul_one]`. Rewrite using `[this]`. Conclude with `hG₂.mul hsu`. Break down `hsplit : M.split with _ | g` into its components or cases.

Establish `hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) = Sum.elim f₂ f₂'`. Unfold `HermSp.MMfam`. Rewrite using `[hsplit]`. Rewrite using `[hMM]`. Conclude with `hgu`.

Use `set qi : E := algebraMap F E ((g.q : F)⁻¹)`. Establish `hq0 : (g.q : F) ≠ 0` using `fun h0 => g.q_irr.ne_zero (Subtype.ext h0)`. Establish `hqi : IsUnit qi` using `((Units.mk0 (g.q : F) hq0)⁻¹.isUnit).map (algebraMap F E)`. Establish `hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) = Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a))`. Unfold `HermSp.MMfam`.

Rewrite using `[hsplit]`. Set `A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E` to `fromBlocks 1 (-(qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) 0 (qi • 1)`. Establish `hw : Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) = fun j => ∑ i, A i j • Sum.elim f₂ f₂' i`. Use function extensionality and compare the values at `j`. Break down `j with a | a` into its components or cases.

Simplify using `[A, Fintype.sum_sum_type, Matrix.one_apply]`. Simplify using `[A, Fintype.sum_sum_type, Matrix.one_apply, smul_sub, sub_eq_add_neg, add_comm]`. Rewrite using `[hMM, hw, gram_recomb, det_mul, det_mul, det_transpose]`. Establish `hA : A.det = qi ^ (r + 1)`. Simplify using `[A, det_fromBlocks_zero₂₁, det_smul]`.

Establish `hAm : (A.map M.L.cj).det = M.L.cj A.det`. Rewrite using `[show A.map M.L.cj = (M.L.cj.toRingEquiv.toRingHom).mapMatrix A from rfl, ← RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[hAm, hA]`. Conclude with `((hqi.pow _).map M.L.cj).mul hgu |>.mul (hqi.pow _)`.
-/
theorem gramMM_holds (M : Model F E) (r n : ℕ) : GramMM M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂
  obtain ⟨hg₁, hF₂, hF₂', hI, -, -⟩ := hyp
  have hT1 := hg₁.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hI.2.2.2.2.2
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  obtain ⟨s, hs, hdet⟩ := gram_det H f₂ f₂' t₁.T t₁.T' hF₂ hF₂' hD₂
  have hgu : IsUnit (H.gram (Sum.elim f₂ f₂')).det := by
    have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
    have : (H.gram (Sum.elim f₂ f₂')).det = H.Gdet f₂ f₂' t₁.T t₁.T' * s := by
      rw [← hdet, mul_assoc, hs, mul_one]
    rw [this]
    exact hG₂.mul hsu
  rcases hsplit : M.split with _ | g
  · have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) = Sum.elim f₂ f₂' := by
      unfold HermSp.MMfam
      rw [hsplit]
    rw [hMM]
    exact hgu
  · set qi : E := algebraMap F E ((g.q : F)⁻¹)
    have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
    have hqi : IsUnit qi := ((Units.mk0 (g.q : F) hq0)⁻¹.isUnit).map (algebraMap F E)
    have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =
        Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) := by
      unfold HermSp.MMfam
      rw [hsplit]
    let A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      fromBlocks 1 (-(qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) 0 (qi • 1)
    have hw : Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) = fun j => ∑ i, A i j • Sum.elim f₂ f₂' i := by
      funext j
      rcases j with a | a
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply, smul_sub, sub_eq_add_neg, add_comm]
    rw [hMM, hw, gram_recomb, det_mul, det_mul, det_transpose]
    have hA : A.det = qi ^ (r + 1) := by
      simp [A, det_fromBlocks_zero₂₁, det_smul]
    have hAm : (A.map M.L.cj).det = M.L.cj A.det := by
      rw [show A.map M.L.cj = (M.L.cj.toRingEquiv.toRingHom).mapMatrix A from rfl, ← RingHom.map_det]
      rfl
    rw [hAm, hA]
    exact ((hqi.pow _).map M.L.cj).mul hgu |>.mul (hqi.pow _)

end Tools

end Formalism.L2.SG.LsDatumA
