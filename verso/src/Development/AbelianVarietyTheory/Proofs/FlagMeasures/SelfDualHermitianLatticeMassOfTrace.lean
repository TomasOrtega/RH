import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNondegenerateTupleComplementFixer
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanEqMap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentOfGram
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassBoundsStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameMass

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

omit [TopologicalSpace E] in
/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [rmul, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem rmul_comp {n m : ℕ} (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

/- English proof (translation)
Simplify using `only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_sum_left (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (c : Fin m → E) (y : Fin n → E) :
    hf L Hm (∑ i, c i • x i) y = ∑ i, c i * hf L Hm (x i) y := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_sum_right (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (c : Fin m → E) (y : Fin n → E) :
    hf L Hm y (∑ i, c i • x i) = ∑ i, L.cj (c i) * hf L Hm y (x i) := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gramT, rmul, Matrix.of_apply, hf_sum_left, hf_sum_right, Matrix.mul_apply, cT, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_rmul (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gramT L Hm (rmul x A) = cT L A * gramT L Hm x * A := by
  ext a b
  simp only [gramT, rmul, Matrix.of_apply, hf_sum_left, hf_sum_right, Matrix.mul_apply, cT,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `h : cT L A = (L.cj.toRingEquiv.toRingHom.mapMatrix A).transpose`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[h, Matrix.det_transpose, ← RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_cT (L : LocE F E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    (cT L A).det = L.cj A.det := by
  have h : cT L A = (L.cj.toRingEquiv.toRingHom.mapMatrix A).transpose := by
    ext i j; rfl
  rw [h, Matrix.det_transpose, ← RingHom.map_det]
  rfl

omit [TopologicalSpace E] in
/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Establish `h : rmul (rmul x B) B⁻¹ = x`. Rewrite using `[rmul_comp, Matrix.mul_nonsing_inv _ hB]`. Use function extensionality and compare the values at `j`.

Simplify using `[rmul, Matrix.one_apply]`. Establish `h2 : x j = ∑ i, B⁻¹ i j • rmul x B i` using `(congrFun h j).symm`. Rewrite using `[SetLike.mem_coe, h2]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem span_rmul {n m : ℕ} (x : Fin m → Fin n → E) (B : Matrix (Fin m) (Fin m) E)
    (hB : IsUnit B.det) :
    Submodule.span E (Set.range x) ≤ Submodule.span E (Set.range (rmul x B)) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have h : rmul (rmul x B) B⁻¹ = x := by
    rw [rmul_comp, Matrix.mul_nonsing_inv _ hB]
    funext j
    simp [rmul, Matrix.one_apply]
  have h2 : x j = ∑ i, B⁻¹ i j • rmul x B i := (congrFun h j).symm
  rw [SetLike.mem_coe, h2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S hk ⟨Λs, hΛs⟩`. Take `⟨x, hx, hME, -, hlat, hmass, hcls⟩` from `GlobalTheory.HL.FrameTuple.main L r k S`. Take `⟨κ, hκ, hU⟩` from `GlobalTheory.T.selfDual_hermitianLattice_mass_bounds L S.ϖ S.ϖ_irr S.Hm S.herm Λs hΛs (2 * r + 2) x hx (by omega) _ hlat`. Use `⟨κ, hκ, fun C hC p hp Mh hle hin hint => ?_⟩` and prove the remaining obligations. Take `⟨y, B, hB, hy, hM⟩` from `hcls C hC p hp`.

Establish `hBu : IsUnit B.det` using `IsUnit.of_mul_eq_one _ hB`. Establish `hBc : IsUnit (L.cj B.det)` using `hBu.map L.cj`. Establish `hyu : IsUnit (gramT L S.Hm y).det`. Rewrite using `[hy, gram_rmul, Matrix.det_mul, Matrix.det_mul, det_cT]`. Conclude with `(hBc.mul hx).mul hBu`.

Take `⟨-, A, hAi, hAu, hMh, hli, hA⟩` from `GlobalTheory.HL.OverBasis.exists_basis_overlattice L S.Hm S.herm (2 * r + 2) y hyu Mh (hM ▸ hle) (fun v hv => by rw [hy]; exact span_rmul x B hBu (hME ▸ hin v hv)) hint`. Take `⟨hv, hidx⟩` from `GlobalTheory.MatrixIndex.index_rmul L S.ϖ S.ϖ_irr _ hli A hAi hAu`. Rewrite `hidx` using `[hA, ← hM, ← hMh]`. Establish `hinv : (A * B⁻¹)⁻¹ = B * A⁻¹`. Rewrite using `[Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hBu]`.

Establish `hr : rmul x (A * B⁻¹)⁻¹ = rmul y A⁻¹` using `by rw [hinv, hy, rmul_comp]`. Establish `hBB : B⁻¹.det * B.det = 1` using `Matrix.det_nonsing_inv_mul_det _ hBu`. Establish `hdet : (A * B⁻¹).det * L.cj (A * B⁻¹).det = A.det * L.cj A.det`. Establish `h1 : L.cj B⁻¹.det * L.cj B.det = 1` using `by rw [← map_mul, hBB, map_one]`. Rewrite using `[Matrix.det_mul, map_mul]`.

Take the linear combination `(-(A.det * L.cj A.det * B⁻¹.det * L.cj B⁻¹.det)) * hB + (A.det * L.cj A.det * L.cj B⁻¹.det * L.cj B.det) * hBB + (A.det * L.cj A.det) * h1`. Establish `hu : IsUnit (A * B⁻¹).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `hAu.mul (IsUnit.of_mul_eq_one _ hBB)`. Establish `hI : IsIntM L (gramT L S.Hm (rmul x (A * B⁻¹)⁻¹))`.

Rewrite using `[hr]`. Introduce `a b`. Apply the tactic sequence `refine hint _ ?_ _ ?_ <;> rw [hMh] <;> exact Submodule.subset_span ⟨_, rfl⟩`. Establish `key` using `hU (A * B⁻¹) hu hI`. Rewrite `key` using `[hr, ← hMh, hdet, hME, ← hmass]`.

Establish `hpow : (resQ S.ϖ : ℝ) ^ (-(vE L S.ϖ (A.det * L.cj A.det) * (((k + 2 * r + 1 : ℕ) : ℤ) - ((2 * r + 2 : ℕ) : ℤ)))) = (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹`. Rewrite using `[hidx, zpow_neg]`. Use `congr 1`. Establish `e : (((k + 2 * r + 1 : ℕ) : ℤ) - ((2 * r + 2 : ℕ) : ℤ)) = ((k - 1 : ℕ) : ℤ)` using `by omega`. Rewrite using `[e]`.

Use `conv_lhs => rw [← Int.toNat_of_nonneg hv]`. Rewrite using `[← Nat.cast_mul, zpow_natCast, pow_mul]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `key` using `[hpow]`.

Conclude with `key`.
-/
theorem mass_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 2 * r + 6 ≤ k → (∃ Λ, IsSD L S.Hm Λ) → ∃ κ : ℝ, 0 < κ ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (∀ x ∈ Mh, x ∈ S.ME) → (∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O) → ENNReal.ofReal (κ / 2 * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) ≤ S.massSig Mh ∧ S.massSig Mh ≤ ENNReal.ofReal (2 * κ * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk ⟨Λs, hΛs⟩
  obtain ⟨x, hx, hME, -, hlat, hmass, hcls⟩ := GlobalTheory.HL.FrameTuple.main L r k S
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.selfDual_hermitianLattice_mass_bounds L S.ϖ S.ϖ_irr S.Hm S.herm Λs hΛs (2 * r + 2) x hx
    (by omega) _ hlat
  refine ⟨κ, hκ, fun C hC p hp Mh hle hin hint => ?_⟩
  obtain ⟨y, B, hB, hy, hM⟩ := hcls C hC p hp
  have hBu : IsUnit B.det := IsUnit.of_mul_eq_one _ hB
  have hBc : IsUnit (L.cj B.det) := hBu.map L.cj
  have hyu : IsUnit (gramT L S.Hm y).det := by
    rw [hy, gram_rmul, Matrix.det_mul, Matrix.det_mul, det_cT]
    exact (hBc.mul hx).mul hBu
  obtain ⟨-, A, hAi, hAu, hMh, hli, hA⟩ := GlobalTheory.HL.OverBasis.exists_basis_overlattice L S.Hm S.herm
    (2 * r + 2) y hyu Mh (hM ▸ hle)
    (fun v hv => by rw [hy]; exact span_rmul x B hBu (hME ▸ hin v hv)) hint
  obtain ⟨hv, hidx⟩ := GlobalTheory.MatrixIndex.index_rmul L S.ϖ S.ϖ_irr _ hli A hAi hAu
  rw [hA, ← hM, ← hMh] at hidx
  have hinv : (A * B⁻¹)⁻¹ = B * A⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hBu]
  have hr : rmul x (A * B⁻¹)⁻¹ = rmul y A⁻¹ := by rw [hinv, hy, rmul_comp]
  have hBB : B⁻¹.det * B.det = 1 := Matrix.det_nonsing_inv_mul_det _ hBu
  have hdet : (A * B⁻¹).det * L.cj (A * B⁻¹).det = A.det * L.cj A.det := by
    have h1 : L.cj B⁻¹.det * L.cj B.det = 1 := by rw [← map_mul, hBB, map_one]
    rw [Matrix.det_mul, map_mul]
    linear_combination (-(A.det * L.cj A.det * B⁻¹.det * L.cj B⁻¹.det)) * hB
      + (A.det * L.cj A.det * L.cj B⁻¹.det * L.cj B.det) * hBB + (A.det * L.cj A.det) * h1
  have hu : IsUnit (A * B⁻¹).det := by
    rw [Matrix.det_mul]; exact hAu.mul (IsUnit.of_mul_eq_one _ hBB)
  have hI : IsIntM L (gramT L S.Hm (rmul x (A * B⁻¹)⁻¹)) := by
    rw [hr]
    intro a b
    refine hint _ ?_ _ ?_ <;> rw [hMh] <;> exact Submodule.subset_span ⟨_, rfl⟩
  have key := hU (A * B⁻¹) hu hI
  rw [hr, ← hMh, hdet, hME, ← hmass] at key
  have hpow : (resQ S.ϖ : ℝ) ^ (-(vE L S.ϖ (A.det * L.cj A.det) *
        (((k + 2 * r + 1 : ℕ) : ℤ) - ((2 * r + 2 : ℕ) : ℤ)))) =
      (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹ := by
    rw [hidx, zpow_neg]
    congr 1
    have e : (((k + 2 * r + 1 : ℕ) : ℤ) - ((2 * r + 2 : ℕ) : ℤ)) = ((k - 1 : ℕ) : ℤ) := by omega
    rw [e]
    conv_lhs => rw [← Int.toNat_of_nonneg hv]
    rw [← Nat.cast_mul, zpow_natCast, pow_mul]
    push_cast
    rfl
  rw [hpow] at key
  exact key

end GlobalTheory.HL.FrameMass
