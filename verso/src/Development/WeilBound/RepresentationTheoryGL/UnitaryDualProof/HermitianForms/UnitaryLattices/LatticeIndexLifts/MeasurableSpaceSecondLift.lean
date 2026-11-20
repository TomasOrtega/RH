import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.AvNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedAbsDetMulIntegralCompMulVecFinitePlace
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorOpenCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexAnnihilatorsDualityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeAnnihilatorWithinNhdsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactLatticeContainingStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaussianDualMeasure.DualMeasure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaussianDualMeasure.SecondCountableTopologyAndT2Space
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContinuousSectionVecMulOrbitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyHaarDetEqOneNearOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSubgroupRelIndexMulStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLLastBasisVecMulEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteImageCompactOpenQuotient

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil GlobalTheory.BZMir Filter
open scoped Topology ENNReal NNReal

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lattices

variable (ψ : AddChar k Circle) {n : ℕ}

/- English proof (translation)
The claim follows from `(GlobalTheory.T.annihilator_open_compact k ψ hψ hψ1 n A hA.1 hA.2).1`.
-/
theorem perp_open (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin n → k)} (hA : Lat A) :
    IsOpen (perp ψ A : Set (Fin n → k)) := (GlobalTheory.T.annihilator_open_compact k ψ hψ hψ1 n A hA.1 hA.2).1

/- English proof (translation)
The claim follows from `(GlobalTheory.T.annihilator_open_compact k ψ hψ hψ1 n A hA.1 hA.2).2`.
-/
theorem perp_compact (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin n → k)} (hA : Lat A) :
    IsCompact (perp ψ A : Set (Fin n → k)) := (GlobalTheory.T.annihilator_open_compact k ψ hψ hψ1 n A hA.1 hA.2).2

/- English proof (translation)
Introduce `_ hξ a ha` and use `hξ a (h ha)`.
-/
theorem perp_anti {A A' : AddSubgroup (Fin n → k)} (h : A ≤ A') : perp ψ A' ≤ perp ψ A :=
  fun _ hξ a ha => hξ a (h ha)

/- English proof (translation)
The claim follows from `GlobalTheory.T.relIndex_annihilators_duality k ψ hψ hψ1 n A₀ A (perp ψ A₀) (perp ψ A) h₀.1 h₀.2 h.1 h.2 hle (fun _ => Iff.rfl) (fun _ => Iff.rfl)`.
-/
theorem perp_relIndex (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A₀ A : AddSubgroup (Fin n → k)} (h₀ : Lat A₀) (h : Lat A)
    (hle : A₀ ≤ A) : (perp ψ A).relIndex (perp ψ A₀) = A₀.relIndex A :=
  GlobalTheory.T.relIndex_annihilators_duality k ψ hψ hψ1 n A₀ A (perp ψ A₀) (perp ψ A) h₀.1 h₀.2 h.1 h.2 hle (fun _ => Iff.rfl) (fun _ => Iff.rfl)

/- English proof (translation)
Use `haveI : CompactSpace A := isCompact_iff_compactSpace.mp h.1`. Establish `ho : IsOpen ((A₀.addSubgroupOf A : AddSubgroup A) : Set A)` using `h₀.2.preimage continuous_subtype_val`. Use `haveI := AddSubgroup.quotient_finite_of_isOpen (A₀.addSubgroupOf A) ho`. Conclude with `AddSubgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_lat {A₀ A : AddSubgroup (Fin n → k)} (h₀ : Lat A₀) (h : Lat A) : A₀.relIndex A ≠ 0 := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp h.1
  have ho : IsOpen ((A₀.addSubgroupOf A : AddSubgroup A) : Set A) := h₀.2.preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen (A₀.addSubgroupOf A) ho
  exact AddSubgroup.index_ne_zero_of_finite

/- English proof (translation)
Take `⟨A, h1, h2, h3⟩` from `GlobalTheory.T.exists_open_compact_lattice_containing k n K hK`. Conclude with `⟨A, ⟨h1, h2⟩, h3⟩`.
-/
theorem lat_over {K : Set (Fin n → k)} (hK : IsCompact K) : ∃ A : AddSubgroup (Fin n → k), Lat A ∧ K ⊆ A := by
  obtain ⟨A, h1, h2, h3⟩ := GlobalTheory.T.exists_open_compact_lattice_containing k n K hK
  exact ⟨A, ⟨h1, h2⟩, h3⟩

/- English proof (translation)
Take `⟨A, h1, h2, h3⟩` from `GlobalTheory.T.lattice_annihilator_within_nhds k ψ hψ hψ1 n U hU`. Conclude with `⟨A, ⟨h1, h2⟩, h3⟩`.
-/
theorem lat_shrink (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {U : Set (Fin n → k)} (hU : U ∈ 𝓝 (0 : Fin n → k)) :
    ∃ A : AddSubgroup (Fin n → k), Lat A ∧ (perp ψ A : Set _) ⊆ U := by
  obtain ⟨A, h1, h2, h3⟩ := GlobalTheory.T.lattice_annihilator_within_nhds k ψ hψ hψ1 n U hU
  exact ⟨A, ⟨h1, h2⟩, h3⟩

/- English proof (translation)
Take `⟨B, hB, hB'⟩` from `lat_over (h.1.union h'.1)`. Conclude with `⟨B, hB, fun x hx => hB' (Or.inl hx), fun x hx => hB' (Or.inr hx)⟩`.
-/
theorem lat_sup {A A' : AddSubgroup (Fin n → k)} (h : Lat A) (h' : Lat A') : ∃ A'', Lat A'' ∧ A ≤ A'' ∧ A' ≤ A'' := by
  obtain ⟨B, hB, hB'⟩ := lat_over (h.1.union h'.1)
  exact ⟨B, hB, fun x hx => hB' (Or.inl hx), fun x hx => hB' (Or.inr hx)⟩

end Lattices

section Forms

variable {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev md (g : GL (Fin (m + 1)) k) : ℝ := nabs k (Matrix.GeneralLinearGroup.det g)

/- English proof (translation)
The claim follows from `NNReal.coe_pos.mpr distribHaarChar_pos`.
-/
theorem md_pos (g : GL (Fin (m + 1)) k) : 0 < md g := NNReal.coe_pos.mpr distribHaarChar_pos

/- English proof (translation)
Simplify using `[md, nabs, map_mul]`.
-/
theorem md_mul (g h : GL (Fin (m + 1)) k) : md (g * h) = md g * md h := by
  simp [md, nabs, map_mul]

/- English proof (translation)
Simplify using `[md, nabs, map_inv]`.
-/
theorem md_inv (g : GL (Fin (m + 1)) k) : md g⁻¹ = (md g)⁻¹ := by
  simp [md, nabs, map_inv]

/- English proof (translation)
Simplify using `[md, nabs]`.
-/
theorem md_one : md (1 : GL (Fin (m + 1)) k) = 1 := by
  simp [md, nabs]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem xz_eq (m : ℕ) : (xz m : Fin (m + 1) → k) = eLast k m := rfl

variable (gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)) (s : ℝ) (C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

def Ct (g : GL (Fin (m + 1)) k) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  (((md g ^ (s + 1) : ℝ) : ℂ)) • (C.compl₂ (gl g⁻¹)).comp (gl g⁻¹)

/- English proof (translation)
Simplify using `[Ct]`.
-/
theorem Ct_apply (g : GL (Fin (m + 1)) k) (v w : V) :
    Ct gl s C g v w = ((md g ^ (s + 1) : ℝ) : ℂ) * C (gl g⁻¹ v) (gl g⁻¹ w) := by
  simp [Ct]

open Classical in

def sect (ξ : Fin (m + 1) → k) : GL (Fin (m + 1)) k :=
  if h : ξ = 0 then 1 else (Classical.choose (GlobalTheory.T.exists_GL_last_basis_vecMul_eq k m ξ h))⁻¹

/- English proof (translation)
Rewrite using `[sect, dif_neg h, inv_inv]`. Conclude with `Classical.choose_spec (GlobalTheory.T.exists_GL_last_basis_vecMul_eq k m ξ h)`.
-/
theorem sect_spec {ξ : Fin (m + 1) → k} (h : ξ ≠ 0) :
    xz m ᵥ* (((sect ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
  rw [sect, dif_neg h, inv_inv]
  exact Classical.choose_spec (GlobalTheory.T.exists_GL_last_basis_vecMul_eq k m ξ h)

open Classical in

def Df (ξ : Fin (m + 1) → k) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := if ξ = 0 then 0 else Ct gl s C (sect ξ)

/- English proof (translation)
Simplify using `[Df]`.
-/
theorem Df_zero : Df gl s C (0 : Fin (m + 1) → k) = 0 := by
  simp [Df]

variable {gl s C}

/- English proof (translation)
Use `set p := h⁻¹ * g with hp_def`. Establish `hp : p⁻¹ ∈ Mir k m` using `by show vecMul (eLast k m) ((p⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = eLast k m`. Rewrite using `[hp_def, _root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, ← xz_eq, hgh, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]`. Establish `hg : g = h * p` using `by rw [hp_def, mul_inv_cancel_left]`. Establish `hgi : g⁻¹ = p⁻¹ * h⁻¹` using `by rw [hg, _root_.mul_inv_rev]`.

Use `LinearMap.ext fun v => LinearMap.ext fun w => ?_` and prove the remaining obligations. Rewrite using `[Ct_apply, Ct_apply, hgi, map_mul, Module.End.mul_apply, Module.End.mul_apply, hC _ hp, ← mul_assoc]`. Use `congr 1`. Rewrite using `[hg, md_mul, md_inv, ← Complex.ofReal_mul, Real.mul_rpow (md_pos h).le (md_pos p).le, Real.inv_rpow (md_pos p).le, mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos (md_pos p) _).ne', mul_one]`.
-/
theorem Ct_congr (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
    {g h : GL (Fin (m + 1)) k}
    (hgh : xz m ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      xz m ᵥ* ((h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) :
    Ct gl s C g = Ct gl s C h := by
  set p := h⁻¹ * g with hp_def
  have hp : p⁻¹ ∈ Mir k m := by
    show vecMul (eLast k m) ((p⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = eLast k m
    rw [hp_def, _root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, ← xz_eq, hgh, vecMul_vecMul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, vecMul_one]
  have hg : g = h * p := by rw [hp_def, mul_inv_cancel_left]
  have hgi : g⁻¹ = p⁻¹ * h⁻¹ := by rw [hg, _root_.mul_inv_rev]
  refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
  rw [Ct_apply, Ct_apply, hgi, map_mul, Module.End.mul_apply, Module.End.mul_apply, hC _ hp, ← mul_assoc]
  congr 1
  rw [hg, md_mul, md_inv, ← Complex.ofReal_mul, Real.mul_rpow (md_pos h).le (md_pos p).le,
    Real.inv_rpow (md_pos p).le, mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos (md_pos p) _).ne', mul_one]

/- English proof (translation)
Rewrite using `[Df, if_neg hξ]`. Conclude with `Ct_congr hC ((sect_spec hξ).trans hg.symm)`.
-/
theorem Df_eq (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
    {ξ : Fin (m + 1) → k} (hξ : ξ ≠ 0) {g : GL (Fin (m + 1)) k}
    (hg : xz m ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ) :
    Df gl s C ξ = Ct gl s C g := by
  rw [Df, if_neg hξ]
  exact Ct_congr hC ((sect_spec hξ).trans hg.symm)

/- English proof (translation)
Establish `h0 : (xz m : Fin (m + 1) → k) ≠ 0`. Introduce `h`. Use `congrFun h (Fin.last m)` as an intermediate fact. Simplify using `[xz] at this`. Rewrite using `[Df_eq hC h0 (g := 1) (by simp), Ct_apply]`.

Simplify using `[md_one]`.
-/
theorem Df_xz (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w) (v w : V) :
    Df gl s C (xz m) v w = C v w := by
  have h0 : (xz m : Fin (m + 1) → k) ≠ 0 := by
    intro h
    have := congrFun h (Fin.last m)
    simp [xz] at this
  rw [Df_eq hC h0 (g := 1) (by simp), Ct_apply]
  simp [md_one]

end Forms

section Forms2

variable {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {ψ : AddChar k Circle}
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} {s : ℝ} {C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

/- English proof (translation)
Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]`. Evaluate the numerical expressions.
-/
theorem circ_mul_conj (z : Circle) : (z : ℂ) * starRingEnd ℂ (z : ℂ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
  norm_num

/- English proof (translation)
Rewrite using `[Ct_apply, Ct_apply, hCp.1, map_mul, Complex.conj_ofReal]`.
-/
theorem Ct_herm (hCp : Psd C) (g : GL (Fin (m + 1)) k) (v w : V) :
    Ct gl s C g w v = starRingEnd ℂ (Ct gl s C g v w) := by
  rw [Ct_apply, Ct_apply, hCp.1, map_mul, Complex.conj_ofReal]

/- English proof (translation)
Rewrite using `[Ct_apply, Complex.re_ofReal_mul]`. Conclude with `mul_nonneg (Real.rpow_nonneg (md_pos g).le _) (hCp.2 _)`.
-/
theorem Ct_re_nonneg (hCp : Psd C) (g : GL (Fin (m + 1)) k) (v : V) : 0 ≤ (Ct gl s C g v v).re := by
  rw [Ct_apply, Complex.re_ofReal_mul]
  exact mul_nonneg (Real.rpow_nonneg (md_pos g).le _) (hCp.2 _)

/- English proof (translation)
Distinguish the cases in `h : ξ = 0`. Substitute `h` using the available equality. Simplify using `[Df_zero]`. Simplify using `only [Df, if_neg h]`. Conclude with `Ct_herm hCp _ _ _`.
-/
theorem Df_herm (hCp : Psd C) (ξ : Fin (m + 1) → k) (v w : V) :
    Df gl s C ξ w v = starRingEnd ℂ (Df gl s C ξ v w) := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · simp only [Df, if_neg h]
    exact Ct_herm hCp _ _ _

/- English proof (translation)
Distinguish the cases in `h : ξ = 0`. Substitute `h` using the available equality. Simplify using `[Df_zero]`. Simplify using `only [Df, if_neg h]`. Conclude with `Ct_re_nonneg hCp _ _`.
-/
theorem Df_re_nonneg (hCp : Psd C) (ξ : Fin (m + 1) → k) (v : V) : 0 ≤ (Df gl s C ξ v v).re := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · simp only [Df, if_neg h]
    exact Ct_re_nonneg hCp _ _

/- English proof (translation)
Rewrite using `[Ct_apply, Ct_apply, hS.conj, hCc, dotProduct_mulVec]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Ct_col (hS : Setup col gl) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
    (g : GL (Fin (m + 1)) k) (x : Fin (m + 1) → k) (v w : V) :
    Ct gl s C g (col x v) w =
      ((ψ ((xz m ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) ⬝ᵥ x) : Circle) : ℂ) *
        Ct gl s C g v w := by
  rw [Ct_apply, Ct_apply, hS.conj, hCc, dotProduct_mulVec]
  ring

variable (hS : Setup col gl) (hCp : Psd C)
  (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
include hS hCc hC

/- English proof (translation)
Distinguish the cases in `h : ξ = 0`. Substitute `h` using the available equality. Simplify using `[Df_zero]`. Rewrite using `[Df_eq hC h (sect_spec h), Ct_col hS hCc, sect_spec h]`.
-/
theorem Df_col (ξ x : Fin (m + 1) → k) (v w : V) :
    Df gl s C ξ (col x v) w = ((ψ (ξ ⬝ᵥ x) : Circle) : ℂ) * Df gl s C ξ v w := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · rw [Df_eq hC h (sect_spec h), Ct_col hS hCc, sect_spec h]

include hCp

/- English proof (translation)
Rewrite using `[Df_herm hCp, Df_col hS hCc hC, map_mul, ← Df_herm hCp]`.
-/
theorem Df_col_right (ξ x : Fin (m + 1) → k) (v w : V) :
    Df gl s C ξ v (col x w) = starRingEnd ℂ ((ψ (ξ ⬝ᵥ x) : Circle) : ℂ) * Df gl s C ξ v w := by
  rw [Df_herm hCp, Df_col hS hCc hC, map_mul, ← Df_herm hCp]

/- English proof (translation)
Rewrite using `[Df_col_right hS hCp hCc hC, Df_col hS hCc hC, ← mul_assoc, mul_comm (starRingEnd ℂ _), circ_mul_conj, one_mul]`.
-/
theorem form_column_invariant (ξ x : Fin (m + 1) → k) (v w : V) : Df gl s C ξ (col x v) (col x w) = Df gl s C ξ v w := by
  rw [Df_col_right hS hCp hCc hC, Df_col hS hCc hC, ← mul_assoc, mul_comm (starRingEnd ℂ _), circ_mul_conj, one_mul]

omit hCp hCc in
/- English proof (translation)
Establish `hξg : ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ≠ 0`. Introduce `h0`. Apply `hξ` to reduce the goal to its premises. Use `congrArg (fun x => x ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) h0` as an intermediate fact. Simplify `this` using `[vecMul_vecMul, ← Units.val_mul]`.

Establish `hτ : xz m ᵥ* (((g⁻¹ * sect ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)`. Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hξ]`. Rewrite using `[Df_eq hC hξ (sect_spec hξ), Df_eq hC hξg hτ, Ct_apply, Ct_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev (g⁻¹) (sect ξ), inv_inv, ← mul_assoc, ← Complex.ofReal_mul]`. Use `congr 2`. Rewrite using `[md_mul, md_inv, Real.mul_rpow (inv_nonneg.mpr (md_pos g).le) (md_pos (sect ξ)).le, Real.inv_rpow (md_pos g).le, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos (md_pos g) _).ne', one_mul]`.
-/
theorem Df_gl {ξ : Fin (m + 1) → k} (hξ : ξ ≠ 0) (g : GL (Fin (m + 1)) k) (v w : V) :
    Df gl s C ξ (gl g v) (gl g w) =
      ((md g ^ (s + 1) : ℝ) : ℂ) * Df gl s C (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) v w := by
  have hξg : ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ≠ 0 := by
    intro h0
    apply hξ
    have := congrArg (fun x => x ᵥ* ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) h0
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  have hτ : xz m ᵥ* (((g⁻¹ * sect ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hξ]
  rw [Df_eq hC hξ (sect_spec hξ), Df_eq hC hξg hτ, Ct_apply, Ct_apply, ← Module.End.mul_apply, ← Module.End.mul_apply,
    ← map_mul, _root_.mul_inv_rev (g⁻¹) (sect ξ), inv_inv, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [md_mul, md_inv, Real.mul_rpow (inv_nonneg.mpr (md_pos g).le) (md_pos (sect ξ)).le, Real.inv_rpow (md_pos g).le,
    ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos (md_pos g) _).ne', one_mul]

omit hS hCc in
/- English proof (translation)
Distinguish the cases in `h : ξ = 0`. Substitute `h` using the available equality. Simplify using `[Df_zero]`. Simplify using `only [Df, if_neg h]`. Rewrite using `[Ct_apply, hCY _ (hY _ _ hy), mul_zero]`.
-/
theorem Df_ker (Y : Submodule ℂ V) (hY : ∀ g, ∀ y ∈ Y, gl g y ∈ Y) (hCY : ∀ y ∈ Y, ∀ w, C y w = 0)
    (ξ : Fin (m + 1) → k) {y : V} (hy : y ∈ Y) (w : V) : Df gl s C ξ y w = 0 := by
  by_cases h : ξ = 0
  · subst h
    simp [Df_zero]
  · simp only [Df, if_neg h]
    rw [Ct_apply, hCY _ (hY _ _ hy), mul_zero]

omit hCp hCc in

/- English proof (translation)
Take `⟨N, hNo, hζN, f, hf, hf1, hfN⟩` from `GlobalTheory.T.local_continuous_section_vecMul_orbit k (m + 1) ζ hζ`. Establish `hH : {h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | gl h w = w} ∩ {h | md h = 1} ∈ 𝓝 (1 : GL (Fin (m + 1)) k)`. Use `Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_` and prove the remaining obligations. Conclude with `(hS.smooth_gl v).mem_nhds (by simp)`. Conclude with `(hS.smooth_gl w).mem_nhds (by simp)`.

Use `filter_upwards [GlobalTheory.T.eventually_haar_det_eq_one_near_one k (m + 1)] with h hh`. Simplify using `[md, nabs, hh]`. Establish `hfc : ContinuousAt f ζ` using `hf.continuousAt (hNo.mem_nhds hζN)`. Establish `hpre : f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | gl h w = w} ∩ {h | md h = 1}) ∈ 𝓝 ζ` using `hfc (by rw [hf1]; exact hH)`. Use `filter_upwards [hNo.mem_nhds hζN, hpre] with ξ hξN hξH`.

Take `⟨⟨hv, hw⟩, hd⟩` from `hξH`. Establish `hξ : ζ ᵥ* (f ξ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ` using `hfN ξ hξN`. Establish `hξ0 : ξ ≠ 0`. Introduce `h0`. Apply `hζ` to reduce the goal to its premises.

Use `congrArg (fun x => x ᵥ* (((f ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) (hξ.trans h0)` as an intermediate fact. Simplify `this` using `[vecMul_vecMul, ← Units.val_mul]`. Establish `hτ : xz m ᵥ* ((((f ξ)⁻¹ * sect ζ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ`. Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hζ, hξ]`. Rewrite using `[Df_eq hC hξ0 hτ, Df_eq hC hζ (sect_spec hζ), Ct_apply, Ct_apply, _root_.mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply, Module.End.mul_apply, hv, hw, md_mul, md_inv, hd, inv_one, one_mul]`.
-/
theorem Df_loc {ζ : Fin (m + 1) → k} (hζ : ζ ≠ 0) (v w : V) : ∀ᶠ ξ in 𝓝 ζ, Df gl s C ξ v w = Df gl s C ζ v w := by
  obtain ⟨N, hNo, hζN, f, hf, hf1, hfN⟩ := GlobalTheory.T.local_continuous_section_vecMul_orbit k (m + 1) ζ hζ
  have hH : {h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | gl h w = w} ∩ {h | md h = 1} ∈ 𝓝 (1 : GL (Fin (m + 1)) k) := by
    refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
    · exact (hS.smooth_gl v).mem_nhds (by simp)
    · exact (hS.smooth_gl w).mem_nhds (by simp)
    · filter_upwards [GlobalTheory.T.eventually_haar_det_eq_one_near_one k (m + 1)] with h hh
      simp [md, nabs, hh]
  have hfc : ContinuousAt f ζ := hf.continuousAt (hNo.mem_nhds hζN)
  have hpre : f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | gl h w = w} ∩ {h | md h = 1}) ∈ 𝓝 ζ :=
    hfc (by rw [hf1]; exact hH)
  filter_upwards [hNo.mem_nhds hζN, hpre] with ξ hξN hξH
  obtain ⟨⟨hv, hw⟩, hd⟩ := hξH
  have hξ : ζ ᵥ* (f ξ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := hfN ξ hξN
  have hξ0 : ξ ≠ 0 := by
    intro h0
    apply hζ
    have := congrArg (fun x => x ᵥ* (((f ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) (hξ.trans h0)
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  have hτ : xz m ᵥ* ((((f ξ)⁻¹ * sect ζ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hζ, hξ]
  rw [Df_eq hC hξ0 hτ, Df_eq hC hζ (sect_spec hζ), Ct_apply, Ct_apply, _root_.mul_inv_rev, inv_inv, map_mul,
    Module.End.mul_apply, Module.End.mul_apply, hv, hw, md_mul, md_inv, hd, inv_one, one_mul]

end Forms2

section Meas

local instance instMeasK : MeasurableSpace k := borel k
local instance instBorelK : BorelSpace k := ⟨rfl⟩
local instance instSCK : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

variable {m : ℕ} (ψ : AddChar k Circle) (ν : Measure (Fin (m + 1) → k)) [ν.IsAddHaarMeasure]

/- English proof (translation)
Use `GlobalTheory.T.haar_measure_subgroup_relIndex_mul (Fin (m + 1) → k) ν (perp ψ A) (perp ψ A₀) (perp_anti ψ hle) (perp_open ψ hψ hψ1 h).measurableSet (by rw [perp_relIndex ψ hψ hψ1 h₀ h hle]; exact relIndex_ne_zero_of_lat h₀ h)` as an intermediate fact. Rewrite using `[this, perp_relIndex ψ hψ hψ1 h₀ h hle]`.
-/
theorem meas_perp_index (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A₀ A : AddSubgroup (Fin (m + 1) → k)} (h₀ : Lat A₀) (h : Lat A)
    (hle : A₀ ≤ A) : ν (perp ψ A₀) = (A₀.relIndex A : ℝ≥0∞) * ν (perp ψ A) := by
  have := GlobalTheory.T.haar_measure_subgroup_relIndex_mul (Fin (m + 1) → k) ν (perp ψ A) (perp ψ A₀) (perp_anti ψ hle)
    (perp_open ψ hψ hψ1 h).measurableSet (by rw [perp_relIndex ψ hψ hψ1 h₀ h hle]; exact relIndex_ne_zero_of_lat h₀ h)
  rw [this, perp_relIndex ψ hψ hψ1 h₀ h hle]

/- English proof (translation)
The claim follows from `(perp_compact ψ hψ hψ1 h).measure_lt_top`.
-/
theorem meas_perp_lt_top (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin (m + 1) → k)} (h : Lat A) :
    ν (perp ψ A) < ∞ := (perp_compact ψ hψ hψ1 h).measure_lt_top

/- English proof (translation)
The claim follows from `(perp_open ψ hψ hψ1 h).measure_ne_zero ν ⟨0, (perp ψ A).zero_mem⟩`.
-/
theorem meas_perp_ne_zero (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {A : AddSubgroup (Fin (m + 1) → k)} (h : Lat A) :
    ν (perp ψ A) ≠ 0 := (perp_open ψ hψ hψ1 h).measure_ne_zero ν ⟨0, (perp ψ A).zero_mem⟩

def gT (g : GL (Fin (m + 1)) k) : GL (Fin (m + 1)) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ)
    (by rw [det_transpose]; exact (Matrix.isUnits_det_units g).ne_zero)

/- English proof (translation)
Establish `: Matrix.GeneralLinearGroup.det (gT g) = Matrix.GeneralLinearGroup.det g`. Use `ext`. Simplify using `[gT, Matrix.GeneralLinearGroup.mkOfDetNeZero, det_transpose]`. Simplify using `only [md, this]`.
-/
theorem md_gT (g : GL (Fin (m + 1)) k) : md (gT g) = md g := by
  have : Matrix.GeneralLinearGroup.det (gT g) = Matrix.GeneralLinearGroup.det g := by
    ext
    simp [gT, Matrix.GeneralLinearGroup.mkOfDetNeZero, det_transpose]
  simp only [md, this]

/- English proof (translation)
Establish `h` using `GlobalTheory.InertLagChar.haarChar_det_mul_integral_comp_mulVec_localField k (m + 1) _ BorelSpace.measurable_eq ν inferInstance (gT g) f`. Establish `h2 : ∀ y : Fin (m + 1) → k, ((gT g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ y = y ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)`. Introduce `y`. Simplify using `[gT, Matrix.GeneralLinearGroup.mkOfDetNeZero, mulVec_transpose]`. Rewrite `h` using `[h2]`.

Establish `hmd : ((distribHaarChar k (Matrix.GeneralLinearGroup.det (gT g)) : ℝ≥0) : ℝ) = md g`. Rewrite using `[← md_gT]`. Both sides reduce to the same expression. Rewrite using `[← h, ← mul_assoc, ← Complex.ofReal_mul, hmd, inv_mul_cancel₀ (md_pos g).ne', Complex.ofReal_one, one_mul]`.
-/
theorem integral_vecMul (f : (Fin (m + 1) → k) → ℂ) (g : GL (Fin (m + 1)) k) :
    ∫ ξ, f (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) ∂ν = ((md g)⁻¹ : ℝ) * ∫ ξ, f ξ ∂ν := by
  have h := GlobalTheory.InertLagChar.haarChar_det_mul_integral_comp_mulVec_localField k (m + 1) _ BorelSpace.measurable_eq ν inferInstance (gT g) f
  have h2 : ∀ y : Fin (m + 1) → k, ((gT g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ y =
      y ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) := by
    intro y
    simp [gT, Matrix.GeneralLinearGroup.mkOfDetNeZero, mulVec_transpose]
  simp_rw [h2] at h
  have hmd : ((distribHaarChar k (Matrix.GeneralLinearGroup.det (gT g)) : ℝ≥0) : ℝ) = md g := by
    rw [← md_gT]; rfl
  rw [← h, ← mul_assoc, ← Complex.ofReal_mul, hmd, inv_mul_cancel₀ (md_pos g).ne', Complex.ofReal_one, one_mul]

/- English proof (translation)
Simplify using `only [mem_perp, gmap, AddSubgroup.mem_map, forall_exists_index, and_imp]`. Prove the components needed by the constructor for the conclusion. Introduce `h a ha`. Rewrite using `[← dotProduct_mulVec]`. Conclude with `h _ a ha (by simp)`.

Introduce and unpack `h _ a ha rfl`. Simplify using `only [LinearMap.toAddMonoidHom_coe, mulVecLin_apply]`. Rewrite using `[dotProduct_mulVec]`. Conclude with `h a ha`.
-/
theorem perp_gmap (g : GL (Fin (m + 1)) k) (A : AddSubgroup (Fin (m + 1) → k)) (ξ : Fin (m + 1) → k) :
    ξ ∈ perp ψ (gmap g A) ↔ ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ∈ perp ψ A := by
  simp only [mem_perp, gmap, AddSubgroup.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h a ha
    rw [← dotProduct_mulVec]
    exact h _ a ha (by simp)
  · rintro h _ a ha rfl
    simp only [LinearMap.toAddMonoidHom_coe, mulVecLin_apply]
    rw [dotProduct_mulVec]
    exact h a ha

/- English proof (translation)
Establish `hmeas : MeasurableSet (perp ψ A : Set (Fin (m + 1) → k))` using `(perp_open ψ hψ hψ1 hA).measurableSet`. Establish `hmeas' : MeasurableSet (perp ψ (gmap g A) : Set (Fin (m + 1) → k))` using `(perp_open ψ hψ hψ1 (lat_gmap g A hA)).measurableSet`. Establish `h` using `integral_vecMul ν ((perp ψ A : Set (Fin (m + 1) → k)).indicator fun _ => (1 : ℂ)) g`. Establish `hset : (fun ξ => (perp ψ A : Set (Fin (m + 1) → k)).indicator (fun _ => (1 : ℂ)) (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k))) = (perp ψ (gmap g A) : Set (Fin (m + 1) → k)).indicator fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `ξ`.

Distinguish the cases in `hξ : ξ ∈ perp ψ (gmap g A)`. Rewrite using `[Set.indicator_of_mem hξ, Set.indicator_of_mem ((perp_gmap ψ g A ξ).1 hξ)]`. Rewrite using `[Set.indicator_of_notMem hξ, Set.indicator_of_notMem (fun h => hξ ((perp_gmap ψ g A ξ).2 h))]`. Rewrite `h` using `[hset, integral_indicator_const _ hmeas', integral_indicator_const _ hmeas]`. Simplify using `only [Complex.real_smul, mul_one] at h`.

Conclude with `h` after adjusting the coercions.
-/
theorem meas_perp_gmap (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (g : GL (Fin (m + 1)) k) {A : AddSubgroup (Fin (m + 1) → k)}
    (hA : Lat A) : (ν (perp ψ (gmap g A))).toReal = (md g)⁻¹ * (ν (perp ψ A)).toReal := by
  have hmeas : MeasurableSet (perp ψ A : Set (Fin (m + 1) → k)) := (perp_open ψ hψ hψ1 hA).measurableSet
  have hmeas' : MeasurableSet (perp ψ (gmap g A) : Set (Fin (m + 1) → k)) :=
    (perp_open ψ hψ hψ1 (lat_gmap g A hA)).measurableSet
  have h := integral_vecMul ν ((perp ψ A : Set (Fin (m + 1) → k)).indicator fun _ => (1 : ℂ)) g
  have hset : (fun ξ => (perp ψ A : Set (Fin (m + 1) → k)).indicator (fun _ => (1 : ℂ))
      (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k))) =
      (perp ψ (gmap g A) : Set (Fin (m + 1) → k)).indicator fun _ => (1 : ℂ) := by
    funext ξ
    by_cases hξ : ξ ∈ perp ψ (gmap g A)
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem ((perp_gmap ψ g A ξ).1 hξ)]
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem (fun h => hξ ((perp_gmap ψ g A ξ).2 h))]
  rw [hset, integral_indicator_const _ hmeas', integral_indicator_const _ hmeas] at h
  simp only [Complex.real_smul, mul_one] at h
  exact_mod_cast h

end Meas

section Psd

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use `set c := E v w with hc`. Distinguish the cases in `h0 : c = 0`. Rewrite using `[h0, norm_zero]`. Conclude with `div_nonneg (add_nonneg (hE.2 v) (hE.2 w)) zero_le_two`. Establish `hn : (‖c‖ : ℝ) ≠ 0` using `norm_ne_zero_iff.mpr h0`.

Take `⟨z, hz⟩ : ∃ z : ℂ, z = c / (‖c‖ : ℂ)` from `⟨_, rfl⟩`. Establish `h` using `hE.2 (v - z • w)`. Establish `hwv : E w v = starRingEnd ℂ c` using `hE.1 v w`. Establish `e1 : starRingEnd ℂ z * c = (‖c‖ : ℂ)`. Rewrite using `[hz, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `e2 : z * starRingEnd ℂ c = (‖c‖ : ℂ)`. Use `congrArg (starRingEnd ℂ) e1` as an intermediate fact. Rewrite `this` using `[map_mul, Complex.conj_conj, Complex.conj_ofReal]`. Then use the resulting hypothesis.

Establish `e3 : z * starRingEnd ℂ z = 1`. Rewrite using `[hz, map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Rewrite using `[← pow_two]`. Conclude with `div_self (pow_ne_zero 2 (by exact_mod_cast hn))`.

Establish `hexp : E (v - z • w) (v - z • w) = E v v - (‖c‖ : ℂ) - (‖c‖ : ℂ) + E w w`. Simplify using `only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul]`. Rewrite using `[← hc, hwv]`. Take the linear combination `-e1 - e2 + (E w w) * e3`. Rewrite `h` using `[hexp]`.

Simplify using `only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem psd_norm_le (E : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hE : Psd E) (v w : V) : ‖E v w‖ ≤ ((E v v).re + (E w w).re) / 2 := by
  set c := E v w with hc
  by_cases h0 : c = 0
  · rw [h0, norm_zero]
    exact div_nonneg (add_nonneg (hE.2 v) (hE.2 w)) zero_le_two
  have hn : (‖c‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr h0
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = c / (‖c‖ : ℂ) := ⟨_, rfl⟩
  have h := hE.2 (v - z • w)
  have hwv : E w v = starRingEnd ℂ c := hE.1 v w
  have e1 : starRingEnd ℂ z * c = (‖c‖ : ℂ) := by
    rw [hz, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    field_simp
  have e2 : z * starRingEnd ℂ c = (‖c‖ : ℂ) := by
    have := congrArg (starRingEnd ℂ) e1
    rwa [map_mul, Complex.conj_conj, Complex.conj_ofReal] at this
  have e3 : z * starRingEnd ℂ z = 1 := by
    rw [hz, map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [← pow_two]
    exact div_self (pow_ne_zero 2 (by exact_mod_cast hn))
  have hexp : E (v - z • w) (v - z • w) = E v v - (‖c‖ : ℂ) - (‖c‖ : ℂ) + E w w := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul]
    rw [← hc, hwv]
    linear_combination -e1 - e2 + (E w w) * e3
  rw [hexp] at h
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at h
  linarith

end Psd

section Main

local instance measurableSpaceSecondLift : MeasurableSpace k := borel k
local instance borelSpaceSecondLift : BorelSpace k := ⟨rfl⟩
local instance instSCK2 : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [gmap, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, mulVecLin_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨z, hz, rfl⟩, rfl⟩`. Rewrite using `[mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]` and apply the resulting hypothesis.

Introduce `hx`. Use `⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x, ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]`.
-/
theorem gmap_gmap_inv {n : ℕ} (g : GL (Fin n) k) (M : AddSubgroup (Fin n → k)) : gmap g (gmap g⁻¹ M) = M := by
  ext x
  simp only [gmap, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, mulVecLin_apply]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  · intro hx
    refine ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x, ⟨x, hx, rfl⟩, ?_⟩
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

variable {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} (hS : Setup col gl) {s : ℝ}
  {B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : Lat A₀)
  (hBp : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
  (hBg : ∀ g v w, B (gl g v) (gl g w) = ((md g ^ s : ℝ) : ℂ) * B v w)
  (hD : IsD ψ col A₀ B B') (hCp : Psd C) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
  (hCB : ∀ v, (C v v).re ≤ (B' v v).re)
  {ν : Measure (Fin (m + 1) → k)} [ν.IsAddHaarMeasure] (hν : ν (perp ψ A₀) = 1)

include hψ hψ1 hS hA₀ hBg hD hCp hC hCB hν in

/- English proof (translation)
Take `⟨A₁, hA₁, hA₀₁, hA₁s⟩` from `hD (gl (sect ζ)⁻¹ v) (gl (sect ζ)⁻¹ v)`. Take `⟨N, hNo, hζN, f, hf, hf1, hfN⟩` from `GlobalTheory.T.local_continuous_section_vecMul_orbit k (m + 1) ζ hζ`. Establish `hH : {h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1} ∈ 𝓝 (1 : GL (Fin (m + 1)) k)`. Use `Filter.inter_mem ((hS.smooth_gl v).mem_nhds (by simp)) ?_` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.T.eventually_haar_det_eq_one_near_one k (m + 1)] with h hh`.

Simplify using `[md, nabs, hh]`. Establish `hfc : ContinuousAt f ζ` using `hf.continuousAt (hNo.mem_nhds hζN)`. Establish `hW : N ∩ f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1}) ∈ 𝓝 ζ` using `Filter.inter_mem (hNo.mem_nhds hζN) (hfc (by rw [hf1]; exact hH))`. Establish `hU : (fun η => ζ + η) ⁻¹' (N ∩ f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1})) ∈ 𝓝 (0 : Fin (m + 1) → k)`. Establish `: Filter.Tendsto (fun η : Fin (m + 1) → k => ζ + η) (𝓝 0) (𝓝 ζ)`.

Simplify using `using (continuous_add_left ζ).tendsto (0 : Fin (m + 1) → k)`. Conclude with `this hW`. Take `⟨M₁, hM₁, hM₁U⟩` from `lat_shrink ψ hψ hψ1 hU`. Establish `hSc : IsCompact ((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)))` using `(perp_compact ψ hψ hψ1 hM₁).image (continuous_const.add continuous_id)`. Establish `hSN : (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)) ⊆ N`.

Introduce and unpack `_ ⟨η, hη, rfl⟩`. Conclude with `(hM₁U hη).1`. Establish `hSH : ∀ ξ ∈ (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)), gl (f ξ) v = v ∧ md (f ξ) = 1`. Introduce and unpack `_ ⟨η, hη, rfl⟩`. Conclude with `(hM₁U hη).2`.

Establish `hKc : IsCompact ((fun p : (Fin (m + 1) → k) × (Fin (m + 1) → k) => ((((f p.1)⁻¹ * sect ζ : GL (Fin (m + 1)) k)) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ p.2) '' (((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))) ×ˢ (A₁ : Set (Fin (m + 1) → k))))`. Use `(hSc.prod hA₁.1).image_of_continuousOn ?_` and prove the remaining obligations. Establish `h1 : ContinuousOn (fun p : (Fin (m + 1) → k) × (Fin (m + 1) → k) => f p.1) (((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))) ×ˢ (A₁ : Set (Fin (m + 1) → k)))` using `(hf.mono hSN).comp continuous_fst.continuousOn (fun p hp => hp.1)`. Establish `h2` using `Units.continuous_val.comp_continuousOn (h1.inv.mul continuousOn_const (g := fun _ => (sect ζ : GL (Fin (m + 1)) k)))`. Conclude with `(continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn (h2.prodMk continuous_snd.continuousOn)`.

Take `⟨M₂, hM₂, hKM₂⟩` from `lat_over hKc`. Take `⟨M₀, hM₀, hM₁M₀, hM₂M₀⟩` from `lat_sup hM₁ hM₂`. Use `⟨M₀, hM₀, fun ξ hξ => ?_⟩` and prove the remaining obligations. Establish `hξS : ξ ∈ (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))` using `⟨ξ - ζ, perp_anti ψ hM₁M₀ hξ, by abel⟩`. Take `⟨hhv, hhd⟩` from `hSH ξ hξS`.

Establish `hζh : ζ ᵥ* (f ξ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ` using `hfN ξ (hSN hξS)`. Establish `hg'ξ : xz m ᵥ* ((((f ξ)⁻¹ * sect ζ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ`. Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hζ, hζh]`. Establish `hξ0 : ξ ≠ 0`. Introduce `h0`.

Apply `hζ` to reduce the goal to its premises. Use `congrArg (fun x => x ᵥ* (((f ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) (hζh.trans h0)` as an intermediate fact. Simplify `this` using `[vecMul_vecMul, ← Units.val_mul]`. Establish `hu : gl ((f ξ)⁻¹ * sect ζ)⁻¹ v = gl (sect ζ)⁻¹ v`. Rewrite using `[_root_.mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply, hhv]`.

Establish `hDg : Df gl s C ξ v v = Ct gl s C ((f ξ)⁻¹ * sect ζ) v v` using `by rw [Df_eq hC hξ0 hg'ξ]`. Establish `hconst : Df gl s C ξ v v = Df gl s C ζ v v`. Rewrite using `[hDg, Df_eq hC hζ (sect_spec hζ), Ct_apply, Ct_apply, hu, md_mul, md_inv, hhd, inv_one, one_mul]`. Use `⟨hconst, fun M hM hM₀M => ?_⟩` and prove the remaining obligations. Use `set g' : GL (Fin (m + 1)) k := (f ξ)⁻¹ * sect ζ with hg'`.

Establish `hA : Lat (gmap g'⁻¹ M)` using `lat_gmap _ M hM`. Establish `hA₁A : A₁ ≤ gmap g'⁻¹ M`. Introduce `a ha`. Establish `hK : ((g' : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a) ∈ M` using `hM₀M (hM₂M₀ (hKM₂ ⟨(ξ, a), ⟨hξS, ha⟩, rfl⟩))`. Use `AddSubgroup.mem_map.mpr ⟨_, hK, ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.toAddMonoidHom_coe, mulVecLin_apply]`. Rewrite using `[mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]`. Establish `hdens` using `hA₁s _ hA hA₁A`. Establish `hav` using `av_conj ψ hψ col hS.col_zero hS.col_add hS.smooth_col gl hS.conj g'⁻¹ M hM ξ v`. Establish `hξg' : ξ ᵥ* (((g'⁻¹)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = xz m`.

Rewrite using `[inv_inv, ← hg'ξ, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]`. Rewrite `hav` using `[hξg', hu]`. Rewrite `hdens` using `[← hav, ← hu, hBg]`. Establish `hmM : (ν (perp ψ M)).toReal = (md g')⁻¹ * (ν (perp ψ (gmap g'⁻¹ M))).toReal`. Rewrite using `[← meas_perp_gmap ψ ν hψ hψ1 g' hA, gmap_gmap_inv]`.

Establish `hidx` using `meas_perp_index ψ ν hψ hψ1 hA₀ hA (hA₀₁.trans hA₁A)`. Rewrite `hidx` using `[hν]`. Establish `hr : ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) * (ν (perp ψ (gmap g'⁻¹ M))).toReal = 1`. Use `congrArg ENNReal.toReal hidx` as an intermediate fact. Rewrite `this` using `[ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one]`.

Conclude with `this.symm`. Establish `hrpos : (0 : ℝ) < (A₀.relIndex (gmap g'⁻¹ M) : ℕ)`. Conclude with `Nat.pos_of_ne_zero (relIndex_ne_zero_of_lat hA₀ hA)` after adjusting the coercions. Establish `hre1 : (Df gl s C ζ v v).re = md g' ^ (s + 1) * (C (gl g'⁻¹ v) (gl g'⁻¹ v)).re`. Rewrite using `[← hconst, hDg, Ct_apply, Complex.re_ofReal_mul]`.

Establish `hre2 : (B' (gl g'⁻¹ v) (gl g'⁻¹ v)).re = ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) * (md g'⁻¹ ^ s * (B (av ψ col ξ M v) v).re)`. Rewrite using `[hdens, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.re_ofReal_mul]`. Establish `hle` using `hCB (gl g'⁻¹ v)`. Use `set t := md g' with ht`. Establish `htpos : 0 < t` using `md_pos g'`.

Use `set r : ℝ := ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) with hrdef`. Use `set b := (B (av ψ col ξ M v) v).re with hb`. Use `set c := (C (gl g'⁻¹ v) (gl g'⁻¹ v)).re with hc`. Use `set μA := (ν (perp ψ (gmap g'⁻¹ M))).toReal with hμA`. Rewrite `hre2` using `[md_inv, ← ht]`.

Rewrite using `[hre1, hmM]`. Establish `hμA' : μA = r⁻¹` using `eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hr)`. Rewrite using `[hμA']`. Establish `hts : t ^ (s + 1) = t ^ s * t` using `Real.rpow_add_one htpos.ne' s`. Establish `hti : t⁻¹ ^ s = (t ^ s)⁻¹` using `Real.inv_rpow htpos.le s`.

Rewrite `hre2` using `[hti]`. Establish `htspos : 0 < t ^ s` using `Real.rpow_pos_of_pos htpos s`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hre2]`. Use `gcongr`.

Use `_ = b := by`. Rewrite using `[hts]`. Clear the denominators using the available nonvanishing facts.
-/
theorem locB {ζ : Fin (m + 1) → k} (hζ : ζ ≠ 0) (v : V) :
    ∃ M₀ : AddSubgroup (Fin (m + 1) → k), Lat M₀ ∧ ∀ ξ, ξ - ζ ∈ perp ψ M₀ →
      Df gl s C ξ v v = Df gl s C ζ v v ∧ ∀ M, Lat M → M₀ ≤ M →
        (Df gl s C ζ v v).re * (ν (perp ψ M)).toReal ≤ (B (av ψ col ξ M v) v).re := by
  obtain ⟨A₁, hA₁, hA₀₁, hA₁s⟩ := hD (gl (sect ζ)⁻¹ v) (gl (sect ζ)⁻¹ v)
  obtain ⟨N, hNo, hζN, f, hf, hf1, hfN⟩ := GlobalTheory.T.local_continuous_section_vecMul_orbit k (m + 1) ζ hζ
  have hH : {h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1} ∈ 𝓝 (1 : GL (Fin (m + 1)) k) := by
    refine Filter.inter_mem ((hS.smooth_gl v).mem_nhds (by simp)) ?_
    filter_upwards [GlobalTheory.T.eventually_haar_det_eq_one_near_one k (m + 1)] with h hh
    simp [md, nabs, hh]
  have hfc : ContinuousAt f ζ := hf.continuousAt (hNo.mem_nhds hζN)
  have hW : N ∩ f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1}) ∈ 𝓝 ζ :=
    Filter.inter_mem (hNo.mem_nhds hζN) (hfc (by rw [hf1]; exact hH))
  have hU : (fun η => ζ + η) ⁻¹' (N ∩ f ⁻¹' ({h : GL (Fin (m + 1)) k | gl h v = v} ∩ {h | md h = 1})) ∈
      𝓝 (0 : Fin (m + 1) → k) := by
    have : Filter.Tendsto (fun η : Fin (m + 1) → k => ζ + η) (𝓝 0) (𝓝 ζ) := by
      simpa using (continuous_add_left ζ).tendsto (0 : Fin (m + 1) → k)
    exact this hW
  obtain ⟨M₁, hM₁, hM₁U⟩ := lat_shrink ψ hψ hψ1 hU
  have hSc : IsCompact ((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))) :=
    (perp_compact ψ hψ hψ1 hM₁).image (continuous_const.add continuous_id)
  have hSN : (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)) ⊆ N := by
    rintro _ ⟨η, hη, rfl⟩
    exact (hM₁U hη).1
  have hSH : ∀ ξ ∈ (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)), gl (f ξ) v = v ∧ md (f ξ) = 1 := by
    rintro _ ⟨η, hη, rfl⟩
    exact (hM₁U hη).2
  have hKc : IsCompact ((fun p : (Fin (m + 1) → k) × (Fin (m + 1) → k) =>
      ((((f p.1)⁻¹ * sect ζ : GL (Fin (m + 1)) k)) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ p.2) ''
        (((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))) ×ˢ (A₁ : Set (Fin (m + 1) → k)))) := by
    refine (hSc.prod hA₁.1).image_of_continuousOn ?_
    have h1 : ContinuousOn (fun p : (Fin (m + 1) → k) × (Fin (m + 1) → k) => f p.1)
        (((fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k))) ×ˢ (A₁ : Set (Fin (m + 1) → k))) :=
      (hf.mono hSN).comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h2 := Units.continuous_val.comp_continuousOn (h1.inv.mul continuousOn_const
      (g := fun _ => (sect ζ : GL (Fin (m + 1)) k)))
    exact (continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn (h2.prodMk continuous_snd.continuousOn)
  obtain ⟨M₂, hM₂, hKM₂⟩ := lat_over hKc
  obtain ⟨M₀, hM₀, hM₁M₀, hM₂M₀⟩ := lat_sup hM₁ hM₂
  refine ⟨M₀, hM₀, fun ξ hξ => ?_⟩
  have hξS : ξ ∈ (fun η => ζ + η) '' (perp ψ M₁ : Set (Fin (m + 1) → k)) :=
    ⟨ξ - ζ, perp_anti ψ hM₁M₀ hξ, by abel⟩
  obtain ⟨hhv, hhd⟩ := hSH ξ hξS
  have hζh : ζ ᵥ* (f ξ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := hfN ξ (hSN hξS)
  have hg'ξ : xz m ᵥ* ((((f ξ)⁻¹ * sect ζ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← vecMul_vecMul, sect_spec hζ, hζh]
  have hξ0 : ξ ≠ 0 := by
    intro h0
    apply hζ
    have := congrArg (fun x => x ᵥ* (((f ξ)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) (hζh.trans h0)
    simpa [vecMul_vecMul, ← Units.val_mul] using this
  have hu : gl ((f ξ)⁻¹ * sect ζ)⁻¹ v = gl (sect ζ)⁻¹ v := by
    rw [_root_.mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply, hhv]
  have hDg : Df gl s C ξ v v = Ct gl s C ((f ξ)⁻¹ * sect ζ) v v := by rw [Df_eq hC hξ0 hg'ξ]
  have hconst : Df gl s C ξ v v = Df gl s C ζ v v := by
    rw [hDg, Df_eq hC hζ (sect_spec hζ), Ct_apply, Ct_apply, hu, md_mul, md_inv, hhd, inv_one, one_mul]
  refine ⟨hconst, fun M hM hM₀M => ?_⟩
  set g' : GL (Fin (m + 1)) k := (f ξ)⁻¹ * sect ζ with hg'
  have hA : Lat (gmap g'⁻¹ M) := lat_gmap _ M hM
  have hA₁A : A₁ ≤ gmap g'⁻¹ M := by
    intro a ha
    have hK : ((g' : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ a) ∈ M :=
      hM₀M (hM₂M₀ (hKM₂ ⟨(ξ, a), ⟨hξS, ha⟩, rfl⟩))
    refine AddSubgroup.mem_map.mpr ⟨_, hK, ?_⟩
    simp only [LinearMap.toAddMonoidHom_coe, mulVecLin_apply]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hdens := hA₁s _ hA hA₁A
  have hav := av_conj ψ hψ col hS.col_zero hS.col_add hS.smooth_col gl hS.conj g'⁻¹ M hM ξ v
  have hξg' : ξ ᵥ* (((g'⁻¹)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = xz m := by
    rw [inv_inv, ← hg'ξ, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
  rw [hξg', hu] at hav
  rw [← hav, ← hu, hBg] at hdens

  have hmM : (ν (perp ψ M)).toReal = (md g')⁻¹ * (ν (perp ψ (gmap g'⁻¹ M))).toReal := by
    rw [← meas_perp_gmap ψ ν hψ hψ1 g' hA, gmap_gmap_inv]
  have hidx := meas_perp_index ψ ν hψ hψ1 hA₀ hA (hA₀₁.trans hA₁A)
  rw [hν] at hidx
  have hr : ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) * (ν (perp ψ (gmap g'⁻¹ M))).toReal = 1 := by
    have := congrArg ENNReal.toReal hidx
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at this
    exact this.symm
  have hrpos : (0 : ℝ) < (A₀.relIndex (gmap g'⁻¹ M) : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero (relIndex_ne_zero_of_lat hA₀ hA)

  have hre1 : (Df gl s C ζ v v).re = md g' ^ (s + 1) * (C (gl g'⁻¹ v) (gl g'⁻¹ v)).re := by
    rw [← hconst, hDg, Ct_apply, Complex.re_ofReal_mul]
  have hre2 : (B' (gl g'⁻¹ v) (gl g'⁻¹ v)).re =
      ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) * (md g'⁻¹ ^ s * (B (av ψ col ξ M v) v).re) := by
    rw [hdens, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hle := hCB (gl g'⁻¹ v)
  set t := md g' with ht
  have htpos : 0 < t := md_pos g'
  set r : ℝ := ((A₀.relIndex (gmap g'⁻¹ M) : ℕ) : ℝ) with hrdef
  set b := (B (av ψ col ξ M v) v).re with hb
  set c := (C (gl g'⁻¹ v) (gl g'⁻¹ v)).re with hc
  set μA := (ν (perp ψ (gmap g'⁻¹ M))).toReal with hμA
  rw [md_inv, ← ht] at hre2
  rw [hre1, hmM]
  have hμA' : μA = r⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hr)
  rw [hμA']
  have hts : t ^ (s + 1) = t ^ s * t := Real.rpow_add_one htpos.ne' s
  have hti : t⁻¹ ^ s = (t ^ s)⁻¹ := Real.inv_rpow htpos.le s
  rw [hti] at hre2
  have htspos : 0 < t ^ s := Real.rpow_pos_of_pos htpos s
  calc t ^ (s + 1) * c * (t⁻¹ * r⁻¹) ≤ t ^ (s + 1) * (r * ((t ^ s)⁻¹ * b)) * (t⁻¹ * r⁻¹) := by
        rw [← hre2]
        gcongr
    _ = b := by
        rw [hts]
        field_simp

end Main

end PositivityTheory.RgUd.Form.U.Lift2
