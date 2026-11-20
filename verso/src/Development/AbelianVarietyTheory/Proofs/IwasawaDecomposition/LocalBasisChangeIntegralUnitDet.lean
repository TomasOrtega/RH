import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalTwSubK
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

noncomputable section

namespace GlobalTheory.LocBasisChange

/- English proof (translation)
Establish `h : x ∈ (NormedField.valuation (K` using `C)).integer := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top`. Rewrite `h` using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `h` after adjusting the coercions.
-/
theorem norm_le_one_of_isIntegral_int {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_` and prove the remaining obligations. Establish `hp : ‖∏ i, M (σ i) i‖ ≤ 1`. Rewrite using `[norm_prod]`. Conclude with `Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _`.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]`. Rewrite using `[one_smul]` and apply the resulting hypothesis. Rewrite using `[Units.neg_smul, one_smul, norm_neg]` and apply the resulting hypothesis.
-/
theorem norm_det_le_one {C : Type} [NormedField C] [IsUltrametricDist C] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (h : ∀ a b, ‖M a b‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hp : ‖∏ i, M (σ i) i‖ ≤ 1 := by
    rw [norm_prod]; exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, norm_neg]

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd Fact.out).2 hs`.
-/
theorem norm_natCast_of_not_dvd {p : ℕ} [Fact p.Prime] {s : ℕ} (hs : ¬ p ∣ s) : ‖(s : ℂ_[p])‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hs

/- English proof (translation)
Introduce `D p _ lam τ N L Bm Bs hR hL`. Establish `hm : ∀ x, TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar` using `fun x => mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)`. Use `set ρ : D.host.E →+* ℂ_[p] := lam.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar hm) with hρ`. Establish `hρe : ∀ x, TaylorLogMetric.tauEmb D lam τ x = ρ x` using `fun x => dif_pos (hm x)`. Establish `hint : ∀ y : 𝓞 D.host.E, ‖ρ (y : D.host.E)‖ ≤ 1` using `fun y => norm_le_one_of_isIntegral_int (map_isIntegral_int ρ y.isIntegral_coe)`.

Establish `hunit : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1` using `fun s hs => by`. Rewrite using `[map_natCast]`. Conclude with `norm_natCast_of_not_dvd hs`. Use `set Mm : Matrix (Fin N) (Fin N) D.host.E := (Bm : Matrix (Fin N) (Fin N) D.host.E) with hMm`. Use `set Mi : Matrix (Fin N) (Fin N) D.host.E := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) with hMi`.

Establish `hMMi : Mm * Mi = 1` using `Bm.mul_inv`. Establish `hMiM : Mi * Mm = 1` using `Bm.inv_mul`. Use `set A : Matrix (Fin N) (Fin N) ℂ_[p] := Mm.map ρ with hA`. Use `set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := Mi.map ρ with hAi`. Establish `hAAi : A * Ai = 1`.

Simplify using `only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMMi, map_one]`. Establish `hAiA : Ai * A = 1`. Simplify using `only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMiM, map_one]`. Use `set g : Matrix (Fin N) (Fin N) ℂ_[p] := Ai * Bs with hg`. Establish `hBs : Bs = A * g` using `by rw [hg, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]`.

Establish `hgi : ∀ a b, ‖g a b‖ ≤ 1`. Introduce `a b`. Take `⟨n, r, x, hr, hx, hB⟩` from `hR.2.2 b`. Establish `e : g a b = ∑ k, r k * ρ ((Mi *ᵥ x k) a)`. Simplify using `only [hg, Matrix.mul_apply, hB, hρe, hAi, Matrix.map_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[e]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_` and prove the remaining obligations. Take `⟨s, hs, hmem⟩` from `(hL (x k)).1 ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using hx k⟩`.

Take `⟨z, hz⟩` from `hmem a`. Establish `h1 : ‖ρ ((s : D.host.E) * (Mi *ᵥ x k) a)‖ ≤ 1` using `by rw [← hz]; exact hint z`. Rewrite `h1` using `[map_mul, norm_mul, hunit s hs, one_mul]`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hBsu : IsUnit Bs.det` using `isUnit_iff_ne_zero.2 hR.1`. Use `set h : Matrix (Fin N) (Fin N) ℂ_[p] := Bs⁻¹ * A with hh`. Establish `hgh : g * h = 1`. Rewrite using `[hg, hh, Matrix.mul_assoc, ← Matrix.mul_assoc Bs, Matrix.mul_nonsing_inv _ hBsu, Matrix.one_mul, hAiA]`. Establish `hhi : ∀ a b, ‖h a b‖ ≤ 1`.

Introduce `a b`. Use `set xb : Fin N → D.host.E := fun j => Mm j b with hxb`. Establish `hcol : ∀ a, (Mi *ᵥ xb) a = (1 : Matrix (Fin N) (Fin N) D.host.E) a b`. Introduce `a`. Rewrite using `[← hMiM]`.

Both sides reduce to the same expression. Take `⟨s, hs, hmem⟩` from `(hL xb).2 ⟨1, (Fact.out : p.Prime).not_dvd_one, fun a => by`. Rewrite using `[hcol, Nat.cast_one, one_mul, Matrix.one_apply]`. Use `split_ifs`. Conclude with `⟨1, map_one _⟩`.

Conclude with `⟨0, map_zero _⟩⟩`. Establish `hb` using `hR.2.1 _ hmem a`. Establish `key : (Bs⁻¹ *ᵥ fun i => TaylorLogMetric.tauEmb D lam τ (((s : D.host.E) • xb) i)) a = ρ s * h a b`. Simplify using `only [hρe, Pi.smul_apply, smul_eq_mul, map_mul, hh, Matrix.mul_apply, Matrix.mulVec, dotProduct, hA, Matrix.map_apply, hxb, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.

Rewrite `hb` using `[key, norm_mul, map_natCast, norm_natCast_of_not_dvd hs, one_mul]`. Conclude with `hb`. Establish `hd1` using `norm_det_le_one g hgi`. Establish `hd2` using `norm_det_le_one h hhi`. Establish `hprod : ‖g.det‖ * ‖h.det‖ = 1`.

Rewrite using `[← norm_mul, ← Matrix.det_mul, hgh, Matrix.det_one, norm_one]`. Use `⟨g, hgi, le_antisymm hd1 ?_, ?_⟩` and prove the remaining obligations. Use `swap`. Rewrite using `[hBs]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `only [hA, Matrix.map_apply, hρe]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem basis_change : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (Bs : Matrix (Fin N) (Fin N) ℂ_[p]),
    GL3Columns.BasR D lam τ L Bs → Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm →
    ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧
      Bs = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  intro D p _ lam τ N L Bm Bs hR hL
  have hm : ∀ x, TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  set ρ : D.host.E →+* ℂ_[p] := lam.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar hm) with hρ
  have hρe : ∀ x, TaylorLogMetric.tauEmb D lam τ x = ρ x := fun x => dif_pos (hm x)
  have hint : ∀ y : 𝓞 D.host.E, ‖ρ (y : D.host.E)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral_int (map_isIntegral_int ρ y.isIntegral_coe)
  have hunit : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1 := fun s hs => by
    rw [map_natCast]; exact norm_natCast_of_not_dvd hs
  set Mm : Matrix (Fin N) (Fin N) D.host.E := (Bm : Matrix (Fin N) (Fin N) D.host.E) with hMm
  set Mi : Matrix (Fin N) (Fin N) D.host.E := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) with hMi
  have hMMi : Mm * Mi = 1 := Bm.mul_inv
  have hMiM : Mi * Mm = 1 := Bm.inv_mul
  set A : Matrix (Fin N) (Fin N) ℂ_[p] := Mm.map ρ with hA
  set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := Mi.map ρ with hAi
  have hAAi : A * Ai = 1 := by
    simp only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMMi, map_one]
  have hAiA : Ai * A = 1 := by
    simp only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMiM, map_one]
  set g : Matrix (Fin N) (Fin N) ℂ_[p] := Ai * Bs with hg
  have hBs : Bs = A * g := by rw [hg, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
  have hgi : ∀ a b, ‖g a b‖ ≤ 1 := by
    intro a b
    obtain ⟨n, r, x, hr, hx, hB⟩ := hR.2.2 b
    have e : g a b = ∑ k, r k * ρ ((Mi *ᵥ x k) a) := by
      simp only [hg, Matrix.mul_apply, hB, hρe, hAi, Matrix.map_apply, Matrix.mulVec, dotProduct, map_sum,
        map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    obtain ⟨s, hs, hmem⟩ := (hL (x k)).1 ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using hx k⟩
    obtain ⟨z, hz⟩ := hmem a
    have h1 : ‖ρ ((s : D.host.E) * (Mi *ᵥ x k) a)‖ ≤ 1 := by rw [← hz]; exact hint z
    rw [map_mul, norm_mul, hunit s hs, one_mul] at h1
    rw [norm_mul]
    calc ‖r k‖ * ‖ρ ((Mi *ᵥ x k) a)‖ ≤ 1 * 1 := by gcongr; exact hr k
      _ = 1 := one_mul 1
  have hBsu : IsUnit Bs.det := isUnit_iff_ne_zero.2 hR.1
  set h : Matrix (Fin N) (Fin N) ℂ_[p] := Bs⁻¹ * A with hh
  have hgh : g * h = 1 := by
    rw [hg, hh, Matrix.mul_assoc, ← Matrix.mul_assoc Bs, Matrix.mul_nonsing_inv _ hBsu, Matrix.one_mul, hAiA]
  have hhi : ∀ a b, ‖h a b‖ ≤ 1 := by
    intro a b
    set xb : Fin N → D.host.E := fun j => Mm j b with hxb
    have hcol : ∀ a, (Mi *ᵥ xb) a = (1 : Matrix (Fin N) (Fin N) D.host.E) a b := by
      intro a; rw [← hMiM]; rfl
    obtain ⟨s, hs, hmem⟩ := (hL xb).2 ⟨1, (Fact.out : p.Prime).not_dvd_one, fun a => by
      rw [hcol, Nat.cast_one, one_mul, Matrix.one_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩⟩
    have hb := hR.2.1 _ hmem a
    have key : (Bs⁻¹ *ᵥ fun i => TaylorLogMetric.tauEmb D lam τ (((s : D.host.E) • xb) i)) a = ρ s * h a b := by
      simp only [hρe, Pi.smul_apply, smul_eq_mul, map_mul, hh, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        hA, Matrix.map_apply, hxb, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [key, norm_mul, map_natCast, norm_natCast_of_not_dvd hs, one_mul] at hb
    exact hb
  have hd1 := norm_det_le_one g hgi
  have hd2 := norm_det_le_one h hhi
  have hprod : ‖g.det‖ * ‖h.det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, hgh, Matrix.det_one, norm_one]
  refine ⟨g, hgi, le_antisymm hd1 ?_, ?_⟩
  swap
  · rw [hBs]; congr 1; ext i j; simp only [hA, Matrix.map_apply, hρe]
  calc (1 : ℝ) = ‖g.det‖ * ‖h.det‖ := hprod.symm
    _ ≤ ‖g.det‖ * 1 := by gcongr
    _ = ‖g.det‖ := mul_one _

end GlobalTheory.LocBasisChange

end
