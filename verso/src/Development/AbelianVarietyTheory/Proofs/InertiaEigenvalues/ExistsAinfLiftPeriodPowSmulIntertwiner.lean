import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeCoeffTensorAinfOfFrobeniusEqMatrixMul

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.PoleBound

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {τ : Ainf l}

/- English proof (translation)
Rewrite using `[frobW_inclW, hτ.1, map_mul]`. Both sides reduce to the same expression.
-/
theorem frobW_per (hτ : bk.IsPer τ) : frobW l (inclW l τ) = bk.evW bk.E * inclW l τ := by
  rw [frobW_inclW, hτ.1, map_mul]; rfl

/- English proof (translation)
Establish `key : ∀ r j, inclW l τ ^ S.a * T r j ∈ (inclW l).range` using `fun r => GlobalTheory.FrobIntTensor.mem_range_inclW l (fun j => inclW l τ ^ S.a * T r j) (Matrix.of fun j i => bk.ev (S.A i j)) fun j => by`. Establish `e` using `congrFun (congrFun h.φ r) j`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e`. Rewrite using `[map_mul, map_pow, frobW_per hτ, mul_pow, mul_comm (bk.evW bk.E ^ S.a), mul_assoc, e, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = bk.evW (S.A i j) * _`. Expand and normalize the polynomial expressions, which then agree. Use `choose t ht using key`. Conclude with `⟨Matrix.of t, Matrix.ext fun r j => ht r j⟩`.
-/
theorem exists_basis {d : ℕ} {S : Strat bk d} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    {T : Matrix (Fin d) (Fin d) (WCb l)} (hτ : bk.IsPer τ) (h : MReal S ρ T) :
    ∃ t : Matrix (Fin d) (Fin d) (Ainf l), t.map (inclW l) = inclW l τ ^ S.a • T := by
  have key : ∀ r j, inclW l τ ^ S.a * T r j ∈ (inclW l).range := fun r =>
    GlobalTheory.FrobIntTensor.mem_range_inclW l (fun j => inclW l τ ^ S.a * T r j)
      (Matrix.of fun j i => bk.ev (S.A i j)) fun j => by
        have e := congrFun (congrFun h.φ r) j
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e
        rw [map_mul, map_pow, frobW_per hτ, mul_pow, mul_comm (bk.evW bk.E ^ S.a), mul_assoc, e, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = bk.evW (S.A i j) * _
        ring
  choose t ht using key
  exact ⟨Matrix.of t, Matrix.ext fun r j => ht r j⟩

/- English proof (translation)
Establish `h1 : U.map (frobW l) * T.map (frobW l) = 1`. Rewrite using `[← Matrix.map_mul (f := frobW l), hU, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h2 : S.A.map bk.evW * S.A'.map bk.evW = bk.evW bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) (WCb l))`. Rewrite using `[← Matrix.map_mul (f := bk.evW), S.A_mul]`. Use `ext1 i j`.

Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h3 : bk.evW bk.E ^ S.b • U.map (frobW l) = bk.evW bk.E ^ S.a • (S.A'.map bk.evW * U)`. Establish `e` using `congrArg (fun M => U.map (frobW l) * (M * S.A'.map bk.evW) * U) h.φ`. Simplify using `only [Matrix.mul_assoc T, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at e`.

Rewrite `e` using `[← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, hT, Matrix.mul_one]`. Conclude with `e.symm`. Establish `key : ∀ r j, inclW l τ ^ S.b * U j r ∈ (inclW l).range` using `fun r => GlobalTheory.FrobIntTensor.mem_range_inclW l (fun j => inclW l τ ^ S.b * U j r) (Matrix.of fun j i => bk.ev (bk.E ^ S.a * S.A' j i)) fun j => by`. Establish `e` using `congrFun (congrFun h3 j) r`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e`.

Rewrite using `[map_mul, map_pow, frobW_per hτ, mul_pow, mul_comm (bk.evW bk.E ^ S.b), mul_assoc, e, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = bk.evW (bk.E ^ S.a * S.A' j i) * _`. Rewrite using `[map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.

Use `choose t ht using key`. Conclude with `⟨Matrix.of fun j r => t r j, Matrix.ext fun j r => ht r j⟩`.
-/
theorem exists_inv {d : ℕ} {S : Strat bk d} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    {T U : Matrix (Fin d) (Fin d) (WCb l)} (hτ : bk.IsPer τ) (h : MReal S ρ T) (hU : U * T = 1) (hT : T * U = 1) :
    ∃ t : Matrix (Fin d) (Fin d) (Ainf l), t.map (inclW l) = inclW l τ ^ S.b • U := by
  have h1 : U.map (frobW l) * T.map (frobW l) = 1 := by
    rw [← Matrix.map_mul (f := frobW l), hU, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : S.A.map bk.evW * S.A'.map bk.evW = bk.evW bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul (f := bk.evW), S.A_mul]
    ext1 i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : bk.evW bk.E ^ S.b • U.map (frobW l) = bk.evW bk.E ^ S.a • (S.A'.map bk.evW * U) := by
    have e := congrArg (fun M => U.map (frobW l) * (M * S.A'.map bk.evW) * U) h.φ
    simp only [Matrix.mul_assoc T, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at e
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, hT, Matrix.mul_one] at e
    exact e.symm
  have key : ∀ r j, inclW l τ ^ S.b * U j r ∈ (inclW l).range := fun r =>
    GlobalTheory.FrobIntTensor.mem_range_inclW l (fun j => inclW l τ ^ S.b * U j r)
      (Matrix.of fun j i => bk.ev (bk.E ^ S.a * S.A' j i)) fun j => by
        have e := congrFun (congrFun h3 j) r
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e
        rw [map_mul, map_pow, frobW_per hτ, mul_pow, mul_comm (bk.evW bk.E ^ S.b), mul_assoc, e, Finset.mul_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = bk.evW (bk.E ^ S.a * S.A' j i) * _
        rw [map_mul, map_pow]
        ring
  choose t ht using key
  exact ⟨Matrix.of fun j r => t r j, Matrix.ext fun j r => ht r j⟩

/- English proof (translation)
Introduce `l _ K bk τ hτ d d' S S' ρ ρ' T T' h h' f X hX`. Take `⟨V, hV⟩` from `h'.unit`. Establish `hU : (V⁻¹ : _ˣ).1 * T' = 1` using `hV ▸ V.inv_mul`. Establish `hT : T' * (V⁻¹ : _ˣ).1 = 1` using `hV ▸ V.mul_inv`. Take `⟨t, ht⟩` from `exists_basis hτ h`.

Take `⟨u, hu⟩` from `exists_inv hτ h' hU hT`. Establish `hf : (f.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW f` using `Matrix.ext fun i j => (inclWA l).commutes (f i j)`. Use `⟨S'.b + S.a, u * (f.map (algebraMap ℤ_[l] (Ainf l)) * t), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, Matrix.map_mul, ht, hu, hf, Matrix.mul_smul, ← hX, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hU, Matrix.one_mul, smul_smul, pow_add]`.
-/
theorem exists_pow_smul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l))
    (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' →
    ∀ (f : Matrix (Fin d') (Fin d) ℤ_[l]) (X : Matrix (Fin d') (Fin d) (WCb l)), T' * X = zW f * T →
    ∃ (M : ℕ) (x : Matrix (Fin d') (Fin d) (Ainf l)), x.map (inclW l) = inclW l τ ^ M • X := by
  intro l _ K bk τ hτ d d' S S' ρ ρ' T T' h h' f X hX
  obtain ⟨V, hV⟩ := h'.unit
  have hU : (V⁻¹ : _ˣ).1 * T' = 1 := hV ▸ V.inv_mul
  have hT : T' * (V⁻¹ : _ˣ).1 = 1 := hV ▸ V.mul_inv
  obtain ⟨t, ht⟩ := exists_basis hτ h
  obtain ⟨u, hu⟩ := exists_inv hτ h' hU hT
  have hf : (f.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW f :=
    Matrix.ext fun i j => (inclWA l).commutes (f i j)
  refine ⟨S'.b + S.a, u * (f.map (algebraMap ℤ_[l] (Ainf l)) * t), ?_⟩
  rw [Matrix.map_mul, Matrix.map_mul, ht, hu, hf, Matrix.mul_smul, ← hX, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_assoc, hU, Matrix.one_mul, smul_smul, pow_add]

end GlobalTheory.BSP.PoleBound
