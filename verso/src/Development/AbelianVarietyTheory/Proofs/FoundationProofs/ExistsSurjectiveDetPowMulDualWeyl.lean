import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.Branching

def lastNat {n : ℕ} (ν : Fin n → ℕ) : ℕ := if h : 0 < n then ν ⟨n - 1, by omega⟩ else 0

/- English proof (translation)
Establish `hn : 0 < n` using `Nat.lt_of_le_of_lt (Nat.zero_le _) a.2`. Establish `ha : a ≤ (⟨n - 1, by omega⟩ : Fin n)` using `Fin.le_def.2 (by have := a.2; simp only; omega)`. Establish `hl` using `lam.anti ha`. Rewrite `hl` using `[h, h]`. Simplify using `only [DomWeight.natW, DomWeight.detShift, lastNat, dif_pos hn, h]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem natW_add_lastNat {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (a : Fin n) : lam.natW a + lastNat ν = ν a := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.2
  have ha : a ≤ (⟨n - 1, by omega⟩ : Fin n) := Fin.le_def.2 (by have := a.2; simp only; omega)
  have hl := lam.anti ha
  rw [h, h] at hl
  simp only [DomWeight.natW, DomWeight.detShift, lastNat, dif_pos hn, h]
  omega

/- English proof (translation)
Introduce `a b hab` and use `by have := lam.anti hab rw [h, h] at this omega`.
-/
theorem antitone_of_weight_eq {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) : Antitone ν := fun a b hab => by
  have := lam.anti hab
  rw [h, h] at this
  omega

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `h1 : Matrix.GeneralLinearGroup.det g = 1` using `Units.ext (by simp)`. Simplify using `[detPow, h1, lastNat]`. Establish `hs : lam.detShift = (lastNat ν : ℤ) + c` using `by simp [DomWeight.detShift, lastNat, hn, h]`. Rewrite using `[hs, detPow, detPow, zpow_add, Units.val_mul, zpow_natCast, mul_comm]`.

Simplify using the standard rewrite rules.
-/
theorem detPow_detShift_eq {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (g : GL (Fin n) ℂ) :
    detPow ℂ n g lam.detShift = detPow ℂ n g c * (g : Matrix (Fin n) (Fin n) ℂ).det ^ lastNat ν := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
    simp [detPow, h1, lastNat]
  · have hs : lam.detShift = (lastNat ν : ℤ) + c := by simp [DomWeight.detShift, lastNat, hn, h]
    rw [hs, detPow, detPow, zpow_add, Units.val_mul, zpow_natCast, mul_comm]
    simp

/- English proof (translation)
Establish `hm` using `(genericDet_pow_mul n (lastNat ν) lam.natW).1 v v.2`. Establish `e : (fun i => lam.natW i + lastNat ν) = ν` using `funext (natW_add_lastNat ν c lam h)`. Rewrite `hm` using `[e]`. Then use the resulting hypothesis.
-/
theorem detPowMul_mem {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (v : nablaSq ℂ n lam) :
    Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * (v : MvPolynomial (Fin n × Fin n) ℂ) ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν := by
  have hm := (genericDet_pow_mul n (lastNat ν) lam.natW).1 v v.2
  have e : (fun i => lam.natW i + lastNat ν) = ν := funext (natW_add_lastNat ν c lam h)
  rwa [e] at hm

def detPowMul {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c) :
    nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν :=
  LinearMap.codRestrict _ ((LinearMap.mulLeft ℂ (Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν)).comp
    (nablaSq ℂ n lam).subtype) (detPowMul_mem ν c lam h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem detPowMul_coe {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c)
    (v : nablaSq ℂ n lam) : (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) =
      Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * (v : MvPolynomial (Fin n × Fin n) ℂ) := rfl

/- English proof (translation)
Rewrite using `[detPowMul_coe, detPowMul_coe, sqRep_coe, sqAct, (genericDet_pow_mul n (lastNat ν) (fun _ => 0)).2.1, Matrix.det_transpose, detPow_detShift_eq ν c lam h, mul_smul_comm, smul_smul]`.
-/
theorem detPowMul_sqRep {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c)
    (g : GL (Fin n) ℂ) (v : nablaSq ℂ n lam) :
    (detPowMul ν c lam h (GlobalTheory.Branching.sqRep ℂ n lam g v) : MvPolynomial (Fin n × Fin n) ℂ) =
      detPow ℂ n g c • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose
        (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) := by
  rw [detPowMul_coe, detPowMul_coe, sqRep_coe, sqAct, (genericDet_pow_mul n (lastNat ν) (fun _ => 0)).2.1,
    Matrix.det_transpose, detPow_detShift_eq ν c lam h, mul_smul_comm, smul_smul]

end GlobalTheory.Branching

namespace GlobalTheory.Branching

/- English proof (translation)
Introduce `n ν c lam h`. Use `⟨detPowMul ν c lam h, ?_, detPowMul_sqRep ν c lam h⟩` and prove the remaining obligations. Set `M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ)` to `(LinearMap.range (detPowMul ν c lam h)).map (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype`. Establish `hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M`. Introduce and unpack `u hu _ ⟨_, ⟨v, rfl⟩, rfl⟩`.

Set `t : Matrix.unitaryGroup (Fin n) ℂ` to `Matrix.UnitaryGroup.transpose ⟨u, hu⟩`. Establish `h1 : (detPowMul ν c lam h (sqRep ℂ n lam (unitaryIncl n t) v) : MvPolynomial (Fin n × Fin n) ℂ) ∈ M` using `⟨_, ⟨_, rfl⟩, rfl⟩`. Rewrite `h1` using `[detPowMul_sqRep]`. Establish `e : ((unitaryIncl n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose = u`. Simplify using `[t]`.

Rewrite `h1` using `[e]`. Conclude with `(M.smul_mem_iff (Units.ne_zero _)).1 h1`. Establish `hcl` using `rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)`. Establish `hν` using `antitone_of_weight_eq ν c lam h`. Establish `hle : M ≤ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν` using `Submodule.map_subtype_le _ _`.

Establish `hne : M ≠ ⊥`. Introduce `e0`. Establish `ha : Antitone lam.natW` using `fun i j hij => by`. Use `lam.anti hij` as an intermediate fact. Simplify using `only [DomWeight.natW]`.

Use linear arithmetic over natural numbers and integers. Set `v : nablaSq ℂ n lam` to `⟨_, Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ ha⟩`. Establish `hm : (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) ∈ M` using `⟨_, ⟨v, rfl⟩, rfl⟩`. Establish `e : (fun i => lam.natW i + lastNat ν) = ν` using `funext (natW_add_lastNat ν c lam h)`. Rewrite `hm` using `[e0, Submodule.mem_bot, detPowMul_coe]`.

Express the relevant statement in the definitionally equal form `Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * Formalism.GradedWeylDivisibility.hw ℂ le_rfl lam.natW = 0 at hm`. Rewrite `hm` using `[genericDet_pow_mul_hw, e]`. Conclude with `Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl ν hm`. Establish `hall` using `dualWeyl_le_of_rowDivClosed le_rfl ν hν M hle hcl hne`. Introduce `y`.

Take `⟨_, ⟨x, rfl⟩, hx⟩` from `hall y.2`. Conclude with `⟨x, Subtype.ext hx⟩`.
-/
theorem exists_surjective_detPowMul_dualWeyl : ∀ (n : ℕ) (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n), (∀ a, lam.w a = (ν a : ℤ) + c) → ∃ e : nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, Function.Surjective e ∧ ∀ (g : GL (Fin n) ℂ) v, (e (GlobalTheory.Branching.sqRep ℂ n lam g v) : MvPolynomial (Fin n × Fin n) ℂ) = detPow ℂ n g c • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose (e v : MvPolynomial (Fin n × Fin n) ℂ) := by
  intro n ν c lam h
  refine ⟨detPowMul ν c lam h, ?_, detPowMul_sqRep ν c lam h⟩
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    (LinearMap.range (detPowMul ν c lam h)).map (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨_, ⟨v, rfl⟩, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    have h1 : (detPowMul ν c lam h (sqRep ℂ n lam (unitaryIncl n t) v) : MvPolynomial (Fin n × Fin n) ℂ) ∈ M :=
      ⟨_, ⟨_, rfl⟩, rfl⟩
    rw [detPowMul_sqRep] at h1
    have e : ((unitaryIncl n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose = u := by
      simp [t]
    rw [e] at h1
    exact (M.smul_mem_iff (Units.ne_zero _)).1 h1
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hν := antitone_of_weight_eq ν c lam h
  have hle : M ≤ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν := Submodule.map_subtype_le _ _
  have hne : M ≠ ⊥ := by
    intro e0
    have ha : Antitone lam.natW := fun i j hij => by
      have := lam.anti hij
      simp only [DomWeight.natW]
      omega
    let v : nablaSq ℂ n lam := ⟨_, Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ ha⟩
    have hm : (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) ∈ M := ⟨_, ⟨v, rfl⟩, rfl⟩
    have e : (fun i => lam.natW i + lastNat ν) = ν := funext (natW_add_lastNat ν c lam h)
    rw [e0, Submodule.mem_bot, detPowMul_coe] at hm
    change Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * Formalism.GradedWeylDivisibility.hw ℂ le_rfl lam.natW = 0 at hm
    rw [genericDet_pow_mul_hw, e] at hm
    exact Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl ν hm
  have hall := dualWeyl_le_of_rowDivClosed le_rfl ν hν M hle hcl hne
  intro y
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hall y.2
  exact ⟨x, Subtype.ext hx⟩

end GlobalTheory.Branching
