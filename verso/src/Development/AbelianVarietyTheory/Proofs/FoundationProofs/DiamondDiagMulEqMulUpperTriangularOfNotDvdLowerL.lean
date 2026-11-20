import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HkInvFin

/- English proof (translation)
Introduce `N l q σ γ hq _ hσ hγ hc`. Use `haveI := Fact.mk hq`. Establish `hdetγ : mat γ 0 0 * mat γ 1 1 - mat γ 0 1 * mat γ 1 0 = 1`. Use `γ.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis.

Establish `hdetσ : mat σ 0 0 * mat σ 1 1 - mat σ 0 1 * mat σ 1 0 = 1`. Use `σ.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `hcq : ((mat γ 1 0 : ℤ) : ZMod q) ≠ 0`. Rewrite using `[Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]` and apply the resulting hypothesis.

Establish `hdiv : (q : ℤ) ∣ mat γ 1 1 - mat γ 1 0 * (((mat γ 1 1 : ℤ) : ZMod q) * ((mat γ 1 0 : ℤ) : ZMod q)⁻¹).val`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val, mul_comm ((mat γ 1 1 : ℤ) : ZMod q), ← mul_assoc, mul_inv_cancel₀ hcq, one_mul, sub_self]`. Take `⟨x, hx⟩` from `hdiv`.

Use `set j' : ℕ := (((mat γ 1 1 : ℤ) : ZMod q) * ((mat γ 1 0 : ℤ) : ZMod q)⁻¹).val with hj'`. Establish `hjlt : j' < q` using `ZMod.val_lt _`. Set `δ : Matrix (Fin 2) (Fin 2) ℤ` to `!![q * mat γ 0 0, mat γ 0 1 - mat γ 0 0 * j'; mat γ 1 0, x]`. Establish `hdetδ : δ.det = 1`. Rewrite using `[Matrix.det_fin_two_of]`.

Take the linear combination `hdetγ - mat γ 0 0 * hx`. Set `γ' : SL(2, ℤ)` to `⟨mat σ * δ, by rw [Matrix.det_mul, hdetδ, σ.2, one_mul]⟩`. Establish `hlev` using `hγ`. Rewrite `hlev` using `[GlobalTheory.Hk.lev, Subgroup.mem_inf, Gamma1_mem, Gamma0_mem]`. Take `⟨⟨ha, hd, hcN⟩, hcl⟩` from `hlev`.

Take `⟨hs10, hs11⟩` from `hσ`. Establish `hs10' : ((N * l : ℕ) : ℤ) ∣ mat σ 1 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hs10`. Establish `hsN : ((mat σ 1 0 : ℤ) : ZMod N) = 0`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Conclude with `dvd_trans (by push_cast; exact dvd_mul_right _ _) hs10'`.

Establish `hsl : ((mat σ 1 0 : ℤ) : ZMod l) = 0`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Conclude with `dvd_trans (by push_cast; exact dvd_mul_left _ _) hs10'`. Use `⟨j', hjlt, γ', ?_, ?_⟩` and prove the remaining obligations. Establish `e00 : γ'.1 0 0 = mat σ 0 0 * (q * mat γ 0 0) + mat σ 0 1 * mat γ 1 0`.

Simplify using `[γ', δ, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e10 : γ'.1 1 0 = mat σ 1 0 * (q * mat γ 0 0) + mat σ 1 1 * mat γ 1 0`. Simplify using `[γ', δ, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e11 : γ'.1 1 1 = mat σ 1 0 * (mat γ 0 1 - mat γ 0 0 * j') + mat σ 1 1 * x`. Simplify using `[γ', δ, Matrix.mul_apply, Fin.sum_univ_two]`.

Establish `hxN` using `congrArg (Int.cast : ℤ → ZMod N) hx`. Establish `hdN` using `congrArg (Int.cast : ℤ → ZMod N) hdetσ`. Establish `ha' : ((mat γ 0 0 : ℤ) : ZMod N) = 1` using `ha`. Establish `hd' : ((mat γ 1 1 : ℤ) : ZMod N) = 1` using `hd`. Establish `hcN' : ((mat γ 1 0 : ℤ) : ZMod N) = 0` using `hcN`.

Establish `hcl' : ((mat γ 1 0 : ℤ) : ZMod l) = 0` using `hcl`. Establish `h11 : ((mat σ 1 1 : ℤ) : ZMod N) = (q : ZMod N)`. Establish `: ((mat σ 1 1 : ℤ) : ZMod N) = ((q : ℤ) : ZMod N)` using `hs11`. Simplify using `using this`. Move the coercions through the operations in `at hxN hdN`.

Rewrite `hxN` using `[hd', hcN']`. Rewrite `hdN` using `[hsN, h11]`. Rewrite using `[GlobalTheory.Hk.lev, Subgroup.mem_inf, Gamma1_mem, Gamma0_mem]`. Use `⟨⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show ((γ'.1 0 0 : ℤ) : ZMod N) = 1`.

Rewrite using `[e00]`. Use `push_cast`. Rewrite using `[ha', hcN']`. Take the linear combination `hdN`. Use `show ((γ'.1 1 1 : ℤ) : ZMod N) = 1`.

Rewrite using `[e11]`. Use `push_cast`. Rewrite using `[hsN, h11]`. Take the linear combination `-hxN`. Use `show ((γ'.1 1 0 : ℤ) : ZMod N) = 0`.

Rewrite using `[e10]`. Use `push_cast`. Rewrite using `[hsN, hcN']`. Expand and normalize the polynomial expressions, which then agree. Use `show ((γ'.1 1 0 : ℤ) : ZMod l) = 0`.

Rewrite using `[e10]`. Use `push_cast`. Rewrite using `[hsl, hcl']`. Expand and normalize the polynomial expressions, which then agree. Use `show mat σ * dg q 1 * mat γ = (mat σ * δ) * _`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc]`. Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dg, δ, Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination hx | ring`.
-/
theorem sigma_dg_mul_eq : ∀ (N l q : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ →
    γ ∈ GlobalTheory.Hk.lev N l → ¬ (q : ℤ) ∣ mat γ 1 0 → ∃ j' < q, ∃ γ' ∈ GlobalTheory.Hk.lev N l,
      mat σ * dg q 1 * mat γ = mat γ' * !![(1 : ℤ), (j' : ℤ); 0, (q : ℤ)] := by
  intro N l q σ γ hq _ hσ hγ hc
  haveI := Fact.mk hq
  have hdetγ : mat γ 0 0 * mat γ 1 1 - mat γ 0 1 * mat γ 1 0 = 1 := by
    have := γ.2; rwa [Matrix.det_fin_two] at this
  have hdetσ : mat σ 0 0 * mat σ 1 1 - mat σ 0 1 * mat σ 1 0 = 1 := by
    have := σ.2; rwa [Matrix.det_fin_two] at this
  have hcq : ((mat γ 1 0 : ℤ) : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hdiv : (q : ℤ) ∣ mat γ 1 1 - mat γ 1 0 *
      (((mat γ 1 1 : ℤ) : ZMod q) * ((mat γ 1 0 : ℤ) : ZMod q)⁻¹).val := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_comm ((mat γ 1 1 : ℤ) : ZMod q), ← mul_assoc,
      mul_inv_cancel₀ hcq, one_mul, sub_self]
  obtain ⟨x, hx⟩ := hdiv
  set j' : ℕ := (((mat γ 1 1 : ℤ) : ZMod q) * ((mat γ 1 0 : ℤ) : ZMod q)⁻¹).val with hj'
  have hjlt : j' < q := ZMod.val_lt _
  let δ : Matrix (Fin 2) (Fin 2) ℤ := !![q * mat γ 0 0, mat γ 0 1 - mat γ 0 0 * j'; mat γ 1 0, x]
  have hdetδ : δ.det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdetγ - mat γ 0 0 * hx
  let γ' : SL(2, ℤ) := ⟨mat σ * δ, by rw [Matrix.det_mul, hdetδ, σ.2, one_mul]⟩
  have hlev := hγ
  rw [GlobalTheory.Hk.lev, Subgroup.mem_inf, Gamma1_mem, Gamma0_mem] at hlev
  obtain ⟨⟨ha, hd, hcN⟩, hcl⟩ := hlev
  obtain ⟨hs10, hs11⟩ := hσ
  have hs10' : ((N * l : ℕ) : ℤ) ∣ mat σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hs10
  have hsN : ((mat σ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (by push_cast; exact dvd_mul_right _ _) hs10'
  have hsl : ((mat σ 1 0 : ℤ) : ZMod l) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (by push_cast; exact dvd_mul_left _ _) hs10'
  refine ⟨j', hjlt, γ', ?_, ?_⟩
  · have e00 : γ'.1 0 0 = mat σ 0 0 * (q * mat γ 0 0) + mat σ 0 1 * mat γ 1 0 := by
      simp [γ', δ, Matrix.mul_apply, Fin.sum_univ_two]
    have e10 : γ'.1 1 0 = mat σ 1 0 * (q * mat γ 0 0) + mat σ 1 1 * mat γ 1 0 := by
      simp [γ', δ, Matrix.mul_apply, Fin.sum_univ_two]
    have e11 : γ'.1 1 1 = mat σ 1 0 * (mat γ 0 1 - mat γ 0 0 * j') + mat σ 1 1 * x := by
      simp [γ', δ, Matrix.mul_apply, Fin.sum_univ_two]
    have hxN := congrArg (Int.cast : ℤ → ZMod N) hx
    have hdN := congrArg (Int.cast : ℤ → ZMod N) hdetσ
    have ha' : ((mat γ 0 0 : ℤ) : ZMod N) = 1 := ha
    have hd' : ((mat γ 1 1 : ℤ) : ZMod N) = 1 := hd
    have hcN' : ((mat γ 1 0 : ℤ) : ZMod N) = 0 := hcN
    have hcl' : ((mat γ 1 0 : ℤ) : ZMod l) = 0 := hcl
    have h11 : ((mat σ 1 1 : ℤ) : ZMod N) = (q : ZMod N) := by
      have : ((mat σ 1 1 : ℤ) : ZMod N) = ((q : ℤ) : ZMod N) := hs11
      simpa using this
    push_cast at hxN hdN
    rw [hd', hcN'] at hxN
    rw [hsN, h11] at hdN
    rw [GlobalTheory.Hk.lev, Subgroup.mem_inf, Gamma1_mem, Gamma0_mem]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show ((γ'.1 0 0 : ℤ) : ZMod N) = 1
      rw [e00]; push_cast; rw [ha', hcN']; linear_combination hdN
    · show ((γ'.1 1 1 : ℤ) : ZMod N) = 1
      rw [e11]; push_cast; rw [hsN, h11]; linear_combination -hxN
    · show ((γ'.1 1 0 : ℤ) : ZMod N) = 0
      rw [e10]; push_cast; rw [hsN, hcN']; ring
    · show ((γ'.1 1 0 : ℤ) : ZMod l) = 0
      rw [e10]; push_cast; rw [hsl, hcl']; ring
  · show mat σ * dg q 1 * mat γ = (mat σ * δ) * _
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg, δ, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hx | ring

end GlobalTheory.HkInvFin
