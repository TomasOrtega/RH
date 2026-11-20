import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.Hk

/- English proof (translation)
Introduce `N l q σ γ hq hnd hσ hγ hc`. Take `⟨u, hu⟩` from `hc`. Establish `hcop : Nat.Coprime q (N * l)` using `(Nat.Prime.coprime_iff_not_dvd hq).2 hnd`. Establish `hcN : IsCoprime (N : ℤ) (q : ℤ)` using `Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_mul_right_right hcop).symm`. Establish `hcl : IsCoprime (l : ℤ) (q : ℤ)` using `Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_mul_left_right hcop).symm`.

Take `⟨h1, h0⟩` from `Subgroup.mem_inf.1 hγ`. Take `⟨ha, hd, hcN'⟩` from `(Gamma1_mem N γ).1 h1`. Establish `hcl'` using `Gamma0_mem.1 h0`. Establish `hu' : (γ 1 0 : ℤ) = q * u` using `hu`. Establish `huN : (u : ZMod N) = 0`.

Rewrite `hcN'`, the goal using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`. Rewrite `hcN'` using `[hu']`. Conclude with `hcN.dvd_of_dvd_mul_left hcN'`. Establish `hul : (u : ZMod l) = 0`. Rewrite `hcl'`, the goal using `[ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Rewrite `hcl'` using `[hu']`. Conclude with `hcl.dvd_of_dvd_mul_left hcl'`. Establish `hs : ((N * l : ℕ) : ℤ) ∣ σ 1 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ.1`. Establish `hsN : ((σ 1 0 : ℤ) : ZMod N) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_right _ _) hs)`. Establish `hsl : ((σ 1 0 : ℤ) : ZMod l) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_left _ _) hs)`.

Establish `dσ : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1`. Use `σ.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `dγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1`. Use `γ.det_coe` as an intermediate fact.

Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `dσN : ((σ 0 0 : ℤ) : ZMod N) * ((σ 1 1 : ℤ) : ZMod N) = 1`. Use `congrArg (Int.cast : ℤ → ZMod N) dσ` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite `this` using `[hsN]`.

Simplify using `using this`. Use `⟨⟨!![(σ 0 0 * γ 0 0 + σ 0 1 * u) * σ 1 1 - (σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1) * σ 1 0, -(σ 0 0 * γ 0 0 + σ 0 1 * u) * σ 0 1 + (σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1) * σ 0 0; (σ 1 0 * γ 0 0 + σ 1 1 * u) * σ 1 1 - (σ 1 0 * (q * γ 0 1) + σ 1 1 * γ 1 1) * σ 1 0, -(σ 1 0 * γ 0 0 + σ …` and prove the remaining obligations. Rewrite using `[Matrix.det_fin_two_of]`. Rewrite `dγ` using `[hu']`. Take the linear combination `(σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 + 1) * (γ 0 0 * γ 1 1 - γ 0 1 * (q * u)) * dσ + dγ`.

Use `Subgroup.mem_inf.2 ⟨(Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩` and prove the remaining obligations. Simplify using `[hsN, huN, ha, hd, dσN]`. Simplify using `[hsN, huN, ha, hd, mul_comm, dσN]`. Simplify using `[hsN, huN]`. Simplify using `[hsl, hul]`.

Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [mat, dg, Matrix.mul_apply, Fin.sum_univ_two, hu']`. Take the linear combination `(-(q : ℤ) * (σ 0 0 * γ 0 0 + σ 0 1 * u)) * dσ`. Take the linear combination `(-(σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1)) * dσ`. Take the linear combination `(-(q : ℤ) * (σ 1 0 * γ 0 0 + σ 1 1 * u)) * dσ`. Take the linear combination `(-(σ 1 0 * (q * γ 0 1) + σ 1 1 * γ 1 1)) * dσ`.
-/
theorem dia_diag_mul_of_dvd_lowerLeft : ∀ (N l q : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 1 0 → ∃ γ' ∈ GlobalTheory.Hk.lev N l, mat σ * dg q 1 * mat γ = mat γ' * (mat σ * dg q 1) := by
  intro N l q σ γ hq hnd hσ hγ hc
  obtain ⟨u, hu⟩ := hc
  have hcop : Nat.Coprime q (N * l) := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  have hcN : IsCoprime (N : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_mul_right_right hcop).symm
  have hcl : IsCoprime (l : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_mul_left_right hcop).symm
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨ha, hd, hcN'⟩ := (Gamma1_mem N γ).1 h1
  have hcl' := Gamma0_mem.1 h0
  have hu' : (γ 1 0 : ℤ) = q * u := hu
  have huN : (u : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcN' ⊢
    rw [hu'] at hcN'
    exact hcN.dvd_of_dvd_mul_left hcN'
  have hul : (u : ZMod l) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcl' ⊢
    rw [hu'] at hcl'
    exact hcl.dvd_of_dvd_mul_left hcl'
  have hs : ((N * l : ℕ) : ℤ) ∣ σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ.1
  have hsN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_right _ _) hs)
  have hsl : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (by push_cast; exact dvd_mul_left _ _) hs)
  have dσ : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.det_coe; rwa [Matrix.det_fin_two] at this
  have dγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have dσN : ((σ 0 0 : ℤ) : ZMod N) * ((σ 1 1 : ℤ) : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) dσ
    push_cast at this
    rw [hsN] at this
    simpa using this
  refine ⟨⟨!![(σ 0 0 * γ 0 0 + σ 0 1 * u) * σ 1 1 - (σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1) * σ 1 0,
      -(σ 0 0 * γ 0 0 + σ 0 1 * u) * σ 0 1 + (σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1) * σ 0 0;
      (σ 1 0 * γ 0 0 + σ 1 1 * u) * σ 1 1 - (σ 1 0 * (q * γ 0 1) + σ 1 1 * γ 1 1) * σ 1 0,
      -(σ 1 0 * γ 0 0 + σ 1 1 * u) * σ 0 1 + (σ 1 0 * (q * γ 0 1) + σ 1 1 * γ 1 1) * σ 0 0], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    rw [hu'] at dγ
    linear_combination (σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 + 1) * (γ 0 0 * γ 1 1 - γ 0 1 * (q * u)) * dσ + dγ
  · refine Subgroup.mem_inf.2 ⟨(Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩
    · simp [hsN, huN, ha, hd, dσN]
    · simp [hsN, huN, ha, hd, mul_comm, dσN]
    · simp [hsN, huN]
    · simp [hsl, hul]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mat, dg, Matrix.mul_apply, Fin.sum_univ_two, hu']
    · linear_combination (-(q : ℤ) * (σ 0 0 * γ 0 0 + σ 0 1 * u)) * dσ
    · linear_combination (-(σ 0 0 * (q * γ 0 1) + σ 0 1 * γ 1 1)) * dσ
    · linear_combination (-(q : ℤ) * (σ 1 0 * γ 0 0 + σ 1 1 * u)) * dσ
    · linear_combination (-(σ 1 0 * (q * γ 0 1) + σ 1 1 * γ 1 1)) * dσ

end GlobalTheory.Hk
