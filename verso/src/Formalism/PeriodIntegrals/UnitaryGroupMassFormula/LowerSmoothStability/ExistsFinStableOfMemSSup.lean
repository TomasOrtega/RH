import Mathlib
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.LowCyc
import Formalism.PeriodIntegrals.KFinSmooth

open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.LowSmooth

open PI.UpqRep

section Directed

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type*}

def FinStable (G : Set ι) (ρ : ι → H →L[ℂ] H) : Set (Submodule ℂ H) :=
  {S | FiniteDimensional ℂ S ∧ ∀ g ∈ G, ∀ x ∈ S, ρ g x ∈ S}

/- English proof (translation)
Use `⟨inferInstance, fun g _ x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hx, map_zero]`.
-/
theorem finStable_bot (G : Set ι) (ρ : ι → H →L[ℂ] H) : (⊥ : Submodule ℂ H) ∈ FinStable G ρ := by
  refine ⟨inferInstance, fun g _ x hx => ?_⟩
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]

/- English proof (translation)
Introduce `S hS T hT`. Use `⟨S ⊔ T, ⟨?_, ?_⟩, le_sup_left, le_sup_right⟩` and prove the remaining obligations. Use `haveI := hS.1 haveI := hT.1 infer_instance`. Introduce `g hg x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hS.2 g hg y hy) (hT.2 g hg z hz)`.
-/
theorem finStable_directed (G : Set ι) (ρ : ι → H →L[ℂ] H) :
    DirectedOn (· ≤ ·) (FinStable G ρ) := by
  intro S hS T hT
  refine ⟨S ⊔ T, ⟨?_, ?_⟩, le_sup_left, le_sup_right⟩
  · haveI := hS.1
    haveI := hT.1
    infer_instance
  · intro g hg x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (hS.2 g hg y hy) (hT.2 g hg z hz)

/- English proof (translation)
Establish `hx' : x ∈ sSup (FinStable G ρ)` using `sSup_le_sSup hF hx`. Conclude with `(Submodule.mem_sSup_of_directed ⟨⊥, finStable_bot G ρ⟩ (finStable_directed G ρ)).mp hx'`.
-/
theorem exists_finStable_of_mem_sSup (G : Set ι) (ρ : ι → H →L[ℂ] H) {F : Set (Submodule ℂ H)}
    (hF : F ⊆ FinStable G ρ) {x : H} (hx : x ∈ sSup F) : ∃ S ∈ FinStable G ρ, x ∈ S := by
  have hx' : x ∈ sSup (FinStable G ρ) := sSup_le_sSup hF hx
  exact (Submodule.mem_sSup_of_directed ⟨⊥, finStable_bot G ρ⟩ (finStable_directed G ρ)).mp hx'

end Directed

section Transport

variable {k r : ℕ}

/- English proof (translation)
Take `⟨⟨_, hJ⟩, hPu⟩` from `hP`. Take `⟨hgH, hgu⟩` from `hg`. Establish `hPs : P * Pᴴ = 1`. Use `Matrix.mem_unitaryGroup_iff.mp hPu` as an intermediate fact. Rewrite `this` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis.

Establish `hsP : Pᴴ * P = 1`. Use `Matrix.mem_unitaryGroup_iff'.mp hPu` as an intermediate fact. Rewrite `this` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `hgs : g * gᴴ = 1`. Use `Matrix.mem_unitaryGroup_iff.mp hgu` as an intermediate fact.

Rewrite `this` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `hinv : P⁻¹ = Pᴴ` using `Matrix.inv_eq_left_inv hsP`. Establish `hgH' : gᴴ * Hpk k r * g = Hpk k r` using `hgH`. Establish `hcomm : g * Hpk k r = Hpk k r * g`. Combine the equalities or inequalities in the displayed calculation.

Establish `hJm : Jm ε = P * Hpk k r * Pᴴ`. Rewrite using `[← hJ]`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[hPs, Matrix.one_mul, Matrix.mul_assoc, hPs, Matrix.mul_one]`. Rewrite using `[hinv]`.

Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hPs' : Pᴴ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]`. Conclude with `hsP`. Conclude with `Submonoid.mul_mem _ (Submonoid.mul_mem _ hPu hgu) hPs'`.

Rewrite using `[hJm]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = P * (g * Hpk k r) * Pᴴ := by`. Rewrite using `[hsP, Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = P * (Hpk k r * g) * Pᴴ := by rw [hcomm]`. Use `_ = P * Hpk k r * (Pᴴ * P) * g * Pᴴ := by`. Rewrite using `[hsP, Matrix.mul_one]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = P * Hpk k r * Pᴴ * (P * g * Pᴴ) := by simp only [Matrix.mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_mem_Kset {ε : Fin (2 * r + k + 1) → Bool} {P g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : IsCayleyU k r ε P)
    (hg : g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)) :
    P * g * P⁻¹ ∈ Kset ε ∧ P⁻¹ * (P * g * P⁻¹) * P = g := by
  obtain ⟨⟨_, hJ⟩, hPu⟩ := hP
  obtain ⟨hgH, hgu⟩ := hg
  have hPs : P * Pᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hPu
    rwa [Matrix.star_eq_conjTranspose] at this
  have hsP : Pᴴ * P = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hPu
    rwa [Matrix.star_eq_conjTranspose] at this
  have hgs : g * gᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hgu
    rwa [Matrix.star_eq_conjTranspose] at this
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hsP
  have hgH' : gᴴ * Hpk k r * g = Hpk k r := hgH

  have hcomm : g * Hpk k r = Hpk k r * g := by
    calc g * Hpk k r = g * (gᴴ * Hpk k r * g) := by rw [hgH']
      _ = (g * gᴴ) * Hpk k r * g := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * g := by rw [hgs, Matrix.one_mul]
  have hJm : Jm ε = P * Hpk k r * Pᴴ := by
    rw [← hJ]
    simp only [← Matrix.mul_assoc]
    rw [hPs, Matrix.one_mul, Matrix.mul_assoc, hPs, Matrix.mul_one]
  rw [hinv]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hPs' : Pᴴ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      exact hsP
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hPu hgu) hPs'
  · rw [hJm]
    calc P * g * Pᴴ * (P * Hpk k r * Pᴴ) = P * g * (Pᴴ * P) * Hpk k r * Pᴴ := by
          simp only [Matrix.mul_assoc]
      _ = P * (g * Hpk k r) * Pᴴ := by
          rw [hsP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = P * (Hpk k r * g) * Pᴴ := by rw [hcomm]
      _ = P * Hpk k r * (Pᴴ * P) * g * Pᴴ := by
          rw [hsP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = P * Hpk k r * Pᴴ * (P * g * Pᴴ) := by simp only [Matrix.mul_assoc]
  · calc Pᴴ * (P * g * Pᴴ) * P = (Pᴴ * P) * g * (Pᴴ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hsP, Matrix.one_mul, Matrix.mul_one]

end Transport

/- English proof (translation)
Take `⟨P, hP, -, hw⟩` from `hlow`. Take `⟨S, ⟨hfin, hst⟩, hwS⟩` from `exists_finStable_of_mem_sSup (Kset ε) (fun h => σ (P⁻¹ * h * P)) (F := {S | IsKTypeOf ε (fun h => σ (P⁻¹ * h * P)) (lowK ε lam) S}) (fun S hS => ⟨hS.1, hS.2.1⟩) hw`. Use `⟨S, hfin, hwS, fun g hg x hx => ?_⟩` and prove the remaining obligations. Take `⟨hK, hback⟩` from `conj_mem_Kset hP hg`. Use `hst _ hK x hx` as an intermediate fact.

Use `beta_reduce at this`. Rewrite `this` using `[hback]`. Then use the resulting hypothesis.
-/
theorem isKFinHpk_of_lowUnit {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {w : H}
    (hlow : IsLowUnitH k r ε lam σ w) : IsKFinHpk (k := k) (r := r) σ w := by
  obtain ⟨P, hP, -, hw⟩ := hlow
  obtain ⟨S, ⟨hfin, hst⟩, hwS⟩ := exists_finStable_of_mem_sSup (Kset ε) (fun h => σ (P⁻¹ * h * P))
    (F := {S | IsKTypeOf ε (fun h => σ (P⁻¹ * h * P)) (lowK ε lam) S})
    (fun S hS => ⟨hS.1, hS.2.1⟩) hw
  refine ⟨S, hfin, hwS, fun g hg x hx => ?_⟩
  obtain ⟨hK, hback⟩ := conj_mem_Kset hP hg
  have := hst _ hK x hx
  beta_reduce at this
  rwa [hback] at this

/- English proof (translation)
Introduce `k r ε lam H _ _ _ σ w hHC hDS hlow`. Conclude with `hK k r ε lam H σ hHC hDS w (isKFinHpk_of_lowUnit hlow)`.
-/
theorem lowSmooth_of_kFinSmooth (hK : PI.KFinSmooth) : PI.LowSmooth := by
  intro k r ε lam H _ _ _ σ w hHC hDS hlow
  exact hK k r ε lam H σ hHC hDS w (isKFinHpk_of_lowUnit hlow)

end PI.UnitaryGroupMassFormula.LowSmooth
