import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LowestRankThree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasModelOfAntitone

open Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta

noncomputable section

namespace GlobalTheory.Published.DSExistsRecordModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `⟨Finset.univ.image fun a : Fin n => ((((n : ℚ) - 1) / 2 - ((a : ℕ) : ℚ)), ε a), DSExistsModel.lamDet n 0, ε, ⟨(DSExistsModel.lamDet_hc n 0).1, fun a => ((n : ℚ) - 1) / 2 - ((a : ℕ) : ℚ), fun a => ?_, rfl⟩, DSExistsModel.lamDet_hc n 0, rfl, rfl⟩` and prove the remaining obligations. Simplify using `[DSExistsModel.lamDet, Formalism.QuantumDeterminants.rhoStd]`.
-/
theorem goodPar_of_signs (n : ℕ) (ε : Fin n → Bool) :
    ∃ S : SPar, GoodPar n (Finset.univ.filter fun a => ε a = true).card
      (Finset.univ.filter fun a => ε a = false).card S := by
  refine ⟨Finset.univ.image fun a : Fin n => ((((n : ℚ) - 1) / 2 - ((a : ℕ) : ℚ)), ε a), DSExistsModel.lamDet n 0, ε,
    ⟨(DSExistsModel.lamDet_hc n 0).1, fun a => ((n : ℚ) - 1) / 2 - ((a : ℕ) : ℚ), fun a => ?_, rfl⟩,
    DSExistsModel.lamDet_hc n 0, rfl, rfl⟩
  simp [DSExistsModel.lamDet, Formalism.QuantumDeterminants.rhoStd]

/- English proof (translation)
Break down `h with h | h` into its components or cases. Use `⟨false, funext fun a => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Simplify using `using h (Finset.mem_univ a)`. Use `⟨true, funext fun a => ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Simplify using `using h (Finset.mem_univ a)`.
-/
theorem const_of_card {n : ℕ} (ε : Fin n → Bool)
    (h : (Finset.univ.filter fun a => ε a = true).card = 0 ∨ (Finset.univ.filter fun a => ε a = false).card = 0) :
    ∃ b, ε = fun _ => b := by
  rcases h with h | h
  · refine ⟨false, funext fun a => ?_⟩
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    simpa using h (Finset.mem_univ a)
  · refine ⟨true, funext fun a => ?_⟩
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    simpa using h (Finset.mem_univ a)

/- English proof (translation)
Introduce `hV hS`. Use `choose lam ε hE hP hp hq using hS`. Establish `key : ∀ τ, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)), IsDS (ε τ) (lam τ) σ`. Introduce `τ`. Take `⟨b, hb⟩` from `const_of_card (ε τ) (by rw [hp, hq]; exact hd τ)`.

Rewrite using `[hb]`. Conclude with `GlobalTheory.CompactDS.exists_isDS_const _ b _ (hP τ)`. Use `choose H i1 i2 σ hσ using key`. Use `choose A hA hG using fun τ => exists_frame_of_hasSignature (hV (tauE D τ)) (ε τ) (hp τ) (hq τ)`. Conclude with `⟨@Formalism.IndefR.Mult.DSModel.mk D V S H i1 i2 σ lam ε A hE hσ hA hG⟩`.
-/
theorem dsExists_of_definite (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar)
    (hd : ∀ τ, (V.sig (tauE D τ)).1 = 0 ∨ (V.sig (tauE D τ)).2 = 0) : Formalism.IndefR.Mult.DSExists V S := by
  intro hV hS
  choose lam ε hE hP hp hq using hS
  have key : ∀ τ, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)), IsDS (ε τ) (lam τ) σ := by
    intro τ
    obtain ⟨b, hb⟩ := const_of_card (ε τ) (by rw [hp, hq]; exact hd τ)
    rw [hb]
    exact GlobalTheory.CompactDS.exists_isDS_const _ b _ (hP τ)
  choose H i1 i2 σ hσ using key
  choose A hA hG using fun τ => exists_frame_of_hasSignature (hV (tauE D τ)) (ε τ) (hp τ) (hq τ)
  exact ⟨@Formalism.IndefR.Mult.DSModel.mk D V S H i1 i2 σ lam ε A hE hσ hA hG⟩

/- English proof (translation)
Rewrite using `[discreteSeriesExists_iff]`. Use `⟨fun h n ε lam _ hl => h n ε lam hl, fun h n ε lam hl => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hc : ∃ a b, ε a ≠ ε b`. Conclude with `h n ε lam hc hl`. Use `push Not at hc`.

Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `DSExistsModel.holds_rank_le_one 0 (by norm_num) ε lam hl`. Establish `: ε = fun _ => ε ⟨0, hn⟩` using `funext fun a => hc _ _`. Rewrite using `[this]`. Conclude with `GlobalTheory.CompactDS.exists_isDS_const _ _ _ hl`.
-/
theorem iff_indefinite : DiscreteSeriesExists ↔
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), (∃ a b, ε a ≠ ε b) → Formalism.QuantumDeterminants.IsHCParam lam →
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ := by
  rw [discreteSeriesExists_iff]
  refine ⟨fun h n ε lam _ hl => h n ε lam hl, fun h n ε lam hl => ?_⟩
  by_cases hc : ∃ a b, ε a ≠ ε b
  · exact h n ε lam hc hl
  · push Not at hc
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact DSExistsModel.holds_rank_le_one 0 (by norm_num) ε lam hl
    · have : ε = fun _ => ε ⟨0, hn⟩ := funext fun a => hc _ _
      rw [this]
      exact GlobalTheory.CompactDS.exists_isDS_const _ _ _ hl

/- English proof (translation)
Assemble the required witnesses or components as `⟨(M.enum τ).1, DSExistsModel.integral_of_isDS (M.ε τ) (M.lam τ) (M.σ τ) (M.ds τ)⟩`.
-/
theorem isHCParam_of_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S)
    (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (M.lam τ) :=
  ⟨(M.enum τ).1, DSExistsModel.integral_of_isDS (M.ε τ) (M.lam τ) (M.σ τ) (M.ds τ)⟩

/- English proof (translation)
Introduce and unpack `⟨-, -, ⟨⟨h1, hm⟩, hn, -⟩, -, -, ⟨S, -, hK, -, ⟨v, hvS, hv, hw⟩, hc⟩, -⟩`. Establish `hL : Formalism.QuantumDeterminants.lowK (fun _ : Fin 2 => true) (fun _ => 1 / 2) = ![0, 1]`. Use function extensionality and compare the values at `a`. Rewrite using `[GlobalTheory.DefiniteCheck.lowK_const]`. Apply the tactic sequence `fin_cases a <;> simp <;> norm_num`.

Rewrite `hw`, `hc` using `[hL]`. Establish `hJ : Formalism.REAL.Jm (fun _ : Fin 2 => true) = 1` using `by simp [Formalism.REAL.Jm]`. Establish `hKU : ∀ g ∈ Formalism.REAL.Kset (fun _ : Fin 2 => true), g ∈ UJset (fun _ : Fin 2 => true)`. Introduce `g hg`. Use `(Matrix.mem_unitaryGroup_iff').1 hg.1` as an intermediate fact.

Use `show gᴴ * _ * g = _`. Rewrite using `[hJ, Matrix.mul_one]`. Conclude with `this`. Set `w : Matrix (Fin 2) (Fin 2) ℂ` to `!![0, 1; 1, 0]`. Establish `hwK : w ∈ Formalism.REAL.Kset (fun _ : Fin 2 => true)`.

Use `⟨?_, by rw [hJ]; simp⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `hne : σ w v ≠ 0`. Introduce `h0`.

Use `hn w (hKU w hwK) v` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `hv (norm_eq_zero.1 this.symm)`. Establish `hwt : IsWtOn (Formalism.REAL.Kset (fun _ : Fin 2 => true)) σ ![1, 0] (σ w v)`. Introduce `θ hθ`.

Establish `h2` using `hw ![θ 1, θ 0] (DSExistsModel.diag_mem _ _)`. Establish `e : Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * w = w * Matrix.diagonal (fun a => Complex.exp (((![θ 1, θ 0] : Fin 2 → ℝ) a : ℂ) * Complex.I))`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]`. Establish `a1` using `congrArg (fun T : H →L[ℂ] H => T v) (hm _ (hKU _ hθ) w (hKU w hwK))`. Establish `a2` using `congrArg (fun T : H →L[ℂ] H => T v) (hm w (hKU w hwK) _ (hKU _ (DSExistsModel.diag_mem _ ![θ 1, θ 0])))`.

Simplify using `only [ContinuousLinearMap.comp_apply] at a1 a2`. Rewrite using `[← a1, e, a2, h2, map_smul]`. Simplify using `[Fin.sum_univ_two]`. Take `⟨c, hc1, hc2⟩` from `hc _ _ (hK w hwK v hvS) hne hwt`. Establish `h10 : c 1 0 = 0`.

Assume the negation of the conclusion as `h; exact absurd (hc1 1 0 h).1 (by decide)`. Use `congrFun hc2 0` as an intermediate fact. Simplify using `[Fin.sum_univ_two, Formalism.REAL.root, h10] at this`. Establish `h0 : (0 : ℝ) ≤ c 0 1` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_isDS_singular {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin 2) (Fin 2) ℂ → (H →L[ℂ] H)) : ¬ IsDS (fun _ => true) (fun _ => 1 / 2) σ := by
  rintro ⟨-, -, ⟨⟨h1, hm⟩, hn, -⟩, -, -, ⟨S, -, hK, -, ⟨v, hvS, hv, hw⟩, hc⟩, -⟩
  have hL : Formalism.QuantumDeterminants.lowK (fun _ : Fin 2 => true) (fun _ => 1 / 2) = ![0, 1] := by
    funext a
    rw [GlobalTheory.DefiniteCheck.lowK_const]
    fin_cases a <;> simp <;> norm_num
  rw [hL] at hw hc
  have hJ : Formalism.REAL.Jm (fun _ : Fin 2 => true) = 1 := by simp [Formalism.REAL.Jm]
  have hKU : ∀ g ∈ Formalism.REAL.Kset (fun _ : Fin 2 => true), g ∈ UJset (fun _ : Fin 2 => true) := by
    intro g hg
    have := (Matrix.mem_unitaryGroup_iff').1 hg.1
    show gᴴ * _ * g = _
    rw [hJ, Matrix.mul_one]; exact this
  let w : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  have hwK : w ∈ Formalism.REAL.Kset (fun _ : Fin 2 => true) := by
    refine ⟨?_, by rw [hJ]; simp⟩
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j; fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two]
  have hne : σ w v ≠ 0 := by
    intro h0
    have := hn w (hKU w hwK) v
    rw [h0, norm_zero] at this
    exact hv (norm_eq_zero.1 this.symm)
  have hwt : IsWtOn (Formalism.REAL.Kset (fun _ : Fin 2 => true)) σ ![1, 0] (σ w v) := by
    intro θ hθ
    have h2 := hw ![θ 1, θ 0] (DSExistsModel.diag_mem _ _)
    have e : Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * w =
        w * Matrix.diagonal (fun a => Complex.exp (((![θ 1, θ 0] : Fin 2 → ℝ) a : ℂ) * Complex.I)) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
    have a1 := congrArg (fun T : H →L[ℂ] H => T v) (hm _ (hKU _ hθ) w (hKU w hwK))
    have a2 := congrArg (fun T : H →L[ℂ] H => T v) (hm w (hKU w hwK) _ (hKU _ (DSExistsModel.diag_mem _ ![θ 1, θ 0])))
    simp only [ContinuousLinearMap.comp_apply] at a1 a2
    rw [← a1, e, a2, h2, map_smul]
    simp [Fin.sum_univ_two]
  obtain ⟨c, hc1, hc2⟩ := hc _ _ (hK w hwK v hvS) hne hwt
  have h10 : c 1 0 = 0 := by
    by_contra h; exact absurd (hc1 1 0 h).1 (by decide)
  have := congrFun hc2 0
  simp [Fin.sum_univ_two, Formalism.REAL.root, h10] at this
  have h0 : (0 : ℝ) ≤ c 0 1 := Nat.cast_nonneg _
  linarith

end GlobalTheory.Published.DSExistsRecordModel
