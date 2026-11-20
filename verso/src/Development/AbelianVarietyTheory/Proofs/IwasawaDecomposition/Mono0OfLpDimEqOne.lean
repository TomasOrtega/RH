import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne.WD

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} [IsAlgClosure E Ω]
variable {h : IsPlaceOver A w}

variable (h) in

/- English proof (translation)
Simplify using `[lpZero]`.
-/
theorem lpDim_zero : lpDim (lpZero h) = 0 := by simp [lpZero]

/- English proof (translation)
Proceed by induction on `a using ind`. Proceed by induction on `b using ind`. Rewrite using `[lpSum_mk, lpDim_mk, lpDim_mk, lpDim_mk, finrank_prod]`.
-/
theorem lpDim_sum (a b : WD h) : lpDim (lpSum a b) = lpDim a + lpDim b := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpDim_mk, lpDim_mk, lpDim_mk, finrank_prod]

/- English proof (translation)
Proceed by induction on `a using ind`. Rewrite using `[lpTw_mk, lpDim_mk, lpDim_mk]`.
-/
theorem lpDim_tw (a : WD h) (s : ℝ) : lpDim (lpTw a s) = lpDim a := by
  induction a using ind
  rw [lpTw_mk, lpDim_mk, lpDim_mk]

/- English proof (translation)
Proceed by induction on `a using ind`. Proceed by induction on `b using ind`. Rewrite using `[lpChar_mk, lpDim_mk, lpDim_mk, lpDim_mk, finrank_tensorProduct]`.
-/
theorem lpDim_tensor (a b : WD h) : lpDim (lpChar a b) = lpDim a * lpDim b := by
  induction a using ind
  induction b using ind
  rw [lpChar_mk, lpDim_mk, lpDim_mk, lpDim_mk, finrank_tensorProduct]

/- English proof (translation)
Rewrite using `[lpDim_tensor, hχ, mul_one]`.
-/
theorem lpDim_char (a χ : WD h) (hχ : lpDim χ = 1) : lpDim (lpChar a χ) = lpDim a := by
  rw [lpDim_tensor, hχ, mul_one]

/- English proof (translation)
Proceed by induction on `a using ind`. Rewrite using `[lpZero, lpSum_mk]`. Conclude with `sound ⟨LinearEquiv.prodUnique, fun _ _ => rfl, fun _ => rfl⟩`.
-/
theorem lpSum_zero (a : WD h) : lpSum a (lpZero h) = a := by
  induction a using ind
  rw [lpZero, lpSum_mk]
  exact sound ⟨LinearEquiv.prodUnique, fun _ _ => rfl, fun _ => rfl⟩

/- English proof (translation)
Proceed by induction on `a using ind`. Proceed by induction on `b using ind`. Rewrite using `[lpSum_mk, lpSum_mk]`. Conclude with `sound ⟨LinearEquiv.prodComm _ _ _, fun _ _ => rfl, fun _ => rfl⟩`.
-/
theorem lpSum_comm (a b : WD h) : lpSum a b = lpSum b a := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpSum_mk]
  exact sound ⟨LinearEquiv.prodComm _ _ _, fun _ _ => rfl, fun _ => rfl⟩

/- English proof (translation)
Proceed by induction on `a using ind`. Proceed by induction on `b using ind`. Proceed by induction on `c using ind`. Rewrite using `[lpSum_mk, lpSum_mk, lpSum_mk, lpSum_mk]`. Conclude with `sound ⟨LinearEquiv.prodAssoc _ _ _ _, fun _ _ => rfl, fun _ => rfl⟩`.
-/
theorem lpSum_assoc (a b c : WD h) : lpSum (lpSum a b) c = lpSum a (lpSum b c) := by
  induction a using ind
  induction b using ind
  induction c using ind
  rw [lpSum_mk, lpSum_mk, lpSum_mk, lpSum_mk]
  exact sound ⟨LinearEquiv.prodAssoc _ _ _ _, fun _ _ => rfl, fun _ => rfl⟩

/- English proof (translation)
Proceed by induction on `a using ind`. Rewrite using `[lpTw_mk]`. Conclude with `sound ⟨.refl _ _, fun σ v => by simp, fun _ => rfl⟩`.
-/
theorem lpTw_zero (a : WD h) : lpTw a 0 = a := by
  induction a using ind
  rw [lpTw_mk]
  exact sound ⟨.refl _ _, fun σ v => by simp, fun _ => rfl⟩

/- English proof (translation)
Proceed by induction on `a using ind`. Establish `hq : ((normV w : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot`. Rewrite using `[lpTw_mk, lpTw_mk, lpTw_mk]`. Use `sound ⟨.refl _ _, fun σ v => ?_, fun _ => rfl⟩` and prove the remaining obligations. Simplify using `only [WDRep.tw_ρ, smul_smul, LinearEquiv.refl_apply]`.

Rewrite using `[Complex.ofReal_add, Complex.cpow_add _ _ hq, mul_zpow, mul_comm]`.
-/
theorem lpTw_add (a : WD h) (s t : ℝ) : lpTw (lpTw a s) t = lpTw a (s + t) := by
  induction a using ind
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  rw [lpTw_mk, lpTw_mk, lpTw_mk]
  refine sound ⟨.refl _ _, fun σ v => ?_, fun _ => rfl⟩
  simp only [WDRep.tw_ρ, smul_smul, LinearEquiv.refl_apply]
  rw [Complex.ofReal_add, Complex.cpow_add _ _ hq, mul_zpow, mul_comm]

/- English proof (translation)
Proceed by induction on `a using ind`. Proceed by induction on `b using ind`. Rewrite using `[lpSum_mk, lpTw_mk, lpTw_mk, lpTw_mk, lpSum_mk]`. Conclude with `sound ⟨.refl _ _, fun _ _ => rfl, fun _ => rfl⟩`.
-/
theorem lpTw_sum (a b : WD h) (s : ℝ) : lpTw (lpSum a b) s = lpSum (lpTw a s) (lpTw b s) := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpTw_mk, lpTw_mk, lpTw_mk, lpSum_mk]
  exact sound ⟨.refl _ _, fun _ _ => rfl, fun _ => rfl⟩

/- English proof (translation)
Proceed by induction on `a using ind`. Proceed by induction on `b using ind`. Rewrite using `[lpSum_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.sum_N]`. Use `⟨fun h0 => ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩, fun h0 => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Prod.fst (LinearMap.congr_fun h0 (v, 0))`.

Conclude with `congrArg Prod.snd (LinearMap.congr_fun h0 (0, v))`. Rewrite using `[h0.1, h0.2, LinearMap.prodMap_zero]`.
-/
theorem monomial_sum_iff (a b : WD h) : mono0 (lpSum a b) ↔ mono0 a ∧ mono0 b := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.sum_N]
  refine ⟨fun h0 => ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩, fun h0 => ?_⟩
  · exact congrArg Prod.fst (LinearMap.congr_fun h0 (v, 0))
  · exact congrArg Prod.snd (LinearMap.congr_fun h0 (0, v))
  · rw [h0.1, h0.2, LinearMap.prodMap_zero]

/- English proof (translation)
Proceed by induction on `a using ind`. Rewrite using `[lpTw_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tw_N]`.
-/
theorem monomial_twist_iff (a : WD h) (s : ℝ) : mono0 (lpTw a s) ↔ mono0 a := by
  induction a using ind
  rw [lpTw_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tw_N]

/- English proof (translation)
Proceed by induction on `χ using ind with`. Consider the case `hP n b`. Rewrite `hχ` using `[lpDim_mk]`. Rewrite using `[monodromyZero_ofWeilDeligneRepClass_iff]`. Establish `h1` using `b.nilpotent.charpoly_eq_X_pow_finrank`.

Establish `h2` using `LinearMap.aeval_self_charpoly b.N`. Rewrite `h2` using `[h1, hχ, pow_one, aeval_X]`. Then use the resulting hypothesis.
-/
theorem mono0_of_lpDim_eq_one {χ : WD h} (hχ : lpDim χ = 1) : mono0 χ := by
  induction χ using ind with
  | hP n b =>
    rw [lpDim_mk] at hχ
    rw [monodromyZero_ofWeilDeligneRepClass_iff]
    have h1 := b.nilpotent.charpoly_eq_X_pow_finrank
    have h2 := LinearMap.aeval_self_charpoly b.N
    rwa [h1, hχ, pow_one, aeval_X] at h2

/- English proof (translation)
Establish `h0` using `mono0_of_lpDim_eq_one hχ`. Proceed by induction on `a using ind with`. Consider the case `hP m a`. Proceed by induction on `χ using ind with`. Consider the case `hP n b`.

Rewrite `hχ` using `[lpDim_mk]`. Rewrite `h0` using `[monodromyZero_ofWeilDeligneRepClass_iff]`. Rewrite using `[lpChar_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, LinearMap.lTensor_zero, add_zero]`. Use `⟨fun h1 => LinearMap.ext fun v => ?_, fun h1 => by rw [h1, LinearMap.rTensor_zero]⟩` and prove the remaining obligations. Set `e : (Fin n → ℂ) ≃ₗ[ℂ] ℂ` to `LinearEquiv.ofFinrankEq _ _ (by rw [hχ, finrank_self])`.

Establish `h2` using `congrArg (fun x => TensorProduct.rid ℂ _ (e.toLinearMap.lTensor _ x)) (LinearMap.congr_fun h1 (v ⊗ₜ e.symm 1))`. Simplify using `using h2`.
-/
theorem monomial_char_iff (a χ : WD h) (hχ : lpDim χ = 1) : mono0 (lpChar a χ) ↔ mono0 a := by
  have h0 := mono0_of_lpDim_eq_one hχ
  induction a using ind with
  | hP m a =>
  induction χ using ind with
  | hP n b =>
    rw [lpDim_mk] at hχ
    rw [monodromyZero_ofWeilDeligneRepClass_iff] at h0
    rw [lpChar_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, LinearMap.lTensor_zero, add_zero]
    refine ⟨fun h1 => LinearMap.ext fun v => ?_, fun h1 => by rw [h1, LinearMap.rTensor_zero]⟩
    let e : (Fin n → ℂ) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by rw [hχ, finrank_self])
    have h2 := congrArg (fun x => TensorProduct.rid ℂ _ (e.toLinearMap.lTensor _ x))
      (LinearMap.congr_fun h1 (v ⊗ₜ e.symm 1))
    simpa using h2

/- English proof (translation)
Proceed by induction on `a using ind`. Proceed by induction on `b using ind`. Rewrite using `[lpSum_mk, charPol_mk, charPol_mk, charPol_mk, WDRep.sum_ρ, LinearMap.charpoly_prodMap]`.
-/
theorem charPol_lpSum (a b : WD h) (σ : Weil h) :
    charPol (lpSum a b) σ = charPol a σ * charPol b σ := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, charPol_mk, charPol_mk, charPol_mk, WDRep.sum_ρ, LinearMap.charpoly_prodMap]

/- English proof (translation)
Distinguish the cases in `hσ : σ ∈ Weil h`. Rewrite using `[inePol_of_mem _ hσ, inePol_of_mem _ hσ, inePol_of_mem _ hσ, charPol_lpSum]`. Rewrite using `[inePol_of_not_mem _ hσ, inePol_of_not_mem _ hσ, inePol_of_not_mem _ hσ, mul_one]`.
-/
theorem inePol_sum (a b : WD h) (σ : G E Ω) :
    inePol (lpSum a b) σ = inePol a σ * inePol b σ := by
  by_cases hσ : σ ∈ Weil h
  · rw [inePol_of_mem _ hσ, inePol_of_mem _ hσ, inePol_of_mem _ hσ, charPol_lpSum]
  · rw [inePol_of_not_mem _ hσ, inePol_of_not_mem _ hσ, inePol_of_not_mem _ hσ, mul_one]

/- English proof (translation)
Introduce `σ hσ`. Proceed by induction on `a using ind`. Rewrite using `[inePol_of_mem_Ine _ hσ, inePol_of_mem_Ine _ hσ, lpTw_mk, charPol_mk, charPol_mk]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem inePol_tw (a : WD h) (s : ℝ) :
    ∀ σ ∈ Ine (F := E) A, inePol (lpTw a s) σ = inePol a σ := by
  intro σ hσ
  induction a using ind
  rw [inePol_of_mem_Ine _ hσ, inePol_of_mem_Ine _ hσ, lpTw_mk, charPol_mk, charPol_mk]
  congr 1
  simp

end GlobalTheory.WeilDeligne.WD
