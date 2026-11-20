import Mathlib
import Formalism.UnipotentAdelicQuotients.JetMomFound
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsoMultiplicative

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.HeightOneInt

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [JetMomFound.mulN, nMul_succ, ih]`.
-/
theorem mulN_eq_nMul {R : Type} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    JetMomFound.mulN F n = nMul F n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [JetMomFound.mulN, nMul_succ, ih]

/- English proof (translation)
Rewrite using `[PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]`. Conclude with `(Valued.toNormedField.norm_le_one_iff).symm`.
-/
theorem mem_int_iff {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

/- English proof (translation)
Use `⟨h0, h1, ?_⟩` and prove the remaining obligations. Establish `hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)` using `fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)`. Establish `hF : PowerSeries.HasSubst F.toPowerSeries` using `PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff`. Establish `hc : ∀ i : Fin 2, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) f) = 0` using `fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) f h0`. Establish `hs : MvPowerSeries.HasSubst ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f, PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f]` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (by`.

Apply the tactic sequence `intro s; fin_cases s <;> simp [hc])`. Rewrite using `[FormalGroup.𝔾ₘ_toPowerSeries, MvPowerSeries.subst_add hs, MvPowerSeries.subst_add hs, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one]`. Establish `hinj : Function.Injective (MvPowerSeries.map (σ` using `Fin 2) φ) := by`. Introduce `a b hab`.

Use extensionality with `ν`. Apply `hφ` to reduce the goal to its premises. Rewrite using `[← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, hab]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_add, map_add, map_mul, PowerSeries.map_subst hF, PowerSeries.map_subst (hX 0), PowerSeries.map_subst (hX 1), MvPowerSeries.map_X, MvPowerSeries.map_X]`.

Conclude with `h`.
-/
theorem isIsoGm_of_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (F : FormalGroup R) (f : PowerSeries R)
    (h0 : PowerSeries.constantCoeff f = 0) (h1 : IsUnit (PowerSeries.coeff 1 f))
    (h : (f.map φ).subst (F.map φ).toPowerSeries =
      (f.map φ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) S) +
        (f.map φ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S) +
        (f.map φ).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) S) *
          (f.map φ).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) S)) :
    JetMomFound.IsIsoGm F f := by
  refine ⟨h0, h1, ?_⟩
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hc : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) f) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) f h0
  have hs : MvPowerSeries.HasSubst
      ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f,
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by
      intro s; fin_cases s <;> simp [hc])
  rw [FormalGroup.𝔾ₘ_toPowerSeries, MvPowerSeries.subst_add hs, MvPowerSeries.subst_add hs,
    MvPowerSeries.subst_mul hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin 2) φ) := by
    intro a b hab
    ext ν
    apply hφ
    rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, hab]
  apply hinj
  rw [map_add, map_add, map_mul, PowerSeries.map_subst hF, PowerSeries.map_subst (hX 0),
    PowerSeries.map_subst (hX 1), MvPowerSeries.map_X, MvPowerSeries.map_X]
  exact h

/- English proof (translation)
Introduce `p _ F _ hH`. Set `φ : 𝓞_ℂ_[p] →+* ℂ_[p]` to `(𝓞_ℂ_[p]).subtype`. Establish `hφ : Function.Injective φ` using `Subtype.val_injective`. Establish `hI : Intg (F.map φ).toPowerSeries`. Introduce `ν`.

Rewrite using `[FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map]`. Conclude with `(mem_int_iff _).1 (MvPowerSeries.coeff ν F.toPowerSeries).2`. Establish `hn : ∀ k, PowerSeries.coeff k (nMul (F.map φ) p) = ((PowerSeries.coeff k (JetMomFound.mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p])`. Introduce `k`. Rewrite using `[← (nMul_props _ F).2.2.2.2 _ φ p, PowerSeries.coeff_map, mulN_eq_nMul]`.

Both sides reduce to the same expression. Take `⟨f, hfI, hf0, hf1, hf⟩` from `HeightOne.exists_iso_multiplicative ℂ_[p] p (F.map φ) hI (by rw [hn]; exact hH.1) (fun k hk => by rw [hn]; exact hH.2 k hk)`. Set `f₀ : PowerSeries 𝓞_ℂ_[p]` to `PowerSeries.mk fun n => ⟨PowerSeries.coeff n f, (mem_int_iff _).2 (hfI (Finsupp.single () n))⟩`. Establish `hc : ∀ n, φ (PowerSeries.coeff n f₀) = PowerSeries.coeff n f`. Introduce `n`.

Simplify using `only [f₀, PowerSeries.coeff_mk]`. Both sides reduce to the same expression. Establish `hm : f₀.map φ = f`. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_map, hc]`.

Use `⟨f₀, isIsoGm_of_map φ hφ F f₀ ?_ ?_ (by rw [hm]; exact hf)⟩` and prove the remaining obligations. Apply `hφ` to reduce the goal to its premises. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc, map_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]`. Establish `hne : PowerSeries.coeff 1 f ≠ 0`. Introduce `h`.

Rewrite `hf1` using `[h, norm_zero]`. Conclude with `zero_ne_one hf1`. Use `IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff 1 f)⁻¹, (mem_int_iff _).2 ?_⟩ ?_` and prove the remaining obligations. Rewrite using `[norm_inv, hf1, inv_one]`. Apply `hφ` to reduce the goal to its premises.

Rewrite using `[map_mul, hc, map_one]`. Conclude with `mul_inv_cancel₀ hne`.
-/
theorem htOneIsGm : JetMomFound.HtOneIsGm := by
  intro p _ F _ hH
  let φ : 𝓞_ℂ_[p] →+* ℂ_[p] := (𝓞_ℂ_[p]).subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have hI : Intg (F.map φ).toPowerSeries := by
    intro ν
    rw [FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map]
    exact (mem_int_iff _).1 (MvPowerSeries.coeff ν F.toPowerSeries).2
  have hn : ∀ k, PowerSeries.coeff k (nMul (F.map φ) p) =
      ((PowerSeries.coeff k (JetMomFound.mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    intro k
    rw [← (nMul_props _ F).2.2.2.2 _ φ p, PowerSeries.coeff_map, mulN_eq_nMul]
    rfl
  obtain ⟨f, hfI, hf0, hf1, hf⟩ := HeightOne.exists_iso_multiplicative ℂ_[p] p (F.map φ) hI
    (by rw [hn]; exact hH.1) (fun k hk => by rw [hn]; exact hH.2 k hk)
  let f₀ : PowerSeries 𝓞_ℂ_[p] := PowerSeries.mk fun n =>
    ⟨PowerSeries.coeff n f, (mem_int_iff _).2 (hfI (Finsupp.single () n))⟩
  have hc : ∀ n, φ (PowerSeries.coeff n f₀) = PowerSeries.coeff n f := by
    intro n
    simp only [f₀, PowerSeries.coeff_mk]
    rfl
  have hm : f₀.map φ = f := by
    ext n
    rw [PowerSeries.coeff_map, hc]
  refine ⟨f₀, isIsoGm_of_map φ hφ F f₀ ?_ ?_ (by rw [hm]; exact hf)⟩
  · apply hφ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc, map_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]
  · have hne : PowerSeries.coeff 1 f ≠ 0 := by
      intro h
      rw [h, norm_zero] at hf1
      exact zero_ne_one hf1
    refine IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff 1 f)⁻¹, (mem_int_iff _).2 ?_⟩ ?_
    · rw [norm_inv, hf1, inv_one]
    · apply hφ
      rw [map_mul, hc, map_one]
      exact mul_inv_cancel₀ hne

end GlobalTheory.ConvSer.HeightOneInt
