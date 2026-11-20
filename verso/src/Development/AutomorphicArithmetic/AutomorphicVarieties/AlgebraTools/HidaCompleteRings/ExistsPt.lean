import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.SepIffInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
open IsLocalRing UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite UpperTheory.V.HV UpperTheory.V.Alg

section SlopeTestRemainingChoices

open Polynomial

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x)` using `rfl`. Rewrite using `[h0, spectralValue_le_one_iff (minpoly.monic hi)]`. Prove the components needed by the constructor for the conclusion. Introduce `h n`.

Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]`. Conclude with `PadicInt.norm_le_one _`. Introduce `h`. Establish `hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l])` using `(lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)`.

Conclude with `⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩`.
-/
private theorem exPt_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨c, le_rfl, by simp⟩`. Consider the case `insert a s _ ih`. Take `⟨d, hd, hd'⟩` from `ih fun x hx => hs x (Finset.mem_insert_of_mem hx)`. Take `⟨e, he, he'⟩` from `(coefSup l).2.2.1 d a (hs a (Finset.mem_insert_self _ _))`.

Use `⟨e, hd.trans he, fun x hx => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Conclude with `he'`. Conclude with `he (hd' x hx)`.
-/
private theorem exPt_coef {l : ℕ} [Fact l.Prime] (c : Coef l) (s : Finset (PadicAlgCl l))
    (hs : ∀ x ∈ s, IsIntegral ℤ_[l] x) : ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ x ∈ s, x ∈ c'.O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨d, hd, hd'⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨e, he, he'⟩ := (coefSup l).2.2.1 d a (hs a (Finset.mem_insert_self _ _))
    refine ⟨e, hd.trans he, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact he'
    · exact he (hd' x hx)

/- English proof (translation)
Introduce `hu`. Take `⟨w, hw⟩` from `hu.exists_right_inv`. Establish `hi : IsIntegral ℤ_[l] (w : PadicAlgCl l)` using `(Algebra.IsIntegral.isIntegral (R := ℤ_[l]) w).map c.O.val`. Establish `h1` using `(exPt_intIff _).1 hi`. Establish `h2 : (x : PadicAlgCl l) * w = 1` using `congrArg Subtype.val hw`.

Establish `h3` using `congrArg norm h2`. Rewrite `h3` using `[norm_mul, norm_one]`. Use polynomial arithmetic with `[norm_nonneg (x : PadicAlgCl l), norm_nonneg (w : PadicAlgCl l)]`.
-/
private theorem exPt_nonunit {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) (hx : ‖(x : PadicAlgCl l)‖ < 1) :
    ¬ IsUnit x := by
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hi : IsIntegral ℤ_[l] (w : PadicAlgCl l) :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) w).map c.O.val
  have h1 := (exPt_intIff _).1 hi
  have h2 : (x : PadicAlgCl l) * w = 1 := congrArg Subtype.val hw
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one] at h3
  nlinarith [norm_nonneg (x : PadicAlgCl l), norm_nonneg (w : PadicAlgCl l)]

/- English proof (translation)
Use `haveI : IsAdicComplete (maximalIdeal O) O := (UpperTheory.V.abelian₂.dvr_finite l O).1`. Take `⟨F, ⟨hC, hX⟩, -⟩` from `co_ev O O O σ (AlgHom.id _ _) a ha`. Use `⟨(F : MvPowerSeries σ O →+* O).comp (MvPowerSeries.map f), fun r => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, MvPowerSeries.map_C, RingHom.coe_coe, hC]`. Both sides reduce to the same expression.

Rewrite using `[RingHom.comp_apply, MvPowerSeries.map_X, RingHom.coe_coe, hX]`.
-/
private theorem exPt_ev (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] {R σ : Type} [CommRing R] [Finite σ] (f : R →+* O)
    (a : σ → O) (ha : ∀ i, ¬ IsUnit (a i)) :
    ∃ G : MvPowerSeries σ R →+* O, (∀ r, G (MvPowerSeries.C r) = f r) ∧ ∀ i, G (MvPowerSeries.X i) = a i := by
  haveI : IsAdicComplete (maximalIdeal O) O := (UpperTheory.V.abelian₂.dvr_finite l O).1
  obtain ⟨F, ⟨hC, hX⟩, -⟩ := co_ev O O O σ (AlgHom.id _ _) a ha
  refine ⟨(F : MvPowerSeries σ O →+* O).comp (MvPowerSeries.map f), fun r => ?_, fun i => ?_⟩
  · rw [RingHom.comp_apply, MvPowerSeries.map_C, RingHom.coe_coe, hC]
    rfl
  · rw [RingHom.comp_apply, MvPowerSeries.map_X, RingHom.coe_coe, hX]

/- English proof (translation)
Introduce `l _ c σ _ z hz`. Use `haveI := Fintype.ofFinite σ`. Take `⟨c', hc, hm⟩` from `exPt_coef c (Finset.univ.image z) fun x hx => by`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `(exPt_intIff _).2 (hz i).le`.

Establish `hm' : ∀ i, z i ∈ c'.O` using `fun i => hm _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Take `⟨G, hC, hX⟩` from `exPt_ev l c'.O (Subalgebra.inclusion hc).toRingHom (fun i => ⟨z i, hm' i⟩) fun i => exPt_nonunit c' _ (hz i)`. Use `⟨c', ⟨c'.O.val.toRingHom.comp G, fun r => ?_⟩, hc, fun f => (G f).2, fun i => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (hC r)`. Conclude with `congrArg Subtype.val (hX i)`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (σ : Type) [Finite σ] (z : σ → PadicAlgCl l), (∀ i, ‖z i‖ < 1) → ∃ (c' : Coef l) (y : MvPowerSeries σ c.O →ₐ[c.O] PadicAlgCl l), c.O ≤ c'.O ∧ (∀ f, y f ∈ c'.O) ∧ ∀ i, y (MvPowerSeries.X i) = z i := by
  intro l _ c σ _ z hz
  classical
  haveI := Fintype.ofFinite σ
  obtain ⟨c', hc, hm⟩ := exPt_coef c (Finset.univ.image z) fun x hx => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact (exPt_intIff _).2 (hz i).le
  have hm' : ∀ i, z i ∈ c'.O := fun i => hm _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  obtain ⟨G, hC, hX⟩ := exPt_ev l c'.O (Subalgebra.inclusion hc).toRingHom (fun i => ⟨z i, hm' i⟩)
    fun i => exPt_nonunit c' _ (hz i)
  refine ⟨c', ⟨c'.O.val.toRingHom.comp G, fun r => ?_⟩, hc, fun f => (G f).2, fun i => ?_⟩
  · exact congrArg Subtype.val (hC r)
  · exact congrArg Subtype.val (hX i)
