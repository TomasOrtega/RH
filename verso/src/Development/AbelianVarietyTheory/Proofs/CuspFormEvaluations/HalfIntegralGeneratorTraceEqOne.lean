import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNormalisedIsoReadingOneAnalyticFrameStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacter

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ)`. Establish `h` using `congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq`. Simplify using `using h`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`.

Use `set u := φ (H.rt : E) with hu`. Establish `hre` using `congrArg Complex.re hsq`. Establish `him` using `congrArg Complex.im hsq`. Simplify using `[pow_two] at hre him`. Establish `him' : u.re * u.im = 0` using `by linarith`.

Establish `hu0 : u.re = 0`. Break down `mul_eq_zero.1 him' with h | h` into its components or cases. Conclude with `h`. Rewrite `hre` using `[h]`. Use polynomial arithmetic with `[sq_nonneg u.re]`.

Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj, map_neg]`. Apply `Complex.ext` to reduce the goal to its premises. Apply the tactic sequence `all_goals simp`. Apply the tactic sequence `all_goals (rw [← hu]; linarith)`.
-/
private theorem complexConj_rt_eq_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
    simpa using h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  set u := φ (H.rt : E) with hu
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp [pow_two] at hre him
  have him' : u.re * u.im = 0 := by linarith
  have hu0 : u.re = 0 := by
    rcases mul_eq_zero.1 him' with h | h
    · exact h
    · rw [h] at hre; nlinarith [sq_nonneg u.re]
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply Complex.ext
  all_goals simp
  all_goals (rw [← hu]; linarith)

/- English proof (translation)
Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `h1` using `congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root`. Rewrite `h1` using `[map_mul, map_add, map_one, map_ofNat]`. Establish `h2` using `congrArg (IsCMField.complexConj E) h1`. Rewrite `h2` using `[map_mul, map_add, map_one, map_ofNat]`.

Establish `hr : IsCMField.complexConj E (algebraMap (𝓞 E) E H.rt) = -(algebraMap (𝓞 E) E H.rt)` using `complexConj_rt_eq_neg H`. Establish `hb : algebraMap (𝓞 E) E (H.bar H.w0) = IsCMField.complexConj E (algebraMap (𝓞 E) E H.w0)` using `H.bar_eq _`. Rewrite using `[map_add, map_one]`. Take the linear combination `(h1 + h2) / 2 + hb + hr / 2`.
-/
theorem halfIntegralGenerator_trace_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  apply RingOfIntegers.coe_injective
  have h1 := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, map_ofNat] at h1
  have h2 := congrArg (IsCMField.complexConj E) h1
  rw [map_mul, map_add, map_one, map_ofNat] at h2
  have hr : IsCMField.complexConj E (algebraMap (𝓞 E) E H.rt) = -(algebraMap (𝓞 E) E H.rt) :=
    complexConj_rt_eq_neg H
  have hb : algebraMap (𝓞 E) E (H.bar H.w0) = IsCMField.complexConj E (algebraMap (𝓞 E) E H.w0) :=
    H.bar_eq _
  rw [map_add, map_one]
  linear_combination (h1 + h2) / 2 + hb + hr / 2

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem univ_finset_fin_two : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide

/- English proof (translation)
Rewrite using `[← (Equiv.ulift (α := Finset (Fin 2))).symm.sum_comp, univ_finset_fin_two, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]`. Simplify using `only [Equiv.ulift_symm_apply, add_assoc]`.
-/
theorem chi_sum_two {M : Type} [AddCommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∑ I, f I = f ⟨∅⟩ + f ⟨{0}⟩ + f ⟨{1}⟩ + f ⟨{0, 1}⟩ := by
  rw [← (Equiv.ulift (α := Finset (Fin 2))).symm.sum_comp, univ_finset_fin_two,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Equiv.ulift_symm_apply, add_assoc]

/- English proof (translation)
Rewrite using `[← (Equiv.ulift (α := Finset (Fin 2))).symm.prod_comp, univ_finset_fin_two, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]`. Simplify using `only [Equiv.ulift_symm_apply, _root_.mul_assoc]`.
-/
theorem chi_prod_two {M : Type} [CommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∏ I, f I = f ⟨∅⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨{0, 1}⟩ := by
  rw [← (Equiv.ulift (α := Finset (Fin 2))).symm.prod_comp, univ_finset_fin_two,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [Equiv.ulift_symm_apply, _root_.mul_assoc]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ y g ty el Φ a ha`. Take `⟨⟨wP, hP⟩, hrd⟩` from `GlobalTheory.T.exists_normalisedIso_reading_one_analyticFrame E H Dw l Xo c y g ty el Φ`. Establish `hlat : ∀ b ∈ Φ.lat, tyAct ty H.w0 b ∈ Φ.lat`. Introduce `b hb`. Use `Xo.univ.t.act.hom H.w0` as an intermediate fact.

Rewrite using `[← Φ.e_ker, Φ.lin, (Φ.e_ker b).2 hb, MonObj.one_comp]`. Establish `hw` using `hlat a ha`. Establish `htr : ∀ w : Fin g → ℂ, tyAct ty H.w0 w + tyAct ty (H.bar H.w0) w = w`. Introduce `w`. Establish `h1 : (H.w0 : E) + ((H.bar H.w0 : 𝓞 E) : E) = 1`.

Conclude with `congrArg (fun x : 𝓞 E => (x : E)) (halfIntegralGenerator_trace_eq_one H)` after adjusting the coercions. Use function extensionality and compare the values at `k`. Simplify using `only [tyAct, Pi.add_apply, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]`. Rewrite using `[← add_mul, ← map_add, h1, map_one, _root_.one_mul]`. Set `Λ : (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, tyAct ty H.w0]))`.

Establish `hΛ : ∀ k z, Λ k z = Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z]) k`. Introduce `k z`. Break down `k with k | I` into its components or cases. Both sides reduce to the same expression. Simplify using `only [Λ, Sum.elim_inr, LinearMap.comp_apply]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`. Establish `hT` using `GlobalTheory.T.abelianHolomorphicFrame_reading_const_of_forms_cancel _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr _ _ _ _ wP hP.1 g (fun z => (Φ.e z).left) Λ Φ.lat Φ.hol (fun z k => by rw [hΛ]; exact (hrd wP hP z).1 k) Φ.span (fun gm hgm => ⟨fun z => by simp only [Φ.e_add, (Φ.e_ker …`. Rewrite using `[hΛ]`.

Break down `k with k | I` into its components or cases. Conclude with `hgm`. Use `show psumL 2 g I ![gm, tyAct ty H.w0 gm] ∈ Φ.lat`. Simplify using `only [psumL, LinearMap.sum_apply, LinearMap.proj_apply]`. Use `AddSubgroup.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Use `fin_cases i`. Conclude with `hgm`. Conclude with `hlat gm hgm⟩)`. Use the proof step `(fun z w => by`. Rewrite using `[Fintype.sum_sum_type, Fin.sum_univ_one, chi_sum_two]`.

Simplify using `[Λ, psumL, cε]`. Establish `hz` using `semichar_herm_add_left Φ.Hm z (tyAct ty H.w0 z) (w + tyAct ty H.w0 w)`. Establish `hz1` using `semichar_herm_add_right Φ.Hm z w (tyAct ty H.w0 w)`. Establish `hz2` using `semichar_herm_add_right Φ.Hm (tyAct ty H.w0 z) w (tyAct ty H.w0 w)`. Establish `h0` using `semichar_herm_zero_left Φ.Hm (0 : Fin g → ℂ)`.

Establish `hadj` using `Φ.adj H.w0 z w`. Establish `hs` using `semichar_herm_add_right Φ.Hm z (tyAct ty H.w0 w) (tyAct ty (H.bar H.w0) w)`. Rewrite `hs` using `[htr]`. Take the linear combination `(-1 : ℂ) * hz - hz1 - hz2 - h0 - hadj + hs)`. Establish `hprod` using `hT.2 a ha`.

Rewrite `hprod` using `[Fintype.prod_sum_type, Fin.prod_univ_one, chi_prod_two]`. Simplify using `[Λ, psumL, cε] at hprod`. Rewrite `hprod` using `[Φ.toAnFr.χ_zero, Φ.toAnFr.χ_add ha hw]`. Establish `ha0` using `Φ.toAnFr.χ_ne_zero ha`. Establish `hw0` using `Φ.toAnFr.χ_ne_zero hw`.

Establish `hX` using `Complex.exp_ne_zero (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ))`. Establish `key : Φ.χ a * (Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ)))⁻¹ = 1`. Rewrite using `[← hprod]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.

Establish `hχ` using `(mul_inv_eq_one₀ hX).1 key`. Take `⟨k, hk⟩` from `Φ.toAnFr.herm_im_int ha hw`. Use `⟨?_, hχ⟩` and prove the remaining obligations. Rewrite using `[hχ, hk, ← Complex.exp_nat_mul]`. Use `Complex.exp_int_mul_two_pi_mul_I k using 2` and compare the differences between its conclusion and the goal.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chi_eq_sign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 ∧ Φ.χ a = Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ a ha
  obtain ⟨⟨wP, hP⟩, hrd⟩ := GlobalTheory.T.exists_normalisedIso_reading_one_analyticFrame E H Dw l Xo c y g ty el Φ
  have hlat : ∀ b ∈ Φ.lat, tyAct ty H.w0 b ∈ Φ.lat := by
    intro b hb
    have := Xo.univ.t.act.hom H.w0
    rw [← Φ.e_ker, Φ.lin, (Φ.e_ker b).2 hb, MonObj.one_comp]
  have hw := hlat a ha
  have htr : ∀ w : Fin g → ℂ, tyAct ty H.w0 w + tyAct ty (H.bar H.w0) w = w := by
    intro w
    have h1 : (H.w0 : E) + ((H.bar H.w0 : 𝓞 E) : E) = 1 := by
      exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) (halfIntegralGenerator_trace_eq_one H)
    funext k
    simp only [tyAct, Pi.add_apply, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    rw [← add_mul, ← map_add, h1, map_one, _root_.one_mul]
  let Λ : (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, tyAct ty H.w0]))
  have hΛ : ∀ k z, Λ k z = Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z]) k := by
    intro k z
    rcases k with k | I
    · rfl
    · simp only [Λ, Sum.elim_inr, LinearMap.comp_apply]
      congr 1
      funext i
      fin_cases i <;> rfl
  have hT := GlobalTheory.T.abelianHolomorphicFrame_reading_const_of_forms_cancel _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr _ _ _ _ wP hP.1 g
    (fun z => (Φ.e z).left) Λ Φ.lat Φ.hol
    (fun z k => by rw [hΛ]; exact (hrd wP hP z).1 k) Φ.span
    (fun gm hgm => ⟨fun z => by simp only [Φ.e_add, (Φ.e_ker gm).2 hgm, _root_.mul_one], fun k => by
      rw [hΛ]
      rcases k with k | I
      · exact hgm
      · show psumL 2 g I ![gm, tyAct ty H.w0 gm] ∈ Φ.lat
        simp only [psumL, LinearMap.sum_apply, LinearMap.proj_apply]
        refine AddSubgroup.sum_mem _ fun i _ => ?_
        fin_cases i
        · exact hgm
        · exact hlat gm hgm⟩)
    (fun z w => by
      rw [Fintype.sum_sum_type, Fin.sum_univ_one, chi_sum_two]
      simp [Λ, psumL, cε]
      have hz := semichar_herm_add_left Φ.Hm z (tyAct ty H.w0 z) (w + tyAct ty H.w0 w)
      have hz1 := semichar_herm_add_right Φ.Hm z w (tyAct ty H.w0 w)
      have hz2 := semichar_herm_add_right Φ.Hm (tyAct ty H.w0 z) w (tyAct ty H.w0 w)
      have h0 := semichar_herm_zero_left Φ.Hm (0 : Fin g → ℂ)
      have hadj := Φ.adj H.w0 z w
      have hs := semichar_herm_add_right Φ.Hm z (tyAct ty H.w0 w) (tyAct ty (H.bar H.w0) w)
      rw [htr] at hs
      linear_combination (-1 : ℂ) * hz - hz1 - hz2 - h0 - hadj + hs)
  have hprod := hT.2 a ha
  rw [Fintype.prod_sum_type, Fin.prod_univ_one, chi_prod_two] at hprod
  simp [Λ, psumL, cε] at hprod
  rw [Φ.toAnFr.χ_zero, Φ.toAnFr.χ_add ha hw] at hprod
  have ha0 := Φ.toAnFr.χ_ne_zero ha
  have hw0 := Φ.toAnFr.χ_ne_zero hw
  have hX := Complex.exp_ne_zero (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ))
  have key : Φ.χ a * (Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ)))⁻¹ = 1 := by
    rw [← hprod]
    field_simp
    try ring
  have hχ := (mul_inv_eq_one₀ hX).1 key
  obtain ⟨k, hk⟩ := Φ.toAnFr.herm_im_int ha hw
  refine ⟨?_, hχ⟩
  rw [hχ, hk, ← Complex.exp_nat_mul]
  convert Complex.exp_int_mul_two_pi_mul_I k using 2
  push_cast
  ring

end GlobalTheory.AnVal
