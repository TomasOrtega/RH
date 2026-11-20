import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.P5meas
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.UnitaryTransvectionZeroSecondMemClosure

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open NumberField.mixedEmbedding WithZero

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.VanishingLemma

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `1 - sFin F 1 + sFin F yf.val = _`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing F) - 0 + 0 = 1`. Rewrite using `[sub_zero, add_zero]`. Express the relevant statement in the definitionally equal form `(1 : Af F) - 1 + (yf : Af F) = _`.

Rewrite using `[sub_self, zero_add]`.
-/
theorem finId_val' (yf : (Af F)ˣ) : ((finId F yf : (Ad F)ˣ) : Ad F) = (1, (yf : Af F)) := by
  change 1 - sFin F 1 + sFin F yf.val = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
    rw [sub_zero, add_zero]
  · change (1 : Af F) - 1 + (yf : Af F) = _
    rw [sub_self, zero_add]

/- English proof (translation)
Establish `hπ : ∀ w : HeightOneSpectrum (𝓞 F), ∃ x ∈ w.asIdeal, x ≠ 0` using `fun w => Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot`. Use `choose π hπmem hπ0 using hπ`. Take `⟨δ, hδmem, hδ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))`. Use `set S := hc.toFinset`. Use `set p : 𝓞 F := ∏ w ∈ S, π w ^ c w`.

Establish `hp0 : p ≠ 0` using `Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hπ0 w)`. Use `⟨δ * p, mul_ne_zero hδ0 hp0, fun w => ?_⟩` and prove the remaining obligations. Establish `hδv : w.intValuation δ ≤ exp (-dd w)`. Establish `h` using `intValuation_le_of_mem_ideal w (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)) hδmem`. Rewrite `h` using `[FractionalIdeal.count_coe F w (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))]`.

Conclude with `h`. Establish `hpv : w.intValuation p ≤ exp (-(c w : ℤ))`. Use `(w.intValuation_le_pow_iff_mem p (c w)).2 ?_` and prove the remaining obligations. Distinguish the cases in `hw : w ∈ S`. Take `⟨q, hq⟩` from `Finset.dvd_prod_of_mem (fun w => π w ^ c w) hw`.

Rewrite using `[show p = π w ^ c w * q from hq]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hπmem w) _)`. Establish `: c w = 0`. Assume the negation of the conclusion as `h`. Conclude with `hw (hc.mem_toFinset.2 h)`.

Rewrite using `[this, pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`. Rewrite using `[map_mul, neg_add, add_comm (-(c w : ℤ)), exp_add]`. Conclude with `mul_le_mul' hδv hpv`.
-/
theorem exists_m {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      w.intValuation m ≤ exp (-((c w : ℤ) + dd w)) := by
  classical
  have hπ : ∀ w : HeightOneSpectrum (𝓞 F), ∃ x ∈ w.asIdeal, x ≠ 0 := fun w =>
    Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  choose π hπmem hπ0 using hπ
  obtain ⟨δ, hδmem, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  set S := hc.toFinset
  set p : 𝓞 F := ∏ w ∈ S, π w ^ c w
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hπ0 w)
  refine ⟨δ * p, mul_ne_zero hδ0 hp0, fun w => ?_⟩
  have hδv : w.intValuation δ ≤ exp (-dd w) := by
    have h := intValuation_le_of_mem_ideal w (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)) hδmem
    rw [FractionalIdeal.count_coe F w (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))] at h
    exact h
  have hpv : w.intValuation p ≤ exp (-(c w : ℤ)) := by
    refine (w.intValuation_le_pow_iff_mem p (c w)).2 ?_
    by_cases hw : w ∈ S
    · obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun w => π w ^ c w) hw
      rw [show p = π w ^ c w * q from hq]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hπmem w) _)
    · have : c w = 0 := by
        by_contra h
        exact hw (hc.mem_toFinset.2 h)
      rw [this, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  rw [map_mul, neg_add, add_comm (-(c w : ℤ)), exp_add]
  exact mul_le_mul' hδv hpv

/- English proof (translation)
Break down `eq_or_ne a 0 with rfl | ha` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[← exp_log ha, ← exp_add, ← exp_zero, exp_le_exp, exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exp_neg_mul_le_one_iff (n : ℤ) (a : ℤᵐ⁰) : exp (-n) * a ≤ 1 ↔ a ≤ exp n := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rw [← exp_log ha, ← exp_add, ← exp_zero, exp_le_exp, exp_le_exp]
  omega

/- English proof (translation)
Take `⟨π, hπ⟩` from `w.valuation_exists_uniformizer F`. Establish `hπ0 : (π : w.adicCompletion F) ≠ 0`. Introduce `h`. Establish `h' : Valued.v ((π : F) : w.adicCompletion F) = 0` using `by rw [h, map_zero]`. Rewrite `h'` using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]`.

Conclude with `exp_ne_zero h'`. Use `set u : w.adicCompletion F := (π : w.adicCompletion F) ^ n`. Establish `hu : Valued.v u = exp (-n)`. Rewrite using `[map_zpow₀, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← exp_zsmul]`. Use `congr 1`.

Simplify using the standard rewrite rules. Establish `heq : {z : w.adicCompletion F | Valued.v z ≤ exp n} = (fun z => u * z) ⁻¹' {z : w.adicCompletion F | Valued.v z ≤ 1}`. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, hu, exp_neg_mul_le_one_iff]`. Rewrite using `[heq]`.

Conclude with `(Valued.isClopen_integer (w.adicCompletion F)).isClosed.preimage (continuous_const.mul continuous_id)`.
-/
theorem isClosed_le_exp (w : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    IsClosed {z : w.adicCompletion F | Valued.v z ≤ exp n} := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer F
  have hπ0 : (π : w.adicCompletion F) ≠ 0 := by
    intro h
    have h' : Valued.v ((π : F) : w.adicCompletion F) = 0 := by rw [h, map_zero]
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ] at h'
    exact exp_ne_zero h'
  set u : w.adicCompletion F := (π : w.adicCompletion F) ^ n
  have hu : Valued.v u = exp (-n) := by
    rw [map_zpow₀, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← exp_zsmul]
    congr 1
    simp
  have heq : {z : w.adicCompletion F | Valued.v z ≤ exp n} =
      (fun z => u * z) ⁻¹' {z : w.adicCompletion F | Valued.v z ≤ 1} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, hu, exp_neg_mul_le_one_iff]
  rw [heq]
  exact (Valued.isClopen_integer (w.adicCompletion F)).isClosed.preimage (continuous_const.mul continuous_id)

/- English proof (translation)
Simplify using `only [L2.pInf_apply_eq]`. Conclude with `((continuous_apply _).comp continuous_fst).comp ((homeomorphMixedSpace F).continuous.comp continuous_fst)`.
-/
theorem continuous_pInf_apply (v : InfinitePlace F) : Continuous fun x : Ad F => UpperTheory.V.TR.pInf F x v := by
  simp only [L2.pInf_apply_eq]
  exact ((continuous_apply _).comp continuous_fst).comp ((homeomorphMixedSpace F).continuous.comp continuous_fst)

/- English proof (translation)
Simplify using `only [Set.setOf_forall]`. Use `isClosed_iInter fun w => (isClosed_le_exp w (n w)).preimage ?_` and prove the remaining obligations. Conclude with `(RestrictedProduct.continuous_eval w).comp (continuous_snd.comp hf)`.
-/
theorem isClosed_cond {X : Type*} [TopologicalSpace X] {f : X → Ad F} (hf : Continuous f) (n : HeightOneSpectrum (𝓞 F) → ℤ) :
    IsClosed {p | ∀ w, Valued.v (pLoc F w (pFin F (f p))) ≤ exp (n w)} := by
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun w => (isClosed_le_exp w (n w)).preimage ?_
  exact (RestrictedProduct.continuous_eval w).comp (continuous_snd.comp hf)

/- English proof (translation)
Unfold `kernF`. Use `Measurable.mul (Continuous.measurable ?_) (Measurable.ite ?_ (Continuous.measurable ?_) measurable_const)` and prove the remaining obligations. Use `continuous_finset_prod _ fun v _ => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun p => (UpperTheory.V.TR.pInf F (A p) v : ℂ)` using `Complex.continuous_ofReal.comp ((continuous_pInf_apply v).comp hA)`. Establish `h2 : Continuous fun p => (UpperTheory.V.TR.pInf F (Z p) v : ℂ)` using `Complex.continuous_ofReal.comp ((continuous_pInf_apply v).comp hZ)`.

Conclude with `(h1.add h2).mul (Complex.continuous_exp.comp (continuous_const.mul ((h1.pow 2).add (h2.pow 2))))`. Use `((isClosed_cond hA fun w => -(c w : ℤ)).inter (isClosed_cond hZ fun w => (c w : ℤ) + dd w)).measurableSet` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp (continuous_finiteAdelicChar.comp (continuous_snd.comp hZ))`.
-/
theorem measurable_kernF_comp {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (c : HeightOneSpectrum (𝓞 F) → ℕ) {A Z : X → Ad F} (hA : Continuous A) (hZ : Continuous Z) :
    Measurable fun p => kernF c (A p) (Z p) := by
  classical
  unfold kernF
  refine Measurable.mul (Continuous.measurable ?_) (Measurable.ite ?_ (Continuous.measurable ?_) measurable_const)
  · refine continuous_finset_prod _ fun v _ => ?_
    have h1 : Continuous fun p => (UpperTheory.V.TR.pInf F (A p) v : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_pInf_apply v).comp hA)
    have h2 : Continuous fun p => (UpperTheory.V.TR.pInf F (Z p) v : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_pInf_apply v).comp hZ)
    exact (h1.add h2).mul (Complex.continuous_exp.comp (continuous_const.mul ((h1.pow 2).add (h2.pow 2))))
  · refine ((isClosed_cond hA fun w => -(c w : ℤ)).inter (isClosed_cond hZ fun w => (c w : ℤ) + dd w)).measurableSet
  · exact continuous_subtype_val.comp (continuous_finiteAdelicChar.comp (continuous_snd.comp hZ))

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.VanishingLemma

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open VanishingLemma

/- English proof (translation)
Introduce `F _ _ _ c hc`. Take `⟨m, hm0, hmv⟩` from `exists_m hc`. Establish `hmF : ((m : 𝓞 F) : F) ≠ 0`. Simplify using `using hm0`. Use `set mu : (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom (Units.mk0 _ hmF)`.

Use `⟨finId F mu, fun Z => ?_, fun Z hZ => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.smul_def, finId_val']`. Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing F) * Z.1 = Z.1`. Rewrite using `[one_mul]`. Rewrite using `[Units.smul_def, finId_val', mem_idealFiniteAdeles]`.

Introduce `w`. Rewrite using `[Units.val_one, FractionalIdeal.count_one, neg_zero, exp_zero]`. Express the relevant statement in the definitionally equal form `Valued.v ((((algebraMap (𝓞 F) F m : F)) : w.adicCompletion F) * Z.2 w) ≤ 1`. Rewrite using `[map_mul, valued_coe_algebraMap]`. Establish `h1` using `hmv w`.

Establish `h2` using `hZ w`. Express the relevant statement in the definitionally equal form `Valued.v (Z.2 w) ≤ _ at h2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem measure_bound_holds : P5mu := by
  intro F _ _ _ c hc
  obtain ⟨m, hm0, hmv⟩ := exists_m hc
  have hmF : ((m : 𝓞 F) : F) ≠ 0 := by
    simpa using hm0
  set mu : (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom (Units.mk0 _ hmF)
  refine ⟨finId F mu, fun Z => ?_, fun Z hZ => ?_⟩
  · rw [Units.smul_def, finId_val']
    change (1 : InfiniteAdeleRing F) * Z.1 = Z.1
    rw [one_mul]
  · rw [Units.smul_def, finId_val', mem_idealFiniteAdeles]
    intro w
    rw [Units.val_one, FractionalIdeal.count_one, neg_zero, exp_zero]
    change Valued.v ((((algebraMap (𝓞 F) F m : F)) : w.adicCompletion F) * Z.2 w) ≤ 1
    rw [map_mul, valued_coe_algebraMap]
    have h1 := hmv w
    have h2 := hZ w
    change Valued.v (Z.2 w) ≤ _ at h2
    calc w.intValuation m * Valued.v (Z.2 w) ≤ exp (-((c w : ℤ) + dd w)) * exp ((c w : ℤ) + dd w) :=
          mul_le_mul' h1 h2
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]

/- English proof (translation)
Introduce `F _ _ _ c κ hκ Y ξ`. Unfold `coefK`. Use `Measurable.tsum fun a => ?_` and prove the remaining obligations. Establish `hτ : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => tau p.1 p.2 * diagonal F a` using `(((continuous_moduleSection (w0 F)).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul continuous_const`. Simplify using `only [kern, hκ]`.

Use `Measurable.mul (Continuous.measurable ?_) (measurable_const.mul ?_)` and prove the remaining obligations. Establish `hm : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ((IdeleGroup.ideleModule F (tau p.1 p.2 * diagonal F a) : {r : ℝ // 0 < r}) : ℝ)` using `continuous_subtype_val.comp ((IdeleGroup.continuous_ideleModule (K := F)).comp hτ)`. Conclude with `(Complex.continuous_ofReal.comp hm).inv₀ fun p => Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule F _).2.ne'`. Use `measurable_kernF_comp c ?_ ?_` and prove the remaining obligations. Conclude with `(Units.continuous_val.comp hτ).mul continuous_const`.

Simplify using `only [Units.smul_def]`. Conclude with `(Units.continuous_val.comp hτ.inv).mul continuous_const`.
-/
theorem measurability_holds : P5meas := by
  intro F _ _ _ c κ hκ Y ξ
  unfold coefK
  refine Measurable.tsum fun a => ?_
  have hτ : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => tau p.1 p.2 * diagonal F a :=
    (((continuous_moduleSection (w0 F)).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul continuous_const
  simp only [kern, hκ]
  refine Measurable.mul (Continuous.measurable ?_) (measurable_const.mul ?_)
  · have hm : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
        ((IdeleGroup.ideleModule F (tau p.1 p.2 * diagonal F a) : {r : ℝ // 0 < r}) : ℝ) :=
      continuous_subtype_val.comp ((IdeleGroup.continuous_ideleModule (K := F)).comp hτ)
    exact (Complex.continuous_ofReal.comp hm).inv₀ fun p => Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule F _).2.ne'
  · refine measurable_kernF_comp c ?_ ?_
    · exact (Units.continuous_val.comp hτ).mul continuous_const
    · simp only [Units.smul_def]
      exact (Units.continuous_val.comp hτ.inv).mul continuous_const

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
