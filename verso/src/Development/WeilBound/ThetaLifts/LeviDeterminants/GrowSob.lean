import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowDef
import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowSobA
import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowSobB
import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowSplit
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.ThKF0.Split

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def lineA (a : V F κ) : ℝ →+ (κ → AF F) where
  toFun t := splitE F κ (t • a, 0)
  map_zero' := by rw [zero_smul]; exact map_zero (splitE F κ)
  map_add' s t := by rw [← map_add, Prod.mk_add_mk, add_zero, add_smul]

/- English proof (translation)
Establish `e : (emb (t • ((a, 0) : V F κ × V F κ))).2 = 0` using `funext fun i => by`. Express the relevant statement in the definitionally equal form `inf (t • (0 : mixedEmbedding.mixedSpace F)) = 0`. Rewrite using `[smul_zero, inf, map_zero]`. Both sides reduce to the same expression. Rewrite using `[schr, e, dotProduct_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]`.

Both sides reduce to the same expression.
-/
theorem schr_lineA (ψ : AddChar (AF F) ℂ) (a : V F κ) (t : ℝ) (Θ : (κ → AF F) → ℂ) (x : κ → AF F) :
    schr ψ (emb (t • ((a, 0) : V F κ × V F κ))) Θ x = Θ (x + lineA a t) := by
  have e : (emb (t • ((a, 0) : V F κ × V F κ))).2 = 0 := funext fun i => by
    change inf (t • (0 : mixedEmbedding.mixedSpace F)) = 0
    rw [smul_zero, inf, map_zero]
    rfl
  rw [schr, e, dotProduct_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  rfl

/- English proof (translation)
Establish `: LocallyCompactSpace (Af F)` using `GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`. Establish `: SecondCountableTopology (Af F)` using `GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`. Establish `: T2Space (Af F)` using `GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F`. Set `mY : MeasurableSpace (κ → Af F)` to `borel _`. Establish `: BorelSpace (κ → Af F)` using `⟨rfl⟩`.

Set `mA : MeasurableSpace (κ → AF F)` to `borel _`. Establish `: BorelSpace (κ → AF F)` using `⟨rfl⟩`. Establish `: SigmaCompactSpace (κ → Af F)` using `sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `set ν : Measure (κ → Af F) := Measure.addHaar with hν`. Establish `: SFinite ν` using `inferInstance`.

Establish `: MeasurableAdd (κ → Af F)` using `ContinuousAdd.measurableAdd`. Establish `: ν.IsAddHaarMeasure` using `by rw [hν]; infer_instance`. Establish `: ((volume : Measure (Fin D → ℝ)).prod ν).IsAddHaarMeasure` using `Measure.prod.instIsAddHaarMeasure _ ν`. Set `J : ((Fin D → ℝ) × (κ → Af F)) ≃+ (κ → AF F)` to `(b.equivFun.symm.toAddEquiv.prodCongr (AddEquiv.refl _)).trans (splitE F κ)`. Establish `hJ : ∀ t y, J (t, y) = splitE F κ (b.equivFun.symm t, y)` using `fun _ _ => rfl`.

Establish `c1 : Continuous J` using `(continuous_splitE F κ).comp ((b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional).prodMap continuous_id)`. Establish `c2 : Continuous J.symm` using `((b.equivFun.toLinearMap.continuous_of_finiteDimensional).prodMap continuous_id).comp (continuous_splitE_symm F κ)`. Establish `hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map J)` using `J.isAddHaarMeasure_map _ c1 c2`. Set `em : ((Fin D → ℝ) × (κ → Af F)) ≃ᵐ (κ → AF F)` to `(Homeomorph.mk J.toEquiv c1 c2).toMeasurableEquiv`. Establish `hint : ∀ h : (κ → AF F) → ℝ≥0∞, ∫⁻ x, h x ∂((volume.prod ν).map J) = ∫⁻ p, h (J p) ∂(volume.prod ν)` using `fun h => lintegral_map_equiv h em`.

Establish `hOc : IsCompact (Om F κ)`. Use `isCompact_univ_pi fun _ : κ => GlobalTheory.AdeleCocompact.isCompact_integral F` as an intermediate fact. Conclude with `this.of_isClosed_subset (by`. Use `this.isClosed using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`.

Conclude with `⟨fun h i _ => h i, fun h i => h i trivial⟩) fun y h i _ => h i`. Establish `hOo : IsOpen (Om F κ)`. Establish `: IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}` using `RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => v.adicCompletionIntegers F) fun v => Valued.isOpen_valuationSubring _`. Use `isOpen_set_pi (i := (Set.univ : Set κ)) Set.finite_univ (fun _ _ => this) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`.

Conclude with `⟨fun h i _ => h i, fun h i => h i trivial⟩`. Establish `h0 : ν (Om F κ) ≠ 0` using `(hOo.measure_pos ν ⟨0, fun i v => zero_mem _⟩).ne'`. Establish `hT : ν (Om F κ) ≠ ⊤` using `hOc.measure_lt_top.ne`. Take `⟨k, hk⟩` from `measure_Om_le F κ ν`. Use `⟨(volume.prod ν).map J, hμH, ((ν (Om F κ))⁻¹).toNNReal, k, fun m hm G hG hinv x => ?_⟩` and prove the remaining obligations.

Take `⟨⟨t₀, y⟩, rfl⟩` from `J.surjective x`. Establish `e1 : ∀ t : Fin D → ℝ, J (t₀, y) + ∑ i, lineA (b i) (t i) = J (t₀ + t, y)` using `fun t => by`. Establish `: ∑ i, lineA (b i) (t i) = J (t, 0)`. Rewrite using `[hJ, Module.Basis.equivFun_symm_apply]`. Express the relevant statement in the definitionally equal form `∑ i, splitE F κ (t i • b i, 0) = _`.

Rewrite using `[← map_sum]`. Use `congr 1`. Conclude with `Prod.ext (by rw [Prod.fst_sum]) (by rw [Prod.snd_sum]; simp)`. Rewrite using `[this, ← map_add, Prod.mk_add_mk, add_zero]`. Simplify using `only [e1]`.

Rewrite using `[lintegral_add_left_eq_self (fun t => G (J (t, y))) t₀, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.2 h0), hint, lintegral_prod (fun p => G (J p)) (hG.comp c1).measurable.aemeasurable]`. Use `set S : Set (κ → Af F) := (fun u => m • u) '' Om F κ`. Establish `hSc : IsCompact S` using `hOc.image (continuous_nsmul m)`. Establish `key : ν S * ∫⁻ t, G (J (t, y)) ≤ ∫⁻ t, ∫⁻ y', G (J (t, y')) ∂ν`. Rewrite using `[← lintegral_const_mul' _ _ hSc.measure_lt_top.ne]`.

Use `lintegral_mono fun z => ?_` and prove the remaining obligations. Establish `hTm : MeasurableSet ((fun y' => y' + -y) ⁻¹' S)` using `hSc.isClosed.measurableSet.preimage (continuous_add_right (-y)).measurable`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_indicator_const hTm, measure_preimage_add_right, mul_comm]`. Use `_ ≤ _ := by`.

Use `lintegral_mono fun y' => (Set.indicator_le (g := fun y' => G (J (z, y'))) (fun a ha => le_of_eq ?_)) y'` and prove the remaining obligations. Take `⟨u, hu, e⟩` from `ha`. Establish `ha' : a = y + m • u`. Rewrite using `[show m • u = a + -y from e]`. Normalize the expressions using the abelian group laws.

Establish `: J (z, a) = J (z, y) + (m : AF F) • J (0, u)`. Rewrite using `[Nat.cast_smul_eq_nsmul, ← map_nsmul, ← map_add, ha']`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `G (J (z, y)) = G (J (z, a))`. Rewrite using `[this, hinv]`.

Introduce `i`. Use `⟨?_, fun v => hu i v⟩` and prove the remaining obligations. Rewrite using `[hJ, map_zero]`. Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]`. Use `_ ≤ (ν (Om F κ))⁻¹ * ((m : ℝ≥0∞) ^ k * ν S * ∫⁻ t, G (J (t, y))) := by gcongr`. Conclude with `hk m hm`. Use `_ ≤ _ := by`. Rewrite using `[mul_assoc, mul_assoc]`.

Use `gcongr`.
-/
theorem slice {D : ℕ} (b : Module.Basis (Fin D) ℝ (V F κ)) : ∃ μ, IsHaar μ ∧ ∃ (C : ℝ≥0) (k : ℕ), ∀ m : ℕ, 1 ≤ m →
    ∀ G : (κ → AF F) → ℝ≥0∞, Continuous G → (∀ u : κ → AF F, (∀ i, IntF (u i)) → ∀ x, G (x + (m : AF F) • u) = G x) →
      ∀ x, ∫⁻ t : Fin D → ℝ, G (x + ∑ i, lineA (b i) (t i)) ≤ C * (m : ℝ≥0∞) ^ k * ∫⁻ y, G y ∂μ := by
  have : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  have : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  have : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  let mY : MeasurableSpace (κ → Af F) := borel _
  have : BorelSpace (κ → Af F) := ⟨rfl⟩
  let mA : MeasurableSpace (κ → AF F) := borel _
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  have : SigmaCompactSpace (κ → Af F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → Af F) := Measure.addHaar with hν
  have : SFinite ν := inferInstance
  have : MeasurableAdd (κ → Af F) := ContinuousAdd.measurableAdd
  have : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  have : ((volume : Measure (Fin D → ℝ)).prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ ν
  let J : ((Fin D → ℝ) × (κ → Af F)) ≃+ (κ → AF F) :=
    (b.equivFun.symm.toAddEquiv.prodCongr (AddEquiv.refl _)).trans (splitE F κ)
  have hJ : ∀ t y, J (t, y) = splitE F κ (b.equivFun.symm t, y) := fun _ _ => rfl
  have c1 : Continuous J := (continuous_splitE F κ).comp
    ((b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional).prodMap continuous_id)
  have c2 : Continuous J.symm :=
    ((b.equivFun.toLinearMap.continuous_of_finiteDimensional).prodMap continuous_id).comp (continuous_splitE_symm F κ)
  have hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map J) := J.isAddHaarMeasure_map _ c1 c2
  let em : ((Fin D → ℝ) × (κ → Af F)) ≃ᵐ (κ → AF F) := (Homeomorph.mk J.toEquiv c1 c2).toMeasurableEquiv
  have hint : ∀ h : (κ → AF F) → ℝ≥0∞, ∫⁻ x, h x ∂((volume.prod ν).map J) = ∫⁻ p, h (J p) ∂(volume.prod ν) :=
    fun h => lintegral_map_equiv h em
  have hOc : IsCompact (Om F κ) := by
    have := isCompact_univ_pi fun _ : κ => GlobalTheory.AdeleCocompact.isCompact_integral F
    exact this.of_isClosed_subset (by
      convert this.isClosed using 1
      ext y
      exact ⟨fun h i _ => h i, fun h i => h i trivial⟩) fun y h i _ => h i
  have hOo : IsOpen (Om F κ) := by
    have : IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
      RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (A := fun v => v.adicCompletionIntegers F) fun v => Valued.isOpen_valuationSubring _
    convert isOpen_set_pi (i := (Set.univ : Set κ)) Set.finite_univ (fun _ _ => this) using 1
    ext y
    exact ⟨fun h i _ => h i, fun h i => h i trivial⟩
  have h0 : ν (Om F κ) ≠ 0 := (hOo.measure_pos ν ⟨0, fun i v => zero_mem _⟩).ne'
  have hT : ν (Om F κ) ≠ ⊤ := hOc.measure_lt_top.ne
  obtain ⟨k, hk⟩ := measure_Om_le F κ ν
  refine ⟨(volume.prod ν).map J, hμH, ((ν (Om F κ))⁻¹).toNNReal, k, fun m hm G hG hinv x => ?_⟩
  obtain ⟨⟨t₀, y⟩, rfl⟩ := J.surjective x
  have e1 : ∀ t : Fin D → ℝ, J (t₀, y) + ∑ i, lineA (b i) (t i) = J (t₀ + t, y) := fun t => by
    have : ∑ i, lineA (b i) (t i) = J (t, 0) := by
      rw [hJ, Module.Basis.equivFun_symm_apply]
      change ∑ i, splitE F κ (t i • b i, 0) = _
      rw [← map_sum]
      congr 1
      exact Prod.ext (by rw [Prod.fst_sum]) (by rw [Prod.snd_sum]; simp)
    rw [this, ← map_add, Prod.mk_add_mk, add_zero]
  simp only [e1]
  rw [lintegral_add_left_eq_self (fun t => G (J (t, y))) t₀, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.2 h0), hint,
    lintegral_prod (fun p => G (J p)) (hG.comp c1).measurable.aemeasurable]
  set S : Set (κ → Af F) := (fun u => m • u) '' Om F κ
  have hSc : IsCompact S := hOc.image (continuous_nsmul m)
  have key : ν S * ∫⁻ t, G (J (t, y)) ≤ ∫⁻ t, ∫⁻ y', G (J (t, y')) ∂ν := by
    rw [← lintegral_const_mul' _ _ hSc.measure_lt_top.ne]
    refine lintegral_mono fun z => ?_
    have hTm : MeasurableSet ((fun y' => y' + -y) ⁻¹' S) :=
      hSc.isClosed.measurableSet.preimage (continuous_add_right (-y)).measurable
    calc ν S * G (J (z, y)) = ∫⁻ y', ((fun y' => y' + -y) ⁻¹' S).indicator (fun _ => G (J (z, y))) y' ∂ν := by
          rw [lintegral_indicator_const hTm, measure_preimage_add_right, mul_comm]
      _ ≤ _ := by
          refine lintegral_mono fun y' => (Set.indicator_le (g := fun y' => G (J (z, y'))) (fun a ha => le_of_eq ?_)) y'
          obtain ⟨u, hu, e⟩ := ha
          have ha' : a = y + m • u := by
            rw [show m • u = a + -y from e]
            abel
          have : J (z, a) = J (z, y) + (m : AF F) • J (0, u) := by
            rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← map_add, ha']
            simp
          change G (J (z, y)) = G (J (z, a))
          rw [this, hinv]
          intro i
          refine ⟨?_, fun v => hu i v⟩
          rw [hJ, map_zero]
          exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
  calc ∫⁻ t, G (J (t, y)) = (ν (Om F κ))⁻¹ * (ν (Om F κ) * ∫⁻ t, G (J (t, y))) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]
    _ ≤ (ν (Om F κ))⁻¹ * ((m : ℝ≥0∞) ^ k * ν S * ∫⁻ t, G (J (t, y))) := by
        gcongr
        exact hk m hm
    _ ≤ _ := by
        rw [mul_assoc, mul_assoc]
        gcongr

/- English proof (translation)
Introduce `F _ _ κ _ ψ hψ`. Set `b` to `Module.finBasis ℝ (V F κ)`. Take `⟨μ, hμ, C, k, hC⟩` from `slice b`. Establish `hS : ∀ Θ ∈ (schA F κ : Set ((κ → AF F) → ℂ)), Continuous Θ` using `fun Θ hΘ => by`. Use `(continuous_comp_splitE F κ Θ hΘ).comp (continuous_splitE_symm F κ)` as an intermediate fact.

Simplify `this` using `only [Function.comp_def, AddEquiv.apply_symm_apply]`. Establish `hd : ∀ w, ∀ Θ ∈ (schA F κ : Set ((κ → AF F) → ℂ)), dR ψ w Θ ∈ (schA F κ : Set ((κ → AF F) → ℂ))` using `fun w Θ hΘ => (h F κ ψ hψ w Θ hΘ).1`. Take `⟨L, hL⟩` from `sobAbs hS hd _ (fun i => ((b i, 0) : V F κ × V F κ)) (fun i => lineA (b i)) (fun i => (continuous_splitE F κ).comp ((continuous_id.smul continuous_const).prodMk continuous_const)) (fun i Θ hΘ x => by simpa only [schr_lineA] using (h F κ ψ hψ (b i, 0) Θ hΘ).2.1 x)`. Use `⟨μ, hμ, L, 2 ^ Module.finrank ℝ (V F κ) * C, k, fun m hm Θ hΘ hl x => (hL Θ hΘ x).trans ?_⟩` and prove the remaining obligations. Establish `hw : ∀ l : List (V F κ × V F κ), Lev m (l.foldr (dR ψ) Θ)` using `fun l => by`.

Proceed by induction on `l with`. Consider the case `nil => exact hl`. Consider the case `cons w l ih => exact (h F κ ψ hψ w _ (foldr_mem hd l hΘ)).2.2 m ih`. Establish `hb` using `hC m hm _ (continuous_sumSq hS hd L hΘ) (fun u hu y => by simp only [sumSq, hw _ u hu y]) x`. Set `: MeasurableSpace (κ → AF F)` to `borel _`.

Establish `: BorelSpace (κ → AF F)` using `⟨rfl⟩`. Rewrite `hb` using `[lintegral_sumSq μ hS hd L hΘ]`. Use `push_cast`. Rewrite using `[mul_assoc, mul_assoc, ← mul_assoc (C : ℝ≥0∞)]`. Use `gcongr`.

Conclude with `hb`.
-/
theorem sob_of (h : DerivOK) : Sob := by
  intro F _ _ κ _ ψ hψ
  let b := Module.finBasis ℝ (V F κ)
  obtain ⟨μ, hμ, C, k, hC⟩ := slice b
  have hS : ∀ Θ ∈ (schA F κ : Set ((κ → AF F) → ℂ)), Continuous Θ := fun Θ hΘ => by
    have := (continuous_comp_splitE F κ Θ hΘ).comp (continuous_splitE_symm F κ)
    simpa only [Function.comp_def, AddEquiv.apply_symm_apply] using this
  have hd : ∀ w, ∀ Θ ∈ (schA F κ : Set ((κ → AF F) → ℂ)), dR ψ w Θ ∈ (schA F κ : Set ((κ → AF F) → ℂ)) :=
    fun w Θ hΘ => (h F κ ψ hψ w Θ hΘ).1
  obtain ⟨L, hL⟩ := sobAbs hS hd _ (fun i => ((b i, 0) : V F κ × V F κ)) (fun i => lineA (b i))
    (fun i => (continuous_splitE F κ).comp ((continuous_id.smul continuous_const).prodMk continuous_const))
    (fun i Θ hΘ x => by simpa only [schr_lineA] using (h F κ ψ hψ (b i, 0) Θ hΘ).2.1 x)
  refine ⟨μ, hμ, L, 2 ^ Module.finrank ℝ (V F κ) * C, k, fun m hm Θ hΘ hl x => (hL Θ hΘ x).trans ?_⟩
  have hw : ∀ l : List (V F κ × V F κ), Lev m (l.foldr (dR ψ) Θ) := fun l => by
    induction l with
    | nil => exact hl
    | cons w l ih => exact (h F κ ψ hψ w _ (foldr_mem hd l hΘ)).2.2 m ih
  have hb := hC m hm _ (continuous_sumSq hS hd L hΘ) (fun u hu y => by simp only [sumSq, hw _ u hu y]) x
  let : MeasurableSpace (κ → AF F) := borel _
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  rw [lintegral_sumSq μ hS hd L hΘ] at hb
  push_cast
  rw [mul_assoc, mul_assoc, ← mul_assoc (C : ℝ≥0∞)]
  gcongr
  exact hb

end PositivityTheory.ThKF0.Grow
