import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Unfold

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

/- English proof (translation)
Set `f : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} → orbS (GamA σ J) (ratTup (F` to `F) (AF F) X0) := fun X => ⟨ratTup (F := F) (AF F) (X : Fin a → Fin M → E), by`. Take `⟨g, hg, hgX⟩` from `hW X X.2`. Use `⟨ratElA σ J g hg, ratElA_mem σ J g hg, ?_⟩` and prove the remaining obligations. Rewrite using `[ratElA_smul]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `hgX i⟩`. Establish `hinj : Function.Injective f` using `fun X X' h => Subtype.ext (ratTup_injective (congrArg Subtype.val h))`. Establish `hsurj : Function.Surjective f`. Introduce and unpack `⟨x, ⟨γ, hγ, rfl⟩⟩`.

Take `⟨g, hg, hgγ⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 (show (show HR (AF F) σ J from γ) ∈ HFinIn (AF F) σ J from hγ))`. Establish `hγe : γ = ratElA σ J g hg` using `Subtype.ext hgγ.symm`. Establish `hg' : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J` using `hg`. Use `⟨⟨fun i => (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i), ?_⟩, ?_⟩` and prove the remaining obligations. Use `show gramE σ J _ = gramE σ J X0`.

Use extensionality with `i j`. Use `show Formalism.UG.hform (σ : E →+* E) J _ _ = Formalism.UG.hform (σ : E →+* E) J _ _`. Rewrite using `[Formalism.UG.P.hform_mulVec, hg']`. Apply `Subtype.ext show ratTup (F := F) (AF F) _ = γ • ratTup (F := F) (AF F) X0` to reduce the goal to its premises. Rewrite using `[hγe, ratElA_smul]`.

Conclude with `⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun X => rfl⟩`.
-/
theorem gram_orbit_equiv {a : ℕ} (X0 : Fin a → Fin M → E)
    (hW : ∀ X : Fin a → Fin M → E, gramE σ J X = gramE σ J X0 →
      ∃ g ∈ Formalism.UG.UJ (σ : E →+* E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i) = X i) :
    ∃ e : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} ≃
        orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
      ∀ X, (e X : Fin a → Fin M → AF F ⊗[F] E) = ratTup (F := F) (AF F) (X : Fin a → Fin M → E) := by
  let f : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} →
      orbS (GamA σ J) (ratTup (F := F) (AF F) X0) := fun X =>
    ⟨ratTup (F := F) (AF F) (X : Fin a → Fin M → E), by
      obtain ⟨g, hg, hgX⟩ := hW X X.2
      refine ⟨ratElA σ J g hg, ratElA_mem σ J g hg, ?_⟩
      rw [ratElA_smul]
      congr 1
      funext i
      exact hgX i⟩
  have hinj : Function.Injective f := fun X X' h =>
    Subtype.ext (ratTup_injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, ⟨γ, hγ, rfl⟩⟩
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.1
      (Subgroup.mem_subgroupOf.1 (show (show HR (AF F) σ J from γ) ∈ HFinIn (AF F) σ J from hγ))
    have hγe : γ = ratElA σ J g hg := Subtype.ext hgγ.symm
    have hg' : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
        (g : Matrix (Fin M) (Fin M) E) = J := hg
    refine ⟨⟨fun i => (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i), ?_⟩, ?_⟩
    · show gramE σ J _ = gramE σ J X0
      ext i j
      show Formalism.UG.hform (σ : E →+* E) J _ _ = Formalism.UG.hform (σ : E →+* E) J _ _
      rw [Formalism.UG.P.hform_mulVec, hg']
    · apply Subtype.ext
      show ratTup (F := F) (AF F) _ = γ • ratTup (F := F) (AF F) X0
      rw [hγe, ratElA_smul]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun X => rfl⟩

end Main

section Of

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C 𝓕' h𝓕' φ hφ0 hadm hθ`. Use `haveI : MeasurableMul (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1`. Use `haveI : MeasurableInv (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2`. Use `haveI : μ.IsHaarMeasure := hμ`. Use `haveI : μ'.IsHaarMeasure := hμ'H`.

Use `haveI : μ.IsInvInvariant := (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1 μ hμ`. Use `haveI : μ'.IsInvInvariant := (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2 ψ hψ μ hμ νX hν μ' hμ'H hμ'C`. Use `haveI : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J`. Use `haveI hΓc : Countable (GamA σ J) := um_countable_HFinIn F E σ M J`. Take `⟨e, he⟩` from `gram_orbit_equiv σ J X0 (hW F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet)`.

Establish `hsub : orbS (GamA σ J) (ratTup (F` using `F) (AF F) X0) ⊆ Set.range (fun γ : (GamA σ J) => (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) X0) := by`. Introduce and unpack `x ⟨γ, hγ, e⟩`. Conclude with `⟨⟨γ, hγ⟩, e⟩`. Use `haveI hcO : Countable (orbS (GamA σ J) (ratTup (F := F) (AF F) X0)) := ((Set.countable_range _).mono hsub).to_subtype`. Establish `hmφ : Measurable fun g : HA (AF F) σ J => φ (g • ratTup (F` using `F) (AF F) X0) := by`.

Use `hMO F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet _ hadm` as an intermediate fact. Establish `h2` using `Complex.measurable_re.comp this`. Simplify using `only [Function.comp_def, Complex.ofReal_re] at h2`. Conclude with `h2`. Establish `hint : Integrable (fun X => (φ X : ℂ)) νX`.

Take `⟨d, b, Φinf, Φf, Φv, h1, h2, h3, h4⟩` from `id hadm`. Take `⟨⟨μinf, hμinf⟩, k1⟩` from `hν.2`. Take `⟨⟨νinf, hνinf⟩, k2⟩` from `k1 μinf hμinf`. Take `⟨⟨μv, hμv⟩, k3⟩` from `k2 νinf hνinf`. Take `⟨⟨νv, hνv⟩, k4⟩` from `k3 μv hμv`.

Take `⟨⟨fI, hfI⟩, k5⟩` from `k4 νv hνv`. Take `⟨⟨fV, hfV⟩, k6⟩` from `k5 fI hfI`. Conclude with `(k6 fV hfV d b _ Φinf Φf Φv h1 h2 h3 h4).1`. Establish `hφae : AEMeasurable φ νX`. Establish `h2` using `Complex.measurable_re.comp_aemeasurable hint.aestronglyMeasurable.aemeasurable`.

Simplify using `only [Function.comp_def, Complex.ofReal_re] at h2`. Conclude with `h2`. Establish `key : ∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J) (ratTup (F` using `F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ = μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX := unfold_abs (Γ := GamA σ J) (H := stabT (AF F) σ J X0) μ μ' (ratTup (F := F) (AF F) X0) (fun k => MulAction.mem_stabilizer_iff) νX (fun X => ENNReal.ofReal (φ …`. Establish `hθS : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J) (ratTup (F` using `F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) = ∑' X : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0}, ENNReal.ofReal (φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin a → Fin M → E))) := by`. Introduce `h`.

Rewrite using `[← e.tsum_eq (fun x => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))))]`. Conclude with `tsum_congr fun X => by rw [he X]`. Establish `hfin : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J) (ratTup (F` using `F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ≠ ⊤ := by`. Introduce `h`. Establish `hF` using `hFT F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet (fun X => (φ X : ℂ)) hadm h`.

Rewrite using `[hθS h]`. Use `ENNReal.tsum_coe_ne_top_iff_summable.2 (summable_of_finite_support ?_)` and prove the remaining obligations. Use `(hF.preimage Subtype.val_injective.injOn).subset ?_` and prove the remaining obligations. Introduce `X hX`. Simplify using `only [Function.mem_support, ne_eq, Real.toNNReal_eq_zero, not_le] at hX`.

Use `show (φ _ : ℂ) ≠ 0`. Conclude with `Complex.ofReal_ne_zero.2 hX.ne'`. Establish `hθm : Measurable fun h : HA (AF F) σ J => ∑' x : orbS (GamA σ J) (ratTup (F` using `F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) := by`. Use `Measurable.ennreal_tsum fun x => ?_` and prove the remaining obligations. Establish `hx : (fun h : HA (AF F) σ J => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))) = fun h => ENNReal.ofReal (φ ((h⁻¹ * repO _ _ x) • ratTup (F` using `F) (AF F) X0)) := by`.

Use function extensionality and compare the values at `h`. Rewrite using `[mul_smul, repO_smul]`. Rewrite using `[hx]`. Conclude with `(hmφ.comp (measurable_inv.mul_const _)).ennreal_ofReal`. Establish `hθeq : ∀ h, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h = (((∑' x : orbS (GamA σ J) (ratTup (F` using `F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))).toReal : ℝ) : ℂ) := by`.

Introduce `h`. Unfold `thetaS`. Rewrite using `[← Complex.ofReal_tsum, hθS h, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]`. Use `congr 1`. Conclude with `tsum_congr fun X => (ENNReal.toReal_ofReal (hφ0 _)).symm`.

Establish `hI1 : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h ∂μ = (((∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J) (ratTup (F` using `F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ).toReal : ℝ) : ℂ) := by`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall hθeq), integral_complex_ofReal, integral_toReal hθm.aemeasurable (Filter.Eventually.of_forall fun h => (hfin h).lt_top)]`. Establish `hI2 : ∫ X, (φ X : ℂ) ∂νX = (((∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal : ℝ) : ℂ)`. Rewrite using `[integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0) hφae.aestronglyMeasurable]`. Rewrite `hθ`, the goal using `[hI1]`.

Rewrite using `[hI2, key]`. Rewrite `hθ` using `[key]`. Establish `hL0 : (μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal ≠ 0` using `fun h0 => hθ (by rw [h0]; simp)`. Establish `hR0 : ∫⁻ X, ENNReal.ofReal (φ X) ∂νX ≠ 0` using `fun h => hL0 (by simp [h])`. Establish `hμ'top : μ' 𝓕' ≠ ⊤` using `fun h => hL0 (by rw [h, ENNReal.top_mul hR0]; simp)`.

Use `⟨hμ'top, ?_⟩` and prove the remaining obligations. Rewrite using `[ENNReal.toReal_mul, Complex.ofReal_mul, Complex.real_smul]`.
-/
theorem unfold_of (hW : Witt) (hFT : FinTheta) (hI : InvInv) (hMO : MeasOrb) (hMG : MeasGrp) :
    Unfold := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C
    𝓕' h𝓕' φ hφ0 hadm hθ
  haveI : MeasurableMul (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  haveI : MeasurableInv (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2
  haveI : μ.IsHaarMeasure := hμ
  haveI : μ'.IsHaarMeasure := hμ'H
  haveI : μ.IsInvInvariant := (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1 μ hμ
  haveI : μ'.IsInvInvariant :=
    (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2 ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  haveI : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J
  haveI hΓc : Countable (GamA σ J) := um_countable_HFinIn F E σ M J
  obtain ⟨e, he⟩ := gram_orbit_equiv σ J X0 (hW F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet)
  have hsub : orbS (GamA σ J) (ratTup (F := F) (AF F) X0) ⊆
      Set.range (fun γ : (GamA σ J) =>
        (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) X0) := by
    rintro x ⟨γ, hγ, e⟩
    exact ⟨⟨γ, hγ⟩, e⟩
  haveI hcO : Countable (orbS (GamA σ J)
      (ratTup (F := F) (AF F) X0)) := ((Set.countable_range _).mono hsub).to_subtype
  have hmφ : Measurable fun g : HA (AF F) σ J => φ (g • ratTup (F := F) (AF F) X0) := by
    have := hMO F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet _ hadm
    have h2 := Complex.measurable_re.comp this
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have hint : Integrable (fun X => (φ X : ℂ)) νX := by
    obtain ⟨d, b, Φinf, Φf, Φv, h1, h2, h3, h4⟩ := id hadm
    obtain ⟨⟨μinf, hμinf⟩, k1⟩ := hν.2
    obtain ⟨⟨νinf, hνinf⟩, k2⟩ := k1 μinf hμinf
    obtain ⟨⟨μv, hμv⟩, k3⟩ := k2 νinf hνinf
    obtain ⟨⟨νv, hνv⟩, k4⟩ := k3 μv hμv
    obtain ⟨⟨fI, hfI⟩, k5⟩ := k4 νv hνv
    obtain ⟨⟨fV, hfV⟩, k6⟩ := k5 fI hfI
    exact (k6 fV hfV d b _ Φinf Φf Φv h1 h2 h3 h4).1
  have hφae : AEMeasurable φ νX := by
    have h2 := Complex.measurable_re.comp_aemeasurable hint.aestronglyMeasurable.aemeasurable
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have key : ∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ =
      μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX :=
    unfold_abs (Γ := GamA σ J) (H := stabT (AF F) σ J X0) μ μ' (ratTup (F := F) (AF F) X0) (fun k => MulAction.mem_stabilizer_iff) νX
      (fun X => ENNReal.ofReal (φ X)) hφae.ennreal_ofReal hmφ.ennreal_ofReal hμ'C.1 hμ'C.2 𝓕 h𝓕 𝓕' h𝓕'
  have hθS : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) =
      ∑' X : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0},
        ENNReal.ofReal (φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin a → Fin M → E))) := by
    intro h
    rw [← e.tsum_eq (fun x => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))))]
    exact tsum_congr fun X => by rw [he X]
  have hfin : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ≠ ⊤ := by
    intro h
    have hF := hFT F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet (fun X => (φ X : ℂ)) hadm h
    rw [hθS h]
    refine ENNReal.tsum_coe_ne_top_iff_summable.2 (summable_of_finite_support ?_)
    refine (hF.preimage Subtype.val_injective.injOn).subset ?_
    intro X hX
    simp only [Function.mem_support, ne_eq, Real.toNNReal_eq_zero, not_le] at hX
    show (φ _ : ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.2 hX.ne'
  have hθm : Measurable fun h : HA (AF F) σ J => ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) := by
    refine Measurable.ennreal_tsum fun x => ?_
    have hx : (fun h : HA (AF F) σ J => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))) =
        fun h => ENNReal.ofReal (φ ((h⁻¹ * repO _ _ x) • ratTup (F := F) (AF F) X0)) := by
      funext h
      rw [mul_smul, repO_smul]
    rw [hx]
    exact (hmφ.comp (measurable_inv.mul_const _)).ennreal_ofReal
  have hθeq : ∀ h, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h =
      (((∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
        ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))).toReal : ℝ) : ℂ) := by
    intro h
    unfold thetaS
    rw [← Complex.ofReal_tsum, hθS h, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    congr 1
    exact tsum_congr fun X => (ENNReal.toReal_ofReal (hφ0 _)).symm
  have hI1 : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h ∂μ =
      (((∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ).toReal
          : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hθeq), integral_complex_ofReal,
      integral_toReal hθm.aemeasurable (Filter.Eventually.of_forall fun h => (hfin h).lt_top)]
  have hI2 : ∫ X, (φ X : ℂ) ∂νX = (((∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
      hφae.aestronglyMeasurable]
  rw [hI1] at hθ ⊢
  rw [hI2, key]
  rw [key] at hθ
  have hL0 : (μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal ≠ 0 := fun h0 => hθ (by rw [h0]; simp)
  have hR0 : ∫⁻ X, ENNReal.ofReal (φ X) ∂νX ≠ 0 := fun h => hL0 (by simp [h])
  have hμ'top : μ' 𝓕' ≠ ⊤ := fun h => hL0 (by rw [h, ENNReal.top_mul hR0]; simp)
  refine ⟨hμ'top, ?_⟩
  rw [ENNReal.toReal_mul, Complex.ofReal_mul, Complex.real_smul]

end Of

end PI.VolStabS
