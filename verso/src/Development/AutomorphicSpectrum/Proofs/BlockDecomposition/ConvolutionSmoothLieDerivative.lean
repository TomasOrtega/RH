import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffIntegralDensity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupport
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def psi (v : GA E a) : Lie E a := toL (GeneralLinearGroup.map (pInf E) v⁻¹).val

def wt (U : Subgroup (GL (Fin a) (Af E))) (F : GA E a → ℂ) (g : GA E a) : GA E a → ℂ :=
  Set.indicator {v | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U} fun v => F (g * v)

open Classical in

/- English proof (translation)
Simplify using `only [wt, Set.indicator_apply, Set.mem_setOf_eq]`.
-/
theorem wt_apply (U : Subgroup (GL (Fin a) (Af E))) (F : GA E a → ℂ) (g v : GA E a) :
    wt U F g v = if GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U then F (g * v) else 0 := by
  simp only [wt, Set.indicator_apply, Set.mem_setOf_eq]

def hb (β : Lie E a → ℂ) (q : Lie E a × Lie E a) : ℂ := β (toL (Matrix.of q.2 * Matrix.of q.1))

/- English proof (translation)
The claim follows from `((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp ((ContAut.continuous_map_pInf E a).comp continuous_inv))`.
-/
theorem continuous_psi : Continuous (psi (E := E) (a := a)) :=
  ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp ((ContAut.continuous_map_pInf E a).comp continuous_inv))

/- English proof (translation)
Use `contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_` and prove the remaining obligations. Establish `e : (fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) i j) = fun q => ∑ k, q.2 i k * q.1 k j`. Use function extensionality and compare the values at `q`. Simplify using `[toL, Matrix.mul_apply]`. Rewrite using `[e]`.

Conclude with `ContDiff.sum fun k _ => ((contDiff_apply ℝ _ k).comp ((contDiff_apply ℝ _ i).comp contDiff_snd)).mul ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_fst))`.
-/
theorem contDiff_mul_lie : ContDiff ℝ ∞ fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e : (fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) i j) =
      fun q => ∑ k, q.2 i k * q.1 k j := by
    funext q; simp [toL, Matrix.mul_apply]
  rw [e]
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply ℝ _ k).comp ((contDiff_apply ℝ _ i).comp contDiff_snd)).mul
      ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_fst))

/- English proof (translation)
The claim follows from `hβ.comp contDiff_mul_lie`.
-/
theorem contDiff_hb {β : Lie E a → ℂ} (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (hb (E := E) (a := a) β) :=
  hβ.comp contDiff_mul_lie

end GlobalTheory.CompanionTheory.SmoothRep.TstConv

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Introduce `E _ _ _ a β hβ x₀ hx₀`. Take `⟨δ, hδ, hball⟩` from `Metric.isOpen_iff.1 (isOpen_invSet (E := E) (a := a)) x₀ hx₀`. Use `set N := Metric.closedBall x₀ (δ / 2)`. Establish `hNs : N ⊆ invSet E a` using `(Metric.closedBall_subset_ball (half_lt_self hδ)).trans hball`. Establish `hNc : IsCompact N` using `isCompact_closedBall x₀ (δ / 2)`.

Establish `hN'` using `isCompact_setOf_toL_mem (E := E) (a := a) hNc hNs`. Establish `hB'` using `isCompact_setOf_toL_mem (E := E) (a := a) hβ.compact hβ.support`. Establish `hcont : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Cinf E) => toL (p.1 * p.2⁻¹).val` using `(Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp (continuous_fst.mul continuous_snd.inv)`. Use `⟨_, (hB'.prod hN').image hcont, ?_, N, Metric.closedBall_mem_nhds x₀ (half_pos hδ), ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨p, -, rfl⟩`.

Conclude with `val_mem_invSet _`. Introduce `y x hx hm`. Take `⟨u, hu⟩` from `hNs hx`. Take `⟨b, hb⟩` from `hβ.support hm`. Use `⟨(b, u), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `toL b.val ∈ tsupport β`. Rewrite using `[hb]`. Conclude with `hm`. Express the relevant statement in the definitionally equal form `toL u.val ∈ N`. Rewrite using `[hu]`.

Conclude with `hx`. Express the relevant statement in the definitionally equal form `toL (b * u⁻¹).val = y`. Establish `e : (b * u⁻¹).val = Matrix.of y`. Rewrite using `[Units.val_mul, hb]`. Express the relevant statement in the definitionally equal form `Matrix.of y * Matrix.of x * u⁻¹.val = Matrix.of y`.

Rewrite using `[← hu, mul_assoc, Units.mul_inv, mul_one]`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem exists_compact_of_mul_mem_tsupport : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ), IsTest β →
    ∀ x₀ ∈ invSet E a, ∃ Kc : Set (Lie E a), IsCompact Kc ∧ Kc ⊆ invSet E a ∧ ∃ N ∈ 𝓝 x₀,
      ∀ y x : Lie E a, x ∈ N → toL (Matrix.of y * Matrix.of x) ∈ tsupport β → y ∈ Kc := by
  intro E _ _ _ a β hβ x₀ hx₀
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_invSet (E := E) (a := a)) x₀ hx₀
  set N := Metric.closedBall x₀ (δ / 2)
  have hNs : N ⊆ invSet E a := (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hball
  have hNc : IsCompact N := isCompact_closedBall x₀ (δ / 2)
  have hN' := isCompact_setOf_toL_mem (E := E) (a := a) hNc hNs
  have hB' := isCompact_setOf_toL_mem (E := E) (a := a) hβ.compact hβ.support
  have hcont : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Cinf E) => toL (p.1 * p.2⁻¹).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp (continuous_fst.mul continuous_snd.inv)
  refine ⟨_, (hB'.prod hN').image hcont, ?_, N, Metric.closedBall_mem_nhds x₀ (half_pos hδ), ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    exact val_mem_invSet _
  · intro y x hx hm
    obtain ⟨u, hu⟩ := hNs hx
    obtain ⟨b, hb⟩ := hβ.support hm
    refine ⟨(b, u), ⟨?_, ?_⟩, ?_⟩
    · change toL b.val ∈ tsupport β
      rw [hb]
      exact hm
    · change toL u.val ∈ N
      rw [hu]
      exact hx
    · change toL (b * u⁻¹).val = y
      have e : (b * u⁻¹).val = Matrix.of y := by
        rw [Units.val_mul, hb]
        change Matrix.of y * Matrix.of x * u⁻¹.val = Matrix.of y
        rw [← hu, mul_assoc, Units.mul_inv, mul_one]
      rw [e]
      rfl

/- English proof (translation)
Introduce `E _ _ _ a μ _ U hU hUc Fl hFl Kc hKc hKs g`. Establish `hS : IsOpen {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U}` using `hU.preimage ((ContAut.continuous_map_pFin E a).comp continuous_inv)`. Establish `hm : MeasurableSet {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc}` using `hS.measurableSet.inter (hKc.isClosed.preimage continuous_psi).measurableSet`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Establish `hK'` using `isCompact_setOf_toL_mem (E := E) (a := a) hKc hKs`.

Establish `hcont : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => (infGL E a p.1 * finGL E a p.2)⁻¹` using `((GlobalTheory.CuspQuot.continuous_infGL.comp continuous_fst).mul ((GlobalTheory.BlockLevel.continuous_finGL a).comp continuous_snd)).inv`. Establish `hD` using `(hK'.prod hUc).image hcont`. Establish `hCD : {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} ⊆ (fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => (infGL E a p.1 * finGL E a p.2)⁻¹) '' ({y : GL (Fin a) (Cinf E) | toL y.val ∈ Kc} ×ˢ (U : Set (GL (Fin a) (Af E))))`. Introduce and unpack `v ⟨hvU, hvK⟩`. Conclude with `⟨(GeneralLinearGroup.map (pInf E) v⁻¹, GeneralLinearGroup.map (pFin E) v⁻¹), ⟨hvK, hvU⟩, by simp only [infGL_mul_finGL, inv_inv]⟩`.

Establish `hDg` using `hD.image (continuous_const_mul g)`. Establish `hi : IntegrableOn (fun v => Fl (g * v)) ((fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => (infGL E a p.1 * finGL E a p.2)⁻¹) '' ({y : GL (Fin a) (Cinf E) | toL y.val ∈ Kc} ×ˢ (U : Set (GL (Fin a) (Af E))))) μ`. Use `((measurePreserving_mul_left μ g).integrableOn_comp_preimage (MeasurableEquiv.mulLeft g).measurableEmbedding).2 (hFl.integrableOn_isCompact hDg)` as an intermediate fact. Rewrite `this` using `[Set.preimage_image_eq _ (mul_right_injective g)]`. Then use the resulting hypothesis. Conclude with `(hi.mono_set hCD).indicator hS.measurableSet`.
-/
theorem measurableSet_integrableOn_wt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ Fl : GA E a → ℂ, LocallyIntegrable Fl μ →
    ∀ Kc : Set (Lie E a), IsCompact Kc → Kc ⊆ invSet E a → ∀ g : GA E a,
      MeasurableSet {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} ∧
      IntegrableOn (wt U Fl g) {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} μ := by
  intro E _ _ _ a μ _ U hU hUc Fl hFl Kc hKc hKs g
  have hS : IsOpen {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U} :=
    hU.preimage ((ContAut.continuous_map_pFin E a).comp continuous_inv)
  have hm : MeasurableSet {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} :=
    hS.measurableSet.inter (hKc.isClosed.preimage continuous_psi).measurableSet
  refine ⟨hm, ?_⟩
  have hK' := isCompact_setOf_toL_mem (E := E) (a := a) hKc hKs
  have hcont : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => (infGL E a p.1 * finGL E a p.2)⁻¹ :=
    ((GlobalTheory.CuspQuot.continuous_infGL.comp continuous_fst).mul
      ((GlobalTheory.BlockLevel.continuous_finGL a).comp continuous_snd)).inv
  have hD := (hK'.prod hUc).image hcont
  have hCD : {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} ⊆
      (fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => (infGL E a p.1 * finGL E a p.2)⁻¹) ''
        ({y : GL (Fin a) (Cinf E) | toL y.val ∈ Kc} ×ˢ (U : Set (GL (Fin a) (Af E)))) := by
    rintro v ⟨hvU, hvK⟩
    exact ⟨(GeneralLinearGroup.map (pInf E) v⁻¹, GeneralLinearGroup.map (pFin E) v⁻¹), ⟨hvK, hvU⟩,
      by simp only [infGL_mul_finGL, inv_inv]⟩
  have hDg := hD.image (continuous_const_mul g)
  have hi : IntegrableOn (fun v => Fl (g * v)) ((fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) =>
      (infGL E a p.1 * finGL E a p.2)⁻¹) '' ({y : GL (Fin a) (Cinf E) | toL y.val ∈ Kc} ×ˢ
        (U : Set (GL (Fin a) (Af E))))) μ := by
    have := ((measurePreserving_mul_left μ g).integrableOn_comp_preimage
      (MeasurableEquiv.mulLeft g).measurableEmbedding).2 (hFl.integrableOn_isCompact hDg)
    rwa [Set.preimage_image_eq _ (mul_right_injective g)] at this
  exact (hi.mono_set hCD).indicator hS.measurableSet

/- English proof (translation)
Rewrite using `[← integral_mul_left_eq_self (fun v => hb β (toL y.val, psi v) * wt U Fl g v) (infGL E a y)]`. Unfold `convR`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Establish `hf : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ = GeneralLinearGroup.map (pFin E) v⁻¹`. Simplify using `[_root_.mul_inv_rev, map_mul, map_inv]`.

Establish `hi : GeneralLinearGroup.map (pInf E) (infGL E a y * v)⁻¹ = GeneralLinearGroup.map (pInf E) v⁻¹ * y⁻¹`. Simplify using `[_root_.mul_inv_rev, map_mul, map_inv]`. Use `show _ = hb β (toL y.val, psi (infGL E a y * v)) * wt U Fl g (infGL E a y * v)`. Rewrite using `[wt_apply]`. Distinguish the cases in `h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U`.

Establish `h' : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ ∈ U` using `hf ▸ h`. Simplify using `only [tst, ker, if_pos h, if_pos h', hb, psi, hi]`. Simplify using `[toL, mul_assoc]`. Establish `h' : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ ∉ U` using `hf ▸ h`. Simplify using `only [tst, ker, if_neg h, if_neg h']`.

Simplify using the standard rewrite rules.
-/
theorem convR_tst_mul_infGL (μ : Measure (GA E a)) [μ.IsMulLeftInvariant] (U : Subgroup (GL (Fin a) (Af E)))
    (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    convR μ (tst U β) Fl (g * infGL E a y) = ∫ v, hb β (toL y.val, psi v) * wt U Fl g v ∂μ := by
  rw [← integral_mul_left_eq_self (fun v => hb β (toL y.val, psi v) * wt U Fl g v) (infGL E a y)]
  unfold convR
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hf : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ = GeneralLinearGroup.map (pFin E) v⁻¹ := by
    simp [_root_.mul_inv_rev, map_mul, map_inv]
  have hi : GeneralLinearGroup.map (pInf E) (infGL E a y * v)⁻¹ = GeneralLinearGroup.map (pInf E) v⁻¹ * y⁻¹ := by
    simp [_root_.mul_inv_rev, map_mul, map_inv]
  show _ = hb β (toL y.val, psi (infGL E a y * v)) * wt U Fl g (infGL E a y * v)
  rw [wt_apply]
  by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
  · have h' : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ ∈ U := hf ▸ h
    simp only [tst, ker, if_pos h, if_pos h', hb, psi, hi]
    simp [toL, mul_assoc]
  · have h' : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ ∉ U := hf ▸ h
    simp only [tst, ker, if_neg h, if_neg h']
    simp
end GlobalTheory.CompanionTheory.SmoothRep.TstConv

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Establish `e : (fun q => hb β (q, y)) = β ∘ lmul y` using `rfl`. Establish `e1 : lmul y (oneL E a) = y` using `mul_one (Matrix.of y)`. Rewrite using `[e, fderiv_comp _ (by rw [e1]; exact (hβ.differentiable (by simp)).differentiableAt) (lmul y).differentiableAt, e1, ContinuousLinearMap.fderiv]`. Both sides reduce to the same expression.
-/
theorem fderiv_hb_one {β : Lie E a → ℂ} (hβ : ContDiff ℝ ∞ β) (y X : Lie E a) :
    fderiv ℝ (fun q => hb β (q, y)) (oneL E a) X = dTest X β y := by
  have e : (fun q => hb β (q, y)) = β ∘ lmul y := rfl
  have e1 : lmul y (oneL E a) = y := mul_one (Matrix.of y)
  rw [e, fderiv_comp _ (by rw [e1]; exact (hβ.differentiable (by simp)).differentiableAt)
    (lmul y).differentiableAt, e1, ContinuousLinearMap.fderiv]
  rfl

/- English proof (translation)
Take `⟨Kc, hKc, hKs, N, hN, hNK⟩` from `exists_compact_of_mul_mem_tsupport E a β hβ x₀ hx₀`. Take `⟨hCm, hCi⟩` from `measurableSet_integrableOn_wt E a μ U hU hUc Fl hFl Kc hKc hKs g`. Conclude with `⟨_, Kc, N, hN, hCm, hKc, fun v hv => hv.2, hCi, fun v hv hvU x hx hm => hv ⟨hvU, hNK _ _ hx hm⟩⟩`.
-/
theorem exists_local {μ : Measure (GA E a)} [μ.IsHaarMeasure] {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ} (hFl : LocallyIntegrable Fl μ) (g : GA E a)
    {x₀ : Lie E a} (hx₀ : x₀ ∈ invSet E a) :
    ∃ C : Set (GA E a), ∃ K : Set (Lie E a), ∃ N ∈ 𝓝 x₀, MeasurableSet C ∧ IsCompact K ∧ (∀ v ∈ C, psi v ∈ K) ∧
      IntegrableOn (wt U Fl g) C μ ∧
      ∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N, toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β := by
  obtain ⟨Kc, hKc, hKs, N, hN, hNK⟩ := exists_compact_of_mul_mem_tsupport E a β hβ x₀ hx₀
  obtain ⟨hCm, hCi⟩ := measurableSet_integrableOn_wt E a μ U hU hUc Fl hFl Kc hKc hKs g
  exact ⟨_, Kc, N, hN, hCm, hKc, fun v hv => hv.2, hCi, fun v hv hvU x hx hm => hv ⟨hvU, hNK _ _ hx hm⟩⟩

/- English proof (translation)
Rewrite using `[wt_apply]`. Distinguish the cases in `h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U`. Rewrite using `[hb, image_eq_zero_of_notMem_tsupport (hC v hv h x hx), zero_mul]`. Rewrite using `[if_neg h, mul_zero]`.
-/
theorem integrand_eq_zero {U : Subgroup (GL (Fin a) (Af E))} {β : Lie E a → ℂ} {Fl : GA E a → ℂ} {g : GA E a}
    {C : Set (GA E a)} {N : Set (Lie E a)}
    (hC : ∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N, toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β)
    {x : Lie E a} (hx : x ∈ N) (v : GA E a) (hv : v ∉ C) : hb β (x, psi v) * wt U Fl g v = 0 := by
  rw [wt_apply]
  by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
  · rw [hb, image_eq_zero_of_notMem_tsupport (hC v hv h x hx), zero_mul]
  · rw [if_neg h, mul_zero]

end GlobalTheory.CompanionTheory.SmoothRep.TstConv

open GlobalTheory.CompanionTheory.SmoothRep.TstConv in

/- English proof (translation)
Introduce `E _ _ _ a μ _ _ U hU hUc β hβ Fl hFl`. Establish `hchart : ∀ g, ∀ x ∈ invSet E a, chart (convR μ (tst U β) Fl) g x = ∫ v, hb β (x, psi v) * wt U Fl g v ∂μ`. Introduce `g x hx`. Take `⟨u, hu⟩` from `id hx`. Establish `e : x = toL u.val` using `hu.symm`.

Substitute `e` using the available equality. Rewrite using `[chart_val, convR_tst_mul_infGL]`. Establish `hev : ∀ g, ∀ x ∈ invSet E a, chart (convR μ (tst U β) Fl) g =ᶠ[𝓝 x] fun x => ∫ v, hb β (x, psi v) * wt U Fl g v ∂μ` using `fun g x hx => Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) (hchart g)`. Establish `hloc : ∀ g, ∀ x₀ ∈ invSet E a, ∃ C : Set (GA E a), ∃ N ∈ 𝓝 x₀, (∀ x ∈ N, (∫ v, hb β (x, psi v) * wt U Fl g v ∂μ) = ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) ∧ ContDiff ℝ ∞ (fun x => ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) ∧ (∀ p X, fderiv ℝ (fun x => ∫ v in C, hb β (x, psi …`. Introduce `g x₀ hx₀`.

Take `⟨C, K, N, hN, hCm, hK, hCK, hCi, hvan⟩` from `exists_local hU hUc hβ hFl g hx₀`. Establish `P` using `GlobalTheory.CompanionTheory.SmoothParam.contDiff_integral_density (GA E a) (Lie E a) (Lie E a) (μ.restrict C) (wt U Fl g) psi K hCi continuous_psi.aestronglyMeasurable hK ((ae_restrict_iff' hCm).2 (Filter.Eventually.of_forall hCK)) (hb β) (contDiff_hb hβ.contDiff)`. Conclude with `⟨C, N, hN, fun x hx => (setIntegral_eq_integral_of_forall_compl_eq_zero (integrand_eq_zero hvan hx)).symm, P.1, P.2, hvan⟩`. Use `⟨fun g x hx => ?_, fun X g => ?_⟩` and prove the remaining obligations. Take `⟨C, N, hN, heq, hcd, -, -⟩` from `hloc g x hx`.

Conclude with `(hcd.contDiffAt.congr_of_eventuallyEq ((hev g x hx).trans (Filter.eventually_of_mem hN heq))).contDiffWithinAt`. Establish `h1 : oneL E a ∈ invSet E a` using `isUnit_one`. Take `⟨C, N, hN, heq, hcd, hder, hvan⟩` from `hloc g _ h1`. Rewrite using `[lieD, ((hev g _ h1).trans (Filter.eventually_of_mem hN heq)).fderiv_eq, hder]`. Repeatedly rewrite using `[fderiv_hb_one hβ.contDiff]`.

Rewrite using `[setIntegral_eq_integral_of_forall_compl_eq_zero ?_]`. Unfold `convR`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Use `show dTest X β (psi v) * wt U Fl g v = tst U (dTest X β) v * Fl (g * v)`. Rewrite using `[wt_apply]`.

Distinguish the cases in `h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U`. Simplify using `only [tst, ker, if_pos h, psi]`. Simplify using `only [tst, ker, if_neg h, mul_zero, zero_mul]`. Introduce `v hv`. Rewrite using `[wt_apply]`.

Distinguish the cases in `h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U`. Establish `hn : psi v ∉ tsupport β`. Use `hvan v hv h (oneL E a) (mem_of_mem_nhds hN)` as an intermediate fact. Simplify `this` using `[toL]`. Establish `h0 : fderiv ℝ β (psi v) = 0`.

Assume the negation of the conclusion as `h0`. Conclude with `hn (support_fderiv_subset ℝ h0)`. Rewrite using `[dTest, h0, ContinuousLinearMap.zero_apply, zero_mul]`. Rewrite using `[if_neg h, mul_zero]`.
-/
theorem GlobalTheory.CompanionTheory.SmoothRep.convR_tst_mem_Sm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ β : Lie E a → ℂ, IsTest β → ∀ Fl : GA E a → ℂ, LocallyIntegrable Fl μ → convR μ (tst U β) Fl ∈ Sm E a ∧ ∀ (X : Lie E a) (g : GA E a), lieD X (convR μ (tst U β) Fl) g = convR μ (tst U (dTest X β)) Fl g := by
  intro E _ _ _ a μ _ _ U hU hUc β hβ Fl hFl

  have hchart : ∀ g, ∀ x ∈ invSet E a,
      chart (convR μ (tst U β) Fl) g x = ∫ v, hb β (x, psi v) * wt U Fl g v ∂μ := by
    intro g x hx
    obtain ⟨u, hu⟩ := id hx
    have e : x = toL u.val := hu.symm
    subst e
    rw [chart_val, convR_tst_mul_infGL]
  have hev : ∀ g, ∀ x ∈ invSet E a, chart (convR μ (tst U β) Fl) g =ᶠ[𝓝 x]
      fun x => ∫ v, hb β (x, psi v) * wt U Fl g v ∂μ := fun g x hx =>
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) (hchart g)

  have hloc : ∀ g, ∀ x₀ ∈ invSet E a, ∃ C : Set (GA E a), ∃ N ∈ 𝓝 x₀,
      (∀ x ∈ N, (∫ v, hb β (x, psi v) * wt U Fl g v ∂μ) = ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) ∧
      ContDiff ℝ ∞ (fun x => ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) ∧
      (∀ p X, fderiv ℝ (fun x => ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) p X =
        ∫ v in C, fderiv ℝ (fun q => hb β (q, psi v)) p X * wt U Fl g v ∂μ) ∧
      (∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N,
        toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β) := by
    intro g x₀ hx₀
    obtain ⟨C, K, N, hN, hCm, hK, hCK, hCi, hvan⟩ := exists_local hU hUc hβ hFl g hx₀
    have P := GlobalTheory.CompanionTheory.SmoothParam.contDiff_integral_density (GA E a) (Lie E a) (Lie E a) (μ.restrict C)
      (wt U Fl g) psi K hCi continuous_psi.aestronglyMeasurable hK
      ((ae_restrict_iff' hCm).2 (Filter.Eventually.of_forall hCK)) (hb β) (contDiff_hb hβ.contDiff)
    exact ⟨C, N, hN, fun x hx => (setIntegral_eq_integral_of_forall_compl_eq_zero
      (integrand_eq_zero hvan hx)).symm, P.1, P.2, hvan⟩
  refine ⟨fun g x hx => ?_, fun X g => ?_⟩
  · obtain ⟨C, N, hN, heq, hcd, -, -⟩ := hloc g x hx
    exact (hcd.contDiffAt.congr_of_eventuallyEq
      ((hev g x hx).trans (Filter.eventually_of_mem hN heq))).contDiffWithinAt
  · have h1 : oneL E a ∈ invSet E a := isUnit_one
    obtain ⟨C, N, hN, heq, hcd, hder, hvan⟩ := hloc g _ h1
    rw [lieD, ((hev g _ h1).trans (Filter.eventually_of_mem hN heq)).fderiv_eq, hder]
    simp_rw [fderiv_hb_one hβ.contDiff]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero ?_]
    · unfold convR
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      show dTest X β (psi v) * wt U Fl g v = tst U (dTest X β) v * Fl (g * v)
      rw [wt_apply]
      by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
      · simp only [tst, ker, if_pos h, psi]
      · simp only [tst, ker, if_neg h, mul_zero, zero_mul]
    · intro v hv
      rw [wt_apply]
      by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
      · have hn : psi v ∉ tsupport β := by
          have := hvan v hv h (oneL E a) (mem_of_mem_nhds hN)
          simpa [toL] using this
        have h0 : fderiv ℝ β (psi v) = 0 := by
          by_contra h0
          exact hn (support_fderiv_subset ℝ h0)
        rw [dTest, h0, ContinuousLinearMap.zero_apply, zero_mul]
      · rw [if_neg h, mul_zero]
