import Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

/- English proof (translation)
Conclude with `Submodule.subset_span ⟨f, φ, hφ, rfl⟩`.
-/
theorem pureA_mem {κ : Type} [Fintype κ] (f : SInf F κ) {φ : (κ → Af F) → ℂ} (hφ : φ ∈ SB _) : pureA F f φ ∈ schA F κ := by
  exact Submodule.subset_span ⟨f, φ, hφ, rfl⟩

/- English proof (translation)
Establish `hpres : ∀ Φ' ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om (g, h) Φ' ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)`. Introduce `Φ' hΦ'`. Establish `e : (g, h) = ((g, 1) : _ × _) * (1, h)` using `by simp`. Take `⟨d', -, hB2⟩` from `hp.weil.2.1`. Establish `h1` using `hp.weil.1.1.toIsSplitting.pres h Φ' hΦ'`.

Establish `h2` using `hB2.1.toIsSplitting.pres g _ h1`. Rewrite using `[e, map_mul]`. Conclude with `h2`. Unfold `theta`. Rewrite using `[map_add]`.

Conclude with `GlobalTheory.WeilM.thetaSum_add F (hpres Φ hΦ) (hpres Ψ hΨ)`.
-/
theorem theta_add (hp : IsPair B M χX χW om r s r' s') {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _) (g h) :
    theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := by
  have hpres : ∀ Φ' ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om (g, h) Φ' ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := by
    intro Φ' hΦ'
    have e : (g, h) = ((g, 1) : _ × _) * (1, h) := by simp
    obtain ⟨d', -, hB2⟩ := hp.weil.2.1
    have h1 := hp.weil.1.1.toIsSplitting.pres h Φ' hΦ'
    have h2 := hB2.1.toIsSplitting.pres g _ h1
    rw [e, map_mul]
    exact h2
  unfold theta
  rw [map_add]
  exact GlobalTheory.WeilM.thetaSum_add F (hpres Φ hΦ) (hpres Ψ hΨ)

/- English proof (translation)
Unfold `theta`. Rewrite using `[map_smul, GlobalTheory.WeilM.thetaSum_smul]`.
-/
theorem theta_smul (hp : IsPair B M χX χW om r s r' s') (c : ℂ) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) (g h) :
    theta om (c • Φ) g h = c * theta om Φ g h := by
  unfold theta
  rw [map_smul, GlobalTheory.WeilM.thetaSum_smul]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp [theta, GlobalTheory.WeilM.thetaSum]`. Consider the case `@insert a S ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, theta_add hp (hΦ a) (Submodule.sum_mem _ fun i _ => hΦ i), ih]`.
-/
theorem theta_sum (hp : IsPair B M χX χW om r s r' s') {ι : Type} (S : Finset ι) {Φ : ι → Fn F n d}
    (hΦ : ∀ i, Φ i ∈ schA F _) (g h) : theta om (∑ i ∈ S, Φ i) g h = ∑ i ∈ S, theta om (Φ i) g h := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [theta, GlobalTheory.WeilM.thetaSum]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      theta_add hp (hΦ a) (Submodule.sum_mem _ fun i _ => hΦ i), ih]

/- English proof (translation)
Take `⟨p, k, G, hpc, hGm, hGi, hbd⟩` from `hD φ hφ`. Establish `hmem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d)` using `fun f => pureA_mem f hsb`. Take `⟨hth, hcf⟩` from `hB F E σ B n d X W M χX χW om r s r' s' hp`. Establish `: OpensMeasurableSpace (UA σ X.J)` using `⟨le_rfl⟩`. Establish `hGfin : ∀ᵐ g ∂(M.μ.restrict M.dom), G g < ⊤` using `ae_lt_top hGm hGi.ne`.

Establish `hGint : Integrable (fun g => (G g).toReal) (M.μ.restrict M.dom)` using `integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hGi.ne`. Establish `hmeas : ∀ (f : SInf F (Fin n × Fin d)) (h : UA σ W.J), AEStronglyMeasurable (fun g => theta om (pureA F f φ) g h) (M.μ.restrict M.dom)` using `fun f h => ((hth _ (hmem f)).1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable`. Establish `hnb : ∀ (f : SInf F (Fin n × Fin d)) (h : UA σ W.J), ∀ᵐ g ∂(M.μ.restrict M.dom), ‖theta om (pureA F f φ) g h‖ ≤ p f * (ht h : ℝ) ^ k * (G g).toReal`. Introduce `f h`. Use `filter_upwards [hGfin] with g hg`.

Establish `h1` using `hbd f g h`. Establish `h2 : 0 ≤ p f * (ht h : ℝ) ^ k` using `mul_nonneg (apply_nonneg p f) (by positivity)`. Establish `h3` using `ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.ne) h1`. Rewrite `h3` using `[toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal h2]`. Then use the resulting hypothesis. Use `⟨fun f => ⟨fun h => ?_, p f * (∫ g in M.dom, (G g).toReal ∂M.μ), k, fun h => ?_⟩, fun h => ?_⟩` and prove the remaining obligations.

Conclude with `Integrable.mono' (hGint.const_mul (p f * (ht h : ℝ) ^ k)) (hmeas f h) (hnb f h)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `f₀`. Use `show ContinuousAt (fun f : SInf F (Fin n × Fin d) => ∫ g in M.dom, theta om (pureA F f φ) g h ∂M.μ) f₀`. Establish `hev : ∀ᶠ f in 𝓝 f₀, p f < p f₀ + 1` using `(hpc.tendsto f₀).eventually (gt_mem_nhds (lt_add_one _))`. Apply `continuousAt_of_dominated (bound := fun g => (p f₀ + 1) * (ht h : ℝ) ^ k * (G g).toReal)` to reduce the goal to its premises. Conclude with `Filter.Eventually.of_forall fun f => hmeas f h`.

Use `filter_upwards [hev] with f hf filter_upwards [hnb f h] with g hg`. Conclude with `hg.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf.le (by positivity)) ENNReal.toReal_nonneg)`. Conclude with `hGint.const_mul _`. Conclude with `Filter.Eventually.of_forall fun g => (hcf φ hsb g h).continuousAt`.
-/
theorem dom_facts (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕)
    (hsb : φ ∈ SB _) :
    (∀ f : SInf F (Fin n × Fin d), M.Conv om (pureA F f φ) ∧
      ∃ (C : ℝ) (k : ℕ), ∀ h, ∫ g in M.dom, ‖theta om (pureA F f φ) g h‖ ∂M.μ ≤ C * (ht h : ℝ) ^ k) ∧
    ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f φ) h := by
  obtain ⟨p, k, G, hpc, hGm, hGi, hbd⟩ := hD φ hφ
  have hmem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f => pureA_mem f hsb
  obtain ⟨hth, hcf⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp
  have : OpensMeasurableSpace (UA σ X.J) := ⟨le_rfl⟩
  have hGfin : ∀ᵐ g ∂(M.μ.restrict M.dom), G g < ⊤ := ae_lt_top hGm hGi.ne
  have hGint : Integrable (fun g => (G g).toReal) (M.μ.restrict M.dom) :=
    integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hGi.ne
  have hmeas : ∀ (f : SInf F (Fin n × Fin d)) (h : UA σ W.J),
      AEStronglyMeasurable (fun g => theta om (pureA F f φ) g h) (M.μ.restrict M.dom) :=
    fun f h => ((hth _ (hmem f)).1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hnb : ∀ (f : SInf F (Fin n × Fin d)) (h : UA σ W.J), ∀ᵐ g ∂(M.μ.restrict M.dom),
      ‖theta om (pureA F f φ) g h‖ ≤ p f * (ht h : ℝ) ^ k * (G g).toReal := by
    intro f h
    filter_upwards [hGfin] with g hg
    have h1 := hbd f g h
    have h2 : 0 ≤ p f * (ht h : ℝ) ^ k := mul_nonneg (apply_nonneg p f) (by positivity)
    have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.ne) h1
    rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal h2] at h3
  refine ⟨fun f => ⟨fun h => ?_, p f * (∫ g in M.dom, (G g).toReal ∂M.μ), k, fun h => ?_⟩, fun h => ?_⟩
  · exact Integrable.mono' (hGint.const_mul (p f * (ht h : ℝ) ^ k)) (hmeas f h) (hnb f h)
  · calc ∫ g in M.dom, ‖theta om (pureA F f φ) g h‖ ∂M.μ
        ≤ ∫ g in M.dom, p f * (ht h : ℝ) ^ k * (G g).toReal ∂M.μ :=
          integral_mono_ae ((Integrable.mono' (hGint.const_mul _) (hmeas f h) (hnb f h)).norm)
            (hGint.const_mul _) (hnb f h)
      _ = p f * (∫ g in M.dom, (G g).toReal ∂M.μ) * (ht h : ℝ) ^ k := by
          rw [integral_const_mul]
          ring
  · rw [continuous_iff_continuousAt]
    intro f₀
    show ContinuousAt (fun f : SInf F (Fin n × Fin d) => ∫ g in M.dom, theta om (pureA F f φ) g h ∂M.μ) f₀
    have hev : ∀ᶠ f in 𝓝 f₀, p f < p f₀ + 1 := (hpc.tendsto f₀).eventually (gt_mem_nhds (lt_add_one _))
    apply continuousAt_of_dominated (bound := fun g => (p f₀ + 1) * (ht h : ℝ) ^ k * (G g).toReal)
    · exact Filter.Eventually.of_forall fun f => hmeas f h
    · filter_upwards [hev] with f hf
      filter_upwards [hnb f h] with g hg
      exact hg.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf.le (by positivity))
        ENNReal.toReal_nonneg)
    · exact hGint.const_mul _
    · exact Filter.Eventually.of_forall fun g => (hcf φ hsb g h).continuousAt

/- English proof (translation)
Use `choose C k hC using ha`. Use `⟨∑ i, |C i|, ∑ i, k i, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Establish `h1 : 1 ≤ w (π y)` using `hw _`.

Establish `h2 : w (π y) ^ k i ≤ w (π y) ^ (∑ j, k j)` using `pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))`. Establish `h3 : 0 ≤ w (π y) ^ k i` using `pow_nonneg (by linarith) _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_common {G ι : Type} [Fintype ι] (w : G → ℝ) (hw : ∀ g, 1 ≤ w g) {Y : Type} (π : Y → G) (a : ι → Y → ℝ)
    (ha : ∀ i, ∃ (C : ℝ) (k : ℕ), ∀ y, a i y ≤ C * w (π y) ^ k) : ∃ (C : ℝ) (k : ℕ), ∀ y, ∑ i, a i y ≤ C * w (π y) ^ k := by
  choose C k hC using ha
  refine ⟨∑ i, |C i|, ∑ i, k i, fun y => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : 1 ≤ w (π y) := hw _
  have h2 : w (π y) ^ k i ≤ w (π y) ^ (∑ j, k j) :=
    pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))
  have h3 : 0 ≤ w (π y) ^ k i := pow_nonneg (by linarith) _
  calc a i y ≤ C i * w (π y) ^ k i := hC i y
    _ ≤ |C i| * w (π y) ^ k i := mul_le_mul_of_nonneg_right (le_abs_self _) h3
    _ ≤ |C i| * w (π y) ^ (∑ j, k j) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

/- English proof (translation)
Conclude with `GlobalTheory.AdelicU.one_le_heightGL F _` after adjusting the coercions.
-/
theorem one_le_ht' {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : (1 : ℝ) ≤ ht g := by
  exact_mod_cast GlobalTheory.AdelicU.one_le_heightGL F _

/- English proof (translation)
Establish `hmem : ∀ i, pureA F (f i) (φ i) ∈ schA F (Fin n × Fin d)` using `fun i => pureA_mem (f i) (hsb i)`. Establish `hfac` using `fun i => dom_facts hB hp hD (hφ i) (hsb i)`. Establish `hconv : ∀ i, M.Conv om (pureA F (f i) (φ i))` using `fun i => ((hfac i).1 (f i)).1`. Establish `hsum : ∀ g h, theta om (∑ i, pureA F (f i) (φ i)) g h = ∑ i, theta om (pureA F (f i) (φ i)) g h` using `fun g h => theta_sum hp Finset.univ hmem g h`. Use `⟨fun h => ?_, ?_, fun h => ?_⟩` and prove the remaining obligations.

Establish `e : (fun g => theta om (∑ i, pureA F (f i) (φ i)) g h) = fun g => ∑ i, theta om (pureA F (f i) (φ i)) g h` using `funext fun g => hsum g h show IntegrableOn (fun g => theta om (∑ i, pureA F (f i) (φ i)) g h) M.dom M.μ`. Rewrite using `[e]`. Conclude with `integrable_finset_sum _ fun i _ => hconv i h`. Take `⟨C, k, hCk⟩` from `exists_common (fun h : UA σ W.J => (ht h : ℝ)) (fun h => one_le_ht' h) id (fun i h => ∫ g in M.dom, ‖theta om (pureA F (f i) (φ i)) g h‖ ∂M.μ) (fun i => ((hfac i).1 (f i)).2)`. Use `⟨C, k, fun h => le_trans ?_ (hCk h)⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => norm_nonneg _) (integrable_finset_sum _ fun i _ => (hconv i h).norm) (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Use `show ‖theta om (∑ i, pureA F (f i) (φ i)) g h‖ ≤ ∑ i, ‖theta om (pureA F (f i) (φ i)) g h‖`. Rewrite using `[hsum]`. Conclude with `norm_sum_le _ _`.

Use `_ = ∑ i, ∫ g in M.dom, ‖theta om (pureA F (f i) (φ i)) g h‖ ∂M.μ := integral_finset_sum _ fun i _ => (hconv i h).norm`. Use `show ∫ g in M.dom, theta om (∑ i, pureA F (f i) (φ i)) g h ∂M.μ = ∑ i, ∫ g in M.dom, theta om (pureA F (f i) (φ i)) g h ∂M.μ`. Repeatedly rewrite using `[hsum]`. Conclude with `integral_finset_sum _ fun i _ => hconv i h`.
-/
theorem dom_sum (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {m : ℕ}
    (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ) (hφ : ∀ i, φ i ∈ 𝓕) (hsb : ∀ i, φ i ∈ SB _) :
    M.Conv om (∑ i, pureA F (f i) (φ i)) ∧
    (∃ (C : ℝ) (k : ℕ), ∀ h, ∫ g in M.dom, ‖theta om (∑ i, pureA F (f i) (φ i)) g h‖ ∂M.μ ≤ C * (ht h : ℝ) ^ k) ∧
    ∀ h, M.I om (∑ i, pureA F (f i) (φ i)) h = ∑ i, M.I om (pureA F (f i) (φ i)) h := by
  have hmem : ∀ i, pureA F (f i) (φ i) ∈ schA F (Fin n × Fin d) := fun i => pureA_mem (f i) (hsb i)
  have hfac := fun i => dom_facts hB hp hD (hφ i) (hsb i)
  have hconv : ∀ i, M.Conv om (pureA F (f i) (φ i)) := fun i => ((hfac i).1 (f i)).1
  have hsum : ∀ g h, theta om (∑ i, pureA F (f i) (φ i)) g h = ∑ i, theta om (pureA F (f i) (φ i)) g h :=
    fun g h => theta_sum hp Finset.univ hmem g h
  refine ⟨fun h => ?_, ?_, fun h => ?_⟩
  · have e : (fun g => theta om (∑ i, pureA F (f i) (φ i)) g h) =
        fun g => ∑ i, theta om (pureA F (f i) (φ i)) g h := funext fun g => hsum g h
    show IntegrableOn (fun g => theta om (∑ i, pureA F (f i) (φ i)) g h) M.dom M.μ
    rw [e]
    exact integrable_finset_sum _ fun i _ => hconv i h
  · obtain ⟨C, k, hCk⟩ := exists_common (fun h : UA σ W.J => (ht h : ℝ)) (fun h => one_le_ht' h) id
      (fun i h => ∫ g in M.dom, ‖theta om (pureA F (f i) (φ i)) g h‖ ∂M.μ) (fun i => ((hfac i).1 (f i)).2)
    refine ⟨C, k, fun h => le_trans ?_ (hCk h)⟩
    calc ∫ g in M.dom, ‖theta om (∑ i, pureA F (f i) (φ i)) g h‖ ∂M.μ
        ≤ ∫ g in M.dom, ∑ i, ‖theta om (pureA F (f i) (φ i)) g h‖ ∂M.μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => norm_nonneg _)
            (integrable_finset_sum _ fun i _ => (hconv i h).norm) (Filter.Eventually.of_forall fun g => ?_)
          show ‖theta om (∑ i, pureA F (f i) (φ i)) g h‖ ≤ ∑ i, ‖theta om (pureA F (f i) (φ i)) g h‖
          rw [hsum]
          exact norm_sum_le _ _
      _ = ∑ i, ∫ g in M.dom, ‖theta om (pureA F (f i) (φ i)) g h‖ ∂M.μ :=
          integral_finset_sum _ fun i _ => (hconv i h).norm
  · show ∫ g in M.dom, theta om (∑ i, pureA F (f i) (φ i)) g h ∂M.μ =
      ∑ i, ∫ g in M.dom, theta om (pureA F (f i) (φ i)) g h ∂M.μ
    simp_rw [hsum]
    exact integral_finset_sum _ fun i _ => hconv i h

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp hc`. Establish `hDom` using `hD F E σ B n d X W M χX χW om r s r' s' hp hc`. Take `⟨-, hsch, -, -⟩` from `hF F E σ B n d X W M χX χW om r s r' s' hp`. Use `⟨fun Φ hΦ => ?_, fun φ hφ h => (dom_facts hB hp hDom hφ hφ).2 h⟩` and prove the remaining obligations. Take `⟨m, f, φ, hφ, rfl⟩` from `hsch Φ hΦ`.

Take `⟨h1, h2, -⟩` from `dom_sum hB hp hDom f φ hφ hφ`. Conclude with `⟨h1, h2⟩`.
-/
theorem weilConv_of (hB : ThetaBasic) (hD : DomWeil) (hF : SoFin) : WeilConv := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp hc
  have hDom := hD F E σ B n d X W M χX χW om r s r' s' hp hc
  obtain ⟨-, hsch, -, -⟩ := hF F E σ B n d X W M χX χW om r s r' s' hp
  refine ⟨fun Φ hΦ => ?_, fun φ hφ h => (dom_facts hB hp hDom hφ hφ).2 h⟩
  obtain ⟨m, f, φ, hφ, rfl⟩ := hsch Φ hΦ
  obtain ⟨h1, h2, -⟩ := dom_sum hB hp hDom f φ hφ hφ
  exact ⟨h1, h2⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp Φ hΦ N`. Take `⟨hSo, -, -, -⟩` from `hF F E σ B n d X W M χX χW om r s r' s' hp`. Take `⟨m, f, φ, hφ, rfl⟩` from `hSo Φ hΦ`. Establish `hb : ∀ i, ∃ (C : ℝ) (k : ℕ), ∀ y : UA σ X.J × UA σ W.J, ‖theta om (pureA F (f i) (φ i)) y.1 y.2‖ * (qht y.1 : ℝ) ^ N ≤ C * (fun h : UA σ W.J => (ht h : ℝ)) y.2 ^ k`. Introduce `i`.

Take `⟨p, k, -, hpk⟩` from `hS F E σ B n d X W M χX χW om r s r' s' hp (φ i) (hφ i) N`. Conclude with `⟨p (f i), k, fun y => hpk (f i) y.1 y.2⟩`. Take `⟨C, k, hCk⟩` from `exists_common (fun h : UA σ W.J => (ht h : ℝ)) (fun h => one_le_ht' h) Prod.snd (fun i y => ‖theta om (pureA F (f i) (φ i)) y.1 y.2‖ * (qht y.1 : ℝ) ^ N) hb`. Use `⟨C, k, fun g h => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ i, pureA F (f i) (φ i) ∈ schA F (Fin n × Fin d)` using `fun i => pureA_mem (f i) (hφ i).1`.

Rewrite using `[theta_sum hp Finset.univ hmem]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem soDecay_of (hS : SoSemi) (hF : SoFin) : SoDecay := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp Φ hΦ N
  obtain ⟨hSo, -, -, -⟩ := hF F E σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨m, f, φ, hφ, rfl⟩ := hSo Φ hΦ
  have hb : ∀ i, ∃ (C : ℝ) (k : ℕ), ∀ y : UA σ X.J × UA σ W.J,
      ‖theta om (pureA F (f i) (φ i)) y.1 y.2‖ * (qht y.1 : ℝ) ^ N ≤ C * (fun h : UA σ W.J => (ht h : ℝ)) y.2 ^ k := by
    intro i
    obtain ⟨p, k, -, hpk⟩ := hS F E σ B n d X W M χX χW om r s r' s' hp (φ i) (hφ i) N
    exact ⟨p (f i), k, fun y => hpk (f i) y.1 y.2⟩
  obtain ⟨C, k, hCk⟩ := exists_common (fun h : UA σ W.J => (ht h : ℝ)) (fun h => one_le_ht' h) Prod.snd
    (fun i y => ‖theta om (pureA F (f i) (φ i)) y.1 y.2‖ * (qht y.1 : ℝ) ^ N) hb
  refine ⟨C, k, fun g h => ?_⟩
  have hmem : ∀ i, pureA F (f i) (φ i) ∈ schA F (Fin n × Fin d) := fun i => pureA_mem (f i) (hφ i).1
  rw [theta_sum hp Finset.univ hmem]
  calc ‖∑ i, theta om (pureA F (f i) (φ i)) g h‖ * (qht g : ℝ) ^ N
      ≤ (∑ i, ‖theta om (pureA F (f i) (φ i)) g h‖) * (qht g : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = ∑ i, ‖theta om (pureA F (f i) (φ i)) g h‖ * (qht g : ℝ) ^ N := Finset.sum_mul _ _ _
    _ ≤ C * (ht h : ℝ) ^ k := hCk (g, h)

/- English proof (translation)
Take `⟨k, hk⟩` from `hD F E σ B n d X W M χX χW om r s r' s' hp`. Introduce `φ hφ`. Take `⟨p, G, hpc, hG, hGi, hb⟩` from `hk φ hφ`. Conclude with `⟨p, k, G, hpc, hG, hGi, hb⟩`.
-/
theorem dom_of_domSoU (hD : DomSoU) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hp : IsPair B M χX χW om r s r' s') : Dom M om (soFin B M) := by
  obtain ⟨k, hk⟩ := hD F E σ B n d X W M χX χW om r s r' s' hp
  intro φ hφ
  obtain ⟨p, G, hpc, hG, hGi, hb⟩ := hk φ hφ
  exact ⟨p, k, G, hpc, hG, hGi, hb⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT3`. Take `⟨hp1, hp2, hdim⟩` from `hT F E σ B a a' G X om om' hT3`. Establish `hW1` using `hW F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hp1 (Or.inl hdim)`. Use `⟨fun Φ hΦ => (hW1.1 Φ hΦ).1, fun Φ' hΦ' => ?_⟩` and prove the remaining obligations. Take `⟨hSo, -, -, -⟩` from `hF F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hp2`.

Take `⟨m, f, φ, hφ, rfl⟩` from `hSo Φ' hΦ'`. Take `⟨hconv, ⟨C, k, hb⟩, -⟩` from `dom_sum hB hp2 (dom_of_domSoU hD hp2) f φ hφ (fun i => (hφ i).1)`. Use `⟨fun N => hS F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hp2 _ hΦ' N, hconv, C, k, fun h => ?_⟩` and prove the remaining obligations. Conclude with `(norm_integral_le_integral_norm _).trans (hb h)`.
-/
theorem kDecay_of (hB : ThetaBasic) (hT : TriplePair) (hW : WeilConv) (hS : SoDecay) (hD : DomSoU) (hF : SoFin) : KDecay := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT3
  obtain ⟨hp1, hp2, hdim⟩ := hT F E σ B a a' G X om om' hT3
  have hW1 := hW F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hp1 (Or.inl hdim)
  refine ⟨fun Φ hΦ => (hW1.1 Φ hΦ).1, fun Φ' hΦ' => ?_⟩
  obtain ⟨hSo, -, -, -⟩ := hF F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hp2
  obtain ⟨m, f, φ, hφ, rfl⟩ := hSo Φ' hΦ'
  obtain ⟨hconv, ⟨C, k, hb⟩, -⟩ := dom_sum hB hp2 (dom_of_domSoU hD hp2) f φ hφ (fun i => (hφ i).1)
  refine ⟨fun N => hS F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hp2 _ hΦ' N, hconv,
    C, k, fun h => ?_⟩
  exact (norm_integral_le_integral_norm _).trans (hb h)

def soCoeff {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {m : ℕ}
    (φ : Fin m → (Fin n × Fin d → Af F) → ℂ) : Submodule ℂ (Fin m → ℂ) where
  carrier := {c | ∀ f : SInf F (Fin n × Fin d), pureA F f (∑ j, c j • φ j) ∈ M.So B.ψ B.τ₁}
  zero_mem' := fun f => by
    have : pureA F f (∑ j, (0 : Fin m → ℂ) j • φ j) = 0 := by funext x; simp [pureA]
    rw [this]; exact zero_mem _
  add_mem' := fun {a b} ha hb f => by
    have : pureA F f (∑ j, (a + b) j • φ j) = pureA F f (∑ j, a j • φ j) + pureA F f (∑ j, b j • φ j) := by
      funext x; simp [pureA, add_mul, Finset.sum_add_distrib, mul_add]
    rw [this]; exact add_mem (ha f) (hb f)
  smul_mem' := fun c a ha f => by
    have : pureA F f (∑ j, (c • a) j • φ j) = c • pureA F f (∑ j, a j • φ j) := by
      funext x; simp [pureA, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]; exact Submodule.smul_mem _ _ (ha f)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp m φ f u hφ hu hf h`. Establish `hdom` using `dom_of_domSoU hD hp`. Take `⟨Q, hQ⟩` from `Submodule.exists_isCompl (soCoeff (B := B) M φ)`. Set `P` to `Submodule.linearProjOfIsCompl _ _ hQ`. Set `ψ : Fin m → (Fin n × Fin d → Af F) → ℂ` to `fun j => ∑ i, (P (Pi.single j 1) : Fin m → ℂ) i • φ i`.

Establish `hψ : ∀ j, ψ j ∈ soFin B M` using `fun j => ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hφ i).1, (P (Pi.single j 1)).2⟩`. Establish `key : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ → ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j)` using `fun w hw => by`. Take `⟨m', f', χ, hχ, e⟩` from `(hF F E σ B n d X W M χX χW om r s r' s' hp).1 _ hw`. Establish `hmem : ∀ x, (fun j => w j x) ∈ soCoeff (B` using `B) M φ := fun x f₀ => by`. Establish `e2 : ∑ j, w j x • φ j = ∑ i, f' i x • χ i`.

Use function extensionality and compare the values at `y`. Take `⟨z, hz1, hz2⟩ : ∃ z : Fin n × Fin d → AdeleRing (𝓞 F) F, (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = x ∧ (fun i => (z i).2) = y` from `⟨fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i),`. Use function extensionality and compare the values at `fun i => RingEquiv.apply_symm_apply _ _, rfl⟩`. Use `congrFun e z` as an intermediate fact. Simplify using `only [Finset.sum_apply, pureA, hz1, hz2] at this`.

Simplify `this` using `[Finset.sum_apply]`. Establish `e3 : pureA F f₀ (∑ i, f' i x • χ i) = ∑ i, f' i x • pureA F f₀ (χ i)`. Use function extensionality and compare the values at `z; simp [pureA, Finset.mul_sum, Finset.sum_apply]; exact Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[e2, e3]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((hχ i).2 f₀)`.

Use function extensionality and compare the values at `z`. Use `set x : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1`. Establish `e4 : (fun j => w j x) = ∑ j, w j x • (P (Pi.single j 1) : Fin m → ℂ)`. Establish `a1 : (P (fun j => w j x) : Fin m → ℂ) = fun j => w j x` using `congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hQ ⟨_, hmem x⟩)`. Establish `a2 : (fun j => w j x) = ∑ j, w j x • (Pi.single j 1 : Fin m → ℂ)`.

Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [← a1, a2]`. Simplify using the standard rewrite rules. Establish `e5 : ∀ i, w i x = ∑ j, w j x * (P (Pi.single j 1) : Fin m → ℂ) i` using `fun i => by`.

Simplify `congrFun e4 i` using `[Finset.sum_apply]`. Simplify using `only [Finset.sum_apply, pureA, ψ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[show w i (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = _ from e5 i, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun j _ => mul_assoc _ _ _`. Rewrite using `[key f hf, (dom_sum hB hp hdom f ψ hψ fun i => (hψ i).1).2.2 h]`. Establish `e : (fun k => M.I om (∑ j, pureA F (u k j) (φ j)) h) = fun k => ∑ j, M.I om (pureA F (u k j) (ψ j)) h`. Use function extensionality and compare the values at `fun k => by rw [key _ (hu k), (dom_sum hB hp hdom (u k) ψ hψ fun i => (hψ i).1).2.2 h]`. Rewrite using `[e]`.

Conclude with `tendsto_finset_sum _ fun j _ => (((dom_facts hB hp hdom (hψ j) (hψ j).1).2 h).tendsto _).comp (hφ j).2`.
-/
theorem soCont_of (hB : ThetaBasic) (hD : DomSoU) (hF : SoFin) : SoCont := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp m φ f u hφ hu hf h
  have hdom := dom_of_domSoU hD hp
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (soCoeff (B := B) M φ)
  let P := Submodule.linearProjOfIsCompl _ _ hQ
  let ψ : Fin m → (Fin n × Fin d → Af F) → ℂ := fun j => ∑ i, (P (Pi.single j 1) : Fin m → ℂ) i • φ i
  have hψ : ∀ j, ψ j ∈ soFin B M := fun j =>
    ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hφ i).1, (P (Pi.single j 1)).2⟩
  have key : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ →
      ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j) := fun w hw => by
    obtain ⟨m', f', χ, hχ, e⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).1 _ hw
    have hmem : ∀ x, (fun j => w j x) ∈ soCoeff (B := B) M φ := fun x f₀ => by
      have e2 : ∑ j, w j x • φ j = ∑ i, f' i x • χ i := by
        funext y
        obtain ⟨z, hz1, hz2⟩ : ∃ z : Fin n × Fin d → AdeleRing (𝓞 F) F,
            (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = x ∧ (fun i => (z i).2) = y :=
          ⟨fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i),
            funext fun i => RingEquiv.apply_symm_apply _ _, rfl⟩
        have := congrFun e z
        simp only [Finset.sum_apply, pureA, hz1, hz2] at this
        simpa [Finset.sum_apply] using this
      have e3 : pureA F f₀ (∑ i, f' i x • χ i) = ∑ i, f' i x • pureA F f₀ (χ i) := by
        funext z; simp [pureA, Finset.mul_sum, Finset.sum_apply]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e2, e3]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((hχ i).2 f₀)
    funext z
    set x : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
    have e4 : (fun j => w j x) = ∑ j, w j x • (P (Pi.single j 1) : Fin m → ℂ) := by
      have a1 : (P (fun j => w j x) : Fin m → ℂ) = fun j => w j x :=
        congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hQ ⟨_, hmem x⟩)
      have a2 : (fun j => w j x) = ∑ j, w j x • (Pi.single j 1 : Fin m → ℂ) := by
        funext i; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [← a1, a2]
      simp
    have e5 : ∀ i, w i x = ∑ j, w j x * (P (Pi.single j 1) : Fin m → ℂ) i := fun i => by
      simpa [Finset.sum_apply] using congrFun e4 i
    simp only [Finset.sum_apply, pureA, ψ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show w i (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = _ from e5 i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  rw [key f hf, (dom_sum hB hp hdom f ψ hψ fun i => (hψ i).1).2.2 h]
  have e : (fun k => M.I om (∑ j, pureA F (u k j) (φ j)) h) = fun k => ∑ j, M.I om (pureA F (u k j) (ψ j)) h :=
    funext fun k => by rw [key _ (hu k), (dom_sum hB hp hdom (u k) ψ hψ fun i => (hψ i).1).2.2 h]
  rw [e]
  exact tendsto_finset_sum _ fun j _ => (((dom_facts hB hp hdom (hψ j) (hψ j).1).2 h).tendsto _).comp (hφ j).2

end PositivityTheory.ThKEst

end
