import Development.WeilBound.ThetaLifts.LatticeBasics.RegOfBound
import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

/- English proof (translation)
The claim follows from `one_le_heightGL F x.1`.
-/
theorem one_le_height_GL2 (x : G2 σ Y) : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f h => exact ⟨h.1, 1, h.2.imp fun N h x => by simpa using h x⟩`. Consider the case `zero => exact ⟨continuous_zero, 0, 0, by simp⟩`. Consider the case `add f g _ _ a b`. Take `⟨a, C, N, hC⟩` from `a`.

Take `⟨b, C', N', hC'⟩` from `b`. Use `⟨a.add b, max C 0 + max C' 0, max N N', fun x => (norm_add_le _ _).trans ?_⟩` and prove the remaining obligations. Use `one_le_height_GL2 x` as an intermediate fact. Rewrite using `[add_mul]`. Apply the tactic sequence `refine add_le_add ((hC x).trans ?_) ((hC' x).trans ?_) <;> gcongr <;> simp`.

Consider the case `smul c f _ a`. Take `⟨a, C, N, hC⟩` from `a`. Conclude with `⟨a.const_smul c, ‖c‖ * C, N, fun x => by`. Rewrite using `[Pi.smul_apply, norm_smul, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩`.
-/
theorem modFun_spec {f : G2 σ Y → ℂ} (hf : f ∈ modFun σ Y) :
    Continuous f ∧ ∃ (C : ℝ) (N : ℕ), ∀ x, ‖f x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  induction hf using Submodule.span_induction with
  | mem f h => exact ⟨h.1, 1, h.2.imp fun N h x => by simpa using h x⟩
  | zero => exact ⟨continuous_zero, 0, 0, by simp⟩
  | add f g _ _ a b =>
    obtain ⟨a, C, N, hC⟩ := a
    obtain ⟨b, C', N', hC'⟩ := b
    refine ⟨a.add b, max C 0 + max C' 0, max N N', fun x => (norm_add_le _ _).trans ?_⟩
    have := one_le_height_GL2 x
    rw [add_mul]
    refine add_le_add ((hC x).trans ?_) ((hC' x).trans ?_) <;> gcongr <;> simp
  | smul c f _ a =>
    obtain ⟨a, C, N, hC⟩ := a
    exact ⟨a.const_smul c, ‖c‖ * C, N, fun x => by
      rw [Pi.smul_apply, norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩

/- English proof (translation)
Take `⟨D, hD, hU', cD⟩` from `local_compact_nhds hU`. Use `An.reg_of_bound (NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)) hD (fun x => (h ((LinearMap.proj x).comp (modFun σ Y).subtype) fun N => ⟨_, fun f hf => hf x⟩).mono hU') (fun s _ => (modFun_spec (H s).2).1) (An.unif_bound one_le …` and prove the remaining obligations. Conclude with `cD.exists_bound_of_continuousOn ((h μ hμ).mono hU').continuousOn`.
-/
theorem reg_of_weak {s₀ : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 s₀) {H : ℂ → modFun σ Y}
    (h : ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U) :
    An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) (fun s => (H s).1) s₀ := by
  obtain ⟨D, hD, hU', cD⟩ := local_compact_nhds hU
  refine An.reg_of_bound (NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)) hD
    (fun x => (h ((LinearMap.proj x).comp (modFun σ Y).subtype) fun N => ⟨_, fun f hf => hf x⟩).mono hU')
    (fun s _ => (modFun_spec (H s).2).1) (An.unif_bound one_le_height_GL2 (fun f hf => (modFun_spec hf).2) fun μ hμ => ?_)
  exact cD.exists_bound_of_continuousOn ((h μ hμ).mono hU').continuousOn

/- English proof (translation)
Establish `disc : ∀ s : ℂ, ∀ᶠ z in 𝓝[≠] s, z ∈ {s | An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) Ê s}` using `fun s =>`. Set `⟨_, _, a, e⟩` to `h3 s`. Use the proof step `a.punct one_le_height_GL2 e`. Use `⟨_, ⟨isOpen_iff_mem_nhds.2 fun s hs => hs.eventually, An.preconn disc, disc, ⟨t, fun s hs => ⟨?_, h1 s hs⟩⟩, fun x s hs => ?_, fun y hy => (An.Reg.contAt hy.1 y.2).continuousWithinAt, fun s hs => ?_⟩, fun s => ?_⟩` and prove the remaining obligations. Take `⟨_, _, a, e⟩` from `h3 s`.

Conclude with `a.remove one_le_height_GL2 e ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) h2`. Take `⟨S, hS, a⟩` from `hs`. Conclude with `((a.hol x).differentiableAt hS).differentiableWithinAt`. Take `⟨S, hS, -, -, C, N, hC⟩` from `hs`. Take `⟨r, r0, hr⟩` from `Metric.mem_nhds_iff.1 hS`.

Conclude with `⟨r, C, N, r0, fun z hz => hC z (hr hz)⟩`. Take `⟨k, H, ⟨S, hS, a⟩, e⟩` from `h3 s`. Take `⟨r, r0, hr⟩` from `Metric.mem_nhds_iff.1 (inter_mem hS (eventually_nhdsWithin_iff.1 e))`. Establish `b` using `a.mono fun z hz => (hr hz).1`. Conclude with `⟨k, r, H, r0, fun z hz => (hr hz).2, b.hol, b.cont, b.grow⟩`.
-/
theorem eisCont_of_reg {f Ê : ℂ → G2 σ Y → ℂ} {t : ℝ} (h1 : ∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (f s) x) (Ê s x))
    (h2 : ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re})
    (h3 : ∀ s₀, ∃ (k : ℕ) (H : ℂ → G2 σ Y → ℂ), An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) H s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, ∀ x, H s x = (s - s₀) ^ k * Ê s x) :
    ∃ U, IsEisCont f U Ê ∧ ∀ s₀, ∃ k, IsRegAt Ê s₀ k := by
  have disc : ∀ s : ℂ, ∀ᶠ z in 𝓝[≠] s, z ∈ {s | An.Reg (fun x : G2 σ Y => (ht2 x : ℝ)) Ê s} := fun s =>
    let ⟨_, _, a, e⟩ := h3 s
    a.punct one_le_height_GL2 e
  refine ⟨_, ⟨isOpen_iff_mem_nhds.2 fun s hs => hs.eventually, An.preconn disc, disc, ⟨t, fun s hs => ⟨?_, h1 s hs⟩⟩,
    fun x s hs => ?_, fun y hy => (An.Reg.contAt hy.1 y.2).continuousWithinAt, fun s hs => ?_⟩, fun s => ?_⟩
  · obtain ⟨_, _, a, e⟩ := h3 s
    exact a.remove one_le_height_GL2 e ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) h2
  · obtain ⟨S, hS, a⟩ := hs
    exact ((a.hol x).differentiableAt hS).differentiableWithinAt
  · obtain ⟨S, hS, -, -, C, N, hC⟩ := hs
    obtain ⟨r, r0, hr⟩ := Metric.mem_nhds_iff.1 hS
    exact ⟨r, C, N, r0, fun z hz => hC z (hr hz)⟩
  · obtain ⟨k, H, ⟨S, hS, a⟩, e⟩ := h3 s
    obtain ⟨r, r0, hr⟩ := Metric.mem_nhds_iff.1 (inter_mem hS (eventually_nhdsWithin_iff.1 e))
    have b := a.mono fun z hz => (hr hz).1
    exact ⟨k, r, H, r0, fun z hz => (hr hz).2, b.hol, b.cont, b.grow⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc K a hK ha s₁ f hf`. Use `haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)`. Take `⟨b, K₀, p, t, hb, hK₀, hp, hk⟩` from `h2 F E σ B n Y r s hB hY K hK`. Take `⟨d, hd⟩ : ∃ d : ℝ, d = absE F E (Matrix.GeneralLinearGroup.det t)` from `⟨_, rfl⟩`. Establish `d0 : 0 < d` using `hd ▸ absE_pos _`.

Establish `a0 : ∀ x, 0 < a x` using `fun x => by`. Take `⟨q, u, hq, k, hk, rfl⟩` from `ha.iwa x`. Conclude with `ha.val q u hq k hk ▸ absE_pos _`. Establish `hk' : ∀ k ∈ K₀, p * k * p⁻¹ ∈ K` using `fun k h => (hk _).2 (by simpa [mul_assoc] using h)`. Establish `ha₀ : IsHgt K₀ fun x => d * a (x * p⁻¹)`.

Use `⟨fun x => ?_, fun q u hq k h => ?_⟩` and prove the remaining obligations. Take `⟨q, u, hq, k, h, e⟩` from `ha.iwa (x * p⁻¹)`. Conclude with `⟨q * p, _, hq.mul hp, _, (hk k).1 h, by rw [mul_inv_eq_iff_eq_mul.1 e]; group⟩`. Rewrite using `[show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, ha.val _ _ (hq.mul hp.inv) _ (hk' k h), map_mul, map_mul, map_inv, map_inv, NNReal.coe_mul, NNReal.coe_inv, ← hd]`. Clear the denominators using the available nonvanishing facts.

Establish `hf₀ : IsSec K₀ χ s₁ fun x => f (x * p⁻¹)`. Use `⟨hf.cont.comp (continuous_mul_const _), fun q u x hq => by rw [mul_assoc, hf.law q u _ hq], ?_⟩` and prove the remaining obligations. Use `haveI := hf.fin`. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k.1))).map (LinearMap.funLeft ℂ ℂ fun x => x * p⁻¹)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `⟨_, Submodule.subset_span ⟨⟨_, hk' k k.2⟩, rfl⟩, funext fun x => by simp [LinearMap.funLeft, mul_assoc]⟩`. Take `⟨Ê, ⟨t₁, e1, e2⟩, e3⟩` from `h1 F E σ B n Y r s hB hn hY χ hχ c hc b K₀ _ hb hK₀ ha₀ s₁ _ hf₀`. Establish `dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (s₁ - z)` using `(differentiable_id.const_sub s₁).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))`. Use `(eisCont_of_reg (f := flat a f s₁) (Ê := fun z x => (d : ℂ) ^ (s₁ - z) * Ê z (x * p)) (t := t₁) (fun z hz x => ?_) (fun x => dc.differentiableOn.mul (e2 _)) fun s₀ => ?_).imp fun U hU => ⟨_, hU⟩` and prove the remaining obligations. Use `(congrArg (HasSum · _) (funext fun q => ?_)).mp ((e1 z hz (x * p)).mul_left ((d : ℂ) ^ (s₁ - z)))` and prove the remaining obligations.

Simplify using `only [eisTerm, flat, ← mul_assoc, mul_inv_cancel_right]`. Rewrite using `[Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg d0.le (a0 _).le, ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]`. Simplify using the standard rewrite rules. Take `⟨k, U, H, hU, e4, e5⟩` from `e3 s₀`. Use `⟨k, _, (reg_of_weak hU e5).mul one_le_height_GL2 (dc.analyticAt s₀) (continuous_mul_const p) (b := ht2 p) fun x => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Conclude with `heightGL_mul_le F x.1 p.1` after adjusting the coercions. Use `filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz hz' x`. Rewrite using `[e4 z hz hz', mul_left_comm]`.
-/
theorem eisContinues_of (h1 : EisBL) (h2 : FrameConj) : EisContinues := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc K a hK ha s₁ f hf
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨b, K₀, p, t, hb, hK₀, hp, hk⟩ := h2 F E σ B n Y r s hB hY K hK
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = absE F E (Matrix.GeneralLinearGroup.det t) := ⟨_, rfl⟩
  have d0 : 0 < d := hd ▸ absE_pos _
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨q, u, hq, k, hk, rfl⟩ := ha.iwa x
    exact ha.val q u hq k hk ▸ absE_pos _
  have hk' : ∀ k ∈ K₀, p * k * p⁻¹ ∈ K := fun k h => (hk _).2 (by simpa [mul_assoc] using h)
  have ha₀ : IsHgt K₀ fun x => d * a (x * p⁻¹) := by
    refine ⟨fun x => ?_, fun q u hq k h => ?_⟩
    · obtain ⟨q, u, hq, k, h, e⟩ := ha.iwa (x * p⁻¹)
      exact ⟨q * p, _, hq.mul hp, _, (hk k).1 h, by rw [mul_inv_eq_iff_eq_mul.1 e]; group⟩
    · rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, ha.val _ _ (hq.mul hp.inv) _ (hk' k h), map_mul, map_mul, map_inv,
        map_inv, NNReal.coe_mul, NNReal.coe_inv, ← hd]
      field_simp
  have hf₀ : IsSec K₀ χ s₁ fun x => f (x * p⁻¹) := by
    refine ⟨hf.cont.comp (continuous_mul_const _), fun q u x hq => by rw [mul_assoc, hf.law q u _ hq], ?_⟩
    haveI := hf.fin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k.1))).map
      (LinearMap.funLeft ℂ ℂ fun x => x * p⁻¹)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨⟨_, hk' k k.2⟩, rfl⟩, funext fun x => by simp [LinearMap.funLeft, mul_assoc]⟩
  obtain ⟨Ê, ⟨t₁, e1, e2⟩, e3⟩ := h1 F E σ B n Y r s hB hn hY χ hχ c hc b K₀ _ hb hK₀ ha₀ s₁ _ hf₀
  have dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (s₁ - z) :=
    (differentiable_id.const_sub s₁).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))
  refine (eisCont_of_reg (f := flat a f s₁) (Ê := fun z x => (d : ℂ) ^ (s₁ - z) * Ê z (x * p)) (t := t₁) (fun z hz x => ?_)
    (fun x => dc.differentiableOn.mul (e2 _)) fun s₀ => ?_).imp fun U hU => ⟨_, hU⟩
  · refine (congrArg (HasSum · _) (funext fun q => ?_)).mp ((e1 z hz (x * p)).mul_left ((d : ℂ) ^ (s₁ - z)))
    simp only [eisTerm, flat, ← mul_assoc, mul_inv_cancel_right]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg d0.le (a0 _).le, ← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]
    simp
  · obtain ⟨k, U, H, hU, e4, e5⟩ := e3 s₀
    refine ⟨k, _, (reg_of_weak hU e5).mul one_le_height_GL2 (dc.analyticAt s₀) (continuous_mul_const p) (b := ht2 p) fun x => ?_, ?_⟩
    · rw [mul_comm]; exact_mod_cast heightGL_mul_le F x.1 p.1
    · filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz hz' x
      rw [e4 z hz hz', mul_left_comm]

end GlobalTheory.ThK.Dbl

end
