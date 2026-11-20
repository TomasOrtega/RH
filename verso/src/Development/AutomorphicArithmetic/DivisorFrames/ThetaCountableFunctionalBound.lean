import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

open scoped ENNReal in

/- English proof (translation)
Introduce `ι K x hx hc`. Establish `key : ∀ u (c : ι → ℂ) (b : ℝ), (∀ i, ‖c i‖ ≤ b) → Summable fun i => c i * x u i` using `fun u c b hb => Summable.of_norm_bounded ((hx u).mul_left b) (fun i => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _))`. Establish `hle : ∀ (c : lp (fun _ : ι => ℂ) ∞) i, ‖c i‖ ≤ ‖c‖` using `fun c i => lp.norm_apply_le_norm ENNReal.top_ne_zero c i`.

Set `T : K → lp (fun _ : ι => ℂ) ∞ →L[ℂ] ℂ` to `fun u => LinearMap.mkContinuous { toFun := fun c => ∑' i, c i * x u i map_add' := fun c c' => by`. Rewrite using `[← (key u _ _ (hle c)).tsum_add (key u _ _ (hle c'))]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[lp.coeFn_add, Pi.add_apply, add_mul]`.

Use the proof step `map_smul' := fun a c => by`. Rewrite using `[RingHom.id_apply, smul_eq_mul, ← tsum_mul_left]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc] }`.

Use the proof step `(∑' i, ‖x u i‖) (fun c => by show ‖∑' i, c i * x u i‖ ≤ (∑' i, ‖x u i‖) * ‖c‖`. Establish `hs : Summable fun i => ‖c‖ * ‖x u i‖` using `(hx u).mul_left _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hle c i) (norm_nonneg _))`.

Use the proof step `(Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hle c i) (norm_nonneg _)) hs) hs`. Use `_ = (∑' i, ‖x u i‖) * ‖c‖ := by rw [tsum_mul_left, mul_comm])`. Establish `hT : ∀ u c, T u c = ∑' i, c i * x u i` using `fun u c => rfl`. Take `⟨C', hC'⟩` from `banach_steinhaus (g := T) (fun c => by`. Take `⟨C, hC⟩` from `hc (fun i => c i) ⟨‖c‖, hle c⟩`.

Conclude with `⟨C, fun u => by rw [hT]; exact hC u⟩)`. Use `⟨max C' 0, fun u => ?_⟩` and prove the remaining obligations. Set `cu : ι → ℂ` to `fun i => starRingEnd ℂ (x u i) / (‖x u i‖ : ℂ)`. Establish `hcu : ∀ i, ‖cu i‖ ≤ 1` using `fun i => by`. Simplify using `only [cu, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm]`.

Conclude with `div_self_le_one _`. Establish `hmem : Memℓp cu ∞` using `memℓp_infty ⟨1, by rintro _ ⟨i, rfl⟩; exact hcu i⟩`. Set `c : lp (fun _ : ι => ℂ) ∞` to `⟨cu, hmem⟩`. Establish `hc1 : ‖c‖ ≤ 1` using `lp.norm_le_of_forall_le zero_le_one (fun i => hcu i)`. Establish `hmul : ∀ i, cu i * x u i = ((‖x u i‖ : ℝ) : ℂ)` using `fun i => by`.

Simplify using `only [cu]`. Break down `eq_or_ne (x u i) 0 with h | h` into its components or cases. Simplify using `[h]`. Establish `hn : (‖x u i‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.mpr h`. Rewrite using `[div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hn]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e : T u c = ((∑' i, ‖x u i‖ : ℝ) : ℂ)`. Rewrite using `[hT, Complex.ofReal_tsum]`. Conclude with `tsum_congr fun i => hmul i`.

Establish `h1 : ∑' i, ‖x u i‖ = ‖T u c‖`. Rewrite using `[e, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun i => norm_nonneg _)]`. Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem UpperTheory.uniform_boundedness_summable : ∀ {ι K : Type} (x : K → ι → ℂ), (∀ u, Summable fun i => ‖x u i‖) →
    (∀ c : ι → ℂ, (∃ b : ℝ, ∀ i, ‖c i‖ ≤ b) → ∃ C : ℝ, ∀ u, ‖∑' i, c i * x u i‖ ≤ C) →
    ∃ C : ℝ, ∀ u, ∑' i, ‖x u i‖ ≤ C := by
  intro ι K x hx hc
  have key : ∀ u (c : ι → ℂ) (b : ℝ), (∀ i, ‖c i‖ ≤ b) → Summable fun i => c i * x u i := fun u c b hb =>
    Summable.of_norm_bounded ((hx u).mul_left b) (fun i => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _))
  have hle : ∀ (c : lp (fun _ : ι => ℂ) ∞) i, ‖c i‖ ≤ ‖c‖ := fun c i => lp.norm_apply_le_norm ENNReal.top_ne_zero c i
  let T : K → lp (fun _ : ι => ℂ) ∞ →L[ℂ] ℂ := fun u =>
    LinearMap.mkContinuous
      { toFun := fun c => ∑' i, c i * x u i
        map_add' := fun c c' => by
          rw [← (key u _ _ (hle c)).tsum_add (key u _ _ (hle c'))]
          congr 1; funext i
          rw [lp.coeFn_add, Pi.add_apply, add_mul]
        map_smul' := fun a c => by
          rw [RingHom.id_apply, smul_eq_mul, ← tsum_mul_left]
          congr 1; funext i
          rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc] }
      (∑' i, ‖x u i‖) (fun c => by
        show ‖∑' i, c i * x u i‖ ≤ (∑' i, ‖x u i‖) * ‖c‖
        have hs : Summable fun i => ‖c‖ * ‖x u i‖ := (hx u).mul_left _
        calc ‖∑' i, c i * x u i‖ ≤ ∑' i, ‖c i * x u i‖ :=
              norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
                (fun i => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hle c i) (norm_nonneg _)) hs)
          _ ≤ ∑' i, ‖c‖ * ‖x u i‖ := Summable.tsum_le_tsum (fun i => by
                rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hle c i) (norm_nonneg _))
              (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
                (fun i => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hle c i) (norm_nonneg _)) hs) hs
          _ = (∑' i, ‖x u i‖) * ‖c‖ := by rw [tsum_mul_left, mul_comm])
  have hT : ∀ u c, T u c = ∑' i, c i * x u i := fun u c => rfl
  obtain ⟨C', hC'⟩ := banach_steinhaus (g := T) (fun c => by
    obtain ⟨C, hC⟩ := hc (fun i => c i) ⟨‖c‖, hle c⟩
    exact ⟨C, fun u => by rw [hT]; exact hC u⟩)
  refine ⟨max C' 0, fun u => ?_⟩
  let cu : ι → ℂ := fun i => starRingEnd ℂ (x u i) / (‖x u i‖ : ℂ)
  have hcu : ∀ i, ‖cu i‖ ≤ 1 := fun i => by
    simp only [cu, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm]
    exact div_self_le_one _
  have hmem : Memℓp cu ∞ := memℓp_infty ⟨1, by rintro _ ⟨i, rfl⟩; exact hcu i⟩
  let c : lp (fun _ : ι => ℂ) ∞ := ⟨cu, hmem⟩
  have hc1 : ‖c‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one (fun i => hcu i)
  have hmul : ∀ i, cu i * x u i = ((‖x u i‖ : ℝ) : ℂ) := fun i => by
    simp only [cu]
    rcases eq_or_ne (x u i) 0 with h | h
    · simp [h]
    · have hn : (‖x u i‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hn]
      push_cast; ring
  have e : T u c = ((∑' i, ‖x u i‖ : ℝ) : ℂ) := by
    rw [hT, Complex.ofReal_tsum]
    exact tsum_congr fun i => hmul i
  have h1 : ∑' i, ‖x u i‖ = ‖T u c‖ := by
    rw [e, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun i => norm_nonneg _)]
  rw [h1]
  calc ‖T u c‖ ≤ ‖T u‖ * ‖c‖ := (T u).le_opNorm c
    _ ≤ ‖T u‖ * 1 := mul_le_mul_of_nonneg_left hc1 (norm_nonneg _)
    _ ≤ max C' 0 := by rw [mul_one]; exact (hC' u).trans (le_max_left _ _)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP ι _ l hl summ Ψ hΨ K hK`. Break down `isEmpty_or_nonempty ι with hι | hι` into its components or cases. Conclude with `⟨0, fun p _ => by simp⟩`. Take `⟨en, hen⟩` from `exists_surjective_nat ι`. Set `S : ℕ → Finset ι` to `fun N => (Finset.range N).image en`.

Establish `hS : Tendsto S atTop atTop`. Use `Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun w => ?_)` and prove the remaining obligations. Conclude with `Finset.image_subset_image (Finset.range_subset_range.2 hab)`. Take `⟨k, rfl⟩` from `hen w`. Conclude with `⟨k + 1, Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_self k))⟩`.

Use `haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _`. Establish `adm : ∀ c : ι → ℂ, (∃ b : ℝ, ∀ ξ, ‖c ξ‖ ≤ b) → ∃ L ∈ (adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ schA F (Fin n × Fin d), L Φ = ∑' ξ, c ξ * l ξ Φ`. Introduce and unpack `c ⟨b, hb⟩`. Establish `hs : ∀ Φ ∈ schA F (Fin n × Fin d), Summable fun ξ => c ξ * l ξ Φ` using `fun Φ hΦ => Summable.of_norm_bounded ((summ Φ hΦ).mul_left b) (fun ξ => by`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (hb ξ) (norm_nonneg _))`. Set `Lc : schA F (Fin n × Fin d) →ₗ[ℂ] ℂ` to `{ toFun := fun Φ => ∑' ξ, c ξ * l ξ Φ.1 map_add' := fun Φ Φ' => by`. Rewrite using `[← (hs _ Φ.2).tsum_add (hs _ Φ'.2)]`. Use `congr 1`. Use function extensionality and compare the values at `ξ`.

Rewrite using `[Submodule.coe_add, map_add]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun a Φ => by`. Simplify using `only [RingHom.id_apply, SetLike.val_smul, smul_eq_mul]`. Rewrite using `[← tsum_mul_left]`.

Use `congr 1`. Use function extensionality and compare the values at `ξ`. Rewrite using `[map_smul, smul_eq_mul]`. Use `ring }`. Take `⟨L, hL⟩` from `LinearMap.exists_extend Lc`.

Establish `hLe : ∀ Φ (hΦ : Φ ∈ schA F (Fin n × Fin d)), L Φ = Lc ⟨Φ, hΦ⟩` using `fun Φ hΦ => by`. Use `LinearMap.congr_fun hL ⟨Φ, hΦ⟩` as an intermediate fact. Simplify using `using this`. Use `⟨L, ?_, fun Φ hΦ => hLe Φ hΦ⟩` and prove the remaining obligations. Introduce `g hg`.

Establish `hmem : ∀ f : SInf F (Fin n × Fin d), pureA F f g ∈ schA F (Fin n × Fin d)` using `fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩`. Establish `hterm : ∀ i, ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), l i (pureA F f g) = T f` using `fun i => hl i g hg`. Use `choose T hT using hterm`. Establish `hlim : Tendsto (fun N f => (∑ w ∈ S N, c w • T w) f) atTop (𝓝 fun f : SInf F (Fin n × Fin d) => ∑' w, c w * l w (pureA F f g))`. Rewrite using `[tendsto_pi_nhds]`.

Introduce `f`. Simplify using `only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ← hT]`. Conclude with `(hs _ (hmem f)).hasSum.comp hS`. Use `⟨continuousLinearMapOfTendsto (fun N => ∑ w ∈ S N, c w • T w) hlim, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[hLe _ (hmem f)]`.

Both sides reduce to the same expression. Establish `hpres : ∀ p : UA σ X.J × UA σ W.J, om p Ψ ∈ schA F (Fin n × Fin d)` using `fun p => (IsUWeilPair.isUSplitting hP.weil).pres p Ψ hΨ`. Take `⟨C, hC⟩` from `UpperTheory.uniform_boundedness_summable (K := K) (fun u ξ => l ξ (om u.1 Ψ)) (fun u => summ _ (hpres _)) (fun c hc => by`. Take `⟨L, hL, hLe⟩` from `adm c hc`. Establish `hcont : Continuous fun p : UA σ X.J × UA σ W.J => L (om p Ψ)` using `(IsUWeilPair.isUSplitting hP.weil).cont L hL Ψ hΨ`.

Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hcont.continuousOn`. Conclude with `⟨C, fun u => by rw [← hLe _ (hpres _)]; exact hC u.1 u.2⟩)`. Conclude with `⟨C, fun u hu => hC ⟨u, hu⟩⟩`.
-/
theorem UpperTheory.theta_countable_functional_bound :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
        (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
        ∀ (ι : Type) [Countable ι] (l : ι → Fn F n d →ₗ[ℂ] ℂ), (∀ i, l i ∈ (adeleClass F).adm (Fin n × Fin d)) →
        (∀ Φ ∈ schA F (Fin n × Fin d), Summable fun i => ‖l i Φ‖) → ∀ Ψ ∈ schA F (Fin n × Fin d),
        ∀ K : Set (UA σ X.J × UA σ W.J), IsCompact K → ∃ C : ℝ, ∀ p ∈ K, ∑' i, ‖l i (om p Ψ)‖ ≤ C := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP ι _ l hl summ Ψ hΨ K hK
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun p _ => by simp⟩
  obtain ⟨en, hen⟩ := exists_surjective_nat ι
  let S : ℕ → Finset ι := fun N => (Finset.range N).image en
  have hS : Tendsto S atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun w => ?_)
    · exact Finset.image_subset_image (Finset.range_subset_range.2 hab)
    · obtain ⟨k, rfl⟩ := hen w
      exact ⟨k + 1, Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_self k))⟩
  haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _
  have adm : ∀ c : ι → ℂ, (∃ b : ℝ, ∀ ξ, ‖c ξ‖ ≤ b) →
      ∃ L ∈ (adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ schA F (Fin n × Fin d), L Φ = ∑' ξ, c ξ * l ξ Φ := by
    rintro c ⟨b, hb⟩
    have hs : ∀ Φ ∈ schA F (Fin n × Fin d), Summable fun ξ => c ξ * l ξ Φ := fun Φ hΦ =>
      Summable.of_norm_bounded ((summ Φ hΦ).mul_left b) (fun ξ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hb ξ) (norm_nonneg _))
    let Lc : schA F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
      { toFun := fun Φ => ∑' ξ, c ξ * l ξ Φ.1
        map_add' := fun Φ Φ' => by
          rw [← (hs _ Φ.2).tsum_add (hs _ Φ'.2)]
          congr 1
          funext ξ
          rw [Submodule.coe_add, map_add]
          ring
        map_smul' := fun a Φ => by
          simp only [RingHom.id_apply, SetLike.val_smul, smul_eq_mul]
          rw [← tsum_mul_left]
          congr 1
          funext ξ
          rw [map_smul, smul_eq_mul]
          ring }
    obtain ⟨L, hL⟩ := LinearMap.exists_extend Lc
    have hLe : ∀ Φ (hΦ : Φ ∈ schA F (Fin n × Fin d)), L Φ = Lc ⟨Φ, hΦ⟩ := fun Φ hΦ => by
      have := LinearMap.congr_fun hL ⟨Φ, hΦ⟩
      simpa using this
    refine ⟨L, ?_, fun Φ hΦ => hLe Φ hΦ⟩
    intro g hg
    have hmem : ∀ f : SInf F (Fin n × Fin d), pureA F f g ∈ schA F (Fin n × Fin d) :=
      fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
    have hterm : ∀ i, ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d),
        l i (pureA F f g) = T f := fun i => hl i g hg
    choose T hT using hterm
    have hlim : Tendsto (fun N f => (∑ w ∈ S N, c w • T w) f) atTop
        (𝓝 fun f : SInf F (Fin n × Fin d) => ∑' w, c w * l w (pureA F f g)) := by
      rw [tendsto_pi_nhds]
      intro f
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ← hT]
      exact (hs _ (hmem f)).hasSum.comp hS
    refine ⟨continuousLinearMapOfTendsto (fun N => ∑ w ∈ S N, c w • T w) hlim, fun f => ?_⟩
    rw [hLe _ (hmem f)]
    rfl
  have hpres : ∀ p : UA σ X.J × UA σ W.J, om p Ψ ∈ schA F (Fin n × Fin d) := fun p =>
    (IsUWeilPair.isUSplitting hP.weil).pres p Ψ hΨ
  obtain ⟨C, hC⟩ := UpperTheory.uniform_boundedness_summable (K := K) (fun u ξ => l ξ (om u.1 Ψ))
    (fun u => summ _ (hpres _)) (fun c hc => by
      obtain ⟨L, hL, hLe⟩ := adm c hc
      have hcont : Continuous fun p : UA σ X.J × UA σ W.J => L (om p Ψ) :=
        (IsUWeilPair.isUSplitting hP.weil).cont L hL Ψ hΨ
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
      exact ⟨C, fun u => by rw [← hLe _ (hpres _)]; exact hC u.1 u.2⟩)
  exact ⟨C, fun u hu => hC ⟨u, hu⟩⟩
