import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedEvaluationGoodModelStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ThKSwapLoc

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
theorem tsum_norm_le_of_bdd_pairing : ∀ {ι K : Type} (x : K → ι → ℂ), (∀ u, Summable fun i => ‖x u i‖) →
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
Use function extensionality and compare the values at `x`. Simplify using `[Darboux.rho, schr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_lin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (γ : Matrix (Fin n) (Fin d) (AE F E)) (a : ℂ)
    (Φ Φ' : Fn F n d) : M.co.rho ψ γ (a • Φ + Φ') = a • M.co.rho ψ γ Φ + M.co.rho ψ γ Φ' := by
  funext x
  simp [Darboux.rho, schr]
  ring

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hEv χX χW om r s r' s' hP Ψ hΨ K hK`. Use `set l : (Fin n → E) → Fn F n d → ℂ := fun ξ Φ => thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Φ)) with hl`. Establish `hψ : IsStd B.ψ` using `hP.base.std`. Establish `lin : ∀ ξ, ∀ Φ ∈ schA F (Fin n × Fin d), ∀ Φ' ∈ schA F (Fin n × Fin d), ∀ a : ℂ, l ξ (a • Φ + Φ') = a * l ξ Φ + l ξ Φ'`. Introduce `ξ Φ hΦ Φ' hΦ' a`.

Establish `m1` using `hEv.maps _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Φ hΦ)`. Establish `m2` using `hEv.maps _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Φ' hΦ')`. Simplify using `only [hl]`. Rewrite using `[rho_lin, map_add, map_smul, GlobalTheory.WeilM.thetaSum_add F (Submodule.smul_mem _ a m1) m2, GlobalTheory.WeilM.thetaSum_smul]`. Establish `ladd : ∀ ξ, ∀ Φ ∈ schA F (Fin n × Fin d), ∀ Φ' ∈ schA F (Fin n × Fin d), l ξ (Φ + Φ') = l ξ Φ + l ξ Φ'`.

Introduce `ξ Φ hΦ Φ' hΦ'`. Simplify using `using lin ξ Φ hΦ Φ' hΦ' 1`. Establish `l0 : ∀ ξ, l ξ 0 = 0`. Introduce `ξ`. Establish `h` using `ladd ξ 0 (zero_mem _) 0 (zero_mem _)`.

Simplify using `only [add_zero] at h`. Take the linear combination `-h`. Establish `lsmul : ∀ ξ, ∀ Φ ∈ schA F (Fin n × Fin d), ∀ a : ℂ, l ξ (a • Φ) = a * l ξ Φ`. Introduce `ξ Φ hΦ a`. Simplify `lin ξ Φ hΦ 0 (zero_mem _) a` using `[l0]`.

Establish `hA` using `GlobalTheory.T.adapted_evaluation_good_model hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hEv hP.base hP.good ⟨r, s, r', s', hP.herm, hP.skew⟩`. Establish `summ : ∀ Φ ∈ schA F (Fin n × Fin d), Summable fun ξ => ‖l ξ Φ‖`. Introduce `Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨f, g, hg, rfl⟩` from `hx`. Take `⟨s₀, C, -, hC⟩` from `hA g hg`. Conclude with `summable_of_sum_le (fun _ => norm_nonneg _) (hC f)`. Consider the case `zero => simp [l0]`. Consider the case `add x y hx hy ihx ihy`.

Use `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_) (ihx.add ihy)` and prove the remaining obligations. Rewrite using `[ladd ξ x hx y hy]`. Conclude with `norm_add_le _ _`. Consider the case `smul a x hx ih`. Use `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_) (ih.mul_left ‖a‖)` and prove the remaining obligations.

Rewrite using `[lsmul ξ x hx a, norm_mul]`. Establish `adm : ∀ c : (Fin n → E) → ℂ, (∃ b : ℝ, ∀ ξ, ‖c ξ‖ ≤ b) → ∃ L ∈ (adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ schA F (Fin n × Fin d), L Φ = ∑' ξ, c ξ * l ξ Φ`. Introduce and unpack `c ⟨b, hb⟩`. Establish `hs : ∀ Φ ∈ schA F (Fin n × Fin d), Summable fun ξ => c ξ * l ξ Φ` using `fun Φ hΦ => Summable.of_norm_bounded ((summ Φ hΦ).mul_left b) (fun ξ => by`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (hb ξ) (norm_nonneg _))`. Set `Lc : schA F (Fin n × Fin d) →ₗ[ℂ] ℂ` to `{ toFun := fun Φ => ∑' ξ, c ξ * l ξ Φ.1 map_add' := fun Φ Φ' => by`. Rewrite using `[← (hs _ Φ.2).tsum_add (hs _ Φ'.2)]`. Use `congr 1`. Use function extensionality and compare the values at `ξ`.

Rewrite using `[Submodule.coe_add, ladd ξ _ Φ.2 _ Φ'.2]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_smul' := fun a Φ => by`. Simplify using `only [RingHom.id_apply, SetLike.val_smul, smul_eq_mul]`. Rewrite using `[← tsum_mul_left]`.

Use `congr 1`. Use function extensionality and compare the values at `ξ`. Rewrite using `[lsmul ξ _ Φ.2 a]`. Use `ring }`. Take `⟨L, hL⟩` from `LinearMap.exists_extend Lc`.

Establish `hLe : ∀ Φ (hΦ : Φ ∈ schA F (Fin n × Fin d)), L Φ = Lc ⟨Φ, hΦ⟩` using `fun Φ hΦ => by`. Use `LinearMap.congr_fun hL ⟨Φ, hΦ⟩` as an intermediate fact. Simplify using `using this`. Use `⟨L, ?_, fun Φ hΦ => hLe Φ hΦ⟩` and prove the remaining obligations. Introduce `g hg`.

Establish `hmem : ∀ f : SInf F (Fin n × Fin d), pureA F f g ∈ schA F (Fin n × Fin d)` using `fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩`. Take `⟨s₀, C, hC0, hC⟩` from `hA g hg`. Use `⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => Lc ⟨pureA F f g, hmem f⟩) ?_ ?_ ?_, fun f => ?_⟩` and prove the remaining obligations. Introduce `f₁ f₂`. Rewrite using `[← map_add]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Simplify using `[pureA, add_mul]`. Introduce `a f`.

Rewrite using `[RingHom.id_apply, ← map_smul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Simplify using `[pureA, mul_assoc]`.

Use `⟨s₀, max b 0 * C, mul_nonneg (le_max_right _ _) hC0, fun f => ?_⟩` and prove the remaining obligations. Establish `hsn` using `summ _ (hmem f)`. Combine the equalities or inequalities in the displayed calculation. Use `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_) (hsn.mul_left (max b 0))` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_right ((hb ξ).trans (le_max_left _ _)) (norm_nonneg _))`. Use `_ ≤ ∑' ξ, max b 0 * ‖l ξ (pureA F f g)‖ := by`. Use `Summable.tsum_le_tsum (fun ξ => ?_) ?_ (hsn.mul_left _)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right ((hb ξ).trans (le_max_left _ _)) (norm_nonneg _)`.

Use `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_) (hsn.mul_left (max b 0))` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right ((hb ξ).trans (le_max_left _ _)) (norm_nonneg _)`. Use `_ = max b 0 * ∑' ξ, ‖l ξ (pureA F f g)‖ := tsum_mul_left`. Use `_ ≤ max b 0 * (C * (s₀.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f) := by`.

Use `mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)` and prove the remaining obligations. Conclude with `hsn.tsum_le_of_sum_le (hC f)`. Use `_ = max b 0 * C * (s₀.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f := by ring`. Rewrite using `[hLe _ (hmem f)]`. Both sides reduce to the same expression.

Establish `hpres : ∀ u : UA σ W.J, om (1, u) Ψ ∈ schA F (Fin n × Fin d)` using `fun u => (IsUWeilPair.isUSplitting hP.weil).pres (1, u) Ψ hΨ`. Take `⟨C, hC⟩` from `tsum_norm_le_of_bdd_pairing (K := K) (fun u ξ => l ξ (om (1, u.1.1) Ψ)) (fun u => summ _ (hpres _)) (fun c hc => by`. Take `⟨L, hL, hLe⟩` from `adm c hc`. Establish `hcont : Continuous fun p : UA σ X.J × UA σ W.J => L (om p Ψ)` using `(IsUWeilPair.isUSplitting hP.weil).cont L hL Ψ hΨ`. Establish `hc2 : Continuous fun u : unip σ W H' => L (om (1, u.1) Ψ)` using `hcont.comp (continuous_const.prodMk continuous_subtype_val)`.

Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hc2.continuousOn`. Conclude with `⟨C, fun u => by rw [← hLe _ (hpres _)]; exact hC u.1 u.2⟩)`. Conclude with `⟨C, fun u hu => ⟨summ _ (hpres _), hC ⟨u, hu⟩⟩⟩`.
-/
theorem sum_norm_bdd : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Ψ ∈ schA F (Fin n × Fin d),
      ∀ K : Set (unip σ W H'), IsCompact K → ∃ C : ℝ, ∀ u ∈ K, Summable (fun ξ : Fin n → E => ‖thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ)))‖) ∧
        ∑' ξ : Fin n → E, ‖thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u.1) Ψ)))‖ ≤ C := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hEv χX χW om r s r' s' hP Ψ hΨ K hK
  set l : (Fin n → E) → Fn F n d → ℂ := fun ξ Φ =>
    thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Φ)) with hl
  have hψ : IsStd B.ψ := hP.base.std
  have lin : ∀ ξ, ∀ Φ ∈ schA F (Fin n × Fin d), ∀ Φ' ∈ schA F (Fin n × Fin d), ∀ a : ℂ,
      l ξ (a • Φ + Φ') = a * l ξ Φ + l ξ Φ' := by
    intro ξ Φ hΦ Φ' hΦ' a
    have m1 := hEv.maps _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Φ hΦ)
    have m2 := hEv.maps _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Φ' hΦ')
    simp only [hl]
    rw [rho_lin, map_add, map_smul, GlobalTheory.WeilM.thetaSum_add F (Submodule.smul_mem _ a m1) m2, GlobalTheory.WeilM.thetaSum_smul]
  have ladd : ∀ ξ, ∀ Φ ∈ schA F (Fin n × Fin d), ∀ Φ' ∈ schA F (Fin n × Fin d), l ξ (Φ + Φ') = l ξ Φ + l ξ Φ' := by
    intro ξ Φ hΦ Φ' hΦ'
    simpa using lin ξ Φ hΦ Φ' hΦ' 1
  have l0 : ∀ ξ, l ξ 0 = 0 := by
    intro ξ
    have h := ladd ξ 0 (zero_mem _) 0 (zero_mem _)
    simp only [add_zero] at h
    linear_combination -h
  have lsmul : ∀ ξ, ∀ Φ ∈ schA F (Fin n × Fin d), ∀ a : ℂ, l ξ (a • Φ) = a * l ξ Φ := by
    intro ξ Φ hΦ a
    simpa [l0] using lin ξ Φ hΦ 0 (zero_mem _) a
  have hA := GlobalTheory.T.adapted_evaluation_good_model hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hEv hP.base hP.good ⟨r, s, r', s', hP.herm, hP.skew⟩
  have summ : ∀ Φ ∈ schA F (Fin n × Fin d), Summable fun ξ => ‖l ξ Φ‖ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      obtain ⟨s₀, C, -, hC⟩ := hA g hg
      exact summable_of_sum_le (fun _ => norm_nonneg _) (hC f)
    | zero => simp [l0]
    | add x y hx hy ihx ihy =>
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_) (ihx.add ihy)
      rw [ladd ξ x hx y hy]
      exact norm_add_le _ _
    | smul a x hx ih =>
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_) (ih.mul_left ‖a‖)
      rw [lsmul ξ x hx a, norm_mul]
  have adm : ∀ c : (Fin n → E) → ℂ, (∃ b : ℝ, ∀ ξ, ‖c ξ‖ ≤ b) →
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
          rw [Submodule.coe_add, ladd ξ _ Φ.2 _ Φ'.2]
          ring
        map_smul' := fun a Φ => by
          simp only [RingHom.id_apply, SetLike.val_smul, smul_eq_mul]
          rw [← tsum_mul_left]
          congr 1
          funext ξ
          rw [lsmul ξ _ Φ.2 a]
          ring }
    obtain ⟨L, hL⟩ := LinearMap.exists_extend Lc
    have hLe : ∀ Φ (hΦ : Φ ∈ schA F (Fin n × Fin d)), L Φ = Lc ⟨Φ, hΦ⟩ := fun Φ hΦ => by
      have := LinearMap.congr_fun hL ⟨Φ, hΦ⟩
      simpa using this
    refine ⟨L, ?_, fun Φ hΦ => hLe Φ hΦ⟩
    intro g hg
    have hmem : ∀ f : SInf F (Fin n × Fin d), pureA F f g ∈ schA F (Fin n × Fin d) :=
      fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
    obtain ⟨s₀, C, hC0, hC⟩ := hA g hg
    refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => Lc ⟨pureA F f g, hmem f⟩) ?_ ?_ ?_, fun f => ?_⟩
    · intro f₁ f₂
      rw [← map_add]
      congr 1
      apply Subtype.ext
      funext x
      simp [pureA, add_mul]
    · intro a f
      rw [RingHom.id_apply, ← map_smul]
      congr 1
      apply Subtype.ext
      funext x
      simp [pureA, mul_assoc]
    · refine ⟨s₀, max b 0 * C, mul_nonneg (le_max_right _ _) hC0, fun f => ?_⟩
      have hsn := summ _ (hmem f)
      calc ‖Lc ⟨pureA F f g, hmem f⟩‖ = ‖∑' ξ, c ξ * l ξ (pureA F f g)‖ := rfl
        _ ≤ ∑' ξ, ‖c ξ * l ξ (pureA F f g)‖ := norm_tsum_le_tsum_norm (by
            refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_) (hsn.mul_left (max b 0))
            rw [norm_mul]; exact mul_le_mul_of_nonneg_right ((hb ξ).trans (le_max_left _ _)) (norm_nonneg _))
        _ ≤ ∑' ξ, max b 0 * ‖l ξ (pureA F f g)‖ := by
            refine Summable.tsum_le_tsum (fun ξ => ?_) ?_ (hsn.mul_left _)
            · rw [norm_mul]; exact mul_le_mul_of_nonneg_right ((hb ξ).trans (le_max_left _ _)) (norm_nonneg _)
            · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_) (hsn.mul_left (max b 0))
              rw [norm_mul]; exact mul_le_mul_of_nonneg_right ((hb ξ).trans (le_max_left _ _)) (norm_nonneg _)
        _ = max b 0 * ∑' ξ, ‖l ξ (pureA F f g)‖ := tsum_mul_left
        _ ≤ max b 0 * (C * (s₀.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
            exact hsn.tsum_le_of_sum_le (hC f)
        _ = max b 0 * C * (s₀.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f := by ring
    · rw [hLe _ (hmem f)]
      rfl
  have hpres : ∀ u : UA σ W.J, om (1, u) Ψ ∈ schA F (Fin n × Fin d) := fun u =>
    (IsUWeilPair.isUSplitting hP.weil).pres (1, u) Ψ hΨ
  obtain ⟨C, hC⟩ := tsum_norm_le_of_bdd_pairing (K := K) (fun u ξ => l ξ (om (1, u.1.1) Ψ)) (fun u => summ _ (hpres _)) (fun c hc => by
    obtain ⟨L, hL, hLe⟩ := adm c hc
    have hcont : Continuous fun p : UA σ X.J × UA σ W.J => L (om p Ψ) :=
      (IsUWeilPair.isUSplitting hP.weil).cont L hL Ψ hΨ
    have hc2 : Continuous fun u : unip σ W H' => L (om (1, u.1) Ψ) :=
      hcont.comp (continuous_const.prodMk continuous_subtype_val)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc2.continuousOn
    exact ⟨C, fun u => by rw [← hLe _ (hpres _)]; exact hC u.1 u.2⟩)
  exact ⟨C, fun u hu => ⟨summ _ (hpres _), hC ⟨u, hu⟩⟩⟩

end GlobalTheory.ThKSwapLoc
