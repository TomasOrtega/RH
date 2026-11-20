import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavinHaarCoord

namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set Filter MeasureTheory Metric

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  [μ.IsHaarMeasure]

/- English proof (translation)
Establish `: SecondCountableTopology G` using `h.secondCountableTopology`. Establish `: LocallyCompactSpace G` using `h.locallyCompactSpace`. Take `⟨S, T, Ψ, hSo, hTo, h0S, hST, hTS, hleft, hright, hΨ, hSN⟩` from `h.exists_prodExp_coord b`. Use `set p : (Fin d → ℝ) → 𝔸 := prodExpVal (fun i => (b i : 𝔸)) with hp_def`. Use `set P : (Fin d → ℝ) → G := h.prodExp ⇑b with hP_def`.

Establish `hPv : ∀ t, (((P t : G) : 𝔸ˣ) : 𝔸) = p t` using `fun t => h.val_prodExp _ t`. Establish `hpc : Continuous p` using `(contDiff_prodExpVal _).continuous`. Establish `hPc : Continuous P` using `h.continuous_prodExp _`. Establish `hp0 : p 0 = 1` using `prodExpVal_zero _`. Establish `hP0 : P 0 = 1` using `Subtype.ext (Units.ext (by rw [hPv, hp0]; rfl))`.

Establish `hΨ0 : Ψ 0 = 0`. Use `hleft 0 h0S` as an intermediate fact. Rewrite `this` using `[prodExpCoord_zero]`. Then use the resulting hypothesis. Use `set c : G → (Fin d → ℝ) := fun y => Ψ (logCoord b (((y : 𝔸ˣ) : 𝔸))) with hc_def`. Use `set Wc : Set G := {y | (((y : 𝔸ˣ) : 𝔸)) ∈ h.nhdOne ∧ logCoord b (((y : 𝔸ˣ) : 𝔸)) ∈ T} with hWc_def`.

Establish `hlogC : ContinuousOn (logCoord b) h.nhdOne` using `(contDiffOn_logCoord b).continuousOn.mono h.nhdOne_subset_target`. Establish `hNT : IsOpen (h.nhdOne ∩ logCoord b ⁻¹' T)` using `hlogC.isOpen_inter_preimage h.isOpen_nhdOne hTo`. Establish `hWco : IsOpen Wc` using `hNT.preimage (continuous_val_val G)`. Establish `hN : ∀ w ∈ T, p (Ψ w) ∈ h.nhdOne` using `fun w hw => hSN _ (hTS hw)`. Establish `hPcW : ∀ y ∈ Wc, P (c y) = y` using `fun y hy => h.prodExp_coord_eq b hright hN hy.1 hy.2`.

Establish `hcP : ∀ z ∈ S, c (P z) = z`. Introduce `z hz`. Use `show Ψ (logCoord b (((P z : G) : 𝔸ˣ) : 𝔸)) = z`. Rewrite using `[hPv]`. Conclude with `hleft z hz`.

Establish `hPW : ∀ z ∈ S, P z ∈ Wc` using `fun z hz => ⟨by rw [hPv]; exact hSN z hz, by rw [hPv]; exact hST hz⟩`. Use `set Λ : 𝔸 × (Fin d → ℝ) → (Fin d → ℝ) := fun q => Ψ (logCoord b (p q.2 * q.1)) with hΛ_def`. Use `set O : Set (𝔸 × (Fin d → ℝ)) := {q | p q.2 * q.1 ∈ h.nhdOne ∧ logCoord b (p q.2 * q.1) ∈ T} with hO_def`. Establish `hm : ContDiff ℝ ∞ (fun q : 𝔸 × (Fin d → ℝ) => p q.2 * q.1)` using `((contDiff_prodExpVal _).comp contDiff_snd).mul contDiff_fst`. Establish `hOo : IsOpen O` using `hNT.preimage hm.continuous`.

Establish `hΛs : ContDiffOn ℝ ∞ Λ O`. Establish `h1 : ContDiffOn ℝ ∞ (fun q : 𝔸 × (Fin d → ℝ) => logCoord b (p q.2 * q.1)) O` using `(contDiffOn_logCoord b).comp hm.contDiffOn (fun q hq => h.nhdOne_subset_target hq.1)`. Conclude with `hΨ.comp h1 (fun q hq => hq.2)`. Use `set J : 𝔸 × (Fin d → ℝ) → ℝ := fun q => (fderiv ℝ (fun z' => Λ (q.1, z')) q.2).det with hJ_def`. Establish `hJs : ContDiffOn ℝ ∞ J O`.

Introduce `q hq`. Apply `ContDiffAt.contDiffWithinAt` to reduce the goal to its premises. Establish `hΛq : ContDiffAt ℝ ∞ Λ q` using `hΛs.contDiffAt (hOo.mem_nhds hq)`. Establish `hfd : ContDiffAt ℝ ∞ (fun q' : 𝔸 × (Fin d → ℝ) => fderiv ℝ (fun z' => Λ (q'.1, z')) q'.2) q`. Use `ContDiffAt.fderiv (f := fun (q' : 𝔸 × (Fin d → ℝ)) (z' : Fin d → ℝ) => Λ (q'.1, z')) (g := Prod.snd) (n := ∞) ?_ contDiffAt_snd (by simp)` and prove the remaining obligations.

Establish `hpr : ContDiffAt ℝ ∞ (fun x : (𝔸 × (Fin d → ℝ)) × (Fin d → ℝ) => (x.1.1, x.2)) (q, q.2)` using `((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffAt`. Conclude with `hΛq.comp (q, q.2) hpr`. Conclude with `contDiff_det_pi.contDiffAt.comp q hfd`. Use `set Og : Set (𝔸 × (Fin d → ℝ)) := O ∩ J ⁻¹' Ioi 0 with hOg_def`. Establish `hOgo : IsOpen Og` using `hJs.continuousOn.isOpen_inter_preimage hOo isOpen_Ioi`.

Choose the witnesses or unpack the hypotheses as in `⟨R, hR, hRS⟩ : ∃ R > 0, closedBall (0 : Fin d → ℝ) R ⊆ S := by`. Take `⟨R', hR', hR'S⟩` from `Metric.isOpen_iff.1 hSo 0 h0S`. Conclude with `⟨R' / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hR'S⟩`. Establish `hJ1 : ∀ z ∈ S, J (1, z) = 1`. Introduce `z hz`.

Establish `heq : (fun z' => Λ ((1 : 𝔸), z')) =ᶠ[𝓝 z] id` using `by filter_upwards [hSo.mem_nhds hz] with z' hz' show Ψ (logCoord b (p z' * 1)) = z'`. Rewrite using `[mul_one]`. Conclude with `hleft z' hz'`. Use `show (fderiv ℝ (fun z' => Λ ((1 : 𝔸), z')) z).det = 1`. Rewrite using `[heq.fderiv_eq, fderiv_id]`.

Use `show LinearMap.det (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = 1`. Conclude with `LinearMap.det_id`. Establish `hsub : ({1} : Set 𝔸) ×ˢ closedBall (0 : Fin d → ℝ) R ⊆ Og`. Introduce and unpack `⟨a, z⟩ ⟨ha, hz⟩`. Rewrite `ha` using `[mem_singleton_iff]`.

Substitute `ha` using the available equality. Establish `hzS` using `hRS hz`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show p z * 1 ∈ h.nhdOne`. Rewrite using `[mul_one]`.

Conclude with `hSN z hzS`. Use `show logCoord b (p z * 1) ∈ T`. Rewrite using `[mul_one]`. Conclude with `hST hzS`. Use `show 0 < J (1, z)`.

Rewrite using `[hJ1 z hzS]`. Conclude with `one_pos`. Take `⟨u, v, hu, hv, h1u, hRv, huv⟩` from `generalized_tube_lemma isCompact_singleton (isCompact_closedBall 0 R) hOgo hsub`. Use `set Q : (Fin d → ℝ) × 𝔸 → 𝔸 := fun q => ((((P q.1)⁻¹ : G) : 𝔸ˣ) : 𝔸) * q.2 with hQ_def`. Establish `hQc : Continuous Q` using `((continuous_val_val G).comp (hPc.comp continuous_fst).inv).mul continuous_snd`.

Establish `hQ0 : Q (0, 1) = 1` using `by simp [hQ_def, hP0]`. Establish `hQp : ∀ z a, Q (z, p z * a) = a`. Introduce `z a`. Use `show ((((P z)⁻¹ : G) : 𝔸ˣ) : 𝔸) * (p z * a) = a`. Rewrite using `[← hPv, ← mul_assoc]`.

Establish `: ((((P z)⁻¹ : G) : 𝔸ˣ) : 𝔸) * (((P z : G) : 𝔸ˣ) : 𝔸) = 1`. Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]`. Both sides reduce to the same expression. Rewrite using `[this, one_mul]`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, hδu⟩ : ∃ δ > 0, ∀ z w, dist z 0 < δ → dist w 1 < δ → Q (z, w) ∈ u := by`.

Establish `hmem : Q ⁻¹' u ∈ 𝓝 ((0 : Fin d → ℝ), (1 : 𝔸))` using `hQc.continuousAt.preimage_mem_nhds (hu.mem_nhds (by rw [hQ0]; exact h1u rfl))`. Take `⟨δ, hδ, hball⟩` from `Metric.mem_nhds_iff.1 hmem`. Use `⟨δ, hδ, fun z w hz hw => hball ?_⟩` and prove the remaining obligations. Rewrite using `[mem_ball, Prod.dist_eq]`. Conclude with `max_lt hz hw`.

Choose the witnesses or unpack the hypotheses as in `⟨δ₂, hδ₂, hδ₂p⟩ : ∃ δ₂ > 0, ∀ z, dist z 0 < δ₂ → dist (p z) 1 < δ / 4 := by`. Take `⟨δ₂, hδ₂, H⟩` from `Metric.continuousAt_iff.1 hpc.continuousAt (δ / 4) (by positivity)`. Conclude with `⟨δ₂, hδ₂, fun z hz => by rw [← hp0]; exact H hz⟩`. Use `set r : ℝ := min (δ / 4) (R / 2) with hr_def`. Establish `hr : 0 < r` using `lt_min (by positivity) (by positivity)`.

Use `set rβ : ℝ := min (δ₂ / 2) (R / 2) with hrβ_def`. Establish `hrβ : 0 < rβ` using `lt_min (by positivity) (by positivity)`. Establish `h2rR : 2 * r ≤ R` using `by have := min_le_right (δ / 4) (R / 2); linarith`. Establish `h2rδ : 2 * r < δ` using `by have := min_le_left (δ / 4) (R / 2); linarith`. Establish `hrβR : rβ ≤ R` using `by have := min_le_right (δ₂ / 2) (R / 2); linarith`.

Establish `hrβδ : rβ < δ₂` using `by have := min_le_left (δ₂ / 2) (R / 2); linarith`. Set `θ : ContDiffBump (0 : Fin d → ℝ)` to `⟨r, 2 * r, hr, by linarith⟩`. Set `β : ContDiffBump (0 : Fin d → ℝ)` to `⟨rβ / 2, rβ, by positivity, by linarith⟩`. Set `χ : ContDiffBump (1 : 𝔸)` to `⟨δ / 4, δ / 2, by positivity, by linarith⟩`. Establish `hχ1 : ∀ w, dist w 1 < δ / 4 → χ w = 1` using `fun w hw => χ.one_of_mem_closedBall (mem_closedBall.2 hw.le)`.

Establish `hχ0 : ∀ w, χ w ≠ 0 → dist w 1 < δ / 2` using `fun w hw => by`. Establish `: w ∈ Function.support χ` using `hw`. Rewrite `this` using `[χ.support_eq]`. Conclude with `this`. Establish `hθ1 : ∀ z ∈ ball (0 : Fin d → ℝ) r, θ z = 1` using `fun z hz => θ.one_of_mem_closedBall (ball_subset_closedBall hz)`.

Establish `hθ0 : ∀ z, θ z ≠ 0 → dist z 0 < 2 * r` using `fun z hz => by`. Establish `: z ∈ Function.support θ` using `hz`. Rewrite `this` using `[θ.support_eq]`. Conclude with `this`. Establish `hβ0 : ∀ s, β s ≠ 0 → dist s 0 < rβ` using `fun s hs => by`.

Establish `: s ∈ Function.support β` using `hs`. Rewrite `this` using `[β.support_eq]`. Conclude with `this`. Establish `hps : ∀ s, dist s 0 < rβ → dist (p s) 1 < δ / 4` using `fun s hs => hδ₂p s (hs.trans hrβδ)`. Establish `hUV : ∀ a z, dist z 0 ≤ 2 * r → dist (p z * a) 1 < δ → (a, z) ∈ Og`.

Introduce `a z hz hw`. Establish `h1 : Q (z, p z * a) ∈ u` using `hδu z _ (by linarith) hw`. Rewrite `h1` using `[hQp]`. Conclude with `huv ⟨h1, hRv (mem_closedBall.2 (by linarith))⟩`. Establish `hkey : ∀ (x : G) (z : Fin d → ℝ), ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ∈ O → P (Λ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z)) = P z * x⁻¹`.

Introduce `x z hq`. Establish `hv : (((P z * x⁻¹ : G) : 𝔸ˣ) : 𝔸) = p z * (((x⁻¹ : G) : 𝔸ˣ) : 𝔸)`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, hPv]`. Establish `hW : P z * x⁻¹ ∈ Wc` using `⟨by rw [hv]; exact hq.1, by rw [hv]; exact hq.2⟩`. Use `hPcW _ hW` as an intermediate fact.

Rewrite `this` using `[show c (P z * x⁻¹) = Λ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) by show Ψ (logCoord b (((P z * x⁻¹ : G) : 𝔸ˣ) : 𝔸)) = _; rw [hv]]`. Then use the resulting hypothesis. Use `set g₀ : 𝔸 × (Fin d → ℝ) → ℝ := fun q => θ q.2 * χ (p q.2 * q.1) with hg₀_def`. Use `set f₀ : 𝔸 × (Fin d → ℝ) → ℝ := fun q => β (Λ q) * J q with hf₀_def`. Use `set Ξ : 𝔸 × (Fin d → ℝ) → ℝ := fun q => g₀ q • f₀ q with hΞ_def`. Establish `hg₀c : ContDiff ℝ ∞ g₀` using `(θ.contDiff.comp contDiff_snd).mul (χ.contDiff.comp hm)`.

Establish `hf₀ : ContDiffOn ℝ ∞ f₀ Og` using `((β.contDiff.comp_contDiffOn hΛs).mul hJs).mono inter_subset_left`. Use `set K₀ : Set (𝔸 × (Fin d → ℝ)) := {q | dist q.2 0 ≤ 2 * r ∧ dist (p q.2 * q.1) 1 ≤ δ / 2} with hK₀_def`. Establish `hK₀cl : IsClosed K₀` using `(isClosed_le (continuous_snd.dist continuous_const) continuous_const).inter (isClosed_le (hm.continuous.dist continuous_const) continuous_const)`. Establish `hg₀K : ∀ q, g₀ q ≠ 0 → q ∈ K₀`. Introduce `q hq`.

Establish `h1 : θ q.2 ≠ 0` using `left_ne_zero_of_mul hq`. Establish `h2 : χ (p q.2 * q.1) ≠ 0` using `right_ne_zero_of_mul hq`. Conclude with `⟨(hθ0 _ h1).le, (hχ0 _ h2).le⟩`. Establish `hK₀Og : K₀ ⊆ Og` using `fun q hq => hUV q.1 q.2 hq.1 (by linarith [hq.2])`. Establish `htsg : tsupport g₀ ⊆ K₀` using `closure_minimal (fun q hq => hg₀K q hq) hK₀cl`.

Establish `hΞc : ContDiff ℝ ∞ Ξ` using `contDiff_smul_of_tsupport hOgo hf₀ hg₀c (htsg.trans hK₀Og)`. Establish `hK₀cpt : IsCompact K₀`. Establish `hsub' : K₀ ⊆ (fun q : (Fin d → ℝ) × 𝔸 => (Q q, q.1)) '' (closedBall 0 (2 * r) ×ˢ closedBall 1 (δ / 2))`. Introduce `q hq`. Use `⟨(q.2, p q.2 * q.1), ⟨mem_closedBall.2 hq.1, mem_closedBall.2 hq.2⟩, ?_⟩` and prove the remaining obligations.

Use `show (Q (q.2, p q.2 * q.1), q.2) = q`. Rewrite using `[hQp]`. Conclude with `(((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (hQc.prodMk continuous_fst)).of_isClosed_subset hK₀cl hsub'`. Establish `hΞ0 : ∀ q, q ∉ K₀ → Ξ q = 0`. Introduce `q hq`.

Establish `: g₀ q = 0` using `by by_contra hne; exact hq (hg₀K q hne)`. Simplify using `[hΞ_def, this]`. Establish `hΞs : HasCompactSupport Ξ` using `HasCompactSupport.intro hK₀cpt hΞ0`. Establish `hΞnn : ∀ q, 0 ≤ Ξ q`. Introduce `q`.

Distinguish the cases in `hq : q ∈ K₀`. Establish `hJq : 0 < J q` using `(hK₀Og hq).2`. Conclude with `smul_nonneg (mul_nonneg θ.nonneg χ.nonneg) (mul_nonneg β.nonneg hJq.le)`. Rewrite using `[hΞ0 q hq]`. Use `set X₀ : Set G := (fun q : (Fin d → ℝ) × (Fin d → ℝ) => (P q.1)⁻¹ * P q.2) '' (closedBall 0 rβ ×ˢ closedBall 0 (2 * r)) with hX₀_def`.

Establish `hX₀ : IsCompact X₀` using `((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image ((hPc.comp continuous_fst).inv.mul (hPc.comp continuous_snd))`. Establish `hsuppx : ∀ (x : G) (z : Fin d → ℝ), Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ≠ 0 → x ∈ X₀ ∧ dist z 0 < 2 * r`. Introduce `x z hne`. Use `set a : 𝔸 := (((x⁻¹ : G) : 𝔸ˣ) : 𝔸)`. Establish `hg : g₀ (a, z) ≠ 0` using `left_ne_zero_of_mul hne`.

Establish `hf : f₀ (a, z) ≠ 0` using `right_ne_zero_of_mul hne`. Establish `hzr : dist z 0 < 2 * r` using `hθ0 z (left_ne_zero_of_mul hg)`. Establish `hw : dist (p z * a) 1 < δ / 2` using `hχ0 _ (right_ne_zero_of_mul hg)`. Establish `hq : (a, z) ∈ Og` using `hUV a z hzr.le (by linarith)`. Establish `hs : dist (Λ (a, z)) 0 < rβ` using `hβ0 _ (left_ne_zero_of_mul hf)`.

Establish `hk` using `hkey x z hq.1`. Use `⟨⟨(Λ (a, z), z), ⟨mem_closedBall.2 hs.le, mem_closedBall.2 hzr.le⟩, ?_⟩, hzr⟩` and prove the remaining obligations. Use `show (P (Λ (a, z)))⁻¹ * P z = x`. Rewrite using `[hk]`. Use `group`.

Use `set D : (Fin d → ℝ) → ℝ := fun z => ∫ x, Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ∂μ with hD_def`. Establish `hu_c : Continuous (fun x : G => (((x⁻¹ : G) : 𝔸ˣ) : 𝔸))` using `(continuous_val_val G).comp continuous_inv`. Establish `hDeq : D = fun z => ∫ x, Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ∂(μ.restrict X₀)`. Use function extensionality and compare the values at `z`. Use `(setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Conclude with `hx (hsuppx x z hne).1`. Establish `: IsFiniteMeasure (μ.restrict X₀)` using `isFiniteMeasure_restrict.2 hX₀.measure_lt_top.ne`. Establish `hDs : ContDiff ℝ ∞ D`. Rewrite using `[hDeq, contDiff_infty]`.

Introduce `n`. Conclude with `contDiff_integral_comp_of_hasCompactSupport (μ.restrict X₀) hu_c n Ξ hΞc hΞs`. Establish `hDpos : ∀ z ∈ ball (0 : Fin d → ℝ) r, 0 < D z`. Introduce `z hz`. Use `set F : G → ℝ := fun x => Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) with hF_def`.

Establish `hFc : Continuous F` using `hΞc.continuous.comp (hu_c.prodMk continuous_const)`. Establish `hFs : HasCompactSupport F` using `HasCompactSupport.intro hX₀ (fun x hx => by`. Assume the negation of the conclusion as `hne`. Conclude with `hx (hsuppx x z hne).1)`. Establish `hFi : Integrable F μ` using `hFc.integrable_of_hasCompactSupport hFs`.

Establish `hFpos : 0 < F (P z)` using `by set a₀ : 𝔸 := ((((P z)⁻¹ : G) : 𝔸ˣ) : 𝔸) with ha₀`. Establish `h1 : p z * a₀ = 1`. Rewrite using `[ha₀, ← hPv, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]`. Both sides reduce to the same expression. Establish `hzr : dist z 0 < r` using `mem_ball.1 hz`.

Establish `hq : (a₀, z) ∈ Og` using `hUV _ z (by linarith) (by rw [h1, dist_self]; exact hδ)`. Establish `hΛ0 : Λ (a₀, z) = 0` using `by show Ψ (logCoord b (p z * a₀)) = 0`. Rewrite using `[h1, logCoord_one, hΨ0]`. Establish `hg1 : g₀ (a₀, z) = 1` using `by show θ z * χ (p z * a₀) = 1`. Rewrite using `[h1, hθ1 z hz, χ.one_of_mem_closedBall (mem_closedBall_self χ.rIn_pos.le), one_mul]`.

Use `show 0 < g₀ (a₀, z) • f₀ (a₀, z)`. Rewrite using `[hg1, one_smul]`. Use `show 0 < β (Λ (a₀, z)) * J (a₀, z)`. Rewrite using `[hΛ0, β.one_of_mem_closedBall (mem_closedBall_self β.rIn_pos.le), one_mul]`. Conclude with `hq.2`.

Use `show 0 < ∫ x, F x ∂μ`. Rewrite using `[integral_pos_iff_support_of_nonneg (fun x => hΞnn _) hFi]`. Conclude with `hFc.isOpen_support.measure_pos μ ⟨P z, hFpos.ne'⟩`. Establish `hC : ∀ (ψ₀ : G → ℂ), tsupport ψ₀ ⊆ P '' ball 0 r → ∀ x : G, ∫ s, (β s : ℂ) * ψ₀ (P s * x) = ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ)`. Introduce `ψ₀ hψsupp x`.

Use `set a : 𝔸 := (((x⁻¹ : G) : 𝔸ˣ) : 𝔸) with ha`. Use `set U : Set (Fin d → ℝ) := ball 0 r ∩ {z | dist (p z * a) 1 < δ / 2} with hU_def`. Establish `hUo : IsOpen U` using `isOpen_ball.inter (isOpen_lt ((hpc.mul continuous_const).dist continuous_const) continuous_const)`. Establish `hUOg : ∀ z ∈ U, (a, z) ∈ Og` using `fun z hz => hUV a z (by have := mem_ball.1 hz.1; linarith) (by have h2 : dist (p z * a) 1 < δ / 2 := hz.2; linarith)`. Use `set Λx : (Fin d → ℝ) → (Fin d → ℝ) := fun z => Λ (a, z) with hΛx_def`.

Establish `hΛxd : ∀ z ∈ U, HasFDerivWithinAt Λx (fderiv ℝ Λx z) U z`. Introduce `z hz`. Establish `h1 : ContDiffAt ℝ ∞ Λ (a, z)` using `hΛs.contDiffAt (hOo.mem_nhds (hUOg z hz).1)`. Establish `h2 : DifferentiableAt ℝ Λx z` using `(h1.differentiableAt (by simp)).comp z ((differentiableAt_const a).prodMk differentiableAt_id)`. Conclude with `h2.hasFDerivAt.hasFDerivWithinAt`.

Establish `hΛxP : ∀ z ∈ U, P (Λx z) = P z * x⁻¹` using `fun z hz => hkey x z (hUOg z hz).1`. Establish `hballS : ∀ z ∈ ball (0 : Fin d → ℝ) r, z ∈ S` using `fun z hz => hRS (mem_closedBall.2 (by have := mem_ball.1 hz; linarith))`. Establish `hinj : InjOn Λx U`. Introduce `z₁ hz₁ z₂ hz₂ heq`. Establish `e1` using `hΛxP z₁ hz₁`.

Establish `e2` using `hΛxP z₂ hz₂`. Rewrite `e1` using `[heq, e2]`. Establish `e3 : P z₁ = P z₂` using `(mul_right_cancel e1).symm`. Rewrite using `[← hcP z₁ (hballS z₁ hz₁.1), ← hcP z₂ (hballS z₂ hz₂.1), e3]`. Establish `hcov` using `integral_image_eq_integral_abs_det_fderiv_smul volume hUo.measurableSet hΛxd hinj (fun s => (β s : ℂ) * ψ₀ (P s * x))`.

Establish `hL : ∫ s in Λx '' U, (β s : ℂ) * ψ₀ (P s * x) = ∫ s, (β s : ℂ) * ψ₀ (P s * x)`. Use `setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hβs : β s ≠ 0`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Establish `hψs : ψ₀ (P s * x) ≠ 0` using `right_ne_zero_of_mul hne`. Establish `hsr : dist s 0 < rβ` using `hβ0 s hβs`.

Take `⟨z, hz, hPz⟩` from `hψsupp (subset_tsupport _ hψs)`. Establish `hsS : s ∈ S` using `hRS (mem_closedBall.2 (by linarith))`. Establish `hw : p z * a = p s`. Establish `e : P z * x⁻¹ = P s` using `by rw [hPz]; group`. Use `congrArg (fun y : G => (((y : G) : 𝔸ˣ) : 𝔸)) e` as an intermediate fact.

Simplify `this` using `only [Subgroup.coe_mul, Units.val_mul, hPv]`. Establish `hzU : z ∈ U` using `⟨hz, by show dist (p z * a) 1 < δ / 2`. Rewrite using `[hw]`. Combine the linear relations using `[hps s hsr]⟩`. Apply `hs` to reduce the goal to its premises.

Use `⟨z, hzU, ?_⟩` and prove the remaining obligations. Use `show Ψ (logCoord b (p z * a)) = s`. Rewrite using `[hw]`. Conclude with `hleft s hsS`. Establish `hR : ∫ z in U, |(fderiv ℝ Λx z).det| • ((β (Λx z) : ℂ) * ψ₀ (P (Λx z) * x)) = ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (Ξ (a, z) : ℂ)`.

Rewrite using `[← integral_indicator hUo.measurableSet, ← integral_indicator measurableSet_ball]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Distinguish the cases in `hzb : z ∈ ball (0 : Fin d → ℝ) r`. Rewrite using `[indicator_of_mem hzb]`.

Distinguish the cases in `hzU : z ∈ U`. Rewrite using `[indicator_of_mem hzU]`. Establish `hq` using `hUOg z hzU`. Establish `hJpos : 0 < J (a, z)` using `hq.2`. Establish `hdet : |(fderiv ℝ Λx z).det| = J (a, z)` using `abs_of_pos hJpos`.

Rewrite using `[hdet, hΛxP z hzU, show P z * x⁻¹ * x = P z by group]`. Use `show J (a, z) • ((β (Λ (a, z)) : ℂ) * ψ₀ (P z)) = ψ₀ (P z) * (((θ z * χ (p z * a)) • (β (Λ (a, z)) * J (a, z)) : ℝ) : ℂ)`. Distinguish the cases in `hβz : β (Λ (a, z)) = 0`. Rewrite using `[hβz]`. Simplify using the standard rewrite rules.

Establish `hs` using `hβ0 _ hβz`. Establish `hpv : p (Λ (a, z)) = p z * a`. Use `congrArg (fun y : G => (((y : G) : 𝔸ˣ) : 𝔸)) (hΛxP z hzU)` as an intermediate fact. Simplify `this` using `only [Subgroup.coe_mul, Units.val_mul, hPv]`. Establish `hχ : χ (p z * a) = 1` using `hχ1 _ (by rw [← hpv]; exact hps _ hs)`.

Rewrite using `[hχ, hθ1 z hzb, Complex.real_smul, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[indicator_of_notMem hzU]`. Establish `hnot : ¬ dist (p z * a) 1 < δ / 2` using `fun h' => hzU ⟨hzb, h'⟩`.

Establish `hχ : χ (p z * a) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hnot (hχ0 _ hne)`. Use `show 0 = ψ₀ (P z) * (((θ z * χ (p z * a)) • (β (Λ (a, z)) * J (a, z)) : ℝ) : ℂ)`. Rewrite using `[hχ]`.

Simplify using the standard rewrite rules. Rewrite using `[indicator_of_notMem hzb, indicator_of_notMem (fun h' => hzb h'.1)]`. Rewrite using `[← hL, hcov, hR]`. Establish `hβint : 0 < ∫ s, β s` using `β.integral_pos`. Use `⟨r, fun z => D z / ∫ s, β s, c, Wc, hr, hDs.div_const _, fun z hz => div_pos (hDpos z hz) hβint, hWco, ?_, hPcW, ?_, ?_⟩` and prove the remaining obligations.

Introduce `z hz`. Establish `hzS : z ∈ S` using `hRS (mem_closedBall.2 (by have := mem_ball.1 hz; linarith))`. Conclude with `⟨hPW z hzS, hcP z hzS⟩`. Introduce `g hg set gv : 𝔸 := (((g : G) : 𝔸ˣ) : 𝔸) with hgv`. Establish `h1 : ContDiffAt ℝ ∞ (fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0` using `(contDiff_const.mul ((contDiff_exp ℝ 𝔸).comp 𝔤.subtypeL.contDiff)).contDiffAt`.

Establish `h2 : ContDiffAt ℝ ∞ (logCoord b) gv` using `(contDiffOn_logCoord b).contDiffAt ((expPartialHomeomorph ℝ 𝔸).open_target.mem_nhds (h.nhdOne_subset_target hg.1))`. Establish `h3 : ContDiffAt ℝ ∞ Ψ (logCoord b gv)` using `hΨ.contDiffAt (hTo.mem_nhds hg.2)`. Establish `h0 : (fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0 = gv` using `by simp`. Establish `h2' : ContDiffAt ℝ ∞ (logCoord b) ((fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0)`. Rewrite using `[h0]`.

Conclude with `h2`. Establish `h21` using `h2'.comp (0 : 𝔤) h1`. Establish `h3' : ContDiffAt ℝ ∞ Ψ ((logCoord b ∘ fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0)` using `by show ContDiffAt ℝ ∞ Ψ (logCoord b ((fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0))`. Rewrite using `[h0]`. Conclude with `h3`.

Establish `h321` using `h3'.comp (0 : 𝔤) h21`. Use `h321.congr_of_eventuallyEq (Eventually.of_forall fun Y => ?_)` and prove the remaining obligations. Use `show Ψ (logCoord b (((g * h.expG Y : G) : 𝔸ˣ) : 𝔸)) = Ψ (logCoord b (gv * exp (Y : 𝔸)))`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, coe_expG]`. Introduce `ψ₀ hψc hψs hψsupp`.

Establish `hint1 : Integrable (Function.uncurry fun (s : Fin d → ℝ) (x : G) => (β s : ℂ) * ψ₀ (P s * x)) (volume.prod μ)`. Establish `hcont : Continuous (Function.uncurry fun (s : Fin d → ℝ) (x : G) => (β s : ℂ) * ψ₀ (P s * x))` using `(Complex.continuous_ofReal.comp (β.continuous.comp continuous_fst)).mul (hψc.comp ((hPc.comp continuous_fst).mul continuous_snd))`. Use `hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (((isCompact_closedBall (0 : Fin d → ℝ) rβ).prod hψs).image (continuous_fst.prodMk ((hPc.comp continuous_fst).inv.mul continuous_snd))) ?_)` and prove the remaining obligations. Introduce `q hq`. Assume the negation of the conclusion as `hne`.

Apply `hq` to reduce the goal to its premises. Establish `hβq : β q.1 ≠ 0` using `fun h0 => hne (by show (β q.1 : ℂ) * ψ₀ (P q.1 * q.2) = 0`. Rewrite using `[h0, Complex.ofReal_zero, zero_mul])`. Establish `hψq : ψ₀ (P q.1 * q.2) ≠ 0` using `right_ne_zero_of_mul hne`. Use `⟨(q.1, P q.1 * q.2), ⟨mem_closedBall.2 (hβ0 _ hβq).le, subset_tsupport _ hψq⟩, ?_⟩` and prove the remaining obligations.

Use `show (q.1, (P q.1)⁻¹ * (P q.1 * q.2)) = q`. Rewrite using `[inv_mul_cancel_left]`. Establish `hint2 : Integrable (Function.uncurry fun (x : G) (z : Fin d → ℝ) => ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ)) (μ.prod (volume.restrict (ball (0 : Fin d → ℝ) r)))`. Establish `hcont : Continuous (Function.uncurry fun (x : G) (z : Fin d → ℝ) => ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ))` using `(hψc.comp (hPc.comp continuous_snd)).mul (Complex.continuous_ofReal.comp (hΞc.continuous.comp ((hu_c.comp continuous_fst).prodMk continuous_snd)))`. Establish `hi : Integrable (Function.uncurry fun (x : G) (z : Fin d → ℝ) => ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ)) (μ.prod volume)`.

Use `hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (hX₀.prod (isCompact_closedBall (0 : Fin d → ℝ) (2 * r))) ?_)` and prove the remaining obligations. Introduce `q hq`. Assume the negation of the conclusion as `hne`. Establish `hΞq : Ξ ((((q.1⁻¹ : G) : 𝔸ˣ) : 𝔸), q.2) ≠ 0` using `fun h0 => hne (by show ψ₀ (P q.2) * (Ξ ((((q.1⁻¹ : G) : 𝔸ˣ) : 𝔸), q.2) : ℂ) = 0`. Rewrite using `[h0, Complex.ofReal_zero, mul_zero])`.

Take `⟨h1, h2⟩` from `hsuppx q.1 q.2 hΞq`. Conclude with `hq ⟨h1, mem_closedBall.2 h2.le⟩`. Establish `e : μ.prod (volume.restrict (ball (0 : Fin d → ℝ) r)) = (μ.prod volume).restrict (univ ×ˢ ball (0 : Fin d → ℝ) r)`. Rewrite using `[← Measure.prod_restrict, Measure.restrict_univ]`. Rewrite using `[e]`.

Conclude with `hi.restrict`. Establish `hA : ((∫ s, β s : ℝ) : ℂ) * ∫ y, ψ₀ y ∂μ = ∫ s, ∫ x, (β s : ℂ) * ψ₀ (P s * x) ∂μ`. Establish `e1 : ∀ s, ∫ x, (β s : ℂ) * ψ₀ (P s * x) ∂μ = (β s : ℂ) * ∫ y, ψ₀ y ∂μ`. Introduce `s`. Rewrite using `[integral_const_mul, integral_mul_left_eq_self]`.

Repeatedly rewrite using `[e1]`. Rewrite using `[integral_mul_const, integral_complex_ofReal]`. Establish `hmain : ((∫ s, β s : ℝ) : ℂ) * ∫ y, ψ₀ y ∂μ = ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (D z : ℂ)`. Rewrite using `[hA, integral_integral_swap hint1]`. Establish `e2 : (fun x : G => ∫ s, (β s : ℂ) * ψ₀ (P s * x)) = fun x => ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ)`.

Use function extensionality and compare the values at `(hC ψ₀ hψsupp)`. Rewrite using `[e2, integral_integral_swap hint2]`. Use `setIntegral_congr_fun measurableSet_ball (fun z _ => ?_)` and prove the remaining obligations. Use `show ∫ x, ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ) ∂μ = ψ₀ (P z) * (D z : ℂ)`. Rewrite using `[integral_const_mul, integral_complex_ofReal]`.

Establish `hβne : ((∫ s, β s : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hβint.ne'`. Establish `e3 : ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (((D z / ∫ s, β s) : ℝ) : ℂ) = ((∫ s, β s : ℝ) : ℂ)⁻¹ * ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (D z : ℂ)`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `z`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `show ∫ y, ψ₀ y ∂μ = ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (((D z / ∫ s, β s) : ℝ) : ℂ)`. Rewrite using `[e3, ← hmain, ← mul_assoc, inv_mul_cancel₀ hβne, one_mul]`.
-/
theorem exists_haar_density_prodExp {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ (r : ℝ) (ρ : (Fin d → ℝ) → ℝ) (c : G → (Fin d → ℝ)) (W : Set G), 0 < r ∧
      ContDiff ℝ ∞ ρ ∧ (∀ z ∈ ball (0 : Fin d → ℝ) r, 0 < ρ z) ∧ IsOpen W ∧
      (∀ z ∈ ball (0 : Fin d → ℝ) r, h.prodExp (⇑b) z ∈ W ∧ c (h.prodExp (⇑b) z) = z) ∧
      (∀ y ∈ W, h.prodExp (⇑b) (c y) = y) ∧
      (∀ g ∈ W, ContDiffAt ℝ ∞ (fun Y : 𝔤 => c (g * h.expG Y)) 0) ∧
      ∀ ψ₀ : G → ℂ, Continuous ψ₀ → HasCompactSupport ψ₀ →
        tsupport ψ₀ ⊆ h.prodExp (⇑b) '' ball 0 r →
        ∫ y, ψ₀ y ∂μ = ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (h.prodExp (⇑b) z) * (ρ z : ℂ) := by
  classical
  have : SecondCountableTopology G := h.secondCountableTopology
  have : LocallyCompactSpace G := h.locallyCompactSpace
  obtain ⟨S, T, Ψ, hSo, hTo, h0S, hST, hTS, hleft, hright, hΨ, hSN⟩ := h.exists_prodExp_coord b
  set p : (Fin d → ℝ) → 𝔸 := prodExpVal (fun i => (b i : 𝔸)) with hp_def
  set P : (Fin d → ℝ) → G := h.prodExp ⇑b with hP_def
  have hPv : ∀ t, (((P t : G) : 𝔸ˣ) : 𝔸) = p t := fun t => h.val_prodExp _ t
  have hpc : Continuous p := (contDiff_prodExpVal _).continuous
  have hPc : Continuous P := h.continuous_prodExp _
  have hp0 : p 0 = 1 := prodExpVal_zero _
  have hP0 : P 0 = 1 := Subtype.ext (Units.ext (by rw [hPv, hp0]; rfl))
  have hΨ0 : Ψ 0 = 0 := by
    have := hleft 0 h0S; rwa [prodExpCoord_zero] at this

  set c : G → (Fin d → ℝ) := fun y => Ψ (logCoord b (((y : 𝔸ˣ) : 𝔸))) with hc_def
  set Wc : Set G := {y | (((y : 𝔸ˣ) : 𝔸)) ∈ h.nhdOne ∧ logCoord b (((y : 𝔸ˣ) : 𝔸)) ∈ T}
    with hWc_def
  have hlogC : ContinuousOn (logCoord b) h.nhdOne :=
    (contDiffOn_logCoord b).continuousOn.mono h.nhdOne_subset_target
  have hNT : IsOpen (h.nhdOne ∩ logCoord b ⁻¹' T) :=
    hlogC.isOpen_inter_preimage h.isOpen_nhdOne hTo
  have hWco : IsOpen Wc := hNT.preimage (continuous_val_val G)
  have hN : ∀ w ∈ T, p (Ψ w) ∈ h.nhdOne := fun w hw => hSN _ (hTS hw)
  have hPcW : ∀ y ∈ Wc, P (c y) = y := fun y hy => h.prodExp_coord_eq b hright hN hy.1 hy.2
  have hcP : ∀ z ∈ S, c (P z) = z := by
    intro z hz
    show Ψ (logCoord b (((P z : G) : 𝔸ˣ) : 𝔸)) = z
    rw [hPv]; exact hleft z hz
  have hPW : ∀ z ∈ S, P z ∈ Wc := fun z hz =>
    ⟨by rw [hPv]; exact hSN z hz, by rw [hPv]; exact hST hz⟩

  set Λ : 𝔸 × (Fin d → ℝ) → (Fin d → ℝ) := fun q => Ψ (logCoord b (p q.2 * q.1)) with hΛ_def
  set O : Set (𝔸 × (Fin d → ℝ)) := {q | p q.2 * q.1 ∈ h.nhdOne ∧ logCoord b (p q.2 * q.1) ∈ T}
    with hO_def
  have hm : ContDiff ℝ ∞ (fun q : 𝔸 × (Fin d → ℝ) => p q.2 * q.1) :=
    ((contDiff_prodExpVal _).comp contDiff_snd).mul contDiff_fst
  have hOo : IsOpen O := hNT.preimage hm.continuous
  have hΛs : ContDiffOn ℝ ∞ Λ O := by
    have h1 : ContDiffOn ℝ ∞ (fun q : 𝔸 × (Fin d → ℝ) => logCoord b (p q.2 * q.1)) O :=
      (contDiffOn_logCoord b).comp hm.contDiffOn (fun q hq => h.nhdOne_subset_target hq.1)
    exact hΨ.comp h1 (fun q hq => hq.2)
  set J : 𝔸 × (Fin d → ℝ) → ℝ := fun q => (fderiv ℝ (fun z' => Λ (q.1, z')) q.2).det
    with hJ_def
  have hJs : ContDiffOn ℝ ∞ J O := by
    intro q hq
    apply ContDiffAt.contDiffWithinAt
    have hΛq : ContDiffAt ℝ ∞ Λ q := hΛs.contDiffAt (hOo.mem_nhds hq)
    have hfd : ContDiffAt ℝ ∞
        (fun q' : 𝔸 × (Fin d → ℝ) => fderiv ℝ (fun z' => Λ (q'.1, z')) q'.2) q := by
      refine ContDiffAt.fderiv (f := fun (q' : 𝔸 × (Fin d → ℝ)) (z' : Fin d → ℝ) => Λ (q'.1, z'))
        (g := Prod.snd) (n := ∞) ?_ contDiffAt_snd (by simp)
      have hpr : ContDiffAt ℝ ∞
          (fun x : (𝔸 × (Fin d → ℝ)) × (Fin d → ℝ) => (x.1.1, x.2)) (q, q.2) :=
        ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
      exact hΛq.comp (q, q.2) hpr
    exact contDiff_det_pi.contDiffAt.comp q hfd
  set Og : Set (𝔸 × (Fin d → ℝ)) := O ∩ J ⁻¹' Ioi 0 with hOg_def
  have hOgo : IsOpen Og := hJs.continuousOn.isOpen_inter_preimage hOo isOpen_Ioi
  obtain ⟨R, hR, hRS⟩ : ∃ R > 0, closedBall (0 : Fin d → ℝ) R ⊆ S := by
    obtain ⟨R', hR', hR'S⟩ := Metric.isOpen_iff.1 hSo 0 h0S
    exact ⟨R' / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hR'S⟩
  have hJ1 : ∀ z ∈ S, J (1, z) = 1 := by
    intro z hz
    have heq : (fun z' => Λ ((1 : 𝔸), z')) =ᶠ[𝓝 z] id := by
      filter_upwards [hSo.mem_nhds hz] with z' hz'
      show Ψ (logCoord b (p z' * 1)) = z'
      rw [mul_one]; exact hleft z' hz'
    show (fderiv ℝ (fun z' => Λ ((1 : 𝔸), z')) z).det = 1
    rw [heq.fderiv_eq, fderiv_id]
    show LinearMap.det (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = 1
    exact LinearMap.det_id
  have hsub : ({1} : Set 𝔸) ×ˢ closedBall (0 : Fin d → ℝ) R ⊆ Og := by
    rintro ⟨a, z⟩ ⟨ha, hz⟩
    rw [mem_singleton_iff] at ha; subst ha
    have hzS := hRS hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show p z * 1 ∈ h.nhdOne
      rw [mul_one]; exact hSN z hzS
    · show logCoord b (p z * 1) ∈ T
      rw [mul_one]; exact hST hzS
    · show 0 < J (1, z)
      rw [hJ1 z hzS]; exact one_pos
  obtain ⟨u, v, hu, hv, h1u, hRv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_closedBall 0 R) hOgo hsub
  set Q : (Fin d → ℝ) × 𝔸 → 𝔸 := fun q => ((((P q.1)⁻¹ : G) : 𝔸ˣ) : 𝔸) * q.2 with hQ_def
  have hQc : Continuous Q :=
    ((continuous_val_val G).comp (hPc.comp continuous_fst).inv).mul continuous_snd
  have hQ0 : Q (0, 1) = 1 := by simp [hQ_def, hP0]
  have hQp : ∀ z a, Q (z, p z * a) = a := by
    intro z a
    show ((((P z)⁻¹ : G) : 𝔸ˣ) : 𝔸) * (p z * a) = a
    rw [← hPv, ← mul_assoc]
    have : ((((P z)⁻¹ : G) : 𝔸ˣ) : 𝔸) * (((P z : G) : 𝔸ˣ) : 𝔸) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, one_mul]
  obtain ⟨δ, hδ, hδu⟩ : ∃ δ > 0, ∀ z w, dist z 0 < δ → dist w 1 < δ → Q (z, w) ∈ u := by
    have hmem : Q ⁻¹' u ∈ 𝓝 ((0 : Fin d → ℝ), (1 : 𝔸)) :=
      hQc.continuousAt.preimage_mem_nhds (hu.mem_nhds (by rw [hQ0]; exact h1u rfl))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hmem
    refine ⟨δ, hδ, fun z w hz hw => hball ?_⟩
    rw [mem_ball, Prod.dist_eq]; exact max_lt hz hw
  obtain ⟨δ₂, hδ₂, hδ₂p⟩ : ∃ δ₂ > 0, ∀ z, dist z 0 < δ₂ → dist (p z) 1 < δ / 4 := by
    obtain ⟨δ₂, hδ₂, H⟩ := Metric.continuousAt_iff.1 hpc.continuousAt (δ / 4) (by positivity)
    exact ⟨δ₂, hδ₂, fun z hz => by rw [← hp0]; exact H hz⟩

  set r : ℝ := min (δ / 4) (R / 2) with hr_def
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  set rβ : ℝ := min (δ₂ / 2) (R / 2) with hrβ_def
  have hrβ : 0 < rβ := lt_min (by positivity) (by positivity)
  have h2rR : 2 * r ≤ R := by have := min_le_right (δ / 4) (R / 2); linarith
  have h2rδ : 2 * r < δ := by have := min_le_left (δ / 4) (R / 2); linarith
  have hrβR : rβ ≤ R := by have := min_le_right (δ₂ / 2) (R / 2); linarith
  have hrβδ : rβ < δ₂ := by have := min_le_left (δ₂ / 2) (R / 2); linarith
  let θ : ContDiffBump (0 : Fin d → ℝ) := ⟨r, 2 * r, hr, by linarith⟩
  let β : ContDiffBump (0 : Fin d → ℝ) := ⟨rβ / 2, rβ, by positivity, by linarith⟩
  let χ : ContDiffBump (1 : 𝔸) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hχ1 : ∀ w, dist w 1 < δ / 4 → χ w = 1 := fun w hw =>
    χ.one_of_mem_closedBall (mem_closedBall.2 hw.le)
  have hχ0 : ∀ w, χ w ≠ 0 → dist w 1 < δ / 2 := fun w hw => by
    have : w ∈ Function.support χ := hw
    rw [χ.support_eq] at this; exact this
  have hθ1 : ∀ z ∈ ball (0 : Fin d → ℝ) r, θ z = 1 := fun z hz =>
    θ.one_of_mem_closedBall (ball_subset_closedBall hz)
  have hθ0 : ∀ z, θ z ≠ 0 → dist z 0 < 2 * r := fun z hz => by
    have : z ∈ Function.support θ := hz
    rw [θ.support_eq] at this; exact this
  have hβ0 : ∀ s, β s ≠ 0 → dist s 0 < rβ := fun s hs => by
    have : s ∈ Function.support β := hs
    rw [β.support_eq] at this; exact this
  have hps : ∀ s, dist s 0 < rβ → dist (p s) 1 < δ / 4 := fun s hs => hδ₂p s (hs.trans hrβδ)
  have hUV : ∀ a z, dist z 0 ≤ 2 * r → dist (p z * a) 1 < δ → (a, z) ∈ Og := by
    intro a z hz hw
    have h1 : Q (z, p z * a) ∈ u := hδu z _ (by linarith) hw
    rw [hQp] at h1
    exact huv ⟨h1, hRv (mem_closedBall.2 (by linarith))⟩

  have hkey : ∀ (x : G) (z : Fin d → ℝ), ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ∈ O →
      P (Λ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z)) = P z * x⁻¹ := by
    intro x z hq
    have hv : (((P z * x⁻¹ : G) : 𝔸ˣ) : 𝔸) = p z * (((x⁻¹ : G) : 𝔸ˣ) : 𝔸) := by
      rw [Subgroup.coe_mul, Units.val_mul, hPv]
    have hW : P z * x⁻¹ ∈ Wc := ⟨by rw [hv]; exact hq.1, by rw [hv]; exact hq.2⟩
    have := hPcW _ hW
    rwa [show c (P z * x⁻¹) = Λ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) by
      show Ψ (logCoord b (((P z * x⁻¹ : G) : 𝔸ˣ) : 𝔸)) = _; rw [hv]] at this

  set g₀ : 𝔸 × (Fin d → ℝ) → ℝ := fun q => θ q.2 * χ (p q.2 * q.1) with hg₀_def
  set f₀ : 𝔸 × (Fin d → ℝ) → ℝ := fun q => β (Λ q) * J q with hf₀_def
  set Ξ : 𝔸 × (Fin d → ℝ) → ℝ := fun q => g₀ q • f₀ q with hΞ_def
  have hg₀c : ContDiff ℝ ∞ g₀ := (θ.contDiff.comp contDiff_snd).mul (χ.contDiff.comp hm)
  have hf₀ : ContDiffOn ℝ ∞ f₀ Og :=
    ((β.contDiff.comp_contDiffOn hΛs).mul hJs).mono inter_subset_left
  set K₀ : Set (𝔸 × (Fin d → ℝ)) := {q | dist q.2 0 ≤ 2 * r ∧ dist (p q.2 * q.1) 1 ≤ δ / 2}
    with hK₀_def
  have hK₀cl : IsClosed K₀ :=
    (isClosed_le (continuous_snd.dist continuous_const) continuous_const).inter
      (isClosed_le (hm.continuous.dist continuous_const) continuous_const)
  have hg₀K : ∀ q, g₀ q ≠ 0 → q ∈ K₀ := by
    intro q hq
    have h1 : θ q.2 ≠ 0 := left_ne_zero_of_mul hq
    have h2 : χ (p q.2 * q.1) ≠ 0 := right_ne_zero_of_mul hq
    exact ⟨(hθ0 _ h1).le, (hχ0 _ h2).le⟩
  have hK₀Og : K₀ ⊆ Og := fun q hq => hUV q.1 q.2 hq.1 (by linarith [hq.2])
  have htsg : tsupport g₀ ⊆ K₀ := closure_minimal (fun q hq => hg₀K q hq) hK₀cl
  have hΞc : ContDiff ℝ ∞ Ξ := contDiff_smul_of_tsupport hOgo hf₀ hg₀c (htsg.trans hK₀Og)
  have hK₀cpt : IsCompact K₀ := by
    have hsub' : K₀ ⊆ (fun q : (Fin d → ℝ) × 𝔸 => (Q q, q.1)) ''
        (closedBall 0 (2 * r) ×ˢ closedBall 1 (δ / 2)) := by
      intro q hq
      refine ⟨(q.2, p q.2 * q.1), ⟨mem_closedBall.2 hq.1, mem_closedBall.2 hq.2⟩, ?_⟩
      show (Q (q.2, p q.2 * q.1), q.2) = q
      rw [hQp]
    exact (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image
      (hQc.prodMk continuous_fst)).of_isClosed_subset hK₀cl hsub'
  have hΞ0 : ∀ q, q ∉ K₀ → Ξ q = 0 := by
    intro q hq
    have : g₀ q = 0 := by by_contra hne; exact hq (hg₀K q hne)
    simp [hΞ_def, this]
  have hΞs : HasCompactSupport Ξ := HasCompactSupport.intro hK₀cpt hΞ0
  have hΞnn : ∀ q, 0 ≤ Ξ q := by
    intro q
    by_cases hq : q ∈ K₀
    · have hJq : 0 < J q := (hK₀Og hq).2
      exact smul_nonneg (mul_nonneg θ.nonneg χ.nonneg) (mul_nonneg β.nonneg hJq.le)
    · rw [hΞ0 q hq]

  set X₀ : Set G := (fun q : (Fin d → ℝ) × (Fin d → ℝ) => (P q.1)⁻¹ * P q.2) ''
    (closedBall 0 rβ ×ˢ closedBall 0 (2 * r)) with hX₀_def
  have hX₀ : IsCompact X₀ :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image
      ((hPc.comp continuous_fst).inv.mul (hPc.comp continuous_snd))
  have hsuppx : ∀ (x : G) (z : Fin d → ℝ), Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ≠ 0 →
      x ∈ X₀ ∧ dist z 0 < 2 * r := by
    intro x z hne
    set a : 𝔸 := (((x⁻¹ : G) : 𝔸ˣ) : 𝔸)
    have hg : g₀ (a, z) ≠ 0 := left_ne_zero_of_mul hne
    have hf : f₀ (a, z) ≠ 0 := right_ne_zero_of_mul hne
    have hzr : dist z 0 < 2 * r := hθ0 z (left_ne_zero_of_mul hg)
    have hw : dist (p z * a) 1 < δ / 2 := hχ0 _ (right_ne_zero_of_mul hg)
    have hq : (a, z) ∈ Og := hUV a z hzr.le (by linarith)
    have hs : dist (Λ (a, z)) 0 < rβ := hβ0 _ (left_ne_zero_of_mul hf)
    have hk := hkey x z hq.1
    refine ⟨⟨(Λ (a, z), z), ⟨mem_closedBall.2 hs.le, mem_closedBall.2 hzr.le⟩, ?_⟩, hzr⟩
    show (P (Λ (a, z)))⁻¹ * P z = x
    rw [hk]; group
  set D : (Fin d → ℝ) → ℝ := fun z => ∫ x, Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ∂μ with hD_def
  have hu_c : Continuous (fun x : G => (((x⁻¹ : G) : 𝔸ˣ) : 𝔸)) :=
    (continuous_val_val G).comp continuous_inv
  have hDeq : D = fun z => ∫ x, Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) ∂(μ.restrict X₀) := by
    funext z
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    by_contra hne; exact hx (hsuppx x z hne).1
  have : IsFiniteMeasure (μ.restrict X₀) := isFiniteMeasure_restrict.2 hX₀.measure_lt_top.ne
  have hDs : ContDiff ℝ ∞ D := by
    rw [hDeq, contDiff_infty]
    intro n
    exact contDiff_integral_comp_of_hasCompactSupport (μ.restrict X₀) hu_c n Ξ hΞc hΞs
  have hDpos : ∀ z ∈ ball (0 : Fin d → ℝ) r, 0 < D z := by
    intro z hz
    set F : G → ℝ := fun x => Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) with hF_def
    have hFc : Continuous F := hΞc.continuous.comp (hu_c.prodMk continuous_const)
    have hFs : HasCompactSupport F := HasCompactSupport.intro hX₀ (fun x hx => by
      by_contra hne; exact hx (hsuppx x z hne).1)
    have hFi : Integrable F μ := hFc.integrable_of_hasCompactSupport hFs
    have hFpos : 0 < F (P z) := by
      set a₀ : 𝔸 := ((((P z)⁻¹ : G) : 𝔸ˣ) : 𝔸) with ha₀
      have h1 : p z * a₀ = 1 := by
        rw [ha₀, ← hPv, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
      have hzr : dist z 0 < r := mem_ball.1 hz
      have hq : (a₀, z) ∈ Og := hUV _ z (by linarith) (by rw [h1, dist_self]; exact hδ)
      have hΛ0 : Λ (a₀, z) = 0 := by
        show Ψ (logCoord b (p z * a₀)) = 0
        rw [h1, logCoord_one, hΨ0]
      have hg1 : g₀ (a₀, z) = 1 := by
        show θ z * χ (p z * a₀) = 1
        rw [h1, hθ1 z hz, χ.one_of_mem_closedBall (mem_closedBall_self χ.rIn_pos.le), one_mul]
      show 0 < g₀ (a₀, z) • f₀ (a₀, z)
      rw [hg1, one_smul]
      show 0 < β (Λ (a₀, z)) * J (a₀, z)
      rw [hΛ0, β.one_of_mem_closedBall (mem_closedBall_self β.rIn_pos.le), one_mul]
      exact hq.2
    show 0 < ∫ x, F x ∂μ
    rw [integral_pos_iff_support_of_nonneg (fun x => hΞnn _) hFi]
    exact hFc.isOpen_support.measure_pos μ ⟨P z, hFpos.ne'⟩

  have hC : ∀ (ψ₀ : G → ℂ), tsupport ψ₀ ⊆ P '' ball 0 r → ∀ x : G,
      ∫ s, (β s : ℂ) * ψ₀ (P s * x) =
        ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ) := by
    intro ψ₀ hψsupp x
    set a : 𝔸 := (((x⁻¹ : G) : 𝔸ˣ) : 𝔸) with ha
    set U : Set (Fin d → ℝ) := ball 0 r ∩ {z | dist (p z * a) 1 < δ / 2} with hU_def
    have hUo : IsOpen U := isOpen_ball.inter
      (isOpen_lt ((hpc.mul continuous_const).dist continuous_const) continuous_const)
    have hUOg : ∀ z ∈ U, (a, z) ∈ Og := fun z hz =>
      hUV a z (by have := mem_ball.1 hz.1; linarith)
        (by have h2 : dist (p z * a) 1 < δ / 2 := hz.2; linarith)
    set Λx : (Fin d → ℝ) → (Fin d → ℝ) := fun z => Λ (a, z) with hΛx_def
    have hΛxd : ∀ z ∈ U, HasFDerivWithinAt Λx (fderiv ℝ Λx z) U z := by
      intro z hz
      have h1 : ContDiffAt ℝ ∞ Λ (a, z) := hΛs.contDiffAt (hOo.mem_nhds (hUOg z hz).1)
      have h2 : DifferentiableAt ℝ Λx z :=
        (h1.differentiableAt (by simp)).comp z
          ((differentiableAt_const a).prodMk differentiableAt_id)
      exact h2.hasFDerivAt.hasFDerivWithinAt
    have hΛxP : ∀ z ∈ U, P (Λx z) = P z * x⁻¹ := fun z hz => hkey x z (hUOg z hz).1
    have hballS : ∀ z ∈ ball (0 : Fin d → ℝ) r, z ∈ S := fun z hz =>
      hRS (mem_closedBall.2 (by have := mem_ball.1 hz; linarith))
    have hinj : InjOn Λx U := by
      intro z₁ hz₁ z₂ hz₂ heq
      have e1 := hΛxP z₁ hz₁
      have e2 := hΛxP z₂ hz₂
      rw [heq, e2] at e1
      have e3 : P z₁ = P z₂ := (mul_right_cancel e1).symm
      rw [← hcP z₁ (hballS z₁ hz₁.1), ← hcP z₂ (hballS z₂ hz₂.1), e3]
    have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume hUo.measurableSet hΛxd
      hinj (fun s => (β s : ℂ) * ψ₀ (P s * x))
    have hL : ∫ s in Λx '' U, (β s : ℂ) * ψ₀ (P s * x) = ∫ s, (β s : ℂ) * ψ₀ (P s * x) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
      by_contra hne
      have hβs : β s ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      have hψs : ψ₀ (P s * x) ≠ 0 := right_ne_zero_of_mul hne
      have hsr : dist s 0 < rβ := hβ0 s hβs
      obtain ⟨z, hz, hPz⟩ := hψsupp (subset_tsupport _ hψs)
      have hsS : s ∈ S := hRS (mem_closedBall.2 (by linarith))
      have hw : p z * a = p s := by
        have e : P z * x⁻¹ = P s := by rw [hPz]; group
        have := congrArg (fun y : G => (((y : G) : 𝔸ˣ) : 𝔸)) e
        simpa only [Subgroup.coe_mul, Units.val_mul, hPv] using this
      have hzU : z ∈ U := ⟨hz, by
        show dist (p z * a) 1 < δ / 2
        rw [hw]; linarith [hps s hsr]⟩
      apply hs
      refine ⟨z, hzU, ?_⟩
      show Ψ (logCoord b (p z * a)) = s
      rw [hw]; exact hleft s hsS
    have hR : ∫ z in U, |(fderiv ℝ Λx z).det| • ((β (Λx z) : ℂ) * ψ₀ (P (Λx z) * x)) =
        ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (Ξ (a, z) : ℂ) := by
      rw [← integral_indicator hUo.measurableSet, ← integral_indicator measurableSet_ball]
      congr 1; funext z
      by_cases hzb : z ∈ ball (0 : Fin d → ℝ) r
      · rw [indicator_of_mem hzb]
        by_cases hzU : z ∈ U
        · rw [indicator_of_mem hzU]
          have hq := hUOg z hzU
          have hJpos : 0 < J (a, z) := hq.2
          have hdet : |(fderiv ℝ Λx z).det| = J (a, z) := abs_of_pos hJpos
          rw [hdet, hΛxP z hzU, show P z * x⁻¹ * x = P z by group]
          show J (a, z) • ((β (Λ (a, z)) : ℂ) * ψ₀ (P z)) =
            ψ₀ (P z) * (((θ z * χ (p z * a)) • (β (Λ (a, z)) * J (a, z)) : ℝ) : ℂ)
          by_cases hβz : β (Λ (a, z)) = 0
          · rw [hβz]; simp
          · have hs := hβ0 _ hβz
            have hpv : p (Λ (a, z)) = p z * a := by
              have := congrArg (fun y : G => (((y : G) : 𝔸ˣ) : 𝔸)) (hΛxP z hzU)
              simpa only [Subgroup.coe_mul, Units.val_mul, hPv] using this
            have hχ : χ (p z * a) = 1 := hχ1 _ (by rw [← hpv]; exact hps _ hs)
            rw [hχ, hθ1 z hzb, Complex.real_smul, smul_eq_mul]
            push_cast; ring
        · rw [indicator_of_notMem hzU]
          have hnot : ¬ dist (p z * a) 1 < δ / 2 := fun h' => hzU ⟨hzb, h'⟩
          have hχ : χ (p z * a) = 0 := by
            by_contra hne; exact hnot (hχ0 _ hne)
          show 0 = ψ₀ (P z) * (((θ z * χ (p z * a)) • (β (Λ (a, z)) * J (a, z)) : ℝ) : ℂ)
          rw [hχ]; simp
      · rw [indicator_of_notMem hzb, indicator_of_notMem (fun h' => hzb h'.1)]
    rw [← hL, hcov, hR]
  have hβint : 0 < ∫ s, β s := β.integral_pos
  refine ⟨r, fun z => D z / ∫ s, β s, c, Wc, hr, hDs.div_const _,
    fun z hz => div_pos (hDpos z hz) hβint, hWco, ?_, hPcW, ?_, ?_⟩
  · intro z hz
    have hzS : z ∈ S := hRS (mem_closedBall.2 (by have := mem_ball.1 hz; linarith))
    exact ⟨hPW z hzS, hcP z hzS⟩
  · intro g hg
    set gv : 𝔸 := (((g : G) : 𝔸ˣ) : 𝔸) with hgv
    have h1 : ContDiffAt ℝ ∞ (fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0 :=
      (contDiff_const.mul ((contDiff_exp ℝ 𝔸).comp 𝔤.subtypeL.contDiff)).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (logCoord b) gv :=
      (contDiffOn_logCoord b).contDiffAt
        ((expPartialHomeomorph ℝ 𝔸).open_target.mem_nhds (h.nhdOne_subset_target hg.1))
    have h3 : ContDiffAt ℝ ∞ Ψ (logCoord b gv) := hΨ.contDiffAt (hTo.mem_nhds hg.2)
    have h0 : (fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0 = gv := by simp
    have h2' : ContDiffAt ℝ ∞ (logCoord b) ((fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0) := by
      rw [h0]; exact h2
    have h21 := h2'.comp (0 : 𝔤) h1
    have h3' : ContDiffAt ℝ ∞ Ψ ((logCoord b ∘ fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0) := by
      show ContDiffAt ℝ ∞ Ψ (logCoord b ((fun Y : 𝔤 => gv * exp (Y : 𝔸)) 0))
      rw [h0]; exact h3
    have h321 := h3'.comp (0 : 𝔤) h21
    refine h321.congr_of_eventuallyEq (Eventually.of_forall fun Y => ?_)
    show Ψ (logCoord b (((g * h.expG Y : G) : 𝔸ˣ) : 𝔸)) = Ψ (logCoord b (gv * exp (Y : 𝔸)))
    rw [Subgroup.coe_mul, Units.val_mul, coe_expG]
  · intro ψ₀ hψc hψs hψsupp
    have hint1 : Integrable (Function.uncurry fun (s : Fin d → ℝ) (x : G) =>
        (β s : ℂ) * ψ₀ (P s * x)) (volume.prod μ) := by
      have hcont : Continuous (Function.uncurry fun (s : Fin d → ℝ) (x : G) =>
          (β s : ℂ) * ψ₀ (P s * x)) :=
        (Complex.continuous_ofReal.comp (β.continuous.comp continuous_fst)).mul
          (hψc.comp ((hPc.comp continuous_fst).mul continuous_snd))
      refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro
        (((isCompact_closedBall (0 : Fin d → ℝ) rβ).prod hψs).image
          (continuous_fst.prodMk ((hPc.comp continuous_fst).inv.mul continuous_snd))) ?_)
      intro q hq
      by_contra hne
      apply hq
      have hβq : β q.1 ≠ 0 := fun h0 => hne (by
        show (β q.1 : ℂ) * ψ₀ (P q.1 * q.2) = 0
        rw [h0, Complex.ofReal_zero, zero_mul])
      have hψq : ψ₀ (P q.1 * q.2) ≠ 0 := right_ne_zero_of_mul hne
      refine ⟨(q.1, P q.1 * q.2), ⟨mem_closedBall.2 (hβ0 _ hβq).le, subset_tsupport _ hψq⟩, ?_⟩
      show (q.1, (P q.1)⁻¹ * (P q.1 * q.2)) = q
      rw [inv_mul_cancel_left]
    have hint2 : Integrable (Function.uncurry fun (x : G) (z : Fin d → ℝ) =>
        ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ))
        (μ.prod (volume.restrict (ball (0 : Fin d → ℝ) r))) := by
      have hcont : Continuous (Function.uncurry fun (x : G) (z : Fin d → ℝ) =>
          ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ)) :=
        (hψc.comp (hPc.comp continuous_snd)).mul (Complex.continuous_ofReal.comp
          (hΞc.continuous.comp ((hu_c.comp continuous_fst).prodMk continuous_snd)))
      have hi : Integrable (Function.uncurry fun (x : G) (z : Fin d → ℝ) =>
          ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ)) (μ.prod volume) := by
        refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro
          (hX₀.prod (isCompact_closedBall (0 : Fin d → ℝ) (2 * r))) ?_)
        intro q hq
        by_contra hne
        have hΞq : Ξ ((((q.1⁻¹ : G) : 𝔸ˣ) : 𝔸), q.2) ≠ 0 := fun h0 => hne (by
          show ψ₀ (P q.2) * (Ξ ((((q.1⁻¹ : G) : 𝔸ˣ) : 𝔸), q.2) : ℂ) = 0
          rw [h0, Complex.ofReal_zero, mul_zero])
        obtain ⟨h1, h2⟩ := hsuppx q.1 q.2 hΞq
        exact hq ⟨h1, mem_closedBall.2 h2.le⟩
      have e : μ.prod (volume.restrict (ball (0 : Fin d → ℝ) r)) =
          (μ.prod volume).restrict (univ ×ˢ ball (0 : Fin d → ℝ) r) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [e]; exact hi.restrict
    have hA : ((∫ s, β s : ℝ) : ℂ) * ∫ y, ψ₀ y ∂μ =
        ∫ s, ∫ x, (β s : ℂ) * ψ₀ (P s * x) ∂μ := by
      have e1 : ∀ s, ∫ x, (β s : ℂ) * ψ₀ (P s * x) ∂μ = (β s : ℂ) * ∫ y, ψ₀ y ∂μ := by
        intro s; rw [integral_const_mul, integral_mul_left_eq_self]
      simp_rw [e1]
      rw [integral_mul_const, integral_complex_ofReal]
    have hmain : ((∫ s, β s : ℝ) : ℂ) * ∫ y, ψ₀ y ∂μ =
        ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (D z : ℂ) := by
      rw [hA, integral_integral_swap hint1]
      have e2 : (fun x : G => ∫ s, (β s : ℂ) * ψ₀ (P s * x)) = fun x =>
          ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ) :=
        funext (hC ψ₀ hψsupp)
      rw [e2, integral_integral_swap hint2]
      refine setIntegral_congr_fun measurableSet_ball (fun z _ => ?_)
      show ∫ x, ψ₀ (P z) * (Ξ ((((x⁻¹ : G) : 𝔸ˣ) : 𝔸), z) : ℂ) ∂μ = ψ₀ (P z) * (D z : ℂ)
      rw [integral_const_mul, integral_complex_ofReal]
    have hβne : ((∫ s, β s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβint.ne'
    have e3 : ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (((D z / ∫ s, β s) : ℝ) : ℂ) =
        ((∫ s, β s : ℝ) : ℂ)⁻¹ * ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (D z : ℂ) := by
      rw [← integral_const_mul]
      congr 1; funext z
      push_cast
      field_simp
    show ∫ y, ψ₀ y ∂μ = ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (P z) * (((D z / ∫ s, β s) : ℝ) : ℂ)
    rw [e3, ← hmain, ← mul_assoc, inv_mul_cancel₀ hβne, one_mul]

end IsExpLieAlgebra

end GroundTheory.Automorphic
