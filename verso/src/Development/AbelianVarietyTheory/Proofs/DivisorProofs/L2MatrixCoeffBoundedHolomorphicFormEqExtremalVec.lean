import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHolomorphicTypeFamilyHolomorphicType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeEqZeroOfTorusLawAtOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmFnAndKilledFnOfHolFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLawOfKilled
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.InterpolationCoefficientsInL2

/- English proof (translation)
Establish `h` using `(LinearIsometry.mk (U : K →ₗ[ℂ] K) hU).inner_map_map F G`. Express the relevant statement in the definitionally equal form `⟪U F, U G⟫_ℂ = _ at h`. Rewrite `h` using `[hF, inner_smul_left]`. Establish `h1 : c * (starRingEnd ℂ) c = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]`.

Simplify using the standard rewrite rules. Rewrite using `[← h, ← mul_assoc, h1, one_mul]`.
-/
lemma inner_iso_eigen {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (U : K →L[ℂ] K)
    (hU : ∀ x, ‖U x‖ = ‖x‖) {F : K} {c : ℂ} (hc : ‖c‖ = 1) (hF : U F = c • F) (G : K) :
    ⟪F, U G⟫_ℂ = c * ⟪F, G⟫_ℂ := by
  have h := (LinearIsometry.mk (U : K →ₗ[ℂ] K) hU).inner_map_map F G
  change ⟪U F, U G⟫_ℂ = _ at h
  rw [hF, inner_smul_left] at h
  have h1 : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  rw [← h, ← mul_assoc, h1, one_mul]

/- English proof (translation)
Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
lemma rep_mul_apply {G K : Type*} [Monoid G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : G →* (K →L[ℂ] K))
    (a b : G) (F : K) : ρ (a * b) F = ρ a (ρ b F) := by
  rw [map_mul]; rfl

/- English proof (translation)
Rewrite using `[map_one, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]`. Simplify using the standard rewrite rules.
-/
lemma inner_rep_one {G K : Type*} [Monoid G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : G →* (K →L[ℂ] K))
    (F : K) : ⟪F, ρ 1 F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_one, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
  simp

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ}

/- English proof (translation)
Take `⟨P, hP, hf⟩` from `hf`. Conclude with `⟨P, hP, fun u hu => (h u hu).trans (hf u hu)⟩`.
-/
lemma holFn_congr {f g : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (h : ∀ u ∈ UG Hm, g u = f u) :
    HolFn Hm q x₀ w g := by
  obtain ⟨P, hP, hf⟩ := hf
  exact ⟨P, hP, fun u hu => (h u hu).trans (hf u hu)⟩

/- English proof (translation)
Take `⟨P, ⟨hP1, hP2⟩, hf⟩` from `hf`. Use `⟨fun x => c * P x, ⟨hP1.const_mul c, fun x hx b hb => ?_⟩, fun u hu => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[hP2 x hx b hb]`. Expand and normalize the polynomial expressions, which then agree.

Use `beta_reduce`. Rewrite using `[hf u hu]`.
-/
lemma holFn_const_mul {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (c : ℂ) :
    HolFn Hm q x₀ w fun u => c * f u := by
  obtain ⟨P, ⟨hP1, hP2⟩, hf⟩ := hf
  refine ⟨fun x => c * P x, ⟨hP1.const_mul c, fun x hx b hb => ?_⟩, fun u hu => ?_⟩
  · beta_reduce
    rw [hP2 x hx b hb]; ring
  · beta_reduce
    rw [hf u hu]

/- English proof (translation)
Take `⟨P, ⟨hP1, hP2⟩, hf⟩` from `hf`. Take `⟨Q, ⟨hQ1, hQ2⟩, hg⟩` from `hg`. Use `⟨fun x => P x - Q x, ⟨hP1.sub hQ1, fun x hx b hb => ?_⟩, fun u hu => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[hP2 x hx b hb, hQ2 x hx b hb]`.

Expand and normalize the polynomial expressions, which then agree. Use `beta_reduce`. Rewrite using `[hf u hu, hg u hu]`.
-/
lemma holFn_sub {f g : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (hg : HolFn Hm q x₀ w g) :
    HolFn Hm q x₀ w fun u => f u - g u := by
  obtain ⟨P, ⟨hP1, hP2⟩, hf⟩ := hf
  obtain ⟨Q, ⟨hQ1, hQ2⟩, hg⟩ := hg
  refine ⟨fun x => P x - Q x, ⟨hP1.sub hQ1, fun x hx b hb => ?_⟩, fun u hu => ?_⟩
  · beta_reduce
    rw [hP2 x hx b hb, hQ2 x hx b hb]; ring
  · beta_reduce
    rw [hf u hu, hg u hu]

omit [Fintype ι] in
/- English proof (translation)
Introduce `τ`. Express the relevant statement in the definitionally equal form `(1 : Mt n)ᴴ * Hm τ * 1 = Hm τ`. Simplify using the standard rewrite rules.
-/
lemma one_mem_UG : (1 : ι → Mt n) ∈ UG Hm := by
  intro τ
  change (1 : Mt n)ᴴ * Hm τ * 1 = Hm τ
  simp

omit [Fintype ι] in
/- English proof (translation)
Introduce `τ`. Establish `h1 : (u τ)ᴴ * Hm τ * u τ = Hm τ` using `hu τ`. Establish `h2 : (u' τ)ᴴ * Hm τ * u' τ = Hm τ` using `hu' τ`. Express the relevant statement in the definitionally equal form `(u τ * u' τ)ᴴ * Hm τ * (u τ * u' τ) = Hm τ`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hm τ := by rw [h1, h2]`.
-/
lemma mul_mem_UG {u u' : ι → Mt n} (hu : u ∈ UG Hm) (hu' : u' ∈ UG Hm) : u * u' ∈ UG Hm := by
  intro τ
  have h1 : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
  have h2 : (u' τ)ᴴ * Hm τ * u' τ = Hm τ := hu' τ
  change (u τ * u' τ)ᴴ * Hm τ * (u τ * u' τ) = Hm τ
  calc (u τ * u' τ)ᴴ * Hm τ * (u τ * u' τ) = (u' τ)ᴴ * ((u τ)ᴴ * Hm τ * u τ) * u' τ := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hm τ := by rw [h1, h2]

/- English proof (translation)
Rewrite using `[norm_prod]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Rewrite using `[norm_zpow, Complex.norm_exp_ofReal_mul_I, _root_.one_zpow]`.
-/
lemma norm_prod_exp (w : Fin n → ℤ) (s : Fin n → ℝ) :
    ‖∏ a, Complex.exp ((s a : ℂ) * Complex.I) ^ w a‖ = 1 := by
  rw [norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [norm_zpow, Complex.norm_exp_ofReal_mul_I, _root_.one_zpow]

/- English proof (translation)
Unfold `torCh`. Rewrite using `[norm_prod]`. Conclude with `Finset.prod_eq_one fun τ _ => norm_prod_exp _ _`.
-/
lemma norm_torCh (w : ι → Fin n → ℤ) (s : ι → Fin n → ℝ) : ‖torCh w s‖ = 1 := by
  unfold torCh
  rw [norm_prod]
  exact Finset.prod_eq_one fun τ _ => norm_prod_exp _ _

/- English proof (translation)
Introduce `u hu` and use `sub_eq_zero.1 (GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law n ι Hm q x₀ w hO _ (holFn_sub hf (holFn_const_mul hg c)) (fun u hu s => by beta_reduce; rw [hfl u hu, hgl u hu]; ring) (by beta_reduce; rw [hf1, hg1, mul_one, sub_self]) u hu)`.
-/
lemma eq_const_mul [DecidableEq ι] (hO : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {f g : (ι → Mt n) → ℂ} (c : ℂ)
    (hf : HolFn Hm q x₀ w f) (hg : HolFn Hm q x₀ w g)
    (hfl : ∀ u ∈ UG Hm, ∀ s, f (torEl x₀ s * u) = torCh w s * f u)
    (hgl : ∀ u ∈ UG Hm, ∀ s, g (torEl x₀ s * u) = torCh w s * g u) (hf1 : f 1 = c) (hg1 : g 1 = 1) :
    ∀ u ∈ UG Hm, f u = c * g u := fun u hu =>
  sub_eq_zero.1 (GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law n ι Hm q x₀ w hO _ (holFn_sub hf (holFn_const_mul hg c))
    (fun u hu s => by beta_reduce; rw [hfl u hu, hgl u hu]; ring)
    (by beta_reduce; rw [hf1, hg1, mul_one, sub_self]) u hu)

end Local

end GlobalTheory.HolDict.InterpolationCoefficientsInL2

open GlobalTheory.HolDict.InterpolationCoefficientsInL2 in

/- English proof (translation)
Introduce `D θ V S M w v hθ hS hW hv μ 𝓕 ρ hfin hreg J χ φ F hφ hF u₀ hu₀`. Use `(GlobalTheory.RealLift.exists_real_lift D θ V hθ).elim fun L hL => ?_` and prove the remaining obligations. Establish `hL1` using `hL.1`. Establish `hLmul` using `hL.2.1`. Establish `hUG` using `hL.2.2.2.1`.

Establish `hLinv` using `hL.2.2.2.2.1`. Establish `hB` using `(GlobalTheory.HolDict.holFn_coef_extVec D θ V S M w v hθ hS hW hv).1`. Establish `hBt` using `(GlobalTheory.HolDict.holFn_coef_extVec D θ V S M w v hθ hS hW hv).2`. Establish `hO : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ)` using `fun τ => ((GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.2.2 hS).1`. Establish `hU : ∀ τ, IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ)` using `fun τ => (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1`.

Establish `htm : ∀ s, torEl (x0Mat M) s ∈ UG (gramAt D V)` using `fun s => by`. Simplify using `using TorusLaw.mul_torEl_mem hO s (one_mem_UG (Hm := gramAt D V))`. Establish `hL0 : L 1 = 1`. Establish `h` using `hLmul 1 one_mem_UG 1 one_mem_UG`. Rewrite `h` using `[mul_one]`.

Conclude with `mul_left_cancel (a := L 1) (by rw [← h, mul_one])`. Establish `horb : ∀ x, HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w fun u => φ (x * L u)`. Introduce `x`. Take `⟨f, hf, hfx⟩` from `hφ.hol x`. Use `holFn_congr hf fun u hu => ?_` and prove the remaining obligations.

Rewrite using `[hfx _ (hL1 u hu).1]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Conclude with `(hL1 u hu).2 τ`. Establish `htor : ∀ s x, φ (x * L (torEl (x0Mat M) s)) = torCh w s * φ x`.

Introduce `s x`. Take `⟨h1, h2⟩` from `GlobalTheory.HolDict.smFn_and_killedFn_of_holFn _ _ _ _ _ _ hO _ (horb x)`. Use `GlobalTheory.HolDict.torus_law_of_killed _ _ _ _ _ _ hO _ h1 h2 1 one_mem_UG s` as an intermediate fact. Simplify `this` using `[hL0]`. Use `hφ.bdd.elim fun C hC => ?_` and prove the remaining obligations.

Establish `hR` using `(GlobalTheory.HolDict.RepresentativeL2.repr_properties D V μ 𝓕 ρ hfin hreg).2.2`. Establish `hR3` using `hR.1`. Establish `hR4` using `hR.2.1`. Establish `hR5` using `hR.2.2.1`. Establish `hR6` using `hR.2.2.2`.

Establish `hρt : ∀ s, ρ (L (torEl (x0Mat M) s)) F = torCh w s • F`. Introduce `s`. Establish `h1` using `hR4 F φ (L (torEl (x0Mat M) s)) hF`. Establish `h2` using `hR5 F F φ φ (torCh w s - 1) hF hF`. Establish `e1 : (torCh w s - 1) • F + F = torCh w s • F` using `by rw [sub_smul, one_smul, sub_add_cancel]`.

Establish `e2 : (torCh w s - 1) • φ + φ = rTr V (L (torEl (x0Mat M) s)) φ`. Use function extensionality and compare the values at `x`. Simplify using `only [rTr, htor, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[e1, e2]`.

Conclude with `hR3 _ _ _ h1 h2`. Use `haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin.fin`. Establish `hA : HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w fun u => ⟪F, ρ (L u) F⟫_ℂ`. Establish `h` using `GlobalTheory.HolDict.holFn_integral _ _ _ _ _ w hO (GA D V) (μ.restrict 𝓕) (fun x u => star (φ x) * φ (x * L u)) (C * C) (fun x => holFn_const_mul (horb x) _) (fun x u _ => by`. Rewrite using `[norm_mul, norm_star]`.

Conclude with `mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC x)))`. Use the proof step `(fun u _ => (hR6 F _ φ _ hF (hR4 F φ (L u) hF)).1.aestronglyMeasurable)`. Conclude with `holFn_congr h fun u _ => (hR6 F _ φ _ hF (hR4 F φ (L u) hF)).2`. Establish `key` using `eq_const_mul hO ((‖F‖ ^ 2 : ℝ) : ℂ) hA hB (fun u hu s => ((congrArg (fun g => ⟪F, ρ g F⟫_ℂ) (hLmul _ (htm s) _ hu)).trans (congrArg (fun G => ⟪F, G⟫_ℂ) (rep_mul_apply ρ _ _ F))).trans (inner_iso_eigen _ (hreg.iso _) (norm_torCh w s) (hρt s) _)) (fun u hu s => by`. Establish `a2 : ∀ τ, ⟪(v τ : M.H τ), M.rep τ ((torEl (x0Mat M) s * u) τ) (v τ : M.H τ)⟫_ℂ = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) * ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ`.

Introduce `τ`. Use `(congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ) ((hU τ).1.2 _ (htm s τ) _ (hu τ))).trans ?_` and prove the remaining obligations. Conclude with `inner_iso_eigen _ ((hU τ).2.1 _ (htm s τ)) (norm_prod_exp _ _) (hBt s τ) _`. Conclude with `(Finset.prod_congr rfl fun τ _ => a2 τ).trans Finset.prod_mul_distrib)`. Use the proof step `((congrArg (fun g => ⟪F, ρ g F⟫_ℂ) hL0).trans (inner_rep_one ρ F))`.

Use the proof step `(Finset.prod_eq_one fun τ _ => by`. Use `(congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ) (hU τ).1.1).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1`. Rewrite using `[inner_self_eq_norm_sq_to_K, (hv τ).1]`. Use the proof step `simp)`.

Use `_ (hUG u₀)`. Conclude with `(congrArg (fun g => ⟪F, ρ g F⟫_ℂ) (hLinv u₀ hu₀)).symm.trans key`.
-/
theorem GlobalTheory.HolDict.inner_reg_eq_coef_extremal : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ) F, HolForm θ M w J χ φ → Repr V μ 𝓕 F φ → ∀ u ∈ GinfC V, ⟪F, ρ u F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ := by
  classical
  intro D θ V S M w v hθ hS hW hv μ 𝓕 ρ hfin hreg J χ φ F hφ hF u₀ hu₀
  refine (GlobalTheory.RealLift.exists_real_lift D θ V hθ).elim fun L hL => ?_
  have hL1 := hL.1
  have hLmul := hL.2.1
  have hUG := hL.2.2.2.1
  have hLinv := hL.2.2.2.2.1
  have hB := (GlobalTheory.HolDict.holFn_coef_extVec D θ V S M w v hθ hS hW hv).1
  have hBt := (GlobalTheory.HolDict.holFn_coef_extVec D θ V S M w v hθ hS hW hv).2
  have hO : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) :=
    fun τ => ((GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.2.2 hS).1
  have hU : ∀ τ, IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) := fun τ => (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1
  have htm : ∀ s, torEl (x0Mat M) s ∈ UG (gramAt D V) := fun s => by
    simpa using TorusLaw.mul_torEl_mem hO s (one_mem_UG (Hm := gramAt D V))
  have hL0 : L 1 = 1 := by
    have h := hLmul 1 one_mem_UG 1 one_mem_UG
    rw [mul_one] at h
    exact mul_left_cancel (a := L 1) (by rw [← h, mul_one])

  have horb : ∀ x, HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w fun u => φ (x * L u) := by
    intro x
    obtain ⟨f, hf, hfx⟩ := hφ.hol x
    refine holFn_congr hf fun u hu => ?_
    rw [hfx _ (hL1 u hu).1]
    congr 1
    funext τ
    exact (hL1 u hu).2 τ
  have htor : ∀ s x, φ (x * L (torEl (x0Mat M) s)) = torCh w s * φ x := by
    intro s x
    obtain ⟨h1, h2⟩ := GlobalTheory.HolDict.smFn_and_killedFn_of_holFn _ _ _ _ _ _ hO _ (horb x)
    have := GlobalTheory.HolDict.torus_law_of_killed _ _ _ _ _ _ hO _ h1 h2 1 one_mem_UG s
    simpa [hL0] using this
  refine hφ.bdd.elim fun C hC => ?_
  have hR := (GlobalTheory.HolDict.RepresentativeL2.repr_properties D V μ 𝓕 ρ hfin hreg).2.2
  have hR3 := hR.1
  have hR4 := hR.2.1
  have hR5 := hR.2.2.1
  have hR6 := hR.2.2.2
  have hρt : ∀ s, ρ (L (torEl (x0Mat M) s)) F = torCh w s • F := by
    intro s
    have h1 := hR4 F φ (L (torEl (x0Mat M) s)) hF
    have h2 := hR5 F F φ φ (torCh w s - 1) hF hF
    have e1 : (torCh w s - 1) • F + F = torCh w s • F := by rw [sub_smul, one_smul, sub_add_cancel]
    have e2 : (torCh w s - 1) • φ + φ = rTr V (L (torEl (x0Mat M) s)) φ := by
      funext x
      simp only [rTr, htor, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2] at h2
    exact hR3 _ _ _ h1 h2
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin.fin
  have hA : HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w fun u => ⟪F, ρ (L u) F⟫_ℂ := by
    have h := GlobalTheory.HolDict.holFn_integral _ _ _ _ _ w hO (GA D V) (μ.restrict 𝓕) (fun x u => star (φ x) * φ (x * L u)) (C * C)
      (fun x => holFn_const_mul (horb x) _)
      (fun x u _ => by
        rw [norm_mul, norm_star]
        exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC x)))
      (fun u _ => (hR6 F _ φ _ hF (hR4 F φ (L u) hF)).1.aestronglyMeasurable)
    exact holFn_congr h fun u _ => (hR6 F _ φ _ hF (hR4 F φ (L u) hF)).2
  have key := eq_const_mul hO ((‖F‖ ^ 2 : ℝ) : ℂ) hA hB
    (fun u hu s => ((congrArg (fun g => ⟪F, ρ g F⟫_ℂ) (hLmul _ (htm s) _ hu)).trans
      (congrArg (fun G => ⟪F, G⟫_ℂ) (rep_mul_apply ρ _ _ F))).trans
      (inner_iso_eigen _ (hreg.iso _) (norm_torCh w s) (hρt s) _))
    (fun u hu s => by
      have a2 : ∀ τ, ⟪(v τ : M.H τ), M.rep τ ((torEl (x0Mat M) s * u) τ) (v τ : M.H τ)⟫_ℂ =
          (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) * ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ := by
        intro τ
        refine (congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ)
          ((hU τ).1.2 _ (htm s τ) _ (hu τ))).trans ?_
        exact inner_iso_eigen _ ((hU τ).2.1 _ (htm s τ)) (norm_prod_exp _ _) (hBt s τ) _
      exact (Finset.prod_congr rfl fun τ _ => a2 τ).trans Finset.prod_mul_distrib)
    ((congrArg (fun g => ⟪F, ρ g F⟫_ℂ) hL0).trans (inner_rep_one ρ F))
    (Finset.prod_eq_one fun τ _ => by
      refine (congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ) (hU τ).1.1).trans ?_
      change ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1
      rw [inner_self_eq_norm_sq_to_K, (hv τ).1]
      simp)
    _ (hUG u₀)
  exact (congrArg (fun g => ⟪F, ρ g F⟫_ℂ) (hLinv u₀ hu₀)).symm.trans key
