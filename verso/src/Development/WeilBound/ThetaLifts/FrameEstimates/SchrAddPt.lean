import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.FrameEstimates.LevelA
import Development.WeilBound.ThetaLifts.FrameEstimates.Parity
import Development.WeilBound.CoreStatements.LocalThetaKernels.LinearIndependentOfNotMem
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace levelStructure

open LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]`. Rewrite using `[← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]`. Use `congr 2`. Simplify using `only [dotProduct_add, add_dotProduct]`.

Take the linear combination `(w.1 ⬝ᵥ δ.2) * invOf_mul_self (2 : AF F)`.
-/
theorem schr_add_pt (ψ : AddChar (AF F) ℂ) (w δ : Pt F κ) (Φ : (κ → AF F) → ℂ) :
    schr ψ (w + δ) Φ = ψ (⅟(2 : AF F) * (δ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ δ.2)) • schr ψ w (schr ψ δ Φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (w.1 ⬝ᵥ δ.2) * invOf_mul_self (2 : AF F)

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.AdelicHeis.isLocallyConstant_fin (ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F))) (hψ.1.comp (continuous_const.prodMk continuous_id)) fun _ => GlobalTheory.CompanionTheory.AdelicHeis.norm_eq_one ψ hψ.1 hψ.2.1 _`.
-/
theorem lc_fin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) :
    IsLocallyConstant fun a : Af F => ψ ((0, a) : Ainf F × Af F) :=
  GlobalTheory.CompanionTheory.AdelicHeis.isLocallyConstant_fin (ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F)))
    (hψ.1.comp (continuous_const.prodMk continuous_id)) fun _ => GlobalTheory.CompanionTheory.AdelicHeis.norm_eq_one ψ hψ.1 hψ.2.1 _

/- English proof (translation)
Rewrite using `[← h, finiteAdeleIdempotentOfF_mul_self]`.
-/
theorem fst_zero {a : AF F} (h : e0 F * a = a) : a.1 = 0 := by
  rw [← h, finiteAdeleIdempotentOfF_mul_self]

/- English proof (translation)
Establish `hc : Continuous fun u : Pt F κ => ((fun i => (u.1 i).2, fun i => (u.2 i).2) : (κ → Af F) × (κ → Af F))` using `(continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp continuous_fst)).prodMk (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp continuous_snd))`. Establish `h` using `(hc.tendsto 0).eventually (eventually_fix _ (lc_fin hψ) ψ.map_zero_eq_one (⅟(2 : AF F)).2 hg)`. Use `filter_upwards [h] with u key hu f`. Use function extensionality and compare the values at `x`. Establish `h1 : ∀ i, (u.1 i).1 = 0` using `fun i => fst_zero (congrFun (congrArg Prod.fst hu) i)`.

Establish `h2 : ∀ i, (u.2 i).1 = 0` using `fun i => fst_zero (congrFun (congrArg Prod.snd hu) i)`. Establish `p : ψ (x ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2)) = ψ ((0, ((fun i => (x i).2) ⬝ᵥ fun i => (u.2 i).2) + (⅟(2 : AF F)).2 * ((fun i => (u.1 i).2) ⬝ᵥ fun i => (u.2 i).2)) : Ainf F × Af F)`. Rewrite using `[← dot_snd, ← dot_snd]`. Use `congrArg ψ (Prod.ext ?_ rfl)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x ⬝ᵥ u.2).1 + (⅟(2 : AF F)).1 * (u.1 ⬝ᵥ u.2).1 = 0`.

Rewrite using `[dot_fst _ _ h2, dot_fst _ _ h2, mul_zero, add_zero]`. Establish `q : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + u.1) i).1) = fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (u.1 i).1) = _`. Rewrite using `[h1 i, add_zero]`.

Simplify using `only [schr, pureA]`. Rewrite using `[p, q, mul_left_comm]`. Conclude with `congrArg _ (key fun i => (x i).2)`.
-/
theorem fix_near {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    ∀ᶠ u in 𝓝 (0 : Pt F κ), e0 F • u = u → ∀ f, schr ψ u (pureA F f g) = pureA F f g := by
  have hc : Continuous fun u : Pt F κ => ((fun i => (u.1 i).2, fun i => (u.2 i).2) : (κ → Af F) × (κ → Af F)) :=
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp continuous_fst)).prodMk
      (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp continuous_snd))
  have h := (hc.tendsto 0).eventually
    (eventually_fix _ (lc_fin hψ) ψ.map_zero_eq_one (⅟(2 : AF F)).2 hg)
  filter_upwards [h] with u key hu f
  funext x
  have h1 : ∀ i, (u.1 i).1 = 0 := fun i => fst_zero (congrFun (congrArg Prod.fst hu) i)
  have h2 : ∀ i, (u.2 i).1 = 0 := fun i => fst_zero (congrFun (congrArg Prod.snd hu) i)
  have p : ψ (x ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2)) = ψ ((0, ((fun i => (x i).2) ⬝ᵥ fun i => (u.2 i).2) +
      (⅟(2 : AF F)).2 * ((fun i => (u.1 i).2) ⬝ᵥ fun i => (u.2 i).2)) : Ainf F × Af F) := by
    rw [← dot_snd, ← dot_snd]
    refine congrArg ψ (Prod.ext ?_ rfl)
    change (x ⬝ᵥ u.2).1 + (⅟(2 : AF F)).1 * (u.1 ⬝ᵥ u.2).1 = 0
    rw [dot_fst _ _ h2, dot_fst _ _ h2, mul_zero, add_zero]
  have q : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + u.1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (u.1 i).1) = _
    rw [h1 i, add_zero]
  simp only [schr, pureA]
  rw [p, q, mul_left_comm]
  exact congrArg _ (key fun i => (x i).2)

/- English proof (translation)
Establish `h1 : ∀ᶠ δ in 𝓝 (0 : Pt F κ), ∀ c ∈ K, ψ (e0 F * (⅟(2 : AF F) * (δ.1 ⬝ᵥ c.2 - c.1 ⬝ᵥ δ.2))) = 1`. Use `hK.eventually_forall_of_forall_eventually fun c _ => ?_` and prove the remaining obligations. Establish `hc : Continuous fun z : Pt F κ × Pt F κ => ⅟(2 : AF F) * (z.1.1 ⬝ᵥ z.2.2 - z.2.1 ⬝ᵥ z.1.2)`. Unfold `dotProduct`. Use `fun_prop`.

Use `filter_upwards [((lc_fin hψ).comp_continuous (continuous_snd.comp hc)).eventually_eq (0, c)] with z hz`. Rewrite using `[finiteAdeleIdempotentOfF_mul_self]`. Use `hz.trans ?_` and prove the remaining obligations. Simplify using `only [Function.comp, Prod.fst_zero, Prod.snd_zero, zero_dotProduct, dotProduct_zero, sub_zero, mul_zero]`. Conclude with `ψ.map_zero_eq_one`.

Use `filter_upwards [h1, fix_near hψ hg] with δ h1 h2 hδ c hc w hw f`. Establish `e : ⅟(2 : AF F) * (δ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ δ.2) = e0 F * (⅟(2 : AF F) * (δ.1 ⬝ᵥ c.2 - c.1 ⬝ᵥ δ.2))`. Establish `a1 : e0 F • δ.1 = δ.1` using `congrArg Prod.fst hδ`. Establish `a2 : e0 F • δ.2 = δ.2` using `congrArg Prod.snd hδ`. Establish `b1 : e0 F • w.1 = e0 F • c.1` using `congrArg Prod.fst hw`.

Establish `b2 : e0 F • w.2 = e0 F • c.2` using `congrArg Prod.snd hw`. Establish `c1 : δ.1 ⬝ᵥ w.2 = e0 F * (δ.1 ⬝ᵥ c.2)` using `by conv_lhs => rw [← a1, smul_dotProduct, ← dotProduct_smul, b2, dotProduct_smul, smul_eq_mul]`. Establish `c2 : w.1 ⬝ᵥ δ.2 = e0 F * (c.1 ⬝ᵥ δ.2)` using `by conv_lhs => rw [← a2, dotProduct_smul, ← smul_dotProduct, b1, smul_dotProduct, smul_eq_mul]`. Rewrite using `[c1, c2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[schr_add_pt, h2 hδ f, e, h1 c hc, one_smul]`.
-/
theorem schr_near {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F))
    {K : Set (Pt F κ)} (hK : IsCompact K) : ∀ᶠ δ in 𝓝 (0 : Pt F κ), e0 F • δ = δ → ∀ c ∈ K, ∀ w, e0 F • w = e0 F • c →
      ∀ f, schr ψ (w + δ) (pureA F f g) = schr ψ w (pureA F f g) := by
  have h1 : ∀ᶠ δ in 𝓝 (0 : Pt F κ), ∀ c ∈ K, ψ (e0 F * (⅟(2 : AF F) * (δ.1 ⬝ᵥ c.2 - c.1 ⬝ᵥ δ.2))) = 1 := by
    refine hK.eventually_forall_of_forall_eventually fun c _ => ?_
    have hc : Continuous fun z : Pt F κ × Pt F κ => ⅟(2 : AF F) * (z.1.1 ⬝ᵥ z.2.2 - z.2.1 ⬝ᵥ z.1.2) := by
      unfold dotProduct; fun_prop
    filter_upwards [((lc_fin hψ).comp_continuous (continuous_snd.comp hc)).eventually_eq (0, c)] with z hz
    rw [finiteAdeleIdempotentOfF_mul_self]
    refine hz.trans ?_
    simp only [Function.comp, Prod.fst_zero, Prod.snd_zero, zero_dotProduct, dotProduct_zero, sub_zero, mul_zero]
    exact ψ.map_zero_eq_one
  filter_upwards [h1, fix_near hψ hg] with δ h1 h2 hδ c hc w hw f
  have e : ⅟(2 : AF F) * (δ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ δ.2) = e0 F * (⅟(2 : AF F) * (δ.1 ⬝ᵥ c.2 - c.1 ⬝ᵥ δ.2)) := by
    have a1 : e0 F • δ.1 = δ.1 := congrArg Prod.fst hδ
    have a2 : e0 F • δ.2 = δ.2 := congrArg Prod.snd hδ
    have b1 : e0 F • w.1 = e0 F • c.1 := congrArg Prod.fst hw
    have b2 : e0 F • w.2 = e0 F • c.2 := congrArg Prod.snd hw
    have c1 : δ.1 ⬝ᵥ w.2 = e0 F * (δ.1 ⬝ᵥ c.2) := by
      conv_lhs => rw [← a1, smul_dotProduct, ← dotProduct_smul, b2, dotProduct_smul, smul_eq_mul]
    have c2 : w.1 ⬝ᵥ δ.2 = e0 F * (c.1 ⬝ᵥ δ.2) := by
      conv_lhs => rw [← a2, dotProduct_smul, ← smul_dotProduct, b1, smul_dotProduct, smul_eq_mul]
    rw [c1, c2]; ring
  rw [schr_add_pt, h2 hδ f, e, h1 c hc, one_smul]

open Classical in
/- English proof (translation)
Introduce `g _`. Use `⟨g (fun i => (y i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩` and prove the remaining obligations. Conclude with `mul_comm _ _`.
-/
theorem ev_adm (y : κ → AF F) : (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (y i).2) •
    (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩
  exact mul_comm _ _

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `h0 : ∀ w, piInf (τ w) ((mat u - 1) i j) = 0` using `fun w => by`. Establish `: (mat u - 1).map (piInf (τ w)) = 0`. Rewrite using `[Matrix.map_sub _ (map_sub _), hu, Matrix.map_one _ (map_zero _) (map_one _), sub_self]`. Conclude with `congrFun (congrFun this i) j`.

Use `GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h τ ((1 - e0 F) • (mat u - 1) i j) ((at_iff _).2 (by` as an intermediate fact. Rewrite using `[smul_smul, mul_sub, mul_one, show e0 F * e0 F = e0 F from finiteAdeleIdempotentOfF_mul_self _, sub_self, zero_smul])) fun w => by`. Rewrite using `[Algebra.smul_def, map_mul, h0, mul_zero]`. Rewrite `this` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `this.symm`.
-/
theorem isFin_of (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    {u : UA σ J} (hu : ∀ w, (mat u).map (piInf (τ w)) = 1) : IsFin u := by
  refine Matrix.ext fun i j => ?_
  have h0 : ∀ w, piInf (τ w) ((mat u - 1) i j) = 0 := fun w => by
    have : (mat u - 1).map (piInf (τ w)) = 0 := by
      rw [Matrix.map_sub _ (map_sub _), hu, Matrix.map_one _ (map_zero _) (map_one _), sub_self]
    exact congrFun (congrFun this i) j
  have := GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h τ ((1 - e0 F) • (mat u - 1) i j) ((at_iff _).2 (by
    rw [smul_smul, mul_sub, mul_one, show e0 F * e0 F = e0 F from finiteAdeleIdempotentOfF_mul_self _, sub_self, zero_smul])) fun w => by
      rw [Algebra.smul_def, map_mul, h0, mul_zero]
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

/- English proof (translation)
Use `ring_AE F E` as an intermediate fact. Establish `: IsModuleTopology (AF F) (Ten F E n d)` using `inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))`. Establish `he : Continuous M.co.e` using `IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap`. Establish `hV` using `schr_near hψ hg (hC.image he)`. Establish `hm : Continuous fun z : UA σ W.J × Ten F E n d => M.co.e (z.2 * (mat z.1 - 1)ᵀ)` using `he.comp (continuous_snd.matrix_mul (((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).sub continuous_const).matrix_transpose)`.

Establish `h1` using `hC.eventually_forall_of_forall_eventually (x₀ := (1 : UA σ W.J)) (P := fun u c => M.co.e (c * (mat u - 1)ᵀ) ∈ _) fun c _ => hm.continuousAt.preimage_mem_nhds (by`. Rewrite using `[show mat (1 : UA σ W.J) = 1 from rfl, sub_self, Matrix.transpose_zero, Matrix.mul_zero, map_zero])` and apply the resulting hypothesis. Use `filter_upwards [h1] with u h1 hu z hz f`. Take `⟨c, hc, hz⟩` from `hz`. Rewrite `hz` using `[at_iff, smul_sub, sub_eq_zero]`.

Establish `hu' : e0 F • (mat u - 1)ᵀ = (mat u - 1)ᵀ` using `by rw [← Matrix.transpose_smul, hu]`. Establish `e : z * (mat u)ᵀ = z + c * (mat u - 1)ᵀ`. Rewrite using `[← hu', Matrix.mul_smul, ← Matrix.smul_mul, ← hz, Matrix.smul_mul, ← Matrix.mul_smul, hu', Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]`. Rewrite using `[e, map_add]`. Conclude with `h1 c hc (by rw [← map_smul, ← Matrix.mul_smul, hu']) _ ⟨c, hc, rfl⟩ _ (by rw [← map_smul, ← map_smul, hz]) f`.
-/
theorem coef_near {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {g : (Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) {C : Set (Ten F E n d)} (hC : IsCompact C) :
    ∀ᶠ u in 𝓝 (1 : UA σ W.J), IsFin u → ∀ z : Ten F E n d, (∃ c ∈ C, At (evI F) (z - c)) → ∀ f,
      schr ψ (M.co.e (z * (mat u)ᵀ)) (pureA F f g) = schr ψ (M.co.e z) (pureA F f g) := by
  have := ring_AE F E
  have : IsModuleTopology (AF F) (Ten F E n d) := inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hV := schr_near hψ hg (hC.image he)
  have hm : Continuous fun z : UA σ W.J × Ten F E n d => M.co.e (z.2 * (mat z.1 - 1)ᵀ) :=
    he.comp (continuous_snd.matrix_mul
      (((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).sub continuous_const).matrix_transpose)
  have h1 := hC.eventually_forall_of_forall_eventually (x₀ := (1 : UA σ W.J))
    (P := fun u c => M.co.e (c * (mat u - 1)ᵀ) ∈ _) fun c _ => hm.continuousAt.preimage_mem_nhds (by
      rwa [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, Matrix.transpose_zero, Matrix.mul_zero, map_zero])
  filter_upwards [h1] with u h1 hu z hz f
  obtain ⟨c, hc, hz⟩ := hz
  rw [at_iff, smul_sub, sub_eq_zero] at hz
  have hu' : e0 F • (mat u - 1)ᵀ = (mat u - 1)ᵀ := by rw [← Matrix.transpose_smul, hu]
  have e : z * (mat u)ᵀ = z + c * (mat u - 1)ᵀ := by
    rw [← hu', Matrix.mul_smul, ← Matrix.smul_mul, ← hz, Matrix.smul_mul, ← Matrix.mul_smul, hu', Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]
  rw [e, map_add]
  exact h1 c hc (by rw [← map_smul, ← Matrix.mul_smul, hu']) _ ⟨c, hc, rfl⟩ _ (by rw [← map_smul, ← map_smul, hz]) f

end levelStructure

open levelStructure in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ`. Distinguish the cases in `h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0`. Conclude with `⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩`. Use `push Not at h0`. Take `⟨f₀, h0⟩` from `h0`.

Take `⟨y, hy⟩` from `Function.ne_iff.1 h0`. Establish `hy : pureA F f₀ φ y ≠ 0` using `hy`. Establish `hs` using `IsUWeilPair.isUSplitting hp.weil`. Establish `mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d)` using `fun f => Submodule.subset_span ⟨f, φ, hφ, rfl⟩`. Take `⟨μ, hμ, -⟩` from `ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)`.

Take `⟨p, C, -, hCc, hb⟩` from `hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0`. Establish `h1` using `coef_near M hp.base.std hφ hCc`. Use `LatticeQuotientMeasure.ring_AE F E` as an intermediate fact. Establish `hi : Continuous fun u : UA σ W.J => u⁻¹` using `((continuous_inv (G := GL (Fin d) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2`. Establish `h2` using `(hi.tendsto' 1 1 inv_one).eventually h1`.

Establish `hc : Continuous fun u : UA σ W.J => ‖om (1, u) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖` using `((((hs.cont _ (ev_adm y) _ (mem f₀)).comp (continuous_const.prodMk continuous_id)).div_const _).sub continuous_const).norm`. Establish `h3` using `pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by`. Express the relevant statement in the definitionally equal form `‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2`. Rewrite using `[map_one, Module.End.one_apply, div_self hy]`. Use the proof step `norm_num))`.

Use `⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩` and prove the remaining obligations. Establish `hu` using `isFin_of hp.base.cm B.emb hu`. Establish `key : ∀ (f : SInf F (Fin n × Fin d)) x, om (1, u) (pureA F f φ) x * (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) = pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y)`. Introduce `f x`. Use `hF F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y` and prove the remaining obligations.

Use function extensionality and compare the values at `w`. Take `⟨z, rfl⟩` from `M.co.e.surjective w`. Rewrite using `[hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), ParityOfCoefficients.mat_one_inv, Matrix.one_mul]`. Distinguish the cases in `a : ∃ c ∈ C, At (evI F) (z - c)`. Unfold `coef`.

Rewrite using `[h2 hu.inv z a]`. Distinguish the cases in `a' : ∃ c ∈ C, At (evI F) (z * (mat u⁻¹)ᵀ - c)`. Unfold `coef`. Rewrite using `[← h1 hu _ a', Matrix.mul_assoc, ← Matrix.transpose_mul, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1, Matrix.transpose_one, Matrix.mul_one]`. Establish `b` using `hb f f₀ z`.

Establish `b'` using `hb f f₀ (z * (mat u⁻¹)ᵀ)`. Rewrite `b` using `[maj, if_neg a, mul_zero, norm_le_zero_iff]`. Rewrite `b'` using `[maj, if_neg a', mul_zero, norm_le_zero_iff]`. Rewrite using `[b, b']`. Establish `h4 : (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) ≠ 0` using `fun h => by`.

Use `key f₀ y` as an intermediate fact. Rewrite `this` using `[h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self]`. Conclude with `hy this`. Take `⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = c • pureA F f φ` from `⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y), fun f => funext fun x => by`. Rewrite using `[Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩`.

Establish `h5 : ∀ k : ℕ, om (1, u ^ k) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, pow_zero, one_smul]`. Conclude with `congrArg (· (pureA F f₀ φ)) (map_one om)`. Consider the case `succ k ih`.

Rewrite using `[pow_succ, show ((1, u ^ k * u) : UA σ X.J × UA σ W.J) = (1, u ^ k) * (1, u) from by simp, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']`. Establish `h6 : c = 1` using `PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by`. Use `h3 hu k` as an intermediate fact. Rewrite `this` using `[Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one]`. Then use the resulting hypothesis. Introduce `f`.

Rewrite using `[hc, h6, one_smul]`.
-/
theorem level_of (hC : CoefEq) (hF : FourierInj) (hB : CoefBd) : Level := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ
  by_cases h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0
  · exact ⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩
  push Not at h0
  obtain ⟨f₀, h0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hy : pureA F f₀ φ y ≠ 0 := hy
  have hs := IsUWeilPair.isUSplitting hp.weil
  have mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
    Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have h1 := coef_near M hp.base.std hφ hCc
  have := LatticeQuotientMeasure.ring_AE F E
  have hi : Continuous fun u : UA σ W.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin d) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ W.J => ‖om (1, u) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (ev_adm y) _ (mem f₀)).comp (continuous_const.prodMk continuous_id)).div_const _).sub
      continuous_const).norm
  have h3 := pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, Module.End.one_apply, div_self hy]
    norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x, om (1, u) (pureA F f φ) x * (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := by
    intro f x
    refine hF F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), ParityOfCoefficients.mat_one_inv, Matrix.one_mul]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold coef
      rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (z * (mat u⁻¹)ᵀ - c)
    · unfold coef
      rw [← h1 hu _ a', Matrix.mul_assoc, ← Matrix.transpose_mul, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1,
        Matrix.transpose_one, Matrix.mul_one]
    have b := hb f f₀ z
    have b' := hb f f₀ (z * (mat u⁻¹)ᵀ)
    rw [maj, if_neg a, mul_zero, norm_le_zero_iff] at b
    rw [maj, if_neg a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y
    rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this
    exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (1, u ^ k) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((1, u ^ k * u) : UA σ X.J × UA σ W.J) = (1, u ^ k) * (1, u) from by simp, map_mul,
        Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f
  rw [hc, h6, one_smul]

end PositivityTheory.ThKEst

end
