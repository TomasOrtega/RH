import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TermEDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactorAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.UiwPow
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HopOloc
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OlocEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SideTrace
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ZBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.TwistedTraces.IwahoriCompactOpenAndIwCosetIndicatorTest

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

/- English proof (translation)
Take `⟨hf, rfl⟩` from `h`. Establish `key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (b • A) v ∈ R) (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A), LinearMap.trace ℂ R ((b • A).restrict h1) = b * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2)`. Introduce `R hR h1 h2`. Substitute `hR` using the available equality. Establish `e : (b • A).restrict h1 = b • A.restrict h2` using `rfl`.

Rewrite using `[e, map_smul, smul_eq_mul]`. Establish `hr : LinearMap.range (b • A) = LinearMap.range A` using `LinearMap.range_smul _ _ hb`. Conclude with `⟨by rw [hr]; exact hf, key _ hr _ _⟩`.
-/
private theorem hasFinTrace_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c : ℂ} (b : ℂ) (hb : b ≠ 0)
    (h : HasFinTrace A c) : HasFinTrace (b • A) (b * c) := by
  obtain ⟨hf, rfl⟩ := h
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (b • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((b • A).restrict h1) = b * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    intro R hR h1 h2
    subst hR
    have e : (b • A).restrict h1 = b • A.restrict h2 := rfl
    rw [e, map_smul, smul_eq_mul]
  have hr : LinearMap.range (b • A) = LinearMap.range A := LinearMap.range_smul _ _ hb
  exact ⟨by rw [hr]; exact hf, key _ hr _ _⟩

/- English proof (translation)
Take `⟨A, hA, hF⟩` from `h`. Establish `hb : (d.toReal : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0, hdt⟩)`. Use `⟨(d.toReal : ℂ) • A, fun v l => ⟨(hA v l).1.smul_measure hdt, ?_⟩, hasFinTrace_smul A _ hb hF⟩` and prove the remaining obligations. Rewrite using `[integral_smul_measure, LinearMap.smul_apply, map_smul, (hA v l).2, Complex.real_smul, smul_eq_mul]`.
-/
private theorem hasTrace_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {s : ℂ} (d : ENNReal) (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (h : HasTrace m ρ f s) : HasTrace (d • m) ρ f ((d.toReal : ℂ) * s) := by
  obtain ⟨A, hA, hF⟩ := h
  have hb : (d.toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0, hdt⟩)
  refine ⟨(d.toReal : ℂ) • A, fun v l => ⟨(hA v l).1.smul_measure hdt, ?_⟩, hasFinTrace_smul A _ hb hF⟩
  rw [integral_smul_measure, LinearMap.smul_apply, map_smul, (hA v l).2, Complex.real_smul, smul_eq_mul]

/- English proof (translation)
Use `⟨fun a => if h : ∃ i, f i = a then h.choose_spec ▸ g h.choose else d a, fun i => ?_⟩` and prove the remaining obligations. Establish `aux : ∀ (j : ι) (e : f j = f i), (e ▸ g j : P (f i)) = g i`. Introduce `j e`. Take `rfl` from `hf e`. Both sides reduce to the same expression.

Establish `h : ∃ j, f j = f i` using `⟨i, rfl⟩`. Simplify using `only [dif_pos h]`. Conclude with `aux _ _`.
-/
private theorem exists_ext {ι α : Type} {P : α → Type} (f : ι → α) (hf : Function.Injective f) (d : ∀ a, P a)
    (g : ∀ i, P (f i)) : ∃ G : ∀ a, P a, ∀ i, G (f i) = g i := by
  classical
  refine ⟨fun a => if h : ∃ i, f i = a then h.choose_spec ▸ g h.choose else d a, fun i => ?_⟩
  have aux : ∀ (j : ι) (e : f j = f i), (e ▸ g j : P (f i)) = g i := by
    intro j e
    obtain rfl := hf e
    rfl
  have h : ∃ j, f j = f i := ⟨i, rfl⟩
  simp only [dif_pos h]
  exact aux _ _

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => intro v hv`. Simplify using `using hv`. Consider the case `cons B l ih`. Introduce `v hv`.

Rewrite using `[List.prod_cons]`. Conclude with `h B (by simp) _ (ih (fun B' hB' => h B' (by simp [hB'])) v hv)`.
-/
private theorem prod_mem_of {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    (l : List (H →L[ℂ] H)) (h : ∀ B ∈ l, ∀ v ∈ W, B v ∈ W) : ∀ v ∈ W, l.prod v ∈ W := by
  induction l with
  | nil => intro v hv; simpa using hv
  | cons B l ih =>
    intro v hv
    rw [List.prod_cons]
    exact h B (by simp) _ (ih (fun B' hB' => h B' (by simp [hB'])) v hv)

section Loc
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

/- English proof (translation)
Establish `hm` using `(UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1`. Establish `hc` using `(UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'`. Express the relevant statement in the definitionally equal form `rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _`. Rewrite using `[← hm, ← hm]`. Unfold `rhoL at *`.

Rewrite using `[hc]`.
-/
private theorem rhoL_comm' {w w' : Pl K} (h : w ≠ w') (g : Gw n w) (g' : Gw n w') :
    Commute (rhoL μ w g) (rhoL μ w' g') := by
  have hm := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  change rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _
  rw [← hm, ← hm]
  unfold rhoL at *
  rw [hc]

/- English proof (translation)
Establish `hc : ∀ x : Gw n w', ∀ b, B (rhoL μ w' x b) = rhoL μ w' x (B b)`. Introduce `x b`. Use `ext_inner_left ℂ fun a => ?_` and prove the remaining obligations. Rewrite using `[hB, ← ContinuousLinearMap.adjoint_inner_left, hB]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Establish `h1` using `congrArg (· b) (rhoL_comm' μ h g x)`. Simplify using `only [ContinuousLinearMap.mul_apply] at h1`. Simplify using `only`. Rewrite using `[ContinuousLinearMap.adjoint_inner_left, h1]`. Simplify using `only [fixL, fixF, Submodule.mem_iInf] at hv ⊢`.

Introduce and unpack `u ⟨k, hk, rfl⟩`. Establish `hv' : rhoL μ w' k v = v` using `hv _ ⟨k, hk, rfl⟩`. Use `show rhoL μ w' k (B v) = B v`. Rewrite using `[← hc, hv']`.
-/
private theorem oloc_fix {w w' : Pl K} (h : w ≠ w') [MeasurableSpace (Gw n w)] (m : Measure (Gw n w)) (ψ : Gw n w → ℂ)
    (B : LL μ →L[ℂ] LL μ) (hB : IsOloc μ w m ψ B) (J : Subgroup (Gw n w')) {v : LL μ} (hv : v ∈ fixL μ w' J) :
    B v ∈ fixL μ w' J := by
  have hc : ∀ x : Gw n w', ∀ b, B (rhoL μ w' x b) = rhoL μ w' x (B b) := by
    intro x b
    refine ext_inner_left ℂ fun a => ?_
    rw [hB, ← ContinuousLinearMap.adjoint_inner_left, hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have h1 := congrArg (· b) (rhoL_comm' μ h g x)
    simp only [ContinuousLinearMap.mul_apply] at h1
    simp only
    rw [ContinuousLinearMap.adjoint_inner_left, h1]
  simp only [fixL, fixF, Submodule.mem_iInf] at hv ⊢
  rintro u ⟨k, hk, rfl⟩
  have hv' : rhoL μ w' k v = v := hv _ ⟨k, hk, rfl⟩
  show rhoL μ w' k (B v) = B v
  rw [← hc, hv']

/- English proof (translation)
Simplify using `only [fixL, fixF, Submodule.coe_iInf]`. Conclude with `isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_eq (rhoF μ u).continuous continuous_id`.
-/
private theorem isClosed_fixL (w : Pl K) (J : Subgroup (Gw n w)) : IsClosed (fixL μ w J : Set (LL μ)) := by
  simp only [fixL, fixF, Submodule.coe_iInf]
  exact isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_eq (rhoF μ u).continuous continuous_id

/- English proof (translation)
The claim follows from `Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure W hx)`.
-/
private theorem prj_of_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) {x : H} (hx : x ∈ W) : prj W x = x :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure W hx)

/- English proof (translation)
The claim follows from `Submodule.topologicalClosure_minimal Y h hW (Submodule.starProjection_apply_mem _ x)`.
-/
private theorem prj_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Y W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (h : Y ≤ W) (x : H) : prj Y x ∈ W :=
  Submodule.topologicalClosure_minimal Y h hW (Submodule.starProjection_apply_mem _ x)

/- English proof (translation)
Establish `: prj (⊥ : Submodule ℂ H) = 0`. Use extensionality with `x`. Simplify using `[prj]`. Simplify using `[trOn, this, GroundTheory.Automorphic.trace]`.
-/
private theorem trOn_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    trOn (⊥ : Submodule ℂ H) T = 0 := by
  have : prj (⊥ : Submodule ℂ H) = 0 := by
    ext x
    simp [prj]
  simp [trOn, this, GroundTheory.Automorphic.trace]

end Loc

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext w.2.over.symm`.
-/
private theorem under_over' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ hgen k n hk hn μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF harch _ _ m hm q w₀ hq T V hV hVθ hrank τ₀ τ hocc₀ hocc y hy`. Take `⟨hZc, hZs, hZa, hY⟩` from `UpperTheory.ConvolutionTheory.L1.zBasic F E σ k n hn μ D s hs hposition νF a q w₀ hq T V hV y hy`. Take `⟨c₁, hc₁, hside⟩` from `UpperTheory.ConvolutionTheory.L1.sideTrace F E σ hgen k n hk hn μ θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq T V hV hVθ hrank y hy`. Choose the witnesses or unpack the hypotheses as in `⟨r, p, hpinj, hpr⟩ : ∃ (r : ℕ) (p : Fin r → Pl F), Function.Injective p ∧ ∀ v, v ∈ T.sp ↔ v ∈ Set.range p := by`. Use `⟨T.sp.card, fun i => (T.sp.equivFin.symm i).1, ?_, fun v => ⟨fun hv => ⟨T.sp.equivFin ⟨v, hv⟩, by simp⟩, ?_⟩⟩` and prove the remaining obligations.

Conclude with `Subtype.val_injective.comp T.sp.equivFin.symm.injective`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `(T.sp.equivFin.symm i).2`. Establish `hpm : ∀ i, p i ∈ T.sp` using `fun i => (hpr _).2 ⟨i, rfl⟩`. Establish `hprod : ∀ t : Pl F → ℂ, ∏ v ∈ T.sp, t v = ∏ i, t (p i)`.

Introduce `t`. Establish `e : T.sp = Finset.univ.image p`. Use extensionality with `v`. Simplify using `[hpr]`. Rewrite using `[e, Finset.prod_image (fun _ _ _ _ h => hpinj h)]`.

Choose the witnesses or unpack the hypotheses as in `⟨mm, hmm, hmm1, bb, hbb, htr⟩ : ∃ mm : ∀ u : Pl E, Measure (Gw n u), (∀ u, (mm u).IsHaarMeasure) ∧ (∀ u, mm u (T.J u) = 1) ∧ ∃ bb : Pl E → ℂ, (∀ u, bb u ≠ 0) ∧ ∀ (u : Pl E) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gw n u) X) (f : Gw n u → ℂ) (z : ℂ), HasTra …`. Establish `h0 : ∀ u, m u (T.J u) ≠ 0` using `fun u => by haveI := hm u`. Conclude with `((T.co u).2.measure_pos (m u) ⟨1, Subgroup.one_mem _⟩).ne'`. Establish `ht : ∀ u, m u (T.J u) ≠ ⊤` using `fun u => by haveI := hm u`. Conclude with `(T.co u).1.measure_lt_top.ne`.

Establish `hd0 : ∀ u, (m u (T.J u))⁻¹ ≠ 0` using `fun u => ENNReal.inv_ne_zero.2 (ht u)`. Establish `hdt : ∀ u, (m u (T.J u))⁻¹ ≠ ⊤` using `fun u => ENNReal.inv_ne_top.2 (h0 u)`. Use `⟨fun u => (m u (T.J u))⁻¹ • m u, fun u => ?_, fun u => ?_, fun u => (((m u (T.J u))⁻¹.toReal : ℝ) : ℂ), fun u => ?_, fun u X _ _ ρ f z h => hasTrace_smul _ (hd0 u) (hdt u) h⟩` and prove the remaining obligations. Use `haveI := hm u`. Conclude with `Measure.IsHaarMeasure.smul _ (hd0 u) (hdt u)`.

Rewrite using `[Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (h0 u) (ht u)]`. Conclude with `Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0 u, hdt u⟩)`. Establish `hJq : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n` using `T.at_q w₀`. Establish `hne : ∀ i, (T.mk' (p i)).1 ≠ w₀.1`. Introduce `i h`.

Establish `h1 : p i = q` using `calc p i = (T.mk' (p i)).1.under (𝓞 F) := (under_over' _).symm _ = w₀.1.under (𝓞 F) := by rw [h] _ = q := under_over' _`. Conclude with `T.q_not (h1 ▸ (Finset.mem_filter.1 (hpm i)).1)`. Establish `hover : ∀ i j, (T.mk' (p i)).1 = (T.mk' (p j)).1 → p i = p j`. Introduce `i j h`. Combine the equalities or inequalities in the displayed calculation.

Use `set O : Fin (k + 1) → LL μ →L[ℂ] LL μ := fun i => OComponent μ (s i) (hs i) νF a with hO`. Establish `hYfix : T.Y μ V O y ≤ fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n)`. Rewrite using `[hY, ← hJq]`. Conclude with `inf_le_right.trans (iInf₂_le w₀.1 (Or.inl rfl))`. Establish `step : ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), T.Fits L ψ → ∀ (e : Fin n → ℤ) (l : ℕ) (𝔢 : Side θ l), Antitone e → GM.IsSideE L νE aE e 𝔢 → ∀ j : ℕ, ∃ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (B i)) ∧ trOn (eigIn V 𝔢.toA …`.

Introduce `L ψ hfit e l 𝔢 he hsd j`. Establish `hB : ∀ i, ∃ B, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) B` using `fun i => by haveI := hmm (T.mk' (p i)).1`. Conclude with `(UpperTheory.ConvolutionTheory.C.olocEx E n μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (hfit.test _ (hpm i)).1).exists`. Use `choose B hB using hB`. Use `⟨B, hB, ?_⟩` and prove the remaining obligations.

Rewrite using `[hside L ψ hfit e l 𝔢 hsd r p hpinj hpr (fun i => mm (T.mk' (p i)).1) (fun i => ⟨hmm _, hmm1 _⟩) B hB j]`. Use `congr 1`. Establish `hP : ∀ x, (List.ofFn B).prod (prj (T.Y μ V O y) x) ∈ fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n)` using `fun x => by`. Use `prod_mem_of _ _ ?_ _ (prj_mem (isClosed_fixL μ _ _) hYfix x)` and prove the remaining obligations. Introduce `C hC v hv`.

Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 hC`. Conclude with `oloc_fix μ (hne i) _ _ _ (hB i) _ hv`. Establish `hU` using `UpperTheory.ConvolutionTheory.C.uiwPow E n μ w₀.1 e he j`. Simplify using `only [trOn]`. Use `congr 1`.

Use `ext1 x`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Rewrite using `[← hU, ContinuousLinearMap.comp_apply, prj_of_mem _ (hP x)]`. Distinguish the cases in `hZ : T.Z μ V O y = ⊥`. Use `⟨0, fun h => absurd hZ h, ?_⟩` and prove the remaining obligations.

Introduce `L ψ hfit e l 𝔢 he hsd j sq t _ _`. Take `⟨B, -, h⟩` from `step L ψ hfit e l 𝔢 he hsd j`. Establish `hYb : T.Y μ V O y = ⊥` using `by rw [hY, hZ, bot_inf_eq]`. Rewrite using `[h, hYb, trOn_bot]`. Simplify using the standard rewrite rules.

Set `w : Fin (r + 1) → Pl E` to `Fin.cons w₀.1 fun i => (T.mk' (p i)).1`. Establish `hw : Function.Injective w`. Use `Fin.cons_injective_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨i, h⟩`. Conclude with `hne i h`.

Introduce `i j h`. Conclude with `hpinj (hover i j h)`. Establish `hmk : ∀ u, u ∈ T.marked ↔ ∃ i, w i = u`. Introduce `u`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `(rfl | ⟨v, hv, rfl⟩)`. Conclude with `⟨0, rfl⟩`. Take `⟨i, rfl⟩` from `(hpr v).1 hv`. Conclude with `⟨i.succ, rfl⟩`. Introduce and unpack `⟨i, rfl⟩`.

Use `Fin.cases (Or.inl rfl) (fun i => Or.inr ⟨p i, hpm i, rfl⟩) i` and prove the remaining obligations. Establish `hinf : ∀ G : ∀ u : Pl E, Subgroup (Gw n u), ⨅ u ∈ T.marked, fixL μ u (G u) = ⨅ i, fixL μ (w i) (G (w i))`. Introduce `G`. Use `le_antisymm (le_iInf fun i => iInf₂_le (w i) ((hmk _).2 ⟨i, rfl⟩)) (le_iInf₂ fun u hu => ?_)` and prove the remaining obligations. Take `⟨i, rfl⟩` from `(hmk u).1 hu`.

Conclude with `iInf_le _ i`. Establish `hYZ : T.Y μ V O y = T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (T.J (w i))` using `by rw [hY, hinf T.J]`. Set `σ' : ∀ i, SmIrr (Gw n (w i))` to `Fin.cons (α := fun i => SmIrr (Gw n (w i))) τ₀ fun i => τ (p i)`. Establish `hoccs : ∀ i, Occurs μ V (w i) (σ' i)`. Introduce `i`.

Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Conclude with `hocc₀`. Conclude with `hocc _ (hpm i)`. Establish `hadm : ∀ U : ∀ i, Subgroup (Gw n (w i)), (∀ i, CO (U i)) → FiniteDimensional ℂ ↥(T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (U i))`. Introduce `U hU`.

Take `⟨G, hG⟩` from `exists_ext (P := fun u : Pl E => Subgroup (Gw n u)) w hw (fun _ => ⊥) U`. Establish `h` using `hZa G (fun u hu => by`. Take `⟨i, rfl⟩` from `(hmk u).1 hu`. Rewrite using `[hG]`. Conclude with `hU i)`.

Establish `e : (⨅ i, fixL μ (w i) (G (w i))) = ⨅ i, fixL μ (w i) (U i)` using `iInf_congr fun i => by rw [hG i]`. Rewrite `h` using `[hinf G, e]`. Conclude with `h`. Take `⟨N, hN, hfac⟩` from `UpperTheory.ConvolutionTheory.C.summandFactor E n μ V (T.Z μ V O y) (r + 1) w σ' hV hw hoccs (fun v hv => hv.1.1) hZ hZc (fun i g v hv => hZs (w i) ((hmk _).2 ⟨i, rfl⟩) g v hv) hadm`. Use `⟨c₁ * N * ∏ i, bb (w i), fun _ => ?_, ?_⟩` and prove the remaining obligations.

Conclude with `mul_ne_zero (mul_ne_zero hc₁ (Nat.cast_ne_zero.2 hN.ne')) (Finset.prod_ne_zero_iff.2 fun i _ => hbb _)`. Introduce `L ψ hfit e l 𝔢 he hsd j sq t hsq ht`. Take `⟨B, hB, h⟩` from `step L ψ hfit e l 𝔢 he hsd j`. Take `⟨hCO, -, hI⟩` from `UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test E n w₀.1`. Take `⟨htest, hinv⟩` from `hI (j • e)`.

Set `φ : ∀ i, Gw n (w i) → ℂ` to `Fin.cons (α := fun i => Gw n (w i) → ℂ) ((GM.iwCoset w₀.1 (j • e)).indicator 1) fun i => ψ (p i)`. Set `T' : Fin (r + 1) → LL μ →L[ℂ] LL μ` to `Fin.cons (α := fun _ => LL μ →L[ℂ] LL μ) (Uiw μ w₀.1 (j • e)) B`. Set `s' : Fin (r + 1) → ℂ` to `Fin.cons (α := fun _ => ℂ) (bb w₀.1 * sq) fun i => bb (T.mk' (p i)).1 * t (p i)`. Establish `h1 : ∀ i, Test (φ i)`. Introduce `i`.

Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Conclude with `htest`. Conclude with `(hfit.test _ (hpm i)).1`. Establish `h2 : ∀ i, ∀ u ∈ T.J (w i), ∀ g, φ i (u * g) = φ i g`. Introduce `i`.

Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Introduce `u hu g`. Conclude with `hinv u (hJq ▸ hu) g`. Introduce `u hu g`. Conclude with `((hfit.test _ (hpm i)).2 u hu g).1`.

Establish `h3 : ∀ i, IsOloc μ (w i) (mm (w i)) (φ i) (T' i)`. Introduce `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Use `haveI := hmm w₀.1`. Conclude with `UpperTheory.ConvolutionTheory.C.hopOloc E n μ w₀.1 (mm w₀.1) (GLnLocal.iwahori (w₀.1.adicCompletion E) n) (Cartan.diagPow (w₀.1.adicCompletion E) n (j • e)) hCO (by rw [← hJq]; exact hmm1 _)`.

Conclude with `hB i`. Establish `h4 : ∀ i, HasTrace (mm (w i)) (σ' i).ρ (φ i) (s' i)`. Introduce `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Conclude with `htr w₀.1 τ₀.V τ₀.ρ _ sq hsq`.

Conclude with `htr _ (τ (p i)).V (τ (p i)).ρ _ _ (ht _ (hpm i))`. Establish `hf : trOn (T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (T.J (w i))) (List.ofFn T').prod = N * ∏ i, s' i` using `hfac (fun i => T.J (w i)) (fun i => mm (w i)) φ T' s' (fun i => T.co _) (fun i => hmm _) h1 h2 h3 h4`. Establish `hlist : (List.ofFn T').prod = Uiw μ w₀.1 (j • e) ∘L (List.ofFn B).prod`. Rewrite using `[List.ofFn_succ, List.prod_cons]`. Both sides reduce to the same expression.

Rewrite using `[h, hYZ, ← hlist, hf, hprod t]`. Establish `hw0 : w 0 = w₀.1` using `rfl`. Establish `hws : ∀ i : Fin r, w i.succ = (T.mk' (p i)).1` using `fun _ => rfl`. Establish `hs0 : s' 0 = bb w₀.1 * sq` using `rfl`. Establish `hss : ∀ i : Fin r, s' i.succ = bb (T.mk' (p i)).1 * t (p i)` using `fun _ => rfl`.

Simplify using `only [Fin.prod_univ_succ, hw0, hws, hs0, hss, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.ConvolutionTheory.C.termE :
    UpperTheory.ConvolutionTheory.C.TermE := by
  classical
  intro F E _ _ _ _ _ _ σ hgen k n hk hn μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF harch _ _ m hm q w₀ hq T V hV hVθ
    hrank τ₀ τ hocc₀ hocc y hy
  obtain ⟨hZc, hZs, hZa, hY⟩ := UpperTheory.ConvolutionTheory.L1.zBasic F E σ k n hn μ D s hs hposition νF a q w₀ hq T V hV y hy
  obtain ⟨c₁, hc₁, hside⟩ := UpperTheory.ConvolutionTheory.L1.sideTrace F E σ hgen k n hk hn μ θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq
    T V hV hVθ hrank y hy
  obtain ⟨r, p, hpinj, hpr⟩ : ∃ (r : ℕ) (p : Fin r → Pl F), Function.Injective p ∧ ∀ v, v ∈ T.sp ↔ v ∈ Set.range p := by
    refine ⟨T.sp.card, fun i => (T.sp.equivFin.symm i).1, ?_, fun v => ⟨fun hv => ⟨T.sp.equivFin ⟨v, hv⟩, by simp⟩, ?_⟩⟩
    · exact Subtype.val_injective.comp T.sp.equivFin.symm.injective
    · rintro ⟨i, rfl⟩
      exact (T.sp.equivFin.symm i).2
  have hpm : ∀ i, p i ∈ T.sp := fun i => (hpr _).2 ⟨i, rfl⟩
  have hprod : ∀ t : Pl F → ℂ, ∏ v ∈ T.sp, t v = ∏ i, t (p i) := by
    intro t
    have e : T.sp = Finset.univ.image p := by
      ext v
      simp [hpr]
    rw [e, Finset.prod_image (fun _ _ _ _ h => hpinj h)]
  obtain ⟨mm, hmm, hmm1, bb, hbb, htr⟩ : ∃ mm : ∀ u : Pl E, Measure (Gw n u), (∀ u, (mm u).IsHaarMeasure) ∧
      (∀ u, mm u (T.J u) = 1) ∧ ∃ bb : Pl E → ℂ, (∀ u, bb u ≠ 0) ∧
        ∀ (u : Pl E) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gw n u) X) (f : Gw n u → ℂ) (z : ℂ),
          HasTrace (m u) ρ f z → HasTrace (mm u) ρ f (bb u * z) := by
    have h0 : ∀ u, m u (T.J u) ≠ 0 := fun u => by
      haveI := hm u
      exact ((T.co u).2.measure_pos (m u) ⟨1, Subgroup.one_mem _⟩).ne'
    have ht : ∀ u, m u (T.J u) ≠ ⊤ := fun u => by
      haveI := hm u
      exact (T.co u).1.measure_lt_top.ne
    have hd0 : ∀ u, (m u (T.J u))⁻¹ ≠ 0 := fun u => ENNReal.inv_ne_zero.2 (ht u)
    have hdt : ∀ u, (m u (T.J u))⁻¹ ≠ ⊤ := fun u => ENNReal.inv_ne_top.2 (h0 u)
    refine ⟨fun u => (m u (T.J u))⁻¹ • m u, fun u => ?_, fun u => ?_, fun u => (((m u (T.J u))⁻¹.toReal : ℝ) : ℂ),
      fun u => ?_, fun u X _ _ ρ f z h => hasTrace_smul _ (hd0 u) (hdt u) h⟩
    · haveI := hm u
      exact Measure.IsHaarMeasure.smul _ (hd0 u) (hdt u)
    · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (h0 u) (ht u)]
    · exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0 u, hdt u⟩)
  have hJq : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
  have hne : ∀ i, (T.mk' (p i)).1 ≠ w₀.1 := by
    intro i h
    have h1 : p i = q := calc
      p i = (T.mk' (p i)).1.under (𝓞 F) := (under_over' _).symm
      _ = w₀.1.under (𝓞 F) := by rw [h]
      _ = q := under_over' _
    exact T.q_not (h1 ▸ (Finset.mem_filter.1 (hpm i)).1)
  have hover : ∀ i j, (T.mk' (p i)).1 = (T.mk' (p j)).1 → p i = p j := by
    intro i j h
    calc
      p i = (T.mk' (p i)).1.under (𝓞 F) := (under_over' _).symm
      _ = (T.mk' (p j)).1.under (𝓞 F) := by rw [h]
      _ = p j := under_over' _
  set O : Fin (k + 1) → LL μ →L[ℂ] LL μ := fun i => OComponent μ (s i) (hs i) νF a with hO
  have hYfix : T.Y μ V O y ≤ fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := by
    rw [hY, ← hJq]
    exact inf_le_right.trans (iInf₂_le w₀.1 (Or.inl rfl))
  have step : ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), T.Fits L ψ →
      ∀ (e : Fin n → ℤ) (l : ℕ) (𝔢 : Side θ l), Antitone e → GM.IsSideE L νE aE e 𝔢 → ∀ j : ℕ,
      ∃ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (B i)) ∧
        trOn (eigIn V 𝔢.toAmp.A (y ^ (k + 1))) ((𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∘L θ.U) =
          c₁ * trOn (T.Y μ V O y) (Uiw μ w₀.1 (j • e) ∘L (List.ofFn B).prod) := by
    intro L ψ hfit e l 𝔢 he hsd j
    have hB : ∀ i, ∃ B, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) B := fun i => by
      haveI := hmm (T.mk' (p i)).1
      exact (UpperTheory.ConvolutionTheory.C.olocEx E n μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (hfit.test _ (hpm i)).1).exists
    choose B hB using hB
    refine ⟨B, hB, ?_⟩
    rw [hside L ψ hfit e l 𝔢 hsd r p hpinj hpr (fun i => mm (T.mk' (p i)).1) (fun i => ⟨hmm _, hmm1 _⟩) B hB j]
    congr 1
    have hP : ∀ x, (List.ofFn B).prod (prj (T.Y μ V O y) x) ∈
        fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := fun x => by
      refine prod_mem_of _ _ ?_ _ (prj_mem (isClosed_fixL μ _ _) hYfix x)
      intro C hC v hv
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hC
      exact oloc_fix μ (hne i) _ _ _ (hB i) _ hv
    have hU := UpperTheory.ConvolutionTheory.C.uiwPow E n μ w₀.1 e he j
    simp only [trOn]
    congr 1
    ext1 x
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hU, ContinuousLinearMap.comp_apply, prj_of_mem _ (hP x)]
  by_cases hZ : T.Z μ V O y = ⊥
  · refine ⟨0, fun h => absurd hZ h, ?_⟩
    intro L ψ hfit e l 𝔢 he hsd j sq t _ _
    obtain ⟨B, -, h⟩ := step L ψ hfit e l 𝔢 he hsd j
    have hYb : T.Y μ V O y = ⊥ := by rw [hY, hZ, bot_inf_eq]
    rw [h, hYb, trOn_bot]
    simp
  let w : Fin (r + 1) → Pl E := Fin.cons w₀.1 fun i => (T.mk' (p i)).1
  have hw : Function.Injective w := by
    refine Fin.cons_injective_iff.2 ⟨?_, ?_⟩
    · rintro ⟨i, h⟩
      exact hne i h
    · intro i j h
      exact hpinj (hover i j h)
  have hmk : ∀ u, u ∈ T.marked ↔ ∃ i, w i = u := by
    intro u
    constructor
    · rintro (rfl | ⟨v, hv, rfl⟩)
      · exact ⟨0, rfl⟩
      · obtain ⟨i, rfl⟩ := (hpr v).1 hv
        exact ⟨i.succ, rfl⟩
    · rintro ⟨i, rfl⟩
      refine Fin.cases (Or.inl rfl) (fun i => Or.inr ⟨p i, hpm i, rfl⟩) i
  have hinf : ∀ G : ∀ u : Pl E, Subgroup (Gw n u),
      ⨅ u ∈ T.marked, fixL μ u (G u) = ⨅ i, fixL μ (w i) (G (w i)) := by
    intro G
    refine le_antisymm (le_iInf fun i => iInf₂_le (w i) ((hmk _).2 ⟨i, rfl⟩)) (le_iInf₂ fun u hu => ?_)
    obtain ⟨i, rfl⟩ := (hmk u).1 hu
    exact iInf_le _ i
  have hYZ : T.Y μ V O y = T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (T.J (w i)) := by rw [hY, hinf T.J]
  let σ' : ∀ i, SmIrr (Gw n (w i)) := Fin.cons (α := fun i => SmIrr (Gw n (w i))) τ₀ fun i => τ (p i)
  have hoccs : ∀ i, Occurs μ V (w i) (σ' i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hocc₀
    · exact hocc _ (hpm i)
  have hadm : ∀ U : ∀ i, Subgroup (Gw n (w i)), (∀ i, CO (U i)) →
      FiniteDimensional ℂ ↥(T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (U i)) := by
    intro U hU
    obtain ⟨G, hG⟩ := exists_ext (P := fun u : Pl E => Subgroup (Gw n u)) w hw (fun _ => ⊥) U
    have h := hZa G (fun u hu => by
      obtain ⟨i, rfl⟩ := (hmk u).1 hu
      rw [hG]
      exact hU i)
    have e : (⨅ i, fixL μ (w i) (G (w i))) = ⨅ i, fixL μ (w i) (U i) := iInf_congr fun i => by rw [hG i]
    rw [hinf G, e] at h
    exact h
  obtain ⟨N, hN, hfac⟩ := UpperTheory.ConvolutionTheory.C.summandFactor E n μ V (T.Z μ V O y) (r + 1) w σ' hV hw hoccs
    (fun v hv => hv.1.1) hZ hZc (fun i g v hv => hZs (w i) ((hmk _).2 ⟨i, rfl⟩) g v hv) hadm
  refine ⟨c₁ * N * ∏ i, bb (w i), fun _ => ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero hc₁ (Nat.cast_ne_zero.2 hN.ne')) (Finset.prod_ne_zero_iff.2 fun i _ => hbb _)
  intro L ψ hfit e l 𝔢 he hsd j sq t hsq ht
  obtain ⟨B, hB, h⟩ := step L ψ hfit e l 𝔢 he hsd j
  obtain ⟨hCO, -, hI⟩ := UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test E n w₀.1
  obtain ⟨htest, hinv⟩ := hI (j • e)
  let φ : ∀ i, Gw n (w i) → ℂ :=
    Fin.cons (α := fun i => Gw n (w i) → ℂ) ((GM.iwCoset w₀.1 (j • e)).indicator 1) fun i => ψ (p i)
  let T' : Fin (r + 1) → LL μ →L[ℂ] LL μ := Fin.cons (α := fun _ => LL μ →L[ℂ] LL μ) (Uiw μ w₀.1 (j • e)) B
  let s' : Fin (r + 1) → ℂ := Fin.cons (α := fun _ => ℂ) (bb w₀.1 * sq) fun i => bb (T.mk' (p i)).1 * t (p i)
  have h1 : ∀ i, Test (φ i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact htest
    · exact (hfit.test _ (hpm i)).1
  have h2 : ∀ i, ∀ u ∈ T.J (w i), ∀ g, φ i (u * g) = φ i g := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro u hu g
      exact hinv u (hJq ▸ hu) g
    · intro u hu g
      exact ((hfit.test _ (hpm i)).2 u hu g).1
  have h3 : ∀ i, IsOloc μ (w i) (mm (w i)) (φ i) (T' i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · haveI := hmm w₀.1
      exact UpperTheory.ConvolutionTheory.C.hopOloc E n μ w₀.1 (mm w₀.1) (GLnLocal.iwahori (w₀.1.adicCompletion E) n)
        (Cartan.diagPow (w₀.1.adicCompletion E) n (j • e)) hCO (by rw [← hJq]; exact hmm1 _)
    · exact hB i
  have h4 : ∀ i, HasTrace (mm (w i)) (σ' i).ρ (φ i) (s' i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact htr w₀.1 τ₀.V τ₀.ρ _ sq hsq
    · exact htr _ (τ (p i)).V (τ (p i)).ρ _ _ (ht _ (hpm i))
  have hf : trOn (T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (T.J (w i))) (List.ofFn T').prod = N * ∏ i, s' i :=
    hfac (fun i => T.J (w i)) (fun i => mm (w i)) φ T' s' (fun i => T.co _) (fun i => hmm _) h1 h2 h3 h4
  have hlist : (List.ofFn T').prod = Uiw μ w₀.1 (j • e) ∘L (List.ofFn B).prod := by
    rw [List.ofFn_succ, List.prod_cons]
    rfl
  rw [h, hYZ, ← hlist, hf, hprod t]
  have hw0 : w 0 = w₀.1 := rfl
  have hws : ∀ i : Fin r, w i.succ = (T.mk' (p i)).1 := fun _ => rfl
  have hs0 : s' 0 = bb w₀.1 * sq := rfl
  have hss : ∀ i : Fin r, s' i.succ = bb (T.mk' (p i)).1 * t (p i) := fun _ => rfl
  simp only [Fin.prod_univ_succ, hw0, hws, hs0, hss, Finset.prod_mul_distrib]
  ring
