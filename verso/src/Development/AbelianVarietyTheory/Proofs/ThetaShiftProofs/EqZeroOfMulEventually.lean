import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentEigenbasisExponentialStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsThetaPt

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ.AnFrEx

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Take `⟨z₀, hz₀⟩` from `hne`. Establish `h1 : ∀ᶠ z in nhds (0 : Fin g → ℂ), θ z = 0` using `by filter_upwards [h, hφ.eventually_ne h0] with z a b`. Conclude with `(mul_eq_zero.1 a).resolve_right b`. Establish `hl : Differentiable ℂ (fun t : ℂ => t • z₀)` using `differentiable_id.smul_const z₀`.

Establish `ht : Filter.Tendsto (fun t : ℂ => t • z₀) (nhds 0) (nhds 0)`. Use `hl.continuous.tendsto 0` as an intermediate fact. Simplify using `using this`. Establish `han : AnalyticOnNhd ℂ (fun t : ℂ => θ (t • z₀)) Set.univ` using `fun t _ => (hθ.comp hl).analyticAt t`. Use `han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) (ht.eventually h1) (Set.mem_univ 1)` as an intermediate fact.

Conclude with `hz₀ (by simpa using this)`.
-/
theorem eq_zero_of_mul_eventually {g : ℕ} (θ φ : (Fin g → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : ∃ z, θ z ≠ 0)
    (hφ : ContinuousAt φ 0) (h : ∀ᶠ z in nhds 0, θ z * φ z = 0) : φ 0 = 0 := by
  by_contra h0
  obtain ⟨z₀, hz₀⟩ := hne
  have h1 : ∀ᶠ z in nhds (0 : Fin g → ℂ), θ z = 0 := by
    filter_upwards [h, hφ.eventually_ne h0] with z a b
    exact (mul_eq_zero.1 a).resolve_right b
  have hl : Differentiable ℂ (fun t : ℂ => t • z₀) := differentiable_id.smul_const z₀
  have ht : Filter.Tendsto (fun t : ℂ => t • z₀) (nhds 0) (nhds 0) := by
    have := hl.continuous.tendsto 0
    simpa using this
  have han : AnalyticOnNhd ℂ (fun t : ℂ => θ (t • z₀)) Set.univ := fun t _ => (hθ.comp hl).analyticAt t
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (ht.eventually h1) (Set.mem_univ 1)
  exact hz₀ (by simpa using this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

/- English proof (translation)
Establish `h` using `((F.hol k 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun x => differentiableOn_const _⟩).2 V 0).1`. Establish `h2` using `h.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Simplify using the standard rewrite rules.
-/
theorem isOpen_ex {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P) (V : Xo.univ.t.G.left.Opens) :
    IsOpen {z | ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ V} := by
  have h := ((F.hol k 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun x => differentiableOn_const _⟩).2 V 0).1
  have h2 := h.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
  convert h2 using 1
  ext z
  simp

/- English proof (translation)
Take `⟨h1, -, h3⟩` from `GlobalTheory.sec_values_complex_fibre hT E H Dw l Xo (F.u k P) s`. Take `⟨a, ha, -⟩` from `hs s'`. Establish `hw : ∀ z, (F.ex k P z).left ≫ Xo.univ.t.G.hom = 𝟙 (Sp ℂ) ≫ F.u k P` using `fun z => (Over.w (F.ex k P z)).trans (Category.id_comp _).symm`. Take `⟨j, hj⟩` from `GlobalTheory.FrameUnif.ThetaPtEx.exists_chart_top Xo.univ.t.PP.isLB (F.ex k P 0).left`. Establish `hn : {z | ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} ∈ nhds (0 : Fin g → ℂ)` using `(isOpen_ex F k P hP _).mem_nhds hj`.

Establish `key : fr' j 0 - a * fr j 0 = 0`. Use `eq_zero_of_mul_eventually θ (fun z => fr' j z - a * fr j z) hθ hne (((hf'.1 j).differentiableAt hn).continuousAt.sub (continuousAt_const.mul ((hf.1 j).differentiableAt hn).continuousAt)) ?_` and prove the remaining obligations. Use `filter_upwards [hn] with z hz`. Set `pt : Sp ℂ ⟶ Gx (F.u k P)` to `pullback.lift (f := (Over.mk (F.u k P)).hom) (g := Xo.univ.t.G.hom) (𝟙 _) (F.ex k P z).left (hw z).symm`. Establish `p1 : pt ≫ gxFst (F.u k P) = (F.ex k P z).left` using `pullback.lift_snd _ _ _`.

Establish `p2 : pt ≫ gxSnd (F.u k P) = 𝟙 (Sp ℂ)` using `pullback.lift_fst _ _ _`. Establish `e'` using `(congrArg (valAt' pt ((PPx (F.u k P)).U (fun _ => j))) (ha (fun _ => j))).trans (h1 a _ pt p2)`. Rewrite `e'` using `[hv j z pt p1 p2 hz, hv' j z pt p1 p2 hz]`. Use `mul_left_cancel₀ hκ ?_` and prove the remaining obligations. Take the linear combination `e'`.

Establish `h00 : fr' j 0 = fr j 0` using `(hf'.2.2.2.1 j hj).trans (hf.2.2.2.1 j hj).symm`. Establish `ha1 : a = 1`. Use `mul_right_cancel₀ (hf.2.1 j 0 hj) ?_` and prove the remaining obligations. Rewrite `key` using `[h00]`. Take the linear combination `-key`.

Use `h3 s' fun i pt hp => ?_` and prove the remaining obligations. Establish `e'` using `(congrArg (valAt' pt ((PPx (F.u k P)).U i)) (ha i)).trans (h1 a _ pt hp)`. Rewrite using `[e', ha1, one_mul]`.
-/
theorem gen_unique (hT : Out.SecTwistSt) {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P)
    (θ : (Fin g → ℂ) → ℂ) (hθ : Differentiable ℂ θ) (hne : ∃ z, θ z ≠ 0) (κ : ℂ) (hκ : κ ≠ 0)
    (fr fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
    (hf : IsThetaFrameAt Xo.univ.t.PP (F.u k P) (fun w => (F.ex k P w).left) θ fr)
    (hf' : IsThetaFrameAt Xo.univ.t.PP (F.u k P) (fun w => (F.ex k P w).left) θ fr')
    (s s' : LB.Sec (PPx (F.u k P))) (hs : GlobalTheory.Frames.SecGen (F.u k P) s)
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx (F.u k P)), pt ≫ gxFst (F.u k P) = (F.ex k P z).left →
      pt ≫ gxSnd (F.u k P) = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (F.u k P)).U (fun _ => j)) (s.f (fun _ => j)) = κ * θ z * fr j z)
    (hv' : ∀ j z (pt : Sp ℂ ⟶ Gx (F.u k P)), pt ≫ gxFst (F.u k P) = (F.ex k P z).left →
      pt ≫ gxSnd (F.u k P) = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (F.u k P)).U (fun _ => j)) (s'.f (fun _ => j)) = κ * θ z * fr' j z) :
    ∀ i, s'.f i = s.f i := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.sec_values_complex_fibre hT E H Dw l Xo (F.u k P) s
  obtain ⟨a, ha, -⟩ := hs s'
  have hw : ∀ z, (F.ex k P z).left ≫ Xo.univ.t.G.hom = 𝟙 (Sp ℂ) ≫ F.u k P := fun z =>
    (Over.w (F.ex k P z)).trans (Category.id_comp _).symm
  obtain ⟨j, hj⟩ := GlobalTheory.FrameUnif.ThetaPtEx.exists_chart_top Xo.univ.t.PP.isLB (F.ex k P 0).left
  have hn : {z | ⊤ ≤ (F.ex k P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} ∈ nhds (0 : Fin g → ℂ) :=
    (isOpen_ex F k P hP _).mem_nhds hj
  have key : fr' j 0 - a * fr j 0 = 0 := by
    refine eq_zero_of_mul_eventually θ (fun z => fr' j z - a * fr j z) hθ hne
      (((hf'.1 j).differentiableAt hn).continuousAt.sub
        (continuousAt_const.mul ((hf.1 j).differentiableAt hn).continuousAt)) ?_
    filter_upwards [hn] with z hz
    let pt : Sp ℂ ⟶ Gx (F.u k P) :=
      pullback.lift (f := (Over.mk (F.u k P)).hom) (g := Xo.univ.t.G.hom) (𝟙 _) (F.ex k P z).left (hw z).symm
    have p1 : pt ≫ gxFst (F.u k P) = (F.ex k P z).left := pullback.lift_snd _ _ _
    have p2 : pt ≫ gxSnd (F.u k P) = 𝟙 (Sp ℂ) := pullback.lift_fst _ _ _
    have e' := (congrArg (valAt' pt ((PPx (F.u k P)).U (fun _ => j))) (ha (fun _ => j))).trans (h1 a _ pt p2)
    rw [hv j z pt p1 p2 hz, hv' j z pt p1 p2 hz] at e'
    refine mul_left_cancel₀ hκ ?_
    linear_combination e'
  have h00 : fr' j 0 = fr j 0 := (hf'.2.2.2.1 j hj).trans (hf.2.2.2.1 j hj).symm
  have ha1 : a = 1 := by
    refine mul_right_cancel₀ (hf.2.1 j 0 hj) ?_
    rw [h00] at key
    linear_combination -key
  refine h3 s' fun i pt hp => ?_
  have e' := (congrArg (valAt' pt ((PPx (F.u k P)).U i)) (ha i)).trans (h1 a _ pt hp)
  rw [e', ha1, one_mul]

/- English proof (translation)
Use function extensionality and compare the values at `jj`. Rewrite using `[Finset.sum_apply]`. Distinguish the cases in `h : (e jj).1 = τ`. Take `⟨⟨τ', k⟩, rfl⟩` from `e.symm.surjective jj`. Take `rfl : τ' = τ` from `by simpa using h`.

Rewrite using `[Finset.sum_eq_single k (fun b _ hb => ?_) (by simp)]`. Simplify using the standard rewrite rules. Establish `: e.symm ⟨τ', k⟩ ≠ e.symm ⟨τ', b⟩` using `fun hh => hb (by simpa using (e.symm.injective hh).symm)`. Simplify using `[Pi.single_eq_of_ne this]`. Establish `h0 : v jj = 0` using `by_contra fun h' => h (hv jj h')`.

Rewrite using `[h0]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Establish `: jj ≠ e.symm ⟨τ, b⟩` using `fun hh => h (by rw [hh]; simp)`. Simplify using `[Pi.single_eq_of_ne this]`.
-/
theorem sum_single_of_support {J : Type} {m : J → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : J, Fin (m τ)) (τ : J)
    (v : Fin g → ℂ) (hv : ∀ jj, v jj ≠ 0 → (e jj).1 = τ) :
    ∑ k : Fin (m τ), v (e.symm ⟨τ, k⟩) • (Pi.single (e.symm ⟨τ, k⟩) 1 : Fin g → ℂ) = v := by
  funext jj
  rw [Finset.sum_apply]
  by_cases h : (e jj).1 = τ
  · obtain ⟨⟨τ', k⟩, rfl⟩ := e.symm.surjective jj
    obtain rfl : τ' = τ := by simpa using h
    rw [Finset.sum_eq_single k (fun b _ hb => ?_) (by simp)]
    · simp
    · have : e.symm ⟨τ', k⟩ ≠ e.symm ⟨τ', b⟩ := fun hh => hb (by simpa using (e.symm.injective hh).symm)
      simp [Pi.single_eq_of_ne this]
  · have h0 : v jj = 0 := by_contra fun h' => h (hv jj h')
    rw [h0]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : jj ≠ e.symm ⟨τ, b⟩ := fun hh => h (by rw [hh]; simp)
    simp [Pi.single_eq_of_ne this]

/- English proof (translation)
Rewrite using `[← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]`. Rewrite `hl`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `cf hc`. Use `hl cf (funext fun jj => ?_)` and prove the remaining obligations. Distinguish the cases in `h : (e jj).1 = τ`.

Take `⟨⟨τ', k⟩, rfl⟩` from `e.symm.surjective jj`. Take `rfl : τ' = τ` from `by simpa using h`. Use `congrFun hc k` as an intermediate fact. Simplify `this` using `[Finset.sum_apply, Matrix.row]`. Rewrite using `[Finset.sum_apply]`.

Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Establish `h0 : v b jj = 0` using `by_contra fun h' => h (hv b jj h')`. Simplify using `[h0]`.
-/
theorem isUnit_det_of_support {J : Type} {m : J → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : J, Fin (m τ)) (τ : J)
    (v : Fin (m τ) → Fin g → ℂ) (hl : LinearIndependent ℂ v) (hv : ∀ i jj, v i jj ≠ 0 → (e jj).1 = τ) :
    IsUnit (Matrix.of fun i k : Fin (m τ) => v i (e.symm ⟨τ, k⟩)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
  rw [Fintype.linearIndependent_iff] at hl ⊢
  intro cf hc
  refine hl cf (funext fun jj => ?_)
  by_cases h : (e jj).1 = τ
  · obtain ⟨⟨τ', k⟩, rfl⟩ := e.symm.surjective jj
    obtain rfl : τ' = τ := by simpa using h
    have := congrFun hc k
    simpa [Finset.sum_apply, Matrix.row] using this
  · rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have h0 : v b jj = 0 := by_contra fun h' => h (hv b jj h')
    simp [h0]

/- English proof (translation)
Introduce `_ L2 E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha th Θ z _ hz w hw`. Establish `hT` using `L2.secTwist`. Establish `hP` using `Ha.period w hw`. Take `⟨hsym, hpos⟩` from `Θ.pos w hw`. Take `⟨hd, w₀, hw₀⟩` from `(GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero Uw.g Θ.c₁ Θ.c₂ Θ.half₁ Θ.half₂).1 _ hsym hpos`.

Establish `hθd : Differentiable ℂ (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v))` using `hd.comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Θ.h)).differentiable`. Establish `hθ : ∃ v, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v) ≠ 0`. Use `⟨∑ k, w₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1)), ?_⟩` and prove the remaining obligations. Establish `: Θ.h.mulVec (∑ k, w₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = w₀`. Rewrite using `[Matrix.mulVec_sum]`.

Simplify using `only [Matrix.mulVec_smul, (Θ.per w _).1]`. Conclude with `(pi_eq_sum_univ' w₀).symm`. Rewrite using `[this]` and apply the resulting hypothesis. Take `⟨-, hder, -⟩` from `GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ Uw.F Ha.i _ hP`. Use `existsUnique_of_exists_of_unique ?_ ?_` and prove the remaining obligations.

Take `⟨u, hu, htan, heig, hbas⟩` from `GlobalTheory.T.exists_tangent_eigenbasis_exponential E H Dw l Xo c σ Uw.g Uw.e Uw.F Ha.i _ hP`. Take `⟨fr, hfr⟩` from `Θ.frame w hw`. Take `⟨s, hs⟩` from `hfr.2.2.2.2`. Take `⟨t, ht, hval⟩` from `GlobalTheory.FrameUnif.ThetaPtEx.exists_gen hT (Uw.F.u Ha.i (Ha.Pw w)) (Uw.F.ex Ha.i (Ha.Pw w)) (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v)) fr Θ.κ Θ.κ_ne hθ hfr.2.1 s hs`. Set `y₀ : FrPt Xo c (CAt σ)` to `⟨Uw.F.u Ha.i (Ha.Pw w), Uw.F.over_σ _ _ hP, u, htan, heig, hbas, t, ht⟩`.

Establish `hch` using `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c (CAt σ) y₀`. Take `⟨⟨x', xo', u', tan', eig', basis', s', gen'⟩, ⟨hx, hc, -⟩, -⟩` from `hch (fun τ => (Matrix.of fun i k : Fin (Dw.mult τ) => z τ i (Uw.e.symm ⟨τ, k⟩) : Matrix _ _ ℂ)) 1 (fun τ => isUnit_det_of_support Uw.e τ (z τ) (hz τ).1 (hz τ).2)`. Simplify using `only [y₀] at hx hc`. Substitute `hx` using the available equality. Use `⟨⟨Uw.F.u Ha.i (Ha.Pw w), xo', u', tan', eig', basis', t, ht⟩, ⟨rfl, fun τ i => ?_⟩, fr, hfr, hval⟩` and prove the remaining obligations.

Use `(GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ Uw.F Ha.i _ hP _ (u τ) _ (hu τ) (fun k => z τ i (Uw.e.symm ⟨τ, k⟩)) (u' τ i)).1 (hc τ i)` as an intermediate fact. Rewrite `this` using `[sum_single_of_support Uw.e τ (z τ i) ((hz τ).2 i)]`. Then use the resulting hypothesis. Introduce and unpack `⟨x, xo, u, tan, eig, basis, s, gen⟩ ⟨x', xo', u', tan', eig', basis', s', gen'⟩ ⟨⟨hx, hu⟩, fr, hfr, hs⟩ ⟨⟨hx', hu'⟩, fr', hfr', hs'⟩ dsimp only at hx hu hs hx' hu' hs'`. Substitute `hx hx'` using the available equality. Take `rfl : u = u'` from `funext fun τ => funext fun i => (hder _).unique (hu τ i) (hu' τ i)`.

Establish `hss` using `gen_unique hT Uw.F Ha.i _ hP _ hθd hθ Θ.κ Θ.κ_ne fr fr' hfr hfr' s s' gen hs hs'`. Choose the witnesses or unpack the hypotheses as in `rfl : s = s' := by`. Consider the cases of `s`. Consider the cases of `s'`. Use `congr 1`.

Conclude with `(funext hss).symm`. Both sides reduce to the same expression.
-/
theorem existsUnique_anFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ w : ℂ, Ha.T < w.im → ∃! y, AnFr Ha Θ z w y := by
  intro _ L2 E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha th Θ z _ hz w hw
  have hT := L2.secTwist
  have hP := Ha.period w hw
  obtain ⟨hsym, hpos⟩ := Θ.pos w hw
  obtain ⟨hd, w₀, hw₀⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero Uw.g Θ.c₁ Θ.c₂ Θ.half₁ Θ.half₂).1 _ hsym hpos
  have hθd : Differentiable ℂ (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v)) :=
    hd.comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Θ.h)).differentiable
  have hθ : ∃ v, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v) ≠ 0 := by
    refine ⟨∑ k, w₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1)), ?_⟩
    have : Θ.h.mulVec (∑ k, w₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = w₀ := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, (Θ.per w _).1]
      exact (pi_eq_sum_univ' w₀).symm
    rwa [this]
  obtain ⟨-, hder, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ Uw.F Ha.i _ hP
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨u, hu, htan, heig, hbas⟩ := GlobalTheory.T.exists_tangent_eigenbasis_exponential E H Dw l Xo c σ Uw.g Uw.e Uw.F Ha.i _ hP
    obtain ⟨fr, hfr⟩ := Θ.frame w hw
    obtain ⟨s, hs⟩ := hfr.2.2.2.2
    obtain ⟨t, ht, hval⟩ := GlobalTheory.FrameUnif.ThetaPtEx.exists_gen hT (Uw.F.u Ha.i (Ha.Pw w)) (Uw.F.ex Ha.i (Ha.Pw w))
      (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v)) fr Θ.κ Θ.κ_ne hθ hfr.2.1 s hs
    let y₀ : FrPt Xo c (CAt σ) := ⟨Uw.F.u Ha.i (Ha.Pw w), Uw.F.over_σ _ _ hP, u, htan, heig, hbas, t, ht⟩
    have hch := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c (CAt σ) y₀
    obtain ⟨⟨x', xo', u', tan', eig', basis', s', gen'⟩, ⟨hx, hc, -⟩, -⟩ :=
      hch (fun τ => (Matrix.of fun i k : Fin (Dw.mult τ) => z τ i (Uw.e.symm ⟨τ, k⟩) : Matrix _ _ ℂ)) 1
        (fun τ => isUnit_det_of_support Uw.e τ (z τ) (hz τ).1 (hz τ).2)
    dsimp only [y₀] at hx hc
    subst hx
    refine ⟨⟨Uw.F.u Ha.i (Ha.Pw w), xo', u', tan', eig', basis', t, ht⟩, ⟨rfl, fun τ i => ?_⟩, fr, hfr, hval⟩
    have := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ Uw.F Ha.i _ hP _ (u τ) _ (hu τ)
      (fun k => z τ i (Uw.e.symm ⟨τ, k⟩)) (u' τ i)).1 (hc τ i)
    rwa [sum_single_of_support Uw.e τ (z τ i) ((hz τ).2 i)] at this
  · rintro ⟨x, xo, u, tan, eig, basis, s, gen⟩ ⟨x', xo', u', tan', eig', basis', s', gen'⟩
      ⟨⟨hx, hu⟩, fr, hfr, hs⟩ ⟨⟨hx', hu'⟩, fr', hfr', hs'⟩
    dsimp only at hx hu hs hx' hu' hs'
    subst hx hx'
    obtain rfl : u = u' := funext fun τ => funext fun i => (hder _).unique (hu τ i) (hu' τ i)
    have hss := gen_unique hT Uw.F Ha.i _ hP _ hθd hθ Θ.κ Θ.κ_ne fr fr' hfr hfr' s s' gen hs hs'
    obtain rfl : s = s' := by
      cases s; cases s'
      congr 1
      exact (funext hss).symm
    rfl

end GlobalTheory.ArcQ.AnFrEx
