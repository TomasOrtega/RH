import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentMapContinuousSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralMultipleExtension
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

open Filter Topology GlobalTheory.ChartGlue

namespace GlobalTheory.Mean4O.HessInd

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨by rw [pow_zero]; exact unitAt_one _, by`. Establish `e` using `ratVal_fnOf (y := y) mem_ptsIn_top trivial 1`. Rewrite using `[map_one, ev_one mem_ptsIn_top, ← pow_zero b, ← pow_zero (ratVal b y)] at e⟩` and apply the resulting hypothesis. Consider the case `succ n ih => exact ⟨by rw [pow_succ]; exact ih.1.mul hb, by`.

Rewrite using `[pow_succ, pow_succ, ratVal_mul ih.1.regAt hb.regAt, ih.2]⟩`.
-/
theorem unitAt_pow_ratVal {k : Type} [CommRing k] {σ : k →+* ℂ} {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    {y : CxPts q σ} {b : Z.functionField} (hb : UnitAt (under y) b) (n : ℕ) :
    UnitAt (under y) (b ^ n) ∧ ratVal (b ^ n) y = ratVal b y ^ n := by
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact unitAt_one _, by
      have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
      rwa [map_one, ev_one mem_ptsIn_top, ← pow_zero b, ← pow_zero (ratVal b y)] at e⟩
  | succ n ih => exact ⟨by rw [pow_succ]; exact ih.1.mul hb, by
      rw [pow_succ, pow_succ, ratVal_mul ih.1.regAt hb.regAt, ih.2]⟩

/- English proof (translation)
Establish `hle : X.basicOpen g ≤ W` using `X.basicOpen_le g`. Establish `ho` using `isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i ⊓ X.basicOpen g))`. Establish `hm` using `mem_over c.e hy (mem_ptsIn_inf.2 ⟨hi, (mem_ptsIn_basicOpen hW g).2 hg0⟩)`. Establish `hg : DifferentiableOn ℂ (ev p σ W g ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ X.basicOpen g))` using `(c.holo _ g).mono fun v hv => ⟨hv.1, ptsIn_mono hle (mem_ptsIn_inf.1 hv.2).2⟩`. Establish `h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ X.basicOpen g), (ev p σ _ g ∘ c.e.symm) v ≠ 0` using `fun v hv => (mem_ptsIn_basicOpen (ptsIn_mono hle (mem_ptsIn_inf.1 hv.2).2) g).1 (mem_ptsIn_inf.1 hv.2).2`.

Establish `e₁` using `ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho ((contDiffOn_chart (h i) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩) (contDiffOn_log_normSq ho hg h0) (-1) hm`. Establish `e₀ : ReciprocityTheory.L2DbarEstimates.cHess e (fun w => ((Real.log (‖(ev p σ _ g ∘ c.e.symm) w‖ ^ 2) : ℝ) : ℂ)) (c.e y) = 0`. Use extensionality with `a b`. Conclude with `ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 a b`. Rewrite `e₁` using `[e₀, smul_zero, add_zero]`.

Use `e₁.symm.trans ((ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_add_const _ (t : ℂ) _).symm.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_))` and prove the remaining obligations. Establish `hc : Tendsto c.e.symm (𝓝 (c.e y)) (𝓝 y)`. Use `c.e.continuousAt_symm (c.e.map_source hy)` as an intermediate fact. Rewrite `this` using `[ContinuousAt, c.e.left_inv hy]`. Then use the resulting hypothesis. Use `filter_upwards [hc.eventually hu] with v hv`.

Rewrite using `[hv]`. Simplify using `only [Function.comp_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hess_eq_of_log {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {e : ℕ} {B : LB X}
    {φ : Weight p σ B} (h : φ.IsCInf) (c : AlgChart p σ e) {y : CxPts p σ} (hy : y ∈ c.e.source) {i : B.ι}
    (hi : y ∈ ptsIn p σ (B.U i)) {W : X.Opens} (g : Γ(X, W)) (hW : y ∈ ptsIn p σ W) (hg0 : ev p σ W g y ≠ 0)
    {u : CxPts p σ → ℝ} (t : ℝ) (hu : ∀ᶠ w in 𝓝 y, u w = φ.φ i w - Real.log (‖ev p σ W g w‖ ^ 2) + t) :
    c.hess φ i y = ReciprocityTheory.L2DbarEstimates.cHess e (fun v => ((u (c.e.symm v) : ℝ) : ℂ)) (c.e y) := by
  have hle : X.basicOpen g ≤ W := X.basicOpen_le g
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i ⊓ X.basicOpen g))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨hi, (mem_ptsIn_basicOpen hW g).2 hg0⟩)
  have hg : DifferentiableOn ℂ (ev p σ W g ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ X.basicOpen g)) :=
    (c.holo _ g).mono fun v hv => ⟨hv.1, ptsIn_mono hle (mem_ptsIn_inf.1 hv.2).2⟩
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ X.basicOpen g),
      (ev p σ _ g ∘ c.e.symm) v ≠ 0 := fun v hv =>
    (mem_ptsIn_basicOpen (ptsIn_mono hle (mem_ptsIn_inf.1 hv.2).2) g).1 (mem_ptsIn_inf.1 hv.2).2
  have e₁ := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h i) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    (contDiffOn_log_normSq ho hg h0) (-1) hm
  have e₀ : ReciprocityTheory.L2DbarEstimates.cHess e (fun w => ((Real.log (‖(ev p σ _ g ∘ c.e.symm) w‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext a b
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 a b
  rw [e₀, smul_zero, add_zero] at e₁
  refine e₁.symm.trans ((ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_add_const _ (t : ℂ) _).symm.trans
    (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_))
  have hc : Tendsto c.e.symm (𝓝 (c.e y)) (𝓝 y) := by
    have := c.e.continuousAt_symm (c.e.map_source hy)
    rwa [ContinuousAt, c.e.left_inv hy] at this
  filter_upwards [hc.eventually hu] with v hv
  rw [hv]
  simp only [Function.comp_apply]
  push_cast
  ring

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {V : Cover Y}

/- English proof (translation)
Substitute `hσ` using the available equality. Establish `hz : under z ∈ (L.B.pull V.j).U (fun _ => i)`. Use `Set.mem_iInter.2 fun _ => ?_` and prove the remaining obligations. Use `mem_ptsIn.1 hi` as an intermediate fact. Rewrite `this` using `[e₂]`.

Conclude with `this`. Establish `hu : V.π (under z) = under y` using `by show _ = y.1 _`. Rewrite using `[e₁]`. Both sides reduce to the same expression. Establish `H` using `h₂ τ z y y' (fun _ => i) e₁ e₂ hz`.

Establish `U₁` using `h₁ _ _ hz`. Rewrite `U₁` using `[hu]`. Establish `hb` using `(Base.isEqn_eqn A.D (under y)).generatesAt_iff.1 hf`. Use `set b := f * (eqn A.D (under y) : Y.Fn) with hbd`. Use `set g := genAt A.D (under y) with hgd`.

Establish `hfb : f = b * g` using `by simp [hbd, hgd, genAt]`. Establish `hP : C.pn Y τ A.D (A.m τ) (C.cx Y τ f) y = ‖ratVal b y‖ ^ 2 * C.pn Y τ A.D (A.m τ) (C.cx Y τ g) y`. Rewrite using `[← C.pn_mul Y τ A.D (A.m τ) _ _ y hb.regAt (generatesAt_genAt A.D _).regularAt, ← hfb]`. Establish `hφb : UnitAt (under z) (V.φ b)` using `V.unitAt_φ (hu ▸ hb)`. Take `⟨k₁, k₂⟩` from `unitAt_pow_ratVal hφb k`.

Rewrite `k₂` using `[V.ratVal_φ z y e₁ hb.regAt]`. Establish `hs : V.φ f ^ k * (r (fun _ => i) : V.G.functionField) = V.φ b ^ k * (V.φ g ^ k * (r (fun _ => i) : V.G.functionField))`. Rewrite using `[hfb, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs]`.

Use `⟨k₁.mul U₁, ?_⟩` and prove the remaining obligations. Rewrite using `[ratVal_mul k₁.regAt U₁.regAt, k₂, lnN, hP]`. Establish `n₁ : 0 < ‖ratVal b y‖` using `norm_pos_iff.2 (ratVal_ne_zero hb)`. Establish `n₂` using `norm_pos_iff.2 (ratVal_ne_zero U₁)`. Establish `n₃ : 0 < C.pn Y τ A.D (A.m τ) (C.cx Y τ g) y` using `hp`.

Establish `H'` using `congrArg Real.log H`. Rewrite `H'` using `[Real.log_pow, Real.log_mul (Real.exp_pos _).ne' n₃.ne', Real.log_exp, Real.log_mul (pow_pos n₂ 2).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]`. Rewrite using `[Real.log_mul (pow_pos n₁ 2).ne' n₃.ne', norm_mul, norm_pow, Real.log_pow, Real.log_pow, Real.log_mul (pow_pos n₁ k).ne' n₂.ne', Real.log_pow]`. Move the coercions through the operations in `at H' ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weight_eq {A : Adl C Y} {L : HermLB V.p} {k : ℕ} {r : (L.B.pull V.j).ι → V.G.functionFieldˣ}
    (h₁ : ∀ i, ∀ x ∈ (L.B.pull V.j).U i, UnitAt x (V.φ (genAt A.D (V.π x)) ^ k * r i))
    (h₂ : ∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)))
      (i : (L.B.pull V.j).ι), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → under z ∈ (L.B.pull V.j).U i →
      (Real.exp (-(2 * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
          C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y) ^ k =
        ‖ratVal (V.φ (genAt A.D (under y)) ^ k * (r i : V.G.functionField)) z‖ ^ 2 *
          Real.exp (-(L.φ _).φ (i PUnit.unit) y'))
    {τ : F →+* ℂ} {σ : 𝓞 F →+* ℂ} (hσ : τ.comp (algebraMap (𝓞 F) F) = σ) (z : CxPts (V.π ≫ Y.str) τ) (y : Pts Y τ)
    (y' : CxPts V.p σ) (i : L.B.ι) (e₁ : y.1 = z.1 ≫ V.π) (e₂ : y'.1 = z.1 ≫ V.j) (hi : y' ∈ ptsIn V.p σ (L.B.U i))
    {f : Y.Fn} (hf : A.D.GeneratesAt (under y) f) (hp : PosAt (A.m τ) y) :
    UnitAt (under z) (V.φ f ^ k * (r (fun _ => i) : V.G.functionField)) ∧
      2 * (k * -lnN (A.m τ) f y) = (L.φ σ).φ i y' -
        Real.log (‖ratVal (V.φ f ^ k * (r (fun _ => i) : V.G.functionField)) z‖ ^ 2) -
          k * (2 * (A.n : ℕ) * A.ci (InfinitePlace.mk τ)) := by
  subst hσ
  have hz : under z ∈ (L.B.pull V.j).U (fun _ => i) := by
    refine Set.mem_iInter.2 fun _ => ?_
    have := mem_ptsIn.1 hi
    rw [e₂] at this
    exact this
  have hu : V.π (under z) = under y := by
    show _ = y.1 _
    rw [e₁]
    rfl
  have H := h₂ τ z y y' (fun _ => i) e₁ e₂ hz
  have U₁ := h₁ _ _ hz
  rw [hu] at U₁
  have hb := (Base.isEqn_eqn A.D (under y)).generatesAt_iff.1 hf
  set b := f * (eqn A.D (under y) : Y.Fn) with hbd
  set g := genAt A.D (under y) with hgd
  have hfb : f = b * g := by simp [hbd, hgd, genAt]
  have hP : C.pn Y τ A.D (A.m τ) (C.cx Y τ f) y = ‖ratVal b y‖ ^ 2 * C.pn Y τ A.D (A.m τ) (C.cx Y τ g) y := by
    rw [← C.pn_mul Y τ A.D (A.m τ) _ _ y hb.regAt (generatesAt_genAt A.D _).regularAt, ← hfb]
  have hφb : UnitAt (under z) (V.φ b) := V.unitAt_φ (hu ▸ hb)
  obtain ⟨k₁, k₂⟩ := unitAt_pow_ratVal hφb k
  rw [V.ratVal_φ z y e₁ hb.regAt] at k₂
  have hs : V.φ f ^ k * (r (fun _ => i) : V.G.functionField) =
      V.φ b ^ k * (V.φ g ^ k * (r (fun _ => i) : V.G.functionField)) := by
    rw [hfb, map_mul]; ring
  rw [hs]
  refine ⟨k₁.mul U₁, ?_⟩
  rw [ratVal_mul k₁.regAt U₁.regAt, k₂, lnN, hP]
  have n₁ : 0 < ‖ratVal b y‖ := norm_pos_iff.2 (ratVal_ne_zero hb)
  have n₂ := norm_pos_iff.2 (ratVal_ne_zero U₁)
  have n₃ : 0 < C.pn Y τ A.D (A.m τ) (C.cx Y τ g) y := hp
  have H' := congrArg Real.log H
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' n₃.ne', Real.log_exp,
    Real.log_mul (pow_pos n₂ 2).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at H'
  rw [Real.log_mul (pow_pos n₁ 2).ne' n₃.ne', norm_mul, norm_pow, Real.log_pow, Real.log_pow,
    Real.log_mul (pow_pos n₁ k).ne' n₂.ne', Real.log_pow]
  push_cast at H' ⊢
  linarith

/- English proof (translation)
Introduce `F _ _ C Y V e M I ε π hD A L k Q hI hQ σ c y hy i hi`. Take `⟨r, -, h₁, h₂, -⟩` from `hI`. Establish `hcont` using `(Cover.isDown_continuous_surjective F Y V e M I ε π hD σ).1`. Take `⟨hσ, hw⟩` from `hD σ`. Use `choose w hwj hwπ using hw`.

Set `z : CxPts V.p σ → CxPts (V.π ≫ Y.str) (I.ε (ε σ))` to `fun a => ⟨w a, by rw [← Category.assoc, hwπ]; exact (I.pt _ (π σ a)).2⟩`. Take `⟨f, hf⟩` from `(hQ (ε σ)).1 (π σ y)`. Establish `key` using `fun a (ha : a ∈ ptsIn V.p σ (L.B.U i)) (hb : π σ a ∈ (Q (ε σ)).U (π σ y)) => weight_eq h₁ h₂ hσ (z a) (I.pt _ (π σ a)) a i (hwπ a).symm (hwj a).symm ha (hf _ hb).1 (hf _ hb).2.1`. Establish `hyQ` using `(Q (ε σ)).mem_U (π σ y)`. Take `⟨W, hW, g, hg⟩` from `(key y hi hyQ).1.regAt.exists_fnOf`.

Take `⟨W', hle, hy', n, g', hn, hg'⟩` from `GenericFibreInt.exists_nat_mul_eq_app F V.X V.G V.p _ V.j V.pb W _ hW Unit fun _ => g`. Establish `hmem (a : CxPts V.p σ) : a ∈ ptsIn V.p σ W' ↔ z a ∈ ptsIn _ _ (V.j ⁻¹ᵁ W')`. Rewrite using `[mem_ptsIn, mem_ptsIn, ← hwj a]`. Both sides reduce to the same expression. Establish `hval (a : CxPts V.p σ) (ha : a ∈ ptsIn V.p σ W') : ev V.p σ W' (g' ()) a = n * ratVal (V.φ f ^ k * (r (fun _ => i) : V.G.functionField)) (z a)`.

Establish `hz` using `(hmem a).1 ha`. Establish `e₁ : ev V.p σ W' (g' ()) a = ev _ _ (V.j ⁻¹ᵁ W') (V.j.app W' (g' ())) (z a)`. Use `Eq.trans ?_ (Points.valR_comp (w a) V.j W' (g' ()))` and prove the remaining obligations. Rewrite using `[hwj a]`. Both sides reduce to the same expression.

Rewrite using `[e₁, ← hg' (), ev_mul, ev_res hle hz, ← hg, ratVal_fnOf (ptsIn_mono hle hz), ev_eq hz, map_natCast]`. Establish `hyW` using `(hmem y).2 (mem_ptsIn.2 hy')`. Establish `hn' : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Use `hess_eq_of_log (L.cInf σ) c hy hi (g' ()) hyW ?_ (u := fun a => 2 * (k * (Q (ε σ)).φ (π σ y) (π σ a))) (Real.log (‖(n : ℂ)‖ ^ 2) - k * (2 * (A.n : ℕ) * A.ci (InfinitePlace.mk (I.ε (ε σ))))) ?_` and prove the remaining obligations. Rewrite using `[hval y hyW]`.

Conclude with `mul_ne_zero hn' (ratVal_ne_zero (key y hi hyQ).1)`. Use `filter_upwards [(isOpen_ptsIn _).mem_nhds hi, (isOpen_ptsIn _).mem_nhds hyW, (((Q (ε σ)).isOpen_U _).preimage hcont).mem_nhds hyQ] with a ha ha' hb`. Take `⟨k₁, k₂⟩` from `key a ha hb`. Rewrite using `[(hf _ hb).2.2, k₂, hval a ha', norm_mul, mul_pow, Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 hn')) (pow_ne_zero 2 (norm_ne_zero_iff.2 (ratVal_ne_zero k₁)))]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hessRel_of_induces : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (e : ℕ)
    (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)),
    V.IsDown I ε π → ∀ (A : Adl C Y) (L : HermLB V.p) (k : ℕ) (Q : M.Pot), V.Induces A L k →
    (∀ a, IsPot (I.pt a) (A.m (I.ε a)) (Q a) ∧ ReciprocityTheory.AnForm.M.IsPotential (M.A a) (Q a)) →
    HessRel ε π L fun a => (Q a).rsmul k := by
  intro F _ _ C Y V e M I ε π hD A L k Q hI hQ σ c y hy i hi
  obtain ⟨r, -, h₁, h₂, -⟩ := hI
  have hcont := (Cover.isDown_continuous_surjective F Y V e M I ε π hD σ).1
  obtain ⟨hσ, hw⟩ := hD σ
  choose w hwj hwπ using hw
  let z : CxPts V.p σ → CxPts (V.π ≫ Y.str) (I.ε (ε σ)) := fun a =>
    ⟨w a, by rw [← Category.assoc, hwπ]; exact (I.pt _ (π σ a)).2⟩
  obtain ⟨f, hf⟩ := (hQ (ε σ)).1 (π σ y)
  have key := fun a (ha : a ∈ ptsIn V.p σ (L.B.U i)) (hb : π σ a ∈ (Q (ε σ)).U (π σ y)) =>
    weight_eq h₁ h₂ hσ (z a) (I.pt _ (π σ a)) a i (hwπ a).symm (hwj a).symm ha (hf _ hb).1 (hf _ hb).2.1
  have hyQ := (Q (ε σ)).mem_U (π σ y)
  obtain ⟨W, hW, g, hg⟩ := (key y hi hyQ).1.regAt.exists_fnOf
  obtain ⟨W', hle, hy', n, g', hn, hg'⟩ := GenericFibreInt.exists_nat_mul_eq_app F V.X V.G V.p _ V.j V.pb W _ hW
    Unit fun _ => g
  have hmem (a : CxPts V.p σ) : a ∈ ptsIn V.p σ W' ↔ z a ∈ ptsIn _ _ (V.j ⁻¹ᵁ W') := by
    rw [mem_ptsIn, mem_ptsIn, ← hwj a]
    rfl
  have hval (a : CxPts V.p σ) (ha : a ∈ ptsIn V.p σ W') : ev V.p σ W' (g' ()) a =
      n * ratVal (V.φ f ^ k * (r (fun _ => i) : V.G.functionField)) (z a) := by
    have hz := (hmem a).1 ha
    have e₁ : ev V.p σ W' (g' ()) a = ev _ _ (V.j ⁻¹ᵁ W') (V.j.app W' (g' ())) (z a) := by
      refine Eq.trans ?_ (Points.valR_comp (w a) V.j W' (g' ()))
      rw [hwj a]
      rfl
    rw [e₁, ← hg' (), ev_mul, ev_res hle hz, ← hg, ratVal_fnOf (ptsIn_mono hle hz), ev_eq hz, map_natCast]
  have hyW := (hmem y).2 (mem_ptsIn.2 hy')
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine hess_eq_of_log (L.cInf σ) c hy hi (g' ()) hyW ?_
    (u := fun a => 2 * (k * (Q (ε σ)).φ (π σ y) (π σ a)))
    (Real.log (‖(n : ℂ)‖ ^ 2) - k * (2 * (A.n : ℕ) * A.ci (InfinitePlace.mk (I.ε (ε σ))))) ?_
  · rw [hval y hyW]
    exact mul_ne_zero hn' (ratVal_ne_zero (key y hi hyQ).1)
  · filter_upwards [(isOpen_ptsIn _).mem_nhds hi, (isOpen_ptsIn _).mem_nhds hyW,
      (((Q (ε σ)).isOpen_U _).preimage hcont).mem_nhds hyQ] with a ha ha' hb
    obtain ⟨k₁, k₂⟩ := key a ha hb
    rw [(hf _ hb).2.2, k₂, hval a ha', norm_mul, mul_pow, Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 hn'))
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (ratVal_ne_zero k₁)))]
    ring

end GlobalTheory.Mean4O.HessInd
