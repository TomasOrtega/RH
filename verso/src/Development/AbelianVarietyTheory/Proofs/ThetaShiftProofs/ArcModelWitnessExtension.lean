import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcNilpotent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOfStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSymplecticCoordinatesAdapted
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnimodularSymplecticCoordinatesAndLatticeRank
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemSpanSingleInlIff
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcTheta

/- English proof (translation)
Simplify using `[omegaStd, Pi.single_apply]`.
-/
theorem omegaStd_single_inl {g : ℕ} (u : Fin g ⊕ Fin g → ℤ) (k : Fin g) :
    omegaStd u (Pi.single (.inl k) 1) = -u (.inr k) := by
  simp [omegaStd, Pi.single_apply]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff`. Consider the case `exact _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff`. Consider the case `(apply _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff ..)`.
-/
theorem mem_span_single_inl {g : ℕ} (S : Finset (Fin g)) (u : Fin g ⊕ Fin g → ℤ) :
    u ∈ Submodule.span ℤ ((fun k => (Pi.single (Sum.inl k) 1 : Fin g ⊕ Fin g → ℤ)) '' (S : Set (Fin g))) ↔
      (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0 := by
  first
  | exact @_root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff
  | exact _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff
  | (apply _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff ..)

/- English proof (translation)
Set `I : Submodule ℤ Λ` to `{ carrier := {t | ∀ v, K v → ω t v = 0} add_mem' := fun ha hb v hv => by simp [ha v hv, hb v hv] zero_mem' := fun v _ => by simp smul_mem' := fun r x hx v hv => by simp [hx v hv] }`. Establish `halt : ω.IsAlt` using `hω`. Take `⟨g', bas, S, hs, hI, hr⟩` from `GlobalTheory.exists_symplectic_coordinates_adapted halt hp (I := I) (fun k x hk hx v hv => by`. Use `hx v hv` as an intermediate fact. Simplify `this)` using `[hk]`.

Use the proof step `(fun x hx y hy => hx y (h1 y hy)) (ε := -1) (Or.inr rfl)`. Take `rfl : g' = g` from `by omega`. Establish `hs' : ∀ u v, ω (bas u) (bas v) = -omegaStd u v` using `fun u v => by rw [hs]; ring`. Establish `horth : ∀ u, bas u ∈ I ↔ (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0` using `fun u => by`. Rewrite using `[← mem_span_single_inl, hI]`.

Establish `: (fun k => bas (Pi.single (Sum.inl k) 1)) '' (S : Set (Fin g')) = bas.toLinearMap '' ((fun k => (Pi.single (Sum.inl k) 1 : Fin g' ⊕ Fin g' → ℤ)) '' (S : Set (Fin g')))`. Rewrite using `[Set.image_image]`. Both sides reduce to the same expression. Rewrite using `[this, ← Submodule.map_span]`. Conclude with `Submodule.mem_map_equiv _ |>.trans (by simp)`.

Use `⟨bas, S, hs', fun u => ⟨fun hu k hk => ?_, fun hu => h2 _ fun t ht => ?_⟩, horth⟩` and prove the remaining obligations. Establish `hm : bas (Pi.single (Sum.inl k) 1) ∈ I`. Rewrite using `[hI]`. Conclude with `Submodule.subset_span ⟨k, hk, rfl⟩`. Use `hm _ hu` as an intermediate fact.

Rewrite `this` using `[← halt.neg_eq, hs', omegaStd_single_inl]`. Simplify using `using this`. Take `⟨t, rfl⟩` from `bas.surjective t`. Take `⟨e1, e2⟩` from `(horth t).1 ht`. Rewrite using `[hs', omegaStd, neg_eq_zero]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k ∈ S`. Simplify using `[e1, hu k hk]`. Simplify using `[e1, e2 k hk]`.
-/
theorem exists_adapted {Λ : Type} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (ω : LinearMap.BilinForm ℤ Λ) (hω : ∀ x, ω x x = 0) (hp : Function.Bijective ω) {g : ℕ}
    (hg : Module.finrank ℤ Λ = 2 * g) (K : Λ → Prop)
    (h1 : ∀ t, (∀ v, K v → ω t v = 0) → K t)
    (h2 : ∀ v, (∀ t, (∀ v', K v' → ω t v' = 0) → ω t v = 0) → K v) :
    ∃ (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] Λ) (S : Finset (Fin g)),
      (∀ u v, ω (bas u) (bas v) = -omegaStd u v) ∧ (∀ u, K (bas u) ↔ ∀ k ∈ S, u (.inr k) = 0) ∧
      ∀ u, (∀ v', K v' → ω (bas u) v' = 0) ↔ (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0 := by
  let I : Submodule ℤ Λ :=
    { carrier := {t | ∀ v, K v → ω t v = 0}
      add_mem' := fun ha hb v hv => by simp [ha v hv, hb v hv]
      zero_mem' := fun v _ => by simp
      smul_mem' := fun r x hx v hv => by simp [hx v hv] }
  have halt : ω.IsAlt := hω
  obtain ⟨g', bas, S, hs, hI, hr⟩ := GlobalTheory.exists_symplectic_coordinates_adapted halt hp (I := I)
    (fun k x hk hx v hv => by
      have := hx v hv
      simpa [hk] using this)
    (fun x hx y hy => hx y (h1 y hy)) (ε := -1) (Or.inr rfl)
  obtain rfl : g' = g := by omega
  have hs' : ∀ u v, ω (bas u) (bas v) = -omegaStd u v := fun u v => by rw [hs]; ring
  have horth : ∀ u, bas u ∈ I ↔ (∀ k, u (.inr k) = 0) ∧ ∀ k ∉ S, u (.inl k) = 0 := fun u => by
    rw [← mem_span_single_inl, hI]
    have : (fun k => bas (Pi.single (Sum.inl k) 1)) '' (S : Set (Fin g')) =
        bas.toLinearMap '' ((fun k => (Pi.single (Sum.inl k) 1 : Fin g' ⊕ Fin g' → ℤ)) '' (S : Set (Fin g'))) := by
      rw [Set.image_image]; rfl
    rw [this, ← Submodule.map_span]
    exact Submodule.mem_map_equiv _ |>.trans (by simp)
  refine ⟨bas, S, hs', fun u => ⟨fun hu k hk => ?_, fun hu => h2 _ fun t ht => ?_⟩, horth⟩
  · have hm : bas (Pi.single (Sum.inl k) 1) ∈ I := by
      rw [hI]; exact Submodule.subset_span ⟨k, hk, rfl⟩
    have := hm _ hu
    rw [← halt.neg_eq, hs', omegaStd_single_inl] at this
    simpa using this
  · obtain ⟨t, rfl⟩ := bas.surjective t
    obtain ⟨e1, e2⟩ := (horth t).1 ht
    rw [hs', omegaStd, neg_eq_zero]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ S
    · simp [e1, hu k hk]
    · simp [e1, e2 k hk]

/- English proof (translation)
Take `⟨fr, h1, h2, h3, h4, h5⟩` from `h`. Use `⟨fun j z => fr j (b, z), fun j => ?_, fun j z => h2 j b z hb, fun j j' z => h3 j j' b z hb, fun j => h4 j b hb, h5 b hb⟩` and prove the remaining obligations. Conclude with `(h1 j).comp ((differentiable_const b).prodMk differentiable_id).differentiableOn fun z hz => ⟨hb, hz⟩`.
-/
theorem isThetaFrameAt_of_isThetaFrame {g m : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] (L : RigLB G)
    (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ S)) (e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left))
    (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) (h : IsThetaFrame L B y e θ) (b : Fin m → ℂ) (hb : b ∈ B) :
    ∃ fr, IsThetaFrameAt L (y b) (e b) (θ b) fr := by
  obtain ⟨fr, h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun j z => fr j (b, z), fun j => ?_, fun j z => h2 j b z hb, fun j j' z => h3 j j' b z hb,
    fun j => h4 j b hb, h5 b hb⟩
  exact (h1 j).comp ((differentiable_const b).prodMk differentiable_id).differentiableOn fun z hz => ⟨hb, hz⟩

/- English proof (translation)
Substitute `hL` using the available equality. Take `⟨w, h1, h2, -⟩` from `m.lin`. Conclude with `⟨w, h1, h2⟩`.
-/
theorem exists_isRigIso {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (L' : RigLB t'.G)
    (hL : L' = t'.PP) : ∃ w : LB.Iso L'.L (t.PP.L.pull m.φ), IsRigIso m.cm L' t.PP w := by
  subst hL
  obtain ⟨w, h1, h2, -⟩ := m.lin
  exact ⟨w, h1, h2⟩

/- English proof (translation)
Introduce `hL hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ th hth`. Take `⟨nn, hN, hbe, -, hnn, hker, -⟩` from `GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha`. Set `w₀ : ℂ` to `((Ha.T + 1 : ℝ) : ℂ) * Complex.I`. Establish `hw₀ : Ha.T < w₀.im` using `by simp [w₀]`. Take `⟨-, hinj, hdisc, hsp, -⟩` from `Ha.period w₀ hw₀`.

Take `⟨hfree, hfin, hrk⟩` from `GlobalTheory.free_finite_finrank_of_discrete_span _ hinj hdisc hsp`. Take `⟨bas, S, hs, hk, horth⟩` from `exists_adapted (Fu.Di Ha.i).EF (Fu.Di Ha.i).alt (Fu.Di Ha.i).unimod hrk (fun v => Ha.y v = 0) hker (fun v hv => by`. Assume the negation of the conclusion as `hne`. Establish `h0` using `hv (nn v) fun v' hv' => by`. Use `hbe v v'` as an intermediate fact.

Rewrite `this` using `[hv', map_zero, neg_eq_zero]`. Conclude with `this`. Establish `h1` using `hbe v v`. Establish `h2` using `a.be_pos _ hne`. Rewrite `h1` using `[h0]`.

Use the proof step `omega)`. Establish `hconst : ∀ w k, Ha.Pw w (bas (Pi.single (.inl k) 1)) = Ha.P₀ (bas (Pi.single (.inl k) 1))` using `fun w k => by`. Rewrite using `[Ha.Pw_eq, hN, hnn _ ((hk _).2 fun j _ => by simp), map_zero, smul_zero, add_zero]`. Establish `hR` using `(GlobalTheory.RiemannRel.riemann_relations E H (Fu.Di Ha.i) g ty bas hs).1`. Take `⟨h, τ₀, hh, -⟩` from `hR _ (Ha.period w₀ hw₀)`.

Set `τ : ℂ → Matrix (Fin g) (Fin g) ℂ` to `fun w => h * Matrix.of fun i j => Ha.Pw w (bas (Pi.single (.inr j) 1)) i`. Establish `hper : ∀ w k, h.mulVec (Ha.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ h.mulVec (Ha.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1)` using `fun w k => by`. Use `⟨by rw [hconst, ← hconst w₀]; exact (hh k).1, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, GlobalTheory.RiemannRel.of_cols_mulVec (fun j => Ha.Pw w (bas (Pi.single (.inr j) 1))) k]`. Establish `hpos : ∀ w, Ha.T < w.im → (τ w).IsSymm ∧ ((τ w).map Complex.im).PosDef` using `fun w hw => by`.

Take `⟨h', τ', -, -, e1, e2, hu⟩` from `hR _ (Ha.period w hw)`. Rewrite using `[(hu h (τ w) (hper w)).2]`. Conclude with `⟨e1, e2⟩`. Set `B : Set (Fin 1 → ℂ)` to `{b | Ha.T < (b 0).im}`. Establish `hBo : IsOpen B` using `isOpen_lt continuous_const (by fun_prop)`.

Establish `hBc : IsPreconnected B`. Use `Convex.isPreconnected (?_ : Convex ℝ B)` and prove the remaining obligations. Conclude with `(convex_halfSpace_im_gt Ha.T).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0)`. Take `⟨c₁, c₂, hc₁, hc₂, hfr⟩` from `Fu.theta Ha.i 1 B (fun b => Ha.Pw (b 0)) bas (-1) (fun _ => h) (fun b => τ (b 0)) hBo hBc ⟨fun b hb => Ha.period _ hb, fun x => by`. Simplify using `only [Ha.Pw_eq]`.

Use the proof step `fun_prop⟩ (fun u v => by rw [hs]; simp) (fun b hb => ⟨(hpos _ hb).2, hper _⟩)`. Establish `hframe : ∀ w, Ha.T < w.im → ∃ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w)) (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr` using `fun w hw => isThetaFrameAt_of_isThetaFrame _ _ _ _ _ hfr (fun _ => w) hw`. Take `⟨⟨θ, ⟨s, fam, -, hex, hfam, -⟩, -⟩, -⟩` from `GlobalTheory.T.existsUnique_thetaOf_alt hL hL2 E H Dw l Xo c O β Y ℂ (σ.comp β) a χ W th hth`. Take `⟨w₂, hw₂⟩` from `exists_isRigIso W.m W.P.U.LG W.P.bundle`. Take `⟨w₁, hw₁⟩` from `exists_isRigIso Y.m _ rfl`.

Take `⟨w₃, hw₃⟩` from `exists_isRigIso Y.m0.toSABMap _ rfl`. Establish `hne : ∃ j, th.f j ≠ 0`. Take `⟨x, -, hx⟩` from `hth (IsLocalRing.closedPoint ℂ)`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Use `⟨j, fun e => ?_⟩` and prove the remaining obligations.

Rewrite `hj` using `[e, Scheme.basicOpen_zero]`. Conclude with `hj`. Take `⟨fr₀, hfr₀⟩` from `hframe w₀ hw₀`. Take `⟨κ, hκ, hS, hB, -⟩` from `Ha.theta th s fam bas S h τ c₁ c₂ w₂ w₁ w₃ hne hex hfam hs hk hper hc₁ hc₂ hw₂ hw₁ hw₃ ⟨w₀, fr₀, hw₀, hfr₀⟩`. Conclude with `⟨⟨bas, S, h, τ, c₁, c₂, κ, hs, hk, horth, hper, hpos, hc₁, hc₂, hframe, hκ, hS, hB⟩⟩`.
-/
theorem nonempty_thetaDat : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), IsTypeFn H Dw.p Dw.q ty → ∀ th : a.D₀.P.L.Sec, ThNZ th → Nonempty (ThetaDat Ha th) := by
  intro hL hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ th hth
  obtain ⟨nn, hN, hbe, -, hnn, hker, -⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  let w₀ : ℂ := ((Ha.T + 1 : ℝ) : ℂ) * Complex.I
  have hw₀ : Ha.T < w₀.im := by simp [w₀]
  obtain ⟨-, hinj, hdisc, hsp, -⟩ := Ha.period w₀ hw₀
  obtain ⟨hfree, hfin, hrk⟩ := GlobalTheory.free_finite_finrank_of_discrete_span _ hinj hdisc hsp
  obtain ⟨bas, S, hs, hk, horth⟩ := exists_adapted (Fu.Di Ha.i).EF (Fu.Di Ha.i).alt (Fu.Di Ha.i).unimod hrk
    (fun v => Ha.y v = 0) hker (fun v hv => by
      by_contra hne
      have h0 := hv (nn v) fun v' hv' => by
        have := hbe v v'
        rw [hv', map_zero, neg_eq_zero] at this
        exact this
      have h1 := hbe v v
      have h2 := a.be_pos _ hne
      rw [h0] at h1
      omega)
  have hconst : ∀ w k, Ha.Pw w (bas (Pi.single (.inl k) 1)) = Ha.P₀ (bas (Pi.single (.inl k) 1)) := fun w k => by
    rw [Ha.Pw_eq, hN, hnn _ ((hk _).2 fun j _ => by simp), map_zero, smul_zero, add_zero]
  have hR := (GlobalTheory.RiemannRel.riemann_relations E H (Fu.Di Ha.i) g ty bas hs).1
  obtain ⟨h, τ₀, hh, -⟩ := hR _ (Ha.period w₀ hw₀)
  let τ : ℂ → Matrix (Fin g) (Fin g) ℂ := fun w =>
    h * Matrix.of fun i j => Ha.Pw w (bas (Pi.single (.inr j) 1)) i
  have hper : ∀ w k, h.mulVec (Ha.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      h.mulVec (Ha.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1) := fun w k => by
    refine ⟨by rw [hconst, ← hconst w₀]; exact (hh k).1, ?_⟩
    rw [← Matrix.mulVec_mulVec, GlobalTheory.RiemannRel.of_cols_mulVec (fun j => Ha.Pw w (bas (Pi.single (.inr j) 1))) k]
  have hpos : ∀ w, Ha.T < w.im → (τ w).IsSymm ∧ ((τ w).map Complex.im).PosDef := fun w hw => by
    obtain ⟨h', τ', -, -, e1, e2, hu⟩ := hR _ (Ha.period w hw)
    rw [(hu h (τ w) (hper w)).2]
    exact ⟨e1, e2⟩
  let B : Set (Fin 1 → ℂ) := {b | Ha.T < (b 0).im}
  have hBo : IsOpen B := isOpen_lt continuous_const (by fun_prop)
  have hBc : IsPreconnected B := by
    refine Convex.isPreconnected (?_ : Convex ℝ B)
    exact (convex_halfSpace_im_gt Ha.T).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0)
  obtain ⟨c₁, c₂, hc₁, hc₂, hfr⟩ := Fu.theta Ha.i 1 B (fun b => Ha.Pw (b 0)) bas (-1) (fun _ => h) (fun b => τ (b 0))
    hBo hBc ⟨fun b hb => Ha.period _ hb, fun x => by
      simp only [Ha.Pw_eq]
      fun_prop⟩ (fun u v => by rw [hs]; simp) (fun b hb => ⟨(hpos _ hb).2, hper _⟩)
  have hframe : ∀ w, Ha.T < w.im → ∃ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w))
      (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr := fun w hw =>
    isThetaFrameAt_of_isThetaFrame _ _ _ _ _ hfr (fun _ => w) hw
  obtain ⟨⟨θ, ⟨s, fam, -, hex, hfam, -⟩, -⟩, -⟩ := GlobalTheory.T.existsUnique_thetaOf_alt hL hL2 E H Dw l Xo c O β Y ℂ (σ.comp β) a χ W th hth
  obtain ⟨w₂, hw₂⟩ := exists_isRigIso W.m W.P.U.LG W.P.bundle
  obtain ⟨w₁, hw₁⟩ := exists_isRigIso Y.m _ rfl
  obtain ⟨w₃, hw₃⟩ := exists_isRigIso Y.m0.toSABMap _ rfl
  have hne : ∃ j, th.f j ≠ 0 := by
    obtain ⟨x, -, hx⟩ := hth (IsLocalRing.closedPoint ℂ)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨j, fun e => ?_⟩
    rw [e, Scheme.basicOpen_zero] at hj
    exact hj
  obtain ⟨fr₀, hfr₀⟩ := hframe w₀ hw₀
  obtain ⟨κ, hκ, hS, hB, -⟩ := Ha.theta th s fam bas S h τ c₁ c₂ w₂ w₁ w₃ hne hex hfam hs hk hper hc₁ hc₂
    hw₂ hw₁ hw₃ ⟨w₀, fr₀, hw₀, hfr₀⟩
  exact ⟨⟨bas, S, h, τ, c₁, c₂, κ, hs, hk, horth, hper, hpos, hc₁, hc₂, hframe, hκ, hS, hB⟩⟩

end GlobalTheory.ArcTheta
