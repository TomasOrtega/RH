import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitWedge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorFieldEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniversalLieModelPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionSpecializeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineGeneratorGeometricStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsAtFieldPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RepScalar

/- English proof (translation)
Establish `hu : LinearIndependent F u`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span]`. Use `linearIndependent_iff_card_eq_finrank_span.1 ht` as an intermediate fact. Rewrite using `[Set.finrank, ← h]`. Conclude with `this`.

Use `⟨hu, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • u k = t i` using `fun i => (Submodule.mem_span_range_iff_exists_fun F).1 (h ▸ Submodule.subset_span ⟨i, rfl⟩)`. Establish `h2 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • t k = u i` using `fun i => (Submodule.mem_span_range_iff_exists_fun F).1 (h.symm ▸ Submodule.subset_span ⟨i, rfl⟩)`. Use `choose A hA using h1`. Use `choose B hB using h2`.

Establish `hAB : (Matrix.of A) * (Matrix.of B) = 1`. Use extensionality with `i l`. Establish `key : ∑ m, ((Matrix.of A * Matrix.of B) i m - (1 : Matrix (Fin n) (Fin n) F) i m) • t m = 0`. Establish `e1 : ∑ m, (Matrix.of A * Matrix.of B) i m • t m = t i` using `by conv_rhs => rw [← hA i]`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, ← hB, Finset.smul_sum, smul_smul]`.

Conclude with `Finset.sum_comm`. Establish `e2 : ∑ m, (1 : Matrix (Fin n) (Fin n) F) i m • t m = t i`. Simplify using `[Matrix.one_apply]`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, e1, e2, sub_self]`. Use `Fintype.linearIndependent_iff.1 ht _ key l` as an intermediate fact.

Conclude with `sub_eq_zero.1 this`. Use `⟨Matrix.of A, fun i => (hA i).symm, ?_⟩` and prove the remaining obligations. Use `congrArg Matrix.det hAB` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `IsUnit.of_mul_eq_one _ this`.
-/
theorem exchange {F W : Type} [Field F] [AddCommGroup W] [Module F W] {n : ℕ} {t u : Fin n → W}
    (ht : LinearIndependent F t) (h : Submodule.span F (Set.range t) = Submodule.span F (Set.range u)) :
    LinearIndependent F u ∧ ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, t i = ∑ k, A i k • u k) ∧ IsUnit A.det := by
  have hu : LinearIndependent F u := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    have := linearIndependent_iff_card_eq_finrank_span.1 ht
    rw [Set.finrank, ← h]
    exact this
  refine ⟨hu, ?_⟩
  have h1 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • u k = t i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun F).1 (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  have h2 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • t k = u i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun F).1 (h.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose A hA using h1
  choose B hB using h2
  have hAB : (Matrix.of A) * (Matrix.of B) = 1 := by
    ext i l
    have key : ∑ m, ((Matrix.of A * Matrix.of B) i m - (1 : Matrix (Fin n) (Fin n) F) i m) • t m = 0 := by
      have e1 : ∑ m, (Matrix.of A * Matrix.of B) i m • t m = t i := by
        conv_rhs => rw [← hA i]
        simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, ← hB, Finset.smul_sum, smul_smul]
        exact Finset.sum_comm
      have e2 : ∑ m, (1 : Matrix (Fin n) (Fin n) F) i m • t m = t i := by
        simp [Matrix.one_apply]
      simp only [sub_smul, Finset.sum_sub_distrib, e1, e2, sub_self]
    have := Fintype.linearIndependent_iff.1 ht _ key l
    exact sub_eq_zero.1 this
  refine ⟨Matrix.of A, fun i => (hA i).symm, ?_⟩
  have := congrArg Matrix.det hAB
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one _ this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

/- English proof (translation)
Take `⟨W, _, _, Mu, Mz, ρ, hu, hz, hS⟩` from `GlobalTheory.T.universal_lie_model_pullback E H D l Xo c O β Y F y`. Take `⟨m, e, cf, h1, h2⟩` from `GlobalTheory.T.eigen_projector_field_embedding E c.F (tauIn c τ)`. Take `⟨u, hval, hspan⟩` from `GlobalTheory.T.lie_model_action_specialize Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M F (y ≫ Y.j) h W Mz (𝓞 E) Y.t.act Z.ρ ρ c.F Z.inc βF (tauIn c τ) m e cf n b Z.gen Y.t.semi.smooth Z.act hz (GlobalTheory.T.constants_at_field_point E H D l Xo c O β Y U Z F βF y hβ hy h) h1 (h2 Z.Ω Z.V Z …`. Use `choose t ht using fun i => Mu.onto _ (hv.1 i).1`. Establish `hvt : v = fun i => Mu.pt (t i)` using `funext fun i => (ht i).symm`.

Substitute `hvt` using the available equality. Take `⟨hti, hts⟩` from `(Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ t).1 hv`. Take `⟨hui, A, hA, hAu⟩` from `exchange hti (hts.trans hspan.symm)`. Use `⟨fun i => Mu.pt (u i), A, (Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ u).2 ⟨hui, hspan⟩, fun i => ⟨Mz.pt (u i), hval i, hS (u i)⟩, fun i => (Test.isComb_iff Mu (A i) u (t i)).2 (hA i), hAu⟩` and prove the remaining obligations.
-/
theorem exists_value_frame (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U)
    (hβ : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (τ : E →+* ℂ) (F : Type) [Field F]
    (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap βF)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (n : ℕ) (b : Fin n → Z.V)
    (hb : (Z.eig τ).IsFrameAt b ⟨centre (y ≫ Y.j), h⟩) (v : Vecs y n)
    (hv : IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c τ)) v) :
    ∃ (v₀ : Vecs y n) (A : Matrix (Fin n) (Fin n) F),
      IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c τ)) v₀ ∧
      (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b i) v' ∧ SameVec Y y (v₀ i) v') ∧
      (∀ i, IsComb (A i) v₀ (v i)) ∧ IsUnit A.det := by
  obtain ⟨W, _, _, Mu, Mz, ρ, hu, hz, hS⟩ := GlobalTheory.T.universal_lie_model_pullback E H D l Xo c O β Y F y
  obtain ⟨m, e, cf, h1, h2⟩ := GlobalTheory.T.eigen_projector_field_embedding E c.F (tauIn c τ)
  obtain ⟨u, hval, hspan⟩ := GlobalTheory.T.lie_model_action_specialize Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M F (y ≫ Y.j) h W Mz (𝓞 E) Y.t.act Z.ρ ρ c.F Z.inc βF
    (tauIn c τ) m e cf n b Z.gen Y.t.semi.smooth Z.act hz (GlobalTheory.T.constants_at_field_point E H D l Xo c O β Y U Z F βF y hβ hy h) h1
    (h2 Z.Ω Z.V Z.inc Z.ρ) hb
  choose t ht using fun i => Mu.onto _ (hv.1 i).1
  have hvt : v = fun i => Mu.pt (t i) := funext fun i => (ht i).symm
  subst hvt
  obtain ⟨hti, hts⟩ := (Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ t).1 hv
  obtain ⟨hui, A, hA, hAu⟩ := exchange hti (hts.trans hspan.symm)
  refine ⟨fun i => Mu.pt (u i), A, (Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ u).2 ⟨hui, hspan⟩,
    fun i => ⟨Mz.pt (u i), hval i, hS (u i)⟩, fun i => (Test.isComb_iff Mu (A i) u (t i)).2 (hA i), hAu⟩

/- English proof (translation)
Take `⟨h, u, hu, rfl⟩` from `ha`. Take `⟨_, w, hw, rfl⟩` from `hb`. Conclude with `⟨h, u * w, by rw [map_mul, hu, hw], map_mul _ _ _⟩`.
-/
theorem valAt_mul {X : Scheme.{0}} {Ω R : Type} [Field Ω] [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X} {a b : Ω} {r s : R}
    (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, u, hu, rfl⟩ := ha
  obtain ⟨_, w, hw, rfl⟩ := hb
  exact ⟨h, u * w, by rw [map_mul, hu, hw], map_mul _ _ _⟩

/- English proof (translation)
Take `⟨h1, s, hs, rfl⟩` from `h`. Take `⟨h2, s', hs', rfl⟩` from `h'`. Rewrite using `[hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)]`.
-/
theorem valAt_eq {X : Scheme.{0}} {Ω R : Type} [Field Ω] [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)]

/- English proof (translation)
Establish `hmem : exteriorPower.ιMulti Ω p f ∈ L.wedge p x` using `Submodule.subset_span ⟨f, fun i => by`. Rewrite using `[hf.2]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩, rfl⟩`. Rewrite `hmem` using `[hL]`. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 hmem`.

Establish `hr' : ((r : Ω) * α) • a = exteriorPower.ιMulti Ω p f`. Rewrite using `[mul_smul]`. Conclude with `hr`. Establish `hne` using `WedgeFrame.wedge_ne_zero f hf.1`. Establish `h0 : (r : Ω) * α ≠ 0`.

Introduce `h0`. Rewrite `hr'` using `[h0, zero_smul]`. Conclude with `hne hr'.symm`. Conclude with `⟨((r : Ω) * α)⁻¹, by rw [← hr', smul_smul, inv_mul_cancel₀ h0, one_smul]⟩`.
-/
theorem exists_eq_smul_wedge {X : Scheme.{0}} {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ V} {x : Cpt ξ} {p : ℕ} {f : Fin p → V}
    (hf : L.IsFrameAt f x) {α : Ω} {a : ⋀[Ω]^p V} (hα : α ≠ 0)
    (hL : L.wedge p x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ g₀ : Ω, a = g₀ • exteriorPower.ιMulti Ω p f := by
  have hmem : exteriorPower.ιMulti Ω p f ∈ L.wedge p x :=
    Submodule.subset_span ⟨f, fun i => by
      rw [hf.2]; exact Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  rw [hL] at hmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
  have hr' : ((r : Ω) * α) • a = exteriorPower.ιMulti Ω p f := by
    rw [mul_smul]; exact hr
  have hne := WedgeFrame.wedge_ne_zero f hf.1
  have h0 : (r : Ω) * α ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hr'; exact hne hr'.symm
  exact ⟨((r : Ω) * α)⁻¹, by rw [← hr', smul_smul, inv_mul_cancel₀ h0, one_smul]⟩

end GlobalTheory.CompanionTheory.Ar.Flat.RepScalar

namespace GlobalTheory.CompanionTheory.Ar.Flat

open RepScalar

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y U Z τ φ φ' hβ hτ hg hl hfl hl' hfl'`. Take `⟨-, a, b, hgen, hrep⟩` from `hfl`. Take `⟨-, a', b', hgen', hrep'⟩` from `hfl'`. Take `⟨x, s, t, hx, ht, hst, ha', hb'⟩` from `GlobalTheory.T.line_generator_geometric E H D l Xo c O β Y U Z τ a a' b b' hβ hg hgen hgen'`. Use `⟨x, hx, fun F _ βF y v w hf => ?_⟩` and prove the remaining obligations.

Take `⟨hy, hU, hv, hw⟩` from `id hf`. Establish `hpt : y (IsLocalRing.closedPoint F) ∈ U` using `hU ⟨_, rfl⟩`. Establish `hsp : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)` using `((Z.closure _).1 hpt).map Y.j.continuous`. Establish `hmem : (⟨centre (y ≫ Y.j), hsp⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib` using `⟨Y.jQ (y (IsLocalRing.closedPoint F)), rfl⟩`. Take `⟨h1, h2, -, -⟩` from `GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ`.

Take `⟨U₁, hU₁, b₁, -, hb₁⟩` from `h1 _ hmem`. Take `⟨U₂, hU₂, b₂, -, hb₂⟩` from `h2 _ hmem`. Establish `f₁` using `hb₁ _ hmem hU₁`. Establish `f₂` using `hb₂ _ hmem hU₂`. Take `⟨v₀, A, hv₀, hval₁, hA, hAu⟩` from `exists_value_frame Y U Z hβ.2.2 τ F βF y hy hsp D.p b₁ f₁ v hv`.

Take `⟨w₀, B, hw₀, hval₂, hB, -⟩` from `exists_value_frame Y U Z hβ.2.2 (ComplexEmbedding.conjugate τ) F βF y hy hsp D.q b₂ f₂ w hw`. Establish `hf₀ : IsFramed U τ βF y v₀ w₀` using `⟨hy, hU, hv₀, hw₀⟩`. Take `⟨-, hb0, hco⟩` from `hgen`. Take `⟨α, κ, hα, hκ, hWa, hWb, -⟩` from `hco _ hmem`. Take `⟨ga, hga⟩` from `exists_eq_smul_wedge f₁ hα hWa`.

Take `⟨gb, hgb⟩` from `exists_eq_smul_wedge f₂ hκ hWb`. Establish `hgb0 : gb ≠ 0`. Introduce and unpack `rfl`. Conclude with `hb0 (by rw [hgb, zero_smul])`. Establish `r1` using `hrep F βF y v₀ w₀ b₁ b₂ ga gb hf₀ hga hgb hval₁ hval₂`.

Establish `r2` using `hrep' F βF y v₀ w₀ b₁ b₂ (s * ga) (t * gb) hf₀ (by rw [ha', hga, smul_smul]) (by rw [hb', hgb, smul_smul]) hval₁ hval₂`. Establish `r3` using `valAt_mul (GlobalTheory.T.constants_at_field_point E H D l Xo c O β Y U Z F βF y hβ.2.2 hy hsp x) r1`. Establish `e : s * ga / (t * gb) = Z.inc x * (ga / gb)`. Rewrite using `[hst]`. Clear the denominators using the available nonvanishing facts.

Rewrite `r2` using `[e]`. Establish `e2 : φ' F y v₀ w₀ = βF x * φ F y v₀ w₀` using `valAt_eq Z.gen r2 r3`. Establish `c1` using `hl.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB`. Establish `c2` using `hl'.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB`. Use `hAu.mul_left_injective ?_` and prove the remaining obligations.

Use `show φ' F y v w * A.det = βF x * φ F y v w * A.det`. Rewrite using `[c2, e2, _root_.mul_assoc (βF x), _root_.mul_assoc (βF x), c1]`.
-/
theorem exists_const_of_flatOnModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → Z.IsGeom → IsLineFn U τ φ → FlatOnModel Z τ φ → IsLineFn U τ φ' → FlatOnModel Z τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ φ φ' hβ hτ hg hl hfl hl' hfl'
  obtain ⟨-, a, b, hgen, hrep⟩ := hfl
  obtain ⟨-, a', b', hgen', hrep'⟩ := hfl'
  obtain ⟨x, s, t, hx, ht, hst, ha', hb'⟩ := GlobalTheory.T.line_generator_geometric E H D l Xo c O β Y U Z τ a a' b b' hβ hg hgen hgen'
  refine ⟨x, hx, fun F _ βF y v w hf => ?_⟩
  obtain ⟨hy, hU, hv, hw⟩ := id hf
  have hpt : y (IsLocalRing.closedPoint F) ∈ U := hU ⟨_, rfl⟩
  have hsp : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := ((Z.closure _).1 hpt).map Y.j.continuous
  have hmem : (⟨centre (y ≫ Y.j), hsp⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := ⟨Y.jQ (y (IsLocalRing.closedPoint F)), rfl⟩
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ
  obtain ⟨U₁, hU₁, b₁, -, hb₁⟩ := h1 _ hmem
  obtain ⟨U₂, hU₂, b₂, -, hb₂⟩ := h2 _ hmem
  have f₁ := hb₁ _ hmem hU₁
  have f₂ := hb₂ _ hmem hU₂
  obtain ⟨v₀, A, hv₀, hval₁, hA, hAu⟩ := exists_value_frame Y U Z hβ.2.2 τ F βF y hy hsp D.p b₁ f₁ v hv
  obtain ⟨w₀, B, hw₀, hval₂, hB, -⟩ := exists_value_frame Y U Z hβ.2.2 (ComplexEmbedding.conjugate τ) F βF y hy hsp D.q b₂ f₂ w hw
  have hf₀ : IsFramed U τ βF y v₀ w₀ := ⟨hy, hU, hv₀, hw₀⟩
  obtain ⟨-, hb0, hco⟩ := hgen
  obtain ⟨α, κ, hα, hκ, hWa, hWb, -⟩ := hco _ hmem
  obtain ⟨ga, hga⟩ := exists_eq_smul_wedge f₁ hα hWa
  obtain ⟨gb, hgb⟩ := exists_eq_smul_wedge f₂ hκ hWb
  have hgb0 : gb ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [hgb, zero_smul])
  have r1 := hrep F βF y v₀ w₀ b₁ b₂ ga gb hf₀ hga hgb hval₁ hval₂
  have r2 := hrep' F βF y v₀ w₀ b₁ b₂ (s * ga) (t * gb) hf₀ (by rw [ha', hga, smul_smul])
    (by rw [hb', hgb, smul_smul]) hval₁ hval₂
  have r3 := valAt_mul (GlobalTheory.T.constants_at_field_point E H D l Xo c O β Y U Z F βF y hβ.2.2 hy hsp x) r1
  have e : s * ga / (t * gb) = Z.inc x * (ga / gb) := by
    rw [hst]; field_simp
  rw [e] at r2
  have e2 : φ' F y v₀ w₀ = βF x * φ F y v₀ w₀ := valAt_eq Z.gen r2 r3
  have c1 := hl.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB
  have c2 := hl'.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB
  refine hAu.mul_left_injective ?_
  show φ' F y v w * A.det = βF x * φ F y v w * A.det
  rw [c2, e2, _root_.mul_assoc (βF x), _root_.mul_assoc (βF x), c1]

end GlobalTheory.CompanionTheory.Ar.Flat
