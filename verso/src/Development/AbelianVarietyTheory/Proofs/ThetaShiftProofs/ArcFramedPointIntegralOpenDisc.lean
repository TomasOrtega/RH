import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralGeneratorOfChartPointCdvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionOfArcNonzeroOnFibresStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarisationSectionGeneratesOfSpecialFibreStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcQ.DiscInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

/- English proof (translation)
Use `show Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem sp_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Rewrite using `[← sp_comp, ← sp_comp]`. Use `congr 1`. Apply the tactic sequence `exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← sp_comp, ← sp_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Rewrite using `[← sp_comp]`. Use `congr 1`. Apply the tactic sequence `exact RingHom.ext fun a => by ext <;> simp [dualMap]`.
-/
theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (dualMap (φ.comp io)) = spMap (dualMap φ) ≫ spMap (dualMap io) := by
  rw [← sp_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap]

/- English proof (translation)
Use `algebraize [f]`. Establish `: FaithfulSMul A V` using `(faithfulSMul_iff_algebraMap_injective A V).2 hf`. Use `show Module.Flat A V`. Use `infer_instance`.
-/
theorem flat_of_injective {A V : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing V] [IsDomain V]
    (f : A →+* V) (hf : Function.Injective f) : f.Flat := by
  algebraize [f]
  have : FaithfulSMul A V := (faithfulSMul_iff_algebraMap_injective A V).2 hf
  show Module.Flat A V
  infer_instance

/- English proof (translation)
Establish `: (1 : ptOver V V ⟶ G).left = η[G].left` using `by show spMap (algebraMap V V) ≫ _ = _`. Rewrite using `[show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]`. Conclude with `Category.id_comp _`. Unfold `IsTan IsTangent`. Rewrite using `[this]`.
-/
theorem isTan_iff {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Take `⟨w0, g0, r0, -⟩` from `m.lin`. Take `⟨θ', hθ'⟩` from `sec_pull_down ((isGen_iff w0).1 g0) t.PP.isLB G.PP.isLB θ`. Establish `he : k.cm.e = n.cm.e ≫ m.cm.e` using `by rw [k.base, n.base, m.base, hb]`. Take `⟨w', r', tri⟩` from `GlobalTheory.Reg.TieIntegral.exists_rigIso_cancel m.cm n.cm k.cm hφ he t'.PP G.PP t.PP w0 w ⟨g0, r0⟩ r`. Use `⟨θ', w', ?_, r', fun (i : PUnit → G.PP.L.ι) k' => fn_ext fun y hy => ?_⟩` and prove the remaining obligations.

Introduce and unpack `s ⟨z, hz, hz'⟩`. Take `⟨y, rfl, hy⟩` from `Scheme.exists_preimage_of_isPullback m.cart.1 z s hz`. Take `⟨j, hj, u⟩` from `(mem_nonzeroLocus _ _).1 hz'`. Take `⟨i, hi⟩` from `exists_chart G.PP.isLB y`. Use `⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨i, hi, ?_⟩⟩` and prove the remaining obligations.

Establish `u₁ : IsUnit (gs m.φ y _ (θ.f j))` using `by rw [gs_stalkMap m.φ y _ hj]; exact u.map _`. Establish `e` using `hθ' _ (𝟙 _) y j i hj hi`. Rewrite `e` using `[Category.id_comp]`. Conclude with `isUnit_of_mul_isUnit_right (e ▸ u₁)`. Establish `hi' : n.φ y ∈ G.PP.L.U (i PUnit.unit)` using `mem_pull.1 hy.1`.

Take `⟨j, hj⟩` from `exists_chart t.PP.isLB (m.φ (n.φ y))`. Establish `pt : k.φ y = m.φ (n.φ y)` using `congrArg (fun q => q y) hφ`. Establish `hj' : k.φ y ∈ t.PP.L.U j` using `pt ▸ hj`. Establish `e1` using `hθ' _ (𝟙 _ ≫ n.φ) y j (i PUnit.unit) hj hi'`. Establish `e2 : gs (𝟙 _ ≫ k.φ) y _ (θ.f j) = (gw w (𝟙 _) y j k').val * gs (𝟙 _) y _ (σ.f k')`.

Establish `hz : y ∈ (t.PP.L.pull k.φ).U (fun _ => j) ⊓ t'.PP.L.U k'` using `⟨mem_pull.2 hj', hy.2⟩`. Establish `le : (t.PP.L.pull k.φ).U (fun _ => j) ≤ k.φ ⁻¹ᵁ t.PP.L.U j` using `fun q hq => mem_pull.1 hq`. Establish `a` using `congrArg (gs (𝟙 _) y _) (hi (fun _ => j) k')`. Use `(gs_appLE k.φ _ _ le (𝟙 _) y hz.1 _).symm.trans ?_` and prove the remaining obligations. Rewrite using `[← hp (fun _ => j) le]`.

Conclude with `(gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))`. Establish `e3` using `tri _ (𝟙 _) y j (i PUnit.unit) k' hj hi' hy.2`. Establish `e4 : (𝟙 _ ≫ n.φ) ≫ m.φ = 𝟙 _ ≫ k.φ` using `by rw [Category.assoc, hφ]`. Rewrite `e1` using `[e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj]`. Use `(gs_res _ y _ hy _).trans ((gs_appLE n.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))` and prove the remaining obligations.

Use `Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)` and prove the remaining obligations. Conclude with `congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)`.
-/
theorem sec_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {G : SAB H S'} {t' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (m : SABMap G t f) (n : SABMap t' G g) (k : SABMap t' t h) (hb : h = g ≫ f)
    (hφ : k.φ = n.φ ≫ m.φ) (θ : LB.Sec t.PP.L) (w : LB.Iso t'.PP.L (t.PP.L.pull k.φ)) (σ : LB.Sec t'.PP.L)
    (θ2 : LB.Sec (t.PP.L.pull k.φ)) (r : RigIso k w) (hi : IsoMaps w σ θ2) (hp : PullSec k.φ θ θ2) :
    ∃ (θ' : LB.Sec G.PP.L) (w' : LB.Iso t'.PP.L (G.PP.L.pull n.φ)),
      (∀ s : S', (∃ x : t.G.left, t.G.hom x = f s ∧ x ∈ Out.nonzeroLocus θ) →
        ∃ x : G.G.left, G.G.hom x = s ∧ x ∈ Out.nonzeroLocus θ') ∧
      RigIso n w' ∧ IsoMaps w' σ (thfPull G.PP.L n.φ θ') := by
  obtain ⟨w0, g0, r0, -⟩ := m.lin
  obtain ⟨θ', hθ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) t.PP.isLB G.PP.isLB θ
  have he : k.cm.e = n.cm.e ≫ m.cm.e := by rw [k.base, n.base, m.base, hb]
  obtain ⟨w', r', tri⟩ := GlobalTheory.Reg.TieIntegral.exists_rigIso_cancel m.cm n.cm k.cm hφ he t'.PP G.PP t.PP w0 w ⟨g0, r0⟩ r
  refine ⟨θ', w', ?_, r', fun (i : PUnit → G.PP.L.ι) k' => fn_ext fun y hy => ?_⟩
  · rintro s ⟨z, hz, hz'⟩
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 z s hz
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨i, hi⟩ := exists_chart G.PP.isLB y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨i, hi, ?_⟩⟩
    have u₁ : IsUnit (gs m.φ y _ (θ.f j)) := by rw [gs_stalkMap m.φ y _ hj]; exact u.map _
    have e := hθ' _ (𝟙 _) y j i hj hi
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · have hi' : n.φ y ∈ G.PP.L.U (i PUnit.unit) := mem_pull.1 hy.1
    obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (n.φ y))
    have pt : k.φ y = m.φ (n.φ y) := congrArg (fun q => q y) hφ
    have hj' : k.φ y ∈ t.PP.L.U j := pt ▸ hj
    have e1 := hθ' _ (𝟙 _ ≫ n.φ) y j (i PUnit.unit) hj hi'
    have e2 : gs (𝟙 _ ≫ k.φ) y _ (θ.f j) = (gw w (𝟙 _) y j k').val * gs (𝟙 _) y _ (σ.f k') := by
      have hz : y ∈ (t.PP.L.pull k.φ).U (fun _ => j) ⊓ t'.PP.L.U k' := ⟨mem_pull.2 hj', hy.2⟩
      have le : (t.PP.L.pull k.φ).U (fun _ => j) ≤ k.φ ⁻¹ᵁ t.PP.L.U j := fun q hq => mem_pull.1 hq
      have a := congrArg (gs (𝟙 _) y _) (hi (fun _ => j) k')
      refine (gs_appLE k.φ _ _ le (𝟙 _) y hz.1 _).symm.trans ?_
      rw [← hp (fun _ => j) le]
      exact (gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))
    have e3 := tri _ (𝟙 _) y j (i PUnit.unit) k' hj hi' hy.2
    have e4 : (𝟙 _ ≫ n.φ) ≫ m.φ = 𝟙 _ ≫ k.φ := by rw [Category.assoc, hφ]
    rw [e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at e1
    refine (gs_res _ y _ hy _).trans ((gs_appLE n.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)

end GlobalTheory.ArcQ.DiscInt

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

open DiscInt in

/- English proof (translation)
Introduce `hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W _ ρ e th hB hth hPI T io ev hinj hρ`. Use `letI := io.toAlgebra`. Introduce `y hy`. Take `⟨z, t', m1, k, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hθ, r1, r2, i1, i2, p2, hg⟩` from `hy`. Choose the witnesses or unpack the hypotheses as in `⟨G, ⟨m⟩⟩ : ∃ G : SAB H (Sp T.V), Nonempty (SABMap G W.t (spMap ev)) := by`.

Take `⟨_, _, _, _, _, m, -⟩` from `sabPull Out.CubePf.cubePull (spMap ev) W.t`. Conclude with `⟨_, ⟨m⟩⟩`. Establish `hb` using `sp_comp ev (algebraMap T.V T.Fr)`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n : SABMap t' G (spMap (algebraMap T.V T.Fr)), k.φ = n.φ ≫ m.φ := by`. Establish `key : ∀ (g : Sp T.Fr ⟶ _) (k : SABMap t' W.t g), g = spMap (algebraMap T.V T.Fr) ≫ spMap ev → ∃ n : SABMap t' G (spMap (algebraMap T.V T.Fr)), k.φ = n.φ ≫ m.φ`.

Introduce `g k hg`. Substitute `hg` using the available equality. Conclude with `sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m k`. Conclude with `key _ k hb`. Take `⟨u, hu1, hu2⟩` from `GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e hB T.V ev (flat_of_injective _ hinj) G m`.

Establish `eig : ∀ (τ : E →+* ℂ) (w : epsR T.V ⟶ G.G), IsEigV c io G τ w ↔ ∀ x : 𝓞 E, (w ≫ G.act.act x).left = spMap (epsScaleR (ev (PowerSeries.C (R` using `A) (ρ τ x)))) ≫ w.left := fun τ w => ⟨fun h x => h x _ (hρ τ x).symm, fun h x s hs => by`. Take `rfl : s = ev (PowerSeries.C (R` from `A) (ρ τ x)) := IsFractionRing.injective T.V T.Fr (hs.trans (hρ τ x))`. Conclude with `h x⟩`. Take `⟨θ', w', hnz, r', i'⟩` from `sec_cancel m n k hb hn θ w2 σ θ2 r2 i2 p2`. Use `⟨G, t', m1, n, ⟨u, fun τ i => (isTan_iff _).2 ((hu2 τ).1 i).1, fun τ i => (eig τ _).2 ((hu2 τ).1 i).2, fun τ w h1 h2 => (hu2 τ).2 w ((isTan_iff _).1 h1) ((eig τ w).1 h2), fun τ i => ?_⟩, θ', GlobalTheory.T.polarisation_section_generates_of_special_fibre hL hL2 E H Dw l Xo c T G t …` and prove the remaining obligations.

Take `⟨v, p, h1, h2, h3, pb⟩` from `hu τ i`. Take `⟨v', h1', h3'⟩` from `hu1 τ i`. Take `rfl : v = v'` from `(GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hL.globalFns E H Dw l Xo c O β Y A b a χ W (e τ i)).1.unique h1 h1'`. Use `⟨p, h2, ?_⟩` and prove the remaining obligations. Apply `m.cart.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, Category.assoc]`. Conclude with `(congrArg _ hn.symm).trans (h3.trans (by rw [dual_comp, Category.assoc]; exact congrArg _ h3'.symm))`. Establish `ub : (u τ i).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V))` using `Over.w (u τ i)`. Rewrite using `[Category.assoc, Category.assoc, n.cart.1.w, ← Category.assoc, pb]`. Conclude with `((congrArg _ ub).trans (dual_alg _)).symm`.
-/
theorem integral_of_isArcFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) [IsPrincipalIdealRing A] (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ArcBasis W ρ e → ThNZ th → PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (ev : PowerSeries A →+* T.V), Function.Injective (ev.comp (PowerSeries.C (R := A))) → (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ev (PowerSeries.C (R := A) (ρ τ x)))) → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y → Integral T io y := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W _ ρ e th hB hth hPI T io ev hinj hρ
  letI := io.toAlgebra
  intro y hy
  obtain ⟨z, t', m1, k, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hθ, r1, r2, i1, i2, p2, hg⟩ := hy
  obtain ⟨G, ⟨m⟩⟩ : ∃ G : SAB H (Sp T.V), Nonempty (SABMap G W.t (spMap ev)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ev) W.t
    exact ⟨_, ⟨m⟩⟩
  have hb := sp_comp ev (algebraMap T.V T.Fr)
  obtain ⟨n, hn⟩ : ∃ n : SABMap t' G (spMap (algebraMap T.V T.Fr)), k.φ = n.φ ≫ m.φ := by
    have key : ∀ (g : Sp T.Fr ⟶ _) (k : SABMap t' W.t g), g = spMap (algebraMap T.V T.Fr) ≫ spMap ev →
        ∃ n : SABMap t' G (spMap (algebraMap T.V T.Fr)), k.φ = n.φ ≫ m.φ := by
      intro g k hg
      subst hg
      exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m k
    exact key _ k hb
  obtain ⟨u, hu1, hu2⟩ := GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e hB T.V ev
    (flat_of_injective _ hinj) G m
  have eig : ∀ (τ : E →+* ℂ) (w : epsR T.V ⟶ G.G), IsEigV c io G τ w ↔ ∀ x : 𝓞 E, (w ≫ G.act.act x).left =
      spMap (epsScaleR (ev (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left := fun τ w =>
    ⟨fun h x => h x _ (hρ τ x).symm, fun h x s hs => by
      obtain rfl : s = ev (PowerSeries.C (R := A) (ρ τ x)) := IsFractionRing.injective T.V T.Fr (hs.trans (hρ τ x))
      exact h x⟩
  obtain ⟨θ', w', hnz, r', i'⟩ := sec_cancel m n k hb hn θ w2 σ θ2 r2 i2 p2
  refine ⟨G, t', m1, n, ⟨u, fun τ i => (isTan_iff _).2 ((hu2 τ).1 i).1, fun τ i => (eig τ _).2 ((hu2 τ).1 i).2,
    fun τ w h1 h2 => (hu2 τ).2 w ((isTan_iff _).1 h1) ((eig τ w).1 h2), fun τ i => ?_⟩, θ',
    GlobalTheory.T.polarisation_section_generates_of_special_fibre hL hL2 E H Dw l Xo c T G t' y.x m1 n θ'
      (hnz _ (GlobalTheory.T.thetaSection_of_arc_nonzero_on_fibres hL hL2 E H Dw l Xo c O β Y A b a χ W th θ hth hθ (Or.inr hPI) _).2),
    w1, w', σ, s1, thfPull G.PP.L n.φ θ', r1, r', i1, i', fun _ _ => rfl, hg⟩
  obtain ⟨v, p, h1, h2, h3, pb⟩ := hu τ i
  obtain ⟨v', h1', h3'⟩ := hu1 τ i
  obtain rfl : v = v' := (GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hL.globalFns E H Dw l Xo c O β Y A b a χ W (e τ i)).1.unique h1 h1'
  refine ⟨p, h2, ?_⟩
  apply m.cart.1.hom_ext
  · rw [Category.assoc, Category.assoc]
    exact (congrArg _ hn.symm).trans (h3.trans (by rw [dual_comp, Category.assoc]; exact congrArg _ h3'.symm))
  · have ub : (u τ i).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (u τ i)
    rw [Category.assoc, Category.assoc, n.cart.1.w, ← Category.assoc, pb]
    exact ((congrArg _ ub).trans (dual_alg _)).symm

end GlobalTheory.ArcQ
