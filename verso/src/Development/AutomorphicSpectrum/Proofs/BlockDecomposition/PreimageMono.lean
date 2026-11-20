import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftCocycleMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCechCohomologyFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverCupActionBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableCoverCechVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherian
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobSerre
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.PolyAll
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.FibGr
open GlobalTheory.CompanionTheory.ChartAlg (fromSpec_comp top_le_fromSpec eq_specMap evalAt_specMap)

section Chart
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (hI : I = ⊥) {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {γ : DividedPowers I} {p : ℕ}

/- English proof (translation)
Substitute `hI` using the available equality. Both sides reduce to the same expression.
-/
theorem bar_mk (r : R) : bar hI (Ideal.Quotient.mk I r) = r := by
  subst hI
  rfl

/- English proof (translation)
Establish `e` using `fib_fst (γ := γ) (p := p) hI T`. Unfold `InU at h`. Rewrite `h` using `[← e]`. Conclude with `h`.
-/
theorem inY_of_inU {V : X.Opens} {T : Thick (nlFun γ p X q κ)} (h : InU V T) :
    InY (fib hI q κ γ p) (jF hI q κ ⁻¹ᵁ V) T := by
  have e := fib_fst (γ := γ) (p := p) hI T
  unfold InU at h
  rw [← e] at h
  exact h

/- English proof (translation)
Establish `e : j.app V ≫ y.appLE (j ⁻¹ᵁ V) ⊤ h = (y ≫ j).appLE V ⊤ h'`. Rewrite using `[Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]`. Unfold `GlobalTheory.Cris.evalAt`. Rewrite using `[← e]`. Both sides reduce to the same expression.
-/
theorem evalAt_comp {Y' X' : Scheme.{0}} {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Y') (j : Y' ⟶ X') {V : X'.Opens}
    (h : ⊤ ≤ y ⁻¹ᵁ (j ⁻¹ᵁ V)) (h' : ⊤ ≤ (y ≫ j) ⁻¹ᵁ V) (f : Γ(X', V)) :
    GlobalTheory.Cris.evalAt (y ≫ j) V h' f = GlobalTheory.Cris.evalAt y (j ⁻¹ᵁ V) h ((j.app V).hom f) := by
  have e : j.app V ≫ y.appLE (j ⁻¹ᵁ V) ⊤ h = (y ≫ j).appLE V ⊤ h' := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  unfold GlobalTheory.Cris.evalAt
  rw [← e]
  rfl

abbrev jf (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (V : X.Opens) : Γ(X, V) →+* Γ(XF hI q κ, jF hI q κ ⁻¹ᵁ V) :=
  ((jF hI q κ).app V).hom

/- English proof (translation)
Establish `key : ∀ (y : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ X) (hy : (fib hI q κ γ p).pt T ≫ jF hI q κ = y) (hh : ⊤ ≤ y ⁻¹ᵁ V), GlobalTheory.Cris.evalAt y V hh f = ev (fib hI q κ γ p) T (inY_of_inU hI h) (jf hI q κ V f)`. Introduce `y hy hh`. Substitute `hy` using the available equality. Conclude with `evalAt_comp _ _ _ _ f`. Conclude with `(key _ (fib_fst hI T) h).symm`.
-/
theorem ev_jf {V : X.Opens} (T : Thick (nlFun γ p X q κ)) (h : InU V T) (f : Γ(X, V)) :
    ev (fib hI q κ γ p) T (inY_of_inU hI h) (jf hI q κ V f) = CrystallineSemistableComparison.Pb.ev T h f := by
  have key : ∀ (y : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ X) (hy : (fib hI q κ γ p).pt T ≫ jF hI q κ = y) (hh : ⊤ ≤ y ⁻¹ᵁ V),
      GlobalTheory.Cris.evalAt y V hh f = ev (fib hI q κ γ p) T (inY_of_inU hI h) (jf hI q κ V f) := by
    intro y hy hh
    subst hy
    exact evalAt_comp _ _ _ _ f
  exact (key _ (fib_fst hI T) h).symm

/- English proof (translation)
Establish `: IsAffineHom (jF hI q κ)` using `MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance`. Conclude with `hV.preimage _`.
-/
theorem aff_pre {V : X.Opens} (hV : IsAffineOpen V) : IsAffineOpen (jF hI q κ ⁻¹ᵁ V) := by
  have : IsAffineHom (jF hI q κ) := MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  exact hV.preimage _

/- English proof (translation)
Establish `hW` using `aff_pre (q := q) (κ := κ) hI hV`. Set `qY` to `qF hI q κ`. Set `j` to `jF hI q κ`. Set `W` to `j ⁻¹ᵁ V`. Set `ψ : R ⧸ I →+* Γ(XF hI q κ, W)` to `(strV qY W).comp (bar hI).toRingHom`.

Establish `hy2 : (hW.fromSpec ≫ j) ≫ q = Spec.map (CommRingCat.ofHom (ψ.comp κ))`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, fromSpec_comp, ← Spec.map_comp]`. Both sides reduce to the same expression. Set `y : PtOver X q κ Γ(XF hI q κ, W)` to `⟨(ψ, hW.fromSpec ≫ j), hy2⟩`. Establish `hyV : ⊤ ≤ y.1.2 ⁻¹ᵁ V` using `top_le_fromSpec hW`.

Take `⟨φ, hφ, -⟩` from `c.rep Γ(XF hI q κ, W) y hyV`. Use `set e := ev (fib hI q κ γ p) c.D (inY_of_inU hI c.inV) with he`. Establish `c1 : Spec.map (CommRingCat.ofHom e) ≫ hW.fromSpec = (fib hI q κ γ p).pt c.D` using `eq_specMap hW _ (inY_of_inU hI c.inV)`. Establish `hφ1 : φ.comp (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 = ψ` using `congrArg (fun z => z.1.1) hφ`. Establish `hφ2 : Spec.map (CommRingCat.ofHom φ) ≫ pt c.D = hW.fromSpec ≫ j` using `congrArg (fun z => z.1.2) hφ`.

Establish `hA : e.comp φ = RingHom.id _`. Take `⟨φ₀, -, hu⟩` from `c.rep (CommRingCat.of (c.D.B ⧸ c.D.J)) c.D.y c.inV`. Establish `h1 : (ptFun X q κ).map (CommRingCat.ofHom (e.comp φ)) c.D.y = c.D.y`. Use `Subtype.ext (Prod.ext ?_ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(e.comp φ).comp (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 = _`.

Rewrite using `[RingHom.comp_assoc, hφ1]`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Establish `e1 : e (strV qY W (bar hI x)) = Ideal.Quotient.mk c.D.J (c.D.i (bar hI x))` using `ev_str _ _ _ _`. Establish `e2` using `c.D.w (bar hI x)`. Rewrite `e2` using `[mk_bar]`.

Conclude with `e1.trans e2.symm`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (e.comp φ)) ≫ pt c.D = pt c.D`. Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφ2, ← Category.assoc, c1]`. Conclude with `fib_fst hI c.D`. Establish `h2 : (ptFun X q κ).map (CommRingCat.ofHom (RingHom.id _)) c.D.y = c.D.y`.

Use `Subtype.ext (Prod.ext (RingHom.ext fun _ => rfl) ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ pt c.D = pt c.D`. Rewrite using `[CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]`. Conclude with `(hu _ h1).trans (hu _ h2).symm`. Establish `hB : φ.comp e = RingHom.id _`.

Establish `hm : φ.comp ((Ideal.Quotient.mk c.D.J).comp c.D.i) = strV qY W`. Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Establish `e2` using `c.D.w r`. Establish `e3` using `RingHom.congr_fun hφ1 (Ideal.Quotient.mk I r)`. Express the relevant statement in the definitionally equal form `φ (Ideal.Quotient.mk c.D.J (c.D.i r)) = _`.

Rewrite using `[← e2]`. Use `e3.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `strV qY W (bar hI _) = _`. Rewrite using `[bar_mk]`. Establish `key : Spec.map (CommRingCat.ofHom (φ.comp e)) ≫ hW.fromSpec = hW.fromSpec`.

Rewrite using `[CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, c1]`. Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, fib_fst]`. Conclude with `hφ2`. Rewrite using `[Category.assoc, (fib hI q κ γ p).str, ← Spec.map_comp, fromSpec_comp, ← CommRingCat.ofHom_comp, hm]`.

Establish `k2 : hW.fromSpec = Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ hW.fromSpec`. Rewrite using `[CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]`. Conclude with `(evalAt_specMap hW (φ.comp e) hW.fromSpec key.symm (top_le_fromSpec hW)).symm.trans (evalAt_specMap hW (RingHom.id _) hW.fromSpec k2 (top_le_fromSpec hW))`. Conclude with `Function.bijective_iff_has_inverse.2 ⟨φ, fun x => RingHom.congr_fun hB x, fun x => RingHom.congr_fun hA x⟩`.
-/
theorem ev_bij {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (hV : IsAffineOpen V) :
    Function.Bijective (ev (fib hI q κ γ p) c.D (inY_of_inU hI c.inV)) := by
  have hW := aff_pre (q := q) (κ := κ) hI hV
  let qY := qF hI q κ
  let j := jF hI q κ
  let W := j ⁻¹ᵁ V
  let ψ : R ⧸ I →+* Γ(XF hI q κ, W) := (strV qY W).comp (bar hI).toRingHom
  have hy2 : (hW.fromSpec ≫ j) ≫ q = Spec.map (CommRingCat.ofHom (ψ.comp κ)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, fromSpec_comp, ← Spec.map_comp]
    rfl
  let y : PtOver X q κ Γ(XF hI q κ, W) := ⟨(ψ, hW.fromSpec ≫ j), hy2⟩
  have hyV : ⊤ ≤ y.1.2 ⁻¹ᵁ V := top_le_fromSpec hW
  obtain ⟨φ, hφ, -⟩ := c.rep Γ(XF hI q κ, W) y hyV
  set e := ev (fib hI q κ γ p) c.D (inY_of_inU hI c.inV) with he
  have c1 : Spec.map (CommRingCat.ofHom e) ≫ hW.fromSpec = (fib hI q κ γ p).pt c.D :=
    eq_specMap hW _ (inY_of_inU hI c.inV)
  have hφ1 : φ.comp (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 = ψ := congrArg (fun z => z.1.1) hφ
  have hφ2 : Spec.map (CommRingCat.ofHom φ) ≫ pt c.D = hW.fromSpec ≫ j := congrArg (fun z => z.1.2) hφ

  have hA : e.comp φ = RingHom.id _ := by
    obtain ⟨φ₀, -, hu⟩ := c.rep (CommRingCat.of (c.D.B ⧸ c.D.J)) c.D.y c.inV
    have h1 : (ptFun X q κ).map (CommRingCat.ofHom (e.comp φ)) c.D.y = c.D.y := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · change (e.comp φ).comp (show PtOver X q κ (c.D.B ⧸ c.D.J) from c.D.y).1.1 = _
        rw [RingHom.comp_assoc, hφ1]
        refine RingHom.ext fun x => ?_
        have e1 : e (strV qY W (bar hI x)) = Ideal.Quotient.mk c.D.J (c.D.i (bar hI x)) := ev_str _ _ _ _
        have e2 := c.D.w (bar hI x)
        rw [mk_bar] at e2
        exact e1.trans e2.symm
      · change Spec.map (CommRingCat.ofHom (e.comp φ)) ≫ pt c.D = pt c.D
        rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφ2, ← Category.assoc, c1]
        exact fib_fst hI c.D
    have h2 : (ptFun X q κ).map (CommRingCat.ofHom (RingHom.id _)) c.D.y = c.D.y := by
      refine Subtype.ext (Prod.ext (RingHom.ext fun _ => rfl) ?_)
      change Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ pt c.D = pt c.D
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    exact (hu _ h1).trans (hu _ h2).symm
  have hB : φ.comp e = RingHom.id _ := by
    have hm : φ.comp ((Ideal.Quotient.mk c.D.J).comp c.D.i) = strV qY W := by
      refine RingHom.ext fun r => ?_
      have e2 := c.D.w r
      have e3 := RingHom.congr_fun hφ1 (Ideal.Quotient.mk I r)
      change φ (Ideal.Quotient.mk c.D.J (c.D.i r)) = _
      rw [← e2]
      refine e3.trans ?_
      change strV qY W (bar hI _) = _
      rw [bar_mk]
    have key : Spec.map (CommRingCat.ofHom (φ.comp e)) ≫ hW.fromSpec = hW.fromSpec := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, c1]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, fib_fst]
        exact hφ2
      · rw [Category.assoc, (fib hI q κ γ p).str, ← Spec.map_comp, fromSpec_comp, ← CommRingCat.ofHom_comp, hm]
    have k2 : hW.fromSpec = Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ hW.fromSpec := by
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    exact (evalAt_specMap hW (φ.comp e) hW.fromSpec key.symm (top_le_fromSpec hW)).symm.trans
      (evalAt_specMap hW (RingHom.id _) hW.fromSpec k2 (top_le_fromSpec hW))
  exact Function.bijective_iff_has_inverse.2 ⟨φ, fun x => RingHom.congr_fun hB x, fun x => RingHom.congr_fun hA x⟩

end Chart

section Geo
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (hI : I = ⊥) {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (γ : DividedPowers I) (p : ℕ)

abbrev SQ (W : X.Opens) : ObjectProperty (Thick (nlFun γ p X q κ)) := St ⊤ {W}

variable {q κ γ p}

/- English proof (translation)
Take `⟨-, V, hV, hT⟩` from `h`. Rewrite `hT` using `[Set.mem_singleton_iff.1 hV]`. Then use the resulting hypothesis.
-/
theorem sq_inU {W : X.Opens} {T : Thick (nlFun γ p X q κ)} (h : SQ q κ γ p W T) : InU W T := by
  obtain ⟨-, V, hV, hT⟩ := h
  rwa [Set.mem_singleton_iff.1 hV] at hT

/- English proof (translation)
The claim follows from `inY_of_inU hI (sq_inU h)`.
-/
theorem sq_inY {W : X.Opens} (T : Thick (nlFun γ p X q κ)) (h : SQ q κ γ p W T) :
    InY (fib hI q κ γ p) (jF hI q κ ⁻¹ᵁ W) T := inY_of_inU hI (sq_inU h)

/- English proof (translation)
Take `⟨c', -, hct⟩` from `GlobalTheory.CompanionTheory.ChartP.exists_chart γ p hp hn q κ c`. Establish `good` using `GlobalTheory.CompanionTheory.ChartMaps.good c'`. Establish `hQ : ∀ T, SQ q κ γ p W T → InU W T` using `fun T h => sq_inU h`. Establish `hD : SQ q κ γ p W c'.D` using `⟨trivial, W, rfl, c'.inV⟩`. Take `⟨-, hgr⟩` from `GlobalTheory.CompanionTheory.ChartFil.chart_grConst c' good (SQ q κ γ p W) hQ hD`.

Establish `hJ : c'.D.J = ⊥` using `c'.J_eq.trans ((Ideal.map_eq_bot_iff_le_ker _).2 (hI.le.trans bot_le))`. Establish `hDY` using `inY_of_inU (γ := γ) (p := p) (q := q) (κ := κ) hI c'.inV`. Set `θ₀ : Γ(XF hI q κ, jF hI q κ ⁻¹ᵁ W) ≃+* c'.D.B ⧸ c'.D.J` to `RingEquiv.ofBijective _ (ev_bij hI c' c.affine)`. Set `θ : Γ(XF hI q κ, jF hI q κ ⁻¹ᵁ W) ≃+* c'.D.B` to `θ₀.trans (bar hJ)`. Establish `mkθ : ∀ f, Ideal.Quotient.mk c'.D.J (θ f) = ev (fib hI q κ γ p) c'.D hDY f` using `fun f => mk_bar hJ _`.

Establish `hval : ∀ (T : Thick (nlFun γ p X q κ)) (h : InY (fib hI q κ γ p) (jF hI q κ ⁻¹ᵁ W) T) (σ : c'.D ⟶ T) (f), Ideal.Quotient.mk T.J (σ.φ (θ f)) = ev (fib hI q κ γ p) T h f`. Introduce `T h σ f`. Rewrite using `[ev_nat _ σ hDY h f, ← mkθ f]`. Both sides reduce to the same expression. Establish `het : ∀ i, θ (jf hI q κ W (c.t i)) = c'.t i`.

Introduce `i`. Establish `h1 : Ideal.Quotient.mk c'.D.J (θ (jf hI q κ W (c.t i))) = Ideal.Quotient.mk c'.D.J (c'.t i)`. Rewrite using `[mkθ, ev_jf hI c'.D c'.inV (c.t i), hct]`. Establish `h2` using `Ideal.Quotient.eq.1 h1`. Rewrite `h2` using `[hJ]`.

Conclude with `sub_eq_zero.1 (Ideal.mem_bot.1 h2)`. Establish `hσ : ∀ T : (SQ q κ γ p W).FullSubcategory, ∃ σ : c'.D ⟶ T.obj, ∀ i, σ.φ (c'.t i) = u i T.obj`. Introduce `T`. Establish `hT` using `hQ _ T.property`. Establish `hTY` using `inY_of_inU (γ := γ) (p := p) (q := q) (κ := κ) hI hT`.

Take `⟨σ₀⟩` from `good.1 T.obj hT`. Take `⟨σ, h1, -⟩` from `good.2 T.obj σ₀ (fun i => u i T.obj - σ₀.φ (c'.t i)) (fun i => by`. Use `Ideal.Quotient.eq.1 ?_` and prove the remaining obligations. Rewrite using `[hu i T.obj hTY, ← het i, hval T.obj hTY σ₀])`. Conclude with `⟨σ, fun i => by simpa using h1 i⟩`.

Use `choose σ hσ using hσ`. Use `⟨c'.frame good (SQ q κ γ p W) hQ hD, fun T => ObjectProperty.homMk (σ T), θ, hgr, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `((GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SQ q κ γ p W)).one _).trans hJ`. Introduce `i T s s'`. Express the relevant statement in the definitionally equal form `(s'.hom.φ (c'.t i) - s.hom.φ (c'.t i) : T.obj.B) = s'.hom.φ (θ _) - s.hom.φ (θ _)`.

Rewrite using `[het]`. Introduce `i T`. Express the relevant statement in the definitionally equal form `(σ T).φ (θ _) = u i T.obj`. Rewrite using `[het, hσ]`. Introduce `T h f`.

Conclude with `hval T.obj h (σ T) f`.
-/
theorem frame_at (hp : p ≠ 0) (hn : IsNilpotent (p : R)) {W : X.Opens} {d : ℕ} (c : Coord q W d)
    (u : Fin d → ∀ T : Thick (nlFun γ p X q κ), T.B)
    (hu : IsLift (fib hI q κ γ p) (jF hI q κ ⁻¹ᵁ W) (fun i => jf hI q κ W (c.t i)) u) :
    ∃ (E : Frame (sP (SQ q κ γ p W)) d) (σ : ∀ T, E.D ⟶ T)
      (θ : Γ(XF hI q κ, jF hI q κ ⁻¹ᵁ W) ≃+* (sP (SQ q κ γ p W)).A.obj E.D),
      E.GrConst (sFil (SQ q κ γ p W)) ∧ (sFil (SQ q κ γ p W) 1).S E.D = ⊥ ∧
      (E.Coords fun i => θ (jf hI q κ W (c.t i))) ∧
      (∀ i T, ((sP (SQ q κ γ p W)).A.map (σ T)).hom (θ (jf hI q κ W (c.t i))) = u i T.obj) ∧
      ∀ (T : (SQ q κ γ p W).FullSubcategory) (h : InY (fib hI q κ γ p) (jF hI q κ ⁻¹ᵁ W) T.obj)
        (f : Γ(XF hI q κ, jF hI q κ ⁻¹ᵁ W)),
        Ideal.Quotient.mk T.obj.J (show T.obj.B from ((sP (SQ q κ γ p W)).A.map (σ T)).hom (θ f)) =
          ev (fib hI q κ γ p) T.obj h f := by
  obtain ⟨c', -, hct⟩ := GlobalTheory.CompanionTheory.ChartP.exists_chart γ p hp hn q κ c
  have good := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hQ : ∀ T, SQ q κ γ p W T → InU W T := fun T h => sq_inU h
  have hD : SQ q κ γ p W c'.D := ⟨trivial, W, rfl, c'.inV⟩
  obtain ⟨-, hgr⟩ := GlobalTheory.CompanionTheory.ChartFil.chart_grConst c' good (SQ q κ γ p W) hQ hD
  have hJ : c'.D.J = ⊥ := c'.J_eq.trans ((Ideal.map_eq_bot_iff_le_ker _).2 (hI.le.trans bot_le))
  have hDY := inY_of_inU (γ := γ) (p := p) (q := q) (κ := κ) hI c'.inV
  let θ₀ : Γ(XF hI q κ, jF hI q κ ⁻¹ᵁ W) ≃+* c'.D.B ⧸ c'.D.J := RingEquiv.ofBijective _ (ev_bij hI c' c.affine)
  let θ : Γ(XF hI q κ, jF hI q κ ⁻¹ᵁ W) ≃+* c'.D.B := θ₀.trans (bar hJ)
  have mkθ : ∀ f, Ideal.Quotient.mk c'.D.J (θ f) = ev (fib hI q κ γ p) c'.D hDY f := fun f => mk_bar hJ _
  have hval : ∀ (T : Thick (nlFun γ p X q κ)) (h : InY (fib hI q κ γ p) (jF hI q κ ⁻¹ᵁ W) T) (σ : c'.D ⟶ T) (f),
      Ideal.Quotient.mk T.J (σ.φ (θ f)) = ev (fib hI q κ γ p) T h f := by
    intro T h σ f
    rw [ev_nat _ σ hDY h f, ← mkθ f]
    rfl
  have het : ∀ i, θ (jf hI q κ W (c.t i)) = c'.t i := by
    intro i
    have h1 : Ideal.Quotient.mk c'.D.J (θ (jf hI q κ W (c.t i))) = Ideal.Quotient.mk c'.D.J (c'.t i) := by
      rw [mkθ, ev_jf hI c'.D c'.inV (c.t i), hct]
    have h2 := Ideal.Quotient.eq.1 h1
    rw [hJ] at h2
    exact sub_eq_zero.1 (Ideal.mem_bot.1 h2)
  have hσ : ∀ T : (SQ q κ γ p W).FullSubcategory, ∃ σ : c'.D ⟶ T.obj, ∀ i, σ.φ (c'.t i) = u i T.obj := by
    intro T
    have hT := hQ _ T.property
    have hTY := inY_of_inU (γ := γ) (p := p) (q := q) (κ := κ) hI hT
    obtain ⟨σ₀⟩ := good.1 T.obj hT
    obtain ⟨σ, h1, -⟩ := good.2 T.obj σ₀ (fun i => u i T.obj - σ₀.φ (c'.t i)) (fun i => by
      refine Ideal.Quotient.eq.1 ?_
      rw [hu i T.obj hTY, ← het i, hval T.obj hTY σ₀])
    exact ⟨σ, fun i => by simpa using h1 i⟩
  choose σ hσ using hσ
  refine ⟨c'.frame good (SQ q κ γ p W) hQ hD, fun T => ObjectProperty.homMk (σ T), θ, hgr, ?_, ?_, ?_, ?_⟩
  · exact ((GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SQ q κ γ p W)).one _).trans hJ
  · intro i T s s'
    change (s'.hom.φ (c'.t i) - s.hom.φ (c'.t i) : T.obj.B) = s'.hom.φ (θ _) - s.hom.φ (θ _)
    rw [het]
  · intro i T
    change (σ T).φ (θ _) = u i T.obj
    rw [het, hσ]
  · intro T h f
    exact hval T.obj h (σ T) f

/- English proof (translation)
Introduce `_ hx` and use `h hx`.
-/
theorem preimage_mono' {V W : X.Opens} (h : W ≤ V) : jF hI q κ ⁻¹ᵁ W ≤ jF hI q κ ⁻¹ᵁ V := fun _ hx => h hx

/- English proof (translation)
Use `congrArg (fun t => t.hom f) ((jF hI q κ).naturality (homOfLE h).op)` as an intermediate fact. Conclude with `this`.
-/
theorem jf_rs {V W : X.Opens} (h : W ≤ V) (f : Γ(X, V)) :
    jf hI q κ W (rs h f) = rs (preimage_mono' hI h) (jf hI q κ V f) := by
  have := congrArg (fun t => t.hom f) ((jF hI q κ).naturality (homOfLE h).op)
  exact this

/- English proof (translation)
Take `⟨c', hc'⟩` from `GlobalTheory.T.coordinates_restrict_affine_open c h hW`. Establish `hu' : IsLift (fib hI q κ γ p) (jF hI q κ ⁻¹ᵁ W) (fun i => jf hI q κ W (c'.t i)) u` using `isLift_res _ (preimage_mono' hI h) hu fun i => by rw [hc', jf_rs]`. Take `⟨E, σ, θ, hGr, hbot, hco, hσ, hpt⟩` from `frame_at hI hp hn c' u hu'`. Take `⟨Qp, hQp⟩` from `CrystallineSemistableComparison.Pb.Site.poly_all' γ p hp q κ ⊤ (Or.inl rfl) {W}`. Conclude with `free_of_frame _ GlobalTheory.CompanionTheory.LocGrStep.loc_gr (fun T => sq_inY hI _ T.property) u _ E σ θ hGr hbot hco hσ hpt Qp r (fun r' _ => (hQp r').1)`.
-/
theorem free_at (hp : p ≠ 0) (hn : IsNilpotent (p : R)) {V W : X.Opens} (h : W ≤ V) (hW : IsAffineOpen W) {d : ℕ}
    (c : Coord q V d) {u : Fin d → ∀ T : Thick (nlFun γ p X q κ), T.B}
    (hu : IsLift (fib hI q κ γ p) (jF hI q κ ⁻¹ᵁ V) (fun i => jf hI q κ V (c.t i)) u) (r : ℕ) :
    Free (fib hI q κ γ p) (jF hI q κ ⁻¹ᵁ W) (SQ q κ γ p W) r u := by
  obtain ⟨c', hc'⟩ := GlobalTheory.T.coordinates_restrict_affine_open c h hW
  have hu' : IsLift (fib hI q κ γ p) (jF hI q κ ⁻¹ᵁ W) (fun i => jf hI q κ W (c'.t i)) u :=
    isLift_res _ (preimage_mono' hI h) hu fun i => by rw [hc', jf_rs]
  obtain ⟨E, σ, θ, hGr, hbot, hco, hσ, hpt⟩ := frame_at hI hp hn c' u hu'
  obtain ⟨Qp, hQp⟩ := CrystallineSemistableComparison.Pb.Site.poly_all' γ p hp q κ ⊤ (Or.inl rfl) {W}
  exact free_of_frame _ GlobalTheory.CompanionTheory.LocGrStep.loc_gr (fun T => sq_inY hI _ T.property) u _ E σ θ hGr hbot hco hσ hpt Qp r
    (fun r' _ => (hQp r').1)

include hI in

/- English proof (translation)
Take `⟨E, σ, θ, hGr, hbot, -⟩` from `frame_at (γ := γ) (p := p) (κ := κ) hI hp hn c (fun k T => lft (fib hI q κ γ p) _ T (jf hI q κ W (c.t k))) (fun k T h => lft_spec _ T h _)`. Take `⟨Qp, hQp⟩` from `CrystallineSemistableComparison.Pb.Site.poly_all' γ p hp q κ ⊤ (Or.inl rfl) {W}`. Conclude with `off_zero GlobalTheory.CompanionTheory.LocGrStep.loc_gr E σ hGr hbot Qp r j (fun r' _ => (hQp r').1) hj`.
-/
theorem off_at (hp : p ≠ 0) (hn : IsNilpotent (p : R)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (r j : ℕ) (hj : j ≠ r) :
    Subsingleton (HU (GF (nlFun γ p X q κ) r) (SQ q κ γ p W) j) := by
  obtain ⟨E, σ, θ, hGr, hbot, -⟩ := frame_at (γ := γ) (p := p) (κ := κ) hI hp hn c
    (fun k T => lft (fib hI q κ γ p) _ T (jf hI q κ W (c.t k))) (fun k T h => lft_spec _ T h _)
  obtain ⟨Qp, hQp⟩ := CrystallineSemistableComparison.Pb.Site.poly_all' γ p hp q κ ⊤ (Or.inl rfl) {W}
  exact off_zero GlobalTheory.CompanionTheory.LocGrStep.loc_gr E σ hGr hbot Qp r j (fun r' _ => (hQp r').1) hj

end Geo

section Vb
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (hI : I = ⊥) {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {γ : DividedPowers I} {p : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h a`. Conclude with `(iInf_le V a) h`. Introduce `h`. Establish `ho : IsOpen (⋂ a, (V a : Set Z))` using `isOpen_iInter_of_finite fun a => (V a).isOpen`.

Establish `hle : (⟨_, ho⟩ : Z.Opens) ≤ ⨅ a, V a` using `le_iInf fun a y hy => Set.mem_iInter.1 hy a`. Conclude with `hle (Set.mem_iInter.2 h)`.
-/
theorem mem_iInf_fin {Z : Scheme.{0}} {n : ℕ} (V : Fin n → Z.Opens) (x : Z) : x ∈ ⨅ a, V a ↔ ∀ a, x ∈ V a := by
  constructor
  · intro h a
    exact (iInf_le V a) h
  · intro h
    have ho : IsOpen (⋂ a, (V a : Set Z)) := isOpen_iInter_of_finite fun a => (V a).isOpen
    have hle : (⟨_, ho⟩ : Z.Opens) ≤ ⨅ a, V a := le_iInf fun a y hy => Set.mem_iInter.1 hy a
    exact hle (Set.mem_iInter.2 h)

/- English proof (translation)
Use `TopologicalSpace.Opens.ext (Set.ext fun x => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x ∈ ⨅ a, jF hI q κ ⁻¹ᵁ U (i a) ↔ (jF hI q κ) x ∈ ⨅ a, U (i a)`. Rewrite using `[mem_iInf_fin, mem_iInf_fin]`. Both sides reduce to the same expression.
-/
theorem capO_pre {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) :
    capO (fun α => jF hI q κ ⁻¹ᵁ U α) i = jF hI q κ ⁻¹ᵁ capO U i := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  change x ∈ ⨅ a, jF hI q κ ⁻¹ᵁ U (i a) ↔ (jF hI q κ) x ∈ ⨅ a, U (i a)
  rw [mem_iInf_fin, mem_iInf_fin]
  rfl

/- English proof (translation)
Establish `isF : ∀ Q : ObjectProperty (Thick (nlFun γ p X q κ)), IsFil (sP Q) (sFil Q)` using `fun Q => GlobalTheory.CompanionTheory.DPFil.isFil_sFil Q`. Set `𝔭` to `fib hI q κ γ p`. Set `U' : U.ι → (XF hI q κ).Opens` to `fun α => jF hI q κ ⁻¹ᵁ U.U α`. Set `tt : ∀ α, Fin (U.d α) → Γ(XF hI q κ, U' α)` to `fun α k => jf hI q κ (U.U α) ((U.c α).t k)`. Use `choose ω hω using fun α => basis_gen 𝔭 (tt α) (SQ q κ γ p (U.U α)) (fun T h => sq_inY hI T h) r`.

Establish `hT : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (T : Thick (nlFun γ p X q κ)), capT (fun α => SQ q κ γ p (U.U α)) i T → InY 𝔭 (capO U' i) T`. Introduce `n i T h`. Rewrite `h` using `[GlobalTheory.CompanionTheory.GrCech.capT_eq]`. Rewrite using `[capO_pre]`. Conclude with `sq_inY hI T h`.

Establish `hle : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (a : Fin (n + 1)), capT (fun α => SQ q κ γ p (U.U α)) i ≤ SQ q κ γ p (U.U (i a))` using `fun i a T h => h a`. Establish `hu : ∀ α, IsLift 𝔭 (U' α) (tt α) (fun k T => lft 𝔭 (U' α) T (tt α k))` using `fun α k T h => lft_spec 𝔭 T h _`. Establish `hfreeT : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (a : Fin (n + 1)), Free 𝔭 (capO U' i) (capT (fun α => SQ q κ γ p (U.U α)) i) r (fun k T => lft 𝔭 (U' (i a)) T (tt (i a) k))`. Introduce `n i a`. Rewrite using `[GlobalTheory.CompanionTheory.GrCech.capT_eq, capO_pre]`.

Conclude with `free_at hI hp hn (capO_le U.U i a) (GlobalTheory.CompanionTheory.GrCech.capO_affine U n i) (U.c (i a)) (hu (i a)) r`. Establish `hpair : ∀ α β, IsAffineOpen (U.U α ⊓ U.U β)`. Introduce `α β`. Establish `h` using `U.inter {α, β} ⟨α, by simp⟩`. Establish `e : (⨅ γ ∈ ({α, β} : Finset U.ι), U.U γ) = U.U α ⊓ U.U β`.

Rewrite using `[Finset.iInf_insert, Finset.iInf_singleton]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `hl2 : ∀ {V W : X.Opens} (h : V ≤ W), SQ q κ γ p V ≤ SQ q κ γ p W`. Introduce and unpack `V W h T ⟨hq, V', hV, hT⟩`. Rewrite `hT` using `[Set.mem_singleton_iff.1 hV]`.

Conclude with `⟨hq, W, rfl, GlobalTheory.CompanionTheory.GrCech.inU_mono h hT⟩`. Establish `hq2 : ∀ α β (T), SQ q κ γ p (U.U α ⊓ U.U β) T → InY 𝔭 (U' α ⊓ U' β) T` using `fun α β T h => sq_inY hI T h`. Establish `hfreeP : ∀ α β, Free 𝔭 (U' α ⊓ U' β) (SQ q κ γ p (U.U α ⊓ U.U β)) r (fun k T => lft 𝔭 (U' α) T (tt α k))` using `fun α β => free_at hI hp hn inf_le_left (hpair α β) (U.c α) (hu α) r`. Establish `hg0` using `fun α β (k' : Idx r (U.d β)) => (hω α (U' α ⊓ U' β) inf_le_left (SQ q κ γ p (U.U α ⊓ U.U β)) (hl2 inf_le_left) (isF _) (hq2 α β) (hfreeP α β) ((resU _ (hl2 inf_le_right)).pull r (ω β k'))).exists`. Use `choose g' hg' using hg0`.

Use `GlobalTheory.CompanionTheory.CechVB.vb_basis (fun W => strV (qF hI q κ) W) _ U' _ r (fun α => Idx r (U.d α)) (fun i => fHom 𝔭 (isF _) (hT i) r) (fun i a k => (resU _ (hle i a)).pull r (ω (i a) k)) (fun α β k k' => g' α β k' k) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `n i a h`. Conclude with `hω (i a) (capO U' i) (capO_le U' i a) _ (hle i a) (isF _) (hT i) (hfreeT i a) h`. Introduce `n i c h`. Conclude with `fAct_str 𝔭 (isF _) (hT i) r c h`.

Introduce `n i j f h`. Conclude with `res_fAct 𝔭 (isF _) (hT _) r (isF _) (hT i) (capO_comp U' i j.succAbove) _ f h`. Introduce `n i j a k`. Conclude with `GlobalTheory.CompanionTheory.GrCech.res_res _ _ _ r _`. Introduce `n i a a' k'`.

Establish `hle2 : capT (fun α => SQ q κ γ p (U.U α)) i ≤ SQ q κ γ p (U.U (i a) ⊓ U.U (i a'))`. Introduce `T h`. Conclude with `⟨(h a).1, _, rfl, le_preimage_inf (pt T) (sq_inU (hle i a T h)) (sq_inU (hle i a' T h))⟩`. Establish `h1` using `congrArg ((resU _ hle2).pull r) (hg' (i a) (i a') k')`. Rewrite `h1` using `[GlobalTheory.CompanionTheory.GrCech.res_res, map_sum]`.

Use `h1.trans (Finset.sum_congr rfl fun k _ => ?_)` and prove the remaining obligations. Use `(res_fAct 𝔭 (isF _) (hq2 _ _) r (isF _) (hT i) (le_inf (capO_le U' i a) (capO_le U' i a')) hle2 _ _).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `fAct _ _ _ r _ _ = fAct _ _ _ r _ _`. Rewrite using `[GlobalTheory.CompanionTheory.GrCech.res_res]`.
-/
theorem vb_cech (hp : p ≠ 0) (hn : IsNilpotent (p : R)) (U : Cov q) (r : ℕ) :
    Nonempty (VB (fun W : (XF hI q κ).Opens => strV (qF hI q κ) W) (fun α => jF hI q κ ⁻¹ᵁ U.U α)
      (CrystallineSemistableComparison.Pb.cechH (GF (nlFun γ p X q κ) r) (fun α => SQ q κ γ p (U.U α)) r)) := by
  classical
  have isF : ∀ Q : ObjectProperty (Thick (nlFun γ p X q κ)), IsFil (sP Q) (sFil Q) :=
    fun Q => GlobalTheory.CompanionTheory.DPFil.isFil_sFil Q
  let 𝔭 := fib hI q κ γ p
  let U' : U.ι → (XF hI q κ).Opens := fun α => jF hI q κ ⁻¹ᵁ U.U α
  let tt : ∀ α, Fin (U.d α) → Γ(XF hI q κ, U' α) := fun α k => jf hI q κ (U.U α) ((U.c α).t k)
  choose ω hω using fun α => basis_gen 𝔭 (tt α) (SQ q κ γ p (U.U α)) (fun T h => sq_inY hI T h) r
  have hT : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (T : Thick (nlFun γ p X q κ)),
      capT (fun α => SQ q κ γ p (U.U α)) i T → InY 𝔭 (capO U' i) T := by
    intro n i T h
    rw [GlobalTheory.CompanionTheory.GrCech.capT_eq] at h
    rw [capO_pre]
    exact sq_inY hI T h
  have hle : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (a : Fin (n + 1)),
      capT (fun α => SQ q κ γ p (U.U α)) i ≤ SQ q κ γ p (U.U (i a)) := fun i a T h => h a
  have hu : ∀ α, IsLift 𝔭 (U' α) (tt α) (fun k T => lft 𝔭 (U' α) T (tt α k)) := fun α k T h => lft_spec 𝔭 T h _
  have hfreeT : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (a : Fin (n + 1)),
      Free 𝔭 (capO U' i) (capT (fun α => SQ q κ γ p (U.U α)) i) r (fun k T => lft 𝔭 (U' (i a)) T (tt (i a) k)) := by
    intro n i a
    rw [GlobalTheory.CompanionTheory.GrCech.capT_eq, capO_pre]
    exact free_at hI hp hn (capO_le U.U i a) (GlobalTheory.CompanionTheory.GrCech.capO_affine U n i) (U.c (i a)) (hu (i a)) r
  have hpair : ∀ α β, IsAffineOpen (U.U α ⊓ U.U β) := by
    intro α β
    have h := U.inter {α, β} ⟨α, by simp⟩
    have e : (⨅ γ ∈ ({α, β} : Finset U.ι), U.U γ) = U.U α ⊓ U.U β := by
      rw [Finset.iInf_insert, Finset.iInf_singleton]
    rwa [e] at h
  have hl2 : ∀ {V W : X.Opens} (h : V ≤ W), SQ q κ γ p V ≤ SQ q κ γ p W := by
    rintro V W h T ⟨hq, V', hV, hT⟩
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact ⟨hq, W, rfl, GlobalTheory.CompanionTheory.GrCech.inU_mono h hT⟩
  have hq2 : ∀ α β (T), SQ q κ γ p (U.U α ⊓ U.U β) T → InY 𝔭 (U' α ⊓ U' β) T := fun α β T h => sq_inY hI T h
  have hfreeP : ∀ α β, Free 𝔭 (U' α ⊓ U' β) (SQ q κ γ p (U.U α ⊓ U.U β)) r (fun k T => lft 𝔭 (U' α) T (tt α k)) :=
    fun α β => free_at hI hp hn inf_le_left (hpair α β) (U.c α) (hu α) r
  have hg0 := fun α β (k' : Idx r (U.d β)) => (hω α (U' α ⊓ U' β) inf_le_left (SQ q κ γ p (U.U α ⊓ U.U β)) (hl2 inf_le_left) (isF _)
    (hq2 α β) (hfreeP α β) ((resU _ (hl2 inf_le_right)).pull r (ω β k'))).exists
  choose g' hg' using hg0
  refine GlobalTheory.CompanionTheory.CechVB.vb_basis (fun W => strV (qF hI q κ) W) _ U' _ r (fun α => Idx r (U.d α))
    (fun i => fHom 𝔭 (isF _) (hT i) r) (fun i a k => (resU _ (hle i a)).pull r (ω (i a) k)) (fun α β k k' => g' α β k' k)
    ?_ ?_ ?_ ?_ ?_
  · intro n i a h
    exact hω (i a) (capO U' i) (capO_le U' i a) _ (hle i a) (isF _) (hT i) (hfreeT i a) h
  · intro n i c h
    exact fAct_str 𝔭 (isF _) (hT i) r c h
  · intro n i j f h
    exact res_fAct 𝔭 (isF _) (hT _) r (isF _) (hT i) (capO_comp U' i j.succAbove) _ f h
  · intro n i j a k
    exact GlobalTheory.CompanionTheory.GrCech.res_res _ _ _ r _
  · intro n i a a' k'
    have hle2 : capT (fun α => SQ q κ γ p (U.U α)) i ≤ SQ q κ γ p (U.U (i a) ⊓ U.U (i a')) := by
      intro T h
      exact ⟨(h a).1, _, rfl, le_preimage_inf (pt T) (sq_inU (hle i a T h)) (sq_inU (hle i a' T h))⟩
    have h1 := congrArg ((resU _ hle2).pull r) (hg' (i a) (i a') k')
    rw [GlobalTheory.CompanionTheory.GrCech.res_res, map_sum] at h1
    refine h1.trans (Finset.sum_congr rfl fun k _ => ?_)
    refine (res_fAct 𝔭 (isF _) (hq2 _ _) r (isF _) (hT i) (le_inf (capO_le U' i a) (capO_le U' i a')) hle2 _ _).trans ?_
    change fAct _ _ _ r _ _ = fAct _ _ _ r _ _
    rw [GlobalTheory.CompanionTheory.GrCech.res_res]

end Vb

section Fin
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (hI : I = ⊥) {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {γ : DividedPowers I} {p : ℕ}

/- English proof (translation)
Use `top_le_iff.1 fun x _ => ?_` and prove the remaining obligations. Establish `hx : (jF hI q κ) x ∈ (⨆ α, U.U α)`. Rewrite using `[U.cover]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨α, hα⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨α, hα⟩`.
-/
theorem cover_pre (U : Cov q) : (⨆ α, jF hI q κ ⁻¹ᵁ U.U α) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have hx : (jF hI q κ) x ∈ (⨆ α, U.U α) := by
    rw [U.cover]
    trivial
  obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨α, hα⟩

include hI in
/- English proof (translation)
Use `haveI : IsProper (qF hI q κ) := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance`. Take `⟨V⟩` from `vb_cech (γ := γ) (p := p) (κ := κ) hI hp hn U r`. Establish `ha : ∀ n (i : Fin (n + 1) → U.ι), IsAffineOpen (capO (fun α => jF hI q κ ⁻¹ᵁ U.U α) i)` using `fun n i => by`. Rewrite using `[capO_pre]`. Conclude with `aff_pre hI (GlobalTheory.CompanionTheory.GrCech.capO_affine U n i)`.

Establish `h` using `@vb_fin R _ _ (XF hI q κ) (qF hI q κ) _ U.ι _ (fun α => jF hI q κ ⁻¹ᵁ U.U α) (cover_pre hI U) ha (CrystallineSemistableComparison.Pb.cechH (GF (nlFun γ p X q κ) r) (fun α => SQ q κ γ p (U.U α)) r) V a`. Conclude with `h`.
-/
theorem cech_fin [IsNoetherianRing R] (hp : p ≠ 0) (hn : IsNilpotent (p : R)) [IsProper q] (U : Cov q) (r a : ℕ) :
    Module.Finite R ((CrystallineSemistableComparison.Pb.cechH (GF (nlFun γ p X q κ) r) (fun α => SQ q κ γ p (U.U α)) r).cx.H a) := by
  haveI : IsProper (qF hI q κ) := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  obtain ⟨V⟩ := vb_cech (γ := γ) (p := p) (κ := κ) hI hp hn U r
  have ha : ∀ n (i : Fin (n + 1) → U.ι), IsAffineOpen (capO (fun α => jF hI q κ ⁻¹ᵁ U.U α) i) := fun n i => by
    rw [capO_pre]
    exact aff_pre hI (GlobalTheory.CompanionTheory.GrCech.capO_affine U n i)
  have h := @vb_fin R _ _ (XF hI q κ) (qF hI q κ) _ U.ι _ (fun α => jF hI q κ ⁻¹ᵁ U.U α) (cover_pre hI U) ha
      (CrystallineSemistableComparison.Pb.cechH (GF (nlFun γ p X q κ) r) (fun α => SQ q κ γ p (U.U α)) r) V a
  exact h
end Fin

end GlobalTheory.CompanionTheory.FibGr
end
