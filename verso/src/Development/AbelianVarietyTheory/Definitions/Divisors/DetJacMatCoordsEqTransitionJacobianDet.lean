import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory

variable {k : Type} [CommRing k] {Y : Scheme.{0}}

abbrev CxPts (p : Y ⟶ Sp k) (σ : k →+* ℂ) : Type := PtsOver p (spMap σ)

namespace CxPts

instance measurableSpace (Y : Scheme.{0}) : MeasurableSpace (Sp ℂ ⟶ Y) := borel _

instance borelSpace (Y : Scheme.{0}) : BorelSpace (Sp ℂ ⟶ Y) := ⟨rfl⟩

variable (p : Y ⟶ Sp k) (σ : k →+* ℂ)

instance t2Space [IsSeparated p] : T2Space (CxPts p σ) := PtsOver.t2Space p _

instance secondCountableTopology [LocallyOfFiniteType p] [QuasiCompact p] :
    SecondCountableTopology (CxPts p σ) := PtsOver.secondCountableTopology p _

variable {p} in

/- English proof (translation)
The claim follows from `PtsOver.compactSpace h _`.
-/
theorem compactSpace (h : IsProjOver p) : CompactSpace (CxPts p σ) := PtsOver.compactSpace h _

def ptsIn (U : Y.Opens) : Set (CxPts p σ) := {y | ⊤ ≤ y.1 ⁻¹ᵁ U}

def ev (U : Y.Opens) (f : Γ(Y, U)) (y : CxPts p σ) : ℂ := valR y.1 U f

variable {p σ} {U W : Y.Opens} {y : CxPts p σ}

/- English proof (translation)
The claim follows from `(isOpen_setOf_le_preimage U).preimage continuous_subtype_val`.
-/
theorem isOpen_ptsIn (U : Y.Opens) : IsOpen (ptsIn p σ U) :=
  (isOpen_setOf_le_preimage U).preimage continuous_subtype_val

/- English proof (translation)
The claim follows from `(continuousOn_valR f).comp continuous_subtype_val.continuousOn fun _ h => h`.
-/
theorem continuousOn_ev (f : Γ(Y, U)) : ContinuousOn (ev p σ U f) (ptsIn p σ U) :=
  (continuousOn_valR f).comp continuous_subtype_val.continuousOn fun _ h => h

/- English proof (translation)
The claim follows from `continuous_induced_rng.trans Points.continuous_iff`.
-/
theorem continuous_iff {B : Type*} [TopologicalSpace B] {e : B → CxPts p σ} :
    Continuous e ↔ ∀ U : Y.Opens, IsOpen (e ⁻¹' ptsIn p σ U) ∧
      ∀ f : Γ(Y, U), ContinuousOn (ev p σ U f ∘ e) (e ⁻¹' ptsIn p σ U) :=
  continuous_induced_rng.trans Points.continuous_iff

/- English proof (translation)
The claim follows from `le_preimage_iff _ _`.
-/
theorem mem_ptsIn : y ∈ ptsIn p σ U ↔ y.1 (IsLocalRing.closedPoint ℂ) ∈ U := le_preimage_iff _ _

/- English proof (translation)
Introduce `y hy` and use `le_preimage_mono y.1 h hy`.
-/
theorem ptsIn_mono (h : W ≤ U) : ptsIn p σ W ⊆ ptsIn p σ U := fun y hy => le_preimage_mono y.1 h hy

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨ptsIn_mono inf_le_left h, ptsIn_mono inf_le_right h⟩, fun h => le_preimage_inf h.1 h.2⟩`.
-/
@[simp] theorem mem_ptsIn_inf : y ∈ ptsIn p σ (U ⊓ W) ↔ y ∈ ptsIn p σ U ∧ y ∈ ptsIn p σ W :=
  ⟨fun h => ⟨ptsIn_mono inf_le_left h, ptsIn_mono inf_le_right h⟩,
    fun h => le_preimage_inf h.1 h.2⟩

/- English proof (translation)
The claim follows from `le_preimage_top _`.
-/
@[simp] theorem mem_ptsIn_top : y ∈ ptsIn p σ ⊤ := le_preimage_top _

/- English proof (translation)
The claim follows from `exists_le_preimage_of_iSup_eq_top y.1 h`.
-/
theorem exists_mem_ptsIn {ι : Sort*} {U : ι → Y.Opens} (h : iSup U = ⊤) (y : CxPts p σ) :
    ∃ i, y ∈ ptsIn p σ (U i) := exists_le_preimage_of_iSup_eq_top y.1 h

def evHom (h : y ∈ ptsIn p σ U) : Γ(Y, U) →+* ℂ := (valMap y.1 U h).hom

/- English proof (translation)
The claim follows from `valR_eq _ _ h f`.
-/
theorem ev_eq (h : y ∈ ptsIn p σ U) (f : Γ(Y, U)) : ev p σ U f y = evHom h f := valR_eq _ _ h f

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evHom_eq_evalPt (h : y ∈ ptsIn p σ U) : evHom h = TangentOrigin.evalPt y.1 U h := rfl

/- English proof (translation)
The claim follows from `dif_neg h`.
-/
theorem ev_of_notMem (h : y ∉ ptsIn p σ U) (f : Γ(Y, U)) : ev p σ U f y = 0 := dif_neg h

/- English proof (translation)
The claim follows from `valR_res _ e h f`.
-/
theorem ev_res (e : W ≤ U) (h : y ∈ ptsIn p σ W) (f : Γ(Y, U)) :
    ev p σ W (resG Y e f) y = ev p σ U f y := valR_res _ e h f

/- English proof (translation)
Distinguish the cases in `h : y ∈ ptsIn p σ U`. Simplify using `only [ev_eq h, map_mul]`. Simplify using `only [ev_of_notMem h, mul_zero]`.
-/
theorem ev_mul (f g : Γ(Y, U)) (y : CxPts p σ) :
    ev p σ U (f * g) y = ev p σ U f y * ev p σ U g y := by
  by_cases h : y ∈ ptsIn p σ U
  · simp only [ev_eq h, map_mul]
  · simp only [ev_of_notMem h, mul_zero]

/- English proof (translation)
Distinguish the cases in `h : y ∈ ptsIn p σ U`. Simplify using `only [ev_eq h, map_add]`. Simplify using `only [ev_of_notMem h, add_zero]`.
-/
theorem ev_add (f g : Γ(Y, U)) (y : CxPts p σ) :
    ev p σ U (f + g) y = ev p σ U f y + ev p σ U g y := by
  by_cases h : y ∈ ptsIn p σ U
  · simp only [ev_eq h, map_add]
  · simp only [ev_of_notMem h, add_zero]

/- English proof (translation)
The claim follows from `valR_constFn_of_over p σ y.1 y.2 U h a`.
-/
theorem ev_algX (h : y ∈ ptsIn p σ U) (a : k) : ev p σ U (algX p U a) y = σ a :=
  valR_constFn_of_over p σ y.1 y.2 U h a

/- English proof (translation)
The claim follows from `ev_eq h f ▸ (hf.map (evHom h)).ne_zero`.
-/
theorem ev_ne_zero (h : y ∈ ptsIn p σ U) {f : Γ(Y, U)} (hf : IsUnit f) : ev p σ U f y ≠ 0 :=
  ev_eq h f ▸ (hf.map (evHom h)).ne_zero

/- English proof (translation)
The claim follows from `(le_preimage_basicOpen_iff y.1 h f).trans isUnit_iff_ne_zero`.
-/
theorem mem_ptsIn_basicOpen (h : y ∈ ptsIn p σ U) (f : Γ(Y, U)) :
    y ∈ ptsIn p σ (Y.basicOpen f) ↔ ev p σ U f y ≠ 0 :=
  (le_preimage_basicOpen_iff y.1 h f).trans isUnit_iff_ne_zero

def ofHom (hU : IsAffineOpen U) (φ : Γ(Y, U) →+* ℂ) (h : ∀ a, φ (algX p U a) = σ a) : CxPts p σ :=
  ⟨Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec, TangentOrigin.eq_spMap_of_evalPt _ _ fun a => by
    have h₁ := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom φ)
    have h₂ := congrArg (fun ψ : Γ(Y, U) ⟶ CommRingCat.of ℂ => ψ.hom (algX p U a))
      (valMap_specMap_fromSpec hU (CommRingCat.ofHom φ) h₁)
    exact (TangentOrigin.evalPt_constFn p _ U h₁ a).symm.trans (h₂.trans (h a))⟩

/- English proof (translation)
The claim follows from `le_preimage_specMap_fromSpec hU (CommRingCat.ofHom φ)`.
-/
theorem ofHom_mem (hU : IsAffineOpen U) (φ : Γ(Y, U) →+* ℂ) (h : ∀ a, φ (algX p U a) = σ a) :
    ofHom hU φ h ∈ ptsIn p σ U := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom φ)

/- English proof (translation)
The claim follows from `(ev_eq (ofHom_mem hU φ h) f).trans (congrArg (fun ψ : Γ(Y, U) ⟶ CommRingCat.of ℂ => ψ.hom f) (valMap_specMap_fromSpec hU (CommRingCat.ofHom φ) (ofHom_mem hU φ h)))`.
-/
theorem ev_ofHom (hU : IsAffineOpen U) (φ : Γ(Y, U) →+* ℂ) (h : ∀ a, φ (algX p U a) = σ a)
    (f : Γ(Y, U)) : ev p σ U f (ofHom hU φ h) = φ f :=
  (ev_eq (ofHom_mem hU φ h) f).trans
    (congrArg (fun ψ : Γ(Y, U) ⟶ CommRingCat.of ℂ => ψ.hom f)
      (valMap_specMap_fromSpec hU (CommRingCat.ofHom φ) (ofHom_mem hU φ h)))

/- English proof (translation)
Establish `hc : ContinuousOn s T` using `fun v hv => ContinuousAt.continuousWithinAt (tendsto_subtype_rng.2 (tendsto_of_isAffineOpen hU (hs v hv) (eventually_of_mem (hT.mem_nhds hv) hs) fun f => ((hd f).differentiableAt (hT.mem_nhds hv)).continuousAt))`. Use `⟨hc, fun W f v hv => DifferentiableAt.differentiableWithinAt ?_⟩` and prove the remaining obligations. Take `⟨h, hhW, hh⟩` from `hU.exists_basicOpen_le (V := W) ⟨_, mem_ptsIn.1 hv.2⟩ (mem_ptsIn.1 (hs v hv.1))`. Establish `hB : s v ∈ ptsIn p σ (Y.basicOpen h)` using `mem_ptsIn.2 hh`. Use `hU.isLocalization_basicOpen h` as an intermediate fact.

Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj h (resG Y hhW f)`. Establish `hda` using `fun a => (hd a).differentiableAt (hT.mem_nhds hv.1)`. Establish `hq : DifferentiableAt ℂ (fun w => ev p σ U a (s w) * (ev p σ U h (s w) ^ n)⁻¹) v` using `(hda a).mul (((hda h).pow n).inv (pow_ne_zero n ((mem_ptsIn_basicOpen (hs v hv.1) h).1 hB)))`. Use `hq.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [(hc.continuousAt (hT.mem_nhds hv.1)).preimage_mem_nhds ((isOpen_ptsIn _).mem_nhds hB)] with w hw`.

Establish `ha' : resG Y hhW f * resG Y (Y.basicOpen_le h) h ^ n = resG Y (Y.basicOpen_le h) a` using `ha`. Establish `e` using `congrArg (evHom hw) ha'`. Rewrite `e` using `[map_mul, map_pow, ← ev_eq, ← ev_eq, ← ev_eq, ev_res _ hw, ev_res _ hw, ev_res _ hw]`. Conclude with `(eq_mul_inv_iff_mul_eq₀ (pow_ne_zero n ((mem_ptsIn_basicOpen (ptsIn_mono (Y.basicOpen_le h) hw) h).1 hw))).2 e`.
-/
theorem holo_of_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (hU : IsAffineOpen U)
    {T : Set E} (hT : IsOpen T) {s : E → CxPts p σ} (hs : ∀ v ∈ T, s v ∈ ptsIn p σ U)
    (hd : ∀ a : Γ(Y, U), DifferentiableOn ℂ (ev p σ U a ∘ s) T) :
    ContinuousOn s T ∧ ∀ (W : Y.Opens) (f : Γ(Y, W)),
      DifferentiableOn ℂ (ev p σ W f ∘ s) (T ∩ s ⁻¹' ptsIn p σ W) := by
  have hc : ContinuousOn s T := fun v hv => ContinuousAt.continuousWithinAt (tendsto_subtype_rng.2
    (tendsto_of_isAffineOpen hU (hs v hv) (eventually_of_mem (hT.mem_nhds hv) hs) fun f =>
      ((hd f).differentiableAt (hT.mem_nhds hv)).continuousAt))
  refine ⟨hc, fun W f v hv => DifferentiableAt.differentiableWithinAt ?_⟩
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := W) ⟨_, mem_ptsIn.1 hv.2⟩
    (mem_ptsIn.1 (hs v hv.1))
  have hB : s v ∈ ptsIn p σ (Y.basicOpen h) := mem_ptsIn.2 hh
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG Y hhW f)
  have hda := fun a => (hd a).differentiableAt (hT.mem_nhds hv.1)
  have hq : DifferentiableAt ℂ (fun w => ev p σ U a (s w) * (ev p σ U h (s w) ^ n)⁻¹) v :=
    (hda a).mul (((hda h).pow n).inv (pow_ne_zero n ((mem_ptsIn_basicOpen (hs v hv.1) h).1 hB)))
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [(hc.continuousAt (hT.mem_nhds hv.1)).preimage_mem_nhds
    ((isOpen_ptsIn _).mem_nhds hB)] with w hw
  have ha' : resG Y hhW f * resG Y (Y.basicOpen_le h) h ^ n = resG Y (Y.basicOpen_le h) a := ha
  have e := congrArg (evHom hw) ha'
  rw [map_mul, map_pow, ← ev_eq, ← ev_eq, ← ev_eq, ev_res _ hw, ev_res _ hw, ev_res _ hw] at e
  exact (eq_mul_inv_iff_mul_eq₀
    (pow_ne_zero n ((mem_ptsIn_basicOpen (ptsIn_mono (Y.basicOpen_le h) hw) h).1 hw))).2 e

end CxPts

open CxPts

structure AlgChart (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) where

  e : OpenPartialHomeomorph (CxPts p σ) (V D)

  U : Y.Opens

  affine : IsAffineOpen U

  x : Fin D → Γ(Y, U)

  etale : (MvPolynomial.eval₂Hom (algX p U) x).Etale

  source_subset : e.source ⊆ ptsIn p σ U

  apply_eq : ∀ y ∈ e.source, ∀ a, e y a = ev p σ U (x a) y

  holo : ∀ (W : Y.Opens) (f : Γ(Y, W)),
    DifferentiableOn ℂ (ev p σ W f ∘ e.symm) (e.target ∩ e.symm ⁻¹' ptsIn p σ W)

namespace AlgChart

variable {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} (c c' : AlgChart p σ D)

/- English proof (translation)
Use `⟨c.affine, ?_⟩` and prove the remaining obligations. Establish `h : IsFreeGen (MvPolynomial (Fin D) k) (dForm (algebraMap k (MvPolynomial (Fin D) k)) (MvPolynomial.X : Fin D → _))`. Establish `key (inst : Algebra k (MvPolynomial (Fin D) k)) (e : inst = AddMonoidAlgebra.algebra) : IsFreeGen (MvPolynomial (Fin D) k) (@dWedge k _ _ _ inst D MvPolynomial.X)`. Substitute `e` using the available equality. Use `isFreeGen_ιMulti (KaehlerDifferential.mvPolynomialBasis k (Fin D))` as an intermediate fact.

Rewrite `this` using `[funext (KaehlerDifferential.mvPolynomialBasis_apply k (Fin D))]`. Then use the resulting hypothesis. Conclude with `key _ (Algebra.algebra_ext _ _ fun _ => rfl)`. Establish `hC : (MvPolynomial.eval₂Hom (algX p c.U) c.x).comp (algebraMap k _) = algX p c.U` using `RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ a`. Use `h.formMap c.etale hC` as an intermediate fact. Rewrite `this` using `[formMap_dForm]`.

Simplify `this` using `only [MvPolynomial.eval₂Hom_X']`.
-/
theorem isFrame : IsFrame (dOn p c.x) := by
  refine ⟨c.affine, ?_⟩
  have h : IsFreeGen (MvPolynomial (Fin D) k)
      (dForm (algebraMap k (MvPolynomial (Fin D) k)) (MvPolynomial.X : Fin D → _)) := by
    have key (inst : Algebra k (MvPolynomial (Fin D) k))
        (e : inst = AddMonoidAlgebra.algebra) :
        IsFreeGen (MvPolynomial (Fin D) k) (@dWedge k _ _ _ inst D MvPolynomial.X) := by
      subst e
      have := isFreeGen_ιMulti (KaehlerDifferential.mvPolynomialBasis k (Fin D))
      rwa [funext (KaehlerDifferential.mvPolynomialBasis_apply k (Fin D))] at this
    exact key _ (Algebra.algebra_ext _ _ fun _ => rfl)
  have hC : (MvPolynomial.eval₂Hom (algX p c.U) c.x).comp (algebraMap k _) = algX p c.U :=
    RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ a
  have := h.formMap c.etale hC
  rw [formMap_dForm] at this
  simpa only [MvPolynomial.eval₂Hom_X'] using this

def restr (S : Set (CxPts p σ)) (hS : IsOpen S) : AlgChart p σ D where
  e := c.e.restrOpen S hS
  U := c.U
  affine := c.affine
  x := c.x
  etale := c.etale
  source_subset := inter_subset_left.trans c.source_subset
  apply_eq y hy := c.apply_eq y hy.1
  holo W f := (c.holo W f).mono fun _ hv => ⟨hv.1.1, hv.2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem restr_source (S : Set (CxPts p σ)) (hS : IsOpen S) :
    (c.restr S hS).e.source = c.e.source ∩ S := rfl

/- English proof (translation)
The claim follows from `differentiableOn_euclidean.2 fun a => ((c.holo _ (c'.x a)).mono fun _ hv => ⟨hv.1, c'.source_subset hv.2⟩).congr fun _ hv => c'.apply_eq _ hv.2 a`.
-/
theorem holo_trans :
    DifferentiableOn ℂ (c'.e ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' c'.e.source) :=
  differentiableOn_euclidean.2 fun a => ((c.holo _ (c'.x a)).mono fun _ hv =>
    ⟨hv.1, c'.source_subset hv.2⟩).congr fun _ hv => c'.apply_eq _ hv.2 a

/- English proof (translation)
The claim follows from `(c.holo W f).differentiableAt ((isOpen_over c.e (isOpen_ptsIn W)).mem_nhds (mem_over c.e hy hW))`.
-/
theorem differentiableAt_ev {W : Y.Opens} (f : Γ(Y, W)) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hW : y ∈ ptsIn p σ W) : DifferentiableAt ℂ (ev p σ W f ∘ c.e.symm) (c.e y) :=
  (c.holo W f).differentiableAt
    ((isOpen_over c.e (isOpen_ptsIn W)).mem_nhds (mem_over c.e hy hW))

def jacMat {W : Y.Opens} (f : Fin D → Γ(Y, W)) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun a b => fderiv ℂ (ev p σ W (f a) ∘ c.e.symm) (c.e y) (EuclideanSpace.single b 1)

/- English proof (translation)
Set `` to `(algX p W).toAlgebra`. Set `` to `(evHom hW).toAlgebra`. Set `` to `σ.toAlgebra`. Establish `: IsScalarTower k Γ(Y, W) ℂ` using `IsScalarTower.of_algebraMap_eq fun a => (ev_algX hW a).symm.trans (ev_eq hW _)`. Establish `hn : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ W` using `eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W)).mem_nhds (mem_over c.e hy hW)) fun _ h => h.2`.

Set `δ (f : Γ(Y, W)) : Fin D → ℂ` to `fun b => fderiv ℂ (ev p σ W f ∘ c.e.symm) (c.e y) (EuclideanSpace.single b 1)`. Establish `hd` using `fun f : Γ(Y, W) => c.differentiableAt_ev f hy hW`. Establish `hmul (f g : Γ(Y, W)) : δ (f * g) = f • δ g + g • δ f`. Use function extensionality and compare the values at `b`. Establish `e : ev p σ W (f * g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) * (ev p σ W g ∘ c.e.symm)`.

Use function extensionality and compare the values at `fun v => ev_mul _ _ _`. Simplify using `only [δ, e, fderiv_mul (hd f) (hd g), Function.comp_apply, c.e.left_inv hy, ev_eq hW]`. Both sides reduce to the same expression. Establish `hc (a : k) : δ (algebraMap k _ a) = 0`. Use function extensionality and compare the values at `b`.

Establish `e : ev p σ W (algX p W a) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] fun _ => σ a` using `hn.mono fun v hv => ev_algX hv a`. Express the relevant statement in the definitionally equal form `fderiv ℂ (ev p σ W (algX p W a) ∘ c.e.symm) _ _ = 0`. Rewrite using `[e.fderiv_eq]`. Simplify using the standard rewrite rules. Set `d : Derivation k Γ(Y, W) (Fin D → ℂ)` to `Derivation.mk' { toFun := δ map_add' := fun f g => by`.

Use function extensionality and compare the values at `b`. Establish `e : ev p σ W (f + g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) + (ev p σ W g ∘ c.e.symm)`. Use function extensionality and compare the values at `fun v => ev_add _ _ _`. Simplify using `only [δ, e, fderiv_add (hd f) (hd g)]`. Both sides reduce to the same expression.

Use the proof step `map_smul' := fun a f => by`. Rewrite using `[Algebra.smul_def, hmul, hc, smul_zero, add_zero, algebraMap_smul]`. Use `rfl } hmul`. Set `det : (Fin D → ℂ) [⋀^Fin D]→ₗ[Γ(Y, W)] ℂ` to `{ (Matrix.detRowAlternating (n := Fin D) (R := ℂ)).toMultilinearMap.restrictScalars Γ(Y, W) with map_eq_zero_of_eq' := (Matrix.detRowAlternating (n := Fin D) (R := ℂ)).map_eq_zero_of_eq }`. Set `Λ` to `exteriorPower.alternatingMapLinearEquiv (det.compLinearMap d.liftKaehlerDifferential)`.

Use `⟨⟨Λ.toAddHom, Λ.map_smul⟩, fun f => ?_⟩` and prove the remaining obligations. Use `(exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans ?_` and prove the remaining obligations. Simplify using `only [AlternatingMap.compLinearMap_apply, Derivation.liftKaehlerDifferential_comp_D]`. Both sides reduce to the same expression.
-/
theorem exists_forms_map {W : Y.Opens} {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hW : y ∈ ptsIn p σ W) : ∃ Λ : FormsOn p D W →ₛₗ[evHom hW] ℂ,
      ∀ f, Λ (dOn p f) = (c.jacMat f y).det := by
  let := (algX p W).toAlgebra
  let := (evHom hW).toAlgebra
  let := σ.toAlgebra
  have : IsScalarTower k Γ(Y, W) ℂ := IsScalarTower.of_algebraMap_eq fun a =>
    (ev_algX hW a).symm.trans (ev_eq hW _)
  have hn : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ W :=
    eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W)).mem_nhds (mem_over c.e hy hW)) fun _ h => h.2
  let δ (f : Γ(Y, W)) : Fin D → ℂ := fun b =>
    fderiv ℂ (ev p σ W f ∘ c.e.symm) (c.e y) (EuclideanSpace.single b 1)
  have hd := fun f : Γ(Y, W) => c.differentiableAt_ev f hy hW
  have hmul (f g : Γ(Y, W)) : δ (f * g) = f • δ g + g • δ f := by
    funext b
    have e : ev p σ W (f * g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) * (ev p σ W g ∘ c.e.symm) :=
      funext fun v => ev_mul _ _ _
    simp only [δ, e, fderiv_mul (hd f) (hd g), Function.comp_apply, c.e.left_inv hy, ev_eq hW]
    rfl
  have hc (a : k) : δ (algebraMap k _ a) = 0 := by
    funext b
    have e : ev p σ W (algX p W a) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] fun _ => σ a :=
      hn.mono fun v hv => ev_algX hv a
    change fderiv ℂ (ev p σ W (algX p W a) ∘ c.e.symm) _ _ = 0
    rw [e.fderiv_eq]
    simp
  let d : Derivation k Γ(Y, W) (Fin D → ℂ) := Derivation.mk'
    { toFun := δ
      map_add' := fun f g => by
        funext b
        have e : ev p σ W (f + g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) + (ev p σ W g ∘ c.e.symm) :=
          funext fun v => ev_add _ _ _
        simp only [δ, e, fderiv_add (hd f) (hd g)]
        rfl
      map_smul' := fun a f => by
        rw [Algebra.smul_def, hmul, hc, smul_zero, add_zero, algebraMap_smul]
        rfl } hmul
  let det : (Fin D → ℂ) [⋀^Fin D]→ₗ[Γ(Y, W)] ℂ :=
    { (Matrix.detRowAlternating (n := Fin D) (R := ℂ)).toMultilinearMap.restrictScalars Γ(Y, W) with
      map_eq_zero_of_eq' := (Matrix.detRowAlternating (n := Fin D) (R := ℂ)).map_eq_zero_of_eq }
  let Λ := exteriorPower.alternatingMapLinearEquiv (det.compLinearMap d.liftKaehlerDifferential)
  refine ⟨⟨Λ.toAddHom, Λ.map_smul⟩, fun f => ?_⟩
  refine (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).trans ?_
  simp only [AlternatingMap.compLinearMap_apply, Derivation.liftKaehlerDifferential_comp_D]
  rfl

/- English proof (translation)
Use extensionality with `a b`. Establish `e : ev p σ W' (resG Y h (f a)) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] ev p σ W (f a) ∘ c.e.symm` using `eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W')).mem_nhds (mem_over c.e hy hW)) fun v hv => ev_res h hv.2 _`. Simplify using `only [jacMat, Matrix.of_apply, e.fderiv_eq]`.
-/
theorem jacMat_res {W W' : Y.Opens} (h : W' ≤ W) (f : Fin D → Γ(Y, W)) {y : CxPts p σ}
    (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W') :
    c.jacMat (fun a => resG Y h (f a)) y = c.jacMat f y := by
  ext a b
  have e : ev p σ W' (resG Y h (f a)) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] ev p σ W (f a) ∘ c.e.symm :=
    eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W')).mem_nhds (mem_over c.e hy hW))
      fun v hv => ev_res h hv.2 _
  simp only [jacMat, Matrix.of_apply, e.fderiv_eq]

/- English proof (translation)
Establish `hn` using `(isOpen_over c.e c'.e.open_source).mem_nhds (mem_over c.e hy hy')`. Rewrite using `[transDet, ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin D) ℂ).toBasis]`. Use `congr 1`. Use extensionality with `a b`. Establish `e : ev p σ _ (c'.x a) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] EuclideanSpace.proj (𝕜` using `ℂ) a ∘ c'.e ∘ c.e.symm := eventually_of_mem hn fun v hv => (c'.apply_eq _ hv.2 a).symm`.

Rewrite using `[jacMat, Matrix.of_apply, e.fderiv_eq, ((EuclideanSpace.proj (𝕜 := ℂ) a).hasFDerivAt.comp _ ((c.holo_trans c').differentiableAt hn).hasFDerivAt).fderiv, LinearMap.toMatrix_apply]`. Simplify using the standard rewrite rules.
-/
theorem det_jacMat_coords_eq_transitionJacobianDet {y : CxPts p σ} (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) :
    (c.jacMat c'.x y).det = transDet c.e c'.e y := by
  have hn := (isOpen_over c.e c'.e.open_source).mem_nhds (mem_over c.e hy hy')
  rw [transDet, ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin D) ℂ).toBasis]
  congr 1
  ext a b
  have e : ev p σ _ (c'.x a) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] EuclideanSpace.proj (𝕜 := ℂ) a ∘ c'.e ∘ c.e.symm :=
    eventually_of_mem hn fun v hv => (c'.apply_eq _ hv.2 a).symm
  rw [jacMat, Matrix.of_apply, e.fderiv_eq, ((EuclideanSpace.proj (𝕜 := ℂ) a).hasFDerivAt.comp _
    ((c.holo_trans c').differentiableAt hn).hasFDerivAt).fderiv, LinearMap.toMatrix_apply]
  simp

/- English proof (translation)
Establish `e : c.e ∘ c.e.symm =ᶠ[𝓝 (c.e y)] id` using `eventually_of_mem (c.e.open_target.mem_nhds (c.e.map_source hy)) fun v hv => c.e.right_inv hv`. Rewrite using `[transDet, e.fderiv_eq, fderiv_id]`. Conclude with `LinearMap.det_id`.
-/
theorem transDet_self {y : CxPts p σ} (hy : y ∈ c.e.source) : transDet c.e c.e y = 1 := by
  have e : c.e ∘ c.e.symm =ᶠ[𝓝 (c.e y)] id :=
    eventually_of_mem (c.e.open_target.mem_nhds (c.e.map_source hy)) fun v hv => c.e.right_inv hv
  rw [transDet, e.fderiv_eq, fderiv_id]
  exact LinearMap.det_id

/- English proof (translation)
Take `⟨W', hW', hyW, e⟩` from `exists_isAffineOpen_le y.1 hW`. Use `replace hyW : y ∈ ptsIn p σ W' := hyW`. Take `⟨Λ, hΛ⟩` from `c.exists_forms_map hy hyW`. Use `congrArg Λ (c.isFrame.resForm_eq_coeff_smul h (dOn p f) hW' e)` as an intermediate fact. Rewrite `this` using `[map_smulₛₗ, resForm_dOn, resForm_dOn, hΛ, hΛ, c.jacMat_res _ _ hy hyW, c.jacMat_res _ _ hy hyW, c.det_jacMat_coords_eq_transitionJacobianDet c hy hy, c.transDet_self hy, smul_eq_mul, mul_one, ← ev_eq, ev_res _ hyW]`.

Conclude with `this.symm`.
-/
theorem ev_coeff_dOn {W : Y.Opens} (h : W ≤ c.U) (f : Fin D → Γ(Y, W)) {y : CxPts p σ}
    (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) :
    ev p σ W (c.isFrame.coeff h (dOn p f)) y = (c.jacMat f y).det := by
  obtain ⟨W', hW', hyW, e⟩ := exists_isAffineOpen_le y.1 hW
  replace hyW : y ∈ ptsIn p σ W' := hyW
  obtain ⟨Λ, hΛ⟩ := c.exists_forms_map hy hyW
  have := congrArg Λ (c.isFrame.resForm_eq_coeff_smul h (dOn p f) hW' e)
  rw [map_smulₛₗ, resForm_dOn, resForm_dOn, hΛ, hΛ, c.jacMat_res _ _ hy hyW, c.jacMat_res _ _ hy hyW,
    c.det_jacMat_coords_eq_transitionJacobianDet c hy hy, c.transDet_self hy, smul_eq_mul, mul_one, ← ev_eq, ev_res _ hyW] at this
  exact this.symm

/- English proof (translation)
Establish `hW : y ∈ ptsIn p σ (c.U ⊓ c'.U)` using `mem_ptsIn_inf.2 ⟨c.source_subset hy, c'.source_subset hy'⟩`. Rewrite using `[← c.det_jacMat_coords_eq_transitionJacobianDet c' hy hy', ← c.jacMat_res inf_le_right _ hy hW, ← c.ev_coeff_dOn inf_le_left _ hy hW, ← resForm_dOn]`. Both sides reduce to the same expression.
-/
theorem ev_ratio {y : CxPts p σ} (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) :
    ev p σ _ (c.isFrame.ratio c'.isFrame).val y = transDet c.e c'.e y := by
  have hW : y ∈ ptsIn p σ (c.U ⊓ c'.U) := mem_ptsIn_inf.2 ⟨c.source_subset hy, c'.source_subset hy'⟩
  rw [← c.det_jacMat_coords_eq_transitionJacobianDet c' hy hy', ← c.jacMat_res inf_le_right _ hy hW,
    ← c.ev_coeff_dOn inf_le_left _ hy hW, ← resForm_dOn]
  rfl

/- English proof (translation)
Take `⟨N, τ, n, f, O, hN, hO, hO₀, hd, hτ, hrec⟩` from `EtaleFamily.exists_holomorphic_sections 0 D k Γ(Y, U) _ univ (fun _ => σ) 0 (evHom hy) hx isOpen_univ trivial (fun a => differentiableOn_const _) (fun a => by rw [MvPolynomial.eval₂Hom_C, ← ev_eq, ev_algX hy])`. Simplify using `only [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X'] at hτ hrec`. Set `j (v : V D) : (Fin 0 → ℂ) × (Fin D → ℂ)` to `(0, v.ofLp)`. Establish `hj : Differentiable ℂ j` using `(differentiable_const _).prodMk (EuclideanSpace.equiv (Fin D) ℂ).differentiable`. Set `s (v : V D) : CxPts p σ` to `if h : j v ∈ N then ofHom hU (τ (j v)) (hτ _ h).2.1 else y`.

Establish `hsU (v) (h : j v ∈ N) : s v ∈ ptsIn p σ U`. Simplify using `only [s, dif_pos h]`. Conclude with `ofHom_mem _ _ _`. Establish `hsv (v) (h : j v ∈ N) (a) : ev p σ U a (s v) = τ (j v) a`. Simplify using `only [s, dif_pos h]`.

Conclude with `ev_ofHom _ _ _ a`. Take `⟨hc, hh⟩` from `holo_of_affine hU (hN.preimage hj.continuous) hsU fun a => ((hd a).comp hj.differentiableOn fun _ h => h).congr fun v hv => hsv v hv a`. Set `S : Set (CxPts p σ)` to `ptsIn p σ U ∩ (fun z => ((0 : Fin 0 → ℂ), fun i => ev p σ U (f i) z)) ⁻¹' O`. Establish `hS : IsOpen S` using `(continuousOn_const.prodMk (continuousOn_pi.2 fun i => continuousOn_ev (f i))).isOpen_inter_preimage (isOpen_ptsIn U) hO`. Set `t (z : CxPts p σ) : V D` to `WithLp.toLp 2 fun a => ev p σ U (x a) z`.

Establish `hts (z) (hz : z ∈ S) : j (t z) ∈ N ∧ s (t z) = z`. Take `⟨h₁, h₂⟩` from `hrec 0 (evHom hz.1) (fun a => by rw [← ev_eq, ev_algX hz.1]) (by simp only [← ev_eq hz.1]; exact hz.2)`. Simplify using `only [← ev_eq hz.1] at h₁ h₂`. Use `⟨h₁, Subtype.ext (ext_of_valR hU (hsU _ h₁) hz.1 fun a => ?_)⟩` and prove the remaining obligations. Conclude with `(hsv _ h₁ a).trans ((congrArg (· a) h₂).trans (ev_eq hz.1 a).symm)`.

Set `e : OpenPartialHomeomorph (CxPts p σ) (V D)` to `{ toFun := t invFun := s source := S target := j ⁻¹' N ∩ s ⁻¹' S map_source' := fun z hz => ⟨(hts z hz).1, by rw [mem_preimage, (hts z hz).2]; exact hz⟩ map_target' := fun v hv => hv.2 left_inv' := fun z hz => (hts z hz).2 right_inv' := fun v hv => by`. Use extensionality with `a`. Conclude with `(hsv v hv.1 _).trans ((hτ _ hv.1).2.2 a)`. Use `open_source := hS`. Use `open_target := hc.isOpen_inter_preimage (hN.preimage hj.continuous) hS`.

Use `continuousOn_toFun := (PiLp.continuous_toLp 2 _).comp_continuousOn ((continuousOn_pi.2 fun a => continuousOn_ev (x a)).mono inter_subset_left)`. Use `continuousOn_invFun := hc.mono inter_subset_left }`. Use `⟨⟨e, U, hU, x, hx, inter_subset_left, fun _ _ _ => rfl, fun W g => (hh W g).mono fun v hv => ⟨hv.1.1, hv.2⟩⟩, ⟨hy, ?_⟩, rfl, rfl⟩` and prove the remaining obligations. Simplify using `only [← ev_eq hy] at hO₀`. Conclude with `hO₀`.
-/
theorem exists_of_etale {U : Y.Opens} (hU : IsAffineOpen U) (x : Fin D → Γ(Y, U))
    (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    ∃ c : AlgChart p σ D, y ∈ c.e.source ∧ ∃ h : c.U = U, c.x = h ▸ x := by
  classical
  obtain ⟨N, τ, n, f, O, hN, hO, hO₀, hd, hτ, hrec⟩ :=
    EtaleFamily.exists_holomorphic_sections 0 D k Γ(Y, U) _ univ (fun _ => σ) 0 (evHom hy) hx
      isOpen_univ trivial (fun a => differentiableOn_const _)
      (fun a => by rw [MvPolynomial.eval₂Hom_C, ← ev_eq, ev_algX hy])
  simp only [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X'] at hτ hrec
  let j (v : V D) : (Fin 0 → ℂ) × (Fin D → ℂ) := (0, v.ofLp)
  have hj : Differentiable ℂ j :=
    (differentiable_const _).prodMk (EuclideanSpace.equiv (Fin D) ℂ).differentiable
  let s (v : V D) : CxPts p σ := if h : j v ∈ N then ofHom hU (τ (j v)) (hτ _ h).2.1 else y
  have hsU (v) (h : j v ∈ N) : s v ∈ ptsIn p σ U := by
    simp only [s, dif_pos h]; exact ofHom_mem _ _ _
  have hsv (v) (h : j v ∈ N) (a) : ev p σ U a (s v) = τ (j v) a := by
    simp only [s, dif_pos h]; exact ev_ofHom _ _ _ a
  obtain ⟨hc, hh⟩ := holo_of_affine hU (hN.preimage hj.continuous) hsU fun a =>
    ((hd a).comp hj.differentiableOn fun _ h => h).congr fun v hv => hsv v hv a
  let S : Set (CxPts p σ) :=
    ptsIn p σ U ∩ (fun z => ((0 : Fin 0 → ℂ), fun i => ev p σ U (f i) z)) ⁻¹' O
  have hS : IsOpen S := (continuousOn_const.prodMk
    (continuousOn_pi.2 fun i => continuousOn_ev (f i))).isOpen_inter_preimage (isOpen_ptsIn U) hO
  let t (z : CxPts p σ) : V D := WithLp.toLp 2 fun a => ev p σ U (x a) z
  have hts (z) (hz : z ∈ S) : j (t z) ∈ N ∧ s (t z) = z := by
    obtain ⟨h₁, h₂⟩ := hrec 0 (evHom hz.1) (fun a => by rw [← ev_eq, ev_algX hz.1])
      (by simp only [← ev_eq hz.1]; exact hz.2)
    simp only [← ev_eq hz.1] at h₁ h₂
    refine ⟨h₁, Subtype.ext (ext_of_valR hU (hsU _ h₁) hz.1 fun a => ?_)⟩
    exact (hsv _ h₁ a).trans ((congrArg (· a) h₂).trans (ev_eq hz.1 a).symm)
  let e : OpenPartialHomeomorph (CxPts p σ) (V D) :=
    { toFun := t
      invFun := s
      source := S
      target := j ⁻¹' N ∩ s ⁻¹' S
      map_source' := fun z hz => ⟨(hts z hz).1, by rw [mem_preimage, (hts z hz).2]; exact hz⟩
      map_target' := fun v hv => hv.2
      left_inv' := fun z hz => (hts z hz).2
      right_inv' := fun v hv => by
        ext a
        exact (hsv v hv.1 _).trans ((hτ _ hv.1).2.2 a)
      open_source := hS
      open_target := hc.isOpen_inter_preimage (hN.preimage hj.continuous) hS
      continuousOn_toFun := (PiLp.continuous_toLp 2 _).comp_continuousOn
        ((continuousOn_pi.2 fun a => continuousOn_ev (x a)).mono inter_subset_left)
      continuousOn_invFun := hc.mono inter_subset_left }
  refine ⟨⟨e, U, hU, x, hx, inter_subset_left, fun _ _ _ => rfl,
    fun W g => (hh W g).mono fun v hv => ⟨hv.1.1, hv.2⟩⟩, ⟨hy, ?_⟩, rfl, rfl⟩
  simp only [← ev_eq hy] at hO₀
  exact hO₀

/- English proof (translation)
Take `⟨W, hW, hz, -⟩` from `Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top z)`. Establish `h` using `HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top`. Take `⟨s, hs, h⟩` from `(RingHom.locally_iff_isLocalization RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h`. Take `⟨t, hzt⟩ : ∃ t : (s : Set Γ(Y, W)), z ∈ Y.basicOpen (t : Γ(Y, W))` from `Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hW).2 hs).ge hz)`. Use `IsAffineOpen.isLocalization_basicOpen hW (t : Γ(Y, W))` as an intermediate fact.

Establish `h₁` using `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, W))))`. Establish `h₂ : (algX p (Y.basicOpen (t : Γ(Y, W)))).IsStandardSmoothOfRelativeDimension D`. Rewrite using `[← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, W)))]`. Conclude with `h₁`. Take `⟨φ, hC, hφ⟩` from `h₂.exists_etale_mvPolynomial`.

Use `⟨_, fun a => φ (MvPolynomial.X a), IsAffineOpen.basicOpen hW _, hzt, ?_⟩` and prove the remaining obligations. Use `hφ` and compare the differences between its conclusion and the goal. Conclude with `MvPolynomial.ringHom_ext (fun a => by rw [MvPolynomial.eval₂Hom_C, ← hC]; rfl) fun a => MvPolynomial.eval₂Hom_X' _ _ a`.
-/
theorem exists_etale_coords [SmoothOfRelativeDimension D p] (z : Y) :
    ∃ (U : Y.Opens) (x : Fin D → Γ(Y, U)), IsAffineOpen U ∧ z ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  obtain ⟨W, hW, hz, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top z)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hzt⟩ : ∃ t : (s : Set Γ(Y, W)), z ∈ Y.basicOpen (t : Γ(Y, W)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hW).2 hs).ge hz)
  have := IsAffineOpen.isLocalization_basicOpen hW (t : Γ(Y, W))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, W))))
  have h₂ : (algX p (Y.basicOpen (t : Γ(Y, W)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, W)))]
    exact h₁
  obtain ⟨φ, hC, hφ⟩ := h₂.exists_etale_mvPolynomial
  refine ⟨_, fun a => φ (MvPolynomial.X a), IsAffineOpen.basicOpen hW _, hzt, ?_⟩
  convert hφ
  exact MvPolynomial.ringHom_ext (fun a => by rw [MvPolynomial.eval₂Hom_C, ← hC]; rfl)
    fun a => MvPolynomial.eval₂Hom_X' _ _ a

/- English proof (translation)
Take `⟨U, x, hU, hz, hx⟩` from `exists_etale_coords (p := p) (D := D) (y.1 (IsLocalRing.closedPoint ℂ))`. Take `⟨c, hc, -⟩` from `exists_of_etale hU x hx (mem_ptsIn.2 hz)`. Conclude with `⟨c, hc⟩`.
-/
theorem exists_mem_source [SmoothOfRelativeDimension D p] (y : CxPts p σ) :
    ∃ c : AlgChart p σ D, y ∈ c.e.source := by
  obtain ⟨U, x, hU, hz, hx⟩ := exists_etale_coords (p := p) (D := D) (y.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨c, hc, -⟩ := exists_of_etale hU x hx (mem_ptsIn.2 hz)
  exact ⟨c, hc⟩

end AlgChart

end GlobalTheory
