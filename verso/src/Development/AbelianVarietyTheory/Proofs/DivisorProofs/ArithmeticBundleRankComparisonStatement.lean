import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelToFlagBundleLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsSameFrameIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedFlagTriangularFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularChangeSpansFlag

set_option autoImplicit false

noncomputable section Comb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam

namespace GlobalTheory.FlagCovQF

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {R : Type} [CommRing R]

/- English proof (translation)
Take `⟨v, hv, e⟩` from `h`. Take `⟨v', hv', e'⟩` from `h'`. Establish `: v = v'` using `funext fun i => Over.OverMorphism.ext ((hv i).trans (hv' i).symm)`. Rewrite using `[← e, ← e', this]`.
-/
private theorem comb_unique {X : Scheme.{0}} {t : SAB H X} {x : Sp R ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {a : Fin m → R}
    {w w' : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x u a w) (h' : IsCombAtG t x u a w') : w = w' := by
  obtain ⟨v, hv, e⟩ := h
  obtain ⟨v', hv', e'⟩ := h'
  have : v = v' := funext fun i => Over.OverMorphism.ext ((hv i).trans (hv' i).symm)
  rw [← e, ← e', this]

/- English proof (translation)
Establish `key (g : EigFrame Z φ x) (a : Fin (Dw.mult τ) → R) (h1 : IsCombAtG Z.t x (g.v τ) a w) : IsCombAtG Z.t x (f.v τ) ((f.co g τ).mulVec a) w`. Rewrite using `[comb_unique h1 ((LieMet.isComb_iff (g.vec τ) a _).2 rfl)]`. Use `(LieMet.isComb_iff (f.vec τ) _ _).2 ?_` and prove the remaining obligations. Simplify using `only [f.vec_eq g τ, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul, mul_comm]`. Conclude with `Finset.sum_comm`.

Establish `e` using `LieMet.tan_ext ((comb_unique ((LieMet.isComb_iff (f.vec τ) _ _).2 rfl) (key g a h1)).trans (comb_unique (key v b h2) ((LieMet.isComb_iff (f.vec τ) _ _).2 rfl)))`. Conclude with `funext (Fintype.linearIndependent_iffₛ.1 (f.linearIndependent_vec τ) _ _ e)`.
-/
private theorem co_mulVec {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f g v : EigFrame Z φ x) (τ : E →+* ℂ)
    {a b : Fin (Dw.mult τ) → R} {w : Sp (DualNumber R) ⟶ Z.t.G.left} (h1 : IsCombAtG Z.t x (g.v τ) a w)
    (h2 : IsCombAtG Z.t x (v.v τ) b w) : (f.co g τ).mulVec a = (f.co v τ).mulVec b := by
  have key (g : EigFrame Z φ x) (a : Fin (Dw.mult τ) → R) (h1 : IsCombAtG Z.t x (g.v τ) a w) :
      IsCombAtG Z.t x (f.v τ) ((f.co g τ).mulVec a) w := by
    rw [comb_unique h1 ((LieMet.isComb_iff (g.vec τ) a _).2 rfl)]
    refine (LieMet.isComb_iff (f.vec τ) _ _).2 ?_
    simp only [f.vec_eq g τ, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul, mul_comm]
    exact Finset.sum_comm
  have e := LieMet.tan_ext ((comb_unique ((LieMet.isComb_iff (f.vec τ) _ _).2 rfl) (key g a h1)).trans
    (comb_unique (key v b h2) ((LieMet.isComb_iff (f.vec τ) _ _).2 rfl)))
  exact funext (Fintype.linearIndependent_iffₛ.1 (f.linearIndependent_vec τ) _ _ e)

end GlobalTheory.FlagCovQF

end Comb

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

noncomputable section

namespace GlobalTheory.FlagCovQF

open CategoryTheory.Limits GlobalTheory.FlagCell GlobalTheory.FlagConnect

/- English proof (translation)
Establish `hp : IsFinite (pullback.snd f y)` using `inferInstance`. Establish `: IsAffine (pullback f y)` using `isAffine_of_isAffineHom (pullback.snd f y)`. Take `⟨φ, hφ⟩` from `Spec.map_surjective ((pullback f y).isoSpec.inv ≫ pullback.snd f y)`. Establish `h4 : φ.hom.Finite`. Rewrite using `[← IsFinite.SpecMap_iff, hφ]`.

Use `infer_instance`. Use `letI : Algebra K Γ(pullback f y, ⊤) := φ.hom.toAlgebra`. Use `haveI : Module.Finite K Γ(pullback f y, ⊤) := h4`. Use `(Set.finite_range fun σ : Γ(pullback f y, ⊤) →ₐ[K] K => Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (pullback f y).isoSpec.inv ≫ pullback.fst f y).subset fun x hx => ?_` and prove the remaining obligations. Set `s : Sp K ⟶ pullback f y` to `pullback.lift x (𝟙 _) (by rw [Category.id_comp]; exact hx)`.

Take `⟨σ, hσ⟩` from `Spec.map_surjective (s ≫ (pullback f y).isoSpec.hom)`. Establish `e : φ ≫ σ = 𝟙 _` using `Spec.map_injective (by`. Rewrite using `[Spec.map_comp, hσ, hφ, Spec.map_id, Category.assoc, Iso.hom_inv_id_assoc]`. Conclude with `pullback.lift_snd _ _ _)`. Use `⟨⟨σ.hom, fun a => congr($e a)⟩, ?_⟩` and prove the remaining obligations.

Use `show Spec.map σ ≫ _ = _`. Rewrite using `[hσ, Category.assoc, Iso.hom_inv_id_assoc]`. Conclude with `pullback.lift_fst _ _ _`.
-/
private theorem finite_points {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (K : Type) [Field K] (y : Sp K ⟶ Y) :
    {x : Sp K ⟶ X | x ≫ f = y}.Finite := by
  have hp : IsFinite (pullback.snd f y) := inferInstance
  have : IsAffine (pullback f y) := isAffine_of_isAffineHom (pullback.snd f y)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback f y).isoSpec.inv ≫ pullback.snd f y)
  have h4 : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  letI : Algebra K Γ(pullback f y, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite K Γ(pullback f y, ⊤) := h4
  refine (Set.finite_range fun σ : Γ(pullback f y, ⊤) →ₐ[K] K =>
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (pullback f y).isoSpec.inv ≫ pullback.fst f y).subset fun x hx => ?_
  let s : Sp K ⟶ pullback f y := pullback.lift x (𝟙 _) (by rw [Category.id_comp]; exact hx)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (s ≫ (pullback f y).isoSpec.hom)
  have e : φ ≫ σ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hσ, hφ, Spec.map_id, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _)
  refine ⟨⟨σ.hom, fun a => congr($e a)⟩, ?_⟩
  show Spec.map σ ≫ _ = _
  rw [hσ, Category.assoc, Iso.hom_inv_id_assoc]
  exact pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)`.
-/
private theorem spMap_trans {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

/- English proof (translation)
The claim follows from `Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)`.
-/
private theorem spMap_fromSpecStalk (X : Scheme.{0}) [IsIntegral X] (x : X) :
    spMap (algebraMap (X.presheaf.stalk x) X.functionField) ≫ X.fromSpecStalk x =
      X.fromSpecStalk (genericPoint X) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)

section Sheaves

open GlobalTheory.Twist (resM resM_resM app_resM)

/- English proof (translation)
Introduce `l`. Proceed by induction on `l using Fin.induction with`. Consider the case `zero`. Establish `z` using `VB.isVB_zero_iff.1 (fl.isVB 0)`. Use `⟨_, (VB.isFrame_freeFrame X (Fin 0)).map_iso ((VB.isVB_zero_iff.1 (VB.isVB_freeModule_fin X 0)).iso z).hom |>.res le_top, fun j => j.elim0⟩` and prove the remaining obligations.

Consider the case `succ i ih`. Take `⟨s, hs, es⟩` from `ih`. Establish `h` using `(VBExt.isFrame_sumElim (S := .mk (fl.step i) (Limits.cokernel.π _) (Limits.cokernel.condition _)) { exact := ShortComplex.exact_cokernel _ } (t := fun _ : Fin 1 => t i) hs (ht i)).comp_equiv finSumFinEquiv.symm`. Use `⟨_, h, fun j => ?_⟩` and prove the remaining obligations. Use `Fin.addCases (m := i) (n := 1) (fun j => ?_) (fun j => ?_) j` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]`. Use `Eq.trans ?_ (es j)` and prove the remaining obligations. Rewrite using `[← fl.step_ι i]`. Both sides reduce to the same expression. Take `rfl : j = 0` from `Subsingleton.elim _ _`.

Conclude with `congrArg (fun z => (fl.ι i.succ).app W (Sum.elim (fun j => (fl.step i).app W (s j)) (fun _ => t i) z)) (finSumFinEquiv_symm_apply_natAdd (m := i) (n := 1) 0)`.
-/
private theorem spans_of_lifts {X : Scheme.{0}} {M : X.Modules} {N : ℕ} (fl : Vert.Flag M N) {W : X.Opens}
    (t : ∀ k : Fin N, Γ(fl.F k.succ, W)) (ht : ∀ k, VB.IsFrame fun _ : Fin 1 => (fl.π k).app W (t k)) :
    Spans fl W fun k => (fl.ι k.succ).app W (t k) := by
  intro l
  induction l using Fin.induction with
  | zero =>
    have z := VB.isVB_zero_iff.1 (fl.isVB 0)
    refine ⟨_, (VB.isFrame_freeFrame X (Fin 0)).map_iso ((VB.isVB_zero_iff.1
      (VB.isVB_freeModule_fin X 0)).iso z).hom |>.res le_top, fun j => j.elim0⟩
  | succ i ih =>
    obtain ⟨s, hs, es⟩ := ih
    have h := (VBExt.isFrame_sumElim (S := .mk (fl.step i) (Limits.cokernel.π _) (Limits.cokernel.condition _))
      { exact := ShortComplex.exact_cokernel _ } (t := fun _ : Fin 1 => t i) hs (ht i)).comp_equiv
      finSumFinEquiv.symm
    refine ⟨_, h, fun j => ?_⟩
    refine Fin.addCases (m := i) (n := 1) (fun j => ?_) (fun j => ?_) j
    · simp only [Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
      refine Eq.trans ?_ (es j)
      rw [← fl.step_ι i]
      rfl
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      exact congrArg (fun z => (fl.ι i.succ).app W (Sum.elim (fun j => (fl.step i).app W (s j)) (fun _ => t i) z))
        (finSumFinEquiv_symm_apply_natAdd (m := i) (n := 1) 0)

/- English proof (translation)
Use `choose W hW hxW t ht using fun k => exists_app_eq_of_epi (fl.π k) ((cc k).e 0) (hcc k)`. Establish `hV (k : Fin N) : U ⊓ Finset.univ.inf W ≤ W k` using `inf_le_right.trans (Finset.inf_le (Finset.mem_univ k))`. Establish `hs (k : Fin N) : (fl.π k).app (U ⊓ Finset.univ.inf W) (resM _ (hV k) (t k)) = resM _ ((hV k).trans (hW k)) ((cc k).e 0)`. Rewrite using `[app_resM, ht, resM_resM]`. Use `⟨U ⊓ Finset.univ.inf W, inf_le_left, fun k => (hV k).trans (hW k), fun k => resM _ (hV k) (t k), ⟨hU, by` and prove the remaining obligations.

Rewrite using `[TopologicalSpace.Opens.coe_finset_inf]`. Simplify using `using hxW⟩, hs, ?_⟩`. Establish `hsp` using `spans_of_lifts fl (fun k => resM _ (hV k) (t k)) fun k => by`. Use `(cc k).isFrame.res ((hV k).trans (hW k))` as an intermediate fact. Rewrite using `[hs]`.

Use `this using 3 with i` and compare the differences between its conclusion and the goal. Conclude with `congrArg _ (Subsingleton.elim _ _)`. Take `⟨s, hs', es⟩` from `hsp (Fin.last N)`. Use `hs'.map_iso (fl.ι (Fin.last N))` as an intermediate fact. Rewrite `this` using `[funext es]`.

Conclude with `this`.
-/
private theorem exists_lifts_isFrame {X : Scheme.{0}} {M : X.Modules} {N : ℕ} (fl : Vert.Flag M N)
    (cc : ∀ k : Fin N, VB.Chart (fl.gr k) 1) {x : X} (hcc : ∀ k, x ∈ (cc k).U) {U : X.Opens} (hU : x ∈ U) :
    ∃ (W : X.Opens) (_ : W ≤ U) (hW : ∀ k, W ≤ (cc k).U) (s : ∀ k : Fin N, Γ(fl.F k.succ, W)), x ∈ W ∧
      (∀ k, (fl.π k).app W (s k) = resM _ (hW k) ((cc k).e 0)) ∧
      VB.IsFrame fun k => (fl.ι k.succ).app W (s k) := by
  choose W hW hxW t ht using fun k => exists_app_eq_of_epi (fl.π k) ((cc k).e 0) (hcc k)
  have hV (k : Fin N) : U ⊓ Finset.univ.inf W ≤ W k :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ k))
  have hs (k : Fin N) : (fl.π k).app (U ⊓ Finset.univ.inf W) (resM _ (hV k) (t k)) =
      resM _ ((hV k).trans (hW k)) ((cc k).e 0) := by
    rw [app_resM, ht, resM_resM]
  refine ⟨U ⊓ Finset.univ.inf W, inf_le_left, fun k => (hV k).trans (hW k), fun k => resM _ (hV k) (t k), ⟨hU, by
    rw [TopologicalSpace.Opens.coe_finset_inf]; simpa using hxW⟩, hs, ?_⟩
  have hsp := spans_of_lifts fl (fun k => resM _ (hV k) (t k)) fun k => by
    have := (cc k).isFrame.res ((hV k).trans (hW k))
    rw [hs]
    convert this using 3 with i
    exact congrArg _ (Subsingleton.elim _ _)
  obtain ⟨s, hs', es⟩ := hsp (Fin.last N)
  have := hs'.map_iso (fl.ι (Fin.last N))
  rw [funext es] at this
  exact this

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use `Eq.trans ?_ (((he.pullback π).basis hV).sum_repr (v j))` and prove the remaining obligations. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[VB.IsFrame.basis_apply]`. Conclude with `congrArg _ (QCoh.res_pullbackSections π E le_rfl hV (e l)).symm`.
-/
private theorem pullCol_toMatrix {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} [E.IsQuasicoherent] {U : B.Opens} {m : ℕ}
    {e : Fin m → Γ(E, U)} (he : VB.IsFrame e) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    (v : Fin m → Γ((Scheme.Modules.pullback π).obj E, V)) :
    pullCol π e hV (((he.pullback π).basis hV).toMatrix v) = v := by
  funext j
  refine Eq.trans ?_ (((he.pullback π).basis hV).sum_repr (v j))
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [VB.IsFrame.basis_apply]
  exact congrArg _ (QCoh.res_pullbackSections π E le_rfl hV (e l)).symm

/- English proof (translation)
Use `(hfl _ (y' ≫ π) (carried π E n fl y' _ rfl)).unique ⟨w, fun a i => ?_⟩ ⟨rfl, carries_carried π E n fl y' _ rfl⟩` and prove the remaining obligations. Take `⟨U, e, V, V', hV, hV', M, M', hy, hy', T, s, s', hT, uT, eT⟩` from `h a`. Establish `hk : ⊤ ≤ (y' ≫ π) ⁻¹ᵁ U` using `fun p hp => hV' (hy' hp)`. Establish `c` using `spans_pullCol_of_carries _ _ _ π ι n E fl y _ w _ (carries_carried π E n fl y _ w) U a e V hV M ⊤ hy hk s`. Establish `c'` using `spans_pullCol_of_carries _ _ _ π ι n E fl y' _ rfl _ (carries_carried π E n fl y' _ rfl) U a e V' hV' M' ⊤ hy' hk s'`.

Set `ρ : K →+* Γ(Sp K, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom`. Establish `hρ (z : Sp K ⟶ Y) (V : Y.Opens) (hz : ⊤ ≤ z ⁻¹ᵁ V) (M : Matrix (Fin (n a)) (Fin (n a)) Γ(Y, V)) : M.map (z.appLE V ⊤ hz).hom = (M.map (TangentOrigin.evalPt z V hz)).map ρ`. Use extensionality with `i j`. Simplify using `[ρ, TangentOrigin.evalPt]`. Establish `c₁` using `Spans.mul_upper _ _ _ _ _ _ (T.map ρ) c (hT.map ρ) (by`.

Use `uT.map ρ` as an intermediate fact. Rewrite using `[RingHom.map_det] at this)` and apply the resulting hypothesis. Establish `e₁ : (fun j => ∑ k, T.map ρ k j • pullCol (y' ≫ π) e hk (M.map (y.appLE V ⊤ hy).hom) k) = pullCol (y' ≫ π) e hk (M'.map (y'.appLE V' ⊤ hy').hom)`. Use function extensionality and compare the values at `j`. Rewrite using `[hρ y' V' hy' M', eT, Matrix.map_mul, ← hρ]`.

Simplify using `only [pullCol, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]`. Rewrite `c₁` using `[e₁]`. Take `⟨φ, hφ⟩` from `carries_carried π E n fl y _ w a i`.

Take `⟨ψ, hψ⟩` from `steps_iso_of_spans_top _ _ _ _ _ _ c₁ c' i`. Conclude with `⟨φ ≪≫ ψ, by rw [Iso.trans_hom, Category.assoc, hψ, hφ]⟩`.
-/
private theorem eq_of_spans {B Y : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (hfl : IsFlagBundle π E n fl)
    {K : Type} [CommRing K] (y y' : Sp K ⟶ Y) (w : y ≫ π = y' ≫ π)
    (h : ∀ a, ∃ (U : B.Opens) (e : Fin (n a) → Γ(E a, U)) (V V' : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (hV' : V' ≤ π ⁻¹ᵁ U)
      (M : Matrix (Fin (n a)) (Fin (n a)) Γ(Y, V)) (M' : Matrix (Fin (n a)) (Fin (n a)) Γ(Y, V'))
      (hy : ⊤ ≤ y ⁻¹ᵁ V) (hy' : ⊤ ≤ y' ⁻¹ᵁ V') (T : Matrix (Fin (n a)) (Fin (n a)) K),
      Spans (fl a) V (pullCol π e hV M) ∧ Spans (fl a) V' (pullCol π e hV' M') ∧ T.BlockTriangular id ∧
        IsUnit T.det ∧ M'.map (TangentOrigin.evalPt y' V' hy') = M.map (TangentOrigin.evalPt y V hy) * T) :
    y = y' := by
  refine (hfl _ (y' ≫ π) (carried π E n fl y' _ rfl)).unique ⟨w, fun a i => ?_⟩
    ⟨rfl, carries_carried π E n fl y' _ rfl⟩
  obtain ⟨U, e, V, V', hV, hV', M, M', hy, hy', T, s, s', hT, uT, eT⟩ := h a
  have hk : ⊤ ≤ (y' ≫ π) ⁻¹ᵁ U := fun p hp => hV' (hy' hp)
  have c := spans_pullCol_of_carries _ _ _ π ι n E fl y _ w _ (carries_carried π E n fl y _ w) U a e V hV M ⊤ hy hk s
  have c' := spans_pullCol_of_carries _ _ _ π ι n E fl y' _ rfl _ (carries_carried π E n fl y' _ rfl) U a e V' hV' M'
    ⊤ hy' hk s'
  let ρ : K →+* Γ(Sp K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hρ (z : Sp K ⟶ Y) (V : Y.Opens) (hz : ⊤ ≤ z ⁻¹ᵁ V) (M : Matrix (Fin (n a)) (Fin (n a)) Γ(Y, V)) :
      M.map (z.appLE V ⊤ hz).hom = (M.map (TangentOrigin.evalPt z V hz)).map ρ := by
    ext i j
    simp [ρ, TangentOrigin.evalPt]
  have c₁ := Spans.mul_upper _ _ _ _ _ _ (T.map ρ) c (hT.map ρ) (by
    have := uT.map ρ
    rwa [RingHom.map_det] at this)
  have e₁ : (fun j => ∑ k, T.map ρ k j • pullCol (y' ≫ π) e hk (M.map (y.appLE V ⊤ hy).hom) k) =
      pullCol (y' ≫ π) e hk (M'.map (y'.appLE V' ⊤ hy').hom) := by
    funext j
    rw [hρ y' V' hy' M', eT, Matrix.map_mul, ← hρ]
    simp only [pullCol, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  rw [e₁] at c₁
  obtain ⟨φ, hφ⟩ := carries_carried π E n fl y _ w a i
  obtain ⟨ψ, hψ⟩ := steps_iso_of_spans_top _ _ _ _ _ _ c₁ c' i
  exact ⟨φ ≪≫ ψ, by rw [Iso.trans_hom, Category.assoc, hψ, hφ]⟩

end Sheaves

section Matrices

variable {L : Type} [Field L] {m : ℕ}

private def Adapted (dual : Bool) (S T A : Matrix (Fin m) (Fin m) L) : Prop :=
  cond dual ((A.transpose.submatrix Fin.revPerm id * T).BlockTriangular id) ((S * A).BlockTriangular id)

/- English proof (translation)
Take `⟨U, rfl⟩ : ∃ U, A' = A * U` from `⟨A⁻¹ * A', (Matrix.mul_nonsing_inv_cancel_left _ _ hA).symm⟩`. Use `⟨U, ?_, isUnit_of_mul_isUnit_right (Matrix.det_mul A U ▸ hA'), rfl⟩` and prove the remaining obligations. Consider the cases of `dual`. Establish `hu : IsUnit (S * A).det` using `by rw [Matrix.det_mul]; exact hS.mul hA`. Use `Matrix.invertibleOfIsUnitDet _ hu` as an intermediate fact.

Establish `h1` using `(Matrix.blockTriangular_inv_of_blockTriangular (M := S * A) h).mul (N := S * (A * U)) h'`. Rewrite `h1` using `[← Matrix.mul_assoc S, Matrix.nonsing_inv_mul_cancel_left _ _ hu]`. Then use the resulting hypothesis. Establish `hu : IsUnit (A.transpose.submatrix Fin.revPerm id * T).det`. Rewrite using `[Matrix.det_mul, Matrix.det_permute, Matrix.det_transpose]`. Conclude with `(((Equiv.Perm.sign _).isUnit.map (Int.castRingHom L)).mul hA).mul hT`.

Use `Matrix.invertibleOfIsUnitDet _ hu` as an intermediate fact. Establish `h1` using `Matrix.BlockTriangular.mul (M := (A * U).transpose.submatrix Fin.revPerm id * T) h' (Matrix.blockTriangular_inv_of_blockTriangular (M := A.transpose.submatrix Fin.revPerm id * T) h)`. Rewrite `h1` using `[Matrix.transpose_mul, ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, Matrix.mul_assoc _ _ T, Matrix.mul_nonsing_inv_cancel_right _ _ hu]`. Introduce `i j hij`. Use `h1 (i := j.rev) (j := i.rev) (Fin.rev_lt_rev.2 hij)` as an intermediate fact.

Simplify using `using this`.
-/
private theorem Adapted.exists_upper {dual : Bool} {S T A A' : Matrix (Fin m) (Fin m) L} (hS : IsUnit S.det)
    (hT : IsUnit T.det) (hA : IsUnit A.det) (hA' : IsUnit A'.det) (h : Adapted dual S T A) (h' : Adapted dual S T A') :
    ∃ U : Matrix (Fin m) (Fin m) L, U.BlockTriangular id ∧ IsUnit U.det ∧ A' = A * U := by
  obtain ⟨U, rfl⟩ : ∃ U, A' = A * U := ⟨A⁻¹ * A', (Matrix.mul_nonsing_inv_cancel_left _ _ hA).symm⟩
  refine ⟨U, ?_, isUnit_of_mul_isUnit_right (Matrix.det_mul A U ▸ hA'), rfl⟩
  cases dual
  · have hu : IsUnit (S * A).det := by rw [Matrix.det_mul]; exact hS.mul hA
    have := Matrix.invertibleOfIsUnitDet _ hu
    have h1 := (Matrix.blockTriangular_inv_of_blockTriangular (M := S * A) h).mul (N := S * (A * U)) h'
    rwa [← Matrix.mul_assoc S, Matrix.nonsing_inv_mul_cancel_left _ _ hu] at h1
  · have hu : IsUnit (A.transpose.submatrix Fin.revPerm id * T).det := by
      rw [Matrix.det_mul, Matrix.det_permute, Matrix.det_transpose]
      exact (((Equiv.Perm.sign _).isUnit.map (Int.castRingHom L)).mul hA).mul hT
    have := Matrix.invertibleOfIsUnitDet _ hu
    have h1 := Matrix.BlockTriangular.mul (M := (A * U).transpose.submatrix Fin.revPerm id * T) h'
      (Matrix.blockTriangular_inv_of_blockTriangular (M := A.transpose.submatrix Fin.revPerm id * T) h)
    rw [Matrix.transpose_mul, ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, Matrix.mul_assoc _ _ T,
      Matrix.mul_nonsing_inv_cancel_right _ _ hu] at h1
    intro i j hij
    have := h1 (i := j.rev) (j := i.rev) (Fin.rev_lt_rev.2 hij)
    simpa using this

/- English proof (translation)
Establish `hu : IsUnit T.det`. Rewrite using `[Matrix.det_of_upperTriangular hT]`. Conclude with `(Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit`. Use `Matrix.invertibleOfIsUnitDet _ hu` as an intermediate fact. Establish `h1` using `hN.mul (Matrix.blockTriangular_inv_of_blockTriangular hT)`.

Rewrite `h1` using `[← e, Matrix.mul_nonsing_inv_cancel_right _ _ hu]`. Then use the resulting hypothesis.
-/
private theorem tri_of_mul {S T N : Matrix (Fin m) (Fin m) L} (hT : T.BlockTriangular id) (hd : ∀ i, T i i ≠ 0)
    (hN : N.BlockTriangular id) (e : S * T = N) : S.BlockTriangular id := by
  have hu : IsUnit T.det := by
    rw [Matrix.det_of_upperTriangular hT]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have := Matrix.invertibleOfIsUnitDet _ hu
  have h1 := hN.mul (Matrix.blockTriangular_inv_of_blockTriangular hT)
  rwa [← e, Matrix.mul_nonsing_inv_cancel_right _ _ hu] at h1

end Matrices

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {R K L : Type} [CommRing R] [Field K] [Field L]

/- English proof (translation)
Establish `key (σ : E →+* ℂ) : IsEigBasis Z φ x σ (Function.update (β` using `fun σ => Fin (Dw.mult σ) → (Sp (DualNumber R) ⟶ Z.t.G.left)) f.v τ u σ) := by`. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Rewrite using `[Function.update_self]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne h]`.

Conclude with `⟨fun i => ⟨f.tan σ i, f.eig σ i⟩, fun w hw => f.basis σ w hw.1 hw.2⟩`. Conclude with `⟨⟨_, fun σ i => ((key σ).1 i).1, fun σ i => ((key σ).1 i).2, fun σ w h1 h2 => (key σ).2 w ⟨h1, h2⟩⟩, Function.update_self τ u f.v⟩`.
-/
private theorem exists_frame_of_basis {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) {τ : E →+* ℂ}
    {u : Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) :
    ∃ g : EigFrame Z φ x, g.v τ = u := by
  have key (σ : E →+* ℂ) : IsEigBasis Z φ x σ (Function.update (β := fun σ => Fin (Dw.mult σ) →
      (Sp (DualNumber R) ⟶ Z.t.G.left)) f.v τ u σ) := by
    by_cases h : σ = τ
    · subst h
      rwa [Function.update_self]
    · rw [Function.update_of_ne h]
      exact ⟨fun i => ⟨f.tan σ i, f.eig σ i⟩, fun w hw => f.basis σ w hw.1 hw.2⟩
  exact ⟨⟨_, fun σ i => ((key σ).1 i).1, fun σ i => ((key σ).1 i).2, fun σ w h1 h2 => (key σ).2 w ⟨h1, h2⟩⟩,
    Function.update_self τ u f.v⟩

/- English proof (translation)
The claim follows from `EigFrame.co_eq fun i => by rw [funext hf, hg i] exact GlobalTheory.GradedPieces.comb_map χ hx.symm (f.co_spec g τ i)`.
-/
private theorem co_map {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {φ' : c.F →+* L} {x' : Sp L ⟶ Z.X} {f g : EigFrame Z φ x}
    {f' g' : EigFrame Z φ' x'} {χ : R →+* L} {τ : E →+* ℂ} (hf : ∀ i, f'.v τ i = spMap (dualMap χ) ≫ f.v τ i)
    (hg : ∀ i, g'.v τ i = spMap (dualMap χ) ≫ g.v τ i) (hx : x' = spMap χ ≫ x) :
    f'.co g' τ = (f.co g τ).map χ :=
  EigFrame.co_eq fun i => by
    rw [funext hf, hg i]
    exact GlobalTheory.GradedPieces.comb_map χ hx.symm (f.co_spec g τ i)

/- English proof (translation)
Substitute `hr` using the available equality. Take `⟨g, rfl⟩` from `exists_frame_of_basis f hu`. Take `⟨f', hf'⟩` from `f.exists_isMap ψ hf.2.1 hf.1`. Take `⟨g', hg'⟩` from `g.exists_isMap ψ hf.2.1 hf.1`. Take `⟨T1, T2⟩` from `hf.co τ hf'`.

Establish `hT : (f'.co v τ).BlockTriangular id` using `fun a i h => T1 a i h`. Establish `down {S : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R} (hS : (S.map ψ).BlockTriangular id) : (S.map χ).BlockTriangular id` using `Matrix.BlockTriangular.map (M := S) χ fun a b hab => hψ ((hS hab).trans (map_zero _).symm)`. Rewrite `h` using `[← funext (hg' τ)]`. Consider the cases of `dual`. Use `choose w cf h1 h2 h4 using h`.

Establish `hC : (Matrix.of fun a i => cf i a).BlockTriangular id` using `fun a i h => h4 i a h`. Establish `e : (f.co g τ * A).map ψ = f'.co v τ * Matrix.of fun a i => cf i a`. Rewrite using `[Matrix.map_mul, ← hf'.co τ hg' hf.1]`. Use extensionality with `a i`. Conclude with `congrFun (co_mulVec f' g' v τ (h1 i) (h2 i)) a`.

Use `down (e ▸ hT.mul hC)` as an intermediate fact. Rewrite `this` using `[Matrix.map_mul, ← co_map (hfL τ) hgL hx]`. Conclude with `this`. Set `A' : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R` to `A.transpose.submatrix Fin.revPerm id`. Establish `e : (A' * g.co f τ).map ψ * f'.co v τ = A'.map ψ * g'.co v τ`.

Rewrite using `[Matrix.map_mul, ← hg'.co τ hf' hf.1, Matrix.mul_assoc, EigFrame.co_mul]`. Establish `hN : (A'.map ψ * g'.co v τ).BlockTriangular id` using `fun a k hk => h a.rev k _ (g'.co_spec v τ k) (by have : (k : ℕ) < a := hk; have := a.2; rw [Fin.val_rev]; omega)`. Use `down (tri_of_mul hT (fun i => T2 i ▸ Units.ne_zero _) hN e)` as an intermediate fact. Rewrite `this` using `[Matrix.map_mul, ← co_map hgL (hfL τ) hx]`. Conclude with `this`.
-/
private theorem adapted_map {ψ : R →+* K} (hψ : Function.Injective ψ) {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {φ' : c.F →+* K}
    {x' : Sp K ⟶ Z.X} {f : EigFrame Z φ x} {v : EigFrame Z φ' x'} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (hf : f.Tri ψ v t) {τ : E →+* ℂ} {m : ℕ} (hr : m = Dw.mult τ)
    {u : Fin m → (Sp (DualNumber R) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) (A : Matrix (Fin m) (Fin m) R)
    (dual : Bool)
    (h : ∀ i : Fin m, cond dual
      (∀ (k : Fin (Dw.mult τ)) (d : Fin m → K), IsCombAtG Z.t x' (fun b => spMap (dualMap ψ) ≫ u b) d (v.v τ k) →
        (k : ℕ) + i + 1 < m → ∑ b, ψ (A b i) * d b = 0)
      (∃ (w : Sp (DualNumber K) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → K),
        IsCombAtG Z.t x' (fun b => spMap (dualMap ψ) ≫ u b) (fun b => ψ (A b i)) w ∧ IsCombAtG Z.t x' (v.v τ) cf w ∧
          ∀ k, Fin.cast hr i < k → cf k = 0))
    (χ : R →+* L) {φL : c.F →+* L} {xL : Sp L ⟶ Z.X} (hx : xL = spMap χ ≫ x) {fL gL : EigFrame Z φL xL}
    (hfL : f.IsMap χ fL) (hgL : ∀ b, gL.v τ (Fin.cast hr b) = spMap (dualMap χ) ≫ u b) :
    Adapted dual ((fL.co gL τ).submatrix (Fin.cast hr) (Fin.cast hr))
      ((gL.co fL τ).submatrix (Fin.cast hr) (Fin.cast hr)) (A.map χ) := by
  subst hr
  obtain ⟨g, rfl⟩ := exists_frame_of_basis f hu
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨g', hg'⟩ := g.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨T1, T2⟩ := hf.co τ hf'
  have hT : (f'.co v τ).BlockTriangular id := fun a i h => T1 a i h
  have down {S : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R} (hS : (S.map ψ).BlockTriangular id) :
      (S.map χ).BlockTriangular id :=
    Matrix.BlockTriangular.map (M := S) χ fun a b hab => hψ ((hS hab).trans (map_zero _).symm)
  rw [← funext (hg' τ)] at h
  cases dual
  · choose w cf h1 h2 h4 using h
    have hC : (Matrix.of fun a i => cf i a).BlockTriangular id := fun a i h => h4 i a h
    have e : (f.co g τ * A).map ψ = f'.co v τ * Matrix.of fun a i => cf i a := by
      rw [Matrix.map_mul, ← hf'.co τ hg' hf.1]
      ext a i
      exact congrFun (co_mulVec f' g' v τ (h1 i) (h2 i)) a
    have := down (e ▸ hT.mul hC)
    rw [Matrix.map_mul, ← co_map (hfL τ) hgL hx] at this
    exact this
  · let A' : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R := A.transpose.submatrix Fin.revPerm id
    have e : (A' * g.co f τ).map ψ * f'.co v τ = A'.map ψ * g'.co v τ := by
      rw [Matrix.map_mul, ← hg'.co τ hf' hf.1, Matrix.mul_assoc, EigFrame.co_mul]
    have hN : (A'.map ψ * g'.co v τ).BlockTriangular id := fun a k hk =>
      h a.rev k _ (g'.co_spec v τ k) (by have : (k : ℕ) < a := hk; have := a.2; rw [Fin.val_rev]; omega)
    have := down (tri_of_mul hT (fun i => T2 i ▸ Units.ne_zero _) hN e)
    rw [Matrix.map_mul, ← co_map hgL (hfL τ) hx] at this
    exact this

/- English proof (translation)
Substitute `hr` using the available equality. Take `⟨g, rfl⟩` from `exists_frame_of_basis f hu`. Conclude with `⟨g, fun _ => rfl⟩`.
-/
private theorem exists_frame_cast {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) {τ : E →+* ℂ} {m : ℕ}
    (hr : m = Dw.mult τ) {u : Fin m → (Sp (DualNumber R) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) :
    ∃ g : EigFrame Z φ x, ∀ b, g.v τ (Fin.cast hr b) = u b := by
  subst hr
  obtain ⟨g, rfl⟩ := exists_frame_of_basis f hu
  exact ⟨g, fun _ => rfl⟩

/- English proof (translation)
Substitute `hr` using the available equality. Conclude with `f.isUnit_det_co g τ`.
-/
private theorem isUnit_det_co_cast {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f g : EigFrame Z φ x) {τ : E →+* ℂ} {m : ℕ}
    (hr : m = Dw.mult τ) : IsUnit ((f.co g τ).submatrix (Fin.cast hr) (Fin.cast hr)).det := by
  subst hr
  exact f.isUnit_det_co g τ

variable {F : Type} [Field F] {e : F ≃+* c.F}

/- English proof (translation)
Take `⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : F →+* C.Y.X.presheaf.stalk y, stalkPt C.Y y ≫ C.Y.str = spMap ψ₀` from `⟨(Spec.preimage (stalkPt C.Y y ≫ C.Y.str)).hom, (Spec.map_preimage _).symm⟩`. Establish `hg : genericPt C.Y ≫ C.Y.str = spMap (algebraMap F C.Y.Fn)` using `(GlobalTheory.FlagBundle.ratOf C.Y).pt_s`. Establish `e1 : (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField).comp ψ₀ = algebraMap F C.Y.Fn`. Use `EigLoc.spMap_inj ?_` and prove the remaining obligations. Rewrite using `[spMap_trans, ← hψ₀, ← hg, ← Category.assoc]`.

Conclude with `congrArg (· ≫ C.Y.str) (spMap_fromSpecStalk C.Y.X y)`. Conclude with `⟨ψ₀, hψ₀, RingHom.ext fun a => IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField ((RingHom.congr_fun h.2.1 a).symm.trans (RingHom.congr_fun e1 (e.symm a)).symm)⟩`.
-/
private theorem exists_const (C : FlagCpt Z e) {y : C.Y.X} {φy : c.F →+* C.Y.X.presheaf.stalk y}
    {fy : EigFrame Z φy (stalkPt C.Y y ≫ C.π ≫ genι Z)} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (h : fy.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t) :
    ∃ ψ₀ : F →+* C.Y.X.presheaf.stalk y, stalkPt C.Y y ≫ C.Y.str = spMap ψ₀ ∧ φy = ψ₀.comp e.symm.toRingHom := by
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : F →+* C.Y.X.presheaf.stalk y, stalkPt C.Y y ≫ C.Y.str = spMap ψ₀ :=
    ⟨(Spec.preimage (stalkPt C.Y y ≫ C.Y.str)).hom, (Spec.map_preimage _).symm⟩
  have hg : genericPt C.Y ≫ C.Y.str = spMap (algebraMap F C.Y.Fn) := (GlobalTheory.FlagBundle.ratOf C.Y).pt_s
  have e1 : (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField).comp ψ₀ = algebraMap F C.Y.Fn := by
    refine EigLoc.spMap_inj ?_
    rw [spMap_trans, ← hψ₀, ← hg, ← Category.assoc]
    exact congrArg (· ≫ C.Y.str) (spMap_fromSpecStalk C.Y.X y)
  exact ⟨ψ₀, hψ₀, RingHom.ext fun a => IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField
    ((RingHom.congr_fun h.2.1 a).symm.trans (RingHom.congr_fun e1 (e.symm a)).symm)⟩

/- English proof (translation)
Take `⟨ψ₀, h1, rfl⟩` from `exists_const C h`. Use `hu.1 U f hf R b hb (ρ.comp ψ₀) ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc b, hρ, spMap_trans, ← h1, Category.assoc, Category.assoc, C.π_str]`.
-/
private theorem isEigBasis_of_stalk (C : FlagCpt Z e) {y : C.Y.X} {φy : c.F →+* C.Y.X.presheaf.stalk y}
    {fy : EigFrame Z φy (stalkPt C.Y y ≫ C.π ≫ genι Z)} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (h : fy.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t) {X W : Scheme.{0}} {jB : W ⟶ X}
    {πB : W ⟶ gen Z} {M : X.Modules} {r : ℕ} {τ : E →+* ℂ} {dual : Bool} {u : FrAssign Z M r jB}
    (hu : IsLieFrames Z e jB πB M r τ dual u) {U : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f)
    (b : Sp R ⟶ W) (hb : ⊤ ≤ (b ≫ jB) ⁻¹ᵁ U) (ρ : C.Y.X.presheaf.stalk y →+* R)
    (hρ : b ≫ πB = spMap ρ ≫ stalkPt C.Y y ≫ C.π) :
    IsEigBasis Z (ρ.comp φy) (b ≫ πB ≫ genι Z) τ (u U f hf R b hb) := by
  obtain ⟨ψ₀, h1, rfl⟩ := exists_const C h
  refine hu.1 U f hf R b hb (ρ.comp ψ₀) ?_
  rw [← Category.assoc b, hρ, spMap_trans, ← h1, Category.assoc, Category.assoc, C.π_str]

/- English proof (translation)
Establish `hs : (algebraMap (G.presheaf.stalk x) G.functionField).comp ρ = φ.comp (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField)`. Use `EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)` and prove the remaining obligations. Rewrite using `[spMap_trans, spMap_trans, Category.assoc, Category.assoc, spMap_fromSpecStalk, ← φs, ← spMap_fromSpecStalk G x, Category.assoc]`. Conclude with `congrArg _ hρ`. Establish `hK : xK = spMap φ ≫ genericPt C.Y ≫ C.π ≫ genι Z`.

Rewrite using `[hxK, ← Category.assoc, φs, Category.assoc]`. Both sides reduce to the same expression. Take `⟨f, hf⟩` from `fy.exists_isMap ρ rfl (x' := xR) (by rw [hxR, ← Category.assoc (spMap _), hρ, Category.assoc])`. Take `⟨v, hv⟩` from `C.f0.exists_isMap φ rfl hK`. Use `⟨f, v, hf, hv, by rw [hxK, hxR, ← Category.assoc (spMap _), spMap_fromSpecStalk], ?_, fun τ i => ?_⟩` and prove the remaining obligations.

Rewrite using `[← RingHom.comp_assoc, hs, RingHom.comp_assoc]`. Conclude with `congrArg _ h.2.1`. Take `⟨cf, c1, c2, c3⟩` from `h.2.2 τ i`. Use `⟨fun k => φ (cf k), congrArg φ c1, fun k hk => (congrArg φ (c2 k hk)).trans (map_zero _), ?_⟩` and prove the remaining obligations. Use `GlobalTheory.GradedPieces.comb_map φ hK.symm c3` as an intermediate fact.

Simplify using `only [GlobalTheory.GradedPieces.dual_comp] at this`. Simplify using `only [hv τ, hf τ, GlobalTheory.GradedPieces.dual_comp, hs]`. Conclude with `this`.
-/
private theorem tri_of_isMap (C : FlagCpt Z e) {G : Scheme.{0}} [IsIntegral G] (p : G ⟶ C.Y.X) (φ : C.Y.Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ p = spMap φ ≫ C.Y.X.fromSpecStalk (genericPoint C.Y.X)) (x : G)
    {y : C.Y.X} {φy : c.F →+* C.Y.X.presheaf.stalk y}
    {fy : EigFrame Z φy (stalkPt C.Y y ≫ C.π ≫ genι Z)} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (h : fy.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t)
    (ρ : C.Y.X.presheaf.stalk y →+* G.presheaf.stalk x) (hρ : spMap ρ ≫ stalkPt C.Y y = G.fromSpecStalk x ≫ p)
    {xR : Sp (G.presheaf.stalk x) ⟶ Z.X} (hxR : xR = G.fromSpecStalk x ≫ p ≫ C.π ≫ genι Z)
    {xK : Sp G.functionField ⟶ Z.X} (hxK : xK = G.fromSpecStalk (genericPoint G) ≫ p ≫ C.π ≫ genι Z) :
    ∃ (f : EigFrame Z (ρ.comp φy) xR) (v : EigFrame Z (φ.comp (constF e C.Y)) xK), fy.IsMap ρ f ∧ C.f0.IsMap φ v ∧
      f.Tri (algebraMap (G.presheaf.stalk x) G.functionField) v (fun τ i => Units.map φ.toMonoidHom (t τ i)) := by
  have hs : (algebraMap (G.presheaf.stalk x) G.functionField).comp ρ =
      φ.comp (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
    rw [spMap_trans, spMap_trans, Category.assoc, Category.assoc, spMap_fromSpecStalk, ← φs,
      ← spMap_fromSpecStalk G x, Category.assoc]
    exact congrArg _ hρ
  have hK : xK = spMap φ ≫ genericPt C.Y ≫ C.π ≫ genι Z := by
    rw [hxK, ← Category.assoc, φs, Category.assoc]; rfl
  obtain ⟨f, hf⟩ := fy.exists_isMap ρ rfl (x' := xR) (by rw [hxR, ← Category.assoc (spMap _), hρ, Category.assoc])
  obtain ⟨v, hv⟩ := C.f0.exists_isMap φ rfl hK
  refine ⟨f, v, hf, hv, by rw [hxK, hxR, ← Category.assoc (spMap _), spMap_fromSpecStalk], ?_, fun τ i => ?_⟩
  · rw [← RingHom.comp_assoc, hs, RingHom.comp_assoc]
    exact congrArg _ h.2.1
  obtain ⟨cf, c1, c2, c3⟩ := h.2.2 τ i
  refine ⟨fun k => φ (cf k), congrArg φ c1, fun k hk => (congrArg φ (c2 k hk)).trans (map_zero _), ?_⟩
  have := GlobalTheory.GradedPieces.comb_map φ hK.symm c3
  simp only [GlobalTheory.GradedPieces.dual_comp] at this
  simp only [hv τ, hf τ, GlobalTheory.GradedPieces.dual_comp, hs]
  exact this

end Frames

section Points

variable {D : D7} {O : Setup D} {c : O.s.Comp} {Bs : Scheme.{0}} {E : D.what₂.Tau × Bool → Bs.Modules}
  (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) {Bg : Scheme.{0}} {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen O.s.T.Z}
  {u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB} {Y₀ : Scheme.{0}} {π₀ : Y₀ ⟶ Bs}
  {fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a)}
  {G : Scheme.{0}} [IsIntegral G] {j : G ⟶ Y₀} {πG : G ⟶ (O.var c).X} {φ : (O.var c).Fn →+* G.functionField}
  {jG : G ⟶ Bg}

/- English proof (translation)
Establish `hqc` using `(hE a).isQuasicoherent`. Use `choose r c3 using c3`. Take `⟨x, χ, hx, rfl⟩ : ∃ (x : G) (χ : G.presheaf.stalk x →+* L), z (IsLocalRing.closedPoint L) = x ∧ z = spMap χ ≫ G.fromSpecStalk x` from `⟨_, (Scheme.stalkClosedPointTo z).hom, rfl, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm⟩`. Rewrite `hzy` using `[hx]`. Establish `hV : π₀ (j x) ∈ V`.

Use `hb (x := IsLocalRing.closedPoint L) trivial` as an intermediate fact. Rewrite `this` using `[← hzb, Category.assoc (_ ≫ _), c1]`. Rewrite using `[← hx]`. Conclude with `this`. Substitute `hzy hzb` using the available equality.

Set `ρ` to `(πG.stalkMap x).hom`. Establish `hρ : spMap ρ ≫ stalkPt (O.Φ.C c).Y (πG x) = G.fromSpecStalk x ≫ πG` using `Scheme.SpecMap_stalkMap_fromSpecStalk πG`. Choose the witnesses or unpack the hypotheses as in `rfl : κ = χ.comp ρ := by`. Use `EigLoc.spMap_inj ((cancel_mono ((O.Φ.C c).Y.X.fromSpecStalk (πG x))).1 (hzκ.symm.trans ?_))` and prove the remaining obligations. Rewrite using `[spMap_trans, Category.assoc, Category.assoc]`.

Conclude with `congrArg _ hρ.symm`. Take `⟨cc, hcc⟩ : ∃ cc : ∀ k, (((fl₀ a).root k).pull j).ι, ∀ k, j x ∈ (cc k PUnit.unit).U` from `by choose U e hU he using fun k => (fl₀ a).isVB_gr k (j x)`. Conclude with `⟨fun k _ => ⟨U k, e k, he k⟩, hU⟩`. Take `⟨W, hWV, hW, s, hxW, hs, hfr⟩` from `exists_lifts_isFrame (fl₀ a) (fun k => cc k PUnit.unit) hcc (U := π₀ ⁻¹ᵁ V) hV`. Establish `hsp` using `spans_of_lifts (fl₀ a) s fun k => by`.

Use `(cc k PUnit.unit).isFrame.res (hW k)` as an intermediate fact. Rewrite using `[hs]`. Use `this using 3 with i` and compare the differences between its conclusion and the goal. Conclude with `congrArg _ (Subsingleton.elim _ _)`. Set `ψ` to `algebraMap (G.presheaf.stalk x) G.functionField`.

Establish `hψ : Function.Injective ψ` using `IsFractionRing.injective _ _`. Establish `hg : FlagCov.genPt G = spMap ψ ≫ G.fromSpecStalk x` using `(spMap_fromSpecStalk G x).symm`. Establish `hst {U : G.Opens} (hU : x ∈ U) : ⊤ ≤ G.fromSpecStalk x ⁻¹ᵁ U` using `fun w _ => by`. Establish `: G.fromSpecStalk x w ∈ Set.range (G.fromSpecStalk x)` using `⟨w, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`.

Conclude with `Specializes.mem_open (x := G.fromSpecStalk x w) this U.isOpen hU`. Establish `hRW : ⊤ ≤ (G.fromSpecStalk x ≫ j) ⁻¹ᵁ W` using `hst (U := j ⁻¹ᵁ W) hxW`. Establish `hRV : ⊤ ≤ ((G.fromSpecStalk x ≫ jG) ≫ jB) ⁻¹ᵁ V`. Rewrite using `[Category.assoc, c1]`. Conclude with `hst (U := (j ≫ π₀) ⁻¹ᵁ V) hV`.

Establish `hW' {K : Type} [CommRing K] (σ : G.presheaf.stalk x →+* K) : ⊤ ≤ ((spMap σ ≫ G.fromSpecStalk x) ≫ j) ⁻¹ᵁ W`. Rewrite using `[Category.assoc]`. Conclude with `fun w _ => hRW (x := spMap σ w) trivial`. Establish `hV' {K : Type} [CommRing K] (σ : G.presheaf.stalk x →+* K) : ⊤ ≤ (((spMap σ ≫ G.fromSpecStalk x) ≫ jG) ≫ jB) ⁻¹ᵁ V`. Rewrite using `[Category.assoc (spMap σ), Category.assoc (spMap σ)]`.

Conclude with `fun w _ => hRV (x := spMap σ w) trivial`. Establish `hKW : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W` using `hg ▸ hW' ψ`. Establish `hKV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V` using `hg ▸ hV' ψ`. Take `⟨fR, v, e1, e2, e3⟩` from `tri_of_isMap (O.Φ.C c) πG φ φs x hy ρ hρ (xR := (G.fromSpecStalk x ≫ jG) ≫ πB ≫ genι O.s.T.Z) (by rw [Category.assoc, ← Category.assoc jG, c2, Category.assoc]) (xK := FlagCov.genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z) (by rw [← Category.assoc jG, c2, Category.assoc]; rfl)`. Establish `hu` using `isEigBasis_of_stalk (O.Φ.C c) hy frB hf (G.fromSpecStalk x ≫ jG) hRV ρ ((Category.assoc _ _ _).trans ((congrArg _ c2).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (O.Φ.C c).π) hρ.symm).trans (Category.assoc _ _ _)))))`.

Establish `hu' {K : Type} [CommRing K] (σ : G.presheaf.stalk x →+* K) (w : Sp K ⟶ Bg) (hw : ⊤ ≤ (w ≫ jB) ⁻¹ᵁ V) (e : w = spMap σ ≫ G.fromSpecStalk x ≫ jG) : u a V f hf K w hw = fun b => spMap (dualMap σ) ≫ u a V f hf _ (G.fromSpecStalk x ≫ jG) hRV b`. Substitute `e` using the available equality. Conclude with `funext (frB.2.2 V f hf _ _ σ _ hRV hw)`. Set `A₀` to `((hf.pullback π₀).basis hWV).toMatrix fun k => ((fl₀ a).ι k.succ).app W (s k)`. Establish `hA₀ : IsUnit A₀.det`.

Use `((hf.pullback π₀).detUnit hfr hWV le_rfl).isUnit` as an intermediate fact. Simplify `this` using `only [IsFrame.val_detUnit, Twist.resM_self, Module.Basis.det_apply]`. Set `A` to `A₀.map (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW)`. Establish `hev {K : Type} [CommRing K] (σ : G.presheaf.stalk x →+* K) (w : Sp K ⟶ Y₀) (hw : ⊤ ≤ w ⁻¹ᵁ W) (e : w = spMap σ ≫ G.fromSpecStalk x ≫ j) (g) : TangentOrigin.evalPt w W hw g = σ (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW g)`. Substitute `e` using the available equality.

Conclude with `TangentOrigin.evalPt_spMap_comp σ _ W hRW hw g`. Establish `hevK (k) : (fun b => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hKW (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι k.succ).app W (s k)) b)) = fun b => ψ (A b k)`. Use function extensionality and compare the values at `fun b => hev ψ _ _ (by rw [hg, Category.assoc]) _`. Establish `huK` using `hu' ψ _ hKV (by rw [hg, Category.assoc])`. Establish `hsec (k)` using `c3 k (cc k) V f hf W (hW k) hWV (s k) (hs k) hKW hKV`.

Establish `hv : (fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) k) = v.v (embB D a)` using `(funext (e2 _)).symm`. Use `⟨W, hWV, A₀, hW' χ, by rw [pullCol_toMatrix π₀ hf]; exact hsp, ?_, ?_⟩` and prove the remaining obligations. Use `hA₀.map (TangentOrigin.evalPt _ W (hW' χ))` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Establish `eA : A₀.map (TangentOrigin.evalPt _ W (hW' χ)) = A.map χ` using `Matrix.ext fun i k => hev χ _ _ (Category.assoc _ _ _) _`.

Rewrite using `[eA]`. Use `adapted_map hψ e3 hr hu A _ (fun k => ?_) χ (by simp only [Category.assoc]) (fun τ i => by rw [hfL, e1, GlobalTheory.GradedPieces.dual_comp]) (fun k => (hgL k).trans (congrFun (hu' χ _ hb (Category.assoc _ _ _)) k))` and prove the remaining obligations. Take `⟨τ, _ | _⟩` from `a`. Introduce `k' d hd`. Use `(hsec k k' d (by rw [huK, hv]; exact hd)).1` as an intermediate fact.

Simplify `this` using `only [fun b => congrFun (hevK k) b]`. Use `hsec k` as an intermediate fact. Simplify using `only [cond_true] at this`. Rewrite `this` using `[huK, hv, hevK]`. Take `⟨w, cf, h1, h2, -, h4⟩` from `this`.

Conclude with `⟨w, cf, h1, h2, h4⟩`.
-/
private theorem exists_adapted (c1 : jG ≫ jB = j ≫ π₀) (c2 : jG ≫ πB = πG ≫ (O.Φ.C c).π)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (a : D.what₂.Tau × Bool) (frB : IsLieFrames O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (!a.2) (u a))
    (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a))
    (c3 : ∀ i, ∃ r, GlobalTheory.FlagCov.IsFrameSec hE jB πB u π₀ fl₀ j φ jG a i hr r)
    {V : Bs.Opens} {f : Fin (rkB D.what₂.Tau O.N O.j a) → Γ(E a, V)} (hf : VB.IsFrame f)
    {y : (O.Φ.C c).Y.X} {φy : _ →+* (O.Φ.C c).Y.X.presheaf.stalk y}
    {fy : EigFrame O.s.T.Z φy (stalkPt (O.Φ.C c).Y y ≫ (O.Φ.C c).π ≫ genι O.s.T.Z)}
    {tY : ∀ τ, Fin (O.S.Dw.mult τ) → (O.Φ.C c).Y.Fnˣ}
    (hy : fy.Tri (algebraMap ((O.Φ.C c).Y.X.presheaf.stalk y) (O.Φ.C c).Y.X.functionField) (O.Φ.C c).f0 tY)
    {L : Type} [Field L] (b : Sp L ⟶ Bg) (hb : ⊤ ≤ (b ≫ jB) ⁻¹ᵁ V) (κ : (O.Φ.C c).Y.X.presheaf.stalk y →+* L)
    {φL : _ →+* L} {fL gL : EigFrame O.s.T.Z φL (b ≫ πB ≫ genι O.s.T.Z)} (hfL : fy.IsMap κ fL)
    (hgL : ∀ k, gL.v (embB D a) (Fin.cast hr k) = u a V f hf L b hb k)
    (z : Sp L ⟶ G) (hzb : z ≫ jG = b) (hzy : πG (z (IsLocalRing.closedPoint L)) = y)
    (hzκ : z ≫ πG = spMap κ ≫ stalkPt (O.Φ.C c).Y y) :
    ∃ (W : Y₀.Opens) (hW : W ≤ π₀ ⁻¹ᵁ V) (M : Matrix _ _ Γ(Y₀, W)) (hz : ⊤ ≤ (z ≫ j) ⁻¹ᵁ W),
      Spans (fl₀ a) W (pullCol π₀ f hW M) ∧ IsUnit (M.map (TangentOrigin.evalPt (z ≫ j) W hz)).det ∧
      Adapted (!a.2) ((fL.co gL (embB D a)).submatrix (Fin.cast hr) (Fin.cast hr))
        ((gL.co fL (embB D a)).submatrix (Fin.cast hr) (Fin.cast hr)) (M.map (TangentOrigin.evalPt (z ≫ j) W hz)) := by
  have hqc := (hE a).isQuasicoherent
  choose r c3 using c3
  obtain ⟨x, χ, hx, rfl⟩ : ∃ (x : G) (χ : G.presheaf.stalk x →+* L), z (IsLocalRing.closedPoint L) = x ∧
      z = spMap χ ≫ G.fromSpecStalk x :=
    ⟨_, (Scheme.stalkClosedPointTo z).hom, rfl, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm⟩
  rw [hx] at hzy
  have hV : π₀ (j x) ∈ V := by
    have := hb (x := IsLocalRing.closedPoint L) trivial
    rw [← hzb, Category.assoc (_ ≫ _), c1] at this
    rw [← hx]
    exact this
  subst hzy hzb
  let ρ := (πG.stalkMap x).hom
  have hρ : spMap ρ ≫ stalkPt (O.Φ.C c).Y (πG x) = G.fromSpecStalk x ≫ πG := Scheme.SpecMap_stalkMap_fromSpecStalk πG
  obtain rfl : κ = χ.comp ρ := by
    refine EigLoc.spMap_inj ((cancel_mono ((O.Φ.C c).Y.X.fromSpecStalk (πG x))).1 (hzκ.symm.trans ?_))
    rw [spMap_trans, Category.assoc, Category.assoc]
    exact congrArg _ hρ.symm
  obtain ⟨cc, hcc⟩ : ∃ cc : ∀ k, (((fl₀ a).root k).pull j).ι, ∀ k, j x ∈ (cc k PUnit.unit).U := by
    choose U e hU he using fun k => (fl₀ a).isVB_gr k (j x)
    exact ⟨fun k _ => ⟨U k, e k, he k⟩, hU⟩
  obtain ⟨W, hWV, hW, s, hxW, hs, hfr⟩ := exists_lifts_isFrame (fl₀ a) (fun k => cc k PUnit.unit) hcc
    (U := π₀ ⁻¹ᵁ V) hV
  have hsp := spans_of_lifts (fl₀ a) s fun k => by
    have := (cc k PUnit.unit).isFrame.res (hW k)
    rw [hs]
    convert this using 3 with i
    exact congrArg _ (Subsingleton.elim _ _)
  let ψ := algebraMap (G.presheaf.stalk x) G.functionField
  have hψ : Function.Injective ψ := IsFractionRing.injective _ _
  have hg : FlagCov.genPt G = spMap ψ ≫ G.fromSpecStalk x := (spMap_fromSpecStalk G x).symm
  have hst {U : G.Opens} (hU : x ∈ U) : ⊤ ≤ G.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : G.fromSpecStalk x w ∈ Set.range (G.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := G.fromSpecStalk x w) this U.isOpen hU
  have hRW : ⊤ ≤ (G.fromSpecStalk x ≫ j) ⁻¹ᵁ W := hst (U := j ⁻¹ᵁ W) hxW
  have hRV : ⊤ ≤ ((G.fromSpecStalk x ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, c1]

    exact hst (U := (j ≫ π₀) ⁻¹ᵁ V) hV
  have hW' {K : Type} [CommRing K] (σ : G.presheaf.stalk x →+* K) : ⊤ ≤ ((spMap σ ≫ G.fromSpecStalk x) ≫ j) ⁻¹ᵁ W := by
    rw [Category.assoc]
    exact fun w _ => hRW (x := spMap σ w) trivial
  have hV' {K : Type} [CommRing K] (σ : G.presheaf.stalk x →+* K) :
      ⊤ ≤ (((spMap σ ≫ G.fromSpecStalk x) ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc (spMap σ), Category.assoc (spMap σ)]
    exact fun w _ => hRV (x := spMap σ w) trivial
  have hKW : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W := hg ▸ hW' ψ
  have hKV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V := hg ▸ hV' ψ
  obtain ⟨fR, v, e1, e2, e3⟩ := tri_of_isMap (O.Φ.C c) πG φ φs x hy ρ hρ
    (xR := (G.fromSpecStalk x ≫ jG) ≫ πB ≫ genι O.s.T.Z)
    (by rw [Category.assoc, ← Category.assoc jG, c2, Category.assoc])
    (xK := FlagCov.genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z) (by rw [← Category.assoc jG, c2, Category.assoc]; rfl)
  have hu := isEigBasis_of_stalk (O.Φ.C c) hy frB hf (G.fromSpecStalk x ≫ jG) hRV ρ
    ((Category.assoc _ _ _).trans ((congrArg _ c2).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (O.Φ.C c).π) hρ.symm).trans (Category.assoc _ _ _)))))
  have hu' {K : Type} [CommRing K] (σ : G.presheaf.stalk x →+* K) (w : Sp K ⟶ Bg) (hw : ⊤ ≤ (w ≫ jB) ⁻¹ᵁ V)
      (e : w = spMap σ ≫ G.fromSpecStalk x ≫ jG) :
      u a V f hf K w hw = fun b => spMap (dualMap σ) ≫ u a V f hf _ (G.fromSpecStalk x ≫ jG) hRV b := by
    subst e
    exact funext (frB.2.2 V f hf _ _ σ _ hRV hw)
  let A₀ := ((hf.pullback π₀).basis hWV).toMatrix fun k => ((fl₀ a).ι k.succ).app W (s k)
  have hA₀ : IsUnit A₀.det := by
    have := ((hf.pullback π₀).detUnit hfr hWV le_rfl).isUnit
    simpa only [IsFrame.val_detUnit, Twist.resM_self, Module.Basis.det_apply] using this
  let A := A₀.map (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW)
  have hev {K : Type} [CommRing K] (σ : G.presheaf.stalk x →+* K) (w : Sp K ⟶ Y₀) (hw : ⊤ ≤ w ⁻¹ᵁ W)
      (e : w = spMap σ ≫ G.fromSpecStalk x ≫ j) (g) :
      TangentOrigin.evalPt w W hw g = σ (TangentOrigin.evalPt (G.fromSpecStalk x ≫ j) W hRW g) := by
    subst e
    exact TangentOrigin.evalPt_spMap_comp σ _ W hRW hw g
  have hevK (k) : (fun b => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hKW
      (((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι k.succ).app W (s k)) b)) = fun b => ψ (A b k) :=
    funext fun b => hev ψ _ _ (by rw [hg, Category.assoc]) _
  have huK := hu' ψ _ hKV (by rw [hg, Category.assoc])
  have hsec (k) := c3 k (cc k) V f hf W (hW k) hWV (s k) (hs k) hKW hKV
  have hv : (fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) k) = v.v (embB D a) := (funext (e2 _)).symm
  refine ⟨W, hWV, A₀, hW' χ, by rw [pullCol_toMatrix π₀ hf]; exact hsp, ?_, ?_⟩
  · have := hA₀.map (TangentOrigin.evalPt _ W (hW' χ))
    rwa [RingHom.map_det] at this
  have eA : A₀.map (TangentOrigin.evalPt _ W (hW' χ)) = A.map χ :=
    Matrix.ext fun i k => hev χ _ _ (Category.assoc _ _ _) _
  rw [eA]
  refine adapted_map hψ e3 hr hu A _ (fun k => ?_) χ (by simp only [Category.assoc])
    (fun τ i => by rw [hfL, e1, GlobalTheory.GradedPieces.dual_comp])
    (fun k => (hgL k).trans (congrFun (hu' χ _ hb (Category.assoc _ _ _)) k))
  obtain ⟨τ, _ | _⟩ := a
  · intro k' d hd
    have := (hsec k k' d (by rw [huK, hv]; exact hd)).1
    simpa only [fun b => congrFun (hevK k) b] using this
  · have := hsec k
    simp only [cond_true] at this
    rw [huK, hv, hevK] at this
    obtain ⟨w, cf, h1, h2, -, h4⟩ := this
    exact ⟨w, cf, h1, h2, h4⟩

/- English proof (translation)
Use `eq_of_spans π₀ E _ fl₀ hfb _ _ (by rw [Category.assoc, Category.assoc, ← c1, ← Category.assoc, ← e₁, Category.assoc]) fun a => ?_` and prove the remaining obligations. Take `⟨y, κ, hy, hκ⟩ : ∃ (y : (O.Φ.C c).Y.X) (κ : (O.Φ.C c).Y.X.presheaf.stalk y →+* L), (z ≫ πG) (IsLocalRing.closedPoint L) = y ∧ z ≫ πG = spMap κ ≫ stalkPt (O.Φ.C c).Y y` from `⟨_, (Scheme.stalkClosedPointTo (z ≫ πG)).hom, rfl, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).symm⟩`. Take `⟨φy, fy, t, h1, -⟩` from `(O.Φ.C c).gr_spec y`. Take `⟨V, f, hV, hf⟩` from `hE a (((z ≫ jG) ≫ jB) (IsLocalRing.closedPoint L))`. Establish `hb : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V` using `fun p _ => by`.

Take `rfl : p = IsLocalRing.closedPoint L` from `Subsingleton.elim (α := PrimeSpectrum L) _ _`. Conclude with `hV`. Establish `hρ : (z ≫ jG) ≫ πB = spMap κ ≫ stalkPt (O.Φ.C c).Y y ≫ (O.Φ.C c).π`. Rewrite using `[Category.assoc, c2, ← Category.assoc, hκ, Category.assoc]`. Take `⟨fL, hfL⟩` from `fy.exists_isMap κ rfl (x' := (z ≫ jG) ≫ πB ≫ genι O.s.T.Z) (by`.

Rewrite using `[← Category.assoc _ πB, hρ, Category.assoc, Category.assoc])`. Take `⟨gL, hgL⟩` from `exists_frame_cast fL (hr a) (isEigBasis_of_stalk (O.Φ.C c) h1 (frB a) hf _ hb κ hρ)`. Take `⟨W, hW, M, hz, s, uM, ad⟩` from `exists_adapted hE c1 c2 φs a (frB a) (hr a) (c3 a) hf h1 _ hb κ hfL hgL z rfl hy hκ`. Take `⟨W', hW', M', hz', s', uM', ad'⟩` from `exists_adapted hE c1 c2 φs a (frB a) (hr a) (c3 a) hf h1 _ hb κ hfL hgL z' e₁ ((congrArg (fun g : Sp L ⟶ (O.var c).X => g (IsLocalRing.closedPoint L)) e₂).trans hy) (e₂.trans hκ)`. Take `⟨U, h₁, h₂, h₃⟩` from `ad.exists_upper (isUnit_det_co_cast _ _ _) (isUnit_det_co_cast _ _ _) uM uM' ad'`.

Conclude with `⟨V, f, W, W', hW, hW', M, M', hz, hz', U, s, s', h₁, h₂, h₃⟩`.
-/
private theorem eq_of_images (c1 : jG ≫ jB = j ≫ π₀) (c2 : jG ≫ πB = πG ≫ (O.Φ.C c).π)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (frB : ∀ a, IsLieFrames O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (!a.2) (u a))
    (hr : ∀ a, rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a))
    (c3 : ∀ a i, ∃ r, GlobalTheory.FlagCov.IsFrameSec hE jB πB u π₀ fl₀ j φ jG a i (hr a) r)
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) {L : Type} [Field L] (z z' : Sp L ⟶ G)
    (e₁ : z' ≫ jG = z ≫ jG) (e₂ : z' ≫ πG = z ≫ πG) : z ≫ j = z' ≫ j := by
  refine eq_of_spans π₀ E _ fl₀ hfb _ _
    (by rw [Category.assoc, Category.assoc, ← c1, ← Category.assoc, ← e₁, Category.assoc]) fun a => ?_
  obtain ⟨y, κ, hy, hκ⟩ : ∃ (y : (O.Φ.C c).Y.X) (κ : (O.Φ.C c).Y.X.presheaf.stalk y →+* L),
      (z ≫ πG) (IsLocalRing.closedPoint L) = y ∧ z ≫ πG = spMap κ ≫ stalkPt (O.Φ.C c).Y y :=
    ⟨_, (Scheme.stalkClosedPointTo (z ≫ πG)).hom, rfl, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).symm⟩
  obtain ⟨φy, fy, t, h1, -⟩ := (O.Φ.C c).gr_spec y
  obtain ⟨V, f, hV, hf⟩ := hE a (((z ≫ jG) ≫ jB) (IsLocalRing.closedPoint L))
  have hb : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V := fun p _ => by
    obtain rfl : p = IsLocalRing.closedPoint L := Subsingleton.elim (α := PrimeSpectrum L) _ _
    exact hV
  have hρ : (z ≫ jG) ≫ πB = spMap κ ≫ stalkPt (O.Φ.C c).Y y ≫ (O.Φ.C c).π := by
    rw [Category.assoc, c2, ← Category.assoc, hκ, Category.assoc]
  obtain ⟨fL, hfL⟩ := fy.exists_isMap κ rfl (x' := (z ≫ jG) ≫ πB ≫ genι O.s.T.Z) (by
    rw [← Category.assoc _ πB, hρ, Category.assoc, Category.assoc])
  obtain ⟨gL, hgL⟩ := exists_frame_cast fL (hr a) (isEigBasis_of_stalk (O.Φ.C c) h1 (frB a) hf _ hb κ hρ)
  obtain ⟨W, hW, M, hz, s, uM, ad⟩ := exists_adapted hE c1 c2 φs a (frB a) (hr a) (c3 a) hf h1 _ hb κ hfL hgL z rfl
    hy hκ
  obtain ⟨W', hW', M', hz', s', uM', ad'⟩ := exists_adapted hE c1 c2 φs a (frB a) (hr a) (c3 a) hf h1 _ hb κ hfL hgL
    z' e₁ ((congrArg (fun g : Sp L ⟶ (O.var c).X => g (IsLocalRing.closedPoint L)) e₂).trans hy) (e₂.trans hκ)
  obtain ⟨U, h₁, h₂, h₃⟩ := ad.exists_upper (isUnit_det_co_cast _ _ _) (isUnit_det_co_cast _ _ _) uM uM' ad'
  exact ⟨V, f, W, W', hW, hW', M, M', hz, hz', U, s, s', h₁, h₂, h₃⟩

end Points

end GlobalTheory.FlagCovQF

end

/- English proof (translation)
Introduce `P2 PH RA SW D O hO B hB R hR c Bs _ q arq nBs E h H Bg jB πB u Gm hL Y₀ _ π₀ fl₀ hfb ar₀ n₀ _ φ₀ h₁ h₂ h₃ πG hs hc hg`. Use `haveI : IsProper (π₀ ≫ q) := GlobalTheory.CommonModel.isProper_of_isProjOver ar₀.isProjOver`. Use `haveI hq : LocallyOfFiniteType (π₀ ≫ q) := inferInstance`. Use `haveI : LocallyOfFiniteType (GlobalTheory.FlagGenFib.sf q π₀) := by`. Establish `hb : MorphismProperty.IsStableUnderBaseChange @LocallyOfFiniteType` using `inferInstance`.

Conclude with `hb.of_isPullback (GlobalTheory.FlagGenFib.isPullback_f q π₀) hq`. Use `haveI : LocallyOfFiniteType πG := by`. Establish `: LocallyOfFiniteType (πG ≫ (O.var c).str)` using `by rw [hs]; infer_instance`. Conclude with `locallyOfFiniteType_of_comp πG (O.var c).str`. Use `haveI : IsFinite πB := hL.2.1`.

Use `LocallyQuasiFinite.of_finite_preimage_singleton πG fun x => ?_` and prove the remaining obligations. Use `GlobalTheory.VarFlag.LQF.finite_preimage_of_finite_points πG x ?_` and prove the remaining obligations. Use `set jG := GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 with hjG`. Use `set P := Spec.map (CommRingCat.ofHom (algebraMap ((O.var c).X.residueField x) (AlgebraicClosure ((O.var c).X.residueField x)))) ≫ (O.var c).X.fromSpecResidueField x with hP`. Establish `hfin` using `GlobalTheory.FlagCovQF.finite_points πB (AlgebraicClosure ((O.var c).X.residueField x)) (P ≫ (O.Φ.C c).π)`.

Use `Set.Finite.of_finite_image (f := fun z => z ≫ jG) (hfin.subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Establish `hz : z ≫ πG = P` using `hz`. Use `show (z ≫ jG) ≫ πB = P ≫ (O.Φ.C c).π`. Rewrite using `[Category.assoc, hc, ← Category.assoc, hz]`.

Introduce `z hz z' hz' e`. Establish `hz : z ≫ πG = P` using `hz`. Establish `hz' : z' ≫ πG = P` using `hz'`. Establish `e : z ≫ jG = z' ≫ jG` using `e`. Establish `hj : z ≫ GlobalTheory.FlagGenFib.jf q π₀ = z' ≫ GlobalTheory.FlagGenFib.jf q π₀` using `GlobalTheory.FlagCovQF.eq_of_images (fun a => (h a).isVB) (GlobalTheory.FlagGenFib.jGf_jB q π₀ jB _ hL.1) hc hg hL.2.2.2.1 (fun a => (hL.2.2.2.2.2.2 a).1) (fun a i => h₃ a i _) hfb z z' e.symm (hz'.trans hz.symm)`.

Establish `hsn : jG ≫ (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) = GlobalTheory.FlagGenFib.sf q π₀` using `hL.1.lift_snd _ _ _`. Establish `hs' : z ≫ GlobalTheory.FlagGenFib.sf q π₀ = z' ≫ GlobalTheory.FlagGenFib.sf q π₀`. Rewrite using `[← hsn, ← Category.assoc, e, Category.assoc]`. Conclude with `(GlobalTheory.FlagGenFib.isPullback_f q π₀).hom_ext hj hs'`.
-/
theorem _root_.GlobalTheory.T.arithmetic_bundle_rank_comparison : ∀ (P2 : Hypotheses2) (PH : HypothesesH) (RA : RegularAlteration) (SW : ScholzeWeinsteinB)
    (D : D7) (O : Setup D) (hO : O.Core) (B : ℝ) (hB : 2 ≤ B) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp)
    (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (Gm : ∀ σ', EigMet O.s.T.Z σ')
    (hL : GlobalTheory.FlagCov.LieWit O B R c q E h jB πB u Gm)
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) [IsIntegral (GlobalTheory.FlagGenFib.Gf q π₀)] (φ₀ : (O.var c).Fn →+* (GlobalTheory.FlagGenFib.Gf q π₀).functionField)
    (h₁ : (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ GlobalTheory.FlagGenFib.sf q π₀ =
        spMap φ₀ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ≫ (O.var c).str)
    (h₂ : (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 ≫ πB =
        spMap φ₀ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ≫ (O.Φ.C c).π)
    (h₃ : ∀ a i (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)),
          ∃ r : (((fl₀ a).root i).pull (GlobalTheory.FlagGenFib.jf q π₀)).ι → (GlobalTheory.FlagGenFib.Gf q π₀).functionFieldˣ,
            GlobalTheory.FlagCov.IsFrameSec (fun a => (h a).isVB) jB πB u π₀ fl₀ (GlobalTheory.FlagGenFib.jf q π₀) φ₀
              (GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1) a i hr r) (πG : (GlobalTheory.FlagGenFib.Gf q π₀) ⟶ (O.var c).X), πG ≫ (O.var c).str = GlobalTheory.FlagGenFib.sf q π₀ →
      GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 ≫ πB = πG ≫ (O.Φ.C c).π →
      (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ πG = spMap φ₀ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) →
      LocallyQuasiFinite πG := by
  intro P2 PH RA SW D O hO B hB R hR c Bs _ q arq nBs E h H Bg jB πB u Gm hL Y₀ _ π₀ fl₀ hfb ar₀ n₀ _ φ₀ h₁ h₂ h₃
    πG hs hc hg
  haveI : IsProper (π₀ ≫ q) := GlobalTheory.CommonModel.isProper_of_isProjOver ar₀.isProjOver
  haveI hq : LocallyOfFiniteType (π₀ ≫ q) := inferInstance
  haveI : LocallyOfFiniteType (GlobalTheory.FlagGenFib.sf q π₀) :=
    by
      have hb : MorphismProperty.IsStableUnderBaseChange @LocallyOfFiniteType := inferInstance
      exact hb.of_isPullback (GlobalTheory.FlagGenFib.isPullback_f q π₀) hq
  haveI : LocallyOfFiniteType πG := by
    have : LocallyOfFiniteType (πG ≫ (O.var c).str) := by rw [hs]; infer_instance
    exact locallyOfFiniteType_of_comp πG (O.var c).str
  haveI : IsFinite πB := hL.2.1
  refine LocallyQuasiFinite.of_finite_preimage_singleton πG fun x => ?_
  refine GlobalTheory.VarFlag.LQF.finite_preimage_of_finite_points πG x ?_
  set jG := GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 with hjG
  set P := Spec.map (CommRingCat.ofHom (algebraMap ((O.var c).X.residueField x)
    (AlgebraicClosure ((O.var c).X.residueField x)))) ≫ (O.var c).X.fromSpecResidueField x with hP
  have hfin := GlobalTheory.FlagCovQF.finite_points πB (AlgebraicClosure ((O.var c).X.residueField x)) (P ≫ (O.Φ.C c).π)
  refine Set.Finite.of_finite_image (f := fun z => z ≫ jG) (hfin.subset ?_) ?_
  · rintro _ ⟨z, hz, rfl⟩
    have hz : z ≫ πG = P := hz
    show (z ≫ jG) ≫ πB = P ≫ (O.Φ.C c).π
    rw [Category.assoc, hc, ← Category.assoc, hz]
  · intro z hz z' hz' e
    have hz : z ≫ πG = P := hz
    have hz' : z' ≫ πG = P := hz'
    have e : z ≫ jG = z' ≫ jG := e
    have hj : z ≫ GlobalTheory.FlagGenFib.jf q π₀ = z' ≫ GlobalTheory.FlagGenFib.jf q π₀ :=
      GlobalTheory.FlagCovQF.eq_of_images (fun a => (h a).isVB) (GlobalTheory.FlagGenFib.jGf_jB q π₀ jB _ hL.1) hc hg hL.2.2.2.1
        (fun a => (hL.2.2.2.2.2.2 a).1) (fun a i => h₃ a i _) hfb z z' e.symm (hz'.trans hz.symm)
    have hsn : jG ≫ (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) = GlobalTheory.FlagGenFib.sf q π₀ :=
      hL.1.lift_snd _ _ _
    have hs' : z ≫ GlobalTheory.FlagGenFib.sf q π₀ = z' ≫ GlobalTheory.FlagGenFib.sf q π₀ := by
      rw [← hsn, ← Category.assoc, e, Category.assoc]
    exact (GlobalTheory.FlagGenFib.isPullback_f q π₀).hom_ext hj hs'
