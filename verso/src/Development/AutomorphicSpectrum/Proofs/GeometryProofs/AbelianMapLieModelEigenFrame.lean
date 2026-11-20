import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecFracExt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelFieldPointStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

/- English proof (translation)
Establish `a₁ : w ≫ Xo.univ.t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) ≫ pullback.fst _ _`. Rewrite using `[hw, Category.assoc, Small.ptF_fst]`. Establish `a₂ : w' ≫ Xo.univ.t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) ≫ pullback.fst _ _`. Rewrite using `[hw', Category.assoc, Small.ptF_fst]`. Establish `e : Y.m0.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) a₁ = Y.m0.cart.1.lift w' (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) a₂` using `Y.m.cart.1.hom_ext h (by rw [IsPullback.lift_snd, IsPullback.lift_snd])`.

Rewrite using `[← Y.m0.cart.1.lift_fst w _ a₁, e, IsPullback.lift_fst]`.
-/
theorem tanW_injective (Y : Model Xo c β) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {w w' : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left}
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (hw' : w' ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (h : tanW Y y w hw = tanW Y y w' hw') : w = w' := by
  have a₁ : w ≫ Xo.univ.t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [hw, Category.assoc, Small.ptF_fst]
  have a₂ : w' ≫ Xo.univ.t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [hw', Category.assoc, Small.ptF_fst]
  have e : Y.m0.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) a₁ =
      Y.m0.cart.1.lift w' (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) a₂ :=
    Y.m.cart.1.hom_ext h (by rw [IsPullback.lift_snd, IsPullback.lift_snd])
  rw [← Y.m0.cart.1.lift_fst w _ a₁, e, IsPullback.lift_fst]

/- English proof (translation)
Rewrite using `[Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit A) (toUnit B)]`.
-/
theorem comp_unit {T : Scheme.{0}} {A B M : CategoryTheory.Over T} [GrpObj M] (u : B ⟶ A) : u ≫ (1 : A ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit A) (toUnit B)]

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Apply the tactic sequence `ext b <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem eps_alg {S : Type} [CommRing S] (a : S) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S (DualNumber S)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext b <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Apply the tactic sequence `ext b <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem eps_zero {S : Type} [CommRing S] :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (0 : S)) =
      spMap (algebraMap S (DualNumber S)) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext b <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]`. Use `congr 1`.
-/
theorem fst_alg {S : Type} [CommRing S] :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

/- English proof (translation)
Use `⟨Over.w _, ?_⟩` and prove the remaining obligations. Set `k : Over.mk x ⟶ tEps x` to `Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by`. Express the relevant statement in the definitionally equal form `_ ≫ _ ≫ x = x`. Rewrite using `[← Category.assoc, fst_alg, Category.id_comp])`. Conclude with `congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)`.
-/
theorem isTanAt_one {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) :
    Formalism.L2.Pj.IsTanAt x (1 : tEps x ⟶ Xo.univ.t.G).left := by
  refine ⟨Over.w _, ?_⟩
  let k : Over.mk x ⟶ tEps x := Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    change _ ≫ _ ≫ x = x
    rw [← Category.assoc, fst_alg, Category.id_comp])
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

/- English proof (translation)
Set `k : tEps x ⟶ tEps x` to `Over.homMk (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a)) (by`. Express the relevant statement in the definitionally equal form `_ ≫ _ ≫ x = _ ≫ x`. Rewrite using `[← Category.assoc, eps_alg])`. Conclude with `congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)`.
-/
theorem eps_one {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) (a : S) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ (1 : tEps x ⟶ Xo.univ.t.G).left =
      (1 : tEps x ⟶ Xo.univ.t.G).left := by
  let k : tEps x ⟶ tEps x := Over.homMk (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a)) (by
    change _ ≫ _ ≫ x = _ ≫ x
    rw [← Category.assoc, eps_alg])
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

/- English proof (translation)
Introduce `a`. Rewrite using `[eps_one]`. Use `haveI := Xo.univ.t.act.hom a`. Establish `h : (1 : tEps x ⟶ Xo.univ.t.G) ≫ Xo.univ.t.act.act a = 1`. Rewrite using `[Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]`.

Conclude with `congrArg (fun z => z.left) h`.
-/
theorem isEigAt_one {S : Type} [CommRing S] [Algebra c.F S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) (τ : E →+* ℂ) :
    Formalism.L2.Pj.IsEigAt c τ (Xo := Xo) (1 : tEps x ⟶ Xo.univ.t.G).left := by
  intro a
  rw [eps_one]
  haveI := Xo.univ.t.act.hom a
  have h : (1 : tEps x ⟶ Xo.univ.t.G) ≫ Xo.univ.t.act.act a = 1 := by
    rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]
  exact congrArg (fun z => z.left) h

/- English proof (translation)
Rewrite using `[eps_zero, Category.assoc, hv.2]`. Set `k : tEps x ⟶ Over.mk x` to `Over.homMk (spMap (algebraMap S (DualNumber S))) rfl`. Conclude with `congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)`.
-/
theorem eps_zero_comp {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X)
    (v : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left) (hv : Formalism.L2.Pj.IsTanAt x v) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (0 : S)) ≫ v = (1 : tEps x ⟶ Xo.univ.t.G).left := by
  rw [eps_zero, Category.assoc, hv.2]
  let k : tEps x ⟶ Over.mk x := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

def combPt {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) (a : Fin n → S) (i : Fin n) : tEps x ⟶ Xo.univ.t.G :=
  Over.homMk (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (a i)) ≫ v i) (by
    change (_ ≫ v i) ≫ _ = _ ≫ x
    rw [Category.assoc, (hv i).1, ← Category.assoc, eps_alg])

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, combPt x v hv a, fun _ => rfl, rfl⟩`.
-/
theorem exists_comb {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) (a : Fin n → S) : ∃ w, IsCombAt x v a w :=
  ⟨_, combPt x v hv a, fun _ => rfl, rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => 1, fun i => (eps_zero_comp x (v i) (hv i)).symm, by simp [List.ofFn_const, List.prod_replicate]⟩`.
-/
theorem comb_zero {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) :
    IsCombAt x v (0 : Fin n → S) (1 : tEps x ⟶ Xo.univ.t.G).left :=
  ⟨fun _ => 1, fun i => (eps_zero_comp x (v i) (hv i)).symm, by
    simp [List.ofFn_const, List.prod_replicate]⟩

/- English proof (translation)
The claim follows from `(y.basis τ _ (isTanAt_one y.x) (isEigAt_one y.x τ)).unique h (comb_zero y.x (y.u τ) (y.tan τ))`.
-/
theorem coeff_zero_of_unit {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (τ : E →+* ℂ)
    (a : Fin (Dw.mult τ) → S) (h : IsCombAt y.x (y.u τ) a (1 : tEps y.x ⟶ Xo.univ.t.G).left) : a = 0 :=
  (y.basis τ _ (isTanAt_one y.x) (isEigAt_one y.x τ)).unique h (comb_zero y.x (y.u τ) (y.tan τ))

/- English proof (translation)
Establish `e₁ : w₁ = (1 : tEps y.x ⟶ Xo.univ.t.G).left`. Take `⟨U, hU, rfl⟩` from `h₁`. Establish `: U = fun _ => 1`. Use function extensionality and compare the values at `i`. Apply `CategoryTheory.Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[hU i]`. Conclude with `eps_zero_comp y.x (y.u τ i) (y.tan τ i)`. Substitute `this` using the available equality. Simplify using `[List.ofFn_const, List.prod_replicate]`. Use `tanW_injective Y y hw hw₁ e` as an intermediate fact.

Rewrite `h` using `[this, e₁]`. Conclude with `coeff_zero_of_unit y τ a h`.
-/
theorem coeff_zero_of_tanW {S : Type} [CommRing S] [Algebra c.F S] (Y : Model Xo c β) (y : FrPt Xo c S) (τ : E →+* ℂ)
    (a : Fin (Dw.mult τ) → S) {w w₁ : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt y.x (y.u τ) a w) (h₁ : IsCombAt y.x (y.u τ) (0 : Fin (Dw.mult τ) → S) w₁)
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (hw₁ : w₁ ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (e : tanW Y y w hw = tanW Y y w₁ hw₁) : a = 0 := by
  have e₁ : w₁ = (1 : tEps y.x ⟶ Xo.univ.t.G).left := by
    obtain ⟨U, hU, rfl⟩ := h₁
    have : U = fun _ => 1 := by
      funext i
      apply CategoryTheory.Over.OverMorphism.ext
      rw [hU i]
      exact eps_zero_comp y.x (y.u τ i) (y.tan τ i)
    subst this
    simp [List.ofFn_const, List.prod_replicate]
  have := tanW_injective Y y hw hw₁ e
  rw [this, e₁] at h
  exact coeff_zero_of_unit y τ a h

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hy τ r hr u hu`. Substitute `hr` using the available equality. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha`. Establish `comb` using `GlobalTheory.T.abelian_map_lie_model_field_point E H Dw l Xo c O β Y X tX f m F g EC MC y hy (Dw.mult τ) (y.u τ) (y.tan τ) u hu`.

Take `⟨w, hc⟩` from `FinRd.Roots.LieBasis.exists_comb y.x (y.u τ) (y.tan τ) a`. Take `⟨w₁, h1⟩` from `FinRd.Roots.LieBasis.exists_comb y.x (y.u τ) (y.tan τ) (0 : Fin (Dw.mult τ) → F)`. Take `⟨hw, ew⟩` from `comb a w hc`. Take `⟨hw1, e1⟩` from `comb 0 w₁ h1`. Establish `hz` using `FinRd.Roots.LieBasis.coeff_zero_of_tanW Y y τ a hc h1 hw hw1 (by`.

Rewrite using `[← ew, ← e1, ha]`. Use the proof step `simp)`. Introduce `i`. Conclude with `congrFun hz i`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.indep_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ) (u : Fin r → EC), (∀ i, (MC.pt (u i)).left ≫ m.φ = Small.tanY Y y τ (Fin.cast hr i)) → LinearIndependent F u := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hy τ r hr u hu
  subst hr
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have comb := GlobalTheory.T.abelian_map_lie_model_field_point E H Dw l Xo c O β Y X tX f m F g EC MC y hy (Dw.mult τ) (y.u τ) (y.tan τ) u hu
  obtain ⟨w, hc⟩ := FinRd.Roots.LieBasis.exists_comb y.x (y.u τ) (y.tan τ) a
  obtain ⟨w₁, h1⟩ := FinRd.Roots.LieBasis.exists_comb y.x (y.u τ) (y.tan τ) (0 : Fin (Dw.mult τ) → F)
  obtain ⟨hw, ew⟩ := comb a w hc
  obtain ⟨hw1, e1⟩ := comb 0 w₁ h1
  have hz := FinRd.Roots.LieBasis.coeff_zero_of_tanW Y y τ a hc h1 hw hw1 (by
    rw [← ew, ← e1, ha]
    simp)
  intro i
  exact congrFun hz i
