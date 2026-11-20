import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndepStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangentStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Reg.TieUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

/- English proof (translation)
Apply `TopCat.Presheaf.section_ext X.sheaf U` to reduce the goal to its premises. Introduce `p hp`. Take `⟨W, hW, hpW, e⟩` from `h p hp`. Establish `e1` using `X.presheaf.germ_res_apply (homOfLE hW) p hpW a`. Establish `e2` using `X.presheaf.germ_res_apply (homOfLE hW) p hpW b`.

Conclude with `e1.symm.trans ((congrArg _ e).trans e2)`.
-/
theorem eq_of_loc {X : Scheme.{0}} {U : X.Opens} (a b : Γ(X, U))
    (h : ∀ p ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), p ∈ W ∧ resG X hW a = resG X hW b) : a = b := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro p hp
  obtain ⟨W, hW, hpW, e⟩ := h p hp
  have e1 := X.presheaf.germ_res_apply (homOfLE hW) p hpW a
  have e2 := X.presheaf.germ_res_apply (homOfLE hW) p hpW b
  exact e1.symm.trans ((congrArg _ e).trans e2)

/- English proof (translation)
Consider the cases of `s`. Consider the cases of `t`. Use `congr 1`. Conclude with `funext h`.
-/
theorem sec_ext {X : Scheme.{0}} {L : LB X} {s t : LB.Sec L} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s
  cases t
  congr 1
  exact funext h

/- English proof (translation)
Use `sec_ext fun i => eq_of_loc _ _ fun p hp => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `exists_chart hL p`. Conclude with `⟨M.U i ⊓ L.U k, inf_le_left, ⟨hp, hk⟩, (h i k).trans (h' i k).symm⟩`.
-/
theorem isoMaps_unique {X : Scheme.{0}} {L M : LB X} (hL : L.IsLB) (w : LB.Iso L M) (σ : LB.Sec L)
    {s s' : LB.Sec M} (h : IsoMaps w σ s) (h' : IsoMaps w σ s') : s = s' := by
  refine sec_ext fun i => eq_of_loc _ _ fun p hp => ?_
  obtain ⟨k, hk⟩ := exists_chart hL p
  exact ⟨M.U i ⊓ L.U k, inf_le_left, ⟨hp, hk⟩, (h i k).trans (h' i k).symm⟩

/- English proof (translation)
Take `rfl : V = g ⁻¹ᵁ U` from `le_antisymm h h'`. Rewrite using `[Scheme.Hom.appLE_eq_app]`. Conclude with `(ConcreteCategory.bijective_of_isIso (g.app U)).1`.
-/
theorem appLE_injective {X Y : Scheme.{0}} (g : Y ⟶ X) [IsIso g] (U : X.Opens) (V : Y.Opens) (h : V ≤ g ⁻¹ᵁ U)
    (h' : g ⁻¹ᵁ U ≤ V) : Function.Injective (g.appLE U V h).hom := by
  obtain rfl : V = g ⁻¹ᵁ U := le_antisymm h h'
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (g.app U)).1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {M : MChart Y} {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x : Sp R ⟶ Xo.X}

/- English proof (translation)
The claim follows from `GlobalTheory.iso_eq_of_maps_along_section (S := S') (exists_chart t'.PP.isLB) (fun y => (exists_chart t.PP.isLB (m.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩) t'.G.hom (eSec t'.G) (Over.w η[t'.G]) (GlobalTheory.globalFns_holds _ _ hab).2 h.1 h'.1 h.2 h'.2`.
-/
theorem rigIso_unique {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {g : S' ⟶ S} (m : SABMap t' t g)
    (hab : IsAbelianScheme t'.G) {w w' : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} (h : RigIso m w) (h' : RigIso m w') :
    w = w' :=
  GlobalTheory.iso_eq_of_maps_along_section (S := S') (exists_chart t'.PP.isLB)
    (fun y => (exists_chart t.PP.isLB (m.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    t'.G.hom (eSec t'.G) (Over.w η[t'.G]) (GlobalTheory.globalFns_holds _ _ hab).2 h.1 h'.1 h.2 h'.2

/- English proof (translation)
Establish `hp : IsProper Λ.t'.G.hom` using `MorphismProperty.of_isPullback (P := @IsProper) Λ.m1.cart.1 Xo.univ.proper`. Conclude with `⟨Λ.t'.semi.comm, Λ.t'.semi.smooth, hp, Λ.t'.semi.geomConnected⟩`.
-/
theorem lift_abelian (Λ : M.Lift f x) : IsAbelianScheme Λ.t'.G := by
  have hp : IsProper Λ.t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) Λ.m1.cart.1 Xo.univ.proper
  exact ⟨Λ.t'.semi.comm, Λ.t'.semi.smooth, hp, Λ.t'.semi.geomConnected⟩

/- English proof (translation)
Establish `e : Λ.m2.φ ≫ Y.t.G.hom = Λ.t'.G.hom ≫ spMap f ≫ M.hU.fromSpec` using `Λ.m2.cart.1.w`. Rewrite using `[← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Use `M.hU.range_fromSpec` as an intermediate fact. Conclude with `this.le ⟨_, rfl⟩`.
-/
theorem lift_mem (Λ : M.Lift f x) (p : Λ.t'.G.left) : Y.t.G.hom (Λ.m2.φ p) ∈ M.U := by
  have e : Λ.m2.φ ≫ Y.t.G.hom = Λ.t'.G.hom ≫ spMap f ≫ M.hU.fromSpec := Λ.m2.cart.1.w
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  have := M.hU.range_fromSpec
  exact this.le ⟨_, rfl⟩

/- English proof (translation)
Take `⟨w1, w2, σ, s1, r1, r2, i1, a, b⟩` from `h`. Take `⟨w1', w2', σ', s1', r1', r2', i1', a', b'⟩` from `h'`. Take `rfl : w1 = w1'` from `rigIso_unique Λ.m1 (lift_abelian Λ) r1 r1'`. Take `rfl : w2 = w2'` from `rigIso_unique Λ.m2 (lift_abelian Λ) r2 r2'`. Choose the witnesses or unpack the hypotheses as in `rfl : σ = σ' := by`.

Use `sec_ext fun k => eq_of_loc _ _ fun p hp => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart Y.t.PP.isLB (Λ.m2.φ p)`. Establish `h₁ : (Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U k ≤ Λ.m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j)` using `fun q hq => ⟨lift_mem Λ q, mem_pull.1 hq.1⟩`. Use `⟨(Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U k, inf_le_right, ⟨mem_pull.2 hj, hp⟩, ?_⟩` and prove the remaining obligations. Establish `e` using `(a j k _ h₁ le_rfl).symm.trans (a' j k _ h₁ le_rfl)`.

Conclude with `(((w2.s (fun _ => j, k)).isUnit.map _).mul_left_cancel e)`. Take `rfl : s1 = s1'` from `isoMaps_unique Λ.t'.PP.isLB w1 σ i1 i1'`. Establish `hc : IsPullback Λ.t'.G.hom Λ.m1.φ x Xo.univ.t.G.hom` using `Λ.m1.cart.1.flip`. Set `g : Λ.t'.G.left ⟶ Gx x` to `hc.isoPullback.hom`. Establish `hg : IsIso g` using `inferInstanceAs (IsIso hc.isoPullback.hom)`.

Establish `g1 : g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ` using `hc.isoPullback_hom_snd`. Establish `g2 : g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom` using `hc.isoPullback_hom_fst`. Use `sec_ext fun i => ?_` and prove the remaining obligations. Take `⟨j, rfl⟩ : ∃ j : Xo.univ.t.PP.L.ι, i = fun _ => j` from `⟨i (0 : Fin 1), funext fun k => congrArg i (Subsingleton.elim (α := Fin 1) k 0)⟩`. Establish `hm : ∀ q : Λ.t'.G.left, q ∈ g ⁻¹ᵁ (PPx x).U (fun _ => j) ↔ Λ.m1.φ q ∈ Xo.univ.t.PP.L.U j`.

Introduce `q`. Rewrite using `[← g1, Scheme.Hom.comp_apply]`. Conclude with `⟨fun hq => Set.mem_iInter.1 hq (0 : Fin 1), fun hq => Set.mem_iInter.2 fun _ => hq⟩`. Establish `h₁ : (Xo.univ.t.PP.L.pull Λ.m1.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j)` using `fun q hq => (hm q).2 (mem_pull.1 hq)`. Conclude with `appLE_injective g _ _ h₁ (fun q hq => mem_pull.2 ((hm q).1 hq)) ((b g g1 g2 (fun _ => j) h₁).symm.trans (b' g g1 g2 (fun _ => j) h₁))`.
-/
theorem thTie_unique (Λ : M.Lift f x) {s s' : LB.Sec (PPx x)} (h : Λ.ThTie s) (h' : Λ.ThTie s') : s = s' := by
  obtain ⟨w1, w2, σ, s1, r1, r2, i1, a, b⟩ := h
  obtain ⟨w1', w2', σ', s1', r1', r2', i1', a', b'⟩ := h'
  obtain rfl : w1 = w1' := rigIso_unique Λ.m1 (lift_abelian Λ) r1 r1'
  obtain rfl : w2 = w2' := rigIso_unique Λ.m2 (lift_abelian Λ) r2 r2'
  obtain rfl : σ = σ' := by
    refine sec_ext fun k => eq_of_loc _ _ fun p hp => ?_
    obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (Λ.m2.φ p)
    have h₁ : (Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U k ≤
        Λ.m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) := fun q hq => ⟨lift_mem Λ q, mem_pull.1 hq.1⟩
    refine ⟨(Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U k, inf_le_right, ⟨mem_pull.2 hj, hp⟩, ?_⟩
    have e := (a j k _ h₁ le_rfl).symm.trans (a' j k _ h₁ le_rfl)
    exact (((w2.s (fun _ => j, k)).isUnit.map _).mul_left_cancel e)
  obtain rfl : s1 = s1' := isoMaps_unique Λ.t'.PP.isLB w1 σ i1 i1'
  have hc : IsPullback Λ.t'.G.hom Λ.m1.φ x Xo.univ.t.G.hom := Λ.m1.cart.1.flip
  let g : Λ.t'.G.left ⟶ Gx x := hc.isoPullback.hom
  have hg : IsIso g := inferInstanceAs (IsIso hc.isoPullback.hom)
  have g1 : g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ := hc.isoPullback_hom_snd
  have g2 : g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom := hc.isoPullback_hom_fst
  refine sec_ext fun i => ?_
  obtain ⟨j, rfl⟩ : ∃ j : Xo.univ.t.PP.L.ι, i = fun _ => j := ⟨i (0 : Fin 1), funext fun k => congrArg i (Subsingleton.elim (α := Fin 1) k 0)⟩
  have hm : ∀ q : Λ.t'.G.left, q ∈ g ⁻¹ᵁ (PPx x).U (fun _ => j) ↔ Λ.m1.φ q ∈ Xo.univ.t.PP.L.U j := by
    intro q
    rw [← g1, Scheme.Hom.comp_apply]
    exact ⟨fun hq => Set.mem_iInter.1 hq (0 : Fin 1), fun hq => Set.mem_iInter.2 fun _ => hq⟩
  have h₁ : (Xo.univ.t.PP.L.pull Λ.m1.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j) :=
    fun q hq => (hm q).2 (mem_pull.1 hq)
  exact appLE_injective g _ _ h₁ (fun q hq => mem_pull.2 ((hm q).1 hq))
    ((b g g1 g2 (fun _ => j) h₁).symm.trans (b' g g1 g2 (fun _ => j) h₁))

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y M L _ _ f u y z hy hz hx`. Take `⟨x, xo, v, t1, t2, t3, s, t4⟩` from `y`. Take `⟨x', xo', v', t1', t2', t3', s', t4'⟩` from `z`. Take `rfl : x = x'` from `hx`. Take `⟨Λ, hv, hs⟩` from `hy`.

Take `⟨Λ', hv', hs'⟩` from `hz`. Take `⟨k1, k2⟩` from `GlobalTheory.T.modelChartLift_coords_generator_indep E H Dw l Xo c O β Y M L f x Λ' Λ`. Choose the witnesses or unpack the hypotheses as in `rfl : v = v' := by`. Use function extensionality and compare the values at `τ i`. Conclude with `((GlobalTheory.T.lieBasis_coordinates_bijective_tangent E H Dw l Xo c O β Y M L f x Λ).1 _).unique (hv τ i) (k1 _ _ (hv' τ i))`.

Take `rfl : s = s'` from `thTie_unique Λ hs (k2 _ hs')`. Both sides reduce to the same expression.
-/
theorem frPt_eq_of_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (y z : FrPt Xo c L), M.Comparison₂ f u y → M.Comparison₂ f u z → y.x = z.x → y = z := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f u y z hy hz hx
  obtain ⟨x, xo, v, t1, t2, t3, s, t4⟩ := y
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := z
  obtain rfl : x = x' := hx
  obtain ⟨Λ, hv, hs⟩ := hy
  obtain ⟨Λ', hv', hs'⟩ := hz
  obtain ⟨k1, k2⟩ := GlobalTheory.T.modelChartLift_coords_generator_indep E H Dw l Xo c O β Y M L f x Λ' Λ
  obtain rfl : v = v' := by
    funext τ i
    exact ((GlobalTheory.T.lieBasis_coordinates_bijective_tangent E H Dw l Xo c O β Y M L f x Λ).1 _).unique (hv τ i) (k1 _ _ (hv' τ i))
  obtain rfl : s = s' := thTie_unique Λ hs (k2 _ hs')
  rfl

end GlobalTheory.Reg.TieUniq
