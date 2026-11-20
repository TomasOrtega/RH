import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

section Ident

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

def pullIdIso {X : Scheme.{0}} (L : LB X) : LB.Iso L (L.pull (𝟙 X)) where
  s := fun p => res (X := X) (U := L.U (p.1 PUnit.unit) ⊓ L.U p.2)
    (V := (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2) (fun _ hx => ⟨mem_pull.1 hx.1, hx.2⟩) (L.g (p.1 PUnit.unit) p.2)

/- English proof (translation)
Establish `hm : f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k` using `⟨mem_pull.2 hj, hk⟩`. Conclude with `gm_res f y _ hm _`.
-/
theorem gw_pullIdIso {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (pullIdIso L) f y j k = gm f y (L.U j ⊓ L.U k) (L.g j k) := by
  have hm : f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  exact gm_res f y _ hm _

/- English proof (translation)
Introduce `Y f y j j' k k' hj hj' hk hk'`. Establish `hj₁ : f y ∈ L.U j` using `hj`. Establish `hj₂ : f y ∈ L.U j'` using `hj'`. Rewrite using `[gw_pullIdIso L f y j k hj₁ hk, gw_pullIdIso L f y j' k' hj₂ hk', Category.comp_id]`. Establish `a` using `gm_cocycle hL f y hj₁ hk hk'`.

Establish `b` using `gm_cocycle hL f y hj₁ hj₂ hk'`. Rewrite using `[mul_right_comm, b, ← a, mul_inv_cancel_right]`.
-/
theorem pgen_pullIdIso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : PGen (pullIdIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have hj₁ : f y ∈ L.U j := hj
  have hj₂ : f y ∈ L.U j' := hj'
  rw [gw_pullIdIso L f y j k hj₁ hk, gw_pullIdIso L f y j' k' hj₂ hk', Category.comp_id]
  have a := gm_cocycle hL f y hj₁ hk hk'
  have b := gm_cocycle hL f y hj₁ hj₂ hk'
  rw [mul_right_comm, b, ← a, mul_inv_cancel_right]

/- English proof (translation)
Introduce `Z r z p q hp hq`. Establish `hp' : ∀ k, φ k (r z) ∈ L.U (p k)` using `hp`. Establish `hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q` using `⟨Set.mem_iInter.2 hp', Set.mem_iInter.2 hq⟩`. Establish `e` using `congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)`. Rewrite using `[Category.comp_id]`.

Use `(gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))` and prove the remaining obligations. Use `(map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))` and prove the remaining obligations. Use `(gm_res r z _ hm _).trans ((gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp' k, hq k⟩ _).trans ?_)` and prove the remaining obligations. Conclude with `(gw_pullIdIso L (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)).symm`.
-/
theorem pmaps_pullIdIso {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (pullIdIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp', Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  refine (gm_res r z _ hm _).trans ((gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp' k, hq k⟩ _).trans ?_)
  exact (gw_pullIdIso L (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)).symm

def cubeMapId {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]

/- English proof (translation)
The claim follows from `(isPullCubical_iff _ _ _).2 ⟨pullIdIso L.L, pgen_pullIdIso L.isLB, pmaps_pullIdIso (K := PUnit) (fun _ => eSec G) (fun _ => 1) L.rig L.rigGen, pmaps_pullIdIso (thφ G (x3 G)) thε c.t c.isGen⟩`.
-/
theorem isPullCubical_id {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G}
    (c : CubicalStr G L) : (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ _ _).2 ⟨pullIdIso L.L, pgen_pullIdIso L.isLB,
    pmaps_pullIdIso (K := PUnit) (fun _ => eSec G) (fun _ => 1) L.rig L.rigGen,
    pmaps_pullIdIso (thφ G (x3 G)) thε c.t c.isGen⟩

/- English proof (translation)
Use `⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩` and prove the remaining obligations. Conclude with `(mul_left_congr (G := G) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm`.
-/
theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (G := G) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

end Ident

/- English proof (translation)
Take `⟨o, ho, hne, hoZ⟩` from `TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ (irreducibleComponent_mem_irreducibleComponents y)`. Take `⟨z, hzo, hzU⟩` from `hd.inter_open_nonempty o ho hne`. Take `⟨g, hg⟩` from `QuasiSober.sober (isIrreducible_irreducibleComponent (x := y)) (isClosed_irreducibleComponent (x := y))`. Conclude with `⟨g, (hg.specializes (hoZ hzo)).mem_open hU hzU, hg.specializes mem_irreducibleComponent⟩`.
-/
theorem exists_gen {X : Type} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {U : Set X} (hU : IsOpen U) (hd : Dense U) (y : X) : ∃ g ∈ U, g ⤳ y := by
  obtain ⟨o, ho, hne, hoZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _
      (irreducibleComponent_mem_irreducibleComponents y)
  obtain ⟨z, hzo, hzU⟩ := hd.inter_open_nonempty o ho hne
  obtain ⟨g, hg⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := y))
    (isClosed_irreducibleComponent (x := y))
  exact ⟨g, (hg.specializes (hoZ hzo)).mem_open hU hzU, hg.specializes mem_irreducibleComponent⟩

/- English proof (translation)
Take `⟨hbij, -⟩` from `h`. Choose the witnesses or unpack the hypotheses as in `⟨q, rfl⟩ : p ∈ Set.range (X.fromSpecStalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) := by`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `hp`. Establish `hF : IsField (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ))` using `MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hbij).toMulEquiv`.

Establish `hsub : Subsingleton (PrimeSpectrum (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)))`. Use `letI := hF.toField`. Use `infer_instance`. Establish `hq : q = IsLocalRing.closedPoint (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ))` using `@Subsingleton.elim _ hsub q _`. Rewrite using `[hq]`.

Conclude with `Scheme.fromSpecStalk_closedPoint`.
-/
theorem eq_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    {p : X} (hp : p ⤳ genPt ξ) : p = genPt ξ := by
  obtain ⟨hbij, -⟩ := h
  obtain ⟨q, rfl⟩ : p ∈ Set.range (X.fromSpecStalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hp
  have hF : IsField (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hbij).toMulEquiv
  have hsub : Subsingleton (PrimeSpectrum (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ))) := by
    letI := hF.toField
    infer_instance
  have hq : q = IsLocalRing.closedPoint (X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ)) :=
    @Subsingleton.elim _ hsub q _
  rw [hq]
  exact Scheme.fromSpecStalk_closedPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
  {Y : Model Xo c β} {Y' : Model Xo c β'} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

def sabMapId {T : Scheme.{0}} (t : SAB H T) : SABMap t t (𝟙 T) where
  cm := cubeMapId t.G
  cart := isGrpPullback_id t.G
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.G t.cub

end GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag
