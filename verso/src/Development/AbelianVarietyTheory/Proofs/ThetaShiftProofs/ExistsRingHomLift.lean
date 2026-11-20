import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtensionComplexPointsEqCharactersStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ArcModel

open FrameValue

section Lift

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

/- English proof (translation)
Rewrite using `[← u.ker]`. Establish `e : u.ex z = u.ex (z - w) * u.ex w` using `by rw [← u.ex_add, sub_add_cancel]`. Rewrite using `[e]`. Conclude with `mul_eq_right`.
-/
theorem ex_eq_iff (z w : Fin g → ℂ) : u.ex z = u.ex w ↔ z - w ∈ u.Λ := by
  rw [← u.ker]
  have e : u.ex z = u.ex (z - w) * u.ex w := by rw [← u.ex_add, sub_add_cancel]
  rw [e]
  exact mul_eq_right

/- English proof (translation)
The claim follows from `(u.ker 0).2 u.Λ.zero_mem`.
-/
theorem ex_zero' : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

/- English proof (translation)
Use `haveI := u.discrete`. Establish `hc : Continuous fun z => (⟨F z - G z, (ex_eq_iff u _ _).1 (h z)⟩ : u.Λ)` using `Continuous.subtype_mk (F.continuous_of_finiteDimensional.sub G.continuous_of_finiteDimensional) _`. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Use `congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`.
-/
theorem lin_ext {F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : ∀ z, u.ex (F z) = u.ex (G z)) : F = G := by
  haveI := u.discrete
  have hc : Continuous fun z => (⟨F z - G z, (ex_eq_iff u _ _).1 (h z)⟩ : u.Λ) :=
    Continuous.subtype_mk (F.continuous_of_finiteDimensional.sub G.continuous_of_finiteDimensional) _
  refine LinearMap.ext fun z => ?_
  have := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa [sub_eq_zero] using this

variable [IsCommMonObj A] {O : Type} [CommRing O]

/- English proof (translation)
Use `choose F hF using fun x => h (r.act x) (r.hom x)`. Establish `add : ∀ a b, F (a + b) = F a + F b` using `fun a b => lin_ext u fun z => by`. Rewrite using `[LinearMap.add_apply, u.ex_add, hF, hF, hF, r.map_add]`. Conclude with `MonObj.comp_mul _ _ _`. Use `⟨{ toFun := F, map_one' := lin_ext u fun z => ?_, map_mul' := fun a b => lin_ext u fun z => ?_, map_zero' := ?_, map_add' := add }, hF⟩` and prove the remaining obligations.

Rewrite using `[hF, r.map_one, Category.comp_id]`. Both sides reduce to the same expression. Rewrite using `[Module.End.mul_apply, hF, hF, hF, r.map_mul, Category.assoc]`. Simplify using `using add 0 0`.
-/
theorem exists_ringHom_lift (r : Out.RingAct A O)
    (h : ∀ f : A ⟶ A, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f) :
    ∃ F : O →+* Module.End ℂ (Fin g → ℂ), ∀ x z, u.ex (F x z) = u.ex z ≫ r.act x := by
  choose F hF using fun x => h (r.act x) (r.hom x)
  have add : ∀ a b, F (a + b) = F a + F b := fun a b => lin_ext u fun z => by
    rw [LinearMap.add_apply, u.ex_add, hF, hF, hF, r.map_add]
    exact MonObj.comp_mul _ _ _
  refine ⟨{ toFun := F, map_one' := lin_ext u fun z => ?_, map_mul' := fun a b => lin_ext u fun z => ?_,
            map_zero' := ?_, map_add' := add }, hF⟩
  · rw [hF, r.map_one, Category.comp_id]; rfl
  · rw [Module.End.mul_apply, hF, hF, hF, r.map_mul, Category.assoc]
  · simpa using add 0 0

/- English proof (translation)
Use `letI : Module O (Fin g → ℂ) := Module.compHom _ F`. Establish `c0 : c 0 = 1`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `(mul_eq_left (a := c 0) (b := c 0)).1 this.symm`.

Set `S : Submodule O (X × (Fin g → ℂ))` to `{ carrier := {p | u.ex p.2 = c p.1} zero_mem' := (ex_zero' u).trans c0.symm add_mem' := fun {p q} hp hq => by`. Express the relevant statement in the definitionally equal form `u.ex (p.2 + q.2) = c (p.1 + q.1)`. Rewrite using `[u.ex_add, hadd, hp, hq]`. Both sides reduce to the same expression. Use the proof step `smul_mem' := fun a p hp => by`.

Express the relevant statement in the definitionally equal form `u.ex (F a p.2) = c (a • p.1)`. Rewrite using `[hF, hlin, hp] }`. Take `⟨s, hs⟩` from `Module.projective_lifting_property ((LinearMap.fst O X _).comp S.subtype) LinearMap.id (fun x => by`. Take `⟨z, hz⟩` from `u.ex_onto (c x)`. Conclude with `⟨⟨(x, z), hz⟩, rfl⟩)`.

Use `⟨(((LinearMap.snd O X _).comp S.subtype).comp s).toAddMonoidHom, fun a x => ?_, fun x => ?_⟩` and prove the remaining obligations. Conclude with `(((LinearMap.snd O X _).comp S.subtype).comp s).map_smul a x`. Conclude with `(s x).2.trans (congrArg c (LinearMap.congr_fun hs x))`.
-/
theorem exists_lift_points (r : Out.RingAct A O) (F : O →+* Module.End ℂ (Fin g → ℂ))
    (hF : ∀ x z, u.ex (F x z) = u.ex z ≫ r.act x) {X : Type} [AddCommGroup X] [Module O X] [Module.Projective O X]
    (c : X → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (hadd : ∀ a b, c (a + b) = padd A (c a) (c b))
    (hlin : ∀ (a : O) y, c (a • y) = c y ≫ r.act a) :
    ∃ ct : X →+ (Fin g → ℂ), (∀ (a : O) x, ct (a • x) = F a (ct x)) ∧ ∀ x, u.ex (ct x) = c x := by
  letI : Module O (Fin g → ℂ) := Module.compHom _ F
  have c0 : c 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left (a := c 0) (b := c 0)).1 this.symm
  let S : Submodule O (X × (Fin g → ℂ)) :=
    { carrier := {p | u.ex p.2 = c p.1}
      zero_mem' := (ex_zero' u).trans c0.symm
      add_mem' := fun {p q} hp hq => by
        change u.ex (p.2 + q.2) = c (p.1 + q.1)
        rw [u.ex_add, hadd, hp, hq]; rfl
      smul_mem' := fun a p hp => by
        change u.ex (F a p.2) = c (a • p.1)
        rw [hF, hlin, hp] }
  obtain ⟨s, hs⟩ := Module.projective_lifting_property ((LinearMap.fst O X _).comp S.subtype) LinearMap.id
    (fun x => by
      obtain ⟨z, hz⟩ := u.ex_onto (c x)
      exact ⟨⟨(x, z), hz⟩, rfl⟩)
  refine ⟨(((LinearMap.snd O X _).comp S.subtype).comp s).toAddMonoidHom, fun a x => ?_, fun x => ?_⟩
  · exact (((LinearMap.snd O X _).comp S.subtype).comp s).map_smul a x
  · exact (s x).2.trans (congrArg c (LinearMap.congr_fun hs x))

end Lift

section Values

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ ≫ p.left = _`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]`. Conclude with `(congrArg (· ≫ p.left) (Spec.map_id _)).trans (Category.id_comp _)`.
-/
theorem jFK_comp_point {B : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ B) :
    Out.jFK (R := ℂ) ℂ ≫ (toUnit (Out.TK ℂ) ≫ p).left = p.left := by
  change Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ ≫ p.left = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact (congrArg (· ≫ p.left) (Spec.map_id _)).trans (Category.id_comp _)

/- English proof (translation)
Simplify using `using jFK_comp_point (𝟙 (𝟙_ (Over (Sp ℂ))))`.
-/
theorem jFK_comp_toUnit : Out.jFK (R := ℂ) ℂ ≫ (toUnit (Out.TK ℂ)).left = 𝟙 (Sp ℂ) := by
  simpa using jFK_comp_point (𝟙 (𝟙_ (Over (Sp ℂ))))

variable (D : Out.DegPre ℂ) {g : ℕ} (u : HolUnif D.P.A D.P.L g) (ct : D.X →+ (Fin g → ℂ))

def psiVal (x : D.X) : ℂ := genVal u D.P.isLB (D.psi x) (Out.jFK (R := ℂ) ℂ) (fun _ => ct x)

def tauVal (a b : D.X) : ℂ := psiVal D u ct (a + b) * (psiVal D u ct a)⁻¹ * (psiVal D u ct b)⁻¹

def tauLift (a b : D.X) : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit → Fin g → ℂ :=
  Sum.elim (Sum.elim (Sum.elim (fun _ => ct (a + b)) (fun _ => ct a)) (fun _ => ct b)) (fun _ => 0)

variable {D u ct}

/- English proof (translation)
Rewrite using `[hc]`. Conclude with `jFK_comp_point _`.
-/
theorem jFK_comp_xK (hc : ∀ x, u.ex (ct x) = D.c x) (x : D.X) :
    Out.jFK (R := ℂ) ℂ ≫ D.xK x = (u.ex (ct x)).left := by
  rw [hc]; exact jFK_comp_point _

/- English proof (translation)
The claim follows from `genVal_ne_zero _ _ fun _ => jFK_comp_xK hc x`.
-/
theorem psiVal_ne_zero (hc : ∀ x, u.ex (ct x) = D.c x) (x : D.X) : psiVal D u ct x ≠ 0 :=
  genVal_ne_zero _ _ fun _ => jFK_comp_xK hc x

/- English proof (translation)
Unfold `Out.DegPre.tau Out.DegPre.rigK`. Rewrite using `[genVal_mul, genVal_mul, genVal_mul, genVal_inv, genVal_inv, genVal_inv, genVal_pull, jFK_comp_toUnit]`. Use `genVal_rig D.P.isLB hr` as an intermediate fact. Use `erw [this]`. Rewrite using `[inv_one, _root_.mul_one]`.

Both sides reduce to the same expression.
-/
theorem genVal_tau (hr : u.IsRig D.rig) (a b : D.X) :
    genVal u D.P.isLB (D.tau a b) (Out.jFK (R := ℂ) ℂ) (tauLift D ct a b) = tauVal D u ct a b := by
  unfold Out.DegPre.tau Out.DegPre.rigK
  rw [genVal_mul, genVal_mul, genVal_mul, genVal_inv, genVal_inv, genVal_inv, genVal_pull, jFK_comp_toUnit]
  have := genVal_rig D.P.isLB hr
  erw [this]
  rw [inv_one, _root_.mul_one]
  rfl

/- English proof (translation)
Introduce and unpack `(((_ | _) | _) | _)`. Conclude with `jFK_comp_xK hc _`. Conclude with `jFK_comp_xK hc _`. Conclude with `jFK_comp_xK hc _`. Express the relevant statement in the definitionally equal form `_ ≫ _ ≫ _ = (u.ex 0).left`.

Rewrite using `[← Category.assoc, jFK_comp_toUnit, ex_zero', Hom.one_def]`. Simplify using `[eSec]`.
-/
theorem isLift_tau (hc : ∀ x, u.ex (ct x) = D.c x) (a b : D.X) :
    IsLift u (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => D.xK (a + b)) (fun _ : PUnit => D.xK a))
      (fun _ : PUnit => D.xK b)) (fun _ : PUnit => (toUnit (Out.TK ℂ)).left ≫ eSec D.P.A))
      (Out.jFK (R := ℂ) ℂ) (tauLift D ct a b) := by
  rintro (((_ | _) | _) | _)
  · exact jFK_comp_xK hc _
  · exact jFK_comp_xK hc _
  · exact jFK_comp_xK hc _
  · change _ ≫ _ ≫ _ = (u.ex 0).left
    rw [← Category.assoc, jFK_comp_toUnit, ex_zero', Hom.one_def]
    simp [eSec]

variable {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

/- English proof (translation)
Establish `e` using `genVal_corr (u := u) D.P.isLB (he x) (y := Out.jFK (R := ℂ) ℂ) (z := Sum.elim (fun _ => ct (-x)) ![-ct x, ct x]) (z' := fun _ => ct x) (by`. Introduce and unpack `(_ | k)`. Conclude with `jFK_comp_xK hc _`. Express the relevant statement in the definitionally equal form `_ ≫ _ ≫ _ = _`. Rewrite using `[← Category.assoc, jFK_comp_xK hc]`.

Conclude with `isLift_sym u _ k)`. Use the proof step `(fun _ => jFK_comp_xK hc x) (fun f => by simp [Fintype.prod_sum_type])`. Rewrite `e` using `[genVal_mul, genVal_pull, jFK_comp_xK hc]`. Establish `s` using `(genVal_sym D.P.isLB h D.sym D.sym_gen D.sym_rig).1 (ct x)`. Conclude with `(_root_.mul_one _).symm.trans ((congrArg _ s.symm).trans e)`.
-/
theorem psiVal_neg (h : u.IsAH Hm χ) (hc : ∀ x, u.ex (ct x) = D.c x) (he : D.PsiEven) (x : D.X) :
    psiVal D u ct (-x) = psiVal D u ct x := by
  have e := genVal_corr (u := u) D.P.isLB (he x) (y := Out.jFK (R := ℂ) ℂ)
    (z := Sum.elim (fun _ => ct (-x)) ![-ct x, ct x]) (z' := fun _ => ct x)
    (by
      rintro (_ | k)
      · exact jFK_comp_xK hc _
      · change _ ≫ _ ≫ _ = _
        rw [← Category.assoc, jFK_comp_xK hc]
        exact isLift_sym u _ k)
    (fun _ => jFK_comp_xK hc x) (fun f => by simp [Fintype.prod_sum_type])
  rw [genVal_mul, genVal_pull, jFK_comp_xK hc] at e
  have s := (genVal_sym D.P.isLB h D.sym D.sym_gen D.sym_rig).1 (ct x)
  exact (_root_.mul_one _).symm.trans ((congrArg _ s.symm).trans e)

/- English proof (translation)
Establish `hp : Out.jFK (R` using `ℂ) ℂ ≫ D.pt3 a a' b = (CubeValues.pt3 u ![ct a, ct a', ct b]).left := by`. Rewrite using `[← jFK_comp_point]`. Simplify using `only [CubeValues.pt3, comp_lift, Out.DegPre.pt3, ← hc]`. Both sides reduce to the same expression. Establish `e` using `genVal_corr (u := u) D.P.isLB (hb a a' b) (y := Out.jFK (R := ℂ) ℂ) (z := Sum.elim (tauLift D ct (a + a') b) (cubeLift ![ct a, ct a', ct b])) (z' := Sum.elim (tauLift D ct a b) (tauLift D ct a' b)) (by`.

Introduce and unpack `(k | k)`. Conclude with `isLift_tau hc _ _ k`. Express the relevant statement in the definitionally equal form `_ ≫ _ ≫ _ = _`. Rewrite using `[← Category.assoc, hp]`. Conclude with `isLift_cube u _ k)`.

Use the proof step `(by`. Introduce and unpack `(k | k)`. Use `exacts [isLift_tau hc _ _ k, isLift_tau hc _ _ k])`. Use the proof step `(fun f => by`. Use `prod_thK (fun I => f (∑ i ∈ I, ![ct a, ct a', ct b] i))` as an intermediate fact.

Simplify using `only [(sum_three _).1, (sum_three _).2.1, (sum_three _).2.2.1, (sum_three _).2.2.2] at this`. Use `(Fintype.prod_sum_type _).trans ((congrArg (_ * ·) this).trans ?_)` and prove the remaining obligations. Simplify using `[tauLift, Fintype.prod_sum_type]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`.

Use the proof step `abel)`. Use `replace e := (genVal_mul _ _ _ _ _).symm.trans (e.trans (genVal_mul _ _ _ _ _))`. Establish `s` using `genVal_cube_of_face D.P.isLB h D.cub.t D.cub.isGen (D.cub.face 0) ![ct a, ct a', ct b]`. Rewrite `s` using `[← hp]`. Use `replace s := (genVal_pull _ _ _ _ _).trans s`.

Rewrite using `[← genVal_tau hr, ← genVal_tau hr, ← genVal_tau hr]`. Conclude with `(_root_.mul_one _).symm.trans ((congrArg _ s.symm).trans e)`.
-/
theorem tauVal_add (h : u.IsAH Hm χ) (hr : u.IsRig D.rig) (hc : ∀ x, u.ex (ct x) = D.c x) (hb : D.TauBimult)
    (a a' b : D.X) : tauVal D u ct (a + a') b = tauVal D u ct a b * tauVal D u ct a' b := by
  have hp : Out.jFK (R := ℂ) ℂ ≫ D.pt3 a a' b = (CubeValues.pt3 u ![ct a, ct a', ct b]).left := by
    rw [← jFK_comp_point]
    simp only [CubeValues.pt3, comp_lift, Out.DegPre.pt3, ← hc]
    rfl
  have e := genVal_corr (u := u) D.P.isLB (hb a a' b) (y := Out.jFK (R := ℂ) ℂ)
    (z := Sum.elim (tauLift D ct (a + a') b) (cubeLift ![ct a, ct a', ct b]))
    (z' := Sum.elim (tauLift D ct a b) (tauLift D ct a' b))
    (by
      rintro (k | k)
      · exact isLift_tau hc _ _ k
      · change _ ≫ _ ≫ _ = _
        rw [← Category.assoc, hp]
        exact isLift_cube u _ k)
    (by
      rintro (k | k)
      exacts [isLift_tau hc _ _ k, isLift_tau hc _ _ k])
    (fun f => by
      have := prod_thK (fun I => f (∑ i ∈ I, ![ct a, ct a', ct b] i))
      simp only [(sum_three _).1, (sum_three _).2.1, (sum_three _).2.2.1, (sum_three _).2.2.2] at this
      refine (Fintype.prod_sum_type _).trans ((congrArg (_ * ·) this).trans ?_)
      simp [tauLift, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  replace e := (genVal_mul _ _ _ _ _).symm.trans (e.trans (genVal_mul _ _ _ _ _))
  have s := genVal_cube_of_face D.P.isLB h D.cub.t D.cub.isGen (D.cub.face 0) ![ct a, ct a', ct b]
  rw [← hp] at s
  replace s := (genVal_pull _ _ _ _ _).trans s
  rw [← genVal_tau hr, ← genVal_tau hr, ← genVal_tau hr]
  exact (_root_.mul_one _).symm.trans ((congrArg _ s.symm).trans e)

/- English proof (translation)
Take `⟨r, hr₁, hr₀⟩` from `exists_ros hG D.P.isAb D.P.isLB f f' hR`. Take `⟨adj, s⟩` from `genVal_rosati D.P.isLB h hF hF' r hr₁ hr₀`. Use `⟨adj, fun y y' => ?_⟩` and prove the remaining obligations. Establish `hp : Out.jFK (R` using `ℂ) ℂ ≫ D.pt2 y y' = (lift (u.ex (ct y)) (u.ex (ct y'))).left := by`. Rewrite using `[← jFK_comp_point]`.

Simplify using `only [comp_lift, Out.DegPre.pt2, ← hc]`. Establish `e` using `genVal_corr (u := u) D.P.isLB (hb r hr₁ hr₀ y y') (y := Out.jFK (R := ℂ) ℂ) (z := Sum.elim (tauLift D ct (a y) y') (rosatiLift F G (ct y) (ct y'))) (z' := tauLift D ct y (a' y')) (by`. Introduce and unpack `(k | k)`. Conclude with `isLift_tau hc _ _ k`. Express the relevant statement in the definitionally equal form `_ ≫ _ ≫ _ = _`.

Rewrite using `[← Category.assoc, hp]`. Conclude with `isLift_rosati hF hF' _ _ k)`. Use the proof step `(isLift_tau hc _ _)`. Use the proof step `(fun f => by`. Simplify using `[Fintype.prod_sum_type, tauLift, rosatiLift, Out.rosatiε, Fin.prod_univ_six, ha, ha']`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Use the proof step `abel)`. Rewrite `e` using `[genVal_mul, genVal_pull, hp]`. Rewrite using `[← genVal_tau hr, ← genVal_tau hr]`.

Conclude with `(_root_.mul_one _).symm.trans ((congrArg _ (s _ _).symm).trans e)`.
-/
theorem tauVal_bal (hG : Out.GlobalFnsSt) (h : u.IsAH Hm χ) (hr : u.IsRig D.rig) (hc : ∀ x, u.ex (ct x) = D.c x)
    {f f' : D.P.A ⟶ D.P.A} [IsMonHom f] [IsMonHom f'] (hR : Out.RosatiAdj D.P.A D.P.L f f')
    {F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) (hF' : ∀ z, u.ex (G z) = u.ex z ≫ f')
    {a a' : D.X → D.X} (ha : ∀ x, ct (a x) = F (ct x)) (ha' : ∀ x, ct (a' x) = G (ct x)) (hb : D.TauBal f f' a a') :
    (∀ x z, hermForm Hm (F x) z = hermForm Hm x (G z)) ∧
      ∀ y y', tauVal D u ct (a y) y' = tauVal D u ct y (a' y') := by
  obtain ⟨r, hr₁, hr₀⟩ := exists_ros hG D.P.isAb D.P.isLB f f' hR
  obtain ⟨adj, s⟩ := genVal_rosati D.P.isLB h hF hF' r hr₁ hr₀
  refine ⟨adj, fun y y' => ?_⟩
  have hp : Out.jFK (R := ℂ) ℂ ≫ D.pt2 y y' = (lift (u.ex (ct y)) (u.ex (ct y'))).left := by
    rw [← jFK_comp_point]
    simp only [comp_lift, Out.DegPre.pt2, ← hc]
  have e := genVal_corr (u := u) D.P.isLB (hb r hr₁ hr₀ y y') (y := Out.jFK (R := ℂ) ℂ)
    (z := Sum.elim (tauLift D ct (a y) y') (rosatiLift F G (ct y) (ct y')))
    (z' := tauLift D ct y (a' y'))
    (by
      rintro (k | k)
      · exact isLift_tau hc _ _ k
      · change _ ≫ _ ≫ _ = _
        rw [← Category.assoc, hp]
        exact isLift_rosati hF hF' _ _ k)
    (isLift_tau hc _ _)
    (fun f => by
      simp [Fintype.prod_sum_type, tauLift, rosatiLift, Out.rosatiε, Fin.prod_univ_six, ha, ha']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  rw [genVal_mul, genVal_pull, hp] at e
  rw [← genVal_tau hr, ← genVal_tau hr]
  exact (_root_.mul_one _).symm.trans ((congrArg _ (s _ _).symm).trans e)

end Values

/- English proof (translation)
Introduce `hL _ hT E _ _ _ H D l c O _ β _ _ b a`. Use `letI := H.starRing`. Take `⟨u, Hm, χ, Ef, hAH, hrig, ht₁, ht₂, hend, hpow, hEf, hbij, -⟩` from `hT a.D₀.P a.D₀.rig a.D₀.rig_gen`. Take `⟨F, hF⟩` from `exists_ringHom_lift u a.oa.onB.toRingAct hend`. Use `haveI : Module.Projective (𝓞 E) a.D₀.X := Forms.projective_of_int _ _`.

Use `haveI : Module.Finite (𝓞 E) a.D₀.X := Module.Finite.of_restrictScalars_finite ℤ _ _`. Take `⟨ct, hct, hc⟩` from `exists_lift_points u a.oa.onB.toRingAct F hF a.D₀.c a.D₀.c_add a.oa.c_lin`. Establish `bal` using `fun x : 𝓞 E => haveI := a.oa.onB.hom x haveI := a.oa.onB.hom (star x) tauVal_bal hL.globalFns hAH hrig hc (a.oa.onB.rosati x) (hF x) (hF (star x)) (hct x) (hct (star x)) (a.oa.tau_bal x)`. Establish `ne` using `psiVal_ne_zero hc`. Establish `symm : ∀ y x, tauVal a.D₀ u ct y x = tauVal a.D₀ u ct x y` using `fun y x => by`.

Rewrite using `[tauVal, tauVal, add_comm, mul_right_comm]`. Establish `hw : H.w0 + star H.w0 = 1`. Express the relevant statement in the definitionally equal form `H.w0 + H.bar H.w0 = 1`. Rewrite using `[HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]`. Take `⟨T, T₁, T₂, T₃⟩` from `Forms.exists_log_of_bimul_ne_zero hw (tauVal a.D₀ u ct) (fun y x => mul_ne_zero (mul_ne_zero (ne _) (inv_ne_zero (ne _))) (inv_ne_zero (ne _))) (fun y x x' => by rw [symm, tauVal_add hAH hrig hc a.bimult, symm x, symm x']) symm (fun x => (bal x).2)`.

Use `choose ex0 hex0 using fun v : (a.D₀.X →+ ℂ) × (Fin a.D₀.P.g → ℂ) => ((GlobalTheory.T.torusExtension_complexPoints_eq_characters a.D₀ _ u Hm χ ct hAH hrig hc v.2).1 v.1).exists`. Set `A : AnArc (𝓞 E)` to `{ gB := a.D₀.P.g, abelian₂ := u.Λ, discrete := u.discrete, full := u.full, Hm := Hm, Hm_herm := hAH.1, Hm_pos := hAH.2.1, Ef := Ef, Ef_eq := hEf, Ef_bij := hbij, chi := χ, chi_norm := hAH.2.2.1, chi_add := chi_add a.D₀.P.isLB hAH, chi_neg := (genVal_sym a.D₀.P.isLB hAH a.D₀.sym a …`. Express the relevant statement in the definitionally equal form `psiVal a.D₀ u ct (x + y) = psiVal a.D₀ u ct x * psiVal a.D₀ u ct y * Complex.exp (2 * Real.pi * Complex.I * T x y)`. Rewrite using `[← T₃, tauVal]`. Use `ne x` as an intermediate fact.

Use `ne y` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Use `be := a.be, be_symm := a.be_symm, be_pos := a.be_pos, be_adj := a.be_adj,`. Use `be_even := fun x => (dvd_mul_right _ _).trans (a.be_dvd x x) }`. Conclude with `⟨{ star_eq := rfl, A := A, ε := LinearEquiv.refl _ _, be_eq := fun _ _ => rfl, gB_eq := rfl, u := u, lam := rfl, ah := hAH, rig := hrig, tan := ⟨ht₁, ht₂⟩, pow := hpow, act := hF, ct := hc, psi := fun _ => rfl, ex0 := ex0, ex0_b := fun v => (hex0 v).1, arcDict_expZero_section := …`.
-/
theorem nonempty_gtAn : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b),
    letI := H.starRing; Nonempty (GtAn a) := by
  intro hL _ hT E _ _ _ H D l c O _ β _ _ b a
  letI := H.starRing
  obtain ⟨u, Hm, χ, Ef, hAH, hrig, ht₁, ht₂, hend, hpow, hEf, hbij, -⟩ := hT a.D₀.P a.D₀.rig a.D₀.rig_gen
  obtain ⟨F, hF⟩ := exists_ringHom_lift u a.oa.onB.toRingAct hend
  haveI : Module.Projective (𝓞 E) a.D₀.X := Forms.projective_of_int _ _
  haveI : Module.Finite (𝓞 E) a.D₀.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨ct, hct, hc⟩ := exists_lift_points u a.oa.onB.toRingAct F hF a.D₀.c a.D₀.c_add a.oa.c_lin
  have bal := fun x : 𝓞 E =>
    haveI := a.oa.onB.hom x
    haveI := a.oa.onB.hom (star x)
    tauVal_bal hL.globalFns hAH hrig hc (a.oa.onB.rosati x) (hF x) (hF (star x)) (hct x) (hct (star x))
      (a.oa.tau_bal x)
  have ne := psiVal_ne_zero hc
  have symm : ∀ y x, tauVal a.D₀ u ct y x = tauVal a.D₀ u ct x y := fun y x => by
    rw [tauVal, tauVal, add_comm, mul_right_comm]
  have hw : H.w0 + star H.w0 = 1 := by
    change H.w0 + H.bar H.w0 = 1
    rw [HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  obtain ⟨T, T₁, T₂, T₃⟩ := Forms.exists_log_of_bimul_ne_zero hw (tauVal a.D₀ u ct)
    (fun y x => mul_ne_zero (mul_ne_zero (ne _) (inv_ne_zero (ne _))) (inv_ne_zero (ne _)))
    (fun y x x' => by rw [symm, tauVal_add hAH hrig hc a.bimult, symm x, symm x']) symm (fun x => (bal x).2)
  choose ex0 hex0 using fun v : (a.D₀.X →+ ℂ) × (Fin a.D₀.P.g → ℂ) =>
    ((GlobalTheory.T.torusExtension_complexPoints_eq_characters a.D₀ _ u Hm χ ct hAH hrig hc v.2).1 v.1).exists
  let A : AnArc (𝓞 E) :=
    { gB := a.D₀.P.g, abelian₂ := u.Λ, discrete := u.discrete, full := u.full, Hm := Hm, Hm_herm := hAH.1,
      Hm_pos := hAH.2.1, Ef := Ef, Ef_eq := hEf, Ef_bij := hbij, chi := χ, chi_norm := hAH.2.2.1,
      chi_add := chi_add a.D₀.P.isLB hAH,
      chi_neg := (genVal_sym a.D₀.P.isLB hAH a.D₀.sym a.D₀.sym_gen a.D₀.sym_rig).2,
      F := F, F_mem := fun x m hm => lift_mem (hF x) ⟨m, hm⟩, F_adj := fun x => (bal x).1,
      X := a.D₀.X, ct := ct, ct_smul := hct,
      T := LinearMap.toAddMonoidHom'.comp T.toAddMonoidHom, T_symm := T₁, T_adj := T₂,
      psi := fun x => Units.mk0 _ (ne x),
      psi_neg := fun x => Units.ext (psiVal_neg hAH hc a.even x),
      psi_add := fun x y => by
        change psiVal a.D₀ u ct (x + y) = psiVal a.D₀ u ct x * psiVal a.D₀ u ct y *
          Complex.exp (2 * Real.pi * Complex.I * T x y)
        rw [← T₃, tauVal]
        have := ne x
        have := ne y
        field_simp
      be := a.be, be_symm := a.be_symm, be_pos := a.be_pos, be_adj := a.be_adj,
      be_even := fun x => (dvd_mul_right _ _).trans (a.be_dvd x x) }
  exact ⟨{ star_eq := rfl, A := A, ε := LinearEquiv.refl _ _, be_eq := fun _ _ => rfl, gB_eq := rfl, u := u,
           lam := rfl, ah := hAH, rig := hrig, tan := ⟨ht₁, ht₂⟩, pow := hpow, act := hF, ct := hc,
           psi := fun _ => rfl, ex0 := ex0, ex0_b := fun v => (hex0 v).1, arcDict_expZero_section := fun v => (hex0 v).2 }⟩

end GlobalTheory.ArcModel
