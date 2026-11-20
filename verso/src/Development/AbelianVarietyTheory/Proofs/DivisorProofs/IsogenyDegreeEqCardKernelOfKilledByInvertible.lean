import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrankStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.DegSep

variable {S : Scheme.{0}}

/- English proof (translation)
Establish `h` using `Over.w (toUnit T)`. Express the relevant statement in the definitionally equal form `(toUnit T ≫ η[G]).left = _`. Rewrite using `[Over.comp_left]`. Use `congr 1`.
-/
theorem one_left' (T : Over S) (G : Over S) [GrpObj G] : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  have h := Over.w (toUnit T)
  change (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left]
  congr 1

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]`.
-/
theorem comp_pow_id (T G : Over S) [GrpObj G] (x : T ⟶ G) (n : ℕ) : x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

end GlobalTheory.AV.DegSep

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (K : Type) [Field K] (X : Scheme) (f : X ⟶ Sp K) [IsFinite f] : LocallyOfFinitePresentation f := inferInstance

namespace GlobalTheory.AV.DegSep

/- English proof (translation)
Establish `h : IsUnit (n : K)` using `hn.isUnit`. Use `h.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom` as an intermediate fact. Simplify using `using this`.
-/
theorem isUnit_natCast_Γ (K : Type) [Field K] (n : ℕ) (hn : (n : K) ≠ 0) : IsUnit (n : Γ(Sp K, ⊤)) := by
  have h : IsUnit (n : K) := hn.isUnit
  have := h.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  simpa using this

/- English proof (translation)
Establish `hfl : Flat f.hom.left` using `(GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hiso).2.1`. Establish `hfin : IsFinite f.hom.left` using `hiso.1`. Establish `hprop : IsProper B.X.hom` using `B.ab.proper`. Set `e : Sp K ⟶ B.X.left` to `η[B.X].left`. Establish `he1 : e ≫ B.X.hom = 𝟙 _` using `Over.w η[B.X]`.

Establish `hecl : IsClosedImmersion e`. Establish `: IsClosedImmersion (e ≫ B.X.hom)` using `by rw [he1]; infer_instance`. Conclude with `IsClosedImmersion.of_comp e B.X.hom`. Set `p` to `pullback.snd f.hom.left e`. Set `i` to `pullback.fst f.hom.left e`.

Establish `hpi : i ≫ A.X.hom = p`. Combine the equalities or inequalities in the displayed calculation. Establish `hifu : FormallyUnramified i` using `inferInstance`. Set `T : Over (Sp K)` to `Over.mk (i ≫ A.X.hom)`. Set `x : T ⟶ A.X` to `Over.homMk i`.

Establish `hx1 : x ≫ f.hom = 1` using `by ext1`. Rewrite using `[Over.comp_left, one_left']`. Express the relevant statement in the definitionally equal form `i ≫ f.hom.left = (i ≫ A.X.hom) ≫ e`. Rewrite using `[hpi, pullback.condition]`. Establish `hxn` using `hker T x hx1`.

Establish `hleft : i ≫ (Out.mulA A.X n).left = p ≫ η[A.X].left`. Establish `h : (x ^ n).left = (1 : T ⟶ A.X).left` using `by rw [hxn]`. Rewrite `h` using `[← comp_pow_id, one_left']`. Express the relevant statement in the definitionally equal form `i ≫ (Out.mulA A.X n).left = _ at h`. Rewrite using `[h]`.

Express the relevant statement in the definitionally equal form `(i ≫ A.X.hom) ≫ _ = _`. Rewrite using `[hpi]`. Set `j : pullback f.hom.left e ⟶ pullback (Out.mulA A.X n).left η[A.X].left` to `pullback.lift i p hleft`. Establish `hmu : FormallyUnramified (Out.mulA A.X n).left` using `GlobalTheory.formallyUnramified_mulA (Sp K) A.X n (isUnit_natCast_Γ K n hn)`. Establish `hsnd : FormallyUnramified (pullback.snd (Out.mulA A.X n).left η[A.X].left)` using `MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hmu`.

Establish `hjfu : FormallyUnramified j`. Establish `: FormallyUnramified (j ≫ pullback.fst _ _)`. Rewrite using `[pullback.lift_fst]`. Conclude with `hifu`. Conclude with `FormallyUnramified.of_comp j (pullback.fst _ _)`.

Establish `hpfu : FormallyUnramified p`. Establish `: j ≫ pullback.snd _ _ = p` using `pullback.lift_snd _ _ _`. Rewrite using `[← this]`. Conclude with `MorphismProperty.comp_mem (@FormallyUnramified) _ _ hjfu hsnd`. Establish `hpet : Etale p` using `Etale.of_formallyUnramified_of_flat p`.

Set `t : Sp (AlgebraicClosure K) ⟶ Sp K` to `(ptOver K (AlgebraicClosure K)).hom`. Take `⟨-, hcard⟩` from `GlobalTheory.FinEt.card_points_eq_finrank p t (IsLocalRing.closedPoint _)`. Rewrite `hcard` using `[Scheme.Hom.finrank_pullback_snd]`. Establish `horig : e (t (IsLocalRing.closedPoint _)) = B.origin`. Rewrite using `[origin, one_left']`.

Express the relevant statement in the definitionally equal form `e _ = (𝟙 (Sp K) ≫ e) _`. Rewrite using `[Category.id_comp]`. Use `congr 1`. Conclude with `Subsingleton.elim _ _`. Rewrite `hcard` using `[horig]`.

Rewrite using `[deg, if_pos hiso, ← hcard]`. Use `symm`. Use `Nat.card_congr ?_` and prove the remaining obligations. Conclude with `{ toFun := fun y => ⟨pullback.lift y.1.left t (by`. Establish `h` using `y.2`.

Rewrite `h` using `[MonoidHom.mem_ker, ptMap_apply]`. Establish `h2 : (y.1 ≫ f.hom).left = (1 : ptOver K (AlgebraicClosure K) ⟶ B.X).left` using `by rw [h]`. Rewrite `h2` using `[Over.comp_left, one_left']`. Conclude with `h2), pullback.lift_snd _ _ _⟩`. Use `invFun := fun y => ⟨Over.homMk (y.1 ≫ i) (by`.

Express the relevant statement in the definitionally equal form `(y.1 ≫ i) ≫ A.X.hom = t`. Rewrite using `[Category.assoc, hpi, y.2]), by`. Rewrite using `[MonoidHom.mem_ker, ptMap_apply]`. Use `ext1`. Rewrite using `[Over.comp_left, one_left']`.

Express the relevant statement in the definitionally equal form `(y.1 ≫ i) ≫ f.hom.left = t ≫ e`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩`. Use `left_inv := fun y => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `ext1`.

Conclude with `pullback.lift_fst _ _ _`. Use `right_inv := fun y => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `pullback.lift_fst _ _ _`.

Rewrite using `[pullback.lift_snd]`. Conclude with `y.2.symm }`.
-/
theorem deg_eq_card_ker (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ) (hn : (n : K) ≠ 0)
    (hiso : IsIsogeny f) (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) :
    deg f = Nat.card (ptMap f).ker := by
  have hfl : Flat f.hom.left := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hiso).2.1
  have hfin : IsFinite f.hom.left := hiso.1
  have hprop : IsProper B.X.hom := B.ab.proper
  let e : Sp K ⟶ B.X.left := η[B.X].left
  have he1 : e ≫ B.X.hom = 𝟙 _ := Over.w η[B.X]
  have hecl : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ B.X.hom) := by rw [he1]; infer_instance
    exact IsClosedImmersion.of_comp e B.X.hom
  let p := pullback.snd f.hom.left e
  let i := pullback.fst f.hom.left e
  have hpi : i ≫ A.X.hom = p := by
    calc i ≫ A.X.hom = i ≫ f.hom.left ≫ B.X.hom := by rw [Over.w f.hom]
      _ = p ≫ e ≫ B.X.hom := by rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = p := by rw [he1, Category.comp_id]
  have hifu : FormallyUnramified i := inferInstance

  let T : Over (Sp K) := Over.mk (i ≫ A.X.hom)
  let x : T ⟶ A.X := Over.homMk i
  have hx1 : x ≫ f.hom = 1 := by
    ext1
    rw [Over.comp_left, one_left']
    change i ≫ f.hom.left = (i ≫ A.X.hom) ≫ e
    rw [hpi, pullback.condition]
  have hxn := hker T x hx1
  have hleft : i ≫ (Out.mulA A.X n).left = p ≫ η[A.X].left := by
    have h : (x ^ n).left = (1 : T ⟶ A.X).left := by rw [hxn]
    rw [← comp_pow_id, one_left'] at h
    change i ≫ (Out.mulA A.X n).left = _ at h
    rw [h]
    change (i ≫ A.X.hom) ≫ _ = _
    rw [hpi]
  let j : pullback f.hom.left e ⟶ pullback (Out.mulA A.X n).left η[A.X].left :=
    pullback.lift i p hleft
  have hmu : FormallyUnramified (Out.mulA A.X n).left :=
    GlobalTheory.formallyUnramified_mulA (Sp K) A.X n (isUnit_natCast_Γ K n hn)
  have hsnd : FormallyUnramified (pullback.snd (Out.mulA A.X n).left η[A.X].left) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hmu
  have hjfu : FormallyUnramified j := by
    have : FormallyUnramified (j ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; exact hifu
    exact FormallyUnramified.of_comp j (pullback.fst _ _)
  have hpfu : FormallyUnramified p := by
    have : j ≫ pullback.snd _ _ = p := pullback.lift_snd _ _ _
    rw [← this]
    exact MorphismProperty.comp_mem (@FormallyUnramified) _ _ hjfu hsnd
  have hpet : Etale p := Etale.of_formallyUnramified_of_flat p

  let t : Sp (AlgebraicClosure K) ⟶ Sp K := (ptOver K (AlgebraicClosure K)).hom
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t (IsLocalRing.closedPoint _)
  rw [Scheme.Hom.finrank_pullback_snd] at hcard
  have horig : e (t (IsLocalRing.closedPoint _)) = B.origin := by
    rw [origin, one_left']
    change e _ = (𝟙 (Sp K) ≫ e) _
    rw [Category.id_comp]
    congr 1
    exact Subsingleton.elim _ _
  rw [horig] at hcard
  rw [deg, if_pos hiso, ← hcard]
  symm
  refine Nat.card_congr ?_
  exact
    { toFun := fun y => ⟨pullback.lift y.1.left t (by
          have h := y.2
          rw [MonoidHom.mem_ker, ptMap_apply] at h
          have h2 : (y.1 ≫ f.hom).left = (1 : ptOver K (AlgebraicClosure K) ⟶ B.X).left := by rw [h]
          rw [Over.comp_left, one_left'] at h2
          exact h2), pullback.lift_snd _ _ _⟩
      invFun := fun y => ⟨Over.homMk (y.1 ≫ i) (by
          change (y.1 ≫ i) ≫ A.X.hom = t
          rw [Category.assoc, hpi, y.2]), by
          rw [MonoidHom.mem_ker, ptMap_apply]
          ext1
          rw [Over.comp_left, one_left']
          change (y.1 ≫ i) ≫ f.hom.left = t ≫ e
          rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩
      left_inv := fun y => by
        apply Subtype.ext
        ext1
        exact pullback.lift_fst _ _ _
      right_inv := fun y => by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · rw [pullback.lift_snd]; exact y.2.symm }

end GlobalTheory.AV.DegSep

namespace GlobalTheory.AV.DegSep

/- English proof (translation)
Introduce `K _ A B f n hn hiso hker` and use `deg_eq_card_ker K A B f n hn hiso hker`.
-/
theorem deg_eq_card_ker_of_killed : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ), (n : K) ≠ 0 →
    IsIsogeny f → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) →
    deg f = Nat.card (ptMap f).ker :=
  fun K _ A B f n hn hiso hker => deg_eq_card_ker K A B f n hn hiso hker

end GlobalTheory.AV.DegSep
