import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveBase
import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafHFlasque

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Topology

universe u

namespace GroundTheory.Arith.SchemeCoh

variable {X : Scheme.{u}}

section Local

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

def PrimeDivisor.divisorSubgroup (Z : PrimeDivisor X) (D : WeilDivisor X) :
    AddSubgroup X.functionField where
  carrier := {f | Z.valuation f ≤ WithZero.exp (D Z)}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    have hf' : Z.valuation f ≤ WithZero.exp (D Z) := hf
    have hg' : Z.valuation g ≤ WithZero.exp (D Z) := hg
    exact (Valuation.map_add _ _ _).trans (max_le hf' hg')
  neg_mem' {f} hf := by
    have hf' : Z.valuation f ≤ WithZero.exp (D Z) := hf
    change Z.valuation (-f) ≤ WithZero.exp (D Z)
    rwa [Valuation.map_neg]

/- English proof (translation)
Simplify using `only [PrimeDivisor.divisorSubgroup, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]`.
-/
lemma PrimeDivisor.mem_divisorSubgroup (Z : PrimeDivisor X) (D : WeilDivisor X)
    (f : X.functionField) : f ∈ Z.divisorSubgroup D ↔ Z.valuation f ≤ WithZero.exp (D Z) := by
  simp only [PrimeDivisor.divisorSubgroup, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]

open Classical in

noncomputable def pointSubgroup (D : WeilDivisor X) (x : X) : AddSubgroup X.functionField :=
  if h : ringKrullDim (X.presheaf.stalk x) = 1 then (PrimeDivisor.ofPoint x h).divisorSubgroup D
  else ⊤

/- English proof (translation)
Unfold `pointSubgroup`. Use `split_ifs with h`. Simplify using `only [PrimeDivisor.mem_divisorSubgroup]`. Conclude with `⟨fun hf _ => hf, fun hf => hf h⟩`. Conclude with `⟨fun _ h' => absurd h' h, fun _ => AddSubgroup.mem_top f⟩`.
-/
lemma mem_pointSubgroup_iff (D : WeilDivisor X) (x : X) (f : X.functionField) :
    f ∈ pointSubgroup D x ↔ ∀ h : ringKrullDim (X.presheaf.stalk x) = 1,
      (PrimeDivisor.ofPoint x h).valuation f ≤ WithZero.exp (D (PrimeDivisor.ofPoint x h)) := by
  unfold pointSubgroup
  split_ifs with h
  · simp only [PrimeDivisor.mem_divisorSubgroup]
    exact ⟨fun hf _ => hf, fun hf => hf h⟩
  · exact ⟨fun _ h' => absurd h' h, fun _ => AddSubgroup.mem_top f⟩

/- English proof (translation)
Rewrite using `[mem_pointSubgroup_iff, PrimeDivisor.mem_divisorSubgroup]`. Conclude with `⟨fun hf => hf Z.2, fun hf _ => hf⟩`.
-/
lemma mem_pointSubgroup_primeDivisor (D : WeilDivisor X) (Z : PrimeDivisor X)
    (f : X.functionField) : f ∈ pointSubgroup D Z.point ↔ f ∈ Z.divisorSubgroup D := by
  rw [mem_pointSubgroup_iff, PrimeDivisor.mem_divisorSubgroup]
  exact ⟨fun hf => hf Z.2, fun hf _ => hf⟩

end Local

section Finite

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

/- English proof (translation)
Distinguish the cases in `hf : f = 0`. Simplify using `[hf]`. Use `((PrimeDivisor.finite_ord_ne_zero hf).union D.support.finite_toSet).subset ?_` and prove the remaining obligations. Introduce `Z hZ`. Assume the negation of the conclusion as `hc`.

Simplify using `only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Finset.mem_coe, Finsupp.mem_support_iff] at hc`. Apply `hZ` to reduce the goal to its premises. Rewrite using `[PrimeDivisor.mem_divisorSubgroup, PrimeDivisor.valuation_le_exp_iff Z hf, hc.1, hc.2]`. Simplify using the standard rewrite rules.
-/
lemma finite_not_mem_divisorSubgroup (D : WeilDivisor X)
    (f : X.functionField) : {Z : PrimeDivisor X | f ∉ Z.divisorSubgroup D}.Finite := by
  by_cases hf : f = 0
  · simp [hf]
  refine ((PrimeDivisor.finite_ord_ne_zero hf).union D.support.finite_toSet).subset ?_
  intro Z hZ
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Finset.mem_coe,
    Finsupp.mem_support_iff] at hc
  apply hZ
  rw [PrimeDivisor.mem_divisorSubgroup, PrimeDivisor.valuation_le_exp_iff Z hf, hc.1, hc.2]
  simp

end Finite

section Constant

variable [IsIntegral X]

def constPredicate : TopCat.LocalPredicate (X := X.carrier) (fun _ => X.functionField) where
  pred {V} f := ∀ y : V, ∃ W : X.Opens, y.1 ∈ W ∧ ∀ z : V, z.1 ∈ W → f z = f y
  res {V W} i f h := by
    intro y
    obtain ⟨W', hyW', hW'⟩ := h (i y)
    exact ⟨W', hyW', fun z hz => hW' (i z) hz⟩
  locality {V} f w := by
    intro y
    obtain ⟨W, hyW, i, hW⟩ := w y
    obtain ⟨W', hyW', hW'⟩ := hW ⟨y.1, hyW⟩
    refine ⟨W ⊓ W', ⟨hyW, hyW'⟩, fun z hz => ?_⟩
    exact hW' ⟨z.1, hz.1⟩ hz.2

def constSections (V : X.Opens) : AddSubgroup (V → X.functionField) where
  carrier := {f | constPredicate.pred f}
  zero_mem' := fun _ => ⟨⊤, trivial, fun _ _ => rfl⟩
  add_mem' {f g} hf hg := by
    intro y
    obtain ⟨W₁, hy₁, h₁⟩ := hf y
    obtain ⟨W₂, hy₂, h₂⟩ := hg y
    exact ⟨W₁ ⊓ W₂, ⟨hy₁, hy₂⟩, fun z hz => by simp only [Pi.add_apply, h₁ z hz.1, h₂ z hz.2]⟩
  neg_mem' {f} hf := by
    intro y
    obtain ⟨W, hyW, h⟩ := hf y
    exact ⟨W, hyW, fun z hz => by simp only [Pi.neg_apply, h z hz]⟩

/- English proof (translation)
Take `⟨Wy, hyW, hy⟩` from `t.2 y`. Take `⟨Wz, hzW, hz⟩` from `t.2 z`. Take `⟨w, hw⟩` from `nonempty_preirreducible_inter (Wy ⊓ V).isOpen (Wz ⊓ V).isOpen ⟨y.1, hyW, y.2⟩ ⟨z.1, hzW, z.2⟩`. Rewrite using `[← hy ⟨w, hw.1.2⟩ hw.1.1, hz ⟨w, hw.1.2⟩ hw.2.1]`.
-/
lemma constSections_apply_eq {V : X.Opens} (t : constSections V) (y z : V) : t.1 y = t.1 z := by
  obtain ⟨Wy, hyW, hy⟩ := t.2 y
  obtain ⟨Wz, hzW, hz⟩ := t.2 z
  obtain ⟨w, hw⟩ := nonempty_preirreducible_inter (Wy ⊓ V).isOpen (Wz ⊓ V).isOpen
    ⟨y.1, hyW, y.2⟩ ⟨z.1, hzW, z.2⟩
  rw [← hy ⟨w, hw.1.2⟩ hw.1.1, hz ⟨w, hw.1.2⟩ hw.2.1]

def constSection (V : X.Opens) (c : X.functionField) : constSections V :=
  ⟨fun _ => c, fun _ => ⟨⊤, trivial, fun _ _ => rfl⟩⟩

def constSectionsRes {V W : X.Opens} (h : W ≤ V) : constSections V →+ constSections W where
  toFun f := ⟨fun y => f.1 ⟨y.1, h y.2⟩, constPredicate.res (homOfLE h) f.1 f.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable (X) in

noncomputable def constPresheaf : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (constSections V.unop)
  map i := AddCommGrpCat.ofHom (constSectionsRes i.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

variable (X) in

/- English proof (translation)
Rewrite using `[TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]`. Use `TopCat.Presheaf.isSheaf_of_iso ?_ (TopCat.subpresheafToTypes.isSheaf (constPredicate (X := X)))` and prove the remaining obligations. Use `NatIso.ofComponents (fun V => Equiv.toIso { toFun := fun f => ⟨f.1, f.2⟩ invFun := fun f => ⟨f.1, f.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }) ?_` and prove the remaining obligations. Introduce `V W i`. Both sides reduce to the same expression.
-/
theorem constPresheaf_isSheaf : TopCat.Presheaf.IsSheaf (X := X.carrier) (constPresheaf X) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]
  refine TopCat.Presheaf.isSheaf_of_iso ?_
    (TopCat.subpresheafToTypes.isSheaf (constPredicate (X := X)))
  refine NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f.1, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) ?_
  intro V W i
  rfl

variable (X) in

noncomputable def constSheaf : Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} :=
  ⟨constPresheaf X, constPresheaf_isSheaf X⟩

instance : TopCat.Presheaf.IsFlasque (constSheaf X).obj where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    by_cases hV : Nonempty V.unop
    · obtain ⟨y⟩ := hV
      refine ⟨constSection U.unop (t.1 y), ?_⟩
      apply Subtype.ext
      funext z
      exact constSections_apply_eq t y z
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      funext z
      exact absurd ⟨z⟩ hV

end Constant

section Quot

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] (D : WeilDivisor X)

def quotPredicate :
    TopCat.LocalPredicate (X := X.carrier) (fun x => X.functionField ⧸ pointSubgroup D x) where
  pred {V} a := ∀ y : V, ∃ W : X.Opens, y.1 ∈ W ∧ {z : V | z.1 ∈ W ∧ a z ≠ 0}.Finite
  res {V W} i a h := by
    intro y
    obtain ⟨W', hyW', hW'⟩ := h (i y)
    refine ⟨W', hyW', ?_⟩
    have hinj : Function.Injective (fun z : V => i z) := fun z z' hz =>
      Subtype.ext (congrArg Subtype.val hz :)
    exact (hW'.preimage hinj.injOn).subset fun z hz => hz
  locality {V} a w := by
    intro y
    obtain ⟨V', hyV', i, hV'⟩ := w y
    obtain ⟨W, hyW, hW⟩ := hV' ⟨y.1, hyV'⟩
    refine ⟨W ⊓ V', ⟨hyW, hyV'⟩, ?_⟩
    refine (hW.image (fun z : V' => i z)).subset ?_
    rintro z ⟨⟨hzW, hzV'⟩, hz⟩
    exact ⟨⟨z.1, hzV'⟩, ⟨hzW, hz⟩, rfl⟩

def quotSections (V : X.Opens) : AddSubgroup (∀ z : V, X.functionField ⧸ pointSubgroup D z.1) where
  carrier := {a | (quotPredicate D).pred a}
  zero_mem' := fun _ => ⟨⊤, trivial, by simp⟩
  add_mem' {a b} ha hb := by
    intro y
    obtain ⟨W₁, hy₁, h₁⟩ := ha y
    obtain ⟨W₂, hy₂, h₂⟩ := hb y
    refine ⟨W₁ ⊓ W₂, ⟨hy₁, hy₂⟩, (h₁.union h₂).subset ?_⟩
    rintro z ⟨⟨hz₁, hz₂⟩, hz⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
    exact hz (by simp only [Pi.add_apply, hc.1 hz₁, hc.2 hz₂, add_zero])
  neg_mem' {a} ha := by
    intro y
    obtain ⟨W, hyW, h⟩ := ha y
    refine ⟨W, hyW, h.subset ?_⟩
    rintro z ⟨hzW, hz⟩
    exact ⟨hzW, fun h0 => hz (by simp only [Pi.neg_apply, h0, neg_zero])⟩

def quotSectionsRes {V W : X.Opens} (h : W ≤ V) : quotSections D V →+ quotSections D W where
  toFun a := ⟨fun y => a.1 ⟨y.1, h y.2⟩, (quotPredicate D).res (homOfLE h) a.1 a.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def quotPresheaf : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (quotSections D V.unop)
  map i := AddCommGrpCat.ofHom (quotSectionsRes D i.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

/- English proof (translation)
Rewrite using `[TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]`. Use `TopCat.Presheaf.isSheaf_of_iso ?_ (TopCat.subpresheafToTypes.isSheaf (quotPredicate D))` and prove the remaining obligations. Use `NatIso.ofComponents (fun V => Equiv.toIso { toFun := fun f => ⟨f.1, f.2⟩ invFun := fun f => ⟨f.1, f.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }) ?_` and prove the remaining obligations. Introduce `V W i`. Both sides reduce to the same expression.
-/
theorem quotPresheaf_isSheaf : TopCat.Presheaf.IsSheaf (X := X.carrier) (quotPresheaf D) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]
  refine TopCat.Presheaf.isSheaf_of_iso ?_
    (TopCat.subpresheafToTypes.isSheaf (quotPredicate D))
  refine NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f.1, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) ?_
  intro V W i
  rfl

noncomputable def quotSheaf : Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u} :=
  ⟨quotPresheaf D, quotPresheaf_isSheaf D⟩

noncomputable def divisorToConst : modulesAb (divisorSheaf D) ⟶ constSheaf X :=
  ⟨{ app := fun V => AddCommGrpCat.ofHom
        { toFun := fun t => ⟨(show divisorSections D V.unop from t).1,
            (show divisorSections D V.unop from t).2.1⟩
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
     naturality := fun _ _ _ => rfl }⟩

end Quot

section Resolution

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X] (D : WeilDivisor X)

/- English proof (translation)
Use `((finite_not_mem_divisorSubgroup D c).image PrimeDivisor.point).subset ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Set.mem_ofPred_eq, mem_pointSubgroup_iff, not_forall] at hx`. Take `⟨h, hc⟩` from `hx`. Conclude with `⟨PrimeDivisor.ofPoint x h, by`.

Simplify `hc, rfl⟩` using `only [Set.mem_ofPred_eq, PrimeDivisor.mem_divisorSubgroup]`.
-/
lemma finite_not_mem_pointSubgroup (c : X.functionField) :
    {x : X | c ∉ pointSubgroup D x}.Finite := by
  refine ((finite_not_mem_divisorSubgroup D c).image PrimeDivisor.point).subset ?_
  intro x hx
  simp only [Set.mem_ofPred_eq, mem_pointSubgroup_iff, not_forall] at hx
  obtain ⟨h, hc⟩ := hx
  exact ⟨PrimeDivisor.ofPoint x h, by
    simpa only [Set.mem_ofPred_eq, PrimeDivisor.mem_divisorSubgroup] using hc, rfl⟩

/- English proof (translation)
Introduce `y`. Use `⟨⊤, trivial, ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (fun z : V => z.1)` using `Subtype.val_injective`. Use `(((finite_not_mem_pointSubgroup D (t.1 y)).preimage hinj.injOn)).subset ?_` and prove the remaining obligations. Introduce and unpack `z ⟨-, hz⟩`.

Introduce `hmem`. Apply `hz` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(QuotientAddGroup.mk (t.1 z) : X.functionField ⧸ pointSubgroup D z.1) = 0`. Rewrite using `[constSections_apply_eq t z y]`. Conclude with `(QuotientAddGroup.eq_zero_iff _).mpr hmem`.
-/
lemma mk_mem_quotSections {V : X.Opens} (t : constSections V) :
    (fun z : V => (QuotientAddGroup.mk (t.1 z) : X.functionField ⧸ pointSubgroup D z.1)) ∈
      quotSections D V := by
  intro y
  refine ⟨⊤, trivial, ?_⟩
  have hinj : Function.Injective (fun z : V => z.1) := Subtype.val_injective
  refine (((finite_not_mem_pointSubgroup D (t.1 y)).preimage hinj.injOn)).subset ?_
  rintro z ⟨-, hz⟩
  intro hmem
  apply hz
  change (QuotientAddGroup.mk (t.1 z) : X.functionField ⧸ pointSubgroup D z.1) = 0
  rw [constSections_apply_eq t z y]
  exact (QuotientAddGroup.eq_zero_iff _).mpr hmem

noncomputable def constToQuot : constSheaf X ⟶ quotSheaf D :=
  ⟨{ app := fun V => AddCommGrpCat.ofHom
        { toFun := fun t => ⟨fun z => QuotientAddGroup.mk (t.1 z), mk_mem_quotSections D t⟩
          map_zero' := by
            apply Subtype.ext
            funext z
            exact QuotientAddGroup.mk_zero _
          map_add' := fun s t => by
            apply Subtype.ext
            funext z
            exact QuotientAddGroup.mk_add _ _ _ }
     naturality := fun _ _ _ => rfl }⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma constToQuot_app_apply (V : X.Opens) (t : constSections V) (z : V) :
    ((constToQuot D).hom.app (op V) t).1 z = QuotientAddGroup.mk (t.1 z) := rfl

noncomputable def divisorSeq : ShortComplex (Sheaf (Opens.grothendieckTopology X.toTopCat)
    AddCommGrpCat.{u}) :=
  ShortComplex.mk (divisorToConst D) (constToQuot D) (by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro t
    apply Subtype.ext
    funext z
    change (QuotientAddGroup.mk ((show divisorSections D V.unop from t).1 z) :
      X.functionField ⧸ pointSubgroup D z.1) = 0
    rw [QuotientAddGroup.eq_zero_iff, mem_pointSubgroup_iff]
    exact fun h => (show divisorSections D V.unop from t).2.2 z h)

instance : Mono (divisorSeq D).f := by
  apply Sheaf.mono_of_injective
  intro V s t hst
  exact Subtype.ext (congrArg Subtype.val hst :)

/- English proof (translation)
Substitute `hx` using the available equality. Rewrite using `[mem_pointSubgroup_iff]`. Introduce `h`. Conclude with `absurd rfl (PrimeDivisor.ofPoint (genericPoint X) h).point_ne_genericPoint`.
-/
lemma mem_pointSubgroup_of_eq_genericPoint {x : X} (hx : x = genericPoint X) (c : X.functionField) :
    c ∈ pointSubgroup D x := by
  subst hx
  rw [mem_pointSubgroup_iff]
  intro h
  exact absurd rfl (PrimeDivisor.ofPoint (genericPoint X) h).point_ne_genericPoint

/- English proof (translation)
Rewrite using `[TopCat.Presheaf.isLocallySurjective_iff]`. Introduce `U t x hxU`. Take `⟨W, hxW, hfin⟩` from `t.2 ⟨x, hxU⟩`. Take `⟨c, hc⟩` from `QuotientAddGroup.mk_surjective (t.1 ⟨x, hxU⟩)`. Establish `hcx : ∀ p : U, p.1 = x → (QuotientAddGroup.mk c : X.functionField ⧸ pointSubgroup D p.1) = t.1 p`.

Introduce and unpack `⟨p, hp⟩ rfl`. Conclude with `hc`. Use `set B : Set X := {y | y ≠ x ∧ ((∃ z : U, z.1 = y ∧ z.1 ∈ W ∧ t.1 z ≠ 0) ∨ c ∉ pointSubgroup D y)} with hB`. Establish `hBfin : B.Finite`. Use `((hfin.image Subtype.val).union (finite_not_mem_pointSubgroup D c)).subset ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨-, ⟨z, rfl, hzW, hz⟩ | hy⟩`. Conclude with `Or.inl ⟨z, ⟨hzW, hz⟩, rfl⟩`. Conclude with `Or.inr hy`. Establish `hBgen : ∀ y ∈ B, y ≠ genericPoint X`. Introduce and unpack `y ⟨-, ⟨z, rfl, -, hz⟩ | hy⟩ hgen`.

Apply `hz` to reduce the goal to its premises. Take `⟨r, hr⟩` from `QuotientAddGroup.mk_surjective (t.1 z)`. Rewrite using `[← hr]`. Conclude with `(QuotientAddGroup.eq_zero_iff r).mpr (mem_pointSubgroup_of_eq_genericPoint D hgen r)`. Conclude with `hy (mem_pointSubgroup_of_eq_genericPoint D hgen c)`.

Establish `hBcl : IsClosed B`. Establish `: B = ⋃ y ∈ B, ({y} : Set X)` using `by simp`. Rewrite using `[this]`. Conclude with `hBfin.isClosed_biUnion fun y hy => isClosed_singleton_of_ne hX (hBgen y hy)`. Set `V : X.Opens` to `U ⊓ W ⊓ ⟨Bᶜ, hBcl.isOpen_compl⟩`.

Establish `hxV : x ∈ V` using `⟨⟨hxU, hxW⟩, fun h => h.1 rfl⟩`. Use `⟨V, fun y hy => hy.1.1, ⟨constSection V c, ?_⟩, hxV⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Express the relevant statement in the definitionally equal form `(QuotientAddGroup.mk c : X.functionField ⧸ pointSubgroup D z.1) = t.1 ⟨z.1, z.2.1.1⟩`.

Distinguish the cases in `hzx : z.1 = x`. Conclude with `hcx ⟨z.1, z.2.1.1⟩ hzx`. Establish `hzB : z.1 ∉ B` using `z.2.2`. Simplify using `only [hB, Set.mem_ofPred_eq, not_and, not_or, not_exists, not_not] at hzB`. Take `⟨h1, h2⟩` from `hzB hzx`.

Rewrite using `[(QuotientAddGroup.eq_zero_iff _).mpr h2]`. Conclude with `(h1 ⟨z.1, z.2.1.1⟩ rfl z.2.1.2).symm`.
-/
theorem constToQuot_isLocallySurjective (hX : topologicalKrullDim X ≤ 1) :
    TopCat.Presheaf.IsLocallySurjective (constToQuot D).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hxU
  obtain ⟨W, hxW, hfin⟩ := t.2 ⟨x, hxU⟩
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (t.1 ⟨x, hxU⟩)
  have hcx : ∀ p : U, p.1 = x →
      (QuotientAddGroup.mk c : X.functionField ⧸ pointSubgroup D p.1) = t.1 p := by
    rintro ⟨p, hp⟩ rfl
    exact hc
  set B : Set X := {y | y ≠ x ∧ ((∃ z : U, z.1 = y ∧ z.1 ∈ W ∧ t.1 z ≠ 0) ∨
    c ∉ pointSubgroup D y)} with hB
  have hBfin : B.Finite := by
    refine ((hfin.image Subtype.val).union (finite_not_mem_pointSubgroup D c)).subset ?_
    rintro y ⟨-, ⟨z, rfl, hzW, hz⟩ | hy⟩
    · exact Or.inl ⟨z, ⟨hzW, hz⟩, rfl⟩
    · exact Or.inr hy
  have hBgen : ∀ y ∈ B, y ≠ genericPoint X := by
    rintro y ⟨-, ⟨z, rfl, -, hz⟩ | hy⟩ hgen
    · apply hz
      obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (t.1 z)
      rw [← hr]
      exact (QuotientAddGroup.eq_zero_iff r).mpr (mem_pointSubgroup_of_eq_genericPoint D hgen r)
    · exact hy (mem_pointSubgroup_of_eq_genericPoint D hgen c)
  have hBcl : IsClosed B := by
    have : B = ⋃ y ∈ B, ({y} : Set X) := by simp
    rw [this]
    exact hBfin.isClosed_biUnion fun y hy => isClosed_singleton_of_ne hX (hBgen y hy)
  let V : X.Opens := U ⊓ W ⊓ ⟨Bᶜ, hBcl.isOpen_compl⟩
  have hxV : x ∈ V := ⟨⟨hxU, hxW⟩, fun h => h.1 rfl⟩
  refine ⟨V, fun y hy => hy.1.1, ⟨constSection V c, ?_⟩, hxV⟩
  apply Subtype.ext
  funext z
  change (QuotientAddGroup.mk c : X.functionField ⧸ pointSubgroup D z.1) = t.1 ⟨z.1, z.2.1.1⟩
  by_cases hzx : z.1 = x
  · exact hcx ⟨z.1, z.2.1.1⟩ hzx
  · have hzB : z.1 ∉ B := z.2.2
    simp only [hB, Set.mem_ofPred_eq, not_and, not_or, not_exists, not_not] at hzB
    obtain ⟨h1, h2⟩ := hzB hzx
    rw [(QuotientAddGroup.eq_zero_iff _).mpr h2]
    exact (h1 ⟨z.1, z.2.1.1⟩ rfl z.2.1.2).symm

/- English proof (translation)
The claim follows from `(TopCat.Sheaf.isLocallySurjective_iff_epi (constToQuot D)).mp (constToQuot_isLocallySurjective D hX)`.
-/
lemma divisorSeq_epi (hX : topologicalKrullDim X ≤ 1) : Epi (divisorSeq D).g :=
  (TopCat.Sheaf.isLocallySurjective_iff_epi (constToQuot D)).mp
    (constToQuot_isLocallySurjective D hX)

/- English proof (translation)
Use `(TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (C := AddCommGrpCat.{u}) (X := X.toTopCat) (divisorSeq D)).mpr fun x => ?_` and prove the remaining obligations. Rewrite using `[ShortComplex.ab_exact_iff]`. Introduce `s hs`. Take `⟨U, hxU, t, rfl⟩` from `TopCat.Presheaf.exists_germ_eq (constSheaf X).obj s`. Express the relevant statement in the definitionally equal form `(TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (constToQuot D).hom (TopCat.Presheaf.germ (constSheaf X).obj U x hxU t) = 0 at hs`.

Rewrite `hs` using `[TopCat.Presheaf.stalkFunctor_map_germ_apply]`. Establish `hs'` using `hs.trans (map_zero (ConcreteCategory.hom (TopCat.Presheaf.germ (quotSheaf D).obj U x hxU))).symm`. Take `⟨W, hxW, iU, iV, heq⟩` from `TopCat.Presheaf.germ_eq _ x hxU hxU _ _ hs'`. Establish `hW : ∀ z : W, t.1 ⟨z.1, iU.le z.2⟩ ∈ pointSubgroup D z.1`. Introduce `z`.

Use `congrArg (fun a => (show quotSections D W from a).1 z) heq` as an intermediate fact. Express the relevant statement in the definitionally equal form `(QuotientAddGroup.mk (t.1 ⟨z.1, iU.le z.2⟩) : X.functionField ⧸ pointSubgroup D z.1) = 0 at this`. Conclude with `(QuotientAddGroup.eq_zero_iff _).mp this`. Set `s' : divisorSections D W` to `⟨fun z => t.1 ⟨z.1, iU.le z.2⟩, constPredicate.res iU t.1 t.2, fun y hy => (mem_pointSubgroup_iff D y.1 _).mp (hW y) hy⟩`. Set `s'' : ToType ((modulesAb (divisorSheaf D)).obj.obj (op W))` to `s'`.

Use `⟨TopCat.Presheaf.germ (modulesAb (divisorSheaf D)).obj W x hxW s'', ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (divisorToConst D).hom (TopCat.Presheaf.germ (modulesAb (divisorSheaf D)).obj W x hxW s'') = _`. Rewrite using `[TopCat.Presheaf.stalkFunctor_map_germ_apply, ← TopCat.Presheaf.germ_res_apply (constSheaf X).obj iU x hxW t]`. Both sides reduce to the same expression.
-/
theorem divisorSeq_exact : (divisorSeq D).Exact := by
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (C := AddCommGrpCat.{u})
    (X := X.toTopCat) (divisorSeq D)).mpr fun x => ?_
  rw [ShortComplex.ab_exact_iff]
  intro s hs
  obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (constSheaf X).obj s
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (constToQuot D).hom
    (TopCat.Presheaf.germ (constSheaf X).obj U x hxU t) = 0 at hs
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hs
  have hs' := hs.trans
    (map_zero (ConcreteCategory.hom (TopCat.Presheaf.germ (quotSheaf D).obj U x hxU))).symm
  obtain ⟨W, hxW, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ hs'
  have hW : ∀ z : W, t.1 ⟨z.1, iU.le z.2⟩ ∈ pointSubgroup D z.1 := by
    intro z
    have := congrArg (fun a => (show quotSections D W from a).1 z) heq
    change (QuotientAddGroup.mk (t.1 ⟨z.1, iU.le z.2⟩) :
      X.functionField ⧸ pointSubgroup D z.1) = 0 at this
    exact (QuotientAddGroup.eq_zero_iff _).mp this
  let s' : divisorSections D W :=
    ⟨fun z => t.1 ⟨z.1, iU.le z.2⟩, constPredicate.res iU t.1 t.2,
      fun y hy => (mem_pointSubgroup_iff D y.1 _).mp (hW y) hy⟩
  let s'' : ToType ((modulesAb (divisorSheaf D)).obj.obj (op W)) := s'
  refine ⟨TopCat.Presheaf.germ (modulesAb (divisorSheaf D)).obj W x hxW s'', ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (divisorToConst D).hom
    (TopCat.Presheaf.germ (modulesAb (divisorSheaf D)).obj W x hxW s'') = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.germ_res_apply (constSheaf X).obj iU x hxW t]
  rfl

/- English proof (translation)
Use `divisorSeq_epi D hX` as an intermediate fact. Conclude with `⟨divisorSeq_exact D⟩`.
-/
theorem divisorSeq_shortExact (hX : topologicalKrullDim X ≤ 1) : (divisorSeq D).ShortExact := by
  have := divisorSeq_epi D hX
  exact ⟨divisorSeq_exact D⟩

end Resolution

end GroundTheory.Arith.SchemeCoh
