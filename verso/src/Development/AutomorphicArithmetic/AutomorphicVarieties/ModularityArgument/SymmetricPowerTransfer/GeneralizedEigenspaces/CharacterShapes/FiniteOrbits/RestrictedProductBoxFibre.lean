import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Box

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K U : ∀ v, Subgroup (Gv v)}

/- English proof (translation)
Simplify using `[RPG.box, Subgroup.mem_iInf]`.
-/
private theorem memBox (P : RPG G Gv K) (U : ∀ v, Subgroup (Gv v)) (g : G) :
    g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem smulMk {A : Type} [Group A] (W W' : Subgroup A) (u : W) (x : A) :
    u • (x : A ⧸ W') = (((u : A) * x : A) : A ⧸ W') := rfl

end Box

end UpperTheory.V.Z.Sym.So

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_doubleCoset_iff_exists_eq_mul_mul {A : Type} [Group A] {W : Subgroup A} {a x : A} :
    x ∈ DC W a ↔ ∃ u ∈ W, ∃ u' ∈ W, x = u * a * u' := Iff.rfl

/- English proof (translation)
Take `⟨u, hu, u', hu', rfl⟩` from `mem_doubleCoset_iff_exists_eq_mul_mul.1 hx`. Conclude with `mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨u, hu, u' * c, mul_mem hu' hc, by simp only [mul_assoc]⟩`.
-/
private theorem mul_mem_doubleCoset_of_mem_doubleCoset_of_mem {A : Type} [Group A] {W : Subgroup A} {a x c : A}
    (hx : x ∈ DC W a) (hc : c ∈ W) : x * c ∈ DC W a := by
  obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hx
  exact mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨u, hu, u' * c, mul_mem hu' hc, by simp only [mul_assoc]⟩

/- English proof (translation)
Take `⟨u, hu, u', hu', rfl⟩` from `mem_doubleCoset_iff_exists_eq_mul_mul.1 hx`. Conclude with `mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨c * u, mul_mem hc hu, u', hu', by simp only [mul_assoc]⟩`.
-/
private theorem mul_mem_doubleCoset_of_mem_of_mem_doubleCoset {A : Type} [Group A] {W : Subgroup A} {a x c : A}
    (hx : x ∈ DC W a) (hc : c ∈ W) : c * x ∈ DC W a := by
  obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hx
  exact mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨c * u, mul_mem hc hu, u', hu', by simp only [mul_assoc]⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul W x`. Rewrite using `[hc]`. Use `⟨mul_mem_doubleCoset_of_mem_doubleCoset_of_mem h1 c.2, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv_rev, mul_assoc]`. Conclude with `mul_mem_doubleCoset_of_mem_of_mem_doubleCoset h2 (inv_mem c.2)`.
-/
private theorem out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset {A : Type} [Group A] {W : Subgroup A} {a b g x : A}
    (h1 : x ∈ DC W a) (h2 : x⁻¹ * g ∈ DC W b) :
    Quotient.out (x : A ⧸ W) ∈ DC W a ∧ (Quotient.out (x : A ⧸ W))⁻¹ * g ∈ DC W b := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul W x
  rw [hc]
  refine ⟨mul_mem_doubleCoset_of_mem_doubleCoset_of_mem h1 c.2, ?_⟩
  rw [mul_inv_rev, mul_assoc]
  exact mul_mem_doubleCoset_of_mem_of_mem_doubleCoset h2 (inv_mem c.2)

/- English proof (translation)
The claim follows from `Quotient.out_eq y`.
-/
private theorem quotientGroup_coe_out_eq_self {A : Type} [Group A] (W : Subgroup A) (y : A ⧸ W) :
    ((Quotient.out y : A) : A ⧸ W) = y := Quotient.out_eq y

/- English proof (translation)
Introduce `I G _ Gv _ K U P S _ a ha`. Establish `hB : ∀ g, g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v` using `memBox P U`. Establish `glue : ∀ x : (v : I) → Gv v, (∀ v ∉ S, x v = 1) → ∃ h : G, ∀ v, P.p v h = x v`. Introduce `x hx`. Apply `P.surj` to reduce the goal to its premises.

Use `Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hvS`. Conclude with `hv (by rw [hx v hvS]; exact one_mem _)`. Establish `key : ∀ c : G, (∀ v ∉ S, P.p v c ∈ U v) → ∀ g : G, g ∈ DC (P.box U) c ↔ (∀ v ∈ S, P.p v g ∈ DC (U v) (P.p v c)) ∧ ∀ v ∉ S, P.p v g ∈ U v`.

Introduce `c hc g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨u, hu, u', hu', rfl⟩` from `mem_doubleCoset_iff_exists_eq_mul_mul.1 hg`. Rewrite `hu`, `hu'` using `[hB]`.

Use `⟨fun v _ => mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨P.p v u, hu v, P.p v u', hu' v, by rw [map_mul, map_mul]⟩, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul]`. Conclude with `mul_mem (mul_mem (hu v) (hc v hv)) (hu' v)`. Introduce and unpack `⟨h1, h2⟩`. Establish `h1' : ∀ v ∈ S, ∃ u ∈ U v, ∃ u' ∈ U v, P.p v g = u * P.p v c * u'` using `fun v hv => mem_doubleCoset_iff_exists_eq_mul_mul.1 (h1 v hv)`.

Use `choose! u hu u' hu' hg using h1'`. Take `⟨w, hw⟩` from `glue (fun v => if v ∈ S then u v else 1) (fun v hv => if_neg hv)`. Use `mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨w, ?_, c⁻¹ * w⁻¹ * g, ?_, by group⟩` and prove the remaining obligations. Rewrite using `[hB]`. Introduce `v`.

Rewrite using `[hw]`. Use `split_ifs with hv`. Use `exacts [hu v hv, one_mem _]`. Rewrite using `[hB]`. Introduce `v`.

Rewrite using `[map_mul, map_mul, map_inv, map_inv, hw]`. Use `split_ifs with hv`. Rewrite using `[hg v hv]`. Establish `e : (P.p v c)⁻¹ * (u v)⁻¹ * (u v * P.p v c * u' v) = u' v` using `by group`. Rewrite using `[e]`.

Conclude with `hu' v hv`. Rewrite using `[inv_one, mul_one]`. Conclude with `mul_mem (inv_mem (hc v hv)) (h2 v hv)`. Use `⟨key a ha, ?_, ?_⟩` and prove the remaining obligations. Introduce `hf`.

Unfold `UpperTheory.V.AlgebraTools.FinOrb at hf ⊢`. Establish `hout : ∀ u : P.box U, ∀ v ∉ S, P.p v (Quotient.out (u • (a : G ⧸ P.box U))) ∈ U v`. Introduce `u v hv`. Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul (P.box U) ((u : G) * a)`. Rewrite using `[smulMk, hc, map_mul, map_mul]`.

Conclude with `mul_mem (mul_mem ((hB _).1 u.2 v) (ha v hv)) ((hB _).1 c.2 v)`. Apply `Set.Finite.of_finite_image (f := fun (y : G ⧸ P.box U) (v : S) => ((P.p v.1 (Quotient.out y) : Gv v.1) : Gv v.1 ⧸ U v.1))` to reduce the goal to its premises. Use `(Set.Finite.pi (t := fun v : S => MulAction.orbit (U v.1) ((P.p v.1 a : Gv v.1) : Gv v.1 ⧸ U v.1)) (fun v => hf v.1 v.2)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, ⟨u, rfl⟩, rfl⟩`. Rewrite using `[Set.mem_univ_pi]`.

Introduce `v`. Use `⟨⟨P.p v.1 u, (hB _).1 u.2 v.1⟩, ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul (P.box U) ((u : G) * a)`. Simplify using `only [smulMk]`. Rewrite using `[hc, QuotientGroup.eq]`.

Use `(hB _).1 c.2 v.1 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_mul, Subgroup.coe_mk]`. Use `group`. Introduce and unpack `_ ⟨u1, rfl⟩ _ ⟨u2, rfl⟩ h12`. Use `(quotientGroup_coe_out_eq_self _ _).symm.trans ((QuotientGroup.eq.2 ?_).trans (quotientGroup_coe_out_eq_self _ _))` and prove the remaining obligations.

Rewrite using `[hB]`. Introduce `v`. Rewrite using `[map_mul, map_inv]`. Distinguish the cases in `hv : v ∈ S`. Conclude with `QuotientGroup.eq.1 (congrFun h12 ⟨v, hv⟩)`.

Conclude with `mul_mem (inv_mem (hout u1 v hv)) (hout u2 v hv)`. Introduce `b hb hloc g`. Establish `hab : ∀ v ∉ S, P.p v (a * b) ∈ U v` using `fun v hv => by`. Rewrite using `[map_mul]`. Conclude with `mul_mem (ha v hv) (hb v hv)`.

Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨hgS, hgN⟩` from `(key _ hab g).1 hg`. Establish `hgl : ∀ v ∈ S, P.p v g ∈ DC (U v) (P.p v a * P.p v b)` using `fun v hv => by`. Rewrite using `[← map_mul]`.

Conclude with `hgS v hv`. Establish `hl : ∀ v ∈ S, ∃ z, z ∈ DC (U v) (P.p v a) ∧ z⁻¹ * P.p v g ∈ DC (U v) (P.p v b)`. Introduce `v hv`. Take `⟨y, hy, -⟩` from `(hloc v hv (P.p v g)).1 (hgl v hv)`. Conclude with `⟨_, hy⟩`.

Use `choose! z hz1 hz2 using hl`. Take `⟨w, hw⟩` from `glue (fun v => if v ∈ S then z v else 1) (fun v hv => if_neg hv)`. Establish `hw1 : w ∈ DC (P.box U) a` using `(key a ha w).2 ⟨fun v hv => by rw [hw, if_pos hv]; exact hz1 v hv, fun v hv => by rw [hw, if_neg hv]; exact one_mem _⟩`. Establish `hw2 : w⁻¹ * g ∈ DC (P.box U) b` using `(key b hb _).2 ⟨fun v hv => by rw [map_mul, map_inv, hw, if_pos hv]; exact hz2 v hv, fun v hv => by rw [map_mul, map_inv, hw, if_neg hv, inv_one, one_mul]; exact hgN v hv⟩`. Use `⟨(w : G ⧸ P.box U), out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset hw1 hw2, ?_⟩` and prove the remaining obligations.

Introduce and unpack `y ⟨hy1, hy2⟩`. Use `(quotientGroup_coe_out_eq_self _ _).symm.trans (QuotientGroup.eq.2 ?_)` and prove the remaining obligations. Rewrite using `[hB]`. Introduce `v`. Rewrite using `[map_mul, map_inv]`.

Establish `ha1` using `(key a ha _).1 hy1`. Establish `hb1` using `(key b hb _).1 hy2`. Distinguish the cases in `hv : v ∈ S`. Establish `hb2` using `hb1.1 v hv`. Rewrite `hb2` using `[map_mul, map_inv]`.

Establish `hz2'` using `hz2 v hv`. Rewrite `hz2'` using `[← if_pos (c := v ∈ S) (t := z v) (e := 1) hv, ← hw v]`. Establish `hz1'` using `hz1 v hv`. Rewrite `hz1'` using `[← if_pos (c := v ∈ S) (t := z v) (e := 1) hv, ← hw v]`. Establish `e` using `((hloc v hv (P.p v g)).1 (hgl v hv)).unique (out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset (ha1.1 v hv) hb2) (out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset hz1' hz2')`.

Conclude with `QuotientGroup.eq.1 e`. Rewrite using `[hw, if_neg hv]`. Conclude with `mul_mem (inv_mem (ha1.2 v hv)) (one_mem _)`. Introduce `y hy1 hy2`. Use `(key _ hab g).2 ⟨fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations.

Establish `h2` using `((key b hb _).1 hy2).1 v hv`. Rewrite `h2` using `[map_mul, map_inv]`. Rewrite using `[map_mul]`. Conclude with `(hloc v hv (P.p v g)).2 (P.p v y) (((key a ha y).1 hy1).1 v hv) h2`. Establish `h1` using `((key a ha y).1 hy1).2 v hv`.

Establish `h2` using `((key b hb _).1 hy2).2 v hv`. Rewrite `h2` using `[map_mul, map_inv]`. Establish `h3` using `mul_mem h1 h2`. Rewrite `h3` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Z.Sym.So.uFBox :
    UpperTheory.V.Z.Sym.So.UFBox := by
  intro I G _ Gv _ K U P S _ a ha
  classical
  have hB : ∀ g, g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := memBox P U
  have glue : ∀ x : (v : I) → Gv v, (∀ v ∉ S, x v = 1) → ∃ h : G, ∀ v, P.p v h = x v := by
    intro x hx
    apply P.surj
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
    intro v hv
    by_contra hvS
    exact hv (by rw [hx v hvS]; exact one_mem _)
  have key : ∀ c : G, (∀ v ∉ S, P.p v c ∈ U v) → ∀ g : G, g ∈ DC (P.box U) c ↔
      (∀ v ∈ S, P.p v g ∈ DC (U v) (P.p v c)) ∧ ∀ v ∉ S, P.p v g ∈ U v := by
    intro c hc g
    constructor
    · intro hg
      obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hg
      rw [hB] at hu hu'
      refine ⟨fun v _ => mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨P.p v u, hu v, P.p v u', hu' v, by rw [map_mul, map_mul]⟩, fun v hv => ?_⟩
      rw [map_mul, map_mul]
      exact mul_mem (mul_mem (hu v) (hc v hv)) (hu' v)
    · rintro ⟨h1, h2⟩
      have h1' : ∀ v ∈ S, ∃ u ∈ U v, ∃ u' ∈ U v, P.p v g = u * P.p v c * u' :=
        fun v hv => mem_doubleCoset_iff_exists_eq_mul_mul.1 (h1 v hv)
      choose! u hu u' hu' hg using h1'
      obtain ⟨w, hw⟩ := glue (fun v => if v ∈ S then u v else 1) (fun v hv => if_neg hv)
      refine mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨w, ?_, c⁻¹ * w⁻¹ * g, ?_, by group⟩
      · rw [hB]
        intro v
        rw [hw]
        split_ifs with hv
        exacts [hu v hv, one_mem _]
      · rw [hB]
        intro v
        rw [map_mul, map_mul, map_inv, map_inv, hw]
        split_ifs with hv
        · rw [hg v hv]
          have e : (P.p v c)⁻¹ * (u v)⁻¹ * (u v * P.p v c * u' v) = u' v := by group
          rw [e]
          exact hu' v hv
        · rw [inv_one, mul_one]
          exact mul_mem (inv_mem (hc v hv)) (h2 v hv)
  refine ⟨key a ha, ?_, ?_⟩
  · intro hf
    unfold UpperTheory.V.AlgebraTools.FinOrb at hf ⊢
    have hout : ∀ u : P.box U, ∀ v ∉ S,
        P.p v (Quotient.out (u • (a : G ⧸ P.box U))) ∈ U v := by
      intro u v hv
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (P.box U) ((u : G) * a)
      rw [smulMk, hc, map_mul, map_mul]
      exact mul_mem (mul_mem ((hB _).1 u.2 v) (ha v hv)) ((hB _).1 c.2 v)
    apply Set.Finite.of_finite_image
      (f := fun (y : G ⧸ P.box U) (v : S) => ((P.p v.1 (Quotient.out y) : Gv v.1) : Gv v.1 ⧸ U v.1))
    · refine (Set.Finite.pi (t := fun v : S =>
        MulAction.orbit (U v.1) ((P.p v.1 a : Gv v.1) : Gv v.1 ⧸ U v.1)) (fun v => hf v.1 v.2)).subset ?_
      rintro _ ⟨y, ⟨u, rfl⟩, rfl⟩
      rw [Set.mem_univ_pi]
      intro v
      refine ⟨⟨P.p v.1 u, (hB _).1 u.2 v.1⟩, ?_⟩
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (P.box U) ((u : G) * a)
      simp only [smulMk]
      rw [hc, QuotientGroup.eq]
      convert (hB _).1 c.2 v.1 using 1
      simp only [map_mul, Subgroup.coe_mk]
      group
    · rintro _ ⟨u1, rfl⟩ _ ⟨u2, rfl⟩ h12
      refine (quotientGroup_coe_out_eq_self _ _).symm.trans ((QuotientGroup.eq.2 ?_).trans (quotientGroup_coe_out_eq_self _ _))
      rw [hB]
      intro v
      rw [map_mul, map_inv]
      by_cases hv : v ∈ S
      · exact QuotientGroup.eq.1 (congrFun h12 ⟨v, hv⟩)
      · exact mul_mem (inv_mem (hout u1 v hv)) (hout u2 v hv)
  · intro b hb hloc g
    have hab : ∀ v ∉ S, P.p v (a * b) ∈ U v := fun v hv => by
      rw [map_mul]
      exact mul_mem (ha v hv) (hb v hv)
    constructor
    · intro hg
      obtain ⟨hgS, hgN⟩ := (key _ hab g).1 hg
      have hgl : ∀ v ∈ S, P.p v g ∈ DC (U v) (P.p v a * P.p v b) := fun v hv => by
        rw [← map_mul]
        exact hgS v hv
      have hl : ∀ v ∈ S, ∃ z, z ∈ DC (U v) (P.p v a) ∧ z⁻¹ * P.p v g ∈ DC (U v) (P.p v b) := by
        intro v hv
        obtain ⟨y, hy, -⟩ := (hloc v hv (P.p v g)).1 (hgl v hv)
        exact ⟨_, hy⟩
      choose! z hz1 hz2 using hl
      obtain ⟨w, hw⟩ := glue (fun v => if v ∈ S then z v else 1) (fun v hv => if_neg hv)
      have hw1 : w ∈ DC (P.box U) a := (key a ha w).2
        ⟨fun v hv => by rw [hw, if_pos hv]; exact hz1 v hv,
         fun v hv => by rw [hw, if_neg hv]; exact one_mem _⟩
      have hw2 : w⁻¹ * g ∈ DC (P.box U) b := (key b hb _).2
        ⟨fun v hv => by rw [map_mul, map_inv, hw, if_pos hv]; exact hz2 v hv,
         fun v hv => by rw [map_mul, map_inv, hw, if_neg hv, inv_one, one_mul]; exact hgN v hv⟩
      refine ⟨(w : G ⧸ P.box U), out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset hw1 hw2, ?_⟩
      rintro y ⟨hy1, hy2⟩
      refine (quotientGroup_coe_out_eq_self _ _).symm.trans (QuotientGroup.eq.2 ?_)
      rw [hB]
      intro v
      rw [map_mul, map_inv]
      have ha1 := (key a ha _).1 hy1
      have hb1 := (key b hb _).1 hy2
      by_cases hv : v ∈ S
      · have hb2 := hb1.1 v hv
        rw [map_mul, map_inv] at hb2
        have hz2' := hz2 v hv
        rw [← if_pos (c := v ∈ S) (t := z v) (e := 1) hv, ← hw v] at hz2'
        have hz1' := hz1 v hv
        rw [← if_pos (c := v ∈ S) (t := z v) (e := 1) hv, ← hw v] at hz1'
        have e := ((hloc v hv (P.p v g)).1 (hgl v hv)).unique
          (out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset (ha1.1 v hv) hb2) (out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset hz1' hz2')
        exact QuotientGroup.eq.1 e
      · rw [hw, if_neg hv]
        exact mul_mem (inv_mem (ha1.2 v hv)) (one_mem _)
    · intro y hy1 hy2
      refine (key _ hab g).2 ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have h2 := ((key b hb _).1 hy2).1 v hv
        rw [map_mul, map_inv] at h2
        rw [map_mul]
        exact (hloc v hv (P.p v g)).2 (P.p v y) (((key a ha y).1 hy1).1 v hv) h2
      · have h1 := ((key a ha y).1 hy1).2 v hv
        have h2 := ((key b hb _).1 hy2).2 v hv
        rw [map_mul, map_inv] at h2
        have h3 := mul_mem h1 h2
        rwa [mul_inv_cancel_left] at h3

end
