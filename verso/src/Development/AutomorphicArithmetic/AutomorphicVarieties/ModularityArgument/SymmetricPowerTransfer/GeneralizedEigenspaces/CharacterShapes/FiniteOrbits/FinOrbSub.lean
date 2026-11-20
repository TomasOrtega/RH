import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G : Type} [Group G] {S U : Subgroup G}

/- English proof (translation)
Take `⟨u, hu, u', hu', rfl⟩` from `h`. Conclude with `⟨u, Subgroup.mem_subgroupOf.mp hu, u', Subgroup.mem_subgroupOf.mp hu', by simp⟩`.
-/
private theorem dc_up {x g : S} (h : g ∈ DC (U.subgroupOf S) x) : (g : G) ∈ DC U (x : G) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := h
  exact ⟨u, Subgroup.mem_subgroupOf.mp hu, u', Subgroup.mem_subgroupOf.mp hu', by simp⟩

/- English proof (translation)
Take `⟨u, hu, u', hu', rfl⟩` from `hz`. Conclude with `⟨w * u, U.mul_mem hw hu, u', hu', by simp only [mul_assoc]⟩`.
-/
private theorem dc_left {b w z : G} (hw : w ∈ U) (hz : z ∈ DC U b) : w * z ∈ DC U b := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hz
  exact ⟨w * u, U.mul_mem hw hu, u', hu', by simp only [mul_assoc]⟩

/- English proof (translation)
Take `⟨u, hu, u', hu', rfl⟩` from `hz`. Conclude with `⟨u, hu, u' * w, U.mul_mem hu' hw, by simp only [mul_assoc]⟩`.
-/
private theorem dc_right {b w z : G} (hw : w ∈ U) (hz : z ∈ DC U b) : z * w ∈ DC U b := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hz
  exact ⟨u, hu, u' * w, U.mul_mem hu' hw, by simp only [mul_assoc]⟩

/- English proof (translation)
Take `⟨u, hu, u', hu', rfl⟩` from `hy`. Take `⟨c, hc, hcx, hcS⟩` from `hx u hu`. Use `⟨⟨u * c⁻¹, hcS⟩, Subgroup.mem_subgroupOf.mpr (U.mul_mem hu (U.inv_mem hc)), ?_⟩` and prove the remaining obligations. Establish `e : ((⟨u * c⁻¹, hcS⟩ * x : S) : G)⁻¹ * (u * (x : G) * u') = c * u'`. Simplify using `only [Subgroup.coe_mul, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]`.

Rewrite using `[← mul_assoc c, hcx]`. Use `group`. Rewrite using `[e]`. Conclude with `U.mul_mem hc hu'`.
-/
private theorem dc_rep {x : S} (hx : ∀ u ∈ U, ∃ c ∈ U, c * (x : G) = x * c ∧ u * c⁻¹ ∈ S)
    {y : G} (hy : y ∈ DC U (x : G)) :
    ∃ t : S, t ∈ U.subgroupOf S ∧ ((t * x : S) : G)⁻¹ * y ∈ U := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hy
  obtain ⟨c, hc, hcx, hcS⟩ := hx u hu
  refine ⟨⟨u * c⁻¹, hcS⟩, Subgroup.mem_subgroupOf.mpr (U.mul_mem hu (U.inv_mem hc)), ?_⟩
  have e : ((⟨u * c⁻¹, hcS⟩ * x : S) : G)⁻¹ * (u * (x : G) * u') = c * u' := by
    simp only [Subgroup.coe_mul, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc c, hcx]
    group
  rw [e]
  exact U.mul_mem hc hu'

/- English proof (translation)
Take `⟨t, ht, hw⟩` from `dc_rep hx hg`. Use `⟨t, ht, (t * x)⁻¹ * g, Subgroup.mem_subgroupOf.2 (by simpa using hw), ?_⟩` and prove the remaining obligations. Use `group`.
-/
private theorem dc_down {x g : S} (hx : ∀ u ∈ U, ∃ c ∈ U, c * (x : G) = x * c ∧ u * c⁻¹ ∈ S)
    (hg : (g : G) ∈ DC U (x : G)) : g ∈ DC (U.subgroupOf S) x := by
  obtain ⟨t, ht, hw⟩ := dc_rep hx hg
  refine ⟨t, ht, (t * x)⁻¹ * g, Subgroup.mem_subgroupOf.2 (by simpa using hw), ?_⟩
  group

/- English proof (translation)
Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `using h`.
-/
private theorem mk_eq_of {r r' : S} (h : (r : G)⁻¹ * r' ∈ U) :
    (r : S ⧸ U.subgroupOf S) = r' := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using h

/- English proof (translation)
Establish `inj : Function.Injective (fun q : S ⧸ U.subgroupOf S => (((Quotient.out q : S) : G) : G ⧸ U))`. Introduce `q1 q2 e`. Simplify using `only at e`. Establish `e'` using `QuotientGroup.eq.mp e`. Combine the equalities or inequalities in the displayed calculation.

Apply `Set.Finite.of_finite_image _ inj.injOn` to reduce the goal to its premises. Apply `h.subset` to reduce the goal to its premises. Introduce and unpack `_ ⟨q, ⟨k, rfl⟩, rfl⟩`. Take `⟨t, ht⟩` from `QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (k.1 * a)`. Use `⟨⟨((k.1 : S) : G), k.2⟩, ?_⟩` and prove the remaining obligations.

Establish `hq : (k • (a : S ⧸ U.subgroupOf S)) = ((k.1 * a : S) : S ⧸ U.subgroupOf S)` using `rfl`. Simplify using `only`. Rewrite using `[hq, ht]`. Use `show ((((k.1 : S) : G) * (a : G) : G) : G ⧸ U) = _`. Rewrite using `[QuotientGroup.eq]`.

Use `Subgroup.mem_subgroupOf.mp t.2 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Subgroup.coe_mul]`. Use `group`.
-/
private theorem finOrb_sub {a : S} (h : AlgebraTools.FinOrb U U (a : G)) :
    AlgebraTools.FinOrb (U.subgroupOf S) (U.subgroupOf S) a := by
  have inj : Function.Injective
      (fun q : S ⧸ U.subgroupOf S => (((Quotient.out q : S) : G) : G ⧸ U)) := by
    intro q1 q2 e
    dsimp only at e
    have e' := QuotientGroup.eq.mp e
    calc q1 = ((Quotient.out q1 : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q1).symm
      _ = ((Quotient.out q2 : S) : S ⧸ U.subgroupOf S) := mk_eq_of e'
      _ = q2 := QuotientGroup.out_eq' q2
  apply Set.Finite.of_finite_image _ inj.injOn
  apply h.subset
  rintro _ ⟨q, ⟨k, rfl⟩, rfl⟩
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (k.1 * a)
  refine ⟨⟨((k.1 : S) : G), k.2⟩, ?_⟩
  have hq : (k • (a : S ⧸ U.subgroupOf S)) = ((k.1 * a : S) : S ⧸ U.subgroupOf S) := rfl
  dsimp only
  rw [hq, ht]
  show ((((k.1 : S) : G) * (a : G) : G) : G ⧸ U) = _
  rw [QuotientGroup.eq]
  convert Subgroup.mem_subgroupOf.mp t.2 using 1
  simp only [Subgroup.coe_mul]
  group

/- English proof (translation)
Establish `ha : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S` using `fun u hu => by`. Take `⟨c, hc, h1, -, h3, -⟩` from `hab u hu`. Conclude with `⟨c, hc, h1, h3⟩`. Establish `hb : ∀ u ∈ U, ∃ c ∈ U, c * (b : G) = b * c ∧ u * c⁻¹ ∈ S` using `fun u hu => by`. Take `⟨c, hc, -, h2, h3, -⟩` from `hab u hu`.

Conclude with `⟨c, hc, h2, h3⟩`. Establish `hab' : ∀ u ∈ U, ∃ c ∈ U, c * ((a * b : S) : G) = ((a * b : S) : G) * c ∧ u * c⁻¹ ∈ S` using `fun u hu => by`. Take `⟨c, hc, h1, h2, h3, -⟩` from `hab u hu`. Use `⟨c, hc, ?_, h3⟩` and prove the remaining obligations. Simplify using `only [Subgroup.coe_mul]`.

Rewrite using `[← mul_assoc, h1, mul_assoc, h2, mul_assoc]`. Introduce `g`. Use `⟨fun hg => ?_, fun y hy hyg => ?_⟩` and prove the remaining obligations. Establish `hg' : (g : G) ∈ DC U ((a : G) * b)`. Rewrite using `[← Subgroup.coe_mul]`.

Conclude with `dc_up hg`. Take `⟨Y, ⟨hY1, hY2⟩, hYu⟩` from `(hUF g).1 hg'`. Take `⟨t, ht, htY⟩` from `dc_rep ha hY1`. Establish `hrg : (t * a)⁻¹ * g ∈ DC (U.subgroupOf S) b`. Apply `dc_down hb` to reduce the goal to its premises.

Establish `e : (((t * a)⁻¹ * g : S) : G) = (((t * a : S) : G)⁻¹ * Quotient.out Y) * ((Quotient.out Y)⁻¹ * g)`. Use `push_cast`. Use `group`. Rewrite using `[e]`. Conclude with `dc_left htY hY2`.

Establish `hrY : ((((t * a : S) : G)) : G ⧸ U) = Y`. Rewrite using `[← QuotientGroup.out_eq' Y]`. Conclude with `QuotientGroup.eq.mpr htY`. Establish `key : ∀ s : G, s ∈ DC U a → s⁻¹ * g ∈ DC U b → (s : G ⧸ U) = Y`. Introduce `s hs1 hs2`.

Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul U s`. Use `hYu _ ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Conclude with `dc_right k.2 hs1`. Rewrite using `[hk, mul_inv_rev, mul_assoc]`.

Conclude with `dc_left (inv_mem k.2) hs2`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (t * a)`. Use `⟨((t * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Conclude with `dc_right k.2 ⟨t, ht, 1, one_mem _, (mul_one _).symm⟩`.

Rewrite using `[hk, mul_inv_rev, mul_assoc]`. Conclude with `dc_left (inv_mem k.2) hrg`. Introduce and unpack `z ⟨hz1, hz2⟩`. Establish `hz : (((Quotient.out z : S) : G) : G ⧸ U) = Y` using `key _ (dc_up hz1) (by simpa using dc_up hz2)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h1` using `(hUF g).2 y (dc_up hy) (by simpa using dc_up hyg)`. Apply `dc_down hab'` to reduce the goal to its premises. Rewrite using `[Subgroup.coe_mul]`. Conclude with `h1`.
-/
private theorem uf_sub {a b : S}
    (hab : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ c * (b : G) = b * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S)
    (hUF : UF U (a : G) (b : G)) : UF (U.subgroupOf S) a b := by
  have ha : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, h1, -, h3, -⟩ := hab u hu
    exact ⟨c, hc, h1, h3⟩
  have hb : ∀ u ∈ U, ∃ c ∈ U, c * (b : G) = b * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, -, h2, h3, -⟩ := hab u hu
    exact ⟨c, hc, h2, h3⟩
  have hab' : ∀ u ∈ U, ∃ c ∈ U, c * ((a * b : S) : G) = ((a * b : S) : G) * c ∧ u * c⁻¹ ∈ S :=
    fun u hu => by
      obtain ⟨c, hc, h1, h2, h3, -⟩ := hab u hu
      refine ⟨c, hc, ?_, h3⟩
      simp only [Subgroup.coe_mul]
      rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  intro g
  refine ⟨fun hg => ?_, fun y hy hyg => ?_⟩
  · have hg' : (g : G) ∈ DC U ((a : G) * b) := by
      rw [← Subgroup.coe_mul]
      exact dc_up hg
    obtain ⟨Y, ⟨hY1, hY2⟩, hYu⟩ := (hUF g).1 hg'
    obtain ⟨t, ht, htY⟩ := dc_rep ha hY1
    have hrg : (t * a)⁻¹ * g ∈ DC (U.subgroupOf S) b := by
      apply dc_down hb
      have e : (((t * a)⁻¹ * g : S) : G)
          = (((t * a : S) : G)⁻¹ * Quotient.out Y) * ((Quotient.out Y)⁻¹ * g) := by
        push_cast
        group
      rw [e]
      exact dc_left htY hY2
    have hrY : ((((t * a : S) : G)) : G ⧸ U) = Y := by
      rw [← QuotientGroup.out_eq' Y]
      exact QuotientGroup.eq.mpr htY
    have key : ∀ s : G, s ∈ DC U a → s⁻¹ * g ∈ DC U b → (s : G ⧸ U) = Y := by
      intro s hs1 hs2
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul U s
      refine hYu _ ⟨?_, ?_⟩
      · rw [hk]
        exact dc_right k.2 hs1
      · rw [hk, mul_inv_rev, mul_assoc]
        exact dc_left (inv_mem k.2) hs2
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (t * a)
    refine ⟨((t * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · rw [hk]
      exact dc_right k.2 ⟨t, ht, 1, one_mem _, (mul_one _).symm⟩
    · rw [hk, mul_inv_rev, mul_assoc]
      exact dc_left (inv_mem k.2) hrg
    · rintro z ⟨hz1, hz2⟩
      have hz : (((Quotient.out z : S) : G) : G ⧸ U) = Y :=
        key _ (dc_up hz1) (by simpa using dc_up hz2)
      calc z = ((Quotient.out z : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' z).symm
        _ = _ := mk_eq_of (QuotientGroup.eq.mp (hz.trans hrY.symm))
  · have h1 := (hUF g).2 y (dc_up hy) (by simpa using dc_up hyg)
    apply dc_down hab'
    rw [Subgroup.coe_mul]
    exact h1

/- English proof (translation)
Establish `orb : ∀ k : S, k ∈ U.subgroupOf S → ((k * a : S) : S ⧸ U.subgroupOf S) ∈ MulAction.orbit (U.subgroupOf S) (a : S ⧸ U.subgroupOf S)` using `fun k hk => ⟨⟨k, hk⟩, rfl⟩`. Use `⟨hfin.toFinset.image (fun q => Quotient.out q), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨q, hq, rfl⟩` from `Finset.mem_image.mp hy`. Take `⟨k, rfl⟩` from `hfin.mem_toFinset.mp hq`.

Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (U.subgroupOf S) ((k : S) * a)`. Establish `hq' : k • (a : S ⧸ U.subgroupOf S) = (((k : S) * a : S) : S ⧸ U.subgroupOf S)` using `rfl`. Simplify using `only`. Rewrite using `[hq', hh]`. Conclude with `dc_right h.2 ⟨k, k.2, 1, one_mem _, (mul_one _).symm⟩`.

Introduce `y hy`. Take `⟨u, hu, u', hu', rfl⟩` from `hy`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (u * a)`. Use `⟨Quotient.out ((u * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr (orb u hu), rfl⟩`.

Rewrite using `[hh]`. Establish `e : (u * a * (h : S))⁻¹ * (u * a * u') = (h : S)⁻¹ * u'` using `by group`. Rewrite using `[e]`. Conclude with `mul_mem (inv_mem h.2) hu'`. Introduce and unpack `r ⟨hr, hry⟩`.

Take `⟨q, -, rfl⟩` from `Finset.mem_image.mp hr`. Establish `e : q = ((u * a : S) : S ⧸ U.subgroupOf S)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show (u * a * u')⁻¹ * (u * a) = u'⁻¹ by group]`. Conclude with `inv_mem hu')`.

Rewrite using `[e]`. Introduce `y hy`. Take `⟨t, ht, hty⟩` from `dc_rep ha hy`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (t * a)`. Use `⟨Quotient.out ((t * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr (orb t ht), rfl⟩`. Rewrite using `[hh]`. Establish `e : ((t * a * (h : S) : S) : G)⁻¹ * y = ((h : S) : G)⁻¹ * (((t * a : S) : G)⁻¹ * y)`. Use `push_cast`. Use `group`.

Rewrite using `[e]`. Conclude with `mul_mem (inv_mem (Subgroup.mem_subgroupOf.mp h.2)) hty`. Introduce and unpack `r ⟨hr, hry⟩`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.mp hr`. Establish `e : q = ((t * a : S) : S ⧸ U.subgroupOf S)`.

Combine the equalities or inequalities in the displayed calculation. Establish `m` using `U.mul_mem hry (U.inv_mem hty)`. Use `m using 1` and compare the differences between its conclusion and the goal. Use the proof step `group)`. Rewrite using `[e]`.
-/
private theorem reps_sub {a : S} (ha : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S)
    (hfin : AlgebraTools.FinOrb (U.subgroupOf S) (U.subgroupOf S) a) :
    ∃ R : Finset S, (∀ y ∈ R, y ∈ DC (U.subgroupOf S) a) ∧
      (∀ y ∈ DC (U.subgroupOf S) a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U.subgroupOf S) ∧
      ∀ y ∈ DC U (a : G), ∃! r : S, r ∈ R ∧ (r : G)⁻¹ * y ∈ U := by
  classical
  have orb : ∀ k : S, k ∈ U.subgroupOf S →
      ((k * a : S) : S ⧸ U.subgroupOf S) ∈
        MulAction.orbit (U.subgroupOf S) (a : S ⧸ U.subgroupOf S) :=
    fun k hk => ⟨⟨k, hk⟩, rfl⟩
  refine ⟨hfin.toFinset.image (fun q => Quotient.out q), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, rfl⟩ := hfin.mem_toFinset.mp hq
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) ((k : S) * a)
    have hq' : k • (a : S ⧸ U.subgroupOf S) = (((k : S) * a : S) : S ⧸ U.subgroupOf S) := rfl
    dsimp only
    rw [hq', hh]
    exact dc_right h.2 ⟨k, k.2, 1, one_mem _, (mul_one _).symm⟩
  · intro y hy
    obtain ⟨u, hu, u', hu', rfl⟩ := hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (u * a)
    refine ⟨Quotient.out ((u * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr (orb u hu), rfl⟩
    · rw [hh]
      have e : (u * a * (h : S))⁻¹ * (u * a * u') = (h : S)⁻¹ * u' := by group
      rw [e]
      exact mul_mem (inv_mem h.2) hu'
    · rintro r ⟨hr, hry⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
      have e : q = ((u * a : S) : S ⧸ U.subgroupOf S) :=
        calc q = ((Quotient.out q : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q).symm
          _ = ((u * a * u' : S) : S ⧸ U.subgroupOf S) := QuotientGroup.eq.mpr hry
          _ = _ := QuotientGroup.eq.mpr (by
            rw [show (u * a * u')⁻¹ * (u * a) = u'⁻¹ by group]
            exact inv_mem hu')
      rw [e]
  · intro y hy
    obtain ⟨t, ht, hty⟩ := dc_rep ha hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (t * a)
    refine ⟨Quotient.out ((t * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr (orb t ht), rfl⟩
    · rw [hh]
      have e : ((t * a * (h : S) : S) : G)⁻¹ * y
          = ((h : S) : G)⁻¹ * (((t * a : S) : G)⁻¹ * y) := by
        push_cast
        group
      rw [e]
      exact mul_mem (inv_mem (Subgroup.mem_subgroupOf.mp h.2)) hty
    · rintro r ⟨hr, hry⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
      have e : q = ((t * a : S) : S ⧸ U.subgroupOf S) :=
        calc q = ((Quotient.out q : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q).symm
          _ = _ := mk_eq_of (by
            have m := U.mul_mem hry (U.inv_mem hty)
            convert m using 1
            group)
      rw [e]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

/- English proof (translation)
Introduce `G V _ _ _ S U a hfin ha _`. Establish `ha' : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S` using `fun u hu => by`. Take `⟨c, hc, h1, h2, _⟩` from `ha u hu`. Conclude with `⟨c, hc, h1, h2⟩`. Establish `hfin'` using `finOrb_sub hfin`.

Conclude with `⟨hfin', fun g => ⟨dc_up, dc_down ha'⟩, fun b hb hUF => uf_sub hb hUF, reps_sub ha' hfin'⟩`.
-/
theorem UpperTheory.V.Z.Sym.So.dcSub :
    UpperTheory.V.Z.Sym.So.DcSub := by
  intro G V _ _ _ S U a hfin ha _
  have ha' : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, h1, h2, _⟩ := ha u hu
    exact ⟨c, hc, h1, h2⟩
  have hfin' := finOrb_sub hfin
  exact ⟨hfin', fun g => ⟨dc_up, dc_down ha'⟩, fun b hb hUF => uf_sub hb hUF, reps_sub ha' hfin'⟩

end
