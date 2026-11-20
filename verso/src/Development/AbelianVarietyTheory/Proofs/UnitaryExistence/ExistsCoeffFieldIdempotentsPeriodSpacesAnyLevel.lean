import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentCuttingPeriodSpaces

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompRat

open GlobalTheory.CompIdem ReciprocityTheory.ChartRestriction.G.TB.ValAt

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ₀ g ty F _ _ _ hA c`. Take `rfl : σ₀ = (KA l).val.toRingHom` from `RingHom.ext hA`. Use `CompFin.quasiCompact_alt Xo` as an intermediate fact. Use `Xo.smooth` as an intermediate fact. Establish `: Smooth Xo.s` using `SmoothOfRelativeDimension.smooth D.dim Xo.s`.

Take `⟨S, hS, hrat⟩` from `exists_rational_components (c.le.trans (coeff_le_algebraicClosure c)) Xo.s`. Use `c.fin` as an intermediate fact. Set `b` to `Module.finBasis ℚ c.F`. Take `⟨c', hc'⟩` from `exists_coeff_containing E H l (S ∪ Finset.univ.image fun j => (b j : ℂ)) (by`. Introduce `z hz`.

Break down `Finset.mem_union.1 hz with h | h` into its components or cases. Conclude with `mem_algebraicClosure_iff.1 (hS z h)`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 h`. Conclude with `mem_algebraicClosure_iff.1 (coeff_le_algebraicClosure c (b j).2))`. Use `⟨c', fun z hz => ?_, fun i => ?_⟩` and prove the remaining obligations.

Establish `e` using `congrArg c.F.val (b.sum_repr ⟨z, hz⟩)`. Rewrite `e` using `[map_sum]`. Establish `e' : z = _` using `e.symm`. Rewrite using `[e']`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_rat_smul]`. Conclude with `IntermediateField.smul_mem _ (hc' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))`. Establish `hr` using `hrat c'.F c'.le (coeff_le_algebraicClosure c') fun z hz => hc' z (Finset.mem_union_left _ hz)`. Take `⟨t, ht, hcont⟩` from `exists_index F`. Use `CompFin.isNoetherian_XF Xo c'` as an intermediate fact.

Set `σ : c'.F →+* ℂ` to `c'.F.val.toRingHom`. Set `s : Xo.XF c' ⟶ Sp c'.F` to `pullback.snd _ _`. Set `pr : Xo.XF c' ⟶ Xo.X` to `pullback.fst _ _`. Establish `hover : ∀ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → (p ≫ pr) ≫ Xo.s = spMap (KA l).val.toRingHom`. Introduce `p hp`.

Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hp, GlobalTheory.CompIdem.spMap_comp]`. Both sides reduce to the same expression. Establish `hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → q ≫ s = spMap σ → p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) → t (p ≫ pr) = t (q ≫ pr)`. Introduce `p q hp hq hpq`. Take `⟨r, hr1, hr2⟩` from `hr (q (IsLocalRing.closedPoint ℂ))`.

Conclude with `const_on_component σ s r hr1 (fun x => t (x ≫ pr)) (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _)) p q hp hq ((connectedComponent_eq hr2) ▸ hpq) hr2`. Set `U : Set (Xo.XF c')` to `{z | ∃ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ ∧ p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i}`. Establish `hUc : ∀ z w, w ∈ connectedComponent z → (w ∈ U ↔ z ∈ U)`. Introduce `z w h`. Simplify using `only [U, Set.mem_setOf_eq, connectedComponent_eq h]`.

Establish `hU : IsClopen U`. Use `⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `⟨connectedComponent z, fun w hw h => hz ((hUc z w hw).1 h), isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩`. Conclude with `⟨connectedComponent z, fun w hw => (hUc z w hw).2 hz, isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩`. Take `⟨e, h1, h2⟩` from `exists_indicator_function U hU`.

Use `⟨e, h1, fun i' P hP p hp1 hp => ?_⟩` and prove the remaining obligations. Establish `hp' : t (p ≫ pr) = i'`. Establish `: p ≫ pr = F.u i' P` using `hp1`. Rewrite using `[this]`. Conclude with `ht i' P hP`.

Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `(h2 p).1 ⟨p, hp, mem_connectedComponent, hp'⟩`. Use `(h2 p).2 ?_` and prove the remaining obligations. Introduce and unpack `⟨q, hq, hqp, hqi⟩`.

Conclude with `h (Fin.ext (hp'.symm.trans ((hconst q p hq hp hqp).symm.trans hqi)))`.
-/
theorem exists_coeff_idempotents_any_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo σ₀ g ty F _ _ _ hA c
  obtain rfl : σ₀ = (KA l).val.toRingHom := RingHom.ext hA
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨S, hS, hrat⟩ := exists_rational_components (c.le.trans (coeff_le_algebraicClosure c)) Xo.s
  have := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c', hc'⟩ := exists_coeff_containing E H l (S ∪ Finset.univ.image fun j => (b j : ℂ)) (by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact mem_algebraicClosure_iff.1 (hS z h)
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
      exact mem_algebraicClosure_iff.1 (coeff_le_algebraicClosure c (b j).2))
  refine ⟨c', fun z hz => ?_, fun i => ?_⟩
  · have e := congrArg c.F.val (b.sum_repr ⟨z, hz⟩)
    rw [map_sum] at e
    have e' : z = _ := e.symm
    rw [e']
    refine sum_mem fun j _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _
      (hc' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have hr := hrat c'.F c'.le (coeff_le_algebraicClosure c') fun z hz => hc' z (Finset.mem_union_left _ hz)
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c'
  let σ : c'.F →+* ℂ := c'.F.val.toRingHom
  let s : Xo.XF c' ⟶ Sp c'.F := pullback.snd _ _
  let pr : Xo.XF c' ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → (p ≫ pr) ≫ Xo.s = spMap (KA l).val.toRingHom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, GlobalTheory.CompIdem.spMap_comp]
    rfl
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    intro p q hp hq hpq
    obtain ⟨r, hr1, hr2⟩ := hr (q (IsLocalRing.closedPoint ℂ))
    exact const_on_component σ s r hr1 (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
      p q hp hq ((connectedComponent_eq hr2) ▸ hpq) hr2
  let U : Set (Xo.XF c') := {z | ∃ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ ∧
    p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i}
  have hUc : ∀ z w, w ∈ connectedComponent z → (w ∈ U ↔ z ∈ U) := by
    intro z w h
    simp only [U, Set.mem_setOf_eq, connectedComponent_eq h]
  have hU : IsClopen U := by
    refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hUc z w hw).1 h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hUc z w hw).2 hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  obtain ⟨e, h1, h2⟩ := exists_indicator_function U hU
  refine ⟨e, h1, fun i' P hP p hp1 hp => ?_⟩
  have hp' : t (p ≫ pr) = i' := by
    have : p ≫ pr = F.u i' P := hp1
    rw [this]
    exact ht i' P hP
  split_ifs with h
  · subst h
    exact (h2 p).1 ⟨p, hp, mem_connectedComponent, hp'⟩
  · refine (h2 p).2 ?_
    rintro ⟨q, hq, hqp, hqi⟩
    exact h (Fin.ext (hp'.symm.trans ((hconst q p hq hp hqp).symm.trans hqi)))

end GlobalTheory.CompRat
