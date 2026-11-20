import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompRat

open GlobalTheory.CompIdem ReciprocityTheory.ChartRestriction.G.TB.ValAt

/- English proof (translation)
Set `V : Bool → X.Opens` to `fun b => match b with`. Consider the case `true => ⟨U, hU.2⟩`. Consider the case `false => ⟨Uᶜ, hU.1.isOpen_compl⟩`. Set `sf : ∀ b, Γ(X, V b)` to `fun b => match b with`. Consider the case `true => 1`.

Consider the case `false => 0`. Establish `hcov : (⊤ : X.Opens) ≤ iSup V`. Introduce `x _`. Rewrite using `[TopologicalSpace.Opens.mem_iSup]`. Distinguish the cases in `h : x ∈ U`.

Conclude with `⟨true, h⟩`. Conclude with `⟨false, h⟩`. Establish `hsub : ∀ W : X.Opens, W = ⊥ → Subsingleton Γ(X, W)`. Introduce and unpack `_ rfl`. Use `infer_instance`.

Establish `hcomp : TopCat.Presheaf.IsCompatible X.presheaf V sf`. Introduce `a b`. Apply the tactic sequence `cases a <;> cases b`. Simplify using `[sf]`. Use `(hsub _ ?_).elim _ _` and prove the remaining obligations.

Use extensionality with `x`. Simplify using `[V]`. Use `(hsub _ ?_).elim _ _` and prove the remaining obligations. Use extensionality with `x`. Simplify using `[V]`.

Simplify using `[sf]`. Take `⟨e, he'⟩ : ∃ e : Γ(X, ⊤), ∀ b, X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e = sf b` from `(X.sheaf.existsUnique_gluing' V ⊤ (fun b => homOfLE le_top) hcov sf hcomp).exists`. Establish `hpt : ∀ (x : Sp ℂ ⟶ X) (b : Bool), x (IsLocalRing.closedPoint ℂ) ∈ V b → ⊤ ≤ x ⁻¹ᵁ V b`. Introduce `x b h z _`. Rewrite using `[Subsingleton.elim (α := PrimeSpectrum ℂ) z (IsLocalRing.closedPoint ℂ)]` and apply the resulting hypothesis.

Use `⟨e, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Use `X.sheaf.eq_of_locally_eq' V ⊤ (fun b => homOfLE le_top) hcov _ _ fun b => ?_ show X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op (e * e) = X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e` and prove the remaining obligations. Rewrite using `[map_mul, he']`. Apply the tactic sequence `cases b <;> simp [sf]`. Use `(TB.ValAt.valAt'_res x le_top (hpt x true h) e).symm.trans ((congrArg (valAt' x _) (he' true)).trans ?_)` and prove the remaining obligations.

Conclude with `TB.ValAt.valAt'_one x _ (hpt x true h)`. Use `(TB.ValAt.valAt'_res x le_top (hpt x false h) e).symm.trans ((congrArg (valAt' x _) (he' false)).trans ?_)` and prove the remaining obligations. Conclude with `(valHom x _ (hpt x false h)).map_zero`.
-/
theorem exists_indicator_function {X : Scheme.{0}} (U : Set X) (hU : IsClopen U) :
    ∃ e : Γ(X, ⊤), e * e = e ∧ ∀ x : Sp ℂ ⟶ X,
      (x (IsLocalRing.closedPoint ℂ) ∈ U → valAt' x ⊤ e = 1) ∧
      (x (IsLocalRing.closedPoint ℂ) ∉ U → valAt' x ⊤ e = 0) := by
  let V : Bool → X.Opens := fun b => match b with
    | true => ⟨U, hU.2⟩
    | false => ⟨Uᶜ, hU.1.isOpen_compl⟩
  let sf : ∀ b, Γ(X, V b) := fun b => match b with
    | true => 1
    | false => 0
  have hcov : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases h : x ∈ U
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  have hsub : ∀ W : X.Opens, W = ⊥ → Subsingleton Γ(X, W) := by
    rintro _ rfl
    infer_instance
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf V sf := by
    intro a b
    cases a <;> cases b
    · simp [sf]
    · refine (hsub _ ?_).elim _ _
      ext x
      simp [V]
    · refine (hsub _ ?_).elim _ _
      ext x
      simp [V]
    · simp [sf]
  obtain ⟨e, he'⟩ : ∃ e : Γ(X, ⊤), ∀ b, X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e = sf b :=
    (X.sheaf.existsUnique_gluing' V ⊤ (fun b => homOfLE le_top) hcov sf hcomp).exists
  have hpt : ∀ (x : Sp ℂ ⟶ X) (b : Bool), x (IsLocalRing.closedPoint ℂ) ∈ V b → ⊤ ≤ x ⁻¹ᵁ V b := by
    intro x b h z _
    rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) z (IsLocalRing.closedPoint ℂ)]
  refine ⟨e, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine X.sheaf.eq_of_locally_eq' V ⊤ (fun b => homOfLE le_top) hcov _ _ fun b => ?_
    show X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op (e * e) = X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e
    rw [map_mul, he']
    cases b <;> simp [sf]
  · refine (TB.ValAt.valAt'_res x le_top (hpt x true h) e).symm.trans ((congrArg (valAt' x _) (he' true)).trans ?_)
    exact TB.ValAt.valAt'_one x _ (hpt x true h)
  · refine (TB.ValAt.valAt'_res x le_top (hpt x false h) e).symm.trans ((congrArg (valAt' x _) (he' false)).trans ?_)
    exact (valHom x _ (hpt x false h)).map_zero

/- English proof (translation)
Establish `hz : zeta l.A = 1`. Rewrite using `[hA, zeta, Nat.cast_one, div_one, Complex.exp_two_pi_mul_I]`. Use extensionality with `⟨x, hx⟩`. Use `show σ ⟨x, hx⟩ = x`. Proceed by induction on `hx using IntermediateField.adjoin_induction with`.

Consider the case `mem x hx`. Break down `hx with rfl | rfl` into its components or cases. Conclude with `hσ`. Establish `: (⟨zeta l.A, IntermediateField.subset_adjoin _ _ (by simp)⟩ : KA l) = 1` using `Subtype.ext hz`. Conclude with `(congrArg σ this).trans ((map_one σ).trans hz.symm)`.

Consider the case `algebraMap q => exact (map_ratCast σ q)`. Consider the case `add x y hx hy h1 h2 => exact (map_add σ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])`. Consider the case `mul x y hx hy h1 h2 => exact (map_mul σ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])`. Consider the case `inv x hx h1 => exact (map_inv₀ σ ⟨x, hx⟩).trans (by rw [h1])`.
-/
theorem eq_val_of_A_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (σ : KA l →+* ℂ) (hσ : σ (baseKA l).ρ = H.rt0) (hA : l.A = 1) : σ = (KA l).val.toRingHom := by
  have hz : zeta l.A = 1 := by
    rw [hA, zeta, Nat.cast_one, div_one, Complex.exp_two_pi_mul_I]
  ext ⟨x, hx⟩
  show σ ⟨x, hx⟩ = x
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hσ
    · have : (⟨zeta l.A, IntermediateField.subset_adjoin _ _ (by simp)⟩ : KA l) = 1 := Subtype.ext hz
      exact (congrArg σ this).trans ((map_one σ).trans hz.symm)
  | algebraMap q => exact (map_ratCast σ q)
  | add x y hx hy h1 h2 => exact (map_add σ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])
  | mul x y hx hy h1 h2 => exact (map_mul σ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])
  | inv x hx h1 => exact (map_inv₀ σ ⟨x, hx⟩).trans (by rw [h1])

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ₀ g ty F _ hσ _ hA c`. Take `rfl` from `eq_val_of_A_eq_one σ₀ hσ hA`. Use `CompFin.quasiCompact_alt Xo` as an intermediate fact. Use `Xo.smooth` as an intermediate fact. Establish `: Smooth Xo.s` using `SmoothOfRelativeDimension.smooth D.dim Xo.s`.

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
theorem exists_coeff_idempotent_functions :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo σ₀ g ty F _ hσ _ hA c
  obtain rfl := eq_val_of_A_eq_one σ₀ hσ hA
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
