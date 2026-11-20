import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.CrdIso

variable {X : Scheme.{0}}

/- English proof (translation)
Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem rr {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

/- English proof (translation)
Use `erw [Scheme.basicOpen_res]`. Both sides reduce to the same expression.
-/
theorem mem_res {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen (resG X h a) ↔ x ∈ V ∧ x ∈ X.basicOpen a := by
  erw [Scheme.basicOpen_res]
  rfl

/- English proof (translation)
Establish `hu : IsUnit (resG X (X.basicOpen_le a) a)` using `X.toRingedSpace.isUnit_res_basicOpen a`. Use `hu.map (resG X hV)` as an intermediate fact. Rewrite `this` using `[rr]`. Then use the resulting hypothesis.
-/
theorem isUnit_res {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) (hV : V ≤ X.basicOpen a) :
    IsUnit (resG X h a) := by
  have hu : IsUnit (resG X (X.basicOpen_le a) a) := X.toRingedSpace.isUnit_res_basicOpen a
  have := hu.map (resG X hV)
  rwa [rr] at this

/- English proof (translation)
Apply `TopCat.Presheaf.section_ext X.sheaf V` to reduce the goal to its premises. Introduce `x hx`. Take `⟨j, hj⟩` from `ha x hx`. Establish `hu` using `(Scheme.mem_basicOpen X (a j) x hx).1 hj`. Use `congrArg (X.presheaf.germ V x hx).hom (h j)` as an intermediate fact.

Rewrite `this` using `[map_mul, map_mul]`. Conclude with `hu.mul_right_cancel this`.
-/
theorem cancel {V : X.Opens} {J : Type} (a : J → Γ(X, V)) (ha : ∀ x ∈ V, ∃ j, x ∈ X.basicOpen (a j))
    {u u' : Γ(X, V)} (h : ∀ j, u * a j = u' * a j) : u = u' := by
  apply TopCat.Presheaf.section_ext X.sheaf V
  intro x hx
  obtain ⟨j, hj⟩ := ha x hx
  have hu := (Scheme.mem_basicOpen X (a j) x hx).1 hj
  have := congrArg (X.presheaf.germ V x hx).hom (h j)
  rw [map_mul, map_mul] at this
  exact hu.mul_right_cancel this

/- English proof (translation)
Establish `hu : ∀ j, IsUnit (resG X (X.basicOpen_le (a j)) (a j))` using `fun j => isUnit_res _ _ le_rfl`. Establish `hq : ∀ j, ∃ q : Γ(X, X.basicOpen (a j)), resG X (X.basicOpen_le (a j)) (b j) = q * resG X (X.basicOpen_le (a j)) (a j)` using `fun j => ⟨resG X (X.basicOpen_le (a j)) (b j) * ↑(hu j).unit⁻¹, by`. Rewrite using `[_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩`. Use `choose q hq using hq`. Establish `hcov : V ≤ ⨆ j, X.basicOpen (a j)` using `fun x hx => TopologicalSpace.Opens.mem_iSup.2 (ha x hx)`.

Establish `hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun j => X.basicOpen (a j)) q`. Introduce `i j`. Express the relevant statement in the definitionally equal form `resG X (inf_le_left : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _) (q i) = resG X (inf_le_right : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _) (q j)`. Establish `hV : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ V` using `inf_le_left.trans (X.basicOpen_le _)`. Establish `e1` using `congrArg (resG X (inf_le_left : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _)) (hq i)`.

Establish `e2` using `congrArg (resG X (inf_le_right : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _)) (hq j)`. Establish `e3` using `congrArg (resG X hV) (hab i j)`. Rewrite `e1`, `e2` using `[map_mul, rr, rr]`. Rewrite `e3` using `[map_mul, map_mul, e1, e2]`. Establish `u` using `(isUnit_res hV (a i) inf_le_left).mul (isUnit_res hV (a j) inf_le_right)`.

Apply `u.mul_right_cancel` to reduce the goal to its premises. Take the linear combination `e3`. Take `⟨r, hr'⟩ : ∃ r : Γ(X, V), ∀ j, resG X (X.basicOpen_le (a j)) r = q j` from `(X.sheaf.existsUnique_gluing' (fun j => X.basicOpen (a j)) V (fun j => homOfLE (X.basicOpen_le _)) hcov q hcomp).exists`. Establish `key : ∀ j, b j = r * a j`. Introduce `j`.

Use `X.sheaf.eq_of_locally_eq' (fun j => X.basicOpen (a j)) V (fun j => homOfLE (X.basicOpen_le _)) hcov _ _ fun k => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `resG X (X.basicOpen_le (a k)) _ = resG X (X.basicOpen_le (a k)) _`. Apply `(hu k).mul_right_cancel` to reduce the goal to its premises. Rewrite using `[← map_mul, hab j k, map_mul, map_mul, hr', hq k]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hunit : IsUnit r`. Use `RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x hx => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `ha x hx`. Use `hb j hj` as an intermediate fact. Rewrite `this` using `[key j, Scheme.basicOpen_mul]`.

Conclude with `(Scheme.mem_basicOpen X r x hx).1 this.1`. Conclude with `⟨hunit.unit, key⟩`.
-/
theorem exists_unit {V : X.Opens} {J : Type} (a b : J → Γ(X, V))
    (ha : ∀ x ∈ V, ∃ j, x ∈ X.basicOpen (a j)) (hb : ∀ j, X.basicOpen (a j) ≤ X.basicOpen (b j))
    (hab : ∀ j k, b j * a k = b k * a j) : ∃ w : Γ(X, V)ˣ, ∀ j, b j = w.val * a j := by
  have hu : ∀ j, IsUnit (resG X (X.basicOpen_le (a j)) (a j)) := fun j => isUnit_res _ _ le_rfl
  have hq : ∀ j, ∃ q : Γ(X, X.basicOpen (a j)), resG X (X.basicOpen_le (a j)) (b j) =
      q * resG X (X.basicOpen_le (a j)) (a j) := fun j =>
    ⟨resG X (X.basicOpen_le (a j)) (b j) * ↑(hu j).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcov : V ≤ ⨆ j, X.basicOpen (a j) := fun x hx => TopologicalSpace.Opens.mem_iSup.2 (ha x hx)
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun j => X.basicOpen (a j)) q := by
    intro i j
    change resG X (inf_le_left : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _) (q i) =
      resG X (inf_le_right : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _) (q j)
    have hV : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ V := inf_le_left.trans (X.basicOpen_le _)
    have e1 := congrArg (resG X (inf_le_left : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : X.basicOpen (a i) ⊓ X.basicOpen (a j) ≤ _)) (hq j)
    have e3 := congrArg (resG X hV) (hab i j)
    rw [map_mul, rr, rr] at e1 e2
    rw [map_mul, map_mul, e1, e2] at e3
    have u := (isUnit_res hV (a i) inf_le_left).mul (isUnit_res hV (a j) inf_le_right)
    apply u.mul_right_cancel
    linear_combination e3
  obtain ⟨r, hr'⟩ : ∃ r : Γ(X, V), ∀ j, resG X (X.basicOpen_le (a j)) r = q j :=
    (X.sheaf.existsUnique_gluing' (fun j => X.basicOpen (a j)) V
      (fun j => homOfLE (X.basicOpen_le _)) hcov q hcomp).exists
  have key : ∀ j, b j = r * a j := by
    intro j
    refine X.sheaf.eq_of_locally_eq' (fun j => X.basicOpen (a j)) V
      (fun j => homOfLE (X.basicOpen_le _)) hcov _ _ fun k => ?_
    change resG X (X.basicOpen_le (a k)) _ = resG X (X.basicOpen_le (a k)) _
    apply (hu k).mul_right_cancel
    rw [← map_mul, hab j k, map_mul, map_mul, hr', hq k]
    ring
  have hunit : IsUnit r := by
    refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x hx => ?_
    obtain ⟨j, hj⟩ := ha x hx
    have := hb j hj
    rw [key j, Scheme.basicOpen_mul] at this
    exact (Scheme.mem_basicOpen X r x hx).1 this.1
  exact ⟨hunit.unit, key⟩

/- English proof (translation)
Use `⟨X.residueField x, inferInstance, X.fromSpecResidueField x, fun U => ?_⟩` and prove the remaining obligations. Establish `e` using `Scheme.fromSpecResidueField_apply x`. Prove the components needed by the constructor for the conclusion. Introduce `hU`. Use `hU (Set.mem_univ (IsLocalRing.closedPoint (X.residueField x)))` as an intermediate fact.

Conclude with `e _ ▸ this`. Introduce `hx y _`. Conclude with `(congrArg (· ∈ U) (e y)).mpr hx`.
-/
theorem exists_pt (x : X) :
    ∃ (K : Type) (_ : Field K) (p : Sp K ⟶ X), ∀ U : X.Opens, ⊤ ≤ p ⁻¹ᵁ U ↔ x ∈ U := by
  refine ⟨X.residueField x, inferInstance, X.fromSpecResidueField x, fun U => ?_⟩
  have e := Scheme.fromSpecResidueField_apply x
  constructor
  · intro hU
    have := hU (Set.mem_univ (IsLocalRing.closedPoint (X.residueField x)))
    exact e _ ▸ this
  · intro hx y _
    exact (congrArg (· ∈ U) (e y)).mpr hx

/- English proof (translation)
Establish `hu` using `SecRatio.isUnit_res t l (V := nonzeroLocus t ⊓ H.U l) inf_le_left inf_le_right`. Establish `: x ∈ X.basicOpen (resG X (inf_le_right : nonzeroLocus t ⊓ H.U l ≤ _) (t.f l))`. Rewrite using `[Scheme.basicOpen_of_isUnit _ hu]`. Conclude with `⟨hx, hl⟩`. Conclude with `((mem_res _ _ _).1 this).2`.
-/
theorem mem_chart {H : LB X} (t : H.Sec) (l : H.ι) {x : X} (hx : x ∈ nonzeroLocus t) (hl : x ∈ H.U l) :
    x ∈ X.basicOpen (t.f l) := by
  have hu := SecRatio.isUnit_res t l (V := nonzeroLocus t ⊓ H.U l) inf_le_left inf_le_right
  have : x ∈ X.basicOpen (resG X (inf_le_right : nonzeroLocus t ⊓ H.U l ≤ _) (t.f l)) := by
    rw [Scheme.basicOpen_of_isUnit _ hu]; exact ⟨hx, hl⟩
  exact ((mem_res _ _ _).1 this).2

variable {H H' : LB X} {J : Type} {s : J → H.Sec} {s' : J → H'.Sec}

/- English proof (translation)
Establish `h1 : Crd H s x (fun j => valR x _ ((s j).f i))` using `⟨i, 1, hi, fun j => by simp⟩`. Establish `h2 : Crd H' s' x (fun j => valR x _ ((s' j).f i'))` using `⟨i', 1, hi', fun j => by simp⟩`. Conclude with `CrdCalc.crd_unique (h K x _ h1) h2`.
-/
theorem val_prop (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v)
    {K : Type} [Field K] (x : Sp K ⟶ X) (i : H.ι) (i' : H'.ι) (hi : ⊤ ≤ x ⁻¹ᵁ H.U i)
    (hi' : ⊤ ≤ x ⁻¹ᵁ H'.U i') :
    ∃ c : Kˣ, ∀ j, valR x _ ((s' j).f i') = c * valR x _ ((s j).f i) := by
  have h1 : Crd H s x (fun j => valR x _ ((s j).f i)) := ⟨i, 1, hi, fun j => by simp⟩
  have h2 : Crd H' s' x (fun j => valR x _ ((s' j).f i')) := ⟨i', 1, hi', fun j => by simp⟩
  exact CrdCalc.crd_unique (h K x _ h1) h2

/- English proof (translation)
Establish `hv : ∀ x ∈ H'.U i' ⊓ H.U i, ∃ (K : Type) (_ : Field K) (φ : Γ(X, H'.U i' ⊓ H.U i) →+* K) (c : Kˣ), (∀ j, φ (resG X inf_le_left ((s' j).f i')) = c * φ (resG X inf_le_right ((s j).f i))) ∧ ∀ f, IsUnit (φ f) ↔ x ∈ X.basicOpen f`. Introduce `x hx`. Take `⟨K, _, p, hp⟩` from `exists_pt x`. Take `⟨c, hc⟩` from `val_prop h p i i' ((hp _).2 hx.2) ((hp _).2 hx.1)`. Use `⟨K, inferInstance, CrdCalc.valHom p _ ((hp _).2 hx), c, fun j => ?_, fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res _ _ ((hp _).2 hx), CrdCalc.valR_res _ _ ((hp _).2 hx), hc]`. Rewrite using `[← CrdCalc.valR_eq, CrdCalc.isUnit_valR_iff _ _ ((hp _).2 hx), hp]`. Apply `exists_unit` to reduce the goal to its premises. Introduce `x hx`. Establish `: x ∈ ⨆ j, nonzeroLocus (s j)` using `by rw [hs]; trivial`.

Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 this`. Conclude with `⟨j, (mem_res _ _ _).2 ⟨hx, mem_chart _ _ hj hx.2⟩⟩`. Introduce `j x hx`. Establish `hx'` using `X.basicOpen_le _ hx`. Take `⟨K, _, φ, c, hc, hunit⟩` from `hv x hx'`.

Rewrite using `[← hunit, hc, Units.isUnit_units_mul, hunit]`. Conclude with `hx`. Introduce `j k`. Rewrite using `[← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]`. Introduce `x hx`.

Establish `hx'` using `X.basicOpen_le _ hx`. Take `⟨K, _, φ, c, hc, hunit⟩` from `hv x hx'`. Use `(hunit _).2 hx` as an intermediate fact. Rewrite `this` using `[map_sub, map_mul, map_mul, hc, hc]`. Conclude with `(this.ne_zero (by ring)).elim`.
-/
theorem exists_chart_unit [IsReduced X] (hs : ⨆ j, nonzeroLocus (s j) = ⊤)
    (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v)
    (i : H.ι) (i' : H'.ι) : ∃ w : Γ(X, H'.U i' ⊓ H.U i)ˣ, ∀ j,
      resG X inf_le_left ((s' j).f i') = w.val * resG X inf_le_right ((s j).f i) := by
  have hv : ∀ x ∈ H'.U i' ⊓ H.U i, ∃ (K : Type) (_ : Field K) (φ : Γ(X, H'.U i' ⊓ H.U i) →+* K) (c : Kˣ),
      (∀ j, φ (resG X inf_le_left ((s' j).f i')) = c * φ (resG X inf_le_right ((s j).f i))) ∧
      ∀ f, IsUnit (φ f) ↔ x ∈ X.basicOpen f := by
    intro x hx
    obtain ⟨K, _, p, hp⟩ := exists_pt x
    obtain ⟨c, hc⟩ := val_prop h p i i' ((hp _).2 hx.2) ((hp _).2 hx.1)
    refine ⟨K, inferInstance, CrdCalc.valHom p _ ((hp _).2 hx), c, fun j => ?_, fun f => ?_⟩
    · rw [← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res _ _ ((hp _).2 hx),
        CrdCalc.valR_res _ _ ((hp _).2 hx), hc]
    · rw [← CrdCalc.valR_eq, CrdCalc.isUnit_valR_iff _ _ ((hp _).2 hx), hp]
  apply exists_unit
  · intro x hx
    have : x ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact ⟨j, (mem_res _ _ _).2 ⟨hx, mem_chart _ _ hj hx.2⟩⟩
  · intro j x hx
    have hx' := X.basicOpen_le _ hx
    obtain ⟨K, _, φ, c, hc, hunit⟩ := hv x hx'
    rw [← hunit, hc, Units.isUnit_units_mul, hunit]
    exact hx
  · intro j k
    rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' := X.basicOpen_le _ hx
    obtain ⟨K, _, φ, c, hc, hunit⟩ := hv x hx'
    have := (hunit _).2 hx
    rw [map_sub, map_mul, map_mul, hc, hc] at this
    exact (this.ne_zero (by ring)).elim

/- English proof (translation)
Introduce `X _ H H' J s s' _ _ hs h`. Use `choose w hw using exists_chart_unit hs h`. Use `⟨⟨fun p => w p.2 p.1⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨i', i⟩ ⟨k', k⟩`. Apply `Units.ext` to reduce the goal to its premises.

Establish `hi' : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H'.U i'` using `inf_le_left.trans inf_le_left`. Establish `hi : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H.U i` using `inf_le_left.trans inf_le_right`. Establish `hk' : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H'.U k'` using `inf_le_right.trans inf_le_left`. Establish `hk : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H.U k` using `inf_le_right.trans inf_le_right`. Use `cancel (V := H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k)) (fun j => resG X hi ((s j).f i)) ?_ fun j => ?_` and prove the remaining obligations.

Introduce `x hx`. Establish `: x ∈ ⨆ j, nonzeroLocus (s j)` using `by rw [hs]; trivial`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 this`. Conclude with `⟨j, (mem_res _ _ _).2 ⟨hx, mem_chart _ _ hj (hi hx)⟩⟩`. Establish `e1` using `congrArg (resG X (inf_le_left : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _)) (hw i i' j)`.

Establish `e2` using `congrArg (resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _)) (hw k k' j)`. Rewrite `e1`, `e2` using `[map_mul, rr, rr]`. Establish `e3` using `SecRatio.compat_res (s j) i k hi hk`. Establish `e4` using `SecRatio.compat_res (s' j) i' k' hi' hk'`. Establish `e5 : ((res (le_inf hi hk) (H.g i k))⁻¹).val * resG X (le_inf hi hk) (H.g i k).val = 1` using `Units.inv_mul _`.

Express the relevant statement in the definitionally equal form `resG X (inf_le_left : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w i i').val * resG X hi ((s j).f i) = resG X (le_inf hi' hk') (H'.g i' k').val * ((res (le_inf hi hk) (H.g i k))⁻¹).val * resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w k k').val * resG X hi ((s j …`. Rewrite using `[← e1, e4, e2, e3]`. Take the linear combination `(-(resG X (le_inf hi' hk') (H'.g i' k').val * resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w k k').val * resG X hk ((s j).f k))) * e5`. Introduce `j x i i' hi hi'`. Establish `hx : (𝟙 X : X ⟶ X) x ∈ H'.U i' ⊓ H.U i` using `⟨hi', hi⟩`.

Establish `e` using `congrArg (gs (𝟙 X) x (H'.U i' ⊓ H.U i)) (hw i i' j)`. Rewrite `e` using `[gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx]`. Conclude with `e`.
-/
theorem exists_iso_of_crd : ∀ (X : Scheme.{0}) [IsIntegral X] (H H' : LB X) (J : Type) (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → (∀ (K : Type) [Field K] (x : Sp K ⟶ X) (v : J → K), Crd H s x v → Crd H' s' x v) → ∃ w : LB.Iso H H', w.IsGen ∧ ∀ j (x : X) (i : H.ι) (i' : H'.ι), x ∈ H.U i → x ∈ H'.U i' → gs (𝟙 X) x _ ((s' j).f i') = gs (𝟙 X) x _ (w.s (i', i)).val * gs (𝟙 X) x _ ((s j).f i) := by
  intro X _ H H' J s s' _ _ hs h
  choose w hw using exists_chart_unit hs h
  refine ⟨⟨fun p => w p.2 p.1⟩, ?_, ?_⟩
  · rintro ⟨i', i⟩ ⟨k', k⟩
    apply Units.ext
    have hi' : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H'.U i' := inf_le_left.trans inf_le_left
    have hi : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H.U i := inf_le_left.trans inf_le_right
    have hk' : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H'.U k' := inf_le_right.trans inf_le_left
    have hk : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ H.U k := inf_le_right.trans inf_le_right
    refine cancel (V := H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k)) (fun j => resG X hi ((s j).f i)) ?_ fun j => ?_
    · intro x hx
      have : x ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
      exact ⟨j, (mem_res _ _ _).2 ⟨hx, mem_chart _ _ hj (hi hx)⟩⟩
    · have e1 := congrArg (resG X (inf_le_left : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _)) (hw i i' j)
      have e2 := congrArg (resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _)) (hw k k' j)
      rw [map_mul, rr, rr] at e1 e2
      have e3 := SecRatio.compat_res (s j) i k hi hk
      have e4 := SecRatio.compat_res (s' j) i' k' hi' hk'
      have e5 : ((res (le_inf hi hk) (H.g i k))⁻¹).val * resG X (le_inf hi hk) (H.g i k).val = 1 :=
        Units.inv_mul _
      change resG X (inf_le_left : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w i i').val *
          resG X hi ((s j).f i) =
        resG X (le_inf hi' hk') (H'.g i' k').val * ((res (le_inf hi hk) (H.g i k))⁻¹).val *
          resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w k k').val * resG X hi ((s j).f i)
      rw [← e1, e4, e2, e3]
      linear_combination (-(resG X (le_inf hi' hk') (H'.g i' k').val *
        resG X (inf_le_right : H'.U i' ⊓ H.U i ⊓ (H'.U k' ⊓ H.U k) ≤ _) (w k k').val *
        resG X hk ((s j).f k))) * e5
  · intro j x i i' hi hi'
    have hx : (𝟙 X : X ⟶ X) x ∈ H'.U i' ⊓ H.U i := ⟨hi', hi⟩
    have e := congrArg (gs (𝟙 X) x (H'.U i' ⊓ H.U i)) (hw i i' j)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx] at e
    exact e

end GlobalTheory.ZH.CrdIso
end
