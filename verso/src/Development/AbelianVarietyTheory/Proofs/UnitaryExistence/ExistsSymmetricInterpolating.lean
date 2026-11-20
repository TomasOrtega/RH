import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemNonzeroLocusIffMemBasicOpenChart
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusProdSec

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.PointInterp

variable {k : Type} [Field k] {X Y : Scheme.{0}}

def valueAt (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp (p.appLE U ⊤ h).hom

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h (show z ∈ (⊤ : (Spec (CommRingCat.of k)).Opens) from trivial), fun h y _ => by obtain rfl : y = z := Subsingleton.elim (α := PrimeSpectrum k) _ _ exact h⟩`.
-/
theorem top_le_iff (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (z : Spec (CommRingCat.of k)) :
    ⊤ ≤ p ⁻¹ᵁ U ↔ p z ∈ U :=
  ⟨fun h => h (show z ∈ (⊤ : (Spec (CommRingCat.of k)).Opens) from trivial), fun h y _ => by
    obtain rfl : y = z := Subsingleton.elim (α := PrimeSpectrum k) _ _
    exact h⟩

/- English proof (translation)
The claim follows from `congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (BoxSection.appLE_res p hle h h' a)`.
-/
theorem valueAt_rs (p : Spec (CommRingCat.of k) ⟶ X) {U V : X.Opens} (hle : V ≤ U) (h : ⊤ ≤ p ⁻¹ᵁ V)
    (h' : ⊤ ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) : valueAt p V h (rs X hle a) = valueAt p U h' a :=
  congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (BoxSection.appLE_res p hle h h' a)

/- English proof (translation)
Use `(valueAt_rs p le_top h le_top _).trans ?_` and prove the remaining obligations. Establish `e : p.appLE ⊤ ⊤ le_top = p.appTop` using `Scheme.Hom.appLE_eq_app p`. Establish `e' : f.appTop ≫ p.appTop = 𝟙 _` using `by rw [← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]`. Express the relevant statement in the definitionally equal form `((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (f.appTop ≫ p.appLE ⊤ ⊤ le_top) ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c = c`. Rewrite using `[e, e', Category.id_comp, Iso.inv_hom_id]`.

Both sides reduce to the same expression.
-/
theorem valueAt_cst (f : X ⟶ Spec (CommRingCat.of k)) (p : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (c : k) : valueAt p U h (cst f U c) = c := by
  refine (valueAt_rs p le_top h le_top _).trans ?_
  have e : p.appLE ⊤ ⊤ le_top = p.appTop := Scheme.Hom.appLE_eq_app p
  have e' : f.appTop ≫ p.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (f.appTop ≫ p.appLE ⊤ ⊤ le_top) ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c = c
  rw [e, e', Category.id_comp, Iso.inv_hom_id]
  rfl

/- English proof (translation)
Establish `hb` using `Scheme.basicOpen_appLE p ⊤ U h a`. Rewrite `hb` using `[top_inf_eq]`. Rewrite using `[← hb, ← isUnit_iff_ne_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `hu`.

Establish `hu'` using `hu.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom`. Establish `: (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (valueAt p U h a) = (p.appLE U ⊤ h).hom a` using `(Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply _`. Rewrite `hu'` using `[this]`. Conclude with `(Scheme.basicOpen_of_isUnit _ hu').ge`. Introduce `hu`.

Use `IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ?_` and prove the remaining obligations. Conclude with `(Spec (CommRingCat.of k)).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => (Scheme.mem_basicOpen _ _ y hy).1 (hu hy)`.
-/
theorem valueAt_ne_zero_iff (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    valueAt p U h a ≠ 0 ↔ ⊤ ≤ p ⁻¹ᵁ X.basicOpen a := by
  have hb := Scheme.basicOpen_appLE p ⊤ U h a
  rw [top_inf_eq] at hb
  rw [← hb, ← isUnit_iff_ne_zero]
  constructor
  · intro hu
    have hu' := hu.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    have : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (valueAt p U h a) = (p.appLE U ⊤ h).hom a :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply _
    rw [this] at hu'
    exact (Scheme.basicOpen_of_isUnit _ hu').ge
  · intro hu
    refine IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ?_
    exact (Spec (CommRingCat.of k)).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
      (Scheme.mem_basicOpen _ _ y hy).1 (hu hy)

/- English proof (translation)
Establish `e : p.appLE U ⊤ hp = q.appLE U ⊤ hq`. Rewrite using `[← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of k)).hom]`. Conclude with `CommRingCat.hom_ext h`. Establish `hV` using `isAffineOpen_top (Spec (CommRingCat.of k))`. Establish `: IsIso hV.fromSpec` using `by rw [IsAffineOpen.fromSpec_top]; infer_instance`.

Rewrite using `[← cancel_epi hV.fromSpec, ← hU.SpecMap_appLE_fromSpec p hV hp, ← hU.SpecMap_appLE_fromSpec q hV hq, e]`.
-/
theorem eq_of_valueAt_eq (p q : Spec (CommRingCat.of k) ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (hp : ⊤ ≤ p ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) (h : valueAt p U hp = valueAt q U hq) : p = q := by
  have e : p.appLE U ⊤ hp = q.appLE U ⊤ hq := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of k)).hom]
    exact CommRingCat.hom_ext h
  have hV := isAffineOpen_top (Spec (CommRingCat.of k))
  have : IsIso hV.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi hV.fromSpec, ← hU.SpecMap_appLE_fromSpec p hV hp, ← hU.SpecMap_appLE_fromSpec q hV hq, e]

def subMulSec (f : X ⟶ Spec (CommRingCat.of k)) {H : LB X} (s t : LB.Sec H) (c : k) : LB.Sec H where
  f j := s.f j - cst f _ c * t.f j
  compat i j := by
    rw [map_sub, map_sub, map_mul, map_mul, s.compat i j, t.compat i j]
    have e₁ := rs_cst f (inf_le_left : H.U i ⊓ H.U j ≤ H.U i) c
    have e₂ := rs_cst f (inf_le_right : H.U i ⊓ H.U j ≤ H.U j) c
    rw [e₁, e₂]
    ring

/- English proof (translation)
Set `z : Spec (CommRingCat.of k)` to `(default : PrimeSpectrum k)`. Rewrite using `[valueAt_ne_zero_iff, top_le_iff _ _ z, top_le_iff _ _ z]`. Conclude with `mem_nonzeroLocus_iff_mem_basicOpen_chart s l ((top_le_iff _ _ z).1 hl)`.
-/
theorem top_le_nonzeroLocus_iff {H : LB X} (s : LB.Sec H) (p : Spec (CommRingCat.of k) ⟶ X) (l : H.ι)
    (hl : ⊤ ≤ p ⁻¹ᵁ H.U l) : ⊤ ≤ p ⁻¹ᵁ nonzeroLocus s ↔ valueAt p _ hl (s.f l) ≠ 0 := by
  let z : Spec (CommRingCat.of k) := (default : PrimeSpectrum k)
  rw [valueAt_ne_zero_iff, top_le_iff _ _ z, top_le_iff _ _ z]
  exact mem_nonzeroLocus_iff_mem_basicOpen_chart s l ((top_le_iff _ _ z).1 hl)

/- English proof (translation)
Set `z : Spec (CommRingCat.of k)` to `(default : PrimeSpectrum k)`. Take `⟨a, ha⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show p z ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)`. Establish `hpa` using `(top_le_iff p _ z).2 ha`. Distinguish the cases in `hqa : ⊤ ≤ q ⁻¹ᵁ nonzeroLocus (s a)`. Use `swap`.

Conclude with `⟨s a, hpa, hqa⟩`. Take `⟨haff, r, hr, hsurj⟩` from `hs.2 a`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, valueAt p _ hpa (r b) ≠ valueAt q _ hqa (r b) := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Use `hne (eq_of_valueAt_eq p q haff hpa hqa (RingHom.ext fun x => ?_))` and prove the remaining obligations. Take `⟨F, rfl⟩` from `hsurj x`. Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C c => rw [MvPolynomial.eval₂Hom_C, valueAt_cst f p hp, valueAt_cst f q hq]`. Consider the case `add F G hF hG => rw [map_add, map_add, map_add, hF, hG]`.

Consider the case `mul_X F j hF => rw [map_mul, MvPolynomial.eval₂Hom_X', map_mul, map_mul, hF, hc]`. Establish `key : ∀ (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hxa : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (s a)) (c : k), ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (subMulSec f (s b) (s a) c) ↔ valueAt x _ hxa (r b) ≠ c`. Introduce `x hx hxa c`. Take `⟨l, hl⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show x z ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)`. Establish `hxl` using `(top_le_iff x _ z).2 hl`.

Establish `hm : ⊤ ≤ x ⁻¹ᵁ (nonzeroLocus (s a) ⊓ H.U l)` using `le_inf hxa hxl`. Establish `e` using `congrArg (valueAt x _ hm) (hr b l)`. Rewrite `e` using `[map_mul, valueAt_rs x _ hm hxl, valueAt_rs x _ hm hxl, valueAt_rs x _ hm hxa]`. Establish `h0` using `(top_le_nonzeroLocus_iff (s a) x l hxl).1 hxa`. Rewrite using `[top_le_nonzeroLocus_iff _ x l hxl]`.

Express the relevant statement in the definitionally equal form `valueAt x _ hxl ((s b).f l - cst f _ c * (s a).f l) ≠ 0 ↔ _`. Rewrite using `[map_sub, map_mul, valueAt_cst f x hx, e, ← sub_mul, mul_ne_zero_iff, sub_ne_zero]`. Conclude with `and_iff_left h0`. Conclude with `⟨subMulSec f (s b) (s a) (valueAt q _ hqa (r b)), (key p hp hpa _).2 hb, fun h => (key q hq hqa _).1 h rfl⟩`.
-/
theorem exists_separating (f : X ⟶ Spec (CommRingCat.of k)) {H : LB X} (hH : H.IsLB) {n : ℕ}
    {s : Fin (n + 1) → LB.Sec H} (hs : VeryAmpleBy f H s) (p q : Spec (CommRingCat.of k) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _) (hne : p ≠ q) :
    ∃ σ : LB.Sec H, ⊤ ≤ p ⁻¹ᵁ nonzeroLocus σ ∧ ¬ ⊤ ≤ q ⁻¹ᵁ nonzeroLocus σ := by
  let z : Spec (CommRingCat.of k) := (default : PrimeSpectrum k)
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show p z ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
  have hpa := (top_le_iff p _ z).2 ha
  by_cases hqa : ⊤ ≤ q ⁻¹ᵁ nonzeroLocus (s a)
  swap
  · exact ⟨s a, hpa, hqa⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs.2 a
  obtain ⟨b, hb⟩ : ∃ b, valueAt p _ hpa (r b) ≠ valueAt q _ hqa (r b) := by
    by_contra hc
    push_neg at hc
    refine hne (eq_of_valueAt_eq p q haff hpa hqa (RingHom.ext fun x => ?_))
    obtain ⟨F, rfl⟩ := hsurj x
    induction F using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.eval₂Hom_C, valueAt_cst f p hp, valueAt_cst f q hq]
    | add F G hF hG => rw [map_add, map_add, map_add, hF, hG]
    | mul_X F j hF => rw [map_mul, MvPolynomial.eval₂Hom_X', map_mul, map_mul, hF, hc]
  have key : ∀ (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hxa : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (s a)) (c : k),
      ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (subMulSec f (s b) (s a) c) ↔ valueAt x _ hxa (r b) ≠ c := by
    intro x hx hxa c
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show x z ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)
    have hxl := (top_le_iff x _ z).2 hl
    have hm : ⊤ ≤ x ⁻¹ᵁ (nonzeroLocus (s a) ⊓ H.U l) := le_inf hxa hxl
    have e := congrArg (valueAt x _ hm) (hr b l)
    rw [map_mul, valueAt_rs x _ hm hxl, valueAt_rs x _ hm hxl, valueAt_rs x _ hm hxa] at e
    have h0 := (top_le_nonzeroLocus_iff (s a) x l hxl).1 hxa
    rw [top_le_nonzeroLocus_iff _ x l hxl]
    change valueAt x _ hxl ((s b).f l - cst f _ c * (s a).f l) ≠ 0 ↔ _
    rw [map_sub, map_mul, valueAt_cst f x hx, e, ← sub_mul, mul_ne_zero_iff, sub_ne_zero]
    exact and_iff_left h0
  exact ⟨subMulSec f (s b) (s a) (valueAt q _ hqa (r b)), (key p hp hpa _).2 hb,
    fun h => (key q hq hqa _).1 h rfl⟩

/- English proof (translation)
Take `⟨l, hl⟩` from `TopologicalSpace.Opens.mem_iSup.1 h`. Establish `hy : y ∈ LB.wchart L φ l` using `Y.basicOpen_le _ hl`. Establish `h₁` using `(mem_basicOpen_finset_prod_iff _ Finset.univ hy).1 hl i (Finset.mem_univ i)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨l i, ((Scheme.basicOpen_appLE (φ i) _ _ (LB.wchart_le L φ l i) _).le h₁).2⟩`.
-/
theorem mem_nonzeroLocus_of_prodSec (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (t : K → L.Sec)
    (y : Y) (h : y ∈ nonzeroLocus (BoxSection.prodSec L φ t)) (i : K) : φ i y ∈ nonzeroLocus (t i) := by
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hy : y ∈ LB.wchart L φ l := Y.basicOpen_le _ hl
  have h₁ := (mem_basicOpen_finset_prod_iff _ Finset.univ hy).1 hl i (Finset.mem_univ i)
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨l i, ((Scheme.basicOpen_appLE (φ i) _ _ (LB.wchart_le L φ l i) _).le h₁).2⟩

/- English proof (translation)
Introduce `k _ _ A _ _ ⟨H, hH, n, s, hs⟩`. Set `φ : Fin 2 → (A.left ⟶ A.left)` to `![𝟙 A.left, (GrpObj.inv : A ⟶ A).left]`. Establish `hL : (LB.LinComb H φ (fun _ => 1)).IsLB` using `LB.isLB_linComb hH _ _`. Use `⟨LB.LinComb H φ (fun _ => 1), hL, ?_, fun r p hp m hm => ?_⟩` and prove the remaining obligations. Use `PrimNorm.hasGen_nested hH φ _ _ _ ?_` and prove the remaining obligations.

Establish `e : (GrpObj.inv : A ⟶ A).left ≫ (GrpObj.inv : A ⟶ A).left = 𝟙 A.left`. Rewrite using `[← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left]`. Simplify using `only [Fin.prod_univ_two, φ, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e, Category.id_comp, zpow_one, zpow_neg]`. Rewrite using `[mul_comm (PrimNorm.cls H (𝟙 A.left)), mul_inv_cancel]`. Set `z : Spec (CommRingCat.of k)` to `(default : PrimeSpectrum k)`.

Set `P : Fin r → (Spec (CommRingCat.of k) ⟶ A.left)` to `fun i => (p i).left`. Establish `hP : ∀ i, P i ≫ A.hom = 𝟙 _` using `fun i => Over.w (p i)`. Establish `hcov : ∀ x : A.left, ∃ σ : LB.Sec H, x ∈ nonzeroLocus σ` using `fun x => by`. Take `⟨a, ha⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)`. Conclude with `⟨s a, ha⟩`.

Establish `hsep : ∀ (i : Fin r) (t : Fin m), ∃ σ : LB.Sec H, P i z ∈ nonzeroLocus σ ∧ ∀ j : Fin r, (j : ℕ) = t → i ≠ j → P j z ∉ nonzeroLocus σ` using `fun i t => by`. Distinguish the cases in `h : ∃ j : Fin r, (j : ℕ) = t ∧ i ≠ j`. Take `⟨j, hj, hij⟩` from `h`. Take `⟨σ, h₁, h₂⟩` from `exists_separating A.hom hH hs (P i) (P j) (hP i) (hP j) fun e => hij (hp (Over.OverMorphism.ext e))`. Use `⟨σ, (top_le_iff _ _ z).1 h₁, fun j' hj' _ h => ?_⟩` and prove the remaining obligations.

Take `rfl : j' = j` from `Fin.ext (hj'.trans hj.symm)`. Conclude with `h₂ ((top_le_iff _ _ z).2 h)`. Take `⟨σ, hσ⟩` from `hcov (P i z)`. Conclude with `⟨σ, hσ, fun j hj hij _ => h ⟨j, hj, hij⟩⟩`. Use `choose σ hσ hσ' using hsep`.

Use `choose τ hτ using fun i => hcov (φ 1 (P i z))`. Establish `hprod : ∀ i : Fin r, ∃ u : LB.Sec (pw (LB.LinComb H φ (fun _ => 1)) m), nonzeroLocus u = ⨅ t ∈ (Finset.univ : Finset (Fin m)), nonzeroLocus (BoxSection.prodSec H φ ![σ i t, τ i])` using `fun i => by`. Establish `h` using `exists_prod_sec_nonzeroLocus _ _ _ (fun t => BoxSection.prodSec H φ ![σ i t, τ i]) (Finset.univ : Finset (Fin m)) hL`. Take `⟨u, -, hu⟩` from `h`. Establish `hc : ((Finset.univ : Finset (Fin m)).card : ℤ) = (m : ℤ)` using `by simp`.

Use `revert u`. Rewrite using `[hc]`. Conclude with `fun u hu => ⟨u, hu⟩`. Use `choose u hu using hprod`. Use `⟨u, fun i j => ?_⟩` and prove the remaining obligations.

Use `(top_le_iff (P j) _ z).trans ?_` and prove the remaining obligations. Rewrite using `[hu, mem_finset_biInf_opens_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hij`.

Conclude with `hσ' i ⟨j, j.2.trans_le hm⟩ j rfl hij (mem_nonzeroLocus_of_prodSec H φ _ _ (h ⟨j, j.2.trans_le hm⟩ (Finset.mem_univ _)) 0)`. Introduce and unpack `rfl t -`. Use `BoxSection.mem_nonzeroLocus_prodSec H φ _ _ fun l => ?_` and prove the remaining obligations. Use `fin_cases l`. Use `exacts [hσ i t, hτ i]`.
-/
theorem exists_symmetric_interpolating : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → IsProjBy A.hom → ∃ L : LB A.left, L.IsLB ∧ Triv (LB.LinComb L (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]) ∧ ∀ (r : ℕ) (p : Fin r → (𝟙_ (Over (Sp k)) ⟶ A)), Function.Injective p → ∀ m : ℕ, r ≤ m → ∃ s : Fin r → LB.Sec (pw L m), ∀ i j, (⊤ ≤ (p j).left ⁻¹ᵁ nonzeroLocus (s i) ↔ i = j) := by
  intro k _ _ A _ _ ⟨H, hH, n, s, hs⟩
  let φ : Fin 2 → (A.left ⟶ A.left) := ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left]
  have hL : (LB.LinComb H φ (fun _ => 1)).IsLB := LB.isLB_linComb hH _ _
  refine ⟨LB.LinComb H φ (fun _ => 1), hL, ?_, fun r p hp m hm => ?_⟩
  · refine PrimNorm.hasGen_nested hH φ _ _ _ ?_
    have e : (GrpObj.inv : A ⟶ A).left ≫ (GrpObj.inv : A ⟶ A).left = 𝟙 A.left := by
      rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left]
    simp only [Fin.prod_univ_two, φ, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e,
      Category.id_comp, zpow_one, zpow_neg]
    rw [mul_comm (PrimNorm.cls H (𝟙 A.left)), mul_inv_cancel]
  · let z : Spec (CommRingCat.of k) := (default : PrimeSpectrum k)
    let P : Fin r → (Spec (CommRingCat.of k) ⟶ A.left) := fun i => (p i).left
    have hP : ∀ i, P i ≫ A.hom = 𝟙 _ := fun i => Over.w (p i)
    have hcov : ∀ x : A.left, ∃ σ : LB.Sec H, x ∈ nonzeroLocus σ := fun x => by
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1
        (show x ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
      exact ⟨s a, ha⟩

    have hsep : ∀ (i : Fin r) (t : Fin m), ∃ σ : LB.Sec H, P i z ∈ nonzeroLocus σ ∧
        ∀ j : Fin r, (j : ℕ) = t → i ≠ j → P j z ∉ nonzeroLocus σ := fun i t => by
      by_cases h : ∃ j : Fin r, (j : ℕ) = t ∧ i ≠ j
      · obtain ⟨j, hj, hij⟩ := h
        obtain ⟨σ, h₁, h₂⟩ := exists_separating A.hom hH hs (P i) (P j) (hP i) (hP j)
          fun e => hij (hp (Over.OverMorphism.ext e))
        refine ⟨σ, (top_le_iff _ _ z).1 h₁, fun j' hj' _ h => ?_⟩
        obtain rfl : j' = j := Fin.ext (hj'.trans hj.symm)
        exact h₂ ((top_le_iff _ _ z).2 h)
      · obtain ⟨σ, hσ⟩ := hcov (P i z)
        exact ⟨σ, hσ, fun j hj hij _ => h ⟨j, hj, hij⟩⟩
    choose σ hσ hσ' using hsep
    choose τ hτ using fun i => hcov (φ 1 (P i z))
    have hprod : ∀ i : Fin r, ∃ u : LB.Sec (pw (LB.LinComb H φ (fun _ => 1)) m),
        nonzeroLocus u = ⨅ t ∈ (Finset.univ : Finset (Fin m)),
          nonzeroLocus (BoxSection.prodSec H φ ![σ i t, τ i]) := fun i => by
      have h := exists_prod_sec_nonzeroLocus _ _ _ (fun t => BoxSection.prodSec H φ ![σ i t, τ i])
        (Finset.univ : Finset (Fin m)) hL
      obtain ⟨u, -, hu⟩ := h
      have hc : ((Finset.univ : Finset (Fin m)).card : ℤ) = (m : ℤ) := by simp
      revert u
      rw [hc]
      exact fun u hu => ⟨u, hu⟩
    choose u hu using hprod
    refine ⟨u, fun i j => ?_⟩
    refine (top_le_iff (P j) _ z).trans ?_
    rw [hu, mem_finset_biInf_opens_iff]
    constructor
    · intro h
      by_contra hij
      exact hσ' i ⟨j, j.2.trans_le hm⟩ j rfl hij
        (mem_nonzeroLocus_of_prodSec H φ _ _ (h ⟨j, j.2.trans_le hm⟩ (Finset.mem_univ _)) 0)
    · rintro rfl t -
      refine BoxSection.mem_nonzeroLocus_prodSec H φ _ _ fun l => ?_
      fin_cases l
      exacts [hσ i t, hτ i]

end GlobalTheory.PointInterp
