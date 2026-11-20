import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CoeffSymmSum
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FormSec
open scoped Pointwise

/- English proof (translation)
Simplify using `only [map_sum, map_mul, Finsupp.prod, map_prod, map_pow]`.
-/
theorem map_form {B B' J : Type} [CommRing B] [CommRing B'] (ψ : B →+* B') (T : Finset (J →₀ ℕ))
    (c : (J →₀ ℕ) → B) (s : J → B) :
    ψ (∑ m ∈ T, c m * m.prod (fun i n => s i ^ n)) =
      ∑ m ∈ T, ψ (c m) * m.prod (fun i n => ψ (s i) ^ n) := by
  simp only [map_sum, map_mul, Finsupp.prod, map_prod, map_pow]

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Simplify using `only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hT m hm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_scale {B J : Type} [CommRing B] (T : Finset (J →₀ ℕ)) (d : ℕ)
    (hT : ∀ m ∈ T, ∑ i ∈ m.support, m i = d) (c : (J →₀ ℕ) → B) (u : B) (s : J → B) :
    ∑ m ∈ T, c m * m.prod (fun i n => (u * s i) ^ n) =
      u ^ d * ∑ m ∈ T, c m * m.prod (fun i n => s i ^ n) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hT m hm]
  ring

section Supp
variable {A X : Type} [CommRing A] [AddCommGroup X]

/- English proof (translation)
Introduce `a ha`. Take `⟨b, hb, c, hc, rfl⟩` from `Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset x y ha)`. Conclude with `Set.add_mem_add (hx hb) (hy hc)`.
-/
theorem supp_mul {x y : AddMonoidAlgebra A X} {S S' : Set X} (hx : (x.coeff.support : Set X) ⊆ S)
    (hy : (y.coeff.support : Set X) ⊆ S') : ((x * y).coeff.support : Set X) ⊆ S + S' := by
  classical
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.1 (AddMonoidAlgebra.support_coeff_mul_subset x y ha)
  exact Set.add_mem_add (hx hb) (hy hc)

/- English proof (translation)
Introduce `a ha`. Use `AddMonoidAlgebra.support_coeff_one_subset (k := A) (G := X) ha` as an intermediate fact. Simplify using `using this`.
-/
theorem supp_one : ((1 : AddMonoidAlgebra A X).coeff.support : Set X) ⊆ 0 := by
  intro a ha
  have := AddMonoidAlgebra.support_coeff_one_subset (k := A) (G := X) ha
  simpa using this

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, zero_nsmul]`. Conclude with `supp_one`. Consider the case `succ n ih => rw [pow_succ, succ_nsmul]`. Conclude with `supp_mul ih hx`.
-/
theorem supp_pow {x : AddMonoidAlgebra A X} {S : Set X} (hx : (x.coeff.support : Set X) ⊆ S) (n : ℕ) :
    ((x ^ n).coeff.support : Set X) ⊆ n • S := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul]; exact supp_one
  | succ n ih => rw [pow_succ, succ_nsmul]; exact supp_mul ih hx

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, Finset.sum_empty, zero_nsmul]`. Conclude with `supp_one`. Consider the case `insert j t hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, add_nsmul]`.

Conclude with `supp_mul (supp_pow (hx j) _) ih`.
-/
theorem supp_prod {J : Type} {x : J → AddMonoidAlgebra A X} {S : Set X}
    (hx : ∀ i, ((x i).coeff.support : Set X) ⊆ S) (n : J → ℕ) (t : Finset J) :
    ((∏ i ∈ t, x i ^ n i).coeff.support : Set X) ⊆ (∑ i ∈ t, n i) • S := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, zero_nsmul]; exact supp_one
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, add_nsmul]
    exact supp_mul (supp_pow (hx j) _) ih

/- English proof (translation)
Set `e` to `RingEquiv.ofBijective _ hb`. Establish `h1 : ∀ x, e.symm (f x) = AddMonoidAlgebra.single 0 x` using `fun x => by`. Rewrite using `[RingEquiv.symm_apply_eq]`. Express the relevant statement in the definitionally equal form `_ = AddMonoidAlgebra.liftNCRingHom f g hc _`. Simplify using `[AddMonoidAlgebra.liftNCRingHom]`.

Express the relevant statement in the definitionally equal form `(e.symm.toRingHom _).coeff α ≠ 0 at hα`. Rewrite `hα` using `[map_form, AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]`. Take `⟨m, hm, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hα`. Establish `h2 : ((e.symm.toRingHom (f (c m))).coeff.support : Set X) ⊆ 0`. Express the relevant statement in the definitionally equal form `((e.symm (f (c m))).coeff.support : Set X) ⊆ 0`.

Rewrite using `[h1, AddMonoidAlgebra.coeff_single]`. Introduce `a ha`. Simplify using `using Finsupp.support_single_subset ha`. Establish `h3` using `supp_mul h2 (supp_prod (x := fun i => e.symm.toRingHom (s i)) (S := S) (fun i a ha => hs i a (Finsupp.mem_support_iff.1 ha)) m m.support) (Finsupp.mem_support_iff.2 hne)`. Rewrite `h3` using `[zero_add, hT m hm, Set.mem_nsmul]`.

Take `⟨β, hβ⟩` from `h3`. Conclude with `⟨fun n => β n, fun n => (β n).2, by rw [← hβ, List.sum_ofFn]⟩`.
-/
theorem supp_form {B J : Type} [CommRing B] (f : A →+* B)
    (g : Multiplicative X →* B) (hc : ∀ x y, Commute (f x) (g y))
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g hc)) (T : Finset (J →₀ ℕ)) (d : ℕ)
    (hT : ∀ m ∈ T, ∑ i ∈ m.support, m i = d) (c : (J →₀ ℕ) → A) (s : J → B) (S : Set X)
    (hs : ∀ i α, ((Equiv.ofBijective _ hb).symm (s i)).coeff α ≠ 0 → α ∈ S) (α : X)
    (hα : ((Equiv.ofBijective _ hb).symm (∑ m ∈ T, f (c m) * m.prod (fun i n => s i ^ n))).coeff α ≠ 0) :
    ∃ β : Fin d → X, (∀ n, β n ∈ S) ∧ α = ∑ n, β n := by
  let e := RingEquiv.ofBijective _ hb
  have h1 : ∀ x, e.symm (f x) = AddMonoidAlgebra.single 0 x := fun x => by
    rw [RingEquiv.symm_apply_eq]
    change _ = AddMonoidAlgebra.liftNCRingHom f g hc _
    simp [AddMonoidAlgebra.liftNCRingHom]
  change (e.symm.toRingHom _).coeff α ≠ 0 at hα
  rw [map_form, AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply] at hα
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
  have h2 : ((e.symm.toRingHom (f (c m))).coeff.support : Set X) ⊆ 0 := by
    change ((e.symm (f (c m))).coeff.support : Set X) ⊆ 0
    rw [h1, AddMonoidAlgebra.coeff_single]
    intro a ha
    simpa using Finsupp.support_single_subset ha
  have h3 := supp_mul h2 (supp_prod (x := fun i => e.symm.toRingHom (s i)) (S := S)
    (fun i a ha => hs i a (Finsupp.mem_support_iff.1 ha)) m m.support) (Finsupp.mem_support_iff.2 hne)
  rw [zero_add, hT m hm, Set.mem_nsmul] at h3
  obtain ⟨β, hβ⟩ := h3
  exact ⟨fun n => β n, fun n => (β n).2, by rw [← hβ, List.sum_ofFn]⟩

end Supp

/- English proof (translation)
The claim follows from `congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)`.
-/
theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U)
    (a : R) : resG X h (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

/- English proof (translation)
Establish `e : p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h = 𝟙 _`. Use `(Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h).trans ?_` and prove the remaining obligations. Use `generalize_proofs h₁`. Use `revert h₁`. Rewrite using `[hx]`.

Introduce `h₁`. Simplify using `only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]`. Conclude with `(Category.id_comp _).trans ((Sp R).presheaf.map_id _)`. Express the relevant statement in the definitionally equal form `((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom a = a`. Rewrite using `[e, Category.id_comp, Iso.inv_hom_id]`.

Both sides reduce to the same expression.
-/
theorem valHom_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (x : Sp R ⟶ X)
    (hx : x ≫ p = 𝟙 _) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) :
    CrdCalc.valHom x U h (constFn p U a) = a := by
  have e : p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h = 𝟙 _ := by
    refine (Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h).trans ?_
    generalize_proofs h₁
    revert h₁
    rw [hx]
    intro h₁
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    exact (Category.id_comp _).trans ((Sp R).presheaf.map_id _)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h) ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom a = a
  rw [e, Category.id_comp, Iso.inv_hom_id]
  rfl

/- English proof (translation)
Introduce `m hm` and use `by have := h (MvPolynomial.mem_support_iff.1 hm) simpa [Finsupp.weight_apply, Finsupp.sum] using this`.
-/
theorem deg_of_mem {k J : Type} [Field k] {d : ℕ} {Pf : MvPolynomial J k} (h : Pf.IsHomogeneous d) :
    ∀ m ∈ Pf.support, ∑ i ∈ m.support, m i = d := fun m hm => by
  have := h (MvPolynomial.mem_support_iff.1 hm)
  simpa [Finsupp.weight_apply, Finsupp.sum] using this

def formSec {k : Type} [Field k] (Φ : FibPre k) {J : Type} (F : J → (Φ.H 1).Sec) {d : ℕ}
    (Pf : MvPolynomial J k) (h : Pf.IsHomogeneous d) : (Φ.H d).Sec where
  f l := ∑ m ∈ Pf.support, constFn Φ.G.hom ((Φ.H d).U l) (Pf.coeff m) *
    m.prod (fun i n => (show Γ(Φ.G.left, (Φ.H d).U l) from (F i).f l) ^ n)
  compat l l' := by
    let V : Φ.G.left.Opens := (Φ.H d).U l ⊓ (Φ.H d).U l'
    let r : Γ(Φ.G.left, (Φ.H d).U l) →+* Γ(Φ.G.left, V) := resG _ inf_le_left
    let r' : Γ(Φ.G.left, (Φ.H d).U l') →+* Γ(Φ.G.left, V) := resG _ inf_le_right
    let u : Γ(Φ.G.left, V)ˣ := pullU Φ.D.q.left (Φ.N₀.U l ⊓ Φ.N₀.U l') (Φ.N₀.g l l')
    have hF : ∀ i, r ((F i).f l) = (u : Γ(Φ.G.left, V)) * r' ((F i).f l') := fun i => by
      have := (F i).compat l l'
      change r ((F i).f l) = ((u ^ 1 : Γ(Φ.G.left, V)ˣ) : Γ(Φ.G.left, V)) * r' ((F i).f l') at this
      exact this.trans (congrArg (fun w : Γ(Φ.G.left, V)ˣ => (w : Γ(Φ.G.left, V)) * r' ((F i).f l')) (pow_one u))
    change r _ = ((u ^ d : Γ(Φ.G.left, V)ˣ) : Γ(Φ.G.left, V)) * r' _
    rw [map_form, map_form, Units.val_pow_eq_pow_val, ← form_scale _ d (deg_of_mem h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [res_constFn, res_constFn]
    congr 2
    funext i n
    exact congrArg (· ^ n) (hF i)

/- English proof (translation)
Introduce `k _ Φ J F d Pf h`. Use `⟨formSec Φ F Pf h, fun _ => rfl, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `α ⟨l, hl⟩`. Use `supp_form _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) Pf.support d (deg_of_mem h) (fun m => constFn Φ.E.B.hom _ (Pf.coeff m)) (fun i => (F i).f l) {β | ∃ i, β ∈ Φ.supp (F i)} (fun i β hβ => ⟨i, l, hβ⟩) α ?_` and prove the remaining obligations. Simplify using `only [WtLin.app_constFn _ _ _ (Over.w Φ.D.q)]`.

Conclude with `hl`. Introduce and unpack `x v ⟨l, c, hl, hv⟩`. Establish `hl' : ⊤ ≤ x.left ⁻¹ᵁ (Φ.H d).U l` using `hl`. Establish `hc : Crd (Φ.H d) (fun _ : Unit => formSec Φ F Pf h) x.left (fun _ => MvPolynomial.eval v Pf)`. Use `⟨l, c ^ d, hl', fun _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[CrdCalc.valR_eq _ _ hl']`. Express the relevant statement in the definitionally equal form `_ = _ * CrdCalc.valHom x.left _ hl' (∑ m ∈ Pf.support, _)`. Rewrite using `[map_form, Units.val_pow_eq_pow_val, ← form_scale _ d (deg_of_mem h), MvPolynomial.eval_eq]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[valHom_constFn _ _ (Over.w x)]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hv i, CrdCalc.valR_eq _ _ hl]`. Both sides reduce to the same expression. Rewrite using `[← CrdCalc.crd_isUnit_iff () hc, isUnit_iff_ne_zero, not_not]`.
-/
theorem exists_formSec : (∀ (k : Type) [Field k] (Φ : FibPre k) (J : Type) (F : J → (Φ.H 1).Sec) (d : ℕ) (Pf : MvPolynomial J k), Pf.IsHomogeneous d → ∃ φ : (Φ.H d).Sec, (∀ l, φ.f l = ∑ m ∈ Pf.support, constFn Φ.G.hom ((Φ.H d).U l) (Pf.coeff m) * m.prod (fun i n => (show Γ(Φ.G.left, (Φ.H d).U l) from (F i).f l) ^ n)) ∧ (∀ α ∈ Φ.supp φ, ∃ β : Fin d → Φ.E.X, (∀ n, ∃ i, β n ∈ Φ.supp (F i)) ∧ α = ∑ n, β n) ∧ ∀ (x : Φ.Pt) (v : J → k), Crd (Φ.H 1) F x.left v → (MvPolynomial.eval v Pf = 0 ↔ ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ)) := by
  intro k _ Φ J F d Pf h
  refine ⟨formSec Φ F Pf h, fun _ => rfl, ?_, ?_⟩
  · rintro α ⟨l, hl⟩
    refine supp_form _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) Pf.support d (deg_of_mem h)
      (fun m => constFn Φ.E.B.hom _ (Pf.coeff m)) (fun i => (F i).f l) {β | ∃ i, β ∈ Φ.supp (F i)}
      (fun i β hβ => ⟨i, l, hβ⟩) α ?_
    simp only [WtLin.app_constFn _ _ _ (Over.w Φ.D.q)]
    exact hl
  · rintro x v ⟨l, c, hl, hv⟩
    have hl' : ⊤ ≤ x.left ⁻¹ᵁ (Φ.H d).U l := hl
    have hc : Crd (Φ.H d) (fun _ : Unit => formSec Φ F Pf h) x.left (fun _ => MvPolynomial.eval v Pf) := by
      refine ⟨l, c ^ d, hl', fun _ => ?_⟩
      rw [CrdCalc.valR_eq _ _ hl']
      change _ = _ * CrdCalc.valHom x.left _ hl' (∑ m ∈ Pf.support, _)
      rw [map_form, Units.val_pow_eq_pow_val, ← form_scale _ d (deg_of_mem h), MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [valHom_constFn _ _ (Over.w x)]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hv i, CrdCalc.valR_eq _ _ hl]
      rfl
    rw [← CrdCalc.crd_isUnit_iff () hc, isUnit_iff_ne_zero, not_not]

end GlobalTheory.ZH.FormSec
end
