import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.TripleTheta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g k : ℕ} {J : Type}
  {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {o : Type} [CommRing o] {b : TBase o k} {S S' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}

def Under (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La)
    (T : TObj g k J b s) : Prop :=
  ∃ φ : t.G ≅ T.A, IsMonHom φ.hom ∧ LBIso t.PP.L (T.L.pull φ.hom.left) ∧
    (∀ j, t.act.act (a j) ≫ φ.hom = φ.hom ≫ T.act j) ∧
    ∀ i, (lv (bas (Pi.single i 1))).left ≫ φ.hom.left = (T.pt i).left

/- English proof (translation)
Take `⟨w, hw, -⟩` from `m.lin`. Conclude with `⟨w, hw⟩`.
-/
theorem lbIso_of_sabMap {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) :
    LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

/- English proof (translation)
Rewrite using `[← Over.comp_left, φ.inv_hom_id, Over.id_left]`.
-/
theorem inv_hom_left {A B : Over S} (φ : A ≅ B) : φ.inv.left ≫ φ.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]

/- English proof (translation)
The claim follows from `inv_hom_left φ.symm`.
-/
theorem hom_inv_left {A B : Over S} (φ : A ≅ B) : φ.hom.left ≫ φ.inv.left = 𝟙 _ := inv_hom_left φ.symm

/- English proof (translation)
The claim follows from `(LBIso.chartPull (chartPullId _) (chartPullUnpull M (𝟙 _) rfl) (PELPull.lbIso_pull h φ.inv.left (inv_hom_left φ).symm)).symm`.
-/
theorem lbIso_inv {A B : Over S} (φ : A ≅ B) {L : LB A.left} {M : LB B.left}
    (h : LBIso L (M.pull φ.hom.left)) : LBIso M (L.pull φ.inv.left) :=
  (LBIso.chartPull (chartPullId _) (chartPullUnpull M (𝟙 _) rfl)
    (PELPull.lbIso_pull h φ.inv.left (inv_hom_left φ).symm)).symm

/- English proof (translation)
Take `⟨φ, hφ, hφL, hφa, hφp⟩` from `h`. Take `⟨ψ, hψ, hψL, hψa, hψp⟩` from `h'`. Establish `: IsMonHom ψ.symm.hom` using `inferInstanceAs (IsMonHom ψ.inv)`. Use `⟨ψ.inv.left ≫ m.φ ≫ φ.hom.left, ?_, ?_, fun i => ?_, fun j => ?_⟩` and prove the remaining obligations. Conclude with `((isGrpPullback_of_iso ψ.symm).comp (m.cart.comp (isGrpPullback_of_iso φ))).congr (by simp) rfl`.

Use `(lbIso_inv ψ hψL).trans T'.isLB (pull_isLB t'.PP.isLB _) (pull_isLB T.isLB _) (PELPull.lbIso_pull ?_ _ rfl)` and prove the remaining obligations. Conclude with `(lbIso_of_sabMap m).trans t'.PP.isLB (pull_isLB t.PP.isLB _) (pull_isLB T.isLB _) (PELPull.lbIso_pull hφL m.φ rfl)`. Rewrite using `[← hψp, ← hφp, Category.assoc, reassoc_of% hom_inv_left ψ, reassoc_of% hl]`. Establish `h₁ : (t.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (T.act j).left` using `congrArg (fun z => z.left) (hφa j)`. Establish `h₂ : (T'.act j).left ≫ ψ.inv.left = ψ.inv.left ≫ (t'.act.act (a j)).left`.

Rewrite using `[← Over.comp_left, ← Over.comp_left]`. Use `congr 1`. Rewrite using `[Iso.comp_inv_eq, Category.assoc, hψa, Iso.inv_hom_id_assoc]`. Establish `h₃ : (t'.act.act (a j)).left ≫ m.φ = m.φ ≫ (t.act.act (a j)).left` using `m.act _`. Rewrite using `[reassoc_of% h₂, reassoc_of% h₃, h₁, Category.assoc, Category.assoc]`.
-/
theorem tmap_of_sabMap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    (h' : Under t' lv' a bas T') {f : S' ⟶ S} (m : SABMap t' t f) (hl : ∀ x, (lv' x).left ≫ m.φ = f ≫ (lv x).left) :
    TMap T' T f := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hψa, hψp⟩ := h'
  have : IsMonHom ψ.symm.hom := inferInstanceAs (IsMonHom ψ.inv)
  refine ⟨ψ.inv.left ≫ m.φ ≫ φ.hom.left, ?_, ?_, fun i => ?_, fun j => ?_⟩
  · exact ((isGrpPullback_of_iso ψ.symm).comp (m.cart.comp (isGrpPullback_of_iso φ))).congr (by simp) rfl
  · refine (lbIso_inv ψ hψL).trans T'.isLB (pull_isLB t'.PP.isLB _) (pull_isLB T.isLB _) (PELPull.lbIso_pull ?_ _ rfl)
    exact (lbIso_of_sabMap m).trans t'.PP.isLB (pull_isLB t.PP.isLB _) (pull_isLB T.isLB _)
      (PELPull.lbIso_pull hφL m.φ rfl)
  · rw [← hψp, ← hφp, Category.assoc, reassoc_of% hom_inv_left ψ, reassoc_of% hl]
  · have h₁ : (t.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (T.act j).left := congrArg (fun z => z.left) (hφa j)
    have h₂ : (T'.act j).left ≫ ψ.inv.left = ψ.inv.left ≫ (t'.act.act (a j)).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      rw [Iso.comp_inv_eq, Category.assoc, hψa, Iso.inv_hom_id_assoc]
    have h₃ : (t'.act.act (a j)).left ≫ m.φ = m.φ ≫ (t.act.act (a j)).left := m.act _
    rw [reassoc_of% h₂, reassoc_of% h₃, h₁, Category.assoc, Category.assoc]

/- English proof (translation)
Take `⟨φ, hφ, hφL, hφa, hφp⟩` from `h`. Take `⟨ψ, hψ, hψL, hpt, hact⟩` from `h'`. Establish `hc : IsGrpPullback t'.G T.A f (m.φ ≫ φ.hom.left)` using `(IsGrpPullback.comp m.cart (isGrpPullback_of_iso φ)).congr (Category.comp_id f) rfl`. Take `⟨e, he, heF⟩` from `grpPullback_iso hc hψ`. Use `⟨e, he, ?_, fun j => ?_, fun i => ?_⟩` and prove the remaining obligations.

Conclude with `((lbIso_of_sabMap m).trans t'.PP.isLB (pull_isLB t.PP.isLB _) (pull_isLB T.isLB _) (PELPull.lbIso_pull hφL m.φ rfl)).trans t'.PP.isLB (pull_isLB T.isLB _) (pull_isLB T'.isLB _) (PELPull.lbIso_pull hψL e.hom.left heF.symm).symm`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hψ.1.hom_ext` to reduce the goal to its premises. Establish `h₁ : (t.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (T.act j).left` using `congrArg (fun z => z.left) (hφa j)`. Establish `h₂ : (t'.act.act (a j)).left ≫ m.φ = m.φ ≫ (t.act.act (a j)).left` using `m.act _`.

Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, heF, hact, ← Category.assoc, h₂, Category.assoc, h₁, ← Category.assoc, ← heF, Category.assoc]`. Rewrite using `[Over.w, Over.w]`. Apply `hψ.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, heF, reassoc_of% hl, hφp, hpt]`. Rewrite using `[Category.assoc, Over.w, Over.w, Over.w]`.

Both sides reduce to the same expression.
-/
theorem under_of_tmap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    {f : S' ⟶ S} (h' : TMap T' T f) (m : SABMap t' t f) (hl : ∀ x, (lv' x).left ≫ m.φ = f ≫ (lv x).left) :
    Under t' lv' a bas T' := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hpt, hact⟩ := h'
  have hc : IsGrpPullback t'.G T.A f (m.φ ≫ φ.hom.left) :=
    (IsGrpPullback.comp m.cart (isGrpPullback_of_iso φ)).congr (Category.comp_id f) rfl
  obtain ⟨e, he, heF⟩ := grpPullback_iso hc hψ
  refine ⟨e, he, ?_, fun j => ?_, fun i => ?_⟩
  · exact ((lbIso_of_sabMap m).trans t'.PP.isLB (pull_isLB t.PP.isLB _) (pull_isLB T.isLB _)
      (PELPull.lbIso_pull hφL m.φ rfl)).trans
      t'.PP.isLB (pull_isLB T.isLB _) (pull_isLB T'.isLB _) (PELPull.lbIso_pull hψL e.hom.left heF.symm).symm
  · apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · have h₁ : (t.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (T.act j).left :=
        congrArg (fun z => z.left) (hφa j)
      have h₂ : (t'.act.act (a j)).left ≫ m.φ = m.φ ≫ (t.act.act (a j)).left := m.act _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, heF, hact, ← Category.assoc, h₂,
        Category.assoc, h₁, ← Category.assoc, ← heF, Category.assoc]
    · rw [Over.w, Over.w]
  · apply hψ.1.hom_ext
    · rw [Category.assoc, heF, reassoc_of% hl, hφp, hpt]
    · rw [Category.assoc, Over.w, Over.w, Over.w]; rfl

/- English proof (translation)
Use `act.add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this`.
-/
theorem act_zero {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) : act.act 0 = 1 := by
  have := act.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

/- English proof (translation)
Use `act.add (-c) c` as an intermediate fact. Rewrite `this` using `[neg_add_cancel, act_zero]`. Conclude with `eq_inv_of_mul_eq_one_left this.symm`.
-/
theorem act_neg {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (c : O) :
    act.act (-c) = (act.act c)⁻¹ := by
  have := act.add (-c) c
  rw [neg_add_cancel, act_zero] at this
  exact eq_inv_of_mul_eq_one_left this.symm

/- English proof (translation)
Set `u : Over.mk (G'.hom ≫ f) ⟶ G` to `Over.homMk φ h.1.w`. Establish `key : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left ↔ pushHom h G' (act'.act c) = preHom u (act.act c)` using `fun c => ⟨fun e => Over.OverMorphism.ext e, fun e => congrArg (fun z => z.left) e⟩`. Establish `hc : c ∈ Subring.closure (Set.range a)` using `ha ▸ Subring.mem_top c`. Proceed by induction on `hc using Subring.closure_induction with`. Consider the case `mem x hx => obtain ⟨j, rfl⟩ := hx`.

Conclude with `hj j`. Consider the case `zero => rw [key, act_zero, act_zero, map_one, map_one]`. Consider the case `one => rw [act.one, act'.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]`. Consider the case `add x y _ _ hx hy => rw [key] at hx hy ⊢`. Rewrite using `[act.add, act'.add, map_mul, map_mul, hx, hy]`.

Consider the case `neg x _ hx => rw [key] at hx ⊢`. Rewrite using `[act_neg, act_neg, map_inv, map_inv, hx]`. Consider the case `mul x y _ _ hx hy => rw [act.mul, act'.mul, Over.comp_left, Over.comp_left, Category.assoc, hy, reassoc_of% hx]`.
-/
theorem act_comm_of_closure {O : Type} [CommRing O] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] (act : OAct O G)
    (act' : OAct O G') {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {a : J → O}
    (ha : Subring.closure (Set.range a) = ⊤) (hj : ∀ j, (act'.act (a j)).left ≫ φ = φ ≫ (act.act (a j)).left) (c : O) :
    (act'.act c).left ≫ φ = φ ≫ (act.act c).left := by
  let u : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have key : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left ↔ pushHom h G' (act'.act c) = preHom u (act.act c) :=
    fun c => ⟨fun e => Over.OverMorphism.ext e, fun e => congrArg (fun z => z.left) e⟩
  have hc : c ∈ Subring.closure (Set.range a) := ha ▸ Subring.mem_top c
  induction hc using Subring.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hj j
  | zero => rw [key, act_zero, act_zero, map_one, map_one]
  | one => rw [act.one, act'.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  | add x y _ _ hx hy => rw [key] at hx hy ⊢; rw [act.add, act'.add, map_mul, map_mul, hx, hy]
  | neg x _ hx => rw [key] at hx ⊢; rw [act_neg, act_neg, map_inv, map_inv, hx]
  | mul x y _ _ hx hy => rw [act.mul, act'.mul, Over.comp_left, Over.comp_left, Category.assoc, hy, reassoc_of% hx]

/- English proof (translation)
Set `u' : D.La →+ Additive A` to `AddMonoidHom.mk' (fun x => Additive.ofMul (u x)) fun x y => by rw [hu]; rfl`. Set `v' : D.La →+ Additive A` to `AddMonoidHom.mk' (fun x => Additive.ofMul (v x)) fun x y => by rw [hv]; rfl`. Establish `: u'.comp bas.toLinearMap.toAddMonoidHom = v'.comp bas.toLinearMap.toAddMonoidHom`. Use `AddMonoidHom.functions_ext' _ _ _ fun i => AddMonoidHom.ext_int ?_` and prove the remaining obligations. Conclude with `congrArg Additive.ofMul (h i)`.

Establish `e` using `DFunLike.congr_fun this (bas.symm x)`. Simplify `e` using `[u', v']`.
-/
theorem eq_of_basis {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u v : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) (hv : ∀ x y, v (x + y) = v x * v y)
    (h : ∀ i, u (bas (Pi.single i 1)) = v (bas (Pi.single i 1))) (x : D.La) : u x = v x := by
  let u' : D.La →+ Additive A := AddMonoidHom.mk' (fun x => Additive.ofMul (u x)) fun x y => by rw [hu]; rfl
  let v' : D.La →+ Additive A := AddMonoidHom.mk' (fun x => Additive.ofMul (v x)) fun x y => by rw [hv]; rfl
  have : u'.comp bas.toLinearMap.toAddMonoidHom = v'.comp bas.toLinearMap.toAddMonoidHom := by
    refine AddMonoidHom.functions_ext' _ _ _ fun i => AddMonoidHom.ext_int ?_
    exact congrArg Additive.ofMul (h i)
  have e := DFunLike.congr_fun this (bas.symm x)
  simpa [u', v'] using e

/- English proof (translation)
Take `⟨φ, hφ, hφL, hφa, hφp⟩` from `h`. Take `⟨ψ, hψ, hψL, hψa, hψp⟩` from `h'`. Take `⟨χ, hχ, hχL, hpt, hact⟩` from `m`. Establish `: IsMonHom φ.symm.hom` using `inferInstanceAs (IsMonHom φ.inv)`. Establish `hc : IsGrpPullback t'.G t.G f (ψ.hom.left ≫ χ ≫ φ.inv.left)` using `((isGrpPullback_of_iso ψ).comp (hχ.comp (isGrpPullback_of_iso φ.symm))).congr (by simp) rfl`.

Take `⟨ν, hν⟩` from `exists_sabMap_of_lbIso E H S S' t t' f _ ⟨hS, fun _ _ _ _ _ _ _ => inferInstance⟩ hc (act_comm_of_closure t.act t'.act hc ha fun j => by`. Establish `h₁ : (t'.act.act (a j)).left ≫ ψ.hom.left = ψ.hom.left ≫ (T'.act j).left` using `congrArg (fun z => z.left) (hψa j)`. Establish `h₂ : (T.act j).left ≫ φ.inv.left = φ.inv.left ≫ (t.act.act (a j)).left`. Rewrite using `[← Over.comp_left, ← Over.comp_left]`. Use `congr 1`.

Rewrite using `[Iso.comp_inv_eq, Category.assoc, hφa, Iso.inv_hom_id_assoc]`. Rewrite using `[reassoc_of% h₁, reassoc_of% hact, h₂, Category.assoc, Category.assoc])`. Use the proof step `(hψL.trans t'.PP.isLB (pull_isLB T'.isLB _) (pull_isLB t.PP.isLB _) (PELPull.lbIso_pull (hχL.trans T'.isLB (pull_isLB T.isLB _) (pull_isLB t.PP.isLB _) (PELPull.lbIso_pull (lbIso_inv φ hφL) χ rfl)) _ rfl))`. Use `⟨ν, fun x => ?_⟩` and prove the remaining obligations. Establish `e` using `eq_of_basis bas lv' (fun x => ObjPull.secPull hc (lv x)) hlv' (fun x y => by rw [hlv, map_mul]) (fun i => Over.OverMorphism.ext (hc.1.hom_ext (by`.

Rewrite using `[ObjPull.secPull_left, reassoc_of% hψp, reassoc_of% hpt, ← hφp, Category.assoc, hom_inv_left, Category.comp_id]) (by rw [Over.w, Over.w]))) x`. Rewrite using `[hν, e, ObjPull.secPull_left]`.
-/
theorem sabMap_of_tmap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    (h' : Under t' lv' a bas T') (hlv : ∀ x y, lv (x + y) = lv x * lv y) (hlv' : ∀ x y, lv' (x + y) = lv' x * lv' y)
    (ha : Subring.closure (Set.range a) = ⊤) (hS : IsReduced S') (hp : IsProper t'.G.hom) {f : S' ⟶ S}
    (m : TMap T' T f) : ∃ ν : SABMap t' t f, ∀ x, (lv' x).left ≫ ν.φ = f ≫ (lv x).left := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hψa, hψp⟩ := h'
  obtain ⟨χ, hχ, hχL, hpt, hact⟩ := m
  have : IsMonHom φ.symm.hom := inferInstanceAs (IsMonHom φ.inv)
  have hc : IsGrpPullback t'.G t.G f (ψ.hom.left ≫ χ ≫ φ.inv.left) :=
    ((isGrpPullback_of_iso ψ).comp (hχ.comp (isGrpPullback_of_iso φ.symm))).congr (by simp) rfl
  obtain ⟨ν, hν⟩ := exists_sabMap_of_lbIso E H S S' t t' f _ ⟨hS, fun _ _ _ _ _ _ _ => inferInstance⟩ hc
    (act_comm_of_closure t.act t'.act hc ha fun j => by
      have h₁ : (t'.act.act (a j)).left ≫ ψ.hom.left = ψ.hom.left ≫ (T'.act j).left :=
        congrArg (fun z => z.left) (hψa j)
      have h₂ : (T.act j).left ≫ φ.inv.left = φ.inv.left ≫ (t.act.act (a j)).left := by
        rw [← Over.comp_left, ← Over.comp_left]
        congr 1
        rw [Iso.comp_inv_eq, Category.assoc, hφa, Iso.inv_hom_id_assoc]
      rw [reassoc_of% h₁, reassoc_of% hact, h₂, Category.assoc, Category.assoc])
    (hψL.trans t'.PP.isLB (pull_isLB T'.isLB _) (pull_isLB t.PP.isLB _) (PELPull.lbIso_pull
      (hχL.trans T'.isLB (pull_isLB T.isLB _) (pull_isLB t.PP.isLB _) (PELPull.lbIso_pull (lbIso_inv φ hφL) χ rfl)) _ rfl))
  refine ⟨ν, fun x => ?_⟩
  have e := eq_of_basis bas lv' (fun x => ObjPull.secPull hc (lv x)) hlv' (fun x y => by rw [hlv, map_mul])
    (fun i => Over.OverMorphism.ext (hc.1.hom_ext (by
      rw [ObjPull.secPull_left, reassoc_of% hψp, reassoc_of% hpt, ← hφp, Category.assoc, hom_inv_left,
        Category.comp_id]) (by rw [Over.w, Over.w]))) x
  rw [hν, e, ObjPull.secPull_left]

end GlobalTheory.TripleTheta
