import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.Adelic

namespace GlobalTheory.Cartier

namespace CartierDiv

variable {X : Scheme.{0}} [IsIntegral X] (k : Type) [Field k] [Algebra k X.functionField]
  (D : CartierDiv X) (V : Set X.functionField)

def IsBasePoint (x : X) : Prop := ∀ f ∈ V, ¬ D.GeneratesAt x f

structure BasePointFree : Prop where

  mem : ∀ f ∈ V, f ∈ D.sections

  exists_generatesAt : ∀ x, ∃ f ∈ V, D.GeneratesAt x f

def VanishesOn (f : X.functionField) (Z : Set X) : Prop := ∀ x ∈ Z, D.VanishesAt x f

def ratioField : IntermediateField k X.functionField :=
  IntermediateField.adjoin k {r | ∃ f ∈ V, ∃ g ∈ V, g ≠ 0 ∧ r = f / g}

structure Birational : Prop where

  mem : ∀ f ∈ V, f ∈ D.sections

  exists_ne_zero : ∃ f ∈ V, f ≠ 0

  ratioField_eq : ratioField k V = ⊤

def SameImage (y y' : X) : Prop :=
  ∀ (n : ℕ) (b : Fin n → X.functionField), (∀ i, b i ∈ V) →
    ∀ (d : ℕ) (g : MvPolynomial (Fin n) k), g.IsHomogeneous d →
      ((d • D).GeneratesAt y (aeval b g) ↔ (d • D).GeneratesAt y' (aeval b g))

def Contracts (C : Set X) : Prop :=
  ∀ y ∈ C, ∀ y' ∈ C, ¬ D.IsBasePoint V y → ¬ D.IsBasePoint V y' → D.SameImage k V y y'

structure NoContract (bd : Set X) : Prop where

  mem : ∀ f ∈ V, f ∈ D.sections

  not_contracts : ∀ C : Set X, IsClosed C → IsIrreducible C → topologicalKrullDim C = 1 →
    Disjoint C bd → ¬ D.Contracts k V C

variable {k D V}

/- English proof (translation)
Introduce `hx` and use `have ⟨f, hf, h'⟩ := h.2 x; hx f hf h'`.
-/
theorem BasePointFree.not_isBasePoint (h : D.BasePointFree V) (x : X) : ¬ D.IsBasePoint V x :=
  fun hx => have ⟨f, hf, h'⟩ := h.2 x; hx f hf h'

/- English proof (translation)
The claim follows from `have ⟨f, hf, h'⟩ := h.2 (genericPoint X); ⟨f, hf, h'.ne_zero⟩`.
-/
theorem BasePointFree.exists_ne_zero (h : D.BasePointFree V) : ∃ f ∈ V, f ≠ 0 :=
  have ⟨f, hf, h'⟩ := h.2 (genericPoint X); ⟨f, hf, h'.ne_zero⟩

/- English proof (translation)
The claim follows from `by_contra fun hf => (vanishesAt_iff.1 (h _ trivial)).2 (D.generatesAt_genericPoint hf)`.
-/
theorem VanishesOn.eq_zero {f : X.functionField} (h : D.VanishesOn f Set.univ) : f = 0 :=
  by_contra fun hf => (vanishesAt_iff.1 (h _ trivial)).2 (D.generatesAt_genericPoint hf)

/- English proof (translation)
The claim follows from `forall₂_congr fun _ _ => h.mem_supp_iff.symm`.
-/
theorem Eff.vanishesOn_one_iff (h : D.Eff) {Z : Set X} : D.VanishesOn 1 Z ↔ Z ⊆ D.supp :=
  forall₂_congr fun _ _ => h.mem_supp_iff.symm

/- English proof (translation)
Establish `e` using `Twist.eval₂Hom_unit_mul (algebraMap k X.functionField) u b (mem_polyGrading_natCast.2 hg)`. Rewrite using `[(h.nsmul d).generatesAt_iff, mul_comm, ← zpow_natCast]`. Simplify using `only [mul_comm (b _)]`. Conclude with `iff_of_eq (congrArg _ e.symm)`.
-/
theorem IsEqn.generatesAt_aeval_iff {x : X} {u : X.functionFieldˣ} (h : D.IsEqn x u) {ι : Type}
    (b : ι → X.functionField) {d : ℕ} {g : MvPolynomial ι k} (hg : g.IsHomogeneous d) :
    (d • D).GeneratesAt x (aeval b g) ↔ UnitAt x (aeval (fun i => b i * u) g) := by
  have e := Twist.eval₂Hom_unit_mul (algebraMap k X.functionField) u b
    (mem_polyGrading_natCast.2 hg)
  rw [(h.nsmul d).generatesAt_iff, mul_comm, ← zpow_natCast]
  simp only [mul_comm (b _)]
  exact iff_of_eq (congrArg _ e.symm)

/- English proof (translation)
Establish `hu (x : X) (c : k) : UnitAt x (algebraMap k X.functionField c) ↔ c ≠ 0` using `⟨fun h e => h.ne_zero (by rw [e, map_zero]), fun h => (unitAt_iff ((map_ne_zero _).2 h)).2 ⟨hk x c, map_inv₀ (algebraMap k X.functionField) c ▸ hk x _⟩⟩`. Establish `key (y : X) (hy : ¬ D.IsBasePoint V y) : D.IsEqn y 1`. Take `⟨f, hf, h⟩ : ∃ f ∈ V, D.GeneratesAt y f` from `by simpa [IsBasePoint] using hy`. Take `⟨c, rfl⟩` from `hV f hf`. Use `(generatesAt_zero_iff.2 ((hu y c).2 fun e => h.ne_zero (by` as an intermediate fact.

Rewrite using `[e, map_zero])).inv).mul h`. Rewrite `this` using `[zero_add, inv_mul_cancel₀ h.ne_zero]`. Conclude with `not_not.1 (notMem_supp_iff.2 this)`. Introduce `y _ y' _ hy hy' n b hb d g hg`. Use `choose c hc using fun i => hV _ (hb i)`.

Rewrite using `[(key y hy).generatesAt_aeval_iff b hg, (key y' hy').generatesAt_aeval_iff b hg]`. Simplify using `only [Units.val_one, mul_one, ← hc]`. Establish `e` using `aeval_algebraMap_apply X.functionField c g`. Rewrite `e` using `[Function.comp_def]`. Rewrite using `[e, hu, hu]`.
-/
theorem contracts_of_constant (hk : ∀ (x : X) (c : k), RegAt x (algebraMap k X.functionField c))
    (hV : ∀ f ∈ V, f ∈ Set.range (algebraMap k X.functionField)) (C : Set X) :
    D.Contracts k V C := by
  have hu (x : X) (c : k) : UnitAt x (algebraMap k X.functionField c) ↔ c ≠ 0 :=
    ⟨fun h e => h.ne_zero (by rw [e, map_zero]), fun h =>
      (unitAt_iff ((map_ne_zero _).2 h)).2 ⟨hk x c, map_inv₀ (algebraMap k X.functionField) c ▸ hk x _⟩⟩
  have key (y : X) (hy : ¬ D.IsBasePoint V y) : D.IsEqn y 1 := by
    obtain ⟨f, hf, h⟩ : ∃ f ∈ V, D.GeneratesAt y f := by simpa [IsBasePoint] using hy
    obtain ⟨c, rfl⟩ := hV f hf
    have := (generatesAt_zero_iff.2 ((hu y c).2 fun e => h.ne_zero (by
      rw [e, map_zero])).inv).mul h
    rw [zero_add, inv_mul_cancel₀ h.ne_zero] at this
    exact not_not.1 (notMem_supp_iff.2 this)
  intro y _ y' _ hy hy' n b hb d g hg
  choose c hc using fun i => hV _ (hb i)
  rw [(key y hy).generatesAt_aeval_iff b hg, (key y' hy').generatesAt_aeval_iff b hg]
  simp only [Units.val_one, mul_one, ← hc]
  have e := aeval_algebraMap_apply X.functionField c g
  rw [Function.comp_def] at e
  rw [e, hu, hu]

end CartierDiv

namespace Presents

open CartierDiv

variable {k : Type} [Field k] {S : LinSys k} [IsIntegral S.Y] [Algebra k S.Y.functionField]
  [IsScalarTower k Γ(S.Y, ⊤) S.Y.functionField] {D : CartierDiv S.Y}
  {r : S.L.ι → S.Y.functionFieldˣ} (h : Presents D S.L r)

def ratSet : Set S.Y.functionField := Set.range fun j => h.rat (S.b j)

omit [Algebra k S.Y.functionField] [IsScalarTower k Γ(S.Y, ⊤) S.Y.functionField] in

/- English proof (translation)
Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `h.rat_mem _`.
-/
theorem mem_of_mem_ratSet : ∀ f ∈ h.ratSet, f ∈ D.sections := by
  rintro _ ⟨j, rfl⟩
  exact h.rat_mem _

omit [Algebra k S.Y.functionField] [IsScalarTower k Γ(S.Y, ⊤) S.Y.functionField] in

/- English proof (translation)
Use `⟨fun hb => eq_top_iff.2 fun x _ => ?_, fun hb => ⟨h.mem_of_mem_ratSet, fun x => ?_⟩⟩` and prove the remaining obligations. Take `⟨_, ⟨j, rfl⟩, hj⟩` from `hb.2 x`. Conclude with `Opens.mem_iSup.2 ⟨j, (h.generatesAt_rat_iff _).1 hj⟩`. Take `⟨j, hj⟩` from `Opens.mem_iSup.1 (hb.ge (Set.mem_univ x))`. Conclude with `⟨_, ⟨j, rfl⟩, (h.generatesAt_rat_iff _).2 hj⟩`.
-/
theorem basePointFree_iff : D.BasePointFree h.ratSet ↔ S.BasePointFree := by
  refine ⟨fun hb => eq_top_iff.2 fun x _ => ?_, fun hb => ⟨h.mem_of_mem_ratSet, fun x => ?_⟩⟩
  · obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hb.2 x
    exact Opens.mem_iSup.2 ⟨j, (h.generatesAt_rat_iff _).1 hj⟩
  · obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hb.ge (Set.mem_univ x))
    exact ⟨_, ⟨j, rfl⟩, (h.generatesAt_rat_iff _).2 hj⟩

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_chart S.isLB x`. Establish `e : aeval (fun j => h.rat (S.b j) * r i) g = fnOf _ (gen_mem hi) (Twist.zfun (S.form hg) i)`. Rewrite using `[LinSys.form, Twist.zfun_formSec, Twist.chartEval, map_eval₂Hom, aeval_def, coe_eval₂Hom]`. Use `congr 1`. Conclude with `RingHom.ext fun a => (IsScalarTower.algebraMap_apply k Γ(S.Y, ⊤) _ a).trans (fnOf_resG le_top _ _).symm`.

Conclude with `funext fun j => (h.rat_mul _ i (gen_mem hi)).trans (fnOf_resG le_rfl (gen_mem hi) _).symm`. Rewrite using `[(h.isEqn i x hi).generatesAt_aeval_iff _ hg, e, unitAt_fnOf_iff hi, Twist.basicOpen_zfun]`. Conclude with `and_iff_right hi`.
-/
theorem generatesAt_aeval_iff {d : ℕ} {g : MvPolynomial (Fin S.N) k} (hg : g.IsHomogeneous d)
    (x : S.Y) : (d • D).GeneratesAt x (aeval (fun j => h.rat (S.b j)) g) ↔
      x ∈ nonzeroLocus (S.form hg) := by
  obtain ⟨i, hi⟩ := exists_chart S.isLB x
  have e : aeval (fun j => h.rat (S.b j) * r i) g =
      fnOf _ (gen_mem hi) (Twist.zfun (S.form hg) i) := by
    rw [LinSys.form, Twist.zfun_formSec, Twist.chartEval, map_eval₂Hom, aeval_def, coe_eval₂Hom]
    congr 1
    · exact RingHom.ext fun a => (IsScalarTower.algebraMap_apply k Γ(S.Y, ⊤) _ a).trans
        (fnOf_resG le_top _ _).symm
    · exact funext fun j => (h.rat_mul _ i (gen_mem hi)).trans
        (fnOf_resG le_rfl (gen_mem hi) _).symm
  rw [(h.isEqn i x hi).generatesAt_aeval_iff _ hg, e, unitAt_fnOf_iff hi, Twist.basicOpen_zfun]
  exact and_iff_right hi

/- English proof (translation)
Use `⟨fun e d g hg => ?_, fun e n b hb d g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[← h.generatesAt_aeval_iff, ← h.generatesAt_aeval_iff]`. Conclude with `e _ _ (fun j => ⟨j, rfl⟩) d g hg`. Use `choose σ hσ using hb`. Use `e d _ (hg.rename_isHomogeneous (f := σ))` as an intermediate fact.

Rewrite `this` using `[← h.generatesAt_aeval_iff, ← h.generatesAt_aeval_iff, aeval_rename, show (fun j => h.rat (S.b j)) ∘ σ = b from funext hσ]`. Then use the resulting hypothesis.
-/
theorem sameImage_iff (y y' : S.Y) : D.SameImage k h.ratSet y y' ↔ S.SameImage y y' := by
  refine ⟨fun e d g hg => ?_, fun e n b hb d g hg => ?_⟩
  · rw [← h.generatesAt_aeval_iff, ← h.generatesAt_aeval_iff]
    exact e _ _ (fun j => ⟨j, rfl⟩) d g hg
  · choose σ hσ using hb
    have := e d _ (hg.rename_isHomogeneous (f := σ))
    rwa [← h.generatesAt_aeval_iff, ← h.generatesAt_aeval_iff, aeval_rename,
      show (fun j => h.rat (S.b j)) ∘ σ = b from funext hσ] at this

/- English proof (translation)
Establish `hn` using `(h.basePointFree_iff.2 hb).not_isBasePoint`. Establish `e (C : Set S.Y) : D.Contracts k h.ratSet C ↔ S.Contracts C` using `forall₄_congr fun y _ y' _ => by rw [imp_iff_right (hn y), imp_iff_right (hn y'), sameImage_iff]`. Conclude with `⟨fun c C h₁ h₂ h₃ h₄ => (e C).not.1 (c.2 C h₁ h₂ h₃ h₄), fun c => ⟨h.mem_of_mem_ratSet, fun C h₁ h₂ h₃ h₄ => (e C).not.2 (c C h₁ h₂ h₃ h₄)⟩⟩`.
-/
theorem noContract_iff (hb : S.BasePointFree) (bd : Set S.Y) :
    D.NoContract k h.ratSet bd ↔ S.NoContract bd := by
  have hn := (h.basePointFree_iff.2 hb).not_isBasePoint
  have e (C : Set S.Y) : D.Contracts k h.ratSet C ↔ S.Contracts C :=
    forall₄_congr fun y _ y' _ => by rw [imp_iff_right (hn y), imp_iff_right (hn y'), sameImage_iff]
  exact ⟨fun c C h₁ h₂ h₃ h₄ => (e C).not.1 (c.2 C h₁ h₂ h₃ h₄),
    fun c => ⟨h.mem_of_mem_ratSet, fun C h₁ h₂ h₃ h₄ => (e C).not.2 (c C h₁ h₂ h₃ h₄)⟩⟩

/- English proof (translation)
Use `set ρ : S.Y.functionField →+* S.Y.residueField (genericPoint S.Y) := (S.Y.residue (genericPoint S.Y)).hom`. Establish `hi` using `gen_mem (S.mem_chartAt (ptOf (resPt (genericPoint S.Y))))`. Establish `e₁ (a : k) : S.baseHom (resPt (genericPoint S.Y)) a = ρ (algebraMap k _ a)`. Rewrite using `[← S.valR_algebraMap, projSys.valR_resPt _ ⊤ trivial, IsScalarTower.algebraMap_apply k Γ(S.Y, ⊤) S.Y.functionField]`. Both sides reduce to the same expression.

Establish `e₂ (i j : Fin S.N) : S.coords (resPt (genericPoint S.Y)) i / S.coords (resPt (genericPoint S.Y)) j = ρ (h.rat (S.b i) / h.rat (S.b j))`. Rewrite using `[← mul_div_mul_right _ _ (r _).ne_zero, h.rat_mul _ _ hi, h.rat_mul _ _ hi, map_div₀]`. Conclude with `congrArg₂ (· / ·) (projSys.valR_resPt _ _ hi _) (projSys.valR_resPt _ _ hi _)`. Use `le_antisymm (Subfield.closure_le.2 ?_) (Subfield.gc_map_comap ρ _ _ |>.2 (Subfield.closure_le.2 ?_))` and prove the remaining obligations. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨i, j, rfl⟩)`.

Conclude with `⟨_, (ratioField k h.ratSet).algebraMap_mem a, (e₁ a).symm⟩`. Use `⟨_, ?_, (e₂ i j).symm⟩` and prove the remaining obligations. Distinguish the cases in `h0 : h.rat (S.b j) = 0`. Rewrite using `[h0, div_zero]`. Conclude with `(ratioField k h.ratSet).zero_mem`.

Conclude with `IntermediateField.subset_adjoin _ _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, h0, rfl⟩`. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, -, rfl⟩)`. Conclude with `Subfield.subset_closure (Or.inl ⟨a, e₁ a⟩)`. Conclude with `Subfield.subset_closure (Or.inr ⟨i, j, (e₂ i j).symm⟩)`.
-/
theorem ratioField_resPt : S.ratioField (resPt (genericPoint S.Y)) =
    (ratioField k h.ratSet).toSubfield.map (S.Y.residue (genericPoint S.Y)).hom := by
  set ρ : S.Y.functionField →+* S.Y.residueField (genericPoint S.Y) :=
    (S.Y.residue (genericPoint S.Y)).hom
  have hi := gen_mem (S.mem_chartAt (ptOf (resPt (genericPoint S.Y))))
  have e₁ (a : k) : S.baseHom (resPt (genericPoint S.Y)) a = ρ (algebraMap k _ a) := by
    rw [← S.valR_algebraMap, projSys.valR_resPt _ ⊤ trivial,
      IsScalarTower.algebraMap_apply k Γ(S.Y, ⊤) S.Y.functionField]
    rfl
  have e₂ (i j : Fin S.N) : S.coords (resPt (genericPoint S.Y)) i /
      S.coords (resPt (genericPoint S.Y)) j = ρ (h.rat (S.b i) / h.rat (S.b j)) := by
    rw [← mul_div_mul_right _ _ (r _).ne_zero, h.rat_mul _ _ hi, h.rat_mul _ _ hi, map_div₀]
    exact congrArg₂ (· / ·) (projSys.valR_resPt _ _ hi _) (projSys.valR_resPt _ _ hi _)
  refine le_antisymm (Subfield.closure_le.2 ?_) (Subfield.gc_map_comap ρ _ _ |>.2
    (Subfield.closure_le.2 ?_))
  · rintro _ (⟨a, rfl⟩ | ⟨i, j, rfl⟩)
    · exact ⟨_, (ratioField k h.ratSet).algebraMap_mem a, (e₁ a).symm⟩
    · refine ⟨_, ?_, (e₂ i j).symm⟩
      by_cases h0 : h.rat (S.b j) = 0
      · rw [h0, div_zero]
        exact (ratioField k h.ratSet).zero_mem
      · exact IntermediateField.subset_adjoin _ _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, h0, rfl⟩
  · rintro _ (⟨a, rfl⟩ | ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, -, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨a, e₁ a⟩)
    · exact Subfield.subset_closure (Or.inr ⟨i, j, (e₂ i j).symm⟩)

/- English proof (translation)
Establish `e : ratioField k h.ratSet = ⊤ ↔ S.ratioField (resPt (genericPoint S.Y)) = ⊤`. Rewrite using `[h.ratioField_resPt]`. Use `⟨fun e => eq_top_iff.2 fun a _ => ?_, fun e => eq_top_iff.2 fun a _ => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `S.Y.residue_surjective _ a`. Conclude with `⟨a, e.ge trivial, rfl⟩`.

Take `⟨b, hb, e'⟩` from `e.ge (Subfield.mem_top ((S.Y.residue (genericPoint S.Y)).hom a))`. Conclude with `RingHom.injective (R := S.Y.functionField) _ e' ▸ hb`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, ⟨_, ⟨j, rfl⟩, hj⟩, ht⟩`. Conclude with `⟨⟨j, fun e => hj (by simp only [e, map_zero])⟩, _, genericPoint_spec S.Y, e.1 ht⟩`.

Introduce and unpack `⟨⟨j, hj⟩, η, hη, ht⟩`. Take `rfl` from `(genericPoint_spec S.Y).eq hη`. Conclude with `⟨h.mem_of_mem_ratSet, ⟨_, ⟨j, rfl⟩, fun e => hj (h.rat_injective (e.trans (map_zero _).symm))⟩, e.2 ht⟩`.
-/
theorem birational_iff : D.Birational k h.ratSet ↔ (∃ j, S.b j ≠ 0) ∧ S.Birational := by
  have e : ratioField k h.ratSet = ⊤ ↔ S.ratioField (resPt (genericPoint S.Y)) = ⊤ := by
    rw [h.ratioField_resPt]
    refine ⟨fun e => eq_top_iff.2 fun a _ => ?_, fun e => eq_top_iff.2 fun a _ => ?_⟩
    · obtain ⟨a, rfl⟩ := S.Y.residue_surjective _ a
      exact ⟨a, e.ge trivial, rfl⟩
    · obtain ⟨b, hb, e'⟩ := e.ge (Subfield.mem_top ((S.Y.residue (genericPoint S.Y)).hom a))
      exact RingHom.injective (R := S.Y.functionField) _ e' ▸ hb
  constructor
  · rintro ⟨-, ⟨_, ⟨j, rfl⟩, hj⟩, ht⟩
    exact ⟨⟨j, fun e => hj (by simp only [e, map_zero])⟩, _, genericPoint_spec S.Y, e.1 ht⟩
  · rintro ⟨⟨j, hj⟩, η, hη, ht⟩
    obtain rfl := (genericPoint_spec S.Y).eq hη
    exact ⟨h.mem_of_mem_ratSet, ⟨_, ⟨j, rfl⟩, fun e => hj (h.rat_injective (e.trans (map_zero _).symm))⟩,
      e.2 ht⟩

end Presents

end GlobalTheory.Cartier
