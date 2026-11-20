import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegreesStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfFiniteOrderOfFixThreeTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducedFrobeniusCompUniqueOriginStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.InducedTranslation

section Transl

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

/- English proof (translation)
Establish `e : translPt A x = (fst T A ≫ x) * snd T A` using `rfl`. Rewrite using `[translT, comp_lift, lift_fst, e, MonObj.comp_mul, lift_fst_assoc, lift_snd]`.
-/
theorem lift_translT {Z : Over S} (t : Z ⟶ T) (u : Z ⟶ A) (x : T ⟶ A) :
    lift t u ≫ translT A x = lift t ((t ≫ x) * u) := by
  have e : translPt A x = (fst T A ≫ x) * snd T A := rfl
  rw [translT, comp_lift, lift_fst, e, MonObj.comp_mul, lift_fst_assoc, lift_snd]

/- English proof (translation)
The claim follows from `hom_ext _ _ (by rw [Category.assoc, hh, lift_fst, lift_fst]) (by rw [Category.assoc, lift_snd])`.
-/
theorem eq_lift {h : T ⊗ A ⟶ T ⊗ A} (hh : h ≫ fst T A = fst T A) {Z : Over S} (t : Z ⟶ T) (u : Z ⟶ A) :
    lift t u ≫ h = lift t (lift t u ≫ h ≫ snd T A) :=
  hom_ext _ _ (by rw [Category.assoc, hh, lift_fst, lift_fst]) (by rw [Category.assoc, lift_snd])

/- English proof (translation)
Rewrite `e` using `[lift_fst_snd, Category.id_comp, Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem end_ext {h h' : T ⊗ A ⟶ T ⊗ A} (e : lift (fst T A) (snd T A) ≫ h = lift (fst T A) (snd T A) ≫ h') :
    h = h' := by
  rwa [lift_fst_snd, Category.id_comp, Category.id_comp] at e

/- English proof (translation)
The claim follows from `end_ext (by rw [← Category.assoc, lift_translT, lift_translT, lift_translT, MonObj.comp_mul, _root_.mul_assoc])`.
-/
theorem translT_comp (x y : T ⟶ A) : translT A x ≫ translT A y = translT A (y * x) :=
  end_ext (by rw [← Category.assoc, lift_translT, lift_translT, lift_translT, MonObj.comp_mul, _root_.mul_assoc])

/- English proof (translation)
The claim follows from `end_ext (by rw [lift_translT, MonObj.comp_one, _root_.one_mul, Category.comp_id])`.
-/
theorem translT_one : translT A (1 : T ⟶ A) = 𝟙 _ :=
  end_ext (by rw [lift_translT, MonObj.comp_one, _root_.one_mul, Category.comp_id])

/- English proof (translation)
The claim follows from `lift_fst _ _`.
-/
theorem translT_fst (x : T ⟶ A) : translT A x ≫ fst T A = fst T A := lift_fst _ _

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact Category.id_comp _`. Consider the case `succ n ih => rw [pow_succ', End.mul_def, Category.assoc, hh, ih]`.
-/
theorem pow_fst (h : CategoryTheory.End (T ⊗ A)) (hh : h ≫ fst T A = fst T A) (n : ℕ) :
    (h ^ n : CategoryTheory.End (T ⊗ A)) ≫ fst T A = fst T A := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih => rw [pow_succ', End.mul_def, Category.assoc, hh, ih]

end Transl

/- English proof (translation)
Take `⟨P', g, hg, -, pm, -⟩` from `laws.polBaseChange S _ T.hom P`. Establish `hg' : IsPullback (snd T P.A).left (fst T P.A).left P.A.hom T.hom` using `(IsPullback.of_hasPullback T.hom P.A.hom).flip`. Set `e` to `hg.isoIsPullback _ _ hg'`. Establish `e₁ : e.hom ≫ (snd T P.A).left = g` using `hg.isoIsPullback_hom_fst _ _ hg'`. Establish `e₂ : e.hom ≫ (fst T P.A).left = P'.A.hom` using `hg.isoIsPullback_hom_snd _ _ hg'`.

Establish `e₃ : h.left ≫ (fst T P.A).left = (fst T P.A).left` using `congrArg (·.left) hfst`. Set `σ : P'.A ⟶ P'.A` to `Over.homMk (e.hom ≫ h.left ≫ e.inv) (by`. Rewrite using `[← e₂, Category.assoc, Category.assoc, e.inv_hom_id_assoc, e₃])`. Establish `hσ : σ.left ≫ e.hom = e.hom ≫ h.left`. Express the relevant statement in the definitionally equal form `(e.hom ≫ h.left ≫ e.inv) ≫ e.hom = _`.

Simplify using the standard rewrite rules. Establish `ex : ∀ {Z : Over S} (t : Z ⟶ T), ∃ ρ : (Over.mk t.left ⟶ P'.A) →* (Z ⟶ P.A), ∀ x, (lift t (ρ x)).left = x.left ≫ e.hom` using `fun {Z} t => by`. Set `c : Z ⟶ Over.mk ((Over.mk t.left).hom ≫ T.hom)` to `Over.homMk (𝟙 _) (by simp)`. Use `⟨MonoidHom.mk' (fun x => c ≫ toBase hg.w x) fun x y => by rw [pm, MonObj.comp_mul], fun x => ?_⟩` and prove the remaining obligations. Use `hg'.hom_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[← Over.comp_left, lift_snd, Category.assoc, e₁]`. Conclude with `Category.id_comp _`. Rewrite using `[← Over.comp_left, lift_fst, Category.assoc, e₂]`. Conclude with `(Over.w x).symm`. Establish `: IsMonHom σ` using `laws.rigidity _ _ _ P'.isAb P'.isAb σ (by`.

Take `⟨ρ, hρ⟩` from `ex (𝟙 T)`. Establish `hη : (1 : Over.mk (𝟙 T : T ⟶ T).left ⟶ P'.A) = η[P'.A]` using `(congrArg (· ≫ η[P'.A]) toUnit_unit).trans (Category.id_comp _)`. Establish `h1` using `hρ 1`. Rewrite `h1` using `[map_one, hη]`. Establish `h2 : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ h.left = (lift (𝟙 T) (1 : T ⟶ P.A)).left` using `congrArg (·.left) h0`.

Rewrite `h2` using `[h1]`. Use `Over.OverMorphism.ext ((cancel_mono e.hom).1 ?_)` and prove the remaining obligations. Rewrite using `[Over.comp_left, Category.assoc, hσ, ← Category.assoc]`. Conclude with `h2)`. Take `⟨ρ, hρ⟩` from `ex t`.

Establish `inj : ∀ a b : Z ⟶ P.A, lift t a = lift t b → a = b` using `fun a b hab => by`. Rewrite using `[← lift_snd t a, hab, lift_snd]`. Establish `sur : ∀ a : Z ⟶ P.A, ∃ x, ρ x = a` using `fun a => ⟨Over.homMk ((lift t a).left ≫ e.inv) (by`. Rewrite using `[← e₂, Category.assoc, e.inv_hom_id_assoc, ← Over.comp_left, lift_fst]`. Use the proof step `rfl),`.

Use `inj _ _ (Over.OverMorphism.ext ((hρ _).trans (by simp)))⟩`. Establish `key : ∀ x, lift t (ρ x) ≫ h ≫ snd _ _ = ρ (x ≫ σ)` using `fun x => inj _ _ (by`. Rewrite using `[← eq_lift hfst]`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Rewrite using `[hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, Category.assoc, hσ])`.

Take `⟨x, rfl⟩` from `sur u`. Take `⟨y, rfl⟩` from `sur v`. Rewrite using `[← map_mul, key, key, key, MonObj.mul_comp, map_mul]`.
-/
theorem map_mul_of_fix_origin (laws : Laws) {S : Scheme.{0}} (P : PolAV S) {T : Over S}
    (h : T ⊗ P.A ⟶ T ⊗ P.A) (hfst : h ≫ fst _ _ = fst _ _) (h0 : ptSecT P.A 1 ≫ h = ptSecT P.A 1)
    {Z : Over S} (t : Z ⟶ T) (u v : Z ⟶ P.A) :
    lift t (u * v) ≫ h ≫ snd _ _ = (lift t u ≫ h ≫ snd _ _) * (lift t v ≫ h ≫ snd _ _) := by
  obtain ⟨P', g, hg, -, pm, -⟩ := laws.polBaseChange S _ T.hom P
  have hg' : IsPullback (snd T P.A).left (fst T P.A).left P.A.hom T.hom :=
    (IsPullback.of_hasPullback T.hom P.A.hom).flip
  let e := hg.isoIsPullback _ _ hg'
  have e₁ : e.hom ≫ (snd T P.A).left = g := hg.isoIsPullback_hom_fst _ _ hg'
  have e₂ : e.hom ≫ (fst T P.A).left = P'.A.hom := hg.isoIsPullback_hom_snd _ _ hg'
  have e₃ : h.left ≫ (fst T P.A).left = (fst T P.A).left := congrArg (·.left) hfst
  let σ : P'.A ⟶ P'.A := Over.homMk (e.hom ≫ h.left ≫ e.inv) (by
    rw [← e₂, Category.assoc, Category.assoc, e.inv_hom_id_assoc, e₃])
  have hσ : σ.left ≫ e.hom = e.hom ≫ h.left := by
    change (e.hom ≫ h.left ≫ e.inv) ≫ e.hom = _
    simp
  have ex : ∀ {Z : Over S} (t : Z ⟶ T), ∃ ρ : (Over.mk t.left ⟶ P'.A) →* (Z ⟶ P.A),
      ∀ x, (lift t (ρ x)).left = x.left ≫ e.hom := fun {Z} t => by
    let c : Z ⟶ Over.mk ((Over.mk t.left).hom ≫ T.hom) := Over.homMk (𝟙 _) (by simp)
    refine ⟨MonoidHom.mk' (fun x => c ≫ toBase hg.w x) fun x y => by rw [pm, MonObj.comp_mul], fun x => ?_⟩
    refine hg'.hom_ext ?_ ?_
    · rw [← Over.comp_left, lift_snd, Category.assoc, e₁]
      exact Category.id_comp _
    · rw [← Over.comp_left, lift_fst, Category.assoc, e₂]
      exact (Over.w x).symm
  have : IsMonHom σ := laws.rigidity _ _ _ P'.isAb P'.isAb σ (by
    obtain ⟨ρ, hρ⟩ := ex (𝟙 T)
    have hη : (1 : Over.mk (𝟙 T : T ⟶ T).left ⟶ P'.A) = η[P'.A] :=
      (congrArg (· ≫ η[P'.A]) toUnit_unit).trans (Category.id_comp _)
    have h1 := hρ 1
    rw [map_one, hη] at h1
    have h2 : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ h.left = (lift (𝟙 T) (1 : T ⟶ P.A)).left :=
      congrArg (·.left) h0
    rw [h1] at h2
    refine Over.OverMorphism.ext ((cancel_mono e.hom).1 ?_)
    rw [Over.comp_left, Category.assoc, hσ, ← Category.assoc]
    exact h2)
  obtain ⟨ρ, hρ⟩ := ex t
  have inj : ∀ a b : Z ⟶ P.A, lift t a = lift t b → a = b := fun a b hab => by
    rw [← lift_snd t a, hab, lift_snd]
  have sur : ∀ a : Z ⟶ P.A, ∃ x, ρ x = a := fun a =>
    ⟨Over.homMk ((lift t a).left ≫ e.inv) (by
      rw [← e₂, Category.assoc, e.inv_hom_id_assoc, ← Over.comp_left, lift_fst]; rfl),
      inj _ _ (Over.OverMorphism.ext ((hρ _).trans (by simp)))⟩
  have key : ∀ x, lift t (ρ x) ≫ h ≫ snd _ _ = ρ (x ≫ σ) := fun x => inj _ _ (by
    rw [← eq_lift hfst]
    refine Over.OverMorphism.ext ?_
    rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, Category.assoc, hσ])
  obtain ⟨x, rfl⟩ := sur u
  obtain ⟨y, rfl⟩ := sur v
  rw [← map_mul, key, key, key, MonObj.mul_comp, map_mul]

/- English proof (translation)
Take `⟨a, ha⟩ : ∃ a, a = ptSecT P.A 1 ≫ ψ ≫ snd _ _` from `⟨_, rfl⟩`. Take `⟨h, hh⟩ : ∃ h : CategoryTheory.End (Over.mk p ⊗ P.A), h = ψ ≫ translT P.A a⁻¹` from `⟨_, rfl⟩`. Establish `hfst : h ≫ fst _ _ = fst _ _` using `by rw [hh, Category.assoc, translT_fst, hψ]`. Establish `h0 : ptSecT P.A 1 ≫ h = ptSecT P.A 1`. Rewrite using `[hh, ← Category.assoc, ptSecT, eq_lift hψ, lift_translT, Category.id_comp, ← ptSecT, ← ptSecT, ← ha, inv_mul_cancel]`.

Establish `hψh : ψ = h ≫ translT P.A a`. Rewrite using `[hh, Category.assoc, translT_comp, mul_inv_cancel, translT_one, Category.comp_id]`. Establish `hmul` using `fun {Z} (t : Z ⟶ Over.mk p) => map_mul_of_fix_origin hL.1 P h hfst h0 t`. Establish `hcomm : ∀ x, translT P.A x ≫ h = h ≫ translT P.A (ptSecT P.A x ≫ h ≫ snd _ _)` using `fun x => end_ext (by`. Rewrite using `[← Category.assoc, lift_translT, eq_lift hfst, hmul, ← Category.assoc (lift _ _) h (translT _ _), eq_lift hfst, lift_translT, ptSecT, ← Category.assoc (fst _ _), comp_lift, Category.comp_id])`.

Establish `hpow : ∀ n : ℕ, ∃ x, (ψ ^ n : CategoryTheory.End _) = (h ^ n : CategoryTheory.End _) ≫ translT P.A x` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨1, by rw [translT_one, Category.comp_id, pow_zero, pow_zero]⟩`. Consider the case `succ n ih`. Take `⟨x, hx⟩` from `ih`.

Use `⟨a * (ptSecT P.A x ≫ h ≫ snd _ _), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ', pow_succ', End.mul_def, End.mul_def, hx, ← translT_comp, Category.assoc, Category.assoc, ← Category.assoc h, ← hcomm, Category.assoc, ← hψh]`. Establish `h0' : ∀ n : ℕ, ptSecT P.A 1 ≫ (h ^ n : CategoryTheory.End _) = ptSecT P.A 1` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => exact Category.comp_id _`.

Consider the case `succ n ih => rw [pow_succ', End.mul_def, ← Category.assoc, ih, h0]`. Establish `hhN : h ^ N = 1`. Take `⟨x, hx⟩` from `hpow N`. Establish `e` using `congrArg (ptSecT P.A 1 ≫ · ≫ snd _ _) hx`. Simplify using `only [hord] at e`.

Rewrite `e` using `[End.one_def, Category.id_comp, ← Category.assoc, ← Category.assoc, h0', ptSecT, lift_translT, lift_snd, lift_snd, Category.id_comp, _root_.mul_one]`. Rewrite `hx` using `[← e, translT_one, Category.comp_id, hord]`. Conclude with `hx.symm`. Set `φ : (Over.mk p ⟶ P.A) →* (Over.mk p ⟶ P.A)` to `MonoidHom.mk' (fun x => ptSecT P.A x ≫ h ≫ snd _ _) (hmul (𝟙 _))`. Set `f : {x : Over.mk p ⟶ P.A // x ^ 3 = 1} → {x : Over.mk p ⟶ P.A // x ^ 3 = 1}` to `fun x => ⟨φ x.1, by rw [← map_pow, x.2, map_one]⟩`.

Establish `hf : ∀ (n : ℕ) x, ptSecT P.A (f^[n] x).1 = ptSecT P.A x.1 ≫ (h ^ n : CategoryTheory.End _)` using `fun n x => by`. Proceed by induction on `n with`. Consider the case `zero => exact (Category.comp_id _).symm`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', pow_succ', End.mul_def, ← Category.assoc, ← ih]`.

Conclude with `(eq_lift hfst _ _).symm`. Establish `hinj : Function.Injective f`. Take `⟨n, rfl⟩ : ∃ n, N = n + 1` from `⟨N - 1, by omega⟩`. Use `Function.LeftInverse.injective (g := f^[n]) fun x => Subtype.ext ?_` and prove the remaining obligations. Establish `e` using `congrArg (· ≫ snd _ _) (hf (n + 1) x)`.

Simplify using `only [hhN] at e`. Rewrite `e` using `[End.one_def, Category.comp_id, ptSecT, ptSecT, lift_snd, lift_snd]`. Then use the resulting hypothesis. Set `π : Equiv.Perm _` to `Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)`. Establish `hπ : π ^ m = 1`. Take `⟨c, rfl⟩` from `hm`.

Rewrite using `[pow_mul, pow_card_eq_one', one_pow]`. Establish `h1 : h ^ m = 1` using `FiniteOrderFix.eq_one_of_finite_order_of_fix_three_torsion hL S P F p (h ^ m) (pow_fst h hfst m) (h0' m) ⟨N, hN, by rw [← pow_mul, mul_comm, pow_mul, hhN, one_pow]⟩ fun x hx => by`. Establish `e : f^[m] ⟨x, hx⟩ = ⟨x, hx⟩`. Use `congrArg (fun s : Equiv.Perm _ => s ⟨x, hx⟩) hπ` as an intermediate fact. Simplify using `only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id] at this`.

Conclude with `this`. Rewrite using `[← hf m ⟨x, hx⟩, e]`. Take `⟨x, hx⟩` from `hpow m`. Conclude with `⟨x, by rw [hx, h1, End.one_def, Category.id_comp]⟩`.
-/
theorem exists_pow_eq_translT (hL : LL) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F : Type} [Field F]
    [IsAlgClosed F] [CharZero F] (p : Spec (CommRingCat.of F) ⟶ S)
    [Finite {x : Over.mk p ⟶ P.A // x ^ 3 = 1}] (ψ : CategoryTheory.End (Over.mk p ⊗ P.A))
    (hψ : ψ ≫ fst _ _ = fst _ _) {N : ℕ} (hN : 1 ≤ N) (hord : ψ ^ N = 1) {m : ℕ}
    (hm : Nat.card (Equiv.Perm {x : Over.mk p ⟶ P.A // x ^ 3 = 1}) ∣ m) :
    ∃ x : Over.mk p ⟶ P.A, (ψ ^ m : CategoryTheory.End _) = translT P.A x := by
  obtain ⟨a, ha⟩ : ∃ a, a = ptSecT P.A 1 ≫ ψ ≫ snd _ _ := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : CategoryTheory.End (Over.mk p ⊗ P.A), h = ψ ≫ translT P.A a⁻¹ := ⟨_, rfl⟩
  have hfst : h ≫ fst _ _ = fst _ _ := by rw [hh, Category.assoc, translT_fst, hψ]
  have h0 : ptSecT P.A 1 ≫ h = ptSecT P.A 1 := by
    rw [hh, ← Category.assoc, ptSecT, eq_lift hψ, lift_translT, Category.id_comp, ← ptSecT, ← ptSecT, ← ha,
      inv_mul_cancel]
  have hψh : ψ = h ≫ translT P.A a := by
    rw [hh, Category.assoc, translT_comp, mul_inv_cancel, translT_one, Category.comp_id]
  have hmul := fun {Z} (t : Z ⟶ Over.mk p) => map_mul_of_fix_origin hL.1 P h hfst h0 t
  have hcomm : ∀ x, translT P.A x ≫ h = h ≫ translT P.A (ptSecT P.A x ≫ h ≫ snd _ _) := fun x => end_ext (by
    rw [← Category.assoc, lift_translT, eq_lift hfst, hmul, ← Category.assoc (lift _ _) h (translT _ _), eq_lift hfst,
      lift_translT, ptSecT, ← Category.assoc (fst _ _), comp_lift, Category.comp_id])
  have hpow : ∀ n : ℕ, ∃ x, (ψ ^ n : CategoryTheory.End _) = (h ^ n : CategoryTheory.End _) ≫ translT P.A x :=
    fun n => by
    induction n with
    | zero => exact ⟨1, by rw [translT_one, Category.comp_id, pow_zero, pow_zero]⟩
    | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      refine ⟨a * (ptSecT P.A x ≫ h ≫ snd _ _), ?_⟩
      rw [pow_succ', pow_succ', End.mul_def, End.mul_def, hx, ← translT_comp, Category.assoc, Category.assoc,
        ← Category.assoc h, ← hcomm, Category.assoc, ← hψh]
  have h0' : ∀ n : ℕ, ptSecT P.A 1 ≫ (h ^ n : CategoryTheory.End _) = ptSecT P.A 1 := fun n => by
    induction n with
    | zero => exact Category.comp_id _
    | succ n ih => rw [pow_succ', End.mul_def, ← Category.assoc, ih, h0]
  have hhN : h ^ N = 1 := by
    obtain ⟨x, hx⟩ := hpow N
    have e := congrArg (ptSecT P.A 1 ≫ · ≫ snd _ _) hx
    simp only [hord] at e
    rw [End.one_def, Category.id_comp, ← Category.assoc, ← Category.assoc, h0', ptSecT, lift_translT, lift_snd,
      lift_snd, Category.id_comp, _root_.mul_one] at e
    rw [← e, translT_one, Category.comp_id, hord] at hx
    exact hx.symm
  let φ : (Over.mk p ⟶ P.A) →* (Over.mk p ⟶ P.A) :=
    MonoidHom.mk' (fun x => ptSecT P.A x ≫ h ≫ snd _ _) (hmul (𝟙 _))
  let f : {x : Over.mk p ⟶ P.A // x ^ 3 = 1} → {x : Over.mk p ⟶ P.A // x ^ 3 = 1} :=
    fun x => ⟨φ x.1, by rw [← map_pow, x.2, map_one]⟩
  have hf : ∀ (n : ℕ) x, ptSecT P.A (f^[n] x).1 = ptSecT P.A x.1 ≫ (h ^ n : CategoryTheory.End _) := fun n x => by
    induction n with
    | zero => exact (Category.comp_id _).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ', End.mul_def, ← Category.assoc, ← ih]
      exact (eq_lift hfst _ _).symm
  have hinj : Function.Injective f := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    refine Function.LeftInverse.injective (g := f^[n]) fun x => Subtype.ext ?_
    have e := congrArg (· ≫ snd _ _) (hf (n + 1) x)
    simp only [hhN] at e
    rwa [End.one_def, Category.comp_id, ptSecT, ptSecT, lift_snd, lift_snd] at e
  let π : Equiv.Perm _ := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hπ : π ^ m = 1 := by
    obtain ⟨c, rfl⟩ := hm
    rw [pow_mul, pow_card_eq_one', one_pow]
  have h1 : h ^ m = 1 := FiniteOrderFix.eq_one_of_finite_order_of_fix_three_torsion hL S P F p (h ^ m)
    (pow_fst h hfst m) (h0' m) ⟨N, hN, by rw [← pow_mul, mul_comm, pow_mul, hhN, one_pow]⟩ fun x hx => by
      have e : f^[m] ⟨x, hx⟩ = ⟨x, hx⟩ := by
        have := congrArg (fun s : Equiv.Perm _ => s ⟨x, hx⟩) hπ
        simp only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id] at this
        exact this
      rw [← hf m ⟨x, hx⟩, e]
  obtain ⟨x, hx⟩ := hpow m
  exact ⟨x, by rw [hx, h1, End.one_def, Category.id_comp]⟩

attribute [local instance] TorusExt.gtGroup

open TorusExt in

/- English proof (translation)
Establish `hg : p.g = m • g'` using `(isNsmul_iff_eq _ _ _).1 hg'`. Establish `hι : (k * m) • g' = iota hB F p.y` using `by rw [mul_nsmul', ← hg, qk_nsmul hB]`. Set `r : ℕ → QkPt D F (k * m)` to `fun j => qkMk hB (j • p.y) (j • g') (by`. Rewrite using `[smul_comm, hι, map_nsmul])`. Take `⟨τ, h1⟩` from `ex (r 1)`.

Establish `h0 : Ind (r 0) 1` using `(comp (r 1) (r 0) (r 0) _ 1 h1).2.2.2 (zero_nsmul _) ((isZero_iff_eq _).2 (zero_nsmul _))`. Establish `hj : ∀ j : ℕ, Ind (r j) (τ ^ j)` using `fun j => by`. Proceed by induction on `j with`. Consider the case `zero => rwa [pow_zero]`. Consider the case `succ j ih`.

Rewrite using `[pow_succ']`. Use `(comp (r j) (r 1) (r (j + 1)) _ _ ih).1 h1 ?_` and prove the remaining obligations. Establish `e : r (j + 1) = qkAdd hB (r j) (r 1)` using `qk_ext (add_nsmul _ _ _) (add_nsmul _ _ _)`. Rewrite using `[e]`. Conclude with `qkAdd_qkAdd hB _ _`.

Use `⟨τ, _, h1, (comp (r (k * m)) (r 0) (r 0) _ _ (hj _)).2.2.1 ((comp (r 0) (r (k * m)) (r 0) _ 1 h0).2.1 ((equiv_iff hB _ _).2 ⟨p.y, ?_, ?_⟩)), (comp (r m) (r 0) (r 0) _ _ (hψ (r m) rfl hg.symm)).2.2.1 (hj m)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(k * m) • p.y = 0 • p.y + (k * m) • p.y`. Rewrite using `[zero_nsmul, zero_add]`. Express the relevant statement in the definitionally equal form `(k * m) • g' = 0 • g' + _`. Rewrite using `[zero_nsmul, zero_add, hι]`.
-/
theorem eq_pow_of_rel {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k m : ℕ} (p : QkPt D F k) (g' : GtPtF D F) (hg' : GtPtF.IsNsmul m g' p.g)
    {E : Type} [Monoid E] (Ind : QkPt D F (k * m) → E → Prop)
    (comp : ∀ p p' p'' ψ ψ', Ind p ψ → (Ind p' ψ' → QkAdd p p' p'' → Ind p'' (ψ' * ψ)) ∧
      (QkPt.Equiv D F p p' → Ind p' ψ) ∧ (Ind p ψ' → ψ = ψ') ∧ (p'.y = 0 → p'.g.IsZero → Ind p' 1))
    (ex : ∀ q, ∃ τ, Ind q τ) (ψ : E) (hψ : ∀ q : QkPt D F (k * m), q.y = m • p.y → q.g = p.g → Ind q ψ) :
    ∃ τ q, Ind q τ ∧ τ ^ (k * m) = 1 ∧ ψ = τ ^ m := by
  have hg : p.g = m • g' := (isNsmul_iff_eq _ _ _).1 hg'
  have hι : (k * m) • g' = iota hB F p.y := by rw [mul_nsmul', ← hg, qk_nsmul hB]
  let r : ℕ → QkPt D F (k * m) := fun j => qkMk hB (j • p.y) (j • g') (by
    rw [smul_comm, hι, map_nsmul])
  obtain ⟨τ, h1⟩ := ex (r 1)
  have h0 : Ind (r 0) 1 :=
    (comp (r 1) (r 0) (r 0) _ 1 h1).2.2.2 (zero_nsmul _) ((isZero_iff_eq _).2 (zero_nsmul _))
  have hj : ∀ j : ℕ, Ind (r j) (τ ^ j) := fun j => by
    induction j with
    | zero => rwa [pow_zero]
    | succ j ih =>
      rw [pow_succ']
      refine (comp (r j) (r 1) (r (j + 1)) _ _ ih).1 h1 ?_
      have e : r (j + 1) = qkAdd hB (r j) (r 1) := qk_ext (add_nsmul _ _ _) (add_nsmul _ _ _)
      rw [e]
      exact qkAdd_qkAdd hB _ _
  refine ⟨τ, _, h1, (comp (r (k * m)) (r 0) (r 0) _ _ (hj _)).2.2.1
    ((comp (r 0) (r (k * m)) (r 0) _ 1 h0).2.1 ((equiv_iff hB _ _).2 ⟨p.y, ?_, ?_⟩)),
    (comp (r m) (r 0) (r 0) _ _ (hψ (r m) rfl hg.symm)).2.2.1 (hj m)⟩
  · change (k * m) • p.y = 0 • p.y + (k * m) • p.y
    rw [zero_nsmul, zero_add]
  · change (k * m) • g' = 0 • g' + _
    rw [zero_nsmul, zero_add, hι]

/- English proof (translation)
Introduce `hL R _ _ _ I hR D A G _ _ hG U F _ _ _ k hk p`. Establish `: CharZero F` using `charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective`. Establish `hcard` using `(hL.1.mulN _ A 3 (by omega)).2.2.2.2 F (jFK (R := R) F) (by norm_num)`. Establish `: Finite {x : Over.mk (jFK (R` using `R) F) ⟶ A.A // x ^ 3 = 1} := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)`. Take `⟨m, hm4, hm⟩ : ∃ m, 4 ≤ m ∧ Nat.card (Equiv.Perm {x : Over.mk (jFK (R` from `R) F) ⟶ A.A // x ^ 3 = 1}) ∣ m := ⟨4 * _, Nat.le_mul_of_pos_right _ Nat.card_pos, Dvd.intro_left _ rfl⟩`.

Establish `hN : 4 ≤ k * m` using `hm4.trans (Nat.le_mul_of_pos_left _ hk)`. Take `⟨g', hg'⟩` from `(gt_onto_divisible_kernel hL R I hR D F).2.1 m (by omega) p.g`. Take `⟨ψ, hψ⟩` from `GlobalTheory.T.exists_automorphism_inducing_frobenius_all_degrees hL R I hR D A G hG U F k hk p`. Take `⟨τ, q, h1, hord, e⟩` from `eq_pow_of_rel D.tau_bimult p g' hg' (E := CategoryTheory.End (TFK (R := R) F ⊗ A.A)) (IndAt U.toUnifPre F (k * m)) (fun a b c s t hs => by`. Take `⟨c₁, c₂, c₃, c₄⟩` from `GlobalTheory.T.indAt_comp_equiv_unique_id hL R I hR D A G hG U F (k * m) (by omega) a b c s t hs`.

Conclude with `⟨c₁, c₂, c₃ hN, c₄⟩)`. Use the proof step `(fun q => by`. Take `⟨χ, hχ⟩` from `GlobalTheory.T.exists_automorphism_inducing_frobenius_all_degrees hL R I hR D A G hG U F (k * m) (by omega) q`. Conclude with `⟨χ.hom, hχ 1 (k * m) le_rfl (_root_.mul_one _).symm q (one_nsmul _).symm rfl⟩)`. Use the proof step `ψ.hom (hψ m _ (by omega) rfl)`.

Take `⟨x, hx⟩` from `exists_pow_eq_translT hL A (jFK (R := R) F) τ h1.1 (by omega : 1 ≤ k * m) hord hm`. Establish `e' : ψ.hom = translT A.A x` using `e.trans hx`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[← e']`. Conclude with `hψ`.
-/
theorem exists_translT_indAt :
    LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q (translT A.A x) := by
  intro hL R _ _ _ I hR D A G _ _ hG U F _ _ _ k hk p
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have hcard := (hL.1.mulN _ A 3 (by omega)).2.2.2.2 F (jFK (R := R) F) (by norm_num)
  have : Finite {x : Over.mk (jFK (R := R) F) ⟶ A.A // x ^ 3 = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨m, hm4, hm⟩ : ∃ m, 4 ≤ m ∧
      Nat.card (Equiv.Perm {x : Over.mk (jFK (R := R) F) ⟶ A.A // x ^ 3 = 1}) ∣ m :=
    ⟨4 * _, Nat.le_mul_of_pos_right _ Nat.card_pos, Dvd.intro_left _ rfl⟩
  have hN : 4 ≤ k * m := hm4.trans (Nat.le_mul_of_pos_left _ hk)
  obtain ⟨g', hg'⟩ := (gt_onto_divisible_kernel hL R I hR D F).2.1 m (by omega) p.g
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_automorphism_inducing_frobenius_all_degrees hL R I hR D A G hG U F k hk p
  obtain ⟨τ, q, h1, hord, e⟩ := eq_pow_of_rel D.tau_bimult p g' hg'
    (E := CategoryTheory.End (TFK (R := R) F ⊗ A.A)) (IndAt U.toUnifPre F (k * m))
    (fun a b c s t hs => by
      obtain ⟨c₁, c₂, c₃, c₄⟩ := GlobalTheory.T.indAt_comp_equiv_unique_id hL R I hR D A G hG U F (k * m) (by omega) a b c s t hs
      exact ⟨c₁, c₂, c₃ hN, c₄⟩)
    (fun q => by
      obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_automorphism_inducing_frobenius_all_degrees hL R I hR D A G hG U F (k * m) (by omega) q
      exact ⟨χ.hom, hχ 1 (k * m) le_rfl (_root_.mul_one _).symm q (one_nsmul _).symm rfl⟩)
    ψ.hom (hψ m _ (by omega) rfl)
  obtain ⟨x, hx⟩ := exists_pow_eq_translT hL A (jFK (R := R) F) τ h1.1 (by omega : 1 ≤ k * m) hord hm
  have e' : ψ.hom = translT A.A x := e.trans hx
  refine ⟨x, ?_⟩
  rw [← e']
  exact hψ

end GlobalTheory.InducedTranslation
