import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTorsionFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevSurjOpen

/- English proof (translation)
The claim follows from `| 0 => by have h := hadd 0 0 rw [add_zero] at h rw [zero_smul, pow_zero] exact mul_eq_left.mp h.symm | n + 1 => by rw [succ_nsmul, hadd, lev_nsmul lev hadd a n, pow_succ]`.
-/
theorem lev_nsmul {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : Type} [AddCommGroup L]
    (lev : L → (𝟙_ (Over S) ⟶ G)) (hadd : ∀ a b, lev (a + b) = lev a * lev b) (a : L) :
    ∀ n : ℕ, lev (n • a) = lev a ^ n
  | 0 => by
    have h := hadd 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.mp h.symm
  | n + 1 => by rw [succ_nsmul, hadd, lev_nsmul lev hadd a n, pow_succ]

/- English proof (translation)
Use `haveI : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))`. Rewrite using `[Set.range_subset_iff]`. Use `⟨fun H => H _, fun H p => ?_⟩` and prove the remaining obligations. Establish `: p = (⊥ : PrimeSpectrum k)` using `Subsingleton.elim (α := Sp k) p (⊥ : PrimeSpectrum k)`. Rewrite using `[this]`.

Conclude with `H`.
-/
theorem range_subset_iff_pt {k : Type} [Field k] {X : Scheme.{0}} (y : Sp k ⟶ X) (O : Set X) :
    Set.range y.base ⊆ O ↔ y.base (⊥ : PrimeSpectrum k) ∈ O := by
  haveI : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  rw [Set.range_subset_iff]
  refine ⟨fun H => H _, fun H p => ?_⟩
  have : p = (⊥ : PrimeSpectrum k) := Subsingleton.elim (α := Sp k) p (⊥ : PrimeSpectrum k)
  rw [this]
  exact H

/- English proof (translation)
The claim follows from `pullback.hom_ext h (toUnit_unique _ _)`.
-/
theorem torsion_hom_ext {S : Scheme.{0}} {G : Over S} [GrpObj G] {M : ℕ} {X : Over S} (u v : X ⟶ torsion G M)
    (h : u ≫ torsion.ι G M = v ≫ torsion.ι G M) : u = v :=
  pullback.hom_ext h (toUnit_unique _ _)

/- English proof (translation)
Introduce `S _ M t G _ _ h lev hab hM hadd htors k _ _ x₀ hx₀`. Use `haveI := hab`. Establish `hM0 : M ≠ 0` using `by omega`. Establish `hu : IsUnit (M : Γ(S, ⊤))`. Simplify using `using (GlobalTheory.SiegelTor.isUnit_natCast hM0).map ((Scheme.ΓSpecIso (CommRingCat.of (cycAway M))).inv ≫ t.appTop).hom`.

Take `⟨-, hfin, het⟩` from `GlobalTheory.GrpTangent.finiteEtale_mulN_torsion G hu`. Use `haveI := hfin`. Use `haveI := het`. Set `ℓ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ torsion G M)` to `fun a => GlobalTheory.TorsionFamily.torsionLift G (lev a) M (htors a)`. Establish `hℓ : ∀ a, ℓ a ≫ torsion.ι G M = lev a` using `fun a => GlobalTheory.TorsionFamily.torsionLift_ι _ _ _ _`.

Establish `hcl : ∀ a, GlobalTheory.LevCover.ClopenCond (torsion G M) fun _ y => y ≫ 𝟙 (torsion G M) = y ≫ (toUnit (torsion G M) ≫ ℓ a)` using `fun a => GlobalTheory.LevCover.clopenCond_eq _ _`. Use `choose U hUc hU using hcl`. Take `⟨κ, _, q, hq⟩` from `GlobalTheory.LevCover.exists_finite_mod (Fin h ⊕ Fin h → ℤ) (n := M) (by omega)`. Set `rep : Set.range q → (Fin h ⊕ Fin h → ℤ)` to `fun c => c.2.choose`. Establish `hrep : ∀ a, lev (rep ⟨q a, a, rfl⟩) = lev a`.

Introduce `a`. Take `⟨c, hc⟩` from `hq _ _ ((⟨q a, a, rfl⟩ : Set.range q).2.choose_spec)`. Establish `e` using `congrArg lev hc`. Rewrite `e` using `[hadd, lev_nsmul lev hadd, htors, _root_.mul_one]`. Conclude with `e.symm`.

Set `Zs : Set (torsion G M).left` to `⋃ c : Set.range q, (U (rep c) : Set (torsion G M).left)`. Establish `hZo : IsOpen Zs` using `isOpen_iUnion fun c => (U _).isOpen`. Establish `hZc : IsClosed Zs` using `isClosed_iUnion_of_finite fun c => hUc _`. Set `C : (torsion G M).left.Opens` to `⟨Zsᶜ, hZc.isOpen_compl⟩`. Take `⟨V, i, hVf, hVe, -, hV⟩` from `GlobalTheory.LevCover.exists_sub C hZo.isClosed_compl`.

Use `haveI := hVf`. Use `haveI := hVe`. Use `haveI : IsFinite (𝟙_ (Over S)).hom := by show IsFinite (𝟙 S); infer_instance`. Use `haveI : Etale (𝟙_ (Over S)).hom := by show Etale (𝟙 S); infer_instance`. Take `⟨U₀, hU₀c, hU₀⟩` from `GlobalTheory.LevCover.exists_image (toUnit V)`.

Set `U₁ : Set S` to `(U₀ : Set (𝟙_ (Over S)).left)`. Establish `hU₁c : IsClosed U₁` using `hU₀c`. Establish `key : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ U₁ ↔ Nonempty (Over.mk x ⟶ V)`. Introduce `k' _ _ x`. Establish `H` using `hU₀ k' x (toUnit _)`.

Establish `hz : (toUnit (Over.mk x) : Over.mk x ⟶ 𝟙_ (Over S)).left = x`. Simplify using `using Over.w (toUnit (Over.mk x))`. Rewrite `H` using `[hz]`. Conclude with `H.trans ⟨fun ⟨w, _⟩ => ⟨w⟩, fun ⟨w⟩ => ⟨w, toUnit_unique _ _⟩⟩`. Use `⟨⟨U₁ᶜ, hU₁c.isOpen_compl⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce `_ ⟨p, hp⟩ hpU`. Substitute `hp` using the available equality. Establish `hr : Set.range x₀.base ⊆ U₁`. Rewrite using `[range_subset_iff_pt]`. Establish `: p = (⊥ : PrimeSpectrum k)` using `@Subsingleton.elim (Sp k) (inferInstanceAs (Subsingleton (PrimeSpectrum k))) p (⊥ : PrimeSpectrum k)`.

Rewrite using `[← this]`. Conclude with `hpU`. Take `⟨w⟩` from `(key k x₀).1 hr`. Set `y` to `w ≫ i`. Establish `hy : Set.range y.left.base ⊆ (C : Set (torsion G M).left)` using `(hV _ y).2 ⟨w, rfl⟩`.

Establish `hg : (y ≫ torsion.ι G M) ^ M = 1`. Rewrite using `[← MonObj.comp_pow, GlobalTheory.TorsionFamily.torsion_ι_pow, MonObj.comp_one]`. Take `⟨a, ha⟩` from `hx₀ _ hg`. Establish `e1 : (toUnit (Over.mk x₀) ≫ ℓ (rep ⟨q a, a, rfl⟩)) ≫ torsion.ι G M = toUnit _ ≫ lev a`. Rewrite using `[Category.assoc, hℓ, hrep]`.

Establish `e2 : y ≫ torsion.ι G M = toUnit _ ≫ lev a` using `ha.symm`. Establish `hy' : y = toUnit _ ≫ ℓ (rep ⟨q a, a, rfl⟩)` using `torsion_hom_ext _ _ (e2.trans e1.symm)`. Establish `hin : Set.range y.left.base ⊆ (U (rep ⟨q a, a, rfl⟩) : Set (torsion G M).left)`. Use `(hU _ _ y).1 ?_` and prove the remaining obligations. Use `show y ≫ 𝟙 _ = y ≫ toUnit _ ≫ ℓ _`.

Rewrite using `[Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit _), ← hy']`. Establish `h1` using `(range_subset_iff_pt _ _).1 hy`. Establish `h2` using `(range_subset_iff_pt _ _).1 hin`. Conclude with `h1 (Set.mem_iUnion.2 ⟨⟨q a, a, rfl⟩, h2⟩)`. Introduce `k' _ _ x hx g hg`.

Set `y` to `GlobalTheory.TorsionFamily.torsionLift G g M hg`. Establish `hnC : ¬ Set.range y.left.base ⊆ (C : Set (torsion G M).left)`. Introduce `H`. Take `⟨w, -⟩` from `(hV _ y).1 H`. Establish `hr` using `(key k' x).2 ⟨w⟩`.

Establish `h1` using `(range_subset_iff_pt _ _).1 hr`. Establish `h2` using `(range_subset_iff_pt _ _).1 hx`. Conclude with `h2 h1`. Rewrite `hnC` using `[range_subset_iff_pt]`. Establish `hZ : y.left.base (⊥ : PrimeSpectrum k') ∈ Zs` using `not_not.1 hnC`.

Take `⟨c, hc⟩` from `Set.mem_iUnion.1 hZ`. Establish `hin : Set.range y.left.base ⊆ (U (rep c) : Set (torsion G M).left)` using `(range_subset_iff_pt _ _).2 hc`. Establish `e : y ≫ 𝟙 _ = y ≫ toUnit _ ≫ ℓ (rep c)` using `(hU _ _ y).2 hin`. Rewrite `e` using `[Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit _)]`. Use `⟨rep c, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hℓ, ← Category.assoc, ← e]`. Conclude with `GlobalTheory.TorsionFamily.torsionLift_ι _ _ _ _`.
-/
theorem exists_open_levSurj : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ g : Over.mk x₀ ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ g : Over.mk x ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g := by
  intro S _ M t G _ _ h lev hab hM hadd htors k _ _ x₀ hx₀
  haveI := hab
  have hM0 : M ≠ 0 := by omega
  have hu : IsUnit (M : Γ(S, ⊤)) := by
    simpa using (GlobalTheory.SiegelTor.isUnit_natCast hM0).map
      ((Scheme.ΓSpecIso (CommRingCat.of (cycAway M))).inv ≫ t.appTop).hom
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion G hu
  haveI := hfin
  haveI := het
  let ℓ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ torsion G M) := fun a =>
    GlobalTheory.TorsionFamily.torsionLift G (lev a) M (htors a)
  have hℓ : ∀ a, ℓ a ≫ torsion.ι G M = lev a := fun a => GlobalTheory.TorsionFamily.torsionLift_ι _ _ _ _

  have hcl : ∀ a, GlobalTheory.LevCover.ClopenCond (torsion G M)
      fun _ y => y ≫ 𝟙 (torsion G M) = y ≫ (toUnit (torsion G M) ≫ ℓ a) :=
    fun a => GlobalTheory.LevCover.clopenCond_eq _ _
  choose U hUc hU using hcl
  obtain ⟨κ, _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod (Fin h ⊕ Fin h → ℤ) (n := M) (by omega)
  let rep : Set.range q → (Fin h ⊕ Fin h → ℤ) := fun c => c.2.choose
  have hrep : ∀ a, lev (rep ⟨q a, a, rfl⟩) = lev a := by
    intro a
    obtain ⟨c, hc⟩ := hq _ _ ((⟨q a, a, rfl⟩ : Set.range q).2.choose_spec)
    have e := congrArg lev hc
    rw [hadd, lev_nsmul lev hadd, htors, _root_.mul_one] at e
    exact e.symm

  let Zs : Set (torsion G M).left := ⋃ c : Set.range q, (U (rep c) : Set (torsion G M).left)
  have hZo : IsOpen Zs := isOpen_iUnion fun c => (U _).isOpen
  have hZc : IsClosed Zs := isClosed_iUnion_of_finite fun c => hUc _
  let C : (torsion G M).left.Opens := ⟨Zsᶜ, hZc.isOpen_compl⟩
  obtain ⟨V, i, hVf, hVe, -, hV⟩ := GlobalTheory.LevCover.exists_sub C hZo.isClosed_compl
  haveI := hVf
  haveI := hVe
  haveI : IsFinite (𝟙_ (Over S)).hom := by show IsFinite (𝟙 S); infer_instance
  haveI : Etale (𝟙_ (Over S)).hom := by show Etale (𝟙 S); infer_instance

  obtain ⟨U₀, hU₀c, hU₀⟩ := GlobalTheory.LevCover.exists_image (toUnit V)
  let U₁ : Set S := (U₀ : Set (𝟙_ (Over S)).left)
  have hU₁c : IsClosed U₁ := hU₀c
  have key : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S),
      Set.range x.base ⊆ U₁ ↔ Nonempty (Over.mk x ⟶ V) := by
    intro k' _ _ x
    have H := hU₀ k' x (toUnit _)
    have hz : (toUnit (Over.mk x) : Over.mk x ⟶ 𝟙_ (Over S)).left = x := by
      simpa using Over.w (toUnit (Over.mk x))
    rw [hz] at H
    exact H.trans ⟨fun ⟨w, _⟩ => ⟨w⟩, fun ⟨w⟩ => ⟨w, toUnit_unique _ _⟩⟩
  refine ⟨⟨U₁ᶜ, hU₁c.isOpen_compl⟩, ?_, ?_⟩
  · intro _ ⟨p, hp⟩ hpU
    subst hp
    have hr : Set.range x₀.base ⊆ U₁ := by
      rw [range_subset_iff_pt]
      have : p = (⊥ : PrimeSpectrum k) :=
        @Subsingleton.elim (Sp k) (inferInstanceAs (Subsingleton (PrimeSpectrum k))) p (⊥ : PrimeSpectrum k)
      rw [← this]
      exact hpU
    obtain ⟨w⟩ := (key k x₀).1 hr
    let y := w ≫ i
    have hy : Set.range y.left.base ⊆ (C : Set (torsion G M).left) := (hV _ y).2 ⟨w, rfl⟩
    have hg : (y ≫ torsion.ι G M) ^ M = 1 := by
      rw [← MonObj.comp_pow, GlobalTheory.TorsionFamily.torsion_ι_pow, MonObj.comp_one]
    obtain ⟨a, ha⟩ := hx₀ _ hg
    have e1 : (toUnit (Over.mk x₀) ≫ ℓ (rep ⟨q a, a, rfl⟩)) ≫ torsion.ι G M = toUnit _ ≫ lev a := by
      rw [Category.assoc, hℓ, hrep]
    have e2 : y ≫ torsion.ι G M = toUnit _ ≫ lev a := ha.symm
    have hy' : y = toUnit _ ≫ ℓ (rep ⟨q a, a, rfl⟩) := torsion_hom_ext _ _ (e2.trans e1.symm)
    have hin : Set.range y.left.base ⊆ (U (rep ⟨q a, a, rfl⟩) : Set (torsion G M).left) := by
      refine (hU _ _ y).1 ?_
      show y ≫ 𝟙 _ = y ≫ toUnit _ ≫ ℓ _
      rw [Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit _), ← hy']
    have h1 := (range_subset_iff_pt _ _).1 hy
    have h2 := (range_subset_iff_pt _ _).1 hin
    exact h1 (Set.mem_iUnion.2 ⟨⟨q a, a, rfl⟩, h2⟩)
  · intro k' _ _ x hx g hg
    let y := GlobalTheory.TorsionFamily.torsionLift G g M hg
    have hnC : ¬ Set.range y.left.base ⊆ (C : Set (torsion G M).left) := by
      intro H
      obtain ⟨w, -⟩ := (hV _ y).1 H
      have hr := (key k' x).2 ⟨w⟩
      have h1 := (range_subset_iff_pt _ _).1 hr
      have h2 := (range_subset_iff_pt _ _).1 hx
      exact h2 h1
    rw [range_subset_iff_pt] at hnC
    have hZ : y.left.base (⊥ : PrimeSpectrum k') ∈ Zs := not_not.1 hnC
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hZ
    have hin : Set.range y.left.base ⊆ (U (rep c) : Set (torsion G M).left) :=
      (range_subset_iff_pt _ _).2 hc
    have e : y ≫ 𝟙 _ = y ≫ toUnit _ ≫ ℓ (rep c) := (hU _ _ y).2 hin
    rw [Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit _)] at e
    refine ⟨rep c, ?_⟩
    rw [← hℓ, ← Category.assoc, ← e]
    exact GlobalTheory.TorsionFamily.torsionLift_ι _ _ _ _

end GlobalTheory.LevSurjOpen
