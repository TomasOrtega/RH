import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsTer

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.Unglue

/- English proof (translation)
Establish `h0 : (I : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 hI`. Establish `h1 : (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ≤ 1`. Introduce `a ha`. Establish `ha'` using `(FractionalIdeal.mem_inv_iff h0).1 ha`. Use `(FractionalIdeal.mem_one_iff _).2 (h a fun i hi => ?_)` and prove the remaining obligations.

Conclude with `(FractionalIdeal.mem_one_iff _).1 (ha' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hi))`. Establish `h2 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ I`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h2` using `[← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal]`. Conclude with `top_le_iff.1 h2`.
-/
theorem ideal_eq_top {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (h : ∀ a : E, (∀ i ∈ I, a * (i : E) ∈ (algebraMap (𝓞 E) E).range) → a ∈ (algebraMap (𝓞 E) E).range) :
    I = ⊤ := by
  have h0 : (I : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI
  have h1 : (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ≤ 1 := by
    intro a ha
    have ha' := (FractionalIdeal.mem_inv_iff h0).1 ha
    refine (FractionalIdeal.mem_one_iff _).2 (h a fun i hi => ?_)
    exact (FractionalIdeal.mem_one_iff _).1 (ha' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hi))
  have h2 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 E)⁰ E) = I * (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ I * 1 := by gcongr
      _ = I := mul_one _
  rw [← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact top_le_iff.1 h2

/- English proof (translation)
Take `⟨b, rfl⟩` from `h`. Conclude with `⟨RingOfIntegers.mapRingEquiv starRingAut b, rfl⟩`.
-/
theorem star_mem {E : Type} [Field E] [NumberField E] [StarRing E] {a : E}
    (h : a ∈ (algebraMap (𝓞 E) E).range) : star a ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨RingOfIntegers.mapRingEquiv starRingAut b, rfl⟩

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target`. Consider the case `exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target`. Consider the case `(apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target ..)`.
-/
theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V) {y : V}
    (hy : y ∈ Submodule.span E (L : Set V)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | (apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target ..)

/- English proof (translation)
Take `⟨hi, ho, hz⟩` from `hl`. Take `⟨hfg, hsp, hsd⟩` from `hL`. Establish `hT` using `Tu_ne_zero u`. Establish `hinj : Function.Injective ι`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Use `X.nondeg.1 x fun y => ?_` and prove the remaining obligations. Rewrite using `[← hi, hx, map_zero, LinearMap.zero_apply]`. Establish `hzU : ∀ a : D.host.E, a • z ∈ flatSp Y X ι z` using `fun a => Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z))`. Establish `hzL : z ∈ L` using `by simpa using (hp 1).2 (one_mem _)`.

Establish `hLU : ∀ y ∈ L, y ∈ flatSp Y X ι z` using `fun y hy => hsp ▸ Submodule.subset_span hy`. Establish `hint : ∀ y ∈ L, Y.hD y z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range` using `fun y hy => (hsd z (hLU z hzL)).1 hzL y hy`. Establish `hdec : ∀ y ∈ L, ∃ x : X.V, y = ι x + (-(Y.hD y z) * (Tu D u)⁻¹) • z`. Introduce `y hy`. Take `⟨_, ⟨x, rfl⟩, b, hb, rfl⟩` from `Submodule.mem_sup.1 (hLU y hy)`.

Take `⟨s, rfl⟩` from `Submodule.mem_span_singleton.1 hb`. Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `: Y.hD (ι x + s • z) z = -(s * Tu D u)`. Establish `h1` using `ho x`. Simplify using `only [HSpace.hD] at h1 hz ⊢`.

Rewrite using `[map_add, map_smul, h1, hz, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts.

Use `⟨GlobalTheory.StdFrames.isLattice_crdLat X ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `Submodule.fg_of_fg_map_injective (ι.restrictScalars (𝓞 D.host.E)) hinj (hfg.of_le ?_)` and prove the remaining obligations. Conclude with `Submodule.map_comap_le _ _`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Take `⟨c, hc, hx⟩` from `exists_smul_mem L (y := ι x) (hsp ▸ Submodule.mem_sup_left ⟨x, rfl⟩)`. Establish `hc1 : algebraMap (𝓞 D.host.E) D.host.E c ≠ 0` using `by simpa using hc`. Establish `: x = (algebraMap (𝓞 D.host.E) D.host.E c)⁻¹ • (c • x)`. Rewrite using `[← algebraMap_smul D.host.E c, smul_smul, inv_mul_cancel₀ hc1, one_smul]`. Rewrite using `[this]`.

Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(ι.restrictScalars (𝓞 D.host.E)) (c • x) ∈ L`. Rewrite using `[map_smul]`. Conclude with `hx`. Set `I : Ideal (𝓞 D.host.E)` to `(L.map ((Y.hT z).restrictScalars (𝓞 D.host.E))).comap (Algebra.linearMap (𝓞 D.host.E) D.host.E)`.

Establish `hI : ∀ i : 𝓞 D.host.E, i ∈ I ↔ ∃ y ∈ L, Y.hD y z = (i : D.host.E)` using `fun i => Iff.rfl`. Establish `hI0 : I ≠ ⊥`. Take `⟨i, hi'⟩` from `hint z hzL`. Introduce `h`. Establish `: i ∈ I` using `(hI i).2 ⟨z, hzL, hi'.symm⟩`.

Rewrite `this` using `[h, Ideal.mem_bot]`. Rewrite `hi'` using `[this, map_zero, hz]`. Conclude with `hT (neg_eq_zero.1 hi'.symm)`. Establish `hItop : I = ⊤`. Use `ideal_eq_top I hI0 fun a ha => ?_` and prove the remaining obligations.

Establish `: star a • z ∈ L`. Use `(hsd _ (hzU _)).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨i, hi'⟩` from `hint x hx`. Use `ha i ((hI i).2 ⟨x, hx, hi'.symm⟩)` as an intermediate fact. Establish `e : Y.hD x (star a • z) = a * Y.hD x z`.

Simplify using `only [HSpace.hD]`. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]`. Use `congr 1`. Conclude with `star_star a`. Rewrite using `[e, ← hi']`.

Conclude with `this`. Simplify using `using star_mem ((hp _).1 this)`. Take `⟨l, hlL, hl1⟩` from `(hI (-1)).1 (hItop ▸ Submodule.mem_top)`. Take `⟨x₀, hx₀⟩` from `hdec l hlL`. Establish `hl2 : l = (Tu D u)⁻¹ • z + ι x₀`.

Rewrite using `[hx₀, hl1, add_comm]`. Simplify using the standard rewrite rules. Establish `hc : (capX Y X ι L).comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) = L.comap (ι.restrictScalars (𝓞 D.host.E))` using `Submodule.comap_map_eq_of_injective (f := (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) (Formalism.L2.Herm.crd X).injective _`. Use `⟨x₀, ?_⟩` and prove the remaining obligations. Rewrite using `[glueLat, hc, ← hl2]`.

Use `le_antisymm (fun y hy => ?_) (sup_le (Submodule.map_comap_le _ _) ((Submodule.span_singleton_le_iff_mem _ _).2 hlL))` and prove the remaining obligations. Take `⟨x, hx⟩` from `hdec y hy`. Take `⟨b, hb⟩` from `hint y hy`. Establish `e : y + b • l = ι (x + b • x₀)`. Rewrite using `[← algebraMap_smul D.host.E b, ← algebraMap_smul D.host.E b x₀, hb, map_add, map_smul, hl2]`.

Generalize the expression as in `Y.hD y z = t at hx ⊢`. Rewrite using `[hx]`. Use `module`. Establish `hm : y + b • l ∈ L` using `L.add_mem hy (L.smul_mem _ hlL)`. Establish `e2 : y = ι (x + b • x₀) - b • l` using `by rw [← e, add_sub_cancel_right]`.

Rewrite using `[e2]`. Use `Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x + b • x₀, ?_, rfl⟩) (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self l)))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι (x + b • x₀) ∈ L`. Rewrite using `[← e]`. Conclude with `hm`.
-/
theorem isLattice_capX_and_exists_glue (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V)
    (hl : IsLine Y X ι z u) (L : Submodule (𝓞 D.host.E) Y.V) (hL : IsSDIn Y (flatSp Y X ι z) L) (hp : IsPrim Y z L) :
    Submodule.IsLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  obtain ⟨hi, ho, hz⟩ := hl
  obtain ⟨hfg, hsp, hsd⟩ := hL
  have hT := Tu_ne_zero u
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine X.nondeg.1 x fun y => ?_
    rw [← hi, hx, map_zero, LinearMap.zero_apply]
  have hzU : ∀ a : D.host.E, a • z ∈ flatSp Y X ι z := fun a =>
    Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z))
  have hzL : z ∈ L := by simpa using (hp 1).2 (one_mem _)
  have hLU : ∀ y ∈ L, y ∈ flatSp Y X ι z := fun y hy => hsp ▸ Submodule.subset_span hy
  have hint : ∀ y ∈ L, Y.hD y z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := fun y hy =>
    (hsd z (hLU z hzL)).1 hzL y hy
  have hdec : ∀ y ∈ L, ∃ x : X.V, y = ι x + (-(Y.hD y z) * (Tu D u)⁻¹) • z := by
    intro y hy
    obtain ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 (hLU y hy)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hb
    refine ⟨x, ?_⟩
    have : Y.hD (ι x + s • z) z = -(s * Tu D u) := by
      have h1 := ho x
      simp only [HSpace.hD] at h1 hz ⊢
      rw [map_add, map_smul, h1, hz, smul_eq_mul]; ring
    rw [this]
    congr 2
    field_simp
  refine ⟨GlobalTheory.StdFrames.isLattice_crdLat X ⟨?_, ?_⟩, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (ι.restrictScalars (𝓞 D.host.E)) hinj (hfg.of_le ?_)
    exact Submodule.map_comap_le _ _
  · rw [eq_top_iff]
    intro x _
    obtain ⟨c, hc, hx⟩ := exists_smul_mem L (y := ι x) (hsp ▸ Submodule.mem_sup_left ⟨x, rfl⟩)
    have hc1 : algebraMap (𝓞 D.host.E) D.host.E c ≠ 0 := by simpa using hc
    have : x = (algebraMap (𝓞 D.host.E) D.host.E c)⁻¹ • (c • x) := by
      rw [← algebraMap_smul D.host.E c, smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    change (ι.restrictScalars (𝓞 D.host.E)) (c • x) ∈ L
    rw [map_smul]
    exact hx
  · let I : Ideal (𝓞 D.host.E) :=
      (L.map ((Y.hT z).restrictScalars (𝓞 D.host.E))).comap (Algebra.linearMap (𝓞 D.host.E) D.host.E)
    have hI : ∀ i : 𝓞 D.host.E, i ∈ I ↔ ∃ y ∈ L, Y.hD y z = (i : D.host.E) := fun i => Iff.rfl
    have hI0 : I ≠ ⊥ := by
      obtain ⟨i, hi'⟩ := hint z hzL
      intro h
      have : i ∈ I := (hI i).2 ⟨z, hzL, hi'.symm⟩
      rw [h, Ideal.mem_bot] at this
      rw [this, map_zero, hz] at hi'
      exact hT (neg_eq_zero.1 hi'.symm)
    have hItop : I = ⊤ := by
      refine ideal_eq_top I hI0 fun a ha => ?_
      have : star a • z ∈ L := by
        refine (hsd _ (hzU _)).2 fun x hx => ?_
        obtain ⟨i, hi'⟩ := hint x hx
        have := ha i ((hI i).2 ⟨x, hx, hi'.symm⟩)
        have e : Y.hD x (star a • z) = a * Y.hD x z := by
          simp only [HSpace.hD]
          rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
          congr 1
          exact star_star a
        rw [e, ← hi']
        exact this
      simpa using star_mem ((hp _).1 this)
    obtain ⟨l, hlL, hl1⟩ := (hI (-1)).1 (hItop ▸ Submodule.mem_top)
    obtain ⟨x₀, hx₀⟩ := hdec l hlL
    have hl2 : l = (Tu D u)⁻¹ • z + ι x₀ := by
      rw [hx₀, hl1, add_comm]
      simp
    have hc : (capX Y X ι L).comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) =
        L.comap (ι.restrictScalars (𝓞 D.host.E)) :=
      Submodule.comap_map_eq_of_injective (f := (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E))
        (Formalism.L2.Herm.crd X).injective _
    refine ⟨x₀, ?_⟩
    rw [glueLat, hc, ← hl2]
    refine le_antisymm (fun y hy => ?_)
      (sup_le (Submodule.map_comap_le _ _) ((Submodule.span_singleton_le_iff_mem _ _).2 hlL))
    obtain ⟨x, hx⟩ := hdec y hy
    obtain ⟨b, hb⟩ := hint y hy
    have e : y + b • l = ι (x + b • x₀) := by
      rw [← algebraMap_smul D.host.E b, ← algebraMap_smul D.host.E b x₀, hb, map_add, map_smul, hl2]
      generalize Y.hD y z = t at hx ⊢
      rw [hx]
      module
    have hm : y + b • l ∈ L := L.add_mem hy (L.smul_mem _ hlL)
    have e2 : y = ι (x + b • x₀) - b • l := by rw [← e, add_sub_cancel_right]
    rw [e2]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x + b • x₀, ?_, rfl⟩)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self l)))
    change ι (x + b • x₀) ∈ L
    rw [← e]
    exact hm

end GlobalTheory.AdIsom.Unglue
