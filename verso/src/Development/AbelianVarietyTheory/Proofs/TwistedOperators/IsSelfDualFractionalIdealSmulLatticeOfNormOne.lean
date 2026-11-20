import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.IdLatDual

variable {D : D7}

def hp (S : HSp D) (x y : Fin S.rank → D.host.E) : D.host.E :=
  ∑ i, ∑ j, star (x i) * S.gram i j * y j

def IsO (z : D.host.E) : Prop := ∃ b : 𝓞 D.host.E, (b : D.host.E) = z

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by simp⟩`.
-/
lemma isO_zero : IsO (0 : D.host.E) := ⟨0, by simp⟩
/- English proof (translation)
Take `⟨b, rfl⟩` from `hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b + c, by push_cast; rfl⟩`.
-/
lemma isO_add {z w : D.host.E} (hz : IsO z) (hw : IsO w) : IsO (z + w) := by
  obtain ⟨b, rfl⟩ := hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b + c, by push_cast; rfl⟩
/- English proof (translation)
Take `⟨b, rfl⟩` from `hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b * c, by push_cast; rfl⟩`.
-/
lemma isO_mul {z w : D.host.E} (hz : IsO z) (hw : IsO w) : IsO (z * w) := by
  obtain ⟨b, rfl⟩ := hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b * c, by push_cast; rfl⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨a, rfl⟩`.
-/
lemma isO_coe (a : 𝓞 D.host.E) : IsO (a : D.host.E) := ⟨a, rfl⟩
/- English proof (translation)
Use `⟨⟨star (a : D.host.E), ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `(RingOfIntegers.isIntegral_coe a).map (starRingEnd D.host.E).toIntAlgHom`.
-/
lemma isO_star (a : 𝓞 D.host.E) : IsO (star (a : D.host.E)) := by
  refine ⟨⟨star (a : D.host.E), ?_⟩, rfl⟩
  exact (RingOfIntegers.isIntegral_coe a).map (starRingEnd D.host.E).toIntAlgHom
/- English proof (translation)
Take `⟨b, hb⟩` from `(FractionalIdeal.mem_one_iff _).1 h`. Conclude with `⟨b, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hb⟩`.
-/
lemma isO_of_mem_one {z : D.host.E} (h : z ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) : IsO z := by
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact ⟨b, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hb⟩

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap]`.
-/
lemma osmul {n : ℕ} (a : 𝓞 D.host.E) (x : Fin n → D.host.E) : a • x = (a : D.host.E) • x := by
  ext i; simp [Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap]

variable (S : HSp D)

/- English proof (translation)
Simplify using `only [hp, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]`.
-/
lemma hp_add_left (x x' y) : hp S (x + x') y = hp S x y + hp S x' y := by
  simp only [hp, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]
/- English proof (translation)
Simplify using `only [hp, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
lemma hp_add_right (x y y') : hp S x (y + y') = hp S x y + hp S x y' := by
  simp only [hp, Pi.add_apply, mul_add, Finset.sum_add_distrib]
/- English proof (translation)
Simplify using `[hp]`.
-/
lemma hp_zero_left (y) : hp S 0 y = 0 := by simp [hp]
/- English proof (translation)
Simplify using `[hp]`.
-/
lemma hp_zero_right (x) : hp S x 0 = 0 := by simp [hp]
/- English proof (translation)
Simplify using `only [hp, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
lemma hp_smul_left (s : D.host.E) (x y) : hp S (s • x) y = star s * hp S x y := by
  simp only [hp, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
/- English proof (translation)
Simplify using `only [hp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
lemma hp_smul_right (t : D.host.E) (x y) : hp S x (t • y) = t * hp S x y := by
  simp only [hp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.IdLatDual

open GlobalTheory.IdLatDual in
/- English proof (translation)
Take `⟨a, ha, hint⟩` from `I.isFractional`. Set `f : (Fin n → D.host.E) →ₗ[𝓞 D.host.E] (Fin n → D.host.E)` to `LinearMap.lsmul (𝓞 D.host.E) (Fin n → D.host.E) a`. Establish `hle : (idLat I Λ).map f ≤ Λ`. Rewrite using `[Submodule.map_le_iff_le_comap]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨s, hs, y, hy, rfl⟩`. Take `⟨r, hr⟩` from `hint s hs`. Use `show a • (s • y) ∈ Λ`. Rewrite using `[← smul_assoc, ← hr, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ hy`.

Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`. Establish `hinj : Function.Injective f`. Introduce `x x' h`. Establish `h' : a • x = a • x'` using `h`. Rewrite `h'` using `[osmul, osmul]`.

Establish `: (a : D.host.E) ≠ 0` using `fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)`. Conclude with `smul_right_injective _ this h'`. Establish `hfg : ((idLat I Λ).map f).FG` using `Submodule.FG.of_le hΛ hle`. Conclude with `Submodule.fg_of_fg_map_injective f hinj hfg`.
-/
lemma GlobalTheory.IdLatDual.idLat_fg {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hΛ : Λ.FG)
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : (idLat I Λ).FG := by
  obtain ⟨a, ha, hint⟩ := I.isFractional
  let f : (Fin n → D.host.E) →ₗ[𝓞 D.host.E] (Fin n → D.host.E) := LinearMap.lsmul (𝓞 D.host.E) (Fin n → D.host.E) a
  have hle : (idLat I Λ).map f ≤ Λ := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, hr⟩ := hint s hs
    show a • (s • y) ∈ Λ
    rw [← smul_assoc, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ hy
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hinj : Function.Injective f := by
    intro x x' h
    have h' : a • x = a • x' := h
    rw [osmul, osmul] at h'
    have : (a : D.host.E) ≠ 0 := fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
    exact smul_right_injective _ this h'
  have hfg : ((idLat I Λ).map f).FG := Submodule.FG.of_le hΛ hle
  exact Submodule.fg_of_fg_map_injective f hinj hfg

open GlobalTheory.IdLatDual in

/- English proof (translation)
Introduce `D S Λ I I' hΛ hII' hconj`. Take `⟨hlat, hdual⟩` from `hΛ`. Establish `intL : ∀ x ∈ Λ, ∀ y ∈ Λ, IsO (hp S x y)` using `fun x hx y hy => (hdual y).1 hy x hx`. Establish `gen : ∀ s ∈ I, ∀ y ∈ Λ, s • y ∈ idLat I Λ` using `fun s hs y hy => Submodule.subset_span ⟨s, hs, y, hy, rfl⟩`. Establish `one_mem : (1 : D.host.E) ∈ I * I'` using `by rw [hII']; exact FractionalIdeal.one_mem_one _`.

Establish `hspan : ∀ y ∈ Λ, y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E))`. Introduce `y hy`. Establish `key : ∀ z ∈ I * I', z • y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E))`. Introduce `z hz`. Use `FractionalIdeal.mul_induction_on hz (fun i hi c _ => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (gen i hi y hy))`. Rewrite using `[add_smul]`. Conclude with `Submodule.add_mem _ ha hb`. Simplify using `using key 1 one_mem`.

Establish `hfg : (idLat I Λ).FG` using `idLat_fg Λ hlat.fg I`. Use `⟨⟨hfg, ?_⟩, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hlat.span_eq_top, Submodule.span_le]`. Conclude with `hspan`. Establish `stepA : ∀ s ∈ I, ∀ x₀ ∈ Λ, ∀ y ∈ idLat I Λ, IsO (hp S (s • x₀) y)`.

Introduce `s hs x₀ hx₀ y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨t, ht, y₀, hy₀, rfl⟩` from `hz`. Rewrite using `[hp_smul_left, hp_smul_right, ← mul_assoc]`.

Use `isO_mul (isO_of_mem_one ?_) (intL x₀ hx₀ y₀ hy₀)` and prove the remaining obligations. Rewrite using `[← hII', mul_comm I]`. Conclude with `FractionalIdeal.mul_mem_mul ((hconj _).2 (by rwa [star_star])) ht`. Consider the case `zero => rw [hp_zero_right]`. Conclude with `isO_zero`.

Consider the case `add a b _ _ ha hb => rw [hp_add_right]`. Conclude with `isO_add ha hb`. Consider the case `smul c z _ hz => rw [osmul, hp_smul_right]`. Conclude with `isO_mul (isO_coe c) hz`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨s, hs, x₀, hx₀, rfl⟩` from `hz`. Take `⟨b, hb⟩` from `stepA s hs x₀ hx₀ y hy`. Conclude with `⟨b, hb⟩`.

Consider the case `zero => exact ⟨0, by rw [← hp, hp_zero_left]; simp⟩`. Consider the case `add a b _ _ ha hb`. Establish `h : IsO (hp S a y + hp S b y)` using `isO_add ha hb`. Rewrite `h` using `[← hp_add_left]`. Conclude with `h`.

Consider the case `smul c z _ hz`. Take `⟨u, hu⟩` from `isO_mul (isO_star c) hz`. Conclude with `⟨u, by rw [← hp, osmul, hp_smul_left]; exact hu⟩`. Establish `hint : ∀ x ∈ idLat I Λ, IsO (hp S x y)` using `fun x hx => hy x hx`. Establish `key : ∀ z ∈ I * I', z • y ∈ idLat I Λ`.

Introduce `z hz`. Use `FractionalIdeal.mul_induction_on hz (fun i hi c hc => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[mul_smul]`. Use `gen i hi _ ((hdual _).2 fun x' hx' => ?_)` and prove the remaining obligations. Establish `hsc : star c ∈ I` using `(hconj c).1 hc`.

Take `⟨b, hb⟩` from `hint _ (gen _ hsc x' hx')`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[hb]`. Use `show hp S (star c • x') y = hp S x' (c • y)`. Rewrite using `[hp_smul_left, hp_smul_right, star_star]`.

Rewrite using `[add_smul]`. Conclude with `Submodule.add_mem _ ha hb`. Simplify using `using key 1 one_mem`.
-/
theorem GlobalTheory.idLat_isSelfDualC : ∀ {D : D7} (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (I I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), IsSelfDualC S Λ → I * I' = 1 →
    (∀ x : D.host.E, x ∈ I' ↔ star x ∈ I) → IsSelfDualC S (idLat I Λ) := by
  intro D S Λ I I' hΛ hII' hconj
  obtain ⟨hlat, hdual⟩ := hΛ
  have intL : ∀ x ∈ Λ, ∀ y ∈ Λ, IsO (hp S x y) := fun x hx y hy => (hdual y).1 hy x hx
  have gen : ∀ s ∈ I, ∀ y ∈ Λ, s • y ∈ idLat I Λ := fun s hs y hy =>
    Submodule.subset_span ⟨s, hs, y, hy, rfl⟩
  have one_mem : (1 : D.host.E) ∈ I * I' := by rw [hII']; exact FractionalIdeal.one_mem_one _

  have hspan : ∀ y ∈ Λ, y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E)) := by
    intro y hy
    have key : ∀ z ∈ I * I', z • y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E)) := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun i hi c _ => ?_) (fun a b ha hb => ?_)
      · rw [mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (gen i hi y hy))
      · rw [add_smul]; exact Submodule.add_mem _ ha hb
    simpa using key 1 one_mem
  have hfg : (idLat I Λ).FG := idLat_fg Λ hlat.fg I
  refine ⟨⟨hfg, ?_⟩, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · rw [eq_top_iff, ← hlat.span_eq_top, Submodule.span_le]
    exact hspan
  ·
    have stepA : ∀ s ∈ I, ∀ x₀ ∈ Λ, ∀ y ∈ idLat I Λ, IsO (hp S (s • x₀) y) := by
      intro s hs x₀ hx₀ y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨t, ht, y₀, hy₀, rfl⟩ := hz
        rw [hp_smul_left, hp_smul_right, ← mul_assoc]
        refine isO_mul (isO_of_mem_one ?_) (intL x₀ hx₀ y₀ hy₀)
        rw [← hII', mul_comm I]
        exact FractionalIdeal.mul_mem_mul ((hconj _).2 (by rwa [star_star])) ht
      | zero => rw [hp_zero_right]; exact isO_zero
      | add a b _ _ ha hb => rw [hp_add_right]; exact isO_add ha hb
      | smul c z _ hz => rw [osmul, hp_smul_right]; exact isO_mul (isO_coe c) hz
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, hs, x₀, hx₀, rfl⟩ := hz
      obtain ⟨b, hb⟩ := stepA s hs x₀ hx₀ y hy
      exact ⟨b, hb⟩
    | zero => exact ⟨0, by rw [← hp, hp_zero_left]; simp⟩
    | add a b _ _ ha hb =>
      have h : IsO (hp S a y + hp S b y) := isO_add ha hb
      rw [← hp_add_left] at h
      exact h
    | smul c z _ hz =>
      obtain ⟨u, hu⟩ := isO_mul (isO_star c) hz
      exact ⟨u, by rw [← hp, osmul, hp_smul_left]; exact hu⟩
  · have hint : ∀ x ∈ idLat I Λ, IsO (hp S x y) := fun x hx => hy x hx
    have key : ∀ z ∈ I * I', z • y ∈ idLat I Λ := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun i hi c hc => ?_) (fun a b ha hb => ?_)
      · rw [mul_smul]
        refine gen i hi _ ((hdual _).2 fun x' hx' => ?_)
        have hsc : star c ∈ I := (hconj c).1 hc
        obtain ⟨b, hb⟩ := hint _ (gen _ hsc x' hx')
        refine ⟨b, ?_⟩
        rw [hb]
        show hp S (star c • x') y = hp S x' (c • y)
        rw [hp_smul_left, hp_smul_right, star_star]
      · rw [add_smul]; exact Submodule.add_mem _ ha hb
    simpa using key 1 one_mem
