import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FgInfRestrictScalarsOfIntegers

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

/- English proof (translation)
Establish `key : ∀ (a b : C) (x : V), b ≠ 0 → v a ≤ v b → b • x ∈ L → a • x ∈ L`. Introduce `a b x hb hab hx`. Establish `hvb : 0 < v b` using `(Valuation.pos_iff v).2 hb`. Establish `h1 : v (a / b) ≤ 1`. Rewrite using `[map_div₀]`.

Conclude with `(div_le_one hvb).2 hab`. Take `⟨o, ho⟩` from `hv.exists_of_le_one h1`. Establish `h2 : a • x = o • (b • x)`. Rewrite using `[← IsScalarTower.algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ hb]`. Rewrite using `[h2]`.

Conclude with `L.smul_mem o hx`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hx⟩` from `hx`. Take `⟨b, hb, hy⟩` from `hy`. Break down `le_total (v a) (v b) with h | h` into its components or cases. Conclude with `⟨a, ha, by rw [smul_add]; exact L.add_mem hx (key a b y hb h hy)⟩`. Conclude with `⟨b, hb, by rw [smul_add]; exact L.add_mem (key b a x ha h hx) hy⟩`.

Consider the case `smul d x _ hx`. Take `⟨a, ha, hx⟩` from `hx`. Distinguish the cases in `hd : d = 0`. Conclude with `⟨1, one_ne_zero, by simp [hd]⟩`. Conclude with `⟨a / d, div_ne_zero ha hd, by rw [smul_smul, div_mul_cancel₀ _ hd]; exact hx⟩`.
-/
theorem exists_smul_mem_of_mem_span_val {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {V : Type} [AddCommGroup V] [Module C V]
    [Module O V] [IsScalarTower O C V] (L : Submodule O V) {u : V}
    (hu : u ∈ Submodule.span C (L : Set V)) : ∃ c : C, c ≠ 0 ∧ c • u ∈ L := by
  have key : ∀ (a b : C) (x : V), b ≠ 0 → v a ≤ v b → b • x ∈ L → a • x ∈ L := by
    intro a b x hb hab hx
    have hvb : 0 < v b := (Valuation.pos_iff v).2 hb
    have h1 : v (a / b) ≤ 1 := by
      rw [map_div₀]
      exact (div_le_one hvb).2 hab
    obtain ⟨o, ho⟩ := hv.exists_of_le_one h1
    have h2 : a • x = o • (b • x) := by
      rw [← IsScalarTower.algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ hb]
    rw [h2]
    exact L.smul_mem o hx
  induction hu using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    rcases le_total (v a) (v b) with h | h
    · exact ⟨a, ha, by rw [smul_add]; exact L.add_mem hx (key a b y hb h hy)⟩
    · exact ⟨b, hb, by rw [smul_add]; exact L.add_mem (key b a x ha h hx) hy⟩
  | smul d x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    by_cases hd : d = 0
    · exact ⟨1, one_ne_zero, by simp [hd]⟩
    · exact ⟨a / d, div_ne_zero ha hd, by rw [smul_smul, div_mul_cancel₀ _ hd]; exact hx⟩

/- English proof (translation)
Introduce `C _ v O _ _ hv V _ _ _ _ L U hL hU`. Establish `hfg` using `GlobalTheory.CompanionTheory.Ar.HT.fg_inf_restrictScalars_of_integers C v O hv V L U hL`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (U.subtype.restrictScalars O)` using `Subtype.val_injective`. Apply `Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars O) hinj` to reduce the goal to its premises.

Use `hfg using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨hy, y.2⟩`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨x, h2⟩, h1, rfl⟩`. Rewrite using `[eq_top_iff]`. Introduce `u _`. Take `⟨c, hc, hcu⟩` from `exists_smul_mem_of_mem_span_val hv L (hU u.2)`.

Establish `h1 : c • u ∈ Submodule.span C (latIn L U : Set U)` using `Submodule.subset_span hcu`. Establish `h2` using `Submodule.smul_mem _ c⁻¹ h1`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis.
-/
theorem latIn_isLattice : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (L : Submodule O V) (U : Submodule C V), L.FG → U ≤ Submodule.span C (L : Set V) → (latIn L U).IsLattice C := by
  intro C _ v O _ _ hv V _ _ _ _ L U hL hU
  have hfg := GlobalTheory.CompanionTheory.Ar.HT.fg_inf_restrictScalars_of_integers C v O hv V L U hL
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (U.subtype.restrictScalars O) := Subtype.val_injective
    apply Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars O) hinj
    convert hfg using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  · rw [eq_top_iff]
    intro u _
    obtain ⟨c, hc, hcu⟩ := exists_smul_mem_of_mem_span_val hv L (hU u.2)
    have h1 : c • u ∈ Submodule.span C (latIn L U : Set U) := Submodule.subset_span hcu
    have h2 := Submodule.smul_mem _ c⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

end GlobalTheory.CompanionTheory.Ar.HT
