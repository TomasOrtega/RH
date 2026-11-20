import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

/- English proof (translation)
Use `set x : (Fin n → E) →ₗ[E] (Fin n → E) := 1 - g with hx`. Establish `hxe : x ^ e = 0`. Establish `: x = -(g - 1)` using `by rw [hx, neg_sub]`. Rewrite using `[this, neg_pow, hg, mul_zero]`. Set `s : Set (Fin n → E)` to `Set.range fun p : Fin (e + 1) × Fin n => (x ^ (p.1 : ℕ)) (Pi.single p.2 1)`.

Establish `hall : ∀ (i : ℕ) (j : Fin n), (x ^ i) (Pi.single j 1) ∈ Submodule.span O s`. Introduce `i j`. Distinguish the cases in `hi : i < e + 1`. Conclude with `Submodule.subset_span ⟨(⟨i, hi⟩, j), rfl⟩`. Establish `: x ^ i = 0` using `pow_eq_zero_of_le (by omega) hxe`.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Establish `hpow : ∀ (k : ℕ), ∀ v ∈ Submodule.span O s, (x ^ k) v ∈ Submodule.span O s`. Introduce `k v hv`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨p, rfl⟩` from `hy`. Use `hall (k + p.1) p.2` as an intermediate fact. Rewrite `this` using `[pow_add, Module.End.mul_apply]`. Then use the resulting hypothesis. Consider the case `zero => rw [map_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha`. Establish `: (x ^ k) (c • a) = c • (x ^ k) a` using `(x ^ k).map_smul (c : E) a`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ c ha`. Use `⟨Submodule.span O s, Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]`. Use `Submodule.span_mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨j, rfl⟩`. Use `hall 0 j` as an intermediate fact. Simplify using `using this`. Introduce `v hv`. Establish `h1` using `hpow 1 v hv`.

Establish `h2 : g v = v - (x ^ 1) v` using `by simp [hx]`. Rewrite using `[h2]`. Conclude with `Submodule.sub_mem _ hv h1`. Introduce `v hv`. Use `⟨(∑ i ∈ Finset.range e, x ^ i) v, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.sum_apply]`. Conclude with `Submodule.sum_mem _ fun i _ => hpow i v hv`. Establish `h` using `mul_neg_geom_sum x e`. Establish `h1 : 1 - x = g` using `by rw [hx, sub_sub_cancel]`. Rewrite `h` using `[h1, hxe, sub_zero]`.

Rewrite using `[← Module.End.mul_apply, h, Module.End.one_apply]`.
-/
theorem exists_fg_span_stable_of_unipotent {E : Type} [CommRing E] (O : Subring E) {n : ℕ}
    (g : (Fin n → E) →ₗ[E] (Fin n → E)) (e : ℕ) (hg : (g - 1) ^ e = 0) :
    ∃ Λ : Submodule O (Fin n → E), Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧
      (∀ v ∈ Λ, g v ∈ Λ) ∧ ∀ v ∈ Λ, ∃ w ∈ Λ, g w = v := by
  set x : (Fin n → E) →ₗ[E] (Fin n → E) := 1 - g with hx
  have hxe : x ^ e = 0 := by
    have : x = -(g - 1) := by rw [hx, neg_sub]
    rw [this, neg_pow, hg, mul_zero]
  let s : Set (Fin n → E) :=
    Set.range fun p : Fin (e + 1) × Fin n => (x ^ (p.1 : ℕ)) (Pi.single p.2 1)
  have hall : ∀ (i : ℕ) (j : Fin n), (x ^ i) (Pi.single j 1) ∈ Submodule.span O s := by
    intro i j
    by_cases hi : i < e + 1
    · exact Submodule.subset_span ⟨(⟨i, hi⟩, j), rfl⟩
    · have : x ^ i = 0 := pow_eq_zero_of_le (by omega) hxe
      rw [this]
      exact Submodule.zero_mem _
  have hpow : ∀ (k : ℕ), ∀ v ∈ Submodule.span O s, (x ^ k) v ∈ Submodule.span O s := by
    intro k v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      have := hall (k + p.1) p.2
      rwa [pow_add, Module.End.mul_apply] at this
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : (x ^ k) (c • a) = c • (x ^ k) a := (x ^ k).map_smul (c : E) a
      rw [this]
      exact Submodule.smul_mem _ c ha
  refine ⟨Submodule.span O s, Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    have := hall 0 j
    simpa using this
  · intro v hv
    have h1 := hpow 1 v hv
    have h2 : g v = v - (x ^ 1) v := by simp [hx]
    rw [h2]
    exact Submodule.sub_mem _ hv h1
  · intro v hv
    refine ⟨(∑ i ∈ Finset.range e, x ^ i) v, ?_, ?_⟩
    · rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun i _ => hpow i v hv
    · have h := mul_neg_geom_sum x e
      have h1 : 1 - x = g := by rw [hx, sub_sub_cancel]
      rw [h1, hxe, sub_zero] at h
      rw [← Module.End.mul_apply, h, Module.End.one_apply]

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L n g e hg`. Take `⟨Λ, h1, h2, h3, h4⟩` from `exists_fg_span_stable_of_unipotent L.O _ e hg`. Use `⟨Λ, ⟨h1, h2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[MulAction.mem_stabilizer_iff]`. Use extensionality with `v`.

Rewrite using `[Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `h3 w hw`. Introduce `hv`.

Take `⟨w, hw, h⟩` from `h4 v hv`. Conclude with `⟨w, hw, h⟩`.
-/
theorem exists_isLat_stabL_of_unipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (g : ((Fin n → E) ≃ₗ[E] (Fin n → E))) (e : ℕ), (((g : (Fin n → E) →ₗ[E] (Fin n → E)) - 1) ^ e = 0) → ∃ Λ : Submodule L.O (Fin n → E), IsLat L Λ ∧ g ∈ stabL L Λ := by
  intro F _ _ _ _ _ E _ _ _ L n g e hg
  obtain ⟨Λ, h1, h2, h3, h4⟩ := exists_fg_span_stable_of_unipotent L.O _ e hg
  refine ⟨Λ, ⟨h1, h2⟩, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact h3 w hw
  · intro hv
    obtain ⟨w, hw, h⟩ := h4 v hv
    exact ⟨w, hw, h⟩

end GlobalTheory.HL
