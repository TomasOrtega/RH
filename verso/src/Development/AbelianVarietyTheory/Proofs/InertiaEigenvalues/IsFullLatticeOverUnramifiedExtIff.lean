import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfValNonneg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerSpanningFamilyOfUnramifiedExtStatement

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

/- English proof (translation)
Establish `hm : ∀ y, y ∈ L ↔ y ∈ M` using `fun y => by`. Rewrite using `[← SetLike.mem_coe, h, SetLike.mem_coe]`. Use `and_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨S, hS⟩`. Use `⟨(Finset.univ ×ˢ S).image fun p : Fin d × A => u p.1 • p.2, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product] at hx`. Take `⟨p, hp, rfl⟩` from `hx`. Conclude with `(hm _).1 (L.smul_mem _ (hS ▸ Submodule.subset_span hp.2))`.

Introduce `x hx`. Establish `hx' : x ∈ Submodule.span O' (S : Set A)` using `hS ▸ (hm x).2 hx`. Use `set N := Submodule.span O ((((Finset.univ ×ˢ S).image fun p : Fin d × A => u p.1 • p.2 : Finset A)) : Set A) with hN`. Establish `key : ∀ c : O', c • x ∈ N` using `by clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`.

Consider the case `mem s hs`. Introduce `c`. Take `⟨a, ha⟩` from `h2 c`. Rewrite using `[Algebra.smul_def, ha, Finset.sum_mul]`. Use `N.sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]`. Use `N.smul_mem _ (Submodule.subset_span ?_)` and prove the remaining obligations. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]`. Conclude with `⟨(i, s), ⟨Finset.mem_univ _, hs⟩, rfl⟩`. Consider the case `zero => intro c`.

Simplify using the standard rewrite rules. Consider the case `add x z _ _ hx hz => intro c`. Rewrite using `[smul_add]`. Conclude with `N.add_mem (hx c) (hz c)`. Consider the case `smul e x _ hx => intro c`.

Rewrite using `[smul_smul]`. Conclude with `hx _`. Simplify using `using key 1`. Introduce and unpack `⟨S, hS⟩`. Use `⟨S, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.span_le, h, ← hS]`. Conclude with `Submodule.subset_span`. Introduce `x hx`. Establish `hx' : x ∈ Submodule.span O (S : Set A)` using `hS ▸ (hm x).1 hx`. Use `clear hx`.

Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem s hs => exact Submodule.subset_span hs`. Consider the case `zero => exact zero_mem _`. Consider the case `add x z _ _ hx hz => exact add_mem hx hz`. Consider the case `smul e x _ hx`.

Take `⟨b, hb⟩` from `h1 e`. Rewrite using `[Algebra.smul_def, ← hb, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ hx`. Introduce `hL`. Rewrite using `[eq_top_iff]`.

Introduce `x hx0`. Use `clear hx0`. Establish `hx' : x ∈ Submodule.span E' (L : Set A)` using `hL ▸ Submodule.mem_top`. Establish `key : ∀ c : E', c • x ∈ Submodule.span E (M : Set A)`. Proceed by induction on `hx' using Submodule.span_induction with`.

Consider the case `mem s hs`. Introduce `c`. Take `⟨e, b, hb⟩` from `h4 c`. Rewrite using `[Algebra.smul_def, hb, mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ((hm _).1 (L.smul_mem _ hs)))`.

Consider the case `zero => intro c`. Simplify using the standard rewrite rules. Consider the case `add x z _ _ hx hz => intro c`. Rewrite using `[smul_add]`. Conclude with `add_mem (hx c) (hz c)`.

Consider the case `smul e x _ hx => intro c`. Rewrite using `[smul_smul]`. Conclude with `hx _`. Simplify using `using key 1`. Introduce `hM`.

Rewrite using `[eq_top_iff]`. Introduce `x hx0`. Use `clear hx0`. Establish `hx' : x ∈ Submodule.span E (M : Set A)` using `hM ▸ Submodule.mem_top`. Proceed by induction on `hx' using Submodule.span_induction with`.

Consider the case `mem s hs => exact Submodule.subset_span ((hm s).2 hs)`. Consider the case `zero => exact zero_mem _`. Consider the case `add x z _ _ hx hz => exact add_mem hx hz`. Consider the case `smul e x _ hx`. Take `⟨b, hb⟩` from `h3 e`.

Rewrite using `[Algebra.smul_def, ← hb, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem isLat_iff_of_coe_eq {O O' E E' A : Type} [CommRing O] [CommRing O'] [Field E] [Field E'] [CommRing A]
    [Algebra O A] [Algebra O' A] [Algebra E A] [Algebra E' A] {d : ℕ} (u : Fin d → O')
    (h1 : ∀ a : O, ∃ b : O', algebraMap O' A b = algebraMap O A a)
    (h2 : ∀ y : O', ∃ a : Fin d → O, algebraMap O' A y = ∑ i, algebraMap O A (a i) * algebraMap O' A (u i))
    (h3 : ∀ e : E, ∃ e' : E', algebraMap E' A e' = algebraMap E A e)
    (h4 : ∀ e' : E', ∃ (e : E) (b : O'), algebraMap E' A e' = algebraMap E A e * algebraMap O' A b)
    (L : Submodule O' A) (M : Submodule O A) (h : (L : Set A) = (M : Set A)) :
    IsLat O' E' L ↔ IsLat O E M := by
  classical
  have hm : ∀ y, y ∈ L ↔ y ∈ M := fun y => by
    rw [← SetLike.mem_coe, h, SetLike.mem_coe]
  refine and_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨S, hS⟩
    refine ⟨(Finset.univ ×ˢ S).image fun p : Fin d × A => u p.1 • p.2, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact (hm _).1 (L.smul_mem _ (hS ▸ Submodule.subset_span hp.2))
    · intro x hx
      have hx' : x ∈ Submodule.span O' (S : Set A) := hS ▸ (hm x).2 hx
      set N := Submodule.span O
        ((((Finset.univ ×ˢ S).image fun p : Fin d × A => u p.1 • p.2 : Finset A)) : Set A) with hN
      have key : ∀ c : O', c • x ∈ N := by
        clear hx
        induction hx' using Submodule.span_induction with
        | mem s hs =>
          intro c
          obtain ⟨a, ha⟩ := h2 c
          rw [Algebra.smul_def, ha, Finset.sum_mul]
          refine N.sum_mem fun i _ => ?_
          rw [mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]
          refine N.smul_mem _ (Submodule.subset_span ?_)
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
          exact ⟨(i, s), ⟨Finset.mem_univ _, hs⟩, rfl⟩
        | zero => intro c; simp
        | add x z _ _ hx hz => intro c; rw [smul_add]; exact N.add_mem (hx c) (hz c)
        | smul e x _ hx => intro c; rw [smul_smul]; exact hx _
      simpa using key 1
  · rintro ⟨S, hS⟩
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le, h, ← hS]
      exact Submodule.subset_span
    · intro x hx
      have hx' : x ∈ Submodule.span O (S : Set A) := hS ▸ (hm x).1 hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem s hs => exact Submodule.subset_span hs
      | zero => exact zero_mem _
      | add x z _ _ hx hz => exact add_mem hx hz
      | smul e x _ hx =>
        obtain ⟨b, hb⟩ := h1 e
        rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ hx
  · intro hL
    rw [eq_top_iff]
    intro x hx0
    clear hx0
    have hx' : x ∈ Submodule.span E' (L : Set A) := hL ▸ Submodule.mem_top
    have key : ∀ c : E', c • x ∈ Submodule.span E (M : Set A) := by
      induction hx' using Submodule.span_induction with
      | mem s hs =>
        intro c
        obtain ⟨e, b, hb⟩ := h4 c
        rw [Algebra.smul_def, hb, mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ((hm _).1 (L.smul_mem _ hs)))
      | zero => intro c; simp
      | add x z _ _ hx hz => intro c; rw [smul_add]; exact add_mem (hx c) (hz c)
      | smul e x _ hx => intro c; rw [smul_smul]; exact hx _
    simpa using key 1
  · intro hM
    rw [eq_top_iff]
    intro x hx0
    clear hx0
    have hx' : x ∈ Submodule.span E (M : Set A) := hM ▸ Submodule.mem_top
    induction hx' using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span ((hm s).2 hs)
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      obtain ⟨b, hb⟩ := h3 e
      rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Distinguish the cases in `hz : z = 0`. Conclude with `⟨0, 0, by simp [hz]⟩`. Take `⟨π, hπ⟩` from `(IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hπ` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero hπ.symm`. Establish `hφ0 : φ π ≠ 0` using `by simpa using hπ0`. Use `set v := (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E with hv`. Establish `h1 : WithZero.log (v (φ π)) = -1`.

Use `hU.2.2.1 π` as an intermediate fact. Unfold `val at this`. Rewrite `this` using `[hπ, WithZero.log_exp, ← hv]`. Use linear arithmetic over natural numbers and integers. Establish `hv0 : v (φ π) ≠ 0` using `by simpa using hφ0`.

Establish `hz0 : v z ≠ 0` using `by simpa using hz`. Take `⟨b, hb⟩` from `mem_range_of_val_nonneg K' (z * φ π ^ (WithZero.log (v z))) (by`. Unfold `val`. Rewrite using `[← hv, map_mul, map_zpow₀, WithZero.log_mul hz0 (zpow_ne_zero _ hv0), WithZero.log_zpow, h1]`. Use the proof step `simp)`.

Use `⟨π ^ (-WithZero.log (v z)), b, ?_⟩` and prove the remaining obligations. Rewrite using `[hb, map_zpow₀, zpow_neg]`. Use `zpow_ne_zero (WithZero.log (v z)) hφ0` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_eq_base_mul_int {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (z : K'.E) :
    ∃ (e : K.E) (b : K'.O), z = φ e * algebraMap K'.O K'.E b := by
  by_cases hz : z = 0
  · exact ⟨0, 0, by simp [hz]⟩
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hφ0 : φ π ≠ 0 := by simpa using hπ0
  set v := (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E with hv
  have h1 : WithZero.log (v (φ π)) = -1 := by
    have := hU.2.2.1 π
    unfold val at this
    rw [hπ, WithZero.log_exp, ← hv] at this
    omega
  have hv0 : v (φ π) ≠ 0 := by simpa using hφ0
  have hz0 : v z ≠ 0 := by simpa using hz
  obtain ⟨b, hb⟩ := mem_range_of_val_nonneg K' (z * φ π ^ (WithZero.log (v z))) (by
    unfold val
    rw [← hv, map_mul, map_zpow₀, WithZero.log_mul hz0 (zpow_ne_zero _ hv0), WithZero.log_zpow, h1]
    simp)
  refine ⟨π ^ (-WithZero.log (v z)), b, ?_⟩
  rw [hb, map_zpow₀, zpow_neg]
  have := zpow_ne_zero (WithZero.log (v z)) hφ0
  field_simp

/- English proof (translation)
Introduce `K K' d φ hU B ψ hψ hσ L M h`. Take `⟨u, hu⟩` from `GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt K K' d φ hU`. Use `letI : Algebra K'.E B.A := ψ.toAlgebra`. Use `letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra`. Establish `hO' : ∀ b : K'.O, algebraMap K'.O B.A b = ψ (algebraMap K'.O K'.E b)` using `fun _ => rfl`.

Establish `hE' : ∀ b : K'.E, algebraMap K'.E B.A b = ψ b` using `fun _ => rfl`. Establish `hO : ∀ a : K.O, algebraMap K.O B.A a = ψ (φ (algebraMap K.O K.E a))` using `fun a => by`. Rewrite using `[hψ, ← IsScalarTower.algebraMap_apply]`. Establish `key` using `isLat_iff_of_coe_eq (O := K.O) (O' := K'.O) (E := K.E) (E' := K'.E) (A := B.A) u ?_ ?_ ?_ ?_`. Conclude with `key L M h`.

Introduce `a`. Take `⟨b, hb⟩` from `exists_int_image hU a`. Conclude with `⟨b, by rw [hO', hO, hb]⟩`. Introduce `y`. Take `⟨a, ha⟩` from `hu y`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[hO', ha, map_sum]`. Simplify using `only [map_mul, hO, hO']`. Introduce `e`. Conclude with `⟨φ e, by rw [hE', hψ]⟩`.

Introduce `z`. Take `⟨e, b, hb⟩` from `exists_eq_base_mul_int hU z`. Conclude with `⟨e, b, by rw [hE', hO', ← hψ, ← map_mul, ← hb]⟩`.
-/
theorem isLat_overExt_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (M : Submodule K.O B.A), (L : Set (overExt φ B ψ hψ hσ).A) = (M : Set B.A) → (IsLat K'.O K'.E L ↔ IsLat K.O K.E M) := by
  intro K K' d φ hU B ψ hψ hσ L M h
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt K K' d φ hU
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  have hO' : ∀ b : K'.O, algebraMap K'.O B.A b = ψ (algebraMap K'.O K'.E b) := fun _ => rfl
  have hE' : ∀ b : K'.E, algebraMap K'.E B.A b = ψ b := fun _ => rfl
  have hO : ∀ a : K.O, algebraMap K.O B.A a = ψ (φ (algebraMap K.O K.E a)) := fun a => by
    rw [hψ, ← IsScalarTower.algebraMap_apply]
  have key := isLat_iff_of_coe_eq (O := K.O) (O' := K'.O) (E := K.E) (E' := K'.E) (A := B.A) u ?_ ?_ ?_ ?_
  · exact key L M h
  · intro a
    obtain ⟨b, hb⟩ := exists_int_image hU a
    exact ⟨b, by rw [hO', hO, hb]⟩
  · intro y
    obtain ⟨a, ha⟩ := hu y
    refine ⟨a, ?_⟩
    rw [hO', ha, map_sum]
    simp only [map_mul, hO, hO']
  · intro e
    exact ⟨φ e, by rw [hE', hψ]⟩
  · intro z
    obtain ⟨e, b, hb⟩ := exists_eq_base_mul_int hU z
    exact ⟨e, b, by rw [hE', hO', ← hψ, ← map_mul, ← hb]⟩

end GlobalTheory.UnitLemma.Unr
