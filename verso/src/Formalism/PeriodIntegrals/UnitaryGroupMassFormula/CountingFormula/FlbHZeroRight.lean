import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Module
open ValuativeRel

/- English proof (translation)
Conclude with `(L.O_def _).2 isIntegral_algebraMap`.
-/
theorem flb_int_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O := by
  exact (L.O_def _).2 isIntegral_algebraMap

/- English proof (translation)
Conclude with `(L.O_def _).2 (((L.O_def x).1 hx).map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F]))`.
-/
theorem flb_cj_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  exact (L.O_def _).2 (((L.O_def x).1 hx).map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F]))

/- English proof (translation)
Use `⟨fun I => ?_⟩` and prove the remaining obligations. Establish `hget : ∀ x : S, x ∈ I → ∀ (j : ℕ) (u : E), u ∈ S → (∃ w ∈ S, u * w = 1) → (x : E) = p ^ j * u → (⟨p, hp⟩ : S) ^ j ∈ I`. Introduce and unpack `x hxI j u hu ⟨w, hw, huw⟩ hxe`. Establish `h : (⟨p, hp⟩ : S) ^ j = x * ⟨w, hw⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]`. Rewrite using `[mul_assoc, huw, mul_one]`. Rewrite using `[h]`. Conclude with `I.mul_mem_right _ hxI`. Distinguish the cases in `hI : ∃ x ∈ I, x ≠ 0`.

Establish `hex : ∃ k : ℕ, (⟨p, hp⟩ : S) ^ k ∈ I`. Take `⟨x, hxI, hx0⟩` from `hI`. Take `⟨k, u, hu, huw, hxe⟩` from `hfac x x.2 (fun h => hx0 (Subtype.ext h))`. Conclude with `⟨k, hget x hxI k u hu huw hxe⟩`. Use `⟨⟨(⟨p, hp⟩ : S) ^ Nat.find hex, ?_⟩⟩` and prove the remaining obligations.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hxI`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`. Conclude with `Submodule.zero_mem _`.

Take `⟨j, u, hu, huw, hxe⟩` from `hfac x x.2 (fun h => hx0 (Subtype.ext h))`. Establish `hkj : Nat.find hex ≤ j` using `Nat.find_min' hex (hget x hxI j u hu huw hxe)`. Rewrite using `[Ideal.submodule_span_eq, Ideal.mem_span_singleton']`. Use `⟨(⟨p, hp⟩ : S) ^ (j - Nat.find hex) * ⟨u, hu⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]`. Rewrite using `[mul_comm, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkj]`. Rewrite using `[Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Nat.find_spec hex`. Use `push Not at hI`.

Use `⟨⟨0, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_singleton_eq_bot.mpr rfl]`. Conclude with `(Submodule.eq_bot_iff I).mpr hI`.
-/
theorem flb_pid {E : Type} [CommRing E] (S : Subring E) (p : E) (hp : p ∈ S)
    (hfac : ∀ x ∈ S, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ S, (∃ w ∈ S, u * w = 1) ∧ x = p ^ k * u) :
    IsPrincipalIdealRing S := by
  classical
  refine ⟨fun I => ?_⟩
  have hget : ∀ x : S, x ∈ I → ∀ (j : ℕ) (u : E), u ∈ S → (∃ w ∈ S, u * w = 1) →
      (x : E) = p ^ j * u → (⟨p, hp⟩ : S) ^ j ∈ I := by
    rintro x hxI j u hu ⟨w, hw, huw⟩ hxe
    have h : (⟨p, hp⟩ : S) ^ j = x * ⟨w, hw⟩ := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]
      rw [mul_assoc, huw, mul_one]
    rw [h]
    exact I.mul_mem_right _ hxI
  by_cases hI : ∃ x ∈ I, x ≠ 0
  · have hex : ∃ k : ℕ, (⟨p, hp⟩ : S) ^ k ∈ I := by
      obtain ⟨x, hxI, hx0⟩ := hI
      obtain ⟨k, u, hu, huw, hxe⟩ := hfac x x.2 (fun h => hx0 (Subtype.ext h))
      exact ⟨k, hget x hxI k u hu huw hxe⟩
    refine ⟨⟨(⟨p, hp⟩ : S) ^ Nat.find hex, ?_⟩⟩
    apply le_antisymm
    · intro x hxI
      by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      obtain ⟨j, u, hu, huw, hxe⟩ := hfac x x.2 (fun h => hx0 (Subtype.ext h))
      have hkj : Nat.find hex ≤ j := Nat.find_min' hex (hget x hxI j u hu huw hxe)
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
      refine ⟨(⟨p, hp⟩ : S) ^ (j - Nat.find hex) * ⟨u, hu⟩, ?_⟩
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]
      rw [mul_comm, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkj]
    · rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
      exact Nat.find_spec hex
  · push Not at hI
    refine ⟨⟨0, ?_⟩⟩
    rw [Submodule.span_singleton_eq_bot.mpr rfl]
    exact (Submodule.eq_bot_iff I).mpr hI

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Rewrite using `[H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]`.
-/
theorem flb_h_add_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

/- English proof (translation)
Rewrite using `[H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]`.
-/
theorem flb_h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (x : V) (a : E) (y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

/- English proof (translation)
Establish `hs` using `map_sum (AddMonoidHom.mk' (H.h x) (flb_h_add_right H x)) (fun i => c i • v i) Finset.univ`. Simplify using `only [AddMonoidHom.mk'_apply] at hs`. Rewrite using `[hs]`. Conclude with `Finset.sum_congr rfl fun i _ => flb_h_smul_right H x (c i) (v i)`.
-/
theorem flb_h_sum_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} [Fintype ι] (x : V) (c : ι → E) (v : ι → V) :
    H.h x (∑ i, c i • v i) = ∑ i, M.L.cj (c i) * H.h x (v i) := by
  have hs := map_sum (AddMonoidHom.mk' (H.h x) (flb_h_add_right H x)) (fun i => c i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hs
  rw [hs]
  exact Finset.sum_congr rfl fun i _ => flb_h_smul_right H x (c i) (v i)

/- English proof (translation)
Establish `hs` using `map_sum (AddMonoidHom.mk' (fun z => H.h z y) (fun a b => H.h_add_left a b y)) (fun i => c i • v i) Finset.univ`. Simplify using `only [AddMonoidHom.mk'_apply] at hs`. Rewrite using `[hs]`. Conclude with `Finset.sum_congr rfl fun i _ => H.h_smul_left (c i) (v i) y`.
-/
theorem flb_h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} [Fintype ι] (y : V) (c : ι → E) (v : ι → V) :
    H.h (∑ i, c i • v i) y = ∑ i, c i * H.h (v i) y := by
  have hs := map_sum (AddMonoidHom.mk' (fun z => H.h z y) (fun a b => H.h_add_left a b y))
    (fun i => c i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hs
  rw [hs]
  exact Finset.sum_congr rfl fun i _ => H.h_smul_left (c i) (v i) y

end Herm

end PI.UnitaryGroupMassFormula.CntFormula
