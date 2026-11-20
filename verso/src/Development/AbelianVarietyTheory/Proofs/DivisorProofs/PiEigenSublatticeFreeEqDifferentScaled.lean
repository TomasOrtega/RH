import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
open scoped NNReal

namespace GlobalTheory.EigenSubFree

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference Polynomial

/- English proof (translation)
Distinguish the cases in `h0 : f = 0`. Simplify using `[h0]`. Establish `hnd : (T.val.map c).Nodup` using `Multiset.Nodup.map_on (fun x hx y hy h => hc hx hy h) T.nodup`. Establish `hle : T.val.map c ≤ f.roots`. Rewrite using `[Multiset.le_iff_subset hnd]`.

Introduce `b hb`. Take `⟨j, hj, rfl⟩` from `Multiset.mem_map.1 hb`. Conclude with `(Polynomial.mem_roots h0).2 (hf j hj)`. Use `(Multiset.prod_X_sub_C_dvd_iff_le_roots h0 _).2 hle` as an intermediate fact. Rewrite `this` using `[Multiset.map_map]`. Then use the resulting hypothesis.
-/
theorem prod_X_sub_C_dvd {O ι : Type} [CommRing O] [IsDomain O] (T : Finset ι)
    (c : ι → O) (hc : Set.InjOn c (↑T : Set ι)) (f : Polynomial O)
    (hf : ∀ j ∈ T, f.eval (c j) = 0) :
    (∏ i ∈ T, (X - C (c i))) ∣ f := by
  by_cases h0 : f = 0
  · simp [h0]
  have hnd : (T.val.map c).Nodup :=
    Multiset.Nodup.map_on (fun x hx y hy h => hc hx hy h) T.nodup
  have hle : T.val.map c ≤ f.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro b hb
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hb
    exact (Polynomial.mem_roots h0).2 (hf j hj)
  have := (Multiset.prod_X_sub_C_dvd_iff_le_roots h0 _).2 hle
  rwa [Multiset.map_map] at this

variable {C : Type} [Field C] {w : Valuation C ℝ≥0} {S : Type}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩ i`. Take `⟨f, hf⟩` from `hx i`. Simplify using `only [LinearMap.proj_apply]`. Rewrite using `[hf τ]`.

Conclude with `Subtype.prop _`. Introduce `hu`. Conclude with `⟨fun _ => u, fun i => ⟨Polynomial.C ⟨u i, hu i⟩, fun s => by simp⟩, rfl⟩`.
-/
theorem mem_eigenQuot_freeLattice (a : S → w.valuationSubring) (r : ℕ) (τ : S) (u : Fin r → C) :
    u ∈ eigenQuot (W := fun _ => Fin r → C) (freeLattice a r) τ ↔
      ∀ i, u i ∈ w.valuationSubring := by
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    obtain ⟨f, hf⟩ := hx i
    simp only [LinearMap.proj_apply]
    rw [hf τ]
    exact Subtype.prop _
  · intro hu
    exact ⟨fun _ => u, fun i => ⟨Polynomial.C ⟨u i, hu i⟩, fun s => by simp⟩, rfl⟩

/- English proof (translation)
Use `show (LinearMap.single w.valuationSubring (fun _ : S => Fin r → C) τ v) ∈ freeLattice a r ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Take `⟨f, hf⟩` from `h i`. Use `⟨f, fun s hs => ?_, ?_⟩` and prove the remaining obligations.

Use `hf s` as an intermediate fact. Simplify using `[hs] at this`. Conclude with `this.symm` after adjusting the coercions. Use `hf τ` as an intermediate fact. Simplify using `at this`.

Conclude with `this.symm`. Introduce `h i`. Take `⟨f, h0, h1⟩` from `h i`. Use `⟨f, fun s => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hs : s = τ`.

Substitute `hs` using the available equality. Simplify using `[h1]`. Simplify using `[hs, h0 s hs]`.
-/
theorem mem_eigenSub_freeLattice [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ) (τ : S)
    (v : Fin r → C) :
    v ∈ eigenSub (W := fun _ => Fin r → C) (freeLattice a r) τ ↔
      ∀ i, ∃ f : Polynomial w.valuationSubring,
        (∀ s, s ≠ τ → f.eval (a s) = 0) ∧ ((f.eval (a τ) : w.valuationSubring) : C) = v i := by
  show (LinearMap.single w.valuationSubring (fun _ : S => Fin r → C) τ v) ∈ freeLattice a r ↔ _
  constructor
  · intro h i
    obtain ⟨f, hf⟩ := h i
    refine ⟨f, fun s hs => ?_, ?_⟩
    · have := hf s
      simp [hs] at this
      exact_mod_cast this.symm
    · have := hf τ
      simp at this
      exact this.symm
  · intro h i
    obtain ⟨f, h0, h1⟩ := h i
    refine ⟨f, fun s => ?_⟩
    by_cases hs : s = τ
    · subst hs; simp [h1]
    · simp [hs, h0 s hs]

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[mem_eigenSub_freeLattice]`. Unfold `flatLattice`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `key : ∀ i, ∃ g : w.valuationSubring, (diffGen a τ : C) * g = v i`. Introduce `i`. Take `⟨f, h0, h1⟩` from `h i`. Take `⟨q, hq⟩` from `prod_X_sub_C_dvd (Finset.univ.erase τ) a (fun x _ y _ e => ha e) f (fun j hj => h0 j (Finset.ne_of_mem_erase hj))`.

Use `⟨q.eval (a τ), ?_⟩` and prove the remaining obligations. Rewrite using `[← h1, hq, eval_mul, eval_prod]`. Simplify using `[diffGen]`. Use `choose g hg using key`. Use `⟨fun i => (g i : C), (mem_eigenQuot_freeLattice a r τ _).2 fun i => (g i).2, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `[Algebra.smul_def, hg i]`. Introduce and unpack `⟨u, hu, rfl⟩ i`. Establish `hu'` using `(mem_eigenQuot_freeLattice a r τ u).1 hu`. Use `⟨Polynomial.C (⟨u i, hu' i⟩ : w.valuationSubring) * ∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s)), fun s hs => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[eval_mul, eval_prod]`. Rewrite using `[Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩) (by simp)]`. Simplify using the standard rewrite rules. Rewrite using `[eval_mul, eval_prod]`. Simplify using `[diffGen, Algebra.smul_def, mul_comm]`.
-/
theorem eigenSub_freeLattice [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ)
    (τ : S) (ha : Function.Injective a) :
    eigenSub (W := fun _ => Fin r → C) (freeLattice a r) τ =
      flatLattice (r := r) a τ (diffGen a τ) := by
  ext v
  rw [mem_eigenSub_freeLattice]
  unfold flatLattice
  rw [Submodule.mem_map]
  constructor
  · intro h
    have key : ∀ i, ∃ g : w.valuationSubring, (diffGen a τ : C) * g = v i := by
      intro i
      obtain ⟨f, h0, h1⟩ := h i
      obtain ⟨q, hq⟩ := prod_X_sub_C_dvd (Finset.univ.erase τ) a
        (fun x _ y _ e => ha e) f (fun j hj => h0 j (Finset.ne_of_mem_erase hj))
      refine ⟨q.eval (a τ), ?_⟩
      rw [← h1, hq, eval_mul, eval_prod]
      simp [diffGen]
    choose g hg using key
    refine ⟨fun i => (g i : C), (mem_eigenQuot_freeLattice a r τ _).2 fun i => (g i).2, ?_⟩
    funext i
    simp [Algebra.smul_def, hg i]
  · rintro ⟨u, hu, rfl⟩ i
    have hu' := (mem_eigenQuot_freeLattice a r τ u).1 hu
    refine ⟨Polynomial.C (⟨u i, hu' i⟩ : w.valuationSubring) *
      ∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s)), fun s hs => ?_, ?_⟩
    · rw [eval_mul, eval_prod]
      rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩) (by simp)]
      simp
    · rw [eval_mul, eval_prod]
      simp [diffGen, Algebra.smul_def, mul_comm]

/- English proof (translation)
Introduce `_ _ _ _ _ _ a r τ ha` and use `eigenSub_freeLattice a r τ ha`.
-/
theorem main : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (r : ℕ) (τ : S), Function.Injective a →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a r) τ =
      GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.flatLattice (r := r) a τ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ) :=
  fun _ _ _ _ _ _ a r τ ha => eigenSub_freeLattice a r τ ha

end GlobalTheory.EigenSubFree
