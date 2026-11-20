import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitelyManyIsoClassesProjectiveNumberField

noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {r m : ℕ}

/- English proof (translation)
Establish `key : ∀ β : LinearMap.BilinForm ℤ X, (∑ j : Fin (m * k), β (a (finProdFinEquiv.symm j).1) (a (finProdFinEquiv.symm j).1) : ℤ) = k * ∑ i, β (a i) (a i)` using `fun β => by`. Rewrite using `[finProdFinEquiv.symm.sum_comp (fun p : Fin m × Fin k => β (a p.1) (a p.1)), Fintype.sum_prod_type]`. Simplify using `[Finset.mul_sum]`. Establish `hk' : (0 : ℝ) < k` using `by exact_mod_cast hk`. Use `⟨?_, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => h.only β hβ hp ?_⟩` and prove the remaining obligations.

Rewrite using `[← h.span]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, rfl⟩`.

Conclude with `⟨_, rfl⟩`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨finProdFinEquiv (i, ⟨0, hk⟩), by simp⟩`. Rewrite using `[key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]`. Use `h.le β hβ hp` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← h.eq j]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `he` using `[key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]`. Establish `: (k : ℝ) * (d * φ.evalZ β) = k * (∑ i, β (a i) (a i) : ℤ)` using `by rw [← he]; ring`.

Conclude with `mul_left_cancel₀ hk'.ne' this`.
-/
theorem Supports.mul {d : ℕ} {γ : Fin r → LinearMap.BilinForm ℤ X} {a : Fin m → X} (h : Supports bar φ d γ a) {k : ℕ}
    (hk : 0 < k) : Supports bar φ (d * k) γ fun j : Fin (m * k) => a (finProdFinEquiv.symm j).1 := by
  have key : ∀ β : LinearMap.BilinForm ℤ X,
      (∑ j : Fin (m * k), β (a (finProdFinEquiv.symm j).1) (a (finProdFinEquiv.symm j).1) : ℤ) =
        k * ∑ i, β (a i) (a i) := fun β => by
    rw [finProdFinEquiv.symm.sum_comp (fun p : Fin m × Fin k => β (a p.1) (a p.1)), Fintype.sum_prod_type]
    simp [Finset.mul_sum]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨?_, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => h.only β hβ hp ?_⟩
  · rw [← h.span]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨finProdFinEquiv (i, ⟨0, hk⟩), by simp⟩
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    have := h.le β hβ hp
    nlinarith
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← h.eq j]; ring
  · rw [key, Nat.cast_mul, Int.cast_mul, Int.cast_natCast] at he
    have : (k : ℝ) * (d * φ.evalZ β) = k * (∑ i, β (a i) (a i) : ℤ) := by rw [← he]; ring
    exact mul_left_cancel₀ hk'.ne' this

/- English proof (translation)
Use `⟨?_, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => ?_⟩` and prove the remaining obligations. Establish `h1 : Set.range (fun i => e (a i)) = e.toAddEquiv.toIntLinearEquiv.toLinearMap '' Set.range a`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h1, Submodule.span_image, h.span, Submodule.map_top, LinearMap.range_eq_top]`.

Conclude with `e.toAddEquiv.toIntLinearEquiv.surjective`. Use `h.le _ (pull_mem e.toLinearMap hβ) fun y => hp _` as an intermediate fact. Rewrite `this` using `[evalZ_pull φ e.surjective]`. Then use the resulting hypothesis. Use `h.eq j` as an intermediate fact. Rewrite `this` using `[evalZ_pull φ e.surjective]`. Then use the resulting hypothesis.

Establish `he' : d * φ.evalZ (pull e.toLinearMap β) = (∑ i, pull e.toLinearMap β (a i) (a i) : ℤ)`. Rewrite using `[evalZ_pull φ e.surjective]`. Conclude with `he`. Take `⟨k, c, hk, hc⟩` from `h.only _ (pull_mem e.toLinearMap hβ) (fun y => hp _) he'`. Use `⟨k, c, hk, LinearMap.ext₂ fun x y => ?_⟩` and prove the remaining obligations.

Use `LinearMap.congr_fun₂ hc (e.symm x) (e.symm y)` as an intermediate fact. Simplify `this` using `[LinearMap.sum_apply]`.
-/
theorem Supports.of_pull {d : ℕ} (e : X ≃ₗ[O] X₁) {γ : Fin r → LinearMap.BilinForm ℤ X₁} {a : Fin m → X}
    (h : Supports bar φ d (fun j => pull e.toLinearMap (γ j)) a) : Supports bar φ d γ fun i => e (a i) := by
  refine ⟨?_, fun β hβ hp => ?_, fun j => ?_, fun β hβ hp he => ?_⟩
  · have h1 : Set.range (fun i => e (a i)) = e.toAddEquiv.toIntLinearEquiv.toLinearMap '' Set.range a := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, h.span, Submodule.map_top, LinearMap.range_eq_top]
    exact e.toAddEquiv.toIntLinearEquiv.surjective
  · have := h.le _ (pull_mem e.toLinearMap hβ) fun y => hp _
    rwa [evalZ_pull φ e.surjective] at this
  · have := h.eq j
    rwa [evalZ_pull φ e.surjective] at this
  · have he' : d * φ.evalZ (pull e.toLinearMap β) = (∑ i, pull e.toLinearMap β (a i) (a i) : ℤ) := by
      rw [evalZ_pull φ e.surjective]; exact he
    obtain ⟨k, c, hk, hc⟩ := h.only _ (pull_mem e.toLinearMap hβ) (fun y => hp _) he'
    refine ⟨k, c, hk, LinearMap.ext₂ fun x y => ?_⟩
    have := LinearMap.congr_fun₂ hc (e.symm x) (e.symm y)
    simpa [LinearMap.sum_apply] using this

end Transport

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Use `choose d hd hP using h`. Establish `hpos : 0 < ∏ i, d i` using `Finset.prod_pos fun i _ => hd i`. Conclude with `⟨_, hpos, fun i => hmul i _ _ (hP i) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) hpos⟩`.
-/
theorem exists_common {ι : Type} [Finite ι] (P : ι → ℕ → Prop) (hmul : ∀ i d d', P i d → d ∣ d' → 0 < d' → P i d')
    (h : ∀ i, ∃ d, 1 ≤ d ∧ P i d) : ∃ d, 1 ≤ d ∧ ∀ i, P i d := by
  have := Fintype.ofFinite ι
  choose d hd hP using h
  have hpos : 0 < ∏ i, d i := Finset.prod_pos fun i _ => hd i
  exact ⟨_, hpos, fun i => hmul i _ _ (hP i) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) hpos⟩

section Module

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O}

/- English proof (translation)
Take `⟨S, hS, hfin⟩` from `hX.finite`. Use `hS.to_subtype` as an intermediate fact. Set `N` to `Nat.card S`. Take `⟨d, hd, hP⟩` from `exists_common (ι := Σ r : Fin (N + 1), (Fin r → S)) (fun i d => IsCone bar φ (fun j => (i.2 j : LinearMap.BilinForm ℤ X)) → ∃ (m : ℕ) (a : Fin m → X), Supports bar φ d (fun j => (i.2 j : LinearMap.BilinForm ℤ X)) a) (fun i d d' h hdd hd' hc => by`. Take `⟨m, a, ha⟩` from `h hc`.

Take `⟨c, rfl⟩` from `hdd`. Conclude with `⟨_, _, ha.mul (Nat.pos_of_mul_pos_left hd')⟩)`. Use the proof step `(fun i => by`. Distinguish the cases in `hc : IsCone bar φ (fun j => (i.2 j : LinearMap.BilinForm ℤ X))`. Take `⟨d, m, a, hd, ha⟩` from `hs _ _ hc`.

Conclude with `⟨d, hd, fun _ => ⟨m, a, ha⟩⟩`. Conclude with `⟨1, le_rfl, fun h => (hc h).elim⟩)`. Use `⟨d, hd, fun r γ hγ => ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `hfin r γ hγ`. Establish `hγ'` using `hγ.pull_equiv e`.

Establish `hr : r ≤ N`. Use `Nat.card_le_card_of_injective (fun i : Fin r => (⟨_, he i⟩ : S)) (fun i j h => hγ'.injective (congrArg Subtype.val h))` as an intermediate fact. Rewrite `this` using `[Nat.card_fin]`. Then use the resulting hypothesis. Take `⟨m, a, ha⟩` from `hP ⟨⟨r, by omega⟩, fun i => ⟨_, he i⟩⟩ hγ'`. Conclude with `⟨m, _, ha.of_pull e⟩`.
-/
theorem exists_common_module {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (hX : IsPolFanOn bar φ X)
    (hs : ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧
      Supports bar φ d γ a) :
    ∃ d, 1 ≤ d ∧ ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (m : ℕ) (a : Fin m → X),
      Supports bar φ d γ a := by
  obtain ⟨S, hS, hfin⟩ := hX.finite
  have := hS.to_subtype
  let N := Nat.card S
  obtain ⟨d, hd, hP⟩ := exists_common (ι := Σ r : Fin (N + 1), (Fin r → S))
    (fun i d => IsCone bar φ (fun j => (i.2 j : LinearMap.BilinForm ℤ X)) →
      ∃ (m : ℕ) (a : Fin m → X), Supports bar φ d (fun j => (i.2 j : LinearMap.BilinForm ℤ X)) a)
    (fun i d d' h hdd hd' hc => by
      obtain ⟨m, a, ha⟩ := h hc
      obtain ⟨c, rfl⟩ := hdd
      exact ⟨_, _, ha.mul (Nat.pos_of_mul_pos_left hd')⟩)
    (fun i => by
      by_cases hc : IsCone bar φ (fun j => (i.2 j : LinearMap.BilinForm ℤ X))
      · obtain ⟨d, m, a, hd, ha⟩ := hs _ _ hc
        exact ⟨d, hd, fun _ => ⟨m, a, ha⟩⟩
      · exact ⟨1, le_rfl, fun h => (hc h).elim⟩)
  refine ⟨d, hd, fun r γ hγ => ?_⟩
  obtain ⟨e, he⟩ := hfin r γ hγ
  have hγ' := hγ.pull_equiv e
  have hr : r ≤ N := by
    have := Nat.card_le_card_of_injective (fun i : Fin r => (⟨_, he i⟩ : S))
      (fun i j h => hγ'.injective (congrArg Subtype.val h))
    rwa [Nat.card_fin] at this
  obtain ⟨m, a, ha⟩ := hP ⟨⟨r, by omega⟩, fun i => ⟨_, he i⟩⟩ hγ'
  exact ⟨m, _, ha.of_pull e⟩

end Module

/- English proof (translation)
Introduce `O _ _ _ _ _ bar q φ hpol hs`. Take `⟨n, Y, hY⟩` from `GlobalTheory.ProjModFinIso.exists_finite_reps (R := O) q`. Take `⟨d, hd, hP⟩` from `exists_common (ι := Fin n) (fun k d => ∀ [Module.Finite O (Y k)] [Module.Projective O (Y k)], Module.finrank O (Y k) ≤ q → ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ (Y k)), IsCone bar φ γ → ∃ (m : ℕ) (a : Fin m → Y k), Supports bar φ d γ a) (fun k d d' h hdd hd' _ _ hq r γ hγ …`. Take `⟨m, a, ha⟩` from `h hq r γ hγ`. Take `⟨c, rfl⟩` from `hdd`.

Conclude with `⟨_, _, ha.mul (Nat.pos_of_mul_pos_left hd')⟩)`. Use the proof step `(fun k => by`. Distinguish the cases in `hk : Module.Finite O (Y k) ∧ Module.Projective O (Y k) ∧ Module.finrank O (Y k) ≤ q`. Take `⟨h1, h2, h3⟩` from `hk`. Take `⟨d, hd, h⟩` from `exists_common_module (hpol _ h3) (hs _ h3)`.

Conclude with `⟨d, hd, fun _ => h⟩`. Conclude with `⟨1, le_rfl, fun h3 => (hk ⟨‹_›, ‹_›, h3⟩).elim⟩)`. Use `⟨d, hd, fun X _ _ _ _ hX r γ hγ => ?_⟩` and prove the remaining obligations. Take `⟨k, ⟨e⟩⟩` from `hY X hX`. Use `haveI := Module.Finite.equiv e`.

Use `haveI := Module.Projective.of_equiv e`. Take `⟨m, a, ha⟩` from `hP k (e.finrank_eq ▸ hX) r _ (hγ.pull_equiv e.symm)`. Conclude with `⟨m, _, ha.of_pull e.symm⟩`.
-/
theorem exists_hasSupports : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [Module.Finite ℤ O] [Module.Free ℤ O]
    [Finite (ClassGroup O)] (bar : O → O) (q : ℕ) (φ : InvFun O), IsPolFan bar q φ →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
      ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧
        Supports bar φ d γ a) → ∃ d, 1 ≤ d ∧ HasSupports bar q φ d := by
  intro O _ _ _ _ _ bar q φ hpol hs
  obtain ⟨n, Y, hY⟩ := GlobalTheory.ProjModFinIso.exists_finite_reps (R := O) q
  obtain ⟨d, hd, hP⟩ := exists_common (ι := Fin n)
    (fun k d => ∀ [Module.Finite O (Y k)] [Module.Projective O (Y k)], Module.finrank O (Y k) ≤ q →
      ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ (Y k)), IsCone bar φ γ → ∃ (m : ℕ) (a : Fin m → Y k),
        Supports bar φ d γ a)
    (fun k d d' h hdd hd' _ _ hq r γ hγ => by
      obtain ⟨m, a, ha⟩ := h hq r γ hγ
      obtain ⟨c, rfl⟩ := hdd
      exact ⟨_, _, ha.mul (Nat.pos_of_mul_pos_left hd')⟩)
    (fun k => by
      by_cases hk : Module.Finite O (Y k) ∧ Module.Projective O (Y k) ∧ Module.finrank O (Y k) ≤ q
      · obtain ⟨h1, h2, h3⟩ := hk
        obtain ⟨d, hd, h⟩ := exists_common_module (hpol _ h3) (hs _ h3)
        exact ⟨d, hd, fun _ => h⟩
      · exact ⟨1, le_rfl, fun h3 => (hk ⟨‹_›, ‹_›, h3⟩).elim⟩)
  refine ⟨d, hd, fun X _ _ _ _ hX r γ hγ => ?_⟩
  obtain ⟨k, ⟨e⟩⟩ := hY X hX
  haveI := Module.Finite.equiv e
  haveI := Module.Projective.of_equiv e
  obtain ⟨m, a, ha⟩ := hP k (e.finrank_eq ▸ hX) r _ (hγ.pull_equiv e.symm)
  exact ⟨m, _, ha.of_pull e.symm⟩

end GlobalTheory.Poinc
