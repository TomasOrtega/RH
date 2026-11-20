import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Use `set J := Ideal.span T with hJ`. Establish `hinv : ∀ s ∈ S, IsUnit s → ∃ t ∈ S, t * s = 1`. Introduce `s hsS hs`. Set `f : S →ₗ[k] S` to `LinearMap.mulLeft k (⟨s, hsS⟩ : S)`. Establish `hfi : Function.Injective f`.

Introduce `x y hxy`. Establish `h1 : s * (x : C) = s * (y : C)` using `congrArg Subtype.val hxy`. Conclude with `Subtype.ext (hs.mul_left_cancel h1)`. Take `⟨y, hy⟩` from `(LinearMap.injective_iff_surjective.mp hfi) 1`. Use `⟨y, y.2, ?_⟩` and prove the remaining obligations.

Establish `h2 : s * (y : C) = 1` using `congrArg Subtype.val hy`. Rewrite using `[mul_comm]`. Conclude with `h2`. Establish `hC : ∀ (n : ℕ) (c : C), ∃ a ∈ S, c - a ∈ J ^ n`. Introduce `n c`.

Take `⟨a, haS, s, hsS, hs, hmem⟩` from `hd n c`. Take `⟨t, htS, hts⟩` from `hinv s hsS hs`. Use `⟨t * a, S.mul_mem htS haS, ?_⟩` and prove the remaining obligations. Establish `e : c - t * a = t * (s * c - a)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ t hmem`. Set `W : ℕ → Submodule k S` to `fun n => Submodule.comap S.val.toLinearMap ((J ^ n).restrictScalars k)`. Establish `hWmem : ∀ n (x : S), x ∈ W n ↔ (x : C) ∈ J ^ n` using `fun n x => Iff.rfl`. Establish `hWle : ∀ n, W (n + 1) ≤ W n`.

Introduce `n x hx`. Rewrite `hx`, the goal using `[hWmem]`. Conclude with `Ideal.pow_le_pow_right (Nat.le_succ n) hx`. Choose the witnesses or unpack the hypotheses as in `⟨n0, hn0⟩ : ∃ n0, W n0 ≤ W (n0 + 1) := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hlt : ∀ n, Module.finrank k (W (n + 1)) < Module.finrank k (W n)`. Introduce `n`. Conclude with `Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hWle n) (fun h => hcon n h.ge))`. Establish `hbd : ∀ n, n + Module.finrank k (W n) ≤ Module.finrank k (W 0)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Use `hlt m` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `hbd (Module.finrank k (W 0) + 1)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hstep : J ^ n0 ≤ J ^ (n0 + 1)`. Introduce `x hx`.

Take `⟨a, haS, hxa⟩` from `hC (n0 + 1) x`. Establish `haJ : a ∈ J ^ n0`. Establish `h1 : x - a ∈ J ^ n0` using `Ideal.pow_le_pow_right (Nat.le_succ n0) hxa`. Establish `h2` using `Ideal.sub_mem _ hx h1`. Simplify using `using h2`.

Establish `ha1 : a ∈ J ^ (n0 + 1)` using `(hWmem (n0 + 1) ⟨a, haS⟩).mp (hn0 ((hWmem n0 ⟨a, haS⟩).mpr haJ))`. Establish `h3` using `Ideal.add_mem _ hxa ha1`. Simplify using `using h3`. Establish `hzero : J ^ n0 = ⊥`. Apply `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot J (J ^ n0) (Ideal.FG.pow (n := n0) hfg)` to reduce the goal to its premises.

Rewrite using `[smul_eq_mul, ← pow_succ']`. Conclude with `hstep`. Introduce `x hx`. Rewrite using `[Ideal.mem_jacobson_bot]`. Introduce `y`.

Establish `h` using `hI (-(x * y)) (J.neg_mem (J.mul_mem_right y hx))`. Rewrite `h` using `[sub_neg_eq_add, add_comm]`. Conclude with `h`. Establish `hsurj : Function.Surjective S.val.toLinearMap`. Introduce `c`.

Take `⟨a, haS, hca⟩` from `hC n0 c`. Rewrite `hca` using `[hzero, Ideal.mem_bot, sub_eq_zero]`. Conclude with `⟨⟨a, haS⟩, hca.symm⟩`. Conclude with `Module.Finite.of_surjective _ hsurj`.
-/
private theorem pullback_fin_relation {k C : Type} [Field k] [CommRing C] [Algebra k C] (S : Subalgebra k C)
    [Module.Finite k S] (T : Set C) (hT : T ⊆ S) (hfg : (Ideal.span T).FG)
    (hI : ∀ x ∈ Ideal.span T, IsUnit (1 - x))
    (hd : ∀ (n : ℕ) (c : C), ∃ a ∈ S, ∃ s ∈ S, IsUnit s ∧ s * c - a ∈ Ideal.span T ^ n) :
    Module.Finite k C := by
  set J := Ideal.span T with hJ
  have hinv : ∀ s ∈ S, IsUnit s → ∃ t ∈ S, t * s = 1 := by
    intro s hsS hs
    let f : S →ₗ[k] S := LinearMap.mulLeft k (⟨s, hsS⟩ : S)
    have hfi : Function.Injective f := by
      intro x y hxy
      have h1 : s * (x : C) = s * (y : C) := congrArg Subtype.val hxy
      exact Subtype.ext (hs.mul_left_cancel h1)
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hfi) 1
    refine ⟨y, y.2, ?_⟩
    have h2 : s * (y : C) = 1 := congrArg Subtype.val hy
    rw [mul_comm]
    exact h2
  have hC : ∀ (n : ℕ) (c : C), ∃ a ∈ S, c - a ∈ J ^ n := by
    intro n c
    obtain ⟨a, haS, s, hsS, hs, hmem⟩ := hd n c
    obtain ⟨t, htS, hts⟩ := hinv s hsS hs
    refine ⟨t * a, S.mul_mem htS haS, ?_⟩
    have e : c - t * a = t * (s * c - a) := by
      calc c - t * a = (t * s) * c - t * a := by rw [hts, one_mul]
        _ = t * (s * c - a) := by ring
    rw [e]
    exact Ideal.mul_mem_left _ t hmem
  let W : ℕ → Submodule k S := fun n =>
    Submodule.comap S.val.toLinearMap ((J ^ n).restrictScalars k)
  have hWmem : ∀ n (x : S), x ∈ W n ↔ (x : C) ∈ J ^ n := fun n x => Iff.rfl
  have hWle : ∀ n, W (n + 1) ≤ W n := by
    intro n x hx
    rw [hWmem] at hx ⊢
    exact Ideal.pow_le_pow_right (Nat.le_succ n) hx
  obtain ⟨n0, hn0⟩ : ∃ n0, W n0 ≤ W (n0 + 1) := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ n, Module.finrank k (W (n + 1)) < Module.finrank k (W n) := by
      intro n
      exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hWle n) (fun h => hcon n h.ge))
    have hbd : ∀ n, n + Module.finrank k (W n) ≤ Module.finrank k (W 0) := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        have := hlt m
        omega
    have := hbd (Module.finrank k (W 0) + 1)
    omega
  have hstep : J ^ n0 ≤ J ^ (n0 + 1) := by
    intro x hx
    obtain ⟨a, haS, hxa⟩ := hC (n0 + 1) x
    have haJ : a ∈ J ^ n0 := by
      have h1 : x - a ∈ J ^ n0 := Ideal.pow_le_pow_right (Nat.le_succ n0) hxa
      have h2 := Ideal.sub_mem _ hx h1
      simpa using h2
    have ha1 : a ∈ J ^ (n0 + 1) := (hWmem (n0 + 1) ⟨a, haS⟩).mp (hn0 ((hWmem n0 ⟨a, haS⟩).mpr haJ))
    have h3 := Ideal.add_mem _ hxa ha1
    simpa using h3
  have hzero : J ^ n0 = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot J (J ^ n0) (Ideal.FG.pow (n := n0) hfg)
    · rw [smul_eq_mul, ← pow_succ']
      exact hstep
    · intro x hx
      rw [Ideal.mem_jacobson_bot]
      intro y
      have h := hI (-(x * y)) (J.neg_mem (J.mul_mem_right y hx))
      rw [sub_neg_eq_add, add_comm] at h
      exact h
  have hsurj : Function.Surjective S.val.toLinearMap := by
    intro c
    obtain ⟨a, haS, hca⟩ := hC n0 c
    rw [hzero, Ideal.mem_bot, sub_eq_zero] at hca
    exact ⟨⟨a, haS⟩, hca.symm⟩
  exact Module.Finite.of_surjective _ hsurj

/- English proof (translation)
Introduce `Λ R _ _ _ _ _ p q L B _ _ _ _ _ _ _ _ _ _ hL hB hq`. Use `haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing Λ R`. Use `haveI := hL.complete`. Establish `hpB : Ideal.map (algebraMap Λ B) p ≤ maximalIdeal B`. Rewrite using `[Ideal.map_le_iff_le_comap, IsScalarTower.algebraMap_eq Λ R B, ← Ideal.comap_comap, hB.comap_eq, hq]`.

Establish `hmL : maximalIdeal L = Ideal.map (algebraMap Λ L) p`. Simplify using `using (IsCplAt.map_pow_eq Λ p L hL 1).symm`. Establish `hle : (maximalIdeal L).map (algebraMap L B) ≤ maximalIdeal B`. Rewrite using `[hmL, Ideal.map_map, ← IsScalarTower.algebraMap_eq]`. Conclude with `hpB`.

Use `haveI : IsHausdorff ((maximalIdeal L).map (algebraMap L B)) B := ⟨fun x hx => IsHausdorff.haus hB.complete.toIsHausdorff x (fun n => SModEq.mono (Submodule.smul_mono_left (Ideal.pow_right_mono hle n)) (hx n))⟩`. Use `letI : Field (L ⧸ maximalIdeal L) := Ideal.Quotient.field _`. Set `π : B →+* (B ⧸ (maximalIdeal L).map (algebraMap L B))` to `Ideal.Quotient.mk _`. Set `φ : R →+* (B ⧸ (maximalIdeal L).map (algebraMap L B))` to `π.comp (algebraMap R B)`. Set `ψ0 : Λ →+* (L ⧸ maximalIdeal L)` to `(Ideal.Quotient.mk (maximalIdeal L)).comp (algebraMap Λ L)`.

Establish `hΛ : ∀ x : Λ, φ (algebraMap Λ R x) = algebraMap (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B)) (ψ0 x)`. Introduce `x`. Use `show π (algebraMap R B (algebraMap Λ R x)) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply Λ R B, IsScalarTower.algebraMap_apply Λ L B]`. Both sides reduce to the same expression.

Establish `hcomp : (algebraMap (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B))).comp ψ0 = φ.comp (algebraMap Λ R)` using `RingHom.ext fun x => (hΛ x).symm`. Take `⟨G, hG⟩` from `Module.Finite.fg_top (R := Λ) (M := R)`. Set `S : Subalgebra (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B))` to `Algebra.adjoin (L ⧸ maximalIdeal L) (φ '' (G : Set R))`. Use `haveI : Module.Finite (L ⧸ maximalIdeal L) S := by`. Establish `hfg` using `fg_adjoin_of_finite (R := L ⧸ maximalIdeal L) ((G.finite_toSet).image φ) (by`.

Introduce and unpack `_ ⟨g, -, rfl⟩`. Take `⟨p0, hmon, hev⟩` from `Algebra.IsIntegral.isIntegral (R := Λ) g`. Use `⟨p0.map ψ0, hmon.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hev, map_zero])`. Conclude with `Module.Finite.iff_fg.mpr hfg`.

Establish `hφS : ∀ r, φ r ∈ S`. Introduce `r`. Establish `hr : r ∈ Submodule.span Λ (G : Set R)`. Rewrite using `[hG]`. Discharge the goal by the elementary cases of `trivial`.

Proceed by induction on `hr using Submodule.span_induction with`. Consider the case `mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`.

Conclude with `S.add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[Algebra.smul_def, map_mul, hΛ]`. Conclude with `S.mul_mem (S.algebraMap_mem _) hx`. Establish `hspan : Ideal.span (φ '' (q : Set R)) = Ideal.map φ q` using `rfl`.

Establish `hmapq : Ideal.map φ q = Ideal.map π (Ideal.map (algebraMap R B) q)`. Rewrite using `[Ideal.map_map]`. Use `haveI : Module.Finite (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B)) := by`. Use `pullback_fin_relation S (φ '' (q : Set R)) (by rintro _ ⟨r, _, rfl⟩; exact hφS r) ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hspan]`.

Conclude with `Ideal.FG.map (IsNoetherian.noetherian q) φ`. Introduce `x hx`. Rewrite `hx` using `[hspan, hmapq, Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective]`. Take `⟨y, hy, rfl⟩` from `hx`. Establish `hyB : y ∈ maximalIdeal B` using `(Ideal.map_le_iff_le_comap.mpr hB.comap_eq.ge) hy`.

Establish `hu` using `isUnit_one_sub_self_of_mem_nonunits y hyB`. Rewrite using `[← map_one π, ← map_sub]`. Conclude with `hu.map π`. Introduce `n c`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective c`.

Take `⟨a0, s0, hs0, hmem⟩` from `hB.dense n b`. Use `⟨φ a0, hφS a0, φ s0, hφS s0, ?_, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap R B s0)`. Assume the negation of the conclusion as `hnu`. Apply `hs0` to reduce the goal to its premises.

Rewrite using `[← hB.comap_eq]`. Conclude with `Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)`. Conclude with `hu.map π`. Establish `hpow : (Ideal.map φ q) ^ n = Ideal.map π (maximalIdeal B ^ n)`. Rewrite using `[← Ideal.map_pow, ← IsCplAt.map_pow_eq R q B hB n, Ideal.map_map]`.

Rewrite using `[hspan, hpow]`. Use `Ideal.mem_map_of_mem π hmem using 1` and compare the differences between its conclusion and the goal. Simplify using `[φ, π]`. Use `haveI : Module.Finite L (B ⧸ (maximalIdeal L).map (algebraMap L B)) := Module.Finite.trans (L ⧸ maximalIdeal L) _`. Conclude with `GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal L)`.
-/
theorem UpperTheory.V.AlgebraTools.IsCplAt.finite_of_finite :
    ∀ (Λ R : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [Algebra Λ R] [Module.Finite Λ R]
      (p : Ideal Λ) (q : Ideal R) (L B : Type) [CommRing L] [IsLocalRing L] [CommRing B] [IsLocalRing B]
      [Algebra Λ L] [Algebra R B] [Algebra L B] [Algebra Λ B] [IsScalarTower Λ R B] [IsScalarTower Λ L B],
      IsCplAt Λ p L → IsCplAt R q B → q.comap (algebraMap Λ R) = p → Module.Finite L B := by
  intro Λ R _ _ _ _ _ p q L B _ _ _ _ _ _ _ _ _ _ hL hB hq
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing Λ R
  haveI := hL.complete
  have hpB : Ideal.map (algebraMap Λ B) p ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsScalarTower.algebraMap_eq Λ R B, ← Ideal.comap_comap,
      hB.comap_eq, hq]
  have hmL : maximalIdeal L = Ideal.map (algebraMap Λ L) p := by
    simpa using (IsCplAt.map_pow_eq Λ p L hL 1).symm
  have hle : (maximalIdeal L).map (algebraMap L B) ≤ maximalIdeal B := by
    rw [hmL, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hpB
  haveI : IsHausdorff ((maximalIdeal L).map (algebraMap L B)) B :=
    ⟨fun x hx => IsHausdorff.haus hB.complete.toIsHausdorff x
      (fun n => SModEq.mono (Submodule.smul_mono_left (Ideal.pow_right_mono hle n)) (hx n))⟩
  letI : Field (L ⧸ maximalIdeal L) := Ideal.Quotient.field _
  let π : B →+* (B ⧸ (maximalIdeal L).map (algebraMap L B)) := Ideal.Quotient.mk _
  let φ : R →+* (B ⧸ (maximalIdeal L).map (algebraMap L B)) := π.comp (algebraMap R B)
  let ψ0 : Λ →+* (L ⧸ maximalIdeal L) := (Ideal.Quotient.mk (maximalIdeal L)).comp (algebraMap Λ L)
  have hΛ : ∀ x : Λ, φ (algebraMap Λ R x) =
      algebraMap (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B)) (ψ0 x) := by
    intro x
    show π (algebraMap R B (algebraMap Λ R x)) = _
    rw [← IsScalarTower.algebraMap_apply Λ R B, IsScalarTower.algebraMap_apply Λ L B]
    rfl
  have hcomp : (algebraMap (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B))).comp ψ0
      = φ.comp (algebraMap Λ R) := RingHom.ext fun x => (hΛ x).symm
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := Λ) (M := R)
  let S : Subalgebra (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B)) :=
    Algebra.adjoin (L ⧸ maximalIdeal L) (φ '' (G : Set R))
  haveI : Module.Finite (L ⧸ maximalIdeal L) S := by
    have hfg := fg_adjoin_of_finite (R := L ⧸ maximalIdeal L) ((G.finite_toSet).image φ) (by
      rintro _ ⟨g, -, rfl⟩
      obtain ⟨p0, hmon, hev⟩ := Algebra.IsIntegral.isIntegral (R := Λ) g
      refine ⟨p0.map ψ0, hmon.map _, ?_⟩
      rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hev, map_zero])
    exact Module.Finite.iff_fg.mpr hfg
  have hφS : ∀ r, φ r ∈ S := by
    intro r
    have hr : r ∈ Submodule.span Λ (G : Set R) := by
      rw [hG]
      trivial
    induction hr using Submodule.span_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact S.add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, hΛ]
      exact S.mul_mem (S.algebraMap_mem _) hx
  have hspan : Ideal.span (φ '' (q : Set R)) = Ideal.map φ q := rfl
  have hmapq : Ideal.map φ q = Ideal.map π (Ideal.map (algebraMap R B) q) := by
    rw [Ideal.map_map]
  haveI : Module.Finite (L ⧸ maximalIdeal L) (B ⧸ (maximalIdeal L).map (algebraMap L B)) := by
    refine pullback_fin_relation S (φ '' (q : Set R)) (by rintro _ ⟨r, _, rfl⟩; exact hφS r) ?_ ?_ ?_
    · rw [hspan]
      exact Ideal.FG.map (IsNoetherian.noetherian q) φ
    · intro x hx
      rw [hspan, hmapq, Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hyB : y ∈ maximalIdeal B := (Ideal.map_le_iff_le_comap.mpr hB.comap_eq.ge) hy
      have hu := isUnit_one_sub_self_of_mem_nonunits y hyB
      rw [← map_one π, ← map_sub]
      exact hu.map π
    · intro n c
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨a0, s0, hs0, hmem⟩ := hB.dense n b
      refine ⟨φ a0, hφS a0, φ s0, hφS s0, ?_, ?_⟩
      · have hu : IsUnit (algebraMap R B s0) := by
          by_contra hnu
          apply hs0
          rw [← hB.comap_eq]
          exact Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
        exact hu.map π
      · have hpow : (Ideal.map φ q) ^ n = Ideal.map π (maximalIdeal B ^ n) := by
          rw [← Ideal.map_pow, ← IsCplAt.map_pow_eq R q B hB n, Ideal.map_map]
        rw [hspan, hpow]
        convert Ideal.mem_map_of_mem π hmem using 1
        simp [φ, π]
  haveI : Module.Finite L (B ⧸ (maximalIdeal L).map (algebraMap L B)) :=
    Module.Finite.trans (L ⧸ maximalIdeal L) _
  exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal L)
