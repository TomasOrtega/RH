import Mathlib

open IsLocalRing

/- English proof (translation)
Establish `h1 : f x ∈ (J • (⊤ : Submodule R N)).map f` using `Submodule.mem_map_of_mem hx`. Rewrite `h1` using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top h1`.
-/
private theorem map_mem_smul_top {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : Module.End R N) {x : N} (hx : x ∈ J • (⊤ : Submodule R N)) :
    f x ∈ J • (⊤ : Submodule R N) := by
  have h1 : f x ∈ (J • (⊤ : Submodule R N)).map f := Submodule.mem_map_of_mem hx
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl le_top h1

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `x`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `x`. Rewrite using `[pow_succ' f k, Module.End.mul_apply, pow_succ J k, Submodule.mul_smul]`. Establish `h1 : f ((f ^ k) x) ∈ (J ^ k • (⊤ : Submodule R N)).map f` using `Submodule.mem_map_of_mem (ih x)`. Rewrite `h1` using `[Submodule.map_smul'']`. Use `Submodule.smul_mono le_rfl ?_ h1` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, _, rfl⟩`. Conclude with `hf z`.
-/
private theorem pow_mem_pow_smul_top {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : Module.End R N) (hf : ∀ x, f x ∈ J • (⊤ : Submodule R N)) (k : ℕ) :
    ∀ x, (f ^ k) x ∈ J ^ k • (⊤ : Submodule R N) := by
  induction k with
  | zero =>
    intro x
    simp
  | succ k ih =>
    intro x
    rw [pow_succ' f k, Module.End.mul_apply, pow_succ J k, Submodule.mul_smul]
    have h1 : f ((f ^ k) x) ∈ (J ^ k • (⊤ : Submodule R N)).map f :=
      Submodule.mem_map_of_mem (ih x)
    rw [Submodule.map_smul''] at h1
    refine Submodule.smul_mono le_rfl ?_ h1
    rintro _ ⟨z, _, rfl⟩
    exact hf z

/- English proof (translation)
Introduce `R N T ι _ _ _ _ _ _ _ ρ I u e hI he hu hspan x`. Establish `hP : ∀ (k : ℕ) (t : T) {z : N}, z ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) → ρ t z ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)` using `fun k t z hz => map_mem_smul_top _ (ρ t) hz`. Prove the components needed by the constructor for the conclusion. Introduce `hx i k`. Take `⟨n, hn⟩` from `hu i`.

Establish `hek : ∀ j : ℕ, ρ (e ^ j) x = x`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ, map_mul, Module.End.mul_apply, hx, ih]`.

Use `⟨n * k, ?_⟩` and prove the remaining obligations. Establish `hmem` using `pow_mem_pow_smul_top (maximalIdeal R) (ρ (u i ^ n * e)) (hI _ hn) k x`. Establish `heq : (ρ (u i) ^ (n * k)) x = (ρ (u i ^ n * e) ^ k) x`. Rewrite using `[← map_pow, ← map_pow, mul_pow, ← pow_mul, map_mul, Module.End.mul_apply, hek k]`. Rewrite using `[heq]`.

Conclude with `hmem`. Introduce `h`. Take `⟨y, hy⟩ : ∃ y, y = ρ (1 - e) x` from `⟨_, rfl⟩`. Establish `hyk : ∀ k : ℕ, y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)`. Introduce `k`.

Set `S : Ideal T` to `{ carrier := {t | ρ t y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)} add_mem' := fun {a b} ha hb => by show ρ (a + b) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `add_mem ha hb`. Use the proof step `zero_mem' := by show ρ 0 y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)`. Rewrite using `[map_zero, LinearMap.zero_apply]`.

Conclude with `zero_mem _`. Use the proof step `smul_mem' := fun c t ht => by show ρ (c * t) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)`. Rewrite using `[map_mul, Module.End.mul_apply]`. Conclude with `hP k c ht }`. Establish `hrad : I ⊔ Ideal.span (Set.range u) ≤ S.radical`.

Use `sup_le (fun μ hμ => Ideal.mem_radical_iff.mpr ⟨k, ?_⟩) (Ideal.span_le.mpr ?_)` and prove the remaining obligations. Use `show ρ (μ ^ k) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)`. Rewrite using `[map_pow]`. Conclude with `pow_mem_pow_smul_top _ (ρ μ) (hI μ hμ) k y`. Introduce and unpack `_ ⟨i, rfl⟩`.

Take `⟨n, hn⟩` from `h i k`. Use `Ideal.mem_radical_iff.mpr ⟨n, ?_⟩` and prove the remaining obligations. Use `show ρ (u i ^ n) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)`. Establish `hc : ρ (u i ^ n) y = ρ (1 - e) ((ρ (u i) ^ n) x)`. Rewrite using `[hy, ← map_pow, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]`.

Rewrite using `[hc]`. Conclude with `hP k _ hn`. Take `⟨K, hK⟩` from `Ideal.mem_radical_iff.mp (hrad hspan)`. Establish `hKy : ρ ((1 - e) ^ K) y = y`. Rewrite using `[hy, ← Module.End.mul_apply, ← map_mul, ← pow_succ, he.one_sub.pow_succ_eq]`.

Establish `hK' : ρ ((1 - e) ^ K) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)` using `hK`. Rewrite `hK'` using `[hKy]`. Then use the resulting hypothesis. Establish `hy0 : y = 0` using `IsHausdorff.haus inferInstance y (fun k => SModEq.zero.mpr (hyk k))`. Rewrite `hy0` using `[hy, map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `hy0.symm`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar :
    ∀ (R N T ι : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup N] [Module R N] [Module.Finite R N] [CommRing T] (ρ : T →+* Module.End R N) (I : Ideal T) (u : ι → T) (e : T), (∀ μ ∈ I, ∀ x, ρ μ x ∈ maximalIdeal R • (⊤ : Submodule R N)) → IsIdempotentElem e → (∀ i, ∃ n : ℕ, u i ^ n * e ∈ I) → 1 - e ∈ I ⊔ Ideal.span (Set.range u) → ∀ x, ρ e x = x ↔ ∀ (i : ι) (k : ℕ), ∃ n : ℕ, (ρ (u i) ^ n) x ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := by
  intro R N T ι _ _ _ _ _ _ _ ρ I u e hI he hu hspan x
  have hP : ∀ (k : ℕ) (t : T) {z : N}, z ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) →
      ρ t z ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) :=
    fun k t z hz => map_mem_smul_top _ (ρ t) hz
  constructor
  · intro hx i k
    obtain ⟨n, hn⟩ := hu i
    have hek : ∀ j : ℕ, ρ (e ^ j) x = x := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, map_mul, Module.End.mul_apply, hx, ih]
    refine ⟨n * k, ?_⟩
    have hmem := pow_mem_pow_smul_top (maximalIdeal R) (ρ (u i ^ n * e)) (hI _ hn) k x
    have heq : (ρ (u i) ^ (n * k)) x = (ρ (u i ^ n * e) ^ k) x := by
      rw [← map_pow, ← map_pow, mul_pow, ← pow_mul, map_mul, Module.End.mul_apply, hek k]
    rw [heq]
    exact hmem
  · intro h
    obtain ⟨y, hy⟩ : ∃ y, y = ρ (1 - e) x := ⟨_, rfl⟩
    have hyk : ∀ k : ℕ, y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := by
      intro k
      let S : Ideal T :=
        { carrier := {t | ρ t y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)}
          add_mem' := fun {a b} ha hb => by
            show ρ (a + b) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_add, LinearMap.add_apply]
            exact add_mem ha hb
          zero_mem' := by
            show ρ 0 y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_zero, LinearMap.zero_apply]
            exact zero_mem _
          smul_mem' := fun c t ht => by
            show ρ (c * t) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_mul, Module.End.mul_apply]
            exact hP k c ht }
      have hrad : I ⊔ Ideal.span (Set.range u) ≤ S.radical := by
        refine sup_le (fun μ hμ => Ideal.mem_radical_iff.mpr ⟨k, ?_⟩) (Ideal.span_le.mpr ?_)
        · show ρ (μ ^ k) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
          rw [map_pow]
          exact pow_mem_pow_smul_top _ (ρ μ) (hI μ hμ) k y
        · rintro _ ⟨i, rfl⟩
          obtain ⟨n, hn⟩ := h i k
          refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
          show ρ (u i ^ n) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
          have hc : ρ (u i ^ n) y = ρ (1 - e) ((ρ (u i) ^ n) x) := by
            rw [hy, ← map_pow, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
              ← map_mul, mul_comm]
          rw [hc]
          exact hP k _ hn
      obtain ⟨K, hK⟩ := Ideal.mem_radical_iff.mp (hrad hspan)
      have hKy : ρ ((1 - e) ^ K) y = y := by
        rw [hy, ← Module.End.mul_apply, ← map_mul, ← pow_succ, he.one_sub.pow_succ_eq]
      have hK' : ρ ((1 - e) ^ K) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := hK
      rwa [hKy] at hK'
    have hy0 : y = 0 := IsHausdorff.haus inferInstance y (fun k => SModEq.zero.mpr (hyk k))
    rw [hy, map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hy0
    exact hy0.symm
