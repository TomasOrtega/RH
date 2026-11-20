import Mathlib

/- English proof (translation)
Introduce `A _ _ K _ _ _ V _ _ _ _ M hM v`. Establish `hv : v ∈ Submodule.span K (↑M : Set V)` using `hM ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩`.

Consider the case `add x y _ _ ihx ihy`. Take `⟨a, ha, hax⟩` from `ihx`. Take `⟨b, hb, hby⟩` from `ihy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`.

Use `M.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `M.smul_mem b hax`. Rewrite using `[mul_smul]`. Conclude with `M.smul_mem a hby`.

Consider the case `smul k x _ ih`. Take `⟨a, ha, hax⟩` from `ih`. Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := A) k`. Establish `hq0 : q ≠ 0` using `nonZeroDivisors.ne_zero hq`. Establish `hqK : algebraMap A K q ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hq0`.

Use `⟨a * q, mul_ne_zero ha hq0, ?_⟩` and prove the remaining obligations. Establish `key : (a * q) • ((algebraMap A K p / algebraMap A K q) • x) = p • (a • x)`. Rewrite using `[← algebraMap_smul K (a * q), ← algebraMap_smul K a, ← algebraMap_smul K p, smul_smul, smul_smul, map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[key]`. Conclude with `M.smul_mem p hax`.
-/
theorem UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top :
    ∀ {A : Type} [inst : CommRing A] [IsDomain A]
    {K : Type} [inst_2 : Field K] [inst_3 : Algebra A K] [IsFractionRing A K] {V : Type} [inst_5 : AddCommGroup V]
    [inst_6 : _root_.Module K V] [inst_7 : _root_.Module A V] [IsScalarTower A K V] (M : Submodule A V),
    Submodule.span K (↑M : Set V) = ⊤ → ∀ (v : V), ∃ (d : A), d ≠ (0 : A) ∧ d • v ∈ M := by
  intro A _ _ K _ _ _ V _ _ _ _ M hM v
  have hv : v ∈ Submodule.span K (↑M : Set V) := hM ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨a, ha, hax⟩ := ihx
    obtain ⟨b, hb, hby⟩ := ihy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hax
    · rw [mul_smul]
      exact M.smul_mem a hby
  | smul k x _ ih =>
    obtain ⟨a, ha, hax⟩ := ih
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) k
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap A K q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hq0
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have key : (a * q) • ((algebraMap A K p / algebraMap A K q) • x) = p • (a • x) := by
      rw [← algebraMap_smul K (a * q), ← algebraMap_smul K a, ← algebraMap_smul K p,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem p hax
