import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

set_option autoImplicit false

noncomputable section

open DividedPowers TensorProduct

namespace GlobalTheory.PDA.Model

variable {B : Type} [CommRing B] {J : Ideal B}

/- English proof (translation)
Establish `: (Q.e.coord 0) ∘ₗ LinearMap.mulRight B (Q.e (n + 1)) = 0`. Use `Q.e.ext fun m ↦ ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.mulRight_apply, Q.e_mul, ← nsmul_eq_mul, map_nsmul, LinearMap.zero_apply, Module.Basis.coord_apply, Module.Basis.repr_self]`. Rewrite using `[Finsupp.single_eq_of_ne (by omega), smul_zero]`. Conclude with `LinearMap.congr_fun this p`.
-/
theorem repr_mul_succ (Q : PDPoly B) (p : Q.P) (n : ℕ) : Q.e.repr (p * Q.e (n + 1)) 0 = 0 := by
  have : (Q.e.coord 0) ∘ₗ LinearMap.mulRight B (Q.e (n + 1)) = 0 := by
    refine Q.e.ext fun m ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Q.e_mul, ← nsmul_eq_mul, map_nsmul,
      LinearMap.zero_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
    rw [Finsupp.single_eq_of_ne (by omega), smul_zero]
  exact LinearMap.congr_fun this p

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 h`. Establish `h1 : ∀ q, Q.e.repr (q * a) 0 ∈ J`. Use `Submodule.span_induction (p := fun a _ ↦ ∀ q, Q.e.repr (q * a) 0 ∈ J) ?_ ?_ ?_ ?_ ha` and prove the remaining obligations.

Introduce and unpack `_ ⟨j, hj, rfl⟩ q`. Rewrite using `[mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `J.mul_mem_right _ hj`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy q`.

Rewrite using `[mul_add, map_add]`. Conclude with `add_mem (hx q) (hy q)`. Introduce `r x _ hx q`. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hx _`.

Establish `h2 : ∀ q, Q.e.repr (q * b) 0 = 0`. Use `Submodule.span_induction (p := fun a _ ↦ ∀ q, Q.e.repr (q * a) 0 = 0) ?_ ?_ ?_ ?_ hb` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩ q`. Conclude with `repr_mul_succ Q q j`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy q`. Rewrite using `[mul_add, map_add, Finsupp.add_apply, hx, hy, add_zero]`. Introduce `r x _ hx q`. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hx _`.

Establish `h1'` using `h1 1`. Establish `h2'` using `h2 1`. Rewrite `h1'`, `h2'` using `[one_mul]`. Rewrite using `[map_add, Finsupp.add_apply, h2', add_zero]`. Conclude with `h1'`.

Introduce `h`. Rewrite using `[← Q.e.linearCombination_repr p, Finsupp.linearCombination_apply, Finsupp.sum]`. Use `Ideal.sum_mem _ fun n _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Break down `n with _ | n` into its components or cases.

Conclude with `Ideal.mul_mem_right _ _ (Q.algebraMap_mem_ext h)`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Q.e_succ_mem_aug n))`.
-/
theorem mem_ext_iff (Q : PDPoly B) (p : Q.P) : p ∈ Q.ext J ↔ Q.e.repr p 0 ∈ J := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    have h1 : ∀ q, Q.e.repr (q * a) 0 ∈ J := by
      refine Submodule.span_induction (p := fun a _ ↦ ∀ q, Q.e.repr (q * a) 0 ∈ J) ?_ ?_ ?_ ?_ ha
      · rintro _ ⟨j, hj, rfl⟩ q
        rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact J.mul_mem_right _ hj
      · simp
      · intro x y _ _ hx hy q; rw [mul_add, map_add]; exact add_mem (hx q) (hy q)
      · intro r x _ hx q; rw [smul_eq_mul, ← mul_assoc]; exact hx _
    have h2 : ∀ q, Q.e.repr (q * b) 0 = 0 := by
      refine Submodule.span_induction (p := fun a _ ↦ ∀ q, Q.e.repr (q * a) 0 = 0) ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨j, rfl⟩ q; exact repr_mul_succ Q q j
      · simp
      · intro x y _ _ hx hy q; rw [mul_add, map_add, Finsupp.add_apply, hx, hy, add_zero]
      · intro r x _ hx q; rw [smul_eq_mul, ← mul_assoc]; exact hx _
    have h1' := h1 1
    have h2' := h2 1
    rw [one_mul] at h1' h2'
    rw [map_add, Finsupp.add_apply, h2', add_zero]; exact h1'
  · intro h
    rw [← Q.e.linearCombination_repr p, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Ideal.sum_mem _ fun n _ ↦ ?_
    rw [Algebra.smul_def]
    rcases n with _ | n
    · exact Ideal.mul_mem_right _ _ (Q.algebraMap_mem_ext h)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Q.e_succ_mem_aug n))

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[Ideal.mem_comap, mem_ext_iff, Algebra.algebraMap_eq_smul_one, ← Q.e_zero]`. Simplify using the standard rewrite rules.
-/
theorem comap_ext (Q : PDPoly B) : (Q.ext J).comap (algebraMap B Q.P) = J := by
  ext a
  rw [Ideal.mem_comap, mem_ext_iff, Algebra.algebraMap_eq_smul_one, ← Q.e_zero]
  simp

/- English proof (translation)
Use `dpow_eq_from_gens η' η (S := algebraMap B Q.P '' J ∪ Set.range fun n : ℕ ↦ Q.e (n + 1)) (by rw [Ideal.span_union]; rfl) ?_` and prove the remaining obligations. Introduce and unpack `n _ (⟨j, hj, rfl⟩ | ⟨k, rfl⟩)`. Rewrite using `[h.dp.dpow_comp j hj, h'.dp.dpow_comp j hj]`. Use `beta_reduce conv_lhs => rw [← h'.var] conv_rhs => rw [← h.var]`. Rewrite using `[η.dpow_comp (by omega) (Q.e_one_mem_ext J), η'.dpow_comp (by omega) (Q.e_one_mem_ext J), h.var, h'.var]`.
-/
theorem isStd_unique {Q : PDPoly B} {δ : DividedPowers J} {η η' : DividedPowers (Q.ext J)}
    (h : Q.IsStd δ η) (h' : Q.IsStd δ η') : η = η' := by
  refine dpow_eq_from_gens η' η (S := algebraMap B Q.P '' J ∪ Set.range fun n : ℕ ↦ Q.e (n + 1))
    (by rw [Ideal.span_union]; rfl) ?_
  rintro n _ (⟨j, hj, rfl⟩ | ⟨k, rfl⟩)
  · rw [h.dp.dpow_comp j hj, h'.dp.dpow_comp j hj]
  · beta_reduce
    conv_lhs => rw [← h'.var]
    conv_rhs => rw [← h.var]
    rw [η.dpow_comp (by omega) (Q.e_one_mem_ext J), η'.dpow_comp (by omega) (Q.e_one_mem_ext J), h.var, h'.var]

/- English proof (translation)
Use `haveI : Module.Free B Q.P := Module.Free.of_basis Q.e`. Set `f : Q.P →+* K ⊗[B] Q.P` to `(Algebra.TensorProduct.includeRight (R := B) (A := K) (B := Q.P)).toRingHom`. Establish `hf : Function.Injective f` using `Algebra.TensorProduct.includeRight_injective hK`. Use `letI : Algebra ℚ (K ⊗[B] Q.P) := ((algebraMap K (K ⊗[B] Q.P)).comp (algebraMap ℚ K)).toAlgebra`. Establish `keyC : ∀ (n : ℕ) (x y : K ⊗[B] Q.P), (n.factorial : K ⊗[B] Q.P) * x = n.factorial * y → x = y` using `fun n x y h ↦ (IsUnit.natCast_factorial_of_algebra (A := K ⊗[B] Q.P) ℚ n).mul_left_cancel h`.

Establish `key : ∀ (n : ℕ) (x y : Q.P), (n.factorial : Q.P) * x = n.factorial * y → x = y` using `fun n x y h ↦ hf (keyC n _ _ (by simpa using congrArg f h))`. Set `κ : DividedPowers ((Q.ext J).map f)` to `RatAlgebra.dividedPowers _`. Establish `hmem : ∀ (n : ℕ) {x : Q.P} (_ : x ∈ Q.ext J), ∃ (y : Q.P) (_ : n ≠ 0 → y ∈ Q.ext J), f y = κ.dpow n (f x)`. Introduce `n x hx`. Establish `hs : Q.ext J = Ideal.span (algebraMap B Q.P '' J ∪ Set.range fun n : ℕ ↦ Q.e (n + 1))`.

Rewrite using `[Ideal.span_union]`. Both sides reduce to the same expression. Establish `hx'` using `hx`. Rewrite `hx'` using `[hs]`. Use `revert n`.

Use `Submodule.span_induction (p := fun x _ ↦ ∀ n, ∃ (y : Q.P) (_ : n ≠ 0 → y ∈ Q.ext J), f y = κ.dpow n (f x)) ?_ ?_ ?_ ?_ hx'` and prove the remaining obligations. Introduce and unpack `_ (⟨j, hj, rfl⟩ | ⟨k, rfl⟩) n`. Use `⟨algebraMap B Q.P (δ.dpow n j), fun hn ↦ Q.algebraMap_mem_ext (δ.dpow_mem hn hj), keyC n _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[factorial_mul_dpow_eq_pow _ (Ideal.mem_map_of_mem f (Q.algebraMap_mem_ext hj)), ← map_pow, ← map_pow, ← factorial_mul_dpow_eq_pow δ hj, map_mul, map_natCast, map_mul, map_natCast]`. Use `⟨(Nat.uniformBell n (k + 1) : Q.P) * Q.e (n * (k + 1)), fun hn ↦ ?_, ?_⟩` and prove the remaining obligations.

Take `⟨m, hm⟩ : ∃ m, n * (k + 1) = m + 1` from `Nat.exists_eq_succ_of_ne_zero (by positivity)`. Rewrite using `[hm]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Q.e_succ_mem_aug m))`. Establish `he : ∀ m, f (Q.e m) = κ.dpow m (f (Q.e 1))` using `fun m ↦ keyC m _ _ (by`. Rewrite using `[factorial_mul_dpow_eq_pow _ (Ideal.mem_map_of_mem f (Q.e_one_mem_ext J)), ← map_pow, Q.e_one_pow, map_mul, map_natCast])`.

Use `beta_reduce`. Rewrite using `[map_mul, map_natCast, he, he (k + 1), κ.dpow_comp (by omega) (Ideal.mem_map_of_mem f (Q.e_one_mem_ext J))]`. Introduce `n`. Break down `n with _ | n` into its components or cases. Conclude with `⟨1, by simp, by rw [map_one, map_zero, κ.dpow_zero (zero_mem _)]⟩`.

Conclude with `⟨0, fun _ ↦ zero_mem _, by rw [map_zero, κ.dpow_eval_zero (by omega)]⟩`. Introduce `x y hx hy ihx ihy n replace hx : x ∈ Q.ext J := hs.ge hx replace hy : y ∈ Q.ext J := hs.ge hy choose u hu hu' using ihx choose v hv hv' using ihy`. Use `⟨∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, u k.1 * v k.2, fun hn ↦ Ideal.sum_mem _ fun k hk ↦ ?_, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Distinguish the cases in `h0 : k.1 = 0`.

Conclude with `Ideal.mul_mem_left _ _ (hv _ (by omega))`. Conclude with `Ideal.mul_mem_right _ _ (hu _ h0)`. Rewrite using `[map_add, κ.dpow_add (Ideal.mem_map_of_mem f hx) (Ideal.mem_map_of_mem f hy), map_sum]`. Simplify using `only [map_mul, hu', hv']`. Introduce `a x hx ih n replace hx : x ∈ Q.ext J := hs.ge hx`.

Take `⟨y, hy, hy'⟩` from `ih n`. Use `⟨a ^ n * y, fun hn ↦ Ideal.mul_mem_left _ _ (hy hn), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, map_mul, map_mul, κ.dpow_mul (Ideal.mem_map_of_mem f hx), hy', map_pow]`. Use `⟨DividedPowers.ofInjective _ _ f hf κ rfl hmem, ⟨le_sup_left, fun {n} a ha ↦ key n _ _ ?_⟩, fun n ↦ key n _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[factorial_mul_dpow_eq_pow _ (Q.algebraMap_mem_ext ha), ← map_pow, ← factorial_mul_dpow_eq_pow δ ha, map_mul, map_natCast]`.

Rewrite using `[factorial_mul_dpow_eq_pow _ (Q.e_one_mem_ext J), Q.e_one_pow]`.
-/
theorem exists_isStd_of_injective (K : Type) [CommRing K] [Algebra ℚ K] [Algebra B K]
    (hK : Function.Injective (algebraMap B K)) (Q : PDPoly B) (δ : DividedPowers J) :
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  classical
  haveI : Module.Free B Q.P := Module.Free.of_basis Q.e
  let f : Q.P →+* K ⊗[B] Q.P := (Algebra.TensorProduct.includeRight (R := B) (A := K) (B := Q.P)).toRingHom
  have hf : Function.Injective f := Algebra.TensorProduct.includeRight_injective hK
  letI : Algebra ℚ (K ⊗[B] Q.P) := ((algebraMap K (K ⊗[B] Q.P)).comp (algebraMap ℚ K)).toAlgebra
  have keyC : ∀ (n : ℕ) (x y : K ⊗[B] Q.P), (n.factorial : K ⊗[B] Q.P) * x = n.factorial * y → x = y :=
    fun n x y h ↦ (IsUnit.natCast_factorial_of_algebra (A := K ⊗[B] Q.P) ℚ n).mul_left_cancel h
  have key : ∀ (n : ℕ) (x y : Q.P), (n.factorial : Q.P) * x = n.factorial * y → x = y :=
    fun n x y h ↦ hf (keyC n _ _ (by simpa using congrArg f h))
  let κ : DividedPowers ((Q.ext J).map f) := RatAlgebra.dividedPowers _
  have hmem : ∀ (n : ℕ) {x : Q.P} (_ : x ∈ Q.ext J), ∃ (y : Q.P) (_ : n ≠ 0 → y ∈ Q.ext J),
      f y = κ.dpow n (f x) := by
    intro n x hx
    have hs : Q.ext J = Ideal.span (algebraMap B Q.P '' J ∪ Set.range fun n : ℕ ↦ Q.e (n + 1)) := by
      rw [Ideal.span_union]; rfl
    have hx' := hx
    rw [hs] at hx'
    revert n
    refine Submodule.span_induction (p := fun x _ ↦ ∀ n, ∃ (y : Q.P) (_ : n ≠ 0 → y ∈ Q.ext J),
      f y = κ.dpow n (f x)) ?_ ?_ ?_ ?_ hx'
    · rintro _ (⟨j, hj, rfl⟩ | ⟨k, rfl⟩) n
      · refine ⟨algebraMap B Q.P (δ.dpow n j), fun hn ↦ Q.algebraMap_mem_ext (δ.dpow_mem hn hj), keyC n _ _ ?_⟩
        rw [factorial_mul_dpow_eq_pow _ (Ideal.mem_map_of_mem f (Q.algebraMap_mem_ext hj)), ← map_pow, ← map_pow,
          ← factorial_mul_dpow_eq_pow δ hj, map_mul, map_natCast, map_mul, map_natCast]
      · refine ⟨(Nat.uniformBell n (k + 1) : Q.P) * Q.e (n * (k + 1)), fun hn ↦ ?_, ?_⟩
        · obtain ⟨m, hm⟩ : ∃ m, n * (k + 1) = m + 1 := Nat.exists_eq_succ_of_ne_zero (by positivity)
          rw [hm]
          exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Q.e_succ_mem_aug m))
        · have he : ∀ m, f (Q.e m) = κ.dpow m (f (Q.e 1)) := fun m ↦ keyC m _ _ (by
            rw [factorial_mul_dpow_eq_pow _ (Ideal.mem_map_of_mem f (Q.e_one_mem_ext J)), ← map_pow, Q.e_one_pow,
              map_mul, map_natCast])
          beta_reduce
          rw [map_mul, map_natCast, he, he (k + 1),
            κ.dpow_comp (by omega) (Ideal.mem_map_of_mem f (Q.e_one_mem_ext J))]
    · intro n
      rcases n with _ | n
      · exact ⟨1, by simp, by rw [map_one, map_zero, κ.dpow_zero (zero_mem _)]⟩
      · exact ⟨0, fun _ ↦ zero_mem _, by rw [map_zero, κ.dpow_eval_zero (by omega)]⟩
    · intro x y hx hy ihx ihy n
      replace hx : x ∈ Q.ext J := hs.ge hx
      replace hy : y ∈ Q.ext J := hs.ge hy
      choose u hu hu' using ihx
      choose v hv hv' using ihy
      refine ⟨∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, u k.1 * v k.2, fun hn ↦ Ideal.sum_mem _ fun k hk ↦ ?_, ?_⟩
      · rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
        by_cases h0 : k.1 = 0
        · exact Ideal.mul_mem_left _ _ (hv _ (by omega))
        · exact Ideal.mul_mem_right _ _ (hu _ h0)
      · rw [map_add, κ.dpow_add (Ideal.mem_map_of_mem f hx) (Ideal.mem_map_of_mem f hy), map_sum]
        simp only [map_mul, hu', hv']
    · intro a x hx ih n
      replace hx : x ∈ Q.ext J := hs.ge hx
      obtain ⟨y, hy, hy'⟩ := ih n
      refine ⟨a ^ n * y, fun hn ↦ Ideal.mul_mem_left _ _ (hy hn), ?_⟩
      rw [smul_eq_mul, map_mul, map_mul, κ.dpow_mul (Ideal.mem_map_of_mem f hx), hy', map_pow]
  refine ⟨DividedPowers.ofInjective _ _ f hf κ rfl hmem, ⟨le_sup_left, fun {n} a ha ↦ key n _ _ ?_⟩,
    fun n ↦ key n _ _ ?_⟩
  · rw [factorial_mul_dpow_eq_pow _ (Q.algebraMap_mem_ext ha), ← map_pow,
      ← factorial_mul_dpow_eq_pow δ ha, map_mul, map_natCast]
  · rw [factorial_mul_dpow_eq_pow _ (Q.e_one_mem_ext J), Q.e_one_pow]

/- English proof (translation)
The claim follows from `exists_isStd_of_injective ℚ (algebraMap ℤ ℚ).injective_int _ _`.
-/
theorem exists_isStd_int : ∃ η : DividedPowers ((stdPoly ℤ).ext ⊥), (stdPoly ℤ).IsStd (dividedPowersBot ℤ) η :=
  exists_isStd_of_injective ℚ (algebraMap ℤ ℚ).injective_int _ _

/- English proof (translation)
The claim follows from `exists_isStd_of_injective ℚ_[p] (IsFractionRing.injective ℤ_[p] ℚ_[p]) _ _`.
-/
theorem exists_isStd_padic (p : ℕ) [Fact p.Prime] :
    ∃ η : DividedPowers ((stdPoly ℤ_[p]).ext (Ideal.span {(p : ℤ_[p])})),
      (stdPoly ℤ_[p]).IsStd (PadicInt.dividedPowers p) η :=
  exists_isStd_of_injective ℚ_[p] (IsFractionRing.injective ℤ_[p] ℚ_[p]) _ _

def gam (n : ℕ) (x : ZMod 4) : ZMod 4 :=
  if x = 0 ∨ x = 2 then (if n = 0 then 1 else if n = 1 ∨ n = 4 then x else 0) else 0

/- English proof (translation)
Rewrite using `[Ideal.mem_span_singleton']`. Use `revert x`. Evaluate the decidable proposition.
-/
theorem mem_two (x : ZMod 4) : x ∈ Ideal.span {(2 : ZMod 4)} ↔ x = 0 ∨ x = 2 := by
  rw [Ideal.mem_span_singleton']; revert x; decide

/- English proof (translation)
Unfold `gam`. Simplify using `only [hm, hn, if_false]`. Apply the tactic sequence `by_cases h1 : m = 1 ∨ m = 4 <;> by_cases h2 : n = 1 ∨ n = 4 <;> simp only [h1, h2] <;> revert x y <;> decide`.
-/
theorem gam_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (x y : ZMod 4) : gam m x * gam n y = 0 := by
  unfold gam
  simp only [hm, hn, if_false]
  by_cases h1 : m = 1 ∨ m = 4 <;> by_cases h2 : n = 1 ∨ n = 4 <;> simp only [h1, h2] <;> revert x y <;> decide

/- English proof (translation)
Use `⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun δ h ↦ ?_⟩` and prove the remaining obligations. Introduce `n x hx`. Rewrite `hx` using `[mem_two]`. Simplify using `only [gam, hx, if_false]`. Introduce `x hx`.

Rewrite `hx` using `[mem_two]`. Simplify using `[gam, hx]`. Introduce `x hx`. Rewrite `hx` using `[mem_two]`. Simplify using `[gam, hx]`.

Apply the tactic sequence `intro n hn x hx; rw [mem_two] at hx ⊢; simp only [gam, hx, hn, if_true, if_false]; split_ifs <;> simp [hx]`. Introduce `n x hx y hy`. Rewrite `hx`, `hy` using `[mem_two]`. Break down `n with _ | n` into its components or cases. Simplify using `only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton] revert x y`.

Evaluate the decidable proposition. Rewrite using `[Finset.Nat.sum_antidiagonal_succ]`. Break down `n with _ | n` into its components or cases. Simplify using `only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton] revert x y`. Evaluate the decidable proposition.

Rewrite using `[Finset.Nat.sum_antidiagonal_succ', Finset.sum_eq_zero fun k _ ↦ gam_mul _ _ (by omega) (by omega) _ _]`. Simplify using `only [gam, add_zero]`. Apply the tactic sequence `by_cases h : n + 1 + 1 = 1 ∨ n + 1 + 1 = 4 <;> simp only [h] <;> simp <;> revert x y <;> decide`. Introduce `n a x hx`. Rewrite `hx` using `[mem_two]`.

Distinguish the cases in `h0 : n = 0`. Substitute `h0` using the available equality. Use `revert a x`. Evaluate the decidable proposition. Distinguish the cases in `h1 : n = 1`.

Substitute `h1` using the available equality. Use `revert a x`. Evaluate the decidable proposition. Distinguish the cases in `h4 : n = 4`. Substitute `h4` using the available equality.

Use `revert a x`. Evaluate the decidable proposition. Simplify using `[gam, h0, h1, h4]`. Introduce `m n x hx`. Rewrite `hx` using `[mem_two]`.

Distinguish the cases in `hm : m = 0`. Substitute `hm` using the available equality. Simplify using `[gam, hx]`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality.

Simplify using `[gam, hx]`. Rewrite using `[gam_mul m n hm hn]`. Distinguish the cases in `h4 : m + n = 4`. Establish `: m = 1 ∧ n = 3 ∨ m = 2 ∧ n = 2 ∨ m = 3 ∧ n = 1` using `by omega`. Apply the tactic sequence `rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert x <;> decide`.

Establish `h1 : m + n ≠ 1` using `by omega`. Establish `h0 : m + n ≠ 0` using `by omega`. Simplify using `only [gam, h0, h1, h4]`. Simplify using the standard rewrite rules. Use `δ.dpow_comp (m := 2) (n := 2) (x := 2) (by omega) ((mem_two 2).2 (Or.inr rfl))` as an intermediate fact.

Rewrite `this` using `[h]`. Establish `hb : Nat.uniformBell 2 2 = 3`. Use `Nat.uniformBell_mul_eq 2 (n := 2) (by omega)` as an intermediate fact. Simplify using `[Nat.factorial] at this`. Use linear arithmetic over natural numbers and integers.

Rewrite `this` using `[hb]`. Use `revert this`. Evaluate the decidable proposition.
-/
theorem gam_isPreDP_and_ne_dpow : IsPreDP (Ideal.span {(2 : ZMod 4)}) gam ∧
    ∀ δ : DividedPowers (Ideal.span {(2 : ZMod 4)}), δ.dpow ≠ gam := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun δ h ↦ ?_⟩
  · intro n x hx; rw [mem_two] at hx; simp only [gam, hx, if_false]
  · intro x hx; rw [mem_two] at hx; simp [gam, hx]
  · intro x hx; rw [mem_two] at hx; simp [gam, hx]
  · intro n hn x hx; rw [mem_two] at hx ⊢; simp only [gam, hx, hn, if_true, if_false]; split_ifs <;> simp [hx]
  · intro n x hx y hy
    rw [mem_two] at hx hy
    rcases n with _ | n
    · simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      revert x y; decide
    · rw [Finset.Nat.sum_antidiagonal_succ]
      rcases n with _ | n
      · simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
        revert x y; decide
      · rw [Finset.Nat.sum_antidiagonal_succ', Finset.sum_eq_zero fun k _ ↦ gam_mul _ _ (by omega) (by omega) _ _]
        simp only [gam, add_zero]
        by_cases h : n + 1 + 1 = 1 ∨ n + 1 + 1 = 4 <;> simp only [h] <;> simp <;> revert x y <;> decide
  · intro n a x hx
    rw [mem_two] at hx
    by_cases h0 : n = 0
    · subst h0; revert a x; decide
    by_cases h1 : n = 1
    · subst h1; revert a x; decide
    by_cases h4 : n = 4
    · subst h4; revert a x; decide
    simp [gam, h0, h1, h4]
  · intro m n x hx
    rw [mem_two] at hx
    by_cases hm : m = 0
    · subst hm; simp [gam, hx]
    by_cases hn : n = 0
    · subst hn; simp [gam, hx]
    rw [gam_mul m n hm hn]
    by_cases h4 : m + n = 4
    · have : m = 1 ∧ n = 3 ∨ m = 2 ∧ n = 2 ∨ m = 3 ∧ n = 1 := by omega
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert x <;> decide
    · have h1 : m + n ≠ 1 := by omega
      have h0 : m + n ≠ 0 := by omega
      simp only [gam, h0, h1, h4]; simp
  · have := δ.dpow_comp (m := 2) (n := 2) (x := 2) (by omega) ((mem_two 2).2 (Or.inr rfl))
    rw [h] at this
    have hb : Nat.uniformBell 2 2 = 3 := by
      have := Nat.uniformBell_mul_eq 2 (n := 2) (by omega)
      simp [Nat.factorial] at this; omega
    rw [hb] at this
    revert this; decide

end GlobalTheory.PDA.Model
