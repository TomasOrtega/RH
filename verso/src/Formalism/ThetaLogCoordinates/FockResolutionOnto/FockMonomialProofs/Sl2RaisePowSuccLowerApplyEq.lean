import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementD

namespace Formalism.InvariantFactorPaths.L4

section
variable {k V : Type} [Field k] [CharZero k] [AddCommGroup V] [Module k V] {e f h : V →ₗ[k] V}

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [hu]`. Consider the case `succ m ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Establish `h1` using `he ((e ^ m) u)`.

Rewrite `h1` using `[sub_eq_iff_eq_add]`. Rewrite using `[h1, ih, map_smul, ← add_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sl2_weight_raise_pow_apply_eq (he : ∀ x, h (e x) - e (h x) = (2 : k) • e x) {u : V} {μ : k} (hu : h u = μ • u) (m : ℕ) :
    h ((e ^ m) u) = (μ + 2 * (m : k)) • (e ^ m) u := by
  induction m with
  | zero => simp [hu]
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h1 := he ((e ^ m) u)
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, ih, map_smul, ← add_smul]
    congr 1
    push_cast
    ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Establish `h1` using `hef u`. Rewrite `h1` using `[sub_eq_iff_eq_add]`. Simplify using `only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero, one_mul]`.

Rewrite using `[h1, hu, add_comm]`. Consider the case `succ m ih`. Establish `hs : e ((e ^ m) u) = (e ^ (m + 1)) u` using `by rw [pow_succ', Module.End.mul_apply]`. Rewrite using `[pow_succ' e (m + 1), Module.End.mul_apply, Module.End.mul_apply, ih, map_add, map_smul]`. Establish `h1` using `hef ((e ^ (m + 1)) u)`.

Rewrite `h1` using `[sub_eq_iff_eq_add]`. Rewrite using `[h1, sl2_weight_raise_pow_apply_eq he hu (m + 1), hs, add_comm (_ • _) (f _), add_assoc, ← add_smul]`. Use `congr 1`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sl2_raise_pow_succ_lower_apply_eq (he : ∀ x, h (e x) - e (h x) = (2 : k) • e x) (hef : ∀ x, e (f x) - f (e x) = h x)
    {u : V} {μ : k} (hu : h u = μ • u) (m : ℕ) :
    (e ^ (m + 1)) (f u) = f ((e ^ (m + 1)) u) + (((m : k) + 1) * (μ + (m : k))) • (e ^ m) u := by
  induction m with
  | zero =>
    have h1 := hef u
    rw [sub_eq_iff_eq_add] at h1
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero, one_mul]
    rw [h1, hu, add_comm]
  | succ m ih =>
    have hs : e ((e ^ m) u) = (e ^ (m + 1)) u := by rw [pow_succ', Module.End.mul_apply]
    rw [pow_succ' e (m + 1), Module.End.mul_apply, Module.End.mul_apply, ih, map_add, map_smul]
    have h1 := hef ((e ^ (m + 1)) u)
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, sl2_weight_raise_pow_apply_eq he hu (m + 1), hs, add_comm (_ • _) (f _), add_assoc, ← add_smul]
    congr 1
    congr 1
    push_cast
    ring

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ h0`. Simplify using `using h0`.

Consider the case `succ j ih`. Introduce `hj h0`. Apply `ih (by omega)` to reduce the goal to its premises. Establish `hc` using `sl2_raise_pow_succ_lower_apply_eq he hef hu j`. Rewrite `hc` using `[hf, map_zero, h0, map_zero, zero_add]`.

Establish `hne : ((j : k) + 1) * (((μ : ℤ) : k) + (j : k)) ≠ 0`. Apply `mul_ne_zero` to reduce the goal to its premises. Conclude with `Nat.succ_ne_zero j` after adjusting the coercions. Establish `h5 : (μ + j : ℤ) ≠ 0` using `by omega`. Conclude with `h5` after adjusting the coercions.

Conclude with `(smul_eq_zero.mp hc.symm).resolve_left hne`.
-/
theorem sl2_eq_zero_of_lower_zero_of_raise_pow_zero (he : ∀ x, h (e x) - e (h x) = (2 : k) • e x) (hef : ∀ x, e (f x) - f (e x) = h x)
    {u : V} {μ : ℤ} (hu : h u = ((μ : ℤ) : k) • u) (hf : f u = 0) :
    ∀ j : ℕ, μ + j ≤ 0 → (e ^ j) u = 0 → u = 0 := by
  intro j
  induction j with
  | zero =>
    intro _ h0
    simpa using h0
  | succ j ih =>
    intro hj h0
    apply ih (by omega)
    have hc := sl2_raise_pow_succ_lower_apply_eq he hef hu j
    rw [hf, map_zero, h0, map_zero, zero_add] at hc
    have hne : ((j : k) + 1) * (((μ : ℤ) : k) + (j : k)) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Nat.succ_ne_zero j
      · have h5 : (μ + j : ℤ) ≠ 0 := by omega
        exact_mod_cast h5
    exact (smul_eq_zero.mp hc.symm).resolve_left hne

end

/- English proof (translation)
Introduce `k V _ _ _ _ e f h he hf hef u μ j hu hex hj h0`. Take `⟨s, hs⟩` from `hex`. Proceed by induction on `s generalizing u μ j with`. Consider the case `zero => simpa using hs`. Consider the case `succ s ih`.

Establish `hfu : f u = 0`. Apply `ih (f u) (μ - 2) (j + 1)` to reduce the goal to its premises. Establish `h1` using `hf u`. Rewrite `h1` using `[hu, map_smul, sub_eq_iff_eq_add]`. Rewrite using `[h1]`.

Use `push_cast`. Rewrite using `[sub_smul]`. Normalize the expressions using the abelian group laws. Use linear arithmetic over natural numbers and integers. Rewrite using `[sl2_raise_pow_succ_lower_apply_eq he hef hu j, pow_succ', Module.End.mul_apply, h0]`.

Simplify using the standard rewrite rules. Rewrite `hs` using `[pow_succ, Module.End.mul_apply]`. Conclude with `hs`. Conclude with `sl2_eq_zero_of_lower_zero_of_raise_pow_zero he hef hu hfu j hj h0`.
-/
theorem sl2_injectivity_holds : Sl2Injective := by
  intro k V _ _ _ _ e f h he hf hef u μ j hu hex hj h0
  obtain ⟨s, hs⟩ := hex
  induction s generalizing u μ j with
  | zero => simpa using hs
  | succ s ih =>
    have hfu : f u = 0 := by
      apply ih (f u) (μ - 2) (j + 1)
      · have h1 := hf u
        rw [hu, map_smul, sub_eq_iff_eq_add] at h1
        rw [h1]
        push_cast
        rw [sub_smul]
        abel
      · omega
      · rw [sl2_raise_pow_succ_lower_apply_eq he hef hu j, pow_succ', Module.End.mul_apply, h0]
        simp
      · rw [pow_succ, Module.End.mul_apply] at hs
        exact hs
    exact sl2_eq_zero_of_lower_zero_of_raise_pow_zero he hef hu hfu j hj h0

end Formalism.InvariantFactorPaths.L4
