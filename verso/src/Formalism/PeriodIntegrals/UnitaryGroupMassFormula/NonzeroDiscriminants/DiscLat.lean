import Mathlib
import Formalism.PeriodIntegrals.DiscrNe

open ModularForm EisensteinSeries UpperHalfPlane

noncomputable section

namespace DiscrNeWork

/- English proof (translation)
Establish `him` using `congrArg Complex.im h`. Use `first`. Consider the case `simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at him`. Consider the case `simp at him`. Establish `key : ((m : ℝ) - m') * (τ : ℂ).im = 0` using `by first`.

Consider the case `linear_combination him`. Consider the case `linarith`. Establish `hpos : 0 < (τ : ℂ).im` using `τ.im_pos`. Establish `hsub : (m : ℝ) - m' = 0` using `(mul_eq_zero.mp key).resolve_right hpos.ne'`. Establish `hm : m = m'` using `by exact_mod_cast sub_eq_zero.mp hsub`.

Substitute `hm` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Establish `hn : (n : ℂ) = n'` using `add_left_cancel h`. Conclude with `hn` after adjusting the coercions.
-/
lemma lin_inj (τ : ℍ) {m n m' n' : ℤ} (h : (m : ℂ) * τ + n = (m' : ℂ) * τ + n') :
    m = m' ∧ n = n' := by
  have him := congrArg Complex.im h
  first
    | simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at him
    | simp at him
  have key : ((m : ℝ) - m') * (τ : ℂ).im = 0 := by
    first
      | linear_combination him
      | linarith
  have hpos : 0 < (τ : ℂ).im := τ.im_pos
  have hsub : (m : ℝ) - m' = 0 := (mul_eq_zero.mp key).resolve_right hpos.ne'
  have hm : m = m' := by exact_mod_cast sub_eq_zero.mp hsub
  subst hm
  refine ⟨rfl, ?_⟩
  have hn : (n : ℂ) = n' := add_left_cancel h
  exact_mod_cast hn

/- English proof (translation)
Introduce `h0`. Apply `hv` to reduce the goal to its premises. Establish `h' : ((v 0 : ℤ) : ℂ) * τ + ((v 1 : ℤ) : ℂ) = ((0 : ℤ) : ℂ) * τ + ((0 : ℤ) : ℂ)` using `by first`. Consider the case `(rw [h0]; simp)`. Consider the case `simpa using h0`.

Take `⟨h1, h2⟩` from `lin_inj τ h'`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `h1`. Conclude with `h2`.
-/
lemma lin_ne (τ : ℍ) (v : Fin 2 → ℤ) (hv : v ≠ 0) : ((v 0 : ℂ) * τ + v 1) ≠ 0 := by
  intro h0
  apply hv
  have h' : ((v 0 : ℤ) : ℂ) * τ + ((v 1 : ℤ) : ℂ) = ((0 : ℤ) : ℂ) * τ + ((0 : ℤ) : ℂ) := by
    first
      | (rw [h0]; simp)
      | simpa using h0
  obtain ⟨h1, h2⟩ := lin_inj τ h'
  funext i
  fin_cases i
  · exact h1
  · exact h2

def nz : Set (Fin 2 → ℤ) := {v | v ≠ 0}

def toLat (a : ℂ) (ha : a ≠ 0) (τ : ℍ) (v : nz) :
    {w : ℂ // w ∈ PI.lat2 a (a * τ) ∧ w ≠ 0} :=
  ⟨a * ((v.1 0 : ℂ) * τ + v.1 1), by
    refine ⟨?_, mul_ne_zero ha (lin_ne τ v.1 v.2)⟩
    rw [PI.lat2, AddSubgroup.mem_closure_pair]
    exact ⟨v.1 1, v.1 0, by simp only [zsmul_eq_mul]; ring⟩⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `v v' hvv`. Establish `h1 : a * ((v.1 0 : ℂ) * τ + v.1 1) = a * ((v'.1 0 : ℂ) * τ + v'.1 1)` using `congrArg Subtype.val hvv`. Establish `h2` using `mul_left_cancel₀ ha h1`. Take `⟨e0, e1⟩` from `lin_inj τ h2`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `e0`. Conclude with `e1`.

Introduce and unpack `⟨w, hw, hw0⟩`. Establish `hw'` using `hw`. Rewrite `hw'` using `[PI.lat2, AddSubgroup.mem_closure_pair]`. Take `⟨m, n, hmn⟩` from `hw'`. Establish `hv : (![n, m] : Fin 2 → ℤ) ∈ nz`.

Introduce `h`. Apply `hw0` to reduce the goal to its premises. Establish `hn : n = 0` using `congrFun h 0`. Establish `hm : m = 0` using `congrFun h 1`. Rewrite using `[← hmn, hn, hm]`.

Simplify using the standard rewrite rules. Use `⟨⟨![n, m], hv⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show a * ((((![n, m] : Fin 2 → ℤ) 0 : ℤ) : ℂ) * (τ : ℂ) + (((![n, m] : Fin 2 → ℤ) 1 : ℤ) : ℂ)) = w`. Establish `e0 : (![n, m] : Fin 2 → ℤ) 0 = n` using `rfl`.

Establish `e1 : (![n, m] : Fin 2 → ℤ) 1 = m` using `rfl`. Rewrite using `[e0, e1, ← hmn, zsmul_eq_mul, zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma toLat_bij (a : ℂ) (ha : a ≠ 0) (τ : ℍ) : Function.Bijective (toLat a ha τ) := by
  constructor
  · intro v v' hvv
    have h1 : a * ((v.1 0 : ℂ) * τ + v.1 1) = a * ((v'.1 0 : ℂ) * τ + v'.1 1) :=
      congrArg Subtype.val hvv
    have h2 := mul_left_cancel₀ ha h1
    obtain ⟨e0, e1⟩ := lin_inj τ h2
    apply Subtype.ext
    funext i
    fin_cases i
    · exact e0
    · exact e1
  · rintro ⟨w, hw, hw0⟩
    have hw' := hw
    rw [PI.lat2, AddSubgroup.mem_closure_pair] at hw'
    obtain ⟨m, n, hmn⟩ := hw'
    have hv : (![n, m] : Fin 2 → ℤ) ∈ nz := by
      intro h
      apply hw0
      have hn : n = 0 := congrFun h 0
      have hm : m = 0 := congrFun h 1
      rw [← hmn, hn, hm]
      simp
    refine ⟨⟨![n, m], hv⟩, ?_⟩
    apply Subtype.ext
    show a * ((((![n, m] : Fin 2 → ℤ) 0 : ℤ) : ℂ) * (τ : ℂ) + (((![n, m] : Fin 2 → ℤ) 1 : ℤ) : ℂ)) = w
    have e0 : (![n, m] : Fin 2 → ℤ) 0 = n := rfl
    have e1 : (![n, m] : Fin 2 → ℤ) 1 = m := rfl
    rw [e0, e1, ← hmn, zsmul_eq_mul, zsmul_eq_mul]
    ring

/- English proof (translation)
Establish `hk2 : 2 * k ≠ 0` using `by omega`. Set `e` to `Equiv.ofBijective _ (toLat_bij a ha τ)`. Establish `hterm : ∀ v : nz, 1 / ((e v : ℂ)) ^ (2 * k) = (a ^ (2 * k))⁻¹ * eisSummand ((2 * k : ℕ) : ℤ) v.1 τ`. Introduce `v`. Establish `hX : eisSummand ((2 * k : ℕ) : ℤ) v.1 τ = 1 / ((v.1 0 : ℂ) * (τ : ℂ) + (v.1 1 : ℂ)) ^ (2 * k)` using `by first`.

Consider the case `((simp only [eisSummand, zpow_neg, zpow_natCast, one_div]) <;> rfl)`. Consider the case `(simp [eisSummand, zpow_natCast, one_div])`. Consider the case `(rw [eisSummand, zpow_neg, zpow_natCast, one_div])`. Consider the case `(unfold eisSummand; done)`. Use `show 1 / (a * ((v.1 0 : ℂ) * (τ : ℂ) + (v.1 1 : ℂ))) ^ (2 * k) = _`.

Rewrite using `[hX]`. Use `first`. Consider the case `(rw [mul_pow, one_div, one_div, mul_inv])`. Consider the case `ring`. Establish `hsupp : Function.support (fun v : Fin 2 → ℤ => eisSummand ((2 * k : ℕ) : ℤ) v τ) ⊆ nz`.

Introduce `v hv`. Use `show v ≠ 0`. Introduce and unpack `rfl`. Apply `hv` to reduce the goal to its premises. Use `first`.

Consider the case `(simp only [eisSummand, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, zpow_neg, zpow_natCast, zero_pow hk2, inv_zero, one_div])`. Consider the case `(simp [eisSummand, hk2])`. Consider the case `(unfold eisSummand; done)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[tsum_subtype_eq_of_support_subset (f := fun v : Fin 2 → ℤ => eisSummand ((2 * k : ℕ) : ℤ) v τ) hsupp]`.
-/
theorem eisG_eq (a : ℂ) (ha : a ≠ 0) (τ : ℍ) (k : ℕ) (hk : 1 ≤ k) :
    PI.eisG (PI.lat2 a (a * τ)) k =
      (a ^ (2 * k))⁻¹ * ∑' v : Fin 2 → ℤ, eisSummand ((2 * k : ℕ) : ℤ) v τ := by
  have hk2 : 2 * k ≠ 0 := by omega
  let e := Equiv.ofBijective _ (toLat_bij a ha τ)
  have hterm : ∀ v : nz, 1 / ((e v : ℂ)) ^ (2 * k) =
      (a ^ (2 * k))⁻¹ * eisSummand ((2 * k : ℕ) : ℤ) v.1 τ := by
    intro v
    have hX : eisSummand ((2 * k : ℕ) : ℤ) v.1 τ =
        1 / ((v.1 0 : ℂ) * (τ : ℂ) + (v.1 1 : ℂ)) ^ (2 * k) := by
      first
        | ((simp only [eisSummand, zpow_neg, zpow_natCast, one_div]) <;> rfl)
        | (simp [eisSummand, zpow_natCast, one_div])
        | (rw [eisSummand, zpow_neg, zpow_natCast, one_div])
        | (unfold eisSummand; done)
    show 1 / (a * ((v.1 0 : ℂ) * (τ : ℂ) + (v.1 1 : ℂ))) ^ (2 * k) = _
    rw [hX]
    first
      | (rw [mul_pow, one_div, one_div, mul_inv])
      | ring
  have hsupp : Function.support (fun v : Fin 2 → ℤ => eisSummand ((2 * k : ℕ) : ℤ) v τ) ⊆
      nz := by
    intro v hv
    show v ≠ 0
    rintro rfl
    apply hv
    first
      | (simp only [eisSummand, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, zpow_neg,
          zpow_natCast, zero_pow hk2, inv_zero, one_div])
      | (simp [eisSummand, hk2])
      | (unfold eisSummand; done)
  calc PI.eisG (PI.lat2 a (a * τ)) k
      = ∑' w : {w : ℂ // w ∈ PI.lat2 a (a * τ) ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k) := rfl
    _ = ∑' v : nz, 1 / ((e v : ℂ)) ^ (2 * k) :=
        (e.tsum_eq (fun w : {w : ℂ // w ∈ PI.lat2 a (a * τ) ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k))).symm
    _ = ∑' v : nz, (a ^ (2 * k))⁻¹ * eisSummand ((2 * k : ℕ) : ℤ) v.1 τ :=
        tsum_congr hterm
    _ = (a ^ (2 * k))⁻¹ * ∑' v : nz, eisSummand ((2 * k : ℕ) : ℤ) v.1 τ :=
        tsum_mul_left
    _ = (a ^ (2 * k))⁻¹ * ∑' v : Fin 2 → ℤ, eisSummand ((2 * k : ℕ) : ℤ) v τ := by
        rw [tsum_subtype_eq_of_support_subset
          (f := fun v : Fin 2 → ℤ => eisSummand ((2 * k : ℕ) : ℤ) v τ) hsupp]

end DiscrNeWork

end
