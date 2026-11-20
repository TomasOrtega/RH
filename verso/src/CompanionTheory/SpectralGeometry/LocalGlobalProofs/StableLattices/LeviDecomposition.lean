import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.BesselLevi

def pr (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if outer k r i then ⟨2 * r + k - i.val, by omega⟩ else i

/- English proof (translation)
Unfold `pr`. Use `i.isLt` as an intermediate fact. Distinguish the cases in `h : outer k r i`. Rewrite using `[if_pos h] left`. Use `⟨h, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h]`. Unfold `outer at h`. Use `right`.

Use linear arithmetic over natural numbers and integers.
-/
theorem pr_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    ((i.val ≤ r ∨ r + k ≤ i.val) ∧ (pr k r i).val + i.val = 2 * r + k) ∨
      (r < i.val ∧ i.val < r + k ∧ (pr k r i).val = i.val) := by
  unfold pr
  have := i.isLt
  by_cases h : outer k r i
  · rw [if_pos h]
    left
    refine ⟨h, ?_⟩
    simp only
    omega
  · rw [if_neg h]
    unfold outer at h
    right
    omega

/- English proof (translation)
Establish `h1` using `pr_val k r i`. Establish `h2` using `pr_val k r (pr k r i)`. Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
theorem pr_pr (k r : ℕ) (i : Fin (2 * r + k + 1)) : pr k r (pr k r i) = i := by
  have h1 := pr_val k r i
  have h2 := pr_val k r (pr k r i)
  apply Fin.ext
  omega

/- English proof (translation)
Establish `h1` using `pr_val k r i`. Unfold `Hq`. Distinguish the cases in `h : outer k r i`. Rewrite using `[if_pos h]`. Unfold `outer at h`.

Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Rewrite using `[Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h]`. Unfold `outer at h`.

Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Rewrite using `[Fin.ext_iff, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Hq_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hq k r i j = if pr k r i = j then 1 else 0 := by
  have h1 := pr_val k r i
  unfold Hq
  by_cases h : outer k r i
  · rw [if_pos h]
    unfold outer at h
    refine if_congr ?_ rfl rfl
    rw [Fin.ext_iff]
    omega
  · rw [if_neg h]
    unfold outer at h
    refine if_congr ?_ rfl rfl
    rw [Fin.ext_iff, Fin.ext_iff]
    omega

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Hq_apply]`.
-/
theorem Hq_mul_apply (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hq k r * g) i j = g (pr k r i) j := by
  simp [Matrix.mul_apply, Hq_apply]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Hq_mul_apply, Hq_apply, pr_pr, Matrix.one_apply]`.
-/
theorem Hq_sq (k r : ℕ) : Hq k r * Hq k r = 1 := by
  ext i j
  rw [Hq_mul_apply, Hq_apply, pr_pr, Matrix.one_apply]

/- English proof (translation)
Unfold `UH`. Rewrite using `[Set.mem_setOf_eq, Matrix.mul_assoc, ← Matrix.ext_iff]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Hq_apply]`. Simplify using `only [Hq_mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]`.
-/
theorem mem_iff (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ UH (Hq k r) ↔ ∀ i j, ∑ x, conj (g x i) * g (pr k r x) j = if pr k r i = j then 1 else 0 := by
  unfold UH
  rw [Set.mem_setOf_eq, Matrix.mul_assoc, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.mul_apply, Hq_apply]
  simp only [Hq_mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]

/- English proof (translation)
Unfold `UH at *`. Rewrite `*` using `[Set.mem_setOf_eq]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = H := by rw [hg, hh]`.
-/
theorem mul_mem {n : ℕ} {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (hh : h ∈ UH H) :
    g * h ∈ UH H := by
  unfold UH at *
  rw [Set.mem_setOf_eq] at *
  calc (g * h)ᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = H := by rw [hg, hh]

/- English proof (translation)
Rewrite using `[mem_iff]`. Introduce `i j`. Rewrite using `[Finset.sum_eq_single i]`. Distinguish the cases in `h : pr k r i = j`. Substitute `h` using the available equality.

Simplify using `[hd]`. Simplify using `[h]`. Introduce `x _ hx`. Simplify using `[hx]`. Simplify using the standard rewrite rules.
-/
theorem diag_mem (k r : ℕ) (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, conj (d i) * d (pr k r i) = 1) :
    Matrix.diagonal d ∈ UH (Hq k r) := by
  rw [mem_iff]
  intro i j
  rw [Finset.sum_eq_single i]
  · by_cases h : pr k r i = j
    · subst h
      simp [hd]
    · simp [h]
  · intro x _ hx
    simp [hx]
  · simp

/- English proof (translation)
Introduce `k r hk s hs htri`. Establish `hz : ∀ i j : Fin (2 * r + k + 1), j.val < i.val → s i j = 0` using `fun i j h => htri h`. Establish `hs'` using `(mem_iff k r s).1 hs`. Set `mid : Fin (2 * r + k + 1) → Prop` to `fun i => r ≤ i.val ∧ i.val ≤ r + k`. Establish `hmidp : ∀ i, mid (pr k r i) ↔ mid i`.

Introduce `i`. Use `pr_val k r i` as an intermediate fact. Simplify using `only [mid]`. Use linear arithmetic over natural numbers and integers. Set `d : Fin (2 * r + k + 1) → ℂ` to `fun i => if mid i then 1 else s i i`.

Establish `hd : ∀ i, conj (d i) * d (pr k r i) = 1`. Introduce `i`. Distinguish the cases in `h : mid i`. Simplify using `[d, h, hmidp]`. Establish `h2` using `hs' i (pr k r i)`.

Rewrite `h2` using `[if_pos rfl, Finset.sum_eq_single i]`. Simplify `h2` using `[d, h, hmidp]`. Introduce `x _ hx`. Establish `e1` using `pr_val k r i`. Establish `e2` using `pr_val k r x`.

Establish `e3 : x.val ≠ i.val` using `fun e => hx (Fin.ext e)`. Simplify using `only [mid] at h`. Distinguish the cases in `hxi : i.val < x.val`. Rewrite using `[hz x i hxi]`. Simplify using the standard rewrite rules.

Rewrite using `[hz (pr k r x) (pr k r i) (by omega)]; simp`. Simplify using the standard rewrite rules. Establish `hdn : ∀ i, ‖d i‖ * ‖d (pr k r i)‖ = 1`. Introduce `i`. Use `congrArg norm (hd i)` as an intermediate fact.

Simplify using `using this`. Establish `hd0 : ∀ i, ‖d i‖ ≠ 0` using `fun i => left_ne_zero_of_mul_eq_one (hdn i)`. Establish `hd0' : ∀ i, ((‖d i‖ : ℝ) : ℂ) ≠ 0` using `fun i => by exact_mod_cast hd0 i`. Set `μ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ` to `fun i j => if mid i ∧ mid j then s i j else if i = j then 1 else 0`. Establish `hμ : μ ∈ UH (Hq k r)`.

Rewrite using `[mem_iff]`. Introduce `i j`. Distinguish the cases in `hi : mid i`. Distinguish the cases in `hj : mid j`. Rewrite using `[← hs' i j]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Distinguish the cases in `hx : mid x`. Simplify using `[μ, hi, hj, hx, hmidp]`. Establish `hxi : x ≠ i` using `fun e => hx (e ▸ hi)`. Establish `e2` using `pr_val k r x`.

Establish `: conj (s x i) * s (pr k r x) j = 0`. Simplify using `only [mid] at hi hj hx`. Distinguish the cases in `hxi : i.val < x.val`. Rewrite using `[hz x i hxi]`. Simplify using the standard rewrite rules.

Rewrite using `[hz (pr k r x) j (by omega)]; simp`. Rewrite using `[this]`. Simplify using `[μ, hx, hxi]`. Establish `hij : pr k r i ≠ j` using `fun e => hj (e ▸ (hmidp i).2 hi)`. Rewrite using `[if_neg hij]`.

Use `Finset.sum_eq_zero fun x _ => ?_` and prove the remaining obligations. Distinguish the cases in `hx : mid x`. Establish `: pr k r x ≠ j` using `fun e => hj (e ▸ (hmidp x).2 hx)`. Simplify using `[μ, hj, this]`. Establish `hxi : x ≠ i` using `fun e => hx (e ▸ hi)`.

Simplify using `[μ, hx, hxi]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[μ, hi, hmidp]`. Introduce `x _ hx`. Simplify using `[μ, hi, hx]`.

Simplify using the standard rewrite rules. Set `t : Fin (2 * r + k + 1) → ℝ` to `fun i => ‖d i‖`. Set `κ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ` to `Matrix.diagonal fun i => d i / (‖d i‖ : ℂ)`. Establish `hκ : κ ∈ UH (Hq k r)`. Apply `diag_mem` to reduce the goal to its premises.

Introduce `i`. Establish `h1 : ((‖d i‖ : ℝ) : ℂ) * ((‖d (pr k r i)‖ : ℝ) : ℂ) = 1` using `by exact_mod_cast hdn i`. Rewrite using `[map_div₀, Complex.conj_ofReal, div_mul_div_comm, hd, h1, div_one]`. Establish `ht : dg t ∈ UH (Hq k r)`. Apply `diag_mem` to reduce the goal to its premises.

Introduce `i`. Rewrite using `[Complex.conj_ofReal]`. Conclude with `hdn i` after adjusting the coercions. Take `⟨l, hl⟩ : ∃ l, l = dg t * μ * κ` from `⟨_, rfl⟩`. Establish `hlU : l ∈ UH (Hq k r)` using `hl ▸ mul_mem (mul_mem ht hμ) hκ`.

Establish `hle : ∀ i j, l i j = if mid i ∧ mid j then s i j else if i = j then s i i else 0`. Introduce `i j`. Establish `e1 : (dg t * μ) i j = ((‖d i‖ : ℝ) : ℂ) * μ i j` using `Matrix.diagonal_mul (fun i => ((‖d i‖ : ℝ) : ℂ)) μ i j`. Establish `e2 : (dg t * μ * κ) i j = (dg t * μ) i j * (d j / ((‖d j‖ : ℝ) : ℂ))` using `Matrix.mul_diagonal (fun i => d i / ((‖d i‖ : ℝ) : ℂ)) (dg t * μ) i j`. Rewrite using `[hl, e2, e1]`.

Distinguish the cases in `h : mid i ∧ mid j`. Simplify using `[d, μ, h.1, h.2]`. Establish `hμe : μ i j = if i = j then 1 else 0` using `if_neg h`. Rewrite using `[hμe, if_neg h]`. Distinguish the cases in `e : i = j`.

Substitute `e` using the available equality. Establish `hi : ¬ mid i` using `fun hi => h ⟨hi, hi⟩`. Use `hd0' i` as an intermediate fact. Rewrite using `[if_pos rfl, if_pos rfl, mul_one, mul_div_cancel₀ _ this]`. Simplify using `[d, hi]`.

Simplify using `[e]`. Establish `hltri : l.BlockTriangular id`. Introduce `i j hij`. Establish `hij' : j.val < i.val` using `hij`. Establish `: i ≠ j` using `fun e => by subst e; omega`.

Rewrite using `[hle, hz i j hij', if_neg this, ite_self]`. Establish `hinv : (Hq k r * lᴴ * Hq k r) * l = 1`. Establish `: lᴴ * Hq k r * l = Hq k r` using `hlU`. Combine the equalities or inequalities in the displayed calculation. Use `letI : Invertible l := invertibleOfLeftInverse _ _ hinv`.

Establish `hitri : l⁻¹.BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hltri`. Establish `hiz : ∀ i j : Fin (2 * r + k + 1), j.val < i.val → l⁻¹ i j = 0` using `fun i j h => hitri h`. Establish `hll : l * l⁻¹ = 1` using `Matrix.mul_inv_of_invertible l`. Establish `hiU : l⁻¹ ∈ UH (Hq k r)`. Establish `h1 : lᴴ * Hq k r * l = Hq k r` using `hlU`.

Express the relevant statement in the definitionally equal form `l⁻¹ᴴ * Hq k r * l⁻¹ = Hq k r`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hq k r := by rw [hll]; simp`.

Establish `hm : ∀ i j : Fin (2 * r + k + 1), (j.val ≤ i.val ∨ (mid i ∧ mid j)) → (s * l⁻¹) i j = if i = j then 1 else 0`. Introduce `i j hij`. Rewrite using `[← Matrix.one_apply, ← hll, Matrix.mul_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : j.val < x.val`.

Rewrite using `[hiz x j h1]`. Simplify using the standard rewrite rules. Distinguish the cases in `h2 : x.val < i.val`. Rewrite using `[hz i x h2, hltri (show id x < id i from h2)]`. Use `congr 1`.

Rewrite using `[hle]`. Distinguish the cases in `h3 : mid i ∧ mid x`. Rewrite using `[if_pos h3]`. Establish `: i = x`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [mid] at h3 hij`. Use linear arithmetic over natural numbers and integers. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Establish `hfix : ∀ x, ¬ mid x → μ *ᵥ bvec x = bvec x`.

Introduce `x hx`. Use extensionality with `i`. Establish `e1 : (μ *ᵥ bvec x) i = μ i x`. Simplify using `[Matrix.mulVec, dotProduct, bvec, Pi.single_apply]`. Establish `e2 : μ i x = if i = x then 1 else 0`.

Establish `: ¬ (mid i ∧ mid x)` using `fun h => hx h.2`. Conclude with `if_neg this`. Rewrite using `[e1, e2]`. Simplify using `[bvec, Pi.single_apply]`. Use `⟨s * l⁻¹, ⟨mul_mem hs hiU, fun a i hai => hm _ _ (Or.inl hai), fun i j h1 h2 h3 => hm _ _ ?_⟩, t, μ, ⟨hμ, fun a => ⟨?_, ?_⟩⟩, κ, hκ, ⟨fun i => ?_, fun i j hi hij => ?_, fun i hi => ?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [mid]`. Use linear arithmetic over natural numbers and integers. Establish `: ¬ mid (eI k r a)`. Use `a.isLt` as an intermediate fact. Simplify using `only [mid, eI]`.

Use linear arithmetic over natural numbers and integers. Conclude with `hfix _ this`. Establish `: ¬ mid (esI k r a)`. Use `a.isLt` as an intermediate fact. Simplify using `only [mid, esI]`.

Use linear arithmetic over natural numbers and integers. Conclude with `hfix _ this`. Conclude with `lt_of_le_of_ne (norm_nonneg _) (hd0 i).symm`. Establish `: pr k r i = j`. Use `pr_val k r i` as an intermediate fact.

Unfold `outer at hi`. Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Substitute `this` using the available equality. Conclude with `hdn i`.

Establish `: mid i`. Unfold `outer at hi`. Simplify using `only [mid]`. Use linear arithmetic over natural numbers and integers. Simplify using `[t, d, this]`.

Establish `: mid (wI k r 0)` using `by simp [mid, wI]`. Simplify using `[t, d, this]`. Establish `: mid (wI k r 0)` using `by simp [mid, wI]`. Simplify using `[t, d, this]`. Simplify using `only [κ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]`.

Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `i`. Use `hd0' i` as an intermediate fact. Simplify using `only [Pi.star_apply, RCLike.star_def]`.

Rewrite using `[map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.conj_mul']`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (dg t), ← hl, Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]`.
-/
theorem leviQ : LeviQ := by
  intro k r hk s hs htri
  have hz : ∀ i j : Fin (2 * r + k + 1), j.val < i.val → s i j = 0 := fun i j h => htri h
  have hs' := (mem_iff k r s).1 hs
  let mid : Fin (2 * r + k + 1) → Prop := fun i => r ≤ i.val ∧ i.val ≤ r + k
  have hmidp : ∀ i, mid (pr k r i) ↔ mid i := by
    intro i
    have := pr_val k r i
    simp only [mid]
    omega
  let d : Fin (2 * r + k + 1) → ℂ := fun i => if mid i then 1 else s i i
  have hd : ∀ i, conj (d i) * d (pr k r i) = 1 := by
    intro i
    by_cases h : mid i
    · simp [d, h, hmidp]
    · have h2 := hs' i (pr k r i)
      rw [if_pos rfl, Finset.sum_eq_single i] at h2
      · simpa [d, h, hmidp] using h2
      · intro x _ hx
        have e1 := pr_val k r i
        have e2 := pr_val k r x
        have e3 : x.val ≠ i.val := fun e => hx (Fin.ext e)
        simp only [mid] at h
        by_cases hxi : i.val < x.val
        · rw [hz x i hxi]; simp
        · rw [hz (pr k r x) (pr k r i) (by omega)]; simp
      · simp
  have hdn : ∀ i, ‖d i‖ * ‖d (pr k r i)‖ = 1 := by
    intro i
    have := congrArg norm (hd i)
    simpa using this
  have hd0 : ∀ i, ‖d i‖ ≠ 0 := fun i => left_ne_zero_of_mul_eq_one (hdn i)
  have hd0' : ∀ i, ((‖d i‖ : ℝ) : ℂ) ≠ 0 := fun i => by exact_mod_cast hd0 i
  let μ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
    if mid i ∧ mid j then s i j else if i = j then 1 else 0
  have hμ : μ ∈ UH (Hq k r) := by
    rw [mem_iff]
    intro i j
    by_cases hi : mid i
    · by_cases hj : mid j
      · rw [← hs' i j]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : mid x
        · simp [μ, hi, hj, hx, hmidp]
        · have hxi : x ≠ i := fun e => hx (e ▸ hi)
          have e2 := pr_val k r x
          have : conj (s x i) * s (pr k r x) j = 0 := by
            simp only [mid] at hi hj hx
            by_cases hxi : i.val < x.val
            · rw [hz x i hxi]; simp
            · rw [hz (pr k r x) j (by omega)]; simp
          rw [this]
          simp [μ, hx, hxi]
      · have hij : pr k r i ≠ j := fun e => hj (e ▸ (hmidp i).2 hi)
        rw [if_neg hij]
        refine Finset.sum_eq_zero fun x _ => ?_
        by_cases hx : mid x
        · have : pr k r x ≠ j := fun e => hj (e ▸ (hmidp x).2 hx)
          simp [μ, hj, this]
        · have hxi : x ≠ i := fun e => hx (e ▸ hi)
          simp [μ, hx, hxi]
    · rw [Finset.sum_eq_single i]
      · simp [μ, hi, hmidp]
      · intro x _ hx
        simp [μ, hi, hx]
      · simp
  let t : Fin (2 * r + k + 1) → ℝ := fun i => ‖d i‖
  let κ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    Matrix.diagonal fun i => d i / (‖d i‖ : ℂ)
  have hκ : κ ∈ UH (Hq k r) := by
    apply diag_mem
    intro i
    have h1 : ((‖d i‖ : ℝ) : ℂ) * ((‖d (pr k r i)‖ : ℝ) : ℂ) = 1 := by exact_mod_cast hdn i
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, hd, h1, div_one]
  have ht : dg t ∈ UH (Hq k r) := by
    apply diag_mem
    intro i
    rw [Complex.conj_ofReal]
    exact_mod_cast hdn i
  obtain ⟨l, hl⟩ : ∃ l, l = dg t * μ * κ := ⟨_, rfl⟩
  have hlU : l ∈ UH (Hq k r) := hl ▸ mul_mem (mul_mem ht hμ) hκ
  have hle : ∀ i j, l i j = if mid i ∧ mid j then s i j else if i = j then s i i else 0 := by
    intro i j
    have e1 : (dg t * μ) i j = ((‖d i‖ : ℝ) : ℂ) * μ i j :=
      Matrix.diagonal_mul (fun i => ((‖d i‖ : ℝ) : ℂ)) μ i j
    have e2 : (dg t * μ * κ) i j = (dg t * μ) i j * (d j / ((‖d j‖ : ℝ) : ℂ)) :=
      Matrix.mul_diagonal (fun i => d i / ((‖d i‖ : ℝ) : ℂ)) (dg t * μ) i j
    rw [hl, e2, e1]
    by_cases h : mid i ∧ mid j
    · simp [d, μ, h.1, h.2]
    · have hμe : μ i j = if i = j then 1 else 0 := if_neg h
      rw [hμe, if_neg h]
      by_cases e : i = j
      · subst e
        have hi : ¬ mid i := fun hi => h ⟨hi, hi⟩
        have := hd0' i
        rw [if_pos rfl, if_pos rfl, mul_one, mul_div_cancel₀ _ this]
        simp [d, hi]
      · simp [e]
  have hltri : l.BlockTriangular id := by
    intro i j hij
    have hij' : j.val < i.val := hij
    have : i ≠ j := fun e => by subst e; omega
    rw [hle, hz i j hij', if_neg this, ite_self]
  have hinv : (Hq k r * lᴴ * Hq k r) * l = 1 := by
    have : lᴴ * Hq k r * l = Hq k r := hlU
    calc _ = Hq k r * (lᴴ * Hq k r * l) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [this, Hq_sq]
  letI : Invertible l := invertibleOfLeftInverse _ _ hinv
  have hitri : l⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hltri
  have hiz : ∀ i j : Fin (2 * r + k + 1), j.val < i.val → l⁻¹ i j = 0 := fun i j h => hitri h
  have hll : l * l⁻¹ = 1 := Matrix.mul_inv_of_invertible l
  have hiU : l⁻¹ ∈ UH (Hq k r) := by
    have h1 : lᴴ * Hq k r * l = Hq k r := hlU
    change l⁻¹ᴴ * Hq k r * l⁻¹ = Hq k r
    calc _ = l⁻¹ᴴ * (lᴴ * Hq k r * l) * l⁻¹ := by rw [h1]
      _ = (l * l⁻¹)ᴴ * Hq k r * (l * l⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hq k r := by rw [hll]; simp
  have hm : ∀ i j : Fin (2 * r + k + 1), (j.val ≤ i.val ∨ (mid i ∧ mid j)) →
      (s * l⁻¹) i j = if i = j then 1 else 0 := by
    intro i j hij
    rw [← Matrix.one_apply, ← hll, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h1 : j.val < x.val
    · rw [hiz x j h1]; simp
    · by_cases h2 : x.val < i.val
      · rw [hz i x h2, hltri (show id x < id i from h2)]
      · congr 1
        rw [hle]
        by_cases h3 : mid i ∧ mid x
        · rw [if_pos h3]
        · have : i = x := by
            apply Fin.ext
            simp only [mid] at h3 hij
            omega
          subst this
          simp
  have hfix : ∀ x, ¬ mid x → μ *ᵥ bvec x = bvec x := by
    intro x hx
    ext i
    have e1 : (μ *ᵥ bvec x) i = μ i x := by
      simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
    have e2 : μ i x = if i = x then 1 else 0 := by
      have : ¬ (mid i ∧ mid x) := fun h => hx h.2
      exact if_neg this
    rw [e1, e2]
    simp [bvec, Pi.single_apply]
  refine ⟨s * l⁻¹, ⟨mul_mem hs hiU, fun a i hai => hm _ _ (Or.inl hai), fun i j h1 h2 h3 => hm _ _ ?_⟩,
    t, μ, ⟨hμ, fun a => ⟨?_, ?_⟩⟩, κ, hκ, ⟨fun i => ?_, fun i j hi hij => ?_, fun i hi => ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [mid]
    omega
  · have : ¬ mid (eI k r a) := by
      have := a.isLt
      simp only [mid, eI]; omega
    exact hfix _ this
  · have : ¬ mid (esI k r a) := by
      have := a.isLt
      simp only [mid, esI]; omega
    exact hfix _ this
  · exact lt_of_le_of_ne (norm_nonneg _) (hd0 i).symm
  · have : pr k r i = j := by
      have := pr_val k r i
      unfold outer at hi
      apply Fin.ext
      omega
    subst this
    exact hdn i
  · have : mid i := by
      unfold outer at hi
      simp only [mid]; omega
    simp [t, d, this]
  · have : mid (wI k r 0) := by simp [mid, wI]
    simp [t, d, this]
  · have : mid (wI k r 0) := by simp [mid, wI]
    simp [t, d, this]
  · simp only [κ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    ext i
    have := hd0' i
    simp only [Pi.star_apply, RCLike.star_def]
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.conj_mul']
    field_simp
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (dg t), ← hl, Matrix.mul_assoc,
      Matrix.inv_mul_of_invertible, Matrix.mul_one]

end GlobalTheory.CompanionTheory.BesselLevi
