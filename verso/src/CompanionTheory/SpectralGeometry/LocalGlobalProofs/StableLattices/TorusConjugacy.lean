import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuTorConj

/- English proof (translation)
Simplify using `[cStd, Complex.I_ne_zero]`.
-/
theorem cStd_ne : cStd ≠ 0 := by
  simp [cStd, Complex.I_ne_zero]

/- English proof (translation)
Take `⟨c', hc'd⟩ : ∃ f : ℕ → ℂ, f = fun m => if h : m < r then c ⟨m, h⟩ else 1` from `⟨_, rfl⟩`. Establish `hc' : ∀ m, c' m ≠ 0` using `fun m => by`. Distinguish the cases in `h : m < r`. Simplify using `only [hc'd, dif_pos h]`. Conclude with `hc _`.

Simplify using `only [hc'd, dif_neg h]`. Conclude with `one_ne_zero`. Use `⟨fun n => ∏ m ∈ Finset.Ico n r, (cStd / c' m), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `n`. Conclude with `Finset.prod_ne_zero_iff.mpr fun m _ => div_ne_zero cStd_ne (hc' m)`.

Introduce `n hn`. Simplify using `[Finset.Ico_eq_empty_of_le hn]`. Introduce `a`. Simplify using `only`. Rewrite using `[Finset.prod_eq_prod_Ico_succ_bot a.isLt]`.

Establish `hca : c' a.val = c a` using `by simp only [hc'd, dif_pos a.isLt]`. Rewrite using `[hca]`. Establish `hcz` using `hc a`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_scale (r : ℕ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    ∃ T : ℕ → ℂ, (∀ n, T n ≠ 0) ∧ (∀ n, r ≤ n → T n = 1) ∧
      ∀ a : Fin r, c a * T a.val = cStd * T (a.val + 1) := by
  classical
  obtain ⟨c', hc'd⟩ : ∃ f : ℕ → ℂ, f = fun m => if h : m < r then c ⟨m, h⟩ else 1 := ⟨_, rfl⟩
  have hc' : ∀ m, c' m ≠ 0 := fun m => by
    by_cases h : m < r
    · simp only [hc'd, dif_pos h]; exact hc _
    · simp only [hc'd, dif_neg h]; exact one_ne_zero
  refine ⟨fun n => ∏ m ∈ Finset.Ico n r, (cStd / c' m), ?_, ?_, ?_⟩
  · intro n
    exact Finset.prod_ne_zero_iff.mpr fun m _ => div_ne_zero cStd_ne (hc' m)
  · intro n hn
    simp [Finset.Ico_eq_empty_of_le hn]
  · intro a
    simp only
    rw [Finset.prod_eq_prod_Ico_succ_bot a.isLt]
    have hca : c' a.val = c a := by simp only [hc'd, dif_pos a.isLt]
    rw [hca]
    have hcz := hc a
    field_simp

/- English proof (translation)
Establish `hp` using `p.isLt`. Establish `hq` using `q.isLt`. Unfold `Hpk`. Distinguish the cases in `hjq : j = q`. Substitute `hjq` using the available equality.

Rewrite using `[if_pos rfl]`. Break down `h with h | h` into its components or cases. Rewrite using `[if_pos ⟨h, hpq⟩]`. Rewrite using `[if_neg (by omega), if_pos ⟨h, hpq⟩]`. Rewrite using `[if_neg hjq]`.

Establish `hjv : j.val ≠ q.val` using `fun e => hjq (Fin.ext e)`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg]`. Introduce and unpack `⟨h1, h2, -⟩`. Use linear arithmetic over natural numbers and integers.
-/
theorem hpk_row (k r : ℕ) (p q : Fin (2 * r + k + 1)) (hpq : p.val + q.val = 2 * r + k)
    (h : p.val < r ∨ q.val < r) (j : Fin (2 * r + k + 1)) :
    Hpk k r p j = if j = q then 1 else 0 := by
  have hp := p.isLt
  have hq := q.isLt
  unfold Hpk
  by_cases hjq : j = q
  · subst hjq
    rw [if_pos rfl]
    rcases h with h | h
    · rw [if_pos ⟨h, hpq⟩]
    · rw [if_neg (by omega), if_pos ⟨h, hpq⟩]
  · rw [if_neg hjq]
    have hjv : j.val ≠ q.val := fun e => hjq (Fin.ext e)
    rw [if_neg (by omega), if_neg (by omega), if_neg]
    rintro ⟨h1, h2, -⟩
    omega

/- English proof (translation)
Take `⟨-, hcols, -⟩` from `hh`. Establish `hplt` using `p.isLt`. Break down `hp with hp | hp` into its components or cases. Establish `e : eI k r ⟨p.val, hp⟩ = p` using `Fin.ext rfl`. Establish `hx` using `congrFun (hcols ⟨p.val, hp⟩).1 i`.

Rewrite `hx` using `[e]`. Simplify `hx` using `[bvec, mulVec_single, Pi.single_apply]`. Establish `e : esI k r ⟨2 * r + k - p.val, by omega⟩ = p`. Apply `Fin.ext` to reduce the goal to its premises. Use `show 2 * r + k - (2 * r + k - p.val) = p.val`.

Use linear arithmetic over natural numbers and integers. Establish `hx` using `congrFun (hcols ⟨2 * r + k - p.val, by omega⟩).2 i`. Rewrite `hx` using `[e]`. Simplify `hx` using `[bvec, mulVec_single, Pi.single_apply]`.
-/
theorem uw_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hh : h ∈ UWset k r z) (p : Fin (2 * r + k + 1)) (hp : p.val < r ∨ r + k < p.val)
    (i : Fin (2 * r + k + 1)) : h i p = if i = p then 1 else 0 := by
  obtain ⟨-, hcols, -⟩ := hh
  have hplt := p.isLt
  rcases hp with hp | hp
  · have e : eI k r ⟨p.val, hp⟩ = p := Fin.ext rfl
    have hx := congrFun (hcols ⟨p.val, hp⟩).1 i
    rw [e] at hx
    simpa [bvec, mulVec_single, Pi.single_apply] using hx
  · have e : esI k r ⟨2 * r + k - p.val, by omega⟩ = p := by
      apply Fin.ext
      show 2 * r + k - (2 * r + k - p.val) = p.val
      omega
    have hx := congrFun (hcols ⟨2 * r + k - p.val, by omega⟩).2 i
    rw [e] at hx
    simpa [bvec, mulVec_single, Pi.single_apply] using hx

/- English proof (translation)
Establish `hqlt` using `q.isLt`. Take `⟨p, hpd⟩ : ∃ p : Fin (2 * r + k + 1), p.val = 2 * r + k - q.val` from `⟨⟨2 * r + k - q.val, by omega⟩, rfl⟩`. Establish `hp : p.val < r ∨ r + k < p.val` using `by omega`. Establish `hpq : p.val + q.val = 2 * r + k` using `by omega`. Establish `hor : p.val < r ∨ q.val < r` using `by omega`.

Establish `hc : ∀ i, h i p = if i = p then 1 else 0` using `uw_col k r z h hh p hp`. Establish `hr : ∀ j', Hpk k r p j' = if j' = q then 1 else 0` using `hpk_row k r p q hpq hor`. Establish `hU : hᴴ * Hpk k r * h = Hpk k r` using `hh.1`. Establish `hx` using `congrFun (congrFun hU p) j`. Simplify using `only [mul_apply, conjTranspose_apply, hc, hr] at hx`.

Simplify `hx` using `[Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul, hr]`.
-/
theorem uw_row (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hh : h ∈ UWset k r z) (q : Fin (2 * r + k + 1)) (hq : q.val < r ∨ r + k < q.val)
    (j : Fin (2 * r + k + 1)) : h q j = if j = q then 1 else 0 := by
  have hqlt := q.isLt
  obtain ⟨p, hpd⟩ : ∃ p : Fin (2 * r + k + 1), p.val = 2 * r + k - q.val := ⟨⟨2 * r + k - q.val, by omega⟩, rfl⟩
  have hp : p.val < r ∨ r + k < p.val := by omega
  have hpq : p.val + q.val = 2 * r + k := by omega
  have hor : p.val < r ∨ q.val < r := by omega
  have hc : ∀ i, h i p = if i = p then 1 else 0 := uw_col k r z h hh p hp
  have hr : ∀ j', Hpk k r p j' = if j' = q then 1 else 0 := hpk_row k r p q hpq hor
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hx := congrFun (congrFun hU p) j
  simp only [mul_apply, conjTranspose_apply, hc, hr] at hx
  simpa [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul, hr] using hx

/- English proof (translation)
Unfold `CompanionTheory.Bmu.TorConj`. Introduce `k r z c hz hc`. Take `⟨T, hT0, hT1, hTc⟩` from `exists_scale r c hc`. Take `⟨d, hd⟩ : ∃ d : Fin (2 * r + k + 1) → ℂ, d = fun i => if i.val < r then T i.val else if i.val ≤ r + k then 1 else (star (T (2 * r + k - i.val)))⁻¹` from `⟨_, rfl⟩`. Establish `hdlow : ∀ i : Fin (2 * r + k + 1), i.val < r → d i = T i.val` using `fun i hi => by`.

Rewrite using `[hd]`. Simplify using `only`. Rewrite using `[if_pos hi]`. Establish `hdmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = 1` using `fun i h1 h2 => by`. Rewrite using `[hd]; simp only; rw [if_neg (by omega), if_pos h2]`.

Establish `hdhigh : ∀ i : Fin (2 * r + k + 1), r + k < i.val → d i = (star (T (2 * r + k - i.val)))⁻¹` using `fun i hi => by`. Rewrite using `[hd]; simp only; rw [if_neg (by omega), if_neg (by omega)]`. Establish `hd0 : ∀ i, d i ≠ 0`. Introduce `i`. Distinguish the cases in `h1 : i.val < r`.

Rewrite using `[hdlow i h1]`. Conclude with `hT0 _`. Distinguish the cases in `h2 : i.val ≤ r + k`. Rewrite using `[hdmid i (by omega) h2]; exact one_ne_zero`. Rewrite using `[hdhigh i (by omega)]; exact inv_ne_zero (star_ne_zero.mpr (hT0 _))`.

Establish `hHnz : ∀ i j : Fin (2 * r + k + 1), Hpk k r i j ≠ 0 → (i.val < r ∧ i.val + j.val = 2 * r + k) ∨ (j.val < r ∧ i.val + j.val = 2 * r + k) ∨ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j)`. Introduce `i j h`. Unfold `Hpk at h`. Apply the tactic sequence `split_ifs at h with h1 h2 h3 <;> first | exact absurd rfl h | tauto`. Establish `hkey : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1`.

Introduce `i j h`. Establish `hilt` using `i.isLt`. Establish `hjlt` using `j.isLt`. Break down `hHnz i j h with ⟨hi, hij⟩ | ⟨hj, hij⟩ | ⟨hi1, hi2, rfl⟩` into its components or cases. Rewrite using `[hdlow i hi, hdhigh j (by omega), show 2 * r + k - j.val = i.val by omega]`.

Conclude with `mul_inv_cancel₀ (star_ne_zero.mpr (hT0 _))`. Rewrite using `[hdhigh i (by omega), hdlow j hj, show 2 * r + k - i.val = j.val by omega]`. Simplify using `[hT0 j.val]`. Rewrite using `[hdmid i hi1 hi2]`. Simplify using the standard rewrite rules.

Establish `hdiagU : ∀ e : Fin (2 * r + k + 1) → ℂ, (∀ i j, Hpk k r i j ≠ 0 → star (e i) * e j = 1) → diagonal e ∈ UH (Hpk k r)`. Introduce `e he`. Use `show (diagonal e)ᴴ * Hpk k r * diagonal e = Hpk k r`. Use extensionality with `i j`. Rewrite using `[diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply]`.

Distinguish the cases in `h0 : Hpk k r i j = 0`. Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Establish `hUmul : ∀ A B, A ∈ UH (Hpk k r) → B ∈ UH (Hpk k r) → A * B ∈ UH (Hpk k r)`.

Introduce `A B hA hB`. Establish `hA' : Aᴴ * Hpk k r * A = Hpk k r` using `hA`. Establish `hB' : Bᴴ * Hpk k r * B = Hpk k r` using `hB`. Use `show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r`. Rewrite using `[conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [hA', hB']`. Establish `hτU : diagonal d ∈ UH (Hpk k r)` using `hdiagU d hkey`. Establish `hτinvU : diagonal (fun i => (d i)⁻¹) ∈ UH (Hpk k r)`.

Use `hdiagU _ fun i j h => ?_` and prove the remaining obligations. Rewrite using `[star_inv₀, ← mul_inv, hkey i j h, inv_one]`. Establish `hτinv : (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹)`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[diagonal_mul_diagonal]`.

Establish `he : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ)` using `funext fun i => inv_mul_cancel₀ (hd0 i)`. Rewrite using `[he, diagonal_one]`. Establish `hcomm : ∀ h ∈ UWset k r z, diagonal d * h = h * diagonal d`. Introduce `h hh`. Use extensionality with `i j`.

Rewrite using `[diagonal_mul, mul_diagonal]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hi : i.val < r ∨ r + k < i.val`.

Rewrite using `[uw_row k r z h hh i hi j, if_neg (fun e => hij e.symm)]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hj : j.val < r ∨ r + k < j.val`. Rewrite using `[uw_col k r z h hh j hj i, if_neg hij]`. Expand and normalize the polynomial expressions, which then agree.

Use `push_neg at hi hj`. Rewrite using `[hdmid i hi.1 hi.2, hdmid j hj.1 hj.2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hzd : ∀ j, (d j)⁻¹ * z j = z j`. Introduce `j`.

Distinguish the cases in `hj : j.val < r ∨ r + k < j.val`. Rewrite using `[hz j hj, mul_zero]`. Use `push_neg at hj`. Rewrite using `[hdmid j hj.1 hj.2, inv_one, one_mul]`. Use `⟨diagonal d, hτU, hcomm, fun m hm => ?_⟩` and prove the remaining obligations.

Rewrite using `[hτinv]`. Take `⟨hmU, hm2, hm3⟩` from `hm`. Establish `hent : ∀ i j, (diagonal d * m * diagonal (fun i => (d i)⁻¹)) i j = d i * m i j * (d j)⁻¹`. Introduce `i j`. Rewrite using `[mul_diagonal, diagonal_mul]`.

Use `⟨⟨hUmul _ _ (hUmul _ _ hτU hmU) hτinvU, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `a i hai`. Rewrite using `[hent, hm2 a i hai]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Rewrite using `[mul_one, mul_inv_cancel₀ (hd0 _)]`. Simplify using the standard rewrite rules. Introduce `i j hj1 hj2 hi`. Rewrite using `[hent, hm3 i j hj1 hj2 hi]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Rewrite using `[mul_one, mul_inv_cancel₀ (hd0 _)]`. Simplify using the standard rewrite rules. Establish `hsum : ∑ a, c a * PI.BesselMapUniq.ellA k r z (diagonal d * m * diagonal (fun i => (d i)⁻¹)) a = cStd * ell k r z m`. Rewrite using `[ell, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[PI.BesselMapUniq.ellA]`. Establish `e1 : d (eI k r a) = T a.val` using `hdlow _ a.isLt`. Use `split_ifs with ha`. Establish `e2 : d (eI k r ⟨a.val + 1, ha⟩) = T (a.val + 1)` using `hdlow _ ha`.

Rewrite using `[hent, e1, e2, ← mul_assoc, ← mul_assoc, hTc a, mul_right_comm (cStd * T (a.val + 1)), mul_inv_cancel_right₀ (hT0 _)]`. Establish `hmv : (diagonal d * m * diagonal (fun i => (d i)⁻¹)).mulVec z (eI k r a) = d (eI k r a) * m.mulVec z (eI k r a)`. Simplify using `only [mulVec, dotProduct, hent, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hmv, e1, ← mul_assoc, hTc a, hT1 _ (by omega), mul_one]`. Rewrite using `[PI.BesselMapUniq.psiGen, psi, hsum]`.
-/
theorem torConj : CompanionTheory.Bmu.TorConj := by
  unfold CompanionTheory.Bmu.TorConj
  intro k r z c hz hc
  obtain ⟨T, hT0, hT1, hTc⟩ := exists_scale r c hc
  obtain ⟨d, hd⟩ : ∃ d : Fin (2 * r + k + 1) → ℂ, d = fun i =>
      if i.val < r then T i.val else if i.val ≤ r + k then 1 else (star (T (2 * r + k - i.val)))⁻¹ :=
    ⟨_, rfl⟩
  have hdlow : ∀ i : Fin (2 * r + k + 1), i.val < r → d i = T i.val := fun i hi => by
    rw [hd]; simp only; rw [if_pos hi]
  have hdmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = 1 := fun i h1 h2 => by
    rw [hd]; simp only; rw [if_neg (by omega), if_pos h2]
  have hdhigh : ∀ i : Fin (2 * r + k + 1), r + k < i.val → d i = (star (T (2 * r + k - i.val)))⁻¹ :=
    fun i hi => by
      rw [hd]; simp only; rw [if_neg (by omega), if_neg (by omega)]
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i
    by_cases h1 : i.val < r
    · rw [hdlow i h1]; exact hT0 _
    by_cases h2 : i.val ≤ r + k
    · rw [hdmid i (by omega) h2]; exact one_ne_zero
    · rw [hdhigh i (by omega)]; exact inv_ne_zero (star_ne_zero.mpr (hT0 _))
  have hHnz : ∀ i j : Fin (2 * r + k + 1), Hpk k r i j ≠ 0 →
      (i.val < r ∧ i.val + j.val = 2 * r + k) ∨ (j.val < r ∧ i.val + j.val = 2 * r + k) ∨
        (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j) := by
    intro i j h
    unfold Hpk at h
    split_ifs at h with h1 h2 h3 <;> first | exact absurd rfl h | tauto
  have hkey : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1 := by
    intro i j h
    have hilt := i.isLt
    have hjlt := j.isLt
    rcases hHnz i j h with ⟨hi, hij⟩ | ⟨hj, hij⟩ | ⟨hi1, hi2, rfl⟩
    · rw [hdlow i hi, hdhigh j (by omega), show 2 * r + k - j.val = i.val by omega]
      exact mul_inv_cancel₀ (star_ne_zero.mpr (hT0 _))
    · rw [hdhigh i (by omega), hdlow j hj, show 2 * r + k - i.val = j.val by omega]
      simp [hT0 j.val]
    · rw [hdmid i hi1 hi2]; simp
  have hdiagU : ∀ e : Fin (2 * r + k + 1) → ℂ, (∀ i j, Hpk k r i j ≠ 0 → star (e i) * e j = 1) →
      diagonal e ∈ UH (Hpk k r) := by
    intro e he
    show (diagonal e)ᴴ * Hpk k r * diagonal e = Hpk k r
    ext i j
    rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply]
    by_cases h0 : Hpk k r i j = 0
    · rw [h0]; ring
    · calc star (e i) * Hpk k r i j * e j = (star (e i) * e j) * Hpk k r i j := by ring
        _ = Hpk k r i j := by rw [he i j h0, one_mul]
  have hUmul : ∀ A B, A ∈ UH (Hpk k r) → B ∈ UH (Hpk k r) → A * B ∈ UH (Hpk k r) := by
    intro A B hA hB
    have hA' : Aᴴ * Hpk k r * A = Hpk k r := hA
    have hB' : Bᴴ * Hpk k r * B = Hpk k r := hB
    show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r
    rw [conjTranspose_mul]
    calc Bᴴ * Aᴴ * Hpk k r * (A * B) = Bᴴ * (Aᴴ * Hpk k r * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hA', hB']
  have hτU : diagonal d ∈ UH (Hpk k r) := hdiagU d hkey
  have hτinvU : diagonal (fun i => (d i)⁻¹) ∈ UH (Hpk k r) := by
    refine hdiagU _ fun i j h => ?_
    rw [star_inv₀, ← mul_inv, hkey i j h, inv_one]
  have hτinv : (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal]
    have he : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ) := funext fun i => inv_mul_cancel₀ (hd0 i)
    rw [he, diagonal_one]
  have hcomm : ∀ h ∈ UWset k r z, diagonal d * h = h * diagonal d := by
    intro h hh
    ext i j
    rw [diagonal_mul, mul_diagonal]
    by_cases hij : i = j
    · subst hij; ring
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [uw_row k r z h hh i hi j, if_neg (fun e => hij e.symm)]; ring
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [uw_col k r z h hh j hj i, if_neg hij]; ring
    push_neg at hi hj
    rw [hdmid i hi.1 hi.2, hdmid j hj.1 hj.2]; ring
  have hzd : ∀ j, (d j)⁻¹ * z j = z j := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
    · push_neg at hj; rw [hdmid j hj.1 hj.2, inv_one, one_mul]
  refine ⟨diagonal d, hτU, hcomm, fun m hm => ?_⟩
  rw [hτinv]
  obtain ⟨hmU, hm2, hm3⟩ := hm
  have hent : ∀ i j, (diagonal d * m * diagonal (fun i => (d i)⁻¹)) i j = d i * m i j * (d j)⁻¹ := by
    intro i j
    rw [mul_diagonal, diagonal_mul]
  refine ⟨⟨hUmul _ _ (hUmul _ _ hτU hmU) hτinvU, ?_, ?_⟩, ?_⟩
  · intro a i hai
    rw [hent, hm2 a i hai]
    split_ifs with h
    · subst h; rw [mul_one, mul_inv_cancel₀ (hd0 _)]
    · simp
  · intro i j hj1 hj2 hi
    rw [hent, hm3 i j hj1 hj2 hi]
    split_ifs with h
    · subst h; rw [mul_one, mul_inv_cancel₀ (hd0 _)]
    · simp
  · have hsum : ∑ a, c a * PI.BesselMapUniq.ellA k r z (diagonal d * m * diagonal (fun i => (d i)⁻¹)) a =
        cStd * ell k r z m := by
      rw [ell, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [PI.BesselMapUniq.ellA]
      have e1 : d (eI k r a) = T a.val := hdlow _ a.isLt
      split_ifs with ha
      · have e2 : d (eI k r ⟨a.val + 1, ha⟩) = T (a.val + 1) := hdlow _ ha
        rw [hent, e1, e2, ← mul_assoc, ← mul_assoc, hTc a,
          mul_right_comm (cStd * T (a.val + 1)), mul_inv_cancel_right₀ (hT0 _)]
      · have hmv : (diagonal d * m * diagonal (fun i => (d i)⁻¹)).mulVec z (eI k r a) =
            d (eI k r a) * m.mulVec z (eI k r a) := by
          simp only [mulVec, dotProduct, hent, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          calc d (eI k r a) * m (eI k r a) j * (d j)⁻¹ * z j
              = d (eI k r a) * m (eI k r a) j * ((d j)⁻¹ * z j) := by ring
            _ = d (eI k r a) * (m (eI k r a) j * z j) := by rw [hzd j]; ring
        rw [hmv, e1, ← mul_assoc, hTc a, hT1 _ (by omega), mul_one]
    rw [PI.BesselMapUniq.psiGen, psi, hsum]

end GlobalTheory.CompanionTheory.BmuTorConj
