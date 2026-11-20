import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZero

noncomputable section

namespace PI.OneCosetSharp.W.C2

open Loc LocE

variable {k : Type} [Field k]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Rewrite using `[Matrix.toLin'_apply]`. Use `show ∑ j, X l j * PI.OneCosetSharp.Loc.eN k A i j = X l ⟨i, hi⟩`. Rewrite using `[Finset.sum_eq_single ⟨i, hi⟩]`. Simplify using `[PI.OneCosetSharp.Loc.eN]`.

Introduce `b _ hb`. Establish `hb' : (b : ℕ) ≠ i` using `fun h => hb (Fin.ext h)`. Simplify using `[PI.OneCosetSharp.Loc.eN, hb']`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem toLin'_eN {A B : ℕ} (X : Matrix (Fin B) (Fin A) k) (i : ℕ) (hi : i < A) :
    Matrix.toLin' X (eN k A i) = fun l => X l ⟨i, hi⟩ := by
  funext l
  rw [Matrix.toLin'_apply]
  show ∑ j, X l j * PI.OneCosetSharp.Loc.eN k A i j = X l ⟨i, hi⟩
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp [PI.OneCosetSharp.Loc.eN]
  · intro b _ hb
    have hb' : (b : ℕ) ≠ i := fun h => hb (Fin.ext h)
    simp [PI.OneCosetSharp.Loc.eN, hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

def xj0 (k₀ n' n : ℕ) : (Fin n' → k) →ₗ[k] (Fin n → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin n) (s : Fin n') =>
    if l.1 = (if s.1 < k₀ then s.1 else s.1 + 1) then (1 : k) else 0)

def τ0 (k₀ n' c n : ℕ) : FC n' (c + 1) n c → k := fun q =>
  if q.1.2.1 = n' + c ∧ q.1.1.1 = k₀ then 1 else 0

/- English proof (translation)
Unfold `PI.OneCosetSharp.Loc.atN`. Simplify using `[h]`.
-/
private theorem atN_of_lt' {N : ℕ} (v : Fin N → k) {i : ℕ} (h : i < N) : PI.OneCosetSharp.Loc.atN v i = v ⟨i, h⟩ := by
  unfold PI.OneCosetSharp.Loc.atN
  simp [h]

/- English proof (translation)
Unfold `PI.OneCosetSharp.ent PI.OneCosetSharp.Loc.xx1`. Rewrite using `[toLin'_eN _ _ hp', atN_of_lt' _ hp]`. Both sides reduce to the same expression.
-/
theorem entry_embedMatrix {n' c n : ℕ} (k₀ : ℕ) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (τ : FC n' (c + 1) n c → k)
    (p p' : ℕ) (hp : fIdx k₀ c n p < n + c) (hp' : fIdx k₀ (c + 1) n' p' < n' + (c + 1)) :
    ent k₀ (c + 1) n' c n (xx1 xj τ) p p' =
      (if hf : IsFree n' n c (fIdx k₀ c n p) (fIdx k₀ (c + 1) n' p') then τ ⟨(⟨_, hp⟩, ⟨_, hp'⟩), hf⟩
       else if hs : fIdx k₀ (c + 1) n' p' < n' then
          (if hl : fIdx k₀ c n p < n then LinearMap.toMatrix' xj ⟨_, hl⟩ ⟨_, hs⟩ else 0)
       else if fIdx k₀ c n p = n + (fIdx k₀ (c + 1) n' p' - n') then 1 else 0) := by
  unfold PI.OneCosetSharp.ent PI.OneCosetSharp.Loc.xx1
  rw [toLin'_eN _ _ hp', atN_of_lt' _ hp]
  rfl

/- English proof (translation)
Take `⟨h1, -, h4, hj1, hjm, hc, he1, he2⟩` from `h`. Establish `hjt : j * t = (j - 1) * t + t`. Take `⟨j', rfl⟩ : ∃ j', j = j' + 1` from `⟨j - 1, by omega⟩`. Simplify using `[add_mul]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_, ?_, he1, ?_⟩ <;> omega`.
-/
theorem facts {k₀ m t j n' c n : ℕ} (h : Nums k₀ m t j n' c n) :
    k₀ ≤ n' ∧ 1 ≤ c ∧ k₀ + c < k₀ + m - 1 ∧ k₀ + m - 1 ≤ n' + (c + 1) ∧ n' + (c + 1) ≤ n + c ∧
      n' + (c + 1) = k₀ + m - 1 + (j - 1) * t ∧ n + c = n' + (c + 1) + t := by
  obtain ⟨h1, -, h4, hj1, hjm, hc, he1, he2⟩ := h
  have hjt : j * t = (j - 1) * t + t := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp [add_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, he1, ?_⟩ <;> omega

/- English proof (translation)
Unfold `PI.OneCosetSharp.LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem fIdx_lt {k₀ c n p : ℕ} (_hk : k₀ ≤ n) (hp : p < n + c) : fIdx k₀ c n p < n + c := by
  unfold PI.OneCosetSharp.LocE.fIdx
  split_ifs <;> omega

/- English proof (translation)
Unfold `PI.OneCosetSharp.LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private theorem fIdx_eq_cases (k₀ c n p : ℕ) :
    (p < k₀ ∧ PI.OneCosetSharp.LocE.fIdx k₀ c n p = p) ∨ (k₀ ≤ p ∧ p < k₀ + c ∧ PI.OneCosetSharp.LocE.fIdx k₀ c n p = n + (p - k₀)) ∨
      (k₀ + c ≤ p ∧ PI.OneCosetSharp.LocE.fIdx k₀ c n p = p - c) := by
  unfold PI.OneCosetSharp.LocE.fIdx
  split_ifs <;> omega

/- English proof (translation)
Take `⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩` from `facts hN`. Establish `hR` using `fIdx_eq_cases k₀ c n p`. Establish `hS` using `fIdx_eq_cases k₀ (c + 1) n' p'`. Establish `hrl : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c` using `fIdx_lt (by omega) hp`. Establish `hsl : PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' < n' + (c + 1)` using `fIdx_lt hk hp'`.

Rewrite using `[entry_embedMatrix k₀ _ _ p p' hrl hsl]`. Generalize the expression as in `PI.OneCosetSharp.LocE.fIdx k₀ c n p = r at hR hrl ⊢`. Generalize the expression as in `PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' = s at hS hsl ⊢`. Simplify using `only [xj0, LinearMap.toMatrix'_toLin', Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; (try simp only [PI.OneCosetSharp.Loc.IsFree] at *); omega)`.
-/
theorem ent_unit {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (τ : FC n' (c + 1) n c → k) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n' + (c + 1)) (hcol : p' ≤ k₀ ∨ k₀ + c < p') :
    ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p p' = if p = p' then 1 else 0 := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  have hR := fIdx_eq_cases k₀ c n p
  have hS := fIdx_eq_cases k₀ (c + 1) n' p'
  have hrl : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c := fIdx_lt (by omega) hp
  have hsl : PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' < n' + (c + 1) := fIdx_lt hk hp'
  rw [entry_embedMatrix k₀ _ _ p p' hrl hsl]
  generalize PI.OneCosetSharp.LocE.fIdx k₀ c n p = r at hR hrl ⊢
  generalize PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' = s at hS hsl ⊢
  simp only [xj0, LinearMap.toMatrix'_toLin', Matrix.of_apply]
  split_ifs <;> first | rfl | (exfalso; (try simp only [PI.OneCosetSharp.Loc.IsFree] at *); omega)

/- English proof (translation)
Take `⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩` from `facts hN`. Establish `hR` using `fIdx_eq_cases k₀ c n p`. Establish `hS` using `fIdx_eq_cases k₀ (c + 1) n' p'`. Establish `hrl : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c` using `fIdx_lt (by omega) hp`. Establish `hsl : PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' < n' + (c + 1)` using `fIdx_lt hk hp'`.

Rewrite using `[entry_embedMatrix k₀ _ _ p p' hrl hsl]`. Generalize the expression as in `PI.OneCosetSharp.LocE.fIdx k₀ c n p = r at hR hrl ⊢`. Generalize the expression as in `PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' = s at hS hsl ⊢`. Simplify using `only [xj0, τ0, LinearMap.toMatrix'_toLin', Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; (try simp only [PI.OneCosetSharp.Loc.IsFree] at *); omega)`.
-/
theorem ent_τ0 {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n' + (c + 1)) :
    ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) (τ0 (k := k) k₀ n' c n)) p p' = if p = p' then 1 else 0 := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  have hR := fIdx_eq_cases k₀ c n p
  have hS := fIdx_eq_cases k₀ (c + 1) n' p'
  have hrl : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c := fIdx_lt (by omega) hp
  have hsl : PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' < n' + (c + 1) := fIdx_lt hk hp'
  rw [entry_embedMatrix k₀ _ _ p p' hrl hsl]
  generalize PI.OneCosetSharp.LocE.fIdx k₀ c n p = r at hR hrl ⊢
  generalize PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' = s at hS hsl ⊢
  simp only [xj0, τ0, LinearMap.toMatrix'_toLin', Matrix.of_apply]
  split_ifs <;> first | rfl | (exfalso; (try simp only [PI.OneCosetSharp.Loc.IsFree] at *); omega)

/- English proof (translation)
Simplify using `[PI.OneCosetSharp.chiV]`.
-/
theorem chiV_one [DecidableEq k] (χ : kˣ →* ℂˣ) : chiV χ (1 : k) = 1 := by
  simp [PI.OneCosetSharp.chiV]

/- English proof (translation)
Take `⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩` from `facts hN`. Establish `hsplit : k₀ + m - 1 - 1 = k₀ + (c + (k₀ + m - 1 - 1 - k₀ - c))` using `by omega`. Rewrite using `[hsplit, Finset.sum_range_add, Finset.sum_range_add]`. Establish `hz : ∀ i, i + 1 < n' + (c + 1) → (i + 1 ≤ k₀ ∨ k₀ + c < i + 1) → PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) i (i + 1) = 0`. Introduce `i hi hcol`.

Rewrite using `[ent_unit hN τ (by omega) hi hcol, if_neg (by omega)]`. Establish `h1 : ∑ i ∈ Finset.range k₀, PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) i (i + 1) = 0` using `Finset.sum_eq_zero fun i hi => by`. Rewrite `hi` using `[Finset.mem_range]`. Conclude with `hz i (by omega) (by omega)`. Establish `h3 : ∑ x ∈ Finset.range (k₀ + m - 1 - 1 - k₀ - c), PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) (k₀ + (c + x)) (k₀ + (c + x) + 1) = 0` using `Finset.sum_eq_zero fun x hx => by`.

Rewrite `hx` using `[Finset.mem_range]`. Conclude with `hz _ (by omega) (by omega)`. Simplify using `only [h1, h3, zero_add, add_zero]`. Unfold `PI.OneCosetSharp.Loc.chArg`. Use `Finset.sum_congr rfl fun e he => ?_` and prove the remaining obligations.

Rewrite `he` using `[Finset.mem_range]`. Unfold `PI.OneCosetSharp.ent`. Establish `e1 : PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' (k₀ + e + 1) = n' + e + 1`. Unfold `PI.OneCosetSharp.LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`.

Establish `e2 : PI.OneCosetSharp.LocE.fIdx k₀ c n (k₀ + e) = n + e`. Unfold `PI.OneCosetSharp.LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[e1, e2]`.
-/
theorem sum_eq_chArg {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (τ : FC n' (c + 1) n c → k) :
    ∑ i ∈ Finset.range (k₀ + m - 1 - 1), ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) i (i + 1) =
      chArg (n' := n') (c' := c + 1) (n := n) (c := c) (xx1 (xj0 k₀ n' n) τ) := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  have hsplit : k₀ + m - 1 - 1 = k₀ + (c + (k₀ + m - 1 - 1 - k₀ - c)) := by omega
  rw [hsplit, Finset.sum_range_add, Finset.sum_range_add]
  have hz : ∀ i, i + 1 < n' + (c + 1) → (i + 1 ≤ k₀ ∨ k₀ + c < i + 1) →
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) i (i + 1) = 0 := by
    intro i hi hcol
    rw [ent_unit hN τ (by omega) hi hcol, if_neg (by omega)]
  have h1 : ∑ i ∈ Finset.range k₀, PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) i (i + 1) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      exact hz i (by omega) (by omega)
  have h3 : ∑ x ∈ Finset.range (k₀ + m - 1 - 1 - k₀ - c),
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) (k₀ + (c + x)) (k₀ + (c + x) + 1) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      rw [Finset.mem_range] at hx
      exact hz _ (by omega) (by omega)
  simp only [h1, h3, zero_add, add_zero]
  unfold PI.OneCosetSharp.Loc.chArg
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.mem_range] at he
  unfold PI.OneCosetSharp.ent
  have e1 : PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' (k₀ + e + 1) = n' + e + 1 := by
    unfold PI.OneCosetSharp.LocE.fIdx
    split_ifs <;> omega
  have e2 : PI.OneCosetSharp.LocE.fIdx k₀ c n (k₀ + e) = n + e := by
    unfold PI.OneCosetSharp.LocE.fIdx
    split_ifs <;> omega
  rw [e1, e2]

open Classical in

/- English proof (translation)
Take `⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩` from `facts hN`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Establish `hit : i * t + t ≤ (j - 1) * t`.

Establish `h` using `Nat.mul_le_mul (show i + 1 ≤ j - 1 by omega) (le_refl t)`. Rewrite `h` using `[add_mul, one_mul]`. Then use the resulting hypothesis. Establish `hM : (Matrix.of fun s s' : Fin t => PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) (k₀ + m - 1 + i * t + s.1) (k₀ + m - 1 + i * t + s'.1)) = 1`. Use extensionality with `s s'`. Establish `hs1` using `s.isLt`.

Establish `hs2` using `s'.isLt`. Rewrite using `[Matrix.of_apply, ent_unit hN τ (by omega) (by omega) (by omega), Matrix.one_apply]`. Distinguish the cases in `h : s = s'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h, if_neg]`. Introduce `h'`. Conclude with `h (Fin.ext (by omega))`. Rewrite using `[hM, Matrix.det_one, chiV_one]`.
-/
theorem prod_blocks {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (χ : ℕ → kˣ →* ℂˣ)
    (τ : FC n' (c + 1) n c → k) :
    ∏ i ∈ Finset.range (j - 1), chiV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t =>
      ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) (k₀ + m - 1 + i * t + s.1) (k₀ + m - 1 + i * t + s'.1))) = 1 := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  apply Finset.prod_eq_one
  intro i hi
  rw [Finset.mem_range] at hi
  have hit : i * t + t ≤ (j - 1) * t := by
    have h := Nat.mul_le_mul (show i + 1 ≤ j - 1 by omega) (le_refl t)
    rwa [add_mul, one_mul] at h
  have hM : (Matrix.of fun s s' : Fin t =>
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) (k₀ + m - 1 + i * t + s.1)
        (k₀ + m - 1 + i * t + s'.1)) = 1 := by
    ext s s'
    have hs1 := s.isLt
    have hs2 := s'.isLt
    rw [Matrix.of_apply, ent_unit hN τ (by omega) (by omega) (by omega), Matrix.one_apply]
    by_cases h : s = s'
    · subst h
      simp
    · rw [if_neg h, if_neg]
      intro h'
      exact h (Fin.ext (by omega))
  rw [hM, Matrix.det_one, chiV_one]

open Classical in

/- English proof (translation)
Take `⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩` from `facts hN`. Establish `hdet : Matrix.det (Matrix.of fun s s' : Fin (k₀ + m - 1 + (j - 1) * t) => PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) s.1 s'.1) = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `s _`.

Establish `hs1` using `s.isLt`. Rewrite using `[Matrix.of_apply]`. Distinguish the cases in `hs : s.1 < k₀ + m - 1`. Conclude with `hC.1 s.1 hs`. Rewrite using `[ent_unit hN τ (by omega) (by omega) (by omega), if_pos rfl]`.

Introduce `s s' hss`. Establish `hss' : s'.1 < s.1` using `hss`. Establish `hs1` using `s.isLt`. Establish `hs2` using `s'.isLt`. Rewrite using `[Matrix.of_apply]`.

Distinguish the cases in `hcol : s'.1 ≤ k₀ ∨ k₀ + c < s'.1`. Rewrite using `[ent_unit hN τ (by omega) (by omega) hcol, if_neg (by omega)]`. Assume the negation of the conclusion as `hne`. Establish `hA` using `hC.2 s.1 s'.1 (by omega) hs2 (by omega) hne`. Unfold `PI.OneCosetSharp.Allow at hA`.

Apply the tactic sequence `split_ifs at hA <;> omega`. Rewrite using `[hdet, chiV_one]`.
-/
theorem top_block {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (χ : ℕ → kˣ →* ℂˣ)
    (τ : FC n' (c + 1) n c → k)
    (hC : (∀ p', p' < k₀ + m - 1 → ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p' p' = 1) ∧
      (∀ p p', p < n + c → p' < k₀ + m - 1 + (j - 1) * t → p ≠ p' →
        ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p p' ≠ 0 → Allow k₀ m t (k₀ + m - 1 + (j - 1) * t) p p')) :
    chiV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin (k₀ + m - 1 + (j - 1) * t) =>
      ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) s.1 s'.1)) = 1 := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  have hdet : Matrix.det (Matrix.of fun s s' : Fin (k₀ + m - 1 + (j - 1) * t) =>
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) s.1 s'.1) = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_eq_one
      intro s _
      have hs1 := s.isLt
      rw [Matrix.of_apply]
      by_cases hs : s.1 < k₀ + m - 1
      · exact hC.1 s.1 hs
      · rw [ent_unit hN τ (by omega) (by omega) (by omega), if_pos rfl]
    · intro s s' hss
      have hss' : s'.1 < s.1 := hss
      have hs1 := s.isLt
      have hs2 := s'.isLt
      rw [Matrix.of_apply]
      by_cases hcol : s'.1 ≤ k₀ ∨ k₀ + c < s'.1
      · rw [ent_unit hN τ (by omega) (by omega) hcol, if_neg (by omega)]
      · by_contra hne
        have hA := hC.2 s.1 s'.1 (by omega) hs2 (by omega) hne
        unfold PI.OneCosetSharp.Allow at hA
        split_ifs at hA <;> omega
  rw [hdet, chiV_one]

open Classical in

/- English proof (translation)
Unfold `PI.OneCosetSharp.PhiS`. Simplify using `only`. Use `split_ifs with h`. Rewrite using `[prod_blocks hN χ τ, top_block hN χ τ h, sum_eq_chArg hN τ]`. Rewrite using `[inv_one, mul_one, mul_one, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`.

Rewrite using `[zero_mul]`.
-/
theorem term_eq {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ)
    (τ : FC n' (c + 1) n c → k) :
    PhiS ψ₀ χ k₀ m t j n' c n (xx1 (xj0 k₀ n' n) τ) *
        ψ₀ (-chArg (n' := n') (c' := c + 1) (n := n) (c := c) (xx1 (xj0 k₀ n' n) τ)) =
      if ((∀ p', p' < k₀ + m - 1 → ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p' p' = 1) ∧
        (∀ p p', p < n + c → p' < k₀ + m - 1 + (j - 1) * t → p ≠ p' →
          ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p p' ≠ 0 → Allow k₀ m t (k₀ + m - 1 + (j - 1) * t) p p'))
      then 1 else 0 := by
  unfold PI.OneCosetSharp.PhiS
  dsimp only
  split_ifs with h
  · rw [prod_blocks hN χ τ, top_block hN χ τ h, sum_eq_chArg hN τ]
    rw [inv_one, mul_one, mul_one, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  · rw [zero_mul]

/- English proof (translation)
Unfold `PI.OneCosetSharp.W.Claim2`. Introduce `k _ _ ψ₀ χ k₀ m t j n' c n hN`. Take `⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩` from `facts hN`. Use `⟨xj0 k₀ n' n, ?_⟩` and prove the remaining obligations. Unfold `PI.OneCosetSharp.Loc.E1`.

Simplify using `only [one_pow, one_mul, term_eq hN ψ₀ χ]`. Rewrite using `[Finset.sum_boole, Nat.cast_ne_zero, Finset.card_ne_zero]`. Use `⟨τ0 k₀ n' c n, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun _ => Finset.mem_univ _, ?_⟩⟩` and prove the remaining obligations. Use `⟨fun p' hp' => ?_, fun p p' hp hp' hne h0 => ?_⟩` and prove the remaining obligations. Rewrite using `[ent_τ0 hN (by omega) (by omega), if_pos rfl]`.

Conclude with `absurd (by rw [ent_τ0 hN hp (by omega), if_neg hne]) h0`.
-/
theorem claim2 : Claim2 := by
  unfold PI.OneCosetSharp.W.Claim2
  intro k _ _ ψ₀ χ k₀ m t j n' c n hN
  classical
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  refine ⟨xj0 k₀ n' n, ?_⟩
  unfold PI.OneCosetSharp.Loc.E1
  simp only [one_pow, one_mul, term_eq hN ψ₀ χ]
  rw [Finset.sum_boole, Nat.cast_ne_zero, Finset.card_ne_zero]
  refine ⟨τ0 k₀ n' c n, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun _ => Finset.mem_univ _, ?_⟩⟩
  refine ⟨fun p' hp' => ?_, fun p p' hp hp' hne h0 => ?_⟩
  · rw [ent_τ0 hN (by omega) (by omega), if_pos rfl]
  · exact absurd (by rw [ent_τ0 hN hp (by omega), if_neg hne]) h0

end PI.OneCosetSharp.W.C2
