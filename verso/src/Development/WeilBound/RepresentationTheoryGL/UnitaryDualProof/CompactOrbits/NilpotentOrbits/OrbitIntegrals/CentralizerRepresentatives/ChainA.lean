import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.IsChain

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Consider the cases of `h`. Simplify using the standard rewrite rules. Introduce and unpack `⟨rfl, h⟩`.

Rewrite using `[Fin.ext h]`.
-/
theorem sigma_fin_eq_iff {ι : Type} {l : ι → ℕ} {b a : ι} {j : Fin (l b)} {i : Fin (l a)} :
    (⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, i⟩ ↔ b = a ∧ (j : ℕ) = i := by
  constructor
  · intro h
    cases h
    simp
  · rintro ⟨rfl, h⟩
    rw [Fin.ext h]

/- English proof (translation)
Establish `key : (B.coord ⟨a, i⟩).comp N = if h : 0 < (i : ℕ) then B.coord ⟨a, ⟨i - 1, by omega⟩⟩ else 0`. Apply `B.ext` to reduce the goal to its premises. Introduce and unpack `⟨b, j⟩`. Rewrite using `[LinearMap.comp_apply, hB]`. Distinguish the cases in `hi : 0 < (i : ℕ)`.

Rewrite using `[dif_pos hi]`. Distinguish the cases in `hj : (j : ℕ) + 1 < l b`. Rewrite using `[dif_pos hj, Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]`. Establish `hiff : ((⟨b, ⟨j + 1, hj⟩⟩ : Σ a, Fin (l a)) = ⟨a, i⟩) ↔ ((⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, ⟨i - 1, by omega⟩⟩)`. Rewrite using `[sigma_fin_eq_iff, sigma_fin_eq_iff]`.

Apply the tactic sequence `constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by simp only at h2 ⊢; omega⟩`. Conclude with `if_congr hiff rfl rfl`. Rewrite using `[dif_neg hj, map_zero, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg]`. Introduce `h`. Rewrite `h` using `[sigma_fin_eq_iff]`.

Take `⟨rfl, h2⟩` from `h`. Simplify using `only at h2`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg hi] split_ifs with hj`.

Rewrite using `[Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg, LinearMap.zero_apply]`. Introduce `h`. Rewrite `h` using `[sigma_fin_eq_iff]`. Take `⟨rfl, h2⟩` from `h`. Simplify using `only at h2`.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Use `LinearMap.congr_fun key z` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, Module.Basis.coord_apply]`. Rewrite using `[this]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem chain_repr_N {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr (N z) ⟨a, i⟩ = if h : 0 < (i : ℕ) then B.repr z ⟨a, ⟨i - 1, by omega⟩⟩ else 0 := by
  classical
  have key : (B.coord ⟨a, i⟩).comp N =
      if h : 0 < (i : ℕ) then B.coord ⟨a, ⟨i - 1, by omega⟩⟩ else 0 := by
    apply B.ext
    rintro ⟨b, j⟩
    rw [LinearMap.comp_apply, hB]
    by_cases hi : 0 < (i : ℕ)
    · rw [dif_pos hi]
      by_cases hj : (j : ℕ) + 1 < l b
      · rw [dif_pos hj, Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
          Module.Basis.repr_self_apply]
        have hiff : ((⟨b, ⟨j + 1, hj⟩⟩ : Σ a, Fin (l a)) = ⟨a, i⟩) ↔
            ((⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, ⟨i - 1, by omega⟩⟩) := by
          rw [sigma_fin_eq_iff, sigma_fin_eq_iff]
          constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by simp only at h2 ⊢; omega⟩
        exact if_congr hiff rfl rfl
      · rw [dif_neg hj, map_zero, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg]
        intro h
        rw [sigma_fin_eq_iff] at h
        obtain ⟨rfl, h2⟩ := h
        simp only at h2
        have := i.2
        omega
    · rw [dif_neg hi]
      split_ifs with hj
      · rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg, LinearMap.zero_apply]
        intro h
        rw [sigma_fin_eq_iff] at h
        obtain ⟨rfl, h2⟩ := h
        simp only at h2
        omega
      · simp
  have := LinearMap.congr_fun key z
  rw [LinearMap.comp_apply, Module.Basis.coord_apply] at this
  rw [this]
  split_ifs <;> simp

/- English proof (translation)
Proceed by induction on `m generalizing z with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ, Module.End.mul_apply, ih]`. Distinguish the cases in `h1 : m + 1 ≤ (i : ℕ)`.

Rewrite using `[dif_pos (by omega), dif_pos h1, chain_repr_N hB, dif_pos (by simp; omega)]`. Use `congr 2`. Rewrite using `[dif_neg h1] split_ifs with h2`. Rewrite using `[chain_repr_N hB, dif_neg]`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem chain_repr_Npow {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (m : ℕ) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr ((N ^ m) z) ⟨a, i⟩ = if h : m ≤ (i : ℕ) then B.repr z ⟨a, ⟨i - m, by omega⟩⟩ else 0 := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    by_cases h1 : m + 1 ≤ (i : ℕ)
    · rw [dif_pos (by omega), dif_pos h1, chain_repr_N hB, dif_pos (by simp; omega)]
      congr 2
    · rw [dif_neg h1]
      split_ifs with h2
      · rw [chain_repr_N hB, dif_neg]
        simp
        omega
      · rfl

/- English proof (translation)
Establish `h` using `chain_repr_Npow hB m z a ⟨i + m, hi⟩`. Rewrite `h` using `[hz, map_zero, dif_pos (by simp)]`. Rewrite `h` using `[Finsupp.zero_apply]`. Rewrite using `[h]`. Use `congr 2`.

Use `ext`. Simplify using the standard rewrite rules.
-/
theorem chain_repr_of_ker {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (m : ℕ) (z : W) (hz : (N ^ m) z = 0) (a : ι) (i : Fin (l a))
    (hi : (i : ℕ) + m < l a) : B.repr z ⟨a, i⟩ = 0 := by
  have h := chain_repr_Npow hB m z a ⟨i + m, hi⟩
  rw [hz, map_zero, dif_pos (by simp)] at h
  rw [Finsupp.zero_apply] at h
  rw [h]
  congr 2
  ext
  simp

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp [hb]`. Consider the case `succ j ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih]`. Distinguish the cases in `hj : j < l b`.

Rewrite using `[dif_pos hj, hB]`. Rewrite using `[dif_neg hj, map_zero, dif_neg (by omega)]`.
-/
theorem chain_Npow_zero {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (b : ι) (hb : 0 < l b) (j : ℕ) :
    (N ^ j) (B ⟨b, ⟨0, hb⟩⟩) = if h : j < l b then B ⟨b, ⟨j, h⟩⟩ else 0 := by
  induction j with
  | zero => simp [hb]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    by_cases hj : j < l b
    · rw [dif_pos hj, hB]
    · rw [dif_neg hj, map_zero, dif_neg (by omega)]

/- English proof (translation)
Establish `hc : Commute A N` using `hA`. Rewrite using `[hv, map_sum, map_sum, Finsupp.finsetSum_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Distinguish the cases in `hb : s b < l b`.

Rewrite using `[dif_pos hb]`. Establish `hlb : 0 < l b` using `by omega`. Establish `h1 : B ⟨b, ⟨s b, hb⟩⟩ = (N ^ s b) (B ⟨b, ⟨0, hlb⟩⟩)`. Rewrite using `[chain_Npow_zero hB b hlb, dif_pos hb]`. Establish `hcomm : ∀ m : ℕ, ∀ x, A ((N ^ m) x) = (N ^ m) (A x)` using `fun m x => LinearMap.congr_fun (hc.pow_right m).eq x`.

Rewrite using `[h1, hcomm, chain_repr_Npow hB]`. Use `split_ifs with h2`. Use `chain_repr_of_ker hB (l b) _ ?_ a _ ?_` and prove the remaining obligations. Rewrite using `[← hcomm, chain_Npow_zero hB b hlb, dif_neg (lt_irrefl _), map_zero]`. Use `hC a b show (i : ℕ) - s b + l b < l a` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Rewrite using `[dif_neg hb, map_zero, map_zero, Finsupp.zero_apply]`.
-/
theorem repr_centralizer_eq_zero (N : W →ₗ[E] W) {ι : Type} [Fintype ι] (l : ι → ℕ)
    (B : Module.Basis (Σ a, Fin (l a)) E W) (hB : IsChain N l B) (s : ι → ℕ) (_hs : ∀ a, s a ≤ l a)
    (hC : ∀ a b, s a ≤ s b + (l a - l b)) (v : W) (hv : v = ∑ a, if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0)
    (A : W →ₗ[E] W) (hA : A ∘ₗ N = N ∘ₗ A) (a : ι) (i : Fin (l a)) (hi : (i : ℕ) < s a) :
    B.repr (A v) ⟨a, i⟩ = 0 := by
  have hc : Commute A N := hA
  rw [hv, map_sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : s b < l b
  · rw [dif_pos hb]
    have hlb : 0 < l b := by omega
    have h1 : B ⟨b, ⟨s b, hb⟩⟩ = (N ^ s b) (B ⟨b, ⟨0, hlb⟩⟩) := by
      rw [chain_Npow_zero hB b hlb, dif_pos hb]
    have hcomm : ∀ m : ℕ, ∀ x, A ((N ^ m) x) = (N ^ m) (A x) := fun m x =>
      LinearMap.congr_fun (hc.pow_right m).eq x
    rw [h1, hcomm, chain_repr_Npow hB]
    split_ifs with h2
    · refine chain_repr_of_ker hB (l b) _ ?_ a _ ?_
      · rw [← hcomm, chain_Npow_zero hB b hlb, dif_neg (lt_irrefl _), map_zero]
      · have := hC a b
        show (i : ℕ) - s b + l b < l a
        omega
    · rfl
  · rw [dif_neg hb, map_zero, map_zero, Finsupp.zero_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
