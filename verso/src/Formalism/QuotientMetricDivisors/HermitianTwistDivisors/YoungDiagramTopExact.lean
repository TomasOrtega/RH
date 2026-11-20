import Formalism.QuotientMetricDivisors.TheoremDivIneqRowsShift
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramHook

open Finset

noncomputable section

namespace Formalism.DivisionValues

/- English proof (translation)
Introduce `J Pl _ _ TT _ n aT w wr ν ap fa a rd La k N S Sc t η m b' cs C1 C0 hLa h1 hk hkN hb' hcs hS hC2 hCcs hSc hC0 hle hsh hwA hBlA hBl0 haA hfa hoff htop`. Establish `hn0 : (0 : ℝ) ≤ (n : ℝ)` using `Nat.cast_nonneg n`. Establish `hk0 : 0 ≤ k` using `by linarith`. Establish `hN0 : 0 ≤ N` using `by linarith`. Establish `hcast : ∀ j ρ, (wr j ρ : ℝ) ≤ (w j ρ : ℝ)` using `fun j ρ => by exact_mod_cast hle j ρ`.

Take `⟨eE, δ, hE1, hE2, hE3, hE4⟩` from `young_diagram_step J Pl TT n aT wr ν ap fa a rd La k N S Sc t η m b' cs C1 hLa h1 hk hkN hb' hcs hC2 hCcs hSc (fun j ρ => by linarith [hwA j ρ, hcast j ρ]) hBlA (fun j ρ hρ => by linarith [haA j ρ hρ, hcast j ρ]) hfa hoff htop`. Use `⟨eE, fun j ρ => δ j ρ - k * ((w j ρ : ℝ) - (wr j ρ : ℝ)), hE1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j ρ`. Use `hE2 j ρ` as an intermediate fact. Simplify using `only`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `j ρ`. Establish `hw0 : (0 : ℝ) ≤ (wr j ρ : ℝ)` using `Nat.cast_nonneg _`. Establish `hX : (wr j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η ≤ (w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η`. Combine the linear relations using `[hcast j ρ]`.

Establish `hX0 : 0 ≤ (wr j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η` using `by positivity`. Establish `s1 : C1 * ((wr j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η) ≤ C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η)` using `mul_le_mul (by linarith) hX hX0 (by linarith)`. Conclude with `le_trans (hE3 j ρ) (mul_le_mul_of_nonneg_right s1 (by linarith))`. Introduce `j ρ`. Establish `hw0 : (0 : ℝ) ≤ (wr j ρ : ℝ)` using `Nat.cast_nonneg _`.

Establish `hT0 : 0 ≤ (if ρ ∈ TT then k * b' else 0)` using `by split_ifs`. Conclude with `mul_nonneg hk0 hb'`. Conclude with `le_rfl`. Use `set T := (if ρ ∈ TT then k * b' else 0) with hT`. Establish `hd : 0 ≤ (w j ρ : ℝ) - (wr j ρ : ℝ)` using `by linarith [hcast j ρ]`.

Establish `a1 : |δ j ρ - k * ((w j ρ : ℝ) - (wr j ρ : ℝ))| ≤ |δ j ρ| + k * ((w j ρ : ℝ) - (wr j ρ : ℝ))`. Use `abs_sub (δ j ρ) (k * ((w j ρ : ℝ) - (wr j ρ : ℝ)))` as an intermediate fact. Rewrite `this` using `[abs_of_nonneg (mul_nonneg hk0 hd)]`. Then use the resulting hypothesis. Establish `a2 : k * ((w j ρ : ℝ) - (wr j ρ : ℝ)) ≤ k * (cs * N)` using `mul_le_mul_of_nonneg_left (hsh j ρ) hk0`. Establish `a3 : C1 * ((wr j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) ≤ C1 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T)` using `mul_le_mul_of_nonneg_left (by linarith [hcast j ρ]) (by linarith)`.

Establish `hkS : 0 ≤ k * S` using `mul_nonneg hk0 hS`. Establish `a4 : k * (cs * N) ≤ cs * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T)`. Establish `: k * N ≤ (w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T` using `by nlinarith [hcast j ρ]`. Combine the equalities or inequalities in the displayed calculation. Establish `hY0 : 0 ≤ (w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T`.

Establish `: 0 ≤ k * N` using `mul_nonneg hk0 hN0`. Use polynomial arithmetic with `[hcast j ρ]`. Establish `a5 : (C1 + cs) * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) ≤ C0 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T)` using `mul_le_mul_of_nonneg_right hC0 hY0`. Use `hE4 j ρ` as an intermediate fact. Simplify using `only`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem young_diagram_step_shift : RowsStepEShift := by
  intro J Pl _ _ TT _ n aT w wr ν ap fa a rd La k N S Sc t η m b' cs C1 C0
    hLa h1 hk hkN hb' hcs hS hC2 hCcs hSc hC0 hle hsh hwA hBlA hBl0 haA hfa hoff htop
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hk0 : 0 ≤ k := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hcast : ∀ j ρ, (wr j ρ : ℝ) ≤ (w j ρ : ℝ) := fun j ρ => by exact_mod_cast hle j ρ
  obtain ⟨eE, δ, hE1, hE2, hE3, hE4⟩ := young_diagram_step J Pl TT n aT wr ν ap fa a rd La k N S Sc t η
    m b' cs C1 hLa h1 hk hkN hb' hcs hC2 hCcs hSc (fun j ρ => by linarith [hwA j ρ, hcast j ρ]) hBlA
    (fun j ρ hρ => by linarith [haA j ρ hρ, hcast j ρ]) hfa hoff htop
  refine ⟨eE, fun j ρ => δ j ρ - k * ((w j ρ : ℝ) - (wr j ρ : ℝ)), hE1, ?_, ?_, ?_⟩
  · intro j ρ
    have := hE2 j ρ
    simp only
    linarith
  · intro j ρ
    have hw0 : (0 : ℝ) ≤ (wr j ρ : ℝ) := Nat.cast_nonneg _
    have hX : (wr j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η ≤ (w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η := by
      linarith [hcast j ρ]
    have hX0 : 0 ≤ (wr j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η := by positivity
    have s1 : C1 * ((wr j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η) ≤
        C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η) :=
      mul_le_mul (by linarith) hX hX0 (by linarith)
    exact le_trans (hE3 j ρ) (mul_le_mul_of_nonneg_right s1 (by linarith))
  · intro j ρ
    have hw0 : (0 : ℝ) ≤ (wr j ρ : ℝ) := Nat.cast_nonneg _
    have hT0 : 0 ≤ (if ρ ∈ TT then k * b' else 0) := by
      split_ifs
      · exact mul_nonneg hk0 hb'
      · exact le_rfl
    set T := (if ρ ∈ TT then k * b' else 0) with hT
    have hd : 0 ≤ (w j ρ : ℝ) - (wr j ρ : ℝ) := by linarith [hcast j ρ]
    have a1 : |δ j ρ - k * ((w j ρ : ℝ) - (wr j ρ : ℝ))| ≤ |δ j ρ| + k * ((w j ρ : ℝ) - (wr j ρ : ℝ)) := by
      have := abs_sub (δ j ρ) (k * ((w j ρ : ℝ) - (wr j ρ : ℝ)))
      rwa [abs_of_nonneg (mul_nonneg hk0 hd)] at this
    have a2 : k * ((w j ρ : ℝ) - (wr j ρ : ℝ)) ≤ k * (cs * N) := mul_le_mul_of_nonneg_left (hsh j ρ) hk0
    have a3 : C1 * ((wr j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) ≤
        C1 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) :=
      mul_le_mul_of_nonneg_left (by linarith [hcast j ρ]) (by linarith)
    have hkS : 0 ≤ k * S := mul_nonneg hk0 hS
    have a4 : k * (cs * N) ≤ cs * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) := by
      have : k * N ≤ (w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T := by nlinarith [hcast j ρ]
      calc k * (cs * N) = cs * (k * N) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hcs
    have hY0 : 0 ≤ (w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T := by
      have : 0 ≤ k * N := mul_nonneg hk0 hN0
      nlinarith [hcast j ρ]
    have a5 : (C1 + cs) * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) ≤
        C0 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + T) := mul_le_mul_of_nonneg_right hC0 hY0
    have := hE4 j ρ
    simp only
    nlinarith

namespace RowsOrigin

/- English proof (translation)
Establish `anti : Antitone νr` using `Fin.antitone_iff_succ_le.2 (fun i => by`. Use `H1 i` as an intermediate fact. Use `H2 i` as an intermediate fact. Use the proof step `omega)`. Establish `lo : ∀ i, wr ≤ νr i` using `fun i => le_trans H3 (anti (Fin.le_last i))`.

Establish `hi : ∀ i, νr i ≤ νr 0` using `fun i => anti (Fin.zero_le i)`. Establish `loa : ∀ i, wr + T ≤ ar i` using `fun i => by have := H2 i; have := lo i.succ; omega`. Use `⟨fun i => νr i - wr, fun i => ar i - (wr + T), ar, blk, sm, ⟨?_, ?_⟩, ?_, hB, ?_, rfl⟩` and prove the remaining obligations. Introduce `i`. Use `⟨Nat.cast_nonneg _, ?_⟩` and prove the remaining obligations.

Establish `h1 : ((νr i - wr : ℕ) : ℝ) = (νr i : ℝ) - (wr : ℝ)` using `Nat.cast_sub (lo i)`. Establish `h2 : (νr i : ℝ) ≤ (νr 0 : ℝ)` using `by exact_mod_cast hi i`. Simplify using `only`. Rewrite using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `i`. Use `H1 i` as an intermediate fact. Use `H2 i` as an intermediate fact. Use `lo i.succ` as an intermediate fact. Use `lo i.castSucc` as an intermediate fact.

Prove the components needed by the constructor for the conclusion. Simplify using `only`. Conclude with `(by omega : ar i - (wr + T) ≤ νr i.castSucc - wr)` after adjusting the coercions. Simplify using `only`. Conclude with `(by omega : νr i.succ - wr ≤ ar i - (wr + T))` after adjusting the coercions.

Introduce `i`. Establish `h1 : ((ar i - (wr + T) : ℕ) : ℝ) = (ar i : ℝ) - ((wr : ℝ) + (T : ℝ))`. Rewrite using `[Nat.cast_sub (loa i)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only`. Rewrite using `[h1]`. Establish `: (ar i : ℝ) - ((wr : ℝ) + ((ar i : ℝ) - ((wr : ℝ) + (T : ℝ)))) = (T : ℝ)` using `by ring`. Rewrite using `[this, abs_of_nonneg (Nat.cast_nonneg _)]`. Conclude with `hT`.

Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `i _`. Use `lo i` as an intermediate fact. Simplify using `only`.

Use linear arithmetic over natural numbers and integers.
-/
theorem off_core {n wr T : ℕ} {Sc Bl sh : ℝ} (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ)
    (blk sm : Multiset ℕ)
    (H1 : ∀ i, ar i ≤ νr i.castSucc + T) (H2 : ∀ i, νr i.succ + T ≤ ar i)
    (H3 : wr ≤ νr (Fin.last (n + 1))) (H4 : (νr 0 : ℝ) ≤ (wr : ℝ) + Sc) (hT : (T : ℝ) ≤ sh)
    (hB : (blk.sum : ℝ) ≤ Bl) :
    IsRowsOff (n + 1) wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm) := by
  have anti : Antitone νr := Fin.antitone_iff_succ_le.2 (fun i => by
    have := H1 i; have := H2 i; omega)
  have lo : ∀ i, wr ≤ νr i := fun i => le_trans H3 (anti (Fin.le_last i))
  have hi : ∀ i, νr i ≤ νr 0 := fun i => anti (Fin.zero_le i)
  have loa : ∀ i, wr + T ≤ ar i := fun i => by have := H2 i; have := lo i.succ; omega
  refine ⟨fun i => νr i - wr, fun i => ar i - (wr + T), ar, blk, sm, ⟨?_, ?_⟩, ?_, hB, ?_, rfl⟩
  · intro i
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have h1 : ((νr i - wr : ℕ) : ℝ) = (νr i : ℝ) - (wr : ℝ) := Nat.cast_sub (lo i)
    have h2 : (νr i : ℝ) ≤ (νr 0 : ℝ) := by exact_mod_cast hi i
    simp only
    rw [h1]; linarith
  · intro i
    have := H1 i; have := H2 i; have := lo i.succ; have := lo i.castSucc
    constructor
    · simp only
      exact_mod_cast (by omega : ar i - (wr + T) ≤ νr i.castSucc - wr)
    · simp only
      exact_mod_cast (by omega : νr i.succ - wr ≤ ar i - (wr + T))
  · intro i
    have h1 : ((ar i - (wr + T) : ℕ) : ℝ) = (ar i : ℝ) - ((wr : ℝ) + (T : ℝ)) := by
      rw [Nat.cast_sub (loa i)]; push_cast; ring
    simp only
    rw [h1]
    have : (ar i : ℝ) - ((wr : ℝ) + ((ar i : ℝ) - ((wr : ℝ) + (T : ℝ)))) = (T : ℝ) := by ring
    rw [this, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hT
  · congr 1
    apply Multiset.map_congr rfl
    intro i _
    have := lo i
    simp only
    omega

/- English proof (translation)
Rewrite using `[Fin.univ_succ]`. Simplify using `only [Finset.cons_val, Multiset.map_cons, Finset.map_val, Multiset.map_map]`. Use `congr 1`. Rewrite using `[Fin.univ_castSuccEmb]`. Simplify using `only [Finset.cons_val, Multiset.map_cons, Finset.map_val, Multiset.map_map]`.

Both sides reduce to the same expression.
-/
theorem univ_split {n : ℕ} (g : Fin (n + 2) → ℕ) :
    (Finset.univ : Finset (Fin (n + 2))).val.map g =
      g 0 ::ₘ g (Fin.last (n + 1)) ::ₘ
        ((Finset.univ : Finset (Fin n)).val.map fun i => g i.castSucc.succ) := by
  rw [Fin.univ_succ]
  simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val, Multiset.map_map]
  congr 1
  rw [Fin.univ_castSuccEmb]
  simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val, Multiset.map_map]
  rfl

/- English proof (translation)
Establish `anti : Antitone ar` using `Fin.antitone_iff_succ_le.2 (fun i => by`. Establish `h1` using `H1 i.succ`. Establish `h2` using `H2 i.castSucc`. Rewrite `h2` using `[Fin.succ_castSucc]`. Use the proof step `omega)`.

Establish `loa : ∀ i, wr + T ≤ ar i` using `fun i => le_trans H3 (anti (Fin.le_last i))`. Establish `hia : ∀ i, ar i ≤ ar 0` using `fun i => anti (Fin.zero_le i)`. Establish `lo : ∀ i : Fin n, wr ≤ νr i.castSucc.succ` using `fun i => by`. Establish `h1` using `H1 i.succ`. Use `loa i.succ` as an intermediate fact.

Rewrite `h1` using `[← Fin.succ_castSucc]`. Use linear arithmetic over natural numbers and integers. Use `⟨fun i => νr i.castSucc.succ - wr, fun i => ar i - (wr + T), ar, νr (Fin.last (n + 1)), blk, sm, ⟨?_, ?_⟩, ?_, Hl, hB, ?_, rfl⟩` and prove the remaining obligations. Introduce `i`. Use `⟨Nat.cast_nonneg _, ?_⟩` and prove the remaining obligations.

Establish `h1 : ((ar i - (wr + T) : ℕ) : ℝ) = (ar i : ℝ) - ((wr : ℝ) + (T : ℝ))`. Rewrite using `[Nat.cast_sub (loa i)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (ar i : ℝ) ≤ (ar 0 : ℝ)` using `by exact_mod_cast hia i`.

Simplify using `only`. Rewrite using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i`. Establish `h1` using `H1 i.succ`.

Establish `h2` using `H2 i.castSucc`. Rewrite `h1` using `[← Fin.succ_castSucc]`. Use `lo i` as an intermediate fact. Use `loa i.succ` as an intermediate fact. Use `loa i.castSucc` as an intermediate fact.

Prove the components needed by the constructor for the conclusion. Simplify using `only`. Conclude with `(by omega : νr i.castSucc.succ - wr ≤ ar i.castSucc - (wr + T))` after adjusting the coercions. Simplify using `only`. Conclude with `(by omega : ar i.succ - (wr + T) ≤ νr i.castSucc.succ - wr)` after adjusting the coercions.

Introduce `i`. Establish `h1 : ((ar i - (wr + T) : ℕ) : ℝ) = (ar i : ℝ) - ((wr : ℝ) + (T : ℝ))`. Rewrite using `[Nat.cast_sub (loa i)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only`. Rewrite using `[h1]`. Establish `: (ar i : ℝ) - ((wr : ℝ) + ((ar i : ℝ) - ((wr : ℝ) + (T : ℝ)))) = (T : ℝ)` using `by ring`. Rewrite using `[this, abs_of_nonneg (Nat.cast_nonneg _)]`. Conclude with `hT`.

Rewrite using `[univ_split νr, H0, Multiset.cons_add, Multiset.cons_add]`. Use `congr 3`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `i _`. Use `lo i` as an intermediate fact.

Simplify using `only`. Use linear arithmetic over natural numbers and integers.
-/
theorem top_core {n wr T aT : ℕ} {Sc Bl sh : ℝ} (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ)
    (blk sm : Multiset ℕ)
    (H1 : ∀ i, ar i ≤ νr i.castSucc + T) (H2 : ∀ i, νr i.succ + T ≤ ar i)
    (H0 : νr 0 = aT + wr) (Hl : νr (Fin.last (n + 1)) ≤ wr)
    (H3 : wr + T ≤ ar (Fin.last n)) (H4 : (ar 0 : ℝ) ≤ (wr : ℝ) + (T : ℝ) + Sc) (hT : (T : ℝ) ≤ sh)
    (hB : (blk.sum : ℝ) ≤ Bl) :
    IsRowsTop n aT wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm) := by
  have anti : Antitone ar := Fin.antitone_iff_succ_le.2 (fun i => by
    have h1 := H1 i.succ; have h2 := H2 i.castSucc
    rw [Fin.succ_castSucc] at h2
    omega)
  have loa : ∀ i, wr + T ≤ ar i := fun i => le_trans H3 (anti (Fin.le_last i))
  have hia : ∀ i, ar i ≤ ar 0 := fun i => anti (Fin.zero_le i)
  have lo : ∀ i : Fin n, wr ≤ νr i.castSucc.succ := fun i => by
    have h1 := H1 i.succ; have := loa i.succ
    rw [← Fin.succ_castSucc] at h1
    omega
  refine ⟨fun i => νr i.castSucc.succ - wr, fun i => ar i - (wr + T), ar, νr (Fin.last (n + 1)), blk, sm,
    ⟨?_, ?_⟩, ?_, Hl, hB, ?_, rfl⟩
  · intro i
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have h1 : ((ar i - (wr + T) : ℕ) : ℝ) = (ar i : ℝ) - ((wr : ℝ) + (T : ℝ)) := by
      rw [Nat.cast_sub (loa i)]; push_cast; ring
    have h2 : (ar i : ℝ) ≤ (ar 0 : ℝ) := by exact_mod_cast hia i
    simp only
    rw [h1]; linarith
  · intro i
    have h1 := H1 i.succ; have h2 := H2 i.castSucc
    rw [← Fin.succ_castSucc] at h1
    have := lo i; have := loa i.succ; have := loa i.castSucc
    constructor
    · simp only
      exact_mod_cast (by omega : νr i.castSucc.succ - wr ≤ ar i.castSucc - (wr + T))
    · simp only
      exact_mod_cast (by omega : ar i.succ - (wr + T) ≤ νr i.castSucc.succ - wr)
  · intro i
    have h1 : ((ar i - (wr + T) : ℕ) : ℝ) = (ar i : ℝ) - ((wr : ℝ) + (T : ℝ)) := by
      rw [Nat.cast_sub (loa i)]; push_cast; ring
    simp only
    rw [h1]
    have : (ar i : ℝ) - ((wr : ℝ) + ((ar i : ℝ) - ((wr : ℝ) + (T : ℝ)))) = (T : ℝ) := by ring
    rw [this, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hT
  · rw [univ_split νr, H0, Multiset.cons_add, Multiset.cons_add]
    congr 3
    apply Multiset.map_congr rfl
    intro i _
    have := lo i
    simp only
    omega

/- English proof (translation)
Establish `hw' : (w : ℝ) = (wr : ℝ) + (s : ℝ)` using `by exact_mod_cast hw.symm`. Establish `hT : (((j - 1) * t : ℕ) : ℝ) = ((j : ℝ) - 1) * (t : ℝ)`. Rewrite using `[Nat.cast_mul, Nat.cast_sub hj]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Introduce `i`. Rewrite using `[hν i, originRow, hw', hs]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i`. Rewrite using `[ha i, originBig, hw', hs, hT]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem origin_rewrite {n j t w s wr : ℕ} {m : ℝ} {u : Fin (n + 2) → ℝ} {v : Fin (n + 1) → ℝ}
    {νr : Fin (n + 2) → ℕ} {ar : Fin (n + 1) → ℕ}
    (hj : 1 ≤ j) (hs : (s : ℝ) = (((n : ℝ) + 2) + (2 * (j : ℝ) - 1) * ((t : ℝ) + 1)) / 2)
    (hw : wr + s = w)
    (hν : ∀ i, (νr i : ℝ) = originRow ((n : ℝ) + 2) t j w (u i) ((i : ℕ) + 1))
    (ha : ∀ i, (ar i : ℝ) = originBig ((n : ℝ) + 2) m t j w (v i) ((i : ℕ) + 1)) :
    (∀ i, (νr i : ℝ) = (wr : ℝ) + (u i - (((n : ℝ) + 2) + 1 - 2 * (((i : ℕ) : ℝ) + 1)) / 2)) ∧
    (∀ i, (ar i : ℝ) = (wr : ℝ) + (v i - (((n : ℝ) + 2) - 2 * (((i : ℕ) : ℝ) + 1)) / 2) +
      (((j - 1) * t : ℕ) : ℝ)) := by
  have hw' : (w : ℝ) = (wr : ℝ) + (s : ℝ) := by exact_mod_cast hw.symm
  have hT : (((j - 1) * t : ℕ) : ℝ) = ((j : ℝ) - 1) * (t : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hj]; simp
  constructor
  · intro i
    rw [hν i, originRow, hw', hs]; ring
  · intro i
    rw [ha i, originBig, hw', hs, hT]; ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i`. Assume the negation of the conclusion as `hc`. Establish `h1 : νr i.castSucc + T + 1 ≤ ar i` using `by omega`. Establish `h2 : (νr i.castSucc : ℝ) + (T : ℝ) + 1 ≤ (ar i : ℝ)` using `by exact_mod_cast h1`.

Establish `h3` using `eν i.castSucc`. Rewrite `h3` using `[Fin.val_castSucc]`. Use `ea i` as an intermediate fact. Use `(hint i).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `i`. Assume the negation of the conclusion as `hc`. Establish `h1 : ar i + 1 ≤ νr i.succ + T` using `by omega`. Establish `h2 : (ar i : ℝ) + 1 ≤ (νr i.succ : ℝ) + (T : ℝ)` using `by exact_mod_cast h1`. Establish `h3` using `eν i.succ`.

Rewrite `h3` using `[Fin.val_succ]`. Move the coercions through the operations in `at h3`. Use `ea i` as an intermediate fact. Use `(hint i).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem origin_interlace {n wr T : ℕ} {u : Fin (n + 2) → ℝ} {v : Fin (n + 1) → ℝ}
    {νr : Fin (n + 2) → ℕ} {ar : Fin (n + 1) → ℕ}
    (eν : ∀ i, (νr i : ℝ) = (wr : ℝ) + (u i - (((n : ℝ) + 2) + 1 - 2 * (((i : ℕ) : ℝ) + 1)) / 2))
    (ea : ∀ i, (ar i : ℝ) = (wr : ℝ) + (v i - (((n : ℝ) + 2) - 2 * (((i : ℕ) : ℝ) + 1)) / 2) + (T : ℝ))
    (hint : ∀ i : Fin (n + 1), v i < u i.castSucc ∧ u i.succ < v i) :
    (∀ i, ar i ≤ νr i.castSucc + T) ∧ (∀ i, νr i.succ + T ≤ ar i) := by
  constructor
  · intro i
    by_contra hc
    have h1 : νr i.castSucc + T + 1 ≤ ar i := by omega
    have h2 : (νr i.castSucc : ℝ) + (T : ℝ) + 1 ≤ (ar i : ℝ) := by exact_mod_cast h1
    have h3 := eν i.castSucc
    rw [Fin.val_castSucc] at h3
    have := ea i; have := (hint i).1
    linarith
  · intro i
    by_contra hc
    have h1 : ar i + 1 ≤ νr i.succ + T := by omega
    have h2 : (ar i : ℝ) + 1 ≤ (νr i.succ : ℝ) + (T : ℝ) := by exact_mod_cast h1
    have h3 := eν i.succ
    rw [Fin.val_succ] at h3
    push_cast at h3
    have := ea i; have := (hint i).2
    linarith

end RowsOrigin

/- English proof (translation)
Introduce `n j t w s wr m Sc Bl sh u v νr ar blk sm hj hs hw hν ha hint hlo hhi hsh hB`. Take `⟨eν, ea⟩` from `RowsOrigin.origin_rewrite hj hs hw hν ha`. Take `⟨H1, H2⟩` from `RowsOrigin.origin_interlace eν ea hint`. Establish `hT : (((j - 1) * t : ℕ) : ℝ) = ((j : ℝ) - 1) * (t : ℝ)`. Rewrite using `[Nat.cast_mul, Nat.cast_sub hj]`.

Simplify using the standard rewrite rules. Use `RowsOrigin.off_core νr ar blk sm H1 H2 ?_ ?_ (by rw [hT]; exact hsh) hB` and prove the remaining obligations. Establish `h3` using `eν (Fin.last (n + 1))`. Rewrite `h3` using `[Fin.val_last]`. Move the coercions through the operations in `at h3`.

Establish `: (wr : ℝ) ≤ (νr (Fin.last (n + 1)) : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `h3` using `eν 0`. Simplify using `only [Fin.val_zero, Nat.cast_zero] at h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem young_diagram_origin_off : RowsOriginOff := by
  intro n j t w s wr m Sc Bl sh u v νr ar blk sm hj hs hw hν ha hint hlo hhi hsh hB
  obtain ⟨eν, ea⟩ := RowsOrigin.origin_rewrite hj hs hw hν ha
  obtain ⟨H1, H2⟩ := RowsOrigin.origin_interlace eν ea hint
  have hT : (((j - 1) * t : ℕ) : ℝ) = ((j : ℝ) - 1) * (t : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hj]; simp
  refine RowsOrigin.off_core νr ar blk sm H1 H2 ?_ ?_ (by rw [hT]; exact hsh) hB
  · have h3 := eν (Fin.last (n + 1))
    rw [Fin.val_last] at h3
    push_cast at h3
    have : (wr : ℝ) ≤ (νr (Fin.last (n + 1)) : ℝ) := by linarith
    exact_mod_cast this
  · have h3 := eν 0
    simp only [Fin.val_zero, Nat.cast_zero] at h3
    linarith

/- English proof (translation)
Introduce `n j t w s wr aT bT m Sc Bl sh u v νr ar blk sm hj hs hw hν ha hint hu0 hul hlo hhi hsh hB`. Take `⟨eν, ea⟩` from `RowsOrigin.origin_rewrite hj hs hw hν ha`. Take `⟨H1, H2⟩` from `RowsOrigin.origin_interlace eν ea hint`. Establish `hT : (((j - 1) * t : ℕ) : ℝ) = ((j : ℝ) - 1) * (t : ℝ)`. Rewrite using `[Nat.cast_mul, Nat.cast_sub hj]`.

Simplify using the standard rewrite rules. Use `RowsOrigin.top_core νr ar blk sm H1 H2 ?_ ?_ ?_ ?_ (by rw [hT]; exact hsh) hB` and prove the remaining obligations. Establish `h3` using `eν 0`. Simplify using `only [Fin.val_zero, Nat.cast_zero] at h3`. Rewrite `h3` using `[hu0]`.

Establish `: (νr 0 : ℝ) = (aT : ℝ) + (wr : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `h3` using `eν (Fin.last (n + 1))`. Rewrite `h3` using `[Fin.val_last, hul]`. Move the coercions through the operations in `at h3`.

Establish `hb : (0 : ℝ) ≤ (bT : ℝ)` using `Nat.cast_nonneg _`. Establish `: (νr (Fin.last (n + 1)) : ℝ) ≤ (wr : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `h3` using `ea (Fin.last n)`. Rewrite `h3` using `[Fin.val_last]`.

Establish `: (wr : ℝ) + (((j - 1) * t : ℕ) : ℝ) ≤ (ar (Fin.last n) : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `h3` using `ea 0`. Simplify using `only [Fin.val_zero, Nat.cast_zero] at h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem young_diagram_origin_top : RowsOriginTop := by
  intro n j t w s wr aT bT m Sc Bl sh u v νr ar blk sm hj hs hw hν ha hint hu0 hul hlo hhi hsh hB
  obtain ⟨eν, ea⟩ := RowsOrigin.origin_rewrite hj hs hw hν ha
  obtain ⟨H1, H2⟩ := RowsOrigin.origin_interlace eν ea hint
  have hT : (((j - 1) * t : ℕ) : ℝ) = ((j : ℝ) - 1) * (t : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hj]; simp
  refine RowsOrigin.top_core νr ar blk sm H1 H2 ?_ ?_ ?_ ?_ (by rw [hT]; exact hsh) hB
  · have h3 := eν 0
    simp only [Fin.val_zero, Nat.cast_zero] at h3
    rw [hu0] at h3
    have : (νr 0 : ℝ) = (aT : ℝ) + (wr : ℝ) := by linarith
    exact_mod_cast this
  · have h3 := eν (Fin.last (n + 1))
    rw [Fin.val_last, hul] at h3
    push_cast at h3
    have hb : (0 : ℝ) ≤ (bT : ℝ) := Nat.cast_nonneg _
    have : (νr (Fin.last (n + 1)) : ℝ) ≤ (wr : ℝ) := by linarith
    exact_mod_cast this
  · have h3 := ea (Fin.last n)
    rw [Fin.val_last] at h3
    have : (wr : ℝ) + (((j - 1) * t : ℕ) : ℝ) ≤ (ar (Fin.last n) : ℝ) := by linarith
    exact_mod_cast this
  · have h3 := ea 0
    simp only [Fin.val_zero, Nat.cast_zero] at h3
    linarith

/- English proof (translation)
Introduce `J Pl _ _ TT _ n t jj s aT bT w u v νr ar blk sm ν ap fa a rd La k N S Sc η m b' C1 C0 hLa h1 hk hm hN hb' hS hC2 hSc hC0 hj1 hjm hs hsw hwA hBlA hBl0 haA hfa hν hap hνr har hblk hint hoff htop`. Establish `hn0 : (0 : ℝ) ≤ (n : ℝ)` using `Nat.cast_nonneg n`. Establish `ht0 : (0 : ℝ) ≤ (t : ℝ)` using `Nat.cast_nonneg t`. Establish `hk0 : 0 ≤ k` using `by linarith`. Establish `hkN : k ≤ N`.

Establish `: 0 ≤ m * ((t : ℝ) + 1)` using `mul_nonneg hm (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hj1' : ∀ j, (1 : ℝ) ≤ (jj j : ℝ)` using `fun j => by exact_mod_cast hj1 j`. Establish `hsN : ∀ j, (s j : ℝ) ≤ 1 * N` using `fun j => by`. Establish `e1 : (jj j : ℝ) * ((t : ℝ) + 1) ≤ m * ((t : ℝ) + 1)` using `mul_le_mul_of_nonneg_right (hjm j) (by linarith)`.

Rewrite using `[hs j]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hshN : ∀ j, ((jj j : ℝ) - 1) * (t : ℝ) ≤ 1 * N` using `fun j => by`. Establish `e1 : (jj j : ℝ) * (t : ℝ) ≤ m * (t : ℝ)` using `mul_le_mul_of_nonneg_right (hjm j) ht0`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hwr : ∀ j ρ, (w j ρ - s j) + s j = w j ρ` using `fun j ρ => Nat.sub_add_cancel (hsw j ρ)`. Establish `hs' : ∀ j, (s j : ℝ) = (((n : ℝ) + 2) + (2 * (jj j : ℝ) - 1) * ((t : ℝ) + 1)) / 2` using `fun j => by`. Rewrite using `[hs j, hk]`. Use `young_diagram_step_shift J Pl TT n aT w (fun j ρ => w j ρ - s j) ν ap fa a rd La k N S Sc t η m b' 1 C1 C0 hLa h1 hk hkN hb' zero_le_one hS hC2 (by linarith) hSc hC0 (fun j ρ => Nat.sub_le _ _) ?_ hwA hBlA hBl0 haA hfa ?_ ?_` and prove the remaining obligations. Introduce `j ρ`.

Establish `: ((w j ρ - s j : ℕ) : ℝ) = (w j ρ : ℝ) - (s j : ℝ)` using `Nat.cast_sub (hsw j ρ)`. Rewrite using `[this]`. Combine the linear relations using `[hsN j]`. Introduce `j ρ hρ`. Rewrite using `[hν j ρ, hap j ρ]`.

Conclude with `young_diagram_origin_off n (jj j) t (w j ρ) (s j) (w j ρ - s j) m Sc _ _ (u ρ) (v ρ) (νr j ρ) (ar j ρ) (blk j ρ) (sm j ρ) (hj1 j) (hs' j) (hwr j ρ) (fun i => by rw [hνr j ρ i, hk]) (fun i => by rw [har j ρ i, hk]) (hint ρ) (by rw [← hk]; exact (hoff ρ hρ).1) (by rw [← hk]; exact …`. Introduce `j ρ hρ`. Rewrite using `[hν j ρ, hap j ρ]`. Take `⟨t1, t2, t3, t4⟩` from `htop ρ hρ`. Conclude with `young_diagram_origin_top n (jj j) t (w j ρ) (s j) (w j ρ - s j) (aT ρ) (bT ρ) m Sc _ _ (u ρ) (v ρ) (νr j ρ) (ar j ρ) (blk j ρ) (sm j ρ) (hj1 j) (hs' j) (hwr j ρ) (fun i => by rw [hνr j ρ i, hk]) (fun i => by rw [har j ρ i, hk]) (hint ρ) (by rw [← hk]; exact t1) (by rw [← hk]; exa …`.
-/
theorem young_diagram_step_origin : RowsStepEOrigin := by
  intro J Pl _ _ TT _ n t jj s aT bT w u v νr ar blk sm ν ap fa a rd La k N S Sc η m b' C1 C0
    hLa h1 hk hm hN hb' hS hC2 hSc hC0 hj1 hjm hs hsw hwA hBlA hBl0 haA hfa hν hap hνr har hblk
    hint hoff htop
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hk0 : 0 ≤ k := by linarith
  have hkN : k ≤ N := by
    have : 0 ≤ m * ((t : ℝ) + 1) := mul_nonneg hm (by linarith)
    linarith
  have hj1' : ∀ j, (1 : ℝ) ≤ (jj j : ℝ) := fun j => by exact_mod_cast hj1 j
  have hsN : ∀ j, (s j : ℝ) ≤ 1 * N := fun j => by
    have e1 : (jj j : ℝ) * ((t : ℝ) + 1) ≤ m * ((t : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (hjm j) (by linarith)
    rw [hs j]
    nlinarith
  have hshN : ∀ j, ((jj j : ℝ) - 1) * (t : ℝ) ≤ 1 * N := fun j => by
    have e1 : (jj j : ℝ) * (t : ℝ) ≤ m * (t : ℝ) := mul_le_mul_of_nonneg_right (hjm j) ht0
    nlinarith
  have hwr : ∀ j ρ, (w j ρ - s j) + s j = w j ρ := fun j ρ => Nat.sub_add_cancel (hsw j ρ)
  have hs' : ∀ j, (s j : ℝ) = (((n : ℝ) + 2) + (2 * (jj j : ℝ) - 1) * ((t : ℝ) + 1)) / 2 := fun j => by
    rw [hs j, hk]
  refine young_diagram_step_shift J Pl TT n aT w (fun j ρ => w j ρ - s j) ν ap fa a rd La k N S Sc t η
    m b' 1 C1 C0 hLa h1 hk hkN hb' zero_le_one hS hC2 (by linarith) hSc hC0
    (fun j ρ => Nat.sub_le _ _) ?_ hwA hBlA hBl0 haA hfa ?_ ?_
  · intro j ρ
    have : ((w j ρ - s j : ℕ) : ℝ) = (w j ρ : ℝ) - (s j : ℝ) := Nat.cast_sub (hsw j ρ)
    rw [this]
    linarith [hsN j]
  · intro j ρ hρ
    rw [hν j ρ, hap j ρ]
    exact young_diagram_origin_off n (jj j) t (w j ρ) (s j) (w j ρ - s j) m Sc _ _ (u ρ) (v ρ) (νr j ρ)
      (ar j ρ) (blk j ρ) (sm j ρ) (hj1 j) (hs' j) (hwr j ρ) (fun i => by rw [hνr j ρ i, hk])
      (fun i => by rw [har j ρ i, hk]) (hint ρ) (by rw [← hk]; exact (hoff ρ hρ).1)
      (by rw [← hk]; exact (hoff ρ hρ).2) (hshN j) (hblk j ρ)
  · intro j ρ hρ
    rw [hν j ρ, hap j ρ]
    obtain ⟨t1, t2, t3, t4⟩ := htop ρ hρ
    exact young_diagram_origin_top n (jj j) t (w j ρ) (s j) (w j ρ - s j) (aT ρ) (bT ρ) m Sc _ _ (u ρ) (v ρ)
      (νr j ρ) (ar j ρ) (blk j ρ) (sm j ρ) (hj1 j) (hs' j) (hwr j ρ) (fun i => by rw [hνr j ρ i, hk])
      (fun i => by rw [har j ρ i, hk]) (hint ρ) (by rw [← hk]; exact t1) (by rw [← hk]; exact t2)
      (by rw [← hk]; exact t3) (by rw [← hk]; exact t4) (hshN j) (hblk j ρ)

end Formalism.DivisionValues
