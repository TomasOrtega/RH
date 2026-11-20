import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.ColComplete

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `m hm u hu`. Use `⟨id, ?_⟩` and prove the remaining obligations.

Establish `: (fun i : Fin N => if (i : ℕ) < m then u i else Pi.single (id i) (1 : C)) = u`. Use function extensionality and compare the values at `i; rw [if_pos (by omega)]`. Rewrite using `[this]`. Substitute `hm` using the available equality. Simplify using `using hu`.

Consider the case `succ n ih`. Introduce `m hm u hu`. Establish `hmN : m < N` using `by omega`. Establish `hW : Submodule.span C (Set.range (fun i : Fin m => u (Fin.castLE (by omega) i))) ≠ ⊤`. Introduce `h`.

Establish `h1` using `finrank_span_eq_card hu`. Rewrite `h1` using `[h, finrank_top]`. Simplify using `at h1`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j : Fin N, Pi.single j (1:C) ∉ Submodule.span C (Set.range (fun i : Fin m => u (Fin.castLE (by omega) i))) := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hW` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← (Pi.basisFun C (Fin N)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Simplify using `using hc j`. Set `m' : Fin N` to `⟨m, hmN⟩`. Set `u'` to `Function.update u m' (Pi.single j 1)`. Establish `hu' : LinearIndependent C (fun i : Fin (m+1) => u' (Fin.castLE (by omega) i))`. Establish `: (fun i : Fin (m+1) => u' (Fin.castLE (by omega) i)) = Fin.snoc (fun i : Fin m => u (Fin.castLE (by omega) i)) (Pi.single j (1:C))`.

Use function extensionality and compare the values at `i`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations. Establish `: (Fin.castLE (by omega) (Fin.last m) : Fin N) = m'` using `by ext; simp [m']`. Simplify using `only [Fin.snoc_last, u', this, Function.update_self]`. Establish `: (Fin.castLE (by omega) (Fin.castSucc i) : Fin N) ≠ m'`.

Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[m'] at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Fin.snoc_castSucc, u', Function.update_of_ne this]`.

Both sides reduce to the same expression. Rewrite using `[this, linearIndependent_fin_snoc]`. Conclude with `⟨hu, hj⟩`. Take `⟨g', hg'⟩` from `ih (m+1) (by omega) u' hu'`. Use `⟨Function.update g' m' j, ?_⟩` and prove the remaining obligations.

Use `hg' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Break down `lt_trichotomy (i : ℕ) m with hi | hi | hi` into its components or cases. Establish `hne : i ≠ m'` using `by intro h; rw [h] at hi; simp [m'] at hi`. Rewrite using `[if_pos hi, if_pos (by omega)]`.

Simplify using `only [u', Function.update_of_ne hne]`. Establish `he : i = m'` using `by ext; simp [m', hi]`. Rewrite using `[if_neg (by omega), if_pos (by omega)]`. Substitute `he` using the available equality. Simplify using `only [u', Function.update_self]`.

Establish `hne : i ≠ m'` using `by intro h; rw [h] at hi; simp [m'] at hi`. Rewrite using `[if_neg (by omega), if_neg (by omega), Function.update_of_ne hne]`.
-/
theorem extend_std {C : Type} [Field C] (N : ℕ) :
    ∀ n m : ℕ, (h : m + n = N) → ∀ u : Fin N → (Fin N → C),
      LinearIndependent C (fun i : Fin m => u (Fin.castLE (by omega) i)) →
      ∃ g : Fin N → Fin N, LinearIndependent C
        (fun i : Fin N => if (i : ℕ) < m then u i else Pi.single (g i) (1 : C)) := by
  intro n
  induction n with
  | zero =>
    intro m hm u hu
    refine ⟨id, ?_⟩
    have : (fun i : Fin N => if (i : ℕ) < m then u i else Pi.single (id i) (1 : C)) = u := by
      funext i; rw [if_pos (by omega)]
    rw [this]
    subst hm
    simpa using hu
  | succ n ih =>
    intro m hm u hu
    have hmN : m < N := by omega
    have hW : Submodule.span C (Set.range (fun i : Fin m => u (Fin.castLE (by omega) i))) ≠ ⊤ := by
      intro h
      have h1 := finrank_span_eq_card hu
      rw [h, finrank_top] at h1
      simp at h1
      omega
    obtain ⟨j, hj⟩ : ∃ j : Fin N, Pi.single j (1:C) ∉
        Submodule.span C (Set.range (fun i : Fin m => u (Fin.castLE (by omega) i))) := by
      by_contra hc
      push_neg at hc
      apply hW
      rw [eq_top_iff, ← (Pi.basisFun C (Fin N)).span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simpa using hc j
    let m' : Fin N := ⟨m, hmN⟩
    let u' := Function.update u m' (Pi.single j 1)
    have hu' : LinearIndependent C (fun i : Fin (m+1) => u' (Fin.castLE (by omega) i)) := by
      have : (fun i : Fin (m+1) => u' (Fin.castLE (by omega) i)) =
          Fin.snoc (fun i : Fin m => u (Fin.castLE (by omega) i)) (Pi.single j (1:C)) := by
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · have : (Fin.castLE (by omega) (Fin.last m) : Fin N) = m' := by ext; simp [m']
          simp only [Fin.snoc_last, u', this, Function.update_self]
        · have : (Fin.castLE (by omega) (Fin.castSucc i) : Fin N) ≠ m' := by
            intro h; have := congrArg Fin.val h; simp [m'] at this; omega
          simp only [Fin.snoc_castSucc, u', Function.update_of_ne this]
          rfl
      rw [this, linearIndependent_fin_snoc]
      exact ⟨hu, hj⟩
    obtain ⟨g', hg'⟩ := ih (m+1) (by omega) u' hu'
    refine ⟨Function.update g' m' j, ?_⟩
    convert hg' using 1
    funext i
    rcases lt_trichotomy (i : ℕ) m with hi | hi | hi
    · have hne : i ≠ m' := by intro h; rw [h] at hi; simp [m'] at hi
      rw [if_pos hi, if_pos (by omega)]
      simp only [u', Function.update_of_ne hne]
    · have he : i = m' := by ext; simp [m', hi]
      rw [if_neg (by omega), if_pos (by omega)]
      subst he
      simp only [u', Function.update_self]
    · have hne : i ≠ m' := by intro h; rw [h] at hi; simp [m'] at hi
      rw [if_neg (by omega), if_neg (by omega), Function.update_of_ne hne]

/- English proof (translation)
Introduce `C _ N β`. Establish `hr : β.rank ≤ N` using `by simpa using β.rank_le_card_width`. Use `⟨hr, ?_⟩` and prove the remaining obligations. Take `⟨κ, a, ha, hsp, hli⟩` from `exists_linearIndependent' C β.col`. Use `haveI : Finite κ := hli.finite`.

Use `haveI := Fintype.ofFinite κ`. Establish `hcard : Fintype.card κ = β.rank`. Rewrite using `[β.rank_eq_finrank_span_cols, ← hsp, finrank_span_eq_card hli]`. Set `e : Fin β.rank ≃ κ` to `(Fintype.equivFinOfCardEq hcard).symm`. Set `k : Fin N → Fin N` to `fun i => if h : (i:ℕ) < β.rank then a (e ⟨i, h⟩) else i`.

Take `⟨g, hg⟩` from `extend_std N (N - β.rank) β.rank (by omega) (fun i => β *ᵥ Pi.single (k i) 1) (by`. Establish `: (fun i : Fin β.rank => β *ᵥ Pi.single (k (Fin.castLE (by omega) i)) (1:C)) = (β.col ∘ a) ∘ e`. Use function extensionality and compare the values at `i`. Simplify using `[k, Matrix.mulVec_single_one]`. Rewrite using `[this]`.

Conclude with `hli.comp e e.injective)`. Use `⟨k, g, ?_⟩` and prove the remaining obligations. Rewrite using `[← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]`. Conclude with `hg`.
-/
theorem cols_complete : ∀ (C : Type) [Field C] (N : ℕ) (β : Matrix (Fin N) (Fin N) C),
    β.rank ≤ N ∧ ∃ k k' : Fin N → Fin N,
      (Matrix.of fun i : Fin N => if (i : ℕ) < β.rank then β *ᵥ Pi.single (k i) 1
        else Pi.single (k' i) 1).det ≠ 0 := by
  intro C _ N β
  have hr : β.rank ≤ N := by simpa using β.rank_le_card_width
  refine ⟨hr, ?_⟩
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' C β.col
  haveI : Finite κ := hli.finite
  haveI := Fintype.ofFinite κ
  have hcard : Fintype.card κ = β.rank := by
    rw [β.rank_eq_finrank_span_cols, ← hsp, finrank_span_eq_card hli]
  let e : Fin β.rank ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let k : Fin N → Fin N := fun i => if h : (i:ℕ) < β.rank then a (e ⟨i, h⟩) else i
  obtain ⟨g, hg⟩ := extend_std N (N - β.rank) β.rank (by omega)
    (fun i => β *ᵥ Pi.single (k i) 1) (by
      have : (fun i : Fin β.rank => β *ᵥ Pi.single (k (Fin.castLE (by omega) i)) (1:C)) =
          (β.col ∘ a) ∘ e := by
        funext i
        simp [k, Matrix.mulVec_single_one]
      rw [this]
      exact hli.comp e e.injective)
  refine ⟨k, g, ?_⟩
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_rows_iff_isUnit]
  exact hg

end GlobalTheory.ColComplete
