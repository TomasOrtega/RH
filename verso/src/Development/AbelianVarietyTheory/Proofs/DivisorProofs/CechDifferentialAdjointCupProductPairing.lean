import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD.CupAdj

variable {k : Type} [Field k] {E : Type} [AddCommGroup E] [Module k E] {ι : Type} [LinearOrder ι]

/- English proof (translation)
The claim follows from `(Submodule.mem_pi.1 ha) s (Set.mem_univ _)`.
-/
theorem cech_apply_mem {F : Finset ι → Submodule k E} {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n)
    (s : Finset ι) : a s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then F s else ⊥) :=
  (Submodule.mem_pi.1 ha) s (Set.mem_univ _)

/- English proof (translation)
Use `cech_apply_mem ha s` as an intermediate fact. Rewrite `this` using `[if_neg h]`. Conclude with `(Submodule.mem_bot k).1 this`.
-/
theorem cech_apply_eq_zero {F : Finset ι → Submodule k E} {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n)
    {s : Finset ι} (h : ¬ (s.Nonempty ∧ (s.card : ℤ) = n + 1)) : a s = 0 := by
  have := cech_apply_mem ha s
  rw [if_neg h] at this
  exact (Submodule.mem_bot k).1 this

/- English proof (translation)
Distinguish the cases in `h : s.Nonempty ∧ (s.card : ℤ) = n + 1`. Use `cech_apply_mem ha s` as an intermediate fact. Rewrite `this` using `[if_pos h]`. Conclude with `hF s t h.1 hst this`. Rewrite using `[cech_apply_eq_zero ha h]`.

Conclude with `zero_mem _`.
-/
theorem cech_apply_mem_of_subset {F : Finset ι → Submodule k E} (hF : ∀ s t, s.Nonempty → s ⊆ t → F s ≤ F t)
    {n : ℤ} {a : Finset ι → E} (ha : a ∈ cechC F n) {s t : Finset ι} (hst : s ⊆ t) : a s ∈ F t := by
  by_cases h : s.Nonempty ∧ (s.card : ℤ) = n + 1
  · have := cech_apply_mem ha s
    rw [if_pos h] at this
    exact hF s t h.1 hst this
  · rw [cech_apply_eq_zero ha h]; exact zero_mem _

end GlobalTheory.PD.CupAdj

namespace GlobalTheory.PD.CupAdj

/- English proof (translation)
Simplify using `[cupPair]`.
-/
theorem cupPair_apply {k : Type} [Field k] {d : ℕ} {E : Type} [AddCommGroup E] [Module k E] {E' : Type}
    [AddCommGroup E'] [Module k E'] (β : E →ₗ[k] E' →ₗ[k] k) (a : Finset (Fin (d+1)) → E)
    (b : Finset (Fin (d+1)) → E') :
    cupPair β a b = ∑ j, β (a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) := by
  simp [cupPair]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem deltaL_apply {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]
    (a : Finset ι → E) (t : Finset ι) :
    deltaL k ι E a t = ∑ i ∈ t, GlobalTheory.cubeSign t i • a (t.erase i) := rfl

/- English proof (translation)
Rewrite using `[show Finset.univ.filter (· ≤ j) = Finset.Iic j by ext; simp, Fin.card_Iic]`.
-/
theorem card_le (d : ℕ) (j : Fin (d+1)) : (Finset.univ.filter (· ≤ j)).card = j.val + 1 := by
  rw [show Finset.univ.filter (· ≤ j) = Finset.Iic j by ext; simp, Fin.card_Iic]

/- English proof (translation)
Rewrite using `[show Finset.univ.filter (j ≤ ·) = Finset.Ici j by ext; simp, Fin.card_Ici]`.
-/
theorem card_ge (d : ℕ) (j : Fin (d+1)) : (Finset.univ.filter (j ≤ ·)).card = d + 1 - j.val := by
  rw [show Finset.univ.filter (j ≤ ·) = Finset.Ici j by ext; simp, Fin.card_Ici]

/- English proof (translation)
Introduce `n`. Establish `van : ∀ {m m' : ℤ} {a : Finset (Fin (d+1)) → E} {b : Finset (Fin (d+1)) → E'}, a ∈ cechC A m → b ∈ cechC B m' → ∀ i s t, s ⊆ Finset.univ.erase i → t ⊆ Finset.univ.erase i → β (a s) (b t) = 0`. Introduce `m m' a b ha hb i s t hs ht`. Distinguish the cases in `hne : s.Nonempty`. Conclude with `hβ i (hne.mono hs) _ (cech_apply_mem_of_subset hA ha hs) _ (cech_apply_mem_of_subset hB hb ht)`.

Rewrite using `[cech_apply_eq_zero ha (fun h => hne h.1), map_zero, LinearMap.zero_apply]`. Distinguish the cases in `hn : 0 ≤ n ∧ n + 1 ≤ d`. Take `⟨m, rfl⟩ : ∃ m : ℕ, n = m` from `⟨n.toNat, (Int.toNat_of_nonneg hn.1).symm⟩`. Establish `hmd : m + 1 ≤ d` using `by exact_mod_cast hn.2`. Use `set j : Fin (d+1) := ⟨m + 1, by omega⟩ with hj`.

Use `set j' : Fin (d+1) := ⟨m, by omega⟩ with hj'`. Use `⟨(-1 : ℤˣ) ^ ((Finset.univ.filter (· ≤ j)).filter (· < j)).card, ?_⟩` and prove the remaining obligations. Introduce `a ha b hb`. Express the relevant statement in the definitionally equal form `cupPair β (deltaL k _ E a) b = _ • cupPair β a (deltaL k _ E' b)`. Establish `L1 : cupPair β (deltaL k _ E a) b = β (deltaL k _ E a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·)))`.

Rewrite using `[cupPair_apply]`. Use `Finset.sum_eq_single j (fun j0 _ hj0 => ?_) (by simp)` and prove the remaining obligations. Rewrite using `[cech_apply_eq_zero hb (s := Finset.univ.filter (j0 ≤ ·)), map_zero]`. Introduce and unpack `⟨-, h⟩`. Use `j0.isLt` as an intermediate fact.

Rewrite `h` using `[card_ge, Nat.cast_sub (by omega)]`. Move the coercions through the operations in `at h`. Apply `hj0` to reduce the goal to its premises. Use `ext`. Simplify using `only [hj]`.

Use linear arithmetic over natural numbers and integers. Establish `L2 : cupPair β a (deltaL k _ E' b) = β (a (Finset.univ.filter (· ≤ j'))) (deltaL k _ E' b (Finset.univ.filter (j' ≤ ·)))`. Rewrite using `[cupPair_apply]`. Use `Finset.sum_eq_single j' (fun j0 _ hj0 => ?_) (by simp)` and prove the remaining obligations. Rewrite using `[cech_apply_eq_zero ha (s := Finset.univ.filter (· ≤ j0)), map_zero, LinearMap.zero_apply]`.

Introduce and unpack `⟨-, h⟩`. Rewrite `h` using `[card_le]`. Move the coercions through the operations in `at h`. Apply `hj0` to reduce the goal to its premises. Use `ext`.

Simplify using `only [hj']`. Use linear arithmetic over natural numbers and integers. Establish `L3 : β (deltaL k _ E a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) = GlobalTheory.cubeSign (Finset.univ.filter (· ≤ j)) j • β (a ((Finset.univ.filter (· ≤ j)).erase j)) (b (Finset.univ.filter (j ≤ ·)))`. Rewrite using `[deltaL_apply, map_sum, LinearMap.sum_apply]`. Use `(Finset.sum_eq_single j (fun i hi hij => ?_) (by simp)).trans ?_` and prove the remaining obligations.

Rewrite using `[map_zsmul, LinearMap.smul_apply]`. Establish `hi' : i < j` using `lt_of_le_of_ne (by simpa using hi) hij`. Rewrite using `[van ha hb i _ _ ?_ ?_, smul_zero]`. Introduce `x hx`. Simplify using `only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`.

Conclude with `⟨hx.1, trivial⟩`. Introduce `x hx`. Simplify using `only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`. Conclude with `⟨fun h => by subst h; exact absurd hx (not_le.2 hi'), trivial⟩`. Rewrite using `[map_zsmul, LinearMap.smul_apply]`.

Establish `L4 : β (a (Finset.univ.filter (· ≤ j'))) (deltaL k _ E' b (Finset.univ.filter (j' ≤ ·))) = β (a (Finset.univ.filter (· ≤ j'))) (b ((Finset.univ.filter (j' ≤ ·)).erase j'))`. Rewrite using `[deltaL_apply, map_sum]`. Use `(Finset.sum_eq_single j' (fun i hi hij => ?_) (by simp)).trans ?_` and prove the remaining obligations. Rewrite using `[map_zsmul]`. Establish `hi' : j' < i` using `lt_of_le_of_ne (by simpa using hi) (Ne.symm hij)`.

Rewrite using `[van ha hb i _ _ ?_ ?_, smul_zero]`. Introduce `x hx`. Simplify using `only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`. Conclude with `⟨fun h => by subst h; exact absurd hx (not_le.2 hi'), trivial⟩`. Introduce `x hx`.

Simplify using `only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`. Conclude with `⟨hx.1, trivial⟩`. Establish `: GlobalTheory.cubeSign (Finset.univ.filter (j' ≤ ·)) j' = 1`. Rewrite using `[GlobalTheory.cubeSign]`. Establish `: ((Finset.univ.filter (j' ≤ ·)).filter (· < j')) = ∅`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[this, one_smul]`.

Establish `e1 : (Finset.univ.filter (· ≤ j)).erase j = Finset.univ.filter (· ≤ j')`. Use extensionality with `x`. Simplify using `only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, Fin.le_iff_val_le_val, hj, hj']`. Use linear arithmetic over natural numbers and integers. Establish `e2 : Finset.univ.filter (j ≤ ·) = (Finset.univ.filter (j' ≤ ·)).erase j'`.

Use extensionality with `x`. Simplify using `only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, Fin.le_iff_val_le_val, hj, hj']`. Use linear arithmetic over natural numbers and integers. Rewrite using `[L1, L2, L3, L4, e1, e2, GlobalTheory.cubeSign, Units.smul_def]`. Use `push_cast`.

Both sides reduce to the same expression. Use `⟨1, ?_⟩` and prove the remaining obligations. Introduce `a ha b hb`. Rewrite using `[one_smul]`. Break down `not_and_or.1 hn with h | h` into its components or cases.

Establish `: a = 0`. Use function extensionality and compare the values at `s`. Use `cech_apply_eq_zero ha ?_` and prove the remaining obligations. Introduce and unpack `⟨hs, hc⟩`. Use `hs.card_pos` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Express the relevant statement in the definitionally equal form `cupPair β (deltaL k _ E a) b = cupPair β a (deltaL k _ E' b)`. Simplify using `[this]`. Establish `: b = 0`. Use function extensionality and compare the values at `s`.

Use `cech_apply_eq_zero hb ?_` and prove the remaining obligations. Introduce and unpack `⟨hs, hc⟩`. Use `hs.card_pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Express the relevant statement in the definitionally equal form `cupPair β (deltaL k _ E a) b = cupPair β a (deltaL k _ E' b)`.

Simplify using `[this]`.
-/
theorem cech_adj (k : Type) [Field k] (d : ℕ) (E : Type) [AddCommGroup E] [Module k E] (E' : Type)
    [AddCommGroup E'] [Module k E'] (A : Finset (Fin (d + 1)) → Submodule k E)
    (B : Finset (Fin (d + 1)) → Submodule k E') (β : E →ₗ[k] E' →ₗ[k] k)
    (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) (hB : ∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t)
    (hβ : ∀ i, (Finset.univ.erase i).Nonempty → ∀ a ∈ A (Finset.univ.erase i), ∀ b ∈ B (Finset.univ.erase i),
      β a b = 0) :
    Adj (cech A) (cech B) (cupPair β) d := by
  intro n
  have van : ∀ {m m' : ℤ} {a : Finset (Fin (d+1)) → E} {b : Finset (Fin (d+1)) → E'},
      a ∈ cechC A m → b ∈ cechC B m' → ∀ i s t, s ⊆ Finset.univ.erase i → t ⊆ Finset.univ.erase i →
      β (a s) (b t) = 0 := by
    intro m m' a b ha hb i s t hs ht
    by_cases hne : s.Nonempty
    · exact hβ i (hne.mono hs) _ (cech_apply_mem_of_subset hA ha hs) _ (cech_apply_mem_of_subset hB hb ht)
    · rw [cech_apply_eq_zero ha (fun h => hne h.1), map_zero, LinearMap.zero_apply]
  by_cases hn : 0 ≤ n ∧ n + 1 ≤ d
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.1).symm⟩
    have hmd : m + 1 ≤ d := by exact_mod_cast hn.2
    set j : Fin (d+1) := ⟨m + 1, by omega⟩ with hj
    set j' : Fin (d+1) := ⟨m, by omega⟩ with hj'
    refine ⟨(-1 : ℤˣ) ^ ((Finset.univ.filter (· ≤ j)).filter (· < j)).card, ?_⟩
    intro a ha b hb
    change cupPair β (deltaL k _ E a) b = _ • cupPair β a (deltaL k _ E' b)
    have L1 : cupPair β (deltaL k _ E a) b =
        β (deltaL k _ E a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) := by
      rw [cupPair_apply]
      refine Finset.sum_eq_single j (fun j0 _ hj0 => ?_) (by simp)
      rw [cech_apply_eq_zero hb (s := Finset.univ.filter (j0 ≤ ·)), map_zero]
      rintro ⟨-, h⟩
      have := j0.isLt
      rw [card_ge, Nat.cast_sub (by omega)] at h
      push_cast at h
      apply hj0; ext; simp only [hj]; omega
    have L2 : cupPair β a (deltaL k _ E' b) =
        β (a (Finset.univ.filter (· ≤ j'))) (deltaL k _ E' b (Finset.univ.filter (j' ≤ ·))) := by
      rw [cupPair_apply]
      refine Finset.sum_eq_single j' (fun j0 _ hj0 => ?_) (by simp)
      rw [cech_apply_eq_zero ha (s := Finset.univ.filter (· ≤ j0)), map_zero, LinearMap.zero_apply]
      rintro ⟨-, h⟩
      rw [card_le] at h
      push_cast at h
      apply hj0; ext; simp only [hj']; omega
    have L3 : β (deltaL k _ E a (Finset.univ.filter (· ≤ j))) (b (Finset.univ.filter (j ≤ ·))) =
        GlobalTheory.cubeSign (Finset.univ.filter (· ≤ j)) j •
          β (a ((Finset.univ.filter (· ≤ j)).erase j)) (b (Finset.univ.filter (j ≤ ·))) := by
      rw [deltaL_apply, map_sum, LinearMap.sum_apply]
      refine (Finset.sum_eq_single j (fun i hi hij => ?_) (by simp)).trans ?_
      · rw [map_zsmul, LinearMap.smul_apply]
        have hi' : i < j := lt_of_le_of_ne (by simpa using hi) hij
        rw [van ha hb i _ _ ?_ ?_, smul_zero]
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨hx.1, trivial⟩
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨fun h => by subst h; exact absurd hx (not_le.2 hi'), trivial⟩
      · rw [map_zsmul, LinearMap.smul_apply]
    have L4 : β (a (Finset.univ.filter (· ≤ j'))) (deltaL k _ E' b (Finset.univ.filter (j' ≤ ·))) =
        β (a (Finset.univ.filter (· ≤ j'))) (b ((Finset.univ.filter (j' ≤ ·)).erase j')) := by
      rw [deltaL_apply, map_sum]
      refine (Finset.sum_eq_single j' (fun i hi hij => ?_) (by simp)).trans ?_
      · rw [map_zsmul]
        have hi' : j' < i := lt_of_le_of_ne (by simpa using hi) (Ne.symm hij)
        rw [van ha hb i _ _ ?_ ?_, smul_zero]
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨fun h => by subst h; exact absurd hx (not_le.2 hi'), trivial⟩
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨hx.1, trivial⟩
      · have : GlobalTheory.cubeSign (Finset.univ.filter (j' ≤ ·)) j' = 1 := by
          rw [GlobalTheory.cubeSign]
          have : ((Finset.univ.filter (j' ≤ ·)).filter (· < j')) = ∅ := by
            ext x; simp
          rw [this]; simp
        rw [this, one_smul]
    have e1 : (Finset.univ.filter (· ≤ j)).erase j = Finset.univ.filter (· ≤ j') := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, Fin.le_iff_val_le_val, hj, hj']
      omega
    have e2 : Finset.univ.filter (j ≤ ·) = (Finset.univ.filter (j' ≤ ·)).erase j' := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, Fin.le_iff_val_le_val, hj, hj']
      omega
    rw [L1, L2, L3, L4, e1, e2, GlobalTheory.cubeSign, Units.smul_def]
    push_cast
    rfl
  · refine ⟨1, ?_⟩
    intro a ha b hb
    rw [one_smul]
    rcases not_and_or.1 hn with h | h
    · have : a = 0 := by
        funext s
        refine cech_apply_eq_zero ha ?_
        rintro ⟨hs, hc⟩
        have := hs.card_pos
        omega
      change cupPair β (deltaL k _ E a) b = cupPair β a (deltaL k _ E' b)
      simp [this]
    · have : b = 0 := by
        funext s
        refine cech_apply_eq_zero hb ?_
        rintro ⟨hs, hc⟩
        have := hs.card_pos
        omega
      change cupPair β (deltaL k _ E a) b = cupPair β a (deltaL k _ E' b)
      simp [this]

end GlobalTheory.PD.CupAdj
