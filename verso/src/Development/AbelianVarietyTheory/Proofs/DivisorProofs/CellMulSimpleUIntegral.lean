import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylRepInvMulDiag
open GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.GKFactor.UnitaryInt

open GlobalTheory.GKFactor

variable {L : Type} [Field L] {n : ℕ}

local notation "M" x:max => ((x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

/- English proof (translation)
Establish `hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype` using `Matrix.map_injective Subtype.val_injective`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩` and prove the remaining obligations. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `g.mul_inv`. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `g.inv_mul`.
-/
theorem mem_GLint_iff_entries (O : Subring L) (g : GL (Fin n) L) :
    g ∈ GLint (Fin n) O ↔ (∀ i j, (M g) i j ∈ O) ∧ ∀ i j, (M g⁻¹) i j ∈ O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

/- English proof (translation)
Rewrite `hg` using `[mem_unipB]`. Establish `hdet : (M g).det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => hg.1 i j hij)]`. Simplify using `[hg.2]`. Use `(mem_GLint_iff_entries O g).2 ⟨h, ?_⟩` and prove the remaining obligations.

Use `set A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h i j⟩`. Establish `hA : (M g) = O.subtype.mapMatrix A` using `by ext i j; rfl`. Establish `hinv : (M g⁻¹) = (M g).adjugate`. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]`. Introduce `i j`.

Rewrite using `[hinv, hA, ← RingHom.map_adjugate]`. Conclude with `(A.adjugate i j).2`.
-/
theorem unip_mem_GLint (O : Subring L) (g : GL (Fin n) L) (hg : g ∈ unipB L (Fin n))
    (h : ∀ i j, (M g) i j ∈ O) : g ∈ GLint (Fin n) O := by
  rw [mem_unipB] at hg
  have hdet : (M g).det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hg.1 i j hij)]
    simp [hg.2]
  refine (mem_GLint_iff_entries O g).2 ⟨h, ?_⟩
  set A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h i j⟩
  have hA : (M g) = O.subtype.mapMatrix A := by ext i j; rfl
  have hinv : (M g⁻¹) = (M g).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  intro i j
  rw [hinv, hA, ← RingHom.map_adjugate]
  exact (A.adjugate i j).2

/- English proof (translation)
Use `set v := x' * u₂ * x'⁻¹ with hv`. Take `⟨hu₁B, hu₁c⟩` from `(mem_cell_iff hx u₁).1 hu₁`. Take `⟨hu₂B, hu₂c⟩` from `(mem_cell_iff hy u₂).1 hu₂`. Rewrite `hu₁B`, `hu₂B` using `[mem_unipB]`. Establish `hvE : ∀ P Q, (M v) P Q = (M x') P (w'⁻¹ P) * (M u₂) (w'⁻¹ P) (w'⁻¹ Q) * (M x'⁻¹) (w'⁻¹ Q) Q`.

Introduce `P Q`. Establish `h` using `weylRep_conj_apply (weylRep_inv hx) u₂ P Q`. Rewrite `h` using `[inv_inv]`. Conclude with `h`. Establish `hsupp : ∀ P Q, P ≠ Q → (M v) P Q ≠ 0 → w'⁻¹ P < w'⁻¹ Q ∧ s⁻¹ (w'⁻¹ Q) < s⁻¹ (w'⁻¹ P)`.

Introduce `P Q hPQ hne`. Establish `hu : (M u₂) (w'⁻¹ P) (w'⁻¹ Q) ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hvE, h0, mul_zero, zero_mul]`.

Establish `hab : w'⁻¹ P ≠ w'⁻¹ Q` using `fun e => hPQ (w'⁻¹.injective e)`. Establish `hlt : w'⁻¹ P < w'⁻¹ Q`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (hu₂B.1 _ _ h) hu`.

Use `⟨hlt, ?_⟩` and prove the remaining obligations. Break down `lt_or_gt_of_ne (fun e : s⁻¹ (w'⁻¹ P) = s⁻¹ (w'⁻¹ Q) => hab (s⁻¹.injective e)) with h | h` into its components or cases. Conclude with `absurd (hu₂c _ _ hlt h) hu`. Conclude with `h`. Establish `hdiag : ∀ P, (M v) P P = 1`.

Introduce `P`. Rewrite using `[hvE, hu₂B.2, mul_one]`. Use `weylRep_mul_inv_diag hx (w'⁻¹ P)` as an intermediate fact. Simplify using `using this`. Establish `hvB : v ∈ unipB L (Fin n)`.

Rewrite using `[mem_unipB]`. Use `⟨fun P Q hQP => ?_, hdiag⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨h1, h2⟩` from `hsupp P Q hQP.ne' hne`. Use `H1 _ _ h1 h2` as an intermediate fact.

Simplify using `at this`. Conclude with `lt_asymm this hQP`. Take `⟨hgE, -⟩` from `(mem_GLint_iff_entries O _).1 hg`. Establish `hgv : ∀ P Q, P ≠ Q → (M v) P Q ≠ 0 → (M (v * u₁)) P Q = (M v) P Q`. Introduce `P Q hPQ hne`.

Take `⟨hab, hs⟩` from `hsupp P Q hPQ hne`. Establish `hPQlt : P < Q` using `by simpa using H1 _ _ hab hs`. Rewrite using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single Q, hu₁B.2, mul_one]`. Introduce `l _ hlQ`. Distinguish the cases in `hlP : l = P`.

Rewrite using `[hlP, hu₁c _ _ hPQlt hab, mul_zero]`. Distinguish the cases in `h1 : (M v) P l = 0`. Rewrite using `[h1, zero_mul]`. Distinguish the cases in `h2 : (M u₁) l Q = 0`. Rewrite using `[h2, mul_zero]`.

It suffices to derive a contradiction. Take `⟨hac, hsc⟩` from `hsupp P l (Ne.symm hlP) h1`. Establish `hlQlt : l < Q`. Break down `lt_or_gt_of_ne hlQ with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd (hu₁B.1 _ _ h) h2`. Establish `hbc : w'⁻¹ Q < w'⁻¹ l`. Break down `lt_or_gt_of_ne (fun e : w'⁻¹ l = w'⁻¹ Q => hlQ (w'⁻¹.injective e)) with h | h` into its components or cases. Conclude with `absurd (hu₁c _ _ hlQlt h) h2`. Conclude with `h`.

Use `H2 _ _ _ hab hs hac hsc hbc` as an intermediate fact. Simplify using `at this`. Conclude with `lt_asymm this hlQlt`. Simplify using the standard rewrite rules. Establish `hvO : ∀ P Q, (M v) P Q ∈ O`.

Introduce `P Q`. Distinguish the cases in `hPQ : P = Q`. Rewrite using `[hPQ, hdiag]`. Conclude with `O.one_mem`. Distinguish the cases in `hne : (M v) P Q = 0`.

Rewrite using `[hne]`. Conclude with `O.zero_mem`. Rewrite using `[← hgv P Q hPQ hne]`. Conclude with `hgE P Q`. Establish `hvK : v ∈ GLint (Fin n) O` using `unip_mem_GLint O v hvB hvO`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : u₁ = v⁻¹ * (v * u₁)` using `by group`. Rewrite using `[e]`. Conclude with `mul_mem (inv_mem hvK) hg`. Establish `e : u₂ = x'⁻¹ * v * x'` using `by rw [hv]; group`.

Rewrite using `[e]`. Conclude with `mul_mem (mul_mem (inv_mem hxO) hvK) hxO`.
-/
theorem cell_conj_mul_integral (O : Subring L) {w' s : Equiv.Perm (Fin n)} {x' y : GL (Fin n) L}
    (hxO : x' ∈ GLint (Fin n) O) (hx : IsWeylRep w' x') (hy : IsWeylRep s y)
    (H1 : ∀ a b, a < b → s⁻¹ b < s⁻¹ a → w' a < w' b)
    (H2 : ∀ a b c, a < b → s⁻¹ b < s⁻¹ a → a < c → s⁻¹ c < s⁻¹ a → b < c → w' b < w' c)
    {u₁ u₂ : GL (Fin n) L} (hu₁ : u₁ ∈ cell x') (hu₂ : u₂ ∈ cell y)
    (hg : x' * u₂ * x'⁻¹ * u₁ ∈ GLint (Fin n) O) : u₁ ∈ GLint (Fin n) O ∧ u₂ ∈ GLint (Fin n) O := by
  set v := x' * u₂ * x'⁻¹ with hv
  obtain ⟨hu₁B, hu₁c⟩ := (mem_cell_iff hx u₁).1 hu₁
  obtain ⟨hu₂B, hu₂c⟩ := (mem_cell_iff hy u₂).1 hu₂
  rw [mem_unipB] at hu₁B hu₂B
  have hvE : ∀ P Q, (M v) P Q = (M x') P (w'⁻¹ P) * (M u₂) (w'⁻¹ P) (w'⁻¹ Q) * (M x'⁻¹) (w'⁻¹ Q) Q := by
    intro P Q
    have h := weylRep_conj_apply (weylRep_inv hx) u₂ P Q
    rw [inv_inv] at h
    exact h
  have hsupp : ∀ P Q, P ≠ Q → (M v) P Q ≠ 0 → w'⁻¹ P < w'⁻¹ Q ∧ s⁻¹ (w'⁻¹ Q) < s⁻¹ (w'⁻¹ P) := by
    intro P Q hPQ hne
    have hu : (M u₂) (w'⁻¹ P) (w'⁻¹ Q) ≠ 0 := by
      intro h0; apply hne; rw [hvE, h0, mul_zero, zero_mul]
    have hab : w'⁻¹ P ≠ w'⁻¹ Q := fun e => hPQ (w'⁻¹.injective e)
    have hlt : w'⁻¹ P < w'⁻¹ Q := by
      rcases lt_or_gt_of_ne hab with h | h
      · exact h
      · exact absurd (hu₂B.1 _ _ h) hu
    refine ⟨hlt, ?_⟩
    rcases lt_or_gt_of_ne (fun e : s⁻¹ (w'⁻¹ P) = s⁻¹ (w'⁻¹ Q) => hab (s⁻¹.injective e)) with h | h
    · exact absurd (hu₂c _ _ hlt h) hu
    · exact h
  have hdiag : ∀ P, (M v) P P = 1 := by
    intro P
    rw [hvE, hu₂B.2, mul_one]
    have := weylRep_mul_inv_diag hx (w'⁻¹ P)
    simpa using this
  have hvB : v ∈ unipB L (Fin n) := by
    rw [mem_unipB]
    refine ⟨fun P Q hQP => ?_, hdiag⟩
    by_contra hne
    obtain ⟨h1, h2⟩ := hsupp P Q hQP.ne' hne
    have := H1 _ _ h1 h2
    simp at this
    exact lt_asymm this hQP
  obtain ⟨hgE, -⟩ := (mem_GLint_iff_entries O _).1 hg
  have hgv : ∀ P Q, P ≠ Q → (M v) P Q ≠ 0 → (M (v * u₁)) P Q = (M v) P Q := by
    intro P Q hPQ hne
    obtain ⟨hab, hs⟩ := hsupp P Q hPQ hne
    have hPQlt : P < Q := by simpa using H1 _ _ hab hs
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single Q, hu₁B.2, mul_one]
    · intro l _ hlQ
      by_cases hlP : l = P
      · rw [hlP, hu₁c _ _ hPQlt hab, mul_zero]
      by_cases h1 : (M v) P l = 0
      · rw [h1, zero_mul]
      by_cases h2 : (M u₁) l Q = 0
      · rw [h2, mul_zero]
      exfalso
      obtain ⟨hac, hsc⟩ := hsupp P l (Ne.symm hlP) h1
      have hlQlt : l < Q := by
        rcases lt_or_gt_of_ne hlQ with h | h
        · exact h
        · exact absurd (hu₁B.1 _ _ h) h2
      have hbc : w'⁻¹ Q < w'⁻¹ l := by
        rcases lt_or_gt_of_ne (fun e : w'⁻¹ l = w'⁻¹ Q => hlQ (w'⁻¹.injective e)) with h | h
        · exact absurd (hu₁c _ _ hlQlt h) h2
        · exact h
      have := H2 _ _ _ hab hs hac hsc hbc
      simp at this
      exact lt_asymm this hlQlt
    · simp
  have hvO : ∀ P Q, (M v) P Q ∈ O := by
    intro P Q
    by_cases hPQ : P = Q
    · rw [hPQ, hdiag]; exact O.one_mem
    by_cases hne : (M v) P Q = 0
    · rw [hne]; exact O.zero_mem
    rw [← hgv P Q hPQ hne]; exact hgE P Q
  have hvK : v ∈ GLint (Fin n) O := unip_mem_GLint O v hvB hvO
  refine ⟨?_, ?_⟩
  · have e : u₁ = v⁻¹ * (v * u₁) := by group
    rw [e]; exact mul_mem (inv_mem hvK) hg
  · have e : u₂ = x'⁻¹ * v * x' := by rw [hv]; group
    rw [e]; exact mul_mem (mul_mem (inv_mem hxO) hvK) hxO

section Comb

variable {n : ℕ}

/- English proof (translation)
Unfold `simpleU partnerU at h`. Simplify using `only [hk, if_true, dif_pos, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at h`. Rewrite `hab` using `[Fin.lt_def]`. Apply the tactic sequence `split_ifs at h <;> simp only [Fin.lt_def, Fin.ext_iff, Fin.val_rev, Fin.coe_castLE] at * <;> omega`.
-/
theorem simpleU_pair_inversion (k : Fin (n / 2)) (hk : k.val + 1 < n / 2) (a b : Fin n) (hab : a < b)
    (h : (simpleU k)⁻¹ b < (simpleU k)⁻¹ a) :
    (a.val = k.val ∧ b.val = k.val + 1) ∨ (a.val = n - 2 - k.val ∧ b.val = n - 1 - k.val) := by
  unfold simpleU partnerU at h
  simp only [hk, if_true, dif_pos, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at h
  rw [Fin.lt_def] at hab
  split_ifs at h <;> simp only [Fin.lt_def, Fin.ext_iff, Fin.val_rev, Fin.coe_castLE] at * <;> omega

/- English proof (translation)
Establish `hk'` using `k.isLt`. Unfold `simpleU at h`. Simplify using `only [hk, if_false, Equiv.swap_inv, Equiv.swap_apply_def] at h`. Rewrite `hab` using `[Fin.lt_def]`. Apply the tactic sequence `split_ifs at h <;> simp only [Fin.lt_def, Fin.ext_iff, Fin.val_rev, Fin.coe_castLE] at * <;> omega`.
-/
theorem simpleU_last_inversion (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (a b : Fin n) (hab : a < b)
    (h : (simpleU k)⁻¹ b < (simpleU k)⁻¹ a) :
    (a.val = k.val ∧ b.val = n - 1 - k.val) ∨ (a.val = k.val ∧ 2 * b.val + 1 = n) ∨
      (2 * a.val + 1 = n ∧ b.val = n - 1 - k.val) := by
  have hk' := k.isLt
  unfold simpleU at h
  simp only [hk, if_false, Equiv.swap_inv, Equiv.swap_apply_def] at h
  rw [Fin.lt_def] at hab
  split_ifs at h <;> simp only [Fin.lt_def, Fin.ext_iff, Fin.val_rev, Fin.coe_castLE] at * <;> omega

end Comb

section Hyps

variable {n : ℕ}

/- English proof (translation)
Establish `hkl` using `k.isLt`. Establish `hval : ∀ i : Fin n, (w' i.rev).val = n - 1 - (w' i).val` using `fun i => by`. Rewrite using `[hw, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hk : k.val + 1 < n / 2`.

Establish `hP : partnerU k = lo (⟨k.val + 1, hk⟩ : Fin (n / 2))` using `by unfold partnerU; rw [dif_pos hk]`. Establish `hPv : (partnerU k).val = k.val + 1` using `by rw [hP]; rfl`. Use `⟨fun a b hab h => ?_, fun a b c hab h hac h' hbc => ?_⟩` and prove the remaining obligations. Break down `simpleU_pair_inversion k hk a b hab h with ⟨ha, hb⟩ | ⟨ha, hb⟩` into its components or cases. Rewrite using `[show a = lo k from Fin.ext (by simp [ha]), show b = partnerU k from Fin.ext (by rw [hPv]; omega)]`.

Conclude with `hlt`. Rewrite using `[show a = (partnerU k).rev from Fin.ext (by rw [Fin.val_rev, hPv]; omega), show b = (lo k).rev from Fin.ext (by rw [Fin.val_rev]; simp; omega), hw, hw]`. Conclude with `Fin.rev_lt_rev.2 hlt`. It suffices to derive a contradiction. Establish `h1` using `simpleU_pair_inversion k hk a b hab h`.

Establish `h2` using `simpleU_pair_inversion k hk a c hac h'`. Rewrite `hbc` using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Establish `hP : partnerU k = (lo k).rev` using `by unfold partnerU; rw [dif_neg hk]`. Rewrite `hlt` using `[hP, hw, Fin.lt_def, Fin.val_rev]`.

Establish `hA : ∀ a : Fin n, a.val = k.val → (w' a).val = (w' (lo k)).val` using `fun a ha => by`. Rewrite using `[show a = lo k from Fin.ext (by simp [ha])]`. Establish `hB : ∀ b : Fin n, b.val = n - 1 - k.val → (w' b).val = n - 1 - (w' (lo k)).val` using `fun b hb => by`. Rewrite using `[show b = (lo k).rev from Fin.ext (by rw [Fin.val_rev]; simp; omega), hval]`. Establish `hC : ∀ b : Fin n, 2 * b.val + 1 = n → 2 * (w' b).val + 1 = n` using `fun b hb => by`.

Establish `e : b.rev = b` using `Fin.ext (by rw [Fin.val_rev]; omega)`. Use `hval b` as an intermediate fact. Rewrite `this` using `[e]`. Use `(w' b).isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `⟨fun a b hab h => ?_, fun a b c hab h hac h' hbc => ?_⟩` and prove the remaining obligations. Rewrite `hab`, the goal using `[Fin.lt_def]`. Break down `simpleU_last_inversion k hk a b hab h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩` into its components or cases. Use `hA a ha` as an intermediate fact. Use `hB b hb` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `hA a ha` as an intermediate fact. Use `hC b hb` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `hC a ha` as an intermediate fact.

Use `hB b hb` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h1` using `simpleU_last_inversion k hk a b hab h`. Establish `h2` using `simpleU_last_inversion k hk a c hac h'`. Rewrite `hab`, `hac`, `hbc`, the goal using `[Fin.lt_def]`.

Apply the tactic sequence `rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>`. Apply the tactic sequence `rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;>`. Use `first`. Consider the case `omega`. Consider the case `(have := hC b h1b; have := hB c h2b; omega)`.
-/
theorem simpleU_hyps (k : Fin (n / 2)) (w' : Equiv.Perm (Fin n)) (hw : ∀ i : Fin n, w' i.rev = (w' i).rev)
    (hlt : w' (lo k) < w' (partnerU k)) :
    (∀ a b, a < b → (simpleU k)⁻¹ b < (simpleU k)⁻¹ a → w' a < w' b) ∧
    (∀ a b c, a < b → (simpleU k)⁻¹ b < (simpleU k)⁻¹ a → a < c → (simpleU k)⁻¹ c < (simpleU k)⁻¹ a → b < c →
      w' b < w' c) := by
  have hkl := k.isLt
  have hval : ∀ i : Fin n, (w' i.rev).val = n - 1 - (w' i).val := fun i => by
    rw [hw, Fin.val_rev]; omega
  by_cases hk : k.val + 1 < n / 2
  · have hP : partnerU k = lo (⟨k.val + 1, hk⟩ : Fin (n / 2)) := by unfold partnerU; rw [dif_pos hk]
    have hPv : (partnerU k).val = k.val + 1 := by rw [hP]; rfl
    refine ⟨fun a b hab h => ?_, fun a b c hab h hac h' hbc => ?_⟩
    · rcases simpleU_pair_inversion k hk a b hab h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [show a = lo k from Fin.ext (by simp [ha]), show b = partnerU k from Fin.ext (by rw [hPv]; omega)]
        exact hlt
      · rw [show a = (partnerU k).rev from Fin.ext (by rw [Fin.val_rev, hPv]; omega),
          show b = (lo k).rev from Fin.ext (by rw [Fin.val_rev]; simp; omega), hw, hw]
        exact Fin.rev_lt_rev.2 hlt
    · exfalso
      have h1 := simpleU_pair_inversion k hk a b hab h
      have h2 := simpleU_pair_inversion k hk a c hac h'
      rw [Fin.lt_def] at hbc
      omega
  · have hP : partnerU k = (lo k).rev := by unfold partnerU; rw [dif_neg hk]
    rw [hP, hw, Fin.lt_def, Fin.val_rev] at hlt
    have hA : ∀ a : Fin n, a.val = k.val → (w' a).val = (w' (lo k)).val := fun a ha => by
      rw [show a = lo k from Fin.ext (by simp [ha])]
    have hB : ∀ b : Fin n, b.val = n - 1 - k.val → (w' b).val = n - 1 - (w' (lo k)).val := fun b hb => by
      rw [show b = (lo k).rev from Fin.ext (by rw [Fin.val_rev]; simp; omega), hval]
    have hC : ∀ b : Fin n, 2 * b.val + 1 = n → 2 * (w' b).val + 1 = n := fun b hb => by
      have e : b.rev = b := Fin.ext (by rw [Fin.val_rev]; omega)
      have := hval b
      rw [e] at this
      have := (w' b).isLt
      omega
    refine ⟨fun a b hab h => ?_, fun a b c hab h hac h' hbc => ?_⟩
    · rw [Fin.lt_def] at hab ⊢
      rcases simpleU_last_inversion k hk a b hab h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have := hA a ha; have := hB b hb; omega
      · have := hA a ha; have := hC b hb; omega
      · have := hC a ha; have := hB b hb; omega
    · have h1 := simpleU_last_inversion k hk a b hab h
      have h2 := simpleU_last_inversion k hk a c hac h'
      rw [Fin.lt_def] at hab hac hbc ⊢
      rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
        rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;>
        first
        | omega
        | (have := hC b h1b; have := hB c h2b; omega)

end Hyps

/- English proof (translation)
Introduce `L _ _ n w' k hw hlt x' y hxO hx hy u₁ hu₁ u₂ hu₂ hg`. Take `⟨H1, H2⟩` from `simpleU_hyps k w' hw hlt`. Conclude with `cell_conj_mul_integral (intL L) hxO hx hy H1 H2 hu₁ hu₂ hg`.
-/
theorem cell_mul_simpleU_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ)
    (w' : Equiv.Perm (Fin n)) (k : Fin (n / 2)),
    (∀ i : Fin n, w' i.rev = (w' i).rev) → w' (lo k) < w' (partnerU k) → ∀ (x' y : GL (Fin n) L),
    x' ∈ GLint (Fin n) (intL L) → IsWeylRep w' x' → IsWeylRep (simpleU k) y →
    ∀ u₁ ∈ cell x', ∀ u₂ ∈ cell y, x' * u₂ * x'⁻¹ * u₁ ∈ GLint (Fin n) (intL L) →
      u₁ ∈ GLint (Fin n) (intL L) ∧ u₂ ∈ GLint (Fin n) (intL L) := by
  intro L _ _ n w' k hw hlt x' y hxO hx hy u₁ hu₁ u₂ hu₂ hg
  obtain ⟨H1, H2⟩ := simpleU_hyps k w' hw hlt
  exact cell_conj_mul_integral (intL L) hxO hx hy H1 H2 hu₁ hu₂ hg

end GlobalTheory.GKFactor.UnitaryInt
