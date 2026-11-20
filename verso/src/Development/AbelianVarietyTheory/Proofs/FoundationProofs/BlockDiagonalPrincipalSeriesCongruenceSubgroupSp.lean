import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

noncomputable section
namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `u _ h`. Rewrite `h` using `[map_zero]`. Establish `h0 : valuation k ((u : k) - 1) = 0` using `le_antisymm h zero_le'`. Rewrite `h0` using `[(valuation k).zero_iff, sub_eq_zero]`. Establish `: u = 1` using `Units.ext h0`.

Rewrite using `[this, map_one]`.
-/
theorem triv_zero' (χ : kˣ →* ℂˣ) : Triv χ (0 : k) := by
  intro u _ h
  rw [map_zero] at h
  have h0 : valuation k ((u : k) - 1) = 0 := le_antisymm h zero_le'
  rw [(valuation k).zero_iff, sub_eq_zero] at h0
  have : u = 1 := Units.ext h0
  rw [this, map_one]

section Blocks

variable {r t : ℕ}

/- English proof (translation)
Use `ext`. Simplify using the standard rewrite rules.
-/
theorem castAdd_eq_stdSum (i : Fin r) : Fin.castAdd t i = stdSum (rfl : r + t = r + t) (Sum.inl i) := by
  ext; simp

/- English proof (translation)
Use `ext`. Simplify using the standard rewrite rules.
-/
theorem natAdd_eq_stdSum (j : Fin t) : Fin.natAdd r j = stdSum (rfl : r + t = r + t) (Sum.inr j) := by
  ext; simp

/- English proof (translation)
Rewrite using `[val_emb₂]`. Simplify using the standard rewrite rules.
-/
theorem emb₂_std_apply (a : GL (Fin r) k) (b : GL (Fin t) k) (x y : Fin r ⊕ Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (stdSum rfl x) (stdSum rfl y) =
      fromBlocks a.val 0 0 b.val x y := by
  rw [val_emb₂]; simp

/- English proof (translation)
Rewrite using `[← map_inv]`. Both sides reduce to the same expression.
-/
theorem emb₂_std_inv (a : GL (Fin r) k) (b : GL (Fin t) k) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))⁻¹ = emb₂ k (stdSum (rfl : r + t = r + t)) (a⁻¹, b⁻¹) := by
  rw [← map_inv]; rfl

/- English proof (translation)
Rewrite using `[GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff, emb₂_std_inv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨⟨fun i j => ?_, fun i j => ?_⟩, ⟨fun i j => ?_, fun i j => ?_⟩⟩` and prove the remaining obligations. Use `h1 (stdSum rfl (.inl i)) (stdSum rfl (.inl j))` as an intermediate fact.

Rewrite `this` using `[emb₂_std_apply, fromBlocks_apply₁₁]`. Then use the resulting hypothesis. Use `h2 (stdSum rfl (.inl i)) (stdSum rfl (.inl j))` as an intermediate fact. Rewrite `this` using `[emb₂_std_apply, fromBlocks_apply₁₁]`. Then use the resulting hypothesis. Use `h1 (stdSum rfl (.inr i)) (stdSum rfl (.inr j))` as an intermediate fact. Rewrite `this` using `[emb₂_std_apply, fromBlocks_apply₂₂]`. Then use the resulting hypothesis.

Use `h2 (stdSum rfl (.inr i)) (stdSum rfl (.inr j))` as an intermediate fact. Rewrite `this` using `[emb₂_std_apply, fromBlocks_apply₂₂]`. Then use the resulting hypothesis. Introduce and unpack `⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩`. Use `⟨fun p q => ?_, fun p q => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `(stdSum (rfl : r + t = r + t)).surjective p`.

Take `⟨y, rfl⟩` from `(stdSum (rfl : r + t = r + t)).surjective q`. Rewrite using `[emb₂_std_apply]`. Apply the tactic sequence `rcases x with x | x <;> rcases y with y | y`. Rewrite using `[fromBlocks_apply₁₁]`. Conclude with `a1 x y`.

Rewrite using `[fromBlocks_apply₁₂, Matrix.zero_apply]`. Conclude with `zero_mem _`. Rewrite using `[fromBlocks_apply₂₁, Matrix.zero_apply]`. Conclude with `zero_mem _`. Rewrite using `[fromBlocks_apply₂₂]`.

Conclude with `b1 x y`. Take `⟨x, rfl⟩` from `(stdSum (rfl : r + t = r + t)).surjective p`. Take `⟨y, rfl⟩` from `(stdSum (rfl : r + t = r + t)).surjective q`. Rewrite using `[emb₂_std_apply]`. Apply the tactic sequence `rcases x with x | x <;> rcases y with y | y`.

Rewrite using `[fromBlocks_apply₁₁]`. Conclude with `a2 x y`. Rewrite using `[fromBlocks_apply₁₂, Matrix.zero_apply]`. Conclude with `zero_mem _`. Rewrite using `[fromBlocks_apply₂₁, Matrix.zero_apply]`.

Conclude with `zero_mem _`. Rewrite using `[fromBlocks_apply₂₂]`. Conclude with `b2 x y`.
-/
theorem emb₂_mem_KO_iff (a : GL (Fin r) k) (b : GL (Fin t) k) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ KO k (Fin (r + t)) ↔
      a ∈ KO k (Fin r) ∧ b ∈ KO k (Fin t) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff, emb₂_std_inv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, ⟨fun i j => ?_, fun i j => ?_⟩⟩
    · have := h1 (stdSum rfl (.inl i)) (stdSum rfl (.inl j))
      rwa [emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h2 (stdSum rfl (.inl i)) (stdSum rfl (.inl j))
      rwa [emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h1 (stdSum rfl (.inr i)) (stdSum rfl (.inr j))
      rwa [emb₂_std_apply, fromBlocks_apply₂₂] at this
    · have := h2 (stdSum rfl (.inr i)) (stdSum rfl (.inr j))
      rwa [emb₂_std_apply, fromBlocks_apply₂₂] at this
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    refine ⟨fun p q => ?_, fun p q => ?_⟩
    · obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
      obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
      rw [emb₂_std_apply]
      rcases x with x | x <;> rcases y with y | y
      · rw [fromBlocks_apply₁₁]; exact a1 x y
      · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₂]; exact b1 x y
    · obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
      obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
      rw [emb₂_std_apply]
      rcases x with x | x <;> rcases y with y | y
      · rw [fromBlocks_apply₁₁]; exact a2 x y
      · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
      · rw [fromBlocks_apply₂₂]; exact b2 x y

/- English proof (translation)
Introduce `i a b j hia hab hbj x hx`. Conclude with `hψ (Fin.castAdd t i) (Fin.castAdd t a) (Fin.castAdd t b) (Fin.castAdd t j) (Fin.le_def.2 (Fin.le_def.1 hia)) (Fin.le_def.2 (Fin.le_def.1 hab)) (Fin.le_def.2 (Fin.le_def.1 hbj)) x hx`.
-/
theorem ordered_castAdd {ψ : Fin (r + t) → kˣ →* ℂˣ} (hψ : Ordered ψ) :
    Ordered (fun i : Fin r => ψ (Fin.castAdd t i)) := by
  intro i a b j hia hab hbj x hx
  exact hψ (Fin.castAdd t i) (Fin.castAdd t a) (Fin.castAdd t b) (Fin.castAdd t j)
    (Fin.le_def.2 (Fin.le_def.1 hia)) (Fin.le_def.2 (Fin.le_def.1 hab)) (Fin.le_def.2 (Fin.le_def.1 hbj)) x hx

/- English proof (translation)
Introduce `i a b j hia hab hbj x hx`. Conclude with `hψ (Fin.natAdd r i) (Fin.natAdd r a) (Fin.natAdd r b) (Fin.natAdd r j) ((Fin.natAdd_le_natAdd_iff r).2 hia) ((Fin.natAdd_le_natAdd_iff r).2 hab) ((Fin.natAdd_le_natAdd_iff r).2 hbj) x hx`.
-/
theorem ordered_natAdd {ψ : Fin (r + t) → kˣ →* ℂˣ} (hψ : Ordered ψ) :
    Ordered (fun i : Fin t => ψ (Fin.natAdd r i)) := by
  intro i a b j hia hab hbj x hx
  exact hψ (Fin.natAdd r i) (Fin.natAdd r a) (Fin.natAdd r b) (Fin.natAdd r j)
    ((Fin.natAdd_le_natAdd_iff r).2 hia) ((Fin.natAdd_le_natAdd_iff r).2 hab) ((Fin.natAdd_le_natAdd_iff r).2 hbj) x hx

/- English proof (translation)
Unfold `grp`. Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[emb₂_mem_KO_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨ha, hb⟩, h⟩`.

Use `⟨⟨ha, fun i j hij => ?_⟩, ⟨hb, fun i j hij => ?_⟩⟩` and prove the remaining obligations. Use `h (Fin.castAdd t i) (Fin.castAdd t j) (Fin.lt_def.2 (Fin.lt_def.1 hij))` as an intermediate fact. Rewrite `this` using `[castAdd_eq_stdSum i, castAdd_eq_stdSum j, emb₂_std_apply, fromBlocks_apply₁₁]`. Then use the resulting hypothesis. Use `h (Fin.natAdd r i) (Fin.natAdd r j) ((Fin.natAdd_lt_natAdd_iff r).2 hij)` as an intermediate fact. Rewrite `this` using `[natAdd_eq_stdSum i, natAdd_eq_stdSum j, emb₂_std_apply, fromBlocks_apply₂₂]`. Then use the resulting hypothesis.

Introduce and unpack `⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩`. Use `⟨⟨ha, hb⟩, fun p q hpq => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `(stdSum (rfl : r + t = r + t)).surjective p`. Take `⟨y, rfl⟩` from `(stdSum (rfl : r + t = r + t)).surjective q`. Rewrite using `[emb₂_std_apply]`.

Apply the tactic sequence `rcases x with x | x <;> rcases y with y | y`. Rewrite using `[fromBlocks_apply₁₁]`. Establish `hxy : x < y`. Rewrite `hpq` using `[← castAdd_eq_stdSum, ← castAdd_eq_stdSum]`. Conclude with `Fin.lt_def.2 (Fin.lt_def.1 hpq)`.

Use `ha' x y hxy` as an intermediate fact. Rewrite `this` using `[castAdd_eq_stdSum x, castAdd_eq_stdSum y]`. Then use the resulting hypothesis. Rewrite using `[fromBlocks_apply₁₂, Matrix.zero_apply]`. Conclude with `triv_zero' _`. It suffices to derive a contradiction.

Use `Fin.lt_def.1 hpq` as an intermediate fact. Rewrite `this` using `[stdSum_inr, stdSum_inl]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[fromBlocks_apply₂₂]`. Establish `hxy : x < y`.

Rewrite `hpq` using `[← natAdd_eq_stdSum, ← natAdd_eq_stdSum]`. Conclude with `(Fin.natAdd_lt_natAdd_iff r).1 hpq`. Use `hb' x y hxy` as an intermediate fact. Rewrite `this` using `[natAdd_eq_stdSum x, natAdd_eq_stdSum y]`. Then use the resulting hypothesis.
-/
theorem emb₂_mem_grp_iff (ψ : Fin (r + t) → kˣ →* ℂˣ) (a : GL (Fin r) k) (b : GL (Fin t) k) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ grp ψ ↔
      a ∈ grp (fun i => ψ (Fin.castAdd t i)) ∧ b ∈ grp (fun i => ψ (Fin.natAdd r i)) := by
  unfold grp
  simp only [Set.mem_setOf_eq]
  rw [emb₂_mem_KO_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    refine ⟨⟨ha, fun i j hij => ?_⟩, ⟨hb, fun i j hij => ?_⟩⟩
    · have := h (Fin.castAdd t i) (Fin.castAdd t j) (Fin.lt_def.2 (Fin.lt_def.1 hij))
      rwa [castAdd_eq_stdSum i, castAdd_eq_stdSum j, emb₂_std_apply, fromBlocks_apply₁₁] at this
    · have := h (Fin.natAdd r i) (Fin.natAdd r j) ((Fin.natAdd_lt_natAdd_iff r).2 hij)
      rwa [natAdd_eq_stdSum i, natAdd_eq_stdSum j, emb₂_std_apply, fromBlocks_apply₂₂] at this
  · rintro ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩
    refine ⟨⟨ha, hb⟩, fun p q hpq => ?_⟩
    obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective p
    obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective q
    rw [emb₂_std_apply]
    rcases x with x | x <;> rcases y with y | y
    · rw [fromBlocks_apply₁₁]
      have hxy : x < y := by
        rw [← castAdd_eq_stdSum, ← castAdd_eq_stdSum] at hpq
        exact Fin.lt_def.2 (Fin.lt_def.1 hpq)
      have := ha' x y hxy
      rwa [castAdd_eq_stdSum x, castAdd_eq_stdSum y] at this
    · rw [fromBlocks_apply₁₂, Matrix.zero_apply]; exact triv_zero' _
    · exfalso
      have := Fin.lt_def.1 hpq
      rw [stdSum_inr, stdSum_inl] at this
      omega
    · rw [fromBlocks_apply₂₂]
      have hxy : x < y := by
        rw [← natAdd_eq_stdSum, ← natAdd_eq_stdSum] at hpq
        exact (Fin.natAdd_lt_natAdd_iff r).1 hpq
      have := hb' x y hxy
      rwa [natAdd_eq_stdSum x, natAdd_eq_stdSum y] at this

end Blocks

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ ψ hψ _` and use `⟨ordered_castAdd hψ, ordered_natAdd hψ, emb₂_mem_grp_iff ψ⟩`.
-/
theorem block_diag_mem_grp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → Cut ψ r → Ordered (fun i => ψ (Fin.castAdd t i)) ∧ Ordered (fun i => ψ (Fin.natAdd r i)) ∧ ∀ (a : GL (Fin r) k) (b : GL (Fin t) k), emb₂ k (stdSum (rfl : r + t = r + t)) (a, b) ∈ grp ψ ↔ a ∈ grp (fun i => ψ (Fin.castAdd t i)) ∧ b ∈ grp (fun i => ψ (Fin.natAdd r i)) :=
  fun _ _ _ _ _ _ _ ψ hψ _ => ⟨ordered_castAdd hψ, ordered_natAdd hψ, emb₂_mem_grp_iff ψ⟩

end GlobalTheory.PsType
