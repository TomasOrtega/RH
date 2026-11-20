import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `g v _`. Conclude with `Submodule.mem_top`.
-/
private theorem inv_top {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) :
    IsInv ρ (⊤ : Submodule k (Fin d → k)) := by
  intro g v _
  exact Submodule.mem_top

/- English proof (translation)
Introduce `g v hv`. Rewrite `hv`, the goal using `[Submodule.mem_bot]`. Substitute `hv` using the available equality. Conclude with `Matrix.mulVec_zero _`.
-/
private theorem inv_bot {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) :
    IsInv ρ (⊥ : Submodule k (Fin d → k)) := by
  intro g v hv
  rw [Submodule.mem_bot] at hv ⊢
  subst hv
  exact Matrix.mulVec_zero _

/- English proof (translation)
Distinguish the cases in `h : W = ⊤`. Substitute `h` using the available equality. Conclude with `⟨⊤, hW, le_rfl, fun h => (h rfl).elim, fun U _ h1 h2 => Or.inl (le_antisymm h2 h1)⟩`. Establish `hne : {U : Submodule k (Fin d → k) | IsInv ρ U ∧ W < U}.Nonempty` using `⟨⊤, inv_top ρ, lt_top_iff_ne_top.2 h⟩`. Take `⟨M, ⟨hMi, hMl⟩, hmin⟩` from `(wellFounded_lt (α := Submodule k (Fin d → k))).has_min _ hne`.

Use `⟨M, hMi, hMl.le, fun _ => hMl, fun U hU h1 h2 => ?_⟩` and prove the remaining obligations. Break down `eq_or_lt_of_le h1 with e | l` into its components or cases. Conclude with `Or.inl e.symm`. Break down `eq_or_lt_of_le h2 with e | l2` into its components or cases. Conclude with `Or.inr e`.

Conclude with `(hmin U ⟨hU, l⟩ l2).elim`.
-/
private theorem flag_step {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k)
    (W : Submodule k (Fin d → k)) (hW : IsInv ρ W) :
    ∃ W' : Submodule k (Fin d → k), IsInv ρ W' ∧ W ≤ W' ∧ (W ≠ ⊤ → W < W') ∧
      ∀ U, IsInv ρ U → W ≤ U → U ≤ W' → U = W ∨ U = W' := by
  by_cases h : W = ⊤
  · subst h
    exact ⟨⊤, hW, le_rfl, fun h => (h rfl).elim, fun U _ h1 h2 => Or.inl (le_antisymm h2 h1)⟩
  · have hne : {U : Submodule k (Fin d → k) | IsInv ρ U ∧ W < U}.Nonempty :=
      ⟨⊤, inv_top ρ, lt_top_iff_ne_top.2 h⟩
    obtain ⟨M, ⟨hMi, hMl⟩, hmin⟩ :=
      (wellFounded_lt (α := Submodule k (Fin d → k))).has_min _ hne
    refine ⟨M, hMi, hMl.le, fun _ => hMl, fun U hU h1 h2 => ?_⟩
    rcases eq_or_lt_of_le h1 with e | l
    · exact Or.inl e.symm
    · rcases eq_or_lt_of_le h2 with e | l2
      · exact Or.inr e
      · exact (hmin U ⟨hU, l⟩ l2).elim

/- English proof (translation)
Introduce `Γ k _ _ d ρ`. Use `choose f hf using (fun (W : {W : Submodule k (Fin d → k) // IsInv ρ W}) => flag_step ρ W.1 W.2)`. Set `S : ℕ → {W : Submodule k (Fin d → k) // IsInv ρ W}` to `fun i => Nat.rec ⟨⊥, inv_bot ρ⟩ (fun _ w => ⟨f w, (hf w).1⟩) i`. Establish `key : ∀ i, (S i).1 = ⊤ ∨ i ≤ Module.finrank k (S i).1`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => exact Or.inr (Nat.zero_le _)`. Consider the case `succ n ih`. Distinguish the cases in `ht : (S n).1 = ⊤`. Use `left`.

Establish `h1 : (S n).1 ≤ (S (n + 1)).1` using `(hf (S n)).2.1`. Rewrite `h1` using `[ht]`. Conclude with `top_le_iff.1 h1`. Use `right`. Establish `hlt : (S n).1 < (S (n + 1)).1` using `(hf (S n)).2.2.1 ht`.

Establish `h2` using `Submodule.finrank_lt_finrank_of_lt hlt`. Break down `ih with h | h` into its components or cases. Conclude with `absurd h ht`. Use linear arithmetic over natural numbers and integers. Use `⟨fun i => (S i).1, monotone_nat_of_le_succ fun i => (hf (S i)).2.1, rfl, ?_, fun i => (S i).2, fun i U hU h1 h2 => (hf (S i)).2.2.2 U hU h1 h2⟩` and prove the remaining obligations.

Break down `key d with h | h` into its components or cases. Conclude with `h`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Establish `h3` using `Submodule.finrank_le (S d).1`. Simplify using `only [Module.finrank_fin_fun] at h3 ⊢`.

Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.Gal.Int.Geo.flagEx_of :
    FlagEx := by
  intro Γ k _ _ d ρ
  choose f hf using
    (fun (W : {W : Submodule k (Fin d → k) // IsInv ρ W}) => flag_step ρ W.1 W.2)
  let S : ℕ → {W : Submodule k (Fin d → k) // IsInv ρ W} :=
    fun i => Nat.rec ⟨⊥, inv_bot ρ⟩ (fun _ w => ⟨f w, (hf w).1⟩) i
  have key : ∀ i, (S i).1 = ⊤ ∨ i ≤ Module.finrank k (S i).1 := by
    intro i
    induction i with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ n ih =>
      by_cases ht : (S n).1 = ⊤
      · left
        have h1 : (S n).1 ≤ (S (n + 1)).1 := (hf (S n)).2.1
        rw [ht] at h1
        exact top_le_iff.1 h1
      · right
        have hlt : (S n).1 < (S (n + 1)).1 := (hf (S n)).2.2.1 ht
        have h2 := Submodule.finrank_lt_finrank_of_lt hlt
        rcases ih with h | h
        · exact absurd h ht
        · omega
  refine ⟨fun i => (S i).1, monotone_nat_of_le_succ fun i => (hf (S i)).2.1, rfl, ?_,
    fun i => (S i).2, fun i U hU h1 h2 => (hf (S i)).2.2.2 U hU h1 h2⟩
  rcases key d with h | h
  · exact h
  · apply Submodule.eq_top_of_finrank_eq
    have h3 := Submodule.finrank_le (S d).1
    simp only [Module.finrank_fin_fun] at h3 ⊢
    omega
