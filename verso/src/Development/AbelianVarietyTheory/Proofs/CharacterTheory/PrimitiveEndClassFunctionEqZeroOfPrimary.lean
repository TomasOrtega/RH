import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ConjOfPrimaryFinrankKerPowEqStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.KerAevalAddStabilizerNilradicalSocleStatement

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

/- English proof (translation)
Introduce `F _ _ V _ _ _ φ hcl hpr f m hf h0`. Use `haveI : Finite V := Module.finite_of_finite F`. Use `haveI : Finite (Module.End F V) := Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective`. Establish `key : ∀ n : ℕ, ∀ g : Module.End F V, Module.finrank F V - Module.finrank F (LinearMap.ker (aeval g f)) = n → LinearMap.charpoly g = f ^ m → φ g = 0`. Introduce `n`.

Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `g hn hg`. Distinguish the cases in `htop : LinearMap.ker (aeval g f) = ⊤`. Conclude with `h0 g hg (LinearMap.ker_eq_top.mp htop)`.

Establish `hCH : ∀ g' : Module.End F V, LinearMap.charpoly g' = f ^ m → aeval g' (f ^ m) = 0`. Introduce `g' hg'`. Rewrite using `[← hg']`. Conclude with `LinearMap.aeval_self_charpoly g'`. Establish `hbot : LinearMap.ker (aeval g f) ≠ ⊥`.

Introduce `hb`. Establish `hinj : Function.Injective (aeval g f : Module.End F V)` using `LinearMap.ker_eq_bot.mp hb`. Establish `hinj' : Function.Injective ((aeval g f) ^ m : Module.End F V)`. Rewrite using `[Module.End.coe_pow]`. Conclude with `hinj.iterate m`.

Rewrite `hinj'` using `[← map_pow, hCH g hg]`. Apply `htop` to reduce the goal to its premises. Rewrite using `[hb, eq_comm, eq_bot_iff]`. Introduce `x _`. Conclude with `(Submodule.mem_bot F).mpr (hinj' (by simp))`.

Establish `hinv : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f)`. Introduce `x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Establish `hc : aeval g f * g = g * aeval g f`. Establish `: aeval g (f * X) = aeval g (X * f)` using `by rw [mul_comm]`.

Simplify using `using this`. Use `congrArg (fun k : Module.End F V => k x) hc` as an intermediate fact. Simplify `this` using `[hx]`. Establish `hsum` using `hpr _ hbot htop g hinv`. Establish `hfin : (nilRad (LinearMap.ker (aeval g f))).Finite` using `Set.toFinite _`.

Rewrite `hsum` using `[finsum_mem_eq_finite_toFinset_sum _ hfin]`. Establish `hterm : ∀ h ∈ hfin.toFinset, φ (g + h) = if LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) then φ g else 0`. Introduce `h hh`. Rewrite `hh` using `[Set.Finite.mem_toFinset]`. Establish `hcp : LinearMap.charpoly (g + h) = f ^ m`.

Rewrite using `[(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V _ g hinv).2 h hh, hg]`. Take `⟨hle, heq⟩` from `GlobalTheory.T.ker_aeval_add_stabilizerNilradical_socle F V g h f hh`. Use `split_ifs with hc`. Take `⟨e, he⟩` from `GlobalTheory.T.conj_of_primary_finrank_ker_pow_eq F V g (g + h) f m hf (hCH g hg) (hCH _ hcp) (heq hc)`. Rewrite using `[← he, hcl e g]`.

Establish `hlt : LinearMap.ker (aeval g f) < LinearMap.ker (aeval (g + h) f)` using `lt_of_le_of_ne hle (Ne.symm hc)`. Establish `h1` using `Submodule.finrank_lt_finrank_of_lt hlt`. Establish `h2` using `Submodule.finrank_le (LinearMap.ker (aeval (g + h) f))`. Conclude with `ih _ (by omega) (g + h) rfl hcp`. Rewrite `hsum` using `[Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`.

Use `(mul_eq_zero.mp hsum).resolve_left ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_eq_zero, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]`. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `[nilRad]`. Introduce `g hg`.

Conclude with `key _ g rfl hg`.
-/
theorem primitive_eq_zero_of_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ (f : F[X]) (m : ℕ), Irreducible f → (∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → aeval g f = 0 → φ g = 0) → ∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → φ g = 0 := by
  intro F _ _ V _ _ _ φ hcl hpr f m hf h0
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective
  have key : ∀ n : ℕ, ∀ g : Module.End F V,
      Module.finrank F V - Module.finrank F (LinearMap.ker (aeval g f)) = n →
      LinearMap.charpoly g = f ^ m → φ g = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro g hn hg
    by_cases htop : LinearMap.ker (aeval g f) = ⊤
    · exact h0 g hg (LinearMap.ker_eq_top.mp htop)
    have hCH : ∀ g' : Module.End F V, LinearMap.charpoly g' = f ^ m → aeval g' (f ^ m) = 0 := by
      intro g' hg'
      rw [← hg']
      exact LinearMap.aeval_self_charpoly g'
    have hbot : LinearMap.ker (aeval g f) ≠ ⊥ := by
      intro hb
      have hinj : Function.Injective (aeval g f : Module.End F V) := LinearMap.ker_eq_bot.mp hb
      have hinj' : Function.Injective ((aeval g f) ^ m : Module.End F V) := by
        rw [Module.End.coe_pow]
        exact hinj.iterate m
      rw [← map_pow, hCH g hg] at hinj'
      apply htop
      rw [hb, eq_comm, eq_bot_iff]
      intro x _
      exact (Submodule.mem_bot F).mpr (hinj' (by simp))
    have hinv : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f) := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hc : aeval g f * g = g * aeval g f := by
        have : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
        simpa using this
      have := congrArg (fun k : Module.End F V => k x) hc
      simpa [hx] using this
    have hsum := hpr _ hbot htop g hinv
    have hfin : (nilRad (LinearMap.ker (aeval g f))).Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    have hterm : ∀ h ∈ hfin.toFinset, φ (g + h) =
        if LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) then φ g else 0 := by
      intro h hh
      rw [Set.Finite.mem_toFinset] at hh
      have hcp : LinearMap.charpoly (g + h) = f ^ m := by
        rw [(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V _ g hinv).2 h hh, hg]
      obtain ⟨hle, heq⟩ := GlobalTheory.T.ker_aeval_add_stabilizerNilradical_socle F V g h f hh
      split_ifs with hc
      · obtain ⟨e, he⟩ := GlobalTheory.T.conj_of_primary_finrank_ker_pow_eq F V g (g + h) f m hf (hCH g hg) (hCH _ hcp) (heq hc)
        rw [← he, hcl e g]
      · have hlt : LinearMap.ker (aeval g f) < LinearMap.ker (aeval (g + h) f) :=
          lt_of_le_of_ne hle (Ne.symm hc)
        have h1 := Submodule.finrank_lt_finrank_of_lt hlt
        have h2 := Submodule.finrank_le (LinearMap.ker (aeval (g + h) f))
        exact ih _ (by omega) (g + h) rfl hcp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
    refine (mul_eq_zero.mp hsum).resolve_left ?_
    rw [Nat.cast_eq_zero, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    refine ⟨0, ?_⟩
    simp [nilRad]
  intro g hg
  exact key _ g rfl hg

end GlobalTheory.CuspGL
