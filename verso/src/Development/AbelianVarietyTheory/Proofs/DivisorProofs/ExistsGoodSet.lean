import Mathlib
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepRealisingCharOfMultiplicityOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalIdempotentCharacters

noncomputable section

namespace GlobalTheory.GoodSetOfChars

open GlobalTheory.FinGL Formalism.L2.DIV Module

/- English proof (translation)
Unfold `Formalism.MainNotions.PrimeDegreeVariant.eS chiIdem`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `[LinearMap.trace_one]`.
-/
theorem eS_eq_chiIdem {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (s : T.S) :
    Formalism.MainNotions.PrimeDegreeVariant.eS T s = chiIdem fun g => LinearMap.trace K (T.W s) (T.tau s g) := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.eS chiIdem
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [LinearMap.trace_one]

/- English proof (translation)
Establish `key : ∀ s : X, ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧ Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = (s : G → K) g` using `fun s => GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one K G s (hX s s.2) P0.H P0.chi (h1 s s.2)`. Use `choose n τ hn hs ht using key`. Establish `ht' : ∀ s : X, (fun g => LinearMap.trace K (Fin (n s) → K) (τ s g)) = (s : G → K)` using `fun s => funext (ht s)`. Set `T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G` to `{ S := X W := fun s => Fin (n s) → K ntW := fun s => by`. Establish `: Nonempty (Fin (n s))` using `⟨⟨0, hn s⟩⟩`.

Use `infer_instance`. Use `tau := τ`. Use `irr := hs`. Use `inj := fun a b hab => Subtype.ext (by rw [← ht' a, ← ht' b]; exact hab) }`. Use `⟨T, fun χ => ⟨fun h => ⟨⟨χ, h⟩, (ht' ⟨χ, h⟩).symm⟩, ?_⟩, fun s => ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨s, rfl⟩`. Conclude with `(ht' s).symm ▸ s.2`. Establish `h2` using `(GlobalTheory.CuspidalIdempotentCharacters.finrank_eq_one_iff (τ s) P0.H P0.chi).2 (by`. Repeatedly rewrite using `[ht s]`. Rewrite using `[h1 _ s.2, Nat.card_eq_fintype_card])`.

Rewrite `h2` using `[← GlobalTheory.CuspidalIdempotentCharacters.eps_eq_lvlIdem]`. Conclude with `h2`. Unfold `Formalism.MainNotions.PrimeDegreeVariant.eG idemOf`. Rewrite using `[← Finset.sum_coe_sort X]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[eS_eq_chiIdem]`. Conclude with `congrArg chiIdem (ht' s)`.
-/
theorem exists_goodSet (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P0 : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) [Fintype P0.H]
    (h1 : ∀ χ ∈ X, ∑ h : P0.H, χ (h : G) * (((P0.chi h)⁻¹ : Kˣ) : K) = (Fintype.card P0.H : K)) :
    ∃ T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G,
      (∀ χ, χ ∈ X ↔ ∃ s, χ = fun g => LinearMap.trace K (T.W s) (T.tau s g)) ∧
        Formalism.MainNotions.PrimeDegreeVariant.M1 T P0 ∧ Formalism.MainNotions.PrimeDegreeVariant.eG T = idemOf X := by
  classical
  have key : ∀ s : X, ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧
      Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = (s : G → K) g :=
    fun s => GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one K G s (hX s s.2) P0.H P0.chi (h1 s s.2)
  choose n τ hn hs ht using key
  have ht' : ∀ s : X, (fun g => LinearMap.trace K (Fin (n s) → K) (τ s g)) = (s : G → K) := fun s => funext (ht s)
  let T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G :=
    { S := X
      W := fun s => Fin (n s) → K
      ntW := fun s => by
        have : Nonempty (Fin (n s)) := ⟨⟨0, hn s⟩⟩
        infer_instance
      tau := τ
      irr := hs
      inj := fun a b hab => Subtype.ext (by rw [← ht' a, ← ht' b]; exact hab) }
  refine ⟨T, fun χ => ⟨fun h => ⟨⟨χ, h⟩, (ht' ⟨χ, h⟩).symm⟩, ?_⟩, fun s => ?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact (ht' s).symm ▸ s.2
  · have h2 := (GlobalTheory.CuspidalIdempotentCharacters.finrank_eq_one_iff (τ s) P0.H P0.chi).2 (by
      simp_rw [ht s]
      rw [h1 _ s.2, Nat.card_eq_fintype_card])
    rw [← GlobalTheory.CuspidalIdempotentCharacters.eps_eq_lvlIdem] at h2
    exact h2
  · unfold Formalism.MainNotions.PrimeDegreeVariant.eG idemOf
    rw [← Finset.sum_coe_sort X]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [eS_eq_chiIdem]
    exact congrArg chiIdem (ht' s)

end GlobalTheory.GoodSetOfChars
