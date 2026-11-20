import Mathlib
import GroundTheory.AutomorphicForms.FiniteLengthJacquet
import GroundTheory.AutomorphicForms.FiniteLengthPieces
import GroundTheory.AutomorphicForms.FiniteLengthLevi
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

/- English proof (translation)
Take `⟨k, w, -, V, h0, hk, -, hV, hΨ⟩` from `geometricLemma (γ := δ) σ hσ`. Use `choose Ψ _ hΨk using hΨ`. Take `⟨j, hj⟩` from `h.exists_piece V hV h0 hk (fun j => indRep (cellLeviSub F β δ (w j)) (normInducing σ δ (w j))) Ψ hΨk`. Establish `hinc : ∀ a b, β (w j a) = β (w j b) → δ a = δ b`. Assume the negation of the conclusion as `hne`.

Use `subsingleton_piece_of_isCuspidal hc hne` as an intermediate fact. Use `hj.subsingleton` as an intermediate fact. Take `⟨u, hu⟩` from `exists_ne_zero_of_isIrreducible (ρ := τ)`. Conclude with `hu (Subsingleton.elim _ _)`. Use `⟨w j, fun a b => ⟨fun hab => ?_, hinc a b⟩, hj⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Take `⟨C, p, hp⟩` from `hj`. Conclude with `not_surjective_of_isCuspidal_piece hσ hinc ⟨a, b, hab, hne⟩ hτ hτc C p hp`.
-/
theorem exists_piece_of_isSubquotient_jacquetRep [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hc : IsCuspidal σ) {δ : Fin n → ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]
    {τ : Representation ℂ (levi F n δ) U} [τ.IsIrreducible] (hτ : IsSmooth τ)
    (hτc : IsCuspidal τ) (h : IsSubquotient τ (jacquetRep F n δ (parabolicInd F n β σ))) :
    ∃ w : Equiv.Perm (Fin n), ∃ _ : ∀ a b, δ a = δ b ↔ β (w a) = β (w b),
      IsSubquotient τ (indRep (cellLeviSub F β δ w) (normInducing σ δ w)) := by
  obtain ⟨k, w, -, V, h0, hk, -, hV, hΨ⟩ := geometricLemma (γ := δ) σ hσ
  choose Ψ _ hΨk using hΨ
  obtain ⟨j, hj⟩ := h.exists_piece V hV h0 hk
    (fun j => indRep (cellLeviSub F β δ (w j)) (normInducing σ δ (w j))) Ψ hΨk
  have hinc : ∀ a b, β (w j a) = β (w j b) → δ a = δ b := by
    by_contra hne
    have := subsingleton_piece_of_isCuspidal hc hne
    have := hj.subsingleton
    obtain ⟨u, hu⟩ := exists_ne_zero_of_isIrreducible (ρ := τ)
    exact hu (Subsingleton.elim _ _)
  refine ⟨w j, fun a b => ⟨fun hab => ?_, hinc a b⟩, hj⟩
  by_contra hne
  obtain ⟨C, p, hp⟩ := hj
  exact not_surjective_of_isCuspidal_piece hσ hinc ⟨a, b, hab, hne⟩ hτ hτc C p hp

/- English proof (translation)
Take `⟨w', hw'⟩` from `hδ`. Take `⟨k, w, -, V, h0, hk, -, hV, hΨ⟩` from `geometricLemma (γ := δ) σ hσ`. Use `choose Ψ _ hΨk using hΨ`. Use `hasFiniteLength_of_filtration V hV h0 hk (fun j => indRep (cellLeviSub F β δ (w j)) (normInducing σ δ (w j))) Ψ hΨk fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hinc : ∀ a b, β (w j a) = β (w j b) → δ a = δ b`.

Use `isIrreducible_piece hσ (w j) (blocks_eq_of_imp (w' := w') hinc hw')` as an intermediate fact. Conclude with `hasFiniteLength_of_isIrreducible`. Use `subsingleton_piece_of_isCuspidal hc hinc` as an intermediate fact. Conclude with `hasFiniteLength_of_subsingleton`.
-/
theorem hasFiniteLength_jacquetRep_parabolicInd [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hc : IsCuspidal σ) {δ : Fin n → ℕ}
    (hδ : ∃ w' : Equiv.Perm (Fin n), ∀ a b, δ a = δ b ↔ β (w' a) = β (w' b)) :
    HasFiniteLength (jacquetRep F n δ (parabolicInd F n β σ)) := by
  obtain ⟨w', hw'⟩ := hδ
  obtain ⟨k, w, -, V, h0, hk, -, hV, hΨ⟩ := geometricLemma (γ := δ) σ hσ
  choose Ψ _ hΨk using hΨ
  refine hasFiniteLength_of_filtration V hV h0 hk
    (fun j => indRep (cellLeviSub F β δ (w j)) (normInducing σ δ (w j))) Ψ hΨk fun j => ?_
  by_cases hinc : ∀ a b, β (w j a) = β (w j b) → δ a = δ b
  · have := isIrreducible_piece hσ (w j) (blocks_eq_of_imp (w' := w') hinc hw')
    exact hasFiniteLength_of_isIrreducible
  · have := subsingleton_piece_of_isCuspidal hc hinc
    exact hasFiniteLength_of_subsingleton

/- English proof (translation)
Set `ι` to `{δ : Fin n → Fin n // ∃ w : Equiv.Perm (Fin n), ∀ a b, δ a = δ b ↔ β (w a) = β (w b)}`. Set `dN : ι → Fin n → ℕ` to `fun δ i => (δ.1 i : ℕ)`. Establish `hdN : ∀ (δ : ι) a b, dN δ a = dN δ b ↔ δ.1 a = δ.1 b` using `fun δ a b => Fin.val_inj`. Establish `: ∀ δ : ι, LocallyCompactSpace (unipotentRadical F n (dN δ))` using `fun δ => isClosed_unipotentRadical.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `hasFiniteLength_of_coinvariants (isSmooth_parabolicInd σ) (fun δ : ι => unipotentRadical F n (dN δ)) (fun δ => exists_compactOpen_unipotentRadical) (M := fun δ => levi F n (dN δ)) (fun δ => jacquetRep F n (dN δ) (parabolicInd F n β σ)) (fun δ m => ⟨m, _, fun v => jacquetRep_mk _ …` and prove the remaining obligations.

Take `⟨w', hw'⟩` from `δ.2`. Take `⟨k, w, -, V, h0, hk, -, hV, hΨ⟩` from `geometricLemma (γ := dN δ) σ hσ`. Use `choose Ψ _ hΨk using hΨ`. Use `hasFiniteLength_of_filtration V hV h0 hk (fun j => indRep (cellLeviSub F β (dN δ) (w j)) (normInducing σ (dN δ) (w j))) Ψ hΨk fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hinc : ∀ a b, β (w j a) = β (w j b) → dN δ a = dN δ b`.

Establish `hiff` using `blocks_eq_of_imp (w' := w') hinc fun a b => (hdN δ a b).trans (hw' a b)`. Use `isIrreducible_piece hσ (w j) hiff` as an intermediate fact. Conclude with `hasFiniteLength_of_isIrreducible`. Use `subsingleton_piece_of_isCuspidal hc hinc` as an intermediate fact. Conclude with `hasFiniteLength_of_subsingleton`.

Introduce `V' _ _ π _ hπ hsub`. Take `⟨v, hv⟩` from `exists_ne_zero_of_isIrreducible (ρ := π)`. Establish `: Nontrivial V'` using `⟨⟨v, 0, hv⟩⟩`. Take `⟨β', U, _, _, τ, hτi, hτs, hτc, -, Φ, hΦ⟩` from `exists_embedding_parabolicInd hπ`. Establish `hq` using `surjective_frobeniusParabolic hπ Φ hΦ`.

Establish `hsubτ : IsSubquotient τ (jacquetRep F n β' (parabolicInd F n β σ))` using `(IsSubquotient.of_surjective _ hq).trans (hsub.jacquetRep (isSmooth_parabolicInd σ) β')`. Take `⟨w, hw, -⟩` from `exists_piece_of_isSubquotient_jacquetRep hσ hc hτs hτc hsubτ`. Establish `hrank : ∀ a b, β' a = β' b ↔ (rankFun β' a : ℕ) = rankFun β' b` using `fun a b => eq_iff_eq_of_lt_iff (fun i j => (rankFun_lt_iff β' i j).symm) a b`. Set `δ : ι` to `⟨rankFun β', w, fun a b => Fin.val_inj.symm.trans ((hrank a b).symm.trans (hw a b))⟩`. Use `⟨δ, ?_⟩` and prove the remaining obligations.

Establish `hN : unipotentRadical F n (dN δ) = unipotentRadical F n β'` using `unipotentRadical_congr (rankFun_lt_iff β')`. Rewrite using `[hN]`. Take `⟨u, hu⟩` from `exists_ne_zero_of_isIrreducible (ρ := τ)`. Take `⟨y, hy⟩` from `hq u`. Conclude with `⟨y, 0, fun h => hu (by rw [← hy, h, map_zero])⟩`.
-/
theorem hasFiniteLength_parabolicInd_of_isCuspidal [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hc : IsCuspidal σ) : HasFiniteLength (parabolicInd F n β σ) := by
  classical

  let ι := {δ : Fin n → Fin n // ∃ w : Equiv.Perm (Fin n), ∀ a b, δ a = δ b ↔ β (w a) = β (w b)}
  let dN : ι → Fin n → ℕ := fun δ i => (δ.1 i : ℕ)
  have hdN : ∀ (δ : ι) a b, dN δ a = dN δ b ↔ δ.1 a = δ.1 b := fun δ a b => Fin.val_inj
  have : ∀ δ : ι, LocallyCompactSpace (unipotentRadical F n (dN δ)) := fun δ =>
    isClosed_unipotentRadical.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine hasFiniteLength_of_coinvariants (isSmooth_parabolicInd σ)
    (fun δ : ι => unipotentRadical F n (dN δ)) (fun δ => exists_compactOpen_unipotentRadical)
    (M := fun δ => levi F n (dN δ)) (fun δ => jacquetRep F n (dN δ) (parabolicInd F n β σ))
    (fun δ m => ⟨m, _, fun v => jacquetRep_mk _ m v⟩) (fun δ => ?_) ?_
  ·
    obtain ⟨w', hw'⟩ := δ.2
    obtain ⟨k, w, -, V, h0, hk, -, hV, hΨ⟩ := geometricLemma (γ := dN δ) σ hσ
    choose Ψ _ hΨk using hΨ
    refine hasFiniteLength_of_filtration V hV h0 hk
      (fun j => indRep (cellLeviSub F β (dN δ) (w j)) (normInducing σ (dN δ) (w j))) Ψ hΨk
      fun j => ?_
    by_cases hinc : ∀ a b, β (w j a) = β (w j b) → dN δ a = dN δ b
    · have hiff := blocks_eq_of_imp (w' := w') hinc fun a b => (hdN δ a b).trans (hw' a b)
      have := isIrreducible_piece hσ (w j) hiff
      exact hasFiniteLength_of_isIrreducible
    · have := subsingleton_piece_of_isCuspidal hc hinc
      exact hasFiniteLength_of_subsingleton
  ·
    intro V' _ _ π _ hπ hsub
    obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
    have : Nontrivial V' := ⟨⟨v, 0, hv⟩⟩
    obtain ⟨β', U, _, _, τ, hτi, hτs, hτc, -, Φ, hΦ⟩ := exists_embedding_parabolicInd hπ
    have hq := surjective_frobeniusParabolic hπ Φ hΦ
    have hsubτ : IsSubquotient τ (jacquetRep F n β' (parabolicInd F n β σ)) :=
      (IsSubquotient.of_surjective _ hq).trans (hsub.jacquetRep (isSmooth_parabolicInd σ) β')
    obtain ⟨w, hw, -⟩ := exists_piece_of_isSubquotient_jacquetRep hσ hc hτs hτc hsubτ
    have hrank : ∀ a b, β' a = β' b ↔ (rankFun β' a : ℕ) = rankFun β' b := fun a b =>
      eq_iff_eq_of_lt_iff (fun i j => (rankFun_lt_iff β' i j).symm) a b
    let δ : ι := ⟨rankFun β', w, fun a b => Fin.val_inj.symm.trans ((hrank a b).symm.trans (hw a b))⟩
    refine ⟨δ, ?_⟩
    have hN : unipotentRadical F n (dN δ) = unipotentRadical F n β' :=
      unipotentRadical_congr (rankFun_lt_iff β')
    rw [hN]
    obtain ⟨u, hu⟩ := exists_ne_zero_of_isIrreducible (ρ := τ)
    obtain ⟨y, hy⟩ := hq u
    exact ⟨y, 0, fun h => hu (by rw [← hy, h, map_zero])⟩

end Parabolic

end GroundTheory.Automorphic
