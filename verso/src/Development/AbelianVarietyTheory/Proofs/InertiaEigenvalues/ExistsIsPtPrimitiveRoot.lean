import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

/- English proof (translation)
Establish `hs : 1 ≤ s` using `h.1`. Establish `hLL` using `h.2.2.2`. Establish `hprim : IsPrimitiveRoot (P.ζQ s) (l ^ s)`. Take `⟨m, rfl⟩ : ∃ m, s = m + 1` from `⟨s - 1, by omega⟩`. Establish `hpow : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]`. Establish `h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1` using `by rw [hpow]; exact P.ζQ_one`.

Establish `h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1`. Rewrite using `[pow_succ, pow_mul, hpow, P.ζQ_succ, P.ζQ_zero]`. Establish `h3` using `orderOf_eq_prime_pow h1 h2`. Rewrite using `[← h3]`. Conclude with `IsPrimitiveRoot.orderOf _`.

Establish `hmem : P.ζQ s ∈ Ks K s` using `(le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ Ks K s) (IntermediateField.subset_adjoin _ _ hprim.pow_eq_one)`. Set `Φ : Om l →ₐ[ℚ_[l]] Om l` to `((H.W K s LL h).emb i).liftNormal (Om l)`. Establish `hΦ : ∀ x : ↥(K0 K), Φ (x : Om l) = (((H.W K s LL h).emb i x : ↥LL.1) : Om l)` using `fun x => AlgHom.liftNormal_commutes ((H.W K s LL h).emb i) (Om l) x`. Set `τ₀ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l` to `Φ.comp (Ks K s).val`. Set `τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1` to `τ₀.codRestrict LL.1.toSubalgebra (hLL τ₀)`.

Establish `hτ : ∀ y : ↥(Ks K s), ((τ y : ↥LL.1) : Om l) = Φ (y : Om l)` using `fun _ => rfl`. Use `⟨τ ⟨P.ζQ s, hmem⟩, τ, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hτ, hxy, hΦ]`.

Introduce `y hy`. Use `congr 1`. Conclude with `Subtype.ext hy`. Establish `h1 : IsPrimitiveRoot (⟨P.ζQ s, hmem⟩ : ↥(Ks K s)) (l ^ s)` using `IsPrimitiveRoot.of_map_of_injective (f := (Ks K s).val) hprim (Ks K s).val.injective`. Conclude with `h1.map_of_injective τ.injective`.
-/
theorem exists_isPt_primitiveRoot {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    ∃ (ζ : ↥LL.1) (τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1), H.IsPt h i ζ τ ∧ IsPrimitiveRoot ζ (l ^ s) := by
  have hs : 1 ≤ s := h.1
  have hLL := h.2.2.2
  have hprim : IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    have hpow : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1 := by
      intro k
      induction k with
      | zero => simp
      | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
    have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [hpow]; exact P.ζQ_one
    have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by
      rw [pow_succ, pow_mul, hpow, P.ζQ_succ, P.ζQ_zero]
    have h3 := orderOf_eq_prime_pow h1 h2
    rw [← h3]
    exact IsPrimitiveRoot.orderOf _
  have hmem : P.ζQ s ∈ Ks K s :=
    (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ Ks K s)
      (IntermediateField.subset_adjoin _ _ hprim.pow_eq_one)
  let Φ : Om l →ₐ[ℚ_[l]] Om l := ((H.W K s LL h).emb i).liftNormal (Om l)
  have hΦ : ∀ x : ↥(K0 K), Φ (x : Om l) = (((H.W K s LL h).emb i x : ↥LL.1) : Om l) := fun x =>
    AlgHom.liftNormal_commutes ((H.W K s LL h).emb i) (Om l) x
  let τ₀ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l := Φ.comp (Ks K s).val
  let τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1 := τ₀.codRestrict LL.1.toSubalgebra (hLL τ₀)
  have hτ : ∀ y : ↥(Ks K s), ((τ y : ↥LL.1) : Om l) = Φ (y : Om l) := fun _ => rfl
  refine ⟨τ ⟨P.ζQ s, hmem⟩, τ, ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    rw [hτ, hxy, hΦ]
  · intro y hy
    congr 1
    exact Subtype.ext hy
  · have h1 : IsPrimitiveRoot (⟨P.ζQ s, hmem⟩ : ↥(Ks K s)) (l ^ s) :=
      IsPrimitiveRoot.of_map_of_injective (f := (Ks K s).val) hprim (Ks K s).val.injective
    exact h1.map_of_injective τ.injective

end GlobalTheory
