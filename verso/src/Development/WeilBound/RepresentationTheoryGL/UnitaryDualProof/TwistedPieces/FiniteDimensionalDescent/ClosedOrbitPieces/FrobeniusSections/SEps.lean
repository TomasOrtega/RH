import Mathlib

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

/- English proof (translation)
Establish `: IsArtinianRing S` using `IsArtinianRing.of_finite k S`. Use `haveI : Fintype (MaximalSpectrum S) := Fintype.ofFinite _`. Use `set φ := IsArtinianRing.equivPi S with hφ`. Set `σ` to `(Fintype.equivFin (MaximalSpectrum S)).symm`. Use `⟨Fintype.card (MaximalSpectrum S), fun t => φ.symm (Pi.single (σ t) 1), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `t show _ * _ = _`. Rewrite using `[← map_mul]`. Use `congr 1`. Use extensionality with `M`. Distinguish the cases in `h : M = σ t`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_sum, map_one]`.

Simplify using `only [AlgEquiv.apply_symm_apply]`. Rewrite using `[Equiv.sum_comp σ (fun M => (Pi.single M 1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal))]`. Conclude with `Finset.univ_sum_single (1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal)`. Introduce `t t' htt`. Rewrite using `[← map_mul]`.

Establish `hne : σ t ≠ σ t'` using `fun h => htt (σ.injective h)`. Establish `: (Pi.single (σ t) 1 * Pi.single (σ t') 1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal) = 0`. Use extensionality with `M`. Distinguish the cases in `h1 : M = σ t`. Substitute `h1` using the available equality.

Simplify using `[hne.symm]`. Simplify using `[h1]`. Rewrite using `[this, map_zero]`. Introduce `t s`. Use `(σ t).isMaximal` as an intermediate fact.

Distinguish the cases in `ha : φ s (σ t) = 0`. Use `left`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_mul, AlgEquiv.apply_symm_apply, map_zero]`. Use extensionality with `M`.

Distinguish the cases in `h1 : M = σ t`. Substitute `h1` using the available equality. Simplify using `[ha]`. Simplify using `[h1]`. Use `right`.

Take `⟨b, hb⟩` from `Ideal.Quotient.exists_inv ha`. Use `⟨φ.symm (Pi.single (σ t) b), ?_⟩` and prove the remaining obligations. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]`. Use extensionality with `M`.

Distinguish the cases in `h1 : M = σ t`. Substitute `h1` using the available equality. Simplify using `only [Pi.mul_apply, Pi.single_eq_same, mul_one]`. Conclude with `hb`. Simplify using `[h1]`.
-/
theorem idem {k S : Type*} [Field k] [CommRing S] [Algebra k S] [FiniteDimensional k S] [IsReduced S] :
    ∃ (m : ℕ) (e : Fin m → S), (∀ t, IsIdempotentElem (e t)) ∧ ∑ t, e t = 1 ∧
      (∀ t t', t ≠ t' → e t * e t' = 0) ∧ ∀ t s, s * e t = 0 ∨ ∃ w, s * e t * w = e t := by
  classical
  have : IsArtinianRing S := IsArtinianRing.of_finite k S
  haveI : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  set φ := IsArtinianRing.equivPi S with hφ
  let σ := (Fintype.equivFin (MaximalSpectrum S)).symm
  refine ⟨Fintype.card (MaximalSpectrum S), fun t => φ.symm (Pi.single (σ t) 1), ?_, ?_, ?_, ?_⟩
  · intro t
    show _ * _ = _
    rw [← map_mul]
    congr 1
    ext M
    by_cases h : M = σ t
    · subst h; simp
    · simp [h]
  · apply φ.injective
    rw [map_sum, map_one]
    simp only [AlgEquiv.apply_symm_apply]
    rw [Equiv.sum_comp σ (fun M => (Pi.single M 1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal))]
    exact Finset.univ_sum_single (1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal)
  · intro t t' htt
    rw [← map_mul]
    have hne : σ t ≠ σ t' := fun h => htt (σ.injective h)
    have : (Pi.single (σ t) 1 * Pi.single (σ t') 1 : ∀ M : MaximalSpectrum S, S ⧸ M.asIdeal) = 0 := by
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp [hne.symm]
      · simp [h1]
    rw [this, map_zero]
  · intro t s
    have := (σ t).isMaximal
    by_cases ha : φ s (σ t) = 0
    · left
      apply φ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, map_zero]
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp [ha]
      · simp [h1]
    · right
      obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv ha
      refine ⟨φ.symm (Pi.single (σ t) b), ?_⟩
      apply φ.injective
      rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      ext M
      by_cases h1 : M = σ t
      · subst h1; simp only [Pi.mul_apply, Pi.single_eq_same, mul_one]; exact hb
      · simp [h1]

/- English proof (translation)
Use `set ε := Submodule.IsPrincipal.generator (nilradical R) with hε`. Establish `hspan : Ideal.span {ε} = nilradical R` using `Ideal.span_singleton_generator _`. Establish `hεn : IsNilpotent ε` using `mem_nilradical.mp (Submodule.IsPrincipal.generator_mem _)`. Use `⟨ε, hεn, fun r => ?_⟩` and prove the remaining obligations. Establish `key : ∀ n : ℕ, ∃ σ : Fin n → R, (∀ l, σ l ∈ S) ∧ ∃ u : R, r = ∑ l, σ l * ε ^ (l : ℕ) + ε ^ n * u`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨Fin.elim0, fun l => l.elim0, r, by simp⟩`. Consider the case `succ n ih`. Take `⟨σ, hσ, u, hu⟩` from `ih`.

Take `⟨s, hs, hn⟩` from `hS u`. Establish `hm : u - s ∈ Ideal.span {ε}` using `by rw [hspan]; exact mem_nilradical.mpr hn`. Take `⟨v, hv⟩` from `Ideal.mem_span_singleton'.mp hm`. Use `⟨Fin.snoc σ s, fun l => ?_, v, ?_⟩` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun i => ?_) l` and prove the remaining obligations.

Simplify using `using hs`. Simplify using `using hσ i`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]`. Rewrite using `[hu]`.

Establish `: u = s + v * ε` using `by rw [hv]; ring`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨σ, hσ, u, hu⟩` from `key q`. Use `⟨σ, hσ, ?_⟩` and prove the remaining obligations.

Rewrite using `[hu, hnil ε hεn, zero_mul, add_zero]`.
-/
theorem sEps {k R : Type*} [Field k] [CommRing R] [Algebra k R] [IsPrincipalIdealRing R] (S : Subalgebra k R)
    (hS : ∀ r : R, ∃ s ∈ S, IsNilpotent (r - s)) (q : ℕ) (hnil : ∀ r : R, IsNilpotent r → r ^ q = 0) :
    ∃ ε : R, IsNilpotent ε ∧ ∀ r : R, ∃ σ : Fin q → R, (∀ l, σ l ∈ S) ∧ r = ∑ l, σ l * ε ^ (l : ℕ) := by
  classical
  set ε := Submodule.IsPrincipal.generator (nilradical R) with hε
  have hspan : Ideal.span {ε} = nilradical R := Ideal.span_singleton_generator _
  have hεn : IsNilpotent ε := mem_nilradical.mp (Submodule.IsPrincipal.generator_mem _)
  refine ⟨ε, hεn, fun r => ?_⟩
  have key : ∀ n : ℕ, ∃ σ : Fin n → R, (∀ l, σ l ∈ S) ∧
      ∃ u : R, r = ∑ l, σ l * ε ^ (l : ℕ) + ε ^ n * u := by
    intro n
    induction n with
    | zero => exact ⟨Fin.elim0, fun l => l.elim0, r, by simp⟩
    | succ n ih =>
      obtain ⟨σ, hσ, u, hu⟩ := ih
      obtain ⟨s, hs, hn⟩ := hS u
      have hm : u - s ∈ Ideal.span {ε} := by rw [hspan]; exact mem_nilradical.mpr hn
      obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hm
      refine ⟨Fin.snoc σ s, fun l => ?_, v, ?_⟩
      · refine Fin.lastCases ?_ (fun i => ?_) l
        · simpa using hs
        · simpa using hσ i
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rw [hu]
        have : u = s + v * ε := by rw [hv]; ring
        rw [this]
        ring
  obtain ⟨σ, hσ, u, hu⟩ := key q
  refine ⟨σ, hσ, ?_⟩
  rw [hu, hnil ε hεn, zero_mul, add_zero]

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
