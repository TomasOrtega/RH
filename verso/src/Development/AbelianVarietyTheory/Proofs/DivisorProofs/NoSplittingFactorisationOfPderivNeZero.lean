import Mathlib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Introduce `Ω _ σ f g i D hsmooth hirr ⟨u, v, _, _, huv, P, Q, hPu, hPg, hQv, hQg⟩`. Substitute `huv` using the available equality. Set `pt : (σ → Ω) → PrimeSpectrum (MvPolynomial σ Ω)` to `fun R => ⟨RingHom.ker (MvPolynomial.eval R), RingHom.ker_isPrime _⟩`. Establish `mem_pt : ∀ R h, h ∈ (pt R).asIdeal ↔ MvPolynomial.eval R h = 0` using `fun R h => RingHom.mem_ker`. Establish `inS : ∀ R, MvPolynomial.eval R (u * v) = 0 → MvPolynomial.eval R g ≠ 0 → pt R ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g}`.

Introduce `R h1 h2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]`. Conclude with `(mem_pt R _).2 h1`. Rewrite using `[PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]`.

Conclude with `fun h => h2 ((mem_pt R _).1 h)`. Establish `hcov : PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g} ⊆ PrimeSpectrum.zeroLocus {u} ∪ PrimeSpectrum.zeroLocus {v}`. Introduce `x hx`. Establish `hx1` using `hx.1`. Rewrite `hx1` using `[PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]`.

Break down `x.isPrime.mem_or_mem hx1 with h | h` into its components or cases. Use `left`. Rewrite using `[PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]`. Conclude with `h`. Use `right`.

Rewrite using `[PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]`. Conclude with `h`. Establish `key : ∀ R, MvPolynomial.eval R u = 0 → MvPolynomial.eval R v = 0 → MvPolynomial.eval R g ≠ 0 → False`. Introduce `R hu hv hg`. Apply `hsmooth R (by simp [hu]) hg` to reduce the goal to its premises.

Simplify using `[Derivation.leibniz, hu, hv]`. Break down `(isPreirreducible_iff_isClosed_union_isClosed.1 hirr) _ _ (PrimeSpectrum.isClosed_zeroLocus _) (PrimeSpectrum.isClosed_zeroLocus _) hcov with h | h` into its components or cases. Establish `hm` using `h (inS Q (by simp [hQv]) hQg)`. Rewrite `hm` using `[PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]`. Conclude with `key Q ((mem_pt Q _).1 hm) hQv hQg`.

Establish `hm` using `h (inS P (by simp [hPu]) hPg)`. Rewrite `hm` using `[PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]`. Conclude with `key P hPu ((mem_pt P _).1 hm) hPg`.
-/
theorem hypersurface_part_no_splitting_factorisation :
    ∀ (Ω : Type) [Field Ω] (σ : Type) (f g : MvPolynomial σ Ω) (i : σ) (D : ℕ),
      (∀ Q : σ → Ω, MvPolynomial.eval Q f = 0 → MvPolynomial.eval Q g ≠ 0 →
        MvPolynomial.eval Q (MvPolynomial.pderiv i f) ≠ 0) →
      IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) →
      ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧
        ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧
          MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) := by
  intro Ω _ σ f g i D hsmooth hirr ⟨u, v, _, _, huv, P, Q, hPu, hPg, hQv, hQg⟩
  subst huv
  let pt : (σ → Ω) → PrimeSpectrum (MvPolynomial σ Ω) := fun R =>
    ⟨RingHom.ker (MvPolynomial.eval R), RingHom.ker_isPrime _⟩
  have mem_pt : ∀ R h, h ∈ (pt R).asIdeal ↔ MvPolynomial.eval R h = 0 :=
    fun R h => RingHom.mem_ker
  have inS : ∀ R, MvPolynomial.eval R (u * v) = 0 → MvPolynomial.eval R g ≠ 0 →
      pt R ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g} := by
    intro R h1 h2
    refine ⟨?_, ?_⟩
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]; exact (mem_pt R _).2 h1
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact fun h => h2 ((mem_pt R _).1 h)
  have hcov : PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g} ⊆
      PrimeSpectrum.zeroLocus {u} ∪ PrimeSpectrum.zeroLocus {v} := by
    intro x hx
    have hx1 := hx.1
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hx1
    rcases x.isPrime.mem_or_mem hx1 with h | h
    · left; rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]; exact h
    · right; rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]; exact h
  have key : ∀ R, MvPolynomial.eval R u = 0 → MvPolynomial.eval R v = 0 →
      MvPolynomial.eval R g ≠ 0 → False := by
    intro R hu hv hg
    apply hsmooth R (by simp [hu]) hg
    simp [Derivation.leibniz, hu, hv]
  rcases (isPreirreducible_iff_isClosed_union_isClosed.1 hirr) _ _
      (PrimeSpectrum.isClosed_zeroLocus _) (PrimeSpectrum.isClosed_zeroLocus _) hcov with h | h
  · have hm := h (inS Q (by simp [hQv]) hQg)
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hm
    exact key Q ((mem_pt Q _).1 hm) hQv hQg
  · have hm := h (inS P (by simp [hPu]) hPg)
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hm
    exact key P hPu ((mem_pt P _).1 hm) hPg

end GlobalTheory
