import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimary

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

/- English proof (translation)
Establish `hP : B.P ≠ 0` using `hs.ne_zero`. Establish `hint : IsIntegral K.E B.g` using `Algebra.IsIntegral.isIntegral _`. Establish `hz : minpoly K.E B.g ≠ 0` using `minpoly.ne_zero hint`. Establish `h0 : aeval (LinearMap.mulLeft K.E B.g) (minpoly K.E B.g) = 0`. Use `Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g (minpoly K.E B.g)` as an intermediate fact.

Rewrite `this` using `[minpoly.aeval, map_zero]`. Conclude with `this`. Establish `hdvd : B.P ∣ minpoly K.E B.g`. Rewrite using `[UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz, Multiset.le_iff_subset ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]`. Introduce `p hp`.

Rewrite `hp` using `[Polynomial.mem_normalizedFactors_iff hP]`. Rewrite using `[Polynomial.mem_normalizedFactors_iff hz]`. Conclude with `⟨hp.1, hp.2.1, GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩`. Establish `hle : Module.finrank K.E B.A ≤ (minpoly K.E B.g).natDegree`. Establish `h1 : B.P.natDegree = Module.finrank K.E B.A` using `LinearMap.charpoly_natDegree _`.

Rewrite using `[← h1]`. Conclude with `natDegree_le_of_dvd hdvd hz`. Establish `hli : LinearIndependent K.E fun i : Fin (minpoly K.E B.g).natDegree => B.g ^ (i : ℕ)` using `linearIndependent_pow B.g`. Establish `hge` using `hli.fintype_card_le_finrank`. Establish `htop` using `hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin] at hge ⊢; omega)`.

Rewrite using `[eq_top_iff, ← htop]`. Conclude with `Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)`.
-/
theorem span_pow_eq_top_of_separable (K : UQ) (B : InvAlg K) (hs : B.P.Separable) :
    Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by
  classical
  have hP : B.P ≠ 0 := hs.ne_zero
  have hint : IsIntegral K.E B.g := Algebra.IsIntegral.isIntegral _
  have hz : minpoly K.E B.g ≠ 0 := minpoly.ne_zero hint
  have h0 : aeval (LinearMap.mulLeft K.E B.g) (minpoly K.E B.g) = 0 := by
    have := Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g (minpoly K.E B.g)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hdvd : B.P ∣ minpoly K.E B.g := by
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz,
      Multiset.le_iff_subset ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]
    intro p hp
    rw [Polynomial.mem_normalizedFactors_iff hP] at hp
    rw [Polynomial.mem_normalizedFactors_iff hz]
    exact ⟨hp.1, hp.2.1, GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩
  have hle : Module.finrank K.E B.A ≤ (minpoly K.E B.g).natDegree := by
    have h1 : B.P.natDegree = Module.finrank K.E B.A := LinearMap.charpoly_natDegree _
    rw [← h1]
    exact natDegree_le_of_dvd hdvd hz
  have hli : LinearIndependent K.E fun i : Fin (minpoly K.E B.g).natDegree => B.g ^ (i : ℕ) :=
    linearIndependent_pow B.g
  have hge := hli.fintype_card_le_finrank
  have htop := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin] at hge ⊢; omega)
  rw [eq_top_iff, ← htop]
  exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)

end GlobalTheory.UnitLemma.Unr
