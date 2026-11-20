import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ

open Matrix Polynomial
open GlobalTheory.ClassParam (krylov krylov_map exists_cyclic_field)

namespace GlobalTheory.SemilocalConj

/- English proof (translation)
Use `haveI : Finite (MaximalSpectrum R) := by haveI := hfin.to_subtype`. Conclude with `Finite.of_injective (fun m : MaximalSpectrum R => (⟨m.asIdeal, m.isMaximal⟩ : {I : Ideal R | I.IsMaximal})) (fun a b h => MaximalSpectrum.ext (congrArg Subtype.val h))`. Establish `hloc : ∀ m : MaximalSpectrum R, ∃ v : Fin r → R ⧸ m.asIdeal, (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0`. Introduce `m`. Use `m.isMaximal` as an intermediate fact.

Use `letI := Ideal.Quotient.field m.asIdeal`. Conclude with `exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)`. Use `choose w hw using hloc`. Establish `hsurj : ∀ i : Fin r, ∃ a : R, ∀ m : MaximalSpectrum R, Ideal.Quotient.mk m.asIdeal a = w m i`. Introduce `i`.

Take `⟨a, ha⟩` from `Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum R => m.asIdeal) (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)`. Conclude with `⟨a, ha⟩`. Use `choose v hv using hsurj`. Use `⟨v, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Take `⟨m, hm, hmem⟩` from `exists_max_ideal_of_mem_nonunits hn`. Apply `hw ⟨m, hm⟩` to reduce the goal to its premises. Establish `: w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v` using `funext fun i => (hv i ⟨m, hm⟩).symm`. Rewrite using `[this, ← krylov_map]`. Rewrite `hmem` using `[← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]`.

Conclude with `hmem`.
-/
theorem exists_cyclic_of_finite_maximal {R : Type} [CommRing R]
    (hfin : Set.Finite {I : Ideal R | I.IsMaximal}) {r : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (hs : g.charpoly.Separable) : ∃ v, IsUnit (krylov g v).det := by
  classical
  haveI : Finite (MaximalSpectrum R) := by
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun m : MaximalSpectrum R =>
      (⟨m.asIdeal, m.isMaximal⟩ : {I : Ideal R | I.IsMaximal}))
      (fun a b h => MaximalSpectrum.ext (congrArg Subtype.val h))
  have hloc : ∀ m : MaximalSpectrum R, ∃ v : Fin r → R ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : R, ∀ m : MaximalSpectrum R,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum R => m.asIdeal)
      (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)
    exact ⟨a, ha⟩
  choose v hv using hsurj
  refine ⟨v, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hw ⟨m, hm⟩
  have : w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v := funext fun i => (hv i ⟨m, hm⟩).symm
  rw [this, ← krylov_map]
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
  exact hmem

/- English proof (translation)
Introduce `R _ hfin n γ δ hχ hs`. Take `⟨v, hv⟩` from `exists_cyclic_of_finite_maximal hfin γ hs`. Take `⟨w, hw⟩` from `exists_cyclic_of_finite_maximal hfin δ (hχ ▸ hs)`. Take `⟨a, ha⟩` from `(isUnit_iff_isUnit_det _).2 hv`. Take `⟨b, hb⟩` from `(isUnit_iff_isUnit_det _).2 hw`.

Establish `h1` using `GlobalTheory.Orb.mul_krylov_eq γ v`. Establish `h2` using `GlobalTheory.Orb.mul_krylov_eq δ w`. Rewrite `h1` using `[← ha]`. Rewrite `h2` using `[← hb, ← hχ]`. Use `⟨a * b⁻¹, ?_⟩` and prove the remaining obligations.

Use `set C := GlobalTheory.Orb.companionMat n γ.charpoly`. Rewrite using `[Units.val_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[mul_assoc]`. Use `_ = ↑a * ↑b⁻¹ * (↑b * C) * ↑b⁻¹ := by rw [h2]`.

Use `_ = ↑a * C * ↑b⁻¹ := by`. Simplify using `[mul_assoc]`. Use `_ = γ * ↑a * ↑b⁻¹ := by rw [h1]`. Use `_ = γ * (↑a * ↑b⁻¹) := by rw [mul_assoc]`.
-/
theorem conj_of_charpoly_eq_of_separable : ∀ (R : Type) [CommRing R], Set.Finite {I : Ideal R | I.IsMaximal} →
    ∀ (n : ℕ) (γ δ : Matrix (Fin n) (Fin n) R), γ.charpoly = δ.charpoly → γ.charpoly.Separable →
      ∃ u : GL (Fin n) R, (u : Matrix (Fin n) (Fin n) R) * δ = γ * u := by
  intro R _ hfin n γ δ hχ hs
  obtain ⟨v, hv⟩ := exists_cyclic_of_finite_maximal hfin γ hs
  obtain ⟨w, hw⟩ := exists_cyclic_of_finite_maximal hfin δ (hχ ▸ hs)
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  obtain ⟨b, hb⟩ := (isUnit_iff_isUnit_det _).2 hw
  have h1 := GlobalTheory.Orb.mul_krylov_eq γ v
  have h2 := GlobalTheory.Orb.mul_krylov_eq δ w
  rw [← ha] at h1
  rw [← hb, ← hχ] at h2
  refine ⟨a * b⁻¹, ?_⟩
  set C := GlobalTheory.Orb.companionMat n γ.charpoly
  rw [Units.val_mul]
  calc (a : Matrix (Fin n) (Fin n) R) * ↑b⁻¹ * δ = ↑a * ↑b⁻¹ * (δ * ↑b) * ↑b⁻¹ := by
        simp [mul_assoc]
    _ = ↑a * ↑b⁻¹ * (↑b * C) * ↑b⁻¹ := by rw [h2]
    _ = ↑a * C * ↑b⁻¹ := by
        simp [mul_assoc]
    _ = γ * ↑a * ↑b⁻¹ := by rw [h1]
    _ = γ * (↑a * ↑b⁻¹) := by rw [mul_assoc]

/- English proof (translation)
The claim follows from `conj_of_charpoly_eq_of_separable`.
-/
example : ∀ (R : Type) [CommRing R], Set.Finite {I : Ideal R | I.IsMaximal} → ∀ (n : ℕ) (γ δ : Matrix (Fin n) (Fin n) R), γ.charpoly = δ.charpoly → γ.charpoly.Separable → ∃ u : GL (Fin n) R, (u : Matrix (Fin n) (Fin n) R) * δ = γ * u :=
  conj_of_charpoly_eq_of_separable

end GlobalTheory.SemilocalConj
