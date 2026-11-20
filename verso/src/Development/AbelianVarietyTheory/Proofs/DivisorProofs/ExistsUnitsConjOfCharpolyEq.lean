import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ

open Matrix Polynomial

namespace GlobalTheory.SemilocalConj

open GlobalTheory.ClassParam (krylov krylov_map exists_cyclic_field)

/- English proof (translation)
Establish `hloc : ∀ m : MaximalSpectrum A, ∃ v : Fin r → A ⧸ m.asIdeal, (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0`. Introduce `m`. Use `m.isMaximal` as an intermediate fact. Use `letI := Ideal.Quotient.field m.asIdeal`. Conclude with `exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)`.

Use `choose w hw using hloc`. Establish `hsurj : ∀ i : Fin r, ∃ a : A, ∀ m : MaximalSpectrum A, Ideal.Quotient.mk m.asIdeal a = w m i`. Introduce `i`. Take `⟨a, ha⟩` from `Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum A => m.asIdeal) (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)`. Conclude with `⟨a, ha⟩`.

Use `choose v hv using hsurj`. Use `⟨v, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Take `⟨m, hm, hmem⟩` from `exists_max_ideal_of_mem_nonunits hn`. Apply `hw ⟨m, hm⟩` to reduce the goal to its premises.

Establish `: w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v` using `funext fun i => (hv i ⟨m, hm⟩).symm`. Rewrite using `[this, ← krylov_map]`. Rewrite `hmem` using `[← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]`. Conclude with `hmem`.
-/
theorem exists_isUnit_det_krylov {A : Type} [CommRing A] [Finite (MaximalSpectrum A)] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) A) (hs : g.charpoly.Separable) :
    ∃ v, IsUnit (krylov g v).det := by
  classical
  have hloc : ∀ m : MaximalSpectrum A, ∃ v : Fin r → A ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : A, ∀ m : MaximalSpectrum A,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum A => m.asIdeal)
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
Establish `hs' : M.charpoly.Separable` using `hχ ▸ hs`. Take `⟨w, hw⟩` from `exists_isUnit_det_krylov M₀ hs`. Take `⟨v, hv⟩` from `exists_isUnit_det_krylov M hs'`. Take `⟨a, ha⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 hw`. Take `⟨b, hb⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 hv`.

Establish `h1` using `GlobalTheory.Orb.mul_krylov_eq M₀ w`. Establish `h2` using `GlobalTheory.Orb.mul_krylov_eq M v`. Rewrite `h1` using `[← ha]`. Rewrite `h2` using `[← hb, hχ]`. Establish `h3 : ((a⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) * M₀ = GlobalTheory.Orb.companionMat n M₀.charpoly * ((a⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A)`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨b * a⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← mul_assoc, h2, mul_assoc, h3, mul_assoc]`.
-/
theorem exists_units_conj_of_charpoly_eq (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (n : ℕ)
    (M₀ M : Matrix (Fin n) (Fin n) A) (hs : M₀.charpoly.Separable) (hχ : M.charpoly = M₀.charpoly) :
    ∃ P : (Matrix (Fin n) (Fin n) A)ˣ, (P : Matrix (Fin n) (Fin n) A) * M₀ = M * P := by
  have hs' : M.charpoly.Separable := hχ ▸ hs
  obtain ⟨w, hw⟩ := exists_isUnit_det_krylov M₀ hs
  obtain ⟨v, hv⟩ := exists_isUnit_det_krylov M hs'
  obtain ⟨a, ha⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hw
  obtain ⟨b, hb⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hv
  have h1 := GlobalTheory.Orb.mul_krylov_eq M₀ w
  have h2 := GlobalTheory.Orb.mul_krylov_eq M v
  rw [← ha] at h1
  rw [← hb, hχ] at h2
  have h3 : ((a⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) * M₀ =
      GlobalTheory.Orb.companionMat n M₀.charpoly * ((a⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) := by
    calc ((a⁻¹ : (Matrix (Fin n) (Fin n) A)ˣ) : Matrix (Fin n) (Fin n) A) * M₀
        = (↑a⁻¹ * M₀ * ↑a) * ↑a⁻¹ := by rw [mul_assoc _ (a : Matrix (Fin n) (Fin n) A), Units.mul_inv, mul_one]
      _ = ↑a⁻¹ * (↑a * GlobalTheory.Orb.companionMat n M₀.charpoly) * ↑a⁻¹ := by rw [mul_assoc (↑a⁻¹) M₀, h1]
      _ = GlobalTheory.Orb.companionMat n M₀.charpoly * ↑a⁻¹ := by rw [← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨b * a⁻¹, ?_⟩
  rw [Units.val_mul, ← mul_assoc, h2, mul_assoc, h3, mul_assoc]

/- English proof (translation)
The claim follows from `exists_units_conj_of_charpoly_eq`.
-/
example : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (n : ℕ) (M₀ M : Matrix (Fin n) (Fin n) A),
    M₀.charpoly.Separable → M.charpoly = M₀.charpoly →
      ∃ P : (Matrix (Fin n) (Fin n) A)ˣ, (P : Matrix (Fin n) (Fin n) A) * M₀ = M * P :=
  exists_units_conj_of_charpoly_eq

end GlobalTheory.SemilocalConj
