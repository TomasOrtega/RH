import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

/- English proof (translation)
Establish `h : ρ.comp (Polynomial.coeToPowerSeries.algHom O) = Polynomial.aeval (ρ X)`. Apply `Polynomial.algHom_ext` to reduce the goal to its premises. Simplify using `[Polynomial.coeToPowerSeries.algHom_apply]`. Establish `h2` using `congrArg (fun f => f r) h`. Simplify `h2` using `[Polynomial.coeToPowerSeries.algHom_apply]`.
-/
theorem algHom_powerSeries_coe_eq_aeval {O S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (ρ : PowerSeries O →ₐ[O] PowerSeries S) (r : Polynomial O) :
    ρ (r : PowerSeries O) = Polynomial.aeval (ρ X) r := by
  have h : ρ.comp (Polynomial.coeToPowerSeries.algHom O) = Polynomial.aeval (ρ X) := by
    apply Polynomial.algHom_ext
    simp [Polynomial.coeToPowerSeries.algHom_apply]
  have h2 := congrArg (fun f => f r) h
  simpa [Polynomial.coeToPowerSeries.algHom_apply] using h2

/- English proof (translation)
Establish `hm : (P ^ k).Monic` using `hP.monic.pow k`. Establish `hne : PowerSeries.map (residue O) ((P ^ k : Polynomial O) : PowerSeries O) ≠ 0`. Rewrite using `[← Polynomial.polynomial_map_coe, Ne, Polynomial.coe_eq_zero_iff]`. Conclude with `(hm.map (residue O)).ne_zero`. Take `⟨q, r, h⟩` from `PowerSeries.exists_isWeierstrassDivision a hne`.

Use `⟨q, r, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.coe_pow]`. Conclude with `h.2`.
-/
theorem exists_pow_mul_add_polynomial {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    (P : Polynomial O) (hP : P.IsDistinguishedAt (maximalIdeal O)) (k : ℕ) (a : PowerSeries O) :
    ∃ (q : PowerSeries O) (r : Polynomial O), a = (P : PowerSeries O) ^ k * q + (r : PowerSeries O) := by
  have hm : (P ^ k).Monic := hP.monic.pow k
  have hne : PowerSeries.map (residue O) ((P ^ k : Polynomial O) : PowerSeries O) ≠ 0 := by
    rw [← Polynomial.polynomial_map_coe, Ne, Polynomial.coe_eq_zero_iff]
    exact (hm.map (residue O)).ne_zero
  obtain ⟨q, r, h⟩ := PowerSeries.exists_isWeierstrassDivision a hne
  refine ⟨q, r, ?_⟩
  rw [← Polynomial.coe_pow]
  exact h.2

/- English proof (translation)
Introduce `O S _ _ _ _ _ P hP ρ ρ' hX h0`. Establish `hpoly : ∀ r : Polynomial O, ρ (r : PowerSeries O) = ρ' (r : PowerSeries O)`. Introduce `r`. Rewrite using `[algHom_powerSeries_coe_eq_aeval, algHom_powerSeries_coe_eq_aeval, hX]`. Establish `hdvd : X ∣ ρ (P : PowerSeries O)`.

Rewrite using `[PowerSeries.X_dvd_iff, algHom_powerSeries_coe_eq_aeval]`. Conclude with `h0`. Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `a`. Use extensionality with `n`.

Take `⟨q, r, hqr⟩` from `exists_pow_mul_add_polynomial P hP (n + 1) a`. Establish `hd : ρ a - ρ' a = ρ (P : PowerSeries O) ^ (n + 1) * (ρ q - ρ' q)`. Rewrite using `[hqr, map_add, map_add, map_mul, map_mul, map_pow, map_pow, hpoly r, ← hpoly P]`. Expand and normalize the polynomial expressions, which then agree. Establish `hX' : X ^ (n + 1) ∣ ρ a - ρ' a`.

Rewrite using `[hd]`. Conclude with `Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hdvd _) _`. Establish `h1` using `(PowerSeries.X_pow_dvd_iff.mp hX') n (Nat.lt_succ_self n)`. Rewrite `h1` using `[map_sub, sub_eq_zero]`. Conclude with `h1`.
-/
theorem rhoUnique : RhoUniqueStatement := by
  intro O S _ _ _ _ _ P hP ρ ρ' hX h0
  have hpoly : ∀ r : Polynomial O, ρ (r : PowerSeries O) = ρ' (r : PowerSeries O) := by
    intro r
    rw [algHom_powerSeries_coe_eq_aeval, algHom_powerSeries_coe_eq_aeval, hX]
  have hdvd : X ∣ ρ (P : PowerSeries O) := by
    rw [PowerSeries.X_dvd_iff, algHom_powerSeries_coe_eq_aeval]
    exact h0
  apply AlgHom.ext
  intro a
  ext n
  obtain ⟨q, r, hqr⟩ := exists_pow_mul_add_polynomial P hP (n + 1) a
  have hd : ρ a - ρ' a = ρ (P : PowerSeries O) ^ (n + 1) * (ρ q - ρ' q) := by
    rw [hqr, map_add, map_add, map_mul, map_mul, map_pow, map_pow, hpoly r, ← hpoly P]
    ring
  have hX' : X ^ (n + 1) ∣ ρ a - ρ' a := by
    rw [hd]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hdvd _) _
  have h1 := (PowerSeries.X_pow_dvd_iff.mp hX') n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at h1
  exact h1

end LevelStatements.Lv
