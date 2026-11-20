import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES

open GlobalTheory.KroneckerCongruence in

/- English proof (translation)
Introduce `Ω _ _ _ ε X q hq V s hs a ha r`. Use `haveI : Fact q.Prime := ⟨hq⟩`. Establish `hε : Function.Injective ε` using `ε.injective`. Establish `hq0 : (q : ℚ) ≠ 0` using `by exact_mod_cast hq.ne_zero`. Use `set ρ := IsLocalRing.residue V with hρ_def`.

Establish `hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1` using `fun x => by`. Rewrite using `[hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]`. Use `haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by`. Establish `: ρ (q : V) = 0` using `(hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hs.1)`. Simplify using `using this)`.

Establish `hfrob : ∀ x : V, ρ ⟨s x, (hs.2 x x.2).1⟩ = ρ x ^ q`. Introduce `x`. Rewrite using `[← sub_eq_zero, ← map_pow, ← map_sub, hρ0]`. Simplify using `using (hs.2 x x.2).2.2`. Use `set c := X.exp a with hc`.

Establish `hdq : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det`. Simplify using `[Matrix.det_fin_two]`. Conclude with `hq.pos` after adjusting the coercions. Establish `hA : (X.exp (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a)).coeff r = c.coeff (r / q)`. Establish `h` using `X.exp_upper (toGQ !![(q : ℤ), 0; 0, 1]) (by rw [ent_toGQ _ hdq]; simp) a (r / q)`.

Rewrite `h` using `[ent_toGQ _ hdq, ent_toGQ _ hdq, ent_toGQ _ hdq]`. Simplify using `[eOm_zero hε, hq0] at h`. Rewrite using `[← h]`. Use `set B := X.exp (X.gal s.symm a) with hB`. Establish `hBc : ∀ t, B.coeff t = s.symm (c.coeff t)` using `fun t => by rw [hB, X.gal_exp]`.

Establish `hBV : ∀ t, B.coeff t ∈ V` using `fun t => by rw [hBc]; exact (hs.2 _ (ha t)).2.1`. Establish `hBq : X.exp ((X.gal s.symm a) ^ q) = hahnSeriesCoeffRingHomMap V.subtype (liftV V B hBV ^ q)`. Rewrite using `[map_pow, map_pow, map_liftV]`. Use `set y : V := (liftV V B hBV ^ q).coeff r with hy_def`. Establish `hy : (X.exp ((X.gal s.symm a) ^ q)).coeff r = (y : Ω)` using `by rw [hBq, hahnSeriesCoeffRingHomMap_coeff]; rfl`.

Establish `hρy : ρ y = ρ ⟨c.coeff (r / q), ha _⟩`. Establish `h1 : ρ y = (hahnSeriesCoeffRingHomMap ρ (liftV V B hBV ^ q)).coeff r` using `by rw [hahnSeriesCoeffRingHomMap_coeff]`. Rewrite using `[h1, map_pow, coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff]`. Establish `h2 : (liftV V B hBV).coeff (r / q) = ⟨s.symm (c.coeff (r / q)), (hs.2 _ (ha _)).2.1⟩` using `Subtype.ext (hBc _)`. Rewrite using `[h2, ← hfrob]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[map_sub, HahnSeries.coeff_sub, hA, hy]`. Establish `hmem : c.coeff (r / q) - (y : Ω) = ((⟨c.coeff (r / q), ha _⟩ - y : V) : Ω)` using `rfl`.

Rewrite using `[hmem, ValuationSubring.mem_nonunits_iff, ← hρ0, map_sub, hρy, sub_self]`.
-/
theorem kron_frob_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (q : ℕ), q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ a : X.K, IntC X V a →
    SmallC X V (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a - (X.gal s.symm a) ^ q) := by
  intro Ω _ _ _ ε X q hq V s hs a ha r
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hε : Function.Injective ε := ε.injective
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hs.1)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs.2 x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs.2 x x.2).2.2
  set c := X.exp a with hc
  have hdq : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hA : (X.exp (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a)).coeff r = c.coeff (r / q) := by
    have h := X.exp_upper (toGQ !![(q : ℤ), 0; 0, 1]) (by rw [ent_toGQ _ hdq]; simp) a (r / q)
    rw [ent_toGQ _ hdq, ent_toGQ _ hdq, ent_toGQ _ hdq] at h
    simp [eOm_zero hε, hq0] at h
    rw [← h]
  set B := X.exp (X.gal s.symm a) with hB
  have hBc : ∀ t, B.coeff t = s.symm (c.coeff t) := fun t => by rw [hB, X.gal_exp]
  have hBV : ∀ t, B.coeff t ∈ V := fun t => by rw [hBc]; exact (hs.2 _ (ha t)).2.1
  have hBq : X.exp ((X.gal s.symm a) ^ q) = hahnSeriesCoeffRingHomMap V.subtype (liftV V B hBV ^ q) := by
    rw [map_pow, map_pow, map_liftV]
  set y : V := (liftV V B hBV ^ q).coeff r with hy_def
  have hy : (X.exp ((X.gal s.symm a) ^ q)).coeff r = (y : Ω) := by rw [hBq, hahnSeriesCoeffRingHomMap_coeff]; rfl
  have hρy : ρ y = ρ ⟨c.coeff (r / q), ha _⟩ := by
    have h1 : ρ y = (hahnSeriesCoeffRingHomMap ρ (liftV V B hBV ^ q)).coeff r := by rw [hahnSeriesCoeffRingHomMap_coeff]
    rw [h1, map_pow, coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff]
    have h2 : (liftV V B hBV).coeff (r / q) = ⟨s.symm (c.coeff (r / q)), (hs.2 _ (ha _)).2.1⟩ :=
      Subtype.ext (hBc _)
    rw [h2, ← hfrob]
    congr 1
    apply Subtype.ext
    simp
  rw [map_sub, HahnSeries.coeff_sub, hA, hy]
  have hmem : c.coeff (r / q) - (y : Ω) = ((⟨c.coeff (r / q), ha _⟩ - y : V) : Ω) := rfl
  rw [hmem, ValuationSubring.mem_nonunits_iff, ← hρ0, map_sub, hρy, sub_self]

end GlobalTheory.KZ.ES
