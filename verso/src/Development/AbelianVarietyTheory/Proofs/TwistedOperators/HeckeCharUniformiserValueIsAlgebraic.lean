import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
open NumberField IsDedekindDomain Formalism.L2.Host
noncomputable section

namespace GlobalTheory

open PI.AlgValsFin.W ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

/- English proof (translation)
The claim follows from `(Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom`.
-/
theorem isAlgebraic_embedding_apply {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (x : L) :
    IsAlgebraic ℚ (φ x) :=
  (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom

/- English proof (translation)
Introduce `L _ _ χ m hm w`. Take `⟨h, hpos, hk⟩` from `(classPow : ClassPow L)`. Take `⟨k, hk⟩` from `hk w`. Establish `hkw : ordF w k = (h : ℤ)` using `by rw [hk w, if_pos rfl]`. Establish `hout : ∀ v, v ∉ ({w} : Finset (HeightOneSpectrum (𝓞 L))) → ordF v k = 0`.

Introduce `v hv`. Rewrite using `[hk v, if_neg (by simpa using hv)]`. Take `⟨r, hr, hdec⟩` from `(decomp : Decomp L) k {w} hout`. Rewrite `hdec` using `[Finset.prod_singleton]`. Establish `hrel : χ.inf k * χ.loc w (atFin w k) * χ.1 r = 1`.

Establish `e` using `χ.2.2 k`. Rewrite `e` using `[hdec, map_mul, map_mul]`. Conclude with `e`. Take `⟨N, hN, hNt⟩` from `torsUnits L χ`. Establish `hinf : IsAlgebraic ℚ ((χ.inf k : ℂˣ) : ℂ)`.

Rewrite using `[hm k, ← mem_algebraicClosure_iff]`. Use `prod_mem fun φ _ => zpow_mem ?_ _` and prove the remaining obligations. Conclude with `mem_algebraicClosure_iff.2 (isAlgebraic_embedding_apply φ _)`. Establish `hloc : IsAlgebraic ℚ ((χ.loc w (atFin w k) : ℂˣ) : ℂ)`. Establish `e : χ.loc w (atFin w k) ^ N = (χ.inf k ^ N)⁻¹`.

Establish `e1` using `congrArg (· ^ N) hrel`. Simplify using `only [mul_pow, hNt r hr, mul_one, one_pow] at e1`. Conclude with `eq_inv_of_mul_eq_one_right e1`. Use `IsAlgebraic.of_pow hN ?_` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, e, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← mem_algebraicClosure_iff]`.

Conclude with `inv_mem (pow_mem (mem_algebraicClosure_iff.2 hinf) _)`. Use `set y : (w.adicCompletion L)ˣ := atFin w (unif w) ^ h * (atFin w k)⁻¹ with hy`. Establish `hyv : Valued.v ((y : (w.adicCompletion L)ˣ) : w.adicCompletion L) = 1`. Establish `h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion L)ˣ) : w.adicCompletion L) = WithZero.exp (-1)` using `unif_spec w`. Rewrite using `[hy, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, h1, valued_atFin, hkw, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]`.

Simplify using the standard rewrite rules. Establish `hyU : localIdele L w y ∈ UFin L`. Use `⟨rfl, fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality.

Rewrite using `[localIdele_snd_self]`. Conclude with `hyv`. Rewrite using `[(localIdele_isSupportedAt L w y).2 v hv, map_one]`. Establish `hyN : χ.loc w y ^ N = 1` using `hNt _ hyU`. Establish `hyval : χ.loc w y = χ.val w ^ h * (χ.loc w (atFin w k))⁻¹`.

Rewrite using `[hy, map_mul, map_pow, map_inv]`. Both sides reduce to the same expression. Establish `hpow : χ.val w ^ (h * N) = χ.loc w (atFin w k) ^ N`. Rewrite `hyN` using `[hyval, mul_pow, ← pow_mul, inv_pow, mul_inv_eq_one]`. Conclude with `hyN`.

Use `IsAlgebraic.of_pow (Nat.mul_pos hpos hN) ?_` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, hpow, Units.val_pow_eq_pow_val, ← mem_algebraicClosure_iff]`. Conclude with `pow_mem (mem_algebraicClosure_iff.2 hloc) _`.
-/
theorem heckeChar_val_isAlgebraic : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∀ w : HeightOneSpectrum (𝓞 L), IsAlgebraic ℚ ((χ.val w : ℂˣ) : ℂ) := by
  intro L _ _ χ m hm w
  classical

  obtain ⟨h, hpos, hk⟩ := (classPow : ClassPow L)
  obtain ⟨k, hk⟩ := hk w
  have hkw : ordF w k = (h : ℤ) := by rw [hk w, if_pos rfl]
  have hout : ∀ v, v ∉ ({w} : Finset (HeightOneSpectrum (𝓞 L))) → ordF v k = 0 := by
    intro v hv
    rw [hk v, if_neg (by simpa using hv)]
  obtain ⟨r, hr, hdec⟩ := (decomp : Decomp L) k {w} hout
  rw [Finset.prod_singleton] at hdec
  have hrel : χ.inf k * χ.loc w (atFin w k) * χ.1 r = 1 := by
    have e := χ.2.2 k
    rw [hdec, map_mul, map_mul] at e
    exact e
  obtain ⟨N, hN, hNt⟩ := torsUnits L χ

  have hinf : IsAlgebraic ℚ ((χ.inf k : ℂˣ) : ℂ) := by
    rw [hm k, ← mem_algebraicClosure_iff]
    refine prod_mem fun φ _ => zpow_mem ?_ _
    exact mem_algebraicClosure_iff.2 (isAlgebraic_embedding_apply φ _)

  have hloc : IsAlgebraic ℚ ((χ.loc w (atFin w k) : ℂˣ) : ℂ) := by
    have e : χ.loc w (atFin w k) ^ N = (χ.inf k ^ N)⁻¹ := by
      have e1 := congrArg (· ^ N) hrel
      simp only [mul_pow, hNt r hr, mul_one, one_pow] at e1
      exact eq_inv_of_mul_eq_one_right e1
    refine IsAlgebraic.of_pow hN ?_
    rw [← Units.val_pow_eq_pow_val, e, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      ← mem_algebraicClosure_iff]
    exact inv_mem (pow_mem (mem_algebraicClosure_iff.2 hinf) _)

  set y : (w.adicCompletion L)ˣ := atFin w (unif w) ^ h * (atFin w k)⁻¹ with hy
  have hyv : Valued.v ((y : (w.adicCompletion L)ˣ) : w.adicCompletion L) = 1 := by
    have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
        WithZero.exp (-1) := unif_spec w
    rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, h1,
      valued_atFin, hkw, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have hyU : localIdele L w y ∈ UFin L := by
    refine ⟨rfl, fun v => ?_⟩
    by_cases hv : v = w
    · subst hv
      rw [localIdele_snd_self]
      exact hyv
    · rw [(localIdele_isSupportedAt L w y).2 v hv, map_one]
  have hyN : χ.loc w y ^ N = 1 := hNt _ hyU
  have hyval : χ.loc w y = χ.val w ^ h * (χ.loc w (atFin w k))⁻¹ := by
    rw [hy, map_mul, map_pow, map_inv]
    rfl
  have hpow : χ.val w ^ (h * N) = χ.loc w (atFin w k) ^ N := by
    rw [hyval, mul_pow, ← pow_mul, inv_pow, mul_inv_eq_one] at hyN
    exact hyN
  refine IsAlgebraic.of_pow (Nat.mul_pos hpos hN) ?_
  rw [← Units.val_pow_eq_pow_val, hpow, Units.val_pow_eq_pow_val, ← mem_algebraicClosure_iff]
  exact pow_mem (mem_algebraicClosure_iff.2 hloc) _

end GlobalTheory
