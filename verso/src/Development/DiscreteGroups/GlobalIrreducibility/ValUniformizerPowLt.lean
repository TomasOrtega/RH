import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzRedSupp

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Simplify using `only [map_mul, Module.End.mul_apply]`. Use `congr 2`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.
-/
theorem rep_conj {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (t u : G) (v : V) :
    π (t * u * t⁻¹) (π t v) = π t (π u v) := by
  simp only [map_mul, Module.End.mul_apply]
  congr 2
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Establish `h` using `GlobalTheory.FiniteGL.mem_unipRadical.1 hu`. Rewrite using `[mem_unipB]`. Use `⟨fun p q hqp => ?_, fun p => ?_⟩` and prove the remaining obligations. Use `h p q (by` as an intermediate fact. Establish `: q.val < p.val` using `hqp`.

Apply the tactic sequence `simp only [GlobalTheory.FiniteGL.twoBlocks]; split_ifs <;> omega)`. Rewrite `this` using `[Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hqp), sub_zero]`. Then use the resulting hypothesis. Use `h p p le_rfl` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem unipRadical_le_unipB {F : Type} [Field F] {n a : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical F (GlobalTheory.FiniteGL.twoBlocks n a)) : u ∈ unipB F (Fin n) := by
  have h := GlobalTheory.FiniteGL.mem_unipRadical.1 hu
  rw [mem_unipB]
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · have := h p q (by
      have : q.val < p.val := hqp
      simp only [GlobalTheory.FiniteGL.twoBlocks]; split_ifs <;> omega)
    rwa [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hqp), sub_zero] at this
  · have := h p p le_rfl
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this

/- English proof (translation)
Establish `hlt` using `GLnLocal.valuation_uniformizer_lt_one K`. Rewrite using `[map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_uniformizer_pow_lt {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (k : ℕ) {y : K} (hy : valuation K y ≤ 1) :
    valuation K ((GLnLocal.uniformizer K : K) ^ (k + 1) * y) < 1 := by
  have hlt := GLnLocal.valuation_uniformizer_lt_one K
  rw [map_mul, map_pow]
  calc valuation K (GLnLocal.uniformizer K : K) ^ (k + 1) * valuation K y
      ≤ valuation K (GLnLocal.uniformizer K : K) ^ (k + 1) := mul_le_of_le_one_right' hy
    _ = valuation K (GLnLocal.uniformizer K : K) ^ k * valuation K (GLnLocal.uniformizer K : K) := pow_succ _ _
    _ ≤ valuation K (GLnLocal.uniformizer K : K) := mul_le_of_le_one_left' (pow_le_one' hlt.le k)
    _ < 1 := hlt

/- English proof (translation)
Establish `hϖ : (GLnLocal.uniformizer K : K) ≠ 0` using `fun h => (GLnLocal.irreducible_uniformizer K).ne_zero (Subtype.ext h)`. Rewrite using `[hk, zpow_add, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, zpow_natCast, Iwasawa.coe_uniformizerUnit]`. Establish `h1 : (GLnLocal.uniformizer K : K) ^ d a ≠ 0` using `zpow_ne_zero _ hϖ`. Establish `h2 : (GLnLocal.uniformizer K : K) ^ (k + 1) ≠ 0` using `pow_ne_zero _ hϖ`. Clear the denominators using the available nonvanishing facts.
-/
theorem torus_entry {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {n : ℕ} (d : Fin n → ℤ) (a b : Fin n) (k : ℕ) (hk : d b = d a + ((k + 1 : ℕ) : ℤ)) (y : K) :
    ((Iwasawa.uniformizerUnit K ^ d a : Kˣ) : K) * ((GLnLocal.uniformizer K : K) ^ (k + 1) * y) *
      ((Iwasawa.uniformizerUnit K ^ d b : Kˣ) : K)⁻¹ = y := by
  have hϖ : (GLnLocal.uniformizer K : K) ≠ 0 := fun h =>
    (GLnLocal.irreducible_uniformizer K).ne_zero (Subtype.ext h)
  rw [hk, zpow_add, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, zpow_natCast,
    Iwasawa.coe_uniformizerUnit]
  have h1 : (GLnLocal.uniformizer K : K) ^ d a ≠ 0 := zpow_ne_zero _ hϖ
  have h2 : (GLnLocal.uniformizer K : K) ^ (k + 1) ≠ 0 := pow_ne_zero _ hϖ
  field_simp

/- English proof (translation)
Establish `hϖ : (GLnLocal.uniformizer K : K) ≠ 0` using `fun h => (GLnLocal.irreducible_uniformizer K).ne_zero (Subtype.ext h)`. Rewrite using `[hk, zpow_add, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, zpow_natCast, Iwasawa.coe_uniformizerUnit]`. Establish `h1 : (GLnLocal.uniformizer K : K) ^ d b ≠ 0` using `zpow_ne_zero _ hϖ`. Clear the denominators using the available nonvanishing facts.
-/
theorem torus_entry' {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {n : ℕ} (d : Fin n → ℤ) (a b : Fin n) (k : ℕ) (hk : d a = d b + ((k + 1 : ℕ) : ℤ)) (y : K) :
    ((Iwasawa.uniformizerUnit K ^ d a : Kˣ) : K) * y * ((Iwasawa.uniformizerUnit K ^ d b : Kˣ) : K)⁻¹ =
      (GLnLocal.uniformizer K : K) ^ (k + 1) * y := by
  have hϖ : (GLnLocal.uniformizer K : K) ≠ 0 := fun h =>
    (GLnLocal.irreducible_uniformizer K).ne_zero (Subtype.ext h)
  rw [hk, zpow_add, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, zpow_natCast,
    Iwasawa.coe_uniformizerUnit]
  have h1 : (GLnLocal.uniformizer K : K) ^ d b ≠ 0 := zpow_ne_zero _ hϖ
  field_simp

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
/- English proof (translation)
Establish `h1 : ‖i.symm y‖ < 1` using `(DzIso.valuation_lt_iff i hi (i.symm y)).1 (by rwa [RingEquiv.apply_symm_apply])`. Set `x : ℤ_[g]` to `⟨i.symm y, h1.le⟩`. Establish `hx : i (x : ℚ_[g]) = y` using `RingEquiv.apply_symm_apply i y`. Rewrite using `[← hx, hψ]`. Establish `h2 : PadicInt.toZMod x = 0`.

Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]`. Conclude with `h1`. Rewrite using `[h2, AddChar.map_zero_eq_one]`.
-/
theorem psi_eq_one (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y < 1) : ψ y = 1 := by
  have h1 : ‖i.symm y‖ < 1 :=
    (DzIso.valuation_lt_iff i hi (i.symm y)).1 (by rwa [RingEquiv.apply_symm_apply])
  let x : ℤ_[g] := ⟨i.symm y, h1.le⟩
  have hx : i (x : ℚ_[g]) = y := RingEquiv.apply_symm_apply i y
  rw [← hx, hψ]
  have h2 : PadicInt.toZMod x = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    exact h1
  rw [h2, AddChar.map_zero_eq_one]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, ψ₀ z ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `h0 (AddChar.ext ψ₀ 1 fun z => (h z).trans (AddChar.one_apply z).symm)`. Use `⟨(z.val : ℤ_[g]), ?_⟩` and prove the remaining obligations.

Rewrite using `[hψ, map_natCast, ZMod.natCast_zmod_val]`. Conclude with `hz`.
-/
theorem exists_psi_ne_one (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1) :
    ∃ x : ℤ_[g], ψ (i (x : ℚ_[g])) ≠ 1 := by
  obtain ⟨z, hz⟩ : ∃ z, ψ₀ z ≠ 1 := by
    by_contra h
    push Not at h
    exact h0 (AddChar.ext ψ₀ 1 fun z => (h z).trans (AddChar.one_apply z).symm)
  refine ⟨(z.val : ℤ_[g]), ?_⟩
  rw [hψ, map_natCast, ZMod.natCast_zmod_val]
  exact hz

include hi in
/- English proof (translation)
Take `⟨κ, h1, rfl⟩` from `DzIso.exists_of_mem_KOne i hi hk`. Rewrite using `[← hφ, h1, map_one]`. Both sides reduce to the same expression.
-/
theorem fix_of_mem_KOne {n : ℕ} (τ : FDRep ℂ (Gn g n)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    {k : GL (Fin n) (w.adicCompletion E)} (hk : k ∈ KOne (w.adicCompletion E) (Fin n)) (x : τ) :
    π k (φ x) = φ x := by
  obtain ⟨κ, h1, rfl⟩ := DzIso.exists_of_mem_KOne i hi hk
  rw [← hφ, h1, map_one]
  rfl

end DiscreteGroups.sglob.DzRed
