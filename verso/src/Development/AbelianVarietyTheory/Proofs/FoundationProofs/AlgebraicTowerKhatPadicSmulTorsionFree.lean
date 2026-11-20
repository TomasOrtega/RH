import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowPropertiesStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

/- English proof (translation)
Use `haveI : NeZero l := ⟨hl.ne'⟩`. Take `⟨ω, hω⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω l`. Establish `hω' : IsPrimitiveRoot (algebraMap Ω K ω) l` using `hω.map_of_injective (algebraMap Ω K).injective`. Establish `hζK : (ζ : K) ^ l = 1` using `by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]`. Take `⟨i, -, hi⟩` from `hω'.eq_pow_of_pow_eq_one hζK`.

Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (ω ^ i) hm`. Establish `hz0 : algebraMap Ω K z ≠ 0`. Introduce `h0`. Establish `: (ζ : K) = 0` using `by rw [← hi, ← map_pow, ← hz, map_pow, h0, zero_pow hm.ne']`. Conclude with `ζ.ne_zero this`.

Use `⟨Units.mk0 _ hz0, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz, map_pow, hi]`.
-/
theorem rootOfUnity_pow {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field K] [Algebra Ω K]
    (l : ℕ) (hl : 0 < l) (ζ : Kˣ) (hζ : ζ ^ l = 1) (m : ℕ) (hm : 0 < m) : ∃ η : Kˣ, ζ = η ^ m := by
  haveI : NeZero l := ⟨hl.ne'⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hω' : IsPrimitiveRoot (algebraMap Ω K ω) l := hω.map_of_injective (algebraMap Ω K).injective
  have hζK : (ζ : K) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  obtain ⟨i, -, hi⟩ := hω'.eq_pow_of_pow_eq_one hζK
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ω ^ i) hm
  have hz0 : algebraMap Ω K z ≠ 0 := by
    intro h0
    have : (ζ : K) = 0 := by rw [← hi, ← map_pow, ← hz, map_pow, h0, zero_pow hm.ne']
    exact ζ.ne_zero this
  refine ⟨Units.mk0 _ hz0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz, map_pow, hi]

/- English proof (translation)
Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. It suffices to establish `hn : ∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0 by`. Apply `AdicCompletion.ext` to reduce the goal to its premises. Introduce `n`. Rewrite using `[← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, hn, map_zero]`.

Introduce `n`. Take `⟨hsurj, -, -, -, -, -, -⟩` from `GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l (n + 1)`. Take `⟨-, hker, hmul, hone, -, -, -⟩` from `GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l (n + 1)`. Take `⟨-, hker0, -, hone0, -, -, -⟩` from `GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n`. Take `⟨-, -, -, -, -, -, hred⟩` from `GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n`.

Take `⟨f, hf⟩` from `hsurj (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x)`. Establish `hpow : ∀ k : ℕ, X.cls l (n + 1) (f ^ k) = k • X.cls l (n + 1) f`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [hone]`.

Consider the case `succ k ih => rw [pow_succ f k, hmul, ih, succ_nsmul]`. Establish `h1 : X.cls l (n + 1) (f ^ l) = X.cls l (n + 1) 1`. Rewrite using `[hpow, hone, hf, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← map_smul, hx, map_zero]`. Take `⟨g, hg⟩` from `(hker _ _).1 h1`. Rewrite `hg` using `[one_mul]`.

Use `set ζ : X.Kˣ := f * (g ^ (l ^ n))⁻¹ with hζdef`. Establish `hζ : ζ ^ l = 1`. Rewrite using `[hζdef, mul_pow, hg, inv_pow, ← pow_mul, ← pow_succ, mul_inv_cancel]`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Take `⟨η, hη⟩` from `rootOfUnity_pow (Ω := Ω) l hl ζ hζ (l ^ n) (pow_pos hl n)`.

Establish `hf' : f = 1 * (η * g) ^ (l ^ n)`. Rewrite using `[one_mul, mul_pow, ← hη, hζdef, inv_mul_cancel_right]`. Rewrite using `[hred x f hf.symm, ← hone0]`. Conclude with `(hker0 _ _).2 ⟨_, hf'⟩`.
-/
theorem khat_l_smul_eq_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    [IsAlgClosed Ω] (x : X.Khat l) (hx : (l : ℤ_[l]) • x = 0) : x = 0 := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  suffices hn : ∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0 by
    apply AdicCompletion.ext
    intro n
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, hn, map_zero]
  intro n
  obtain ⟨hsurj, -, -, -, -, -, -⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l (n + 1)
  obtain ⟨-, hker, hmul, hone, -, -, -⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l (n + 1)
  obtain ⟨-, hker0, -, hone0, -, -, -⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n
  obtain ⟨-, -, -, -, -, -, hred⟩ := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n
  obtain ⟨f, hf⟩ := hsurj (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x)
  have hpow : ∀ k : ℕ, X.cls l (n + 1) (f ^ k) = k • X.cls l (n + 1) f := by
    intro k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ f k, hmul, ih, succ_nsmul]
  have h1 : X.cls l (n + 1) (f ^ l) = X.cls l (n + 1) 1 := by
    rw [hpow, hone, hf, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← map_smul, hx, map_zero]
  obtain ⟨g, hg⟩ := (hker _ _).1 h1
  rw [one_mul] at hg
  set ζ : X.Kˣ := f * (g ^ (l ^ n))⁻¹ with hζdef
  have hζ : ζ ^ l = 1 := by
    rw [hζdef, mul_pow, hg, inv_pow, ← pow_mul, ← pow_succ, mul_inv_cancel]
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨η, hη⟩ := rootOfUnity_pow (Ω := Ω) l hl ζ hζ (l ^ n) (pow_pos hl n)
  have hf' : f = 1 * (η * g) ^ (l ^ n) := by
    rw [one_mul, mul_pow, ← hη, hζdef, inv_mul_cancel_right]
  rw [hred x f hf.symm, ← hone0]
  exact (hker0 _ _).2 ⟨_, hf'⟩

/- English proof (translation)
Establish `key : ∀ k : ℕ, ∀ y : X.Khat l, ((l : ℤ_[l]) ^ k) • y = 0 → y = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro y hy`. Simplify using `using hy`.

Consider the case `succ k ih`. Introduce `y hy`. Apply `khat_l_smul_eq_zero X l` to reduce the goal to its premises. Apply `ih` to reduce the goal to its premises. Rewrite using `[smul_smul, ← pow_succ]`.

Conclude with `hy`. Apply `key c.valuation` to reduce the goal to its premises. Establish `h` using `PadicInt.unitCoeff_spec hc`. Establish `: ((PadicInt.unitCoeff hc)⁻¹ : ℤ_[l]ˣ) • (c • x) = 0` using `by rw [hcx, smul_zero]`. Rewrite `this` using `[Units.smul_def, smul_smul]`.

Use `nth_rw 2 [h] at this`. Rewrite `this` using `[← mul_assoc, Units.inv_mul, one_mul]`. Then use the resulting hypothesis.
-/
theorem khat_torsionFree (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    [IsAlgClosed Ω] (c : ℤ_[l]) (x : X.Khat l) (hc : c ≠ 0) (hcx : c • x = 0) : x = 0 := by
  have key : ∀ k : ℕ, ∀ y : X.Khat l, ((l : ℤ_[l]) ^ k) • y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      apply khat_l_smul_eq_zero X l
      apply ih
      rw [smul_smul, ← pow_succ]; exact hy
  apply key c.valuation
  have h := PadicInt.unitCoeff_spec hc
  have : ((PadicInt.unitCoeff hc)⁻¹ : ℤ_[l]ˣ) • (c • x) = 0 := by rw [hcx, smul_zero]
  rw [Units.smul_def, smul_smul] at this
  nth_rw 2 [h] at this
  rwa [← mul_assoc, Units.inv_mul, one_mul] at this

end GlobalTheory.KZ.H3
