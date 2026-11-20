import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

/- English proof (translation)
Establish `: NeZero l` using `⟨hl.ne'⟩`. Take `⟨ω, hω⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω l`. Establish `hω' : IsPrimitiveRoot (algebraMap Ω K ω) l` using `hω.map_of_injective (algebraMap Ω K).injective`. Establish `hζK : (ζ : K) ^ l = 1` using `by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]`. Take `⟨i, -, hi⟩` from `hω'.eq_pow_of_pow_eq_one hζK`.

Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (ω ^ i) hm`. Establish `hz0 : algebraMap Ω K z ≠ 0`. Introduce `h0`. Establish `: (ζ : K) = 0` using `by rw [← hi, ← map_pow, ← hz, map_pow, h0, zero_pow hm.ne']`. Conclude with `ζ.ne_zero this`.

Use `⟨Units.mk0 _ hz0, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz, map_pow, hi]`.
-/
theorem rootOfUnity_eq_pow {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field K] [Algebra Ω K]
    (l : ℕ) (hl : 0 < l) (ζ : Kˣ) (hζ : ζ ^ l = 1) (m : ℕ) (hm : 0 < m) : ∃ η : Kˣ, ζ = η ^ m := by
  have : NeZero l := ⟨hl.ne'⟩
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
Introduce `Ω _ _ _ ε X l _ x hx`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed ℚ`. Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. It suffices to establish `hn : ∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0 by`. Apply `AdicCompletion.ext` to reduce the goal to its premises.

Introduce `n`. Rewrite using `[← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, hn, map_zero]`. Introduce `n`. Take `⟨hsurj, hker, hmul, hone, -, -, -⟩` from `H3.cls_props Ω ε X l (n + 1)`. Take `⟨-, hker0, -, hone0, -, -, hred⟩` from `H3.cls_props Ω ε X l n`.

Take `⟨f, hf⟩` from `hsurj (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x)`. Establish `hpow : ∀ k : ℕ, X.cls l (n + 1) (f ^ k) = k • X.cls l (n + 1) f`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [hone]`.

Consider the case `succ k ih => rw [pow_succ f k, hmul, ih, succ_nsmul]`. Establish `h1 : X.cls l (n + 1) (f ^ l) = X.cls l (n + 1) 1`. Rewrite using `[hpow, hone, hf, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← map_smul, hx, map_zero]`. Take `⟨g, hg⟩` from `(hker _ _).1 h1`. Rewrite `hg` using `[one_mul]`.

Use `set ζ : X.Kˣ := f * (g ^ (l ^ n))⁻¹ with hζdef`. Establish `hζ : ζ ^ l = 1`. Rewrite using `[hζdef, mul_pow, hg, inv_pow, ← pow_mul, ← pow_succ, mul_inv_cancel]`. Establish `: CharZero Ω` using `algebraRat.charZero Ω`. Take `⟨η, hη⟩` from `rootOfUnity_eq_pow (Ω := Ω) l hl ζ hζ (l ^ n) (pow_pos hl n)`.

Establish `hf' : f = 1 * (η * g) ^ (l ^ n)`. Rewrite using `[one_mul, mul_pow, ← hη, hζdef, inv_mul_cancel_right]`. Rewrite using `[hred x f hf.symm, ← hone0]`. Conclude with `(hker0 _ _).2 ⟨_, hf'⟩`.
-/
theorem khat_no_l_torsion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (x : X.Khat l), (l : ℤ_[l]) • x = 0 → x = 0 := by
  intro Ω _ _ _ ε X l _ x hx
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  suffices hn : ∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0 by
    apply AdicCompletion.ext
    intro n
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, hn, map_zero]
  intro n
  obtain ⟨hsurj, hker, hmul, hone, -, -, -⟩ := H3.cls_props Ω ε X l (n + 1)
  obtain ⟨-, hker0, -, hone0, -, -, hred⟩ := H3.cls_props Ω ε X l n
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
  have : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨η, hη⟩ := rootOfUnity_eq_pow (Ω := Ω) l hl ζ hζ (l ^ n) (pow_pos hl n)
  have hf' : f = 1 * (η * g) ^ (l ^ n) := by
    rw [one_mul, mul_pow, ← hη, hζdef, inv_mul_cancel_right]
  rw [hred x f hf.symm, ← hone0]
  exact (hker0 _ _).2 ⟨_, hf'⟩

end GlobalTheory.KZ.BettiB
