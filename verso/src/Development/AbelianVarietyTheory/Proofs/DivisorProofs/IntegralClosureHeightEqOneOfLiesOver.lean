import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

/- English proof (translation)
Introduce `k F K _ _ _ _ _ _ _ _ A _ B hB p hp hp1 Q hQ hlo`. Establish `hmem : ∀ a : A, algebraMap F K (a : F) ∈ B`. Introduce `a`. Rewrite using `[hB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]`. Conclude with `isIntegral_algebraMap (R := A) (A := K) (x := a)`.

Set `f : A →+* B` to `((algebraMap F K).comp A.val.toRingHom).codRestrict B hmem`. Use `letI : Algebra A B := f.toAlgebra`. Establish `hf : ∀ a : A, ((algebraMap A B a : B) : K) = algebraMap F K (a : F)` using `fun _ => rfl`. Set `φ : B →ₐ[A] K` to `{ toRingHom := B.val.toRingHom commutes' := fun a => rfl }`. Establish `hint : Algebra.IsIntegral A B`.

Use `⟨fun b => ?_⟩` and prove the remaining obligations. Establish `key : ∀ x : K, x ∈ B → x ∈ integralClosure A K`. Introduce `x hx`. Rewrite `hx` using `[hB, Subalgebra.mem_restrictScalars]`. Conclude with `hx`.

Establish `hb : (b : K) ∈ integralClosure A K` using `key b b.2`. Rewrite using `[← isIntegral_algHom_iff φ Subtype.val_injective]`. Conclude with `hb`. Establish `hcomap : Q.comap (algebraMap A B) = p`. Use extensionality with `a`.

Conclude with `hlo a (algebraMap A B a) (hf a)`. Use `haveI := hp`. Use `haveI := hQ`. Establish `hpne : p ≠ ⊥` using `Ideal.ne_bot_of_height_eq_one hp1`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by rfl, Ideal.height_le_iff]`. Introduce `Q' hQ' hlt`. Use `haveI := hQ'`. Assume the negation of the conclusion as `hge`. Establish `hQ'ne : Q' ≠ ⊥`.

Introduce `h`. Apply `hge` to reduce the goal to its premises. Rewrite using `[h, Ideal.height_bot]`. Evaluate the numerical expressions. Establish `h1 : Q'.comap (algebraMap A B) ≠ ⊥` using `Ideal.IsIntegral.comap_ne_bot A hQ'ne`.

Establish `h2 : Q'.comap (algebraMap A B) < p` using `hcomap ▸ Ideal.IsIntegral.comap_lt_comap hlt`. Use `haveI : (Q'.comap (algebraMap A B)).IsPrime := Ideal.comap_isPrime _ _`. Establish `h3` using `Ideal.height_add_one_le_of_lt_of_isPrime h2`. Establish `h4 : 1 ≤ (Q'.comap (algebraMap A B)).height`. Rewrite using `[Order.one_le_iff_pos, pos_iff_ne_zero]`.

Conclude with `fun h => h1 (Ideal.height_eq_zero_iff_eq_bot.mp h)`. Rewrite `h3` using `[hp1]`. Establish `: (1 : ℕ∞) + 1 ≤ 1` using `(add_le_add h4 le_rfl).trans h3`. Evaluate the numerical expressions using `at this`. Rewrite using `[Order.one_le_iff_pos, pos_iff_ne_zero]`.

Introduce `h`. Rewrite `h` using `[Ideal.height_eq_zero_iff_eq_bot]`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hpne`. Establish `: algebraMap A B a ∈ Q` using `by rw [← Ideal.mem_comap, hcomap]; exact ha`. Rewrite `this` using `[h, Ideal.mem_bot]`.

Apply `ha0` to reduce the goal to its premises. Use `congrArg (fun x : B => (x : K)) this` as an intermediate fact. Simplify using `only [hf, ZeroMemClass.coe_zero] at this`. Conclude with `Subtype.ext ((algebraMap F K).injective (this.trans (map_zero _).symm))`.
-/
theorem integralClosure_height_eq_one_of_liesOver : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (A : Subalgebra k F) [IsFractionRing A F] (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 := by
  intro k F K _ _ _ _ _ _ _ _ A _ B hB p hp hp1 Q hQ hlo

  have hmem : ∀ a : A, algebraMap F K (a : F) ∈ B := by
    intro a
    rw [hB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (R := A) (A := K) (x := a)
  let f : A →+* B := ((algebraMap F K).comp A.val.toRingHom).codRestrict B hmem
  letI : Algebra A B := f.toAlgebra
  have hf : ∀ a : A, ((algebraMap A B a : B) : K) = algebraMap F K (a : F) := fun _ => rfl

  let φ : B →ₐ[A] K :=
    { toRingHom := B.val.toRingHom
      commutes' := fun a => rfl }
  have hint : Algebra.IsIntegral A B := by
    refine ⟨fun b => ?_⟩
    have key : ∀ x : K, x ∈ B → x ∈ integralClosure A K := by
      intro x hx
      rw [hB, Subalgebra.mem_restrictScalars] at hx
      exact hx
    have hb : (b : K) ∈ integralClosure A K := key b b.2
    rw [← isIntegral_algHom_iff φ Subtype.val_injective]
    exact hb

  have hcomap : Q.comap (algebraMap A B) = p := by
    ext a
    exact hlo a (algebraMap A B a) (hf a)
  haveI := hp
  haveI := hQ
  have hpne : p ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hp1
  apply le_antisymm
  · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by rfl, Ideal.height_le_iff]
    intro Q' hQ' hlt
    haveI := hQ'
    by_contra hge
    have hQ'ne : Q' ≠ ⊥ := by
      intro h
      apply hge
      rw [h, Ideal.height_bot]
      norm_num
    have h1 : Q'.comap (algebraMap A B) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot A hQ'ne
    have h2 : Q'.comap (algebraMap A B) < p := hcomap ▸ Ideal.IsIntegral.comap_lt_comap hlt
    haveI : (Q'.comap (algebraMap A B)).IsPrime := Ideal.comap_isPrime _ _
    have h3 := Ideal.height_add_one_le_of_lt_of_isPrime h2
    have h4 : 1 ≤ (Q'.comap (algebraMap A B)).height := by
      rw [Order.one_le_iff_pos, pos_iff_ne_zero]
      exact fun h => h1 (Ideal.height_eq_zero_iff_eq_bot.mp h)
    rw [hp1] at h3
    have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add h4 le_rfl).trans h3
    norm_num at this
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    intro h
    rw [Ideal.height_eq_zero_iff_eq_bot] at h
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
    have : algebraMap A B a ∈ Q := by rw [← Ideal.mem_comap, hcomap]; exact ha
    rw [h, Ideal.mem_bot] at this
    apply ha0
    have := congrArg (fun x : B => (x : K)) this
    simp only [hf, ZeroMemClass.coe_zero] at this
    exact Subtype.ext ((algebraMap F K).injective (this.trans (map_zero _).symm))

end GlobalTheory
