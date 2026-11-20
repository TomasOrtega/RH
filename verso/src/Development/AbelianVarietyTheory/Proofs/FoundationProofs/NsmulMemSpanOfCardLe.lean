import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.CycIndex

/- English proof (translation)
Introduce `l _ c C r`. Establish `hl0 : ((l : ℕ) : c.O) ≠ 0`. Introduce `h0`. Establish `h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0` using `by rw [h0]; rfl`. Establish `: ((l : ℕ) : PadicAlgCl l) = 0` using `by simpa using h'`.

Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this`. Establish `hfin : ∀ k : ℕ, Finite (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ k))` using `fun k => (UpperTheory.V.X.So.levFacts l c.O _ (pow_ne_zero k hl0) _ ⟨LinearEquiv.refl _ _⟩).1`. Use `⟨(C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ r))).factorial, Nat.factorial_pos _, ?_⟩` and prove the remaining obligations. Introduce `n H _ _ _ hkill hcard z hann h`. Use `set L : c.O := ((l : ℕ) : c.O) with hL`.

Use `haveI := hfin n`. Use `haveI := hfin r`. Set `f : UpperTheory.V.X.Lev (L ^ n) →ₗ[c.O] H` to `(Ideal.span {L ^ n}).liftQ (LinearMap.toSpanSingleton c.O H z) (by`. Rewrite using `[Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Conclude with `hkill z)`.

Establish `hf : ∀ x : c.O, f (UpperTheory.V.X.Lev.mk (L ^ n) x) = x • z` using `fun x => rfl`. Set `g : UpperTheory.V.X.Lev (L ^ r) →ₗ[c.O] UpperTheory.V.X.Lev (L ^ n)` to `(Ideal.span {L ^ r}).liftQ ((L ^ (n - r)) • UpperTheory.V.X.Lev.mk (L ^ n)) (by`. Rewrite using `[Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul, UpperTheory.V.X.Lev.mk_eq_zero, smul_eq_mul, ← pow_add]`. Conclude with `pow_dvd_pow _ (by omega))`. Establish `hg : ∀ w : c.O, g (UpperTheory.V.X.Lev.mk (L ^ r) w) = UpperTheory.V.X.Lev.mk (L ^ n) (L ^ (n - r) * w)`.

Introduce `w`. Use `show (L ^ (n - r)) • UpperTheory.V.X.Lev.mk (L ^ n) w = _`. Rewrite using `[← map_smul, smul_eq_mul]`. Establish `hker : LinearMap.ker f ≤ LinearMap.range g`. Introduce `y hy`.

Take `⟨x, rfl⟩` from `UpperTheory.V.X.Lev.mk_surjective (L ^ n) y`. Rewrite `hy` using `[LinearMap.mem_ker, hf]`. Take `⟨w, rfl⟩` from `hann x hy`. Conclude with `⟨UpperTheory.V.X.Lev.mk (L ^ r) w, hg w⟩`. Establish `hK : Nat.card (LinearMap.ker f) ≤ Nat.card (UpperTheory.V.X.Lev (L ^ r))` using `(Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hker)).trans (Nat.card_le_card_of_surjective _ g.surjective_rangeRestrict)`.

Establish `h1 : Nat.card (UpperTheory.V.X.Lev (L ^ n)) = Nat.card (LinearMap.ker f) * Nat.card (UpperTheory.V.X.Lev (L ^ n) ⧸ LinearMap.ker f)` using `Submodule.card_eq_card_quotient_mul_card _`. Rewrite `h1` using `[Nat.card_congr f.quotKerEquivRange.toEquiv]`. Establish `h2 : Nat.card H = Nat.card (LinearMap.range f) * Nat.card (H ⧸ LinearMap.range f)` using `Submodule.card_eq_card_quotient_mul_card _`. Establish `hSpos : 0 < Nat.card (LinearMap.range f)` using `Nat.card_pos`. Establish `hQ : Nat.card (H ⧸ LinearMap.range f) ≤ C * Nat.card (UpperTheory.V.X.Lev (L ^ r))`.

Establish `: Nat.card (H ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) ≤ (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))) * Nat.card (LinearMap.range f)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, mul_comm]`. Use `_ ≤ C * Nat.card (UpperTheory.V.X.Lev (L ^ n)) := hcard`. Use `_ = C * (Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f)) := by rw [h1]`.

Use `_ ≤ C * (Nat.card (UpperTheory.V.X.Lev (L ^ r)) * Nat.card (LinearMap.range f)) := by gcongr`. Use `_ = _ := by ring`. Conclude with `Nat.le_of_mul_le_mul_right this hSpos`. Use `haveI : Finite (H ⧸ LinearMap.range f) := Finite.of_surjective _ (Submodule.mkQ_surjective _)`. Establish `hdvd : Nat.card (H ⧸ LinearMap.range f) ∣ (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))).factorial` using `Nat.dvd_factorial Nat.card_pos hQ`.

Take `⟨k, hk⟩` from `hdvd`. Establish `hmem : (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))).factorial • h ∈ LinearMap.range f`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_nsmul, hk, mul_comm, mul_nsmul, card_nsmul_eq_zero']`. Take `⟨y, hy⟩` from `hmem`. Take `⟨x, rfl⟩` from `UpperTheory.V.X.Lev.mk_surjective (L ^ n) y`.

Conclude with `⟨x, by rw [← hy, hf]⟩`.
-/
theorem nsmul_mem_span_of_card_le : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (C r : ℕ), ∃ m : ℕ, 0 < m ∧ ∀ (n : ℕ) (H : Type) [AddCommGroup H] [Module c.O H] [Finite H], (∀ h : H, ((l : ℕ) : c.O) ^ n • h = 0) → Nat.card H ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) → ∀ z : H, (∀ x : c.O, x • z = 0 → ((l : ℕ) : c.O) ^ (n - r) ∣ x) → ∀ h : H, ∃ x : c.O, m • h = x • z := by
  intro l _ c C r
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h0
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h0]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hfin : ∀ k : ℕ, Finite (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ k)) := fun k =>
    (UpperTheory.V.X.So.levFacts l c.O _ (pow_ne_zero k hl0) _ ⟨LinearEquiv.refl _ _⟩).1
  refine ⟨(C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ r))).factorial, Nat.factorial_pos _, ?_⟩
  intro n H _ _ _ hkill hcard z hann h
  set L : c.O := ((l : ℕ) : c.O) with hL
  haveI := hfin n
  haveI := hfin r
  let f : UpperTheory.V.X.Lev (L ^ n) →ₗ[c.O] H :=
    (Ideal.span {L ^ n}).liftQ (LinearMap.toSpanSingleton c.O H z) (by
      rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hkill z)
  have hf : ∀ x : c.O, f (UpperTheory.V.X.Lev.mk (L ^ n) x) = x • z := fun x => rfl
  let g : UpperTheory.V.X.Lev (L ^ r) →ₗ[c.O] UpperTheory.V.X.Lev (L ^ n) :=
    (Ideal.span {L ^ r}).liftQ ((L ^ (n - r)) • UpperTheory.V.X.Lev.mk (L ^ n)) (by
      rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul,
        UpperTheory.V.X.Lev.mk_eq_zero, smul_eq_mul, ← pow_add]
      exact pow_dvd_pow _ (by omega))
  have hg : ∀ w : c.O, g (UpperTheory.V.X.Lev.mk (L ^ r) w) = UpperTheory.V.X.Lev.mk (L ^ n) (L ^ (n - r) * w) := by
    intro w
    show (L ^ (n - r)) • UpperTheory.V.X.Lev.mk (L ^ n) w = _
    rw [← map_smul, smul_eq_mul]
  have hker : LinearMap.ker f ≤ LinearMap.range g := by
    intro y hy
    obtain ⟨x, rfl⟩ := UpperTheory.V.X.Lev.mk_surjective (L ^ n) y
    rw [LinearMap.mem_ker, hf] at hy
    obtain ⟨w, rfl⟩ := hann x hy
    exact ⟨UpperTheory.V.X.Lev.mk (L ^ r) w, hg w⟩
  have hK : Nat.card (LinearMap.ker f) ≤ Nat.card (UpperTheory.V.X.Lev (L ^ r)) :=
    (Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hker)).trans
      (Nat.card_le_card_of_surjective _ g.surjective_rangeRestrict)
  have h1 : Nat.card (UpperTheory.V.X.Lev (L ^ n)) =
      Nat.card (LinearMap.ker f) * Nat.card (UpperTheory.V.X.Lev (L ^ n) ⧸ LinearMap.ker f) :=
    Submodule.card_eq_card_quotient_mul_card _
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have h2 : Nat.card H = Nat.card (LinearMap.range f) * Nat.card (H ⧸ LinearMap.range f) :=
    Submodule.card_eq_card_quotient_mul_card _
  have hSpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  have hQ : Nat.card (H ⧸ LinearMap.range f) ≤ C * Nat.card (UpperTheory.V.X.Lev (L ^ r)) := by
    have : Nat.card (H ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) ≤
        (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))) * Nat.card (LinearMap.range f) := by
      calc Nat.card (H ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) = Nat.card H := by
              rw [h2, mul_comm]
        _ ≤ C * Nat.card (UpperTheory.V.X.Lev (L ^ n)) := hcard
        _ = C * (Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f)) := by rw [h1]
        _ ≤ C * (Nat.card (UpperTheory.V.X.Lev (L ^ r)) * Nat.card (LinearMap.range f)) := by gcongr
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this hSpos
  haveI : Finite (H ⧸ LinearMap.range f) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hdvd : Nat.card (H ⧸ LinearMap.range f) ∣ (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))).factorial :=
    Nat.dvd_factorial Nat.card_pos hQ
  obtain ⟨k, hk⟩ := hdvd
  have hmem : (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))).factorial • h ∈ LinearMap.range f := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_nsmul, hk, mul_comm, mul_nsmul,
      card_nsmul_eq_zero']
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨x, rfl⟩ := UpperTheory.V.X.Lev.mk_surjective (L ^ n) y
  exact ⟨x, by rw [← hy, hf]⟩

end GlobalTheory.CycIndex
