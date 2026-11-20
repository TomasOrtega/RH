import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

open Polynomial in

/- English proof (translation)
Take `⟨hfg, hspan⟩` from `hL`. Use `haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hfg`. Set `f : Module.End O L` to `(LinearMap.mulLeft O g).restrict hg`. Establish `hpow : ∀ (n : ℕ) (y : L), ((f ^ n) y : A) = g ^ n * y`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro y`. Simplify using the standard rewrite rules. Consider the case `succ n ih => intro y`. Rewrite using `[pow_succ', Module.End.mul_apply, pow_succ', mul_assoc, ← ih]`.

Both sides reduce to the same expression. Establish `hact : ∀ (q : O[X]) (y : L), ((aeval f q) y : A) = aeval g q * y`. Introduce `q y`. Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp' hq' => simp [add_mul, hp', hq']`.

Consider the case `monomial n c => simp [aeval_monomial, hpow, Algebra.smul_def, mul_assoc]`. Take `⟨p, hmon, hp⟩` from `LinearMap.exists_monic_and_aeval_eq_zero O f`. Establish `hzero : ∀ y ∈ Submodule.span E (L : Set A), aeval g p * y = 0`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem x hx => rw [← hact p ⟨x, hx⟩, hp]`. Both sides reduce to the same expression. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]`. Consider the case `smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]`.

Use `⟨p, hmon, ?_⟩` and prove the remaining obligations. Establish `h1` using `hzero 1 (hspan ▸ Submodule.mem_top)`. Rewrite `h1` using `[mul_one]`. Rewrite using `[← aeval_def]` and apply the resulting hypothesis.
-/
theorem _root_.GlobalTheory.UnitLemma.isIntegral_of_isLat_stable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (L : Submodule O A) (hL : _root_.GlobalTheory.UnitLemma.IsLat O E L) (g : A) (hg : ∀ y ∈ L, g * y ∈ L) :
    IsIntegral O g := by
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hfg
  let f : Module.End O L := (LinearMap.mulLeft O g).restrict hg
  have hpow : ∀ (n : ℕ) (y : L), ((f ^ n) y : A) = g ^ n * y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih => intro y; rw [pow_succ', Module.End.mul_apply, pow_succ', mul_assoc, ← ih]; rfl
  have hact : ∀ (q : O[X]) (y : L), ((aeval f q) y : A) = aeval g q * y := by
    intro q y
    induction q using Polynomial.induction_on' with
    | add p q hp' hq' => simp [add_mul, hp', hq']
    | monomial n c => simp [aeval_monomial, hpow, Algebra.smul_def, mul_assoc]
  obtain ⟨p, hmon, hp⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hzero : ∀ y ∈ Submodule.span E (L : Set A), aeval g p * y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => rw [← hact p ⟨x, hx⟩, hp]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]
  refine ⟨p, hmon, ?_⟩
  have h1 := hzero 1 (hspan ▸ Submodule.mem_top)
  rw [mul_one] at h1
  rwa [← aeval_def]

open Polynomial in
/- English proof (translation)
Unfold `_root_.GlobalTheory.UnitLemma.InvAlg.N _root_.GlobalTheory.UnitLemma.orbSum _root_.GlobalTheory.UnitLemma.InvAlg.X`. Use `finsum_eq_zero_of_forall_eq_zero fun o => absurd ?_ hB` and prove the remaining obligations. Take `⟨hfull, hstab, -⟩` from `(Quot.out o).2`. Conclude with `_root_.GlobalTheory.UnitLemma.isIntegral_of_isLat_stable _ hfull _ hstab`.
-/
private lemma latticeCount_eq_zero_of_not_isIntegral_lemma (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (hB : ¬ IsIntegral K.O B.g) (k : B.Cl) :
    B.N k.rep = 0 := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.N _root_.GlobalTheory.UnitLemma.orbSum _root_.GlobalTheory.UnitLemma.InvAlg.X
  refine finsum_eq_zero_of_forall_eq_zero fun o => absurd ?_ hB
  obtain ⟨hfull, hstab, -⟩ := (Quot.out o).2
  exact _root_.GlobalTheory.UnitLemma.isIntegral_of_isLat_stable _ hfull _ hstab

open Polynomial in
/- English proof (translation)
Unfold `_root_.GlobalTheory.UnitLemma.InvAlg.stSum`. Conclude with `finsum_eq_zero_of_forall_eq_zero fun k => latticeCount_eq_zero_of_not_isIntegral_lemma K B hB k`.
-/
private lemma stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (hB : ¬ IsIntegral K.O B.g) :
    B.stSum = 0 := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.stSum
  exact finsum_eq_zero_of_forall_eq_zero fun k => latticeCount_eq_zero_of_not_isIntegral_lemma K B hB k

open Polynomial in

/- English proof (translation)
Introduce `K B₁ B₂ h`. Establish `hprod : ¬ IsIntegral K.O (B₁.prod B₂).g`. Introduce `hi`. Establish `hi' : IsIntegral K.O ((B₁.g, B₂.g) : B₁.A × B₂.A)` using `hi`. Apply `h` to reduce the goal to its premises.

Conclude with `⟨hi'.map (AlgHom.fst K.O B₁.A B₂.A), hi'.map (AlgHom.snd K.O B₁.A B₂.A)⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.UnitLemma.InvAlg.kapSum`. Use `finsum_eq_zero_of_forall_eq_zero fun k => ?_` and prove the remaining obligations. Rewrite using `[latticeCount_eq_zero_of_not_isIntegral_lemma K _ hprod k, mul_zero]`.

Distinguish the cases in `h₁ : IsIntegral K.O B₁.g`. Rewrite using `[stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 K B₂ fun h₂ => h ⟨h₁, h₂⟩, mul_zero]`. Rewrite using `[stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 K B₁ h₁, zero_mul]`.
-/
theorem _root_.GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral :
    ∀ (K : _root_.GlobalTheory.UnitLemma.UQ) (B₁ B₂ : _root_.GlobalTheory.UnitLemma.InvAlg K),
      ¬ (IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g) →
      _root_.GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ = 0 ∧
        B₁.stSum * B₂.stSum = 0 := by
  intro K B₁ B₂ h
  have hprod : ¬ IsIntegral K.O (B₁.prod B₂).g := by
    intro hi
    have hi' : IsIntegral K.O ((B₁.g, B₂.g) : B₁.A × B₂.A) := hi
    apply h
    exact ⟨hi'.map (AlgHom.fst K.O B₁.A B₂.A), hi'.map (AlgHom.snd K.O B₁.A B₂.A)⟩
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.InvAlg.kapSum
    refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
    rw [latticeCount_eq_zero_of_not_isIntegral_lemma K _ hprod k, mul_zero]
  · by_cases h₁ : IsIntegral K.O B₁.g
    · rw [stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 K B₂ fun h₂ => h ⟨h₁, h₂⟩, mul_zero]
    · rw [stableLatticeCountSum_eq_zero_of_not_isIntegral_lemma_2 K B₁ h₁, zero_mul]

end GlobalTheory.UnitLemma
