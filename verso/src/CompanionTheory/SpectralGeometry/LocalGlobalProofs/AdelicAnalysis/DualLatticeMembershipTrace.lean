import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (algebraMap F (A F)) B y i).symm`.
-/
theorem Bf_mulVec_toA {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (y : ι → F) : Bf B *ᵥ toA y = toA (B *ᵥ y) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap F (A F)) B y i).symm

/- English proof (translation)
Use `choose m hm using h`. Establish `hr : (r : F) = ∑ v, ((b.repr r v : ℤ) : F) * (b v : F)` using `by conv_lhs => rw [← b.sum_repr r]`. Simplify using `[map_sum]`. Use `⟨∑ v, b.repr r v * m v, ?_⟩` and prove the remaining obligations. Rewrite using `[hr, Finset.mul_sum, map_sum]`.

Use `push_cast`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Establish `e : (N : F) * c * (((b.repr r v : ℤ) : F) * (b v : F)) = (((b.repr r v : ℤ) : ℚ) * (N : ℚ)) • ((b v : F) * c)`. Rewrite using `[Algebra.smul_def]`. Simplify using `only [eq_ratCast, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_smul, smul_eq_mul, mul_assoc, hm v]`.
-/
theorem trace_int_of_basis {F : Type} [Field F] [NumberField F]
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ) (c : F)
    (h : ∀ v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * c) = m) (r : 𝓞 F) :
    ∃ n : ℤ, Algebra.trace ℚ F ((N : F) * c * (r : F)) = n := by
  choose m hm using h
  have hr : (r : F) = ∑ v, ((b.repr r v : ℤ) : F) * (b v : F) := by
    conv_lhs => rw [← b.sum_repr r]
    simp [map_sum]
  refine ⟨∑ v, b.repr r v * m v, ?_⟩
  rw [hr, Finset.mul_sum, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  have e : (N : F) * c * (((b.repr r v : ℤ) : F) * (b v : F)) =
      (((b.repr r v : ℤ) : ℚ) * (N : ℚ)) • ((b v : F) * c) := by
    rw [Algebra.smul_def]
    simp only [eq_ratCast, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]
    ring
  rw [e, map_smul, smul_eq_mul, mul_assoc, hm v]

/- English proof (translation)
Introduce `F _ _ ψ hψ ι _ _ B b N _ y`. Take `⟨-, hall⟩` from `GlobalTheory.T.standard_adelic_character F`. Take `⟨-, -, hchar⟩` from `hall ψ hψ`. Establish `hBy` using `Bf_mulVec_toA B y`. Prove the components needed by the constructor for the conclusion.

Introduce `h i v`. Establish `h1 : ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1`. Introduce `x hx`. Establish `hmem : (Pi.single i ((N : A F) * x) : ι → A F) ∈ latN F ι N`. Use `fun j => ?_` and prove the remaining obligations.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Conclude with `⟨x, hx, by simp⟩`. Conclude with `⟨0, oh_zero, by simp [Pi.single_eq_of_ne hj]⟩`. Establish `h2 : ψ ((Pi.single i ((N : A F) * x) : ι → A F) ⬝ᵥ (Bf B *ᵥ toA y)) = 1` using `h _ hmem`.

Rewrite `h2` using `[hBy, single_dotProduct]`. Rewrite using `[← h2, map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]`. Use `congr 1`. Simplify using `only [toA]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨n, hn⟩` from `(hchar _).mp h1 (b v)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn]`. Establish `e : (N : F) * (B *ᵥ y) i * (b v : F) = (N : ℚ) • ((b v : F) * (B *ᵥ y) i)`. Rewrite using `[Algebra.smul_def]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_smul, smul_eq_mul]`. Introduce `h x hx`. Establish `h1 : ∀ i, ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1` using `fun i => (hchar _).mpr (trace_int_of_basis b N _ (h i))`.

Use `show ψ (x ⬝ᵥ (Bf B *ᵥ toA y)) = 1`. Rewrite using `[hBy, dotProduct]`. Establish `h2 : ∀ s : Finset ι, ψ (∑ i ∈ s, x i * toA (B *ᵥ y) i) = 1`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, AddChar.map_add_eq_mul, ih, mul_one]`. Take `⟨x', hx', e⟩` from `hx i`. Rewrite using `[e, ← h1 i x' hx', map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]`.

Use `congr 1`. Simplify using `only [toA]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h2 Finset.univ`.
-/
theorem toA_mem_perp_latN_iff : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ), IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), 0 < N → ∀ y : ι → F, toA y ∈ perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F)) ↔ ∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m := by
  intro F _ _ ψ hψ ι _ _ B b N _ y
  obtain ⟨-, hall⟩ := GlobalTheory.T.standard_adelic_character F
  obtain ⟨-, -, hchar⟩ := hall ψ hψ
  have hBy := Bf_mulVec_toA B y
  constructor
  · intro h i v
    have h1 : ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1 := by
      intro x hx
      have hmem : (Pi.single i ((N : A F) * x) : ι → A F) ∈ latN F ι N := by
        refine fun j => ?_
        by_cases hj : j = i
        · subst hj
          exact ⟨x, hx, by simp⟩
        · exact ⟨0, oh_zero, by simp [Pi.single_eq_of_ne hj]⟩
      have h2 : ψ ((Pi.single i ((N : A F) * x) : ι → A F) ⬝ᵥ (Bf B *ᵥ toA y)) = 1 := h _ hmem
      rw [hBy, single_dotProduct] at h2
      rw [← h2, map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]
      congr 1
      simp only [toA]
      ring
    obtain ⟨n, hn⟩ := (hchar _).mp h1 (b v)
    refine ⟨n, ?_⟩
    rw [← hn]
    have e : (N : F) * (B *ᵥ y) i * (b v : F) = (N : ℚ) • ((b v : F) * (B *ᵥ y) i) := by
      rw [Algebra.smul_def]
      push_cast
      ring
    rw [e, map_smul, smul_eq_mul]
  · intro h x hx
    have h1 : ∀ i, ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1 :=
      fun i => (hchar _).mpr (trace_int_of_basis b N _ (h i))
    show ψ (x ⬝ᵥ (Bf B *ᵥ toA y)) = 1
    rw [hBy, dotProduct]
    have h2 : ∀ s : Finset ι, ψ (∑ i ∈ s, x i * toA (B *ᵥ y) i) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, ih, mul_one]
        obtain ⟨x', hx', e⟩ := hx i
        rw [e, ← h1 i x' hx', map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]
        congr 1
        simp only [toA]
        ring
    exact h2 Finset.univ

end GlobalTheory.CompanionTheory.SW.ThW
