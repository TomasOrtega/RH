import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StandardDeterminantUnit

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Survey.StandardDeterminantUnits

open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

omit [StarRing E] in
/- English proof (translation)
Take `⟨r, s, hs, hsa⟩` from `h`. Establish `h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1` using `(P.valuation_eq_one_iff_notMem (K := E)).2 hs`. Establish `h2 : P.valuation E (algebraMap (𝓞 E) E r) ≤ 1` using `P.valuation_le_one r`. Rewrite `h2` using `[← hsa, map_mul, h1, one_mul]`. Conclude with `h2`.
-/
theorem val_le_one_of_intAt {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : IntAt P a) : P.valuation E a ≤ 1 := by
  obtain ⟨r, s, hs, hsa⟩ := h
  have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
    (P.valuation_eq_one_iff_notMem (K := E)).2 hs
  have h2 : P.valuation E (algebraMap (𝓞 E) E r) ≤ 1 := P.valuation_le_one r
  rw [← hsa, map_mul, h1, one_mul] at h2
  exact h2

/- English proof (translation)
Rewrite using `[stdAt, mem_localization_standardLattice]`. Introduce `i`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `using IntAt.coe P (1 : 𝓞 E)`.

Simplify `IntAt.coe P (0 : 𝓞 E)` using `[Pi.single_apply, hij]`.
-/
private theorem single_one_mem_stdAt (P : HeightOneSpectrum (𝓞 E)) (j : Fin n) :
    (Pi.single j (1 : E) : Sp E n) ∈ stdAt E n P := by
  rw [stdAt, mem_localization_standardLattice]
  intro i
  by_cases hij : i = j
  · subst hij
    simpa using IntAt.coe P (1 : 𝓞 E)
  · simpa [Pi.single_apply, hij] using IntAt.coe P (0 : 𝓞 E)

/- English proof (translation)
Rewrite using `[← LinearMap.det_toMatrix', ← Valuation.mem_integer_iff, Matrix.det_apply']`. Use `Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _) (Subring.prod_mem _ fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Valuation.mem_integer_iff, LinearMap.toMatrix'_apply]`. Establish `hx` using `hg _ (single_one_mem_stdAt P i)`. Rewrite `hx` using `[stdAt, mem_localization_standardLattice]`.

Conclude with `val_le_one_of_intAt (hx (σ i))`.
-/
theorem val_det_le_one {P : HeightOneSpectrum (𝓞 E)} (g : Sp E n →ₗ[E] Sp E n)
    (hg : ∀ x ∈ stdAt E n P, g x ∈ stdAt E n P) : P.valuation E (LinearMap.det g) ≤ 1 := by

  rw [← LinearMap.det_toMatrix', ← Valuation.mem_integer_iff, Matrix.det_apply']
  refine Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
    (Subring.prod_mem _ fun i _ => ?_)
  rw [Valuation.mem_integer_iff, LinearMap.toMatrix'_apply]
  have hx := hg _ (single_one_mem_stdAt P i)
  rw [stdAt, mem_localization_standardLattice] at hx
  exact val_le_one_of_intAt (hx (σ i))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx y hy`. Rewrite `hx`, `hy` using `[mem_locP]`. Take `⟨t, ht, htx⟩` from `hx`. Take `⟨s, hs, hsy⟩` from `hy`.

Establish `htd : t • x ∈ dual (hStd E n) N` using `by rw [hu]; exact htx`. Take `⟨r, hr⟩` from `Submodule.mem_one.1 ((mem_dual N _).1 htd _ hsy)`. Use `⟨r, cO E s * t, ?_, ?_⟩` and prove the remaining obligations. Introduce `hmul`. Break down `(conjPrime₂ P).isPrime.mem_or_mem hmul with h1 | h1` into its components or cases.

Rewrite `h1` using `[mem_conjP, cO_cO]`. Conclude with `hs h1`. Conclude with `ht h1`. Rewrite using `[hr, hStd_osmul_left, smul_smul, LinearMap.map_smul_of_tower, Algebra.smul_def]`. Introduce `hx classical`.

Take `⟨S, hS⟩` from `hl`. Establish `hz : ∀ z ∈ S, ∃ s : 𝓞 E, s ∉ (conjPrime₂ P).asIdeal ∧ hStd E n z (s • x) ∈ (1 : Submodule (𝓞 E) E)`. Introduce `z hzS`. Take `⟨r, s, hs, hsr⟩` from `hx z (le_locP P N (hS ▸ Submodule.subset_span hzS))`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smul_of_tower, Algebra.smul_def, hsr]`. Conclude with `Submodule.mem_one.2 ⟨r, rfl⟩`. Use `choose! sf hsf hsm using hz`. Establish `hprod : (∏ z ∈ S, sf z) ∈ (conjPrime₂ P).asIdeal.primeCompl` using `Submonoid.prod_mem _ fun z hzS => hsf z hzS`. Use `(mem_locP _ _ _).2 ⟨∏ z ∈ S, sf z, hprod, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hu, mem_dual]`. Introduce `y hy`. Rewrite `hy` using `[← hS]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hzS`.

Rewrite using `[← Finset.mul_prod_erase S sf hzS, mul_comm, ← smul_smul, LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem _ _ (hsm z hzS)`. Consider the case `zero => simp`. Consider the case `add y₁ y₂ _ _ h₁ h₂`. Rewrite using `[map_add, LinearMap.add_apply]`.

Conclude with `Submodule.add_mem _ h₁ h₂`. Consider the case `smul a y _ h`. Rewrite using `[hStd_osmul_left, LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem _ _ h`.
-/
theorem mem_at_conj {N : Submodule (𝓞 E) (Sp E n)} (hl : N.FG) (hu : IsUnimodular (hStd E n) N)
    (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ localization₂ (conjPrime₂ P).asIdeal N ↔ ∀ y ∈ localization₂ P.asIdeal N, IntAt (conjPrime₂ P) (hStd E n y x) := by
  constructor
  · intro hx y hy
    rw [mem_locP] at hx hy
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨s, hs, hsy⟩ := hy
    have htd : t • x ∈ dual (hStd E n) N := by rw [hu]; exact htx
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 ((mem_dual N _).1 htd _ hsy)
    refine ⟨r, cO E s * t, ?_, ?_⟩
    · intro hmul
      rcases (conjPrime₂ P).isPrime.mem_or_mem hmul with h1 | h1
      · rw [mem_conjP, cO_cO] at h1
        exact hs h1
      · exact ht h1
    · rw [hr, hStd_osmul_left, smul_smul, LinearMap.map_smul_of_tower, Algebra.smul_def]
  · intro hx
    classical
    obtain ⟨S, hS⟩ := hl

    have hz : ∀ z ∈ S, ∃ s : 𝓞 E, s ∉ (conjPrime₂ P).asIdeal ∧
        hStd E n z (s • x) ∈ (1 : Submodule (𝓞 E) E) := by
      intro z hzS
      obtain ⟨r, s, hs, hsr⟩ := hx z (le_locP P N (hS ▸ Submodule.subset_span hzS))
      refine ⟨s, hs, ?_⟩
      rw [LinearMap.map_smul_of_tower, Algebra.smul_def, hsr]
      exact Submodule.mem_one.2 ⟨r, rfl⟩
    choose! sf hsf hsm using hz
    have hprod : (∏ z ∈ S, sf z) ∈ (conjPrime₂ P).asIdeal.primeCompl :=
      Submonoid.prod_mem _ fun z hzS => hsf z hzS
    refine (mem_locP _ _ _).2 ⟨∏ z ∈ S, sf z, hprod, ?_⟩
    rw [← hu, mem_dual]
    intro y hy
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem z hzS =>
      rw [← Finset.mul_prod_erase S sf hzS, mul_comm, ← smul_smul, LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ _ (hsm z hzS)
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ h₁ h₂
    | smul a y _ h =>
      rw [hStd_osmul_left, LinearMap.map_smul_of_tower]
      exact Submodule.smul_mem _ _ h

end Generic

end GlobalTheory.Survey.StandardDeterminantUnits
