import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFactsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

/- English proof (translation)
Introduce `l _ K bk A _ s ι TB a x`. Use `haveI hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff`. Take `⟨h1, -, -, h4, -⟩` from `GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ i`.

Conclude with `⟨TB.c i y, TB.c_mul i a y⟩`. Introduce `h`. Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Use `⟨0, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_zero]`. Conclude with `h1 x fun i => zero_dvd_iff.1 (h i)`. Use `choose z hz using h`. Take `⟨k, hk⟩` from `Ideal.exists_pow_inf_eq_pow_smul bk.J (M := bk.S) (Submodule.span bk.S {a})`. Establish `key : ∀ (n : ℕ) (w : bk.S), a * w ∈ bk.J ^ (n + k) → w ∈ bk.J ^ n`.

Introduce `n w hw`. Establish `hmem : a * w ∈ bk.J ^ (n + k) • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a}`. Use `Submodule.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top]`. Conclude with `hw`.

Conclude with `Submodule.mem_span_singleton.2 ⟨w, by rw [smul_eq_mul, mul_comm]⟩`. Rewrite `hmem` using `[hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel]`. Establish `h2 : bk.J ^ n • (bk.J ^ k • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a}) ≤ bk.J ^ n * Ideal.span {a}` using `Submodule.smul_mono le_rfl inf_le_right`. Take `⟨v, hv, hva⟩` from `Ideal.mem_mul_span_singleton.1 (h2 hmem)`. Establish `hwv : w = v` using `mul_left_cancel₀ ha (by rw [← hva, mul_comm])`.

Conclude with `hwv ▸ hv`. Establish `hfin : ∀ n : ℕ, {i | z i ∉ bk.J ^ n}.Finite` using `fun n => (TB.fin x (n + k)).subset fun i hi hx => hi (key n (z i) (hz i ▸ hx))`. Take `⟨y, hy⟩` from `h4 z hfin`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `h0` using `h1 (x - s a * y) fun i => by`.

Rewrite using `[map_sub, TB.c_mul, hy, hz, sub_self]`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (a : bk.S) (x : A), s a ∣ x ↔ ∀ i, a ∣ TB.c i x := by
  intro l _ K bk A _ s ι TB a x
  haveI hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨TB.c i y, TB.c_mul i a y⟩
  · intro h
    by_cases ha : a = 0
    · subst ha
      refine ⟨0, ?_⟩
      rw [mul_zero]
      exact h1 x fun i => zero_dvd_iff.1 (h i)
    · choose z hz using h
      obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul bk.J (M := bk.S) (Submodule.span bk.S {a})
      have key : ∀ (n : ℕ) (w : bk.S), a * w ∈ bk.J ^ (n + k) → w ∈ bk.J ^ n := by
        intro n w hw
        have hmem : a * w ∈ bk.J ^ (n + k) • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a} := by
          refine Submodule.mem_inf.2 ⟨?_, ?_⟩
          · rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hw
          · exact Submodule.mem_span_singleton.2 ⟨w, by rw [smul_eq_mul, mul_comm]⟩
        rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at hmem
        have h2 : bk.J ^ n • (bk.J ^ k • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a}) ≤
            bk.J ^ n * Ideal.span {a} :=
          Submodule.smul_mono le_rfl inf_le_right
        obtain ⟨v, hv, hva⟩ := Ideal.mem_mul_span_singleton.1 (h2 hmem)
        have hwv : w = v := mul_left_cancel₀ ha (by rw [← hva, mul_comm])
        exact hwv ▸ hv
      have hfin : ∀ n : ℕ, {i | z i ∉ bk.J ^ n}.Finite := fun n =>
        (TB.fin x (n + k)).subset fun i hi hx => hi (key n (z i) (hz i ▸ hx))
      obtain ⟨y, hy⟩ := h4 z hfin
      refine ⟨y, ?_⟩
      have h0 := h1 (x - s a * y) fun i => by
        rw [map_sub, TB.c_mul, hy, hz, sub_self]
      exact sub_eq_zero.1 h0
