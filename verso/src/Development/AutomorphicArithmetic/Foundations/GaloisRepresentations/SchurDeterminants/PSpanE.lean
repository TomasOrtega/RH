import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

/- English proof (translation)
Unfold `eSpan`. Conclude with `Submodule.subset_span ⟨Fin.elim0, by simp⟩`.
-/
private theorem one_mem_eSpan (K : Type) [CommRing K] (n : ℕ) :
    (1 : MvPolynomial (Fin n) K) ∈ eSpan K n 0 := by
  unfold eSpan
  exact Submodule.subset_span ⟨Fin.elim0, by simp⟩

/- English proof (translation)
Unfold `eSpan`. Conclude with `Submodule.subset_span ⟨fun _ => i.succ, by simp⟩`.
-/
private theorem esymm_mem_eSpan (K : Type) [CommRing K] (n : ℕ) (i : Fin n) :
    esymm (Fin n) K ((i : ℕ) + 1) ∈ eSpan K n 1 := by
  unfold eSpan
  exact Submodule.subset_span ⟨fun _ => i.succ, by simp⟩

/- English proof (translation)
Take `⟨hmono, hmul⟩` from `h K n`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_C, Algebra.algebraMap_eq_smul_one]`.

Conclude with `Submodule.smul_mem _ a (one_mem_eSpan K n)`. Consider the case `add p q hp hq`. Take `⟨k, hk⟩` from `hp`. Take `⟨l, hl⟩` from `hq`. Use `⟨max k l, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ (hmono _ _ (le_max_left k l) hk) (hmono _ _ (le_max_right k l) hl)`. Consider the case `mul_X p i hp`. Take `⟨k, hk⟩` from `hp`. Use `⟨k + 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, aeval_X]`. Conclude with `hmul _ _ _ _ hk (esymm_mem_eSpan K n i)`.
-/
private theorem exists_mem_eSpan (h : ESpanMul) (K : Type) [CommRing K] (n : ℕ)
    (q : MvPolynomial (Fin n) K) :
    ∃ k, aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q ∈ eSpan K n k := by
  obtain ⟨hmono, hmul⟩ := h K n
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    rw [aeval_C, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ a (one_mem_eSpan K n)
  | add p q hp hq =>
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hq
    refine ⟨max k l, ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (hmono _ _ (le_max_left k l) hk) (hmono _ _ (le_max_right k l) hl)
  | mul_X p i hp =>
    obtain ⟨k, hk⟩ := hp
    refine ⟨k + 1, ?_⟩
    rw [map_mul, aeval_X]
    exact hmul _ _ _ _ hk (esymm_mem_eSpan K n i)

/- English proof (translation)
Introduce `h K _ n P hP`. Take `⟨q, hq⟩` from `esymmAlgHom_fin_surjective K (le_refl n) ⟨P, (mem_symmetricSubalgebra P).2 hP⟩`. Establish `hq' : aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q = P`. Use `congrArg Subtype.val hq` as an intermediate fact. Rewrite `this` using `[esymmAlgHom_apply]`. Then use the resulting hypothesis.

Take `⟨k₀, hk₀⟩` from `exists_mem_eSpan h K n q`. Use `⟨k₀, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hmem` using `(h K n).1 _ _ hk hk₀`. Rewrite `hmem` using `[hq']`. Unfold `eSpan at hmem`.

Take `⟨w, hw⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hmem`. Conclude with `⟨w, hw.symm⟩`.
-/
theorem spanE_of : ESpanMul → SpanE := by
  intro h K _ n P hP
  obtain ⟨q, hq⟩ := esymmAlgHom_fin_surjective K (le_refl n) ⟨P, (mem_symmetricSubalgebra P).2 hP⟩
  have hq' : aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q = P := by
    have := congrArg Subtype.val hq
    rwa [esymmAlgHom_apply] at this
  obtain ⟨k₀, hk₀⟩ := exists_mem_eSpan h K n q
  refine ⟨k₀, fun k hk => ?_⟩
  have hmem := (h K n).1 _ _ hk hk₀
  rw [hq'] at hmem
  unfold eSpan at hmem
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  exact ⟨w, hw.symm⟩

end UpperTheory.Gal.Schur
