import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormDim
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChowFormDimLe

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h0` using `hI.isHomog g hg 0`. Rewrite `h0` using `[homogeneousComponent_zero]`. Conclude with `hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))`.
-/
theorem coeff_zero_eq_zero_of_mem {F : Type} [Field F] {n : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    (hI : IsProjPrime I) {g : MvPolynomial (Fin n) F} (hg : g ∈ I) : coeff 0 g = 0 := by
  by_contra h
  have h0 := hI.isHomog g hg 0
  rw [homogeneousComponent_zero] at h0
  exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))

/- English proof (translation)
Set `_` to `MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)`. Establish `: Module.Flat (MvPolynomial (Fin n) F) (MvPolynomial (Fin n) K)` using `Module.Flat.isBaseChange F (MvPolynomial (Fin n) F) K (MvPolynomial (Fin n) K) (Algebra.IsPushout.out (R := F) (S := MvPolynomial (Fin n) F) (R' := K) (S' := MvPolynomial (Fin n) K))`. Use `set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K))`. Establish `: Q.IsMaximal` using `RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)`. Establish `hle : I ≤ Q.under (MvPolynomial (Fin n) F)`.

Introduce `g hg`. Rewrite using `[Ideal.under, Ideal.mem_comap, MvPolynomial.algebraMap_def, RingHom.mem_ker, eval_map, eval₂_zero_apply, constantCoeff_eq, hI g hg, map_zero]`. Take `⟨P, hPQ, hP, hPI⟩` from `Ideal.exists_ideal_le_liesOver_of_le Q hle`. Use `⟨P, hP, hPQ, ?_⟩` and prove the remaining obligations. Rewrite using `[P.over_def I]`.

Both sides reduce to the same expression.
-/
theorem exists_prime_liesOver {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (hI : ∀ g ∈ I, coeff 0 g = 0) :
    ∃ P : Ideal (MvPolynomial (Fin n) K), P.IsPrime ∧
      P ≤ RingHom.ker (eval (0 : Fin n → K)) ∧
      P.comap (MvPolynomial.map (algebraMap F K)) = I := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : Module.Flat (MvPolynomial (Fin n) F) (MvPolynomial (Fin n) K) :=
    Module.Flat.isBaseChange F (MvPolynomial (Fin n) F) K (MvPolynomial (Fin n) K)
      (Algebra.IsPushout.out (R := F) (S := MvPolynomial (Fin n) F) (R' := K)
        (S' := MvPolynomial (Fin n) K))
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K))
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  have hle : I ≤ Q.under (MvPolynomial (Fin n) F) := by
    intro g hg
    rw [Ideal.under, Ideal.mem_comap, MvPolynomial.algebraMap_def, RingHom.mem_ker, eval_map,
      eval₂_zero_apply, constantCoeff_eq, hI g hg, map_zero]
  obtain ⟨P, hPQ, hP, hPI⟩ := Ideal.exists_ideal_le_liesOver_of_le Q hle
  refine ⟨P, hP, hPQ, ?_⟩
  rw [P.over_def I]
  rfl

/- English proof (translation)
Set `_` to `MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)`. Establish `: P.LiesOver I` using `⟨hPI.symm⟩`. Conclude with `GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin n) F ⧸ I) (MvPolynomial (Fin n) K ⧸ P))`.
-/
theorem ringKrullDim_eq_of_comap {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F))
    (P : Ideal (MvPolynomial (Fin n) K)) (hPI : P.comap (MvPolynomial.map (algebraMap F K)) = I) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ I) := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : P.LiesOver I := ⟨hPI.symm⟩
  exact GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral
    (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin n) F ⧸ I) (MvPolynomial (Fin n) K ⧸ P))

/- English proof (translation)
Use `set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K)) with hQdef`. Establish `: Q.IsMaximal` using `RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)`. Set `mk` to `Ideal.Quotient.mk P`. Set `ℓ : Fin k → MvPolynomial (Fin n) K` to `fun i => ∑ j, C (u (i, j)) * X j`. Establish `hℓQ : ∀ i, ℓ i ∈ Q`.

Introduce `i`. Simplify using `[Q, ℓ, RingHom.mem_ker]`. Use `set Mb : Ideal (MvPolynomial (Fin n) K ⧸ P) := Q.map mk`. Establish `: Mb.IsMaximal` using `Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPQ)`. Set `s : Finset (MvPolynomial (Fin n) K ⧸ P)` to `Finset.univ.image (fun i => mk (ℓ i))`.

Establish `hsM : Ideal.span (s : Set (MvPolynomial (Fin n) K ⧸ P)) ≤ Mb`. Rewrite using `[Ideal.span_le]`. Introduce `y hy`. Simplify using `only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy`. Take `⟨i, rfl⟩` from `hy`.

Conclude with `Ideal.mem_map_of_mem _ (hℓQ i)`. Take `⟨q, hqmin, hqM⟩` from `Ideal.exists_minimalPrimes_le hsM`. Establish `: q.IsPrime` using `hqmin.1.1`. Establish `hqht : q.height ≤ k`. Use `(Ideal.height_le_card_of_mem_minimalPrimes_span_finset hqmin).trans ?_` and prove the remaining obligations.

Conclude with `Finset.card_image_le.trans (by simp)` after adjusting the coercions. Establish `hMht : (Mb.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) K ⧸ P)`. Establish `h` using `GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient K Mb`. Establish `hF : IsField ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb)` using `(Ideal.Quotient.maximal_ideal_iff_isField_quotient Mb).mp inferInstance`. Establish `h0 : ringKrullDim ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) = 0`.

Establish `h00` using `ringKrullDim_eq_zero_of_isField (F := (MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) hF`. Use `h00 using 2` and compare the differences between its conclusion and the goal. Rewrite `h` using `[h0, add_zero]`. Then use the resulting hypothesis. Establish `hqne : q ≠ Mb`. Introduce `hq`.

Rewrite `hqht` using `[hq]`. Establish `h1 : ((Mb.height : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞)` using `by exact_mod_cast hqht`. Rewrite `h1` using `[hMht]`. Conclude with `absurd h1 (not_le.mpr (by exact_mod_cast hdim))`. Use `set Q' := q.comap mk`.

Establish `: Q'.IsPrime` using `Ideal.comap_isPrime mk q`. Establish `hQQ' : ¬ Q ≤ Q'`. Introduce `h`. Apply `hqne` to reduce the goal to its premises. Use `le_antisymm hqM ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hnull` using `MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) Q'`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx, hx0⟩ : ∃ x ∈ zeroLocus K Q', x ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_and, not_not] at hcon`.

Apply `hQQ'` to reduce the goal to its premises. Introduce `g hg`. Rewrite using `[← hnull, mem_vanishingIdeal_iff]`. Introduce `x hx`. Rewrite using `[hcon x hx]`.

Simplify `hg` using `[Q, RingHom.mem_ker]`. Use `⟨x, hx0, fun g hg => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `hgQ' : g ∈ Q'` using `by show mk g ∈ q`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr hg]`. Conclude with `q.zero_mem`.

Simplify using `using (mem_zeroLocus_iff.mp hx) g hgQ'`. Establish `hmem : ℓ i ∈ Q'` using `by show mk (ℓ i) ∈ q`. Conclude with `hqmin.1.2 (Ideal.subset_span (by simp [s]))`. Simplify `(mem_zeroLocus_iff.mp hx) _ hmem` using `[ℓ]`.
-/
theorem exists_ne_zero_common_zero {K : Type} [Field K] [IsAlgClosed K] {n k : ℕ}
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] (hPQ : P ≤ RingHom.ker (eval (0 : Fin n → K)))
    (hdim : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) K ⧸ P))
    (u : Fin k × Fin n → K) :
    ∃ x : Fin n → K, x ≠ 0 ∧ (∀ g ∈ P, eval x g = 0) ∧ ∀ i, ∑ j, u (i, j) * x j = 0 := by
  classical
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K)) with hQdef
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  let mk := Ideal.Quotient.mk P
  let ℓ : Fin k → MvPolynomial (Fin n) K := fun i => ∑ j, C (u (i, j)) * X j
  have hℓQ : ∀ i, ℓ i ∈ Q := by
    intro i
    simp [Q, ℓ, RingHom.mem_ker]
  set Mb : Ideal (MvPolynomial (Fin n) K ⧸ P) := Q.map mk
  have : Mb.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hPQ)
  let s : Finset (MvPolynomial (Fin n) K ⧸ P) := Finset.univ.image (fun i => mk (ℓ i))
  have hsM : Ideal.span (s : Set (MvPolynomial (Fin n) K ⧸ P)) ≤ Mb := by
    rw [Ideal.span_le]
    intro y hy
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact Ideal.mem_map_of_mem _ (hℓQ i)
  obtain ⟨q, hqmin, hqM⟩ := Ideal.exists_minimalPrimes_le hsM
  have : q.IsPrime := hqmin.1.1
  have hqht : q.height ≤ k := by
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hqmin).trans ?_
    exact_mod_cast Finset.card_image_le.trans (by simp)
  have hMht : (Mb.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) K ⧸ P) := by
    have h := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient K Mb
    have hF : IsField ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient Mb).mp inferInstance
    have h0 : ringKrullDim ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) = 0 := by
      have h00 := ringKrullDim_eq_zero_of_isField (F := (MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) hF
      convert h00 using 2
    rwa [h0, add_zero] at h
  have hqne : q ≠ Mb := by
    intro hq
    rw [hq] at hqht
    have h1 : ((Mb.height : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hqht
    rw [hMht] at h1
    exact absurd h1 (not_le.mpr (by exact_mod_cast hdim))
  set Q' := q.comap mk
  have : Q'.IsPrime := Ideal.comap_isPrime mk q
  have hQQ' : ¬ Q ≤ Q' := by
    intro h
    apply hqne
    refine le_antisymm hqM ?_
    calc Mb = Q.map mk := rfl
      _ ≤ Q'.map mk := Ideal.map_mono h
      _ = q := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q
  have hnull := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) Q'
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ zeroLocus K Q', x ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hQQ'
    intro g hg
    rw [← hnull, mem_vanishingIdeal_iff]
    intro x hx
    rw [hcon x hx]
    simpa [Q, RingHom.mem_ker] using hg
  refine ⟨x, hx0, fun g hg => ?_, fun i => ?_⟩
  · have hgQ' : g ∈ Q' := by
      show mk g ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]
      exact q.zero_mem
    simpa using (mem_zeroLocus_iff.mp hx) g hgQ'
  · have hmem : ℓ i ∈ Q' := by
      show mk (ℓ i) ∈ q
      exact hqmin.1.2 (Ideal.subset_span (by simp [s]))
    simpa [ℓ] using (mem_zeroLocus_iff.mp hx) _ hmem

/- English proof (translation)
Introduce `F _ n k I f hI hf`. Assume the negation of the conclusion as `hdim`. Rewrite `hdim` using `[not_le]`. Use `hI.isPrime` as an intermediate fact. Take `⟨P, hP, hPQ, hPI⟩` from `exists_prime_liesOver (AlgebraicClosure F) I (fun g hg => coeff_zero_eq_zero_of_mem hI hg)`.

Establish `hdimP : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure F) ⧸ P)`. Rewrite using `[ringKrullDim_eq_of_comap (AlgebraicClosure F) I P hPI]`. Conclude with `hdim` after adjusting the coercions. Establish `hall : ∀ u : Fin k × Fin n → AlgebraicClosure F, u ∈ incidence I k`. Introduce `u`.

Take `⟨x, hx0, hxP, hxu⟩` from `exists_ne_zero_common_zero P hPQ hdimP u`. Use `⟨x, hx0, fun g hg => ?_, hxu⟩` and prove the remaining obligations. Establish `hgP : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) g ∈ P`. Rewrite `hg` using `[← hPI]`. Conclude with `hg`.

Use `hxP _ hgP` as an intermediate fact. Rewrite `this` using `[eval_map, ← aeval_def]`. Then use the resulting hypothesis. Apply `hf.1` to reduce the goal to its premises. Apply `map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F (AlgebraicClosure F)).injective` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises.

Introduce `u`. Rewrite using `[eval_map, ← aeval_def, ((hf.2 f).mpr dvd_rfl) u (hall u), map_zero, map_zero]`.
-/
theorem proof : ChowFormDimLe.Statement := by
  intro F _ n k I f hI hf
  by_contra hdim
  rw [not_le] at hdim
  have := hI.isPrime
  obtain ⟨P, hP, hPQ, hPI⟩ := exists_prime_liesOver (AlgebraicClosure F) I
    (fun g hg => coeff_zero_eq_zero_of_mem hI hg)
  have hdimP : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure F) ⧸ P) := by
    rw [ringKrullDim_eq_of_comap (AlgebraicClosure F) I P hPI]
    exact_mod_cast hdim
  have hall : ∀ u : Fin k × Fin n → AlgebraicClosure F, u ∈ incidence I k := by
    intro u
    obtain ⟨x, hx0, hxP, hxu⟩ := exists_ne_zero_common_zero P hPQ hdimP u
    refine ⟨x, hx0, fun g hg => ?_, hxu⟩
    have hgP : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) g ∈ P := by
      rw [← hPI] at hg
      exact hg
    have := hxP _ hgP
    rwa [eval_map, ← aeval_def] at this
  apply hf.1
  apply map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F (AlgebraicClosure F)).injective
  apply MvPolynomial.funext
  intro u
  rw [eval_map, ← aeval_def, ((hf.2 f).mpr dvd_rfl) u (hall u), map_zero, map_zero]

end ChowFormDimLe

end

end GroundTheory.Heights₂.Heights
