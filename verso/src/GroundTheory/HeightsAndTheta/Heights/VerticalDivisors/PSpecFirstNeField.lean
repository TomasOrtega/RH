import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSpecFirst
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncidenceZeroLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

/- English proof (translation)
Take `⟨x, hx0, hxJ, hxv⟩` from `hv`. Establish `hP : (RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F)).IsPrime` using `RingHom.ker_isPrime _`. Establish `hJP : J ≤ RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F)` using `fun g hg => RingHom.mem_ker.mpr (hxJ g hg)`. Take `⟨W, hW, hWP⟩` from `Ideal.exists_minimalPrimes_le hJP`. Use `⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxv⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hrel`. Apply `hx0` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Establish `hj : X j ∈ W`. Assume the negation of the conclusion as `hj`.

Conclude with `hrel ⟨j, hj⟩`. Simplify using `using RingHom.mem_ker.mp (hWP hj)`.
-/
theorem exists_relComps_of_mem_incidence_field {F : Type*} [Field F] {n k : ℕ}
    {J : Ideal (MvPolynomial (Fin n) F)} {v : Fin k × Fin n → AlgebraicClosure F}
    (hv : v ∈ incidence J k) : ∃ W ∈ relComps J, v ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxv⟩ := hv
  have hP : (RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F)).IsPrime :=
    RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) :=
    fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxv⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  simpa using RingHom.mem_ker.mp (hWP hj)

/- English proof (translation)
Introduce `F _ n e I f u hI hf hu h0`. Establish `hdim` using `h₁ F n (e + 1) I f hI hf`. Establish `hG : ∀ W : Ideal (MvPolynomial (Fin n) F), ∃ g : MvPolynomial (Fin e × Fin n) F, g ≠ 0 ∧ (W ∈ relComps (I ⊔ Ideal.span {linForm u}) → IsChowForm W e g)`. Introduce `W`. Distinguish the cases in `hW : W ∈ relComps (I ⊔ Ideal.span {linForm u})`.

Take `⟨hWp, hWd⟩` from `h₂ F n e I W u hI hdim hu hW`. Take `⟨g, hg⟩` from `h₃ F n e W hWp hWd`. Conclude with `⟨g, hg.1, fun _ => hg⟩`. Conclude with `⟨1, one_ne_zero, fun h => absurd h hW⟩`. Use `choose G hG0 hGc using hG`.

Set `S` to `((I ⊔ Ideal.span {linForm u}).finite_minimalPrimes_of_isNoetherianRing _).toFinset`. Establish `hprod : ∀ v : Fin e × Fin n → AlgebraicClosure F, aeval v (∏ W ∈ S, G W) = 0`. Introduce `v`. Set `w : Fin (e + 1) × Fin n → AlgebraicClosure F` to `fun ij => Fin.cases (motive := fun _ => AlgebraicClosure F) (algebraMap F _ (u ij.2)) (fun i => v (i, ij.2)) ij.1`. Establish `hw : aeval w f = 0`.

Establish `hs : aeval v (specFirst f u) = aeval w f`. Establish `hfun : (fun ij => aeval v (specFirstVar u ij)) = w`. Use function extensionality and compare the values at `ij`. Take `⟨i, j⟩` from `ij`. Proceed by induction on `i using Fin.cases with`.

Consider the case `zero => simp [specFirstVar, w]`. Consider the case `succ i => simp [specFirstVar, w]`. Unfold `specFirst`. Rewrite using `[aeval_bind₁, hfun]`. Rewrite using `[← hs, h0, map_zero]`.

Establish `hinc : ∀ g ∈ GroundTheory.Heights₂.Heights.incIdeal I (e + 1), aeval w g = 0`. Introduce `g hg`. Simplify using `only [GroundTheory.Heights₂.Heights.incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg`. Take `⟨h, rfl⟩` from `(hf.2 g).1 hg`. Rewrite using `[map_mul, hw, zero_mul]`.

Take `⟨y, hy0, hyI, hyw⟩` from `h₄ F n (e + 1) I hI.isHomog (AlgebraicClosure F) w hinc`. Establish `hvJ : v ∈ incidence (I ⊔ Ideal.span {linForm u}) e`. Use `⟨y, hy0, fun g hg => ?_, fun i => by simpa [w] using hyw i.succ⟩` and prove the remaining obligations. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hg`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hb`.

Establish `hu0 : aeval y (linForm u) = 0`. Simplify `hyw 0` using `[w, linForm]`. Rewrite using `[map_add, map_mul, hu0, mul_zero, add_zero, hyI a ha]`. Take `⟨W, hW, hvW⟩` from `exists_relComps_of_mem_incidence_field hvJ`. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_eq_zero ((Set.Finite.mem_toFinset _).mpr hW.1) (((hGc W hW).2 (G W)).2 dvd_rfl v hvW)`. Establish `hne : (∏ W ∈ S, G W) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun W _ => hG0 W`. Apply `hne` to reduce the goal to its premises. Apply `MvPolynomial.map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F _).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[eval_map, ← aeval_def, hprod v, map_zero]`.
-/
theorem SpecFirstNeField.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConeDimComponent.Statement)
    (h₃ : ChowFormExists.Statement) (h₄ : IncidenceZeroLocus.Statement) :
    SpecFirstNeField.Statement := by
  classical
  intro F _ n e I f u hI hf hu h0
  have hdim := h₁ F n (e + 1) I f hI hf

  have hG : ∀ W : Ideal (MvPolynomial (Fin n) F), ∃ g : MvPolynomial (Fin e × Fin n) F,
      g ≠ 0 ∧ (W ∈ relComps (I ⊔ Ideal.span {linForm u}) → IsChowForm W e g) := by
    intro W
    by_cases hW : W ∈ relComps (I ⊔ Ideal.span {linForm u})
    · obtain ⟨hWp, hWd⟩ := h₂ F n e I W u hI hdim hu hW
      obtain ⟨g, hg⟩ := h₃ F n e W hWp hWd
      exact ⟨g, hg.1, fun _ => hg⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hW⟩
  choose G hG0 hGc using hG
  let S := ((I ⊔ Ideal.span {linForm u}).finite_minimalPrimes_of_isNoetherianRing _).toFinset
  have hprod : ∀ v : Fin e × Fin n → AlgebraicClosure F, aeval v (∏ W ∈ S, G W) = 0 := by
    intro v
    let w : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij =>
      Fin.cases (motive := fun _ => AlgebraicClosure F) (algebraMap F _ (u ij.2))
        (fun i => v (i, ij.2)) ij.1
    have hw : aeval w f = 0 := by
      have hs : aeval v (specFirst f u) = aeval w f := by
        have hfun : (fun ij => aeval v (specFirstVar u ij)) = w := by
          funext ij
          obtain ⟨i, j⟩ := ij
          induction i using Fin.cases with
          | zero => simp [specFirstVar, w]
          | succ i => simp [specFirstVar, w]
        unfold specFirst
        rw [aeval_bind₁, hfun]
      rw [← hs, h0, map_zero]
    have hinc : ∀ g ∈ GroundTheory.Heights₂.Heights.incIdeal I (e + 1), aeval w g = 0 := by
      intro g hg
      simp only [GroundTheory.Heights₂.Heights.incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
      obtain ⟨h, rfl⟩ := (hf.2 g).1 hg
      rw [map_mul, hw, zero_mul]
    obtain ⟨y, hy0, hyI, hyw⟩ := h₄ F n (e + 1) I hI.isHomog (AlgebraicClosure F) w hinc
    have hvJ : v ∈ incidence (I ⊔ Ideal.span {linForm u}) e := by
      refine ⟨y, hy0, fun g hg => ?_, fun i => by simpa [w] using hyw i.succ⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hg
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      have hu0 : aeval y (linForm u) = 0 := by
        simpa [w, linForm] using hyw 0
      rw [map_add, map_mul, hu0, mul_zero, add_zero, hyI a ha]
    obtain ⟨W, hW, hvW⟩ := exists_relComps_of_mem_incidence_field hvJ
    rw [map_prod]
    exact Finset.prod_eq_zero ((Set.Finite.mem_toFinset _).mpr hW.1)
      (((hGc W hW).2 (G W)).2 dvd_rfl v hvW)
  have hne : (∏ W ∈ S, G W) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W _ => hG0 W
  apply hne
  apply MvPolynomial.map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F _).injective
  rw [map_zero]
  apply MvPolynomial.funext
  intro v
  rw [eval_map, ← aeval_def, hprod v, map_zero]

end

end GroundTheory.Heights₂.Heights.Vertical
