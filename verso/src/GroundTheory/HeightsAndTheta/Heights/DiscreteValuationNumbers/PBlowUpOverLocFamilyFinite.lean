import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFamilyFiniteCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingIso
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocalChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_or]`. Take `⟨hQP, hQW'⟩` from `h`. Establish `hWp : W.IsPrime` using `hW.1.1`. Set `f` to `Ideal.Quotient.mk P`.

Establish `hf : Function.Surjective f` using `Ideal.Quotient.mk_surjective`. Establish `hker : RingHom.ker f ≤ Q` using `by rw [Ideal.mk_ker]; exact hPQ`. Establish `hkerW : RingHom.ker f ≤ W` using `hker.trans hQW`. Establish `: (Q.map f).IsPrime` using `Ideal.map_isPrime_of_surjective hf hker`. Establish `: (W.map f).IsPrime` using `Ideal.map_isPrime_of_surjective hf hkerW`.

Establish `: (⊥ : Ideal (A ⧸ P)).IsPrime` using `Ideal.isPrime_bot`. Establish `h1 : (⊥ : Ideal (A ⧸ P)) < Q.map f`. Use `bot_lt_iff_ne_bot.mpr fun h0 => hQP (le_antisymm (fun q hq => ?_) hPQ)` and prove the remaining obligations. Establish `hq' : f q ∈ Q.map f` using `Ideal.mem_map_of_mem f hq`. Rewrite `hq'` using `[h0, Ideal.mem_bot]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp hq'`. Establish `h2 : Q.map f < W.map f`. Use `lt_of_le_of_ne (Ideal.map_mono hQW) fun e => hQW' ?_` and prove the remaining obligations. Establish `e'` using `congrArg (Ideal.comap f) e`. Rewrite `e'` using `[Ideal.comap_map_of_surjective' f hf, Ideal.comap_map_of_surjective' f hf, sup_eq_left.mpr hker, sup_eq_left.mpr hkerW]`. Then use the resulting hypothesis.

Establish `e1` using `Ideal.height_add_one_le_of_lt_of_isPrime h1`. Establish `e2` using `Ideal.height_add_one_le_of_lt_of_isPrime h2`. Establish `e3` using `Ideal.map_height_le_one_of_mem_minimalPrimes hW`. Rewrite `e1` using `[Ideal.height_bot]`. Establish `e4 : (0 : ℕ∞) + 1 + 1 ≤ 1` using `((add_le_add e1 le_rfl).trans e2).trans e3`.

Evaluate the numerical expressions using `at e4`.
-/
theorem prime_eq_or_eq_of_le_mem_minimalPrimes_sup_span {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P W Q : Ideal A} (hP : P.IsPrime) (hQ : Q.IsPrime) {x : A}
    (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P ≤ Q) (hQW : Q ≤ W) : Q = P ∨ Q = W := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hQP, hQW'⟩ := h
  have hWp : W.IsPrime := hW.1.1
  let f := Ideal.Quotient.mk P
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ Q := by rw [Ideal.mk_ker]; exact hPQ
  have hkerW : RingHom.ker f ≤ W := hker.trans hQW
  have : (Q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hkerW
  have : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have h1 : (⊥ : Ideal (A ⧸ P)) < Q.map f := by
    refine bot_lt_iff_ne_bot.mpr fun h0 => hQP (le_antisymm (fun q hq => ?_) hPQ)
    have hq' : f q ∈ Q.map f := Ideal.mem_map_of_mem f hq
    rw [h0, Ideal.mem_bot] at hq'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq'
  have h2 : Q.map f < W.map f := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun e => hQW' ?_
    have e' := congrArg (Ideal.comap f) e
    rwa [Ideal.comap_map_of_surjective' f hf, Ideal.comap_map_of_surjective' f hf,
      sup_eq_left.mpr hker, sup_eq_left.mpr hkerW] at e'
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h2
  have e3 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  rw [Ideal.height_bot] at e1
  have e4 : (0 : ℕ∞) + 1 + 1 ≤ 1 := ((add_le_add e1 le_rfl).trans e2).trans e3
  norm_num at e4

/- English proof (translation)
Use `le_antisymm (fun F hF => ?_) hle` and prove the remaining obligations. Establish `hcomp : ∀ b, weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F ∈ blowUpOf P u`. Introduce `b`. Use `set G := weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F`. Establish `hG : IsMultiHomog G b` using `weightedHomogeneousComponent_isWeightedHomogeneous _ _`.

Establish `hGQ : G ∈ Q` using `hQh F hF b`. Take `⟨f, hf⟩` from `Ideal.Quotient.mk_surjective (blowUpEval P u G)`. Establish `hrel : liftForm (u j) ^ (b none) * G - newVar j ^ (b none) * liftForm f ∈ blowUpOf P u`. Rewrite using `[blowUpOf, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow, aeval_blowUpSubst_of_isMultiHomog P u hG, aeval_blowUpSubst_liftForm, aeval_blowUpSubst_liftForm, aeval_blowUpSubst_newVar, ← hf]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : newVar j ^ (b none) * liftForm f ∈ Q`. Establish `h` using `Q.sub_mem (Q.mul_mem_left (liftForm (u j) ^ (b none)) hGQ) (hle hrel)`. Rewrite `h` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h2 : liftForm f ∈ Q` using `(hQp.mem_or_mem h1).resolve_left fun h => hj (hQp.mem_of_pow_mem _ h)`. Establish `h3 : f ∈ P` using `hc h2`.

Rewrite using `[blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_of_isMultiHomog P u hG, ← hf, Ideal.Quotient.eq_zero_iff_mem.mpr h3, map_zero, zero_mul]`. Rewrite using `[← sum_weightedHomogeneousComponent (blockWeight (extIdx ι J)) F]`. Conclude with `finsum_induction (· ∈ blowUpOf P u) (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) hcomp`.
-/
theorem eq_blowUpOf_of_comap_liftForm_le {K : Type} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*}
    [CommRing R] {P : Ideal (MRing ι R)} {u : J → MRing ι R} {Q : Ideal (MRing (extIdx ι J) R)}
    (hQp : Q.IsPrime) (hQh : IsMultiHomogIdeal Q) (hle : blowUpOf P u ≤ Q) {j : J}
    (hj : (newVar j : MRing (extIdx ι J) R) ∉ Q)
    (hc : Q.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ P) : Q = blowUpOf P u := by
  classical
  refine le_antisymm (fun F hF => ?_) hle
  have hcomp : ∀ b, weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F ∈ blowUpOf P u := by
    intro b
    set G := weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F
    have hG : IsMultiHomog G b := weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hGQ : G ∈ Q := hQh F hF b
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (blowUpEval P u G)
    have hrel : liftForm (u j) ^ (b none) * G - newVar j ^ (b none) * liftForm f ∈ blowUpOf P u := by
      rw [blowUpOf, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow,
        aeval_blowUpSubst_of_isMultiHomog P u hG, aeval_blowUpSubst_liftForm, aeval_blowUpSubst_liftForm,
        aeval_blowUpSubst_newVar, ← hf]
      ring
    have h1 : newVar j ^ (b none) * liftForm f ∈ Q := by
      have h := Q.sub_mem (Q.mul_mem_left (liftForm (u j) ^ (b none)) hGQ) (hle hrel)
      rwa [sub_sub_cancel] at h
    have h2 : liftForm f ∈ Q :=
      (hQp.mem_or_mem h1).resolve_left fun h => hj (hQp.mem_of_pow_mem _ h)
    have h3 : f ∈ P := hc h2
    rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_of_isMultiHomog P u hG, ← hf,
      Ideal.Quotient.eq_zero_iff_mem.mpr h3, map_zero, zero_mul]
  rw [← sum_weightedHomogeneousComponent (blockWeight (extIdx ι J)) F]
  exact finsum_induction (· ∈ blowUpOf P u) (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) hcomp

/- English proof (translation)
Introduce `O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel`. Establish `hPp : P.IsPrime` using `hP.multiProj.isPrime`. Use `((Set.finite_singleton (blowUpOf P u)).union (h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel)).subset ?_` and prove the remaining obligations. Introduce and unpack `Q ⟨hQp, hQh, hQr, hQle, hQW⟩`. Take `⟨hcp, hPc, -, j, hj⟩` from `comap_liftForm_facts hQp hQle hQr`.

Break down `prime_eq_or_eq_of_le_mem_minimalPrimes_sup_span hPp hcp hWmin hPc hQW with h | h` into its components or cases. Conclude with `Or.inl (eq_blowUpOf_of_comap_liftForm_le hQp hQh hQle hj h.le)`. Conclude with `Or.inr ⟨hQp, hQh, hQr, hQle, h⟩`.
-/
theorem BlowUpOverLocFamilyFinite.proof (h₁ : BlowUpOverLocFibreFinite.Statement.{u}) :
    BlowUpOverLocFamilyFinite.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have hPp : P.IsPrime := hP.multiProj.isPrime
  refine ((Set.finite_singleton (blowUpOf P u)).union
    (h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel)).subset ?_
  rintro Q ⟨hQp, hQh, hQr, hQle, hQW⟩
  obtain ⟨hcp, hPc, -, j, hj⟩ := comap_liftForm_facts hQp hQle hQr
  rcases prime_eq_or_eq_of_le_mem_minimalPrimes_sup_span hPp hcp hWmin hPc hQW with h | h
  · exact Or.inl (eq_blowUpOf_of_comap_liftForm_le hQp hQh hQle hj h.le)
  · exact Or.inr ⟨hQp, hQh, hQr, hQle, h⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
