import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicIsOfFinOrderOfFiniteIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulMemRangePiQuotientMinimalPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicPiIsOfFinOrderStatement

namespace GlobalTheory.PicReducedTors

/- English proof (translation)
Introduce `B _ _ _ M`. Use `haveI : IsNoetherian ℤ B := inferInstance`. Use `haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance`. Use `haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype`. Set `φ` to `Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)`.

Use `haveI : Module.Finite ℤ ((P : minimalPrimes B) → B ⧸ (P : Ideal B)) := inferInstance`. Take `⟨n, hn, hmul⟩` from `GlobalTheory.T.exists_nat_mul_mem_range_pi_quotient_minimalPrimes' B`. Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `b hb`.

Establish `hrad : b ∈ (⊥ : Ideal B).radical`. Rewrite using `[← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]`. Introduce `P hP`. Use `congrFun hb ⟨P, hP⟩` as an intermediate fact. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `this`. Take `⟨k, hk⟩` from `hrad`. Conclude with `IsReduced.eq_zero b ⟨k, by simpa using hk⟩`. Use `GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B _ φ n hinj hn hmul M ?_` and prove the remaining obligations. Use `GlobalTheory.T.pic_pi_isOfFinOrder' _ _ (fun P N => ?_) _` and prove the remaining obligations.

Use `haveI : (P : Ideal B).IsPrime := P.2.1.1`. Conclude with `GlobalTheory.T.pic_isOfFinOrder_of_finite_int' _ N`.
-/
theorem pic_isOfFinOrder : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B),
    IsOfFinOrder M := by
  intro B _ _ _ M
  haveI : IsNoetherian ℤ B := inferInstance
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  let φ := Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)
  haveI : Module.Finite ℤ ((P : minimalPrimes B) → B ⧸ (P : Ideal B)) := inferInstance
  obtain ⟨n, hn, hmul⟩ := GlobalTheory.T.exists_nat_mul_mem_range_pi_quotient_minimalPrimes' B
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hrad : b ∈ (⊥ : Ideal B).radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      have := congrFun hb ⟨P, hP⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact this
    obtain ⟨k, hk⟩ := hrad
    exact IsReduced.eq_zero b ⟨k, by simpa using hk⟩
  refine GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B _ φ n hinj hn hmul M ?_
  refine GlobalTheory.T.pic_pi_isOfFinOrder' _ _ (fun P N => ?_) _
  haveI : (P : Ideal B).IsPrime := P.2.1.1
  exact GlobalTheory.T.pic_isOfFinOrder_of_finite_int' _ N

end GlobalTheory.PicReducedTors
