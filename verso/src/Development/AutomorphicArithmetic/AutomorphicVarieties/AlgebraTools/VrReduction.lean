import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsBasic

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `B E _ _ _ T ι _ _ o U F _ _ r p q hst hx hr`. Take `⟨-, -, h3, h4, h5, -, h7⟩` from `units_basic T o U`. Establish `hep : ∀ k, r (U.ep (o k)) = Matrix.single (o k) (o k) 1`. Introduce `k`. Rewrite using `[← U.x_base k, hx, U.o_o]`.

Establish `hz : ∀ w i j, r (U.x i * w * T.st (U.x j)) = Matrix.single (o i) (o j) (r w i j)`. Introduce `w i j`. Rewrite using `[map_mul, map_mul, hst, hx, hx, Matrix.transpose_single, Matrix.single_mul_mul_single, one_mul, mul_one]`. Establish `key : ∀ w i j, algebraMap B F (T.tr (U.x i * w * T.st (U.x j))) = r w i j`. Introduce `w i j`.

Distinguish the cases in `hij : o i = o j`. Establish `e` using `congrArg (fun M => M (o i) (o j)) (hz w i j)`. Simplify using `only [Matrix.single_apply_same] at e`. Rewrite using `[← e]`. Use `conv_rhs => rw [h5 i j w hij, map_smul, hep i, ← hij]`.

Simplify using `[Matrix.smul_apply, Algebra.smul_def]`. Rewrite using `[hr w i j hij, ← h7 i j w, h3 _ _ _ hij, map_zero]`. Use `⟨fun y i j => ?_, ?_⟩` and prove the remaining obligations. Use `show algebraMap B F (T.tr (U.x i * y * T.st (U.x j))) = _`. Conclude with `key y i j`.

Introduce `hp hq hpq`. Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `c ⟨b, b', rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Use `show algebraMap B F (T.tr ((b : E) * T.st (b' : E))) = 0`.

Take `⟨z, hz'⟩` from `b.2`. Establish `hb : r (b : E) = 0`. Rewrite using `[← hz']`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, map_mul]`. Establish `hpp` using `hep p`.

Rewrite `hpp` using `[hp]`. Establish `hqq` using `hep q`. Rewrite `hqq` using `[hq]`. Rewrite using `[hpp, hqq, ← mul_assoc, Matrix.single_mul_mul_single, hr z p q (by rw [hp, hq]; exact hpq)]`. Simplify using the standard rewrite rules.

Rewrite using `[h4, map_sum]`. Use `Finset.sum_eq_zero (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[key, map_mul, hb, zero_mul, Matrix.zero_apply]`.
-/
theorem UpperTheory.V.AlgebraTools.vr_reduction :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) {F : Type} [CommRing F] [Algebra B F] (r : E →ₐ[B] Matrix ι ι F) (p q : ι), (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (o i) i 1) → (∀ y i j, o i ≠ o j → r y i j = 0) → (∀ y i j, algebraMap B F (U.vr p q y i j).ev = r y i j) ∧ (o p = p → o q = q → p ≠ q → (U.oddForm p q).red ≤ RingHom.ker (algebraMap B F)) := by
  intro B E _ _ _ T ι _ _ o U F _ _ r p q hst hx hr
  obtain ⟨-, -, h3, h4, h5, -, h7⟩ := units_basic T o U
  have hep : ∀ k, r (U.ep (o k)) = Matrix.single (o k) (o k) 1 := by
    intro k
    rw [← U.x_base k, hx, U.o_o]
  have hz : ∀ w i j, r (U.x i * w * T.st (U.x j)) = Matrix.single (o i) (o j) (r w i j) := by
    intro w i j
    rw [map_mul, map_mul, hst, hx, hx, Matrix.transpose_single, Matrix.single_mul_mul_single, one_mul, mul_one]
  have key : ∀ w i j, algebraMap B F (T.tr (U.x i * w * T.st (U.x j))) = r w i j := by
    intro w i j
    by_cases hij : o i = o j
    · have e := congrArg (fun M => M (o i) (o j)) (hz w i j)
      simp only [Matrix.single_apply_same] at e
      rw [← e]
      conv_rhs => rw [h5 i j w hij, map_smul, hep i, ← hij]
      simp [Matrix.smul_apply, Algebra.smul_def]
    · rw [hr w i j hij, ← h7 i j w, h3 _ _ _ hij, map_zero]
  refine ⟨fun y i j => ?_, ?_⟩
  · show algebraMap B F (T.tr (U.x i * y * T.st (U.x j))) = _
    exact key y i j
  · intro hp hq hpq
    refine Ideal.span_le.mpr ?_
    rintro c ⟨b, b', rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show algebraMap B F (T.tr ((b : E) * T.st (b' : E))) = 0
    obtain ⟨z, hz'⟩ := b.2
    have hb : r (b : E) = 0 := by
      rw [← hz']
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, map_mul]
      have hpp := hep p
      rw [hp] at hpp
      have hqq := hep q
      rw [hq] at hqq
      rw [hpp, hqq, ← mul_assoc, Matrix.single_mul_mul_single, hr z p q (by rw [hp, hq]; exact hpq)]
      simp
    rw [h4, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [key, map_mul, hb, zero_mul, Matrix.zero_apply]
