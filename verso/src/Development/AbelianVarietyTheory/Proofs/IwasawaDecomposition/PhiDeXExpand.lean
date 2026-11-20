import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncreasingRowChoicePerColumn
open MvPolynomial

noncomputable section
namespace GlobalTheory.WeylLatDualProof

/- English proof (translation)
Unfold `PI.WwCauchyBinet.minY GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod, map_prod]`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Unfold `Formalism.GradedWeylDivisibility.initMinor`.

Rewrite using `[RingHom.map_det, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Establish `hj : (j : ℕ) < N` using `lt_of_lt_of_le j.2 (GlobalTheory.WeylMinorDual.colLen_le (hY s) c)`. Simplify using `[WeylLatticeDuality.colsOf, hj, Fin.castLE]`.
-/
theorem minY_colsOf_eq (p : ℕ) [Fact p.Prime] {Lt T : Type} [Fintype Lt] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (y : T → Matrix (Fin N) (Fin N) ℂ_[p])
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    PI.WwCauchyBinet.minY N nu J (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
        (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) (J s))) := by
  unfold PI.WwCauchyBinet.minY GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (GlobalTheory.WeylMinorDual.colLen_le (hY s) c)
  simp [WeylLatticeDuality.colsOf, hj, Fin.castLE]

/- English proof (translation)
Establish `h0 : (Int.castRingHom ℂ_[p]) = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ)` using `RingHom.ext_int _ _`. Rewrite using `[h0, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J]`. Repeatedly rewrite using `[hb, map_sum, map_smul]`. Rewrite using `[Fintype.prod_sum, map_sum]`. Use `Finset.sum_congr rfl fun κ _ => ?_` and prove the remaining obligations.

Simplify using `only [smul_eq_C_mul, Finset.prod_mul_distrib, map_mul, map_prod, MvPolynomial.map_C]`. Use `congr 1`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem map_nablaX_expand (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ)
    (hb : ∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k)
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
      ∑ κ : (∀ s, ι s), (∏ s, ((c s (J s) (κ s) : ℤ) : ℂ_[p])) •
        MvPolynomial.map (algebraMap ℚ ℂ_[p]) (∏ s, MvPolynomial.rename (sig N s) (b s (κ s))) := by
  have h0 : (Int.castRingHom ℂ_[p]) = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
  rw [h0, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J]
  simp_rw [hb, map_sum, map_smul]
  rw [Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_mul, map_prod, MvPolynomial.map_C]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  simp

/- English proof (translation)
Introduce `p _ Lt T _ _ _ e N nu hY ι _ b g c hb hg φ y`. Establish `h1` using `cauchy_binet_minors Lt ℂ_[p] N nu (fun s => WeylLatticeDuality.colsOf (y (e s)))`. Rewrite `h1` using `[finsum_eq_sum_of_fintype]`. Establish `h2 : WeylLatticeDuality.DeX N nu (fun s => WeylLatticeDuality.colsOf (y (e s))) = ∑ J : (∀ s, IncreasingRowChoicePerColumn N (nu s)), MvPolynomial.C (PI.WwCauchyBinet.minY N nu J (fun s => WeylLatticeDuality.colsOf (y (e s)))) * MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatti …`. Use `h1 using 2` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `all_goals try rfl`. Establish `hG : ∀ s k, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2) (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k)) = ∑ J, ((c s J k : ℤ) : ℂ_[p]) * MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2) (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDua …`. Introduce `s k`. Rewrite using `[hg]`. Simplify using `[map_sum, smul_eq_C_mul]`.

Rewrite using `[h2, map_sum]`. Repeatedly rewrite using `[MvPolynomial.C_mul', map_smul, map_nablaX_expand p N nu hY ι b c hb, minY_colsOf_eq p e N nu hY y, map_sum, map_smul, smul_eq_mul, hG, Fintype.prod_sum]`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phi_DeX_expand : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, g s k = ∑ J, (c s J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]),
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) := by
  intro p _ Lt T _ _ _ e N nu hY ι _ b g c hb hg φ y
  have h1 := cauchy_binet_minors Lt ℂ_[p] N nu (fun s => WeylLatticeDuality.colsOf (y (e s)))
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 : WeylLatticeDuality.DeX N nu (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∑ J : (∀ s, IncreasingRowChoicePerColumn N (nu s)), MvPolynomial.C (PI.WwCauchyBinet.minY N nu J
        (fun s => WeylLatticeDuality.colsOf (y (e s)))) *
        MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) := by
    convert h1 using 2
    all_goals try rfl
  have hG : ∀ s k, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
      (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k)) = ∑ J, ((c s J k : ℤ) : ℂ_[p]) *
        MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
          (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J)) := by
    intro s k
    rw [hg]
    simp [map_sum, smul_eq_C_mul]
  rw [h2, map_sum]
  simp_rw [MvPolynomial.C_mul', map_smul, map_nablaX_expand p N nu hY ι b c hb, minY_colsOf_eq p e N nu hY y,
    map_sum, map_smul, smul_eq_mul, hG, Fintype.prod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.WeylLatDualProof
