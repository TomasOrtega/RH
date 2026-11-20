import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundlesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmpleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SumMonomialAddSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsDimSymmetricAmplePowEqMulPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MatrixPolynomialDetNormFixedPointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseTorsionAndEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsPowerGrowthVolumePullFiniteEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqProdOfMul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSqAddSubDvd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
namespace GlobalTheory.SectionCount
open Polynomial

def PolyHom (n : ℕ) (D : ℤ[X] → ℚ) : Prop :=
  ∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous n ∧ ∀ a : Fin r → ℤ,
    D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ

/- English proof (translation)
Introduce `r`. Take `⟨Φ, hΦ, hD⟩` from `h r`. Use `⟨MvPolynomial.C c⁻¹ * Φ, ?_, fun a => ?_⟩` and prove the remaining obligations. Simplify using `using (MvPolynomial.isHomogeneous_C (Fin r) c⁻¹).mul hΦ`. Simplify using `only [hD a, map_mul, MvPolynomial.eval_C]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem PolyHom.div {n : ℕ} {D : ℤ[X] → ℚ} (h : PolyHom n D) (c : ℚ) : PolyHom n (fun F => D F / c) := by
  intro r
  obtain ⟨Φ, hΦ, hD⟩ := h r
  refine ⟨MvPolynomial.C c⁻¹ * Φ, ?_, fun a => ?_⟩
  · simpa using (MvPolynomial.isHomogeneous_C (Fin r) c⁻¹).mul hΦ
  · simp only [hD a, map_mul, MvPolynomial.eval_C]
    ring

/- English proof (translation)
Introduce `r`. Take `⟨Φ, hΦ, hD⟩` from `h (2 * r)`. Set `q : Fin (2 * r) → MvPolynomial (Fin r) ℚ` to `fun k => ∑ i : Fin r, ∑ j : Fin r, if (i : ℕ) + j = k then MvPolynomial.X i * MvPolynomial.X j else 0`. Establish `hq : ∀ k, (q k).IsHomogeneous 2`. Introduce `k`.

Use `MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `(MvPolynomial.isHomogeneous_X ℚ i).mul (MvPolynomial.isHomogeneous_X ℚ j)`. Conclude with `MvPolynomial.isHomogeneous_zero _ _ _`. Use `⟨MvPolynomial.aeval q Φ, hΦ.aeval q hq, fun a => ?_⟩` and prove the remaining obligations.

Set `b : Fin (2 * r) → ℤ` to `fun k => ∑ i : Fin r, ∑ j : Fin r, if (i : ℕ) + j = k then a i * a j else 0`. Establish `e : (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) ^ 2 = ∑ k : Fin (2 * r), Polynomial.monomial (k : ℕ) (b k)`. Simplify using `only [b, map_sum]`. Rewrite using `[pow_two, Finset.sum_mul_sum, Finset.sum_comm (γ := Fin (2 * r))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm (γ := Fin (2 * r))]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (⟨i + j, by omega⟩ : Fin (2 * r))]`. Simplify using `[monomial_mul_monomial]`. Introduce `k _ hk`.

Rewrite using `[if_neg, map_zero]`. Introduce `h'`. Conclude with `hk (Fin.ext h'.symm)`. Simplify using the standard rewrite rules. Use `show D _ = _`.

Rewrite using `[e, hD b]`. Establish `: (fun k => (b k : ℚ)) = fun k => MvPolynomial.eval (fun i => (a i : ℚ)) (q k)`. Use function extensionality and compare the values at `k`. Simplify using `only [b, q, map_sum, Int.cast_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[this, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_eq_eval_map]`. Establish `h2 : ((MvPolynomial.eval fun i => (a i : ℚ)).comp (algebraMap ℚ (MvPolynomial (Fin r) ℚ))) = RingHom.id ℚ`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite using `[h2, MvPolynomial.map_id]`. Both sides reduce to the same expression.
-/
theorem PolyHom.sq {n : ℕ} {D : ℤ[X] → ℚ} (h : PolyHom n D) : PolyHom (2 * n) (fun F => D (F ^ 2)) := by
  classical
  intro r
  obtain ⟨Φ, hΦ, hD⟩ := h (2 * r)
  let q : Fin (2 * r) → MvPolynomial (Fin r) ℚ := fun k =>
    ∑ i : Fin r, ∑ j : Fin r, if (i : ℕ) + j = k then MvPolynomial.X i * MvPolynomial.X j else 0
  have hq : ∀ k, (q k).IsHomogeneous 2 := by
    intro k
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_
    split_ifs
    · exact (MvPolynomial.isHomogeneous_X ℚ i).mul (MvPolynomial.isHomogeneous_X ℚ j)
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  refine ⟨MvPolynomial.aeval q Φ, hΦ.aeval q hq, fun a => ?_⟩
  let b : Fin (2 * r) → ℤ := fun k => ∑ i : Fin r, ∑ j : Fin r, if (i : ℕ) + j = k then a i * a j else 0
  have e : (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) ^ 2 =
      ∑ k : Fin (2 * r), Polynomial.monomial (k : ℕ) (b k) := by
    simp only [b, map_sum]
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_comm (γ := Fin (2 * r))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (γ := Fin (2 * r))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (⟨i + j, by omega⟩ : Fin (2 * r))]
    · simp [monomial_mul_monomial]
    · intro k _ hk
      rw [if_neg, map_zero]
      intro h'
      exact hk (Fin.ext h'.symm)
    · simp
  show D _ = _
  rw [e, hD b]
  have : (fun k => (b k : ℚ)) = fun k => MvPolynomial.eval (fun i => (a i : ℚ)) (q k) := by
    funext k
    simp only [b, q, map_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [this, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_eq_eval_map]
  have h2 : ((MvPolynomial.eval fun i => (a i : ℚ)).comp (algebraMap ℚ (MvPolynomial (Fin r) ℚ))) = RingHom.id ℚ := by
    ext x; simp
  rw [h2, MvPolynomial.map_id]
  rfl

/- English proof (translation)
Take `⟨Φ, -, hD⟩` from `h (F.natDegree + 1)`. Use `⟨MvPolynomial.aeval (fun i : Fin (F.natDegree + 1) => (C (F.coeff i : ℚ) + if i = 0 then X else 0 : ℚ[X])) Φ, fun t => ?_⟩` and prove the remaining obligations. Establish `e : F + t = ∑ i : Fin (F.natDegree + 1), Polynomial.monomial (i : ℕ) (F.coeff i + if i = 0 then (t : ℤ) else 0)`. Simplify using `only [map_add, Finset.sum_add_distrib]`. Use `congr 1`.

Use `conv_lhs => rw [F.as_sum_range]`. Conclude with `(Fin.sum_univ_eq_sum_range (fun i => monomial i (F.coeff i)) _).symm`. Rewrite using `[Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Rewrite using `[if_neg hk, map_zero]`. Simplify using the standard rewrite rules. Rewrite using `[e, hD, ← Polynomial.coe_evalRingHom, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_eq_eval_map]`. Establish `h2 : ((evalRingHom (t : ℚ)).comp (algebraMap ℚ ℚ[X])) = RingHom.id ℚ`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite using `[h2, MvPolynomial.map_id]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases hi : i = 0 <;> simp [hi]`.
-/
theorem PolyHom.exists_shift {n : ℕ} {D : ℤ[X] → ℚ} (h : PolyHom n D) (F : ℤ[X]) :
    ∃ p : ℚ[X], ∀ t : ℕ, D (F + t) = p.eval (t : ℚ) := by
  classical
  obtain ⟨Φ, -, hD⟩ := h (F.natDegree + 1)
  refine ⟨MvPolynomial.aeval (fun i : Fin (F.natDegree + 1) =>
    (C (F.coeff i : ℚ) + if i = 0 then X else 0 : ℚ[X])) Φ, fun t => ?_⟩
  have e : F + t = ∑ i : Fin (F.natDegree + 1),
      Polynomial.monomial (i : ℕ) (F.coeff i + if i = 0 then (t : ℤ) else 0) := by
    simp only [map_add, Finset.sum_add_distrib]
    congr 1
    · conv_lhs => rw [F.as_sum_range]
      exact (Fin.sum_univ_eq_sum_range (fun i => monomial i (F.coeff i)) _).symm
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk
        rw [if_neg hk, map_zero]
      · simp
  rw [e, hD, ← Polynomial.coe_evalRingHom, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left,
    MvPolynomial.eval₂_eq_eval_map]
  have h2 : ((evalRingHom (t : ℚ)).comp (algebraMap ℚ ℚ[X])) = RingHom.id ℚ := by
    ext x; simp
  rw [h2, MvPolynomial.map_id]
  congr 2
  funext i
  by_cases hi : i = 0 <;> simp [hi]

/- English proof (translation)
Take `⟨p, hp⟩` from `h.exists_shift F`. Take `⟨q, hq⟩` from `h.exists_shift G`. Establish `: p = q`. Take `⟨N, hN⟩` from `Filter.eventually_atTop.1 e`. Use `Polynomial.eq_of_infinite_eval_eq p q ?_` and prove the remaining obligations.

Use `Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((N + k : ℕ) : ℚ)) ?_ ?_` and prove the remaining obligations. Introduce `a b hab`. Use `Nat.cast_injective (R := ℚ) hab` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `k show p.eval _ = q.eval _`.

Rewrite using `[← hp, ← hq]`. Conclude with `hN _ (by omega)`. Establish `h1` using `hp 0`. Establish `h2` using `hq 0`. Simplify using `only [Nat.cast_zero, add_zero] at h1 h2`.

Rewrite using `[h1, h2, this]`.
-/
theorem PolyHom.eq_of_eventually {n : ℕ} {D : ℤ[X] → ℚ} (h : PolyHom n D) (F G : ℤ[X])
    (e : ∀ᶠ t : ℕ in Filter.atTop, D (F + t) = D (G + t)) : D F = D G := by
  obtain ⟨p, hp⟩ := h.exists_shift F
  obtain ⟨q, hq⟩ := h.exists_shift G
  have : p = q := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 e
    refine Polynomial.eq_of_infinite_eval_eq p q ?_
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((N + k : ℕ) : ℚ)) ?_ ?_
    · intro a b hab
      have := Nat.cast_injective (R := ℚ) hab
      omega
    · intro k
      show p.eval _ = q.eval _
      rw [← hp, ← hq]
      exact hN _ (by omega)
  have h1 := hp 0
  have h2 := hq 0
  simp only [Nat.cast_zero, add_zero] at h1 h2
  rw [h1, h2, this]

/- English proof (translation)
Set `φ : ℤ[X] →+ Q` to `AddMonoidHom.mk' (fun F => act F x) (fun F G => hadd F G x)`. Establish `hp : ∀ n : ℕ, aeval s (X ^ n : ℤ[X]) x = act (X ^ n) x`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [h1]`.

Consider the case `succ n ih => rw [pow_succ', hX, ← ih]`. Simplify using the standard rewrite rules. Proceed by induction on `F using Polynomial.induction_on' with`. Consider the case `add p q hp' hq' => rw [map_add, LinearMap.add_apply, hp', hq', hadd]`. Consider the case `monomial n a`.

Establish `: (monomial n a : ℤ[X]) = a • X ^ n`. Rewrite using `[← C_mul_X_pow_eq_monomial, smul_eq_C_mul]`. Rewrite using `[this, map_smul, LinearMap.smul_apply, hp]`. Conclude with `(map_zsmul φ a (X ^ n)).symm`.
-/
theorem aeval_eq_of_act {Q : Type} [AddCommGroup Q] (s : Module.End ℤ Q) (act : ℤ[X] → Q → Q)
    (h1 : ∀ x, act 1 x = x) (hadd : ∀ F G x, act (F + G) x = act F x + act G x)
    (hX : ∀ F x, act (X * F) x = s (act F x)) (F : ℤ[X]) (x : Q) : aeval s F x = act F x := by
  let φ : ℤ[X] →+ Q := AddMonoidHom.mk' (fun F => act F x) (fun F G => hadd F G x)
  have hp : ∀ n : ℕ, aeval s (X ^ n : ℤ[X]) x = act (X ^ n) x := by
    intro n
    induction n with
    | zero => simp [h1]
    | succ n ih => rw [pow_succ', hX, ← ih]; simp
  induction F using Polynomial.induction_on' with
  | add p q hp' hq' => rw [map_add, LinearMap.add_apply, hp', hq', hadd]
  | monomial n a =>
    have : (monomial n a : ℤ[X]) = a • X ^ n := by
      rw [← C_mul_X_pow_eq_monomial, smul_eq_C_mul]
    rw [this, map_smul, LinearMap.smul_apply, hp]
    exact (map_zsmul φ a (X ^ n)).symm

end GlobalTheory.SectionCount

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
namespace GlobalTheory.SectionCount

variable {K : Type} [Field K] [IsAlgClosed K]

noncomputable def ptEnd (P : Out.PolAV (Sp K)) (s : P.A ⟶ P.A) [IsMonHom s] :
    Module.End ℤ (Additive (Out.baseOver (Sp K) ⟶ P.A)) :=
  (AddMonoidHom.mk' (fun x : Additive (Out.baseOver (Sp K) ⟶ P.A) =>
    Additive.ofMul (x.toMul ≫ s)) (fun x y => by
      rw [toMul_add, ← ofMul_mul, MonObj.mul_comp])).toIntLinearMap

/- English proof (translation)
Rewrite using `[Out.linComb, List.prod_ofFn, ofMul_prod]`. Simplify using `only [ofMul_pow]`.
-/
theorem linComb_eq (P : Out.PolAV (Sp K)) {m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ P.A)) (c : Fin m → ℕ) :
    Additive.ofMul (Out.linComb pt c) = ∑ i, c i • Additive.ofMul (pt i) := by
  rw [Out.linComb, List.prod_ofFn, ofMul_prod]
  simp only [ofMul_pow]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hact : ∀ (F : Polynomial ℤ) (x : Additive (Out.baseOver (Sp K) ⟶ P.A)), Polynomial.aeval (ptEnd P s) F x = Additive.ofMul (x.toMul ≫ ev F)`. Use `aeval_eq_of_act (ptEnd P s) (fun F x => Additive.ofMul (x.toMul ≫ ev F)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `x`. Simplify using `[h1]`.

Introduce `F G x`. Rewrite using `[hadd, MonObj.comp_mul, ofMul_mul]`. Introduce `F x`. Rewrite using `[hX, ← Category.assoc]`. Both sides reduce to the same expression.

Establish `hcard : ∀ j : ℕ, Nat.card {x : Additive (Out.baseOver (Sp K) ⟶ P.A) // l ^ j • x = 0} = l ^ (2 * P.g * j)`. Introduce `j`. Use `(hL.mulN (Sp K) P (l ^ j) (Nat.one_le_pow _ _ hp.pos)).2.2.2.2 K (𝟙 _) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl)` as an intermediate fact. Rewrite using `[mul_comm (2 * P.g) j, pow_mul, ← this]`. Conclude with `Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun x => Iff.rfl)`.

Take `⟨U, hU1, hU2, hU3⟩` from `GlobalTheory.T.matrix_polynomial_det_norm_fixed_points l (2 * P.g) _ (ptEnd P s) hcard`. Establish `eq : ∀ F, {x : Additive (Out.baseOver (Sp K) ⟶ P.A) // Polynomial.aeval (ptEnd P s) F x = 0} ≃ {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ ev F = 1}` using `fun F => Equiv.subtypeEquiv Additive.toMul fun x => by rw [hact]; exact Iff.rfl`. Use `⟨U, fun F hF => ?_, fun F hF => ?_, fun j pt Mat hb ha => ?_⟩` and prove the remaining obligations. Rewrite using `[hU1 F (Finite.of_equiv _ (eq F).symm), Nat.card_congr (eq F)]`. Use `(GlobalTheory.PrimePowerTorsion.dense_torsion_and_eq_one hL hL2 K P l hp hl).2 _ fun j x hx => ?_` and prove the remaining obligations.

Use `hU2 F hF j (Additive.ofMul x) hx` as an intermediate fact. Rewrite `this` using `[hact]`. Conclude with `this`. Use `hU3 j (fun i => Additive.ofMul (pt i)) Mat (fun i => hb.pow_eq_one i) (fun y hy => ?_) (fun i => ?_)` and prove the remaining obligations. Use `hb.existsUnique (y := y.toMul) hy` as an intermediate fact.

Simplify using `only [← linComb_eq]`. Conclude with `this`. Rewrite using `[← linComb_eq, ← ha.comp_eq i]`. Both sides reduce to the same expression.
-/
theorem exists_matrix (hL : Out.Laws) (hL2 : Out.Laws2) (P : Out.PolAV (Sp K)) (s : P.A ⟶ P.A) [IsMonHom s]
    (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (ev : Polynomial ℤ → (P.A ⟶ P.A)) (h1 : ev 1 = 𝟙 P.A)
    (hadd : ∀ F G, ev (F + G) = ev F * ev G) (hX : ∀ F, ev (Polynomial.X * F) = ev F ≫ s) :
    ∃ U : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) ℤ_[l],
      (∀ F : Polynomial ℤ, Finite {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ ev F = 1} →
        ‖(Polynomial.aeval U F).det‖ =
          ‖((Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ ev F = 1} : ℕ) : ℚ_[l])‖) ∧
      (∀ F : Polynomial ℤ, Polynomial.aeval U F = 0 → ev F = 1) ∧
      ∀ (j : ℕ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A))
        (Mat : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ j))),
        TorsBasis P.A (l ^ j) pt → ActsBy pt s Mat → PadicInt.toZModPow j U.det = Mat.det := by
  have hp : l.Prime := Fact.out
  have hact : ∀ (F : Polynomial ℤ) (x : Additive (Out.baseOver (Sp K) ⟶ P.A)),
      Polynomial.aeval (ptEnd P s) F x = Additive.ofMul (x.toMul ≫ ev F) := by
    refine aeval_eq_of_act (ptEnd P s) (fun F x => Additive.ofMul (x.toMul ≫ ev F)) ?_ ?_ ?_
    · intro x; simp [h1]
    · intro F G x
      rw [hadd, MonObj.comp_mul, ofMul_mul]
    · intro F x
      rw [hX, ← Category.assoc]
      rfl
  have hcard : ∀ j : ℕ, Nat.card {x : Additive (Out.baseOver (Sp K) ⟶ P.A) // l ^ j • x = 0} =
      l ^ (2 * P.g * j) := by
    intro j
    have := (hL.mulN (Sp K) P (l ^ j) (Nat.one_le_pow _ _ hp.pos)).2.2.2.2 K (𝟙 _)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl)
    rw [mul_comm (2 * P.g) j, pow_mul, ← this]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun x => Iff.rfl)
  obtain ⟨U, hU1, hU2, hU3⟩ := GlobalTheory.T.matrix_polynomial_det_norm_fixed_points l (2 * P.g) _ (ptEnd P s) hcard
  have eq : ∀ F, {x : Additive (Out.baseOver (Sp K) ⟶ P.A) // Polynomial.aeval (ptEnd P s) F x = 0} ≃
      {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ ev F = 1} := fun F =>
    Equiv.subtypeEquiv Additive.toMul fun x => by rw [hact]; exact Iff.rfl
  refine ⟨U, fun F hF => ?_, fun F hF => ?_, fun j pt Mat hb ha => ?_⟩
  · rw [hU1 F (Finite.of_equiv _ (eq F).symm), Nat.card_congr (eq F)]
  · refine (GlobalTheory.PrimePowerTorsion.dense_torsion_and_eq_one hL hL2 K P l hp hl).2 _ fun j x hx => ?_
    have := hU2 F hF j (Additive.ofMul x) hx
    rw [hact] at this
    exact this
  · refine hU3 j (fun i => Additive.ofMul (pt i)) Mat (fun i => hb.pow_eq_one i) (fun y hy => ?_) (fun i => ?_)
    · have := hb.existsUnique (y := y.toMul) hy
      simp only [← linComb_eq]
      exact this
    · rw [← linComb_eq, ← ha.comp_eq i]
      rfl

/- English proof (translation)
Introduce `hL hL2 K _ _ P M s l hp hl hM hamp hsym hform`. Use `haveI : Fact l.Prime := ⟨hp⟩`. Use `haveI : IsMonHom s := hform.1`. Take `⟨δ, -, hvol, hH⟩` from `GlobalTheory.sectionsDim_symmetricAmple_pow_eq_mul_pow hL hL2 K P M hM hamp hsym`. Use `⟨δ, hvol, hH, ?_⟩` and prove the remaining obligations.

Take `⟨⟨ev, h1, hadd, hX⟩, hev⟩` from `GlobalTheory.T.polarisationForm_intPolynomial_bundles hL hL2 K P M s hM hform`. Take `⟨hmon, hmul, -, hsq, -, hone, hXM⟩` from `hev ev h1 hadd hX`. Take `⟨D, hDp, hDv, hDe⟩` from `GlobalTheory.VolPoly.exists_vol_poly hL hL2 K P M s hM hform ev h1 hadd hX`. Take `⟨U, hU1, hU2, hU3⟩` from `exists_matrix hL hL2 P s l hl ev h1 hadd hX`. Use `replace hDp : PolyHom P.g D := hDp`.

Establish `hB : ∀ F, (cubeLB P.A ![𝟙 P.A, ev F] P.L).IsLB` using `fun F => DVR.linComb_isLB _ P.isLB _ _`. Establish `uniq : ∀ F (a : ℝ), Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L) → Vol P.A.hom (cubeLB P.A ![𝟙 P.A, ev F] P.L) P.g a → (D F : ℝ) = a` using `fun F a h h' => (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g (hB F)).2.1 _ _ (hDv F h) h'`. Establish `fa` using `fun (ψ : P.A ⟶ P.A) (N : LB P.A.left) (n : ℕ) (hn : 0 < n) (hN : N.IsLB) (hψ : IsFinite ψ.left) => GlobalTheory.relAmple_finite_pow_iso (Sp K) P.A P.A ψ N n hn P.isAb P.isAb hN hψ`. Establish `hid : IsFinite (𝟙 P.A : P.A ⟶ P.A).left` using `by rw [Over.id_left]; infer_instance`. Establish `hsqr : ∀ F (N : LB P.A.left) (a : ℝ), N.IsLB → Out.RelAmple P.A N → Vol P.A.hom N P.g a → LBIso (cubeLB P.A ![𝟙 P.A, ev F] P.L) (lbPow N 2) → Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L) ∧ (D F : ℝ) = 2 ^ P.g * a`.

Introduce `F N a hN hA hV hI`. Establish `hN2 : (lbPow N 2).IsLB` using `DVR.linComb_isLB _ hN _ _`. Establish `hA2` using `(fa _ _ 1 one_pos hN2 hid).2.2.2 _ (hB F) hI.symm ((fa _ N 2 two_pos hN hid).2.1.2 hA)`. Use `⟨hA2, uniq F _ hA2 ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hN).2.2.2.1 2 a one_le_two hV` as an intermediate fact.

Conclude with `(GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hN2).2.2.1 _ _ (hB F) hI.symm (by simpa using this)`. Take `⟨hA1, hD1⟩` from `hsqr 1 P.L 1 P.isLB P.ample (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample hL hL2 K P).1 hone`. Take `⟨-, hDX⟩` from `hsqr Polynomial.X M δ hM hamp hvol (hXM hsym)`. Use `replace hD1 : D 1 = 2 ^ P.g := by exact_mod_cast (by simpa using hD1 : (D 1 : ℝ) = 2 ^ P.g)`. Use `replace hDX : D Polynomial.X = 2 ^ P.g * δ := by exact_mod_cast hDX`.

Establish `h2 : (2 : ℚ) ^ P.g ≠ 0` using `pow_ne_zero _ two_ne_zero`. Establish `hpull : ∀ (G F : Polynomial ℤ) (d : ℕ), IsFinite (ev G).left → MapDeg (ev G).left d → Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L) → Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (G ^ 2 * F)] P.L) ∧ D (G ^ 2 * F) = d * D F`. Introduce `G F d hf hd hA`. Establish `hP : ((cubeLB P.A ![𝟙 P.A, ev F] P.L).pull (ev G).left).IsLB` using `LB.isLB_pull (hB F) _`. Establish `hA2` using `(fa _ _ 1 one_pos hP hid).2.2.2 _ (hB _) (hsq F G).symm ((fa _ _ 1 one_pos (hB F) hf).1 hA)`.

Use `⟨hA2, ?_⟩` and prove the remaining obligations. Use `uniq _ _ hA2 ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hP).2.2.1 _ _ (hB _) (hsq F G).symm (GlobalTheory.T.sectionsPowerGrowthVolume_pull_finite_endomorphism K P (ev G) d _ _ (hmon G) hf hd (hB F) hA (hDv F hA)))` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hN : ∀ G, ((D (G ^ 2) / 2 ^ P.g : ℚ) : ℚ_[l]) = ((Polynomial.aeval U G).det : ℤ_[l])`. Use `GlobalTheory.PolyNorm.eq_det l (2 * P.g) U (fun G => D (G ^ 2) / 2 ^ P.g) (fun G => IsFinite (ev G).left) (hDp.sq.div (2 ^ P.g)) (by simp [hD1]) (fun F => (hDe F).mono fun t h => h.2) ?_ ?_` and prove the remaining obligations.

Introduce `F G hF hG`. Take `⟨-, e, hd⟩` from `GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel K P (ev F) (hmon F) hF`. Take `⟨-, e', hd'⟩` from `GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel K P (ev G) (hmon G) hG`. Take `⟨a1, a2⟩` from `hpull G 1 _ hG hd' hA1`. Establish `a3` using `(hpull F 1 _ hF hd hA1).2`.

Establish `a4` using `(hpull F _ _ hF hd a1).2`. Rewrite `a2`, `a3`, `a4` using `[_root_.mul_one]`. Use `show D ((F * G) ^ 2) / _ = D (F ^ 2) / _ * (D (G ^ 2) / _)`. Rewrite using `[mul_pow, a4, a3, hD1]`. Clear the denominators using the available nonvanishing facts.

Introduce `F hF`. Take `⟨hfin, e, hd⟩` from `GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel K P (ev F) (hmon F) hF`. Establish `a3` using `(hpull F 1 _ hF hd hA1).2`. Rewrite `a3` using `[_root_.mul_one]`. Use `show ‖((D (F ^ 2) / _ : ℚ) : ℚ_[l])‖ = _`.

Rewrite using `[a3, hD1, mul_div_assoc, div_self h2, _root_.mul_one, hU1 F hfin]`. Establish `hc : ‖((ringExpChar K : ℕ) : ℚ_[l])‖ = 1`. Rewrite using `[Padic.norm_natCast_eq_one_iff]`. Break down `expChar_is_prime_or_one K (ringExpChar K) with h | h` into its components or cases. Rewrite using `[Nat.coprime_primes hp h]`.

Introduce and unpack `rfl'`. Take `⟨q, hq⟩` from `ExpChar.exists K`. Establish `e1 : ringExpChar K = q` using `ringExpChar.eq K q`. Consider the cases of `hq with`. Consider the case `zero => rw [e1] at h`.

Conclude with `Nat.not_prime_one h`. Consider the case `prime hq => exact hl (by rw [rfl', e1]; exact CharP.cast_eq_zero K q)`. Rewrite using `[h]`. Conclude with `Nat.coprime_one_right l`. Use `push_cast`.

Rewrite using `[norm_mul, norm_pow, hc, one_pow, _root_.one_mul]`. Establish `hH0 : ∀ F H, Polynomial.aeval U H = 0 → D (F + H) / 2 ^ P.g = D F / 2 ^ P.g`. Introduce `F H h`. Use `congr 1`. Use `hDp.eq_of_eventually _ _ ((hDe F).mono fun t ht => ?_)` and prove the remaining obligations.

Establish `e : ev (F + H + t) = ev (F + t)`. Rewrite using `[add_right_comm, hadd (F + t) H, hU2 H h, _root_.mul_one]`. Use `uniq (F + H + t) (D (F + t)) (by rw [e]; exact ht.1) (by rw [e]; exact hDv _ ht.1)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `key` using `GlobalTheory.sq_eq_det_aeval_of_sq l (2 * P.g) P.g U (fun F => D F / 2 ^ P.g) (hDp.div (2 ^ P.g)) hN hH0 Polynomial.X`.

Rewrite `key` using `[hDX, mul_div_cancel_left₀ _ h2, Polynomial.aeval_X]`. Establish `key' : (δ : ℤ_[l]) ^ 2 = U.det`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← key]`. Use `push_cast`.

Both sides reduce to the same expression. Introduce `j pt Mat hb ha`. Rewrite using `[← hU3 j pt Mat hb ha, ← key']`. Simplify using the standard rewrite rules.
-/
theorem sq_vol_eq_det : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A) (l : ℕ), l.Prime → (l : K) ≠ 0 → M.IsLB → Out.RelAmple P.A M → SymB M → FormIs P M s → ∃ δ : ℕ, Vol P.A.hom M P.g δ ∧ (∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow M e) (δ * e ^ P.g)) ∧ ∀ (j : ℕ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A)) (Mat : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ j))), TorsBasis P.A (l ^ j) pt → ActsBy pt s Mat → (δ : ZMod (l ^ j)) ^ 2 = Mat.det := by
  intro hL hL2 K _ _ P M s l hp hl hM hamp hsym hform
  haveI : Fact l.Prime := ⟨hp⟩
  haveI : IsMonHom s := hform.1
  obtain ⟨δ, -, hvol, hH⟩ := GlobalTheory.sectionsDim_symmetricAmple_pow_eq_mul_pow hL hL2 K P M hM hamp hsym
  refine ⟨δ, hvol, hH, ?_⟩
  obtain ⟨⟨ev, h1, hadd, hX⟩, hev⟩ := GlobalTheory.T.polarisationForm_intPolynomial_bundles hL hL2 K P M s hM hform
  obtain ⟨hmon, hmul, -, hsq, -, hone, hXM⟩ := hev ev h1 hadd hX
  obtain ⟨D, hDp, hDv, hDe⟩ := GlobalTheory.VolPoly.exists_vol_poly hL hL2 K P M s hM hform ev h1 hadd hX
  obtain ⟨U, hU1, hU2, hU3⟩ := exists_matrix hL hL2 P s l hl ev h1 hadd hX
  replace hDp : PolyHom P.g D := hDp
  have hB : ∀ F, (cubeLB P.A ![𝟙 P.A, ev F] P.L).IsLB := fun F => DVR.linComb_isLB _ P.isLB _ _
  have uniq : ∀ F (a : ℝ), Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L) →
      Vol P.A.hom (cubeLB P.A ![𝟙 P.A, ev F] P.L) P.g a → (D F : ℝ) = a := fun F a h h' =>
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g (hB F)).2.1 _ _ (hDv F h) h'
  have fa := fun (ψ : P.A ⟶ P.A) (N : LB P.A.left) (n : ℕ) (hn : 0 < n) (hN : N.IsLB) (hψ : IsFinite ψ.left) =>
    GlobalTheory.relAmple_finite_pow_iso (Sp K) P.A P.A ψ N n hn P.isAb P.isAb hN hψ
  have hid : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := by rw [Over.id_left]; infer_instance

  have hsqr : ∀ F (N : LB P.A.left) (a : ℝ), N.IsLB → Out.RelAmple P.A N → Vol P.A.hom N P.g a →
      LBIso (cubeLB P.A ![𝟙 P.A, ev F] P.L) (lbPow N 2) →
      Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L) ∧ (D F : ℝ) = 2 ^ P.g * a := by
    intro F N a hN hA hV hI
    have hN2 : (lbPow N 2).IsLB := DVR.linComb_isLB _ hN _ _
    have hA2 := (fa _ _ 1 one_pos hN2 hid).2.2.2 _ (hB F) hI.symm ((fa _ N 2 two_pos hN hid).2.1.2 hA)
    refine ⟨hA2, uniq F _ hA2 ?_⟩
    have := (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hN).2.2.2.1 2 a one_le_two hV
    exact (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hN2).2.2.1 _ _ (hB F) hI.symm (by simpa using this)
  obtain ⟨hA1, hD1⟩ := hsqr 1 P.L 1 P.isLB P.ample (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample hL hL2 K P).1 hone
  obtain ⟨-, hDX⟩ := hsqr Polynomial.X M δ hM hamp hvol (hXM hsym)
  replace hD1 : D 1 = 2 ^ P.g := by exact_mod_cast (by simpa using hD1 : (D 1 : ℝ) = 2 ^ P.g)
  replace hDX : D Polynomial.X = 2 ^ P.g * δ := by exact_mod_cast hDX
  have h2 : (2 : ℚ) ^ P.g ≠ 0 := pow_ne_zero _ two_ne_zero

  have hpull : ∀ (G F : Polynomial ℤ) (d : ℕ), IsFinite (ev G).left → MapDeg (ev G).left d →
      Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L) →
      Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (G ^ 2 * F)] P.L) ∧ D (G ^ 2 * F) = d * D F := by
    intro G F d hf hd hA
    have hP : ((cubeLB P.A ![𝟙 P.A, ev F] P.L).pull (ev G).left).IsLB := LB.isLB_pull (hB F) _
    have hA2 := (fa _ _ 1 one_pos hP hid).2.2.2 _ (hB _) (hsq F G).symm ((fa _ _ 1 one_pos (hB F) hf).1 hA)
    refine ⟨hA2, ?_⟩
    have := uniq _ _ hA2 ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hP).2.2.1 _ _ (hB _) (hsq F G).symm
      (GlobalTheory.T.sectionsPowerGrowthVolume_pull_finite_endomorphism K P (ev G) d _ _ (hmon G) hf hd (hB F) hA (hDv F hA)))
    exact_mod_cast this
  have hN : ∀ G, ((D (G ^ 2) / 2 ^ P.g : ℚ) : ℚ_[l]) = ((Polynomial.aeval U G).det : ℤ_[l]) := by
    refine GlobalTheory.PolyNorm.eq_det l (2 * P.g) U (fun G => D (G ^ 2) / 2 ^ P.g) (fun G => IsFinite (ev G).left)
      (hDp.sq.div (2 ^ P.g)) (by simp [hD1]) (fun F => (hDe F).mono fun t h => h.2) ?_ ?_
    · intro F G hF hG
      obtain ⟨-, e, hd⟩ := GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel K P (ev F) (hmon F) hF
      obtain ⟨-, e', hd'⟩ := GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel K P (ev G) (hmon G) hG
      obtain ⟨a1, a2⟩ := hpull G 1 _ hG hd' hA1
      have a3 := (hpull F 1 _ hF hd hA1).2
      have a4 := (hpull F _ _ hF hd a1).2
      rw [_root_.mul_one] at a2 a3 a4
      show D ((F * G) ^ 2) / _ = D (F ^ 2) / _ * (D (G ^ 2) / _)
      rw [mul_pow, a4, a3, hD1]
      field_simp
    · intro F hF
      obtain ⟨hfin, e, hd⟩ := GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel K P (ev F) (hmon F) hF
      have a3 := (hpull F 1 _ hF hd hA1).2
      rw [_root_.mul_one] at a3
      show ‖((D (F ^ 2) / _ : ℚ) : ℚ_[l])‖ = _
      rw [a3, hD1, mul_div_assoc, div_self h2, _root_.mul_one, hU1 F hfin]
      have hc : ‖((ringExpChar K : ℕ) : ℚ_[l])‖ = 1 := by
        rw [Padic.norm_natCast_eq_one_iff]
        rcases expChar_is_prime_or_one K (ringExpChar K) with h | h
        · rw [Nat.coprime_primes hp h]
          rintro rfl'
          obtain ⟨q, hq⟩ := ExpChar.exists K
          have e1 : ringExpChar K = q := ringExpChar.eq K q
          cases hq with
          | zero => rw [e1] at h; exact Nat.not_prime_one h
          | prime hq => exact hl (by rw [rfl', e1]; exact CharP.cast_eq_zero K q)
        · rw [h]; exact Nat.coprime_one_right l
      push_cast
      rw [norm_mul, norm_pow, hc, one_pow, _root_.one_mul]
  have hH0 : ∀ F H, Polynomial.aeval U H = 0 → D (F + H) / 2 ^ P.g = D F / 2 ^ P.g := by
    intro F H h
    congr 1
    refine hDp.eq_of_eventually _ _ ((hDe F).mono fun t ht => ?_)
    have e : ev (F + H + t) = ev (F + t) := by
      rw [add_right_comm, hadd (F + t) H, hU2 H h, _root_.mul_one]
    have := uniq (F + H + t) (D (F + t)) (by rw [e]; exact ht.1) (by rw [e]; exact hDv _ ht.1)
    exact_mod_cast this
  have key := GlobalTheory.sq_eq_det_aeval_of_sq l (2 * P.g) P.g U (fun F => D F / 2 ^ P.g) (hDp.div (2 ^ P.g)) hN hH0
    Polynomial.X
  rw [hDX, mul_div_cancel_left₀ _ h2, Polynomial.aeval_X] at key
  have key' : (δ : ℤ_[l]) ^ 2 = U.det := by
    apply Subtype.ext
    rw [← key]
    push_cast
    rfl
  intro j pt Mat hb ha
  rw [← hU3 j pt Mat hb ha, ← key']
  simp

end GlobalTheory.SectionCount
