import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.DetSplit
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

section SlopeTestRemainingChoices

open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
open scoped Matrix

/- English proof (translation)
Simplify using `only [fockF, coeff_add, star_add, mul_add, add_mul, Finset.sum_add_distrib]`.
-/
private theorem fock_add_right {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    fockF f (g + g') = fockF f g + fockF f g' := by
  simp only [fockF, coeff_add, star_add, mul_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [fockF, coeff_smul, smul_eq_mul, star_mul', Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`.
-/
private theorem fock_smul_right {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (c • g) = star c * fockF f g := by
  simp only [fockF, coeff_smul, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

private noncomputable def fischer (σ : Type) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f h => fockF f (map (starRingEnd ℂ) h))
    (fun f f' h => by
      rw [Formalism.GradedWeylDivisibility.fockHerm σ _ (f + f'), fock_add_right, star_add, ← Formalism.GradedWeylDivisibility.fockHerm, ← Formalism.GradedWeylDivisibility.fockHerm])
    (fun c f h => by
      rw [Formalism.GradedWeylDivisibility.fockHerm σ _ (c • f), fock_smul_right, star_mul', star_star, ← Formalism.GradedWeylDivisibility.fockHerm, smul_eq_mul])
    (fun f h h' => by rw [map_add, fock_add_right])
    (fun c f h => by
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, fock_smul_right, smul_eq_mul]
      simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem fischer_apply {σ : Type} (f h : MvPolynomial σ ℂ) :
    fischer σ f h = fockF f (map (starRingEnd ℂ) h) := rfl

/- English proof (translation)
Proceed by induction on `h using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp]`.

Use `congr 1`. Simplify using `[rowAct]`.
-/
private theorem map_rowAct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : MvPolynomial (Fin n × Fin n) ℂ) :
    map (starRingEnd ℂ) (rowAct ℂ A h) = rowAct ℂ (Aᵀ)ᴴ (map (starRingEnd ℂ) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [rowAct]

/- English proof (translation)
Rewrite using `[fischer_apply, fischer_apply, Formalism.GradedWeylDivisibility.fockRowAdj, map_rowAct]`.
-/
private theorem fischer_adj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (f h : MvPolynomial (Fin n × Fin n) ℂ) :
    fischer _ (rowAct ℂ Aᵀ f) h = fischer _ f (rowAct ℂ A h) := by
  rw [fischer_apply, fischer_apply, Formalism.GradedWeylDivisibility.fockRowAdj, map_rowAct]

/- English proof (translation)
Establish `: (rowAct ℂ (n` using `n) A).comp (rowAct ℂ B) = AlgHom.id ℂ _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, rowAct, aeval_X, map_sum, map_mul, algHom_C, AlgHom.id_apply]`. Simplify using `only [algebraMap_eq, Finset.mul_sum, ← mul_assoc, ← C_mul]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, hAB, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single v.1]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules. Conclude with `DFunLike.congr_fun this h`.
-/
private theorem rowAct_rowAct {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : B * A = 1)
    (h : MvPolynomial (Fin n × Fin n) ℂ) : rowAct ℂ A (rowAct ℂ B h) = h := by
  have : (rowAct ℂ (n := n) A).comp (rowAct ℂ B) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rowAct, aeval_X, map_sum, map_mul, algHom_C, AlgHom.id_apply]
    simp only [algebraMap_eq, Finset.mul_sum, ← mul_assoc, ← C_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, hAB, Matrix.one_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  exact DFunLike.congr_fun this h

/- English proof (translation)
Introduce `h`. Establish `h1` using `GlobalTheory.Branching.genericDet_pow_mul_hw ℂ n 1 (fun _ => 0)`. Rewrite `h1` using `[h, pow_one, zero_mul]`. Conclude with `hwNe ℂ n n le_rfl _ h1.symm`.
-/
private theorem lp_ne (n : ℕ) : lpMinor ℂ n (le_refl n) (le_refl n) ≠ 0 := by
  intro h
  have h1 := GlobalTheory.Branching.genericDet_pow_mul_hw ℂ n 1 (fun _ => 0)
  rw [h, pow_one, zero_mul] at h1
  exact hwNe ℂ n n le_rfl _ h1.symm

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨c, hc, hdet⟩ : ∃ c : ℕ, (fun a => lam.natW a + c) = ν ∧ ∀ g : GL (Fin n) ℂ, detPow ℂ n g lam.detShift = detPow ℂ n g s * (g : Matrix (Fin n) (Fin n) ℂ).det ^ c := by`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Use `⟨0, funext fun a => a.elim0, fun g => ?_⟩` and prove the remaining obligations. Establish `: Matrix.GeneralLinearGroup.det g = 1` using `Units.ext (by simp)`.

Simplify using `[detPow, this]`. Establish `h3 : lam.detShift = lam.w ⟨n - 1, by omega⟩` using `by simp [DomWeight.detShift, hn]`. Use `⟨ν ⟨n - 1, by omega⟩, funext fun a => ?_, fun g => ?_⟩` and prove the remaining obligations. Establish `h1 : lam.w ⟨n - 1, by omega⟩ ≤ lam.w a` using `lam.anti (by`. Use `a.2` as an intermediate fact.

Rewrite using `[Fin.le_def]`. Simplify using `only`. Use the proof step `omega)`. Simplify using `only [DomWeight.natW, h3]`. Rewrite `h1` using `[hl, hl]`.

Rewrite using `[hl, hl]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h3, hl, add_comm, detPow, detPow, zpow_add, zpow_natCast]`. Simplify using the standard rewrite rules. Substitute `hc` using the available equality.

Take `⟨dm, de, -⟩` from `GlobalTheory.Branching.genericDet_pow_mul n c lam.natW`. Set `D : nablaSq ℂ n lam →ₗ[ℂ] dualWeyl ℂ n n (fun i => lam.natW i + c)` to `{ toFun := fun f => ⟨lpMinor ℂ n le_rfl le_rfl ^ c * f, dm f f.2⟩ map_add' := fun f f' => Subtype.ext (by simp [mul_add]) map_smul' := fun a f => Subtype.ext (by simp) }`. Use `⟨D, ⟨fun f f' e => Subtype.ext ?_, fun f => ?_⟩, fun g f => ?_⟩` and prove the remaining obligations. Conclude with `mul_left_cancel₀ (pow_ne_zero c (lp_ne n)) (congrArg Subtype.val e)`. Take `⟨f', hf', e⟩` from `PI.WMI.determinant_splitting_formula n lam.natW c (fun h => by simp [DomWeight.natW, DomWeight.detShift, h]) f f.2`.

Conclude with `⟨⟨f', hf'⟩, Subtype.ext e.symm⟩`. Express the relevant statement in the definitionally equal form `lpMinor ℂ n le_rfl le_rfl ^ c * sqAct ℂ n lam g f = detPow ℂ n g s • rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ (lpMinor ℂ n le_rfl le_rfl ^ c * (f : MvPolynomial (Fin n × Fin n) ℂ))`. Rewrite using `[de, sqAct, hdet, Matrix.det_transpose, mul_smul_comm, smul_smul]`.
-/
private theorem exists_j (n : ℕ) (ν : Fin n → ℕ) (s : ℤ) (lam : DomWeight n) (hl : ∀ a, lam.w a = (ν a : ℤ) + s) :
    ∃ j : nablaSq ℂ n lam →ₗ[ℂ] dualWeyl ℂ n n ν, Function.Bijective j ∧
      ∀ (g : GL (Fin n) ℂ) v, (j (GlobalTheory.Branching.sqRep ℂ n lam g v) : MvPolynomial (Fin n × Fin n) ℂ) =
        ((Matrix.GeneralLinearGroup.det g ^ s : ℂˣ) : ℂ) • rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ (j v) := by
  obtain ⟨c, hc, hdet⟩ : ∃ c : ℕ, (fun a => lam.natW a + c) = ν ∧ ∀ g : GL (Fin n) ℂ,
      detPow ℂ n g lam.detShift = detPow ℂ n g s * (g : Matrix (Fin n) (Fin n) ℂ).det ^ c := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨0, funext fun a => a.elim0, fun g => ?_⟩
      have : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
      simp [detPow, this]
    · have h3 : lam.detShift = lam.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
      refine ⟨ν ⟨n - 1, by omega⟩, funext fun a => ?_, fun g => ?_⟩
      · have h1 : lam.w ⟨n - 1, by omega⟩ ≤ lam.w a := lam.anti (by
          have := a.2
          rw [Fin.le_def]
          simp only
          omega)
        simp only [DomWeight.natW, h3]
        rw [hl, hl] at h1
        rw [hl, hl]
        omega
      · rw [h3, hl, add_comm, detPow, detPow, zpow_add, zpow_natCast]
        simp
  subst hc
  obtain ⟨dm, de, -⟩ := GlobalTheory.Branching.genericDet_pow_mul n c lam.natW
  let D : nablaSq ℂ n lam →ₗ[ℂ] dualWeyl ℂ n n (fun i => lam.natW i + c) :=
    { toFun := fun f => ⟨lpMinor ℂ n le_rfl le_rfl ^ c * f, dm f f.2⟩
      map_add' := fun f f' => Subtype.ext (by simp [mul_add])
      map_smul' := fun a f => Subtype.ext (by simp) }
  refine ⟨D, ⟨fun f f' e => Subtype.ext ?_, fun f => ?_⟩, fun g f => ?_⟩
  · exact mul_left_cancel₀ (pow_ne_zero c (lp_ne n)) (congrArg Subtype.val e)
  · obtain ⟨f', hf', e⟩ := PI.WMI.determinant_splitting_formula n lam.natW c
      (fun h => by simp [DomWeight.natW, DomWeight.detShift, h]) f f.2
    exact ⟨⟨f', hf'⟩, Subtype.ext e.symm⟩
  · change lpMinor ℂ n le_rfl le_rfl ^ c * sqAct ℂ n lam g f =
      detPow ℂ n g s • rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ
        (lpMinor ℂ n le_rfl le_rfl ^ c * (f : MvPolynomial (Fin n × Fin n) ℂ))
    rw [de, sqAct, hdet, Matrix.det_transpose, mul_smul_comm, smul_smul]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `n ν s lam hl`. Take `⟨j, hj, he⟩` from `exists_j n ν s lam hl`. Set `P : nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν →ₗ[ℂ] ℂ` to `(fischer _).compl₁₂ ((Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype ∘ₗ j) (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype`. Establish `hP : ∀ v u, P v u = fischer _ (j v : MvPolynomial (Fin n × Fin n) ℂ) u` using `fun _ _ => rfl`. Set `e` to `LinearEquiv.ofBijective j hj`.

Use `haveI : FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) := e.finiteDimensional`. Establish `hinj : Function.Injective P.flip`. Use `(injective_iff_map_eq_zero _).2 fun u hu => ?_` and prove the remaining obligations. Take `⟨v, hv⟩` from `hj.2 ⟨_, Formalism.GradedWeylDivisibility.dualWeylMap ℂ ℂ (starRingEnd ℂ) n n ν u u.2⟩`. Establish `h0 : P v u = 0` using `LinearMap.congr_fun hu v`.

Rewrite `h0` using `[hP, hv, fischer_apply]`. Assume the negation of the conclusion as `hne`. Establish `hne' : MvPolynomial.map (starRingEnd ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0` using `fun h => hne (Subtype.ext (MvPolynomial.map_injective _ (starRingEnd ℂ).injective (h.trans (map_zero _).symm)))`. Use `(Formalism.GradedWeylDivisibility.fockPos _ _ hne').1` as an intermediate fact. Rewrite `this` using `[h0]`.

Simplify using `at this`. Use `⟨P, ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩, fun g v u => ?_⟩` and prove the remaining obligations. Rewrite using `[← e.finrank_eq]`. Conclude with `(Subspace.dual_finrank_eq).symm`. Rewrite using `[hP, hP, he, map_smul, LinearMap.smul_apply, fischer_adj, Formalism.UG.dualWeylRep_apply, Formalism.UG.dwAct, rowAct_rowAct _ _ (by simp), smul_eq_mul]`.
-/
theorem UpperTheory.exists_invariant_perfect_pairing_nablaSq_dualWeyl :
    ∀ (n : ℕ) (ν : Fin n → ℕ) (s : ℤ) (lam : DomWeight n), (∀ a, lam.w a = (ν a : ℤ) + s) →
        ∃ P : nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν →ₗ[ℂ] ℂ, Function.Bijective P.flip ∧
          ∀ (g : GL (Fin n) ℂ) v u, P (GlobalTheory.Branching.sqRep ℂ n lam g v) (Formalism.UG.dualWeylRep ℂ n n ν g u) =
            ((Matrix.GeneralLinearGroup.det g ^ s : ℂˣ) : ℂ) * P v u := by
  intro n ν s lam hl
  obtain ⟨j, hj, he⟩ := exists_j n ν s lam hl
  let P : nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν →ₗ[ℂ] ℂ :=
    (fischer _).compl₁₂ ((Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype ∘ₗ j) (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype
  have hP : ∀ v u, P v u = fischer _ (j v : MvPolynomial (Fin n × Fin n) ℂ) u := fun _ _ => rfl
  let e := LinearEquiv.ofBijective j hj
  haveI : FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) := e.finiteDimensional
  have hinj : Function.Injective P.flip := by
    refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
    obtain ⟨v, hv⟩ := hj.2 ⟨_, Formalism.GradedWeylDivisibility.dualWeylMap ℂ ℂ (starRingEnd ℂ) n n ν u u.2⟩
    have h0 : P v u = 0 := LinearMap.congr_fun hu v
    rw [hP, hv, fischer_apply] at h0
    by_contra hne
    have hne' : MvPolynomial.map (starRingEnd ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0 := fun h =>
      hne (Subtype.ext (MvPolynomial.map_injective _ (starRingEnd ℂ).injective (h.trans (map_zero _).symm)))
    have := (Formalism.GradedWeylDivisibility.fockPos _ _ hne').1
    rw [h0] at this
    simp at this
  refine ⟨P, ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩, fun g v u => ?_⟩
  · rw [← e.finrank_eq]
    exact (Subspace.dual_finrank_eq).symm
  · rw [hP, hP, he, map_smul, LinearMap.smul_apply, fischer_adj, Formalism.UG.dualWeylRep_apply, Formalism.UG.dwAct,
      rowAct_rowAct _ _ (by simp), smul_eq_mul]
