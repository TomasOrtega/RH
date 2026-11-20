import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorIrreducibleNontrivial

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.JacCentral

/- English proof (translation)
Take `⟨s, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Establish `hs : S.toRepresentation g s = c • s` using `Subtype.ext (h s)`. Use `show Submodule.Quotient.mk (S.toRepresentation g s) = _`. Rewrite using `[hs, Submodule.Quotient.mk_smul]`.
-/
theorem subQuot_apply_of_smul {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) {g : G} {c : ℂ}
    (h : ∀ v, ρ g v = c • v) (y : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :
    subQuot S T g y = c • y := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hs : S.toRepresentation g s = c • s := Subtype.ext (h s)
  show Submodule.Quotient.mk (S.toRepresentation g s) = _
  rw [hs, Submodule.Quotient.mk_smul]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `h (le_antisymm (iSup₂_le fun r hr => ?_) bot_le)` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos r with rfl | hpos` into its components or cases. Simplify using the standard rewrite rules. Take `⟨S, T, -, -, hi⟩` from `hr`.

Conclude with `absurd ⟨S ⟨0, hpos⟩, T ⟨0, hpos⟩, hi ⟨0, hpos⟩⟩ hc`.
-/
theorem exists_step_of_jhMult_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : jhMult σ ρ ≠ 0) :
    ∃ S T : Subrepresentation ρ, Nonempty ((subQuot S T).Equiv σ) := by
  by_contra hc
  refine h (le_antisymm (iSup₂_le fun r hr => ?_) bot_le)
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · simp
  · obtain ⟨S, T, -, -, hi⟩ := hr
    exact absurd ⟨S ⟨0, hpos⟩, T ⟨0, hpos⟩, hi ⟨0, hpos⟩⟩ hc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Take `⟨⟨a, i⟩, rfl⟩` from `(stdBlocks d hd).surjective i`. Take `⟨⟨b, j⟩, rfl⟩` from `(stdBlocks d hd).surjective j`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Rewrite using `[leviEmb_apply_same]`. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply]`. Rewrite using `[leviEmb_apply_ne k _ _ hab]`. Establish `: (stdBlocks d hd) ⟨a, i⟩ ≠ (stdBlocks d hd) ⟨b, j⟩` using `fun h => by`.

Use `(stdBlocks d hd).injective h` as an intermediate fact. Conclude with `hab (congrArg Sigma.fst this)`. Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply, this]`.
-/
theorem leviEmb_scalar {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = N) (t : kˣ) :
    leviEmb k (stdBlocks d hd) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) =
      Matrix.GeneralLinearGroup.scalar (Fin N) t := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  · rw [leviEmb_apply_ne k _ _ hab]
    have : (stdBlocks d hd) ⟨a, i⟩ ≠ (stdBlocks d hd) ⟨b, j⟩ := fun h => by
      have := (stdBlocks d hd).injective h
      exact hab (congrArg Sigma.fst this)
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, this]

/- English proof (translation)
Establish `: Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t) = t ^ n` using `by ext; simp [Matrix.GeneralLinearGroup.scalar]`. Rewrite using `[this]`. Simplify using `[nabs]`.
-/
theorem nabs_det_scalar (n : ℕ) (t : kˣ) :
    nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t)) =
      nabs k t ^ n := by
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t) = t ^ n := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rw [this]
  simp [nabs]

/- English proof (translation)
Establish `h0 : modExp (fun a => Fin (d a)) (0 : Fin 2) = d 1`. Simplify using `[modExp, Finset.sum_filter, Fin.sum_univ_two]`. Establish `h1 : modExp (fun a => Fin (d a)) (1 : Fin 2) = -(d 0 : ℤ)`. Simplify using `[modExp, Finset.sum_filter, Fin.sum_univ_two]`. Establish `hm : modulus k (fun a => Fin (d a)) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1`.

Establish `hp` using `(nabs_pos' k t).ne'`. Rewrite using `[modulus, Fin.prod_univ_two, h0, h1, nabs_det_scalar, nabs_det_scalar, zpow_natCast, zpow_neg, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm (d 0) (d 1)]`. Conclude with `mul_inv_cancel₀ (pow_ne_zero _ hp)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[val_deltaHalf, hm]`.

Simplify using the standard rewrite rules.
-/
theorem deltaHalf_scalar (d : Fin 2 → ℕ) (t : kˣ) :
    deltaHalf k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
  have h0 : modExp (fun a => Fin (d a)) (0 : Fin 2) = d 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have h1 : modExp (fun a => Fin (d a)) (1 : Fin 2) = -(d 0 : ℤ) := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have hm : modulus k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
    have hp := (nabs_pos' k t).ne'
    rw [modulus, Fin.prod_univ_two, h0, h1, nabs_det_scalar, nabs_det_scalar, zpow_natCast, zpow_neg,
      zpow_natCast, ← pow_mul, ← pow_mul, mul_comm (d 0) (d 1)]
    exact mul_inv_cancel₀ (pow_ne_zero _ hp)
  apply Units.ext
  rw [val_deltaHalf, hm]
  simp

/- English proof (translation)
Proceed by induction on `w using PiTensorProduct.induction_on with`. Consider the case `add y z hy hz => rw [map_add, hy, hz, smul_add]`. Consider the case `smul_tprod r y`. Rewrite using `[map_smul, piTensor_tprod, smul_comm]`. Use `congr 1`.

Simplify using `only [hc]`. Conclude with `MultilinearMap.map_smul_univ _ _ _`.
-/
theorem piTensor_apply_of_smul {h : ℕ} (x : Fin h → IrrGL k) (g : ∀ a, GL (Fin (x a).1) k)
    (c : Fin h → ℂ) (hc : ∀ a v, (x a).rep (g a) v = c a • v)
    (w : PiTensorProduct ℂ (fun a => (x a).2.rep.V)) :
    piTensor (fun a => (x a).rep) g w = (∏ a, c a) • w := by
  induction w using PiTensorProduct.induction_on with
  | add y z hy hz => rw [map_add, hy, hz, smul_add]
  | smul_tprod r y =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    simp only [hc]
    exact MultilinearMap.map_smul_univ _ _ _

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_ne (0 : W)`. Take `⟨y, rfl⟩` from `E.toLinearEquiv.surjective w`. Establish `hE : E.toIntertwiningMap (ρ g y) = σ g (E.toIntertwiningMap y)` using `E.toIntertwiningMap.isIntertwining _ _ g y`. Rewrite `hE` using `[hρ, hσ, map_smul]`. Establish `h2 : (c - c') • E.toLinearEquiv y = 0`.

Rewrite using `[sub_smul, sub_eq_zero]`. Conclude with `hE`. Break down `smul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `(sub_eq_zero.1 h3).symm`. Conclude with `absurd h3 hw`.
-/
theorem smul_eq_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [Nontrivial W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (E : ρ.Equiv σ) {g : G} {c c' : ℂ} (hρ : ∀ v, ρ g v = c • v) (hσ : ∀ w, σ g w = c' • w) :
    c' = c := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨y, rfl⟩ := E.toLinearEquiv.surjective w
  have hE : E.toIntertwiningMap (ρ g y) = σ g (E.toIntertwiningMap y) :=
    E.toIntertwiningMap.isIntertwining _ _ g y
  rw [hρ, hσ, map_smul] at hE
  have h2 : (c - c') • E.toLinearEquiv y = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hE
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact (sub_eq_zero.1 h3).symm
  · exact absurd h3 hw

/- English proof (translation)
Introduce `k _ _ _ _ N V _ _ π x hd hj t c c0 c1 hc h0 h1`. Take `⟨S, T, ⟨E⟩⟩` from `exists_step_of_jhMult_ne_zero (show jhMult _ _ ≠ 0 from hj)`. Set `g : Levi k (fun a => Fin (x a).1)` to `fun a => Matrix.GeneralLinearGroup.scalar (Fin (x a).1) t`. Establish `hjac : ∀ v, jac (stdBlocks (fun a => (x a).1) hd) π g v = c • v`. Introduce `v`.

Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ v`. Rewrite using `[jac_mk, show deltaHalf k (fun a => Fin (x a).1) g = 1 from deltaHalf_scalar _ t, show leviEmb k (stdBlocks (fun a => (x a).1) hd) g = _ from leviEmb_scalar _ hd t, hc]`. Simplify using `[Submodule.Quotient.mk_smul]`. Set `cc : Fin 2 → ℂ` to `![c0, c1]`. Establish `hcc : ∀ a v, (x a).rep (g a) v = cc a • v`.

Introduce `a v`. Use `fin_cases a`. Conclude with `h0 v`. Conclude with `h1 v`. Use `haveI := GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL k x`.

Establish `hfin` using `smul_eq_of_equiv E (subQuot_apply_of_smul S T hjac) (piTensor_apply_of_smul x g cc hcc)`. Rewrite `hfin` using `[Fin.prod_univ_two]`. Conclude with `hfin`.
-/
theorem scalar_mul_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (x : Fin 2 → IrrGL k) (hd : ∑ a, (x a).1 = N), Zc.jm x hd π ≠ 0 → ∀ (t : kˣ) (c c0 c1 : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → Zl.ScalarBy (x 0) t c0 → Zl.ScalarBy (x 1) t c1 → c0 * c1 = c := by
  intro k _ _ _ _ N V _ _ π x hd hj t c c0 c1 hc h0 h1
  obtain ⟨S, T, ⟨E⟩⟩ := exists_step_of_jhMult_ne_zero (show jhMult _ _ ≠ 0 from hj)
  let g : Levi k (fun a => Fin (x a).1) := fun a => Matrix.GeneralLinearGroup.scalar (Fin (x a).1) t
  have hjac : ∀ v, jac (stdBlocks (fun a => (x a).1) hd) π g v = c • v := by
    intro v
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [jac_mk, show deltaHalf k (fun a => Fin (x a).1) g = 1 from deltaHalf_scalar _ t,
      show leviEmb k (stdBlocks (fun a => (x a).1) hd) g = _ from leviEmb_scalar _ hd t, hc]
    simp [Submodule.Quotient.mk_smul]
  let cc : Fin 2 → ℂ := ![c0, c1]
  have hcc : ∀ a v, (x a).rep (g a) v = cc a • v := by
    intro a v
    fin_cases a
    · exact h0 v
    · exact h1 v
  haveI := GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL k x
  have hfin := smul_eq_of_equiv E (subQuot_apply_of_smul S T hjac)
    (piTensor_apply_of_smul x g cc hcc)
  rw [Fin.prod_univ_two] at hfin
  exact hfin

end GlobalTheory.CompanionTheory.JacCentral

end
