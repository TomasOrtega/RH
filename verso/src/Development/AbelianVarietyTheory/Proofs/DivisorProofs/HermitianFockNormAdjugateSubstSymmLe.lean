import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistHighestWeight
import Formalism.LocalToGlobal.Columns.CoefModB

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunIsom

open scoped ComplexOrder

section One

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.ValCmp

/- English proof (translation)
Establish `hnext : ∀ (μ : Fin (m + 1) → ℕ) (s : Fin m), nuNext μ s.castSucc = μ s.succ`. Introduce `μ s`. Establish `: s.castSucc.val + 1 < m + 1` using `by simp`. Rewrite using `[nuNext, dif_pos this]`. Both sides reduce to the same expression.

Establish `e1 : Formalism.UG.dwAct R (m + 1) (m + 1) (antiDiagGL R (m + 1)) (hw R le_rfl (nuDual ν)) = ∏ s : Fin m, revInitMinor R (m + 1) (m + 1 - (s.val + 1)) ^ (ν s.castSucc - ν s.succ)`. Rewrite using `[hw, map_prod, Fin.prod_univ_castSucc]`. Simplify using `only [map_pow, dwAct_antiDiag_lpMinor, hnext]`. Establish `: nuDual ν (Fin.last m) = 0` using `by simp [nuDual]`. Rewrite using `[this, Nat.zero_sub, pow_zero, mul_one, ← Equiv.prod_comp Fin.revPerm]`.

Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `h1 : ν s.castSucc ≤ ν 0` using `hν (Fin.zero_le _)`. Establish `h2 : ν s.succ ≤ ν s.castSucc` using `hν (Fin.castSucc_lt_succ).le`. Establish `hs` using `s.isLt`. Use `congr 1`.

Use `congr 1`. Simplify using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [nuDual, Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev]`. Use linear arithmetic over natural numbers and integers.

Use `choose ε hε using fun s : Fin m => cofAct_lpMinor R (m + 1) s.val (by have := s.isLt; omega) (by have := s.isLt; omega)`. Use `⟨∏ s : Fin m, ε s ^ (ν s.castSucc - ν s.succ), ?_⟩` and prove the remaining obligations. Establish `hsum : ∑ i, ν i - ν 0 = ∑ s : Fin m, s.val * (ν s.castSucc - ν s.succ)`. Use `sum_mul_sub_succ m ν hν` as an intermediate fact. Rewrite `this` using `[h0]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[CofRel, e1, hsum, hw, map_prod, Fin.prod_univ_castSucc, h0, Nat.zero_sub, pow_zero, map_one, mul_one]`. Simplify using `only [map_pow, hnext, Fin.val_castSucc, hε, zsmul_eq_mul, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cofRel_hw_explicit (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (h0 : ν (Fin.last m) = 0) : ∃ ε : ℤˣ, CofRel R m ν (hw R le_rfl ν)
      ((ε : ℤ) • Formalism.UG.dwAct R (m + 1) (m + 1) (antiDiagGL R (m + 1)) (hw R le_rfl (nuDual ν))) := by
  have hnext : ∀ (μ : Fin (m + 1) → ℕ) (s : Fin m), nuNext μ s.castSucc = μ s.succ := by
    intro μ s
    have : s.castSucc.val + 1 < m + 1 := by simp
    rw [nuNext, dif_pos this]
    rfl
  have e1 : Formalism.UG.dwAct R (m + 1) (m + 1) (antiDiagGL R (m + 1)) (hw R le_rfl (nuDual ν)) =
      ∏ s : Fin m, revInitMinor R (m + 1) (m + 1 - (s.val + 1)) ^ (ν s.castSucc - ν s.succ) := by
    rw [hw, map_prod, Fin.prod_univ_castSucc]
    simp only [map_pow, dwAct_antiDiag_lpMinor, hnext]
    have : nuDual ν (Fin.last m) = 0 := by simp [nuDual]
    rw [this, Nat.zero_sub, pow_zero, mul_one, ← Equiv.prod_comp Fin.revPerm]
    refine Finset.prod_congr rfl fun s _ => ?_
    have h1 : ν s.castSucc ≤ ν 0 := hν (Fin.zero_le _)
    have h2 : ν s.succ ≤ ν s.castSucc := hν (Fin.castSucc_lt_succ).le
    have hs := s.isLt
    congr 1
    · congr 1
      simp [Fin.val_rev]
      omega
    · simp only [nuDual, Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev]
      omega
  choose ε hε using fun s : Fin m =>
    cofAct_lpMinor R (m + 1) s.val (by have := s.isLt; omega) (by have := s.isLt; omega)
  refine ⟨∏ s : Fin m, ε s ^ (ν s.castSucc - ν s.succ), ?_⟩
  have hsum : ∑ i, ν i - ν 0 = ∑ s : Fin m, s.val * (ν s.castSucc - ν s.succ) := by
    have := sum_mul_sub_succ m ν hν
    rw [h0] at this
    omega
  rw [CofRel, e1, hsum, hw, map_prod, Fin.prod_univ_castSucc, h0, Nat.zero_sub, pow_zero, map_one, mul_one]
  simp only [map_pow, hnext, Fin.val_castSucc, hε, zsmul_eq_mul, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

variable {K : Type} [Field K] {n : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Express the relevant statement in the definitionally equal form `(if a = b.rev then (1 : K) else 0) = if b = a.rev then 1 else 0`. Use `congr 1`. Conclude with `propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩`.
-/
theorem antiDiag_transpose : ((antiDiagGL K n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
    (((antiDiagGL K n)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  ext a b
  change (if a = b.rev then (1 : K) else 0) = if b = a.rev then 1 else 0
  congr 1
  exact propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩

/- English proof (translation)
Rewrite using `[funDetPow_eq, ← mul_zpow, ← Matrix.det_mul]`. Establish `: ((antiDiagGL K n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (antiDiagGL K n : GL (Fin n) K) = 1` using `(antiDiagGL K n).val_inv`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem antiDiag_detPow_sq (c : ℤ) : detPow K n (antiDiagGL K n) c * detPow K n (antiDiagGL K n) c = 1 := by
  rw [funDetPow_eq, ← mul_zpow, ← Matrix.det_mul]
  have : ((antiDiagGL K n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (antiDiagGL K n : GL (Fin n) K) = 1 :=
    (antiDiagGL K n).val_inv
  rw [this]
  simp

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Use `⟨1, one_mul _, ?_⟩` and prove the remaining obligations. Simplify using `[funCof_zero, extremal, hw, detPow, DomWeight.detShift]`. Consider the case `succ m`.

Take `⟨ε, hε⟩` from `cofRel_hw_explicit K m l.natW (funNat_antitone l) (funNat_last l)`. Use `⟨((ε : ℤ) : K) * detPow K (m + 1) (antiDiagGL K (m + 1)) l.dual.detShift, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_mul_mul_comm, antiDiag_detPow_sq, mul_one, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]`. Simplify using the standard rewrite rules. Rewrite using `[smul_smul, mul_assoc, antiDiag_detPow_sq, mul_one, Int.cast_smul_eq_zsmul, antiDiag_transpose, funExp_succ, extremal, extremal, funNat_dual]`.

Conclude with `hε`.
-/
theorem funPos_extremal (l : DomWeight n) : ∃ c : K, c * c = 1 ∧
    (genM K n).det ^ funExp l * (c • (detPow K n (antiDiagGL K n) l.dual.detShift •
      rowAct K ((antiDiagGL K n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ (extremal K n l.dual))) =
      cofAct K n (extremal K n l) := by
  cases n with
  | zero =>
    refine ⟨1, one_mul _, ?_⟩
    simp [funCof_zero, extremal, hw, detPow, DomWeight.detShift]
  | succ m =>
    obtain ⟨ε, hε⟩ := cofRel_hw_explicit K m l.natW (funNat_antitone l) (funNat_last l)
    refine ⟨((ε : ℤ) : K) * detPow K (m + 1) (antiDiagGL K (m + 1)) l.dual.detShift, ?_, ?_⟩
    · rw [mul_mul_mul_comm, antiDiag_detPow_sq, mul_one, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    · rw [smul_smul, mul_assoc, antiDiag_detPow_sq, mul_one, Int.cast_smul_eq_zsmul, antiDiag_transpose, funExp_succ,
        extremal, extremal, funNat_dual]
      exact hε

end One

variable {ι : Type} [Fintype ι] {n : ℕ}

def extVec (σ : ι → DomWeight n) : VV ℂ σ :=
  ⟨ten fun τ => extremal ℂ n (σ τ), GlobalTheory.Proof.TensorMapDescent.ten_mem σ _ fun τ =>
    Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (funNat_antitone (σ τ))⟩

/- English proof (translation)
Establish `h` using `pairingBExtremal_holds ℂ ι n σ 1`. Rewrite `h` using `[map_one, polyAction_one₂]`. Rewrite using `[pairBK_apply]`. Conclude with `h`.
-/
theorem pairBK_extVec (σ : ι → DomWeight n) : pairBK σ (extVec σ) (extVec σ) = 1 := by
  have h := pairingBExtremal_holds ℂ ι n σ 1
  rw [map_one, polyAction_one₂] at h
  rw [pairBK_apply]
  exact h

/- English proof (translation)
Use `choose c hc hrel using fun τ => funPos_extremal (K := ℂ) (σ τ)`. Establish `h1` using `funRel_unique (funEquiv_rel σ (extVec σ)) (funRel_ten hrel)`. Establish `h2 : ∀ (c : ι → ℂ) (x : ι → MvPolynomial (Fin n × Fin n) ℂ), ten (fun τ => c τ • x τ) = (∏ τ, c τ) • ten x`. Introduce `c x`. Unfold `ten`.

Simplify using `only [map_smul]`. Rewrite using `[Finset.prod_smul]`. Rewrite `h1` using `[h2, ← funAct_ten (fun τ => (σ τ).dual) (fun _ => GlobalTheory.ValCmp.antiDiagGL ℂ n)]`. Establish `hJ : invTrK (fun _ : ι => GlobalTheory.ValCmp.antiDiagGL ℂ n) = fun _ => GlobalTheory.ValCmp.antiDiagGL ℂ n`. Use function extensionality and compare the values at `τ`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[invTrK_coe, ← antiDiag_transpose, Matrix.transpose_transpose]`. Establish `h3` using `pairingBExtremal_holds ℂ ι n (fun τ => (σ τ).dual) (fun _ => GlobalTheory.ValCmp.antiDiagGL ℂ n)`. Rewrite `h3` using `[hJ]`. Rewrite using `[pairBK_apply, h1, map_smul, map_smul, LinearMap.smul_apply, h3, smul_smul, ← Finset.prod_mul_distrib]`.

Simplify using `[hc]`.
-/
theorem pairBK_funEquiv_extVec (σ : ι → DomWeight n) :
    pairBK (fun τ => (σ τ).dual) (funEquiv σ (extVec σ)) (funEquiv σ (extVec σ)) = 1 := by
  choose c hc hrel using fun τ => funPos_extremal (K := ℂ) (σ τ)
  have h1 := funRel_unique (funEquiv_rel σ (extVec σ)) (funRel_ten hrel)
  have h2 : ∀ (c : ι → ℂ) (x : ι → MvPolynomial (Fin n × Fin n) ℂ), ten (fun τ => c τ • x τ) = (∏ τ, c τ) • ten x := by
    intro c x
    unfold ten
    simp only [map_smul]
    rw [Finset.prod_smul]
  rw [h2, ← funAct_ten (fun τ => (σ τ).dual) (fun _ => GlobalTheory.ValCmp.antiDiagGL ℂ n)] at h1
  have hJ : invTrK (fun _ : ι => GlobalTheory.ValCmp.antiDiagGL ℂ n) = fun _ => GlobalTheory.ValCmp.antiDiagGL ℂ n := by
    funext τ
    apply Units.ext
    rw [invTrK_coe, ← antiDiag_transpose, Matrix.transpose_transpose]
  have h3 := pairingBExtremal_holds ℂ ι n (fun τ => (σ τ).dual) (fun _ => GlobalTheory.ValCmp.antiDiagGL ℂ n)
  rw [hJ] at h3
  rw [pairBK_apply, h1, map_smul, map_smul, LinearMap.smul_apply, h3, smul_smul, ← Finset.prod_mul_distrib]
  simp [hc]

/- English proof (translation)
Rewrite using `[pairBK_apply, pairBK_apply, rhoK_coe, rhoK_coe]`. Conclude with `pairingBInvariantK_holds ℂ ι n σ g x.1 y.1`.
-/
theorem pairBK_inv (σ : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (x y : VV ℂ σ) :
    pairBK σ (rhoK σ (invTrK g) x) (rhoK σ g y) = pairBK σ x y := by
  rw [pairBK_apply, pairBK_apply, rhoK_coe, rhoK_coe]
  exact pairingBInvariantK_holds ℂ ι n σ g x.1 y.1

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (VV ℂ σ) := Module.Finite.of_basis (bVV ℂ σ)`. Establish `hnd` using `pairingBNondegenerate_holds ℂ ι n σ`. Establish `hne : extVec σ ≠ 0` using `fun h => by`. Use `pairBK_extVec σ` as an intermediate fact. Rewrite `this` using `[h]`.

Simplify using `at this`. Use `haveI : Nontrivial (VV ℂ σ) := ⟨⟨_, _, hne⟩⟩`. Set `T : VV ℂ σ →ₗ[ℂ] VV ℂ σ` to `(LinearMap.BilinForm.toDual (pairBK σ) hnd).symm.toLinearMap ∘ₗ (pairBK fun τ => (σ τ).dual).compl₁₂ (funEquiv σ).toLinearMap (funEquiv σ).toLinearMap`. Establish `hp : ∀ v y, pairBK σ (T v) y = pairBK (fun τ => (σ τ).dual) (funEquiv σ v) (funEquiv σ y)` using `fun v y => by`. Simplify using `only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.BilinForm.apply_toDual_symm_apply, LinearMap.compl₁₂_apply]`.

Establish `hT : ∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ σ), T (rhoK σ g v) = rhoK σ g (T v)` using `fun g v => by`. Use `sub_eq_zero.1 (hnd.1 _ fun y => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, LinearMap.sub_apply, sub_eq_zero, hp]`. Take `⟨y', rfl⟩ : ∃ y', y = rhoK σ (invTrK g) y'` from `⟨rhoK σ (invTrK g)⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩`. Rewrite using `[funEquiv_rhoK, funEquiv_rhoK, pb_invTrK_invTrK, pairBK_inv, ← hp]`.

Establish `h` using `pairBK_inv σ (invTrK g) (T v) y'`. Rewrite `h` using `[pb_invTrK_invTrK]`. Conclude with `h.symm`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue T`. Establish `hU` using `GlobalTheory.CoefModel.eq_bot_or_top σ (G := fun _ => 1) (fun _ => Matrix.PosDef.one) (Module.End.eigenspace T c) fun g _ x hx => by`.

Rewrite `hx`, the goal using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[hT, hx, map_smul]`. Establish `hall : ∀ v, T v = c • v` using `fun v => by`. Break down `hU with h | h` into its components or cases. Conclude with `absurd h hc`.

Conclude with `Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top)`. Establish `h1 : c = 1`. Establish `h` using `hp (extVec σ) (extVec σ)`. Rewrite `h` using `[pairBK_funEquiv_extVec, hall, map_smul, LinearMap.smul_apply, pairBK_extVec, smul_eq_mul, mul_one]`. Then use the resulting hypothesis. Rewrite using `[← hp, hall, h1, one_smul]`.
-/
theorem pairBK_funEquiv (σ : ι → DomWeight n) (a b : VV ℂ σ) :
    pairBK (fun τ => (σ τ).dual) (funEquiv σ a) (funEquiv σ b) = pairBK σ a b := by
  haveI : FiniteDimensional ℂ (VV ℂ σ) := Module.Finite.of_basis (bVV ℂ σ)
  have hnd := pairingBNondegenerate_holds ℂ ι n σ
  have hne : extVec σ ≠ 0 := fun h => by
    have := pairBK_extVec σ
    rw [h] at this
    simp at this
  haveI : Nontrivial (VV ℂ σ) := ⟨⟨_, _, hne⟩⟩
  let T : VV ℂ σ →ₗ[ℂ] VV ℂ σ :=
    (LinearMap.BilinForm.toDual (pairBK σ) hnd).symm.toLinearMap ∘ₗ
      (pairBK fun τ => (σ τ).dual).compl₁₂ (funEquiv σ).toLinearMap (funEquiv σ).toLinearMap
  have hp : ∀ v y, pairBK σ (T v) y = pairBK (fun τ => (σ τ).dual) (funEquiv σ v) (funEquiv σ y) := fun v y => by
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.BilinForm.apply_toDual_symm_apply,
      LinearMap.compl₁₂_apply]
  have hT : ∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ σ), T (rhoK σ g v) = rhoK σ g (T v) := fun g v => by
    refine sub_eq_zero.1 (hnd.1 _ fun y => ?_)
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero, hp]
    obtain ⟨y', rfl⟩ : ∃ y', y = rhoK σ (invTrK g) y' :=
      ⟨rhoK σ (invTrK g)⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]⟩
    rw [funEquiv_rhoK, funEquiv_rhoK, pb_invTrK_invTrK, pairBK_inv, ← hp]
    have h := pairBK_inv σ (invTrK g) (T v) y'
    rw [pb_invTrK_invTrK] at h
    exact h.symm
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  have hU := GlobalTheory.CoefModel.eq_bot_or_top σ (G := fun _ => 1) (fun _ => Matrix.PosDef.one) (Module.End.eigenspace T c)
    fun g _ x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [hT, hx, map_smul]
  have hall : ∀ v, T v = c • v := fun v => by
    rcases hU with h | h
    · exact absurd h hc
    · exact Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top)
  have h1 : c = 1 := by
    have h := hp (extVec σ) (extVec σ)
    rwa [pairBK_funEquiv_extVec, hall, map_smul, LinearMap.smul_apply, pairBK_extVec, smul_eq_mul, mul_one] at h
  rw [← hp, hall, h1, one_smul]

/- English proof (translation)
Establish `h` using `pairP_eq_pairB σ (1 : ι → GL (Fin n) ℂ) x.1 y.1`. Rewrite `h` using `[polyAction_one₂]`. Rewrite using `[pairK_apply, pairBK_apply, GlobalTheory.CoefModel.mapVV_coe]`. Conclude with `h`.
-/
theorem pairK_one_eq (σ : ι → DomWeight n) (x y : VV ℂ σ) :
    pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) x y =
      pairBK σ (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) σ x) y := by
  have h := pairP_eq_pairB σ (1 : ι → GL (Fin n) ℂ) x.1 y.1
  rw [polyAction_one₂] at h
  rw [pairK_apply, pairBK_apply, GlobalTheory.CoefModel.mapVV_coe]
  exact h

/- English proof (translation)
Establish `h` using `(isFunForm_iff_eq σ _ _).1 (GlobalTheory.BrRat.isFunForm_map (starRingEnd ℂ) σ (isFunForm_funEquiv σ a))`. Rewrite using `[pairK_one_eq, pairK_one_eq, ← pairBK_funEquiv σ]`. Use `congr 2`.
-/
theorem pairK_funEquiv (σ : ι → DomWeight n) (a b : VV ℂ σ) :
    pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (funEquiv σ a) (funEquiv σ b) =
      pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) a b := by
  have h := (isFunForm_iff_eq σ _ _).1 (GlobalTheory.BrRat.isFunForm_map (starRingEnd ℂ) σ (isFunForm_funEquiv σ a))
  rw [pairK_one_eq, pairK_one_eq, ← pairBK_funEquiv σ]
  congr 2

/- English proof (translation)
Introduce `ι _ n σ w`. Rewrite using `[← pairK_funEquiv σ, LinearEquiv.apply_symm_apply]`.
-/
theorem pairK_funEquiv_symm_le : ∀ {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) (w : VV ℂ fun τ => (σ τ).dual),
    (pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) ((GlobalTheory.FunObj.funEquiv σ).symm w) ((GlobalTheory.FunObj.funEquiv σ).symm w)).re ≤
      (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w w).re := by
  intro ι _ n σ w
  rw [← pairK_funEquiv σ, LinearEquiv.apply_symm_apply]

end GlobalTheory.FunIsom

end
