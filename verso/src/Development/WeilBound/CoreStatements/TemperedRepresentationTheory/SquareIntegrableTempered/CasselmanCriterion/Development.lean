import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NotMemLpOfGrowthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LtOneOfPowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeOneOfPowerBoundsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalOpenStabilizerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfPowTendstoZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRepIsSmoothFoundationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIndexMonotoneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingMemLeviStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockCentralElementCommutesLeviStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingCentralUnipotentCongruenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleEquivFoundationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientScalarActionModStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientNontrivialExistsMemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorCentralBlockScalarStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityNeZeroSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorIrreducibleNontrivialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCentralLeviFixedSubmoduleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCentralLeviCongruenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpCoefficientCenterNormPreservedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastBlockCentralScalarModulusOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusContractingBlockLtOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetMeasurableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetVolumeBoundStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult MeasureTheory

namespace Zl.JC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `hi` as an intermediate fact. Establish `hsF : GroundTheory.Automorphic.IsSmooth π` using `GlobalTheory.T.smooth_rep_is_smooth_foundation k N π hs`. Establish `hadm : GroundTheory.Automorphic.IsAdmissible π` using `GroundTheory.Automorphic.Parabolic.isAdmissible_of_isIrreducible hsF`. Take `⟨S, T, hST⟩` from `GlobalTheory.T.jacquet_multiplicity_ne_zero_subquotient k x hd π hjm`. Establish `hscal` using `GlobalTheory.T.pi_tensor_central_block_scalar k x t c hc j`.

Use `set Λ : ℂ := ∏ i ∈ Finset.univ.filter (· ≤ j), c i with hΛdef`. Use `set δ : ℂ := ((deltaHalf k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j) : ℂˣ) : ℂ) with hδdef`. Establish `hmod : ∀ s ∈ S.toSubmodule, jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s - Λ • s ∈ T.toSubmodule` using `GlobalTheory.T.subquotient_scalar_action_mod _ _ S T hST (zj (fun a => (x a).1) t j) Λ hscal`. Use `GlobalTheory.T.pi_tensor_irreducible_nontrivial k x` as an intermediate fact. Establish `hΛ : Λ ≠ 0`.

Introduce `h0`. Take `⟨v, hv0⟩` from `exists_ne (0 : PiTensorProduct ℂ (fun a => (x a).2.rep.V))`. Apply `hv0` to reduce the goal to its premises. Establish `h2 : piTensor (fun a => (x a).rep) (zj (fun a => (x a).1) t j)⁻¹ (piTensor (fun a => (x a).rep) (zj (fun a => (x a).1) t j) v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.

Rewrite `h2` using `[hscal v, h0, zero_smul, map_zero]`. Conclude with `h2.symm`. Establish `hδ : δ ≠ 0` using `Units.ne_zero _`. Establish `hjacU : ∀ s, jacU (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s = δ • jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s`. Introduce `s`.

Simplify using `only [jac, twist_apply, smul_smul]`. Rewrite using `[hδdef, ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_smul]`. Take `⟨e, -, he2⟩` from `GlobalTheory.T.jacquet_module_equiv_foundation k N π h (fun a => (x a).1) hd`. Establish `ha` using `GlobalTheory.T.levi_embedding_mem_levi k h N (fun a => (x a).1) hd (zj (fun a => (x a).1) t j)`. Establish `hcen` using `GlobalTheory.T.block_central_element_commutes_levi k h N (fun a => (x a).1) hd t j`.

Establish `hmono` using `GlobalTheory.T.block_index_monotone h N (fun a => (x a).1) hd`. Use `set W := S.toSubmodule.map e.toLinearMap`. Use `set T' := (S.toSubmodule ⊓ T.toSubmodule).map e.toLinearMap`. Establish `hle : T' ≤ W` using `Submodule.map_mono inf_le_left`. Establish `hSU : ∀ s ∈ S.toSubmodule, jacU (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s ∈ S.toSubmodule`.

Introduce `s hs'`. Rewrite using `[hjacU]`. Conclude with `S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hs')`. Establish `hWst : ∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N (blockIdx (fun a => (x a).1) hd) π ⟨_, ha⟩ w ∈ W`. Introduce and unpack `_ ⟨s, hs', rfl⟩`.

Use `⟨_, hSU s hs', ?_⟩` and prove the remaining obligations. Conclude with `he2 _ ha s`. Establish `hWmod : ∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N (blockIdx (fun a => (x a).1) hd) π ⟨_, ha⟩ w - (δ * Λ) • w ∈ T'`. Introduce and unpack `_ ⟨s, hs', rfl⟩`. Use `⟨δ • (jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s - Λ • s), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `S.toSubmodule.smul_mem _ (S.toSubmodule.sub_mem (S.apply_mem_toSubmodule _ hs') (S.toSubmodule.smul_mem _ hs'))`. Conclude with `T.toSubmodule.smul_mem _ (hmod s hs')`. Simplify using `only [LinearEquiv.coe_coe]`. Rewrite using `[← he2 _ ha s, hjacU]`. Simplify using `only [map_smul, map_sub, smul_sub, smul_smul]`.

Establish `hex : ∃ w ∈ W, w ∉ T'`. Take `⟨s, hsS, hsT⟩` from `GlobalTheory.T.subquotient_nontrivial_exists_mem _ _ S T hST inferInstance`. Use `⟨e s, ⟨s, hsS, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨s', hs', hes⟩`. Establish `: s' = s` using `e.injective hes`.

Conclude with `hsT (this ▸ hs'.2)`. Take `⟨m₀, hm₀⟩` from `GlobalTheory.T.admissible_central_levi_fixed_submodule k N π hadm (blockIdx (fun a => (x a).1) hd) hmono _ ha hcen W T' (δ * Λ) (mul_ne_zero hδ hΛ) hle hWst hWmod hex`. Take `⟨y, hy0, hyfix, hyeig⟩` from `hm₀ (max m₀ 1) (le_max_left _ _)`. Take `⟨hcN, hcNbar⟩` from `GlobalTheory.T.contracting_central_unipotent_congruence k h N (fun a => (x a).1) hd t hv.le j (max m₀ 1)`. Take `⟨w, l, hw, hl, hcoef⟩` from `GlobalTheory.T.admissible_central_levi_congruence k N π hadm (blockIdx (fun a => (x a).1) hd) hmono (max m₀ 1) (le_max_right _ _) _ ha hcen hcN hcNbar y (δ * Λ) hy0 hyfix hyeig`.

Conclude with `⟨max m₀ 1, le_max_right _ _, w, l, hw, hl, hcoef⟩`.
-/
theorem claim {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) {h : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N)
    (hjm : Zc.jm x hd π ≠ 0) (t : kˣ) (hv : ValuativeRel.valuation k (t : k) < 1) (c : Fin h → ℂ)
    (hc : ∀ i, Zl.ScalarBy (x i) t (c i)) (j : Fin h) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ (w : V) (l : Module.Dual ℂ V),
      (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, π g w = w) ∧
      (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, l ∘ₗ π g = l) ∧
      ∀ r : ℕ, l (π ((leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t j)) ^ r) w) =
        ((((deltaHalf k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j) : ℂˣ) : ℂ)) *
          ∏ i ∈ Finset.univ.filter (· ≤ j), c i) ^ r := by
  classical
  have := hi
  have hsF : GroundTheory.Automorphic.IsSmooth π := GlobalTheory.T.smooth_rep_is_smooth_foundation k N π hs
  have hadm : GroundTheory.Automorphic.IsAdmissible π := GroundTheory.Automorphic.Parabolic.isAdmissible_of_isIrreducible hsF
  obtain ⟨S, T, hST⟩ := GlobalTheory.T.jacquet_multiplicity_ne_zero_subquotient k x hd π hjm
  have hscal := GlobalTheory.T.pi_tensor_central_block_scalar k x t c hc j
  set Λ : ℂ := ∏ i ∈ Finset.univ.filter (· ≤ j), c i with hΛdef
  set δ : ℂ := ((deltaHalf k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j) : ℂˣ) : ℂ) with hδdef
  have hmod : ∀ s ∈ S.toSubmodule, jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s - Λ • s
      ∈ T.toSubmodule :=
    GlobalTheory.T.subquotient_scalar_action_mod _ _ S T hST (zj (fun a => (x a).1) t j) Λ hscal
  have := GlobalTheory.T.pi_tensor_irreducible_nontrivial k x
  have hΛ : Λ ≠ 0 := by
    intro h0
    obtain ⟨v, hv0⟩ := exists_ne (0 : PiTensorProduct ℂ (fun a => (x a).2.rep.V))
    apply hv0
    have h2 : piTensor (fun a => (x a).rep) (zj (fun a => (x a).1) t j)⁻¹
        (piTensor (fun a => (x a).rep) (zj (fun a => (x a).1) t j) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hscal v, h0, zero_smul, map_zero] at h2
    exact h2.symm
  have hδ : δ ≠ 0 := Units.ne_zero _
  have hjacU : ∀ s, jacU (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s =
      δ • jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s := by
    intro s
    simp only [jac, twist_apply, smul_smul]
    rw [hδdef, ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_smul]
  obtain ⟨e, -, he2⟩ := GlobalTheory.T.jacquet_module_equiv_foundation k N π h (fun a => (x a).1) hd
  have ha := GlobalTheory.T.levi_embedding_mem_levi k h N (fun a => (x a).1) hd (zj (fun a => (x a).1) t j)
  have hcen := GlobalTheory.T.block_central_element_commutes_levi k h N (fun a => (x a).1) hd t j
  have hmono := GlobalTheory.T.block_index_monotone h N (fun a => (x a).1) hd
  set W := S.toSubmodule.map e.toLinearMap
  set T' := (S.toSubmodule ⊓ T.toSubmodule).map e.toLinearMap
  have hle : T' ≤ W := Submodule.map_mono inf_le_left
  have hSU : ∀ s ∈ S.toSubmodule, jacU (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s ∈ S.toSubmodule := by
    intro s hs'
    rw [hjacU]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hs')
  have hWst : ∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N (blockIdx (fun a => (x a).1) hd) π ⟨_, ha⟩ w ∈ W := by
    rintro _ ⟨s, hs', rfl⟩
    refine ⟨_, hSU s hs', ?_⟩
    exact he2 _ ha s
  have hWmod : ∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N (blockIdx (fun a => (x a).1) hd) π ⟨_, ha⟩ w -
      (δ * Λ) • w ∈ T' := by
    rintro _ ⟨s, hs', rfl⟩
    refine ⟨δ • (jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s - Λ • s), ⟨?_, ?_⟩, ?_⟩
    · exact S.toSubmodule.smul_mem _ (S.toSubmodule.sub_mem (S.apply_mem_toSubmodule _ hs') (S.toSubmodule.smul_mem _ hs'))
    · exact T.toSubmodule.smul_mem _ (hmod s hs')
    · simp only [LinearEquiv.coe_coe]
      rw [← he2 _ ha s, hjacU]
      simp only [map_smul, map_sub, smul_sub, smul_smul]
  have hex : ∃ w ∈ W, w ∉ T' := by
    obtain ⟨s, hsS, hsT⟩ := GlobalTheory.T.subquotient_nontrivial_exists_mem _ _ S T hST inferInstance
    refine ⟨e s, ⟨s, hsS, rfl⟩, ?_⟩
    rintro ⟨s', hs', hes⟩
    have : s' = s := e.injective hes
    exact hsT (this ▸ hs'.2)
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.admissible_central_levi_fixed_submodule k N π hadm (blockIdx (fun a => (x a).1) hd) hmono _ ha hcen W T' (δ * Λ)
    (mul_ne_zero hδ hΛ) hle hWst hWmod hex
  obtain ⟨y, hy0, hyfix, hyeig⟩ := hm₀ (max m₀ 1) (le_max_left _ _)
  obtain ⟨hcN, hcNbar⟩ := GlobalTheory.T.contracting_central_unipotent_congruence k h N (fun a => (x a).1) hd t hv.le j (max m₀ 1)
  obtain ⟨w, l, hw, hl, hcoef⟩ := GlobalTheory.T.admissible_central_levi_congruence k N π hadm (blockIdx (fun a => (x a).1) hd) hmono (max m₀ 1)
    (le_max_right _ _) _ ha hcen hcN hcNbar y (δ * Λ) hy0 hyfix hyeig
  exact ⟨max m₀ 1, le_max_right _ _, w, l, hw, hl, hcoef⟩

/- English proof (translation)
Take `⟨m, hm, w, l, hw, hl, hcoef⟩` from `claim π hs hi x hd hjm t hv c hc j`. Use `borelize (AdGL k N)`. Establish `hopen : IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l}` using `GlobalTheory.T.invariant_functional_open_stabilizer π (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m) (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m) l hl`. Take `⟨F, hF, hFmem⟩` from `hL (Measure.haar (G := AdGL k N)) inferInstance w l hopen`. Take `⟨hmeas, hdisj⟩` from `GlobalTheory.T.contracting_double_coset_measurable k h N (fun a => (x a).1) hd hpos t hv j hj m hm`.

Take `⟨c0, hc0, hvol⟩` from `GlobalTheory.T.contracting_double_coset_volume_bound k h N (fun a => (x a).1) hd hpos t hv j hj m hm (Measure.haar (G := AdGL k N)) inferInstance`. Use `set δ : ℂ := ((deltaHalf k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j) : ℂˣ) : ℂ) with hδdef`. Use `set Λ : ℂ := ∏ i ∈ Finset.univ.filter (· ≤ j), c i`. Establish `hnorm : ‖δ * Λ‖ = Real.sqrt (modulus k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j)) * ‖Λ‖`. Rewrite using `[norm_mul, hδdef, val_deltaHalf, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]`.

Rewrite using `[← hnorm]`. Use `GlobalTheory.T.not_mem_Lp_of_growth (Measure.haar (G := AdGL k N)) F p hp hFmem _ hmeas hdisj c0 _ 1 ‖δ * Λ‖ hc0 one_pos (norm_nonneg _) hvol ?_` and prove the remaining obligations. Introduce and unpack `r _ ⟨g, ⟨x1, hx1, y1, hy1, rfl⟩, rfl⟩`. Rewrite using `[hF, one_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hw y1 hy1]`. Establish `h1 : l (π x1 (π ((leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t j)) ^ r) w)) = l (π ((leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t j)) ^ r) w)` using `LinearMap.congr_fun (hl x1 hx1) _`.

Rewrite using `[h1, hcoef r, norm_pow]`. Conclude with `le_of_eq (abs_of_nonneg (by positivity)).symm`.
-/
theorem lpBound {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) {h : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N)
    (hpos : ∀ a, 0 < (x a).1) (hjm : Zc.jm x hd π ≠ 0) (t : kˣ) (hv : ValuativeRel.valuation k (t : k) < 1)
    (c : Fin h → ℂ) (hc : ∀ i, Zl.ScalarBy (x i) t (c i)) (j : Fin h) (hj : j.val + 1 < h) (p : ℝ) (hp : 0 < p)
    (hL : CoeffLp p π) :
    (modulus k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j))⁻¹ *
      (Real.sqrt (modulus k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j)) *
        ‖∏ i ∈ Finset.univ.filter (· ≤ j), c i‖) ^ p < 1 := by
  classical
  obtain ⟨m, hm, w, l, hw, hl, hcoef⟩ := claim π hs hi x hd hjm t hv c hc j
  borelize (AdGL k N)
  have hopen : IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} :=
    GlobalTheory.T.invariant_functional_open_stabilizer π (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)
      (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m) l hl
  obtain ⟨F, hF, hFmem⟩ := hL (Measure.haar (G := AdGL k N)) inferInstance w l hopen
  obtain ⟨hmeas, hdisj⟩ := GlobalTheory.T.contracting_double_coset_measurable k h N (fun a => (x a).1) hd hpos t hv j hj m hm
  obtain ⟨c0, hc0, hvol⟩ := GlobalTheory.T.contracting_double_coset_volume_bound k h N (fun a => (x a).1) hd hpos t hv j hj m hm
    (Measure.haar (G := AdGL k N)) inferInstance
  set δ : ℂ := ((deltaHalf k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j) : ℂˣ) : ℂ) with hδdef
  set Λ : ℂ := ∏ i ∈ Finset.univ.filter (· ≤ j), c i
  have hnorm : ‖δ * Λ‖ = Real.sqrt (modulus k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j)) * ‖Λ‖ := by
    rw [norm_mul, hδdef, val_deltaHalf, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [← hnorm]
  refine GlobalTheory.T.not_mem_Lp_of_growth (Measure.haar (G := AdGL k N)) F p hp hFmem _ hmeas hdisj c0 _ 1 ‖δ * Λ‖ hc0 one_pos
    (norm_nonneg _) hvol ?_
  rintro r _ ⟨g, ⟨x1, hx1, y1, hy1, rfl⟩, rfl⟩
  rw [hF, one_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hw y1 hy1]
  have h1 : l (π x1 (π ((leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t j)) ^ r) w)) =
      l (π ((leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t j)) ^ r) w) :=
    LinearMap.congr_fun (hl x1 hx1) _
  rw [h1, hcoef r, norm_pow]
  exact le_of_eq (abs_of_nonneg (by positivity)).symm

/- English proof (translation)
Use `set jl : Fin h := ⟨h - 1, by omega⟩`. Take `⟨m, hm, w, l, hw, hl, hcoef⟩` from `claim π hs hi x hd hjm t hv c hc jl`. Take `⟨hsc, hmod1⟩` from `GlobalTheory.T.last_block_central_scalar_modulus_one k h N (fun a => (x a).1) hd t jl (by simp [jl]; omega)`. Establish `hopen : IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l}` using `GlobalTheory.T.invariant_functional_open_stabilizer π (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m) (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m) l hl`. Establish `hcent : leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t jl) ∈ Subgroup.center (GL (Fin N) k)`.

Rewrite using `[hsc]`. Use `Subgroup.mem_center_iff.2 fun g => Units.ext ?_` and prove the remaining obligations. Conclude with `(Matrix.scalar_commute (t : k) (fun _ => Commute.all _ _) g.val).symm.eq`. Establish `hc1` using `GlobalTheory.T.lp_coefficient_center_norm_preserved k N π p hL _ hcent w l hopen`. Establish `h0` using `hcoef 0`.

Establish `h1` using `hcoef 1`. Simplify using `only [pow_zero, map_one, Module.End.one_apply] at h0`. Simplify using `only [pow_one] at h1`. Rewrite `hc1` using `[h1, h0, norm_one, norm_mul, val_deltaHalf, hmod1, Real.sqrt_one, Complex.ofReal_one, norm_one, one_mul, norm_prod]`. Establish `hfilt : Finset.univ.filter (· ≤ jl) = Finset.univ`.

Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]`. Conclude with `Fin.le_iff_val_le_val.2 (by simp [jl]; omega)`. Rewrite `hc1` using `[hfilt]`. Conclude with `hc1`.
-/
theorem totalNorm {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) {h : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N)
    (hjm : Zc.jm x hd π ≠ 0) (t : kˣ) (hv : ValuativeRel.valuation k (t : k) < 1)
    (c : Fin h → ℂ) (hc : ∀ i, Zl.ScalarBy (x i) t (c i)) (hh : 0 < h) (p : ℝ) (hL : CoeffLp p π) :
    ∏ i, ‖c i‖ = 1 := by
  classical
  set jl : Fin h := ⟨h - 1, by omega⟩
  obtain ⟨m, hm, w, l, hw, hl, hcoef⟩ := claim π hs hi x hd hjm t hv c hc jl
  obtain ⟨hsc, hmod1⟩ := GlobalTheory.T.last_block_central_scalar_modulus_one k h N (fun a => (x a).1) hd t jl (by simp [jl]; omega)
  have hopen : IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} :=
    GlobalTheory.T.invariant_functional_open_stabilizer π (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)
      (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m) l hl
  have hcent : leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t jl) ∈
      Subgroup.center (GL (Fin N) k) := by
    rw [hsc]
    refine Subgroup.mem_center_iff.2 fun g => Units.ext ?_
    exact (Matrix.scalar_commute (t : k) (fun _ => Commute.all _ _) g.val).symm.eq
  have hc1 := GlobalTheory.T.lp_coefficient_center_norm_preserved k N π p hL _ hcent w l hopen
  have h0 := hcoef 0
  have h1 := hcoef 1
  simp only [pow_zero, map_one, Module.End.one_apply] at h0
  simp only [pow_one] at h1
  rw [h1, h0, norm_one, norm_mul, val_deltaHalf, hmod1, Real.sqrt_one, Complex.ofReal_one, norm_one, one_mul,
    norm_prod] at hc1
  have hfilt : Finset.univ.filter (· ≤ jl) = Finset.univ := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact Fin.le_iff_val_le_val.2 (by simp [jl]; omega)
  rw [hfilt] at hc1
  exact hc1

/- English proof (translation)
Introduce `N V _ _ π hN hs hi hsq h x hd hpos hjm t ht c hc`. Establish `hv` using `GlobalTheory.T.valuation_lt_one_of_pow_tendsto_zero k t ht`. Establish `hh : 0 < h`. Break down `Nat.eq_zero_or_pos h with rfl | hh` into its components or cases. Simplify using `at hd`.

Use linear arithmetic over natural numbers and integers. Conclude with `hh`. Use `⟨fun j hj => ?_, totalNorm π hs hi x hd hjm t hv c hc hh 2 hsq⟩` and prove the remaining obligations. Establish `key` using `lpBound π hs hi x hd hpos hjm t hv c hc j hj 2 two_pos hsq`. Use `GlobalTheory.T.lt_one_of_power_bound _ _ (modulus_pos k _) (norm_nonneg _) key` as an intermediate fact.

Rewrite `this` using `[norm_prod]`. Then use the resulting hypothesis.
-/
theorem casselmanNecSq_holds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Zl.CasselmanNecSq k := by
  intro N V _ _ π hN hs hi hsq h x hd hpos hjm t ht c hc
  have hv := GlobalTheory.T.valuation_lt_one_of_pow_tendsto_zero k t ht
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp at hd; omega
    · exact hh
  refine ⟨fun j hj => ?_, totalNorm π hs hi x hd hjm t hv c hc hh 2 hsq⟩
  have key := lpBound π hs hi x hd hpos hjm t hv c hc j hj 2 two_pos hsq
  have := GlobalTheory.T.lt_one_of_power_bound _ _ (modulus_pos k _) (norm_nonneg _) key
  rwa [norm_prod] at this

/- English proof (translation)
Introduce `N V _ _ π hN hs hi htemp h x hd hpos hjm t ht c hc`. Establish `hv` using `GlobalTheory.T.valuation_lt_one_of_pow_tendsto_zero k t ht`. Establish `hh : 0 < h`. Break down `Nat.eq_zero_or_pos h with rfl | hh` into its components or cases. Simplify using `at hd`.

Use linear arithmetic over natural numbers and integers. Conclude with `hh`. Use `⟨fun j hj => ?_, totalNorm π hs hi x hd hjm t hv c hc hh (2 + 1) (htemp 1 one_pos)⟩` and prove the remaining obligations. Establish `hlt` using `GlobalTheory.T.modulus_contracting_block_lt_one k h N (fun a => (x a).1) hd hpos t hv j hj`. Use `GlobalTheory.T.le_one_of_power_bounds _ _ (modulus_pos k _) hlt (norm_nonneg _) (fun ε hε => lpBound π hs hi x hd hpos hjm t hv c hc j hj (2 + ε) (by linarith) (htemp ε hε))` as an intermediate fact.

Rewrite `this` using `[norm_prod]`. Then use the resulting hypothesis.
-/
theorem casselmanNecTemp_holds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Zl.CasselmanNecTemp k := by
  intro N V _ _ π hN hs hi htemp h x hd hpos hjm t ht c hc
  have hv := GlobalTheory.T.valuation_lt_one_of_pow_tendsto_zero k t ht
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp at hd; omega
    · exact hh
  refine ⟨fun j hj => ?_, totalNorm π hs hi x hd hjm t hv c hc hh (2 + 1) (htemp 1 one_pos)⟩
  have hlt := GlobalTheory.T.modulus_contracting_block_lt_one k h N (fun a => (x a).1) hd hpos t hv j hj
  have := GlobalTheory.T.le_one_of_power_bounds _ _ (modulus_pos k _) hlt (norm_nonneg _)
    (fun ε hε => lpBound π hs hi x hd hpos hjm t hv c hc j hj (2 + ε) (by linarith) (htemp ε hε))
  rwa [norm_prod] at this

end Zl.JC

end
