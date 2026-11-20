import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.PrIsoScale

section Alg

variable {T : Type} [Fintype T] [DecidableEq T] {E : T → Type}
  [∀ τ, NormedAddCommGroup (E τ)] [∀ τ, InnerProductSpace ℂ (E τ)]

def pSum (ι : T → Type) [∀ τ, Fintype (ι τ)] (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ))
    (φ ψ : (⨂[ℂ] τ, E τ) →ₗ[ℂ] ℂ) : ℂ :=
  ∑ f : (∀ τ, ι τ), starRingEnd ℂ (φ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) *
    ψ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))

/- English proof (translation)
Establish `h : (fun τ => b τ (f τ)) = fun τ => ∑ j, ⟪b' τ j, b τ (f τ)⟫_ℂ • b' τ j`. Use function extensionality and compare the values at `fun τ => ((b' τ).sum_repr' _).symm`. Rewrite using `[h, MultilinearMap.map_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Conclude with `MultilinearMap.map_smul_univ _ _ _`.
-/
theorem tprod_expand {ι κ : T → Type} [∀ τ, Fintype (ι τ)] [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ)) (b' : ∀ τ, OrthonormalBasis (κ τ) ℂ (E τ)) (f : ∀ τ, ι τ) :
    (PiTensorProduct.tprod ℂ fun τ => b τ (f τ)) =
      ∑ g : (∀ τ, κ τ), (∏ τ, ⟪b' τ (g τ), b τ (f τ)⟫_ℂ) • PiTensorProduct.tprod ℂ fun τ => b' τ (g τ) := by
  have h : (fun τ => b τ (f τ)) = fun τ => ∑ j, ⟪b' τ j, b τ (f τ)⟫_ℂ • b' τ j :=
    funext fun τ => ((b' τ).sum_repr' _).symm
  rw [h, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  exact MultilinearMap.map_smul_univ _ _ _

/- English proof (translation)
Unfold `pSum`. Use `set U : (∀ τ, ι τ) → (∀ τ, κ τ) → ℂ := fun f g => ∏ τ, ⟪b' τ (g τ), b τ (f τ)⟫_ℂ with hU`. Use `set t' : (∀ τ, κ τ) → ⨂[ℂ] τ, E τ := fun g => PiTensorProduct.tprod ℂ fun τ => b' τ (g τ) with ht'`. Establish `hχ : ∀ (χ : (⨂[ℂ] τ, E τ) →ₗ[ℂ] ℂ) (f : ∀ τ, ι τ), χ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ)) = ∑ g, U f g * χ (t' g)`. Introduce `χ f`.

Rewrite using `[tprod_expand b b' f, map_sum]`. Simplify using `only [map_smul, smul_eq_mul, U, t']`. Establish `horth : ∀ g g' : (∀ τ, κ τ), ∑ f, starRingEnd ℂ (U f g) * U f g' = if g = g' then 1 else 0`. Introduce `g g'`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Simplify using `only [U, map_prod, inner_conj_symm, Finset.prod_mul_distrib]`. Use `_ = ∏ τ, ∑ i, ⟪b τ i, b' τ (g τ)⟫_ℂ * ⟪b' τ (g' τ), b τ i⟫_ℂ := by`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `_ = ∏ τ, ⟪b' τ (g' τ), b' τ (g τ)⟫_ℂ := by`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← (b τ).sum_inner_mul_inner]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Use `_ = ∏ τ, if g' τ = g τ then (1 : ℂ) else 0 := by`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Conclude with `(b' τ).inner_eq_ite _ _`. Use `_ = if g = g' then 1 else 0 := by`. Rewrite using `[Finset.prod_boole]`. Simplify using `only [Finset.mem_univ, true_implies]`. Distinguish the cases in `h : g = g'`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg]`. Introduce `h'`. Conclude with `h (funext fun τ => (h' τ).symm)`.

Repeatedly rewrite using `[hχ φ, hχ ψ]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun g' _ => ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ∑ g, starRingEnd ℂ (φ (t' g)) * ψ (t' g) := by`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Simplify using `only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem pSum_indep {ι κ : T → Type} [∀ τ, Fintype (ι τ)] [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ)) (b' : ∀ τ, OrthonormalBasis (κ τ) ℂ (E τ))
    (φ ψ : (⨂[ℂ] τ, E τ) →ₗ[ℂ] ℂ) : pSum ι b φ ψ = pSum κ b' φ ψ := by
  classical
  unfold pSum
  set U : (∀ τ, ι τ) → (∀ τ, κ τ) → ℂ := fun f g => ∏ τ, ⟪b' τ (g τ), b τ (f τ)⟫_ℂ with hU
  set t' : (∀ τ, κ τ) → ⨂[ℂ] τ, E τ := fun g => PiTensorProduct.tprod ℂ fun τ => b' τ (g τ) with ht'
  have hχ : ∀ (χ : (⨂[ℂ] τ, E τ) →ₗ[ℂ] ℂ) (f : ∀ τ, ι τ),
      χ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ)) = ∑ g, U f g * χ (t' g) := by
    intro χ f
    rw [tprod_expand b b' f, map_sum]
    simp only [map_smul, smul_eq_mul, U, t']
  have horth : ∀ g g' : (∀ τ, κ τ), ∑ f, starRingEnd ℂ (U f g) * U f g' = if g = g' then 1 else 0 := by
    intro g g'
    calc ∑ f, starRingEnd ℂ (U f g) * U f g'
        = ∑ f : (∀ τ, ι τ), ∏ τ, (⟪b τ (f τ), b' τ (g τ)⟫_ℂ * ⟪b' τ (g' τ), b τ (f τ)⟫_ℂ) := by
          refine Finset.sum_congr rfl fun f _ => ?_
          simp only [U, map_prod, inner_conj_symm, Finset.prod_mul_distrib]
      _ = ∏ τ, ∑ i, ⟪b τ i, b' τ (g τ)⟫_ℂ * ⟪b' τ (g' τ), b τ i⟫_ℂ := by
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      _ = ∏ τ, ⟪b' τ (g' τ), b' τ (g τ)⟫_ℂ := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          rw [← (b τ).sum_inner_mul_inner]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = ∏ τ, if g' τ = g τ then (1 : ℂ) else 0 := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          exact (b' τ).inner_eq_ite _ _
      _ = if g = g' then 1 else 0 := by
          rw [Finset.prod_boole]
          simp only [Finset.mem_univ, true_implies]
          by_cases h : g = g'
          · subst h; simp
          · rw [if_neg h, if_neg]
            intro h'
            exact h (funext fun τ => (h' τ).symm)
  simp_rw [hχ φ, hχ ψ]
  calc ∑ f, starRingEnd ℂ (∑ g, U f g * φ (t' g)) * ∑ g', U f g' * ψ (t' g')
      = ∑ g, ∑ g', starRingEnd ℂ (φ (t' g)) * ψ (t' g') * ∑ f, starRingEnd ℂ (U f g) * U f g' := by
        simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g' _ => ?_
        refine Finset.sum_congr rfl fun f _ => ?_
        ring
    _ = ∑ g, starRingEnd ℂ (φ (t' g)) * ψ (t' g) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Alg

section Alg2

variable {T : Type} [Fintype T] [DecidableEq T] {E : T → Type}
  [∀ τ, NormedAddCommGroup (E τ)] [∀ τ, InnerProductSpace ℂ (E τ)]

/- English proof (translation)
Set `b1 : ∀ ρ, OrthonormalBasis (ι ρ) ℂ (E ρ)` to `Function.update b τ ((b τ).map A)`. Establish `hv : ∀ f : (∀ ρ, ι ρ), (fun ρ => b1 ρ (f ρ)) = Function.update (fun ρ => b ρ (f ρ)) τ (A (b τ (f τ)))`. Introduce `f`. Use function extensionality and compare the values at `ρ`. Distinguish the cases in `h : ρ = τ`.

Substitute `h` using the available equality. Simplify using `[b1, OrthonormalBasis.map_apply]`. Simplify using `[b1, Function.update_of_ne h]`. Rewrite using `[← pSum_indep b1 b]`. Unfold `pSum`.

Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[hv f, hφ, hψ]`.
-/
theorem pSum_of_iso {ι : T → Type} [∀ τ, Fintype (ι τ)] (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ)) (τ : T)
    (A : E τ ≃ₗᵢ[ℂ] E τ) (φ ψ φ' ψ' : (⨂[ℂ] ρ, E ρ) →ₗ[ℂ] ℂ)
    (hφ : ∀ v : ∀ ρ, E ρ, φ' (PiTensorProduct.tprod ℂ (Function.update v τ (A (v τ)))) = φ (PiTensorProduct.tprod ℂ v))
    (hψ : ∀ v : ∀ ρ, E ρ, ψ' (PiTensorProduct.tprod ℂ (Function.update v τ (A (v τ)))) = ψ (PiTensorProduct.tprod ℂ v)) :
    pSum ι b φ' ψ' = pSum ι b φ ψ := by
  let b1 : ∀ ρ, OrthonormalBasis (ι ρ) ℂ (E ρ) := Function.update b τ ((b τ).map A)
  have hv : ∀ f : (∀ ρ, ι ρ), (fun ρ => b1 ρ (f ρ)) = Function.update (fun ρ => b ρ (f ρ)) τ (A (b τ (f τ))) := by
    intro f
    funext ρ
    by_cases h : ρ = τ
    · subst h
      simp [b1, OrthonormalBasis.map_apply]
    · simp [b1, Function.update_of_ne h]
  rw [← pSum_indep b1 b]
  unfold pSum
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hv f, hφ, hψ]

end Alg2

section Model

variable {D : D7}

def smIso {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.sm τ →ₗᵢ[ℂ] M.sm τ where
  toLinearMap := (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ).restrict
    (fun w hw => GlobalTheory.SmoothStable.rep_mem_sm D V S M τ g hg w hw)
  norm_map' x := (M.ds τ).2.2.1.2.1 _ (Formalism.IndefR.SchurOrthogonalityAlt.conj_mem M τ hg) x

end Model

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Distinguish the cases in `hfin : ∀ τ, FiniteDimensional ℂ (MX.sm τ)`. Use `swap`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Introduce `ι _ b`. Conclude with `absurd (fun τ => Module.Finite.of_basis (b τ).toBasis) hfin`.

Take `⟨b0⟩ : Nonempty (∀ τ, OrthonormalBasis (Fin (Module.finrank ℂ (MX.sm τ))) ℂ (MX.sm τ))` from `⟨fun τ => stdOrthonormalBasis ℂ (MX.sm τ)⟩`. Take `⟨u, hu'⟩ : ∃ u : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))) → cX.W, ∀ f x, ⟪u f, x⟫_ℂ = prX x (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))` from `⟨fun f => (InnerProductSpace.toDual ℂ cX.W).symm (LinearMap.toContinuousLinearMap (prX.flip (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)))), fun f x => by rw [InnerProductSpace.toDual_symm_apply]; rfl⟩`. Take `⟨T, hTdef⟩ : ∃ T : Module.End ℂ cX.W, T = ∑ f, (prX.flip (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))).smulRight (u f)` from `⟨_, rfl⟩`. Establish `hT : ∀ w w', ⟪w, T w'⟫_ℂ = pSum _ b0 (prX w) (prX w')`. Introduce `w w'`.

Rewrite using `[hTdef, LinearMap.sum_apply, inner_sum]`. Unfold `pSum`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smulRight_apply]`. Simplify using `only [inner_smul_right, LinearMap.flip_apply]`.

Establish `e2 : ⟪w, u f⟫_ℂ = starRingEnd ℂ (prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)))`. Rewrite using `[← hu' f w, inner_conj_symm]`. Simplify using `only [e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hinv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ w w', pSum _ b0 (prX (cX.ρ (atTau θ D.sp.X' τ g) w)) (prX (cX.ρ (atTau θ D.sp.X' τ g) w')) = pSum _ b0 (prX w) (prX w')`.

Introduce `τ g hg w w'`. Take `⟨A, hA⟩ : ∃ A : MX.sm τ ≃ₗᵢ[ℂ] MX.sm τ, ∀ x, ((A x : MX.sm τ) : MX.H τ) = MX.rep τ g x` from `⟨(smIso MX τ hg).toLinearIsometryEquiv rfl, fun x => rfl⟩`. Conclude with `pSum_of_iso b0 τ A _ _ _ _ (fun v => hpr.2 τ g hg w v (A (v τ)) (hA _)) (fun v => hpr.2 τ g hg w' v (A (v τ)) (hA _))`. Establish `hρinv : ∀ (h : GA D D.sp.X') (z : cX.W), cX.ρ h (cX.ρ h⁻¹ z) = z`. Introduce `h z`.

Establish `e : cX.ρ h * cX.ρ h⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Conclude with `congrArg (fun F : Module.End ℂ cX.W => F z) e`. Establish `hcommAt : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), T * cX.ρ (atTau θ D.sp.X' τ g) = cX.ρ (atTau θ D.sp.X' τ g) * T`. Introduce `τ g hg`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `w'`. Apply `ext_inner_left ℂ` to reduce the goal to its premises. Introduce `z`. Take `⟨w, rfl⟩ : ∃ w, cX.ρ (atTau θ D.sp.X' τ g) w = z` from `⟨cX.ρ (atTau θ D.sp.X' τ g)⁻¹ z, hρinv _ z⟩`. Establish `e1` using `hT (cX.ρ (atTau θ D.sp.X' τ g) w) (cX.ρ (atTau θ D.sp.X' τ g) w')`.

Establish `e2` using `hinv τ g hg w w'`. Establish `e3` using `hT w w'`. Establish `e4` using `hc.2.1 (atTau θ D.sp.X' τ g) w (T w')`. Simplify using `only [Module.End.mul_apply]`. Rewrite using `[e1, e2, ← e3, e4]`.

Set `U : Submonoid (GA D D.sp.X')` to `(Submonoid.centralizer ({T} : Set (Module.End ℂ cX.W))).comap cX.ρ`. Establish `hU : ∀ h, h ∈ U ↔ T * cX.ρ h = cX.ρ h * T`. Introduce `h`. Simplify using `[U, Submonoid.mem_centralizer_iff]`. Establish `hall : ∀ h, T * cX.ρ h = cX.ρ h * T`.

Introduce `h`. Take `⟨a, ha, k, hk, rfl⟩` from `(GlobalTheory.UnitarySplit.real_finite_split D D.sp.X').1 h`. Establish `h1 : a ∈ U` using `GlobalTheory.DefiniteMult.real_le hθ U (fun τ g hg => (hU _).2 (hcommAt τ g hg)) ha`. Establish `h2 : k ∈ U` using `(hU k).2 (by rw [hc.1 k hk, mul_one, one_mul])`. Conclude with `(hU _).1 (U.mul_mem h1 h2)`.

Use `haveI : Nontrivial cX.W := hc.2.2.2.1`. Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue T`. Establish `hstab : ∀ h, (T.eigenspace μ).map (cX.ρ h) ≤ T.eigenspace μ`. Introduce `h y hy`. Take `⟨x, hx, rfl⟩` from `hy`.

Rewrite `hx` using `[SetLike.mem_coe, Module.End.mem_eigenspace_iff]`. Rewrite using `[Module.End.mem_eigenspace_iff]`. Establish `e` using `congrArg (fun F : Module.End ℂ cX.W => F x) (hall h)`. Simplify using `only [Module.End.mul_apply] at e`. Rewrite using `[e, hx, map_smul]`.

Establish `hE : T.eigenspace μ = ⊤`. Break down `hc.2.2.2.2 (T.eigenspace μ) hstab with h | h` into its components or cases. Conclude with `absurd h (Module.End.hasEigenvalue_iff.1 hμ)`. Conclude with `h`. Establish `hTμ : ∀ x, T x = μ • x` using `fun x => Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top)`.

Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w, prX w ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hpr.1 (LinearMap.ext h)`. Choose the witnesses or unpack the hypotheses as in `⟨f0, hf0⟩ : ∃ f : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))), prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)) ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hw` to reduce the goal to its premises. Use `(Basis.piTensorProduct fun τ => (b0 τ).toBasis).ext fun f => ?_` and prove the remaining obligations. Rewrite using `[Basis.piTensorProduct_apply]`.

Simplify using `using h f`. Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Conclude with `hw (map_zero prX)`. Establish `hsq : ∀ z : ℂ, starRingEnd ℂ z * z = (‖z‖ : ℂ) ^ 2` using `fun z => Complex.conj_mul' z`.

Choose the witnesses or unpack the hypotheses as in `⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ pSum _ b0 (prX w) (prX w) = (s : ℂ) := by`. Use `⟨∑ f : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))), ‖prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))‖ ^ 2, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.sum_pos' (fun f _ => sq_nonneg _) ⟨f0, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hf0) 2⟩`. Unfold `pSum`. Use `push_cast`.

Conclude with `Finset.sum_congr rfl fun f _ => hsq _`. Establish `hwpos : 0 < ‖w‖ ^ 2` using `pow_pos (norm_pos_iff.2 hw0) 2`. Use `set r : ℝ := s / ‖w‖ ^ 2 with hr`. Establish `hr0 : 0 < r` using `div_pos hs0 hwpos`. Establish `hμr : μ = (r : ℂ)`.

Establish `e1` using `hT w w`. Establish `e2 : ⟪w, T w⟫_ℂ = μ * ((‖w‖ ^ 2 : ℝ) : ℂ)`. Establish `hww : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ)` using `by first`. Consider the case `(rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl)`. Consider the case `exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w`.

Consider the case `simp [inner_self_eq_norm_sq_to_K]`. Rewrite using `[hTμ, inner_smul_right, hww]`. Rewrite `e1` using `[e2, hs]`. Establish `hn : ((‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hwpos.ne'`. Rewrite using `[hr, Complex.ofReal_div, eq_div_iff hn]`.

Conclude with `e1`. Use `⟨((Real.sqrt r)⁻¹ : ℝ), Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_ne_zero'.2 hr0)), ?_⟩` and prove the remaining obligations. Establish `hcc : starRingEnd ℂ (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * (((Real.sqrt r)⁻¹ : ℝ) : ℂ) = ((r⁻¹ : ℝ) : ℂ)`. Rewrite using `[hsq, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs, inv_pow, Real.sq_sqrt hr0.le]`. Introduce `ι _ b w₁ w₂`.

Establish `e : (starRingEnd ℂ (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * (((Real.sqrt r)⁻¹ : ℝ) : ℂ)) * pSum ι b (prX w₁) (prX w₂) = ∑ f : (∀ τ, ι τ), starRingEnd ℂ (((((Real.sqrt r)⁻¹ : ℝ) : ℂ) • prX) w₁ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) * ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) • prX) w₂ (PiTensorPro …`. Unfold `pSum`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `Eq.trans ?_ e` and prove the remaining obligations. Establish `e3 : pSum ι b (prX w₁) (prX w₂) = μ * ⟪w₁, w₂⟫_ℂ`. Rewrite using `[pSum_indep b b0, ← hT, hTμ, inner_smul_right]`. Rewrite using `[e3, hcc, hμr, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hr0.ne', Complex.ofReal_one, one_mul]`.
-/
theorem exists_smul_prIso (D : D7) (θ : InfFam D) (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m))
    (cX : CoefA D.sp.X') (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ) (hθ : IsInfFam θ) (hc : cX.Is)
    (hpr : IsDualPair θ MX cX prX) : ∃ c : ℂ, c ≠ 0 ∧ Seed.PrIso MX cX (c • prX) := by
  classical
  by_cases hfin : ∀ τ, FiniteDimensional ℂ (MX.sm τ)
  swap
  · refine ⟨1, one_ne_zero, ?_⟩
    intro ι _ b
    exact absurd (fun τ => Module.Finite.of_basis (b τ).toBasis) hfin
  obtain ⟨b0⟩ : Nonempty (∀ τ, OrthonormalBasis (Fin (Module.finrank ℂ (MX.sm τ))) ℂ (MX.sm τ)) :=
    ⟨fun τ => stdOrthonormalBasis ℂ (MX.sm τ)⟩
  obtain ⟨u, hu'⟩ : ∃ u : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))) → cX.W, ∀ f x,
      ⟪u f, x⟫_ℂ = prX x (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)) :=
    ⟨fun f => (InnerProductSpace.toDual ℂ cX.W).symm
      (LinearMap.toContinuousLinearMap (prX.flip (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)))),
      fun f x => by rw [InnerProductSpace.toDual_symm_apply]; rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Module.End ℂ cX.W,
      T = ∑ f, (prX.flip (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))).smulRight (u f) := ⟨_, rfl⟩
  have hT : ∀ w w', ⟪w, T w'⟫_ℂ = pSum _ b0 (prX w) (prX w') := by
    intro w w'
    rw [hTdef, LinearMap.sum_apply, inner_sum]
    unfold pSum
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [LinearMap.smulRight_apply]
    simp only [inner_smul_right, LinearMap.flip_apply]
    have e2 : ⟪w, u f⟫_ℂ = starRingEnd ℂ (prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))) := by
      rw [← hu' f w, inner_conj_symm]
    simp only [e2]
    ring

  have hinv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ w w',
      pSum _ b0 (prX (cX.ρ (atTau θ D.sp.X' τ g) w)) (prX (cX.ρ (atTau θ D.sp.X' τ g) w')) =
        pSum _ b0 (prX w) (prX w') := by
    intro τ g hg w w'
    obtain ⟨A, hA⟩ : ∃ A : MX.sm τ ≃ₗᵢ[ℂ] MX.sm τ, ∀ x, ((A x : MX.sm τ) : MX.H τ) = MX.rep τ g x :=
      ⟨(smIso MX τ hg).toLinearIsometryEquiv rfl, fun x => rfl⟩
    exact pSum_of_iso b0 τ A _ _ _ _ (fun v => hpr.2 τ g hg w v (A (v τ)) (hA _))
      (fun v => hpr.2 τ g hg w' v (A (v τ)) (hA _))

  have hρinv : ∀ (h : GA D D.sp.X') (z : cX.W), cX.ρ h (cX.ρ h⁻¹ z) = z := by
    intro h z
    have e : cX.ρ h * cX.ρ h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun F : Module.End ℂ cX.W => F z) e
  have hcommAt : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ),
      T * cX.ρ (atTau θ D.sp.X' τ g) = cX.ρ (atTau θ D.sp.X' τ g) * T := by
    intro τ g hg
    apply LinearMap.ext
    intro w'
    apply ext_inner_left ℂ
    intro z
    obtain ⟨w, rfl⟩ : ∃ w, cX.ρ (atTau θ D.sp.X' τ g) w = z :=
      ⟨cX.ρ (atTau θ D.sp.X' τ g)⁻¹ z, hρinv _ z⟩
    have e1 := hT (cX.ρ (atTau θ D.sp.X' τ g) w) (cX.ρ (atTau θ D.sp.X' τ g) w')
    have e2 := hinv τ g hg w w'
    have e3 := hT w w'
    have e4 := hc.2.1 (atTau θ D.sp.X' τ g) w (T w')
    simp only [Module.End.mul_apply]
    rw [e1, e2, ← e3, e4]
  let U : Submonoid (GA D D.sp.X') := (Submonoid.centralizer ({T} : Set (Module.End ℂ cX.W))).comap cX.ρ
  have hU : ∀ h, h ∈ U ↔ T * cX.ρ h = cX.ρ h * T := by
    intro h
    simp [U, Submonoid.mem_centralizer_iff]
  have hall : ∀ h, T * cX.ρ h = cX.ρ h * T := by
    intro h
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D D.sp.X').1 h
    have h1 : a ∈ U := GlobalTheory.DefiniteMult.real_le hθ U (fun τ g hg => (hU _).2 (hcommAt τ g hg)) ha
    have h2 : k ∈ U := (hU k).2 (by rw [hc.1 k hk, mul_one, one_mul])
    exact (hU _).1 (U.mul_mem h1 h2)

  haveI : Nontrivial cX.W := hc.2.2.2.1
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  have hstab : ∀ h, (T.eigenspace μ).map (cX.ρ h) ≤ T.eigenspace μ := by
    intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx
    rw [Module.End.mem_eigenspace_iff]
    have e := congrArg (fun F : Module.End ℂ cX.W => F x) (hall h)
    simp only [Module.End.mul_apply] at e
    rw [e, hx, map_smul]
  have hE : T.eigenspace μ = ⊤ := by
    rcases hc.2.2.2.2 (T.eigenspace μ) hstab with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hμ)
    · exact h
  have hTμ : ∀ x, T x = μ • x := fun x =>
    Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top)

  obtain ⟨w, hw⟩ : ∃ w, prX w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hpr.1 (LinearMap.ext h)
  obtain ⟨f0, hf0⟩ : ∃ f : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))),
      prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw
    refine (Basis.piTensorProduct fun τ => (b0 τ).toBasis).ext fun f => ?_
    rw [Basis.piTensorProduct_apply]
    simpa using h f
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (map_zero prX)
  have hsq : ∀ z : ℂ, starRingEnd ℂ z * z = (‖z‖ : ℂ) ^ 2 := fun z => Complex.conj_mul' z
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ pSum _ b0 (prX w) (prX w) = (s : ℂ) := by
    refine ⟨∑ f : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))),
      ‖prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))‖ ^ 2, ?_, ?_⟩
    · exact Finset.sum_pos' (fun f _ => sq_nonneg _) ⟨f0, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hf0) 2⟩
    · unfold pSum
      push_cast
      exact Finset.sum_congr rfl fun f _ => hsq _
  have hwpos : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.2 hw0) 2
  set r : ℝ := s / ‖w‖ ^ 2 with hr
  have hr0 : 0 < r := div_pos hs0 hwpos
  have hμr : μ = (r : ℂ) := by
    have e1 := hT w w
    have e2 : ⟪w, T w⟫_ℂ = μ * ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      have hww : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
        first
          | (rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl)
          | exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w
          | simp [inner_self_eq_norm_sq_to_K]
      rw [hTμ, inner_smul_right, hww]
    rw [e2, hs] at e1
    have hn : ((‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hwpos.ne'
    rw [hr, Complex.ofReal_div, eq_div_iff hn]
    exact e1

  refine ⟨((Real.sqrt r)⁻¹ : ℝ), Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_ne_zero'.2 hr0)), ?_⟩
  have hcc : starRingEnd ℂ (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * (((Real.sqrt r)⁻¹ : ℝ) : ℂ) = ((r⁻¹ : ℝ) : ℂ) := by
    rw [hsq, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs, inv_pow, Real.sq_sqrt hr0.le]
  intro ι _ b w₁ w₂
  have e : (starRingEnd ℂ (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * (((Real.sqrt r)⁻¹ : ℝ) : ℂ)) * pSum ι b (prX w₁) (prX w₂) =
      ∑ f : (∀ τ, ι τ), starRingEnd ℂ (((((Real.sqrt r)⁻¹ : ℝ) : ℂ) • prX) w₁ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) *
        ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) • prX) w₂ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ)) := by
    unfold pSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring
  refine Eq.trans ?_ e
  have e3 : pSum ι b (prX w₁) (prX w₂) = μ * ⟪w₁, w₂⟫_ℂ := by
    rw [pSum_indep b b0, ← hT, hTμ, inner_smul_right]
  rw [e3, hcc, hμr, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hr0.ne', Complex.ofReal_one, one_mul]

end GlobalTheory.PrIsoScale
