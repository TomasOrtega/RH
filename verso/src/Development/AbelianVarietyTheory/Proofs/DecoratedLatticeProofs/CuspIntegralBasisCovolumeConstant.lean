import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.BlockDiagonalMulVecApply

noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.RealCoordCusp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem normSq_det_UJ {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Complex.normSq (uMat g).det = 1 := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have hJ : (Formalism.REAL.Jm ε).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (Formalism.REAL.Jm_mul_self ε)
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h1 := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have h2 : star (uMat g).det * (uMat g).det = 1 := by
    have : (star (uMat g).det * (uMat g).det - 1) * (Formalism.REAL.Jm ε).det = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · linear_combination h
    · exact absurd h hJ
  have h3 : ((Complex.normSq (uMat g).det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h2
  exact_mod_cast h3

variable (I : AutInst)

abbrev Idx : Type := Σ _ : Fin I.n, Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)

def cBasis : Module.Basis (Σ _ : InfinitePlace I.F, Σ _ : Fin I.n, Fin 2) ℝ (InfinitePlace I.F → Fin I.n → ℂ) :=
  Pi.basis fun _ => Pi.basis fun _ => Complex.basisOneI

/- English proof (translation)
Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_eq : Fintype.card (Σ _ : InfinitePlace I.F, Σ _ : Fin I.n, Fin 2) = Fintype.card (Idx I) := by
  simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Formalism.L2.SG.Pf.Tau.card_infinite_places, Formalism.L2.SG.Pf.Tau.card_integral_basis]
  ring

def rho : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin (Fintype.card (Idx I)) → ℝ) :=
  ((cBasis I).reindex (Fintype.equivFinOfCardEq (card_eq I))).equivFun

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules.
-/
theorem rho_isRealCoord : IsRealCoord I (rho I) := by
  intro x y
  simp only [rho, Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply, dotProduct]
  rw [(Fintype.equivFinOfCardEq (card_eq I)).symm.sum_comp
    (fun s => (cBasis I).repr x s * (cBasis I).repr y s)]
  simp only [cBasis, Fintype.sum_sigma, Pi.basis_repr, Complex.coe_basisOneI_repr, Fin.sum_univ_two]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def bQ : Module.Basis (Idx I) ℚ (Fin I.n → I.E) := Pi.basis fun _ => integralBasis I.E

def eB : Fin (Fintype.card (Idx I)) → Fin I.n → I.E := fun k => bQ I ((Fintype.equivFin (Idx I)).symm k)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem bQ_apply (p : Idx I) : bQ I p = Pi.single p.1 (integralBasis I.E p.2) := by
  simp [bQ, Pi.basis_apply]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eB_isZBasis : IsZBasis I (eB I) := by
  refine ⟨((bQ I).linearIndependent.comp _ (Fintype.equivFin (Idx I)).symm.injective).restrict_scalars' ℤ, ?_⟩
  intro u
  constructor
  · intro hu
    have hm := Formalism.L2.SG.Pf.Tau.mem_integral_vectors I I.n u (fun k => ⟨⟨u k, hu k⟩, rfl⟩)
    rw [Formalism.L2.SG.Pf.Tau.t8O, Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨fun k => c ((Fintype.equivFin (Idx I)).symm k), ?_⟩
    rw [← hc, ← (Fintype.equivFin (Idx I)).symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [eB, bQ_apply]
  · rintro ⟨z, rfl⟩ i
    rw [← mem_integralClosure_iff]
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine zsmul_mem ?_ _
    rw [eB, bQ_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      rw [mem_integralClosure_iff, integralBasis_apply]
      exact (RingOfIntegers.basis I.E _).isIntegral_coe
    · exact zero_mem _

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def bm (y : I.Ginf) : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
  LinearMap.pi fun v => ((Matrix.toLin' (uMat (y v)⁻¹)).restrictScalars ℝ).comp (LinearMap.proj v)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem vec_eq (y : I.Ginf) (u : Fin I.n → I.E) : GlobalTheory.CuspGeo.vec I y u = bm I y (GlobalTheory.CuspGeo.vec I 1 u) := by
  funext v
  have h1 : uMat (1 : Formalism.REAL.UJ (I.ε v)) = 1 := by simp [uMat]
  simp [GlobalTheory.CuspGeo.vec, bm, h1]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem det_bm (y : I.Ginf) : LinearMap.det (bm I y) = 1 := by
  rw [bm, LinearMap.det_pi]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  exact normSq_det_UJ _

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem gm_eq {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) :
    gm I ρ y e = LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ bm I y ∘ₗ ρ.symm.toLinearMap) * gm I ρ 1 e := by
  ext i j
  rw [Matrix.mul_apply]
  change ρ (GlobalTheory.CuspGeo.vec I y (e j)) i = (LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ bm I y ∘ₗ ρ.symm.toLinearMap) *ᵥ
    (fun k => ρ (GlobalTheory.CuspGeo.vec I 1 (e j)) k)) i
  rw [LinearMap.toMatrix'_mulVec]
  simp [vec_eq I y]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem det_gm {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) : (gm I ρ y e).det = (gm I ρ 1 e).det := by
  rw [gm_eq, Matrix.det_mul, LinearMap.det_toMatrix', LinearMap.det_conj, det_bm, one_mul]

end GlobalTheory.RealCoordCusp

namespace GlobalTheory.RealCoordCusp

variable (I : AutInst)

def qm : (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) :=
  LinearMap.pi fun v => ((Matrix.toLin' (I.P v)⁻¹).restrictScalars ℝ).comp (LinearMap.proj v)

def sw : (Fin I.n × InfinitePlace I.F → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun z := fun v i => z (i, v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem qm_injective : Function.Injective (qm I) := by
  intro x y h
  funext v
  have h0 := congrFun h v
  simp only [qm, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
    Function.eval, LinearMap.coe_restrictScalars, Matrix.toLin'_apply] at h0
  have hu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h2 := congrArg (fun w => I.P v *ᵥ w) h0
  simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h2
  exact h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem sw_injective : Function.Injective (sw I) := by
  intro x y h
  funext q
  exact congrFun (congrFun h q.2) q.1

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Both sides reduce to the same expression. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem vec_one_bQ (p : Idx I) :
    GlobalTheory.CuspGeo.vec I 1 (bQ I p) = qm I (sw I (Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p)) := by
  funext v
  have h1 : uMat (1 : Formalism.REAL.UJ (I.ε v)) = 1 := by simp [uMat]
  have h2 : (fun i => I.φ v (bQ I p i)) = sw I (Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p) v := by
    funext i
    rw [bQ_apply, Pi.single_apply]
    change _ = Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p (i, v)
    rw [Formalism.L2.SG.Pf.Tau.placeCoordsBasis_apply]
    split_ifs with h
    · subst h; rfl
    · exact map_zero _
  simp only [GlobalTheory.CuspGeo.vec, Pi.one_apply, inv_one, h1, Matrix.one_mulVec]
  rw [h2]
  rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem det_gm_one_ne : (gm I (rho I) 1 (eB I)).det ≠ 0 := by
  have hli : LinearIndependent ℝ (fun j => (gm I (rho I) 1 (eB I))ᵀ j) := by
    have hf : LinearMap.ker ((rho I).toLinearMap ∘ₗ qm I ∘ₗ sw I) = ⊥ :=
      LinearMap.ker_eq_bot.2 ((rho I).injective.comp ((qm_injective I).comp (sw_injective I)))
    have h := ((Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n).linearIndependent.map' _ hf).comp _
      (Fintype.equivFin (Idx I)).symm.injective
    have heq : (fun j => (gm I (rho I) 1 (eB I))ᵀ j) =
        ((⇑((rho I).toLinearMap ∘ₗ qm I ∘ₗ sw I) ∘ ⇑(Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n)) ∘
          ⇑(Fintype.equivFin (Idx I)).symm) := by
      funext j
      funext i
      simp only [Matrix.transpose_apply, gm, Matrix.of_apply, Function.comp_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe]
      rw [eB, vec_one_bQ]
    rw [heq]
    exact h
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)).ne_zero

end GlobalTheory.RealCoordCusp

open GlobalTheory.RealCoordCusp in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.
-/
theorem GlobalTheory.CuspGeo.covolume_const : ∀ I : AutInst, ∃ (N : ℕ) (e : Fin N → Fin I.n → I.E)
    (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (d : ℝ),
    0 < d ∧ IsZBasis I e ∧ IsRealCoord I ρ ∧ ∀ y : I.Ginf, |(gm I ρ y e).det| = d := by
  intro I
  refine ⟨_, eB I, rho I, |(gm I (rho I) 1 (eB I)).det|, abs_pos.2 (det_gm_one_ne I), eB_isZBasis I,
    rho_isRealCoord I, fun y => by rw [det_gm]⟩
