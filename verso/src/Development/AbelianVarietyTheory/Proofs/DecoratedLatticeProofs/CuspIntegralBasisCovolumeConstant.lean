import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.BlockDiagonalMulVecApply

noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.RealCoordCusp

/- English proof (translation)
Establish `hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε` using `g.2`. Establish `hJ : (Formalism.REAL.Jm ε).det ≠ 0`. Introduce `h`. Use `congrArg Matrix.det (Formalism.REAL.Jm_mul_self ε)` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h, zero_mul, Matrix.det_one]`.

Conclude with `zero_ne_one this`. Establish `h1` using `congrArg Matrix.det hg`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Establish `h2 : star (uMat g).det * (uMat g).det = 1`. Establish `: (star (uMat g).det * (uMat g).det - 1) * (Formalism.REAL.Jm ε).det = 0` using `by linear_combination h1`.

Break down `mul_eq_zero.1 this with h | h` into its components or cases. Take the linear combination `h`. Conclude with `absurd h hJ`. Establish `h3 : ((Complex.normSq (uMat g).det : ℝ) : ℂ) = 1`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`.

Conclude with `h2`. Conclude with `h3` after adjusting the coercions.
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
Simplify using `only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Formalism.L2.SG.Pf.Tau.card_infinite_places, Formalism.L2.SG.Pf.Tau.card_integral_basis]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_eq : Fintype.card (Σ _ : InfinitePlace I.F, Σ _ : Fin I.n, Fin 2) = Fintype.card (Idx I) := by
  simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Formalism.L2.SG.Pf.Tau.card_infinite_places, Formalism.L2.SG.Pf.Tau.card_integral_basis]
  ring

def rho : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin (Fintype.card (Idx I)) → ℝ) :=
  ((cBasis I).reindex (Fintype.equivFinOfCardEq (card_eq I))).equivFun

/- English proof (translation)
Introduce `x y`. Simplify using `only [rho, Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply, dotProduct]`. Rewrite using `[(Fintype.equivFinOfCardEq (card_eq I)).symm.sum_comp (fun s => (cBasis I).repr x s * (cBasis I).repr y s)]`. Simplify using `only [cBasis, Fintype.sum_sigma, Pi.basis_repr, Complex.coe_basisOneI_repr, Fin.sum_univ_two]`. Use `Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `[Complex.mul_re]`.
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
Simplify using `[bQ, Pi.basis_apply]`.
-/
theorem bQ_apply (p : Idx I) : bQ I p = Pi.single p.1 (integralBasis I.E p.2) := by
  simp [bQ, Pi.basis_apply]

/- English proof (translation)
Use `⟨((bQ I).linearIndependent.comp _ (Fintype.equivFin (Idx I)).symm.injective).restrict_scalars' ℤ, ?_⟩` and prove the remaining obligations. Introduce `u`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Establish `hm` using `Formalism.L2.SG.Pf.Tau.mem_integral_vectors I I.n u (fun k => ⟨⟨u k, hu k⟩, rfl⟩)`.

Rewrite `hm` using `[Formalism.L2.SG.Pf.Tau.t8O, Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, hc⟩` from `hm`. Use `⟨fun k => c ((Fintype.equivFin (Idx I)).symm k), ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, ← (Fintype.equivFin (Idx I)).symm.sum_comp]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `[eB, bQ_apply]`. Introduce and unpack `⟨z, rfl⟩ i`. Rewrite using `[← mem_integralClosure_iff]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Use `Subalgebra.sum_mem _ fun k _ => ?_` and prove the remaining obligations.

Use `zsmul_mem ?_ _` and prove the remaining obligations. Rewrite using `[eB, bQ_apply, Pi.single_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[mem_integralClosure_iff, integralBasis_apply]`.

Conclude with `(RingOfIntegers.basis I.E _).isIntegral_coe`. Conclude with `zero_mem _`.
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
Use function extensionality and compare the values at `v`. Establish `h1 : uMat (1 : Formalism.REAL.UJ (I.ε v)) = 1` using `by simp [uMat]`. Simplify using `[GlobalTheory.CuspGeo.vec, bm, h1]`.
-/
theorem vec_eq (y : I.Ginf) (u : Fin I.n → I.E) : GlobalTheory.CuspGeo.vec I y u = bm I y (GlobalTheory.CuspGeo.vec I 1 u) := by
  funext v
  have h1 : uMat (1 : Formalism.REAL.UJ (I.ε v)) = 1 := by simp [uMat]
  simp [GlobalTheory.CuspGeo.vec, bm, h1]

/- English proof (translation)
Rewrite using `[bm, LinearMap.det_pi]`. Use `Finset.prod_eq_one fun v _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]`. Conclude with `normSq_det_UJ _`.
-/
theorem det_bm (y : I.Ginf) : LinearMap.det (bm I y) = 1 := by
  rw [bm, LinearMap.det_pi]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  exact normSq_det_UJ _

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Express the relevant statement in the definitionally equal form `ρ (GlobalTheory.CuspGeo.vec I y (e j)) i = (LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ bm I y ∘ₗ ρ.symm.toLinearMap) *ᵥ (fun k => ρ (GlobalTheory.CuspGeo.vec I 1 (e j)) k)) i`. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Simplify using `[vec_eq I y]`.
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
Rewrite using `[gm_eq, Matrix.det_mul, LinearMap.det_toMatrix', LinearMap.det_conj, det_bm, one_mul]`.
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
Introduce `x y h`. Use function extensionality and compare the values at `v`. Establish `h0` using `congrFun h v`. Simplify using `only [qm, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval, LinearMap.coe_restrictScalars, Matrix.toLin'_apply] at h0`. Establish `hu : IsUnit (I.P v).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)`.

Establish `h2` using `congrArg (fun w => I.P v *ᵥ w) h0`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec] at h2`. Conclude with `h2`.
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
Introduce `x y h`. Use function extensionality and compare the values at `q`. Conclude with `congrFun (congrFun h q.2) q.1`.
-/
theorem sw_injective : Function.Injective (sw I) := by
  intro x y h
  funext q
  exact congrFun (congrFun h q.2) q.1

/- English proof (translation)
Use function extensionality and compare the values at `v`. Establish `h1 : uMat (1 : Formalism.REAL.UJ (I.ε v)) = 1` using `by simp [uMat]`. Establish `h2 : (fun i => I.φ v (bQ I p i)) = sw I (Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p) v`. Use function extensionality and compare the values at `i`. Rewrite using `[bQ_apply, Pi.single_apply]`.

Express the relevant statement in the definitionally equal form `_ = Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n p (i, v)`. Rewrite using `[Formalism.L2.SG.Pf.Tau.placeCoordsBasis_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Both sides reduce to the same expression.

Conclude with `map_zero _`. Simplify using `only [GlobalTheory.CuspGeo.vec, Pi.one_apply, inv_one, h1, Matrix.one_mulVec]`. Rewrite using `[h2]`. Both sides reduce to the same expression.
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
Establish `hli : LinearIndependent ℝ (fun j => (gm I (rho I) 1 (eB I))ᵀ j)`. Establish `hf : LinearMap.ker ((rho I).toLinearMap ∘ₗ qm I ∘ₗ sw I) = ⊥` using `LinearMap.ker_eq_bot.2 ((rho I).injective.comp ((qm_injective I).comp (sw_injective I)))`. Establish `h` using `((Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n).linearIndependent.map' _ hf).comp _ (Fintype.equivFin (Idx I)).symm.injective`. Establish `heq : (fun j => (gm I (rho I) 1 (eB I))ᵀ j) = ((⇑((rho I).toLinearMap ∘ₗ qm I ∘ₗ sw I) ∘ ⇑(Formalism.L2.SG.Pf.Tau.placeCoordsBasis I I.n)) ∘ ⇑(Fintype.equivFin (Idx I)).symm)`. Use function extensionality and compare the values at `j`.

Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.transpose_apply, gm, Matrix.of_apply, Function.comp_apply, LinearMap.coe_comp, LinearEquiv.coe_coe]`. Rewrite using `[eB, vec_one_bQ]`. Rewrite using `[heq]`. Conclude with `h`.

Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)).ne_zero`.
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
Introduce `I`. Use `⟨_, eB I, rho I, |(gm I (rho I) 1 (eB I)).det|, abs_pos.2 (det_gm_one_ne I), eB_isZBasis I, rho_isRealCoord I, fun y => by rw [det_gm]⟩` and prove the remaining obligations.
-/
theorem GlobalTheory.CuspGeo.covolume_const : ∀ I : AutInst, ∃ (N : ℕ) (e : Fin N → Fin I.n → I.E)
    (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (d : ℝ),
    0 < d ∧ IsZBasis I e ∧ IsRealCoord I ρ ∧ ∀ y : I.Ginf, |(gm I ρ y e).det| = d := by
  intro I
  refine ⟨_, eB I, rho I, |(gm I (rho I) 1 (eB I)).det|, abs_pos.2 (det_gm_one_ne I), eB_isZBasis I,
    rho_isRealCoord I, fun y => by rw [det_gm]⟩
