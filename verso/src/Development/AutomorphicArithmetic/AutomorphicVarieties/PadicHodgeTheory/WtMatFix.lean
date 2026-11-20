import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsMonicUnitCoeffZeroAnnihilatingOfSpectrumNo
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCrystallinePeriodMatrixBcrisOfIsCrys
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrystallinePeriodMatrixMemFilZeroOfWeightZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.InertiaFixesOfFrobeniusAnnihilatedMemFilZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfMemSpectrumFrobeniusMatrixFilZero
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc

open Polynomial

variable {l : ℕ} [Fact l.Prime]

private def wtS (l : ℕ) [Fact l.Prime] : Subring (Bcr l) where
  carrier := {b | (PP l).ιB b ∈ ((PP l).PD (botExt l)).Fil 0}
  mul_mem' := fun {a b} ha hb => by
    have := ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ ha hb
    rw [add_zero, ← map_mul] at this
    exact this
  one_mem' := by
    change (PP l).ιB 1 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_one]; exact ((PP l).PD (botExt l)).one_mem
  add_mem' := fun {a b} ha hb => by
    change (PP l).ιB (a + b) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    change (PP l).ιB 0 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_zero]; exact Submodule.zero_mem _
  neg_mem' := fun {a} ha => by
    change (PP l).ιB (-a) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_neg]; exact Submodule.neg_mem _ ha

/- English proof (translation)
Establish `h : (PP l).ιB (algebraMap ↥(K0 K) (Bcr l) c) ∈ ((PP l).PD K).Fil 0`. Rewrite using `[← (PP l).PD_ι K, AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 (PP l).R.BdR, Algebra.algebraMap_eq_smul_one]`. Conclude with `(((PP l).PD K).Fil 0).smul_mem _ ((PP l).PD K).one_mem`. Establish `h2` using `(PP l).PD_Fil K (botExt l) 0`. Express the relevant statement in the definitionally equal form `(PP l).ιB _ ∈ (((PP l).PD (botExt l)).Fil 0 : Set (PP l).R.BdR)`.

Rewrite using `[← h2]`. Conclude with `h`.
-/
private theorem wt_alg (K : FinExt l) (c : ↥(K0 K)) : algebraMap ↥(K0 K) (Bcr l) c ∈ wtS l := by
  have h : (PP l).ιB (algebraMap ↥(K0 K) (Bcr l) c) ∈ ((PP l).PD K).Fil 0 := by
    rw [← (PP l).PD_ι K, AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 (PP l).R.BdR,
      Algebra.algebraMap_eq_smul_one]
    exact (((PP l).PD K).Fil 0).smul_mem _ ((PP l).PD K).one_mem
  have h2 := (PP l).PD_Fil K (botExt l) 0
  change (PP l).ιB _ ∈ (((PP l).PD (botExt l)).Fil 0 : Set (PP l).R.BdR)
  rw [← h2]
  exact h

/- English proof (translation)
Rewrite using `[← (PP l).PD_φ K, ((PP l).PD K).φ_K₀]`.
-/
private theorem wt_phi (K : FinExt l) (c : ↥(K0 K)) :
    (PP l).φB (algebraMap ↥(K0 K) (Bcr l) c) = algebraMap ↥(K0 K) (Bcr l) (((PP l).PD K).σ c) := by
  rw [← (PP l).PD_φ K, ((PP l).PD K).φ_K₀]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨1, by simp, by simp⟩`. Consider the case `succ k ih`. Take `⟨F, hF, e⟩` from `ih`. Use `⟨A * F.map ((PP l).PD K).σ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_mul]`. Use `hA.mul ?_` and prove the remaining obligations. Use `hF.map (((PP l).PD K).σ : ↥(K0 K) →+* ↥(K0 K))` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Conclude with `this`.

Rewrite using `[Function.iterate_succ', ← Matrix.map_map, e, Matrix.map_mul, h, Matrix.map_mul, Matrix.mul_assoc]`. Use `congr 2`. Use extensionality with `i j`. Conclude with `wt_phi K _`.
-/
private theorem wt_iter (K : FinExt l) {d : ℕ} (M : Matrix (Fin d) (Fin d) (Bcr l))
    (A : Matrix (Fin d) (Fin d) ↥(K0 K)) (hA : IsUnit A.det)
    (h : M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l))) (k : ℕ) :
    ∃ F : Matrix (Fin d) (Fin d) ↥(K0 K), IsUnit F.det ∧
      M.map (((PP l).φB)^[k]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) := by
  induction k with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨F, hF, e⟩ := ih
    refine ⟨A * F.map ((PP l).PD K).σ, ?_, ?_⟩
    · rw [Matrix.det_mul]
      refine hA.mul ?_
      have := hF.map (((PP l).PD K).σ : ↥(K0 K) →+* ↥(K0 K))
      rw [RingHom.map_det] at this
      exact this
    · rw [Function.iterate_succ', ← Matrix.map_map, e, Matrix.map_mul, h, Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext i j
      exact wt_phi K _

/- English proof (translation)
Rewrite `ha` using `[spectrum.mem_iff]`. Establish `h0 : a ≠ 0`. Introduce and unpack `rfl`. Apply `ha` to reduce the goal to its premises. Rewrite using `[map_zero, zero_sub]`.

Conclude with `((Matrix.isUnit_iff_isUnit_det _).2 hG).neg`. Use `⟨h0, spectrum.mem_iff.2 fun hu => ha ?_⟩` and prove the remaining obligations. Establish `e : (algebraMap L (Matrix (Fin d) (Fin d) L) a⁻¹ - (G⁻¹).transpose).transpose * ((-a) • G) = algebraMap L (Matrix (Fin d) (Fin d) L) a - G`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.nonsing_inv_mul _ hG, smul_sub, smul_smul, neg_ …`. Normalize the expressions using the abelian group laws.

Rewrite using `[← e]`. Use `((Matrix.isUnit_transpose _).2 hu).mul ?_` and prove the remaining obligations. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]`. Conclude with `((IsUnit.mk0 _ (neg_ne_zero.2 h0)).pow _).mul hG`.
-/
private theorem wt_spec {L : Type} [Field L] {d : ℕ} (G : Matrix (Fin d) (Fin d) L) (hG : IsUnit G.det) {a : L}
    (ha : a ∈ spectrum L G) : a ≠ 0 ∧ a⁻¹ ∈ spectrum L (G⁻¹).transpose := by
  rw [spectrum.mem_iff] at ha
  have h0 : a ≠ 0 := by
    rintro rfl
    apply ha
    rw [map_zero, zero_sub]
    exact ((Matrix.isUnit_iff_isUnit_det _).2 hG).neg
  refine ⟨h0, spectrum.mem_iff.2 fun hu => ha ?_⟩
  have e : (algebraMap L (Matrix (Fin d) (Fin d) L) a⁻¹ - (G⁻¹).transpose).transpose * ((-a) • G) =
      algebraMap L (Matrix (Fin d) (Fin d) L) a - G := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.nonsing_inv_mul _ hG, smul_sub, smul_smul, neg_mul,
      mul_inv_cancel₀ h0, neg_smul, neg_smul, one_smul]
    abel
  rw [← e]
  refine ((Matrix.isUnit_transpose _).2 hu).mul ?_
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
  exact ((IsUnit.mk0 _ (neg_ne_zero.2 h0)).pow _).mul hG

/- English proof (translation)
Establish `hp : ∀ n : ℕ, M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ n) = M * (F ^ n).map (algebraMap ↥(K0 K) (Bcr l))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, pow_zero, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`.

Both sides reduce to the same expression. Consider the case `succ n ih`. Establish `e : M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ (n + 1)) = (M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ n)).map ψ`. Use extensionality with `i j`. Rewrite using `[pow_succ']`.

Both sides reduce to the same expression. Rewrite using `[e, ih, Matrix.map_mul, h, pow_succ', Matrix.map_mul, Matrix.mul_assoc]`. Use `congr 2`. Use extensionality with `i j`. Conclude with `hψ _`.

Proceed by induction on `Q using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Rewrite using `[Polynomial.map_add, map_add, map_add, Matrix.map_add _ (map_add _), Matrix.mul_add, ← hp, ← hq]`. Both sides reduce to the same expression. Consider the case `monomial n a`.

Rewrite using `[Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]`. Use extensionality with `i j`. Use `congrFun (congrFun (hp n) i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply, Matrix.mul_apply] at this`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, LinearMap.smul_apply, this, Matrix.smul_apply, smul_eq_mul, map_mul, ← IsScalarTower.algebraMap_apply]`.

Rewrite using `[Algebra.smul_def, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
private theorem wt_aeval (K : FinExt l) (ψ : Bcr l →ₐ[ℚ_[l]] Bcr l)
    (hψ : ∀ c : ↥(K0 K), ψ (algebraMap ↥(K0 K) (Bcr l) c) = algebraMap ↥(K0 K) (Bcr l) c) {d : ℕ}
    (M : Matrix (Fin d) (Fin d) (Bcr l)) (F : Matrix (Fin d) (Fin d) ↥(K0 K))
    (h : M.map ψ = M * F.map (algebraMap ↥(K0 K) (Bcr l))) (Q : ℚ_[l][X]) :
    M.map (aeval (ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) Q) =
      M * (aeval F (Q.map (algebraMap ℚ_[l] ↥(K0 K)))).map (algebraMap ↥(K0 K) (Bcr l)) := by
  have hp : ∀ n : ℕ, M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ n) =
      M * (F ^ n).map (algebraMap ↥(K0 K) (Bcr l)) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      rfl
    | succ n ih =>
      have e : M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ (n + 1)) =
          (M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ n)).map ψ := by
        ext i j
        rw [pow_succ']
        rfl
      rw [e, ih, Matrix.map_mul, h, pow_succ', Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext i j
      exact hψ _
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, map_add, map_add, Matrix.map_add _ (map_add _), Matrix.mul_add, ← hp, ← hq]
    rfl
  | monomial n a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]
    ext i j
    have := congrFun (congrFun (hp n) i) j
    simp only [Matrix.map_apply, Matrix.mul_apply] at this
    simp only [Matrix.map_apply, Matrix.mul_apply, LinearMap.smul_apply, this, Matrix.smul_apply, smul_eq_mul,
      map_mul, ← IsScalarTower.algebraMap_apply]
    rw [Algebra.smul_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Use `haveI := ((PP l).PD K).finK₀`. Set `s : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K)` to `AlgEquiv.ofBijective ((PP l).PD K).σ ((PP l).PD K).σ_bij`. Establish `hf : 0 < orderOf s` using `orderOf_pos s`. Establish `hσ : ∀ x : ↥(K0 K), (((PP l).PD K).σ)^[orderOf s] x = x` using `fun x => by`. Use `AlgEquiv.congr_fun (pow_orderOf_eq_one s) x` as an intermediate fact.

Rewrite `this` using `[AlgEquiv.coe_pow]`. Conclude with `this`. Generalize the expression as in `orderOf s = f at hf hσ`. Establish `hMM' : M' * M = 1` using `mul_eq_one_comm.1 hMM`. Establish `hc : ∀ k : ℕ, ((PP l).φB)^[k] = ⇑((PP l).φB ^ k)` using `fun k => (AlgHom.coe_pow _ _).symm`.

Use `choose F hF hMF using wt_iter K M A hA h`. Establish `hinv : ∀ k, M'.transpose.map (((PP l).φB)^[k]) = M'.transpose * ((F k)⁻¹).transpose.map (algebraMap ↥(K0 K) (Bcr l))`. Introduce `k`. Rewrite using `[Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul]`. Use `congr 1`.

Establish `e1 : M'.map (((PP l).φB)^[k]) * M.map (((PP l).φB)^[k]) = 1`. Rewrite using `[hc, ← Matrix.map_mul, hMM', Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `e2 : (F k).map (algebraMap ↥(K0 K) (Bcr l)) * ((F k)⁻¹).map (algebraMap ↥(K0 K) (Bcr l)) = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ (hF k), Matrix.map_one _ (map_zero _) (map_one _)]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Matrix.mul_assoc M, ← hMF, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul]`. Establish `hS : ∀ (N : Matrix (Fin d) (Fin d) (Bcr l)) (E : Matrix (Fin d) (Fin d) ↥(K0 K)) (k : ℕ), (∀ i j, N i j ∈ wtS l) → N.map (((PP l).φB)^[k]) = N * E.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ i j, ((PP l).φB)^[k] (N i j) ∈ wtS l`. Introduce `N E k hN e i j`. Use `congrFun (congrFun e i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply, Matrix.mul_apply]`.

Rewrite using `[this]`. Conclude with `Subring.sum_mem _ fun r _ => Subring.mul_mem _ (hN _ _) (wt_alg K _)`. Establish `h1` using `UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ M M' (F f) hMM' (fun k => hS M (F k) k hM (hMF k)) (hMF f)`. Establish `h2` using `UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ M'.transpose M.transpose ((F f)⁻¹).transpose (by rw [← Matrix.transpose_mul, hMM', Matrix.transpose_one]) (fun k => hS M'.transpose _ k (fun i j => hM' j i) (hinv k)) (hinv f)`. Take `⟨P, hP, hP0, hPF⟩` from `UpperTheory.exists_monic_unit_coeff_zero_annihilating_of_spectrum_norm_one (K0 K) (F f) (fun a ha => by`.

Establish `hu : IsUnit ((F f).map (algebraMap ↥(K0 K) (Om l))).det`. Use `(hF f).map (algebraMap ↥(K0 K) (Om l))` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Conclude with `this`. Take `⟨h0, ha'⟩` from `wt_spec _ hu ha`.

Establish `e : ((F f).map (algebraMap ↥(K0 K) (Om l)))⁻¹ = ((F f)⁻¹).map (algebraMap ↥(K0 K) (Om l))`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ (hF f), Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite `ha'` using `[e, ← Matrix.transpose_map]`. Establish `h3` using `h2 _ ha'`.

Rewrite `h3` using `[norm_inv, inv_le_one₀ (norm_pos_iff.2 h0)]`. Conclude with `le_antisymm (h1 a ha) h3)`. Establish `hfix : ∀ (k : ℕ) (c : ↥(K0 K)), ((PP l).φB)^[k] (algebraMap ↥(K0 K) (Bcr l) c) = algebraMap ↥(K0 K) (Bcr l) ((((PP l).PD K).σ)^[k] c)`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro c`. Both sides reduce to the same expression. Consider the case `succ k ih => intro c`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ih, wt_phi]`. Establish `h4` using `wt_aeval K ((PP l).φB ^ f) (fun c => by rw [← hc, hfix, hσ]) M (F f) (by rw [← hc]; exact hMF f) (P.map (algebraMap ℤ_[l] ℚ_[l]))`.

Rewrite `h4` using `[Polynomial.map_map, hPF, Matrix.map_zero _ (map_zero _), Matrix.mul_zero]`. Introduce `g hg`. Use extensionality with `i j`. Use `UpperTheory.inertia_fixes_of_frobenius_annihilated_mem_fil_zero (expand ℤ_[l] f P) (hP.expand hf) (by rwa [coeff_expand hf, if_pos (dvd_zero _), Nat.zero_div]) (M i j) ?_ (fun k => hS M (F k) k hM (hMF k) i j) g hg` and prove the remaining obligations. Establish `e : ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ f = ((PP l).φB ^ f).toLinearMap`.

Use extensionality with `x`. Rewrite using `[Module.End.pow_apply, AlgHom.toLinearMap_apply, ← hc]`. Both sides reduce to the same expression. Rewrite using `[Polynomial.map_expand, expand_aeval, e]`. Conclude with `congrFun (congrFun h4 i) j`.
-/
private theorem wt_matFix (K : FinExt l) {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l))
    (A : Matrix (Fin d) (Fin d) ↥(K0 K)) (hMM : M * M' = 1) (hM : ∀ i j, M i j ∈ wtS l)
    (hM' : ∀ i j, M' i j ∈ wtS l) (hA : IsUnit A.det)
    (h : M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l))) :
    ∀ g ∈ Iq l, M.map ((PP l).actQ g) = M := by
  haveI := ((PP l).PD K).finK₀
  let s : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K) := AlgEquiv.ofBijective ((PP l).PD K).σ ((PP l).PD K).σ_bij
  have hf : 0 < orderOf s := orderOf_pos s
  have hσ : ∀ x : ↥(K0 K), (((PP l).PD K).σ)^[orderOf s] x = x := fun x => by
    have := AlgEquiv.congr_fun (pow_orderOf_eq_one s) x
    rw [AlgEquiv.coe_pow] at this
    exact this
  generalize orderOf s = f at hf hσ
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  have hc : ∀ k : ℕ, ((PP l).φB)^[k] = ⇑((PP l).φB ^ k) := fun k => (AlgHom.coe_pow _ _).symm
  choose F hF hMF using wt_iter K M A hA h
  have hinv : ∀ k, M'.transpose.map (((PP l).φB)^[k]) =
      M'.transpose * ((F k)⁻¹).transpose.map (algebraMap ↥(K0 K) (Bcr l)) := by
    intro k
    rw [Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul]
    congr 1
    have e1 : M'.map (((PP l).φB)^[k]) * M.map (((PP l).φB)^[k]) = 1 := by
      rw [hc, ← Matrix.map_mul, hMM', Matrix.map_one _ (map_zero _) (map_one _)]
    have e2 : (F k).map (algebraMap ↥(K0 K) (Bcr l)) * ((F k)⁻¹).map (algebraMap ↥(K0 K) (Bcr l)) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (hF k), Matrix.map_one _ (map_zero _) (map_one _)]
    calc M'.map (((PP l).φB)^[k]) = M'.map (((PP l).φB)^[k]) * (M * ((F k).map (algebraMap ↥(K0 K) (Bcr l)) *
          ((F k)⁻¹).map (algebraMap ↥(K0 K) (Bcr l))) * M') := by rw [e2, Matrix.mul_one, hMM, Matrix.mul_one]
      _ = _ := by
        rw [← Matrix.mul_assoc M, ← hMF, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hS : ∀ (N : Matrix (Fin d) (Fin d) (Bcr l)) (E : Matrix (Fin d) (Fin d) ↥(K0 K)) (k : ℕ),
      (∀ i j, N i j ∈ wtS l) → N.map (((PP l).φB)^[k]) = N * E.map (algebraMap ↥(K0 K) (Bcr l)) →
      ∀ i j, ((PP l).φB)^[k] (N i j) ∈ wtS l := by
    intro N E k hN e i j
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    rw [this]
    exact Subring.sum_mem _ fun r _ => Subring.mul_mem _ (hN _ _) (wt_alg K _)
  have h1 := UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ M M' (F f) hMM' (fun k => hS M (F k) k hM (hMF k)) (hMF f)
  have h2 := UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ M'.transpose M.transpose ((F f)⁻¹).transpose
    (by rw [← Matrix.transpose_mul, hMM', Matrix.transpose_one])
    (fun k => hS M'.transpose _ k (fun i j => hM' j i) (hinv k)) (hinv f)
  obtain ⟨P, hP, hP0, hPF⟩ := UpperTheory.exists_monic_unit_coeff_zero_annihilating_of_spectrum_norm_one (K0 K) (F f) (fun a ha => by
    have hu : IsUnit ((F f).map (algebraMap ↥(K0 K) (Om l))).det := by
      have := (hF f).map (algebraMap ↥(K0 K) (Om l))
      rw [RingHom.map_det] at this
      exact this
    obtain ⟨h0, ha'⟩ := wt_spec _ hu ha
    have e : ((F f).map (algebraMap ↥(K0 K) (Om l)))⁻¹ = ((F f)⁻¹).map (algebraMap ↥(K0 K) (Om l)) := by
      apply Matrix.inv_eq_right_inv
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (hF f), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e, ← Matrix.transpose_map] at ha'
    have h3 := h2 _ ha'
    rw [norm_inv, inv_le_one₀ (norm_pos_iff.2 h0)] at h3
    exact le_antisymm (h1 a ha) h3)
  have hfix : ∀ (k : ℕ) (c : ↥(K0 K)), ((PP l).φB)^[k] (algebraMap ↥(K0 K) (Bcr l) c) =
      algebraMap ↥(K0 K) (Bcr l) ((((PP l).PD K).σ)^[k] c) := by
    intro k
    induction k with
    | zero => intro c; rfl
    | succ k ih => intro c; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, wt_phi]
  have h4 := wt_aeval K ((PP l).φB ^ f) (fun c => by rw [← hc, hfix, hσ]) M (F f) (by rw [← hc]; exact hMF f)
    (P.map (algebraMap ℤ_[l] ℚ_[l]))
  rw [Polynomial.map_map, hPF, Matrix.map_zero _ (map_zero _), Matrix.mul_zero] at h4
  intro g hg
  ext i j
  refine UpperTheory.inertia_fixes_of_frobenius_annihilated_mem_fil_zero (expand ℤ_[l] f P) (hP.expand hf) (by rwa [coeff_expand hf, if_pos (dvd_zero _), Nat.zero_div])
    (M i j) ?_ (fun k => hS M (F k) k hM (hMF k) i j) g hg
  have e : ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ f = ((PP l).φB ^ f).toLinearMap := by
    ext x
    rw [Module.End.pow_apply, AlgHom.toLinearMap_apply, ← hc]
    rfl
  rw [Polynomial.map_expand, expand_aeval, e]
  exact congrFun (congrFun h4 i) j

end UpperTheory.V.Loc

/- English proof (translation)
Introduce `l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ _ hcr h0 h1 g hg`. Take `⟨K, e, -, -, he, -, -, hidx⟩` from `openField φ hφ`. Establish `he' : ∀ x, ((e x : ↥(GK K)) : GQ l) = φ x` using `fun x => DFunLike.congr_fun he x`. Set `ρ' : Representation ℚ_[l] ↥(GK K) V` to `(resCoef ℚ_[l] ρ).comp e.symm.toMonoidHom`. Establish `hB : ∀ x y, actVB ((PP l).PD K) ρ' (e x) y = actC φ (resCoef ℚ_[l] ρ) x y`.

Introduce `x y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul v b`. Express the relevant statement in the definitionally equal form `ρ (e.symm (e x)) v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actB (e x) b = ρ x v ⊗ₜ[ℚ_[l]] (PP l).actQ (φ x) b`.

Rewrite using `[(PP l).PD_actB, he', e.symm_apply_apply]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hD : ∀ x y, actVdR ((PP l).PD K) ρ' (e x) y = actD φ ρ x y`. Introduce `x y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp only [map_zero]`. Consider the case `tmul v b`. Express the relevant statement in the definitionally equal form `ρ (e.symm (e x)) v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actdR (e x) b = ρ x v ⊗ₜ[ℚ_[l]] (PP l).actQdR (φ x) b`. Rewrite using `[(PP l).PD_actdR, he', e.symm_apply_apply]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Establish `hC : Dcris ((PP l).PD K) ρ' = Dcr φ (resCoef ℚ_[l] ρ)`. Use extensionality with `y`. Simplify using `only [Dcris, Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, e.surjective.forall, hB]`. Establish `hDD : ∀ y, y ∈ DdR ((PP l).PD K) ρ' ↔ y ∈ Ddr φ ρ`. Introduce `y`.

Simplify using `only [DdR, Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, e.surjective.forall, hD]`. Establish `hFil : ∀ a, (((PP l).PD K).Fil a).restrictScalars ℚ_[l] = (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l]` using `fun a => SetLike.coe_injective ((PP l).PD_Fil K (botExt l) a)`. Establish `hF : ∀ a y, y ∈ FilV ((PP l).PD K) (LL` using `ℚ_[l]) (V := V) a ↔ y ∈ FilT A V a := by`. Introduce `a y`. Unfold `FilV FilT`.

Rewrite using `[hFil]`. Conclude with `Iff.rfl`. Establish `hcrys : IsCrys ((PP l).PD K) ρ'`. Unfold `IsCrys`. Rewrite using `[hC, ← hidx]`.

Conclude with `hcr`. Set `b` to `Module.finBasis ℚ_[l] V`. Take `⟨M, M', A', hMM, hA, hφM, hρ⟩` from `UpperTheory.exists_crystalline_period_matrix_bcris_of_isCrys K ρ' b hcrys`. Take `⟨hM, hM'⟩` from `UpperTheory.crystalline_period_matrix_mem_fil_zero_of_weight_zero K ρ' b hcrys (fun y hy => (hF 0 y).2 ((h0.ge ((hDD y).1 hy)).2)) (eq_bot_iff.2 fun y hy => h1.le ⟨(hDD y).1 hy.1, (hF 1 y).1 hy.2⟩) M M' hMM hρ`. Establish `h2` using `hρ (e g)`.

Rewrite `h2` using `[he', wt_matFix K M M' A' hMM hM hM' hA hφM _ hg]`. Establish `h3` using `congrArg (· * M') h2`. Simplify using `only [Matrix.mul_assoc, hMM, Matrix.mul_one] at h3`. Use `haveI : Nontrivial (Bcr l) := ⟨⟨1, 0, fun h => ((PP l).PD K).not_mem_filtration_two (by`. Rewrite using `[← mul_one ((PP l).PD K).t, h, mul_zero, map_zero]`.

Conclude with `Submodule.zero_mem _)⟩⟩`. Establish `h4 : LinearMap.toMatrix b b (ρ' (e g)) = 1`. Apply `Matrix.map_injective (algebraMap ℚ_[l] (Bcr l)).injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Matrix.map _ _ = Matrix.map _ _`. Rewrite using `[h3, Matrix.map_one _ (map_zero _) (map_one _)]`.

Rewrite `h4` using `[← LinearMap.toMatrix_one b]`. Establish `h5` using `(LinearMap.toMatrix b b).injective h4`. Use extensionality with `v`. Establish `h6 : ρ (e.symm (e g)) v = v` using `LinearMap.congr_fun h5 v`. Rewrite `h6` using `[e.symm_apply_apply]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Loc.crWt0 :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → IsCr φ ρ → FilD φ ρ 0 = Ddr φ ρ → FilD φ ρ 1 = ⊥ → ∀ g, φ g ∈ Iq l → ρ g = 1 := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ _ hcr h0 h1 g hg
  obtain ⟨K, e, -, -, he, -, -, hidx⟩ := openField φ hφ
  have he' : ∀ x, ((e x : ↥(GK K)) : GQ l) = φ x := fun x => DFunLike.congr_fun he x
  let ρ' : Representation ℚ_[l] ↥(GK K) V := (resCoef ℚ_[l] ρ).comp e.symm.toMonoidHom
  have hB : ∀ x y, actVB ((PP l).PD K) ρ' (e x) y = actC φ (resCoef ℚ_[l] ρ) x y := by
    intro x y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b =>
      change ρ (e.symm (e x)) v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actB (e x) b = ρ x v ⊗ₜ[ℚ_[l]] (PP l).actQ (φ x) b
      rw [(PP l).PD_actB, he', e.symm_apply_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hD : ∀ x y, actVdR ((PP l).PD K) ρ' (e x) y = actD φ ρ x y := by
    intro x y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b =>
      change ρ (e.symm (e x)) v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actdR (e x) b = ρ x v ⊗ₜ[ℚ_[l]] (PP l).actQdR (φ x) b
      rw [(PP l).PD_actdR, he', e.symm_apply_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hC : Dcris ((PP l).PD K) ρ' = Dcr φ (resCoef ℚ_[l] ρ) := by
    ext y
    simp only [Dcris, Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      e.surjective.forall, hB]
  have hDD : ∀ y, y ∈ DdR ((PP l).PD K) ρ' ↔ y ∈ Ddr φ ρ := by
    intro y
    simp only [DdR, Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      e.surjective.forall, hD]
  have hFil : ∀ a, (((PP l).PD K).Fil a).restrictScalars ℚ_[l] =
      (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l] := fun a =>
    SetLike.coe_injective ((PP l).PD_Fil K (botExt l) a)
  have hF : ∀ a y, y ∈ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a ↔ y ∈ FilT A V a := by
    intro a y
    unfold FilV FilT
    rw [hFil]
    exact Iff.rfl
  have hcrys : IsCrys ((PP l).PD K) ρ' := by
    unfold IsCrys
    rw [hC, ← hidx]
    exact hcr
  let b := Module.finBasis ℚ_[l] V
  obtain ⟨M, M', A', hMM, hA, hφM, hρ⟩ := UpperTheory.exists_crystalline_period_matrix_bcris_of_isCrys K ρ' b hcrys
  obtain ⟨hM, hM'⟩ := UpperTheory.crystalline_period_matrix_mem_fil_zero_of_weight_zero K ρ' b hcrys
    (fun y hy => (hF 0 y).2 ((h0.ge ((hDD y).1 hy)).2))
    (eq_bot_iff.2 fun y hy => h1.le ⟨(hDD y).1 hy.1, (hF 1 y).1 hy.2⟩) M M' hMM hρ
  have h2 := hρ (e g)
  rw [he', wt_matFix K M M' A' hMM hM hM' hA hφM _ hg] at h2
  have h3 := congrArg (· * M') h2
  simp only [Matrix.mul_assoc, hMM, Matrix.mul_one] at h3
  haveI : Nontrivial (Bcr l) := ⟨⟨1, 0, fun h => ((PP l).PD K).not_mem_filtration_two (by
    rw [← mul_one ((PP l).PD K).t, h, mul_zero, map_zero]; exact Submodule.zero_mem _)⟩⟩
  have h4 : LinearMap.toMatrix b b (ρ' (e g)) = 1 := by
    apply Matrix.map_injective (algebraMap ℚ_[l] (Bcr l)).injective
    change Matrix.map _ _ = Matrix.map _ _
    rw [h3, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← LinearMap.toMatrix_one b] at h4
  have h5 := (LinearMap.toMatrix b b).injective h4
  ext v
  have h6 : ρ (e.symm (e g)) v = v := LinearMap.congr_fun h5 v
  rwa [e.symm_apply_apply] at h6
