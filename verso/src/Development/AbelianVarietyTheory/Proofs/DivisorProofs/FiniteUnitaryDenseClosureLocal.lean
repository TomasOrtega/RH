import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFiniteAdeleLocalApproximation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoUnitaryAdelicPointsAgreeOnGrowingFinset

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Filter Topology GlobalTheory.AdelicLocalPoint

noncomputable section

namespace GlobalTheory.FinPlaceDense

/- English proof (translation)
Establish `h1 : ε * (1 - δ) = ε` using `by linear_combination -h`. Establish `h2 : (1 - ε) * δ = δ` using `by linear_combination -h`. Establish `h3 : (1 - ε) * (1 - δ) = 1 - (ε + δ)` using `by linear_combination h`. Simplify using `only [cut, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, smul_add, mul_comm δ, mul_comm (1 - δ), h, h1, h2, h3, zero_smul, zero_add, add_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem cut_add {S ι : Type} [CommRing S] [Fintype ι] [DecidableEq ι] {ε δ : S} (h : ε * δ = 0) (A : Matrix ι ι S) :
    cut ε A * cut δ A = cut (ε + δ) A := by
  have h1 : ε * (1 - δ) = ε := by linear_combination -h
  have h2 : (1 - ε) * δ = δ := by linear_combination -h
  have h3 : (1 - ε) * (1 - δ) = 1 - (ε + δ) := by linear_combination h
  simp only [cut, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_add, mul_comm δ, mul_comm (1 - δ), h, h1, h2, h3, zero_smul, zero_add, add_smul]
  abel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idemS (T : Finset (Pl F)) : AF F := ∑ v ∈ T, GlobalTheory.LatVac.liftV v 1

variable (F) in

def idemFin : AF F := LinearMap.inr F (Ainf F) (Af F) 1

/- English proof (translation)
Rewrite using `[idemS, map_sum]`. Conclude with `Finset.sum_eq_zero fun v _ => rfl`.
-/
theorem idemS_fst (T : Finset (Pl F)) : fstA F (idemS T) = 0 := by
  rw [idemS, map_sum]
  exact Finset.sum_eq_zero fun v _ => rfl

open Classical in
/- English proof (translation)
Establish `hne : ∀ v, v ≠ u → evFin F u (GlobalTheory.LatVac.liftV v (1 : Fv F v)) = 0` using `fun v hv => evalV_singleFin_ne (Ne.symm hv) _`. Rewrite using `[idemS, map_sum]`. Use `split_ifs with hu`. Rewrite using `[Finset.sum_eq_single u (fun v _ hv => hne v hv) (fun h => absurd hu h), GlobalTheory.LatVac.evFin_liftV]`. Conclude with `Finset.sum_eq_zero fun v hv => hne v (by rintro rfl; exact hu hv)`.
-/
theorem evFin_idemS (T : Finset (Pl F)) (u : Pl F) : evFin F u (idemS T) = if u ∈ T then 1 else 0 := by
  have hne : ∀ v, v ≠ u → evFin F u (GlobalTheory.LatVac.liftV v (1 : Fv F v)) = 0 := fun v hv =>
    evalV_singleFin_ne (Ne.symm hv) _
  rw [idemS, map_sum]
  split_ifs with hu
  · rw [Finset.sum_eq_single u (fun v _ hv => hne v hv) (fun h => absurd hu h), GlobalTheory.LatVac.evFin_liftV]
  · exact Finset.sum_eq_zero fun v hv => hne v (by rintro rfl; exact hu hv)

/- English proof (translation)
Use `Tendsto.prodMk_nhds (mx := fun T => (idemS T * a).1) (my := fun T => (idemS T * a).2) ?_ ?_` and prove the remaining obligations. Establish `: (fun T => (idemS T * a).1) = fun _ => (0 : Ainf F) * a.1`. Use function extensionality and compare the values at `T`. Express the relevant statement in the definitionally equal form `fstA F (idemS T) * a.1 = _`. Rewrite using `[idemS_fst]`.

Rewrite using `[this]`. Conclude with `tendsto_const_nhds`. Use `GlobalTheory.AdelicLimit.tendsto_finAdele _ _ 0 (fun T v hv => ?_) (fun T v hv => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `evFin F v (idemS T * a) = evalV F v (1 * a.2)`. Rewrite using `[map_mul, evFin_idemS, if_pos hv, one_mul, one_mul]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `evFin F v (idemS T * a) = 0`. Rewrite using `[map_mul, evFin_idemS, if_neg hv, zero_mul]`.
-/
theorem tendsto_idemS_mul (a : AF F) :
    Tendsto (fun T => idemS T * a) atTop (𝓝 (idemFin F * a)) := by
  refine Tendsto.prodMk_nhds (mx := fun T => (idemS T * a).1) (my := fun T => (idemS T * a).2) ?_ ?_
  · have : (fun T => (idemS T * a).1) = fun _ => (0 : Ainf F) * a.1 := by
      funext T
      change fstA F (idemS T) * a.1 = _
      rw [idemS_fst]
    rw [this]
    exact tendsto_const_nhds
  · refine GlobalTheory.AdelicLimit.tendsto_finAdele _ _ 0 (fun T v hv => ?_) (fun T v hv => ?_)
    · change evFin F v (idemS T * a) = evalV F v (1 * a.2)
      rw [map_mul, evFin_idemS, if_pos hv, one_mul, one_mul]
      rfl
    · change evFin F v (idemS T * a) = 0
      rw [map_mul, evFin_idemS, if_neg hv, zero_mul]

/- English proof (translation)
Use `haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simpa using tendsto_const_nhds`. Consider the case `tmul a e`. Establish `h : ∀ b : AF F, b • (a ⊗ₜ[F] e : AE F E) = (b * a) • ((1 : AF F) ⊗ₜ[F] e : AE F E)` using `fun b => by`.

Rewrite using `[TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one]`. Rewrite using `[h]`. Conclude with `((tendsto_idemS_mul a).smul_const _).congr fun T => (h _).symm`. Consider the case `add x y hx hy`. Simplify using `only [smul_add]`.

Conclude with `hx.add hy`.
-/
theorem tendsto_idemS_smul (x : AE F E) :
    Tendsto (fun T : Finset (Pl F) => idemS T • x) atTop (𝓝 (idemFin F • x)) := by
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  induction x using TensorProduct.induction_on with
  | zero => simpa using tendsto_const_nhds
  | tmul a e =>
    have h : ∀ b : AF F, b • (a ⊗ₜ[F] e : AE F E) = (b * a) • ((1 : AF F) ⊗ₜ[F] e : AE F E) := fun b => by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one]
    rw [h]
    exact ((tendsto_idemS_mul a).smul_const _).congr fun T => (h _).symm
  | add x y hx hy =>
    simp only [smul_add]
    exact hx.add hy

/- English proof (translation)
Set `i : Ainf F →ₗ[F] AF F` to `LinearMap.inl F (Ainf F) (Af F)`. Establish `key : ∀ x : AE F E, idemFin F • x + TensorProduct.map i (LinearMap.id : E →ₗ[F] E) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x) = x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a e`. Rewrite using `[Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul']`. Express the relevant statement in the definitionally equal form `_ + _ ⊗ₜ[F] e = _`. Rewrite using `[← TensorProduct.add_tmul]`. Use `congr 1`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `0 * a.1 + a.1 = a.1`. Rewrite using `[zero_mul, zero_add]`. Express the relevant statement in the definitionally equal form `1 * a.2 + 0 = a.2`. Rewrite using `[one_mul, add_zero]`.

Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add, smul_add, add_add_add_comm, hx, hy]`. Use `key x` as an intermediate fact. Rewrite `this` using `[hx, map_zero, add_zero]`. Then use the resulting hypothesis.
-/
theorem fin_smul_eq {x : AE F E} (hx : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x = 0) :
    idemFin F • x = x := by
  let i : Ainf F →ₗ[F] AF F := LinearMap.inl F (Ainf F) (Af F)
  have key : ∀ x : AE F E, idemFin F • x +
      TensorProduct.map i (LinearMap.id : E →ₗ[F] E) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul']
      change _ + _ ⊗ₜ[F] e = _
      rw [← TensorProduct.add_tmul]
      congr 1
      refine Prod.ext ?_ ?_
      · change 0 * a.1 + a.1 = a.1
        rw [zero_mul, zero_add]
      · change 1 * a.2 + 0 = a.2
        rw [one_mul, add_zero]
    | add x y hx hy =>
      rw [map_add, map_add, smul_add, add_add_add_comm, hx, hy]
  have := key x
  rwa [hx, map_zero, add_zero] at this

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mul' (g g' : UA σ J) : mat (g * g') = mat g * mat g' := rfl

/- English proof (translation)
Use `haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _`. Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Establish `h0 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) ((mat g - 1) i j) = 0`. Use `congrFun (congrFun (mem_finU.1 hg) i) j` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply]`.

Rewrite using `[Matrix.sub_apply, map_sub, this, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h1` using `(tendsto_idemS_smul ((mat g - 1) i j)).add_const ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j)`. Rewrite `h1` using `[fin_smul_eq h0, Matrix.sub_apply, sub_add_cancel]`. Use `h1.congr fun T => ?_` and prove the remaining obligations.

Use `congrFun (congrFun (cut_sub_one (algebraMap (AF F) (AE F E) (idemS T)) (mat g)) i) j` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, ← Algebra.smul_def]`. Rewrite using `[← this, sub_add_cancel]`.
-/
theorem tendsto_cut {g : UA σ J} (hg : g ∈ finU σ J) :
    Tendsto (fun T => cut (algebraMap (AF F) (AE F E) (idemS T)) (mat g)) atTop (𝓝 (mat g)) := by
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h0 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) ((mat g - 1) i j) = 0 := by
    have := congrFun (congrFun (mem_finU.1 hg) i) j
    rw [Matrix.map_apply] at this
    rw [Matrix.sub_apply, map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h1 := (tendsto_idemS_smul ((mat g - 1) i j)).add_const ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j)
  rw [fin_smul_eq h0, Matrix.sub_apply, sub_add_cancel] at h1
  refine h1.congr fun T => ?_
  have := congrFun (congrFun (cut_sub_one (algebraMap (AF F) (AE F E) (idemS T)) (mat g)) i) j
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, ← Algebra.smul_def] at this
  rw [← this, sub_add_cancel]

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact ⟨1, one_mem _, by simp [idemS, cut, mat], by simp [idemS, cut, mat]⟩`. Consider the case `insert v T hv ih`. Take `⟨k, hk, h1, h2⟩` from `ih`. Establish `h0 : (idem v : AE F E) * algebraMap (AF F) (AE F E) (idemS T) = 0`.

Rewrite using `[idem, ← map_mul, liftV_one_mul_eq, evFin_idemS, if_neg hv, map_zero, map_zero]`. Establish `hs : algebraMap (AF F) (AE F E) (idemS (insert v T)) = idem v + algebraMap (AF F) (AE F E) (idemS T)`. Rewrite using `[idemS, Finset.sum_insert hv, map_add]`. Both sides reduce to the same expression. Use `⟨atV v g * k, mul_mem (Subgroup.subset_closure (Set.mem_iUnion.2 ⟨v, ?_⟩)) hk, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Rewrite using `[mat_atV, cut_sub_one, smul_eq_alg, smul_smul, idem, ← map_mul, mul_comm, liftV_one_mul_eq, hw, map_zero, map_zero, zero_smul]`. Rewrite using `[mat_mul', h1, mat_atV, cut_add h0, hs]`. Rewrite using `[mul_inv_rev, mat_mul', h2, hs, add_comm, ← cut_add ((mul_comm _ _).trans h0)]`. Both sides reduce to the same expression.
-/
theorem exists_prod (W : Spc F E n) (g : UA σ W.J) (T : Finset (Pl F)) :
    ∃ k ∈ Subgroup.closure (⋃ v : Pl F, UAt σ W (evFin F v)),
      mat k = cut (algebraMap (AF F) (AE F E) (idemS T)) (mat g) ∧
      mat k⁻¹ = cut (algebraMap (AF F) (AE F E) (idemS T)) (mat g⁻¹) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp [idemS, cut, mat], by simp [idemS, cut, mat]⟩
  | insert v T hv ih =>
    obtain ⟨k, hk, h1, h2⟩ := ih
    have h0 : (idem v : AE F E) * algebraMap (AF F) (AE F E) (idemS T) = 0 := by
      rw [idem, ← map_mul, liftV_one_mul_eq, evFin_idemS, if_neg hv, map_zero, map_zero]
    have hs : algebraMap (AF F) (AE F E) (idemS (insert v T)) = idem v + algebraMap (AF F) (AE F E) (idemS T) := by
      rw [idemS, Finset.sum_insert hv, map_add]
      rfl
    refine ⟨atV v g * k, mul_mem (Subgroup.subset_closure (Set.mem_iUnion.2 ⟨v, ?_⟩)) hk, ?_, ?_⟩
    · intro w hw
      rw [mat_atV, cut_sub_one, smul_eq_alg, smul_smul, idem, ← map_mul, mul_comm, liftV_one_mul_eq, hw, map_zero,
        map_zero, zero_smul]
    · rw [mat_mul', h1, mat_atV, cut_add h0, hs]
    · rw [mul_inv_rev, mat_mul', h2, hs, add_comm, ← cut_add ((mul_comm _ _).trans h0)]
      rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d W _ h hh U hU`. Use `choose k hk h1 h2 using exists_prod W h`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Establish `ht : Tendsto k atTop (𝓝 h)`. Rewrite using `[tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]`.

Use `Tendsto.prodMk_nhds (mx := fun T => mat (k T)) (my := fun T => MulOpposite.op (mat (k T)⁻¹)) ?_ ?_` and prove the remaining obligations. Simplify using `only [h1]`. Conclude with `tendsto_cut hh`. Simplify using `only [h2]`. Conclude with `(MulOpposite.continuous_op.tendsto _).comp (tendsto_cut (inv_mem hh))`.

Establish `ht2 : Tendsto (fun T => (k T)⁻¹ * h) atTop (𝓝 (h⁻¹ * h))` using `ht.inv.mul_const h`. Rewrite `ht2` using `[inv_mul_cancel]`. Take `⟨T, hT⟩` from `(ht2.eventually (hU.mem_nhds U.one_mem)).exists`. Use `⟨k T, hk T, hT, mul_mem (inv_mem ?_) hh⟩` and prove the remaining obligations. Rewrite using `[mem_finU, h1]`.

Establish `h0 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (algebraMap (AF F) (AE F E) (idemS T)) = 0`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]`. Simplify using `[idemS_fst]`. Use extensionality with `i j`. Simplify using `only [cut, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, h0, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem exists_closure_mod_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d), IsCMExt F E σ → ∀ h ∈ finU σ W.J, ∀ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) → ∃ h' ∈ Subgroup.closure (⋃ v : Pl F, UAt σ W (evFin F v)), h'⁻¹ * h ∈ U ∧ h'⁻¹ * h ∈ finU σ W.J := by
  intro F E _ _ _ _ _ σ d W _ h hh U hU
  choose k hk h1 h2 using exists_prod W h
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have ht : Tendsto k atTop (𝓝 h) := by
    rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds (mx := fun T => mat (k T)) (my := fun T => MulOpposite.op (mat (k T)⁻¹)) ?_ ?_
    · simp only [h1]
      exact tendsto_cut hh
    · simp only [h2]
      exact (MulOpposite.continuous_op.tendsto _).comp (tendsto_cut (inv_mem hh))
  have ht2 : Tendsto (fun T => (k T)⁻¹ * h) atTop (𝓝 (h⁻¹ * h)) := ht.inv.mul_const h
  rw [inv_mul_cancel] at ht2
  obtain ⟨T, hT⟩ := (ht2.eventually (hU.mem_nhds U.one_mem)).exists
  refine ⟨k T, hk T, hT, mul_mem (inv_mem ?_) hh⟩
  rw [mem_finU, h1]
  have h0 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (algebraMap (AF F) (AE F E) (idemS T)) = 0 := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
    simp [idemS_fst]
  ext i j
  simp only [cut, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, h0,
    Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.FinPlaceDense

end
