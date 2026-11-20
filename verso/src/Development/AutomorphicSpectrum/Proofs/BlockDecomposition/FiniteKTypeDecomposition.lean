import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelRep

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

section Rep

variable {G : Type} [Group G] {K : Subgroup G} {V : Submodule ℂ (G → ℂ)}

def rt (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) : K →* Module.End ℂ V where
  toFun k :=
    { toFun := fun v => ⟨fun x => v.1 (x * (k : G)), hV v.1 v.2 k⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    simp
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext x
    simp [mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rt_apply (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K) (v : V) (x : G) :
    (rt hV k v).1 x = v.1 (x * (k : G)) := rfl

variable [FiniteDimensional ℂ V]

def mat (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K) :
    Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
  LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (rt hV k)

/- English proof (translation)
Simplify using `only [mat, map_mul]`. Conclude with `LinearMap.toMatrix_mul _ _ _`.
-/
theorem mat_mul (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (a b : K) :
    mat hV (a * b) = mat hV a * mat hV b := by
  simp only [mat, map_mul]
  exact LinearMap.toMatrix_mul _ _ _

/- English proof (translation)
Simplify using `only [mat, map_one]`. Conclude with `LinearMap.toMatrix_one _`.
-/
theorem mat_one (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) : mat hV 1 = 1 := by
  simp only [mat, map_one]
  exact LinearMap.toMatrix_one _

def rho (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) :
    K →* ((Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ V) → ℂ)) where
  toFun k := LinearMap.toContinuousLinearMap (Matrix.toLin' (mat hV k⁻¹)ᵀ)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro a
    simp [mat_one]
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    simp [mul_inv_rev, mat_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((mat hV k⁻¹)ᵀ *ᵥ a) i = _`. Simplify using `[Matrix.mulVec, dotProduct, mat, LinearMap.toMatrix_apply]`.
-/
theorem rho_apply (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K)
    (a : Fin (Module.finrank ℂ V) → ℂ) (i : Fin (Module.finrank ℂ V)) :
    rho hV k a i = ∑ j, (Module.finBasis ℂ V).repr (rt hV k⁻¹ (Module.finBasis ℂ V i)) j * a j := by
  change ((mat hV k⁻¹)ᵀ *ᵥ a) i = _
  simp [Matrix.mulVec, dotProduct, mat, LinearMap.toMatrix_apply]

/- English proof (translation)
Establish `h` using `congrArg (fun y : V => y.1 x) ((Module.finBasis ℂ V).sum_repr z)`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h`. Conclude with `h`.
-/
theorem sum_repr_apply (z : V) (x : G) :
    ∑ j, (Module.finBasis ℂ V).repr z j * (Module.finBasis ℂ V j).1 x = z.1 x := by
  have h := congrArg (fun y : V => y.1 x) ((Module.finBasis ℂ V).sum_repr z)
  simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  exact h

def w₀ (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] : Fin (Module.finrank ℂ V) → ℂ :=
  fun j => (Module.finBasis ℂ V j).1 1

/- English proof (translation)
Rewrite using `[rho_apply]`. Simplify using `only [w₀]`. Rewrite using `[sum_repr_apply, rt_apply]`. Simplify using the standard rewrite rules.
-/
theorem rho_w₀ (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V) (k : K)
    (i : Fin (Module.finrank ℂ V)) : rho hV k (w₀ V) i = (Module.finBasis ℂ V i).1 ((k : G)⁻¹) := by
  rw [rho_apply]
  simp only [w₀]
  rw [sum_repr_apply, rt_apply]
  simp

end Rep

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
  {V : Submodule ℂ (G → ℂ)} [FiniteDimensional ℂ V]

def evl (V : Submodule ℂ (G → ℂ)) (x : G) : Module.Dual ℂ V := (LinearMap.proj x).comp V.subtype

/- English proof (translation)
Establish `h : (Submodule.span ℂ (Set.range (evl V))).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Rewrite `hv` using `[Submodule.mem_dualCoannihilator]`. Establish `: v = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Conclude with `hv _ (Submodule.subset_span ⟨x, rfl⟩)`. Simplify using `[this]`. Establish `h2` using `Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range (evl V)))`.

Rewrite `h2` using `[h]`. Simplify using `using h2.symm`.
-/
theorem span_evl : Submodule.span ℂ (Set.range (evl V)) = ⊤ := by
  have h : (Submodule.span ℂ (Set.range (evl V))).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    have : v = 0 := by
      apply Subtype.ext
      funext x
      exact hv _ (Submodule.subset_span ⟨x, rfl⟩)
    simp [this]
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq
    (W := Submodule.span ℂ (Set.range (evl V)))
  rw [h] at h2
  simpa using h2.symm

/- English proof (translation)
Establish `hℓ : ℓ ∈ Submodule.span ℂ (Set.range (evl V))`. Rewrite using `[span_evl]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hℓ using Submodule.span_induction with`. Consider the case `mem ℓ h`.

Take `⟨x, rfl⟩` from `h`. Establish `h1 : Continuous fun k : K => x * (((k⁻¹ : K)) : G)` using `continuous_const.mul (continuous_subtype_val.comp continuous_inv)`. Conclude with `(hc v.1 v.2).comp h1`. Consider the case `zero => simpa using continuous_const`. Consider the case `add a b _ _ ha hb => exact ha.add hb`.

Consider the case `smul a ℓ _ h => exact continuous_const.mul h`.
-/
theorem cont_coef (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V)
    (hc : ∀ v ∈ V, Continuous v) (ℓ : Module.Dual ℂ V) (v : V) :
    Continuous fun k : K => ℓ (rt hV k⁻¹ v) := by
  have hℓ : ℓ ∈ Submodule.span ℂ (Set.range (evl V)) := by
    rw [span_evl]
    trivial
  induction hℓ using Submodule.span_induction with
  | mem ℓ h =>
    obtain ⟨x, rfl⟩ := h
    have h1 : Continuous fun k : K => x * (((k⁻¹ : K)) : G) :=
      continuous_const.mul (continuous_subtype_val.comp continuous_inv)
    exact (hc v.1 v.2).comp h1
  | zero => simpa using continuous_const
  | add a b _ _ ha hb => exact ha.add hb
  | smul a ℓ _ h => exact continuous_const.mul h

/- English proof (translation)
Rewrite using `[continuous_clm_apply]`. Introduce `a`. Use `continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [rho_apply]`. Use `continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `(cont_coef hV hc ((Module.finBasis ℂ V).coord j) _).mul continuous_const`.
-/
theorem rho_cont (hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V)
    (hc : ∀ v ∈ V, Continuous v) : Continuous (rho hV) := by
  rw [continuous_clm_apply]
  intro a
  refine continuous_pi fun i => ?_
  simp only [rho_apply]
  refine continuous_finset_sum _ fun j _ => ?_
  exact (cont_coef hV hc ((Module.finBasis ℂ V).coord j) _).mul continuous_const

end Cont

/- English proof (translation)
Establish `h1` using `h.mul 1 P.one_mem 1 P.one_mem`. Establish `h2` using `h.norm 1 P.one_mem`. Establish `h0 : c 1 ≠ 0`. Introduce `h0`. Simplify using `[h0] at h2`.

Rewrite `h1` using `[mul_one]`. Conclude with `mul_left_cancel₀ h0 (by rw [mul_one]; exact h1.symm)`.
-/
theorem ch_one {G : Type} [Group G] [TopologicalSpace G] {Γ P : Subgroup G} {c : G → ℂ}
    (h : IsCh Γ P c) : c 1 = 1 := by
  have h1 := h.mul 1 P.one_mem 1 P.one_mem
  have h2 := h.norm 1 P.one_mem
  have h0 : c 1 ≠ 0 := by
    intro h0
    simp [h0] at h2
  rw [mul_one] at h1
  exact mul_left_cancel₀ h0 (by rw [mul_one]; exact h1.symm)

/- English proof (translation)
Introduce `G _ _ _ Γ K P c η hch hηK _ f u hf hlaw hfd`. Take `⟨V, hVdef⟩ : ∃ V : Submodule ℂ (G → ℂ), V = Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G)))` from `⟨_, rfl⟩`. Rewrite `hfd` using `[← hVdef]`. Establish `hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V`. Introduce `v hv k`.

Rewrite `hv`, the goal using `[hVdef]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨k', rfl⟩` from `hv`. Conclude with `Submodule.subset_span ⟨k * k', by funext x; simp [mul_assoc]⟩`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => exact Submodule.add_mem _ ha hb`. Consider the case `smul a v _ hv => exact Submodule.smul_mem _ a hv`. Establish `hcont : ∀ v ∈ V, Continuous v`. Introduce `v hv`.

Rewrite `hv` using `[hVdef]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨k', rfl⟩` from `hv`. Conclude with `hf.comp (continuous_id.mul continuous_const)`.

Consider the case `zero => exact continuous_const`. Consider the case `add a b _ _ ha hb => exact ha.add hb`. Consider the case `smul a v _ hv => exact continuous_const.smul hv`. Establish `hl : ∀ v ∈ V, ∀ p ∈ P, ∀ x, v (p * x) = c p * Complex.exp (u * η p) * v x`. Introduce `v hv p hp x`.

Rewrite `hv` using `[hVdef]`. Proceed by induction on `hv using Submodule.span_induction generalizing x with`. Consider the case `mem v hv`. Take `⟨k', rfl⟩` from `hv`. Express the relevant statement in the definitionally equal form `f (p * x * (k' : G)) = c p * Complex.exp (u * η p) * f (x * (k' : G))`.

Rewrite using `[mul_assoc, hlaw p hp]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul a v _ hv => simp only [Pi.smul_apply, hv, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfV : f ∈ V`. Rewrite using `[hVdef]`. Conclude with `Submodule.subset_span ⟨1, by funext x; simp⟩`. Use `⟨Module.finrank ℂ V, rho hV, w₀ V, ∑ i, (Module.finBasis ℂ V).repr ⟨f, hfV⟩ i • (ContinuousLinearMap.proj i : (Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] ℂ), rho_cont hV hcont, ?_, ?_⟩` and prove the remaining obligations.

Introduce `r hr`. Use function extensionality and compare the values at `i`. Establish `hri : ((r : G))⁻¹ ∈ P` using `P.inv_mem hr`. Establish `hrK : ((r : G))⁻¹ ∈ K` using `K.inv_mem r.2`. Establish `h1` using `hl _ (Module.finBasis ℂ V i).2 _ hri 1`.

Establish `h2 : c r * c ((r : G))⁻¹ = 1`. Rewrite using `[← hch.mul _ hr _ hri, mul_inv_cancel, ch_one hch]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[rho_w₀]`. Rewrite `h1` using `[mul_one, hηK _ hri hrK]`.

Rewrite using `[h1]`. Simplify using `only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]`. Rewrite using `[← mul_assoc, h2, one_mul]`. Both sides reduce to the same expression. Introduce `k`.

Establish `h` using `sum_repr_apply (V := V) ⟨f, hfV⟩ (k : G)`. Simplify using `only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]`. Simplify using `only [rho_w₀]`. Simplify using `using h`.
-/
theorem exists_rep : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ K P : Subgroup G) (c : G → ℂ) (η : G → ℝ), IsCh Γ P c → (∀ r ∈ P, r ∈ K → η r = 0) → (∀ p ∈ P, ∀ q ∈ P, η (p * q) = η p + η q) → ∀ (f : G → ℂ) (u : ℂ), Continuous f → (∀ p ∈ P, ∀ x, f (p * x) = c p * Complex.exp (u * η p) * f x) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G)))) → ∃ (d : ℕ) (ρ : K →* ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))) (w : Fin d → ℂ) (e : (Fin d → ℂ) →L[ℂ] ℂ), Continuous ρ ∧ w ∈ secSp K P c ρ ∧ ∀ k : K, e (ρ k⁻¹ w) = f k := by
  intro G _ _ _ Γ K P c η hch hηK _ f u hf hlaw hfd
  obtain ⟨V, hVdef⟩ : ∃ V : Submodule ℂ (G → ℂ),
      V = Submodule.span ℂ (Set.range fun k : K => fun x => f (x * (k : G))) := ⟨_, rfl⟩
  rw [← hVdef] at hfd
  have hV : ∀ v ∈ V, ∀ k : K, (fun x => v (x * (k : G))) ∈ V := by
    intro v hv k
    rw [hVdef] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      exact Submodule.subset_span ⟨k * k', by funext x; simp [mul_assoc]⟩
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul a v _ hv => exact Submodule.smul_mem _ a hv
  have hcont : ∀ v ∈ V, Continuous v := by
    intro v hv
    rw [hVdef] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      exact hf.comp (continuous_id.mul continuous_const)
    | zero => exact continuous_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul a v _ hv => exact continuous_const.smul hv
  have hl : ∀ v ∈ V, ∀ p ∈ P, ∀ x, v (p * x) = c p * Complex.exp (u * η p) * v x := by
    intro v hv p hp x
    rw [hVdef] at hv
    induction hv using Submodule.span_induction generalizing x with
    | mem v hv =>
      obtain ⟨k', rfl⟩ := hv
      change f (p * x * (k' : G)) = c p * Complex.exp (u * η p) * f (x * (k' : G))
      rw [mul_assoc, hlaw p hp]
    | zero => simp
    | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]; ring
    | smul a v _ hv => simp only [Pi.smul_apply, hv, smul_eq_mul]; ring
  have hfV : f ∈ V := by
    rw [hVdef]
    exact Submodule.subset_span ⟨1, by funext x; simp⟩
  refine ⟨Module.finrank ℂ V, rho hV, w₀ V,
    ∑ i, (Module.finBasis ℂ V).repr ⟨f, hfV⟩ i •
      (ContinuousLinearMap.proj i : (Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] ℂ),
    rho_cont hV hcont, ?_, ?_⟩
  · intro r hr
    funext i
    have hri : ((r : G))⁻¹ ∈ P := P.inv_mem hr
    have hrK : ((r : G))⁻¹ ∈ K := K.inv_mem r.2
    have h1 := hl _ (Module.finBasis ℂ V i).2 _ hri 1
    have h2 : c r * c ((r : G))⁻¹ = 1 := by
      rw [← hch.mul _ hr _ hri, mul_inv_cancel, ch_one hch]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [rho_w₀]
    rw [mul_one, hηK _ hri hrK] at h1
    rw [h1]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [← mul_assoc, h2, one_mul]
    rfl
  · intro k
    have h := sum_repr_apply (V := V) ⟨f, hfV⟩ (k : G)
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    simp only [rho_w₀]
    simpa using h

end GlobalTheory.CompanionTheory.SiegelRep
