import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll

noncomputable section

namespace PI.VolStabSW

namespace SdDualW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Use `⟨((π⁻¹ : F) : Fv F v), ?_⟩` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.notMem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ]`. Simplify using `only [← WithZero.exp_neg, neg_neg]`. Rewrite using `[← WithZero.exp_zero]`.

Conclude with `WithZero.exp_lt_exp.2 one_pos`.
-/
theorem exists_notMem_int : ∃ c : Fv F v, c ∉ v.adicCompletionIntegers F := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨((π⁻¹ : F) : Fv F v), ?_⟩
  rw [HeightOneSpectrum.notMem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ]
  simp only [← WithZero.exp_neg, neg_neg]
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.2 one_pos

variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def latSub (a M : ℕ) : AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E) where
  carrier := latV b v
  zero_mem' := by
    simp only [latV, Set.mem_ofPred_eq]
    intro p i k
    simp
  add_mem' := by
    intro X Y hX hY
    simp only [latV, Set.mem_ofPred_eq] at hX hY ⊢
    intro p i k
    simpa [Pi.add_apply, map_add] using add_mem (hX p i k) (hY p i k)
  neg_mem' := by
    intro X hX
    simp only [latV, Set.mem_ofPred_eq] at hX ⊢
    intro p i k
    simpa [map_neg] using neg_mem (hX p i k)

/- English proof (translation)
Simplify using `[crd]`.
-/
theorem crd_smul (s : Fv F v) (z : Fv F v ⊗[F] E) (k : Fin d) :
    crd b (Fv F v) (s • z) k = s * crd b (Fv F v) z k := by
  simp [crd]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`. Use `congr 1`. Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem sigR_smul (σ : E →ₐ[F] E) (s : Fv F v) (z : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (s • z) = s • sigR (Fv F v) σ z := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Simplify using `only [BR, hR, Formalism.UG.hform, Pi.smul_apply, sigR_smul, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul, Finset.mul_sum]`.
-/
theorem BR_smul_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : Fv F v)
    (X Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J (s • X) Y = s * BR (Fv F v) σ J X Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.smul_apply, sigR_smul, smul_mul_assoc, ← Finset.smul_sum,
    map_smul, smul_eq_mul, Finset.mul_sum]

/- English proof (translation)
Simplify using `only [BR, hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]`.
-/
theorem BR_add_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y Y' : Fin n → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X (Y + Y') = BR (Fv F v) σ J X Y + BR (Fv F v) σ J X Y' := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]

/- English proof (translation)
Simplify using `only [BR, hR, Formalism.UG.hform, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul, Finset.mul_sum]`.
-/
theorem BR_smul_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : Fv F v)
    (X Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X (s • Y) = s * BR (Fv F v) σ J X Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul,
    smul_eq_mul, Finset.mul_sum]

section Nondeg

variable [FiniteDimensional F E]

/- English proof (translation)
Rewrite using `[Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]`. Use `congr 1`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul k y => simp [Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem trace_one_tmul (e : E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((1 : Fv F v) ⊗ₜ[F] e) =
      algebraMap F (Fv F v) (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k y => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

include b in

/- English proof (translation)
Set `B` to `Algebra.TensorProduct.basis (Fv F v) b`. Establish `hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] b k` using `fun k => Algebra.TensorProduct.basis_apply _ _`. Set `c : Fin d → Fv F v` to `fun k => B.repr z k`. Set `G : Matrix (Fin d) (Fin d) (Fv F v)` to `(Algebra.traceMatrix F b).map (algebraMap F (Fv F v))`. Establish `hc : G.mulVec c = 0`.

Use function extensionality and compare the values at `l`. Establish `hz` using `h (B l)`. Rewrite `hz` using `[← B.sum_repr z, Finset.mul_sum, map_sum]`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`. Rewrite using `[← hz]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, map_smul, hB, hB, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul, smul_eq_mul, mul_comm]`. Simplify using `[G, Algebra.traceMatrix_apply, Algebra.traceForm_apply, c]`. Establish `hdet : G.det ≠ 0`. Rewrite using `[show G.det = algebraMap F (Fv F v) (Algebra.traceMatrix F b).det from (RingHom.map_det _ _).symm]`.

Conclude with `(map_ne_zero _).2 (Algebra.discr_not_zero_of_basis F b)`. Establish `hc0 : c = 0` using `Matrix.eq_zero_of_mulVec_eq_zero hdet hc`. Rewrite using `[← B.sum_repr z]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Establish `: B.repr z k = 0` using `congrFun hc0 k`.

Rewrite using `[this, zero_smul]`.
-/
theorem trace_nondeg [Algebra.IsSeparable F E] (z : Fv F v ⊗[F] E)
    (h : ∀ w, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w * z) = 0) : z = 0 := by
  classical
  let B := Algebra.TensorProduct.basis (Fv F v) b
  have hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  let c : Fin d → Fv F v := fun k => B.repr z k
  let G : Matrix (Fin d) (Fin d) (Fv F v) :=
    (Algebra.traceMatrix F b).map (algebraMap F (Fv F v))
  have hc : G.mulVec c = 0 := by
    funext l
    have hz := h (B l)
    rw [← B.sum_repr z, Finset.mul_sum, map_sum] at hz
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← hz]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, map_smul, hB, hB, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      trace_one_tmul, smul_eq_mul, mul_comm]
    simp [G, Algebra.traceMatrix_apply, Algebra.traceForm_apply, c]
  have hdet : G.det ≠ 0 := by
    rw [show G.det = algebraMap F (Fv F v) (Algebra.traceMatrix F b).det from
      (RingHom.map_det _ _).symm]
    exact (map_ne_zero _).2 (Algebra.discr_not_zero_of_basis F b)
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hc
  rw [← B.sum_repr z]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : B.repr z k = 0 := congrFun hc0 k
  rw [this, zero_smul]

end Nondeg

section Dual

variable [FiniteDimensional F E] (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)

def eT (q : Fin a × Fin M × Fin d) : Fin a → Fin M → Fv F v ⊗[F] E :=
  Pi.single q.1 (Pi.single q.2.1 ((1 : Fv F v) ⊗ₜ[F] b q.2.2))

/- English proof (translation)
Use `show ∀ p i l, (Algebra.TensorProduct.basis (Fv F v) b).repr (eT v b q p i) l ∈ v.adicCompletionIntegers F`. Introduce `p i l`. Establish `hB : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b) k = (1 : Fv F v) ⊗ₜ[F] b k` using `fun k => Algebra.TensorProduct.basis_apply _ _`. Distinguish the cases in `h1 : p = q.1`. Substitute `h1` using the available equality.

Distinguish the cases in `h2 : i = q.2.1`. Substitute `h2` using the available equality. Simplify using `only [eT, Pi.single_eq_same]`. Rewrite using `[← hB, Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Simplify using `[eT, h2]`. Simplify using `[eT, h1]`.
-/
theorem eT_mem (q : Fin a × Fin M × Fin d) : eT v b q ∈ latSub v b a M := by
  show ∀ p i l, (Algebra.TensorProduct.basis (Fv F v) b).repr (eT v b q p i) l ∈
    v.adicCompletionIntegers F
  intro p i l
  have hB : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b) k = (1 : Fv F v) ⊗ₜ[F] b k :=
    fun k => Algebra.TensorProduct.basis_apply _ _
  by_cases h1 : p = q.1
  · subst h1
    by_cases h2 : i = q.2.1
    · subst h2
      simp only [eT, Pi.single_eq_same]
      rw [← hB, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · simp [eT, h2]
  · simp [eT, h1]

/- English proof (translation)
Use function extensionality and compare the values at `p i`. Rewrite using `[Finset.sum_apply, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single p]`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single i]`. Simplify using `only [eT, Pi.smul_apply, Pi.single_eq_same]`. Conclude with `eq_sum_crd b (Fv F v) (X p i)`.

Introduce `j _ hj`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Simplify using `[eT, hj]`. Simplify using the standard rewrite rules. Introduce `x _ hx`.

Use `Finset.sum_eq_zero fun y _ => ?_` and prove the remaining obligations. Simplify using `[eT, Ne.symm hx]`. Simplify using the standard rewrite rules.
-/
theorem sum_eT (X : Fin a → Fin M → Fv F v ⊗[F] E) :
    X = ∑ q : Fin a × Fin M × Fin d, crd b (Fv F v) (X q.1 q.2.1) q.2.2 • eT v b q := by
  funext p i
  rw [Finset.sum_apply, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single p]
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp only [eT, Pi.smul_apply, Pi.single_eq_same]
      exact eq_sum_crd b (Fv F v) (X p i)
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [eT, hj]
    · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [eT, Ne.symm hx]
  · simp

def brL (Y : Fin a → Fin M → Fv F v ⊗[F] E) : (Fin a → Fin M → Fv F v ⊗[F] E) →ₗ[Fv F v] Fv F v
    where
  toFun X := BR (Fv F v) σ J X Y
  map_add' X X' := by rw [add_comm X X', BR_add, add_comm]
  map_smul' s X := by rw [BR_smul_left]; rfl

/- English proof (translation)
Establish `h` using `congrArg (brL v σ J Y) (sum_eT v b X)`. Simplify using `only [map_sum, map_smul, smul_eq_mul] at h`. Conclude with `h`.
-/
theorem BR_expand (X Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X Y =
      ∑ q : Fin a × Fin M × Fin d, crd b (Fv F v) (X q.1 q.2.1) q.2.2 * BR (Fv F v) σ J (eT v b q) Y := by
  have h := congrArg (brL v σ J Y) (sum_eT v b X)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  exact h

def phiL : (Fin a → Fin M → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin a × Fin M × Fin d → Fv F v) where
  toFun Y q := BR (Fv F v) σ J (eT v b q) Y
  map_add' Y Y' := by funext q; simp [BR_add_right]
  map_smul' s Y := by funext q; simp [BR_smul_right]

include b in
/- English proof (translation)
Establish `hker : LinearMap.ker (phiL (a` using `a) v b σ J) = ⊥ := by`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `Y hY`. Apply `hN Y` to reduce the goal to its premises. Introduce `X`.

Rewrite using `[BR_expand v b σ J X Y]`. Use `Finset.sum_eq_zero fun q _ => ?_` and prove the remaining obligations. Establish `: BR (Fv F v) σ J (eT v b q) Y = 0` using `congrFun hY q`. Rewrite using `[this, mul_zero]`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (phiL (a := a) v b σ J) hker`.

Establish `hgc : Continuous g` using `IsModuleTopology.continuous_of_linearMap g`. Set `box : Set (Fin a × Fin M × Fin d → Fv F v)` to `Set.pi Set.univ fun _ => (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))`. Establish `hbox : IsCompact box` using `isCompact_univ_pi fun _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image (continuous_const.mul continuous_id)`. Use `⟨g '' box, hbox.image hgc, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Use `⟨phiL (a := a) v b σ J y, ?_, ?_⟩` and prove the remaining obligations. Introduce `q _`. Conclude with `hy _ (eT_mem v b q)`. Conclude with `LinearMap.congr_fun hg y`.
-/
theorem bound_alt
    (hN : ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, (∀ X, BR (Fv F v) σ J X Y = 0) → Y = 0)
    (c : Fv F v) : ∃ K, IsCompact K ∧
      {y | ∀ x ∈ latSub v b a M, BR (Fv F v) σ J x y ∈
        (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))} ⊆ K := by
  classical
  have hker : LinearMap.ker (phiL (a := a) v b σ J) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro Y hY
    apply hN Y
    intro X
    rw [BR_expand v b σ J X Y]
    refine Finset.sum_eq_zero fun q _ => ?_
    have : BR (Fv F v) σ J (eT v b q) Y = 0 := congrFun hY q
    rw [this, mul_zero]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (phiL (a := a) v b σ J) hker
  have hgc : Continuous g := IsModuleTopology.continuous_of_linearMap g
  let box : Set (Fin a × Fin M × Fin d → Fv F v) :=
    Set.pi Set.univ fun _ => (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))
  have hbox : IsCompact box := isCompact_univ_pi fun _ =>
    (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image (continuous_const.mul continuous_id)
  refine ⟨g '' box, hbox.image hgc, ?_⟩
  intro y hy
  refine ⟨phiL (a := a) v b σ J y, ?_, ?_⟩
  · intro q _
    exact hy _ (eT_mem v b q)
  · exact LinearMap.congr_fun hg y

include b in
/- English proof (translation)
Establish `hker : LinearMap.ker (phiL (a` using `a) v b σ J) = ⊥ := by`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `Y hY`. Apply `hN Y` to reduce the goal to its premises. Introduce `X`.

Rewrite using `[BR_expand v b σ J X Y]`. Use `Finset.sum_eq_zero fun q _ => ?_` and prove the remaining obligations. Establish `: BR (Fv F v) σ J (eT v b q) Y = 0` using `congrFun hY q`. Rewrite using `[this, mul_zero]`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (phiL (a := a) v b σ J) hker`.

Establish `hgc : Continuous g` using `IsModuleTopology.continuous_of_linearMap g`. Use `⟨latSub v b a M, isCompact_latV b v a M, (isClopen_latV b v a M).isOpen, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs x hx`. Use `⟨s • x, ?_, fun y => BR_smul_left v σ J s x y⟩` and prove the remaining obligations. Use `show ∀ p i l, (Algebra.TensorProduct.basis (Fv F v) b).repr ((s • x) p i) l ∈ v.adicCompletionIntegers F`.

Introduce `p i l`. Use `crd_smul v b s (x p i) l` as an intermediate fact. Simplify using `only [crd] at this`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, this]`. Conclude with `mul_mem hs (hx p i l)`.

Introduce `c`. Set `box : Set (Fin a × Fin M × Fin d → Fv F v)` to `Set.pi Set.univ fun _ => (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))`. Establish `hbox : IsCompact box` using `isCompact_univ_pi fun _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image (continuous_const.mul continuous_id)`. Use `⟨g '' box, hbox.image hgc, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Use `⟨phiL (a := a) v b σ J y, ?_, ?_⟩` and prove the remaining obligations. Introduce `q _`. Conclude with `hy _ (eT_mem v b q)`. Conclude with `LinearMap.congr_fun hg y`.
-/
theorem dualAt_alt
    (hN : ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, (∀ X, BR (Fv F v) σ J X Y = 0) → Y = 0) :
    DualAt v (BR (Fv F v) σ J (n := a)) := by
  classical
  have hker : LinearMap.ker (phiL (a := a) v b σ J) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro Y hY
    apply hN Y
    intro X
    rw [BR_expand v b σ J X Y]
    refine Finset.sum_eq_zero fun q _ => ?_
    have : BR (Fv F v) σ J (eT v b q) Y = 0 := congrFun hY q
    rw [this, mul_zero]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (phiL (a := a) v b σ J) hker
  have hgc : Continuous g := IsModuleTopology.continuous_of_linearMap g
  refine ⟨latSub v b a M, isCompact_latV b v a M, (isClopen_latV b v a M).isOpen, ?_, ?_⟩
  · intro s hs x hx
    refine ⟨s • x, ?_, fun y => BR_smul_left v σ J s x y⟩
    show ∀ p i l, (Algebra.TensorProduct.basis (Fv F v) b).repr ((s • x) p i) l ∈
      v.adicCompletionIntegers F
    intro p i l
    have := crd_smul v b s (x p i) l
    simp only [crd] at this
    rw [Pi.smul_apply, Pi.smul_apply, this]
    exact mul_mem hs (hx p i l)
  · intro c
    let box : Set (Fin a × Fin M × Fin d → Fv F v) :=
      Set.pi Set.univ fun _ => (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))
    have hbox : IsCompact box := isCompact_univ_pi fun _ =>
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image (continuous_const.mul continuous_id)
    refine ⟨g '' box, hbox.image hgc, ?_⟩
    intro y hy
    refine ⟨phiL (a := a) v b σ J y, ?_, ?_⟩
    · intro q _
      exact hy _ (eT_mem v b q)
    · exact LinearMap.congr_fun hg y

end Dual

section NondegBR

variable [FiniteDimensional F E]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Establish `hz : ∀ i, (JR (Fv F v) J).mulVec (Y p) i = 0`. Introduce `i`. Apply `trace_nondeg v (Module.finBasis F E)` to reduce the goal to its premises. Introduce `w`.

Use `h (Pi.single p (Pi.single i (sigR (Fv F v) σ w)))` as an intermediate fact. Simplify using `only [BR, hR, Formalism.UG.hform] at this`. Rewrite `this` using `[Finset.sum_eq_single p (fun p' _ hp' => by simp [Pi.single_apply, hp']) (by simp)]`. Rewrite `this` using `[Finset.sum_eq_single i (fun i' _ hi' => by simp [Pi.single_apply, hi']) (by simp)]`. Simplify using `only [Pi.single_eq_same, sigR_invol (Fv F v) σ hσ] at this`.

Simplify `this` using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Establish `hdet : IsUnit ((1 : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * JR (Fv F v) J).det`. Rewrite using `[one_mul]`. Establish `e` using `RingHom.map_det (inclR (F := F) (E := E) (Fv F v)) J`. Rewrite `e` using `[RingHom.mapMatrix_apply]`.

Use `show IsUnit (J.map (inclR (Fv F v))).det`. Rewrite using `[← e]`. Conclude with `(isUnit_iff_ne_zero.2 hJ).map _`. Conclude with `TensAllW.inj_of_isUnit _ 1 hdet _ (funext hz)`.
-/
theorem nondeg_BR [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) (Y : Fin a → Fin M → Fv F v ⊗[F] E)
    (h : ∀ X, BR (Fv F v) σ J X Y = 0) : Y = 0 := by
  classical
  funext p
  have hz : ∀ i, (JR (Fv F v) J).mulVec (Y p) i = 0 := by
    intro i
    apply trace_nondeg v (Module.finBasis F E)
    intro w
    have := h (Pi.single p (Pi.single i (sigR (Fv F v) σ w)))
    simp only [BR, hR, Formalism.UG.hform] at this
    rw [Finset.sum_eq_single p (fun p' _ hp' => by simp [Pi.single_apply, hp']) (by simp)] at this
    rw [Finset.sum_eq_single i (fun i' _ hi' => by simp [Pi.single_apply, hi']) (by simp)] at this
    simp only [Pi.single_eq_same, sigR_invol (Fv F v) σ hσ] at this
    simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using this
  have hdet : IsUnit ((1 : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * JR (Fv F v) J).det := by
    rw [one_mul]
    have e := RingHom.map_det (inclR (F := F) (E := E) (Fv F v)) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR (Fv F v))).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  exact TensAllW.inj_of_isUnit _ 1 hdet _ (funext hz)

end NondegBR

section Herm

variable [FiniteDimensional F E]

def latA : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := {z | ∀ k, crd b (Fv F v) z k ∈ v.adicCompletionIntegers F}
  zero_mem' := by intro k; simp [crd]
  add_mem' := by
    intro x y hx hy k
    simpa [crd, map_add] using add_mem (hx k) (hy k)
  neg_mem' := by
    intro x hx k
    simpa [crd, map_neg] using neg_mem (hx k)

/- English proof (translation)
Establish `e : (latA v b : Set (Fv F v ⊗[F] E)) = ⋂ k, (fun z => crd b (Fv F v) z k) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))`. Use extensionality with `z`. Simplify using `[latA]`. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun k => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).preimage (continuous_crd b (Fv F v) k)`.
-/
theorem isOpen_latA : IsOpen (latA v b : Set (Fv F v ⊗[F] E)) := by
  have e : (latA v b : Set (Fv F v ⊗[F] E)) = ⋂ k, (fun z => crd b (Fv F v) z k) ⁻¹'
      (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext z; simp [latA]
  rw [e]
  exact isOpen_iInter_of_finite fun k =>
    (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).preimage (continuous_crd b (Fv F v) k)

/- English proof (translation)
Establish `e : (latA v b : Set (Fv F v ⊗[F] E)) = (fun Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E => Y 0 0) '' latV (M` using `1) (n := 1) b v := by`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Conclude with `⟨fun _ _ => z, fun p i k => hz k, rfl⟩`.

Introduce and unpack `⟨Y, hY, rfl⟩ k`. Conclude with `hY 0 0 k`. Rewrite using `[e]`. Conclude with `(isCompact_latV b v 1 1).image ((continuous_apply 0).comp (continuous_apply 0))`.
-/
theorem isCompact_latA : IsCompact (latA v b : Set (Fv F v ⊗[F] E)) := by
  have e : (latA v b : Set (Fv F v ⊗[F] E)) =
      (fun Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E => Y 0 0) '' latV (M := 1) (n := 1) b v := by
    ext z
    constructor
    · intro hz
      exact ⟨fun _ _ => z, fun p i k => hz k, rfl⟩
    · rintro ⟨Y, hY, rfl⟩ k
      exact hY 0 0 k
  rw [e]
  exact (isCompact_latV b v 1 1).image ((continuous_apply 0).comp (continuous_apply 0))

def latS (σ : E →ₐ[F] E) : AddSubgroup (Fv F v ⊗[F] E) :=
  latA v b ⊔ (latA v b).map (sigR (Fv F v) σ).toAddMonoidHom

/- English proof (translation)
Simplify using `only [latS, AddSubgroup.mem_sup, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩`. Conclude with `⟨x, hx, y, hy, rfl⟩`. Introduce and unpack `⟨x, hx, y, hy, rfl⟩`.

Conclude with `⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩`.
-/
theorem mem_latS (σ : E →ₐ[F] E) (z : Fv F v ⊗[F] E) :
    z ∈ latS v b σ ↔ ∃ x ∈ latA v b, ∃ y ∈ latA v b, x + sigR (Fv F v) σ y = z := by
  simp only [latS, AddSubgroup.mem_sup, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩

/- English proof (translation)
Establish `e : (latS v b σ : Set (Fv F v ⊗[F] E)) = (fun p : (Fv F v ⊗[F] E) × (Fv F v ⊗[F] E) => p.1 + sigR (Fv F v) σ p.2) '' ((latA v b : Set (Fv F v ⊗[F] E)) ×ˢ (latA v b : Set (Fv F v ⊗[F] E)))`. Use extensionality with `z`. Rewrite using `[SetLike.mem_coe, mem_latS]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, y, hy, rfl⟩`.

Conclude with `⟨(x, y), ⟨hx, hy⟩, rfl⟩`. Introduce and unpack `⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩`. Conclude with `⟨x, hx, y, hy, rfl⟩`. Rewrite using `[e]`. Use `locallyCompact_Fv F v` as an intermediate fact.

Conclude with `((isCompact_latA v b).prod (isCompact_latA v b)).image (continuous_fst.add ((continuous_sigR (Fv F v) σ).comp continuous_snd))`.
-/
theorem isCompact_latS (σ : E →ₐ[F] E) : IsCompact (latS v b σ : Set (Fv F v ⊗[F] E)) := by
  have e : (latS v b σ : Set (Fv F v ⊗[F] E)) =
      (fun p : (Fv F v ⊗[F] E) × (Fv F v ⊗[F] E) => p.1 + sigR (Fv F v) σ p.2) ''
        ((latA v b : Set (Fv F v ⊗[F] E)) ×ˢ (latA v b : Set (Fv F v ⊗[F] E))) := by
    ext z
    rw [SetLike.mem_coe, mem_latS]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
  rw [e]
  have := locallyCompact_Fv F v
  exact ((isCompact_latA v b).prod (isCompact_latA v b)).image
    (continuous_fst.add ((continuous_sigR (Fv F v) σ).comp continuous_snd))

/- English proof (translation)
The claim follows from `AddSubgroup.isOpen_mono le_sup_left (isOpen_latA v b)`.
-/
theorem isOpen_latS (σ : E →ₐ[F] E) : IsOpen (latS v b σ : Set (Fv F v ⊗[F] E)) :=
  AddSubgroup.isOpen_mono le_sup_left (isOpen_latA v b)

/- English proof (translation)
Introduce `k`. Rewrite using `[crd_smul]`. Conclude with `mul_mem hs (hx k)`.
-/
theorem smul_mem_latA {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ latA v b) : s • x ∈ latA v b := by
  intro k
  rw [crd_smul]
  exact mul_mem hs (hx k)

/- English proof (translation)
Rewrite `hz`, the goal using `[mem_latS]`. Take `⟨x, hx, y, hy, rfl⟩` from `hz`. Conclude with `⟨s • x, smul_mem_latA v b hs hx, s • y, smul_mem_latA v b hs hy, by`. Rewrite using `[smul_add, sigR_smul]⟩`.
-/
theorem smul_mem_latS (σ : E →ₐ[F] E) {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {z : Fv F v ⊗[F] E} (hz : z ∈ latS v b σ) : s • z ∈ latS v b σ := by
  rw [mem_latS] at hz ⊢
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  exact ⟨s • x, smul_mem_latA v b hs hx, s • y, smul_mem_latA v b hs hy, by
    rw [smul_add, sigR_smul]⟩

/- English proof (translation)
Set `B` to `Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)`. Establish `hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] (Module.finBasis F E) k` using `fun k => Algebra.TensorProduct.basis_apply _ _`. Set `eσ : E ≃ₐ[F] E` to `AlgEquiv.ofBijective σ ⟨σ.toRingHom.injective, fun x => ⟨σ x, hσ x⟩⟩`. Establish `htr : ∀ e : E, Algebra.trace F E (σ e) = Algebra.trace F E e` using `fun e => Algebra.trace_eq_of_algEquiv eσ e`. Use `conv_lhs => rw [← B.sum_repr w]`.

Use `conv_rhs => rw [← B.sum_repr w]`. Rewrite using `[map_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[sigR_smul, map_smul, map_smul, hB]`. Establish `: sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] (Module.finBasis F E) k) = (1 : Fv F v) ⊗ₜ[F] σ ((Module.finBasis F E) k)` using `by simp [sigR]`.

Rewrite using `[this, trace_one_tmul, trace_one_tmul, htr]`.
-/
theorem trace_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ w) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  let B := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
  have hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] (Module.finBasis F E) k := fun k =>
    Algebra.TensorProduct.basis_apply _ _
  let eσ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ
    ⟨σ.toRingHom.injective, fun x => ⟨σ x, hσ x⟩⟩
  have htr : ∀ e : E, Algebra.trace F E (σ e) = Algebra.trace F E e := fun e =>
    Algebra.trace_eq_of_algEquiv eσ e
  conv_lhs => rw [← B.sum_repr w]
  conv_rhs => rw [← B.sum_repr w]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sigR_smul, map_smul, map_smul, hB]
  have : sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] (Module.finBasis F E) k) =
      (1 : Fv F v) ⊗ₜ[F] σ ((Module.finBasis F E) k) := by simp [sigR]
  rw [this, trace_one_tmul, trace_one_tmul, htr]

def latH (σ : E →ₐ[F] E) (a : ℕ) : AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ p q, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q ∈ latS v b σ}
  zero_mem' := by intro p q; simp
  add_mem' := by
    intro S T hS hT p q
    simpa using add_mem (hS p q) (hT p q)
  neg_mem' := by
    intro S hS p q
    simpa using neg_mem (hS p q)

/- English proof (translation)
Use extensionality with `S`. Conclude with `⟨fun h p _ q _ => h p q, fun h p q => h p (Set.mem_univ _) q (Set.mem_univ _)⟩`.
-/
theorem latH_eq (σ : E →ₐ[F] E) (a : ℕ) :
    (latH v b σ a : Set (HermR (Fv F v) σ a)) = Subtype.val ⁻¹'
      ((Set.univ.pi fun _ => Set.univ.pi fun _ => (latS v b σ : Set (Fv F v ⊗[F] E))) :
        Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) := by
  ext S
  exact ⟨fun h p _ q _ => h p q, fun h p q => h p (Set.mem_univ _) q (Set.mem_univ _)⟩

def iota (σ : E →ₐ[F] E) {a : ℕ} (X : Fin a → Fin a → Fv F v ⊗[F] E) :
    Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
  fun p q => sigR (Fv F v) σ (X p q) + X q p

/- English proof (translation)
Introduce `p q`. Simplify using `only [iota, map_add, sigR_invol (Fv F v) σ hσ]`. Conclude with `add_comm _ _`.
-/
theorem iota_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {a : ℕ}
    (X : Fin a → Fin a → Fv F v ⊗[F] E) : iota v σ X ∈ HermR (Fv F v) σ a := by
  intro p q
  simp only [iota, map_add, sigR_invol (Fv F v) σ hσ]
  exact add_comm _ _

/- English proof (translation)
Use `set Tm := (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) with hTm`. Establish `hT : ∀ p q, Tm q p = sigR (Fv F v) σ (Tm p q)` using `fun p q => (T.2 q p).symm`. Establish `h2 : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ p, ∑ q, X q p * Tm q p) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ p, ∑ q, sigR (Fv F v) σ (X p q) * Tm q p)`. Simplify using `only [map_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hT q p, ← trace_sigR v σ hσ, map_mul, sigR_invol (Fv F v) σ hσ]`. Establish `hBR : BR (Fv F v) σ (1 : Matrix (Fin a) (Fin a) E) X (fun p i => Tm i p) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ p, ∑ q, sigR (Fv F v) σ (X p q) * Tm q p)`. Simplify using `only [BR, hR, Formalism.UG.hform, JR, Matrix.map_apply, Matrix.one_apply, apply_ite, map_one, map_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum]`. Rewrite using `[hBR]`.

Simplify using `only [pairHerm, iota, add_mul, Finset.sum_add_distrib, map_add]`. Simplify using `only [← hTm]`. Rewrite using `[h2]`. Establish `h12 : algebraMap F (Fv F v) (1 / 2) * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul]`.

Evaluate the numerical expressions. Take the linear combination `(Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ p, ∑ q, sigR (Fv F v) σ (X p q) * Tm q p)) * h12`.
-/
theorem pairHerm_iota (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {a : ℕ}
    (X : Fin a → Fin a → Fv F v ⊗[F] E) (T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a ⟨iota v σ X, iota_mem v σ hσ X⟩ T =
      BR (Fv F v) σ (1 : Matrix (Fin a) (Fin a) E) X
        (fun p i => (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i p) := by
  set Tm := (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) with hTm
  have hT : ∀ p q, Tm q p = sigR (Fv F v) σ (Tm p q) := fun p q => (T.2 q p).symm
  have h2 : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ p, ∑ q, X q p * Tm q p) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ p, ∑ q, sigR (Fv F v) σ (X p q) * Tm q p) := by
    simp only [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hT q p, ← trace_sigR v σ hσ, map_mul, sigR_invol (Fv F v) σ hσ]
  have hBR : BR (Fv F v) σ (1 : Matrix (Fin a) (Fin a) E) X (fun p i => Tm i p) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ p, ∑ q, sigR (Fv F v) σ (X p q) * Tm q p) := by
    simp only [BR, hR, Formalism.UG.hform, JR, Matrix.map_apply, Matrix.one_apply, apply_ite,
      map_one, map_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, map_sum]
  rw [hBR]
  simp only [pairHerm, iota, add_mul, Finset.sum_add_distrib, map_add]
  simp only [← hTm]
  rw [h2]
  have h12 : algebraMap F (Fv F v) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul]
    norm_num
  linear_combination (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
    (∑ p, ∑ q, sigR (Fv F v) σ (X p q) * Tm q p)) * h12

include b in
/- English proof (translation)
Use `locallyCompact_Fv F v` as an intermediate fact. Establish `hcl` using `(isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal`. Establish `hKc : IsCompact ((Set.univ.pi fun _ => Set.univ.pi fun _ => (latS v b σ : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)))` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_latS v b σ`. Establish `hKo : IsOpen ((Set.univ.pi fun _ => Set.univ.pi fun _ => (latS v b σ : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)))` using `isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_latS v b σ`. Use `⟨latH v b σ a, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[latH_eq]`. Conclude with `hcl.isCompact_preimage hKc`. Rewrite using `[latH_eq]`. Conclude with `hKo.preimage continuous_subtype_val`. Introduce `s hs S hS`.

Establish `hmem : s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ HermR (Fv F v) σ a`. Introduce `p q`. Simplify using `only [Matrix.smul_apply, sigR_smul, S.2 p q]`. Use `⟨⟨_, hmem⟩, fun p q => smul_mem_latS v b σ hs (hS p q), fun T => ?_⟩` and prove the remaining obligations. Simplify using `only [pairHerm, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `c`. Establish `hN : ∀ Y : Fin a → Fin a → Fv F v ⊗[F] E, (∀ X, BR (Fv F v) σ (1 : Matrix (Fin a) (Fin a) E) X Y = 0) → Y = 0` using `fun Y hY => nondeg_BR v σ hσ 1 (by simp) Y hY`. Take `⟨K, hK, hKs⟩` from `bound_alt v b σ (1 : Matrix (Fin a) (Fin a) E) (a := a) hN c`. Set `tr : (Fin a → Fin a → Fv F v ⊗[F] E) → Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)` to `fun Y i p => Y p i`.

Establish `htr : Continuous tr` using `continuous_pi fun i => continuous_pi fun p => (continuous_apply i).comp (continuous_apply p)`. Use `⟨Subtype.val ⁻¹' (tr '' K), hcl.isCompact_preimage (hK.image htr), ?_⟩` and prove the remaining obligations. Introduce `T hT`. Use `⟨fun p i => (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i p, ?_, rfl⟩` and prove the remaining obligations. Apply `hKs` to reduce the goal to its premises.

Introduce `X hX`. Establish `hS : (⟨iota v σ X, iota_mem v σ hσ X⟩ : HermR (Fv F v) σ a) ∈ latH v b σ a`. Introduce `p q`. Establish `h1 : X p q ∈ latA v b` using `fun k => hX p q k`. Establish `h2 : X q p ∈ latA v b` using `fun k => hX q p k`.

Rewrite using `[mem_latS]`. Conclude with `⟨X q p, h2, X p q, h1, add_comm _ _⟩`. Use `hT _ hS` as an intermediate fact. Rewrite `this` using `[pairHerm_iota v σ hσ]`. Then use the resulting hypothesis.
-/
theorem dualAt_H [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) :
    DualAt v (pairHerm (Fv F v) σ a) := by
  classical
  have := locallyCompact_Fv F v
  have hcl := (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal
  have hKc : IsCompact ((Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (latS v b σ : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_latS v b σ
  have hKo : IsOpen ((Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (latS v b σ : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_latS v b σ
  refine ⟨latH v b σ a, ?_, ?_, ?_, ?_⟩
  · rw [latH_eq]
    exact hcl.isCompact_preimage hKc
  · rw [latH_eq]
    exact hKo.preimage continuous_subtype_val
  · intro s hs S hS
    have hmem : s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ HermR (Fv F v) σ a := by
      intro p q
      simp only [Matrix.smul_apply, sigR_smul, S.2 p q]
    refine ⟨⟨_, hmem⟩, fun p q => smul_mem_latS v b σ hs (hS p q), fun T => ?_⟩
    simp only [pairHerm, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul,
      smul_eq_mul]
    ring
  · intro c
    have hN : ∀ Y : Fin a → Fin a → Fv F v ⊗[F] E,
        (∀ X, BR (Fv F v) σ (1 : Matrix (Fin a) (Fin a) E) X Y = 0) → Y = 0 :=
      fun Y hY => nondeg_BR v σ hσ 1 (by simp) Y hY
    obtain ⟨K, hK, hKs⟩ := bound_alt v b σ (1 : Matrix (Fin a) (Fin a) E) (a := a) hN c
    let tr : (Fin a → Fin a → Fv F v ⊗[F] E) → Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
      fun Y i p => Y p i
    have htr : Continuous tr := continuous_pi fun i => continuous_pi fun p =>
      (continuous_apply i).comp (continuous_apply p)
    refine ⟨Subtype.val ⁻¹' (tr '' K), hcl.isCompact_preimage (hK.image htr), ?_⟩
    intro T hT
    refine ⟨fun p i => (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i p, ?_, rfl⟩
    apply hKs
    intro X hX
    have hS : (⟨iota v σ X, iota_mem v σ hσ X⟩ : HermR (Fv F v) σ a) ∈ latH v b σ a := by
      intro p q
      have h1 : X p q ∈ latA v b := fun k => hX p q k
      have h2 : X q p ∈ latA v b := fun k => hX q p k
      rw [mem_latS]
      exact ⟨X q p, h2, X p q, h1, add_comm _ _⟩
    have := hT _ hS
    rwa [pairHerm_iota v σ hσ] at this

end Herm

end SdDualW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW

def DualHV : Prop := InCtx fun F E _ _ _ _ _ σ _M _J a _X0 _hT =>
  ∀ v : HeightOneSpectrum (𝓞 F), DualAt v (pairHerm (Fv F v) σ a)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Establish `hσ : ∀ x, σ (σ x) = x` using `sigma_invol σ hCM.2.2.2`. Use `⟨?_, hH F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v⟩` and prove the remaining obligations. Conclude with `SdDualW.dualAt_alt v (Module.finBasis F E) σ J (fun Y hY => SdDualW.nondeg_BR v σ hσ J hJ.2 Y hY)`.
-/
theorem dualLatV_of (hH : DualHV) : DualLatV := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  refine ⟨?_, hH F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v⟩
  exact SdDualW.dualAt_alt v (Module.finBasis F E) σ J
    (fun Y hY => SdDualW.nondeg_BR v σ hσ J hJ.2 Y hY)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Conclude with `SdDualW.dualAt_H v (Module.finBasis F E) σ (sigma_invol σ hCM.2.2.2) a`.
-/
theorem dualHV_holds : DualHV := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact SdDualW.dualAt_H v (Module.finBasis F E) σ (sigma_invol σ hCM.2.2.2) a

/- English proof (translation)
The claim follows from `dualLatV_of dualHV_holds`.
-/
theorem dualLatV_holds : DualLatV := dualLatV_of dualHV_holds

/- English proof (translation)
The claim follows from `sdUniq_of_dual hI dualLatV_holds`.
-/
theorem sdUniq_of_inf (hI : SdTestInf) : SdUniq := sdUniq_of_dual hI dualLatV_holds

/- English proof (translation)
The claim follows from `sdUniq_of_dual hI (dualLatV_of hH)`.
-/
theorem sdUniq_of_H (hI : SdTestInf) (hH : DualHV) : SdUniq :=
  sdUniq_of_dual hI (dualLatV_of hH)

end PI.VolStabSW
