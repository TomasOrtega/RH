import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CxRootsInjective
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

/- English proof (translation)
Set `φ : Fld P →+* ℂ` to `(starRingEnd ℂ).comp ((psiL P τ m).comp (star' P : Fld P →+* Fld P))`. Establish `hE : φ.comp (algebraMap E (Fld P)) = τ.1`. Use extensionality with `e`. Express the relevant statement in the definitionally equal form `conj (psiL P τ m (star' P (algebraMap E (Fld P) e))) = τ.1 e`. Rewrite using `[star'_algebraMap, psiL_algebraMap, hCM.2.2.2 τ.1 e]`.

Simplify using the standard rewrite rules. Establish `hα : φ (alpha P) = (conj (cxRoots τ.1 P m))⁻¹`. Express the relevant statement in the definitionally equal form `conj (psiL P τ m (star' P (alpha P))) = _`. Rewrite using `[star'_alpha, map_inv₀, psiL_alpha, map_inv₀]`. Establish `h0` using `congrArg φ (eval_alpha P)`.

Rewrite `h0` using `[hom_eval₂, hE, hα, map_zero, ← eval_map, cxRoots_spec, eval_prod, Finset.prod_eq_zero_iff]`. Take `⟨j, -, hj⟩` from `h0`. Use `⟨j, ?_⟩` and prove the remaining obligations. Rewrite `hj` using `[eval_sub, eval_X, eval_C, sub_eq_zero]`. Conclude with `hj.symm`.
-/
theorem exists_conjInv_root (hCM : IsCMExt F E σ) (m : Fin r) :
    ∃ j, cxRoots τ.1 P j = (conj (cxRoots τ.1 P m))⁻¹ := by
  let φ : Fld P →+* ℂ := (starRingEnd ℂ).comp ((psiL P τ m).comp (star' P : Fld P →+* Fld P))
  have hE : φ.comp (algebraMap E (Fld P)) = τ.1 := by
    ext e
    change conj (psiL P τ m (star' P (algebraMap E (Fld P) e))) = τ.1 e
    rw [star'_algebraMap, psiL_algebraMap, hCM.2.2.2 τ.1 e]
    simp
  have hα : φ (alpha P) = (conj (cxRoots τ.1 P m))⁻¹ := by
    change conj (psiL P τ m (star' P (alpha P))) = _
    rw [star'_alpha, map_inv₀, psiL_alpha, map_inv₀]
  have h0 := congrArg φ (eval_alpha P)
  rw [hom_eval₂, hE, hα, map_zero, ← eval_map, cxRoots_spec, eval_prod, Finset.prod_eq_zero_iff] at h0
  obtain ⟨j, -, hj⟩ := h0
  refine ⟨j, ?_⟩
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
  exact hj.symm

end GlobalTheory.TrEll.RealTorus

open GlobalTheory.TrEll.RealTorus in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM r P w τ hB hK i`. Establish `hw : w.IsReal` using `by haveI := hCM.1; exact IsTotallyReal.isReal w`. Take `⟨π, hπ⟩ : ∃ π : Fin r → Fin r, ∀ m, cxRoots τ.1 P (π m) = (conj (cxRoots τ.1 P m))⁻¹` from `⟨fun m => (exists_conjInv_root P τ hCM m).choose, fun m => (exists_conjInv_root P τ hCM m).choose_spec⟩`. Establish `hinv : ∀ m, π (π m) = m` using `fun m => cxRoots_injective P τ (by rw [hπ, hπ, map_inv₀, Complex.conj_conj, inv_inv])`. Establish `hpsi : ∀ m, (psiL P τ m).comp (star' P : Fld P →+* Fld P) = (starRingEnd ℂ).comp (psiL P τ (π m))`.

Introduce `m`. Use `AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `psiL P τ m (star' P (algebraMap E (Fld P) e)) = conj (psiL P τ (π m) (algebraMap E (Fld P) e))`. Rewrite using `[star'_algebraMap, psiL_algebraMap, psiL_algebraMap]`. Conclude with `hCM.2.2.2 τ.1 e`.

Express the relevant statement in the definitionally equal form `psiL P τ m (star' P (alpha P)) = conj (psiL P τ (π m) (alpha P))`. Rewrite using `[star'_alpha, map_inv₀, psiL_alpha, psiL_alpha, hπ, map_inv₀, Complex.conj_conj]`. Establish `hsig : ∀ m y, Psi P τ m (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y) = conj (Psi P τ (π m) y)`. Introduce `m y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a l`. Express the relevant statement in the definitionally equal form `Psi P τ m (a ⊗ₜ[F] star' P l) = _`. Rewrite using `[Psi_tmul, Psi_tmul, map_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a, Complex.conj_ofReal]`.

Conclude with `congrArg _ (RingHom.congr_fun (hpsi m) l)`. Establish `h0 : cxRoots τ.1 P i ≠ 0`. Rewrite using `[← psiL_alpha P τ i]`. Conclude with `(_root_.map_ne_zero _).2 (alpha_ne_zero P)`. It suffices to establish `hfix : π i = i by`.

Establish `e` using `hπ i`. Rewrite `e` using `[hfix]`. Establish `h1 : cxRoots τ.1 P i * conj (cxRoots τ.1 P i) = 1` using `by nth_rw 1 [e]`. Conclude with `inv_mul_cancel₀ ((_root_.map_ne_zero _).2 h0)`. Rewrite `h1` using `[Complex.mul_conj, ← Complex.sq_norm]`.

Establish `h2 : ‖cxRoots τ.1 P i‖ ^ 2 = 1` using `by exact_mod_cast h1`. Use polynomial arithmetic with `[norm_nonneg (cxRoots τ.1 P i)]`. Assume the negation of the conclusion as `hji`. Establish `hcont : Continuous (fun g : Tor P w.Completion => ‖Psi P τ i (g.1.1 0 0)‖)`. Use `letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra`.

Use `haveI : ContinuousSMul w.Completion ℂ := continuousSMul_of_algebraMap _ _ (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous`. Use `haveI : IsModuleTopology w.Completion (w.Completion ⊗[F] Fld P) := ⟨rfl⟩`. Set `L : w.Completion ⊗[F] Fld P →ₗ[w.Completion] ℂ` to `{ toFun := Psi P τ i map_add' := map_add _ map_smul' := by`. Introduce `c y`. Establish `: c • y = (c ⊗ₜ[F] (1 : Fld P)) * y`.

Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[this, map_mul, Psi_tmul, map_one, mul_one]`. Use `rfl }`. Establish `hL : Continuous L` using `IsModuleTopology.continuous_of_linearMap L`.

Establish `hv : Continuous (fun g : Tor P w.Completion => (g.1.1 : Matrix (Fin 1) (Fin 1) (w.Completion ⊗[F] Fld P)))` using `Units.continuous_val.comp continuous_subtype_val`. Conclude with `continuous_norm.comp (hL.comp (hv.matrix_elem 0 0))`. Take `⟨M, hM⟩` from `(isCompact_range hcont).bddAbove`. Take `⟨j, hj⟩ : ∃ j, π i = j` from `⟨_, rfl⟩`. Establish `hji' : j ≠ i` using `by rw [← hj]; exact hji`.

Establish `hπj : π j = i` using `by rw [← hj]; exact hinv i`. Establish `hne : ∀ m, m ≠ j → π m ≠ i` using `fun m hm h => hm (by have := hinv m; rw [h, hj] at this; exact this.symm)`. Establish `hne' : ∀ m, m ≠ i → π m ≠ j` using `fun m hm h => hm (by have := hinv m; rw [h, hπj] at this; exact this.symm)`. Use `set t : ℝ := max M 0 + 1 with ht`. Establish `ht0 : 0 < t` using `by positivity`.

Set `v : Fin r → ℂ` to `fun m => if m = i then (t : ℂ) else if m = j then (t : ℂ)⁻¹ else 1`. Take `⟨y, hy⟩` from `hB.2 v`. Establish `hyv : ∀ m, Psi P τ m y = v m` using `fun m => congrFun hy m`. Establish `htc : (t : ℂ) ≠ 0` using `by exact_mod_cast ht0.ne'`. Establish `hyy : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y * y = 1`.

Apply `hB.1` to reduce the goal to its premises. Use function extensionality and compare the values at `m`. Rewrite using `[map_mul, map_one, Pi.mul_apply, PsiAll_apply, PsiAll_apply, hsig, hyv, hyv, Pi.one_apply]`. Distinguish the cases in `hmi : m = i`. Rewrite using `[hmi, hj]`.

Simplify using `[v, hji', htc]`. Distinguish the cases in `hmj : m = j`. Rewrite using `[hmj, hπj]`. Simplify using `[v, hji', htc]`. Simplify using `[v, hmi, hmj, hne m hmj, hne' m hmi]`.

Set `u : (w.Completion ⊗[F] Fld P)ˣ` to `⟨y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y, by rw [mul_comm]; exact hyy, hyy⟩`. Set `g : Tor P w.Completion` to `⟨Matrix.GeneralLinearGroup.scalar (Fin 1) u, by`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT _ _ * _ * _ = _`. Use extensionality with `a b`. Simplify using `[Formalism.UG.cT, Matrix.mul_apply, Subsingleton.elim a 0, Subsingleton.elim b 0, JR, inclR, u, ← Algebra.TensorProduct.one_def, hyy]⟩`.

Establish `hg : ‖Psi P τ i (g.1.1 0 0)‖ = t`. Establish `: g.1.1 0 0 = y` using `by simp [g, u]`. Rewrite using `[this, hyv]`. Simplify using `[v, abs_of_pos ht0]`. Establish `hle : ‖Psi P τ i (g.1.1 0 0)‖ ≤ M` using `hM ⟨g, rfl⟩`.

Rewrite `hle` using `[hg]`. Establish `: M < t` using `by rw [ht]; linarith [le_max_left M 0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem GlobalTheory.TrEll.realTorus_norm_cxRoots : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) → CompactSpace (Tor P w.Completion) → ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  intro F E _ _ _ _ _ σ hCM r P w τ hB hK i
  have hw : w.IsReal := by haveI := hCM.1; exact IsTotallyReal.isReal w
  obtain ⟨π, hπ⟩ : ∃ π : Fin r → Fin r, ∀ m, cxRoots τ.1 P (π m) = (conj (cxRoots τ.1 P m))⁻¹ :=
    ⟨fun m => (exists_conjInv_root P τ hCM m).choose, fun m => (exists_conjInv_root P τ hCM m).choose_spec⟩
  have hinv : ∀ m, π (π m) = m := fun m =>
    cxRoots_injective P τ (by rw [hπ, hπ, map_inv₀, Complex.conj_conj, inv_inv])
  have hpsi : ∀ m, (psiL P τ m).comp (star' P : Fld P →+* Fld P) = (starRingEnd ℂ).comp (psiL P τ (π m)) := by
    intro m
    refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
    · change psiL P τ m (star' P (algebraMap E (Fld P) e)) = conj (psiL P τ (π m) (algebraMap E (Fld P) e))
      rw [star'_algebraMap, psiL_algebraMap, psiL_algebraMap]
      exact hCM.2.2.2 τ.1 e
    · change psiL P τ m (star' P (alpha P)) = conj (psiL P τ (π m) (alpha P))
      rw [star'_alpha, map_inv₀, psiL_alpha, psiL_alpha, hπ, map_inv₀, Complex.conj_conj]
  have hsig : ∀ m y, Psi P τ m (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y) = conj (Psi P τ (π m) y) := by
    intro m y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a l =>
      change Psi P τ m (a ⊗ₜ[F] star' P l) = _
      rw [Psi_tmul, Psi_tmul, map_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a,
        Complex.conj_ofReal]
      exact congrArg _ (RingHom.congr_fun (hpsi m) l)
  have h0 : cxRoots τ.1 P i ≠ 0 := by
    rw [← psiL_alpha P τ i]; exact (_root_.map_ne_zero _).2 (alpha_ne_zero P)
  suffices hfix : π i = i by
    have e := hπ i
    rw [hfix] at e
    have h1 : cxRoots τ.1 P i * conj (cxRoots τ.1 P i) = 1 := by
      nth_rw 1 [e]
      exact inv_mul_cancel₀ ((_root_.map_ne_zero _).2 h0)
    rw [Complex.mul_conj, ← Complex.sq_norm] at h1
    have h2 : ‖cxRoots τ.1 P i‖ ^ 2 = 1 := by exact_mod_cast h1
    nlinarith [norm_nonneg (cxRoots τ.1 P i)]

  by_contra hji

  have hcont : Continuous (fun g : Tor P w.Completion => ‖Psi P τ i (g.1.1 0 0)‖) := by
    letI : Algebra w.Completion ℂ := (InfinitePlace.Completion.extensionEmbedding w).toAlgebra
    haveI : ContinuousSMul w.Completion ℂ :=
      continuousSMul_of_algebraMap _ _ (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
    haveI : IsModuleTopology w.Completion (w.Completion ⊗[F] Fld P) := ⟨rfl⟩
    let L : w.Completion ⊗[F] Fld P →ₗ[w.Completion] ℂ :=
      { toFun := Psi P τ i
        map_add' := map_add _
        map_smul' := by
          intro c y
          have : c • y = (c ⊗ₜ[F] (1 : Fld P)) * y := by
            rw [Algebra.smul_def]; rfl
          rw [this, map_mul, Psi_tmul, map_one, mul_one]; rfl }
    have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
    have hv : Continuous (fun g : Tor P w.Completion => (g.1.1 : Matrix (Fin 1) (Fin 1) (w.Completion ⊗[F] Fld P))) :=
      Units.continuous_val.comp continuous_subtype_val
    exact continuous_norm.comp (hL.comp (hv.matrix_elem 0 0))
  obtain ⟨M, hM⟩ := (isCompact_range hcont).bddAbove
  obtain ⟨j, hj⟩ : ∃ j, π i = j := ⟨_, rfl⟩
  have hji' : j ≠ i := by rw [← hj]; exact hji
  have hπj : π j = i := by rw [← hj]; exact hinv i
  have hne : ∀ m, m ≠ j → π m ≠ i := fun m hm h => hm (by have := hinv m; rw [h, hj] at this; exact this.symm)
  have hne' : ∀ m, m ≠ i → π m ≠ j := fun m hm h => hm (by have := hinv m; rw [h, hπj] at this; exact this.symm)
  set t : ℝ := max M 0 + 1 with ht
  have ht0 : 0 < t := by positivity
  let v : Fin r → ℂ := fun m => if m = i then (t : ℂ) else if m = j then (t : ℂ)⁻¹ else 1
  obtain ⟨y, hy⟩ := hB.2 v
  have hyv : ∀ m, Psi P τ m y = v m := fun m => congrFun hy m
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hyy : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y * y = 1 := by
    apply hB.1
    funext m
    rw [map_mul, map_one, Pi.mul_apply, PsiAll_apply, PsiAll_apply, hsig, hyv, hyv, Pi.one_apply]
    by_cases hmi : m = i
    · rw [hmi, hj]
      simp [v, hji', htc]
    · by_cases hmj : m = j
      · rw [hmj, hπj]
        simp [v, hji', htc]
      · simp [v, hmi, hmj, hne m hmj, hne' m hmi]
  let u : (w.Completion ⊗[F] Fld P)ˣ := ⟨y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion (star' P) y, by rw [mul_comm]; exact hyy, hyy⟩
  let g : Tor P w.Completion := ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) u, by
    change Formalism.UG.cT _ _ * _ * _ = _
    ext a b
    simp [Formalism.UG.cT, Matrix.mul_apply, Subsingleton.elim a 0, Subsingleton.elim b 0, JR, inclR, u, ← Algebra.TensorProduct.one_def, hyy]⟩
  have hg : ‖Psi P τ i (g.1.1 0 0)‖ = t := by
    have : g.1.1 0 0 = y := by simp [g, u]
    rw [this, hyv]
    simp [v, abs_of_pos ht0]
  have hle : ‖Psi P τ i (g.1.1 0 0)‖ ≤ M := hM ⟨g, rfl⟩
  rw [hg] at hle
  have : M < t := by rw [ht]; linarith [le_max_left M 0]
  linarith
