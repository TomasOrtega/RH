import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.SmoothMultilinear

/- English proof (translation)
Establish `hd : IsUnit (M.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `hg' : gᴴ * gramAt D V τ * g = gramAt D V τ` using `hg`. Establish `h1` using `M.fr_gram τ`. Establish `h2 : M.fr τ * (M.fr τ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hd`. Use `show (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹) = Formalism.REAL.Jm (M.ε τ)`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by`. Rewrite using `[h1, hg']`. Use `_ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [h2]; simp`.
-/
theorem conj_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {g : Mt V.rank} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h1 := M.fr_gram τ
  have h2 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  show (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹) = Formalism.REAL.Jm (M.ε τ)
  calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by
        rw [h1, hg']
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h2]; simp

/- English proof (translation)
Establish `hd : IsUnit (M.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Unfold `DSModel.rep`. Rewrite using `[Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]`. Conclude with `(M.ds τ).2.2.1.1.1`.
-/
theorem rep_one {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    M.rep τ 1 = 1 := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  unfold DSModel.rep
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

/- English proof (translation)
Establish `hd : IsUnit (M.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `h2 : (M.fr τ)⁻¹ * M.fr τ = 1` using `Matrix.nonsing_inv_mul _ hd`. Unfold `DSModel.rep`. Establish `e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = (M.fr τ * a * (M.fr τ)⁻¹) * (M.fr τ * b * (M.fr τ)⁻¹)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h2]`. Simplify using `only [Matrix.mul_assoc, Matrix.one_mul]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`. Rewrite using `[e]`. Conclude with `(M.ds τ).2.2.1.1.2 _ (conj_mem M τ ha) _ (conj_mem M τ hb)`.
-/
theorem rep_mul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {a b : Mt V.rank} (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (a * b) = M.rep τ a * M.rep τ b := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h2 : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
  unfold DSModel.rep
  have e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = (M.fr τ * a * (M.fr τ)⁻¹) * (M.fr τ * b * (M.fr τ)⁻¹) := by
    calc _ = M.fr τ * a * ((M.fr τ)⁻¹ * M.fr τ) * b * (M.fr τ)⁻¹ := by
          rw [h2]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  exact (M.ds τ).2.2.1.1.2 _ (conj_mem M τ ha) _ (conj_mem M τ hb)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => show (1 : Mt n)ᴴ * H * 1 = H`. Simplify using the standard rewrite rules. Consider the case `cons a l ih`. Rewrite using `[List.prod_cons]`.

Conclude with `CCRuleCW.UH_mul _ _ _ (hl a (by simp)) (ih fun g hg => hl g (by simp [hg]))`.
-/
theorem prod_mem {n : ℕ} (H : Mt n) (l : List (Mt n)) (hl : ∀ g ∈ l, g ∈ Formalism.QuantumDeterminants.UH H) :
    l.prod ∈ Formalism.QuantumDeterminants.UH H := by
  induction l with
  | nil => show (1 : Mt n)ᴴ * H * 1 = H; simp
  | cons a l ih =>
    rw [List.prod_cons]
    exact CCRuleCW.UH_mul _ _ _ (hl a (by simp)) (ih fun g hg => hl g (by simp [hg]))

/- English proof (translation)
Apply `CCRuleCW.exp_mem_UH` to reduce the goal to its premises. Use `CCRuleCW.lie_smul H X hX t` as an intermediate fact. Rewrite `this` using `[Complex.coe_smul]`. Then use the resulting hypothesis.
-/
theorem exp_mem {n : ℕ} (H X : Mt n) (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  apply CCRuleCW.exp_mem_UH
  have := CCRuleCW.lie_smul H X hX t
  rwa [Complex.coe_smul] at this

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => intro k Xs _`. Simplify using `only [map_zero]`. Conclude with `contDiff_const`.

Consider the case `add x y _ _ hx hy => intro k Xs h`. Simplify using `only [map_add]`. Conclude with `(hx k Xs h).add (hy k Xs h)`. Consider the case `smul c x _ hx => intro k Xs h`. Simplify using `only [map_smul]`.

Conclude with `(hx k Xs h).const_smul c`.
-/
theorem smooth_of_span {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Mt n)) (σ : Mt n → (H →L[ℂ] H)) (v : H) (hv : v ∈ Submodule.span ℂ {w | SmoothVec L σ w}) :
    SmoothVec L σ v := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro k Xs _; simp only [map_zero]; exact contDiff_const
  | add x y _ _ hx hy => intro k Xs h; simp only [map_add]; exact (hx k Xs h).add (hy k Xs h)
  | smul c x _ hx => intro k Xs h; simp only [map_smul]; exact (hx k Xs h).const_smul c

/- English proof (translation)
Establish `h` using `hv 1 (fun _ => X) (fun _ => hX)`. Establish `h2 : ContDiff ℝ ∞ (fun t : ℝ => (fun _ : Fin 1 => t))` using `contDiff_pi.2 fun _ => contDiff_id`. Establish `h3` using `h.comp h2`. Establish `h4 : ContDiff ℝ ∞ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v)`. Use `h3 using 2` and compare the differences between its conclusion and the goal.

Simplify using the standard rewrite rules. Conclude with `(h4.differentiable (by simp) 0).hasDerivAt`.
-/
theorem hasDerivAt_of_smooth {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Mt n)) (σ : Mt n → (H →L[ℂ] H)) (v : H) (hv : SmoothVec L σ v) (X : Mt n) (hX : X ∈ L) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0 := by
  have h := hv 1 (fun _ => X) (fun _ => hX)
  have h2 : ContDiff ℝ ∞ (fun t : ℝ => (fun _ : Fin 1 => t)) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := h.comp h2
  have h4 : ContDiff ℝ ∞ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) := by
    convert h3 using 2
    simp
  exact (h4.differentiable (by simp) 0).hasDerivAt

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [rep_one]`. Consider the case `cons p l ih`. Establish `hl' : ∀ q ∈ l, q.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V q.1)` using `fun q hq => hl q (by simp [hq])`. Rewrite using `[List.map_cons, List.prod_cons, map_mul, ContinuousLinearMap.mul_apply, ih hl', ← h p.1 p.2 (hl p (by simp))]`.

Use `congr 1`. Use function extensionality and compare the values at `τ`. Rewrite using `[List.map_cons, List.prod_cons]`. Distinguish the cases in `e : p.1 = τ`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self, if_pos rfl, rep_mul M _ (hl p (by simp)), ContinuousLinearMap.mul_apply]`. Apply `prod_mem` to reduce the goal to its premises. Introduce `g hg`. Take `⟨q, hq, rfl⟩` from `List.mem_map.1 hg`. Use `split_ifs with e`.

Conclude with `e ▸ hl' q hq`. Conclude with `prod_mem _ [] (by simp)`. Rewrite using `[Function.update_of_ne (Ne.symm e), if_neg e, one_mul]`.
-/
theorem act_list {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K)
    (h : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y))
    (y : ∀ τ, M.H τ) (l : List (D.what₂.Tau × Mt V.rank))
    (hl : ∀ p ∈ l, p.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V p.1)) :
    ρ (l.map fun p => atTau θ V p.1 p.2).prod (Φ y) =
      Φ fun τ => M.rep τ (l.map fun p => if p.1 = τ then p.2 else 1).prod (y τ) := by
  induction l with
  | nil => simp [rep_one]
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V q.1) := fun q hq => hl q (by simp [hq])
    rw [List.map_cons, List.prod_cons, map_mul, ContinuousLinearMap.mul_apply, ih hl',
      ← h p.1 p.2 (hl p (by simp))]
    congr 1
    funext τ
    rw [List.map_cons, List.prod_cons]
    by_cases e : p.1 = τ
    · subst e
      rw [Function.update_self, if_pos rfl, rep_mul M _ (hl p (by simp)), ContinuousLinearMap.mul_apply]
      apply prod_mem
      intro g hg
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
      split_ifs with e
      · exact e ▸ hl' q hq
      · exact prod_mem _ [] (by simp)
    · rw [Function.update_of_ne (Ne.symm e), if_neg e, one_mul]

/- English proof (translation)
Introduce `D θ V _ S M K _ _ ρ Φ h v`. Establish `hs : ∀ τ, SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ)` using `fun τ => smooth_of_span _ _ _ (v τ).2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `k τs Xs hX`. Establish `e : (fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod (Φ fun τ => (v τ : M.H τ))) = fun t : Fin k → ℝ => Φ fun τ => M.rep τ (List.ofFn fun i => NormedSpace.exp (t i • (if τs i = τ then Xs i else 0))).prod (v τ : M.H τ)`.

Use function extensionality and compare the values at `t`. Use `act_list θ M ρ Φ h (fun τ => (v τ : M.H τ)) (List.ofFn fun i => (τs i, NormedSpace.exp (t i • Xs i))) (by` as an intermediate fact. Introduce `p hp`. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hp`. Conclude with `exp_mem _ _ (hX i) _)`.

Simplify using `only [List.map_ofFn] at this`. Use `this.trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `τ`. Use `congr 4`.

Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e]`. Establish `hΦ : ContDiff ℝ ∞ (Φ : (∀ τ, M.H τ) → K)` using `(Φ.contDiff (n := ∞)).restrict_scalars ℝ`.

Use `hΦ.comp (contDiff_pi.2 fun τ => ?_)` and prove the remaining obligations. Use `hs τ k _ fun i => ?_` and prove the remaining obligations. Use `split_ifs with e`. Conclude with `e ▸ hX i`. Simplify using `[lieAt]`.

Introduce `τ X hX`. Establish `e : (fun t : ℝ => ρ (oneP θ V τ X t) (Φ fun τ => (v τ : M.H τ))) = fun t : ℝ => (Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ) (M.rep τ (NormedSpace.exp (t • X)) (v τ))`. Use function extensionality and compare the values at `t`. Conclude with `(h τ _ (exp_mem _ _ hX t) _).symm`. Unfold `dL2`.

Simplify using `only`. Rewrite using `[e]`. Establish `h1` using `hasDerivAt_of_smooth _ _ _ (hs τ) X hX`. Conclude with `(((Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1).deriv`.
-/
theorem smooth_map : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K)) (Φ : ContinuousMultilinearMap ℂ M.H K), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) → ∀ v : M.Vec, IsSmoothVector' θ V ρ (Φ fun τ => (v τ : M.H τ)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) = Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))) := by
  intro D θ V _ S M K _ _ ρ Φ h v
  have hs : ∀ τ, SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) := fun τ => smooth_of_span _ _ _ (v τ).2
  refine ⟨?_, ?_⟩
  · intro k τs Xs hX
    have e : (fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod (Φ fun τ => (v τ : M.H τ))) =
        fun t : Fin k → ℝ => Φ fun τ => M.rep τ
          (List.ofFn fun i => NormedSpace.exp (t i • (if τs i = τ then Xs i else 0))).prod (v τ : M.H τ) := by
      funext t
      have := act_list θ M ρ Φ h (fun τ => (v τ : M.H τ))
        (List.ofFn fun i => (τs i, NormedSpace.exp (t i • Xs i))) (by
          intro p hp
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
          exact exp_mem _ _ (hX i) _)
      simp only [List.map_ofFn] at this
      refine this.trans ?_
      congr 1
      funext τ
      congr 4
      funext i
      simp only [Function.comp]
      split_ifs <;> simp
    rw [e]
    have hΦ : ContDiff ℝ ∞ (Φ : (∀ τ, M.H τ) → K) := (Φ.contDiff (n := ∞)).restrict_scalars ℝ
    refine hΦ.comp (contDiff_pi.2 fun τ => ?_)
    refine hs τ k _ fun i => ?_
    split_ifs with e
    · exact e ▸ hX i
    · simp [lieAt]
  · intro τ X hX
    have e : (fun t : ℝ => ρ (oneP θ V τ X t) (Φ fun τ => (v τ : M.H τ))) =
        fun t : ℝ => (Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ)
          (M.rep τ (NormedSpace.exp (t • X)) (v τ)) := by
      funext t
      exact (h τ _ (exp_mem _ _ hX t) _).symm
    unfold dL2
    simp only
    rw [e]
    have h1 := hasDerivAt_of_smooth _ _ _ (hs τ) X hX
    exact (((Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1).deriv

end GlobalTheory.SmoothMultilinear
