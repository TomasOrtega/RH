import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ClosureK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

/- English proof (translation)
Establish `hZ0 : ∀ a b, ε a ≠ ε b → Z a b = 0`. Introduce `a b hab`. Establish `h` using `congrFun (congrFun hZ.2 a) b`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h`. Establish `hne : (if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1) ≠ 0`.

Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp_all <;> norm_num`. Establish `h2 : Z a b * ((if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1)) = 0`. Take the linear combination `h`. Conclude with `(mul_eq_zero.mp h2).resolve_right hne`. Simplify using `only [actM, LinearMap.sum_apply, LinearMap.smul_apply]`.

Use `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hab : ε a = ε b`. Conclude with `S.smul_mem _ (hS a b hab x hx)`. Rewrite using `[hZ0 a b hab, zero_smul]`. Conclude with `S.zero_mem`.
-/
theorem actM_mem_of_isKStableSub_inK {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {x : D} (hx : x ∈ S) :
    actM E Z x ∈ S := by
  have hZ0 : ∀ a b, ε a ≠ ε b → Z a b = 0 := by
    intro a b hab
    have h := congrFun (congrFun hZ.2 a) b
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hne : (if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1) ≠ 0 := by
      cases ha : ε a <;> cases hb : ε b <;> simp_all <;> norm_num
    have h2 : Z a b * ((if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h2).resolve_right hne
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  by_cases hab : ε a = ε b
  · exact S.smul_mem _ (hS a b hab x hx)
  · rw [hZ0 a b hab, zero_smul]
    exact S.zero_mem

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using hx`. Consider the case `succ m ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `actM_mem_of_isKStableSub_inK hS hZ ih`.
-/
theorem actM_pow_mem_of_isKStableSub_inK {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {x : D} (hx : x ∈ S) (m : ℕ) :
    ((actM E Z) ^ m) x ∈ S := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact actM_mem_of_isKStableSub_inK hS hZ ih

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ S := hSf`. Set `g : S →ₗ[ℂ] S` to `(actM E Z).restrict (fun x hx => actM_mem_of_isKStableSub_inK hS hZ hx)`. Set `gL : S →L[ℂ] S` to `LinearMap.toContinuousLinearMap g`. Use `⟨‖gL‖, norm_nonneg _, ?_⟩` and prove the remaining obligations. Establish `key : ∀ y : S, ‖actM E Z (y : D)‖ ≤ ‖gL‖ * ‖y‖` using `fun y => gL.le_opNorm y`.

Introduce `x hx m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `hm` using `actM_pow_mem_of_isKStableSub_inK hS hZ hx m`.

Establish `h1` using `key ⟨_, hm⟩`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_norm_actM_pow_le_of_isKStableSub {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    (hSf : FiniteDimensional ℂ S) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ m : ℕ, ‖((actM E Z) ^ m) x‖ ≤ C ^ m * ‖x‖ := by
  haveI : FiniteDimensional ℂ S := hSf
  let g : S →ₗ[ℂ] S := (actM E Z).restrict (fun x hx => actM_mem_of_isKStableSub_inK hS hZ hx)
  let gL : S →L[ℂ] S := LinearMap.toContinuousLinearMap g
  refine ⟨‖gL‖, norm_nonneg _, ?_⟩
  have key : ∀ y : S, ‖actM E Z (y : D)‖ ≤ ‖gL‖ * ‖y‖ := fun y => gL.le_opNorm y
  intro x hx m
  induction m with
  | zero => simp
  | succ m ih =>
    have hm := actM_pow_mem_of_isKStableSub_inK hS hZ hx m
    have h1 := key ⟨_, hm⟩
    rw [pow_succ', Module.End.mul_apply]
    calc ‖actM E Z (((actM E Z) ^ m) x)‖ ≤ ‖gL‖ * ‖((actM E Z) ^ m) x‖ := h1
      _ ≤ ‖gL‖ * (‖gL‖ ^ m * ‖x‖) := mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = ‖gL‖ ^ (m + 1) * ‖x‖ := by ring

/- English proof (translation)
Introduce `g hg v hv`. Take `⟨Z, hZ, rfl⟩` from `exists_exp_eq_of_mem_Kset hg`. Take `⟨C, hC0, hC⟩` from `exists_norm_actM_pow_le_of_isKStableSub hk hS hZ`. Establish `hs : Summable fun m : ℕ => (C ^ m * ‖v‖) * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ)`. Simplify using `only [sub_zero, abs_one, one_pow, mul_one]`.

Conclude with `((Real.summable_pow_div_factorial C).mul_right ‖v‖).congr fun m => by ring`. Establish `h` using `hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖) (fun m => hC v hv m) 0 1 hs`. Simplify using `only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply, Complex.ofReal_one, one_smul] at h`. Use `haveI : FiniteDimensional ℂ S := hS`. Establish `hT : IsClosed ((S.map D.subtype : Submodule ℂ H) : Set H)` using `Submodule.closed_of_finiteDimensional _`.

Establish `hmem : σ (NormedSpace.exp Z) (v : H) ∈ S.map D.subtype`. Use `hT.mem_of_tendsto h.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ⟨_, actM_pow_mem_of_isKStableSub_inK hk hZ hv m, rfl⟩`. Take `⟨w, hwS, hw⟩` from `hmem`. Conclude with `⟨w, hwS, hw⟩`.
-/
theorem kStable_of_isKStableSub (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (S : Submodule ℂ D)
    (hS : FiniteDimensional ℂ S) (hk : IsKStableSub ε E S) :
    ∀ k ∈ Kset ε, ∀ v ∈ S, ∃ w ∈ S, (w : H) = σ k v := by
  intro g hg v hv
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hg
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_isKStableSub hk hS hZ
  have hs : Summable fun m : ℕ => (C ^ m * ‖v‖) * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    simp only [sub_zero, abs_one, one_pow, mul_one]
    exact ((Real.summable_pow_div_factorial C).mul_right ‖v‖).congr fun m => by ring
  have h := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖) (fun m => hC v hv m) 0 1 hs
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1,
    ContinuousLinearMap.one_apply, Complex.ofReal_one, one_smul] at h
  haveI : FiniteDimensional ℂ S := hS
  have hT : IsClosed ((S.map D.subtype : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : σ (NormedSpace.exp Z) (v : H) ∈ S.map D.subtype := by
    refine hT.mem_of_tendsto h.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
    exact Submodule.sum_mem _ fun m _ =>
      Submodule.smul_mem _ _ ⟨_, actM_pow_mem_of_isKStableSub_inK hk hZ hv m, rfl⟩
  obtain ⟨w, hwS, hw⟩ := hmem
  exact ⟨w, hwS, hw⟩

end ReciprocityTheory.ChartRestriction.DS
