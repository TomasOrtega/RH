import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.OeEqOfRangeSub

noncomputable section

open Matrix Classical

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

section
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

/- English proof (translation)
Unfold `VnuMap`. Rewrite using `[finsum_eq_sum_of_fintype]`. Both sides reduce to the same expression.
-/
theorem vnuMap_eq (f : Lt → Matrix (Fin N) (Fin N) ℂ) (φ : LaC N nu) (I : ColChoice N nu) :
    VnuMap nu f φ I = ∑ J, E nu f I J * φ J := by
  unfold VnuMap
  rw [finsum_eq_sum_of_fintype]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `I`. Simplify using `only [vnuMap_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem vnuMap_add (f : Lt → Matrix (Fin N) (Fin N) ℂ) (φ ψ : LaC N nu) :
    VnuMap nu f (φ + ψ) = VnuMap nu f φ + VnuMap nu f ψ := by
  funext I
  simp only [vnuMap_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Use function extensionality and compare the values at `I`. Simplify using `only [vnuMap_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun J _ => by ring`.
-/
theorem vnuMap_smul (f : Lt → Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (φ : LaC N nu) :
    VnuMap nu f (a • φ) = a • VnuMap nu f φ := by
  funext I
  simp only [vnuMap_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun J _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `I`. Simplify using `[vnuMap_eq]`.
-/
theorem vnuMap_zero (f : Lt → Matrix (Fin N) (Fin N) ℂ) : VnuMap nu f (0 : LaC N nu) = 0 := by
  funext I
  simp [vnuMap_eq]

/- English proof (translation)
Unfold `E`. Simplify using `only [map_prod]`. Use `Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[starRingEnd_apply, ← Matrix.det_conjTranspose]`. Use `congr 1`.
-/
theorem eStar (k : Lt → Matrix (Fin N) (Fin N) ℂ) (I J : ColChoice N nu) :
    starRingEnd ℂ (E nu k I J) = E nu (fun s => star (k s)) J I := by
  unfold E
  simp only [map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [starRingEnd_apply, ← Matrix.det_conjTranspose]
  congr 1

/- English proof (translation)
Establish `: g = fun s => Matrix.diagonal (fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `s`. Rewrite using `[hg, Matrix.diagonal_one]`. Rewrite using `[this, metric_diagonal]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem e_one (g : Lt → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ s, g s = 1) (I J : ColChoice N nu) :
    E nu g I J = if I = J then 1 else 0 := by
  have : g = fun s => Matrix.diagonal (fun _ => (1 : ℂ)) := by
    funext s
    rw [hg, Matrix.diagonal_one]
  rw [this, metric_diagonal]
  split_ifs <;> simp
end

/- English proof (translation)
Introduce `Lt _ _ N nu f φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, rfl⟩` from `hx`. Rewrite using `[hM]`.

Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Consider the case `zero => rw [vnuMap_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [vnuMap_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul a x _ hx => rw [vnuMap_smul]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem stab_of (hM : HvMap) : Stab := by
  intro Lt _ _ N nu f φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    rw [hM]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => rw [vnuMap_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [vnuMap_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [vnuMap_smul]; exact Submodule.smul_mem _ a hx

/- English proof (translation)
Introduce `Lt _ _ N nu k`. Unfold `u0`. Rewrite using `[hM]`. Use `congr 1`. Use function extensionality and compare the values at `s a j`.

Unfold `fr colsOf`. Distinguish the cases in `hj : j < N`. Simplify using `[hj, Matrix.one_apply]`. Simplify using `[hj]`.
-/
theorem hvCols_of (hM : HvMap) : HvCols := by
  intro Lt _ _ N nu k
  unfold u0
  rw [hM]
  congr 1
  funext s a j
  unfold fr colsOf
  by_cases hj : j < N
  · simp [hj, Matrix.one_apply]
  · simp [hj]

/- English proof (translation)
Introduce `Lt _ _ N nu k hk φ ψ`. Establish `hkk : ∀ z, star (k z) * k z = 1` using `fun z => Matrix.mem_unitaryGroup_iff'.mp (hk z)`. Establish `h1 : ∀ J J' : ColChoice N nu, ∑ I, starRingEnd ℂ (E nu k I J) * E nu k I J' = if J = J' then 1 else 0`. Introduce `J J'`. Simplify using `only [eStar]`.

Rewrite using `[hE]`. Conclude with `e_one _ hkk J J'`. Establish `step : ∀ J J' : ColChoice N nu, ∑ I, star (E nu k I J * φ J) * (E nu k I J' * ψ J') = star (φ J) * ψ J' * (if J = J' then 1 else 0)`. Introduce `J J'`. Rewrite using `[← h1 J J', Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul', starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree. Unfold `ipl`. Simplify using `only [vnuMap_eq]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[star_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `_ = ∑ J, ∑ J', ∑ I, star (E nu k I J * φ J) * (E nu k I J' * ψ J') := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `_ = ∑ J, star (φ J) * ψ J := by`.

Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Simplify using `only [step, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules.
-/
theorem unit_of (hE : EMul) : Unit := by
  intro Lt _ _ N nu k hk φ ψ
  have hkk : ∀ z, star (k z) * k z = 1 := fun z => Matrix.mem_unitaryGroup_iff'.mp (hk z)
  have h1 : ∀ J J' : ColChoice N nu,
      ∑ I, starRingEnd ℂ (E nu k I J) * E nu k I J' = if J = J' then 1 else 0 := by
    intro J J'
    simp only [eStar]
    rw [hE]
    exact e_one _ hkk J J'
  have step : ∀ J J' : ColChoice N nu, ∑ I, star (E nu k I J * φ J) * (E nu k I J' * ψ J') =
      star (φ J) * ψ J' * (if J = J' then 1 else 0) := by
    intro J J'
    rw [← h1 J J', Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [star_mul', starRingEnd_apply]
    ring
  unfold ipl
  simp only [vnuMap_eq]
  calc ∑ I, star (∑ J, E nu k I J * φ J) * ∑ J', E nu k I J' * ψ J'
      = ∑ I, ∑ J, ∑ J', star (E nu k I J * φ J) * (E nu k I J' * ψ J') := by
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ J, ∑ J', ∑ I, star (E nu k I J * φ J) * (E nu k I J' * ψ J') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ J, star (φ J) * ψ J := by
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [step, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp

/- English proof (translation)
Introduce `Lt _ _ N nu k hk φ`. Establish `hkk : ∀ z, k z * star (k z) = 1` using `fun z => Matrix.mem_unitaryGroup_iff.mp (hk z)`. Use function extensionality and compare the values at `I`. Establish `h1 : ∀ K, ∑ J, E nu k I J * E nu (fun z => star (k z)) J K = if I = K then 1 else 0`. Introduce `K`.

Rewrite using `[hE]`. Conclude with `e_one _ hkk I K`. Simplify using `only [vnuMap_eq, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← mul_assoc, ← Finset.sum_mul, h1, ite_mul, one_mul, zero_mul]`.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules.
-/
theorem invK_of (hE : EMul) : InvK := by
  intro Lt _ _ N nu k hk φ
  have hkk : ∀ z, k z * star (k z) = 1 := fun z => Matrix.mem_unitaryGroup_iff.mp (hk z)
  funext I
  have h1 : ∀ K, ∑ J, E nu k I J * E nu (fun z => star (k z)) J K = if I = K then 1 else 0 := by
    intro K
    rw [hE]
    exact e_one _ hkk I K
  simp only [vnuMap_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, h1, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

end PI.IsoInvMetricW
