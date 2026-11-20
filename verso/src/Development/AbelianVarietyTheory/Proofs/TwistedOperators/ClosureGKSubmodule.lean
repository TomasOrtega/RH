import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteOrthogonalComplement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothIntertwinerExtension

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.GKClosure

open GlobalTheory.MatrixCoeffAgree

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Use `set G : H → ℝ → ℂ := fun z s => ⟪w, π (NormedSpace.exp (s • X)) z⟫_ℂ with hGdef`. Establish `hderiv : ∀ z ∈ Y, ∀ s, HasDerivAt (G z) (G (dRep π X z) s) s`. Introduce `z hz s`. Establish `h1` using `hasDerivAt_orbit hπ hX (hasDerivAt_zero_of_smoothVec hX (hY.smooth z hz)) s`. Conclude with `((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1`.

Establish `hiter : ∀ k, ∀ z ∈ Y, iteratedDeriv k (G z) 0 = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `z hz`.

Simplify using `only [iteratedDeriv_zero, hGdef, zero_smul, NormedSpace.exp_zero, hπ.1, ContinuousLinearMap.one_apply]`. Conclude with `Submodule.inner_left_of_mem_orthogonal hz hw`. Consider the case `succ k ih`. Introduce `z hz`. Rewrite using `[iteratedDeriv_succ']`.

Establish `: deriv (G z) = G (dRep π X z)` using `funext fun s => (hderiv z hz s).deriv`. Rewrite using `[this, ih _ (hY.lieStable X hX z hz)]`. Establish `han' : ∀ s, AnalyticAt ℝ (G y) s`. Introduce `s`. Establish `h1` using `han.analytic_exp one_mem_UJset hX s`.

Simplify `h1` using `only [Matrix.one_mul]`. Conclude with `eq_zero_of_iteratedDeriv han' (fun k => hiter k y hy) t`.
-/
theorem inner_exp_eq_zero (hπ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) {Y : Submodule ℂ H} (hY : IsGKSub ε π Y) {w : H}
    (hw : w ∈ Yᗮ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) {y : H} (hy : y ∈ Y)
    (han : AnalyticOnUJ ε fun g => ⟪w, π g y⟫_ℂ) (t : ℝ) : ⟪w, π (NormedSpace.exp (t • X)) y⟫_ℂ = 0 := by
  set G : H → ℝ → ℂ := fun z s => ⟪w, π (NormedSpace.exp (s • X)) z⟫_ℂ with hGdef
  have hderiv : ∀ z ∈ Y, ∀ s, HasDerivAt (G z) (G (dRep π X z) s) s := by
    intro z hz s
    have h1 := hasDerivAt_orbit hπ hX (hasDerivAt_zero_of_smoothVec hX (hY.smooth z hz)) s
    exact ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
  have hiter : ∀ k, ∀ z ∈ Y, iteratedDeriv k (G z) 0 = 0 := by
    intro k
    induction k with
    | zero =>
      intro z hz
      simp only [iteratedDeriv_zero, hGdef, zero_smul, NormedSpace.exp_zero, hπ.1, ContinuousLinearMap.one_apply]
      exact Submodule.inner_left_of_mem_orthogonal hz hw
    | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ']
      have : deriv (G z) = G (dRep π X z) := funext fun s => (hderiv z hz s).deriv
      rw [this, ih _ (hY.lieStable X hX z hz)]
  have han' : ∀ s, AnalyticAt ℝ (G y) s := by
    intro s
    have h1 := han.analytic_exp one_mem_UJset hX s
    simpa only [Matrix.one_mul] using h1
  exact eq_zero_of_iteratedDeriv han' (fun k => hiter k y hy) t

/- English proof (translation)
Use `⟨Unitary.star_mem hk.1, ?_⟩` and prove the remaining obligations. Use `congrArg Matrix.conjTranspose (show k * Jm ε = Jm ε * k from hk.2)` as an intermediate fact. Simplify using `only [Matrix.conjTranspose_mul, Jm_conjTranspose] at this`. Conclude with `this.symm`.
-/
theorem conjTranspose_mem_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : kᴴ ∈ Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have := congrArg Matrix.conjTranspose (show k * Jm ε = Jm ε * k from hk.2)
  simp only [Matrix.conjTranspose_mul, Jm_conjTranspose] at this
  exact this.symm

/- English proof (translation)
Introduce `k hk u hu`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `y hy`. Establish `hk'` using `conjTranspose_mem_Kset hk`. Establish `h1 : π k (π kᴴ y) = y`.

Use `hπ.1.2 k (mem_UJset_of_mem_Kset hk) kᴴ (mem_UJset_of_mem_Kset hk')` as an intermediate fact. Rewrite `this` using `[show k * kᴴ = 1 from Matrix.mem_unitaryGroup_iff.1 hk.1, hπ.1.1]`. Conclude with `(congrArg (fun A : H →L[ℂ] H => A y) this).symm`. Rewrite using `[← h1, GlobalTheory.KPerp.inner_map_map_of_norm (hπ.2.2.1 k hk)]`. Conclude with `Submodule.inner_right_of_mem_orthogonal (hY _ hk' y hy) hu`.
-/
theorem isKStableOn_orthogonal (hπ : IsAdmRep ε π) {Y : Submodule ℂ H} (hY : IsKStableOn ε π Y) :
    IsKStableOn ε π Yᗮ := by
  intro k hk u hu
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hk' := conjTranspose_mem_Kset hk
  have h1 : π k (π kᴴ y) = y := by
    have := hπ.1.2 k (mem_UJset_of_mem_Kset hk) kᴴ (mem_UJset_of_mem_Kset hk')
    rw [show k * kᴴ = 1 from Matrix.mem_unitaryGroup_iff.1 hk.1, hπ.1.1] at this
    exact (congrArg (fun A : H →L[ℂ] H => A y) this).symm
  rw [← h1, GlobalTheory.KPerp.inner_map_map_of_norm (hπ.2.2.1 k hk)]
  exact Submodule.inner_right_of_mem_orthogonal (hY _ hk' y hy) hu

/- English proof (translation)
Use `le_antisymm (fun v hv => ?_) (le_inf Y.le_topologicalClosure hle)` and prove the remaining obligations. Establish `hZ : Y ⊔ (Yᗮ ⊓ kFinVec ε π) = kFinVec ε π`. Assume the negation of the conclusion as `hne`. Take `⟨a, ha0, ha, hz⟩` from `GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec n ε H π hπ _ (sup_le hle inf_le_right) (fun k hk x hx => by`. Take `⟨y, hy, u, hu, rfl⟩` from `Submodule.mem_sup.1 hx`.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hY k hk y hy) ⟨isKStableOn_orthogonal hπ hY k hk u hu.1, isKStableOn_kFinVec ε π k hk u hu.2⟩) hne`. Establish `haY : a ∈ Yᗮ` using `(Submodule.mem_orthogonal' _ _).2 fun y hy => hz y (Submodule.mem_sup_left hy)`. Conclude with `ha0 (inner_self_eq_zero.1 (hz a (Submodule.mem_sup_right ⟨haY, ha⟩)))`. Take `⟨y, hy, u, hu, rfl⟩` from `Submodule.mem_sup.1 (hZ.symm ▸ hv.2 : v ∈ Y ⊔ (Yᗮ ⊓ kFinVec ε π))`.

Establish `h1 : u ∈ Y.topologicalClosure`. Simplify using `using Y.topologicalClosure.sub_mem hv.1 (Y.le_topologicalClosure hy)`. Rewrite `h1` using `[← Submodule.orthogonal_orthogonal_eq_closure]`. Establish `h2 : u = 0` using `inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hu.1 h1)`. Rewrite using `[h2, add_zero]` and apply the resulting hypothesis.
-/
theorem topologicalClosure_inf_kFinVec [CompleteSpace H] (hπ : IsAdmRep ε π) {Y : Submodule ℂ H}
    (hle : Y ≤ kFinVec ε π) (hY : IsKStableOn ε π Y) : Y.topologicalClosure ⊓ kFinVec ε π = Y := by
  refine le_antisymm (fun v hv => ?_) (le_inf Y.le_topologicalClosure hle)
  have hZ : Y ⊔ (Yᗮ ⊓ kFinVec ε π) = kFinVec ε π := by
    by_contra hne
    obtain ⟨a, ha0, ha, hz⟩ := GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec n ε H π hπ _ (sup_le hle inf_le_right)
      (fun k hk x hx => by
        obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
        rw [map_add]
        exact Submodule.add_mem_sup (hY k hk y hy)
          ⟨isKStableOn_orthogonal hπ hY k hk u hu.1, isKStableOn_kFinVec ε π k hk u hu.2⟩) hne
    have haY : a ∈ Yᗮ := (Submodule.mem_orthogonal' _ _).2 fun y hy => hz y (Submodule.mem_sup_left hy)
    exact ha0 (inner_self_eq_zero.1 (hz a (Submodule.mem_sup_right ⟨haY, ha⟩)))
  obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 (hZ.symm ▸ hv.2 : v ∈ Y ⊔ (Yᗮ ⊓ kFinVec ε π))
  have h1 : u ∈ Y.topologicalClosure := by
    simpa using Y.topologicalClosure.sub_mem hv.1 (Y.le_topologicalClosure hy)
  rw [← Submodule.orthogonal_orthogonal_eq_closure] at h1
  have h2 : u = 0 := inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hu.1 h1)
  rwa [h2, add_zero]

/- English proof (translation)
Introduce `hA n ε H _ _ _ π hπ Y hY`. Use `⟨fun g hg v hv => ?_, topologicalClosure_inf_kFinVec hπ hY.kFin hY.kStable⟩` and prove the remaining obligations. Establish `key : ∀ y ∈ Y, π g y ∈ Y.topologicalClosure`. Introduce `y hy`. Take `⟨k, hk, X, hX, rfl⟩` from `ReciprocityTheory.ChartRestriction.DS.polar_UJ (show g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε from hg)`.

Establish `hk' : k ∈ Kset ε` using `hk`. Establish `hZ` using `conj_mem_lieSet hk' (show X ∈ lieSet ε from hX.1)`. Establish `hky` using `hY.kStable k hk' y hy`. Rewrite using `[mul_exp_eq hk', hπ.1.2 _ (exp_mem_UJset hZ 1) _ (mem_UJset_of_mem_Kset hk'), ContinuousLinearMap.comp_apply, ← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]`. Introduce `w hw`.

Conclude with `inner_exp_eq_zero hπ.1 hY hw hZ hky (GlobalTheory.T.admissible_unitary_K_finite.2 hA n ε H π hπ _ w (hY.kFin _ hky)) 1`. Establish `: Y.topologicalClosure ≤ Y.topologicalClosure.comap (π g : H →ₗ[ℂ] H)` using `Y.topologicalClosure_minimal key (Y.isClosed_topologicalClosure.preimage (π g).continuous)`. Conclude with `this hv`.
-/
theorem topologicalClosure_stable_inf_kFinVec : GlobalTheory.Published.KFiniteCoefficientsAnalytic → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε π → ∀ Y : Submodule ℂ H, IsGKSub ε π Y → (∀ g ∈ UJset ε, ∀ v ∈ Y.topologicalClosure, π g v ∈ Y.topologicalClosure) ∧ Y.topologicalClosure ⊓ kFinVec ε π = Y := by
  intro hA n ε H _ _ _ π hπ Y hY
  refine ⟨fun g hg v hv => ?_, topologicalClosure_inf_kFinVec hπ hY.kFin hY.kStable⟩
  have key : ∀ y ∈ Y, π g y ∈ Y.topologicalClosure := by
    intro y hy
    obtain ⟨k, hk, X, hX, rfl⟩ := ReciprocityTheory.ChartRestriction.DS.polar_UJ (show g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε from hg)
    have hk' : k ∈ Kset ε := hk
    have hZ := conj_mem_lieSet hk' (show X ∈ lieSet ε from hX.1)
    have hky := hY.kStable k hk' y hy
    rw [mul_exp_eq hk', hπ.1.2 _ (exp_mem_UJset hZ 1) _ (mem_UJset_of_mem_Kset hk'),
      ContinuousLinearMap.comp_apply, ← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    exact inner_exp_eq_zero hπ.1 hY hw hZ hky (GlobalTheory.T.admissible_unitary_K_finite.2 hA n ε H π hπ _ w (hY.kFin _ hky)) 1
  have : Y.topologicalClosure ≤ Y.topologicalClosure.comap (π g : H →ₗ[ℂ] H) :=
    Y.topologicalClosure_minimal key (Y.isClosed_topologicalClosure.preimage (π g).continuous)
  exact this hv

end GlobalTheory.GKClosure

end
