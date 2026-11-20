import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Rewrite using `[(h4 n N h lam).2]`. Use `iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.map_le_iff_le_comap]`. Introduce `s hs`. Conclude with `hP mu hmu φ hφ s hs`.
-/
theorem nablaSq_le_of_gen (h4 : PI.GTBranch) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N)
    (P : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hP : ∀ (mu : DomWeight n), Interlace h lam mu →
      ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
        ∀ s ∈ nablaSq ℂ n mu, φ s ∈ P) :
    nablaSq ℂ N lam ≤ P := by
  rw [(h4 n N h lam).2]
  refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
  rw [Submodule.map_le_iff_le_comap]
  intro s hs
  exact hP mu hmu φ hφ s hs

/- English proof (translation)
Establish `hterm : ∀ ω : Fin n → ℕ, Z (weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s))) = z • weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s))`. Introduce `ω`. Establish `hc : weightedHomogeneousComponent (rowW n n) ω s ∈ nablaSq ℂ n mu` using `dualWeylRowGraded ℂ n n mu.natW ω s hs`. Establish `hhom : IsWeightedHomogeneous (rowW N N) (φ (weightedHomogeneousComponent (rowW n n) ω s)) (liftWt h lam mu ω)` using `hW n N h lam mu hmu φ hφ ω _ hc (weightedHomogeneousComponent_isWeightedHomogeneous ω s)`. Distinguish the cases in `hν : ν = liftWt h lam mu ω`.

Substitute `hν` using the available equality. Rewrite using `[hhom.weightedHomogeneousComponent_same]`. Conclude with `hz _ hc`. Rewrite using `[hhom.weightedHomogeneousComponent_ne ν hν, map_zero, smul_zero]`. Establish `hsum : s = ∑ ω ∈ (weightedHomogeneousComponent_finsupp (w` using `rowW n n) s).toFinset, weightedHomogeneousComponent (rowW n n) ω s := by conv_lhs => rw [← finsum_weightedHomogeneousComponent (rowW n n) s]`.

Conclude with `finsum_eq_sum _ _`. Rewrite using `[hz s hs, map_smul]`. Use `conv_lhs => rw [hsum]`. Use `conv_rhs => rw [hsum]`. Simplify using `only [map_sum, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun ω _ => hterm ω`.
-/
theorem comp_gen (hW : EqvRowWt) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (hmu : Interlace h lam mu)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (Z : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (z : ℂ)
    (hz : ∀ s ∈ nablaSq ℂ n mu, Z (φ s) = z • φ s) (ν : Fin N → ℕ) (s : MvPolynomial (Fin n × Fin n) ℂ)
    (hs : s ∈ nablaSq ℂ n mu) :
    Z (weightedHomogeneousComponent (rowW N N) ν (φ s)) =
      weightedHomogeneousComponent (rowW N N) ν (Z (φ s)) := by

  have hterm : ∀ ω : Fin n → ℕ,
      Z (weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s))) =
        z • weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s)) := by
    intro ω
    have hc : weightedHomogeneousComponent (rowW n n) ω s ∈ nablaSq ℂ n mu :=
      dualWeylRowGraded ℂ n n mu.natW ω s hs
    have hhom : IsWeightedHomogeneous (rowW N N)
        (φ (weightedHomogeneousComponent (rowW n n) ω s)) (liftWt h lam mu ω) :=
      hW n N h lam mu hmu φ hφ ω _ hc (weightedHomogeneousComponent_isWeightedHomogeneous ω s)
    by_cases hν : ν = liftWt h lam mu ω
    · subst hν
      rw [hhom.weightedHomogeneousComponent_same]
      exact hz _ hc
    · rw [hhom.weightedHomogeneousComponent_ne ν hν, map_zero, smul_zero]
  have hsum : s = ∑ ω ∈ (weightedHomogeneousComponent_finsupp (w := rowW n n) s).toFinset,
      weightedHomogeneousComponent (rowW n n) ω s := by
    conv_lhs => rw [← finsum_weightedHomogeneousComponent (rowW n n) s]
    exact finsum_eq_sum _ _
  rw [hz s hs, map_smul]
  conv_lhs => rw [hsum]
  conv_rhs => rw [hsum]
  simp only [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun ω _ => hterm ω

/- English proof (translation)
Introduce `n N h lam Z hZ`. Establish `hcomp : ∀ ν : Fin N → ℕ, ∀ f ∈ nablaSq ℂ N lam, Z (weightedHomogeneousComponent (rowW N N) ν f) = weightedHomogeneousComponent (rowW N N) ν (Z f)`. Introduce `ν f hf`. Establish `hle` using `nablaSq_le_of_gen h4 h lam (LinearMap.eqLocus (Z ∘ₗ weightedHomogeneousComponent (rowW N N) ν) (weightedHomogeneousComponent (rowW N N) ν ∘ₗ Z)) (by`. Introduce `mu hmu φ hφ s hs`.

Take `⟨z, hz⟩` from `hZ mu hmu φ hφ`. Rewrite using `[LinearMap.mem_eqLocus]`. Conclude with `comp_gen hW h lam mu hmu φ hφ Z z hz ν s hs)`. Use `hle hf` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_eqLocus]`.

Conclude with `this`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf`. Establish `hle` using `nablaSq_le_of_gen h4 h lam ((nablaSq ℂ N lam).comap Z) (by`. Introduce `mu hmu φ hφ s hs`.

Take `⟨z, hz⟩` from `hZ mu hmu φ hφ`. Rewrite using `[Submodule.mem_comap, hz s hs]`. Conclude with `Submodule.smul_mem _ z (hφ.1 s hs))`. Conclude with `hle hf`. Introduce `a b hab k f hf`.

Establish `hle` using `nablaSq_le_of_gen h4 h lam (LinearMap.eqLocus (Z ∘ₗ rowDivL ℂ (eRow h a) (eRow h b) k) (rowDivL ℂ (eRow h a) (eRow h b) k ∘ₗ Z)) (by`. Introduce `mu hmu φ hφ s hs`. Take `⟨z, hz⟩` from `hZ mu hmu φ hφ`. Rewrite using `[LinearMap.mem_eqLocus]`. Simplify using `only [LinearMap.comp_apply, rowDivL_apply]`.

Establish `hs' : rowDiv ℂ a b k s ∈ nablaSq ℂ n mu` using `rowDivStable ℂ n n mu.natW a b k s hs`. Rewrite using `[← hD n N h mu lam φ hφ a b hab k s hs, hz _ hs', hz s hs, rowDiv_smul, hD n N h mu lam φ hφ a b hab k s hs])`. Use `hle hf` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_eqLocus]`. Simplify `this` using `only [LinearMap.comp_apply, rowDivL_apply]`.

Introduce `ω f hf hhom`. Rewrite using `[← hhom.weightedHomogeneousComponent_same, hcomp ω f hf]`. Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous ω _`.
-/
theorem zComm_of (h4 : PI.GTBranch) (hD : EqvDiv) (hW : EqvRowWt) : ZComm := by
  intro n N h lam Z hZ

  have hcomp : ∀ ν : Fin N → ℕ, ∀ f ∈ nablaSq ℂ N lam,
      Z (weightedHomogeneousComponent (rowW N N) ν f) = weightedHomogeneousComponent (rowW N N) ν (Z f) := by
    intro ν f hf
    have hle := nablaSq_le_of_gen h4 h lam
      (LinearMap.eqLocus (Z ∘ₗ weightedHomogeneousComponent (rowW N N) ν)
        (weightedHomogeneousComponent (rowW N N) ν ∘ₗ Z)) (by
        intro mu hmu φ hφ s hs
        obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
        rw [LinearMap.mem_eqLocus]
        exact comp_gen hW h lam mu hmu φ hφ Z z hz ν s hs)
    have := hle hf
    rw [LinearMap.mem_eqLocus] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    have hle := nablaSq_le_of_gen h4 h lam ((nablaSq ℂ N lam).comap Z) (by
      intro mu hmu φ hφ s hs
      obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
      rw [Submodule.mem_comap, hz s hs]
      exact Submodule.smul_mem _ z (hφ.1 s hs))
    exact hle hf
  · intro a b hab k f hf
    have hle := nablaSq_le_of_gen h4 h lam
      (LinearMap.eqLocus (Z ∘ₗ rowDivL ℂ (eRow h a) (eRow h b) k)
        (rowDivL ℂ (eRow h a) (eRow h b) k ∘ₗ Z)) (by
        intro mu hmu φ hφ s hs
        obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
        rw [LinearMap.mem_eqLocus]
        simp only [LinearMap.comp_apply, rowDivL_apply]
        have hs' : rowDiv ℂ a b k s ∈ nablaSq ℂ n mu := rowDivStable ℂ n n mu.natW a b k s hs
        rw [← hD n N h mu lam φ hφ a b hab k s hs, hz _ hs', hz s hs, rowDiv_smul,
          hD n N h mu lam φ hφ a b hab k s hs])
    have := hle hf
    rw [LinearMap.mem_eqLocus] at this
    simpa only [LinearMap.comp_apply, rowDivL_apply] using this
  · intro ω f hf hhom
    rw [← hhom.weightedHomogeneousComponent_same, hcomp ω f hf]
    exact weightedHomogeneousComponent_isWeightedHomogeneous ω _

end PI.WGL
