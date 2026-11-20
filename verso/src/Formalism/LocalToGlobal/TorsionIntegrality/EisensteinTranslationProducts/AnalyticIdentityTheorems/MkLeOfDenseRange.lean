import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula

open Cardinal Filter Topology

namespace Formalism.L2.Th1.F

namespace Iota

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem mk_le_of_denseRange {D X : Type} [TopologicalSpace X] [FirstCountableTopology X] [T2Space X]
    (f : D → X) (hf : DenseRange f) : #X ≤ #D ^ ℵ₀ := by
  have h : ∀ x : X, ∃ u : ℕ → D, Tendsto (fun n => f (u n)) atTop (𝓝 x) := by
    intro x
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose u hu using hv
    exact ⟨u, by simpa only [hu] using hlim⟩
  choose g hg using h
  have hinj : Function.Injective g := by
    intro x y hxy
    have := hg y
    rw [← hxy] at this
    exact tendsto_nhds_unique (hg x) this
  have := mk_le_of_injective hinj
  simpa using this

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem mk_padic_le (l : ℕ) [Fact l.Prime] : #ℚ_[l] ≤ 𝔠 := by
  have := mk_le_of_denseRange _ (Padic.denseRange_ratCast l)
  simpa using this

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mk_padicAlgCl_le (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) ≤ 𝔠 :=
  (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans
    (max_le (mk_padic_le l) aleph0_le_continuum)

/- English proof (translation)
Establish an intermediate fact. Chain the equalities or inequalities of the calculation.
-/
theorem mk_padicComplex_le (l : ℕ) [Fact l.Prime] : #ℂ_[l] ≤ 𝔠 := by
  have h := mk_le_of_denseRange _ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l))
  calc #ℂ_[l] ≤ #(PadicAlgCl l) ^ ℵ₀ := h
    _ ≤ 𝔠 ^ ℵ₀ := power_le_power_right (mk_padicAlgCl_le l)
    _ = 𝔠 := continuum_power_aleph0

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mk_padicComplex (l : ℕ) [Fact l.Prime] : #ℂ_[l] = 𝔠 :=
  le_antisymm (mk_padicComplex_le l) (continuum_le_cardinal_of_nontriviallyNormedField ℂ_[l])

end Iota

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem iotaExists_thm : IotaExists := by
  intro l _
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero ?_ ?_
  · rw [mk_complex]; exact aleph0_lt_continuum
  · exact Cardinal.eq.1 (by rw [mk_complex, Iota.mk_padicComplex])

end Formalism.L2.Th1.F
