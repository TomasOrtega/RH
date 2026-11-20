import Mathlib

noncomputable section
open Cardinal Filter Topology

namespace ReciprocityTheory.ChartRestriction.T1

/- English proof (translation)
Establish `hseq : ∀ x : X, ∃ u : ℕ → D, Tendsto (f ∘ u) atTop (𝓝 x)`. Introduce `x`. Establish `hx : x ∈ closure (Set.range f)` using `by rw [hf.closure_range]; exact Set.mem_univ x`. Take `⟨v, hv, hlim⟩` from `mem_closure_iff_seq_limit.1 hx`. Use `choose u hu using hv`.

Use `⟨u, ?_⟩` and prove the remaining obligations. Establish `hfu : f ∘ u = v` using `funext hu`. Rewrite using `[hfu]`. Conclude with `hlim`. Use `choose g hg using hseq`.

Establish `hinj : Function.Injective g`. Introduce `x y hxy`. Establish `h' : Tendsto (f ∘ g x) atTop (𝓝 y)` using `by rw [hxy]; exact hg y`. Conclude with `tendsto_nhds_unique (hg x) h'`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lat_mk_le_of_denseRange {D X : Type} [TopologicalSpace X] [FirstCountableTopology X] [T2Space X]
    (f : D → X) (hf : DenseRange f) : #X ≤ #D ^ ℵ₀ := by
  classical
  have hseq : ∀ x : X, ∃ u : ℕ → D, Tendsto (f ∘ u) atTop (𝓝 x) := by
    intro x
    have hx : x ∈ closure (Set.range f) := by rw [hf.closure_range]; exact Set.mem_univ x
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 hx
    choose u hu using hv
    refine ⟨u, ?_⟩
    have hfu : f ∘ u = v := funext hu
    rw [hfu]
    exact hlim
  choose g hg using hseq

  have hinj : Function.Injective g := by
    intro x y hxy
    have h' : Tendsto (f ∘ g x) atTop (𝓝 y) := by rw [hxy]; exact hg y
    exact tendsto_nhds_unique (hg x) h'
  calc Cardinal.mk X ≤ Cardinal.mk (ℕ → D) := Cardinal.mk_le_of_injective hinj
    _ = Cardinal.mk D ^ ℵ₀ := by rw [← Cardinal.mk_nat, Cardinal.power_def]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `h1 : Cardinal.mk ℚ_[p] ≤ 𝔠`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Cardinal.mk (PadicAlgCl p) ≤ 𝔠` using `(Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans (max_le h1 Cardinal.aleph0_le_continuum)`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨g, -, -, hg⟩` from `Perfect.exists_nat_bool_injection (C := (Set.univ : Set ℂ_[p])) ⟨isClosed_univ, PerfectSpace.univ_preperfect⟩ ⟨0, trivial⟩`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Cardinal.two_power_aleph0, ← Cardinal.mk_nat, ← Cardinal.mk_bool, Cardinal.power_def]`. Use `_ ≤ Cardinal.mk ℂ_[p] := Cardinal.mk_le_of_injective hg`.
-/
theorem lat_mk_Cp (p : ℕ) [Fact p.Prime] : #ℂ_[p] = 𝔠 := by
  apply le_antisymm
  · have h1 : Cardinal.mk ℚ_[p] ≤ 𝔠 := by
      calc Cardinal.mk ℚ_[p] ≤ Cardinal.mk ℚ ^ ℵ₀ :=
            lat_mk_le_of_denseRange ((↑) : ℚ → ℚ_[p]) (Padic.denseRange_ratCast p)
        _ = 𝔠 := by rw [Cardinal.mkRat, Cardinal.aleph0_power_aleph0]
    have h2 : Cardinal.mk (PadicAlgCl p) ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans
        (max_le h1 Cardinal.aleph0_le_continuum)
    calc Cardinal.mk ℂ_[p] ≤ Cardinal.mk (PadicAlgCl p) ^ ℵ₀ :=
          lat_mk_le_of_denseRange ((↑) : PadicAlgCl p → ℂ_[p]) UniformSpace.Completion.denseRange_coe
      _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right h2
      _ = 𝔠 := Cardinal.continuum_power_aleph0
  ·
    obtain ⟨g, -, -, hg⟩ := Perfect.exists_nat_bool_injection (C := (Set.univ : Set ℂ_[p]))
      ⟨isClosed_univ, PerfectSpace.univ_preperfect⟩ ⟨0, trivial⟩
    calc 𝔠 = Cardinal.mk (ℕ → Bool) := by
          rw [← Cardinal.two_power_aleph0, ← Cardinal.mk_nat, ← Cardinal.mk_bool, Cardinal.power_def]
      _ ≤ Cardinal.mk ℂ_[p] := Cardinal.mk_le_of_injective hg

end ReciprocityTheory.ChartRestriction.T1

namespace ReciprocityTheory.ChartRestriction.B3

/- English proof (translation)
Use `letI : Algebra R K := f.toAlgebra`. Use `letI : Algebra R L := g.toAlgebra`. Use `haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 f.injective`. Use `haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 g.injective`. Take `⟨s, hs⟩` from `exists_isTranscendenceBasis R K`.

Take `⟨t, ht⟩` from `exists_isTranscendenceBasis R L`. Establish `h1` using `IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs hR hK`. Establish `h2` using `IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hR (hKL ▸ hK)`. Simplify using `only [Cardinal.lift_id] at h1 h2`. Establish `hst : Cardinal.mk s = Cardinal.mk t` using `by rw [← h1, ← h2, hKL]`.

Take `⟨e⟩` from `Cardinal.eq.1 hst`. Use `letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs`. Use `letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht`. Set `eA : Algebra.adjoin R (Set.range (Subtype.val : s → K)) ≃ₐ[R] Algebra.adjoin R (Set.range (Subtype.val : t → L))` to `hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)`. Use `⟨IsAlgClosure.equivOfEquiv K L eA.toRingEquiv, fun r => ?_⟩` and prove the remaining obligations.

Establish `e1 : f r = algebraMap (Algebra.adjoin R (Set.range (Subtype.val : s → K))) K (algebraMap R _ r)` using `rfl`. Establish `e2 : g r = algebraMap (Algebra.adjoin R (Set.range (Subtype.val : t → L))) L (algebraMap R _ r)` using `rfl`. Rewrite using `[e1, IsAlgClosure.equivOfEquiv_algebraMap, e2]`. Use `congr 1`. Conclude with `eA.commutes r`.
-/
theorem iop_extEmb {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  letI : Algebra R K := f.toAlgebra
  letI : Algebra R L := g.toAlgebra
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 f.injective
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 g.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L

  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs hR hK
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hR (hKL ▸ hK)
  simp only [Cardinal.lift_id] at h1 h2
  have hst : Cardinal.mk s = Cardinal.mk t := by rw [← h1, ← h2, hKL]
  obtain ⟨e⟩ := Cardinal.eq.1 hst
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let eA : Algebra.adjoin R (Set.range (Subtype.val : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range (Subtype.val : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L eA.toRingEquiv, fun r => ?_⟩
  have e1 : f r = algebraMap (Algebra.adjoin R (Set.range (Subtype.val : s → K))) K
      (algebraMap R _ r) := rfl
  have e2 : g r = algebraMap (Algebra.adjoin R (Set.range (Subtype.val : t → L))) L
      (algebraMap R _ r) := rfl
  rw [e1, IsAlgClosure.equivOfEquiv_algebraMap, e2]
  congr 1
  exact eA.commutes r

end ReciprocityTheory.ChartRestriction.B3
