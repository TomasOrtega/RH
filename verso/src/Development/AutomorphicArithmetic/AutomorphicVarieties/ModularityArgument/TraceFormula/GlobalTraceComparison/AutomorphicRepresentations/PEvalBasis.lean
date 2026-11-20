import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

/- English proof (translation)
Introduce `X V _ _ ev hsep W hW`. Use `haveI := hW`. Set `r : X → Module.Dual ℂ W` to `fun x => (ev x).domRestrict W`. Establish `hspan : Submodule.span ℂ (Set.range r) = ⊤`. Assume the negation of the conclusion as `hne`.

Take `⟨f, hf0, hf⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Take `⟨v, rfl⟩` from `(Module.evalEquiv ℂ W).surjective f`. Establish `hv : (v : V) = 0` using `hsep v fun x => by`. Establish `h` using `hf (Submodule.subset_span (Set.mem_range_self x))`. Simplify `h` using `[r]`.

Establish `hv0 : v = 0` using `Subtype.ext hv`. Conclude with `hf0 (by simp [hv0])`. Take `⟨b, hbs, hbspan, hli⟩` from `exists_linearIndependent ℂ (Set.range r)`. Set `B0` to `Module.Basis.mk hli (by simp [hbspan, hspan])`. Use `haveI : Finite b := Module.Finite.finite_basis B0`.

Use `letI := Fintype.ofFinite b`. Set `B` to `B0.reindex (Fintype.equivFin b)`. Establish `hx : ∀ i, ∃ x, r x = B i` using `fun i => by`. Establish `hm : B i ∈ b` using `by simp [B, B0]`. Conclude with `hbs hm`.

Use `choose x hx using hx`. Use `⟨Fintype.card b, x, fun i => ((Module.evalEquiv ℂ W).symm (B.coord i) : W), fun i => Subtype.coe_prop _, fun v hv => ?_⟩` and prove the remaining obligations. Establish `key : (⟨v, hv⟩ : W) = ∑ i, (B i ⟨v, hv⟩) • (Module.evalEquiv ℂ W).symm (B.coord i)`. Apply `(Module.evalEquiv ℂ W).injective` to reduce the goal to its premises. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, LinearEquiv.apply_symm_apply]`. Conclude with `(B.sum_dual_apply_smul_coord _).symm`. Establish `h2` using `congrArg (Subtype.val) key`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h2`. Use `h2.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[← hx i]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.evalBasis_pf :
    EvalBasis := by
  intro X V _ _ ev hsep W hW
  classical
  haveI := hW
  let r : X → Module.Dual ℂ W := fun x => (ev x).domRestrict W
  have hspan : Submodule.span ℂ (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ W).surjective f
    have hv : (v : V) = 0 := hsep v fun x => by
      have h := hf (Submodule.subset_span (Set.mem_range_self x))
      simpa [r] using h
    have hv0 : v = 0 := Subtype.ext hv
    exact hf0 (by simp [hv0])
  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent ℂ (Set.range r)
  let B0 := Module.Basis.mk hli (by simp [hbspan, hspan])
  haveI : Finite b := Module.Finite.finite_basis B0
  letI := Fintype.ofFinite b
  let B := B0.reindex (Fintype.equivFin b)
  have hx : ∀ i, ∃ x, r x = B i := fun i => by
    have hm : B i ∈ b := by simp [B, B0]
    exact hbs hm
  choose x hx using hx
  refine ⟨Fintype.card b, x, fun i => ((Module.evalEquiv ℂ W).symm (B.coord i) : W),
    fun i => Subtype.coe_prop _, fun v hv => ?_⟩
  have key : (⟨v, hv⟩ : W) = ∑ i, (B i ⟨v, hv⟩) • (Module.evalEquiv ℂ W).symm (B.coord i) := by
    apply (Module.evalEquiv ℂ W).injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    exact (B.sum_dual_apply_smul_coord _).symm
  have h2 := congrArg (Subtype.val) key
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  refine h2.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [← hx i]
  rfl
