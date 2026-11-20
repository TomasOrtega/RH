import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfEigencharacter

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep PositivityTheory.Rg.BcB.F.Tail.PExp GlobalTheory.CompanionTheory.SubEig

namespace GlobalTheory.CompanionTheory.SubEigIrr

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h k hk`. Use `h ⟨k, hk⟩` as an intermediate fact. Simplify using `using this`. Introduce `h k`.

Simplify using `using h k.1 k.2`.
-/
theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have := h ⟨k, hk⟩
    simpa using this
  · intro h k
    simpa using h k.1 k.2

/- English proof (translation)
Unfold `hkS`. Use `finsum_eq_sum_of_support_subset _ fun q hq => ?_` and prove the remaining obligations. Simplify using `only [Set.Finite.coe_toFinset]`. Introduce `h0`. Conclude with `hq (by simp [h0])`.
-/
theorem hkS_eq_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (f : G → ℂ) (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (v : V) :
    hkS ρ K f v = ∑ q ∈ hf.toFinset, f q.out • ρ q.out v := by
  unfold hkS
  refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
  simp only [Set.Finite.coe_toFinset]
  intro h0
  exact hq (by simp [h0])

/- English proof (translation)
Rewrite using `[hkS_eq_sum ρ K f hf, hkS_eq_sum σ K f hf]`. Use `show φ.toLinearMap _ = _`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`.

Use `congr 1`. Conclude with `φ.isIntertwining _ _ q.out v`.
-/
theorem hkS_map {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : Representation.IntertwiningMap ρ σ)
    (K : Subgroup G) (f : G → ℂ) (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (v : V) :
    φ (hkS ρ K f v) = hkS σ K f (φ v) := by
  rw [hkS_eq_sum ρ K f hf, hkS_eq_sum σ K f hf]
  show φ.toLinearMap _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul]
  congr 1
  exact φ.isIntertwining _ _ q.out v

/- English proof (translation)
Introduce `G _ _ _ V _ _ ρ hρ K X f e hfin u hu hu0 heig`. Set `S` to `cyc ρ u`. Set `u' : S.toSubmodule` to `⟨u, mem_cyc ρ u⟩`. Establish `hu' : u' ≠ 0` using `fun h => hu0 (congrArg Subtype.val h)`. Take `⟨T, huT, hmax⟩` from `exists_max_avoid S.toRepresentation hu'`.

Establish `hst : ∀ g, T.toSubmodule ≤ T.toSubmodule.comap (S.toRepresentation g)` using `fun g _ hv => T.apply_mem_toSubmodule g hv`. Set `τ` to `S.toRepresentation.quotient T.toSubmodule hst`. Establish `hirr : τ.IsIrreducible` using `quot_irred S.toRepresentation T huT hmax (cyc_gen ρ u) hst`. Establish `hsm : IsSmooth τ` using `smooth_quot (smooth_sub hρ S) _ hst`. Set `p` to `mkI S.toRepresentation T.toSubmodule hst`.

Set `w : S.toSubmodule ⧸ T.toSubmodule` to `p u'`. Establish `hw0 : w ≠ 0` using `by show (Submodule.Quotient.mk u' : S.toSubmodule ⧸ T.toSubmodule) ≠ 0`. Rewrite using `[Ne, Submodule.Quotient.mk_eq_zero]` and apply the resulting hypothesis. Establish `hsub : IsSubquotient τ ρ`. Use `⟨S, p, fun y => ?_⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Conclude with `⟨x, rfl⟩`. Use `⟨⟨_, τ, hsm, hirr⟩, hsub, w, ?_, hw0, fun x => ?_⟩` and prove the remaining obligations. Use `mem_fixed_iff.2 fun k hk => ?_` and prove the remaining obligations. Establish `hh' : S.toRepresentation k u' = u'` using `Subtype.ext (mem_fixed_iff.1 hu k hk)`.

Use `p.isIntertwining _ _ k u'` as an intermediate fact. Rewrite `this` using `[hh']`. Conclude with `this.symm`. Establish `h1 : hkS S.toRepresentation K (f x) u' = e x • u'`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `hkS_map (inclI S) K (f x) (hfin x) u'` as an intermediate fact. Conclude with `this.trans (heig x)`. Use `hkS_map p K (f x) (hfin x) u'` as an intermediate fact. Rewrite `this` using `[h1, map_smul]`. Conclude with `this.symm`.
-/
theorem subEig : SubEig := by
  intro G _ _ _ V _ _ ρ hρ K X f e hfin u hu hu0 heig
  let S := cyc ρ u
  let u' : S.toSubmodule := ⟨u, mem_cyc ρ u⟩
  have hu' : u' ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  obtain ⟨T, huT, hmax⟩ := exists_max_avoid S.toRepresentation hu'
  have hst : ∀ g, T.toSubmodule ≤ T.toSubmodule.comap (S.toRepresentation g) :=
    fun g _ hv => T.apply_mem_toSubmodule g hv
  let τ := S.toRepresentation.quotient T.toSubmodule hst
  have hirr : τ.IsIrreducible := quot_irred S.toRepresentation T huT hmax (cyc_gen ρ u) hst
  have hsm : IsSmooth τ := smooth_quot (smooth_sub hρ S) _ hst
  let p := mkI S.toRepresentation T.toSubmodule hst
  let w : S.toSubmodule ⧸ T.toSubmodule := p u'
  have hw0 : w ≠ 0 := by
    show (Submodule.Quotient.mk u' : S.toSubmodule ⧸ T.toSubmodule) ≠ 0
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hsub : IsSubquotient τ ρ := by
    refine ⟨S, p, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨x, rfl⟩
  refine ⟨⟨_, τ, hsm, hirr⟩, hsub, w, ?_, hw0, fun x => ?_⟩
  · refine mem_fixed_iff.2 fun k hk => ?_
    have hh' : S.toRepresentation k u' = u' := Subtype.ext (mem_fixed_iff.1 hu k hk)
    have := p.isIntertwining _ _ k u'
    rw [hh'] at this
    exact this.symm
  · have h1 : hkS S.toRepresentation K (f x) u' = e x • u' := by
      apply Subtype.ext
      have := hkS_map (inclI S) K (f x) (hfin x) u'
      exact this.trans (heig x)
    have := hkS_map p K (f x) (hfin x) u'
    rw [h1, map_smul] at this
    exact this.symm

end GlobalTheory.CompanionTheory.SubEigIrr

end
