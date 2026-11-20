import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

/- English proof (translation)
Introduce `k k' _ _ _ J e M N _ _ _ _ ψ hψ I c`. Set `T : (I →₀ k') ≃+ (J →₀ M)` to `(Finsupp.mapRange.addEquiv e.repr.toAddEquiv).trans ((Finsupp.curryAddEquiv).symm.trans ((Finsupp.domCongr (Equiv.prodComm I J)).trans (Finsupp.curryAddEquiv.trans (Finsupp.mapRange.addEquiv c.repr.symm.toAddEquiv))))`. Establish `hTs : ∀ (i : I) (a : k'), T (Finsupp.single i a) = Finsupp.mapRange (fun b : k => b • c i) (zero_smul k _) (e.repr a)`. Introduce `i a`. Use extensionality with `j`.

Simplify using `only [Finsupp.mapRange_apply]`. Simplify using `[T, Finsupp.curryAddEquiv]`. Establish `h : ((Finsupp.equivMapDomain (Equiv.prodComm I J) (Finsupp.single i (e.repr a)).uncurry).curry j) = Finsupp.single i (e.repr a j)`. Use extensionality with `i'`. Simplify using `only [Finsupp.curry_apply, Finsupp.equivMapDomain_apply, Finsupp.uncurry_apply]`.

Rewrite using `[Finsupp.single_apply, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> simp_all`. Rewrite using `[h, Finsupp.linearCombination_single]`. Establish `hbc : ∀ f : J →₀ M, bcSum e ψ f = f.sum (fun j m => e j • ψ m)`. Introduce `f`.

Simplify using `[bcSum]`. Both sides reduce to the same expression. Set `Φ : (I →₀ k') →ₗ[k'] N` to `Finsupp.linearCombination k' (fun i => ψ (c i))`. Establish `key : ∀ g, Φ g = bcSum e ψ (T g)`. Introduce `g`.

Proceed by induction on `g using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg => rw [map_add, map_add, map_add, hf, hg]`. Consider the case `single i a`. Rewrite using `[hTs, hbc, Finsupp.sum_mapRange_index (by intro j; simp)]`.

Simplify using `only [Φ, Finsupp.linearCombination_single]`. Use `conv_lhs => rw [← e.linearCombination_repr a, Finsupp.linearCombination_apply]`. Rewrite using `[Finsupp.sum, Finsupp.sum, Finset.sum_smul]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, Algebra.smul_def, mul_comm, mul_smul]`.

Establish `hΦ : Function.Bijective Φ`. Establish `h : (Φ : (I →₀ k') → N) = bcSum e ψ ∘ T` using `funext key`. Rewrite using `[h]`. Conclude with `hψ.comp T.bijective`. Set `E` to `LinearEquiv.ofBijective Φ hΦ`.

Use `⟨Module.Basis.ofRepr E.symm, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.coe_ofRepr]`. Simplify using `[E, Φ]`.
-/
theorem UpperTheory.Gal.G3.jHBasis :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_basis := by
  classical
  intro k k' _ _ _ J e M N _ _ _ _ ψ hψ I c
  let T : (I →₀ k') ≃+ (J →₀ M) :=
    (Finsupp.mapRange.addEquiv e.repr.toAddEquiv).trans ((Finsupp.curryAddEquiv).symm.trans
      ((Finsupp.domCongr (Equiv.prodComm I J)).trans
        (Finsupp.curryAddEquiv.trans (Finsupp.mapRange.addEquiv c.repr.symm.toAddEquiv))))
  have hTs : ∀ (i : I) (a : k'),
      T (Finsupp.single i a) = Finsupp.mapRange (fun b : k => b • c i) (zero_smul k _) (e.repr a) := by
    intro i a
    ext j
    simp only [Finsupp.mapRange_apply]
    simp [T, Finsupp.curryAddEquiv]
    have h : ((Finsupp.equivMapDomain (Equiv.prodComm I J) (Finsupp.single i (e.repr a)).uncurry).curry j)
        = Finsupp.single i (e.repr a j) := by
      ext i'
      simp only [Finsupp.curry_apply, Finsupp.equivMapDomain_apply, Finsupp.uncurry_apply]
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp_all
    rw [h, Finsupp.linearCombination_single]
  have hbc : ∀ f : J →₀ M, bcSum e ψ f = f.sum (fun j m => e j • ψ m) := by
    intro f
    simp [bcSum]; rfl
  let Φ : (I →₀ k') →ₗ[k'] N := Finsupp.linearCombination k' (fun i => ψ (c i))
  have key : ∀ g, Φ g = bcSum e ψ (T g) := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
    | single i a =>
      rw [hTs, hbc, Finsupp.sum_mapRange_index (by intro j; simp)]
      simp only [Φ, Finsupp.linearCombination_single]
      conv_lhs => rw [← e.linearCombination_repr a, Finsupp.linearCombination_apply]
      rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smulₛₗ, Algebra.smul_def, mul_comm, mul_smul]
  have hΦ : Function.Bijective Φ := by
    have h : (Φ : (I →₀ k') → N) = bcSum e ψ ∘ T := funext key
    rw [h]
    exact hψ.comp T.bijective
  let E := LinearEquiv.ofBijective Φ hΦ
  refine ⟨Module.Basis.ofRepr E.symm, fun i => ?_⟩
  rw [Module.Basis.coe_ofRepr]
  simp [E, Φ]
