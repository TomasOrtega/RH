import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.FixedUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevFixedUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
/- English proof (translation)
Take `⟨q, hq⟩` from `hd`. Establish `h0` using `congrArg (Polynomial.aeval f) hq`. Rewrite `h0` using `[map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]`. Establish `hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple` using `Module.End.isSemisimple_sub_algebraMap_iff.2 hf`. Use `sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)` as an intermediate fact.

Rewrite `this` using `[map_one]`. Then use the resulting hypothesis.
-/
private theorem eq_one_of_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (X - C 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  have := sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
  rwa [map_one] at this
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
/- English proof (translation)
Establish `hs` using `b.semisimple (frob h)`. Establish `htop : ⨆ c, Module.End.eigenspace (b.ρ (frob h)) c = ⊤`. Establish `h1` using `Module.End.iSup_maxGenEigenspace_eq_top (b.ρ (frob h))`. Simplify `h1` using `only [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]`. Choose the witnesses or unpack the hypotheses as in `⟨c, v, hv, hNv⟩ : ∃ c v, v ∈ Module.End.eigenspace (b.ρ (frob h)) c ∧ b.N v ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use `hN (LinearMap.ker_eq_top.1 (top_le_iff.1 ?_))` and prove the remaining obligations. Rewrite using `[← htop]`. Conclude with `iSup_le fun c v hv => hc c v hv`.

Establish `hfv : b.ρ (frob h) v = c • v` using `Module.End.mem_eigenspace_iff.1 hv`. Establish `hv0 : v ≠ 0` using `fun e => hNv (by rw [e, map_zero])`. Establish `root : ∀ z u, u ≠ 0 → b.ρ (frob h) u = z • u → ∃ i, z = (μ i (frob h) : ℂ)` using `fun z u hu e => by`. Establish `h1 : Module.End.HasEigenvalue (b.ρ (frob h)) z` using `Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 e, hu⟩`. Establish `h2` using `Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.1 h1`.

Rewrite `h2` using `[hp, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff]`. Take `⟨i, -, hi⟩` from `h2`. Conclude with `⟨i, by simpa [sub_eq_zero] using hi⟩`. Establish `hc2 : b.ρ (frob h) (b.N v) = (((normV w : ℕ) : ℂ) * c) • b.N v`. Rewrite using `[b.comm_apply, deg_frob, zpow_one, hfv, map_smul, smul_smul]`.

Take `⟨j, hj⟩` from `root _ _ hv0 hfv`. Take `⟨i, hi⟩` from `root _ _ hNv hc2`. Conclude with `⟨i, j, by rw [← hi, ← hj]⟩`.
-/
private theorem link {n m : ℕ} (b : WDRep h (Fin m → ℂ)) (μ : Fin n → Weil h →* ℂˣ)
    (hp : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ))) (hN : b.N ≠ 0) :
    ∃ i j, (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h) := by
  have hs := b.semisimple (frob h)
  have htop : ⨆ c, Module.End.eigenspace (b.ρ (frob h)) c = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top (b.ρ (frob h))
    simpa only [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using h1
  obtain ⟨c, v, hv, hNv⟩ : ∃ c v, v ∈ Module.End.eigenspace (b.ρ (frob h)) c ∧ b.N v ≠ 0 := by
    by_contra hc
    push_neg at hc
    refine hN (LinearMap.ker_eq_top.1 (top_le_iff.1 ?_))
    rw [← htop]
    exact iSup_le fun c v hv => hc c v hv
  have hfv : b.ρ (frob h) v = c • v := Module.End.mem_eigenspace_iff.1 hv
  have hv0 : v ≠ 0 := fun e => hNv (by rw [e, map_zero])
  have root : ∀ z u, u ≠ 0 → b.ρ (frob h) u = z • u → ∃ i, z = (μ i (frob h) : ℂ) := fun z u hu e => by
    have h1 : Module.End.HasEigenvalue (b.ρ (frob h)) z :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 e, hu⟩
    have h2 := Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.1 h1
    rw [hp, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
    obtain ⟨i, -, hi⟩ := h2
    exact ⟨i, by simpa [sub_eq_zero] using hi⟩
  have hc2 : b.ρ (frob h) (b.N v) = (((normV w : ℕ) : ℂ) * c) • b.N v := by
    rw [b.comm_apply, deg_frob, zpow_one, hfv, map_smul, smul_smul]
  obtain ⟨j, hj⟩ := root _ _ hv0 hfv
  obtain ⟨i, hi⟩ := root _ _ hNv hc2
  exact ⟨i, j, by rw [← hi, ← hj]⟩
/- English proof (translation)
Take `⟨t, ht⟩` from `exists_eq_zpow_mul (deg_frob (h := h)) s`. Establish `hv : ∀ k, (μ k s : ℂ) = (μ k (frob h) : ℂ) ^ deg s` using `fun k => by conv_lhs => rw [ht]`. Rewrite using `[map_mul, map_zpow, hu, mul_one, Units.val_zpow_eq_zpow_val]`. Rewrite using `[hv, hv, e, mul_zpow]`.
-/
private theorem link_all {n : ℕ} (μ : Fin n → Weil h →* ℂˣ) (hu : ∀ i (s : Ine (F := E) A), μ i (ineIncl h s) = 1)
    {i j : Fin n} (e : (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h)) (s : Weil h) :
    (μ i s : ℂ) = ((normV w : ℕ) : ℂ) ^ deg s * μ j s := by
  obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
  have hv : ∀ k, (μ k s : ℂ) = (μ k (frob h) : ℂ) ^ deg s := fun k => by
    conv_lhs => rw [ht]
    rw [map_mul, map_zpow, hu, mul_one, Units.val_zpow_eq_zpow_val]
  rw [hv, hv, e, mul_zpow]
end
/- English proof (translation)
Introduce `P F Ω _ _ _ _ _ n w A h rc hrc σ μ hp hu`. Take `⟨a, ha, ε, H⟩` from `_root_.UpperTheory.V.Z.Win.toV' hrc`. Use `haveI : CharZero (w.adicCompletion F) := algebraRat.charZero _`. Establish `hine : ∀ t : Ine (F` using `F) A, (rc (algNorm σ)).charPol (ineIncl h t) = (X - C 1) ^ n := fun t => by`. Rewrite using `[hp]`.

Simplify using `[hu]`. Prove the components needed by the constructor for the conclusion. Establish `hfx : fixed (algNorm σ).rep (iwahori (w.adicCompletion F) (Fin (algNorm σ).1)) ≠ ⊥`. Use `UnramSupport.fixed_iwahori_ne_bot P.litN.loc.geo P.litN.loc.zel P.litN.loc.bz _ _ _ _ (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr fun s hs y hy => ?_` and prove the remaining obligations. Establish `hyc : y.IsCusp` using `hs.isCusp hy`.

Take `⟨m, b, hb, hirr⟩` from `id ((H.cusp y).1 hyc)`. Establish `hN : b.N = 0`. Establish `h0` using `TemperedRec.monodromy_zero_of_irreducible_weilDeligne F Ω A w h (rc y) ((H.cusp y).1 hyc)`. Rewrite `h0` using `[← hb, WD.monodromyZero_ofWeilDeligneRepClass_iff]`. Then use the resulting hypothesis. Establish `hI : ∀ t : Ine (F` using `F) A, b.ρ (ineIncl h t) = 1 := fun t => by`.

Use `eq_one_of_dvd _ (b.semisimple _) (n := n) ?_` and prove the remaining obligations. Rewrite using `[← WD.charPol_mk, hb, ← hine t, H.supp _ s hs]`. Conclude with `Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol (ineIncl h t)) hy)`. Establish `hunr : (rc y).unr`. Rewrite using `[← hb, WD.unr_mk]`.

Conclude with `⟨hN, hI⟩`. Conclude with `isUnramChar_of_isCusp_of_isSpherical P.litN.loc.geo P.litN.loc.bz P.litN.loc.zel _ y hyc ((H.sph y).2 hunr)`. Establish `hfx' : fixed (IrrGL.of σ.ρ σ.smooth σ.irred).rep (iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥` using `GlobalTheory.AboveL.IwaFix.fixed_iwahori_ne_bot_of_twist _ ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _)) hfx`. Conclude with `fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm hfx'`. Introduce `hne`.

Take `⟨m, b, hb⟩` from `(rc (algNorm σ)).exists_rep`. Establish `hpb : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ))` using `fun s => by`. Rewrite using `[← WD.charPol_mk, hb]`. Conclude with `hp s`. Establish `hN : b.N = 0`.

Assume the negation of the conclusion as `h0`. Take `⟨i, j, e⟩` from `link b μ hpb h0`. Take `⟨s, hs⟩` from `hne i j`. Conclude with `hs (link_all μ hu e s)`. Establish `hunr : (rc (algNorm σ)).unr`.

Rewrite using `[← hb, WD.unr_mk]`. Use `⟨hN, fun t => eq_one_of_dvd _ (b.semisimple _) (n := n) ?_⟩` and prove the remaining obligations. Rewrite using `[← WD.charPol_mk, hb, hine t]`. Take `⟨v, hv0, hv⟩` from `UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ le_rfl ((H.sph _).2 hunr)`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.Parabolic.mem_fixed.2 hv, hv0⟩`.
-/
theorem UpperTheory.V.Z.Win.T2.fixedUnr_alt :
    _root_.UpperTheory.V.Lev.fixedUnr_s_ty := by
  intro P F Ω _ _ _ _ _ n w A h rc hrc σ μ hp hu
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  haveI : CharZero (w.adicCompletion F) := algebraRat.charZero _
  have hine : ∀ t : Ine (F := F) A, (rc (algNorm σ)).charPol (ineIncl h t) = (X - C 1) ^ n := fun t => by
    rw [hp]
    simp [hu]
  constructor
  · have hfx : fixed (algNorm σ).rep (iwahori (w.adicCompletion F) (Fin (algNorm σ).1)) ≠ ⊥ := by
      refine UnramSupport.fixed_iwahori_ne_bot P.litN.loc.geo P.litN.loc.zel P.litN.loc.bz _ _ _ _
        (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr fun s hs y hy => ?_
      have hyc : y.IsCusp := hs.isCusp hy
      obtain ⟨m, b, hb, hirr⟩ := id ((H.cusp y).1 hyc)
      have hN : b.N = 0 := by
        have h0 := TemperedRec.monodromy_zero_of_irreducible_weilDeligne F Ω A w h (rc y) ((H.cusp y).1 hyc)
        rwa [← hb, WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
      have hI : ∀ t : Ine (F := F) A, b.ρ (ineIncl h t) = 1 := fun t => by
        refine eq_one_of_dvd _ (b.semisimple _) (n := n) ?_
        rw [← WD.charPol_mk, hb, ← hine t, H.supp _ s hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol (ineIncl h t)) hy)
      have hunr : (rc y).unr := by
        rw [← hb, WD.unr_mk]
        exact ⟨hN, hI⟩
      exact isUnramChar_of_isCusp_of_isSpherical P.litN.loc.geo P.litN.loc.bz P.litN.loc.zel _ y hyc
        ((H.sph y).2 hunr)
    have hfx' : fixed (IrrGL.of σ.ρ σ.smooth σ.irred).rep (iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ :=
      GlobalTheory.AboveL.IwaFix.fixed_iwahori_ne_bot_of_twist _
        ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _)) hfx
    exact fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm hfx'
  · intro hne
    obtain ⟨m, b, hb⟩ := (rc (algNorm σ)).exists_rep
    have hpb : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ)) := fun s => by
      rw [← WD.charPol_mk, hb]
      exact hp s
    have hN : b.N = 0 := by
      by_contra h0
      obtain ⟨i, j, e⟩ := link b μ hpb h0
      obtain ⟨s, hs⟩ := hne i j
      exact hs (link_all μ hu e s)
    have hunr : (rc (algNorm σ)).unr := by
      rw [← hb, WD.unr_mk]
      refine ⟨hN, fun t => eq_one_of_dvd _ (b.semisimple _) (n := n) ?_⟩
      rw [← WD.charPol_mk, hb, hine t]
    obtain ⟨v, hv0, hv⟩ := UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ le_rfl ((H.sph _).2 hunr)
    exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.Parabolic.mem_fixed.2 hv, hv0⟩
end
