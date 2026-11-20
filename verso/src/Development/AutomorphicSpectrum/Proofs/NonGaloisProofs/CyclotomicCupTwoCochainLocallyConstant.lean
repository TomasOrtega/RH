import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.TopCoh

open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift

/- English proof (translation)
Set `rho : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K) M` to `scalRep M (cycK l K n)`. Establish `hrho : ContAction rho` using `(continuous_of_discreteTopology (f := fun q : ZMod (l ^ n) × M => q.1 • q.2)).comp ((hχ.comp continuous_fst).prodMk continuous_snd)`. Establish `hz2 : z ∈ Z2 (rho.comp (MonoidHom.id _))` using `⟨hz, hcoc⟩`. Establish `hb` using `(hT l K hK n M rho hn hrho).2.2.2.2`. Establish `hzero : cup20 (cycK l K n) rho (MonoidHom.id _) (Submodule.Quotient.mk ⟨z, hz2⟩) = 0`.

Use `LinearMap.ext fun φ => ?_` and prove the remaining obligations. Use `(Submodule.Quotient.mk_eq_zero _).2 ?_` and prove the remaining obligations. Set `φ' : M →ₗ[ZMod (l ^ n)] ZMod (l ^ n)` to `φ.1`. Take `⟨f, hf, hd⟩` from `hchar φ'.toAddMonoidHom`. Conclude with `⟨f, hf, funext fun p => hd p.1 p.2⟩`.

Establish `h0` using `hb.1 (hzero.trans (map_zero _).symm)`. Take `⟨c, hc, hd⟩` from `(Submodule.Quotient.mk_eq_zero _).1 h0`. Conclude with `⟨c, hc, fun g h => congrFun hd (g, h)⟩`.
-/
theorem coboundary_of_characters (hT : LocalTateDualityK) (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (hK : FiniteDimensional ℚ_[l] K) (n : ℕ) (hn : 0 < n)
    (hχ : Continuous fun g => ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (z : Formalism.GaloisCohomology.GK l K × Formalism.GaloisCohomology.GK l K → M) (hz : Continuous z)
    (hcoc : ∀ g h k, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • z (h, k) - z (g * h, k) +
      z (g, h * k) - z (g, h) = 0)
    (hchar : ∀ ψ : M →+ ZMod (l ^ n), ∃ f : Formalism.GaloisCohomology.GK l K → ZMod (l ^ n), Continuous f ∧
      ∀ g h, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * f h - f (g * h) + f g = ψ (z (g, h))) :
    ∃ f : Formalism.GaloisCohomology.GK l K → M, Continuous f ∧
      ∀ g h, ((cycK l K n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • f h - f (g * h) + f g = z (g, h) := by
  let rho : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K) M := scalRep M (cycK l K n)
  have hrho : ContAction rho :=
    (continuous_of_discreteTopology (f := fun q : ZMod (l ^ n) × M => q.1 • q.2)).comp
      ((hχ.comp continuous_fst).prodMk continuous_snd)
  have hz2 : z ∈ Z2 (rho.comp (MonoidHom.id _)) := ⟨hz, hcoc⟩
  have hb := (hT l K hK n M rho hn hrho).2.2.2.2
  have hzero : cup20 (cycK l K n) rho (MonoidHom.id _) (Submodule.Quotient.mk ⟨z, hz2⟩) = 0 := by
    refine LinearMap.ext fun φ => ?_
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    let φ' : M →ₗ[ZMod (l ^ n)] ZMod (l ^ n) := φ.1
    obtain ⟨f, hf, hd⟩ := hchar φ'.toAddMonoidHom
    exact ⟨f, hf, funext fun p => hd p.1 p.2⟩
  have h0 := hb.1 (hzero.trans (map_zero _).symm)
  obtain ⟨c, hc, hd⟩ := (Submodule.Quotient.mk_eq_zero _).1 h0
  exact ⟨c, hc, fun g h => congrFun hd (g, h)⟩

/- English proof (translation)
Introduce `hT D l _ K n χ hn hχ M _ _ _ z hz hcoc hchar`. Take `⟨hΦ1, hΦ2⟩` from `GlobalTheory.Cyc.TwistLift.continuous_fixingSubgroupEquiv K.1`. Set `Ψ : Formalism.GaloisCohomology.GK l K.1 ≃* ↥(GK K)` to `K.1.fixingSubgroupEquiv.symm`. Establish `hΨ : Continuous Ψ` using `hΦ1`. Establish `hΨ' : Continuous Ψ.symm` using `hΦ2`.

Establish `hcyc : IsCyc (D.loc l).χQ` using `(D.loc l).χQ_cyc`. Set `χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ` to `(cyclotomicCharacter (PadicAlgCl l) l).comp (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))`. Establish `hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = ((D.loc l).χQ (Ψ g : GQ l) : ℚ_[l])` using `fun g => by`. Rewrite using `[isCyc_unique hcyc (isCyc_cycChar l)]`. Both sides reduce to the same expression.

Establish `hχc : Continuous fun g => (χZ g : ℤ_[l])`. Rewrite using `[continuous_iff_coe]`. Simplify using `only [hχZ]`. Conclude with `hcyc.continuous.comp (continuous_subtype_val.comp hΨ)`. Establish `hval : ∀ g : Formalism.GaloisCohomology.GK l K.1, (χ (Ψ g) : ZMod (l ^ n)) = (Formalism.GaloisCohomology.cycK l K.1 n g : ZMod (l ^ n))` using `fun g => by`.

Take `⟨u, hu, hu'⟩` from `hχ (Ψ g)`. Rewrite `hu` using `[(D.loc l).PD_χ K (Ψ g), ← hχZ]`. Rewrite using `[← hu', show u = (χZ g : ℤ_[l]) from Subtype.ext hu]`. Both sides reduce to the same expression. Use `letI : TopologicalSpace M := ⊥`.

Use `haveI : DiscreteTopology M := ⟨rfl⟩`. Take `⟨c, hc, hd⟩` from `coboundary_of_characters hT l K.1 K.2 n hn ((continuous_toZModPow n).comp hχc) M (fun p => z (Ψ p.1, Ψ p.2)) (hz.continuous.comp (hΨ.prodMap hΨ)) (fun g h k => by`. Use `hcoc (Ψ g) (Ψ h) (Ψ k)` as an intermediate fact. Rewrite `this` using `[hval, ← map_mul Ψ, ← map_mul Ψ]`. Conclude with `this)`.

Use the proof step `(fun ψ => by`. Take `⟨f, hf, hd⟩` from `hchar ψ`. Use `⟨fun g => f (Ψ g), hf.continuous.comp hΨ, fun g h => ?_⟩` and prove the remaining obligations. Use `hd (Ψ g) (Ψ h)` as an intermediate fact. Rewrite `this` using `[hval, ← map_mul Ψ]`.

Conclude with `this)`. Use `⟨fun g => c (Ψ.symm g), (IsLocallyConstant.iff_continuous _).2 (hc.comp hΨ'), fun g h => ?_⟩` and prove the remaining obligations. Use `hd (Ψ.symm g) (Ψ.symm h)` as an intermediate fact. Rewrite `this` using `[← map_mul Ψ.symm, ← hval]`. Simplify using `using this`.
-/
theorem coboundary_of_characters_GK : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (n : ℕ) (χ : ↥(GK K) →* (ZMod (l ^ n))ˣ), 0 < n → (∀ g, ∃ u : ℤ_[l], (u : ℚ_[l]) = ((((D.loc l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧ PadicInt.toZModPow n u = (χ g : ZMod (l ^ n))) → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] (z : ↥(GK K) × ↥(GK K) → M), IsLocallyConstant z → (∀ g h k, (χ g : ZMod (l ^ n)) • z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → (∀ ψ : M →+ ZMod (l ^ n), ∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = ψ (z (g, h))) → ∃ f : ↥(GK K) → M, IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) • f h - f (g * h) + f g = z (g, h) := by
  intro hT D l _ K n χ hn hχ M _ _ _ z hz hcoc hchar
  obtain ⟨hΦ1, hΦ2⟩ := GlobalTheory.Cyc.TwistLift.continuous_fixingSubgroupEquiv K.1
  let Ψ : Formalism.GaloisCohomology.GK l K.1 ≃* ↥(GK K) := K.1.fixingSubgroupEquiv.symm
  have hΨ : Continuous Ψ := hΦ1
  have hΨ' : Continuous Ψ.symm := hΦ2
  have hcyc : IsCyc (D.loc l).χQ := (D.loc l).χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = ((D.loc l).χQ (Ψ g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΨ)
  have hval : ∀ g : Formalism.GaloisCohomology.GK l K.1,
      (χ (Ψ g) : ZMod (l ^ n)) = (Formalism.GaloisCohomology.cycK l K.1 n g : ZMod (l ^ n)) := fun g => by
    obtain ⟨u, hu, hu'⟩ := hχ (Ψ g)
    rw [(D.loc l).PD_χ K (Ψ g), ← hχZ] at hu
    rw [← hu', show u = (χZ g : ℤ_[l]) from Subtype.ext hu]
    rfl
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  obtain ⟨c, hc, hd⟩ := coboundary_of_characters hT l K.1 K.2 n hn
    ((continuous_toZModPow n).comp hχc) M (fun p => z (Ψ p.1, Ψ p.2))
    (hz.continuous.comp (hΨ.prodMap hΨ))
    (fun g h k => by
      have := hcoc (Ψ g) (Ψ h) (Ψ k)
      rw [hval, ← map_mul Ψ, ← map_mul Ψ] at this
      exact this)
    (fun ψ => by
      obtain ⟨f, hf, hd⟩ := hchar ψ
      refine ⟨fun g => f (Ψ g), hf.continuous.comp hΨ, fun g h => ?_⟩
      have := hd (Ψ g) (Ψ h)
      rw [hval, ← map_mul Ψ] at this
      exact this)
  refine ⟨fun g => c (Ψ.symm g), (IsLocallyConstant.iff_continuous _).2 (hc.comp hΨ'), fun g h => ?_⟩
  have := hd (Ψ.symm g) (Ψ.symm h)
  rw [← map_mul Ψ.symm, ← hval] at this
  simpa using this

end GlobalTheory.CompanionTheory.LocDual.TopCoh
