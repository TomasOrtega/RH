import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasisStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.FinCoc

section Generic

variable {G LL O V : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V]
  [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}

/- English proof (translation)
Take `⟨t, rfl⟩` from `Submodule.Quotient.mk_surjective _ m`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (actT L 1 t) = Submodule.Quotient.mk t`. Use `congr 1`. Conclude with `Subtype.ext (by simp [actT])`.
-/
theorem actQ_one' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (m : ↥L.T ⧸ I) :
    actQ L I hI 1 m = m := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L 1 t) = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext (by simp [actT])

/- English proof (translation)
Take `⟨t, rfl⟩` from `Submodule.Quotient.mk_surjective _ m`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (actT L (g * h) t) = Submodule.Quotient.mk (actT L g (actT L h t))`. Use `congr 1`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ρ (g * h) (t : V) = ρ g (ρ h (t : V))`.

Simplify using the standard rewrite rules.
-/
theorem actQ_mul' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (g h : G)
    (m : ↥L.T ⧸ I) : actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L (g * h) t) = Submodule.Quotient.mk (actT L g (actT L h t))
  congr 1
  refine Subtype.ext ?_
  change ρ (g * h) (t : V) = ρ g (ρ h (t : V))
  simp

/- English proof (translation)
Take `⟨t, rfl⟩` from `Submodule.Quotient.mk_surjective _ m`. Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.1 hn`. Rewrite using `[← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Establish `hc : ((n ^ r : ℕ) : O) = ϖ ^ r * u ^ r`. Rewrite using `[Nat.cast_pow, ← hu, mul_pow, mul_comm]`.

Rewrite using `[hc, mul_smul]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top`.
-/
theorem pow_nsmul_quot (L : Lattice (O := O) ρ) {ϖ : O} {n : ℕ} (hn : (n : O) ∈ Ideal.span {ϖ}) (r : ℕ)
    (m : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) : n ^ r • m = 0 := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hn
  rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hc : ((n ^ r : ℕ) : O) = ϖ ^ r * u ^ r := by
    rw [Nat.cast_pow, ← hu, mul_pow, mul_comm]
  rw [hc, mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

variable [TopologicalSpace V] [ContinuousAdd V]

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `hc : Continuous fun y : ↥L.T => (y : V) + -(x : V)` using `continuous_subtype_val.add continuous_const`. Establish `hev` using `hc.continuousAt.eventually_mem (x := x) (s := (fun x => ϖ ^ r • x) '' (L.T : Set V)) (by simpa using hW)`. Use `filter_upwards [hev] with y hy`.

Take `⟨t, ht, h⟩` from `hy`. Rewrite using `[Submodule.Quotient.eq]`. Establish `hxy : y - x = ϖ ^ r • (⟨t, ht⟩ : ↥L.T)` using `Subtype.ext (by simpa [sub_eq_add_neg] using h.symm)`. Rewrite using `[hxy]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top`.
-/
theorem mk_isLocallyConstant (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ}
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V)) :
    IsLocallyConstant (fun x : ↥L.T =>
      (Submodule.Quotient.mk x : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : ↥L.T => (y : V) + -(x : V) :=
    continuous_subtype_val.add continuous_const
  have hev := hc.continuousAt.eventually_mem (x := x)
    (s := (fun x => ϖ ^ r • x) '' (L.T : Set V)) (by simpa using hW)
  filter_upwards [hev] with y hy
  obtain ⟨t, ht, h⟩ := hy
  rw [Submodule.Quotient.eq]
  have hxy : y - x = ϖ ^ r • (⟨t, ht⟩ : ↥L.T) :=
    Subtype.ext (by simpa [sub_eq_add_neg] using h.symm)
  rw [hxy]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

/- English proof (translation)
Establish `hcs : CompactSpace ↥L.T` using `isCompact_iff_compactSpace.1 hC`. Use `Set.finite_univ_iff.1 ?_` and prove the remaining obligations. Rewrite using `[← (Submodule.Quotient.mk_surjective _).range_eq]`. Conclude with `(mk_isLocallyConstant L hW).range_finite`.
-/
theorem finite_quot (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ} (hC : IsCompact (L.T : Set V))
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V)) :
    Finite (↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) := by
  have hcs : CompactSpace ↥L.T := isCompact_iff_compactSpace.1 hC
  refine Set.finite_univ_iff.1 ?_
  rw [← (Submodule.Quotient.mk_surjective _).range_eq]
  exact (mk_isLocallyConstant L hW).range_finite

/- English proof (translation)
Take `⟨t, rfl⟩` from `Submodule.Quotient.mk_surjective _ m`. Establish `hc : Continuous fun g : G => actT L g t` using `(hcont (t : V)).subtype_mk _`. Conclude with `(mk_isLocallyConstant L hW).comp_continuous hc`.
-/
theorem actQ_isLocallyConstant [TopologicalSpace G] (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ}
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V))
    (hcont : ∀ x, Continuous fun g => ρ g x)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (m : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) :
    IsLocallyConstant fun g => actQ L _ hI g m := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have hc : Continuous fun g : G => actT L g t := (hcont (t : V)).subtype_mk _
  exact (mk_isLocallyConstant L hW).comp_continuous hc

end Generic

/- English proof (translation)
Introduce `hT hE D l _ K LL _ _ _ O _ _ hg A LA ϖ hϖ r hI`. Take `⟨-, -, -, ⟨-, hl, -⟩, -, -⟩` from `GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hg ϖ hϖ`. Take `⟨-, hB, hC, -, -⟩` from `GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hg A LA ϖ hϖ`. Establish `hW : (fun x => ϖ ^ r • x) '' (LA.T : Set A.V) ∈ nhds (0 : A.V)` using `hB.mem_of_mem trivial`. Establish `hMfin` using `finite_quot LA hC hW`.

Establish `hfin` using `GlobalTheory.CocycleCount.cocycles_finite_ncard_le hT hE l K r _ (fun g => (actQ LA _ hI g).toAddMonoidHom) (actQ_one' LA _ hI) (fun g h m => actQ_mul' LA _ hI g h m) (pow_nsmul_quot LA hl r) (actQ_isLocallyConstant LA hW A.cont hI)`. Conclude with `hfin.1.to_subtype`.
-/
theorem finZQ_of_duality : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), FinZQ ((D.loc l).PD K) := by
  intro hT hE D l _ K LL _ _ _ O _ _ hg A LA ϖ hϖ r hI
  obtain ⟨-, -, -, ⟨-, hl, -⟩, -, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hg ϖ hϖ
  obtain ⟨-, hB, hC, -, -⟩ := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hg A LA ϖ hϖ
  have hW : (fun x => ϖ ^ r • x) '' (LA.T : Set A.V) ∈ nhds (0 : A.V) := hB.mem_of_mem trivial
  have hMfin := finite_quot LA hC hW
  have hfin := GlobalTheory.CocycleCount.cocycles_finite_ncard_le hT hE l K r _
    (fun g => (actQ LA _ hI g).toAddMonoidHom) (actQ_one' LA _ hI)
    (fun g h m => actQ_mul' LA _ hI g h m) (pow_nsmul_quot LA hl r)
    (actQ_isLocallyConstant LA hW A.cont hI)
  exact hfin.1.to_subtype

end GlobalTheory.CompanionTheory.FinCoc
