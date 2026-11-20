import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

namespace GlobalTheory.RegSSClass

/- English proof (translation)
Use `set f := Matrix.toLin' A`. Establish `hcp : f.charpoly = A.charpoly` using `Matrix.charpoly_toLin' A`. Establish `hfg : Commute f (Matrix.toLin' N)` using `hc.map Matrix.toLinAlgEquiv'`. Establish `hNl : IsNilpotent (Matrix.toLin' N)` using `hN.map Matrix.toLinAlgEquiv'`. Take `⟨k, hk⟩` from `hNl`.

Establish `key : ∀ μ, Module.End.maxGenEigenspace f μ ≤ LinearMap.ker (Matrix.toLin' N)` using `fun μ v hv => by`. Establish `h1 : Module.finrank K (Module.End.maxGenEigenspace f μ) ≤ 1`. Rewrite using `[LinearMap.finrank_maxGenEigenspace_eq, hcp]`. Conclude with `Polynomial.rootMultiplicity_le_one_of_separable hA μ`. Distinguish the cases in `h0 : v = 0`.

Simplify using `[h0]`. Establish `h2 : Module.finrank K (Module.End.maxGenEigenspace f μ) = 1` using `le_antisymm h1 (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ) fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨_, Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv⟩`. Establish `hc' : Matrix.toLin' N v = c • v` using `(congrArg Subtype.val hc).symm`. Establish `hpow : ∀ m : ℕ, (Matrix.toLin' N ^ m) v = c ^ m • v`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc', smul_smul, pow_succ]`. Establish `h5 : c ^ k • v = 0` using `by rw [← hpow, hk]; rfl`.

Establish `hc0 : c = 0`. Break down `smul_eq_zero.1 h5 with h | h` into its components or cases. Conclude with `pow_eq_zero_iff'.1 h |>.1`. Conclude with `absurd h h0`. Rewrite using `[LinearMap.mem_ker, hc', hc0, zero_smul]`.

Establish `h3` using `iSup_le key`. Rewrite `h3` using `[Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top]`. Conclude with `Matrix.toLin'.injective (by rw [h3, map_zero])`.
-/
theorem nilpotent_eq_zero_of_commute_sep_alg {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  set f := Matrix.toLin' A
  have hcp : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' N) := hc.map Matrix.toLinAlgEquiv'
  have hNl : IsNilpotent (Matrix.toLin' N) := hN.map Matrix.toLinAlgEquiv'
  obtain ⟨k, hk⟩ := hNl
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤ LinearMap.ker (Matrix.toLin' N) := fun μ v hv => by
    have h1 : Module.finrank K (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hcp]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have h2 : Module.finrank K (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨_, Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv⟩
    have hc' : Matrix.toLin' N v = c • v := (congrArg Subtype.val hc).symm
    have hpow : ∀ m : ℕ, (Matrix.toLin' N ^ m) v = c ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc', smul_smul, pow_succ]
    have h5 : c ^ k • v = 0 := by rw [← hpow, hk]; rfl
    have hc0 : c = 0 := by
      rcases smul_eq_zero.1 h5 with h | h
      · exact pow_eq_zero_iff'.1 h |>.1
      · exact absurd h h0
    rw [LinearMap.mem_ker, hc', hc0, zero_smul]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top] at h3
  exact Matrix.toLin'.injective (by rw [h3, map_zero])

/- English proof (translation)
Establish `h` using `nilpotent_eq_zero_of_commute_sep_alg (K := AlgebraicClosure K) (A := A.map (algebraMap K (AlgebraicClosure K))) (N := N.map (algebraMap K (AlgebraicClosure K))) (by rw [Matrix.charpoly_map]; exact hA.map) (hN.map (algebraMap K (AlgebraicClosure K)).mapMatrix) (hc.map (algebraMap …`. Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify using `using this`.
-/
theorem nilpotent_eq_zero_of_commute_sep {K : Type} [Field K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  have h := nilpotent_eq_zero_of_commute_sep_alg (K := AlgebraicClosure K)
    (A := A.map (algebraMap K (AlgebraicClosure K))) (N := N.map (algebraMap K (AlgebraicClosure K)))
    (by rw [Matrix.charpoly_map]; exact hA.map) (hN.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
    (hc.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

/- English proof (translation)
Use `Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := A.charpoly) h.squarefree ?_` and prove the remaining obligations. Use `LinearMap.aeval_self_charpoly (Matrix.toLin' A)` as an intermediate fact. Rewrite `this` using `[Matrix.charpoly_toLin']`. Then use the resulting hypothesis.
-/
theorem isSemisimple_of_charpoly_separable {K : Type} [Field K] {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (h : A.charpoly.Separable) : Module.End.IsSemisimple (Matrix.toLin' A) := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := A.charpoly) h.squarefree ?_
  have := LinearMap.aeval_self_charpoly (Matrix.toLin' A)
  rwa [Matrix.charpoly_toLin'] at this

/- English proof (translation)
Take `⟨c, rfl⟩` from `isConj_iff.1 h`. Simplify using `using Matrix.charpoly_units_conj c.1 a.1.1`.
-/
theorem charpoly_eq_of_isConj {K : Type} [Field K] {n : ℕ} {G : Subgroup (GL (Fin n) K)} {a b : G}
    (h : IsConj a b) : b.1.1.charpoly = a.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  simpa using Matrix.charpoly_units_conj c.1 a.1.1

end GlobalTheory.RegSSClass

open GlobalTheory.RegSSClass in
/- English proof (translation)
Introduce `D V γ hγ`. Establish `hs : γ.1.1.charpoly.Separable` using `hγ`. Use `⟨γ, isSemisimple_of_charpoly_separable hs, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨x, ⟨isSemisimple_of_charpoly_separable ?_, Commute.refl _, by simp⟩, hx⟩` and prove the remaining obligations. Rewrite using `[charpoly_eq_of_isConj hx]`. Conclude with `hs`.

Introduce and unpack `⟨s, ⟨_, hcomm, hnil⟩, hconj⟩`. Establish `hss : s.1.1.charpoly.Separable` using `by rw [charpoly_eq_of_isConj hconj]; exact hs`. Establish `h0` using `nilpotent_eq_zero_of_commute_sep hss hnil (hcomm.symm.sub_right (Commute.refl _))`. Establish `hxs : x = s` using `Subtype.ext (Units.ext (sub_eq_zero.1 h0))`. Rewrite using `[hxs]`.

Conclude with `hconj`.
-/
theorem GlobalTheory.regSS_conjClass_isSSClass : ∀ {D : D7} {V : HSp D} (γ : GF V), IsRegSS γ.1.1 → IsSSClass {δ : GF V | IsConj γ δ} := by
  intro D V γ hγ
  have hs : γ.1.1.charpoly.Separable := hγ
  refine ⟨γ, isSemisimple_of_charpoly_separable hs, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨x, ⟨isSemisimple_of_charpoly_separable ?_, Commute.refl _, by simp⟩, hx⟩
    rw [charpoly_eq_of_isConj hx]; exact hs
  · rintro ⟨s, ⟨_, hcomm, hnil⟩, hconj⟩
    have hss : s.1.1.charpoly.Separable := by rw [charpoly_eq_of_isConj hconj]; exact hs
    have h0 := nilpotent_eq_zero_of_commute_sep hss hnil (hcomm.symm.sub_right (Commute.refl _))
    have hxs : x = s := Subtype.ext (Units.ext (sub_eq_zero.1 h0))
    rw [hxs]; exact hconj
