import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.CharLat

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis O T`. Use `haveI hsub : Subsingleton (Module.Free.ChooseBasisIndex O T) := by`. Prove the components needed by the constructor for the conclusion. Introduce `i j`. Assume the negation of the conclusion as `hij`.

Establish `hi : ((b i : T) : K) ≠ 0` using `fun h0 => b.ne_zero i (Subtype.ext h0)`. Take `⟨a, d, hd0, hd⟩` from `hfr (((b j : T) : K) / ((b i : T) : K))`. Establish `hrel : d • b j + (-a) • b i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm, ZeroMemClass.coe_zero, map_neg, ← hd]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hinj : Function.Injective ![j, i]`. Introduce `x y hxy`. Apply the tactic sequence `fin_cases x <;> fin_cases y`.

Both sides reduce to the same expression. Conclude with `absurd (hxy : j = i).symm hij`. Conclude with `absurd (hxy : i = j) hij`. Both sides reduce to the same expression. Establish `hli : LinearIndependent O ![b j, b i]`.

Use `b.linearIndependent.comp ![j, i] hinj` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`. Apply the tactic sequence `fin_cases k <;> rfl`. Establish `h2` using `LinearIndependent.pair_iff.1 hli d (-a) hrel`.

Conclude with `hd0 h2.1`. Use `haveI hne : Nonempty (Module.Free.ChooseBasisIndex O T) := by`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`. Apply `hT` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `h0 : (⟨x, hx⟩ : T) = 0` using `b.repr.injective (Subsingleton.elim _ _)`. Simplify using `using congrArg Subtype.val h0`. Use `haveI : Unique (Module.Free.ChooseBasisIndex O T) := uniqueOfSubsingleton (Classical.arbitrary _)`.

Conclude with `⟨(LinearEquiv.funUnique (Module.Free.ChooseBasisIndex O T) O O).symm.trans b.equivFun.symm⟩`.
-/
theorem nonempty_equiv_of_free {O K : Type} [CommRing O] [IsDomain O] [Field K] [Module O K]
    (φ : O →+* K) (hsm : ∀ (o : O) (x : K), o • x = φ o * x)
    (hfr : ∀ z : K, ∃ a d : O, d ≠ 0 ∧ z * φ d = φ a)
    (T : Submodule O K) [Module.Free O T] (hT : T ≠ ⊥) :
    Nonempty (O ≃ₗ[O] T) := by
  let b := Module.Free.chooseBasis O T
  haveI hsub : Subsingleton (Module.Free.ChooseBasisIndex O T) := by
    constructor
    intro i j
    by_contra hij
    have hi : ((b i : T) : K) ≠ 0 := fun h0 => b.ne_zero i (Subtype.ext h0)
    obtain ⟨a, d, hd0, hd⟩ := hfr (((b j : T) : K) / ((b i : T) : K))
    have hrel : d • b j + (-a) • b i = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm, ZeroMemClass.coe_zero,
        map_neg, ← hd]
      field_simp
      ring
    have hinj : Function.Injective ![j, i] := by
      intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · exact absurd (hxy : j = i).symm hij
      · exact absurd (hxy : i = j) hij
      · rfl
    have hli : LinearIndependent O ![b j, b i] := by
      have := b.linearIndependent.comp ![j, i] hinj
      convert this using 1
      ext k
      fin_cases k <;> rfl
    have h2 := LinearIndependent.pair_iff.1 hli d (-a) hrel
    exact hd0 h2.1
  haveI hne : Nonempty (Module.Free.ChooseBasisIndex O T) := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hT
    rw [eq_bot_iff]
    intro x hx
    have h0 : (⟨x, hx⟩ : T) = 0 := b.repr.injective (Subsingleton.elim _ _)
    simpa using congrArg Subtype.val h0
  haveI : Unique (Module.Free.ChooseBasisIndex O T) := uniqueOfSubsingleton (Classical.arbitrary _)
  exact ⟨(LinearEquiv.funUnique (Module.Free.ChooseBasisIndex O T) O O).symm.trans b.equivFun.symm⟩

end GlobalTheory.CharLat

namespace GlobalTheory.CharLat

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `l _ LL G _ _ θ Lc`. Use `haveI := LL.2`. Use `haveI hF : IsFractionRing (↥(OL LL)) (↥LL.1) := integralClosure.isFractionRing_of_finite_extension (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥LL.1)`. Use `haveI := Lc.free`. Establish `hT : Lc.T ≠ ⊥`.

Introduce `h`. Establish `hs` using `Lc.span`. Rewrite `hs` using `[h, Submodule.bot_coe, Submodule.span_zero_singleton]`. Conclude with `bot_ne_top hs`. Establish `hsm : ∀ (o : ↥(OL LL)) (x : ↥LL.1), o • x = algebraMap (↥(OL LL)) (↥LL.1) o * x` using `fun o x => rfl`.

Establish `hfr : ∀ z : ↥LL.1, ∃ a d : ↥(OL LL), d ≠ 0 ∧ z * algebraMap (↥(OL LL)) (↥LL.1) d = algebraMap (↥(OL LL)) (↥LL.1) a`. Introduce `z`. Take `⟨⟨a, d⟩, hd⟩` from `IsLocalization.surj (nonZeroDivisors (↥(OL LL))) z`. Conclude with `⟨a, d, nonZeroDivisors.coe_ne_zero d, hd⟩`. Take `⟨e⟩` from `nonempty_equiv_of_free (algebraMap (↥(OL LL)) (↥LL.1)) hsm hfr Lc.T hT`.

Use `⟨e, fun g a => ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.GaloisCohomology.scalRep_apply, map_smul]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_smul, hsm]`. Both sides reduce to the same expression.
-/
theorem exists_equiv_charLattice : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) {G : Type} [Group G] [TopologicalSpace G]
    (θ : G →* (↥(OL LL))ˣ) (Lc : Lattice (O := ↥(OL LL)) (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) θ))),
    ∃ e : ↥(OL LL) ≃ₗ[↥(OL LL)] ↥Lc.T, ∀ g a, e (Formalism.GaloisCohomology.scalRep (↥(OL LL)) θ g a) = latRep Lc g (e a) := by
  intro l _ LL G _ _ θ Lc
  haveI := LL.2
  haveI hF : IsFractionRing (↥(OL LL)) (↥LL.1) :=
    integralClosure.isFractionRing_of_finite_extension (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥LL.1)
  haveI := Lc.free
  have hT : Lc.T ≠ ⊥ := by
    intro h
    have hs := Lc.span
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at hs
    exact bot_ne_top hs
  have hsm : ∀ (o : ↥(OL LL)) (x : ↥LL.1), o • x = algebraMap (↥(OL LL)) (↥LL.1) o * x :=
    fun o x => rfl
  have hfr : ∀ z : ↥LL.1, ∃ a d : ↥(OL LL), d ≠ 0 ∧ z * algebraMap (↥(OL LL)) (↥LL.1) d =
      algebraMap (↥(OL LL)) (↥LL.1) a := by
    intro z
    obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (↥(OL LL))) z
    exact ⟨a, d, nonZeroDivisors.coe_ne_zero d, hd⟩
  obtain ⟨e⟩ := nonempty_equiv_of_free (algebraMap (↥(OL LL)) (↥LL.1)) hsm hfr Lc.T hT
  refine ⟨e, fun g a => ?_⟩
  rw [Formalism.GaloisCohomology.scalRep_apply, map_smul]
  apply Subtype.ext
  rw [Submodule.coe_smul, hsm]
  rfl

end GlobalTheory.CharLat
