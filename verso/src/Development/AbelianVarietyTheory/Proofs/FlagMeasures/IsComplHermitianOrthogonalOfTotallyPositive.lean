import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hmem : ∀ v, v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0`. Introduce `v`. Simplify using `[orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Establish `hdis : U ⊓ orth S U = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `x hx`. Break down `hx with ⟨hxU, hxO⟩` into its components or cases. Assume the negation of the conclusion as `hne`. Establish `h0 : S.hT x x = 0` using `(hmem x).1 hxO x hxU`. Use `hpos x hxO hne` as an intermediate fact.

Rewrite `this` using `[h0, map_zero]`. Conclude with `lt_irrefl _ this`. Set `b` to `Module.finBasis E U`. Set `φ : S.V →ₗ[E] (Fin (Module.finrank E U) → E)` to `LinearMap.pi fun i => S.hT (b i : S.V)`. Establish `hker : LinearMap.ker φ ≤ orth S U`.

Introduce `y hy`. Rewrite `hy` using `[LinearMap.mem_ker]`. Rewrite using `[hmem]`. Introduce `x hx`. Establish `hy' : ∀ i, S.hT (b i : S.V) y = 0` using `fun i => congrFun hy i`.

Establish `hx' : (⟨x, hx⟩ : U) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i` using `(b.sum_repr _).symm`. Establish `hxs : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : S.V)`. Use `congrArg (Subtype.val) hx'` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at this`. Conclude with `this`.

Rewrite using `[hxs, map_sum]`. Simplify using `[LinearMap.sum_apply, hy']`. Establish `hrk : Module.finrank E S.V ≤ Module.finrank E U + Module.finrank E (orth S U)`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker φ`. Establish `h2 : Module.finrank E (LinearMap.range φ) ≤ Module.finrank E U`.

Use `Submodule.finrank_le (LinearMap.range φ)` as an intermediate fact. Simplify using `using this`. Establish `h3` using `Submodule.finrank_mono hker`. Use linear arithmetic over natural numbers and integers. Establish `hcod : U ⊔ orth S U = ⊤`.

Establish `h` using `Submodule.finrank_sup_add_finrank_inf_eq U (orth S U)`. Rewrite `h` using `[hdis, finrank_bot]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Use `Submodule.finrank_le (U ⊔ orth S U)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `⟨disjoint_iff.2 hdis, codisjoint_iff.2 hcod⟩`.
-/
theorem GlobalTheory.isCompl_orth_of_definite {E : Type} [Field E] [NumberField E] [StarRing E]
    (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V)
    (hpos : ∀ x ∈ orth S U, x ≠ 0 → 0 < Algebra.trace ℚ E (S.hT x x)) :
    IsCompl U (orth S U) := by
  have hmem : ∀ v, v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
    intro v
    simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  have hdis : U ⊓ orth S U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases hx with ⟨hxU, hxO⟩
    by_contra hne
    have h0 : S.hT x x = 0 := (hmem x).1 hxO x hxU
    have := hpos x hxO hne
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  let b := Module.finBasis E U
  let φ : S.V →ₗ[E] (Fin (Module.finrank E U) → E) := LinearMap.pi fun i => S.hT (b i : S.V)
  have hker : LinearMap.ker φ ≤ orth S U := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [hmem]
    intro x hx
    have hy' : ∀ i, S.hT (b i : S.V) y = 0 := fun i => congrFun hy i
    have hx' : (⟨x, hx⟩ : U) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
    have hxs : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : S.V) := by
      have := congrArg (Subtype.val) hx'
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this
    rw [hxs, map_sum]
    simp [LinearMap.sum_apply, hy']
  have hrk : Module.finrank E S.V ≤ Module.finrank E U + Module.finrank E (orth S U) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank E (LinearMap.range φ) ≤ Module.finrank E U := by
      have := Submodule.finrank_le (LinearMap.range φ)
      simpa using this
    have h3 := Submodule.finrank_mono hker
    omega
  have hcod : U ⊔ orth S U = ⊤ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U (orth S U)
    rw [hdis, finrank_bot] at h
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (U ⊔ orth S U)
    omega
  exact ⟨disjoint_iff.2 hdis, codisjoint_iff.2 hcod⟩
