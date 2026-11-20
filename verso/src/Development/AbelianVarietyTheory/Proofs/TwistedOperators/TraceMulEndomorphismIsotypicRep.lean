import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasFiniteRankTraceOfOfRangeLeFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMatrixPiOperatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveSumOfLinIndepIntertwinersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerMemISupRangeEqSumSmulStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.IsoTrace

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a t ha ih => simp [Finset.sum_insert ha, ih]`.
-/
theorem intertwining_sum_apply {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
    {π : Representation ℂ G N} {ρ : Representation ℂ G X} {ι : Type} (t : Finset ι)
    (c : ι → ℂ) (φ : ι → π.IntertwiningMap ρ) (n : N) : (∑ j ∈ t, c j • φ j) n = ∑ j ∈ t, c j • φ j n := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => simp [Finset.sum_insert ha, ih]

/- English proof (translation)
Introduce `G _ N X _ _ _ _ π ρ hirr hschur hiso H hH ⟨s, hs⟩`. Set `S` to `Submodule.span ℂ (s : Set (π.IntertwiningMap ρ))`. Use `haveI : FiniteDimensional ℂ S := FiniteDimensional.span_finset ℂ s`. Set `bS` to `Module.finBasis ℂ S`. Set `φ : Fin (Module.finrank ℂ S) → π.IntertwiningMap ρ` to `fun j => (bS j : π.IntertwiningMap ρ)`.

Establish `hli : LinearIndependent ℂ φ` using `bS.linearIndependent.map' S.subtype (Submodule.ker_subtype S)`. Establish `hinj` using `GlobalTheory.T.injective_sum_of_linIndep_intertwiners G N X π ρ hirr hschur _ φ hli`. Establish `hY : LinearMap.range H ≤ ⨆ j, LinearMap.range (φ j).toLinearMap`. Use `hs.trans (iSup₂_le fun ψ hψ => ?_)` and prove the remaining obligations. Establish `hψS : ψ ∈ S` using `Submodule.subset_span hψ`.

Establish `e : ψ = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j`. Use `congrArg Subtype.val (bS.sum_repr ⟨ψ, hψS⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Conclude with `this.symm`. Introduce and unpack `_ ⟨n, rfl⟩`.

Establish `hn : ψ n = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j n`. Rewrite using `[← intertwining_sum_apply, ← e]`. Express the relevant statement in the definitionally equal form `ψ n ∈ _`. Rewrite using `[hn]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem j ⟨n, rfl⟩)`.

Establish `hcoef : ∀ ψ : π.IntertwiningMap ρ, ∃ c : Fin (Module.finrank ℂ S) → ℂ, ∀ n, H (ψ n) = ∑ j, c j • φ j n`. Introduce `ψ`. Set `Hψ : π.IntertwiningMap ρ` to `(H ∘ₗ ψ.toLinearMap).intertwiningMap_of_isIntertwiningMap π ρ (fun g v => by simp [ψ.isIntertwining, hH])`. Establish `hr : LinearMap.range Hψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap`. Introduce and unpack `_ ⟨n, rfl⟩`.

Conclude with `hY ⟨ψ n, rfl⟩`. Conclude with `GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range G N X π ρ hschur _ φ hinj Hψ hr`. Use `choose hc hhc using fun j => hcoef (φ j)`. Use `⟨∑ j, hc j j, fun A B hB b hb => ?_⟩` and prove the remaining obligations. Take `⟨hfin, htr⟩` from `hb`.

Set `R` to `LinearMap.range A`. Set `Φ' : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] X` to `∑ j, (φ j).toLinearMap ∘ₗ R.subtype ∘ₗ LinearMap.proj j`. Establish `hΦ' : ∀ w, Φ' w = ∑ j, φ j (w j : N)`. Introduce `w`. Simplify using `[Φ', LinearMap.sum_apply]`.

Establish `hinj' : Function.Injective Φ'`. Introduce `w w' e`. Rewrite `e` using `[hΦ', hΦ']`. Use `hinj e` as an intermediate fact. Use function extensionality and compare the values at `j`.

Conclude with `Subtype.ext (congrFun this j)`. Set `Z` to `LinearMap.range Φ'`. Establish `hBφ : ∀ (ψ : π.IntertwiningMap ρ) n, B (ψ n) = ψ (A n)` using `fun ψ n => DFunLike.congr_fun (hB ψ) n`. Establish `hrange : LinearMap.range (H ∘ₗ B) ≤ Z`. Introduce and unpack `_ ⟨x, rfl⟩`.

Establish `hx : x ∈ ⨆ f : π.IntertwiningMap ρ, LinearMap.range f.toLinearMap`. Establish `: x ∈ isoPartAlg π ρ` using `hiso ▸ Submodule.mem_top`. Conclude with `this`. Use `Submodule.iSup_induction _ (motive := fun x => (H ∘ₗ B) x ∈ Z) hx ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `ψ _ ⟨n, rfl⟩`.

Take `⟨c, hc'⟩` from `hcoef ψ`. Use `⟨fun j => c j • ⟨A n, LinearMap.mem_range_self A n⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ']`. Simplify using `only [LinearMap.comp_apply, Pi.smul_apply, SetLike.val_smul, map_smul]`. Rewrite using `[show ψ.toLinearMap n = ψ n from rfl, hBφ, hc']`.

Simplify using the standard rewrite rules. Introduce `x y hx hy`. Simplify using `using Z.add_mem hx hy`. Use `haveI : FiniteDimensional ℂ Z := LinearMap.finiteDimensional_range Φ'`. Establish `hT1` using `GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional X (H ∘ₗ B) Z hrange`.

Set `e : (Fin (Module.finrank ℂ S) → R) ≃ₗ[ℂ] Z` to `LinearEquiv.ofInjective Φ' hinj'`. Set `A' : R →ₗ[ℂ] R` to `A.restrict (p := R) (q := R) fun v _ => LinearMap.mem_range_self A v`. Set `h : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ` to `Matrix.of fun k j => hc j k`. Set `M : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → R)` to `∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ => R) k ∘ₗ A' ∘ₗ LinearMap.proj j)`. Establish `hM : ∀ w k, (M w k : N) = ∑ j, hc j k • A (w j)`.

Introduce `w k`. Simplify using `[M, h, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, A']`. Establish `hconj : (H ∘ₗ B).restrict (p` using `Z) (q := Z) (fun x _ => hrange (LinearMap.mem_range_self _ x)) = e.conj M := by`. Use `LinearMap.ext fun z => Subtype.ext ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `e.surjective z`.

Rewrite using `[LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]`. Express the relevant statement in the definitionally equal form `H (B (Φ' w)) = Φ' (M w)`. Rewrite using `[hΦ', hΦ', map_sum, map_sum]`. Repeatedly rewrite using `[hBφ, hhc, hM, map_sum, map_smul]`. Rewrite using `[Finset.sum_comm]`.

Establish `key : LinearMap.trace ℂ Z ((H ∘ₗ B).restrict (p` using `Z) (q := Z) fun x _ => hrange (LinearMap.mem_range_self _ x)) = (∑ j, hc j j) * b := by`. Rewrite using `[hconj, LinearMap.trace_conj', GlobalTheory.T.trace_sum_single_comp_proj_eq R _ h A', ← htr]`. Simplify using `[h, Matrix.trace, A', R]`. Rewrite using `[← key]`. Conclude with `hT1`.
-/
theorem trace_mul_isotypic : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible → (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) → IsIsotypicAlg π ρ → ∀ H : X →ₗ[ℂ] X, (∀ g x, H (ρ g x) = ρ g (H x)) → (∃ s : Finset (π.IntertwiningMap ρ), LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) → ∃ c : ℂ, ∀ (A : N →ₗ[ℂ] N) (B : X →ₗ[ℂ] X), (∀ φ : π.IntertwiningMap ρ, B ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ A) → ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (H ∘ₗ B) (c * b) := by
  intro G _ N X _ _ _ _ π ρ hirr hschur hiso H hH ⟨s, hs⟩
  let S := Submodule.span ℂ (s : Set (π.IntertwiningMap ρ))
  haveI : FiniteDimensional ℂ S := FiniteDimensional.span_finset ℂ s
  let bS := Module.finBasis ℂ S
  let φ : Fin (Module.finrank ℂ S) → π.IntertwiningMap ρ := fun j => (bS j : π.IntertwiningMap ρ)
  have hli : LinearIndependent ℂ φ := bS.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hinj := GlobalTheory.T.injective_sum_of_linIndep_intertwiners G N X π ρ hirr hschur _ φ hli
  have hY : LinearMap.range H ≤ ⨆ j, LinearMap.range (φ j).toLinearMap := by
    refine hs.trans (iSup₂_le fun ψ hψ => ?_)
    have hψS : ψ ∈ S := Submodule.subset_span hψ
    have e : ψ = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j := by
      have := congrArg Subtype.val (bS.sum_repr ⟨ψ, hψS⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rintro _ ⟨n, rfl⟩
    have hn : ψ n = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j n := by
      rw [← intertwining_sum_apply, ← e]
    change ψ n ∈ _
    rw [hn]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem j ⟨n, rfl⟩)
  have hcoef : ∀ ψ : π.IntertwiningMap ρ, ∃ c : Fin (Module.finrank ℂ S) → ℂ,
      ∀ n, H (ψ n) = ∑ j, c j • φ j n := by
    intro ψ
    let Hψ : π.IntertwiningMap ρ := (H ∘ₗ ψ.toLinearMap).intertwiningMap_of_isIntertwiningMap π ρ
      (fun g v => by simp [ψ.isIntertwining, hH])
    have hr : LinearMap.range Hψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap := by
      rintro _ ⟨n, rfl⟩
      exact hY ⟨ψ n, rfl⟩
    exact GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range G N X π ρ hschur _ φ hinj Hψ hr
  choose hc hhc using fun j => hcoef (φ j)
  refine ⟨∑ j, hc j j, fun A B hB b hb => ?_⟩
  obtain ⟨hfin, htr⟩ := hb
  let R := LinearMap.range A
  let Φ' : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] X :=
    ∑ j, (φ j).toLinearMap ∘ₗ R.subtype ∘ₗ LinearMap.proj j
  have hΦ' : ∀ w, Φ' w = ∑ j, φ j (w j : N) := by
    intro w
    simp [Φ', LinearMap.sum_apply]
  have hinj' : Function.Injective Φ' := by
    intro w w' e
    rw [hΦ', hΦ'] at e
    have := hinj e
    funext j
    exact Subtype.ext (congrFun this j)
  let Z := LinearMap.range Φ'
  have hBφ : ∀ (ψ : π.IntertwiningMap ρ) n, B (ψ n) = ψ (A n) := fun ψ n =>
    DFunLike.congr_fun (hB ψ) n
  have hrange : LinearMap.range (H ∘ₗ B) ≤ Z := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ ⨆ f : π.IntertwiningMap ρ, LinearMap.range f.toLinearMap := by
      have : x ∈ isoPartAlg π ρ := hiso ▸ Submodule.mem_top
      exact this
    refine Submodule.iSup_induction _ (motive := fun x => (H ∘ₗ B) x ∈ Z) hx ?_ ?_ ?_
    · rintro ψ _ ⟨n, rfl⟩
      obtain ⟨c, hc'⟩ := hcoef ψ
      refine ⟨fun j => c j • ⟨A n, LinearMap.mem_range_self A n⟩, ?_⟩
      rw [hΦ']
      simp only [LinearMap.comp_apply, Pi.smul_apply, SetLike.val_smul, map_smul]
      rw [show ψ.toLinearMap n = ψ n from rfl, hBφ, hc']
    · simp
    · intro x y hx hy
      simpa using Z.add_mem hx hy
  haveI : FiniteDimensional ℂ Z := LinearMap.finiteDimensional_range Φ'
  have hT1 := GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional X (H ∘ₗ B) Z hrange
  let e : (Fin (Module.finrank ℂ S) → R) ≃ₗ[ℂ] Z := LinearEquiv.ofInjective Φ' hinj'
  let A' : R →ₗ[ℂ] R := A.restrict (p := R) (q := R) fun v _ => LinearMap.mem_range_self A v
  let h : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ := Matrix.of fun k j => hc j k
  let M : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → R) :=
    ∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ => R) k ∘ₗ A' ∘ₗ LinearMap.proj j)
  have hM : ∀ w k, (M w k : N) = ∑ j, hc j k • A (w j) := by
    intro w k
    simp [M, h, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, A']
  have hconj : (H ∘ₗ B).restrict (p := Z) (q := Z) (fun x _ => hrange (LinearMap.mem_range_self _ x)) =
      e.conj M := by
    refine LinearMap.ext fun z => Subtype.ext ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    change H (B (Φ' w)) = Φ' (M w)
    rw [hΦ', hΦ', map_sum, map_sum]
    simp_rw [hBφ, hhc, hM, map_sum, map_smul]
    rw [Finset.sum_comm]
  have key : LinearMap.trace ℂ Z ((H ∘ₗ B).restrict (p := Z) (q := Z)
      fun x _ => hrange (LinearMap.mem_range_self _ x)) = (∑ j, hc j j) * b := by
    rw [hconj, LinearMap.trace_conj', GlobalTheory.T.trace_sum_single_comp_proj_eq R _ h A', ← htr]
    simp [h, Matrix.trace, A', R]
  rw [← key]
  exact hT1

end GlobalTheory.IsoTrace
