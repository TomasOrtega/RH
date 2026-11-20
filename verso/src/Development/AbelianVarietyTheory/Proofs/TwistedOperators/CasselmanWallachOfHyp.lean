import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CasselmanWallachAdm
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CasselmanWallachLift
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobBdSeminorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteApproximateIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KAverageSmoothFunctional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyGrpData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix Filter GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped Topology

namespace GlobalTheory.CWGeneral

variable {n : ℕ} {ε : Fin n → Bool}

section Sub

variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]

open Classical in

def subOp (π : Mx n → (E →L[ℂ] E)) (S : Set (Mx n)) (F : Submodule ℂ E)
    (hinv : ∀ g ∈ S, ∀ x ∈ F, π g x ∈ F) (g : Mx n) : F →L[ℂ] F :=
  if hg : g ∈ S then ((π g).comp F.subtypeL).codRestrict F (fun x => hinv g hg x x.2) else 0

end Sub

section KFin

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)}

/- English proof (translation)
Break down `subsingleton_or_nontrivial H with hs | hn` into its components or cases. Introduce `x`. Rewrite using `[Subsingleton.elim x 0]`. Conclude with `subset_closure (smoothAll (Jm ε) σ).zero_mem`. Use `dense_of_irred hi (fun g hg v hv k x hx hxG => ?_) ?_` and prove the remaining obligations.

Use `letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)`. Use `letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)`. Establish `h1` using `hv k (fun t => x t * g) (hx.mul contDiff_const) fun t => mul_mem_UJ (hxG t) hg`. Use `h1 using 2 with t` and compare the differences between its conclusion and the goal. Conclude with `(sigma_mul hσ (hxG t) hg v).symm`.

Take `⟨v, hv, hs⟩` from `GlobalTheory.GardingVec.exists_garding hσ`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨v, hs, hv⟩`.
-/
theorem dense_smoothAll_of_irred (hσ : IsURepOn (UJset ε) σ) (hi : IsIrredOn (UJset ε) σ) :
    Dense (smoothAll (Jm ε) σ : Set H) := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · intro x
    rw [Subsingleton.elim x 0]
    exact subset_closure (smoothAll (Jm ε) σ).zero_mem
  · refine dense_of_irred hi (fun g hg v hv k x hx hxG => ?_) ?_
    · letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
      letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
      have h1 := hv k (fun t => x t * g) (hx.mul contDiff_const) fun t => mul_mem_UJ (hxG t) hg
      convert h1 using 2 with t
      exact (sigma_mul hσ (hxG t) hg v).symm
    · obtain ⟨v, hv, hs⟩ := GlobalTheory.GardingVec.exists_garding hσ
      exact (Submodule.ne_bot_iff _).2 ⟨v, hs, hv⟩

/- English proof (translation)
Use `hHC.smoothVec hσ hi hv (P := 1) (G := Jm ε) isUnit_one (by simp)` as an intermediate fact. Rewrite `this` using `[conj_one_eq]`. Then use the resulting hypothesis.
-/
theorem sm_of_isKFin (hHC : GlobalTheory.Published.HarishChandraModules) (hσ : IsURepOn (UJset ε) σ)
    (hi : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : Sm ε σ v := by
  have := hHC.smoothVec hσ hi hv (P := 1) (G := Jm ε) isUnit_one (by simp)
  rwa [conj_one_eq] at this

/- English proof (translation)
Take `⟨S, h1, h2, h3⟩` from `hv`. Establish `hS : S ≤ smooth (Jm ε) σ` using `fun s hs => sm_of_isKFin hHC hσ hi ⟨S, h1, hs, h3⟩`. Set `b` to `Module.finBasis ℝ (lie (Jm ε))`. Set `L : Fin (Module.finrank ℝ (lie (Jm ε))) → (S →ₗ[ℂ] H)` to `fun i => (smooth (Jm ε) σ).subtype ∘ₗ dOp (isUnit_Jm ε) hσ (b i).2 ∘ₗ Submodule.inclusion hS`. Set `T : Submodule ℂ H` to `⨆ i, LinearMap.range (L i)`.

Establish `hT : ∀ Y ∈ lieSet ε, ∀ s ∈ S, dRep σ Y s ∈ T`. Introduce `Y hY s hs`. Establish `e : Y = ∑ i, b.repr ⟨Y, hY⟩ i • (b i : Mx n)`. Use `congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)` as an intermediate fact. Simplify `this.symm` using `only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]`.

Rewrite using `[e, GlobalTheory.LowTypeDetermined.dRep_sum (isUnit_Jm ε) hσ (dense_smoothAll_of_irred hσ hi) (fun i => (b i).2) (hS hs)]`. Use `T.sum_mem fun i _ => T.smul_mem _ ?_` and prove the remaining obligations. Conclude with `Submodule.mem_iSup_of_mem i ⟨⟨s, hs⟩, rfl⟩`. Use `⟨T, inferInstance, hT X hX v h2, fun k hk w hw => ?_⟩` and prove the remaining obligations. Establish `hg` using `K_le_UJ hk`.

Establish `: T ≤ T.comap (σ k : H →ₗ[ℂ] H)`. Use `iSup_le fun i => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩`. Establish `hinv : (k⁻¹)⁻¹ = k` using `Matrix.inv_eq_left_inv (mul_inv_UJ hg)`. Establish `hY : k * (b i : Mx n) * k⁻¹ ∈ lieSet ε`.

Use `conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) (b i).2` as an intermediate fact. Rewrite `this` using `[hinv]`. Then use the resulting hypothesis. Establish `e` using `Dw_translate hσ hg (hS s.2) (l := [k * (b i : Mx n) * k⁻¹]) (by simpa using hY)`. Establish `e2 : k⁻¹ * (k * (b i : Mx n) * k⁻¹) * k = b i`. Rewrite using `[← mul_assoc, ← mul_assoc, inv_mul_UJ hg, one_mul, mul_assoc, inv_mul_UJ hg, mul_one]`.

Simplify using `only [Dw, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, e2] at e`. Use `show σ k (dRep σ (b i) s) ∈ T`. Rewrite using `[← e]`. Conclude with `hT _ hY _ (h3 k hk s s.2)`. Conclude with `this hw`.
-/
theorem isKFin_dRep_of_irred (hHC : GlobalTheory.Published.HarishChandraModules) (hσ : IsURepOn (UJset ε) σ)
    (hi : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    IsKFin ε σ (dRep σ X v) := by
  obtain ⟨S, h1, h2, h3⟩ := hv
  have hS : S ≤ smooth (Jm ε) σ := fun s hs => sm_of_isKFin hHC hσ hi ⟨S, h1, hs, h3⟩
  let b := Module.finBasis ℝ (lie (Jm ε))
  let L : Fin (Module.finrank ℝ (lie (Jm ε))) → (S →ₗ[ℂ] H) := fun i =>
    (smooth (Jm ε) σ).subtype ∘ₗ dOp (isUnit_Jm ε) hσ (b i).2 ∘ₗ Submodule.inclusion hS
  let T : Submodule ℂ H := ⨆ i, LinearMap.range (L i)
  have hT : ∀ Y ∈ lieSet ε, ∀ s ∈ S, dRep σ Y s ∈ T := by
    intro Y hY s hs
    have e : Y = ∑ i, b.repr ⟨Y, hY⟩ i • (b i : Mx n) := by
      have := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
      simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using this.symm
    rw [e, GlobalTheory.LowTypeDetermined.dRep_sum (isUnit_Jm ε) hσ (dense_smoothAll_of_irred hσ hi) (fun i => (b i).2)
      (hS hs)]
    refine T.sum_mem fun i _ => T.smul_mem _ ?_
    exact Submodule.mem_iSup_of_mem i ⟨⟨s, hs⟩, rfl⟩
  refine ⟨T, inferInstance, hT X hX v h2, fun k hk w hw => ?_⟩
  have hg := K_le_UJ hk
  have : T ≤ T.comap (σ k : H →ₗ[ℂ] H) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨s, rfl⟩
    have hinv : (k⁻¹)⁻¹ = k := Matrix.inv_eq_left_inv (mul_inv_UJ hg)
    have hY : k * (b i : Mx n) * k⁻¹ ∈ lieSet ε := by
      have := conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) (b i).2
      rwa [hinv] at this
    have e := Dw_translate hσ hg (hS s.2) (l := [k * (b i : Mx n) * k⁻¹]) (by simpa using hY)
    have e2 : k⁻¹ * (k * (b i : Mx n) * k⁻¹) * k = b i := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_UJ hg, one_mul, mul_assoc, inv_mul_UJ hg, mul_one]
    simp only [Dw, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, e2] at e
    show σ k (dRep σ (b i) s) ∈ T
    rw [← e]
    exact hT _ hY _ (h3 k hk s s.2)
  exact this hw

end KFin

end GlobalTheory.CWGeneral

end
