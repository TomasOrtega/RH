import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivCrysJumpZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

noncomputable section

namespace GlobalTheory.HodgeCrysSeq

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `T₁ T₂ F h1 _ hF τ a hj`. Establish `hs : Function.Surjective F.f`. Establish `hr : LinearMap.range F.f = ⊤`. Rewrite using `[eq_top_iff, ← T₂.L.span, Submodule.span_le]`.

Introduce `y hy`. Take `⟨x, -, rfl⟩` from `hF y hy`. Conclude with `⟨x, rfl⟩`. Conclude with `LinearMap.range_eq_top.1 hr`. Establish `hst : ∀ g, LinearMap.ker F.f ≤ (LinearMap.ker F.f).comap (T₁.ρ g)`.

Introduce `g v hv`. Rewrite using `[Submodule.mem_comap, LinearMap.mem_ker, F.equiv, LinearMap.mem_ker.1 hv, map_zero]`. Establish `hdr` using `(GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h1.2.2.2).1`. Use `GlobalTheory.Per.ExactMult.exact_hodge_add l P AI hT K LL (LinearMap.ker F.f) (T₁.ρ.subrepresentation (LinearMap.ker F.f) hst) T₁.V T₁.ρ T₂.V T₂.ρ (LinearMap.ker F.f).subtype F.f (fun _ _ => rfl) F.equiv (LinearMap.ker F.f).injective_subtype hs (Submodule.range_subtype _) hdr` as an intermediate fact. Conclude with `(this.2.2 τ a).2.2.2 (Or.inr hj)`.

Introduce `T₀ T₁ T₂ ι π hS h1`. Take `⟨hi, hs, -, hk, -⟩` from `hS`. Establish `c0` using `(GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hi h1.2.2.2`. Establish `c2` using `((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI hT K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2 hs h1.2.2.2).1`. Establish `hr : LinearMap.range ι.f = LinearMap.ker π.f`.

Use extensionality with `x`. Rewrite using `[LinearMap.mem_range, LinearMap.mem_ker]`. Conclude with `(hk x).symm`. Establish `hdr` using `(GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h1.2.2.2).1`. Use `GlobalTheory.Per.ExactMult.exact_hodge_add l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ ι.f π.f ι.equiv π.equiv hi hs hr hdr` as an intermediate fact.

Conclude with `⟨⟨inferInstance, inferInstance, T₀.cont, c0⟩, ⟨inferInstance, inferInstance, T₂.cont, c2⟩, fun τ a => (this.2.2 τ a).2.2⟩`. Introduce `T hT' τ a hj`. Conclude with `(GlobalTheory.TrivCrys.triv_crys_jump_zero l P AI hT K LL T.V T.ρ hT').2 τ a hj`.
-/
theorem hodgeExact_at (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) : Formalism.MainNotions.WachCoordinates.HodgeExact (P.PD K) ↥LL.1 ↥(OL LL) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T₁ T₂ F h1 _ hF τ a hj
    have hs : Function.Surjective F.f := by
      have hr : LinearMap.range F.f = ⊤ := by
        rw [eq_top_iff, ← T₂.L.span, Submodule.span_le]
        intro y hy
        obtain ⟨x, -, rfl⟩ := hF y hy
        exact ⟨x, rfl⟩
      exact LinearMap.range_eq_top.1 hr
    have hst : ∀ g, LinearMap.ker F.f ≤ (LinearMap.ker F.f).comap (T₁.ρ g) := by
      intro g v hv
      rw [Submodule.mem_comap, LinearMap.mem_ker, F.equiv, LinearMap.mem_ker.1 hv, map_zero]
    have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h1.2.2.2).1
    have := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI hT K LL (LinearMap.ker F.f)
      (T₁.ρ.subrepresentation (LinearMap.ker F.f) hst) T₁.V T₁.ρ T₂.V T₂.ρ
      (LinearMap.ker F.f).subtype F.f (fun _ _ => rfl) F.equiv (LinearMap.ker F.f).injective_subtype hs
      (Submodule.range_subtype _) hdr
    exact (this.2.2 τ a).2.2.2 (Or.inr hj)
  · intro T₀ T₁ T₂ ι π hS h1
    obtain ⟨hi, hs, -, hk, -⟩ := hS
    have c0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hi
      h1.2.2.2
    have c2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI hT K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2 hs
      h1.2.2.2).1
    have hr : LinearMap.range ι.f = LinearMap.ker π.f := by
      ext x
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      exact (hk x).symm
    have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h1.2.2.2).1
    have := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ ι.f π.f
      ι.equiv π.equiv hi hs hr hdr
    exact ⟨⟨inferInstance, inferInstance, T₀.cont, c0⟩, ⟨inferInstance, inferInstance, T₂.cont, c2⟩,
      fun τ a => (this.2.2 τ a).2.2⟩
  · intro T hT' τ a hj
    exact (GlobalTheory.TrivCrys.triv_crys_jump_zero l P AI hT K LL T.V T.ρ hT').2 τ a hj

/- English proof (translation)
Introduce `D l _ K LL`. Conclude with `hodgeExact_at l (D.loc l) (D.locA l) (D.locT l) K LL`.
-/
theorem hodge_crystalline_sequences : ∀ D : D7, Formalism.MainNotions.WachCoordinates.adm14 D := by
  intro D l _ K LL
  exact hodgeExact_at l (D.loc l) (D.locA l) (D.locT l) K LL

end GlobalTheory.HodgeCrysSeq
