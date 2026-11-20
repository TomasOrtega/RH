import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTwistRepDualOfPairing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAll

/- English proof (translation)
Set `f : V₀ × V₂ →ₗ[L] V₁` to `ι.coprod s`. Establish `hf : ∀ a b, f (a, b) = ι a + s b` using `fun a b => rfl`. Establish `hπι : ∀ a, π (ι a) = 0` using `fun a => by`. Establish `: ι a ∈ LinearMap.ker π` using `hk ▸ LinearMap.mem_range_self ι a`. Conclude with `this`.

Establish `hbij : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨a, b⟩ h`. Rewrite `h` using `[hf]`.

Establish `hb : b = 0`. Use `congrArg π h` as an intermediate fact. Rewrite `this` using `[map_add, hπι, hps, zero_add, map_zero]`. Then use the resulting hypothesis. Substitute `hb` using the available equality. Rewrite `h` using `[map_zero, add_zero]`.

Establish `ha : a = 0` using `hi (by rw [h, map_zero])`. Rewrite using `[ha]`. Both sides reduce to the same expression. Introduce `z`. Establish `hz : z - s (π z) ∈ LinearMap.range ι`.

Rewrite using `[hk, LinearMap.mem_ker, map_sub, hps, sub_self]`. Take `⟨a, ha⟩` from `hz`. Conclude with `⟨(a, π z), by rw [hf, ha, sub_add_cancel]⟩`. Set `e` to `(LinearEquiv.ofBijective f hbij).symm`. Use `⟨e, fun g v => ?_⟩` and prove the remaining obligations.

Apply `(LinearEquiv.ofBijective f hbij).injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `f (e (ρ₁ g v)) = f (ρ₀ g (e v).1, ρ₂ g (e v).2)`. Establish `h1 : ∀ w, f (e w) = w` using `fun w => (LinearEquiv.ofBijective f hbij).apply_symm_apply w`. Rewrite using `[h1, hf, hι, hs, ← map_add, ← hf]`. Establish `: ((e v).1, (e v).2) = e v` using `rfl`.

Rewrite using `[this, h1]`.
-/
theorem split_equiv {G L V₀ V₁ V₂ : Type} [Group G] [Field L] [AddCommGroup V₀] [Module L V₀]
    [AddCommGroup V₁] [Module L V₁] [AddCommGroup V₂] [Module L V₂]
    (ρ₀ : Representation L G V₀) (ρ₁ : Representation L G V₁) (ρ₂ : Representation L G V₂)
    (ι : V₀ →ₗ[L] V₁) (π : V₁ →ₗ[L] V₂) (hι : ∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x))
    (hi : Function.Injective ι) (hk : LinearMap.range ι = LinearMap.ker π)
    (s : V₂ →ₗ[L] V₁) (hs : ∀ g x, s (ρ₂ g x) = ρ₁ g (s x)) (hps : ∀ x, π (s x) = x) :
    ∃ e : V₁ ≃ₗ[L] (V₀ × V₂), ∀ g v, e (ρ₁ g v) = (ρ₀ g (e v).1, ρ₂ g (e v).2) := by
  let f : V₀ × V₂ →ₗ[L] V₁ := ι.coprod s
  have hf : ∀ a b, f (a, b) = ι a + s b := fun a b => rfl
  have hπι : ∀ a, π (ι a) = 0 := fun a => by
    have : ι a ∈ LinearMap.ker π := hk ▸ LinearMap.mem_range_self ι a
    exact this
  have hbij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ h
      rw [hf] at h
      have hb : b = 0 := by
        have := congrArg π h
        rwa [map_add, hπι, hps, zero_add, map_zero] at this
      subst hb
      rw [map_zero, add_zero] at h
      have ha : a = 0 := hi (by rw [h, map_zero])
      rw [ha]; rfl
    · intro z
      have hz : z - s (π z) ∈ LinearMap.range ι := by
        rw [hk, LinearMap.mem_ker, map_sub, hps, sub_self]
      obtain ⟨a, ha⟩ := hz
      exact ⟨(a, π z), by rw [hf, ha, sub_add_cancel]⟩
  let e := (LinearEquiv.ofBijective f hbij).symm
  refine ⟨e, fun g v => ?_⟩
  apply (LinearEquiv.ofBijective f hbij).injective
  change f (e (ρ₁ g v)) = f (ρ₀ g (e v).1, ρ₂ g (e v).2)
  have h1 : ∀ w, f (e w) = w := fun w => (LinearEquiv.ofBijective f hbij).apply_symm_apply w
  rw [h1, hf, hι, hs, ← map_add, ← hf]
  have : ((e v).1, (e v).2) = e v := rfl
  rw [this, h1]

/- English proof (translation)
Introduce `D l _ K LL`. Establish `T` using `D.locT l`. Unfold `Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `A₀ A₁ A₂ ι π hι hπ hi hs hk`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h1`. Establish `c0` using `(GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL A₀.V A₀.ρ A₁.V A₁.ρ ι hι).1 hi h1`. Establish `c2` using `((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ A₂.V A₂.ρ π hπ).2 hs h1).1`. Establish `d1` using `(GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ h1).1`.

Take `⟨-, -, hm⟩` from `GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) T K LL A₀.V A₀.ρ A₁.V A₁.ρ A₂.V A₂.ρ ι π hι hπ hi hs hk d1`. Conclude with `⟨c0, c2, fun τ a => (hm τ a).2.1⟩`. Introduce and unpack `⟨s, hs', hps⟩ h0 h2`. Take `⟨e, he⟩` from `split_equiv A₀.ρ A₁.ρ A₂.ρ ι π hι hi hk s hs' hps`. Conclude with `((GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ A₀.V A₀.ρ A₂.V A₂.ρ e he).2.1).2 ⟨h0, h2⟩`.

Introduce `A A' χ htw hχ hA`. Conclude with `GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) T K LL A.V A.ρ A'.V A'.ρ χ htw hχ hA`. Introduce `A A' P hD hA`. Conclude with `GlobalTheory.DualOne.isCrys_of_isDual1 l (D.loc l) (D.locA l) T K LL A.V A.ρ A'.V A'.ρ P hD hA`. Introduce `A hA`.

Conclude with `(GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL A.V A.ρ hA).1`.
-/
theorem fontaineAt_all : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l),
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL) := by
  intro D l _ K LL
  have T := D.locT l
  unfold Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A₀ A₁ A₂ ι π hι hπ hi hs hk
    refine ⟨?_, ?_⟩
    · intro h1
      have c0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL A₀.V A₀.ρ A₁.V A₁.ρ ι hι).1 hi h1
      have c2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ A₂.V A₂.ρ π hπ).2 hs h1).1
      have d1 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ h1).1
      obtain ⟨-, -, hm⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) T K LL A₀.V A₀.ρ A₁.V A₁.ρ
        A₂.V A₂.ρ ι π hι hπ hi hs hk d1
      exact ⟨c0, c2, fun τ a => (hm τ a).2.1⟩
    · rintro ⟨s, hs', hps⟩ h0 h2
      obtain ⟨e, he⟩ := split_equiv A₀.ρ A₁.ρ A₂.ρ ι π hι hi hk s hs' hps
      exact ((GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ A₀.V A₀.ρ
        A₂.V A₂.ρ e he).2.1).2 ⟨h0, h2⟩
  · intro A A' χ htw hχ hA
    exact GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) T K LL A.V A.ρ A'.V A'.ρ χ htw hχ hA
  · intro A A' P hD hA
    exact GlobalTheory.DualOne.isCrys_of_isDual1 l (D.loc l) (D.locA l) T K LL A.V A.ρ A'.V A'.ρ P hD hA
  · intro A hA
    exact (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL A.V A.ρ hA).1

end GlobalTheory.FontaineAll
