import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

noncomputable section

namespace GlobalTheory.CrysExtCrit

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

/- English proof (translation)
Take `⟨f, hf, hf0⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance`. Establish `hle : LinearMap.range ι ≤ LinearMap.ker ((f x)⁻¹ • f)`. Introduce `y hy`. Establish `: f y = 0`. Establish `: f y ∈ (LinearMap.range ι).map f` using `⟨y, hy, rfl⟩`.

Rewrite `this` using `[hf0, Submodule.mem_bot]`. Then use the resulting hypothesis. Simplify using `[this]`. Establish `hpx : ((f x)⁻¹ • f) x = 1` using `by simp [hf]`. Use `⟨(f x)⁻¹ • f, hpx, (Submodule.eq_of_le_of_finrank_le hle ?_).symm⟩` and prove the remaining obligations. Establish `hne : LinearMap.ker ((f x)⁻¹ • f) ≠ ⊤` using `fun h => by`.

Establish `: x ∈ LinearMap.ker ((f x)⁻¹ • f)` using `h ▸ Submodule.mem_top`. Rewrite `this` using `[LinearMap.mem_ker, hpx]`. Conclude with `one_ne_zero this`. Use `Submodule.finrank_lt hne` as an intermediate fact. Rewrite using `[LinearMap.finrank_range_of_inj hι]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_form {L V₀ V₁ : Type} [Field L] [AddCommGroup V₀] [Module L V₀] [AddCommGroup V₁] [Module L V₁]
    [FiniteDimensional L V₁] (ι : V₀ →ₗ[L] V₁) (hι : Function.Injective ι)
    (hd : finrank L V₁ = finrank L V₀ + 1) (x : V₁) (hx : x ∉ LinearMap.range ι) :
    ∃ p : V₁ →ₗ[L] L, p x = 1 ∧ LinearMap.ker p = LinearMap.range ι := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hle : LinearMap.range ι ≤ LinearMap.ker ((f x)⁻¹ • f) := by
    intro y hy
    have : f y = 0 := by
      have : f y ∈ (LinearMap.range ι).map f := ⟨y, hy, rfl⟩
      rwa [hf0, Submodule.mem_bot] at this
    simp [this]
  have hpx : ((f x)⁻¹ • f) x = 1 := by simp [hf]
  refine ⟨(f x)⁻¹ • f, hpx, (Submodule.eq_of_le_of_finrank_le hle ?_).symm⟩
  have hne : LinearMap.ker ((f x)⁻¹ • f) ≠ ⊤ := fun h => by
    have : x ∈ LinearMap.ker ((f x)⁻¹ • f) := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hpx] at this
    exact one_ne_zero this
  have := Submodule.finrank_lt hne
  rw [LinearMap.finrank_range_of_inj hι]
  omega

/- English proof (translation)
Introduce `l _ P AI _ K LL V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ ι hιρ hι hd hV x hx c hc`. Use `haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2`. Take `⟨p, hpx, hk⟩` from `exists_form ι hι hd x hx`. Establish `hex : Function.Exact ι p` using `LinearMap.exact_iff.2 hk`. Establish `hs : Function.Surjective p` using `fun a => ⟨a • x, by simp [hpx]⟩`.

Establish `hinv : ∀ g y, p (ρ₁ g y) = p y`. Introduce `g y`. Take `⟨v, hv⟩` from `(hex (y - p y • x)).1 (by simp [hpx])`. Establish `h1 : ρ₁ g y = ι (ρ₀ g v) + p y • (ι (c g) + x)`. Rewrite using `[hιρ, hv, hc, map_sub, map_smul, sub_add_cancel, sub_add_cancel]`.

Rewrite using `[h1]`. Simplify using `[hex.apply_apply_eq_zero, hpx]`. Establish `h : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt ρ₀ ρ₁ ι p` using `⟨hι, hex, hs, hιρ, hinv⟩`. Establish `hc' : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsCocycleOf ρ₁ ι p c` using `⟨x, hpx, fun g => by rw [hc, add_sub_cancel]⟩`. Rewrite using `[GlobalTheory.CrysExt.isCrys_iff_surjective (P.PD K) hV h, ← GlobalTheory.CrysExt.lift_iff_surjective (P.PD K) h, ← GlobalTheory.CrysExt.coboundary_iff_lift (P.PD K) h hc']`.
-/
theorem coboundary_iff_isCrys : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V₀ : Type) [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₀] (ρ₀ : Representation ↥LL.1 ↥(GK K) V₀) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (ι : V₀ →ₗ[↥LL.1] V₁), (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → Function.Injective ι → finrank ↥LL.1 V₁ = finrank ↥LL.1 V₀ + 1 → IsCrys (P.PD K) ρ₀ → ∀ x : V₁, x ∉ LinearMap.range ι → ∀ c : ↥(GK K) → V₀, (∀ g, ι (c g) = ρ₁ g x - x) → ((∃ y : V₀ ⊗[ℚ_[l]] P.R.B, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) ρ₀ g y - y) ↔ IsCrys (P.PD K) ρ₁) := by
  intro l _ P AI _ K LL V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ ι hιρ hι hd hV x hx c hc
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨p, hpx, hk⟩ := exists_form ι hι hd x hx
  have hex : Function.Exact ι p := LinearMap.exact_iff.2 hk
  have hs : Function.Surjective p := fun a => ⟨a • x, by simp [hpx]⟩
  have hinv : ∀ g y, p (ρ₁ g y) = p y := by
    intro g y
    obtain ⟨v, hv⟩ := (hex (y - p y • x)).1 (by simp [hpx])
    have h1 : ρ₁ g y = ι (ρ₀ g v) + p y • (ι (c g) + x) := by
      rw [hιρ, hv, hc, map_sub, map_smul, sub_add_cancel, sub_add_cancel]
    rw [h1]
    simp [hex.apply_apply_eq_zero, hpx]
  have h : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt ρ₀ ρ₁ ι p := ⟨hι, hex, hs, hιρ, hinv⟩
  have hc' : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsCocycleOf ρ₁ ι p c := ⟨x, hpx, fun g => by rw [hc, add_sub_cancel]⟩
  rw [GlobalTheory.CrysExt.isCrys_iff_surjective (P.PD K) hV h, ← GlobalTheory.CrysExt.lift_iff_surjective (P.PD K) h,
    ← GlobalTheory.CrysExt.coboundary_iff_lift (P.PD K) h hc']

end GlobalTheory.CrysExtCrit
