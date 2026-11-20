import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannFormStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

/- English proof (translation)
Take `⟨β, hβ⟩` from `PowSec.exists_basis_sections hH ℂ P 1 le_rfl`. Establish `i₀ : Fin (1 ^ P.g)` using `⟨0, by simp⟩`. Establish `su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀` using `fun q => Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)`. Take `⟨a, ha, -⟩` from `hβ s`. Take `⟨b, hb, -⟩` from `hβ t`.

Establish `hc : ∀ U : P.A.left.Opens, ∃ e : ℂ →+* Γ(P.A.left, U), ∀ x, constFn P.A.hom U x = e x` using `fun U => ⟨((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ P.A.hom.appLE ⊤ U (fun _ _ => trivial)).hom, fun _ => rfl⟩`. Establish `ha0 : a i₀ ≠ 0`. Introduce `h0`. Apply `hθ` to reduce the goal to its premises. Use function extensionality and compare the values at `z`.

Establish `hm : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ (⊤ : P.A.left.Opens)` using `trivial`. Rewrite `hm` using `[← P.isLB.cover]`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hm`. Establish `hi₁ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i` using `(top_le_preimage_iff_mem _ _).2 hi`. Establish `hi₂ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i)` using `(top_le_preimage_iff_mem _ _).2 (Set.mem_iInter.2 fun _ => hi)`.

Establish `e` using `hs (fun _ => i) z hi₂`. Take `⟨c, hc'⟩` from `hc ((lbPow P.L 1).U (fun _ => i))`. Establish `e0` using `(ha (fun _ => i)).trans (su _)`. Rewrite `e0` using `[h0, hc', map_zero, zero_mul]`. Establish `e1` using `e.symm.trans ((congrArg (valAt' _ _) e0).trans (valAt'_zero _ _))`.

Rewrite `e1` using `[pow_one]`. Conclude with `(mul_eq_zero.1 e1).resolve_right (u.fr_ne i z hi₁)`. Use `⟨b i₀ / a i₀, fun j => ?_⟩` and prove the remaining obligations. Take `⟨c, hc'⟩` from `hc ((lbPow P.L 1).U j)`. Rewrite using `[ha, hb, su, su, hc', hc', hc', ← _root_.mul_assoc, ← map_mul, div_mul_cancel₀ _ ha0]`.
-/
theorem exists_const_mul_of_isFnPow_ne_zero (hH : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    (θ : (Fin P.g → ℂ) → ℂ) (hθ : θ ≠ 0) (s : (lbPow P.L 1).Sec) (hs : u.IsFnPow 1 s θ) (t : (lbPow P.L 1).Sec) :
    ∃ a : ℂ, ∀ j, t.f j = constFn P.A.hom _ a * s.f j := by
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hH ℂ P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  obtain ⟨a, ha, -⟩ := hβ s
  obtain ⟨b, hb, -⟩ := hβ t
  have hc : ∀ U : P.A.left.Opens, ∃ e : ℂ →+* Γ(P.A.left, U), ∀ x, constFn P.A.hom U x = e x := fun U =>
    ⟨((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ P.A.hom.appLE ⊤ U (fun _ _ => trivial)).hom, fun _ => rfl⟩
  have ha0 : a i₀ ≠ 0 := by
    intro h0
    apply hθ
    funext z
    have hm : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ (⊤ : P.A.left.Opens) := trivial
    rw [← P.isLB.cover] at hm
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    have hi₁ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i := (top_le_preimage_iff_mem _ _).2 hi
    have hi₂ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) :=
      (top_le_preimage_iff_mem _ _).2 (Set.mem_iInter.2 fun _ => hi)
    have e := hs (fun _ => i) z hi₂
    obtain ⟨c, hc'⟩ := hc ((lbPow P.L 1).U (fun _ => i))
    have e0 := (ha (fun _ => i)).trans (su _)
    rw [h0, hc', map_zero, zero_mul] at e0
    have e1 := e.symm.trans ((congrArg (valAt' _ _) e0).trans (valAt'_zero _ _))
    rw [pow_one] at e1
    exact (mul_eq_zero.1 e1).resolve_right (u.fr_ne i z hi₁)
  refine ⟨b i₀ / a i₀, fun j => ?_⟩
  obtain ⟨c, hc'⟩ := hc ((lbPow P.L 1).U j)
  rw [ha, hb, su, su, hc', hc', hc', ← _root_.mul_assoc, ← map_mul, div_mul_cancel₀ _ ha0]

/- English proof (translation)
Introduce `hL hL2 hG hU P u Hm χ θ T _ p hAH hθ hne`. Take `⟨-, -, -, -, -, -, -, hsec, -⟩` from `GlobalTheory.T.appellHumbert_uniformisation_riemannForm hL hL2 hG hU P u Hm χ hAH`. Take `⟨s, hs, -⟩` from `(hsec 1).2 θ hθ`. Establish `hT : ∀ {X : Over (Sp ℂ)} (f g : X ⟶ T), f = g` using `fun f g => Over.OverMorphism.ext ((cancel_mono T.hom).1 ((Over.w f).trans (Over.w g).symm))`. Set `ρ : P.A ⟶ T ⊗ P.A` to `lift (toUnit _ ≫ p) (𝟙 _)`.

Establish `r₂ : ρ ≫ snd T P.A = 𝟙 _` using `lift_snd _ _`. Establish `r₃ : snd T P.A ≫ ρ = 𝟙 _` using `CartesianMonoidalCategory.hom_ext _ _ (hT _ _) (by rw [Category.assoc, r₂, Category.comp_id, Category.id_comp])`. Establish `ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _` using `congrArg (fun q => q.left) r₂`. Establish `ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _` using `congrArg (fun q => q.left) r₃`. Establish `ρ₁ : ρ.left ≫ (fst T P.A).left ≫ T.hom = P.A.hom` using `Over.w (ρ ≫ fst T P.A)`.

Use `haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩`. Take `⟨th, hth⟩` from `PowSec.down_surjective P.L (snd T P.A).left ρ.left ρ₂ ((1 : ℕ) : ℤ) s`. Use `⟨th, fun t => ?_, fun j z hz => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_const_mul_of_isFnPow_ne_zero hL.globalSectionsRank P u θ hne s hs (PowSec.down P.L (snd T P.A).left ρ.left ρ₂ ((1 : ℕ) : ℤ) t)`. Use `⟨T.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a), fun j => ?_⟩` and prove the remaining obligations.

Take `⟨k, rfl⟩ : ∃ k, j = fun _ => k` from `⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩`. Establish `hch` using `PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)`. Use `PowSec.appLE_injective ρ.left _ _ hch ?_` and prove the remaining obligations. Use `(ha (fun _ => k)).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (map_mul (ρ.left.appLE _ _ hch.le).hom _ _).symm)` and prove the remaining obligations. Establish `h0 : (T.hom.appTop ≫ (fst T P.A).left.appTop ≫ (T ⊗ P.A).left.presheaf.map (homOfLE le_top).op) = ((fst T P.A).left ≫ T.hom).appLE ⊤ (LB.wchart P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => k)) (fun _ _ => trivial)`.

Rewrite using `[← Category.assoc, ← Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression. Establish `h1` using `(Scheme.Hom.appLE_comp_appLE ρ.left ((fst T P.A).left ≫ T.hom) ⊤ _ _ (fun _ _ => trivial) hch.le).trans (PowSec.appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))`. Rewrite `h1` using `[← h0]`. Conclude with `(congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) h1).symm`.

Rewrite using `[← hth]`. Both sides reduce to the same expression. Take `⟨k, rfl⟩ : ∃ k, j = fun _ => k` from `⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩`. Establish `hch` using `PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)`. Establish `hz₂ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => k)` using `(top_le_preimage_iff_mem _ _).2 (Set.mem_iInter.2 fun _ => (top_le_preimage_iff_mem _ _).1 hz)`.

Establish `e` using `hs (fun _ => k) z hz₂`. Establish `e₁ : lift p (u.ex z) = u.ex z ≫ ρ` using `CartesianMonoidalCategory.hom_ext _ _ (hT _ _) (by rw [Category.assoc, r₂, Category.comp_id, lift_snd])`. Establish `e₂` using `valAt'_appLE (u.ex z).left ρ.left _ _ hch.le (th.f (fun _ => k)) hz₂`. Rewrite using `[e₁, zpow_one]`. Rewrite `e` using `[← hth, pow_one]`.

Conclude with `e₂.symm.trans e`.
-/
theorem exists_isGenSec_of_isThetaFn : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T), u.IsAH Hm χ → u.IsThetaFn Hm χ 1 θ → θ ≠ 0 → ∃ th : LB.Sec (Out.LPow P.A P.L 1 T), Out.IsGenSec P.A P.L 1 th ∧ (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L 1 T).U j) (th.f j) = θ z * u.fr (j 0) z ^ (1 : ℤ)) := by
  intro hL hL2 hG hU P u Hm χ θ T _ p hAH hθ hne
  obtain ⟨-, -, -, -, -, -, -, hsec, -⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm hL hL2 hG hU P u Hm χ hAH
  obtain ⟨s, hs, -⟩ := (hsec 1).2 θ hθ
  have hT : ∀ {X : Over (Sp ℂ)} (f g : X ⟶ T), f = g := fun f g =>
    Over.OverMorphism.ext ((cancel_mono T.hom).1 ((Over.w f).trans (Over.w g).symm))
  let ρ : P.A ⟶ T ⊗ P.A := lift (toUnit _ ≫ p) (𝟙 _)
  have r₂ : ρ ≫ snd T P.A = 𝟙 _ := lift_snd _ _
  have r₃ : snd T P.A ≫ ρ = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ (hT _ _) (by rw [Category.assoc, r₂, Category.comp_id, Category.id_comp])
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) r₂
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := congrArg (fun q => q.left) r₃
  have ρ₁ : ρ.left ≫ (fst T P.A).left ≫ T.hom = P.A.hom := Over.w (ρ ≫ fst T P.A)
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  obtain ⟨th, hth⟩ := PowSec.down_surjective P.L (snd T P.A).left ρ.left ρ₂ ((1 : ℕ) : ℤ) s
  refine ⟨th, fun t => ?_, fun j z hz => ?_⟩
  · obtain ⟨a, ha⟩ := exists_const_mul_of_isFnPow_ne_zero hL.globalSectionsRank P u θ hne s hs
      (PowSec.down P.L (snd T P.A).left ρ.left ρ₂ ((1 : ℕ) : ℤ) t)
    refine ⟨T.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a), fun j => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    have hch := PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)
    refine PowSec.appLE_injective ρ.left _ _ hch ?_
    refine (ha (fun _ => k)).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (map_mul (ρ.left.appLE _ _ hch.le).hom _ _).symm)
    · have h0 : (T.hom.appTop ≫ (fst T P.A).left.appTop ≫ (T ⊗ P.A).left.presheaf.map (homOfLE le_top).op) =
          ((fst T P.A).left ≫ T.hom).appLE ⊤ (LB.wchart P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => k))
            (fun _ _ => trivial) := by
        rw [← Category.assoc, ← Scheme.Hom.comp_appTop]; rfl
      have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left ((fst T P.A).left ≫ T.hom) ⊤ _ _ (fun _ _ => trivial)
        hch.le).trans (PowSec.appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
      rw [← h0] at h1
      exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) h1).symm
    · rw [← hth]; rfl
  · obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    have hch := PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)
    have hz₂ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => k) :=
      (top_le_preimage_iff_mem _ _).2 (Set.mem_iInter.2 fun _ => (top_le_preimage_iff_mem _ _).1 hz)
    have e := hs (fun _ => k) z hz₂
    have e₁ : lift p (u.ex z) = u.ex z ≫ ρ :=
      CartesianMonoidalCategory.hom_ext _ _ (hT _ _) (by rw [Category.assoc, r₂, Category.comp_id, lift_snd])
    have e₂ := valAt'_appLE (u.ex z).left ρ.left _ _ hch.le (th.f (fun _ => k)) hz₂
    rw [e₁, zpow_one]
    rw [← hth, pow_one] at e
    exact e₂.symm.trans e

end GlobalTheory
