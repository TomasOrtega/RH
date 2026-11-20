import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealOfFlatStalkPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuasiCompactQuasiSeparatedOverBaseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupStalkEtaleResidueUnramStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStalkIdealOfCodimOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdealPowComapPrincipalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdealEqTopDimZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupBoundaryDivisorCartierStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.MixedLower

/- English proof (translation)
Establish `h0` using `ringKrullDim_nonneg_of_nontrivial (R := A)`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ∞, ringKrullDim A = m := by`. Consider the cases of `hA : ringKrullDim A with`. Consider the case `bot => rw [hA] at h0; exact absurd h0 (by simp)`. Consider the case `coe m => exact ⟨m, rfl⟩`.

Rewrite `h`, the goal using `[hm]`. Establish `h' : m ≤ 1` using `by exact_mod_cast h`. Proceed by induction on `m using ENat.recTopCoe with`. Consider the case `top => exact absurd h' (by simp)`. Consider the case `coe m`.

Establish `: m ≤ 1` using `by exact_mod_cast h'`. Use `interval_cases m`. Use `left`. Both sides reduce to the same expression. Use `right`.

Both sides reduce to the same expression.
-/
theorem ringKrullDim_eq_zero_or_one {A : Type} [CommRing A] [Nontrivial A] (h : ringKrullDim A ≤ 1) :
    ringKrullDim A = 0 ∨ ringKrullDim A = 1 := by
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := A)
  obtain ⟨m, hm⟩ : ∃ m : ℕ∞, ringKrullDim A = m := by
    cases hA : ringKrullDim A with
    | bot => rw [hA] at h0; exact absurd h0 (by simp)
    | coe m => exact ⟨m, rfl⟩
  rw [hm] at h ⊢
  have h' : m ≤ 1 := by exact_mod_cast h
  induction m using ENat.recTopCoe with
  | top => exact absurd h' (by simp)
  | coe m =>
    have : m ≤ 1 := by exact_mod_cast h'
    interval_cases m
    · left; rfl
    · right; rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX hg hφs hRef hCones hN4 hPol hd' hY hB R _ _ _ ξ t mξ P k' γ hCN hEt hFU hTI hCone hIn ℓ hℓ h hh`. Take `⟨hqc, hqs⟩` from `GlobalTheory.T.quasiCompact_quasiSeparated_over_base E H D l Xo c X Z π hB.2.2.1`. Rewrite using `[hB.2.2.2.2.2.2.1]`. Establish `hN` using `GlobalTheory.T.blowup_stalk_etale_residue_unram E H D l Xo c X Z Y π e hB.2.1 hB.2.2.1 hB.2.2.2.1 R ξ hCN hEt hFU`. Use `GlobalTheory.T.mem_ideal_of_flat_stalk_pullback (e.hom ≫ genι Z ≫ π) ((BY.idealSheaf ^ n).comap (genι Y)) ξ hEt.1 h ?_` and prove the remaining obligations.

Use `GlobalTheory.T.mem_stalk_ideal_of_codim_one _ (((BY.idealSheaf ^ n).comap (genι Y)).comap (pullback.snd ξ (e.hom ≫ genι Z ≫ π))) hN (fun w => ?_) _ (fun w hw => ?_)` and prove the remaining obligations. Rewrite using `[← Scheme.IdealSheafData.comap_comp]`. Conclude with `GlobalTheory.T.stalk_ideal_pow_comap_principal BY n _ w`. Break down `ringKrullDim_eq_zero_or_one hw with h0 | h1` into its components or cases. Rewrite using `[GlobalTheory.T.stalk_ideal_eq_top_dim_zero (e.hom ≫ genι Z ≫ π) (genι Y) BY n ξ hEt.1 w h0]`.

Discharge the goal by the elementary cases of `trivial`. Establish `hO1` using `@GlobalTheory.T.blowup_boundary_divisor_cartier E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX hg hφs hRef hCones hN4 hPol hd' hY hB R _ _ _ ξ t mξ P k' γ hCN hEt hFU hTI hCone hIn hN w h1`. Take `⟨W, _, _, _, ϖ, gv, B, hW, hϖ, hbal, hFA, hmem⟩` from `hO1`. Apply `hmem` to reduce the goal to its premises. Establish `hpsd : ∀ y, 0 ≤ B y y` using `fun y => by`.

Take `⟨r, n₀, -, hr, -⟩` from `hFA y`. Rewrite using `[hr]`. Check the signs of the components of the expression. Establish `hcone : GlobalTheory.ChartMono.InRealCone γ B` using `hIn W hW ϖ hϖ _ B hbal.1 hFA`. Establish `h1'` using `hℓ B hbal hpsd hcone`.

Establish `hφ0 : 0 ≤ φ.evalZ B` using `hRef.2.2.2.2.1.2 _ _`. Establish `hℓ0 : 0 ≤ ℓ B`. Establish `: (0 : ℝ) ≤ ℓ B` using `le_trans (mul_nonneg (Nat.cast_nonneg _) hφ0) h1'`. Conclude with `this` after adjusting the coercions. Take `⟨m, hm⟩` from `Int.eq_ofNat_of_zero_le hℓ0`.

Establish `ha` using `hh W hW ϖ hϖ _ B hbal.1 hFA m hm.symm`. Use `⟨m, ?_, ha.symm.dvd⟩` and prove the remaining obligations. Rewrite `h1'` using `[hm]`. Conclude with `h1'` after adjusting the coercions.
-/
theorem mem_idlAlong_of_traitMono : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X → X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (t : SAB H (Sp R)), SABMap t X.t ξ → ∀ (P : PELUnif (maximalIdeal R) t) (k' : ℕ) (γ : Fin k' → LinearMap.BilinForm ℤ P.D.toPre.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ConeZ E φs P.D.toPre.X k' γ → InCone P.D.toPre γ → ∀ ℓ : LinearMap.BilinForm ℤ P.D.toPre.X →ₗ[ℤ] ℤ, (∀ β ∈ balForms H.bar P.D.toPre.X, (∀ y, 0 ≤ β y y) → GlobalTheory.ChartMono.InRealCone γ β → ((n * d' : ℕ) : ℝ) * φ.evalZ β ≤ ℓ β) → ∀ h : R, GlobalTheory.ChartMono.TraitMono P.D.toPre ℓ h → h ∈ idlAlong J ξ := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX hg hφs hRef hCones hN4 hPol hd' hY hB R _ _ _ ξ t mξ P k' γ hCN hEt hFU hTI hCone hIn ℓ hℓ h hh
  obtain ⟨hqc, hqs⟩ := GlobalTheory.T.quasiCompact_quasiSeparated_over_base E H D l Xo c X Z π hB.2.2.1
  rw [hB.2.2.2.2.2.2.1]
  have hN := GlobalTheory.T.blowup_stalk_etale_residue_unram E H D l Xo c X Z Y π e hB.2.1 hB.2.2.1 hB.2.2.2.1 R ξ hCN hEt hFU
  refine GlobalTheory.T.mem_ideal_of_flat_stalk_pullback (e.hom ≫ genι Z ≫ π) ((BY.idealSheaf ^ n).comap (genι Y)) ξ hEt.1 h ?_
  refine GlobalTheory.T.mem_stalk_ideal_of_codim_one _ (((BY.idealSheaf ^ n).comap (genι Y)).comap (pullback.snd ξ (e.hom ≫ genι Z ≫ π))) hN
    (fun w => ?_) _ (fun w hw => ?_)
  · rw [← Scheme.IdealSheafData.comap_comp]
    exact GlobalTheory.T.stalk_ideal_pow_comap_principal BY n _ w
  · rcases ringKrullDim_eq_zero_or_one hw with h0 | h1
    · rw [GlobalTheory.T.stalk_ideal_eq_top_dim_zero (e.hom ≫ genι Z ≫ π) (genι Y) BY n ξ hEt.1 w h0]
      trivial
    · have hO1 := @GlobalTheory.T.blowup_boundary_divisor_cartier E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX
        hg hφs hRef hCones hN4 hPol hd' hY hB R _ _ _ ξ t mξ P k' γ hCN hEt hFU hTI hCone hIn hN w h1
      obtain ⟨W, _, _, _, ϖ, gv, B, hW, hϖ, hbal, hFA, hmem⟩ := hO1
      apply hmem
      have hpsd : ∀ y, 0 ≤ B y y := fun y => by
        obtain ⟨r, n₀, -, hr, -⟩ := hFA y
        rw [hr]; positivity
      have hcone : GlobalTheory.ChartMono.InRealCone γ B := hIn W hW ϖ hϖ _ B hbal.1 hFA
      have h1' := hℓ B hbal hpsd hcone
      have hφ0 : 0 ≤ φ.evalZ B := hRef.2.2.2.2.1.2 _ _
      have hℓ0 : 0 ≤ ℓ B := by
        have : (0 : ℝ) ≤ ℓ B := le_trans (mul_nonneg (Nat.cast_nonneg _) hφ0) h1'
        exact_mod_cast this
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hℓ0
      have ha := hh W hW ϖ hϖ _ B hbal.1 hFA m hm.symm
      refine ⟨m, ?_, ha.symm.dvd⟩
      rw [hm] at h1'
      exact_mod_cast h1'

end GlobalTheory.MixedLower
