import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinOfIsPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BasisGenericExtendsSectionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BasisLevelZeroSectionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionBasisDomainRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BasisLocalRingReductionStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

/- English proof (translation)
Introduce `W _ _ _ n d`. Set `K` to `FractionRing W`. Set `v` to `ValuationRing.valuation W K`. Establish `integ : ∀ x : K, v x ≤ 1 → ∃ a, algebraMap W K a = x` using `fun x hx => (ValuationRing.mem_integer_iff W K x).1 hx`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Conclude with `Or.inl ⟨Fin.elim0, fun i => i.elim0⟩`. Take `⟨j, -, hj⟩` from `Finset.exists_max_image Finset.univ (fun i => v (d i)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩`. Distinguish the cases in `h : v (d j) ≤ 1`. Use `left choose c hc using fun i => integ (d i) ((hj i (Finset.mem_univ _)).trans h)`. Conclude with `⟨c, hc⟩`.

Use `right replace h := not_le.1 h`. Establish `hd : d j ≠ 0` using `fun e => by rw [e, map_zero] at h; exact absurd h (not_lt.2 zero_le_one)`. Establish `hv : ∀ i, v (d i * (d j)⁻¹) ≤ 1` using `fun i => by`. Rewrite using `[map_mul, map_inv₀]`. Conclude with `(div_le_one₀ (lt_trans zero_lt_one h)).2 (hj i (Finset.mem_univ _))`.

Use `choose c hc using fun i => integ _ (hv i)`. Take `⟨a, ha⟩` from `integ (d j)⁻¹ (by`. Rewrite using `[map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ h.le)`. Use `⟨a, c, j, ?_, IsFractionRing.injective W K (by rw [hc, map_one, mul_inv_cancel₀ hd]), fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce and unpack `⟨u, rfl⟩`. Apply `not_le.2 h` to reduce the goal to its premises. Establish `: d j = algebraMap W K (↑u⁻¹ : W)`. Rewrite using `[← inv_inv (d j), ← ha, ← map_units_inv]`.

Rewrite using `[this]`. Conclude with `(ValuationRing.mem_integer_iff W K _).2 ⟨_, rfl⟩`. Rewrite using `[hc, ha, mul_comm]`.
-/
theorem valPick : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (n : ℕ)
    (d : Fin n → FractionRing W),
    (∃ c : Fin n → W, ∀ i, algebraMap W (FractionRing W) (c i) = d i) ∨
    ∃ (a : W) (c : Fin n → W) (j : Fin n), a ∈ maximalIdeal W ∧ c j = 1 ∧
      ∀ i, algebraMap W (FractionRing W) (c i) = algebraMap W (FractionRing W) a * d i := by
  intro W _ _ _ n d
  let K := FractionRing W
  let v := ValuationRing.valuation W K
  have integ : ∀ x : K, v x ≤ 1 → ∃ a, algebraMap W K a = x := fun x hx =>
    (ValuationRing.mem_integer_iff W K x).1 hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl ⟨Fin.elim0, fun i => i.elim0⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => v (d i)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  by_cases h : v (d j) ≤ 1
  · left
    choose c hc using fun i => integ (d i) ((hj i (Finset.mem_univ _)).trans h)
    exact ⟨c, hc⟩
  · right
    replace h := not_le.1 h
    have hd : d j ≠ 0 := fun e => by rw [e, map_zero] at h; exact absurd h (not_lt.2 zero_le_one)
    have hv : ∀ i, v (d i * (d j)⁻¹) ≤ 1 := fun i => by
      rw [map_mul, map_inv₀]
      exact (div_le_one₀ (lt_trans zero_lt_one h)).2 (hj i (Finset.mem_univ _))
    choose c hc using fun i => integ _ (hv i)
    obtain ⟨a, ha⟩ := integ (d j)⁻¹ (by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ h.le)
    refine ⟨a, c, j, ?_, IsFractionRing.injective W K (by rw [hc, map_one, mul_inv_cancel₀ hd]), fun i => ?_⟩
    · rw [mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, rfl⟩
      apply not_le.2 h
      have : d j = algebraMap W K (↑u⁻¹ : W) := by
        rw [← inv_inv (d j), ← ha, ← map_units_inv]
      rw [this]
      exact (ValuationRing.mem_integer_iff W K _).2 ⟨_, rfl⟩
    · rw [hc, ha, mul_comm]

end GlobalTheory.TorRef
namespace GlobalTheory.TorRef

/- English proof (translation)
Introduce `E _ _ _ H R _ _ _ t P N n b hb hind W _ _ _ hW φ hφ s`. Establish `hW1 : IsDiscreteValuationRing W` using `((cDvr_iff W).1 hW).1`. Establish `hK : Function.Injective (algebraMap W (FractionRing W))` using `IsFractionRing.injective W (FractionRing W)`. Establish `hψ : Function.Injective ((algebraMap W (FractionRing W)).comp φ)` using `hK.comp hφ`. Take `⟨s', hs'⟩` from `GlobalTheory.FramePull.exists_isPull (jC φ (algebraMap W (FractionRing W))) s`.

Establish `hsL` using `lin_of_isPull hs'`. Establish `uniq : ∀ c c', Lin t.G t.PP.L N (toBase φ) b c s → Lin t.G t.PP.L N (toBase φ) b c' s → c = c'`. Introduce `c c' h h'`. Establish `e₁` using `lin_comp _ _ h hsL`. Establish `e₂` using `lin_comp _ _ h' hsL`.

Rewrite `e₁`, `e₂` using `[jC_toBase]`. Establish `e` using `hind (FractionRing W) ((algebraMap W (FractionRing W)).comp φ) _ _ s' e₁ e₂`. Use function extensionality and compare the values at `i`. Conclude with `GlobalTheory.FrameGen.appTop_injective _ hK (congrFun e i)`. Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d, Lin t.G t.PP.L N (toBase ((algebraMap W (FractionRing W)).comp φ)) b d s' := by`.

Break down `Nat.eq_zero_or_pos N with hN | hN` into its components or cases. Conclude with `GlobalTheory.T.basis_level_zero_sections E H R t P N n b hN hb _ _ hψ s'`. Conclude with `GlobalTheory.T.basis_generic_extends_sections E H R t P N n b hN hb _ _ hψ s'`. Set `ε` to `(Scheme.ΓSpecIso (CommRingCat.of (FractionRing W))).commRingCatIsoToRingEquiv`. Establish `hε : ∀ i, GlobalTheory.OneBasis.fnR (ε (d i)) = d i` using `fun i => ε.symm_apply_apply (d i)`.

Break down `valPick W n (fun i => ε (d i)) with ⟨c, hc⟩ | ⟨a, c, j, ha, hcj, hc⟩` into its components or cases. Establish `hA : LinA t.G t.PP.L N (toBase ((algebraMap W (FractionRing W)).comp φ)) b (fun i => GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) (c i))) (GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) 1)) s'`. Use `lin_iff_linA.1 hd` as an intermediate fact. Simplify `this` using `only [hc, hε, map_one]`. Establish `h2` using `GlobalTheory.T.section_basis_domain_relation E H R t N n b W φ c 1 s s' hsL hA`.

Rewrite `h2` using `[fnR_one, ← lin_iff_linA]`. Conclude with `⟨_, h2, fun c' hc' => uniq _ _ hc' h2⟩`. It suffices to derive a contradiction. Establish `hA : LinA t.G t.PP.L N (toBase ((algebraMap W (FractionRing W)).comp φ)) b (fun i => GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) (c i))) (GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) a)) s'`. Use `linA_scale (GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) a)) hd` as an intermediate fact.

Simplify `this` using `only [hc, map_mul, hε]`. Establish `h2` using `GlobalTheory.T.section_basis_domain_relation E H R t N n b W φ c a s s' hsL hA`. Take `⟨z, hz₁, hz₀⟩` from `GlobalTheory.T.basis_local_ring_reduction E H R t N n b W φ c a s ha h2`. Establish `e` using `congrFun (hind (ResidueField W) ((residue W).comp φ) _ _ z hz₁ hz₀) j`. Rewrite `e` using `[hcj, map_one, fnR_one]`.

Express the relevant statement in the definitionally equal form `(1 : Γ(Sp (ResidueField W), ⊤)) = 0 at e`. Use `haveI := GlobalTheory.FrameGen.nontrivial_top (ResidueField W)`. Conclude with `one_ne_zero e`.
-/
theorem freeTrait : FreeTraitSt := by
  intro E _ _ _ H R _ _ _ t P N n b hb hind W _ _ _ hW φ hφ s
  have hW1 : IsDiscreteValuationRing W := ((cDvr_iff W).1 hW).1
  have hK : Function.Injective (algebraMap W (FractionRing W)) := IsFractionRing.injective W (FractionRing W)
  have hψ : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := hK.comp hφ
  obtain ⟨s', hs'⟩ := GlobalTheory.FramePull.exists_isPull (jC φ (algebraMap W (FractionRing W))) s
  have hsL := lin_of_isPull hs'
  have uniq : ∀ c c', Lin t.G t.PP.L N (toBase φ) b c s → Lin t.G t.PP.L N (toBase φ) b c' s → c = c' := by
    intro c c' h h'
    have e₁ := lin_comp _ _ h hsL
    have e₂ := lin_comp _ _ h' hsL
    rw [jC_toBase] at e₁ e₂
    have e := hind (FractionRing W) ((algebraMap W (FractionRing W)).comp φ) _ _ s' e₁ e₂
    funext i
    exact GlobalTheory.FrameGen.appTop_injective _ hK (congrFun e i)
  obtain ⟨d, hd⟩ : ∃ d, Lin t.G t.PP.L N (toBase ((algebraMap W (FractionRing W)).comp φ)) b d s' := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · exact GlobalTheory.T.basis_level_zero_sections E H R t P N n b hN hb _ _ hψ s'
    · exact GlobalTheory.T.basis_generic_extends_sections E H R t P N n b hN hb _ _ hψ s'
  let ε := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing W))).commRingCatIsoToRingEquiv
  have hε : ∀ i, GlobalTheory.OneBasis.fnR (ε (d i)) = d i := fun i => ε.symm_apply_apply (d i)
  rcases valPick W n (fun i => ε (d i)) with ⟨c, hc⟩ | ⟨a, c, j, ha, hcj, hc⟩
  · have hA : LinA t.G t.PP.L N (toBase ((algebraMap W (FractionRing W)).comp φ)) b
        (fun i => GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) (c i)))
        (GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) 1)) s' := by
      have := lin_iff_linA.1 hd
      simpa only [hc, hε, map_one] using this
    have h2 := GlobalTheory.T.section_basis_domain_relation E H R t N n b W φ c 1 s s' hsL hA
    rw [fnR_one, ← lin_iff_linA] at h2
    exact ⟨_, h2, fun c' hc' => uniq _ _ hc' h2⟩
  · exfalso
    have hA : LinA t.G t.PP.L N (toBase ((algebraMap W (FractionRing W)).comp φ)) b
        (fun i => GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) (c i)))
        (GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) a)) s' := by
      have := linA_scale (GlobalTheory.OneBasis.fnR (algebraMap W (FractionRing W) a)) hd
      simpa only [hc, map_mul, hε] using this
    have h2 := GlobalTheory.T.section_basis_domain_relation E H R t N n b W φ c a s s' hsL hA
    obtain ⟨z, hz₁, hz₀⟩ := GlobalTheory.T.basis_local_ring_reduction E H R t N n b W φ c a s ha h2
    have e := congrFun (hind (ResidueField W) ((residue W).comp φ) _ _ z hz₁ hz₀) j
    rw [hcj, map_one, fnR_one] at e
    change (1 : Γ(Sp (ResidueField W), ⊤)) = 0 at e
    haveI := GlobalTheory.FrameGen.nontrivial_top (ResidueField W)
    exact one_ne_zero e

end GlobalTheory.TorRef
