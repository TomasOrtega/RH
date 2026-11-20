import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexCongruenceSubgroupLeAbsNormPowStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHermitianLatticeOfDeepStarCongruenceStatement

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.WtSkew

/- English proof (translation)
Unfold `GlobalTheory.HL.invVol`. Break down `Nat.eq_zero_or_pos (A.relIndex B) with h | h` into its components or cases. Simplify using `[h]`. Conclude with `div_le_self (Nat.cast_nonneg _) (by exact_mod_cast h)`.
-/
theorem invVol_le_relIndex {G : Type} [Group G] (A B : Subgroup G) :
    GlobalTheory.HL.invVol A B ≤ (B.relIndex A : ℝ) := by
  unfold GlobalTheory.HL.invVol
  rcases Nat.eq_zero_or_pos (A.relIndex B) with h | h
  · simp [h]
  · exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast h)

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

omit [NumberField K] [StarRing K] in
/- English proof (translation)
Introduce and unpack `_ ⟨t, -, rfl⟩`. Conclude with `S.smul_mem t h`.
-/
theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (h : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨t, -, rfl⟩
  exact S.smul_mem t h

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, a.2, rfl⟩`.
-/
theorem e_mem_X (F : FlagD H r) (a : Fin r) : F.e a.castSucc ∈ F.X :=
  Submodule.subset_span ⟨a, a.2, rfl⟩

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
The claim follows from `Submodule.mem_sup_right (Submodule.subset_span (by simp))`.
-/
theorem lastVector_mem_jointSpan_left (F F' : FlagD H r) : F.z ∈ V0 F F' :=
  Submodule.mem_sup_right (Submodule.subset_span (by simp))

/- English proof (translation)
Unfold `NF.P0`. Use `sup_le (sup_le (sup_le (iSup_le fun a => line_le ?_) (iSup_le fun a => iSup_le fun _ => line_le ?_)) (line_le ?_)) (iSup_le fun a => iSup_le fun ha => line_le ?_)` and prove the remaining obligations. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X _ a)))`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X _ a)))`. Conclude with `Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)`.

Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩)`.
-/
theorem normalForm_baseLattice_le_dualSpan_sup_line (N : NF H r) : N.P0 ≤ rs (𝓞 K) (V0 N.F N.F' ⊔ N.Ist) := by
  unfold NF.P0
  refine sup_le (sup_le (sup_le (iSup_le fun a => line_le ?_) (iSup_le fun a => iSup_le fun _ => line_le ?_))
    (line_le ?_)) (iSup_le fun a => iSup_le fun ha => line_le ?_)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X _ a)))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X _ a)))
  · exact Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩)

/- English proof (translation)
Establish `h0 : N.P0 ≤ rs (𝓞 K) N.Pi` using `hp ▸ normalForm_baseLattice_le_dualSpan_sup_line N`. Establish `hzP : N.F.z ∈ N.Pi` using `hp ▸ Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)`. Use `le_antisymm ?_ (le_inf le_sup_left h0)` and prove the remaining obligations. Introduce and unpack `x ⟨hx, hxP⟩`. Take `⟨p, hpP, l, ⟨hlL, hlW⟩, rfl⟩` from `Submodule.mem_sup.1 hx`.

Establish `hlW' : l ∈ N.Wt ⊔ Submodule.span K {N.F.z}` using `hn ▸ hlW`. Take `⟨w, hw, y, hy, rfl⟩` from `Submodule.mem_sup.1 hlW'`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Establish `hxP' : p + (w + t • N.F.z) ∈ N.Pi` using `hxP`. Establish `hpP' : p ∈ N.Pi` using `h0 hpP`.

Establish `hwP : w ∈ N.Pi`. Use `N.Pi.sub_mem (N.Pi.sub_mem hxP' hpP') (N.Pi.smul_mem t hzP)` as an intermediate fact. Simplify using `using this`. Establish `hw0 : w = 0` using `(Submodule.disjoint_def.1 hc.disjoint) w hw hwP`. Substitute `hw0` using the available equality.

Rewrite `hlL`, the goal using `[zero_add]`. Use `N.P0.add_mem hpP ?_` and prove the remaining obligations. Unfold `NF.P0`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right ⟨t, hz t hlL, rfl⟩)`.
-/
theorem ref_inf_Pi (N : NF H r) (L : Submodule (𝓞 K) V) (hc : IsCompl N.Wt N.Pi)
    (hn : N.Wn = N.Wt ⊔ Submodule.span K {N.F.z}) (hp : N.Pi = V0 N.F N.F' ⊔ N.Ist)
    (hz : ∀ t : K, t • N.F.z ∈ L → t ∈ (1 : Submodule (𝓞 K) K)) :
    N.Ref L ⊓ rs (𝓞 K) N.Pi = N.P0 := by
  have h0 : N.P0 ≤ rs (𝓞 K) N.Pi := hp ▸ normalForm_baseLattice_le_dualSpan_sup_line N
  have hzP : N.F.z ∈ N.Pi := hp ▸ Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)
  refine le_antisymm ?_ (le_inf le_sup_left h0)
  rintro x ⟨hx, hxP⟩
  obtain ⟨p, hpP, l, ⟨hlL, hlW⟩, rfl⟩ := Submodule.mem_sup.1 hx
  have hlW' : l ∈ N.Wt ⊔ Submodule.span K {N.F.z} := hn ▸ hlW
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hlW'
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hxP' : p + (w + t • N.F.z) ∈ N.Pi := hxP
  have hpP' : p ∈ N.Pi := h0 hpP
  have hwP : w ∈ N.Pi := by
    have := N.Pi.sub_mem (N.Pi.sub_mem hxP' hpP') (N.Pi.smul_mem t hzP)
    simpa using this
  have hw0 : w = 0 := (Submodule.disjoint_def.1 hc.disjoint) w hw hwP
  subst hw0
  rw [zero_add] at hlL ⊢
  refine N.P0.add_mem hpP ?_
  unfold NF.P0
  exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨t, hz t hlL, rfl⟩)

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN`. Take `⟨-, -, hc, hdim, hn, -, -, -, -, -, -, hp⟩` from `GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N`. Take `⟨hR, -⟩` from `GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary K V H hK r N`. Take `⟨-, -, hz, -, hlat, -⟩` from `GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hT`. Establish `hstab` using `GlobalTheory.T.stabilizer_hermitianLattice_of_deep_star_congruence K V H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN`.

Establish `hP` using `ref_inf_Pi N (latL N.F N.F' Λ) hc hn hp (fun t ht => (hz t).1 ht)`. Establish `hfg : N.P0.FG`. Use `Submodule.FG.of_le hlat.fg ?_` and prove the remaining obligations. Rewrite using `[← hP]`. Conclude with `inf_le_left`.

Establish `hmap : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, ∀ x ∈ N.P0, s x ∈ N.P0`. Introduce and unpack `s ⟨⟨hsR, hsS⟩, -, hsW⟩ x hx`. Rewrite `hx`, the goal using `[← hP]`. Establish `hsS' : s • N.Ref (latL N.F N.F' Λ) = N.Ref (latL N.F N.F' Λ)` using `hsS`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hsS']`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ hx.1`. Establish `hx2 : x ∈ perp H N.Wt` using `hx.2`. Express the relevant statement in the definitionally equal form `s x ∈ perp H N.Wt`. Rewrite `hx2`, the goal using `[mem_perp_iff]`.

Introduce `w hw`. Establish `hw' : s w = w` using `(mem_fixingSubgroup_iff _).1 hsW w hw`. Use `((hR s).1 hsR).1.1 x w` as an intermediate fact. Simplify using `only [LinearEquiv.coe_coe, hw'] at this`. Rewrite using `[this]`.

Conclude with `hx2 w hw`. Establish `hfix : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, s • N.P0 = N.P0`. Introduce `s hs`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Introduce `y hy`.

Take `⟨x, hx, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy`. Conclude with `hmap s hs x hx`. Introduce `y hy`. Use `(Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s⁻¹ y, hmap _ (inv_mem hs) y hy, ?_⟩` and prove the remaining obligations. Conclude with `s.apply_symm_apply y`.

Establish `hm : 𝔠 ^ (3 * e + 10) ≠ ⊥` using `pow_ne_zero _ h0`. Take `⟨-, hle⟩` from `GlobalTheory.T.relIndex_congruence_subgroup_le_absNorm_pow K V (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) N.P0 (𝔠 ^ (3 * e + 10)) (N.Gam Λ ⊓ N.ZI) hfg hm hfix (fun s hs hx => ⟨⟨hs.1.1, hstab s ⟨hs.1.1, hs.2.2⟩ hx⟩, hs.2⟩)`. Establish `hrk : Module.finrank K (Submodule.span K (N.P0 : Set V)) ≤ 2 * r + 1`. Establish `h1 : Submodule.span K (N.P0 : Set V) ≤ N.Pi`. Rewrite using `[Submodule.span_le, ← hP]`.

Conclude with `fun x hx => hx.2`. Establish `h2` using `Submodule.finrank_mono h1`. Establish `h3` using `Submodule.finrank_add_eq_of_isCompl hc`. Use linear arithmetic over natural numbers and integers. Establish `hpos : 1 ≤ Ideal.absNorm 𝔠` using `Nat.one_le_iff_ne_zero.2 (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h))`.

Use `(invVol_le_relIndex _ _).trans ?_` and prove the remaining obligations. Establish `: (N.Gam Λ ⊓ N.ZI).relIndex (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) ≤ Ideal.absNorm 𝔠 ^ ((3 * e + 11) * (2 * r + 1) ^ 2)`. Use `hle.trans ?_` and prove the remaining obligations. Rewrite using `[map_pow, ← pow_mul]`. Conclude with `Nat.pow_le_pow_right hpos (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hrk 2))`.

Conclude with `this` after adjusting the coercions.
-/
theorem invVol_skew_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) (N.Gam Λ ⊓ N.ZI) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN
  obtain ⟨-, -, hc, hdim, hn, -, -, -, -, -, -, hp⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hR, -⟩ := GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary K V H hK r N
  obtain ⟨-, -, hz, -, hlat, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hT
  have hstab := GlobalTheory.T.stabilizer_hermitianLattice_of_deep_star_congruence K V H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN
  have hP := ref_inf_Pi N (latL N.F N.F' Λ) hc hn hp (fun t ht => (hz t).1 ht)
  have hfg : N.P0.FG := by
    refine Submodule.FG.of_le hlat.fg ?_
    rw [← hP]; exact inf_le_left
  have hmap : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, ∀ x ∈ N.P0, s x ∈ N.P0 := by
    rintro s ⟨⟨hsR, hsS⟩, -, hsW⟩ x hx
    rw [← hP] at hx ⊢
    have hsS' : s • N.Ref (latL N.F N.F' Λ) = N.Ref (latL N.F N.F' Λ) := hsS
    refine ⟨?_, ?_⟩
    · rw [← hsS']
      exact Submodule.smul_mem_pointwise_smul _ _ _ hx.1
    · have hx2 : x ∈ perp H N.Wt := hx.2
      change s x ∈ perp H N.Wt
      rw [mem_perp_iff] at hx2 ⊢
      intro w hw
      have hw' : s w = w := (mem_fixingSubgroup_iff _).1 hsW w hw
      have := ((hR s).1 hsR).1.1 x w
      simp only [LinearEquiv.coe_coe, hw'] at this
      rw [this]; exact hx2 w hw
  have hfix : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, s • N.P0 = N.P0 := by
    intro s hs
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      exact hmap s hs x hx
    · intro y hy
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s⁻¹ y, hmap _ (inv_mem hs) y hy, ?_⟩
      exact s.apply_symm_apply y
  have hm : 𝔠 ^ (3 * e + 10) ≠ ⊥ := pow_ne_zero _ h0
  obtain ⟨-, hle⟩ := GlobalTheory.T.relIndex_congruence_subgroup_le_absNorm_pow K V (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) N.P0 (𝔠 ^ (3 * e + 10))
    (N.Gam Λ ⊓ N.ZI) hfg hm hfix (fun s hs hx =>
      ⟨⟨hs.1.1, hstab s ⟨hs.1.1, hs.2.2⟩ hx⟩, hs.2⟩)
  have hrk : Module.finrank K (Submodule.span K (N.P0 : Set V)) ≤ 2 * r + 1 := by
    have h1 : Submodule.span K (N.P0 : Set V) ≤ N.Pi := by
      rw [Submodule.span_le, ← hP]
      exact fun x hx => hx.2
    have h2 := Submodule.finrank_mono h1
    have h3 := Submodule.finrank_add_eq_of_isCompl hc
    omega
  have hpos : 1 ≤ Ideal.absNorm 𝔠 := Nat.one_le_iff_ne_zero.2 (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h))
  refine (invVol_le_relIndex _ _).trans ?_
  have : (N.Gam Λ ⊓ N.ZI).relIndex (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) ≤
      Ideal.absNorm 𝔠 ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
    refine hle.trans ?_
    rw [map_pow, ← pow_mul]
    exact Nat.pow_le_pow_right hpos (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hrk 2))
  exact_mod_cast this

end GlobalTheory.DegCnt.WtSkew
