import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EventuallyOneTmulAdicIntegralCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIntegralAdeleLimitCompatibleIntSystem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieLatticeAgree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvrStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateDualEqOfOmegaEqStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEqOfCodimOneEqStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LatticeStalkDvrTwistedModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CmpBundK

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Establish `hv : ∀ s : CMType H ⊕ CMType H, ((labelEmb c s H.rt : c.F) : ℂ) = Sum.elim (fun _ => H.rt0) (fun _ => starRingEnd ℂ H.rt0) s`. Introduce and unpack `(τ | τ)`. Conclude with `τ.2`. Use `show τ.1 ((H.bar H.rt : 𝓞 E) : E) = _`. Rewrite using `[H.bar_eq, IsCMField.complexEmbedding_complexConj, τ.2]`.

Both sides reduce to the same expression. Establish `h1` using `RingHom.congr_fun h H.rt`. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, g.s_rt] at h1`. Establish `h2` using `congrArg Subtype.val (cst.injective h1)`. Rewrite `h2` using `[hv, hv]`.

Establish `hne : starRingEnd ℂ H.rt0 ≠ H.rt0`. Introduce `hc`. Take `⟨r, hr⟩` from `Complex.conj_eq_iff_real.1 hc`. Establish `hsq` using `H.sqrt_neg_disc_sq`. Rewrite `hsq` using `[hr]`.

Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `: ((r ^ 2 : ℝ) : ℂ) = ((-(H.d : ℝ)) : ℝ)` using `by push_cast; exact hsq`. Use `Complex.ofReal_injective this` as an intermediate fact. Use polynomial arithmetic with `[sq_nonneg r]`. Apply the tactic sequence `rcases s with τ | τ <;> rcases s' with τ' | τ' <;> simp at h2 ⊢`.

Conclude with `hne h2`. Conclude with `hne h2.symm`.
-/
theorem labels_side (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l)
    (Ω : Type) [Field Ω] (cst : c.F →+* Ω) (g : HostAut H) (s s' : CMType H ⊕ CMType H)
    (h : cst.comp (labelEmb c s') = (cst.comp (labelEmb c s)).comp g.s.toRingHom) : s.isLeft = s'.isLeft := by
  have hv : ∀ s : CMType H ⊕ CMType H, ((labelEmb c s H.rt : c.F) : ℂ) =
      Sum.elim (fun _ => H.rt0) (fun _ => starRingEnd ℂ H.rt0) s := by
    rintro (τ | τ)
    · exact τ.2
    · show τ.1 ((H.bar H.rt : 𝓞 E) : E) = _
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, τ.2]
      rfl
  have h1 := RingHom.congr_fun h H.rt
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, g.s_rt] at h1
  have h2 := congrArg Subtype.val (cst.injective h1)
  rw [hv, hv] at h2
  have hne : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
    intro hc
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 hc
    have hsq := H.sqrt_neg_disc_sq
    rw [hr] at hsq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have : ((r ^ 2 : ℝ) : ℂ) = ((-(H.d : ℝ)) : ℝ) := by push_cast; exact hsq
    have := Complex.ofReal_injective this
    nlinarith [sq_nonneg r]
  rcases s with τ | τ <;> rcases s' with τ' | τ' <;> simp at h2 ⊢
  · exact hne h2
  · exact hne h2.symm

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem span_coe_congr {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] (R R' : Subring Ω)
    (h : R = R') (T : Set V) : (Submodule.span R T : Set V) = Submodule.span R' T := by
  subst h; rfl

/- English proof (translation)
Establish `hg : genPt ξ = e.hom (genPt ξ')`. Rewrite using `[← he]`. Both sides reduce to the same expression. Establish `hsp : ∀ q' : Cpt ξ', genPt ξ ⤳ e.hom q'.1` using `fun q' => by`. Rewrite using `[hg]`.

Conclude with `q'.2.map e.hom.base.hom.continuous`. Introduce `p' _`. Take `⟨U, hU, b, hb, hfr⟩` from `hL ⟨e.hom p'.1, hsp p'⟩ trivial`. Use `⟨e.hom ⁻¹ᵁ U, hU, b, hb, fun q' _ hq' => ?_⟩` and prove the remaining obligations. Take `⟨hli, hspan⟩` from `hfr ⟨e.hom q'.1, hsp q'⟩ trivial hq'`.

Take `⟨hR, hcar⟩` from `hc q' (hsp q')`. Use `⟨hli, SetLike.ext' ?_⟩` and prove the remaining obligations. Rewrite using `[hcar, hspan]`. Conclude with `span_coe_congr _ _ hR.symm _`.
-/
theorem isVB_of_iso (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (e : X' ≅ X) (he : ξ' ≫ e.hom = ξ) (V : Type) [AddCommGroup V] [Module Ω V]
    (L : Lat ξ V) (L' : Lat ξ' V) (r : ℕ) (W : Submodule Ω V)
    (hc : ∀ (q' : Cpt ξ') (h : genPt ξ ⤳ e.hom q'.1), regAt ξ' q' = regAt ξ ⟨e.hom q'.1, h⟩ ∧
      (L' q' : Set V) = L ⟨e.hom q'.1, h⟩) (hL : L.IsVB r W) : L'.IsVB r W := by
  have hg : genPt ξ = e.hom (genPt ξ') := by
    rw [← he]; rfl
  have hsp : ∀ q' : Cpt ξ', genPt ξ ⤳ e.hom q'.1 := fun q' => by
    rw [hg]; exact q'.2.map e.hom.base.hom.continuous
  intro p' _
  obtain ⟨U, hU, b, hb, hfr⟩ := hL ⟨e.hom p'.1, hsp p'⟩ trivial
  refine ⟨e.hom ⁻¹ᵁ U, hU, b, hb, fun q' _ hq' => ?_⟩
  obtain ⟨hli, hspan⟩ := hfr ⟨e.hom q'.1, hsp q'⟩ trivial hq'
  obtain ⟨hR, hcar⟩ := hc q' (hsp q')
  refine ⟨hli, SetLike.ext' ?_⟩
  rw [hcar, hspan]
  exact span_coe_congr _ _ hR.symm _

/- English proof (translation)
Introduce `p hp`. Take `⟨U, hpU, b, hb, hfr⟩` from `hL p hp`. Use `⟨U, hpU, fun i => φ.symm (b i), ?_, fun q hq hqU => ?_⟩` and prove the remaining obligations. Rewrite using `[← hb, Submodule.comap_equiv_eq_map_symm, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression.

Take `⟨hli, hsp⟩` from `hfr q hq hqU`. Use `⟨hli.map' φ.symm.toLinearMap φ.symm.ker, ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Use `show φ v ∈ L q ↔ _`. Rewrite using `[hsp, Submodule.mem_span_range_iff_exists_fun, Submodule.mem_span_range_iff_exists_fun]`.

Use `exists_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[← φ.symm.injective.eq_iff, LinearEquiv.symm_apply_apply]`. Simplify using `only [map_sum]`. Use `Iff.of_eq (congrArg (· = v) ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `show φ.symm ((c i : Ω) • b i) = (c i : Ω) • φ.symm (b i)`. Rewrite using `[map_smul]`.
-/
theorem isVB_comap_equiv (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (L : Lat ξ V) (φ : V' ≃ₗ[Ω] V)
    (r : ℕ) (W : Submodule Ω V) (hL : L.IsVB r W) : (L.comap φ.toLinearMap).IsVB r (W.comap φ.toLinearMap) := by
  intro p hp
  obtain ⟨U, hpU, b, hb, hfr⟩ := hL p hp
  refine ⟨U, hpU, fun i => φ.symm (b i), ?_, fun q hq hqU => ?_⟩
  · rw [← hb, Submodule.comap_equiv_eq_map_symm, Submodule.map_span, ← Set.range_comp]
    rfl
  · obtain ⟨hli, hsp⟩ := hfr q hq hqU
    refine ⟨hli.map' φ.symm.toLinearMap φ.symm.ker, ?_⟩
    ext v
    show φ v ∈ L q ↔ _
    rw [hsp, Submodule.mem_span_range_iff_exists_fun, Submodule.mem_span_range_iff_exists_fun]
    refine exists_congr fun c => ?_
    rw [← φ.symm.injective.eq_iff, LinearEquiv.symm_apply_apply]
    simp only [map_sum]
    refine Iff.of_eq (congrArg (· = v) ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    show φ.symm ((c i : Ω) • b i) = (c i : Ω) • φ.symm (b i)
    rw [map_smul]

/- English proof (translation)
Establish `hw : ∀ N w, w ∈ M'.htOm L' N q' ↔ w ∈ M.htOm L N q` using `fun N w => by`. Rewrite using `[← SetLike.mem_coe, hom N, SetLike.mem_coe]`. Establish `hD : ∀ N (σ₀ : 𝓞 E →+* Ω) e, e ∈ M'.htDual L' N ρ σ₀ q' ↔ e ∈ M.htDual L N ρ σ₀ q`. Introduce `N σ₀ e`. Rewrite using `[LieModel.mem_htDual_iff, LieModel.mem_htDual_iff]`.

Simplify using `only [hw, hR]`. Establish `hDc : ∀ N σ₀, (M'.htDual L' N ρ σ₀ q' : Set V) = M.htDual L N ρ σ₀ q` using `fun N σ₀ => Set.ext fun e => hD N σ₀ e`. Establish `hWc : ∀ N σ₀ (𝔡 : Ideal (𝓞 E)), (M'.htW L' N ρ σ₀ 𝔡 q' : Set V) = M.htW L N ρ σ₀ 𝔡 q`. Introduce `N σ₀ 𝔡`. Simplify using `only [LieModel.htW]`.

Rewrite using `[span_coe_congr _ _ hR]`. Use `congr 2`. Use extensionality with `e`. Simplify using `only [Set.mem_setOf_eq, hD]`. Establish `hE : (M'.eigLat ρ (σ s) q' : Set V) = M.eigLat ρ (σ s) q`.

Simplify using `only [LieModel.eigLat, Lat.inter, Submodule.coe_inf, Submodule.coe_restrictScalars, hlat]`. Establish `hH : ∀ p, (htLabel M' L' (n p) ρ σ s q' : Set V) = htLabel M L (n p) ρ σ s q`. Introduce `p`. Break down `s with τ | τ` into its components or cases. Conclude with `hWc _ _ _`.

Conclude with `hDc _ _`. Establish `hIF : ∀ p, InFibre ξ' p q' = InFibre ξ p q` using `fun p => by simp only [InFibre, unitAt, hR]`. Simplify using `only [Lat.patch]`. Distinguish the cases in `hF : ∃ p ∈ S, InFibre ξ p q`. Rewrite using `[if_pos (by simpa only [hIF] using hF), if_pos hF]`.

Simplify using `only [Submodule.coe_iInf, hH, hIF]`. Rewrite using `[if_neg (by simpa only [hIF] using hF), if_neg hF]`. Conclude with `hE`.
-/
theorem patch_coe_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X')
    (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (V : Type) [AddCommGroup V] [Module Ω V]
    (M : LieModel G ξ V) (M' : LieModel G' ξ' V) (L : LB G.left) (L' : LB G'.left) (S : Finset ℕ) (n : ℕ → ℕ)
    (ρ : 𝓞 E →+* Module.End Ω V) (σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω)) (s : CMType H ⊕ CMType H)
    (q : Cpt ξ) (q' : Cpt ξ') (hR : regAt ξ' q' = regAt ξ q) (hlat : (M'.lat q' : Set V) = M.lat q)
    (hom : ∀ N, (M'.htOm L' N q' : Set (Module.Dual Ω V)) = M.htOm L N q) :
    (Lat.patch S (M'.eigLat ρ (σ s)) (fun p => htLabel M' L' (n p) ρ σ s) q' : Set V) =
      Lat.patch S (M.eigLat ρ (σ s)) (fun p => htLabel M L (n p) ρ σ s) q := by
  have hw : ∀ N w, w ∈ M'.htOm L' N q' ↔ w ∈ M.htOm L N q := fun N w => by
    rw [← SetLike.mem_coe, hom N, SetLike.mem_coe]
  have hD : ∀ N (σ₀ : 𝓞 E →+* Ω) e, e ∈ M'.htDual L' N ρ σ₀ q' ↔ e ∈ M.htDual L N ρ σ₀ q := by
    intro N σ₀ e
    rw [LieModel.mem_htDual_iff, LieModel.mem_htDual_iff]
    simp only [hw, hR]
  have hDc : ∀ N σ₀, (M'.htDual L' N ρ σ₀ q' : Set V) = M.htDual L N ρ σ₀ q :=
    fun N σ₀ => Set.ext fun e => hD N σ₀ e
  have hWc : ∀ N σ₀ (𝔡 : Ideal (𝓞 E)), (M'.htW L' N ρ σ₀ 𝔡 q' : Set V) = M.htW L N ρ σ₀ 𝔡 q := by
    intro N σ₀ 𝔡
    simp only [LieModel.htW]
    rw [span_coe_congr _ _ hR]
    congr 2
    ext e
    simp only [Set.mem_setOf_eq, hD]
  have hE : (M'.eigLat ρ (σ s) q' : Set V) = M.eigLat ρ (σ s) q := by
    simp only [LieModel.eigLat, Lat.inter, Submodule.coe_inf, Submodule.coe_restrictScalars, hlat]
  have hH : ∀ p, (htLabel M' L' (n p) ρ σ s q' : Set V) = htLabel M L (n p) ρ σ s q := by
    intro p; rcases s with τ | τ
    · exact hWc _ _ _
    · exact hDc _ _
  have hIF : ∀ p, InFibre ξ' p q' = InFibre ξ p q := fun p => by simp only [InFibre, unitAt, hR]
  simp only [Lat.patch]
  by_cases hF : ∃ p ∈ S, InFibre ξ p q
  · rw [if_pos (by simpa only [hIF] using hF), if_pos hF]
    simp only [Submodule.coe_iInf, hH, hIF]
  · rw [if_neg (by simpa only [hIF] using hF), if_neg hF]
    exact hE

/- English proof (translation)
Establish `h : φ ⁻¹' T = ((φ.restrictScalars R).symm.toLinearMap) '' T`. Use extensionality with `v`. Simplify using `only [Set.mem_preimage, Set.mem_image, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Conclude with `⟨φ v, hv, (φ.restrictScalars R).symm_apply_apply v⟩`. Introduce and unpack `⟨w, hw, rfl⟩`. Establish `: φ ((φ.restrictScalars R).symm w) = w` using `(φ.restrictScalars R).apply_symm_apply w`. Rewrite using `[this]`. Conclude with `hw`.

Rewrite using `[h, Submodule.span_image]`. Use extensionality with `v`. Rewrite using `[Submodule.mem_comap, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Conclude with `⟨φ v, hv, (φ.restrictScalars R).symm_apply_apply v⟩`. Introduce and unpack `⟨w, hw, rfl⟩`. Establish `: φ ((φ.restrictScalars R).symm w) = w` using `(φ.restrictScalars R).apply_symm_apply w`. Use `show φ ((φ.restrictScalars R).symm w) ∈ _`. Rewrite using `[this]`.

Conclude with `hw`.
-/
theorem comap_span_equiv {Ω : Type} [Field Ω] {F F' : Type} [AddCommGroup F] [Module Ω F] [AddCommGroup F']
    [Module Ω F'] (R : Subring Ω) (φ : F' ≃ₗ[Ω] F) (T : Set F) :
    (Submodule.span R T).comap (φ.toLinearMap.restrictScalars R) = Submodule.span R (φ ⁻¹' T) := by
  have h : φ ⁻¹' T = ((φ.restrictScalars R).symm.toLinearMap) '' T := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image, LinearEquiv.coe_coe]
    constructor
    · intro hv; exact ⟨φ v, hv, (φ.restrictScalars R).symm_apply_apply v⟩
    · rintro ⟨w, hw, rfl⟩
      have : φ ((φ.restrictScalars R).symm w) = w := (φ.restrictScalars R).apply_symm_apply w
      rw [this]; exact hw
  rw [h, Submodule.span_image]
  ext v
  rw [Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hv
    exact ⟨φ v, hv, (φ.restrictScalars R).symm_apply_apply v⟩
  · rintro ⟨w, hw, rfl⟩
    have : φ ((φ.restrictScalars R).symm w) = w := (φ.restrictScalars R).apply_symm_apply w
    show φ ((φ.restrictScalars R).symm w) ∈ _
    rw [this]; exact hw

/- English proof (translation)
Use `set M₂ := Flat.lieModelOfEquiv M φ with hM₂`. Establish `hext : ∀ p e v, M₂.Extends p e v ↔ M.Extends p (φ e) v` using `fun _ _ _ => Iff.rfl`. Establish `hlat : ∀ p, M₂.lat p = (M.lat p).comap (φ.toLinearMap.restrictScalars (regAt ξ p))`. Introduce `p`. Simplify using `only [LieModel.lat]`.

Rewrite using `[comap_span_equiv]`. Both sides reduce to the same expression. Establish `hlatm : ∀ p e, e ∈ M₂.lat p ↔ φ e ∈ M.lat p` using `fun p e => by rw [hlat]; rfl`. Establish `heig : ∀ (σ₀ : 𝓞 E →+* Ω) e, e ∈ eigSp ρ σ₀ ↔ φ e ∈ eigSp ρ' σ₀`. Introduce `σ₀ e`.

Simplify using `only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[← hρ, ← map_smul, φ.injective.eq_iff]`. Set `ψ : Module.Dual Ω F' ≃ₗ[Ω] Module.Dual Ω F` to `φ.symm.dualMap`. Establish `hψ : ∀ w e, ψ w e = w (φ.symm e)` using `fun _ _ => rfl`.

Establish `hom_dual : ∀ p w, w ∈ M₂.omLat p ↔ ψ w ∈ M.omLat p`. Introduce `p w`. Use `show (∀ e ∈ M₂.lat p, w e ∈ regAt ξ p) ↔ (∀ e ∈ M.lat p, (ψ w) e ∈ regAt ξ p)`. Prove the components needed by the constructor for the conclusion. Introduce `h e he`.

Rewrite using `[hψ]`. Conclude with `h (φ.symm e) ((hlatm p _).2 (by simpa using he))`. Introduce `h e he`. Use `h (φ e) ((hlatm p e).1 he)` as an intermediate fact. Rewrite `this` using `[hψ, LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis.

Establish `hHT : ∀ N x p w, M₂.IsHTAt L N x p w ↔ M.IsHTAt L N x p (ψ w)`. Introduce `N x p w`. Unfold `LieModel.IsHTAt`. Rewrite using `[hom_dual]`. Use `and_congr Iff.rfl (exists_congr fun W => exists_congr fun f => and_congr Iff.rfl (and_congr Iff.rfl ?_))` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `h e v he hW`. Take `⟨r, hr, hr'⟩` from `h (φ.symm e) v ((hext p _ v).2 (by simpa using he)) hW`. Conclude with `⟨r, hr, by rw [hψ]; exact hr'⟩`. Introduce `h e v he hW`.

Take `⟨r, hr, hr'⟩` from `h (φ e) v ((hext p e v).1 he) hW`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Rewrite `hr'` using `[hψ, LinearEquiv.symm_apply_apply]`. Conclude with `hr'`. Establish `hhtOm : ∀ N p w, w ∈ M₂.htOm L N p ↔ ψ w ∈ M.htOm L N p`.

Introduce `N p w`. Establish `h : M₂.htOm L N p = (M.htOm L N p).comap (ψ.toLinearMap.restrictScalars (regAt ξ p))`. Simplify using `only [LieModel.htOm]`. Rewrite using `[comap_span_equiv]`. Use `congr 1`.

Use extensionality with `w'`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, hHT]`. Rewrite using `[h]`. Both sides reduce to the same expression. Establish `hdual : ∀ N (σ₀ : 𝓞 E →+* Ω) p e, e ∈ M₂.htDual L N ρ σ₀ p ↔ φ e ∈ M.htDual L N ρ' σ₀ p`.

Introduce `N σ₀ p e`. Rewrite using `[LieModel.mem_htDual_iff, LieModel.mem_htDual_iff, heig]`. Use `and_congr Iff.rfl ⟨fun h w hw => ?_, fun h w hw => ?_⟩` and prove the remaining obligations. Use `h (ψ.symm w) ((hhtOm N p _).2 (by simpa using hw))` as an intermediate fact. Establish `e1 : ψ.symm w e = w (φ e)`.

Use `hψ (ψ.symm w) (φ e)` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]`. Conclude with `this.symm`. Rewrite `this` using `[e1]`. Then use the resulting hypothesis. Use `h (ψ w) ((hhtOm N p w).1 hw)` as an intermediate fact.

Rewrite `this` using `[hψ, LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis. Establish `hW : ∀ N (σ₀ : 𝓞 E →+* Ω) (𝔡 : Ideal (𝓞 E)) p, M₂.htW L N ρ σ₀ 𝔡 p = (M.htW L N ρ' σ₀ 𝔡 p).comap (φ.toLinearMap.restrictScalars (regAt ξ p))`. Introduce `N σ₀ 𝔡 p`. Simplify using `only [LieModel.htW]`. Rewrite using `[comap_span_equiv]`.

Use `congr 1`. Use extensionality with `e`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, heig, hdual, map_smul]`. Establish `hD : ∀ N (σ₀ : 𝓞 E →+* Ω) p, M₂.htDual L N ρ σ₀ p = (M.htDual L N ρ' σ₀ p).comap (φ.toLinearMap.restrictScalars (regAt ξ p))`. Introduce `N σ₀ p`.

Use extensionality with `e`. Conclude with `hdual N σ₀ p e`. Establish `hE : ∀ (σ₀ : 𝓞 E →+* Ω) p, M₂.eigLat ρ σ₀ p = (M.eigLat ρ' σ₀ p).comap (φ.toLinearMap.restrictScalars (regAt ξ p))`. Introduce `σ₀ p`. Use extensionality with `e`.

Simplify using `only [LieModel.eigLat, Lat.inter, Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem]`. Rewrite using `[hlatm, heig]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `p`. Simplify using `only [Lat.comap, Lat.patch]`.

Use `split_ifs with hF`. Simplify using `only [Submodule.comap_iInf]`. Use `iInf_congr fun q => iInf_congr fun _ => iInf_congr fun _ => ?_` and prove the remaining obligations. Break down `s with τ | τ` into its components or cases. Conclude with `(hW _ _ _ p).symm`.

Conclude with `(hD _ _ p).symm`. Conclude with `(hE _ p).symm`.
-/
theorem patch_comap_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (G : Over X) [GrpObj G]
    (F F' : Type) [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (M : LieModel G ξ F) (φ : F' ≃ₗ[Ω] F) (L : LB G.left) (S : Finset ℕ) (n : ℕ → ℕ)
    (ρ : 𝓞 E →+* Module.End Ω F') (ρ' : 𝓞 E →+* Module.End Ω F) (hρ : ∀ a v, φ (ρ a v) = ρ' a (φ v))
    (σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω)) (s : CMType H ⊕ CMType H) :
    (Lat.patch S (M.eigLat ρ' (σ s)) (fun p => htLabel M L (n p) ρ' σ s)).comap φ.toLinearMap =
      Lat.patch S ((Flat.lieModelOfEquiv M φ).eigLat ρ (σ s))
        (fun p => htLabel (Flat.lieModelOfEquiv M φ) L (n p) ρ σ s) := by
  set M₂ := Flat.lieModelOfEquiv M φ with hM₂
  have hext : ∀ p e v, M₂.Extends p e v ↔ M.Extends p (φ e) v := fun _ _ _ => Iff.rfl
  have hlat : ∀ p, M₂.lat p = (M.lat p).comap (φ.toLinearMap.restrictScalars (regAt ξ p)) := by
    intro p
    simp only [LieModel.lat]
    rw [comap_span_equiv]
    rfl
  have hlatm : ∀ p e, e ∈ M₂.lat p ↔ φ e ∈ M.lat p := fun p e => by rw [hlat]; rfl
  have heig : ∀ (σ₀ : 𝓞 E →+* Ω) e, e ∈ eigSp ρ σ₀ ↔ φ e ∈ eigSp ρ' σ₀ := by
    intro σ₀ e
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← hρ, ← map_smul, φ.injective.eq_iff]
  let ψ : Module.Dual Ω F' ≃ₗ[Ω] Module.Dual Ω F := φ.symm.dualMap
  have hψ : ∀ w e, ψ w e = w (φ.symm e) := fun _ _ => rfl
  have hom_dual : ∀ p w, w ∈ M₂.omLat p ↔ ψ w ∈ M.omLat p := by
    intro p w
    show (∀ e ∈ M₂.lat p, w e ∈ regAt ξ p) ↔ (∀ e ∈ M.lat p, (ψ w) e ∈ regAt ξ p)
    constructor
    · intro h e he
      rw [hψ]
      exact h (φ.symm e) ((hlatm p _).2 (by simpa using he))
    · intro h e he
      have := h (φ e) ((hlatm p e).1 he)
      rwa [hψ, LinearEquiv.symm_apply_apply] at this
  have hHT : ∀ N x p w, M₂.IsHTAt L N x p w ↔ M.IsHTAt L N x p (ψ w) := by
    intro N x p w
    unfold LieModel.IsHTAt
    rw [hom_dual]
    refine and_congr Iff.rfl (exists_congr fun W => exists_congr fun f =>
      and_congr Iff.rfl (and_congr Iff.rfl ?_))
    constructor
    · intro h e v he hW
      obtain ⟨r, hr, hr'⟩ := h (φ.symm e) v ((hext p _ v).2 (by simpa using he)) hW
      exact ⟨r, hr, by rw [hψ]; exact hr'⟩
    · intro h e v he hW
      obtain ⟨r, hr, hr'⟩ := h (φ e) v ((hext p e v).1 he) hW
      refine ⟨r, hr, ?_⟩
      rw [hψ, LinearEquiv.symm_apply_apply] at hr'
      exact hr'
  have hhtOm : ∀ N p w, w ∈ M₂.htOm L N p ↔ ψ w ∈ M.htOm L N p := by
    intro N p w
    have h : M₂.htOm L N p = (M.htOm L N p).comap (ψ.toLinearMap.restrictScalars (regAt ξ p)) := by
      simp only [LieModel.htOm]
      rw [comap_span_equiv]
      congr 1
      ext w'
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hHT]
    rw [h]; rfl
  have hdual : ∀ N (σ₀ : 𝓞 E →+* Ω) p e, e ∈ M₂.htDual L N ρ σ₀ p ↔ φ e ∈ M.htDual L N ρ' σ₀ p := by
    intro N σ₀ p e
    rw [LieModel.mem_htDual_iff, LieModel.mem_htDual_iff, heig]
    refine and_congr Iff.rfl ⟨fun h w hw => ?_, fun h w hw => ?_⟩
    · have := h (ψ.symm w) ((hhtOm N p _).2 (by simpa using hw))
      have e1 : ψ.symm w e = w (φ e) := by
        have := hψ (ψ.symm w) (φ e)
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at this
        exact this.symm
      rwa [e1] at this
    · have := h (ψ w) ((hhtOm N p w).1 hw)
      rwa [hψ, LinearEquiv.symm_apply_apply] at this
  have hW : ∀ N (σ₀ : 𝓞 E →+* Ω) (𝔡 : Ideal (𝓞 E)) p,
      M₂.htW L N ρ σ₀ 𝔡 p = (M.htW L N ρ' σ₀ 𝔡 p).comap (φ.toLinearMap.restrictScalars (regAt ξ p)) := by
    intro N σ₀ 𝔡 p
    simp only [LieModel.htW]
    rw [comap_span_equiv]
    congr 1
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_preimage, heig, hdual, map_smul]
  have hD : ∀ N (σ₀ : 𝓞 E →+* Ω) p,
      M₂.htDual L N ρ σ₀ p = (M.htDual L N ρ' σ₀ p).comap (φ.toLinearMap.restrictScalars (regAt ξ p)) := by
    intro N σ₀ p
    ext e
    exact hdual N σ₀ p e
  have hE : ∀ (σ₀ : 𝓞 E →+* Ω) p,
      M₂.eigLat ρ σ₀ p = (M.eigLat ρ' σ₀ p).comap (φ.toLinearMap.restrictScalars (regAt ξ p)) := by
    intro σ₀ p
    ext e
    simp only [LieModel.eigLat, Lat.inter, Submodule.mem_inf, Submodule.mem_comap, Submodule.restrictScalars_mem]
    rw [hlatm, heig]
    rfl
  funext p
  simp only [Lat.comap, Lat.patch]
  split_ifs with hF
  · simp only [Submodule.comap_iInf]
    refine iInf_congr fun q => iInf_congr fun _ => iInf_congr fun _ => ?_
    rcases s with τ | τ
    · exact (hW _ _ _ p).symm
    · exact (hD _ _ p).symm
  · exact (hE _ p).symm

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨m, rfl⟩`.
-/
theorem sabMap_congr_base {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (h : f = f') (m : SABMap t' t f) :
    ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

/- English proof (translation)
Introduce `E _ _ _ H D l B _ b S₀ s₀ o₀ g X Ω _ _ ξ x t t' tΩ m m' u V _ _ M M' n q hgen hn hFT htie hq`. Take `⟨o, ⟨mo⟩⟩` from `GlobalTheory.ObjPull.objPull_of_pol (GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally) E H D l B B b b (RingHom.id B) S₀ (Sp Ω) s₀ (x ≫ s₀) x rfl rfl (by simp [spMap]) o₀`. Take `⟨n₀, -⟩` from `sabMap_congr_base (Category.id_comp x).symm mo.toSABMap`. Take `⟨c, -⟩` from `sabCancel pullCubCancel E H S₀ (Sp Ω) (Sp Ω) o₀.t tΩ o.t x (𝟙 _) u n₀`. Take `⟨n₁, hn₁⟩` from `sabComp pullCubComp E H X (Sp Ω) (Sp Ω) t tΩ o.t ξ (𝟙 _) m c`.

Take `⟨n₂, hn₂⟩` from `sabComp pullCubComp E H X (Sp Ω) (Sp Ω) t' (twistSAB tΩ g) (twistSAB o.t g) ξ (𝟙 _) m' (twistMap c g)`. Take `⟨k₁, hk₁⟩` from `sabMap_congr_base (Category.id_comp ξ) n₁`. Take `⟨k₂, hk₂⟩` from `sabMap_congr_base (Category.id_comp ξ) n₂`. Use `PositivityTheory.UnitarySelfGeneration.lattice_stalk_dvr_twisted_models E H D l B b g X Ω ξ (x ≫ s₀) o t t' k₁ k₂ V M M' n q hgen hn hFT (fun e => ?_) hq` and prove the remaining obligations. Take `⟨w, hw, hw'⟩` from `htie e`.

Establish `hp` using `c.cart.1`. Set `v0 : (epsAt (𝟙 (Sp Ω))).left ⟶ o.t.G.left` to `hp.lift w.left (epsAt (𝟙 (Sp Ω))).hom (by rw [Over.w w, Category.comp_id])`. Establish `hv0 : v0 ≫ c.φ = w.left` using `hp.lift_fst _ _ _`. Use `⟨Over.homMk v0 (hp.lift_snd _ _ _), ?_, ?_⟩` and prove the remaining obligations. Use `show v0 ≫ k₁.φ = _`.

Rewrite using `[hk₁, hn₁, ← Category.assoc, hv0, hw]`. Use `show v0 ≫ k₂.φ = _`. Rewrite using `[hk₂, hn₂]`. Conclude with `(Category.assoc v0 c.φ m'.φ).symm.trans ((congrArg (· ≫ m'.φ) hv0).trans hw')`.
-/
theorem htOm_eq_of_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S₀ : Scheme.{0}) (s₀ : S₀ ⟶ Sp B) (o₀ : Obj D l b s₀)
    (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (x : Sp Ω ⟶ S₀)
    (t t' : SAB H X) (tΩ : SAB H (Sp Ω)) (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ)
    (u : SABMap tΩ o₀.t x) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V)
    (M' : LieModel t'.G ξ V) (n : ℕ) (q : Cpt ξ), IsCptGen ξ → 0 < n → FullTorsion t.G ξ n →
    (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, v.left ≫ m.φ = (M.pt e).left ∧ v.left ≫ m'.φ = (M'.pt e).left) →
    (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) →
    M'.htOm t'.PP.L n q = M.htOm t.PP.L n q := by
  intro E _ _ _ H D l B _ b S₀ s₀ o₀ g X Ω _ _ ξ x t t' tΩ m m' u V _ _ M M' n q hgen hn hFT htie hq
  obtain ⟨o, ⟨mo⟩⟩ := GlobalTheory.ObjPull.objPull_of_pol
    (GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally) E H D l B B b b (RingHom.id B)
    S₀ (Sp Ω) s₀ (x ≫ s₀) x rfl rfl (by simp [spMap]) o₀
  obtain ⟨n₀, -⟩ := sabMap_congr_base (Category.id_comp x).symm mo.toSABMap
  obtain ⟨c, -⟩ := sabCancel pullCubCancel E H S₀ (Sp Ω) (Sp Ω) o₀.t tΩ o.t x (𝟙 _) u n₀
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H X (Sp Ω) (Sp Ω) t tΩ o.t ξ (𝟙 _) m c
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H X (Sp Ω) (Sp Ω) t' (twistSAB tΩ g) (twistSAB o.t g) ξ (𝟙 _) m'
    (twistMap c g)
  obtain ⟨k₁, hk₁⟩ := sabMap_congr_base (Category.id_comp ξ) n₁
  obtain ⟨k₂, hk₂⟩ := sabMap_congr_base (Category.id_comp ξ) n₂
  refine PositivityTheory.UnitarySelfGeneration.lattice_stalk_dvr_twisted_models E H D l B b g X Ω ξ (x ≫ s₀) o t t' k₁ k₂ V M M' n q hgen hn hFT (fun e => ?_) hq
  obtain ⟨w, hw, hw'⟩ := htie e
  have hp := c.cart.1
  let v0 : (epsAt (𝟙 (Sp Ω))).left ⟶ o.t.G.left :=
    hp.lift w.left (epsAt (𝟙 (Sp Ω))).hom (by rw [Over.w w, Category.comp_id])
  have hv0 : v0 ≫ c.φ = w.left := hp.lift_fst _ _ _
  refine ⟨Over.homMk v0 (hp.lift_snd _ _ _), ?_, ?_⟩
  · show v0 ≫ k₁.φ = _
    rw [hk₁, hn₁, ← Category.assoc, hv0, hw]
  · show v0 ≫ k₂.φ = _
    rw [hk₂, hn₂]
    exact (Category.assoc v0 c.φ m'.φ).symm.trans ((congrArg (· ≫ m'.φ) hv0).trans hw')

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR t tΩ k m mA' u u' M₁ φ E1 E2 E3 hk htie hFT hT hact s s' hss'`. Establish `hside : s.isLeft = s'.isLeft` using `labels_side E H l c Ω A.cst g s s' (by have h := hss'; unfold HodgeCpt.emb at h; rwa [← hc] at h)`. Use `haveI : IsLocallyNoetherian A'.X := by`. Use `(GlobalTheory.T.regAt_noetherian_model_noetherian A'.X Ω A'.ξ ℤ ((k : K) → J k) (fun c' => ∏ k, y ⟨k, c' k⟩) A'.tie).2 A'.all` as an intermediate fact. Use `haveI := this.1`.

Use `infer_instance`. Set `M₂ : LieModel A'.t.G A'.ξ A.Li` to `Flat.lieModelOfEquiv A'.M φ`. Establish `hlat : M₁.lat = M₂.lat` using `GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_of_normal A'.X Ω A'.ξ A'.tie.gen t.G A'.t.G tΩ.G m.φ mA'.φ t.semi A'.t.semi m.cart mA'.cart A.Li M₁ M₂ htie inferInstance A'.normal`. Use `haveI : CharZero Ω := (RingHom.charZero_iff A.cst.injective).1 inferInstance`. Establish `heig : (eigSp A'.ρ (A'.emb s')).comap φ.toLinearMap = eigSp A.ρ (A.emb s)`.

Rewrite using `[← eigSp_comp_ringEquiv Ω A.Li (𝓞 E) A.ρ g.s (A.emb s), ← hss']`. Use extensionality with `v`. Simplify using `only [eigSp, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[show (A.ρ.comp g.s.toRingHom) a v = A.ρ (g.s a) v from rfl, ← φ.injective.eq_iff, hact, map_smul]`.

Establish `hom : ∀ q : Cpt A'.ξ, (∃ _ : IsDomain (A'.X.presheaf.stalk q.1), IsDiscreteValuationRing (A'.X.presheaf.stalk q.1)) → ∀ p ∈ S, M₂.htOm A'.t.PP.L (p ^ A.R p) q = M₁.htOm t.PP.L (p ^ A.R p) q` using `fun q hq p hp => htOm_eq_of_dvr E H D l _ (baseKA l) _ _ Y.oF g A'.X Ω A'.ξ x t A'.t tΩ m mA' u A.Li M₁ M₂ (p ^ A.R p) q A'.tie.gen (pow_pos (A.S_prime p hp).pos _) (hFT _ (A.tors p hp)) htie hq`. Set `La : Lat A'.ξ A.Li` to `Lat.patch S (M₁.eigLat A.ρ (A.emb s)) (fun p => htLabel M₁ t.PP.L (p ^ A.R p) A.ρ A.emb s)`. Set `Lb : Lat A'.ξ A.Li` to `(A'.V s').comap φ.toLinearMap`. Establish `hLb : Lb = Lat.patch S (M₂.eigLat (A.ρ.comp g.s.toRingHom) (A'.emb s')) (fun p => htLabel M₂ A'.t.PP.L (p ^ A'.R p) (A.ρ.comp g.s.toRingHom) A'.emb s')` using `patch_comap_equiv E H A'.X Ω A'.ξ A'.t.G A'.Li A.Li A'.M φ A'.t.PP.L S (fun p => p ^ A'.R p) (A.ρ.comp g.s.toRingHom) A'.ρ hact A'.emb s'`. Establish `hcar : ∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), (La q : Set A.Li) = A.V s ⟨e.hom q.1, h⟩` using `fun q h => patch_coe_eq E H A.X A'.X Ω A.ξ A'.ξ A.t.G t.G A.Li A.M M₁ A.t.PP.L t.PP.L S (fun p => p ^ A.R p) A.ρ A.emb s ⟨e.hom q.1, h⟩ q (hT q h).1 (hT q h).2.1 (hT q h).2.2`.

Establish `hvbA : La.IsVB (labelRk D s) (eigSp A.ρ (A.emb s))` using `isVB_of_iso A.X A'.X Ω A.ξ A'.ξ e hξ A.Li (A.V s) La _ _ (fun q h => ⟨(hT q h).1, hcar q h⟩) (A.vb s)`. Establish `hrk : labelRk D s' = labelRk D s`. Apply the tactic sequence `rcases s with τ | τ <;> rcases s' with τ' | τ' <;> simp at hside <;> rfl`. Establish `hvbB : Lb.IsVB (labelRk D s) (eigSp A.ρ (A.emb s))`. Establish `h1` using `isVB_comap_equiv A'.X Ω A'.ξ A'.Li A.Li (A'.V s') φ _ _ (A'.vb s')`.

Rewrite `h1` using `[hrk]`. Rewrite using `[← heig]`. Conclude with `h1`. Establish `hagree : ∀ q ∈ (Set.univ : Set (Cpt A'.ξ)), La q = Lb q`. Use `GlobalTheory.T.lattice_eq_of_codim_one_eq A'.X Ω A'.ξ A'.tie.gen Set.univ (fun _ _ _ _ => trivial) (fun p _ => (A'.normal p.1).2) A.Li La Lb (labelRk D s) (eigSp A.ρ (A.emb s)) hvbA hvbB ?_` and prove the remaining obligations.

Introduce `q _ hq1`. Establish `hdvr` using `GlobalTheory.T.normal_codim_one_stalk_dvr A'.X A'.normal q.1 hq1`. Rewrite using `[hLb]`. Simplify using `only [La, Lat.patch]`. Use `split_ifs with hF`.

Use `iInf_congr fun p => iInf_congr fun hp => iInf_congr fun _ => ?_` and prove the remaining obligations. Rewrite using `[hR p hp]`. Establish `key` using `GlobalTheory.T.hodge_tate_dual_eq_of_omega_eq E g.s A'.X Ω A'.ξ t.G A'.t.G t.PP.L A'.t.PP.L A.Li M₁ M₂ (p ^ A.R p) (p ^ A.R p) A.ρ (A.emb s) q (hom q hdvr p hp)`. Apply the tactic sequence `rcases s with τ | τ <;> rcases s' with τ' | τ' <;> simp at hside`. Simplify using `only [htLabel]`.

Rewrite using `[hss']`. Conclude with `key.2.symm`. Simplify using `only [htLabel]`. Rewrite using `[hss']`. Conclude with `key.1.symm`.

Simplify using `only [LieModel.eigLat, Lat.inter]`. Rewrite using `[hss', eigSp_comp_ringEquiv, hlat]`. Introduce `q h v`. Establish `e1 : v ∈ A.V s ⟨e.hom q.1, h⟩ ↔ v ∈ La q`. Rewrite using `[← SetLike.mem_coe, ← hcar q h, SetLike.mem_coe]`.

Rewrite using `[e1, hagree q trivial]`. Conclude with `Iff.rfl`.
-/
theorem bund : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ → mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ →
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ →
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) → (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) → (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) →
      (∀ a v, φ (A.ρ (g.s a) v) = A'.ρ a (φ v)) →
      ∀ s s', A'.emb s' = (A.emb s).comp g.s.toRingHom → ∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1) (v : A.Li),
        v ∈ A.V s ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V s' q := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hx hx' hf hs hc hcx hR
    t tΩ k m mA' u u' M₁ φ E1 E2 E3 hk htie hFT hT hact s s' hss'

  have hside : s.isLeft = s'.isLeft :=
    labels_side E H l c Ω A.cst g s s' (by have h := hss'; unfold HodgeCpt.emb at h; rwa [← hc] at h)

  haveI : IsLocallyNoetherian A'.X := by
    have := (GlobalTheory.T.regAt_noetherian_model_noetherian A'.X Ω A'.ξ ℤ ((k : K) → J k) (fun c' => ∏ k, y ⟨k, c' k⟩) A'.tie).2 A'.all
    haveI := this.1
    infer_instance
  let M₂ : LieModel A'.t.G A'.ξ A.Li := Flat.lieModelOfEquiv A'.M φ
  have hlat : M₁.lat = M₂.lat :=
    GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_of_normal A'.X Ω A'.ξ A'.tie.gen t.G A'.t.G tΩ.G m.φ mA'.φ t.semi A'.t.semi m.cart mA'.cart A.Li M₁ M₂
      htie inferInstance A'.normal
  haveI : CharZero Ω := (RingHom.charZero_iff A.cst.injective).1 inferInstance
  have heig : (eigSp A'.ρ (A'.emb s')).comap φ.toLinearMap = eigSp A.ρ (A.emb s) := by
    rw [← eigSp_comp_ringEquiv Ω A.Li (𝓞 E) A.ρ g.s (A.emb s), ← hss']
    ext v
    simp only [eigSp, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe]
    refine forall_congr' fun a => ?_
    rw [show (A.ρ.comp g.s.toRingHom) a v = A.ρ (g.s a) v from rfl, ← φ.injective.eq_iff, hact, map_smul]
  have hom : ∀ q : Cpt A'.ξ, (∃ _ : IsDomain (A'.X.presheaf.stalk q.1),
      IsDiscreteValuationRing (A'.X.presheaf.stalk q.1)) →
      ∀ p ∈ S, M₂.htOm A'.t.PP.L (p ^ A.R p) q = M₁.htOm t.PP.L (p ^ A.R p) q := fun q hq p hp =>
    htOm_eq_of_dvr E H D l _ (baseKA l) _ _ Y.oF g A'.X Ω A'.ξ x t A'.t tΩ m mA' u A.Li M₁ M₂ (p ^ A.R p) q
      A'.tie.gen (pow_pos (A.S_prime p hp).pos _) (hFT _ (A.tors p hp)) htie hq
  let La : Lat A'.ξ A.Li :=
    Lat.patch S (M₁.eigLat A.ρ (A.emb s)) (fun p => htLabel M₁ t.PP.L (p ^ A.R p) A.ρ A.emb s)
  let Lb : Lat A'.ξ A.Li := (A'.V s').comap φ.toLinearMap
  have hLb : Lb = Lat.patch S (M₂.eigLat (A.ρ.comp g.s.toRingHom) (A'.emb s'))
      (fun p => htLabel M₂ A'.t.PP.L (p ^ A'.R p) (A.ρ.comp g.s.toRingHom) A'.emb s') :=
    patch_comap_equiv E H A'.X Ω A'.ξ A'.t.G A'.Li A.Li A'.M φ A'.t.PP.L S (fun p => p ^ A'.R p)
      (A.ρ.comp g.s.toRingHom) A'.ρ hact A'.emb s'
  have hcar : ∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), (La q : Set A.Li) = A.V s ⟨e.hom q.1, h⟩ :=
    fun q h => patch_coe_eq E H A.X A'.X Ω A.ξ A'.ξ A.t.G t.G A.Li A.M M₁ A.t.PP.L t.PP.L S
      (fun p => p ^ A.R p) A.ρ A.emb s ⟨e.hom q.1, h⟩ q (hT q h).1 (hT q h).2.1 (hT q h).2.2
  have hvbA : La.IsVB (labelRk D s) (eigSp A.ρ (A.emb s)) :=
    isVB_of_iso A.X A'.X Ω A.ξ A'.ξ e hξ A.Li (A.V s) La _ _ (fun q h => ⟨(hT q h).1, hcar q h⟩) (A.vb s)
  have hrk : labelRk D s' = labelRk D s := by
    rcases s with τ | τ <;> rcases s' with τ' | τ' <;> simp at hside <;> rfl
  have hvbB : Lb.IsVB (labelRk D s) (eigSp A.ρ (A.emb s)) := by
    have h1 := isVB_comap_equiv A'.X Ω A'.ξ A'.Li A.Li (A'.V s') φ _ _ (A'.vb s')
    rw [hrk] at h1
    rw [← heig]
    exact h1
  have hagree : ∀ q ∈ (Set.univ : Set (Cpt A'.ξ)), La q = Lb q := by
    refine GlobalTheory.T.lattice_eq_of_codim_one_eq A'.X Ω A'.ξ A'.tie.gen Set.univ (fun _ _ _ _ => trivial)
      (fun p _ => (A'.normal p.1).2) A.Li La Lb (labelRk D s) (eigSp A.ρ (A.emb s)) hvbA hvbB ?_
    intro q _ hq1
    have hdvr := GlobalTheory.T.normal_codim_one_stalk_dvr A'.X A'.normal q.1 hq1
    rw [hLb]
    simp only [La, Lat.patch]
    split_ifs with hF
    · refine iInf_congr fun p => iInf_congr fun hp => iInf_congr fun _ => ?_
      rw [hR p hp]
      have key := GlobalTheory.T.hodge_tate_dual_eq_of_omega_eq E g.s A'.X Ω A'.ξ t.G A'.t.G t.PP.L A'.t.PP.L A.Li M₁ M₂ (p ^ A.R p)
        (p ^ A.R p) A.ρ (A.emb s) q (hom q hdvr p hp)
      rcases s with τ | τ <;> rcases s' with τ' | τ' <;> simp at hside
      · simp only [htLabel]; rw [hss']; exact key.2.symm
      · simp only [htLabel]; rw [hss']; exact key.1.symm
    · simp only [LieModel.eigLat, Lat.inter]
      rw [hss', eigSp_comp_ringEquiv, hlat]
  intro q h v
  have e1 : v ∈ A.V s ⟨e.hom q.1, h⟩ ↔ v ∈ La q := by
    rw [← SetLike.mem_coe, ← hcar q h, SetLike.mem_coe]
  rw [e1, hagree q trivial]
  exact Iff.rfl

end GlobalTheory.CompanionTheory.Ar.CmpBundK

namespace PositivityTheory.UnitarySelfGeneration

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
The claim follows from `@GlobalTheory.CompanionTheory.Ar.CmpBundK.bund`.
-/
theorem twisted_bundles_match_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ → mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ →
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ →
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) → (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) → (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) →
      (∀ a v, φ (A.ρ (g.s a) v) = A'.ρ a (φ v)) →
      ∀ s s', A'.emb s' = (A.emb s).comp g.s.toRingHom → ∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1) (v : A.Li),
        v ∈ A.V s ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V s' q :=
  @GlobalTheory.CompanionTheory.Ar.CmpBundK.bund

end PositivityTheory.UnitarySelfGeneration
