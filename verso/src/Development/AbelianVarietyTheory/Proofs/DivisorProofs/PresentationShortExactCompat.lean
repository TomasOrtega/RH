import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkUniqueCharacterizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeFinitePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoShortExactCompatibleStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixedLocalChains

/- English proof (translation)
Use `hS.epi_g` as an intermediate fact. Use `haveI := h₁.isQuasicoherent`. Use `haveI := (VBExt.isVB_X₂_of_shortExact X _ r s hS h₁ h₃).isQuasicoherent`. Conclude with `ShortComplex.ShortExact.mk' (QCoh.exact_map_pullback f hS.exact).1 (FlagPull.mono_pullback_map_f f _ hS h₃) (QCoh.exact_map_pullback f hS.exact).2`.
-/
theorem shortExact_map_pullback_of_isVB {X Y : Scheme.{0}} (f : Y ⟶ X) {E₁ E₂ E₃ : X.Modules}
    (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (h : a ≫ b = 0) (hS : (ShortComplex.mk a b h).ShortExact)
    {r s : ℕ} (h₁ : GlobalTheory.VB.IsVB E₁ r) (h₃ : GlobalTheory.VB.IsVB E₃ s) :
    ((ShortComplex.mk a b h).map (Scheme.Modules.pullback f)).ShortExact := by
  have := hS.epi_g
  haveI := h₁.isQuasicoherent
  haveI := (VBExt.isVB_X₂_of_shortExact X _ r s hS h₁ h₃).isQuasicoherent
  exact ShortComplex.ShortExact.mk' (QCoh.exact_map_pullback f hS.exact).1
    (FlagPull.mono_pullback_map_f f _ hS h₃) (QCoh.exact_map_pullback f hS.exact).2

/- English proof (translation)
Introduce `O _ _ _ p _ _ _ B hB P₁ P₂ P₃ a b a' b' h h' hS hS' h₁ h₂ k`. Use `haveI : Nonempty B.X := ⟨genericPoint B.X⟩`. Establish `hr : P₂.r = P₁.r + P₃.r` using `P₂.vb.rank_unique (VBExt.isVB_X₂_of_shortExact _ (ShortComplex.mk a b h) _ _ hS P₁.vb P₃.vb)`. Set `Ps : Fin 2 → Pres B` to `![P₁, P₃]`. Take `⟨B', f, hB', hf0, hF⟩` from `GlobalTheory.T.normal_model_trivializing_blowup O p B hB 2 (fun i => (Ps i).r) (fun i => (Ps i).E) (fun i => (Ps i).E') (fun i => haveI := (Ps i).iso; Vert.Model.GenIso.ofHom (Ps i).ψ) (fun i => ⟨(Ps i).vb, (Ps i).vb'⟩)`.

Take `⟨F₁⟩` from `hF 0`. Take `⟨F₃⟩` from `hF 1`. Use `haveI := P₁.iso`. Use `haveI := P₂.iso`. Use `haveI := P₃.iso`.

Set `F` to `Scheme.Modules.pullback f.f`. Take `⟨F₂, hF₂⟩` from `GlobalTheory.T.generic_iso_short_exact_compatible O p B' _ _ _ _ _ _ (F.map a) (F.map b) (F.map a') (F.map b') ((F.map_comp a b).symm.trans (by rw [h, F.map_zero])) ((F.map_comp a' b').symm.trans (by rw [h', F.map_zero])) (shortExact_map_pullback_of_isVB f.f a b h hS P₁.vb P₃.vb) …`. Establish `c₁` using `(GlobalTheory.T.ck_unique_characterization O p B hB P₁.E P₁.E' (Vert.Model.GenIso.ofHom P₁.ψ) P₁.r k P₁.vb P₁.vb').1 ⟨B', f, F₁⟩ hB' hf0`. Establish `c₂` using `(GlobalTheory.T.ck_unique_characterization O p B hB P₂.E P₂.E' (Vert.Model.GenIso.ofHom P₂.ψ) P₂.r k P₂.vb P₂.vb').1 ⟨B', f, F₂⟩ hB' hf0`. Establish `c₃` using `(GlobalTheory.T.ck_unique_characterization O p B hB P₃.E P₃.E' (Vert.Model.GenIso.ofHom P₃.ψ) P₃.r k P₃.vb P₃.vb').1 ⟨B', f, F₃⟩ hB' hf0`.

Establish `hpos` using `(GlobalTheory.T.cap_degree_finite_pullback O p B hB B' f hf0).1`. Use extensionality with `Q`. Establish `e₁` using `c₁ Q`. Establish `e₂` using `c₂ Q`. Establish `e₃` using `c₃ Q`.

Simplify using `only [Vert.Model.FlagModel.toFPair] at e₁ e₂ e₃`. Rewrite `e₂` using `[hF₂, e₁, e₃, ← mul_add]`. Simplify using `only [Pres.ck, LinearMap.add_apply]`. Conclude with `(mul_left_cancel₀ hpos.ne' e₂).symm`.
-/
theorem Pres.ck_add_of_shortExact : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P₁ P₂ P₃ : Pres B) (a : P₁.E ⟶ P₂.E) (b : P₂.E ⟶ P₃.E) (a' : P₁.E' ⟶ P₂.E') (b' : P₂.E' ⟶ P₃.E') (h : a ≫ b = 0) (h' : a' ≫ b' = 0), (ShortComplex.mk a b h).ShortExact → (ShortComplex.mk a' b' h').ShortExact → P₁.ψ ≫ a = a' ≫ P₂.ψ → P₂.ψ ≫ b = b' ≫ P₃.ψ → ∀ k : ℕ, P₂.ck p k = P₁.ck p k + P₃.ck p k := by
  intro O _ _ _ p _ _ _ B hB P₁ P₂ P₃ a b a' b' h h' hS hS' h₁ h₂ k
  haveI : Nonempty B.X := ⟨genericPoint B.X⟩
  have hr : P₂.r = P₁.r + P₃.r :=
    P₂.vb.rank_unique (VBExt.isVB_X₂_of_shortExact _ (ShortComplex.mk a b h) _ _ hS P₁.vb P₃.vb)
  let Ps : Fin 2 → Pres B := ![P₁, P₃]
  obtain ⟨B', f, hB', hf0, hF⟩ := GlobalTheory.T.normal_model_trivializing_blowup O p B hB 2 (fun i => (Ps i).r) (fun i => (Ps i).E)
    (fun i => (Ps i).E') (fun i => haveI := (Ps i).iso; Vert.Model.GenIso.ofHom (Ps i).ψ)
    (fun i => ⟨(Ps i).vb, (Ps i).vb'⟩)
  obtain ⟨F₁⟩ := hF 0
  obtain ⟨F₃⟩ := hF 1
  haveI := P₁.iso
  haveI := P₂.iso
  haveI := P₃.iso
  let F := Scheme.Modules.pullback f.f
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.generic_iso_short_exact_compatible O p B' _ _ _ _ _ _ (F.map a) (F.map b) (F.map a') (F.map b')
    ((F.map_comp a b).symm.trans (by rw [h, F.map_zero]))
    ((F.map_comp a' b').symm.trans (by rw [h', F.map_zero]))
    (shortExact_map_pullback_of_isVB f.f a b h hS P₁.vb P₃.vb)
    (shortExact_map_pullback_of_isVB f.f a' b' h' hS' P₁.vb' P₃.vb')
    (F.map P₁.ψ) (F.map P₂.ψ) (F.map P₃.ψ)
    (by rw [← F.map_comp, ← F.map_comp, h₁]) (by rw [← F.map_comp, ← F.map_comp, h₂])
    ((Vert.Model.GenIso.ofHom P₁.ψ).pull f.comp_str) ((Vert.Model.GenIso.ofHom P₂.ψ).pull f.comp_str)
    ((Vert.Model.GenIso.ofHom P₃.ψ).pull f.comp_str)
    (Vert.Model.GenIso.pull_inv f.comp_str rfl) (Vert.Model.GenIso.pull_inv f.comp_str rfl)
    (Vert.Model.GenIso.pull_inv f.comp_str rfl) P₁.r P₂.r P₃.r hr F₁ F₃
  have c₁ := (GlobalTheory.T.ck_unique_characterization O p B hB P₁.E P₁.E' (Vert.Model.GenIso.ofHom P₁.ψ) P₁.r k P₁.vb
    P₁.vb').1 ⟨B', f, F₁⟩ hB' hf0
  have c₂ := (GlobalTheory.T.ck_unique_characterization O p B hB P₂.E P₂.E' (Vert.Model.GenIso.ofHom P₂.ψ) P₂.r k P₂.vb
    P₂.vb').1 ⟨B', f, F₂⟩ hB' hf0
  have c₃ := (GlobalTheory.T.ck_unique_characterization O p B hB P₃.E P₃.E' (Vert.Model.GenIso.ofHom P₃.ψ) P₃.r k P₃.vb
    P₃.vb').1 ⟨B', f, F₃⟩ hB' hf0
  have hpos := (GlobalTheory.T.cap_degree_finite_pullback O p B hB B' f hf0).1
  ext Q
  have e₁ := c₁ Q
  have e₂ := c₂ Q
  have e₃ := c₃ Q
  simp only [Vert.Model.FlagModel.toFPair] at e₁ e₂ e₃
  rw [hF₂, e₁, e₃, ← mul_add] at e₂
  simp only [Pres.ck, LinearMap.add_apply]
  exact (mul_left_cancel₀ hpos.ne' e₂).symm

end GlobalTheory.MixedLocalChains

end
