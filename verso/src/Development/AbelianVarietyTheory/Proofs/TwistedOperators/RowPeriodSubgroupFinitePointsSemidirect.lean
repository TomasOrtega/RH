import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicProjectionUnitaryInvEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagStabilizerAnisotropicBlockExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchingTranslatesBottom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.RowGrpSemi

/- English proof (translation)
Establish `hnorm : s.range ≤ Subgroup.normalizer (N : Set X)`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Subgroup.mem_normalizer_iff]`. Introduce `n`. Use `⟨fun hn => hconj n hn y, fun hn => ?_⟩` and prove the remaining obligations.

Use `hconj _ hn y⁻¹` as an intermediate fact. Establish `e : s y⁻¹ * (s y * n * (s y)⁻¹) * (s y⁻¹)⁻¹ = n` using `by rw [map_inv]; group`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hdec : ∀ x ∈ R, ∃ n ∈ N, ∃ h, x = n * s h`. Introduce `x hx`.

Rewrite `hx` using `[hR, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N s.range hnorm]`. Take `⟨n, hn, _, ⟨h, rfl⟩, e⟩` from `hx`. Conclude with `⟨n, hn, h, e.symm⟩`. Establish `hmemR : ∀ n ∈ N, ∀ h, n * s h ∈ R` using `fun n hn h => by`. Rewrite using `[hR]`.

Conclude with `mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)`. Establish `hpeq : ∀ x y (hx : x ∈ R) (hy : y ∈ R), x = y → p ⟨x, hx⟩ = p ⟨y, hy⟩`. Introduce and unpack `x _ hx hy rfl`. Both sides reduce to the same expression. Establish `hval : ∀ x (hx : x ∈ R), ∃ n ∈ N, x = n * s (p ⟨x, hx⟩)`.

Introduce `x hx`. Take `⟨n, hn, h, rfl⟩` from `hdec x hx`. Conclude with `⟨n, hn, by rw [hpn n hn h hx]⟩`. Establish `hpmul : ∀ x y (hx : x ∈ R) (hy : y ∈ R) (hxy : x * y ∈ R), p ⟨x * y, hxy⟩ = p ⟨x, hx⟩ * p ⟨y, hy⟩`. Introduce `x y hx hy hxy`.

Take `⟨n, hn, h, rfl⟩` from `hdec x hx`. Take `⟨n', hn', h', rfl⟩` from `hdec y hy`. Establish `e : n * s h * (n' * s h') = (n * (s h * n' * (s h)⁻¹)) * s (h * h')` using `by rw [map_mul]; group`. Rewrite using `[hpeq _ _ hxy (hmemR _ (mul_mem hn (hconj n' hn' h)) _) e, hpn _ (mul_mem hn (hconj n' hn' h)), hpn n hn h, hpn n' hn' h']`. Establish `hp1 : ∀ (h1 : (1 : X) ∈ R), p ⟨1, h1⟩ = 1`.

Introduce `h1`. Rewrite using `[hpeq 1 (1 * s 1) h1 (hmemR 1 N.one_mem 1) (by rw [map_one, one_mul]), hpn 1 N.one_mem 1]`. Establish `hfin : ∀ x (hx : x ∈ R), x ∈ Xf → p ⟨x, hx⟩ ∈ Yf`. Introduce `x hx hxf`. Take `⟨n, hn, e⟩` from `hval x hx`.

Conclude with `hkey n hn _ (e ▸ hxf)`. Establish `hRf : ∀ r : R.subgroupOf Xf, r.1.1 ∈ R` using `fun r => Subgroup.mem_subgroupOf.1 r.2`. Set `π : R.subgroupOf Xf →* Yf` to `{ toFun := fun r => ⟨p ⟨r.1.1, hRf r⟩, hfin _ _ r.1.2⟩ map_one' := Subtype.ext (hp1 _) map_mul' := fun r r' => Subtype.ext (hpmul _ _ (hRf r) (hRf r') (hRf (r * r'))) }`. Establish `hsR : ∀ y, s y ∈ R` using `fun y => by rw [hR]; exact Subgroup.mem_sup_right ⟨y, rfl⟩`. Set `σ : Yf →* R.subgroupOf Xf` to `{ toFun := fun y => ⟨⟨s y.1, hsf _ y.2⟩, Subgroup.mem_subgroupOf.2 (hsR _)⟩ map_one' := Subtype.ext (Subtype.ext (map_one s)) map_mul' := fun y y' => Subtype.ext (Subtype.ext (map_mul s _ _)) }`.

Establish `hπ : ∀ r, (π r).1 = p ⟨r.1.1, hRf r⟩` using `fun r => rfl`. Use `⟨π, σ, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hp.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _`. Conclude with `((hs.comp continuous_subtype_val).subtype_mk _).subtype_mk _`. Introduce `y`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hπ]`. Conclude with `(hpeq _ (1 * s y.1) _ (hmemR 1 N.one_mem _) (one_mul _).symm).trans (hpn 1 N.one_mem _ _)`. Introduce `r`. Rewrite using `[Subgroup.mem_subgroupOf]`.

Prove the components needed by the constructor for the conclusion. Introduce `h1`. Establish `h1' : p ⟨r.1.1, hRf r⟩ = 1` using `by rw [← hπ, h1]; rfl`. Take `⟨n, hn, e⟩` from `hval _ (hRf r)`. Rewrite `e` using `[h1', map_one, mul_one]`.

Conclude with `e ▸ hn`. Introduce `hn`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hπ]`. Conclude with `(hpeq _ (r.1.1 * s 1) _ (hmemR _ hn 1) (by rw [map_one, mul_one])).trans (hpn _ hn 1 _)`.

Introduce `b`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, hk⟩`. Establish `hxf : n * s g.1 ∈ Xf`.

Establish `e : n * s g.1 = b.1 * ((b.1)⁻¹ * (n * s g.1) * b.1) * (b.1)⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `mul_mem (mul_mem b.2 (hK hk)) (inv_mem b.2)`. Use `⟨⟨⟨n * s g.1, hxf⟩, Subgroup.mem_subgroupOf.2 (hmemR n hn _)⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show ((b⁻¹ * ⟨n * s g.1, hxf⟩ * b : Xf) : X) ∈ K`.

Conclude with `hk`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hπ]`. Conclude with `hpn n hn _ _`. Introduce and unpack `⟨r, hr, rfl⟩`.

Take `⟨n, hn, e⟩` from `hval _ (hRf r)`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[hπ, ← e]`. Conclude with `hr`.
-/
theorem finite_split {X Y : Type} [Group X] [TopologicalSpace X] [Group Y] [TopologicalSpace Y]
    (Xf : Subgroup X) (Yf : Subgroup Y) (N R K : Subgroup X) (s : Y →* X) (p : R → Y)
    (hR : R = N ⊔ s.range) (hconj : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) (hs : Continuous s) (hp : Continuous p)
    (hpn : ∀ n ∈ N, ∀ h (hm : n * s h ∈ R), p ⟨n * s h, hm⟩ = h) (hsf : ∀ y ∈ Yf, s y ∈ Xf)
    (hkey : ∀ n ∈ N, ∀ h, n * s h ∈ Xf → h ∈ Yf) (hK : K ≤ Xf) :
    ∃ (π : R.subgroupOf Xf →* Yf) (σ : Yf →* R.subgroupOf Xf),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf Xf) ∧
      ∀ b : Xf, {g : Yf | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} = π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf Xf} := by

  have hnorm : s.range ≤ Subgroup.normalizer (N : Set X) := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hconj n hn y, fun hn => ?_⟩
    have := hconj _ hn y⁻¹
    have e : s y⁻¹ * (s y * n * (s y)⁻¹) * (s y⁻¹)⁻¹ = n := by rw [map_inv]; group
    rwa [e] at this
  have hdec : ∀ x ∈ R, ∃ n ∈ N, ∃ h, x = n * s h := by
    intro x hx
    rw [hR, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N s.range hnorm] at hx
    obtain ⟨n, hn, _, ⟨h, rfl⟩, e⟩ := hx
    exact ⟨n, hn, h, e.symm⟩
  have hmemR : ∀ n ∈ N, ∀ h, n * s h ∈ R := fun n hn h => by
    rw [hR]; exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)
  have hpeq : ∀ x y (hx : x ∈ R) (hy : y ∈ R), x = y → p ⟨x, hx⟩ = p ⟨y, hy⟩ := by
    rintro x _ hx hy rfl; rfl
  have hval : ∀ x (hx : x ∈ R), ∃ n ∈ N, x = n * s (p ⟨x, hx⟩) := by
    intro x hx
    obtain ⟨n, hn, h, rfl⟩ := hdec x hx
    exact ⟨n, hn, by rw [hpn n hn h hx]⟩
  have hpmul : ∀ x y (hx : x ∈ R) (hy : y ∈ R) (hxy : x * y ∈ R), p ⟨x * y, hxy⟩ = p ⟨x, hx⟩ * p ⟨y, hy⟩ := by
    intro x y hx hy hxy
    obtain ⟨n, hn, h, rfl⟩ := hdec x hx
    obtain ⟨n', hn', h', rfl⟩ := hdec y hy
    have e : n * s h * (n' * s h') = (n * (s h * n' * (s h)⁻¹)) * s (h * h') := by rw [map_mul]; group
    rw [hpeq _ _ hxy (hmemR _ (mul_mem hn (hconj n' hn' h)) _) e, hpn _ (mul_mem hn (hconj n' hn' h)),
      hpn n hn h, hpn n' hn' h']
  have hp1 : ∀ (h1 : (1 : X) ∈ R), p ⟨1, h1⟩ = 1 := by
    intro h1
    rw [hpeq 1 (1 * s 1) h1 (hmemR 1 N.one_mem 1) (by rw [map_one, one_mul]), hpn 1 N.one_mem 1]
  have hfin : ∀ x (hx : x ∈ R), x ∈ Xf → p ⟨x, hx⟩ ∈ Yf := by
    intro x hx hxf
    obtain ⟨n, hn, e⟩ := hval x hx
    exact hkey n hn _ (e ▸ hxf)
  have hRf : ∀ r : R.subgroupOf Xf, r.1.1 ∈ R := fun r => Subgroup.mem_subgroupOf.1 r.2
  let π : R.subgroupOf Xf →* Yf :=
    { toFun := fun r => ⟨p ⟨r.1.1, hRf r⟩, hfin _ _ r.1.2⟩
      map_one' := Subtype.ext (hp1 _)
      map_mul' := fun r r' => Subtype.ext (hpmul _ _ (hRf r) (hRf r') (hRf (r * r'))) }
  have hsR : ∀ y, s y ∈ R := fun y => by rw [hR]; exact Subgroup.mem_sup_right ⟨y, rfl⟩
  let σ : Yf →* R.subgroupOf Xf :=
    { toFun := fun y => ⟨⟨s y.1, hsf _ y.2⟩, Subgroup.mem_subgroupOf.2 (hsR _)⟩
      map_one' := Subtype.ext (Subtype.ext (map_one s))
      map_mul' := fun y y' => Subtype.ext (Subtype.ext (map_mul s _ _)) }
  have hπ : ∀ r, (π r).1 = p ⟨r.1.1, hRf r⟩ := fun r => rfl
  refine ⟨π, σ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hp.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
  · exact ((hs.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  · intro y
    apply Subtype.ext
    rw [hπ]
    exact (hpeq _ (1 * s y.1) _ (hmemR 1 N.one_mem _) (one_mul _).symm).trans (hpn 1 N.one_mem _ _)
  · intro r
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h1' : p ⟨r.1.1, hRf r⟩ = 1 := by rw [← hπ, h1]; rfl
      obtain ⟨n, hn, e⟩ := hval _ (hRf r)
      rw [h1', map_one, mul_one] at e
      exact e ▸ hn
    · intro hn
      apply Subtype.ext
      rw [hπ]
      exact (hpeq _ (r.1.1 * s 1) _ (hmemR _ hn 1) (by rw [map_one, mul_one])).trans (hpn _ hn 1 _)
  · intro b
    ext g
    constructor
    · rintro ⟨n, hn, hk⟩
      have hxf : n * s g.1 ∈ Xf := by
        have e : n * s g.1 = b.1 * ((b.1)⁻¹ * (n * s g.1) * b.1) * (b.1)⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem b.2 (hK hk)) (inv_mem b.2)
      refine ⟨⟨⟨n * s g.1, hxf⟩, Subgroup.mem_subgroupOf.2 (hmemR n hn _)⟩, ?_, ?_⟩
      · show ((b⁻¹ * ⟨n * s g.1, hxf⟩ * b : Xf) : X) ∈ K
        exact hk
      · apply Subtype.ext
        rw [hπ]
        exact hpn n hn _ _
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨n, hn, e⟩ := hval _ (hRf r)
      refine ⟨n, hn, ?_⟩
      rw [hπ, ← e]
      exact hr

end GlobalTheory.RowGrpSemi

namespace GlobalTheory.RowGrpSemi

open GlobalTheory.Core.Mi

/- English proof (translation)
Rewrite `hf`, the goal using `[CenAct.mem_GfC_iff]`. Use `GlobalTheory.LevNorm.finf_sand d.p0 _ d.j0 hf d.p0_j0` as an intermediate fact. Rewrite `this` using `[GlobalTheory.JacProj.witt_anisotropic_block_flag_mul_embedded d hn h]`. Then use the resulting hypothesis.
-/
theorem key_jac {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {n : GA D S} (hn : n ∈ flagN d) (h : GA D S₀)
    (hf : n * d.emb0 h ∈ GfC S) : h ∈ GfC S₀ := by
  rw [CenAct.mem_GfC_iff] at hf ⊢
  have := GlobalTheory.LevNorm.finf_sand d.p0 _ d.j0 hf d.p0_j0
  rwa [GlobalTheory.JacProj.witt_anisotropic_block_flag_mul_embedded d hn h] at this

/- English proof (translation)
Substitute `hN hs hR` using the available equality. Conclude with `finite_split (GfC S) (GfC S₀) (flagN d) _ K d.emb0 (GlobalTheory.JacProj.proj d) rfl (fun n hn h => GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn h) d.continuous_embed (GlobalTheory.JacProj.continuous_proj d) (fun n hn h _ => GlobalTheory.Ja …`.
-/
theorem jac_case {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (N R K : Subgroup (GA D S)) (s : GA D S₀ →* GA D S)
    (hN : N = flagN d) (hs : s = d.emb0) (hR : R = N ⊔ s.range) (hK : K ≤ GfC S) :
    ∃ (π : R.subgroupOf (GfC S) →* GfC S₀) (σ : GfC S₀ →* R.subgroupOf (GfC S)),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf (GfC S)) ∧
      ∀ b : GfC S, {g : GfC S₀ | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} =
        π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf (GfC S)} := by
  subst hN hs hR
  exact finite_split (GfC S) (GfC S₀) (flagN d) _ K d.emb0 (GlobalTheory.JacProj.proj d) rfl
    (fun n hn h => GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn h) d.continuous_embed (GlobalTheory.JacProj.continuous_proj d)
    (fun n hn h _ => GlobalTheory.JacProj.proj_mul d h ⟨n, hn⟩) (fun y hy => CenAct.witt_embedding_mem_finite_unitary_points d hy)
    (fun n hn h hf => key_jac d hn h hf) hK

/- English proof (translation)
Substitute `hN hs hR` using the available equality. Take `⟨p, hp, hpn⟩` from `GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o`. Use `finite_split (GfC S) (GfC A) (flagN d) _ K (embA d o) p rfl (fun n hn h => ?_) (d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))) hp (fun n hn h _ => hpn h ⟨n, hn⟩) (fun y hy => CenAct.embA_mem_GfC d o hy) (fun n hn h hf => ?_) hK` and prove the remaining obligations. Rewrite using `[embA_apply]`. Conclude with `GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn _`.

Rewrite `hf` using `[embA_apply]`. Establish `h0` using `key_jac d hn _ hf`. Establish `h1 : embA d o h ∈ GfC S` using `by rw [embA_apply]; exact CenAct.witt_embedding_mem_finite_unitary_points d h0`. Conclude with `GlobalTheory.LevNorm.mem_GfC_of_embA d o h1`.
-/
theorem bes_case {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (N R K : Subgroup (GA D S))
    (s : GA D A →* GA D S) (hN : N = flagN d) (hs : s = embA d o) (hR : R = N ⊔ s.range) (hK : K ≤ GfC S) :
    ∃ (π : R.subgroupOf (GfC S) →* GfC A) (σ : GfC A →* R.subgroupOf (GfC S)),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf (GfC S)) ∧
      ∀ b : GfC S, {g : GfC A | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} =
        π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf (GfC S)} := by
  subst hN hs hR
  obtain ⟨p, hp, hpn⟩ := GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o
  refine finite_split (GfC S) (GfC A) (flagN d) _ K (embA d o) p rfl (fun n hn h => ?_)
    (d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))) hp (fun n hn h _ => hpn h ⟨n, hn⟩) (fun y hy => CenAct.embA_mem_GfC d o hy)
    (fun n hn h hf => ?_) hK
  · rw [embA_apply]
    exact GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn _
  · rw [embA_apply] at hf
    have h0 := key_jac d hn _ hf
    have h1 : embA d o h ∈ GfC S := by rw [embA_apply]; exact CenAct.witt_embedding_mem_finite_unitary_points d h0
    exact GlobalTheory.LevNorm.mem_GfC_of_embA d o h1

end GlobalTheory.RowGrpSemi

namespace GlobalTheory.CellMass

/- English proof (translation)
Introduce `D Γ _ _ Pl0 T A Ks _ _ _ R ch j hj`. Establish `hj'` using `List.mem_range'_1.1 hj`. Establish `sp` using `GlobalTheory.RowGrpSplit.grpAt_all ch j hj`. Establish `hNfl : ∃ (S₀ : HSp D) (ρ : ℕ) (d : HypDec (ch.G.V (.grid D.R.m j)) S₀ ρ), rowN ch.G j = flagN d`. Distinguish the cases in `h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m`.

Conclude with `⟨_, _, _, by unfold rowN; rw [dif_pos h1]⟩`. Establish `h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m` using `by omega`. Conclude with `⟨_, _, _, by unfold rowN; rw [dif_neg h1, dif_pos h2]⟩`. Establish `hNc : IsClosed ((rowN ch.G j : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) : Set (GA D (ch.G.V (.grid D.R.m j))))`. Take `⟨S₀, ρ, d, e⟩` from `hNfl`.

Rewrite using `[e]`. Conclude with `GlobalTheory.Mem.TrueRecord.isClosed_NFlag _ (isIsoSub_e d)`. Use `⟨?_, ?_, ?_, sp.opn, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `sp.clR.preimage continuous_subtype_val`.

Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `hNc.preimage continuous_subtype_val`. Introduce `x hx`. Rewrite `hx`, the goal using `[Subgroup.mem_subgroupOf]`. Rewrite using `[rowGrp_eq]`.

Conclude with `Subgroup.mem_sup_left hx`. Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `sp.clB.isClosedEmbedding_subtypeVal.isCompact_preimage sp.cpt`. Distinguish the cases in `h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m`. Conclude with `GlobalTheory.RowGrpSemi.jac_case (rowJac ch.G j (by omega) ((D.R.m - 1 - j) / 2) (by omega)) _ _ _ _ (by unfold rowN; rw [dif_pos h1]) (by unfold rowEmb; rw [dif_pos h1]) (rowGrp_eq ch.G j) sp.le`.

Establish `h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m` using `by omega`. Conclude with `GlobalTheory.RowGrpSemi.bes_case (besDecAt ch.G j _ h2) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) _ _ _ _ (by unfold rowN; rw [dif_neg h1, dif_pos h2]) (by unfold rowEmb; rw [dif_neg h1, dif_pos h2]) (rowGrp_eq ch.G j) sp.le`.
-/
theorem rowGrp_finite_semidirect : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R), ∀ j ∈ idx D,
    IsClosed (((rowGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsClosed (((rowN ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    (rowN ch.G j).subgroupOf (GfC _) ≤ (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) ∧
    IsOpen (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsCompact (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    ∃ (π : (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) →* GfC (ch.G.V (.top j)))
      (σ : GfC (ch.G.V (.top j)) →* (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ (rowN ch.G j).subgroupOf (GfC _)) ∧
      ∀ b : GfC (ch.G.V (.grid D.R.m j)), prSet ch.G j b = π '' {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch j hj
  have hj' := List.mem_range'_1.1 hj
  have sp := GlobalTheory.RowGrpSplit.grpAt_all ch j hj
  have hNfl : ∃ (S₀ : HSp D) (ρ : ℕ) (d : HypDec (ch.G.V (.grid D.R.m j)) S₀ ρ), rowN ch.G j = flagN d := by
    by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · exact ⟨_, _, _, by unfold rowN; rw [dif_pos h1]⟩
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      exact ⟨_, _, _, by unfold rowN; rw [dif_neg h1, dif_pos h2]⟩
  have hNc : IsClosed ((rowN ch.G j : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) : Set (GA D (ch.G.V (.grid D.R.m j)))) := by
    obtain ⟨S₀, ρ, d, e⟩ := hNfl
    rw [e]
    exact GlobalTheory.Mem.TrueRecord.isClosed_NFlag _ (isIsoSub_e d)
  refine ⟨?_, ?_, ?_, sp.opn, ?_, ?_⟩
  · rw [Subgroup.coe_subgroupOf]
    exact sp.clR.preimage continuous_subtype_val
  · rw [Subgroup.coe_subgroupOf]
    exact hNc.preimage continuous_subtype_val
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [rowGrp_eq]
    exact Subgroup.mem_sup_left hx
  · rw [Subgroup.coe_subgroupOf]
    exact sp.clB.isClosedEmbedding_subtypeVal.isCompact_preimage sp.cpt
  · by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · exact GlobalTheory.RowGrpSemi.jac_case (rowJac ch.G j (by omega) ((D.R.m - 1 - j) / 2) (by omega)) _ _ _ _
        (by unfold rowN; rw [dif_pos h1]) (by unfold rowEmb; rw [dif_pos h1]) (rowGrp_eq ch.G j) sp.le
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      exact GlobalTheory.RowGrpSemi.bes_case (besDecAt ch.G j _ h2) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) _ _ _ _
        (by unfold rowN; rw [dif_neg h1, dif_pos h2]) (by unfold rowEmb; rw [dif_neg h1, dif_pos h2]) (rowGrp_eq ch.G j) sp.le

end GlobalTheory.CellMass
