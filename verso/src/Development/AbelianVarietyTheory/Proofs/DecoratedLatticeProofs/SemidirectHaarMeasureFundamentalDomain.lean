import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoPolish
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.SemiFd

variable {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [LocallyCompactSpace K]
  [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

def semiMap (N : Subgroup G) (s : K →* G) (p : K × N) : (N ⊔ s.range : Subgroup G) :=
  ⟨p.2.1 * s p.1, mul_mem (Subgroup.mem_sup_left p.2.2) (Subgroup.mem_sup_right ⟨p.1, rfl⟩)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem semiMeas_eq (N : Subgroup G) (s : K →* G) (μ : Measure K) (ν : Measure N) :
    semiMeas N s μ ν = (μ.prod ν).map (semiMap N s) := rfl

/- English proof (translation)
Introduce and unpack `⟨h, n⟩ ⟨h', n'⟩ he`. Use `hinj n.1 n.2 n'.1 n'.2 h h' (congrArg Subtype.val he)` as an intermediate fact. Conclude with `Prod.ext this.2 (Subtype.ext this.1)`.
-/
theorem semiMap_injective (N : Subgroup G) (s : K →* G)
    (hinj : ∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h') :
    Function.Injective (semiMap N s) := by
  rintro ⟨h, n⟩ ⟨h', n'⟩ he
  have := hinj n.1 n.2 n'.1 n'.2 h h' (congrArg Subtype.val he)
  exact Prod.ext this.2 (Subtype.ext this.1)

/- English proof (translation)
Use `haveI : LocallyCompactSpace N := hN.locallyCompactSpace`. Use `haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : PolishSpace K := PI.VolStabW.TopoPolish.polish_of_lcsc K`. Use `haveI : PolishSpace N := PI.VolStabW.TopoPolish.polish_of_lcsc N`. Conclude with `Continuous.measurableEmbedding (Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd).mul (hs.comp continuous_fst)) _) (semiMap_injective N s hinj)`.
-/
theorem semiMap_me (N : Subgroup G) (s : K →* G) (hN : IsClosed (N : Set G)) (hs : Continuous s)
    (hinj : ∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h') :
    MeasurableEmbedding (semiMap N s) := by
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : PolishSpace K := PI.VolStabW.TopoPolish.polish_of_lcsc K
  haveI : PolishSpace N := PI.VolStabW.TopoPolish.polish_of_lcsc N
  exact Continuous.measurableEmbedding
    (Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd).mul (hs.comp continuous_fst)) _)
    (semiMap_injective N s hinj)

def conjN (N : Subgroup G) (s : K →* G) (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) (g : K) : N ≃* N where
  toFun n := ⟨s g * n * (s g)⁻¹, hc n n.2 g⟩
  invFun n := ⟨s g⁻¹ * n * (s g⁻¹)⁻¹, hc n n.2 g⁻¹⟩
  left_inv n := by ext; simp [mul_assoc]
  right_inv n := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjN_apply (N : Subgroup G) (s : K →* G) (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) (g : K) (n : N) :
    ((conjN N s hc g n : N) : G) = s g * n * (s g)⁻¹ := rfl

/- English proof (translation)
Use `haveI : LocallyCompactSpace N := hN.locallyCompactSpace`. Use `haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : PolishSpace N := PI.VolStabW.TopoPolish.polish_of_lcsc N`. Establish `hcont : ∀ g, Continuous (conjN N s hc g)` using `fun g => Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _`. Establish `hcs : Continuous (conjN N s hc g).symm` using `Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _`.

Establish `hme` using `(hcont g).measurableEmbedding (conjN N s hc g).injective`. Use `haveI := MulEquiv.isHaarMeasure_map ν (conjN N s hc g) (hcont g) hcs`. Rewrite using `[← hme.map_apply]`. Conclude with `Measure.absolutelyContinuous_isHaarMeasure _ ν hA`.
-/
theorem conjN_null (N : Subgroup G) (s : K →* G) (hN : IsClosed (N : Set G)) (hs : Continuous s)
    (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) (ν : Measure N) [ν.IsHaarMeasure] (g : K) {A : Set N}
    (hA : ν A = 0) : ν ((conjN N s hc g) ⁻¹' A) = 0 := by
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : PolishSpace N := PI.VolStabW.TopoPolish.polish_of_lcsc N
  have hcont : ∀ g, Continuous (conjN N s hc g) := fun g =>
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hcs : Continuous (conjN N s hc g).symm :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hme := (hcont g).measurableEmbedding (conjN N s hc g).injective
  haveI := MulEquiv.isHaarMeasure_map ν (conjN N s hc g) (hcont g) hcs
  rw [← hme.map_apply]
  exact Measure.absolutelyContinuous_isHaarMeasure _ ν hA

end GlobalTheory.Unf.SemiFd

namespace GlobalTheory.Unf.SemiFd

variable {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [LocallyCompactSpace K]
  [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

/- English proof (translation)
Set `P : Subgroup G` to `{ carrier := {x | ∃ n ∈ N, ∃ h, x = n * s h} one_mem' := ⟨1, one_mem _, 1, by simp⟩ mul_mem' := by`. Introduce and unpack `_ _ ⟨n, hn, h, rfl⟩ ⟨n', hn', h', rfl⟩`. Use `⟨n * (s h * n' * (s h)⁻¹), mul_mem hn (hc n' hn' h), h * h', ?_⟩` and prove the remaining obligations. Simplify using `[mul_assoc]`. Use the proof step `inv_mem' := by`.

Introduce and unpack `_ ⟨n, hn, h, rfl⟩`. Use `⟨s h⁻¹ * n⁻¹ * (s h⁻¹)⁻¹, hc _ (inv_mem hn) h⁻¹, h⁻¹, ?_⟩` and prove the remaining obligations. Simplify using `[mul_assoc] }`. Establish `hle : N ⊔ s.range ≤ P` using `sup_le (fun n hn => ⟨n, hn, 1, by simp⟩) (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, by simp⟩)`. Conclude with `hle hx`.
-/
theorem mem_sup_decomp (N : Subgroup G) (s : K →* G) (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    {x : G} (hx : x ∈ N ⊔ s.range) : ∃ n ∈ N, ∃ h, x = n * s h := by
  let P : Subgroup G :=
    { carrier := {x | ∃ n ∈ N, ∃ h, x = n * s h}
      one_mem' := ⟨1, one_mem _, 1, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, h, rfl⟩ ⟨n', hn', h', rfl⟩
        refine ⟨n * (s h * n' * (s h)⁻¹), mul_mem hn (hc n' hn' h), h * h', ?_⟩
        simp [mul_assoc]
      inv_mem' := by
        rintro _ ⟨n, hn, h, rfl⟩
        refine ⟨s h⁻¹ * n⁻¹ * (s h⁻¹)⁻¹, hc _ (inv_mem hn) h⁻¹, h⁻¹, ?_⟩
        simp [mul_assoc] }
  have hle : N ⊔ s.range ≤ P := sup_le (fun n hn => ⟨n, hn, 1, by simp⟩)
    (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, by simp⟩)
  exact hle hx

end GlobalTheory.Unf.SemiFd

namespace GlobalTheory.Unf.SemiFd

open scoped Pointwise

variable {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [LocallyCompactSpace K]
  [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

/- English proof (translation)
Introduce and unpack `⟨h, n⟩ hp`. Take `⟨_, ⟨⟨h0, n0⟩, ⟨h0F, n0N⟩, rfl⟩, he⟩` from `Set.mem_smul_set.1 hp`. Establish `hv : (m * s g) * (n0.1 * s h0) = n.1 * s h`. Use `congrArg Subtype.val he` as an intermediate fact. Rewrite using `[← hx]`.

Conclude with `this`. Establish `hv' : (m * (s g * n0.1 * (s g)⁻¹)) * s (g * h0) = n.1 * s h`. Rewrite using `[← hv]`. Simplify using `[mul_assoc]`. Take `⟨h1, h2⟩` from `hinj _ (mul_mem hm (hc _ n0.2 g)) _ n.2 _ _ hv'`.

Substitute `h2` using the available equality. Use `⟨by simpa using h0F, ?_⟩` and prove the remaining obligations. Establish `hn0 : conjN N s hc g⁻¹ ((⟨m, hm⟩ : N)⁻¹ * n) = n0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [conjN_apply, Subgroup.coe_mul, Subgroup.coe_inv, ← h1]`.

Simplify using `[mul_assoc]`. Use `show conjN N s hc g⁻¹ ((⟨m, hm⟩ : N)⁻¹ * n) ∈ 𝓝`. Rewrite using `[hn0]`. Conclude with `n0N`.
-/
theorem preimage_smul_subset (N : Subgroup G) (s : K →* G) (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    (hinj : ∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h') (ΓG : Subgroup G)
    (𝓕 : Set K) (𝓝 : Set N) (x : (ΓG ⊓ (N ⊔ s.range)).subgroupOf (N ⊔ s.range)) {m : G} (hm : m ∈ N) (g : K)
    (hx : x.1.1 = m * s g) :
    semiMap N s ⁻¹' (x • (semiMap N s '' (𝓕 ×ˢ 𝓝))) ⊆
      {h | g⁻¹ * h ∈ 𝓕} ×ˢ {n | conjN N s hc g⁻¹ ((⟨m, hm⟩ : N)⁻¹ * n) ∈ 𝓝} := by
  rintro ⟨h, n⟩ hp
  obtain ⟨_, ⟨⟨h0, n0⟩, ⟨h0F, n0N⟩, rfl⟩, he⟩ := Set.mem_smul_set.1 hp
  have hv : (m * s g) * (n0.1 * s h0) = n.1 * s h := by
    have := congrArg Subtype.val he
    rw [← hx]
    exact this
  have hv' : (m * (s g * n0.1 * (s g)⁻¹)) * s (g * h0) = n.1 * s h := by
    rw [← hv]; simp [mul_assoc]
  obtain ⟨h1, h2⟩ := hinj _ (mul_mem hm (hc _ n0.2 g)) _ n.2 _ _ hv'
  subst h2
  refine ⟨by simpa using h0F, ?_⟩
  have hn0 : conjN N s hc g⁻¹ ((⟨m, hm⟩ : N)⁻¹ * n) = n0 := by
    apply Subtype.ext
    simp only [conjN_apply, Subgroup.coe_mul, Subgroup.coe_inv, ← h1]
    simp [mul_assoc]
  show conjN N s hc g⁻¹ ((⟨m, hm⟩ : N)⁻¹ * n) ∈ 𝓝
  rw [hn0]; exact n0N

/- English proof (translation)
Use `haveI : LocallyCompactSpace N := hN.locallyCompactSpace`. Use `haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _`. Establish `hme` using `semiMap_me N s hN hs hinj`. Establish `hi` using `semiMap_injective N s hinj`. Establish `hsR : ∀ g ∈ ΓK, s g ∈ ΓG` using `fun g hg => by`.

Simplify using `using (hrat 1 (one_mem _) g).2 ⟨one_mem _, hg⟩`. Rewrite using `[semiMeas_eq]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨t, -, ht, hts⟩` from `(h𝓕.nullMeasurableSet.prod h𝓝.nullMeasurableSet).exists_measurable_superset_ae_eq`. Use `(hme.measurableSet_image.2 ht).nullMeasurableSet.congr ?_` and prove the remaining obligations.

Rewrite using `[ae_eq_set, ← Set.image_diff hi, ← Set.image_diff hi, hme.map_apply, hme.map_apply, Set.preimage_image_eq _ hi, Set.preimage_image_eq _ hi]`. Conclude with `ae_eq_set.1 hts`. Rewrite using `[hme.ae_map_iff]`. Establish `hH : ∀ᵐ p ∂(μ.prod ν), ∃ γ : ΓK, γ • p.1 ∈ 𝓕` using `Measure.quasiMeasurePreserving_fst.ae h𝓕.ae_covers`. Establish `hNγ : ∀ γ : ΓK, ∀ᵐ n ∂ν, ∃ m : ΓG.subgroupOf N, m • conjN N s hc γ n ∈ 𝓝`.

Introduce `γ`. Rewrite using `[ae_iff]`. Conclude with `conjN_null N s hN hs hc ν γ (ae_iff.1 h𝓝.ae_covers)`. Establish `hN' : ∀ᵐ p ∂(μ.prod ν), ∀ γ : ΓK, ∃ m : ΓG.subgroupOf N, m • conjN N s hc γ p.2 ∈ 𝓝` using `Measure.quasiMeasurePreserving_snd.ae (ae_all_iff.2 hNγ)`. Use `filter_upwards [hH, hN'] with p hp1 hall`.

Take `⟨γ, hγ⟩` from `hp1`. Take `⟨m, hm⟩` from `hall γ`. Establish `hmG : (m : N).1 ∈ ΓG` using `Subgroup.mem_subgroupOf.1 m.2`. Establish `hmR : (m : N).1 * s γ ∈ N ⊔ s.range` using `mul_mem (Subgroup.mem_sup_left (m : N).2) (Subgroup.mem_sup_right ⟨γ, rfl⟩)`. Use `⟨⟨⟨(m : N).1 * s γ, hmR⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨(hrat _ (m : N).2 γ).2 ⟨hmG, γ.2⟩, hmR⟩)⟩, (γ • p.1, m • conjN N s hc γ p.2), ⟨hγ, hm⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[semiMap, conjN_apply, Subgroup.smul_def, mul_assoc]`. Introduce `γ γ' hne`. Take `⟨m, hm, g, hg⟩` from `mem_sup_decomp N s hc γ.1.2`. Take `⟨m', hm', g', hg'⟩` from `mem_sup_decomp N s hc γ'.1.2`.

Establish `hγG : γ.1.1 ∈ ΓG` using `(Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 γ.2)).1`. Establish `hγG' : γ'.1.1 ∈ ΓG` using `(Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 γ'.2)).1`. Take `⟨hmG, hgK⟩` from `(hrat m hm g).1 (hg ▸ hγG)`. Take `⟨hmG', hgK'⟩` from `(hrat m' hm' g').1 (hg' ▸ hγG')`. Use `show (Measure.map (semiMap N s) (μ.prod ν)) (_ ∩ _) = 0`.

Rewrite using `[hme.map_apply, Set.preimage_inter]`. Use `measure_mono_null (Set.inter_subset_inter (preimage_smul_subset N s hc hinj ΓG 𝓕 𝓝 γ hm g hg) (preimage_smul_subset N s hc hinj ΓG 𝓕 𝓝 γ' hm' g' hg')) ?_` and prove the remaining obligations. Rewrite using `[Set.prod_inter_prod, Measure.prod_prod]`. Distinguish the cases in `hgg : g = g'`. Substitute `hgg` using the available equality.

Establish `hmm : m ≠ m'`. Introduce and unpack `rfl`. Conclude with `hne (Subtype.ext (Subtype.ext (hg.trans hg'.symm)))`. Use `mul_eq_zero_of_right _ ?_` and prove the remaining obligations. Use `set c := conjN N s hc g⁻¹ with hcdef`.

Use `set u : N := c ((⟨m, hm⟩ : N)⁻¹ * ⟨m', hm'⟩) with hudef`. Establish `huG : u ∈ ΓG.subgroupOf N`. Rewrite using `[Subgroup.mem_subgroupOf]`. Use `show s g⁻¹ * (m⁻¹ * m') * (s g⁻¹)⁻¹ ∈ ΓG`. Conclude with `mul_mem (mul_mem (hsR _ (inv_mem hgK)) (mul_mem (inv_mem hmG) hmG')) (inv_mem (hsR _ (inv_mem hgK)))`.

Establish `hu1 : (1 : ΓG.subgroupOf N) ≠ ⟨u, huG⟩`. Introduce `h1`. Establish `hu : u = 1` using `(congrArg Subtype.val h1).symm`. Establish `h2 : ((⟨m, hm⟩ : N)⁻¹ * ⟨m', hm'⟩ : N) = 1` using `c.injective (by rw [← hudef, hu, map_one])`. Apply `hmm` to reduce the goal to its premises.

Establish `h3` using `congrArg Subtype.val h2`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h3`. Conclude with `inv_mul_eq_one.1 h3`. Establish `hZ : ν (𝓝 ∩ ((⟨u, huG⟩ : ΓG.subgroupOf N) • 𝓝)) = 0`. Establish `h5` using `h𝓝.aedisjoint hu1`.

Simplify `h5` using `[AEDisjoint, Function.onFun]`. Use `measure_mono_null (t := (fun n => (⟨m, hm⟩ : N)⁻¹ * n) ⁻¹' (c ⁻¹' (𝓝 ∩ ((⟨u, huG⟩ : ΓG.subgroupOf N) • 𝓝)))) ?_ ?_` and prove the remaining obligations. Introduce and unpack `n ⟨h1, h2⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`.

Establish `heq : ((⟨u, huG⟩ : ΓG.subgroupOf N)⁻¹ • c ((⟨m, hm⟩ : N)⁻¹ * n)) = c ((⟨m', hm'⟩ : N)⁻¹ * n)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv, hudef, hcdef, conjN_apply, InvMemClass.coe_inv, map_inv]`. Use `group`. Rewrite using `[heq]`.

Conclude with `h2`. Rewrite using `[measure_preimage_mul]`. Conclude with `conjN_null N s hN hs hc ν g⁻¹ hZ`. Use `mul_eq_zero_of_left ?_ _` and prove the remaining obligations. Establish `hne' : (⟨g, hgK⟩ : ΓK) ≠ ⟨g', hgK'⟩` using `fun h => hgg (congrArg Subtype.val h)`.

Establish `h5 : μ (((⟨g, hgK⟩ : ΓK) • 𝓕) ∩ ((⟨g', hgK'⟩ : ΓK) • 𝓕)) = 0` using `h𝓕.aedisjoint hne'`. Use `measure_mono_null ?_ h5` and prove the remaining obligations. Introduce and unpack `h ⟨h1, h2⟩`. Use `⟨Set.mem_smul_set_iff_inv_smul_mem.2 ?_, Set.mem_smul_set_iff_inv_smul_mem.2 ?_⟩` and prove the remaining obligations. Simplify `h1` using `[Subgroup.smul_def]`.

Simplify `h2` using `[Subgroup.smul_def]`.
-/
theorem isFundamentalDomain_semi (N : Subgroup G) (s : K →* G) (hN : IsClosed (N : Set G)) (hs : Continuous s)
    (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    (hinj : ∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h')
    (ΓG : Subgroup G) (ΓK : Subgroup K) [Countable ΓK]
    (hrat : ∀ n ∈ N, ∀ h, n * s h ∈ ΓG ↔ n ∈ ΓG ∧ h ∈ ΓK)
    (μ : Measure K) [μ.IsHaarMeasure] (ν : Measure N) [ν.IsHaarMeasure] (𝓕 : Set K) (𝓝 : Set N)
    (h𝓕 : IsFundamentalDomain ΓK 𝓕 μ) (h𝓝 : IsFundamentalDomain (ΓG.subgroupOf N) 𝓝 ν) :
    IsFundamentalDomain ((ΓG ⊓ (N ⊔ s.range)).subgroupOf (N ⊔ s.range)) (semiMap N s '' (𝓕 ×ˢ 𝓝))
      (semiMeas N s μ ν) := by
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  have hme := semiMap_me N s hN hs hinj
  have hi := semiMap_injective N s hinj
  have hsR : ∀ g ∈ ΓK, s g ∈ ΓG := fun g hg => by
    simpa using (hrat 1 (one_mem _) g).2 ⟨one_mem _, hg⟩
  rw [semiMeas_eq]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨t, -, ht, hts⟩ :=
      (h𝓕.nullMeasurableSet.prod h𝓝.nullMeasurableSet).exists_measurable_superset_ae_eq
    refine (hme.measurableSet_image.2 ht).nullMeasurableSet.congr ?_
    rw [ae_eq_set, ← Set.image_diff hi, ← Set.image_diff hi, hme.map_apply, hme.map_apply,
      Set.preimage_image_eq _ hi, Set.preimage_image_eq _ hi]
    exact ae_eq_set.1 hts
  · rw [hme.ae_map_iff]
    have hH : ∀ᵐ p ∂(μ.prod ν), ∃ γ : ΓK, γ • p.1 ∈ 𝓕 :=
      Measure.quasiMeasurePreserving_fst.ae h𝓕.ae_covers
    have hNγ : ∀ γ : ΓK, ∀ᵐ n ∂ν, ∃ m : ΓG.subgroupOf N, m • conjN N s hc γ n ∈ 𝓝 := by
      intro γ
      rw [ae_iff]
      exact conjN_null N s hN hs hc ν γ (ae_iff.1 h𝓝.ae_covers)
    have hN' : ∀ᵐ p ∂(μ.prod ν), ∀ γ : ΓK, ∃ m : ΓG.subgroupOf N, m • conjN N s hc γ p.2 ∈ 𝓝 :=
      Measure.quasiMeasurePreserving_snd.ae (ae_all_iff.2 hNγ)
    filter_upwards [hH, hN'] with p hp1 hall
    obtain ⟨γ, hγ⟩ := hp1
    obtain ⟨m, hm⟩ := hall γ
    have hmG : (m : N).1 ∈ ΓG := Subgroup.mem_subgroupOf.1 m.2
    have hmR : (m : N).1 * s γ ∈ N ⊔ s.range :=
      mul_mem (Subgroup.mem_sup_left (m : N).2) (Subgroup.mem_sup_right ⟨γ, rfl⟩)
    refine ⟨⟨⟨(m : N).1 * s γ, hmR⟩,
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨(hrat _ (m : N).2 γ).2 ⟨hmG, γ.2⟩, hmR⟩)⟩,
      (γ • p.1, m • conjN N s hc γ p.2), ⟨hγ, hm⟩, ?_⟩
    apply Subtype.ext
    simp [semiMap, conjN_apply, Subgroup.smul_def, mul_assoc]
  · intro γ γ' hne
    obtain ⟨m, hm, g, hg⟩ := mem_sup_decomp N s hc γ.1.2
    obtain ⟨m', hm', g', hg'⟩ := mem_sup_decomp N s hc γ'.1.2
    have hγG : γ.1.1 ∈ ΓG := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 γ.2)).1
    have hγG' : γ'.1.1 ∈ ΓG := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 γ'.2)).1
    obtain ⟨hmG, hgK⟩ := (hrat m hm g).1 (hg ▸ hγG)
    obtain ⟨hmG', hgK'⟩ := (hrat m' hm' g').1 (hg' ▸ hγG')
    show (Measure.map (semiMap N s) (μ.prod ν)) (_ ∩ _) = 0
    rw [hme.map_apply, Set.preimage_inter]
    refine measure_mono_null (Set.inter_subset_inter
      (preimage_smul_subset N s hc hinj ΓG 𝓕 𝓝 γ hm g hg)
      (preimage_smul_subset N s hc hinj ΓG 𝓕 𝓝 γ' hm' g' hg')) ?_
    rw [Set.prod_inter_prod, Measure.prod_prod]
    by_cases hgg : g = g'
    · subst hgg
      have hmm : m ≠ m' := by
        rintro rfl; exact hne (Subtype.ext (Subtype.ext (hg.trans hg'.symm)))
      refine mul_eq_zero_of_right _ ?_
      set c := conjN N s hc g⁻¹ with hcdef
      set u : N := c ((⟨m, hm⟩ : N)⁻¹ * ⟨m', hm'⟩) with hudef
      have huG : u ∈ ΓG.subgroupOf N := by
        rw [Subgroup.mem_subgroupOf]
        show s g⁻¹ * (m⁻¹ * m') * (s g⁻¹)⁻¹ ∈ ΓG
        exact mul_mem (mul_mem (hsR _ (inv_mem hgK)) (mul_mem (inv_mem hmG) hmG'))
          (inv_mem (hsR _ (inv_mem hgK)))
      have hu1 : (1 : ΓG.subgroupOf N) ≠ ⟨u, huG⟩ := by
        intro h1
        have hu : u = 1 := (congrArg Subtype.val h1).symm
        have h2 : ((⟨m, hm⟩ : N)⁻¹ * ⟨m', hm'⟩ : N) = 1 := c.injective (by rw [← hudef, hu, map_one])
        apply hmm
        have h3 := congrArg Subtype.val h2
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h3
        exact inv_mul_eq_one.1 h3
      have hZ : ν (𝓝 ∩ ((⟨u, huG⟩ : ΓG.subgroupOf N) • 𝓝)) = 0 := by
        have h5 := h𝓝.aedisjoint hu1
        simpa [AEDisjoint, Function.onFun] using h5
      refine measure_mono_null (t := (fun n => (⟨m, hm⟩ : N)⁻¹ * n) ⁻¹'
        (c ⁻¹' (𝓝 ∩ ((⟨u, huG⟩ : ΓG.subgroupOf N) • 𝓝)))) ?_ ?_
      · rintro n ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [Set.mem_smul_set_iff_inv_smul_mem]
        have heq : ((⟨u, huG⟩ : ΓG.subgroupOf N)⁻¹ • c ((⟨m, hm⟩ : N)⁻¹ * n)) =
            c ((⟨m', hm'⟩ : N)⁻¹ * n) := by
          apply Subtype.ext
          simp only [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv, hudef, hcdef, conjN_apply,
            InvMemClass.coe_inv, map_inv]
          group
        rw [heq]; exact h2
      · rw [measure_preimage_mul]
        exact conjN_null N s hN hs hc ν g⁻¹ hZ
    · refine mul_eq_zero_of_left ?_ _
      have hne' : (⟨g, hgK⟩ : ΓK) ≠ ⟨g', hgK'⟩ := fun h => hgg (congrArg Subtype.val h)
      have h5 : μ (((⟨g, hgK⟩ : ΓK) • 𝓕) ∩ ((⟨g', hgK'⟩ : ΓK) • 𝓕)) = 0 := h𝓕.aedisjoint hne'
      refine measure_mono_null ?_ h5
      rintro h ⟨h1, h2⟩
      refine ⟨Set.mem_smul_set_iff_inv_smul_mem.2 ?_, Set.mem_smul_set_iff_inv_smul_mem.2 ?_⟩
      · simpa [Subgroup.smul_def] using h1
      · simpa [Subgroup.smul_def] using h2

end GlobalTheory.Unf.SemiFd

namespace GlobalTheory.Unf

/- English proof (translation)
Introduce `D S H N s hs hN hc hinj hrat vH ν 𝓝 hν h𝓝 _hsemi`. Take `⟨lS, scS, t2S, bS, tgS, -, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S`. Take `⟨lH, scH, t2H, bH, tgH, -, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D H`. Use `haveI : Countable (GQ H) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig H.gram`. Use `haveI := vH.haar`.

Use `haveI : LocallyCompactSpace N := hN.locallyCompactSpace`. Use `haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _`. Establish `hme` using `SemiFd.semiMap_me N s hN hs hinj`. Establish `hi` using `SemiFd.semiMap_injective N s hinj`. Use `⟨SemiFd.semiMap N s '' (vH.𝓕 ×ˢ 𝓝), SemiFd.isFundamentalDomain_semi N s hN hs hc hinj (GQ S) (GQ H) hrat vH.μ ν vH.𝓕 𝓝 vH.fund h𝓝, fun f _ => ?_⟩` and prove the remaining obligations.

Establish `hres : (semiMeas N s vH.μ ν).restrict (SemiFd.semiMap N s '' (vH.𝓕 ×ˢ 𝓝)) = ((vH.μ.restrict vH.𝓕).prod (ν.restrict 𝓝)).map (SemiFd.semiMap N s)`. Rewrite using `[SemiFd.semiMeas_eq, hme.restrict_map, Set.preimage_image_eq _ hi, Measure.prod_restrict]`. Establish `hcomp : (fun r : (N ⊔ s.range : Subgroup (GA D S)) => f r) ∘ SemiFd.semiMap N s = Function.uncurry (fun h (n : N) => f (n.1 * s h))`. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression.

Prove the components needed by the constructor for the conclusion. Unfold `IntegrableOn AbsConv`. Rewrite using `[hres, hme.integrable_map_iff, hcomp]`. Introduce `hconv`. Rewrite using `[hres, hme.integral_map]`.

Conclude with `integral_prod (Function.uncurry fun h (n : N) => f (n.1 * s h)) hconv`.
-/
theorem semiFd_iterated : ∀ (D : D7) (S H : HSp D) (N : Subgroup (GA D S)) (s : GA D H →* GA D S), Continuous s → IsClosed (N : Set (GA D S)) → (∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) → (∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h') → (∀ n ∈ N, ∀ h, n * s h ∈ GQ S ↔ n ∈ GQ S ∧ h ∈ GQ H) → ∀ (vH : Vol H) (ν : Measure N) (𝓝 : Set N), ν.IsHaarMeasure → IsFundamentalDomain ((GQ S).subgroupOf N) 𝓝 ν → (semiMeas N s vH.μ ν).IsHaarMeasure → ∃ 𝓡 : Set (N ⊔ s.range : Subgroup (GA D S)), IsFundamentalDomain ((GQ S ⊓ (N ⊔ s.range)).subgroupOf (N ⊔ s.range)) 𝓡 (semiMeas N s vH.μ ν) ∧ ∀ f : GA D S → ℂ, Measurable f → (IntegrableOn (fun r : (N ⊔ s.range : Subgroup (GA D S)) => f r) 𝓡 (semiMeas N s vH.μ ν) ↔ AbsConv vH.μ vH.𝓕 ν 𝓝 fun h n => f (n.1 * s h)) ∧ (AbsConv vH.μ vH.𝓕 ν 𝓝 (fun h n => f (n.1 * s h)) → ∫ r in 𝓡, f (r : GA D S) ∂(semiMeas N s vH.μ ν) = ∫ h in vH.𝓕, ∫ n in 𝓝, f (n.1 * s h) ∂ν ∂vH.μ) := by
  intro D S H N s hs hN hc hinj hrat vH ν 𝓝 hν h𝓝 _hsemi
  obtain ⟨lS, scS, t2S, bS, tgS, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨lH, scH, t2H, bH, tgH, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D H
  haveI : Countable (GQ H) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig H.gram
  haveI := vH.haar
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  have hme := SemiFd.semiMap_me N s hN hs hinj
  have hi := SemiFd.semiMap_injective N s hinj
  refine ⟨SemiFd.semiMap N s '' (vH.𝓕 ×ˢ 𝓝),
    SemiFd.isFundamentalDomain_semi N s hN hs hc hinj (GQ S) (GQ H) hrat vH.μ ν vH.𝓕 𝓝 vH.fund h𝓝,
    fun f _ => ?_⟩
  have hres : (semiMeas N s vH.μ ν).restrict (SemiFd.semiMap N s '' (vH.𝓕 ×ˢ 𝓝)) =
      ((vH.μ.restrict vH.𝓕).prod (ν.restrict 𝓝)).map (SemiFd.semiMap N s) := by
    rw [SemiFd.semiMeas_eq, hme.restrict_map, Set.preimage_image_eq _ hi, Measure.prod_restrict]
  have hcomp : (fun r : (N ⊔ s.range : Subgroup (GA D S)) => f r) ∘ SemiFd.semiMap N s =
      Function.uncurry (fun h (n : N) => f (n.1 * s h)) := by
    funext p; rfl
  constructor
  · unfold IntegrableOn AbsConv
    rw [hres, hme.integrable_map_iff, hcomp]
  · intro hconv
    rw [hres, hme.integral_map]
    exact integral_prod (Function.uncurry fun h (n : N) => f (n.1 * s h)) hconv

end GlobalTheory.Unf
