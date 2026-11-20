import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PrincipalHartogs

/- English proof (translation)
Distinguish the cases in `hf : f = 0`. Substitute `hf` using the available equality. Take `⟨u, hu, hus⟩` from `h ⊥ Ideal.isPrime_bot (by simp)`. Rewrite `hus`, the goal using `[Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot]`. Break down `mul_eq_zero.mp hus with h0 | h0` into its components or cases.

Conclude with `absurd (h0 ▸ Submodule.zero_mem ⊥) hu`. Conclude with `h0`. Set `K` to `FractionRing B`. Establish `hfK : algebraMap B K f ≠ 0` using `IsFractionRing.to_map_eq_zero_iff.not.mpr hf`. Set `d : Ideal B` to `(Ideal.span {f}).colon {s}`.

Establish `hd : ∀ a, a ∈ d ↔ a * s ∈ Ideal.span {f}` using `fun a => by`. Simplify using `only [d, Submodule.mem_colon_singleton, smul_eq_mul]`. Distinguish the cases in `hd1 : d = ⊤`. Simplify using `using (hd 1).1 (hd1 ▸ Submodule.mem_top)`. It suffices to derive a contradiction.

Take `⟨Q, hQ, hdQ⟩` from `Ideal.exists_le_maximal d hd1`. Establish `hreg : ∀ a c : B, algebraMap B K a * (algebraMap B K s / algebraMap B K f) = algebraMap B K c → a ∈ d` using `fun a c e => by`. Rewrite using `[hd, Ideal.mem_span_singleton]`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul]`.

Rewrite using `[mul_comm f c]`. Conclude with `IsFractionRing.injective B K e`. Take `⟨p, hp, -, h1, hpf⟩` from `NormalPole.exists_height_one (K := K) (algebraMap B K s / algebraMap B K f) Q (fun a c e => hdQ (hreg a c e))`. Take `⟨u, hu, hus⟩` from `h p hp h1.le`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hus`.

Use `hu (hpf u c ?_)` and prove the remaining obligations. Rewrite using `[← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul, hc]`.
-/
theorem mem_span_singleton_of_forall_height_le_one {B : Type} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [IsNoetherianRing B] (f s : B)
    (h : ∀ q : Ideal B, q.IsPrime → q.height ≤ 1 → ∃ u, u ∉ q ∧ u * s ∈ Ideal.span {f}) :
    s ∈ Ideal.span {f} := by
  by_cases hf : f = 0
  · subst hf
    obtain ⟨u, hu, hus⟩ := h ⊥ Ideal.isPrime_bot (by simp)
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hus ⊢
    rcases mul_eq_zero.mp hus with h0 | h0
    · exact absurd (h0 ▸ Submodule.zero_mem ⊥) hu
    · exact h0
  let K := FractionRing B
  have hfK : algebraMap B K f ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hf
  let d : Ideal B := (Ideal.span {f}).colon {s}
  have hd : ∀ a, a ∈ d ↔ a * s ∈ Ideal.span {f} := fun a => by
    simp only [d, Submodule.mem_colon_singleton, smul_eq_mul]
  by_cases hd1 : d = ⊤
  · simpa using (hd 1).1 (hd1 ▸ Submodule.mem_top)
  exfalso
  obtain ⟨Q, hQ, hdQ⟩ := Ideal.exists_le_maximal d hd1
  have hreg : ∀ a c : B, algebraMap B K a * (algebraMap B K s / algebraMap B K f) = algebraMap B K c →
      a ∈ d := fun a c e => by
    rw [hd, Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul] at e
    rw [mul_comm f c]
    exact IsFractionRing.injective B K e
  obtain ⟨p, hp, -, h1, hpf⟩ := NormalPole.exists_height_one (K := K)
    (algebraMap B K s / algebraMap B K f) Q (fun a c e => hdQ (hreg a c e))
  obtain ⟨u, hu, hus⟩ := h p hp h1.le
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hus
  refine hu (hpf u c ?_)
  rw [← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul, hc]

end GlobalTheory.PrincipalHartogs

namespace GlobalTheory.PrincipalHartogs

/- English proof (translation)
Introduce `V I hB hPr s hs v`. Take `⟨hd, hic, hn⟩` from `hB v`. Take `⟨f, hf0⟩` from `(hPr v).principal`. Establish `hf : FinalTheorems.stalkId I v = Ideal.span {f}` using `hf0`. Take `⟨U, hU, hv, -⟩` from `exists_isAffineOpen_mem_and_subset (x := v) (U := ⊤) trivial`.

Use `letI : Algebra Γ(V, U) (V.presheaf.stalk v) := V.presheaf.algebra_section_stalk ⟨v, hv⟩`. Use `haveI hlocv := hU.isLocalization_stalk ⟨v, hv⟩`. Use `set t : Γ(V, U) := V.presheaf.map (homOfLE le_top).op s with ht`. Establish `hgerm : ∀ (y : V) (hy : y ∈ U), (V.presheaf.germ ⊤ y trivial).hom s = (V.presheaf.germ U y hy).hom t` using `fun y hy => by`. Rewrite using `[ht, ← CommRingCat.comp_apply, V.presheaf.germ_res]`.

Establish `key : ∀ q : Ideal (V.presheaf.stalk v), q.IsPrime → q.height ≤ 1 → ∃ u, u ∉ q ∧ u * (V.presheaf.germ ⊤ v trivial).hom s ∈ Ideal.span {f}`. Introduce `q hq hq1`. Set `P : Ideal Γ(V, U)` to `q.comap (algebraMap Γ(V, U) (V.presheaf.stalk v))`. Use `haveI hPp : P.IsPrime := Ideal.comap_isPrime _ q`. Set `Pt : PrimeSpectrum Γ(V, U)` to `⟨P, hPp⟩`.

Establish `hyU : hU.fromSpec Pt ∈ U`. Establish `: hU.fromSpec Pt ∈ Set.range hU.fromSpec` using `⟨Pt, rfl⟩`. Rewrite `this` using `[hU.range_fromSpec]`. Then use the resulting hypothesis. Set `yU : U` to `⟨hU.fromSpec Pt, hyU⟩`. Establish `hPt : hU.primeIdealOf yU = Pt` using `hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf yU)`.

Use `letI : Algebra Γ(V, U) (V.presheaf.stalk yU.1) := V.presheaf.algebra_section_stalk yU`. Establish `hlocy` using `hU.isLocalization_stalk yU`. Rewrite `hlocy` using `[hPt]`. Establish `hdim : ringKrullDim (V.presheaf.stalk yU.1) ≤ 1`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height P (V.presheaf.stalk yU.1)]`.

Use `IsLocalization.height_comap (hU.primeIdealOf ⟨v, hv⟩).asIdeal.primeCompl q` as an intermediate fact. Express the relevant statement in the definitionally equal form `(P.height : WithBot ℕ∞) ≤ 1`. Rewrite using `[show P = Ideal.under Γ(V, U) q from rfl, this]`. Conclude with `hq1` after adjusting the coercions. Establish `hy` using `hs yU.1 hdim`.

Rewrite `hy` using `[hgerm yU.1 hyU, ds_stalkId_eq_map I ⟨U, hU⟩ yU.1 hyU]`. Express the relevant statement in the definitionally equal form `algebraMap Γ(V, U) (V.presheaf.stalk yU.1) t ∈ Ideal.map (algebraMap Γ(V, U) (V.presheaf.stalk yU.1)) (I.ideal ⟨U, hU⟩) at hy`. Take `⟨⟨a, w⟩, e⟩` from `(IsLocalization.mem_map_algebraMap_iff P.primeCompl _).mp hy`. Rewrite `e` using `[← map_mul]`. Take `⟨c, hc⟩` from `IsLocalization.exists_of_eq (M := P.primeCompl) e`.

Use `⟨algebraMap Γ(V, U) (V.presheaf.stalk v) (c * w), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(P.primeCompl.mul_mem c.2 w.2 : (c : Γ(V, U)) * w ∉ P)`. Rewrite using `[← hf, ds_stalkId_eq_map I ⟨U, hU⟩ v hv, hgerm v hv]`. Express the relevant statement in the definitionally equal form `algebraMap Γ(V, U) (V.presheaf.stalk v) (c * w) * algebraMap Γ(V, U) _ t ∈ Ideal.map (algebraMap Γ(V, U) (V.presheaf.stalk v)) (I.ideal ⟨U, hU⟩)`. Rewrite using `[← map_mul, show (c : Γ(V, U)) * w * t = c * (t * w) by ring, hc]`.

Conclude with `Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ a.2)`. Rewrite using `[hf]`. Conclude with `mem_span_singleton_of_forall_height_le_one f _ key`.
-/
theorem mem_stalkId_of_forall_ringKrullDim_le_one : ∀ (V : Scheme.{0}) (I : V.IdealSheafData), (∀ v : V, IsDomain (V.presheaf.stalk v) ∧ IsIntegrallyClosed (V.presheaf.stalk v) ∧ IsNoetherianRing (V.presheaf.stalk v)) → (∀ v : V, (FinalTheorems.stalkId I v).IsPrincipal) → ∀ s : Γ(V, ⊤), (∀ v : V, ringKrullDim (V.presheaf.stalk v) ≤ 1 → (V.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) → ∀ v : V, (V.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v := by
  intro V I hB hPr s hs v
  obtain ⟨hd, hic, hn⟩ := hB v
  obtain ⟨f, hf0⟩ := (hPr v).principal
  have hf : FinalTheorems.stalkId I v = Ideal.span {f} := hf0
  obtain ⟨U, hU, hv, -⟩ := exists_isAffineOpen_mem_and_subset (x := v) (U := ⊤) trivial
  letI : Algebra Γ(V, U) (V.presheaf.stalk v) := V.presheaf.algebra_section_stalk ⟨v, hv⟩
  haveI hlocv := hU.isLocalization_stalk ⟨v, hv⟩
  set t : Γ(V, U) := V.presheaf.map (homOfLE le_top).op s with ht
  have hgerm : ∀ (y : V) (hy : y ∈ U), (V.presheaf.germ ⊤ y trivial).hom s =
      (V.presheaf.germ U y hy).hom t := fun y hy => by
    rw [ht, ← CommRingCat.comp_apply, V.presheaf.germ_res]
  have key : ∀ q : Ideal (V.presheaf.stalk v), q.IsPrime → q.height ≤ 1 →
      ∃ u, u ∉ q ∧ u * (V.presheaf.germ ⊤ v trivial).hom s ∈ Ideal.span {f} := by
    intro q hq hq1
    let P : Ideal Γ(V, U) := q.comap (algebraMap Γ(V, U) (V.presheaf.stalk v))
    haveI hPp : P.IsPrime := Ideal.comap_isPrime _ q
    let Pt : PrimeSpectrum Γ(V, U) := ⟨P, hPp⟩
    have hyU : hU.fromSpec Pt ∈ U := by
      have : hU.fromSpec Pt ∈ Set.range hU.fromSpec := ⟨Pt, rfl⟩
      rwa [hU.range_fromSpec] at this
    let yU : U := ⟨hU.fromSpec Pt, hyU⟩
    have hPt : hU.primeIdealOf yU = Pt :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf yU)
    letI : Algebra Γ(V, U) (V.presheaf.stalk yU.1) := V.presheaf.algebra_section_stalk yU
    have hlocy := hU.isLocalization_stalk yU
    rw [hPt] at hlocy
    have hdim : ringKrullDim (V.presheaf.stalk yU.1) ≤ 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (V.presheaf.stalk yU.1)]
      have := IsLocalization.height_comap (hU.primeIdealOf ⟨v, hv⟩).asIdeal.primeCompl q
      change (P.height : WithBot ℕ∞) ≤ 1
      rw [show P = Ideal.under Γ(V, U) q from rfl, this]
      exact_mod_cast hq1
    have hy := hs yU.1 hdim
    rw [hgerm yU.1 hyU, ds_stalkId_eq_map I ⟨U, hU⟩ yU.1 hyU] at hy
    change algebraMap Γ(V, U) (V.presheaf.stalk yU.1) t ∈
      Ideal.map (algebraMap Γ(V, U) (V.presheaf.stalk yU.1)) (I.ideal ⟨U, hU⟩) at hy
    obtain ⟨⟨a, w⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl _).mp hy
    rw [← map_mul] at e
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) e
    refine ⟨algebraMap Γ(V, U) (V.presheaf.stalk v) (c * w), ?_, ?_⟩
    · exact (P.primeCompl.mul_mem c.2 w.2 : (c : Γ(V, U)) * w ∉ P)
    · rw [← hf, ds_stalkId_eq_map I ⟨U, hU⟩ v hv, hgerm v hv]
      change algebraMap Γ(V, U) (V.presheaf.stalk v) (c * w) * algebraMap Γ(V, U) _ t ∈
        Ideal.map (algebraMap Γ(V, U) (V.presheaf.stalk v)) (I.ideal ⟨U, hU⟩)
      rw [← map_mul, show (c : Γ(V, U)) * w * t = c * (t * w) by ring, hc]
      exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ a.2)
  rw [hf]
  exact mem_span_singleton_of_forall_height_le_one f _ key

end GlobalTheory.PrincipalHartogs
