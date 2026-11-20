import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPDelStdOfIsBasisAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual

noncomputable section

namespace GlobalTheory.ColPeriod.WeylLoc

open NumberField IsDedekindDomain MvPolynomial Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/- English proof (translation)
Introduce and unpack `x ⟨s, hs, hx⟩`. Take `⟨t, ht, h'⟩` from `h hx`. Conclude with `⟨t * s, mul_mem ht hs, by rw [mul_smul]; exact h'⟩`.
-/
theorem localized_le_of_le_localized {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    {N N' : Submodule (𝓞 K) V} (h : N ≤ localization₂ w.asIdeal N') : localization₂ w.asIdeal N ≤ localization₂ w.asIdeal N' := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, h'⟩ := h hx
  exact ⟨t * s, mul_mem ht hs, by rw [mul_smul]; exact h'⟩

omit [NumberField K] in
/- English proof (translation)
Introduce `ha`. Establish `hco : IsCoprime (p : ℤ) c` using `(Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hc`. Take `⟨x, y, e⟩` from `hco.map (Int.castRingHom (𝓞 K))`. Simplify using `only [eq_intCast, Int.cast_natCast] at e`. Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ ha)))`.
-/
theorem intCast_notMem {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) : (c : 𝓞 K) ∉ w.asIdeal := by
  intro ha
  have hco : IsCoprime (p : ℤ) c := (Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hc
  obtain ⟨x, y, e⟩ := hco.map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at e
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ ha)))

/- English proof (translation)
Unfold `nablaSq`. Rewrite using `[GlobalTheory.StdDual.dualWeyl_eq, Submodule.map_span, Submodule.span_le, ← GlobalTheory.StdDual.image_bidSet (Int.castRingHom (𝓞 K))]`. Introduce and unpack `_ ⟨_, ⟨f, hf, rfl⟩, rfl⟩`. Establish `hf' : f ∈ nablaSq ℤ n lam`. Unfold `nablaSq`.

Rewrite using `[GlobalTheory.StdDual.dualWeyl_eq]`. Conclude with `Submodule.subset_span hf`. Take `⟨c, hc, hcf⟩` from `h n lam p hp hs f hf'`. Use `⟨(c : 𝓞 K), intCast_notMem hp w hw hc, map (Int.castRingHom (𝓞 K)) (c • f), GlobalTheory.TestLat.WeylLocal.map_mem_weyl _ _ hcf, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zsmul, ← Int.cast_smul_eq_zsmul (𝓞 K), map_smul]`.

Both sides reduce to the same expression.
-/
theorem nablaSq_le_locP (h : NablaMemDeltaLocallyAtLargePrime) {n : ℕ} (lam : DomWeight n) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) (hs : lam.spread < p) :
    (nablaSq (𝓞 K) n lam).map (toK K _) ≤ localization₂ w.asIdeal ((delSq (𝓞 K) n lam).map (toK K _)) := by
  unfold nablaSq
  rw [GlobalTheory.StdDual.dualWeyl_eq, Submodule.map_span, Submodule.span_le,
    ← GlobalTheory.StdDual.image_bidSet (Int.castRingHom (𝓞 K))]
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  have hf' : f ∈ nablaSq ℤ n lam := by
    unfold nablaSq
    rw [GlobalTheory.StdDual.dualWeyl_eq]
    exact Submodule.subset_span hf
  obtain ⟨c, hc, hcf⟩ := h n lam p hp hs f hf'
  refine ⟨(c : 𝓞 K), intCast_notMem hp w hw hc, map (Int.castRingHom (𝓞 K)) (c • f),
    GlobalTheory.TestLat.WeylLocal.map_mem_weyl _ _ hcf, ?_⟩
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul (𝓞 K), map_smul]
  rfl

/- English proof (translation)
Unfold `nabStd Formalism.GradedWeylDivisibility.tensorLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Conclude with `GlobalTheory.TestLat.WeylLocal.ten_mem_locP w _ f fun τ => nablaSq_le_locP h (lam τ) hp w hw (hs τ) (hf τ)`.
-/
theorem nabStd_le_locP (h : NablaMemDeltaLocallyAtLargePrime) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) (hs : ∀ τ, (lam τ).spread < p) :
    nabStd K lam ≤ localization₂ w.asIdeal (delStd K lam) := by
  unfold nabStd Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  exact GlobalTheory.TestLat.WeylLocal.ten_mem_locP w _ f fun τ => nablaSq_le_locP h (lam τ) hp w hw (hs τ) (hf τ)

/- English proof (translation)
Introduce `K _ _ ι _ n lam M hM p w hp hw hs x hx`. Use `choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w`. Establish `h1` using `GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB`. Establish `hx' : x.1 ∈ localization₂ w.asIdeal (nabP lam M)` using `hx`. Express the relevant statement in the definitionally equal form `x.1 ∈ localization₂ w.asIdeal (delP lam M)`.

Rewrite `hx'` using `[h1.1]`. Rewrite using `[h1.2]`. Conclude with `Submodule.map_mono (localized_le_of_le_localized w (nabStd_le_locP h lam hp w hw hs)) hx'`.
-/
theorem nabLeDel_of_local (h : NablaMemDeltaLocallyAtLargePrime) : GlobalTheory.ColPeriod.NabLeDel := by
  intro K _ _ ι _ n lam M hM p w hp hw hs x hx
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w
  have h1 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB
  have hx' : x.1 ∈ localization₂ w.asIdeal (nabP lam M) := hx
  change x.1 ∈ localization₂ w.asIdeal (delP lam M)
  rw [h1.1] at hx'
  rw [h1.2]
  exact Submodule.map_mono (localized_le_of_le_localized w (nabStd_le_locP h lam hp w hw hs)) hx'

end GlobalTheory.ColPeriod.WeylLoc
