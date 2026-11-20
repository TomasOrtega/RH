import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

/- English proof (translation)
Introduce `hFC hEB K M Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r sat' hatt`. Establish `hbad` using `Filter.eventually_cofinite.1 hatt.2`. Establish `himg` using `hbad.image (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K))`. Establish `hev` using `(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M) himg.compl_mem_cofinite`. Use `filter_upwards [hev] with w hw w' hw'`.

Establish `good : ∀ u : HeightOneSpectrum (𝓞 M), u.under (𝓞 K) = w.under (𝓞 K) → ∃ B, sat' u B ∧ FrobEig ι (r.comp (resG K M Ω)) u (algSat n (normV u) B)`. Introduce `u hu`. Assume the negation of the conclusion as `hn`. Conclude with `hw ⟨u, hn, hu⟩`. Take `⟨B, hB, hE⟩` from `good w rfl`.

Take `⟨B', hB', hE'⟩` from `good w' hw'`. Take `⟨hN, hT⟩` from `hFC K M Ω l ι n r w w' hw'`. Establish `h1` using `hT _ hE`. Rewrite `h1` using `[← hN]`. Establish `hBB : B = B'` using `(hEB M Ω l ι w').2.2 n _ B B' h1 hE'`.

Conclude with `⟨B, hB, hBB ▸ hB'⟩`.
-/
theorem UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic :
    UpperTheory.V.Af.Sol.FrobConj → UpperTheory.V.Af.Sol.EigBasic → UpperTheory.V.Af.Sol.InvSat := by
  intro hFC hEB K M Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r sat' hatt
  have hbad := Filter.eventually_cofinite.1 hatt.2
  have himg := hbad.image (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K))
  have hev := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M) himg.compl_mem_cofinite
  filter_upwards [hev] with w hw w' hw'
  have good : ∀ u : HeightOneSpectrum (𝓞 M), u.under (𝓞 K) = w.under (𝓞 K) →
      ∃ B, sat' u B ∧ FrobEig ι (r.comp (resG K M Ω)) u (algSat n (normV u) B) := by
    intro u hu
    by_contra hn
    exact hw ⟨u, hn, hu⟩
  obtain ⟨B, hB, hE⟩ := good w rfl
  obtain ⟨B', hB', hE'⟩ := good w' hw'
  obtain ⟨hN, hT⟩ := hFC K M Ω l ι n r w w' hw'
  have h1 := hT _ hE
  rw [← hN] at h1
  have hBB : B = B' := (hEB M Ω l ι w').2.2 n _ B B' h1 hE'
  exact ⟨B, hB, hBB ▸ hB'⟩
