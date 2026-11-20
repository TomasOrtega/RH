import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

section Corner

variable {R S : Type} [CommRing R] [CommRing S]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `p q`. Take `⟨⟨a, i⟩, rfl⟩` from `(stdBlocks n h).surjective p`. Take `⟨⟨b, j⟩, rfl⟩` from `(stdBlocks n h).surjective q`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Rewrite using `[leviEmb_apply_same]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[GlobalTheory.IwasawaAdelic.cornerGL_entry_same, GlobalTheory.IwasawaAdelic.cornerGL_entry_same, leviEmb_apply_same]`.

Establish `hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩` using `fun he => hij (by simpa using (stdBlocks n h).injective he)`. Rewrite using `[GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hij, leviEmb_apply_same]`. Establish `hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩` using `fun he => hab (congrArg Sigma.fst ((stdBlocks n h).injective he))`. Rewrite using `[leviEmb_apply_ne _ _ _ hab, GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, leviEmb_apply_ne _ _ _ hab, map_zero]`.
-/
theorem cc_cornerGL_leviEmb {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (s : R →ₙ+* S)
    (l : ∀ i, GL (Fin (n i)) R) :
    cornerGL N s (leviEmb R (stdBlocks n h) l) = leviEmb S (stdBlocks n h) (fun i => cornerGL (n i) s (l i)) := by
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective q
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_same, GlobalTheory.IwasawaAdelic.cornerGL_entry_same, leviEmb_apply_same]
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he =>
        hij (by simpa using (stdBlocks n h).injective he)
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hij,
        leviEmb_apply_same]
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he =>
      hab (congrArg Sigma.fst ((stdBlocks n h).injective he))
    rw [leviEmb_apply_ne _ _ _ hab, GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, leviEmb_apply_ne _ _ _ hab, map_zero]

/- English proof (translation)
Rewrite `hu`, the goal using `[mem_unipRad]`. Take `⟨hP, hD⟩` from `hu`. Use `⟨mem_parab_iff.2 fun a b i j hlt => ?_, fun a i j => ?_⟩` and prove the remaining obligations. Establish `hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩` using `fun he => by`. Use `congrArg Sigma.fst ((stdBlocks n h).injective he)` as an intermediate fact.

Conclude with `(ne_of_gt hlt) this`. Rewrite using `[GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, mem_parab_iff.1 hP a b i j hlt, map_zero]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[GlobalTheory.IwasawaAdelic.cornerGL_entry_same, hD a i i]`.

Simplify using the standard rewrite rules. Establish `hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩` using `fun he => by`. Conclude with `hij (by simpa using (stdBlocks n h).injective he)`. Rewrite using `[GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, hD a i j, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]`.
-/
theorem cc_cornerGL_mem_unipRad {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (s : R →ₙ+* S) {u : GL (Fin N) R}
    (hu : u ∈ unipRad R (stdBlocks n h)) : cornerGL N s u ∈ unipRad S (stdBlocks n h) := by
  rw [mem_unipRad] at hu ⊢
  obtain ⟨hP, hD⟩ := hu
  refine ⟨mem_parab_iff.2 fun a b i j hlt => ?_, fun a i j => ?_⟩
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he => by
      have := congrArg Sigma.fst ((stdBlocks n h).injective he)
      exact (ne_of_gt hlt) this
    rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, mem_parab_iff.1 hP a b i j hlt, map_zero]
  · by_cases hij : i = j
    · subst hij
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_same, hD a i i]; simp
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he => by
        exact hij (by simpa using (stdBlocks n h).injective he)
      rw [GlobalTheory.IwasawaAdelic.cornerGL_entry_ne _ _ hne, hD a i j, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij,
        map_zero]

end Corner

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Take `⟨b, hb, k, hy⟩` from `GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E N (Matrix.GeneralLinearGroup.map (pInf E) x)`. Establish `hbP` using `GlobalTheory.IwasawaAdelic.mem_parab_of_upper n h b hb`. Take `⟨u, hu, hbu⟩` from `exists_levi_mul_unip (Cinf E) (stdBlocks n h) ⟨b, hbP⟩`. Use `set L := leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩) with hL`. Establish `hN` using `leviEmb_mem_normalizer (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩)`.

Establish `hu' : L * u * L⁻¹ ∈ unipRad (Cinf E) (stdBlocks n h)` using `(Subgroup.mem_normalizer_iff.1 hN u).1 hu`. Use `⟨infGL E N (L * u * L⁻¹), GlobalTheory.IwasawaAdelic.infGL_mem_unipRad E n h _ hu', fun i => leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩ i, k, ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.IwasawaAdelic.infGL_leviEmb, ← hL]`. Use `conv_lhs => rw [← infGL_mul_finGL x, hy]`. Simplify using `only [Subtype.coe_mk] at hbu`.

Rewrite using `[hbu]`. Simplify using `only [map_mul, map_inv]`. Use `group`.
-/
theorem iwasawa_inf {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (x : GA E N) :
    ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GL (Fin (n i)) (Cinf E)) (k : Kinf E N),
      x = u * leviEmb (Ad E) (stdBlocks n h) (fun i => infGL E (n i) (m i)) *
        (infGL E N (Unitary.toUnits k) * finGL E N (Matrix.GeneralLinearGroup.map (pFin E) x)) := by
  obtain ⟨b, hb, k, hy⟩ :=
    GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E N (Matrix.GeneralLinearGroup.map (pInf E) x)
  have hbP := GlobalTheory.IwasawaAdelic.mem_parab_of_upper n h b hb
  obtain ⟨u, hu, hbu⟩ := exists_levi_mul_unip (Cinf E) (stdBlocks n h) ⟨b, hbP⟩
  set L := leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩) with hL
  have hN := leviEmb_mem_normalizer (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩)
  have hu' : L * u * L⁻¹ ∈ unipRad (Cinf E) (stdBlocks n h) := (Subgroup.mem_normalizer_iff.1 hN u).1 hu
  refine ⟨infGL E N (L * u * L⁻¹), GlobalTheory.IwasawaAdelic.infGL_mem_unipRad E n h _ hu',
    fun i => leviProj (Cinf E) (stdBlocks n h) ⟨b, hbP⟩ i, k, ?_⟩
  rw [← GlobalTheory.IwasawaAdelic.infGL_leviEmb, ← hL]
  conv_lhs => rw [← infGL_mul_finGL x, hy]
  simp only [Subtype.coe_mk] at hbu
  rw [hbu]
  simp only [map_mul, map_inv]
  group

/- English proof (translation)
Rewrite using `[locGL, cc_cornerGL_leviEmb, finGL, cc_cornerGL_leviEmb]`. Both sides reduce to the same expression.
-/
theorem finGL_locGL_leviEmb {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (w : HeightOneSpectrum (𝓞 E))
    (μ : ∀ i, GL (Fin (n i)) (w.adicCompletion E)) :
    finGL E N (locGL E N w (leviEmb (w.adicCompletion E) (stdBlocks n h) μ)) =
      leviEmb (Ad E) (stdBlocks n h) (fun i => finGL E (n i) (locGL E (n i) w (μ i))) := by
  rw [locGL, cc_cornerGL_leviEmb, finGL, cc_cornerGL_leviEmb]
  rfl

/- English proof (translation)
Conclude with `cc_cornerGL_mem_unipRad n h _ (cc_cornerGL_mem_unipRad n h _ hu)`.
-/
theorem finGL_locGL_mem_unipRad {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (w : HeightOneSpectrum (𝓞 E))
    {u : GL (Fin N) (w.adicCompletion E)} (hu : u ∈ unipRad (w.adicCompletion E) (stdBlocks n h)) :
    finGL E N (locGL E N w u) ∈ unipRad (Ad E) (stdBlocks n h) := by
  exact cc_cornerGL_mem_unipRad n h _ (cc_cornerGL_mem_unipRad n h _ hu)

/- English proof (translation)
Establish `hc` using `LocSph.comm_locGL w _ hy g`. Use `conv_lhs => rw [← infGL_mul_finGL y]`. Use `conv_rhs => rw [← infGL_mul_finGL y]`. Rewrite using `[mul_assoc, ← (finGL E N).map_mul, hc, (finGL E N).map_mul, ← mul_assoc, infGL_comm, mul_assoc]`.
-/
theorem commute_finGL_locGL {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) {y : GA E N}
    (hy : Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y) = 1)
    (g : GL (Fin N) (w.adicCompletion E)) :
    y * finGL E N (locGL E N w g) = finGL E N (locGL E N w g) * y := by
  have hc := LocSph.comm_locGL w _ hy g
  conv_lhs => rw [← infGL_mul_finGL y]
  conv_rhs => rw [← infGL_mul_finGL y]
  rw [mul_assoc, ← (finGL E N).map_mul, hc, (finGL E N).map_mul, ← mul_assoc, infGL_comm, mul_assoc]

/- English proof (translation)
Use `set g := Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y)`. Use `⟨y * (finGL E N (locGL E N w g))⁻¹, g, ?_, by group⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_inv, map_inv, pFin_finGL, pLoc_locGL, mul_inv_cancel]`.
-/
theorem exists_split_at {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) (y : GA E N) :
    ∃ (y₀ : GA E N) (g : GL (Fin N) (w.adicCompletion E)),
      Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y₀) = 1 ∧
        y = y₀ * finGL E N (locGL E N w g) := by
  set g := Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y)
  refine ⟨y * (finGL E N (locGL E N w g))⁻¹, g, ?_, by group⟩
  rw [map_mul, map_mul, map_inv, map_inv, pFin_finGL, pLoc_locGL, mul_inv_cancel]

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
