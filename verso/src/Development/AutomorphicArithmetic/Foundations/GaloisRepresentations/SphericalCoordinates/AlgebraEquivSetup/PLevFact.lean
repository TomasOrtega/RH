import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

/- English proof (translation)
Distinguish the cases in `h : GlobalTheory.Cong.Apart u w`. Conclude with `Or.inl h`. Conclude with `Or.inr (GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc (not_not.1 h))`.
-/
private theorem apart_or {E : Type} [Field E] [NumberField E] [IsCMField E] (u w : Plc E) :
    GlobalTheory.Cong.Apart u w ∨ u = w ∨ u = UpperTheory.Gal.CertificateRingHomMap.cj w := by
  by_cases h : GlobalTheory.Cong.Apart u w
  · exact Or.inl h
  · exact Or.inr (GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc (not_not.1 h))

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.OnlyStab.conjSrc_invol w`.
-/
private theorem cj_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Plc E) :
    UpperTheory.Gal.CertificateRingHomMap.cj (UpperTheory.Gal.CertificateRingHomMap.cj w) = w := GlobalTheory.CompanionTheory.OnlyStab.conjSrc_invol w

/- English proof (translation)
Introduce `hA hI E _ _ _ A n p _ S T hc S₀ Kw w hw hp hcj`. Establish `hsec : ∀ x, T.sec ((T.at hc w hw hp).loc x) = CertificateRingHomMap.loc hw x` using `(hA E A n p S T hc w hw hp).1`. Establish `hn : 0 < n` using `S.facts.pos`. Use `⟨fun hwS => ⟨fun x hx => ?_, fun g hg => ?_⟩, fun hwS => ⟨fun x hx => ?_, fun g hg => ?_⟩⟩` and prove the remaining obligations. Use `show T.sec _ ∈ lev S₀ Kw`.

Rewrite using `[hsec, CertificateRingHomMap.mem_lev]`. Use `⟨by rw [CertificateRingHomMap.sim_loc]; exact one_mem _, fun u hu => ?_, fun u hu hcu => ?_⟩` and prove the remaining obligations. Break down `apart_or u w with h | h | h` into its components or cases. Rewrite using `[CertificateRingHomMap.comp_loc_of_apart hw h]`. Conclude with `one_mem _`.

Substitute `h` using the available equality. Rewrite using `[CertificateRingHomMap.comp_loc]`. Conclude with `hx`. Substitute `h` using the available equality. Conclude with `absurd hu hcj`.

Break down `apart_or u w with h | h | h` into its components or cases. Rewrite using `[CertificateRingHomMap.comp_loc_of_apart hw h]`. Conclude with `one_mem _`. Substitute `h` using the available equality. Conclude with `absurd hwS hu`.

Substitute `h; exact absurd (by rwa [cj_cj]) hcu` using the available equality. Conclude with `(CertificateRingHomMap.mem_lev.1 hg).2.1 w hwS`. Use `show T.sec _ ∈ lev S₀ Kw`. Rewrite using `[hsec, CertificateRingHomMap.mem_lev]`. Use `⟨by rw [CertificateRingHomMap.sim_loc]; exact one_mem _, fun u hu => ?_, fun u hu hcu => ?_⟩` and prove the remaining obligations.

Break down `apart_or u w with h | h | h` into its components or cases. Rewrite using `[CertificateRingHomMap.comp_loc_of_apart hw h]`. Conclude with `one_mem _`. Substitute `h` using the available equality. Conclude with `absurd hu hwS`.

Substitute `h` using the available equality. Conclude with `absurd hu hcj`. Break down `apart_or u w with h | h | h` into its components or cases. Rewrite using `[CertificateRingHomMap.comp_loc_of_apart hw h]`. Conclude with `one_mem _`.

Substitute `h` using the available equality. Rewrite using `[CertificateRingHomMap.comp_loc]`. Conclude with `hx`. Substitute `h` using the available equality. Use `(hI E n (CertificateRingHomMap.loc hw x) w hn).1 ?_ ?_` and prove the remaining obligations.

Rewrite using `[CertificateRingHomMap.sim_loc]`. Conclude with `one_mem _`. Rewrite using `[CertificateRingHomMap.comp_loc]`. Conclude with `hx`. Conclude with `(CertificateRingHomMap.mem_lev.1 hg).2.2 w hwS hcj`.
-/
theorem UpperTheory.Gal.W2.Seed.pLevFact :
    AtApart → IntConj → LevFact := by
  intro hA hI E _ _ _ A n p _ S T hc S₀ Kw w hw hp hcj
  have hsec : ∀ x, T.sec ((T.at hc w hw hp).loc x) = CertificateRingHomMap.loc hw x := (hA E A n p S T hc w hw hp).1
  have hn : 0 < n := S.facts.pos
  refine ⟨fun hwS => ⟨fun x hx => ?_, fun g hg => ?_⟩, fun hwS => ⟨fun x hx => ?_, fun g hg => ?_⟩⟩
  · show T.sec _ ∈ lev S₀ Kw
    rw [hsec, CertificateRingHomMap.mem_lev]
    refine ⟨by rw [CertificateRingHomMap.sim_loc]; exact one_mem _, fun u hu => ?_, fun u hu hcu => ?_⟩
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; rw [CertificateRingHomMap.comp_loc]; exact hx
      · subst h; exact absurd hu hcj
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; exact absurd hwS hu
      · subst h; exact absurd (by rwa [cj_cj]) hcu
  · exact (CertificateRingHomMap.mem_lev.1 hg).2.1 w hwS
  · show T.sec _ ∈ lev S₀ Kw
    rw [hsec, CertificateRingHomMap.mem_lev]
    refine ⟨by rw [CertificateRingHomMap.sim_loc]; exact one_mem _, fun u hu => ?_, fun u hu hcu => ?_⟩
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; exact absurd hu hwS
      · subst h; exact absurd hu hcj
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; rw [CertificateRingHomMap.comp_loc]; exact hx
      · subst h
        refine (hI E n (CertificateRingHomMap.loc hw x) w hn).1 ?_ ?_
        · rw [CertificateRingHomMap.sim_loc]; exact one_mem _
        · rw [CertificateRingHomMap.comp_loc]; exact hx
  · exact (CertificateRingHomMap.mem_lev.1 hg).2.2 w hwS hcj
