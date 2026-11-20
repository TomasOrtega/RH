import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PointEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceOf

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ F n T Φ hΦ h4 J hJ x L p hp hTI hM P hP hPp`. Establish `key : ∀ Q : Ideal L.R, J.map Φ ≤ L.π Q ↔ J ≤ Q.comap (T.phi Φ L : T.B.B →+* L.R)`. Introduce `Q`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Conclude with `Iff.rfl`.

Take `⟨y, j, hker, hloc, hρ, hψ, hpt⟩` from `UpperTheory.V.Pr.pointEx l O F n T Φ hΦ x L p hp.prime hp.dim hp.char`. Substitute `hker` using the available equality. Take `⟨h1, h3, hI, -⟩` from `UpperTheory.V.Pr.niceOf l O F n T x L y j hloc hp hρ hψ`. Rewrite `hM`, the goal using `[key]`. Use `haveI := hP`.

Conclude with `hJ y (j.comp (T.phi Φ L)) ⟨h1, hI hTI, h3, h4 y⟩ hpt (fun a ha => hM ha) (T.back Φ L P) (fun a ha => hPp ha)`.
-/
theorem UpperTheory.V.Pr.p1Of :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.FirstPrimeConditionTransfer := by
  intro l _ O _ _ _ _ _ F n T Φ hΦ h4 J hJ x L p hp hTI hM P hP hPp
  have key : ∀ Q : Ideal L.R, J.map Φ ≤ L.π Q ↔ J ≤ Q.comap (T.phi Φ L : T.B.B →+* L.R) := by
    intro Q
    rw [Ideal.map_le_iff_le_comap]
    exact Iff.rfl
  obtain ⟨y, j, hker, hloc, hρ, hψ, hpt⟩ :=
    UpperTheory.V.Pr.pointEx l O F n T Φ hΦ x L p hp.prime hp.dim hp.char
  subst hker
  obtain ⟨h1, h3, hI, -⟩ := UpperTheory.V.Pr.niceOf l O F n T x L y j hloc hp hρ hψ
  rw [key] at hM ⊢
  haveI := hP
  exact hJ y (j.comp (T.phi Φ L)) ⟨h1, hI hTI, h3, h4 y⟩ hpt (fun a ha => hM ha) (T.back Φ L P)
    (fun a ha => hPp ha)
