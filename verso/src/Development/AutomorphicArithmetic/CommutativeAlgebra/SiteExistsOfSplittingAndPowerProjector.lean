import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFiniteStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `hM hS hB hP`. Introduce `p _ D G hSc E _ _ e gb hstd w q _ r 𝔴 𝔫 hpl hat hlev`. Establish `sp` using `hS p D hSc.m1 q`. Take `⟨N₀, 𝔞, h3, hcq, hcp, hsup, hupow, hlv⟩` from `hlev`. Take `⟨f, b, hmat, hstdb, hqmem, hnorm⟩` from `hB q (datAt hat sp) hSc.a1 hSc.m1 E e gb hstd w 𝔴 r hpl hat.le N₀ h3 hcq`.

Take `⟨M⟩` from `hM.ex q (datAt hat sp) (Ow w) b N₀ h3 hcq`. Establish `hEt : UpperTheory.Gal.FiniteEtaleModels.IsEtIdeal b 𝔞` using `(hM.placeOf q (datAt hat sp) (Ow w) b r 𝔴 hat.max hstdb.pmem hSc.a1 hstdb.ule hstdb.tw 𝔞 hsup).2 hupow`. Take `⟨Y, π, ρ, hov, ⟨hmπ⟩, hgal⟩` from `hM.finModel q (datAt hat sp) (Ow w) b N₀ h3 hcq 𝔞 1 hEt M`. Establish `hfin : IsFinite π` using `hgal.fin`. Establish `het : Etale π` using `hgal.etale`.

Establish `hMproj : IsProjOver M.s` using `hM.proj q (datAt hat sp) (Ow w) b N₀ h3 hcq hSc.cpt M`. Establish `hYproj : IsProjOver Y.s`. Rewrite using `[← hov]`. Conclude with `GlobalTheory.T.isProjOver_comp_finite (Ow w) M.X Y.X π M.s hfin hMproj`. Establish `hYsm : SmoothOfRelativeDimension (0 + (datAt hat sp).a * ((datAt hat sp).n - 1)) Y.s`.

Rewrite using `[← hov]`. Use `haveI : SmoothOfRelativeDimension 0 π := by`. Rewrite using `[← AlgebraicGeometry.Etale.eq_smoothOfRelativeDimension_zero]`. Conclude with `het`. Use `haveI := M.smooth`.

Use `infer_instance`. Establish `hPw` using `fun k => hP q (datAt hat sp) (Ow w) b N₀ h3 hcq Y.X Y.s Y.univ k`. Conclude with `⟨⟨hat, sp, f, b, hmat, N₀, 𝔞, hstdb, hqmem, hnorm, hcp, hsup, hupow, hlv, M, Y, π, hov, hmπ, hfin, het, fun k => (hPw k).1 hYproj, fun k => (hPw k).2 _ hYsm⟩⟩`.
-/
theorem UpperTheory.site_exists_of_splitting_and_power_projector :
    MIn → SplitQ → BaseEx → PowProj → SiteEx := by
  intro hM hS hB hP
  intro p _ D G hSc E _ _ e gb hstd w q _ r 𝔴 𝔫 hpl hat hlev
  have sp := hS p D hSc.m1 q
  obtain ⟨N₀, 𝔞, h3, hcq, hcp, hsup, hupow, hlv⟩ := hlev
  obtain ⟨f, b, hmat, hstdb, hqmem, hnorm⟩ :=
    hB q (datAt hat sp) hSc.a1 hSc.m1 E e gb hstd w 𝔴 r hpl hat.le N₀ h3 hcq
  obtain ⟨M⟩ := hM.ex q (datAt hat sp) (Ow w) b N₀ h3 hcq
  have hEt : UpperTheory.Gal.FiniteEtaleModels.IsEtIdeal b 𝔞 :=
    (hM.placeOf q (datAt hat sp) (Ow w) b r 𝔴 hat.max hstdb.pmem hSc.a1 hstdb.ule hstdb.tw 𝔞 hsup).2 hupow
  obtain ⟨Y, π, ρ, hov, ⟨hmπ⟩, hgal⟩ := hM.finModel q (datAt hat sp) (Ow w) b N₀ h3 hcq 𝔞 1 hEt M
  have hfin : IsFinite π := hgal.fin
  have het : Etale π := hgal.etale
  have hMproj : IsProjOver M.s := hM.proj q (datAt hat sp) (Ow w) b N₀ h3 hcq hSc.cpt M
  have hYproj : IsProjOver Y.s := by
    rw [← hov]
    exact GlobalTheory.T.isProjOver_comp_finite (Ow w) M.X Y.X π M.s hfin hMproj
  have hYsm : SmoothOfRelativeDimension (0 + (datAt hat sp).a * ((datAt hat sp).n - 1)) Y.s := by
    rw [← hov]
    haveI : SmoothOfRelativeDimension 0 π := by
      rw [← AlgebraicGeometry.Etale.eq_smoothOfRelativeDimension_zero]
      exact het
    haveI := M.smooth
    infer_instance
  have hPw := fun k => hP q (datAt hat sp) (Ow w) b N₀ h3 hcq Y.X Y.s Y.univ k
  exact ⟨⟨hat, sp, f, b, hmat, N₀, 𝔞, hstdb, hqmem, hnorm, hcp, hsup, hupow, hlv, M, Y, π, hov, hmπ,
    hfin, het, fun k => (hPw k).1 hYproj, fun k => (hPw k).2 _ hYsm⟩⟩
