import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernDegreePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace GlobalTheory.Published.ChernDegreeComplexModel

variable (Y : Var ℂ)

/- English proof (translation)
Take `⟨i₀, h₀⟩` from `exists_chart φ.isLB (genericPoint Y.X)`. Conclude with `⟨ofLB φ.isLB i₀ h₀, frameRat L i₀ h₀, presents_ofLB φ.isLB i₀ h₀⟩`.
-/
theorem exists_presents {L : LB Y.X} (φ : Weight Y.str (RingHom.id ℂ) L) :
    ∃ (Δ : Y.Dv) (r : L.ι → Y.Fnˣ), Presents Δ L r := by
  obtain ⟨i₀, h₀⟩ := exists_chart φ.isLB (genericPoint Y.X)
  exact ⟨ofLB φ.isLB i₀ h₀, frameRat L i₀ h₀, presents_ofLB φ.isLB i₀ h₀⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, (proj ℂ n).presents_hyp (proj_gen_mem ℂ n 0), isCInf_fs (proj ℂ n) (RingHom.id ℂ), inter_projHyp ℂ n⟩`.
-/
theorem hyp_proj (n : ℕ) : ∃ r, Presents (projHyp ℂ n) (proj ℂ n).O1 r ∧
    (fs (proj ℂ n) (RingHom.id ℂ)).IsCInf ∧ (proj ℂ n).inter (fun _ => projHyp ℂ n) = 1 :=
  ⟨_, (proj ℂ n).presents_hyp (proj_gen_mem ℂ n 0), isCInf_fs (proj ℂ n) (RingHom.id ℂ), inter_projHyp ℂ n⟩

/- English proof (translation)
Establish `: CompactSpace (CxPts Y.str (RingHom.id ℂ))` using `CxPts.compactSpace _ Y.isProjOver`. Set `R` to `AnRead.all Y.str (RingHom.id ℂ) Y.dim`. Establish `hs : φ.IsSmooth R` using `(Weight.isCInf_iff_isSmooth R).1 h`. Establish `hm` using `ReciprocityTheory.AnForm.M.mIntegrableCont R.finAtlas (fun _ => φ.locPot) (fun _ => Weight.isPotential_locPot hs) (fun _ => 1) continuous_const`. Conclude with `((Weight.chernInt_eq_mInt R h measurable_const).1).2 hm`.
-/
theorem integrable {L : LB Y.X} (φ : Weight Y.str (RingHom.id ℂ) L) (h : φ.IsCInf) :
    φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) := by
  have : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace _ Y.isProjOver
  let R := AnRead.all Y.str (RingHom.id ℂ) Y.dim
  have hs : φ.IsSmooth R := (Weight.isCInf_iff_isSmooth R).1 h
  have hm := ReciprocityTheory.AnForm.M.mIntegrableCont R.finAtlas (fun _ => φ.locPot)
    (fun _ => Weight.isPotential_locPot hs) (fun _ => 1) continuous_const
  exact ((Weight.chernInt_eq_mInt R h measurable_const).1).2 hm

/- English proof (translation)
Establish `hneg : (fs Y (RingHom.id ℂ)).chernPart Y.dim (-1) = 0` using `Weight.chernPart_neg_eq_zero (isCInf_fs Y (RingHom.id ℂ)) (Weight.semiPosReg_fsBasis _ _ _ _ _)`. Unfold `Weight.chernInt`. Rewrite using `[hneg]`. Rewrite using `[MeasureTheory.Measure.restrict_zero, MeasureTheory.integral_zero_measure, sub_zero]`. Conclude with `MeasureTheory.integral_nonneg fun _ => zero_le_one`.
-/
theorem mass_fs_nonneg : 0 ≤ (fs Y (RingHom.id ℂ)).chernInt Y.dim Set.univ (fun _ => 1) := by
  have hneg : (fs Y (RingHom.id ℂ)).chernPart Y.dim (-1) = 0 :=
    Weight.chernPart_neg_eq_zero (isCInf_fs Y (RingHom.id ℂ)) (Weight.semiPosReg_fsBasis _ _ _ _ _)
  unfold Weight.chernInt
  rw [hneg]
  rw [MeasureTheory.Measure.restrict_zero, MeasureTheory.integral_zero_measure, sub_zero]
  exact MeasureTheory.integral_nonneg fun _ => zero_le_one

/- English proof (translation)
The claim follows from `(chernDegree_point (RingHom.id ℂ) Δ L φ h).2`.
-/
theorem point (Δ : (proj ℂ 0).Dv) (L : LB (proj ℂ 0).X) (φ : Weight (proj ℂ 0).str (RingHom.id ℂ) L)
    (h : φ.IsCInf) : φ.chernInt 0 Set.univ (fun _ => 1) = ((proj ℂ 0).inter (fun _ => Δ) : ℝ) :=
  (chernDegree_point (RingHom.id ℂ) Δ L φ h).2

/- English proof (translation)
Take `⟨r, hr, hfs, hint⟩` from `hyp_proj n`. Establish `key` using `(H (proj ℂ n) (projHyp ℂ n) (proj ℂ n).O1 r hr _ hfs).2`. Rewrite `key` using `[hint, proj_dim]`. Conclude with `key` after adjusting the coercions.
-/
theorem mass_proj (H : ChernDegreeComplex) (n : ℕ) :
    (fs (proj ℂ n) (RingHom.id ℂ)).chernInt n Set.univ (fun _ => 1) = 1 := by
  obtain ⟨r, hr, hfs, hint⟩ := hyp_proj n
  have key := (H (proj ℂ n) (projHyp ℂ n) (proj ℂ n).O1 r hr _ hfs).2
  rw [hint, proj_dim] at key
  exact_mod_cast key

/- English proof (translation)
Take `⟨Δ, r, hp⟩` from `exists_presents Y φ`. Conclude with `(H Y Δ L r hp φ h).2.trans (H Y Δ L r hp ψ h').2.symm`.
-/
theorem mass_indep (H : ChernDegreeComplex) {L : LB Y.X} (φ ψ : Weight Y.str (RingHom.id ℂ) L)
    (h : φ.IsCInf) (h' : ψ.IsCInf) :
    φ.chernInt Y.dim Set.univ (fun _ => 1) = ψ.chernInt Y.dim Set.univ (fun _ => 1) := by
  obtain ⟨Δ, r, hp⟩ := exists_presents Y φ
  exact (H Y Δ L r hp φ h).2.trans (H Y Δ L r hp ψ h').2.symm

end GlobalTheory.Published.ChernDegreeComplexModel
