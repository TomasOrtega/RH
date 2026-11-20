import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.InfLifts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsLpDimMono0CharPol
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolEqOfDegNeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRestrictionWdCompatible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemWeilGroupAtPlaceOfFixesExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsModelOfMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsWdPst
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2

/- English proof (translation)
Introduce `hMix hTor hDR hRec hR1 E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w σ hσ hfix hcase A h rc hrc hm0`. Break down `hcase with hpt | ⟨hQ, hap⟩` into its components or cases. Take `⟨haway, habove⟩` from `hR1 E Ω l ι n hn π χ hπ r hr w σ hσ hpt`. Use `⟨fun hl => ?_, fun hl => ?_⟩` and prove the remaining obligations. Take `⟨hm, he⟩` from `haway hl A h`.

Conclude with `⟨hm, fun t => by rw [he rc hrc]⟩`. Take `⟨hd, hb⟩` from `habove hl`. Use `⟨hd, fun Q AI hT O _ _ _ Bw hj => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `hb Q AI hT A h O Bw hj`. Conclude with `⟨h1, h2, fun t => h3 rc hrc _⟩`.

Establish `hmix` using `hMix E Ω n π w σ hσ hfix hap A h rc hrc hm0`. Take `⟨X, P, χ', u, h', T, rc', hP, hW, hinf, hTc, hPT, hrc', hine⟩` from `hTor E Ω l ι n hn π χ hπ r hr w σ hσ hQ hmix A h rc hrc`. Take `⟨haway, habove⟩` from `hR1 X.K Ω l ι n hn P χ' hP (resTo X.K r) hW u T hTc hPT`. Use `⟨fun hl => ?_, fun hl => ?_⟩` and prove the remaining obligations. Establish `hl' : ((l : ℕ) : 𝓞 X.K) ∉ u.asIdeal`.

Introduce `hm`. Apply `hl` to reduce the goal to its premises. Rewrite using `[← h]`. Rewrite `hm` using `[← h']`. Simplify using `using hm`.

Take `⟨hm', he⟩` from `haway hl' A h'`. Establish `hres` using `GlobalTheory.AboveL.wdOf_restricts E X.K Ω A w u h h' l ι n r hl hl' hr.1`. Take `⟨-, hmono, hcp⟩` from `GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E X.K Ω A w u h h' _ _ hres`. Use `⟨hmono.mp hm', fun t => ?_⟩` and prove the remaining obligations. Take `⟨t', hz, hc⟩` from `hine t`.

Rewrite using `[← hcp (ineIncl h t) (ineIncl h' t') (fun z => by simpa [coe_ineIncl] using hz z), he rc' hrc', hc]`. Establish `hl' : ((l : ℕ) : 𝓞 X.K) ∈ u.asIdeal`. Rewrite `hl` using `[← h]`. Rewrite using `[← h']`. Simplify using `using hl`.

Take `⟨-, hb⟩` from `habove hl'`. Use `⟨?_, fun Q AI hT O _ _ _ Bw hj => ?_⟩` and prove the remaining obligations. Use `hDR E Ω l ι n π r hr.1 w fun A' hA' => ?_` and prove the remaining obligations. Take `⟨rc₁, hrc₁⟩` from `hRec E Ω A' w hA'`. Take `⟨X₁, P₁, χ₁, u₁, h₁, T₁, rc₁', hP₁, hW₁, hinf₁, hTc₁, hPT₁, -, -⟩` from `hTor E Ω l ι n hn π χ hπ r hr w σ hσ hQ hmix A' hA' rc₁ hrc₁`.

Establish `hl₁ : ((l : ℕ) : 𝓞 X₁.K) ∈ u₁.asIdeal`. Rewrite `hl` using `[← hA']`. Rewrite using `[← h₁]`. Simplify using `using hl`. Conclude with `⟨X₁, P₁, u₁, h₁, hinf₁, ((hR1 X₁.K Ω l ι n hn P₁ χ₁ hP₁ (resTo X₁.K r) hW₁ u₁ T₁ hTc₁ hPT₁).2 hl₁).1⟩`.

Take `⟨LL₀, Bw₀, hjj₀, -, -⟩` from `GlobalTheory.AboveLRes.exists_bridge (L := X.K) Bw hj Bw.LL`. Establish `hj₀ : GlobalTheory.Pst.Induces Bw₀` using `fun x => by rw [hjj₀]; exact hj x`. Establish `hp₀` using `(hb Q AI hT A h' _ Bw₀ hj₀).1`. Establish `hpst : IsPstAt Q Bw (r.comp (Dec (F` using `E) A).subtype) := GlobalTheory.AboveLRes.isPstAt_of_resTo E X.K Ω A l Q AI hT n r hr.1 O _ Bw Bw₀ hj hj₀ hp₀`. Take `⟨O', _, _, _, Bw', hj', -, hres⟩` from `GlobalTheory.AboveLRes.wdAt_resTo E X.K Ω A w u h h' l ι Q AI hT n r O Bw hj hpst`.

Take `⟨-, hmono, hcp⟩` from `GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E X.K Ω A w u h h' _ _ hres`. Take `⟨-, hm', hc'⟩` from `hb Q AI hT A h' O' Bw' hj'`. Use `⟨hpst, hmono.mp hm', fun t => ?_⟩` and prove the remaining obligations. Take `⟨t', hz, hc⟩` from `hine t`. Rewrite using `[← hcp (ineIncl h t) (ineIncl h' t') (fun z => by simpa [coe_ineIncl] using hz z), hc' rc' hrc', hc]`.
-/
theorem UpperTheory.Gal.ToralGalois.R2.r2g :
    MixedOf → ToTor → DRDesc → UpperTheory.Zero.LLC.RecTExists → GlobalTheory.DeRhamOfPlainTorus.R1 → LocalGlobalCompatAtIwahoriFixedPlaces := by
  intro hMix hTor hDR hRec hR1 E Ω _ _ _ _ _ _ l _ ι n hn π χ hπ r hr w σ hσ hfix hcase A h rc hrc hm0
  rcases hcase with hpt | ⟨hQ, hap⟩
  · obtain ⟨haway, habove⟩ := hR1 E Ω l ι n hn π χ hπ r hr w σ hσ hpt
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · obtain ⟨hm, he⟩ := haway hl A h
      exact ⟨hm, fun t => by rw [he rc hrc]⟩
    · obtain ⟨hd, hb⟩ := habove hl
      refine ⟨hd, fun Q AI hT O _ _ _ Bw hj => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hb Q AI hT A h O Bw hj
      exact ⟨h1, h2, fun t => h3 rc hrc _⟩
  · have hmix := hMix E Ω n π w σ hσ hfix hap A h rc hrc hm0
    obtain ⟨X, P, χ', u, h', T, rc', hP, hW, hinf, hTc, hPT, hrc', hine⟩ :=
      hTor E Ω l ι n hn π χ hπ r hr w σ hσ hQ hmix A h rc hrc
    obtain ⟨haway, habove⟩ := hR1 X.K Ω l ι n hn P χ' hP (resTo X.K r) hW u T hTc hPT
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hl' : ((l : ℕ) : 𝓞 X.K) ∉ u.asIdeal := by
        intro hm
        apply hl
        rw [← h]
        rw [← h'] at hm
        simpa using hm
      obtain ⟨hm', he⟩ := haway hl' A h'
      have hres := GlobalTheory.AboveL.wdOf_restricts E X.K Ω A w u h h' l ι n r hl hl' hr.1
      obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E X.K Ω A w u h h' _ _ hres
      refine ⟨hmono.mp hm', fun t => ?_⟩
      obtain ⟨t', hz, hc⟩ := hine t
      rw [← hcp (ineIncl h t) (ineIncl h' t') (fun z => by simpa [coe_ineIncl] using hz z), he rc' hrc', hc]
    · have hl' : ((l : ℕ) : 𝓞 X.K) ∈ u.asIdeal := by
        rw [← h] at hl
        rw [← h']
        simpa using hl
      obtain ⟨-, hb⟩ := habove hl'
      refine ⟨?_, fun Q AI hT O _ _ _ Bw hj => ?_⟩
      · refine hDR E Ω l ι n π r hr.1 w fun A' hA' => ?_
        obtain ⟨rc₁, hrc₁⟩ := hRec E Ω A' w hA'
        obtain ⟨X₁, P₁, χ₁, u₁, h₁, T₁, rc₁', hP₁, hW₁, hinf₁, hTc₁, hPT₁, -, -⟩ :=
          hTor E Ω l ι n hn π χ hπ r hr w σ hσ hQ hmix A' hA' rc₁ hrc₁
        have hl₁ : ((l : ℕ) : 𝓞 X₁.K) ∈ u₁.asIdeal := by
          rw [← hA'] at hl
          rw [← h₁]
          simpa using hl
        exact ⟨X₁, P₁, u₁, h₁, hinf₁,
          ((hR1 X₁.K Ω l ι n hn P₁ χ₁ hP₁ (resTo X₁.K r) hW₁ u₁ T₁ hTc₁ hPT₁).2 hl₁).1⟩
      · obtain ⟨LL₀, Bw₀, hjj₀, -, -⟩ := GlobalTheory.AboveLRes.exists_bridge (L := X.K) Bw hj Bw.LL
        have hj₀ : GlobalTheory.Pst.Induces Bw₀ := fun x => by rw [hjj₀]; exact hj x
        have hp₀ := (hb Q AI hT A h' _ Bw₀ hj₀).1
        have hpst : IsPstAt Q Bw (r.comp (Dec (F := E) A).subtype) :=
          GlobalTheory.AboveLRes.isPstAt_of_resTo E X.K Ω A l Q AI hT n r hr.1 O _ Bw Bw₀ hj hj₀ hp₀
        obtain ⟨O', _, _, _, Bw', hj', -, hres⟩ :=
          GlobalTheory.AboveLRes.wdAt_resTo E X.K Ω A w u h h' l ι Q AI hT n r O Bw hj hpst
        obtain ⟨-, hmono, hcp⟩ := GlobalTheory.AboveL.restricts_lpDim_mono0_charPol E X.K Ω A w u h h' _ _ hres
        obtain ⟨-, hm', hc'⟩ := hb Q AI hT A h' O' Bw' hj'
        refine ⟨hpst, hmono.mp hm', fun t => ?_⟩
        obtain ⟨t', hz, hc⟩ := hine t
        rw [← hcp (ineIncl h t) (ineIncl h' t') (fun z => by simpa [coe_ineIncl] using hz z), hc' rc' hrc', hc]
