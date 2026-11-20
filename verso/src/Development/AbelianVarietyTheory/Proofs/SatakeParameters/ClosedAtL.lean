import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedOfCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstOfCoordRev
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

noncomputable section

namespace GlobalTheory.LimitTop

open Matrix Formalism.WeaklyAdmissibleFiltrations

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ a ha P AI hT w A hA O _ _ _ Bw hBw J r hr hss C hC hρ`. Take `⟨T⟩` from `hT`. Set `jl : ↥(GK Bw.Kw) →* Formalism.ConjugateSelfDual.G E Ω` to `(ReciprocityTheory.Gal.Dec (F := E) A).subtype.comp Bw.e.symm.toMonoidHom`. Establish `hjl : Continuous jl` using `continuous_subtype_val.comp Bw.e_symm_cont`. Set `jE : E →+* ↥Bw.Kw.1` to `(Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E`.

Set `J' : (↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ` to `fun τ'' => J (τ''.toRingHom.comp jE)`. Take `⟨Cv⟩` from `GlobalTheory.TraceConjugationCover.cover_exists l (Formalism.ConjugateSelfDual.G E Ω) a Bw.LL r hr hss C (fun ρ hm => (hρ ρ hm).1) hC`. Take `⟨Cv'⟩` from `GlobalTheory.BKLim.cover_pull l (Formalism.ConjugateSelfDual.G E Ω) ↥(GK Bw.Kw) jl hjl a Bw.LL r C Cv`. Establish `tr : ∀ (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = ((ρ.com …` using `E) A).subtype) L (r'.comp Bw.e.toMonoidHom) ∧ Bw.repE L (r'.comp Bw.e.toMonoidHom) = R := by`. Introduce `ρ L r' R hle hR he`.

Use `⟨⟨hle, ?_⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `g i k`. Use `he (Bw.e g) i k` as an intermediate fact. Simplify `this` using `[jl, mapRep]`. Use `MonoidHom.ext fun g => LinearMap.ext fun v => ?_` and prove the remaining obligations.

Rewrite using `[hR]`. Simplify using `[LocBridge.repE, Matrix.toLin'_apply]`. Establish `hCl : ∀ ρ₁ ∈ (fun ρ => ρ.comp jl) '' C, ∀ (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = (ρ₁ g).val i k) → IsSst P R ∧ ∀ (τ …`. Introduce and unpack `_ ⟨ρ, hm, rfl⟩ L r' R hle hR he`. Take `⟨hmod, hrep⟩` from `tr ρ L r' R hle hR he`.

Use `⟨hrep ▸ GlobalTheory.SstModel.main l P AI ⟨T⟩ E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O Bw a _ L _ hmod (hρ ρ hm).2.1, fun τ n => ?_⟩` and prove the remaining obligations. Establish `hi : IsInduced Bw ((L.1.val.comp τ).toRingHom.comp jE) τ` using `fun x => rfl`. Use `IsJumpsAt.count_eq P hmod hi ((hρ ρ hm).2.2 _ L τ hi) n` as an intermediate fact. Rewrite using `[← hrep]`. Conclude with `this.symm`.

Establish `hcr : (∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype)) → ∀ ρ₁ ∈ (fun ρ => ρ.comp jl) '' C, ∀ (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = (ρ₁ g).val i k) → IsCry …`. Introduce `hc`. Introduce and unpack `_ ⟨ρ, hm, rfl⟩ L r' R hle hR he`. Take `⟨hmod, hrep⟩` from `tr ρ L r' R hle hR he`. Rewrite using `[← hrep]`.

Conclude with `(hmod.isCrysAt_iff P).1 (hc ρ hm)`. Establish `hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l)))` using `Units.continuous_val.comp hr`. Establish `model : ∀ L₀ : FinExt l, ∃ (L : FinExt l) (r₁ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) ↥L.1), L₀.1 ≤ L.1 ∧ Bw.LL.1 ≤ L.1 ∧ mapRep (algebraMap ↥L.1 (Om l)) r₁ = r`. Introduce `L₀`. Use `haveI := L₀.2`.

Use `haveI := Bw.LL.2`. Take `⟨L, hL, hmem⟩` from `GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a r hcont ⟨L₀.1 ⊔ Bw.LL.1, IntermediateField.finiteDimensional_sup _ _⟩`. Take `⟨r₁, -, hr₁⟩` from `GlobalTheory.DeRhamRead.exists_model_of_mem r hcont L hmem`. Conclude with `⟨L, r₁, le_sup_left.trans hL, le_sup_right.trans hL, hr₁⟩`. Establish `top : ∀ (L : FinExt l) (r₁ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) ↥L.1), Bw.LL.1 ≤ L.1 → mapRep (algebraMap ↥L.1 (Om l)) r₁ = r → IsModel Bw (r.comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype) L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧ Bw.IsdRE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧ (∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), Bw.multE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ n = ((J' (L.1.val. …`.

Introduce `L r₁ hle hr₁`. Establish `hmod : IsModel Bw (r.comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype) L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := ⟨hle, by rw [← hr₁]; rfl⟩`. Take `⟨hdr, hmu, hcy⟩` from `GlobalTheory.CovClose.closed_of_cover l Bw.Kw Bw.LL P AI T a ha Bw.LL_split (r.comp jl) _ Cv' J' hCl L (r₁.comp jl) (Bw.repE L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) hle (fun g v => by simp [LocBridge.repE, jl, Matrix.toLin'_apply]) (fun g i k => by rw [← hr₁]; …`. Use `⟨hmod, ?_, hmu, fun hc => hcy (hcr hc)⟩` and prove the remaining obligations. Establish `h` using `hdr`.

Unfold `Formalism.MainNotions.N.IsDR at h`. Rewrite `h` using `[Module.finrank_fin_fun]`. Conclude with `h`. Use `⟨⟨?_, fun τ LL' τ' hi => ?_⟩, fun hc => ?_⟩` and prove the remaining obligations. Take `⟨L, r₁, -, hle, hr₁⟩` from `model Bw.LL`.

Take `⟨hmod, hdr, -, -⟩` from `top L r₁ hle hr₁`. Conclude with `⟨L, _, hmod, hdr⟩`. Take `⟨L, r₁, hL', hle, hr₁⟩` from `model LL'`. Take `⟨hmod, hdr, hmu, -⟩` from `top L r₁ hle hr₁`. Set `τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1` to `(IntermediateField.inclusion hL').comp τ'`.

Establish `hi' : IsInduced Bw τ τ''` using `fun x => hi x`. Establish `hτ : (L.1.val.comp τ'').toRingHom.comp jE = τ` using `RingHom.ext fun x => (hi x).symm`. Use `⟨L, _, hmod, hdr, τ'', hi', fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[hmu τ'' n]`. Use `show ((J τ).count n : ℤ) = ((J ((L.1.val.comp τ'').toRingHom.comp jE)).count n : ℤ)`.

Rewrite using `[hτ]`. Take `⟨L, r₁, -, hle, hr₁⟩` from `model Bw.LL`. Take `⟨hmod, -, -, hcy⟩` from `top L r₁ hle hr₁`. Conclude with `⟨L, _, hmod, hcy hc⟩`.
-/
theorem closedAtL : ClosedAtL := by
  intro E Ω _ _ _ _ _ l _ a ha P AI hT w A hA O _ _ _ Bw hBw J r hr hss C hC hρ
  classical
  obtain ⟨T⟩ := hT

  let jl : ↥(GK Bw.Kw) →* Formalism.ConjugateSelfDual.G E Ω := (ReciprocityTheory.Gal.Dec (F := E) A).subtype.comp Bw.e.symm.toMonoidHom
  have hjl : Continuous jl := continuous_subtype_val.comp Bw.e_symm_cont

  let jE : E →+* ↥Bw.Kw.1 := (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E
  let J' : (↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ := fun τ'' => J (τ''.toRingHom.comp jE)
  obtain ⟨Cv⟩ := GlobalTheory.TraceConjugationCover.cover_exists l (Formalism.ConjugateSelfDual.G E Ω) a Bw.LL r hr hss C (fun ρ hm => (hρ ρ hm).1) hC
  obtain ⟨Cv'⟩ := GlobalTheory.BKLim.cover_pull l (Formalism.ConjugateSelfDual.G E Ω) ↥(GK Bw.Kw) jl hjl a Bw.LL r C Cv

  have tr : ∀ (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 →
      (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = ((ρ.comp jl) g).val i k) →
      IsModel Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r'.comp Bw.e.toMonoidHom) ∧
        Bw.repE L (r'.comp Bw.e.toMonoidHom) = R := by
    intro ρ L r' R hle hR he
    refine ⟨⟨hle, ?_⟩, ?_⟩
    · ext g i k
      have := he (Bw.e g) i k
      simpa [jl, mapRep] using this
    · refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
      rw [hR]
      simp [LocBridge.repE, Matrix.toLin'_apply]

  have hCl : ∀ ρ₁ ∈ (fun ρ => ρ.comp jl) '' C, ∀ (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = (ρ₁ g).val i k) →
      IsSst P R ∧ ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD Bw.Kw) R τ n = ((J' (L.1.val.comp τ)).count n : ℤ) := by
    rintro _ ⟨ρ, hm, rfl⟩ L r' R hle hR he
    obtain ⟨hmod, hrep⟩ := tr ρ L r' R hle hR he
    refine ⟨hrep ▸ GlobalTheory.SstModel.main l P AI ⟨T⟩ E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O Bw a _ L _ hmod (hρ ρ hm).2.1, fun τ n => ?_⟩
    have hi : IsInduced Bw ((L.1.val.comp τ).toRingHom.comp jE) τ := fun x => rfl
    have := IsJumpsAt.count_eq P hmod hi ((hρ ρ hm).2.2 _ L τ hi) n
    rw [← hrep]
    exact this.symm
  have hcr : (∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) → ∀ ρ₁ ∈ (fun ρ => ρ.comp jl) '' C,
      ∀ (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)),
      Bw.LL.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = (ρ₁ g).val i k) → IsCrys (P.PD Bw.Kw) R := by
    intro hc
    rintro _ ⟨ρ, hm, rfl⟩ L r' R hle hR he
    obtain ⟨hmod, hrep⟩ := tr ρ L r' R hle hR he
    rw [← hrep]
    exact (hmod.isCrysAt_iff P).1 (hc ρ hm)

  have hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) := Units.continuous_val.comp hr
  have model : ∀ L₀ : FinExt l, ∃ (L : FinExt l) (r₁ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) ↥L.1), L₀.1 ≤ L.1 ∧ Bw.LL.1 ≤ L.1 ∧
      mapRep (algebraMap ↥L.1 (Om l)) r₁ = r := by
    intro L₀
    haveI := L₀.2
    haveI := Bw.LL.2
    obtain ⟨L, hL, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a r hcont
      ⟨L₀.1 ⊔ Bw.LL.1, IntermediateField.finiteDimensional_sup _ _⟩
    obtain ⟨r₁, -, hr₁⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem r hcont L hmem
    exact ⟨L, r₁, le_sup_left.trans hL, le_sup_right.trans hL, hr₁⟩

  have top : ∀ (L : FinExt l) (r₁ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) ↥L.1), Bw.LL.1 ≤ L.1 → mapRep (algebraMap ↥L.1 (Om l)) r₁ = r →
      IsModel Bw (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
      Bw.IsdRE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
      (∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ),
        Bw.multE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ n = ((J' (L.1.val.comp τ)).count n : ℤ)) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) →
        Bw.IsCrysE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by
    intro L r₁ hle hr₁
    have hmod : IsModel Bw (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
      ⟨hle, by rw [← hr₁]; rfl⟩
    obtain ⟨hdr, hmu, hcy⟩ := GlobalTheory.CovClose.closed_of_cover l Bw.Kw Bw.LL P AI T a ha Bw.LL_split (r.comp jl) _ Cv' J' hCl L
      (r₁.comp jl) (Bw.repE L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) hle
      (fun g v => by simp [LocBridge.repE, jl, Matrix.toLin'_apply]) (fun g i k => by rw [← hr₁]; rfl)
    refine ⟨hmod, ?_, hmu, fun hc => hcy (hcr hc)⟩
    have h := hdr
    unfold Formalism.MainNotions.N.IsDR at h
    rw [Module.finrank_fin_fun] at h
    exact h
  refine ⟨⟨?_, fun τ LL' τ' hi => ?_⟩, fun hc => ?_⟩
  · obtain ⟨L, r₁, -, hle, hr₁⟩ := model Bw.LL
    obtain ⟨hmod, hdr, -, -⟩ := top L r₁ hle hr₁
    exact ⟨L, _, hmod, hdr⟩
  · obtain ⟨L, r₁, hL', hle, hr₁⟩ := model LL'
    obtain ⟨hmod, hdr, hmu, -⟩ := top L r₁ hle hr₁
    let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1 := (IntermediateField.inclusion hL').comp τ'
    have hi' : IsInduced Bw τ τ'' := fun x => hi x
    have hτ : (L.1.val.comp τ'').toRingHom.comp jE = τ := RingHom.ext fun x => (hi x).symm
    refine ⟨L, _, hmod, hdr, τ'', hi', fun n => ?_⟩
    rw [hmu τ'' n]
    show ((J τ).count n : ℤ) = ((J ((L.1.val.comp τ'').toRingHom.comp jE)).count n : ℤ)
    rw [hτ]
  · obtain ⟨L, r₁, -, hle, hr₁⟩ := model Bw.LL
    obtain ⟨hmod, -, -, hcy⟩ := top L r₁ hle hr₁
    exact ⟨L, _, hmod, hcy hc⟩

end GlobalTheory.LimitTop
