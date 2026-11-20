import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianOverSubfield
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalCoreLeFixingSubgroupNormalClosure
import ReciprocityTheory.GaloisValuations.Global
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemRealOfSq

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Introduce `x` and use `by rw [IsScalarTower.algebraMap_apply F K Ω] exact h (algebraMap (𝓞 F) (𝓞 K) x)`.
-/
private theorem over_under {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra K Ω] [Algebra F Ω] [IsScalarTower F K Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
  rw [IsScalarTower.algebraMap_apply F K Ω]
  exact h (algebraMap (𝓞 F) (𝓞 K) x)

/- English proof (translation)
Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[ValuationSubring.coe_pointwise_smul, ValuationSubring.coe_pointwise_smul]`. Use extensionality with `x`. Simplify using `only [Set.mem_smul_set, AlgEquiv.smul_def, hg]`.
-/
private theorem smul_congr {K K' Ω : Type} [Field K] [Field K'] [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    (A : ValuationSubring Ω) (g : G K Ω) (g' : G K' Ω) (hg : ∀ x, g x = g' x) : g • A = g' • A := by
  apply SetLike.coe_injective
  rw [ValuationSubring.coe_pointwise_smul, ValuationSubring.coe_pointwise_smul]
  ext x
  simp only [Set.mem_smul_set, AlgEquiv.smul_def, hg]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh55.mem_real_of_sq hq hδ`.
-/
private theorem mem_real_of_sq {Y : Type} [Field Y] {δ : Y} {q : ℕ} (hq : 0 < q) (hδ : δ ^ 2 = (q : Y)) :
    δ ∈ maximalRealSubfield Y :=
  _root_.UpperTheory.Reformulated.B.Qh55.mem_real_of_sq hq hδ

/- English proof (translation)
The claim follows from `(mem_maximalRealSubfield_iff _).2 fun φ => (mem_maximalRealSubfield_iff x).1 hx (φ.comp (algebraMap E Y))`.
-/
private theorem algebraMap_mem_real {E Y : Type} [Field E] [Field Y] [Algebra E Y] {x : E}
    (hx : x ∈ maximalRealSubfield E) : algebraMap E Y x ∈ maximalRealSubfield Y :=
  (mem_maximalRealSubfield_iff _).2 fun φ => (mem_maximalRealSubfield_iff x).1 hx (φ.comp (algebraMap E Y))

/- English proof (translation)
Introduce `hv`. Use `haveI : IsAlgClosure (maximalRealSubfield Y) Ω := ⟨IsAlgClosure.isAlgClosed Y, Algebra.IsAlgebraic.trans _ Y Ω⟩`. Establish `h1` using `over_under (F := maximalRealSubfield Y) hw₁`. Establish `h2` using `over_under (F := maximalRealSubfield Y) hw₂`. Rewrite `h2` using `[← hv]`.

Take `⟨ρ, hρ⟩` from `exists_smul_eq_of_isPlaceOver h1 h2`. Establish `hδr : δ ∈ maximalRealSubfield Y` using `mem_real_of_sq hq hδ`. Establish `hρδ : ρ (algebraMap Y Ω δ) = algebraMap Y Ω δ` using `ρ.commutes (⟨δ, hδr⟩ : maximalRealSubfield Y)`. Establish `hρF : ∀ x : maximalRealSubfield E, ρ.toRingEquiv (algebraMap (maximalRealSubfield E) Ω x) = algebraMap (maximalRealSubfield E) Ω x` using `fun x => by`. Establish `h` using `ρ.commutes (⟨algebraMap E Y x, algebraMap_mem_real x.2⟩ : maximalRealSubfield Y)`.

Establish `e : algebraMap (maximalRealSubfield Y) Ω ⟨algebraMap E Y x, algebraMap_mem_real x.2⟩ = algebraMap (maximalRealSubfield E) Ω x`. Express the relevant statement in the definitionally equal form `algebraMap Y Ω (algebraMap E Y x) = algebraMap E Ω x`. Conclude with `(IsScalarTower.algebraMap_apply E Y Ω _).symm`. Rewrite `h` using `[e]`. Conclude with `h`.

Set `ρ' : G (maximalRealSubfield E) Ω` to `AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv) hρF`. Set `σ' : G (maximalRealSubfield E) Ω` to `σ.restrictScalars _`. Establish `hg : ρ'⁻¹ * σ' ∈ Dec (F` using `maximalRealSubfield E) A := mem_Dec.2 (by`. Rewrite using `[mul_smul, inv_smul_eq_iff, smul_congr A σ' σ (fun _ => rfl), ← hρ, smul_congr A ρ' ρ (fun _ => rfl)])`. Establish `h3` using `hfix _ hg`.

Establish `h4 : σ' (algebraMap Y Ω δ) = ρ' (algebraMap Y Ω δ)`. Use `congrArg ρ' h3` as an intermediate fact. Rewrite `this` using `[AlgEquiv.mul_apply, ← AlgEquiv.mul_apply ρ', mul_inv_cancel, AlgEquiv.one_apply]`. Then use the resulting hypothesis. Establish `h5 : -algebraMap Y Ω δ = algebraMap Y Ω δ`. Establish `a : σ' (algebraMap Y Ω δ) = σ (algebraMap Y Ω δ)` using `rfl`.

Establish `b : ρ' (algebraMap Y Ω δ) = ρ (algebraMap Y Ω δ)` using `rfl`. Rewrite `h4` using `[a, b, hσ, hρδ]`. Conclude with `h4`. Use `haveI : CharZero Y := algebraRat.charZero Y`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective`.

Establish `h6 : algebraMap Y Ω δ = 0` using `self_eq_neg.1 h5.symm`. Establish `h7 : δ = 0` using `(map_eq_zero _).1 h6`. Rewrite `hδ` using `[h7]`. Establish `: (q : Y) = 0` using `by simpa using hδ.symm`. Conclude with `hq.ne' (by exact_mod_cast this)`.
-/
private theorem apart_of_moves {E Y Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Y] [NumberField Y] [IsCMField Y]
    [Field Ω] [Algebra E Y] [Algebra E Ω] [Algebra Y Ω] [IsScalarTower E Y Ω] [IsAlgClosure Y Ω] {δ : Y} {q : ℕ} (hq : 0 < q)
    (hδ : δ ^ 2 = (q : Y)) (A : ValuationSubring Ω) (σ : G E Ω) (hσ : σ (algebraMap Y Ω δ) = -algebraMap Y Ω δ)
    (hfix : ∀ g ∈ Dec (F := maximalRealSubfield E) A, g (algebraMap Y Ω δ) = algebraMap Y Ω δ)
    {w₁ w₂ : HeightOneSpectrum (𝓞 Y)} (hw₁ : IsPlaceOver A w₁) (hw₂ : IsPlaceOver (σ • A) w₂) : GlobalTheory.Cong.Apart w₁ w₂ := by
  intro hv
  haveI : IsAlgClosure (maximalRealSubfield Y) Ω :=
    ⟨IsAlgClosure.isAlgClosed Y, Algebra.IsAlgebraic.trans _ Y Ω⟩
  have h1 := over_under (F := maximalRealSubfield Y) hw₁
  have h2 := over_under (F := maximalRealSubfield Y) hw₂
  rw [← hv] at h2
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isPlaceOver h1 h2
  have hδr : δ ∈ maximalRealSubfield Y := mem_real_of_sq hq hδ
  have hρδ : ρ (algebraMap Y Ω δ) = algebraMap Y Ω δ := ρ.commutes (⟨δ, hδr⟩ : maximalRealSubfield Y)
  have hρF : ∀ x : maximalRealSubfield E, ρ.toRingEquiv (algebraMap (maximalRealSubfield E) Ω x) =
      algebraMap (maximalRealSubfield E) Ω x := fun x => by
    have h := ρ.commutes (⟨algebraMap E Y x, algebraMap_mem_real x.2⟩ : maximalRealSubfield Y)
    have e : algebraMap (maximalRealSubfield Y) Ω ⟨algebraMap E Y x, algebraMap_mem_real x.2⟩ =
        algebraMap (maximalRealSubfield E) Ω x := by
      change algebraMap Y Ω (algebraMap E Y x) = algebraMap E Ω x
      exact (IsScalarTower.algebraMap_apply E Y Ω _).symm
    rw [e] at h
    exact h
  let ρ' : G (maximalRealSubfield E) Ω := AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv) hρF
  let σ' : G (maximalRealSubfield E) Ω := σ.restrictScalars _
  have hg : ρ'⁻¹ * σ' ∈ Dec (F := maximalRealSubfield E) A := mem_Dec.2 (by
    rw [mul_smul, inv_smul_eq_iff, smul_congr A σ' σ (fun _ => rfl), ← hρ, smul_congr A ρ' ρ (fun _ => rfl)])
  have h3 := hfix _ hg
  have h4 : σ' (algebraMap Y Ω δ) = ρ' (algebraMap Y Ω δ) := by
    have := congrArg ρ' h3
    rwa [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply ρ', mul_inv_cancel, AlgEquiv.one_apply] at this
  have h5 : -algebraMap Y Ω δ = algebraMap Y Ω δ := by
    have a : σ' (algebraMap Y Ω δ) = σ (algebraMap Y Ω δ) := rfl
    have b : ρ' (algebraMap Y Ω δ) = ρ (algebraMap Y Ω δ) := rfl
    rw [a, b, hσ, hρδ] at h4
    exact h4
  haveI : CharZero Y := algebraRat.charZero Y
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  have h6 : algebraMap Y Ω δ = 0 := self_eq_neg.1 h5.symm
  have h7 : δ = 0 := (map_eq_zero _).1 h6
  rw [h7] at hδ
  have : (q : Y) = 0 := by simpa using hδ.symm
  exact hq.ne' (by exact_mod_cast this)

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ T Q h0 t ht`. Take `⟨⟨δ, ⟨⟨q, hq, hδ⟩, _, s, hs, hsδ⟩, hfix⟩, _, _⟩` from `h0`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω t`. Set `σ : G E Ω` to `AlgEquiv.ofRingEquiv (f := s) (fun x => hs (algebraMap E Ω) x)`. Establish `hA' : IsPlaceOver (σ • A) t` using `GlobalTheory.NormalClosureSolv.isPlaceOver_smul' hA σ`.

Take `⟨w₁, hw₁⟩` from `GlobalTheory.AbOverSubfield.exists_place_between (K := ↥Q.K) hA`. Take `⟨w₂, hw₂⟩` from `GlobalTheory.AbOverSubfield.exists_place_between (K := ↥Q.K) hA'`. Conclude with `⟨w₁, w₂, eq_of_isPlaceOver (over_under hw₁) hA, eq_of_isPlaceOver (over_under hw₂) hA', apart_of_moves hq hδ A σ hsδ (hfix t ht A hA) hw₁ hw₂⟩`.
-/
theorem double : Double := by
  intro E Ω _ _ _ _ _ _ T Q h0 t ht
  obtain ⟨⟨δ, ⟨⟨q, hq, hδ⟩, _, s, hs, hsδ⟩, hfix⟩, _, _⟩ := h0
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω t
  let σ : G E Ω := AlgEquiv.ofRingEquiv (f := s) (fun x => hs (algebraMap E Ω) x)
  have hA' : IsPlaceOver (σ • A) t := GlobalTheory.NormalClosureSolv.isPlaceOver_smul' hA σ
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.AbOverSubfield.exists_place_between (K := ↥Q.K) hA
  obtain ⟨w₂, hw₂⟩ := GlobalTheory.AbOverSubfield.exists_place_between (K := ↥Q.K) hA'
  exact ⟨w₁, w₂, eq_of_isPlaceOver (over_under hw₁) hA, eq_of_isPlaceOver (over_under hw₂) hA',
    apart_of_moves hq hδ A σ hsδ (hfix t ht A hA) hw₁ hw₂⟩

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
