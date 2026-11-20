import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GaloisLiftFixedPoints

open scoped Pointwise

section

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/- English proof (translation)
The claim follows from `IntermediateField.mem_bot.1 ((InfiniteGalois.mem_bot_iff_fixed y).2 hy)`.
-/
theorem exists_of_fixed (y : Ω) (hy : ∀ s : Formalism.ConjugateSelfDual.G K Ω, s y = y) : ∃ x : K, algebraMap K Ω x = y :=
  IntermediateField.mem_bot.1 ((InfiniteGalois.mem_bot_iff_fixed y).2 hy)

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

noncomputable def liftEquiv (φ : Ω ≃+* Ω) (h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ (algebraMap K Ω x))
    (h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ.symm (algebraMap K Ω x)) : K ≃+* K where
  toFun x := (h1 x).choose
  invFun x := (h2 x).choose
  left_inv x := (algebraMap K Ω).injective (by
    rw [(h2 _).choose_spec, (h1 x).choose_spec, φ.symm_apply_apply])
  right_inv x := (algebraMap K Ω).injective (by
    rw [(h1 _).choose_spec, (h2 x).choose_spec, φ.apply_symm_apply])
  map_mul' x y := (algebraMap K Ω).injective (by
    rw [(h1 _).choose_spec, map_mul, map_mul, map_mul, (h1 x).choose_spec, (h1 y).choose_spec])
  map_add' x y := (algebraMap K Ω).injective (by
    rw [(h1 _).choose_spec, map_add, map_add, map_add, (h1 x).choose_spec, (h1 y).choose_spec])

/- English proof (translation)
The claim follows from `(h1 x).choose_spec`.
-/
theorem liftEquiv_spec (φ : Ω ≃+* Ω) (h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ (algebraMap K Ω x))
    (h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ.symm (algebraMap K Ω x)) (x : K) :
    algebraMap K Ω (liftEquiv φ h1 h2 x) = φ (algebraMap K Ω x) :=
  (h1 x).choose_spec

end

end GlobalTheory.GaloisLiftFixedPoints

open scoped Pointwise
open GlobalTheory.GaloisLiftFixedPoints in
/- English proof (translation)
Introduce `F Ω _ _ _ _ _ _ K _ _ _ _ _ _ l _ ι a π r g c hc hsurj hr`. Establish `ginv : ∀ z : Ω, g⁻¹ (g z) = z` using `fun z => by`. Rewrite using `[← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]`. Establish `gg : ∀ z : Ω, g (g⁻¹ z) = z` using `fun z => by`. Rewrite using `[← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]`.

Establish `hcx : ∀ (s : G K Ω) (x : Ω), c s x = g (s (g⁻¹ x))` using `fun s x => by`. Use `congrArg (fun φ : G F Ω => φ x) (hc s)` as an intermediate fact. Conclude with `this`. Use `set σ' : Ω ≃+* Ω := (g⁻¹ : G F Ω).toRingEquiv with hσ'`. Establish `hsymm : ∀ z : Ω, σ'.symm z = g z` using `fun z => by`.

Rewrite using `[RingEquiv.symm_apply_eq]`. Conclude with `(ginv z).symm`. Establish `h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = σ' (algebraMap K Ω x)` using `fun x => by`. Use `exists_of_fixed _ fun s => ?_` and prove the remaining obligations. Establish `e` using `hcx s (algebraMap K Ω x)`.

Rewrite `e` using `[AlgEquiv.commutes]`. Use `show s (g⁻¹ (algebraMap K Ω x)) = g⁻¹ (algebraMap K Ω x)`. Establish `e2` using `congrArg (fun z => g⁻¹ z) e`. Simplify using `only [ginv] at e2`. Conclude with `e2.symm`.

Establish `h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = σ'.symm (algebraMap K Ω x)` using `fun x => by`. Rewrite using `[hsymm]`. Use `exists_of_fixed _ fun s => ?_` and prove the remaining obligations. Take `⟨t, rfl⟩` from `hsurj s`. Rewrite using `[hcx, ginv, AlgEquiv.commutes]`.

Use `set τ : K ≃+* K := liftEquiv σ' h1 h2 with hτ`. Establish `hL : IsLift τ σ'` using `fun x => (liftEquiv_spec σ' h1 h2 x).symm`. Establish `hτF : ∀ y : F, τ (algebraMap F K y) = algebraMap F K y` using `fun y => (algebraMap K Ω).injective (by`. Rewrite using `[← hL, ← IsScalarTower.algebraMap_apply]`. Conclude with `AlgEquiv.commutes _ _)`.

Establish `hconj : ∀ s : G K Ω, c s = conjGal hL s` using `fun s => AlgEquiv.ext fun x => by`. Rewrite using `[conjGal_apply, hsymm, hcx]`. Both sides reduce to the same expression. Establish `hσA : ∀ A : ValuationSubring Ω, ∀ x, σ' x ∈ A ↔ x ∈ g • A` using `fun A x => by`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]`.

Both sides reduce to the same expression. Establish `hfrob : ∀ (A : ValuationSubring Ω) (q : ℕ) (s : G K Ω), IsFrob A q s → IsFrob (g • A) q (c s)` using `fun A q s hs => by`. Rewrite using `[hconj]`. Use `⟨conjGal_mem_Dec hL (hσA A) hs.1, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← val_lt_one (hσA A), map_sub, map_pow, apply_conjGal]`.

Conclude with `hs.2 _ ((A.valuation_le_one_iff _).2 ((hσA A x).2 (((g • A).valuation_le_one_iff _).1 hx)))`. Establish `hine : ∀ (A : ValuationSubring Ω) (s : G K Ω), s ∈ Ine (F` using `K) A → c s ∈ Ine (F := K) (g • A) := fun A s hs => by`. Rewrite using `[hconj]`. Conclude with `conjGal_mem_Ine hL (hσA A) hs`. Use `set e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv τ with he`.

Establish `hunder : ∀ w : HeightOneSpectrum (𝓞 K), (preplace τ w).under (𝓞 F) = w.under (𝓞 F)` using `fun w => by`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Establish `hx : e (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x` using `RingOfIntegers.ext (hτF (x : F))`. Use `show algebraMap (𝓞 F) (𝓞 K) x ∈ (preplace τ w).asIdeal ↔ algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal`.

Rewrite using `[mem_preplace, ← he, hx]`. Establish `hnorm : ∀ w : HeightOneSpectrum (𝓞 K), normV (preplace τ w) = normV w` using `fun w => by show Nat.card (𝓞 K ⧸ (w.asIdeal.comap (e : 𝓞 K →+* 𝓞 K))) = Nat.card (𝓞 K ⧸ w.asIdeal)`. Conclude with `Nat.card_congr (Ideal.quotientEquiv _ _ e (Ideal.map_comap_of_surjective (e : 𝓞 K →+* 𝓞 K) e.surjective _).symm).toEquiv`. Establish `hinj : Function.Injective (preplace τ)` using `fun u v huv => (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ)).symm.injective huv`. Unfold `AttRes at hr ⊢`.

Use `filter_upwards [hinj.tendsto_cofinite.eventually hr] with w hw f hf`. Establish `hf' : normV (preplace τ w) = normV ((preplace τ w).under (𝓞 F)) ^ f`. Rewrite using `[hnorm, hunder]`. Conclude with `hf`. Take `⟨B, hB, hE⟩` from `hw f hf'`.

Rewrite `hB`, `hE` using `[hunder]`. Use `⟨B, hB, fun A hA => ?_⟩` and prove the remaining obligations. Take `⟨k1, k2⟩` from `hE (g • A) (isPlaceOver_preplace hL (hσA A) hA)`. Use `⟨fun s hs => k1 _ (hine A s hs), fun s hs => ?_⟩` and prove the remaining obligations. Use `k2 (c s) (by rw [hnorm]; exact hfrob A _ s hs)` as an intermediate fact.

Rewrite using `[MonoidHom.comp_apply, map_inv]`. Conclude with `this`.
-/
theorem _root_.GlobalTheory.T.attached_rep_conjugate_invariant : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)) (g : G F Ω) (c : G K Ω →* G K Ω), (∀ s, res F Ω K (c s) = g * res F Ω K s * g⁻¹) → Function.Surjective c → AttRes π ι K r → AttRes π ι K (r.comp c) := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ l _ ι a π r g c hc hsurj hr
  have ginv : ∀ z : Ω, g⁻¹ (g z) = z := fun z => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have gg : ∀ z : Ω, g (g⁻¹ z) = z := fun z => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hcx : ∀ (s : G K Ω) (x : Ω), c s x = g (s (g⁻¹ x)) := fun s x => by
    have := congrArg (fun φ : G F Ω => φ x) (hc s)
    exact this
  set σ' : Ω ≃+* Ω := (g⁻¹ : G F Ω).toRingEquiv with hσ'
  have hsymm : ∀ z : Ω, σ'.symm z = g z := fun z => by
    rw [RingEquiv.symm_apply_eq]
    exact (ginv z).symm
  have h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = σ' (algebraMap K Ω x) := fun x => by
    refine exists_of_fixed _ fun s => ?_
    have e := hcx s (algebraMap K Ω x)
    rw [AlgEquiv.commutes] at e
    show s (g⁻¹ (algebraMap K Ω x)) = g⁻¹ (algebraMap K Ω x)
    have e2 := congrArg (fun z => g⁻¹ z) e
    simp only [ginv] at e2
    exact e2.symm
  have h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = σ'.symm (algebraMap K Ω x) := fun x => by
    rw [hsymm]
    refine exists_of_fixed _ fun s => ?_
    obtain ⟨t, rfl⟩ := hsurj s
    rw [hcx, ginv, AlgEquiv.commutes]
  set τ : K ≃+* K := liftEquiv σ' h1 h2 with hτ
  have hL : IsLift τ σ' := fun x => (liftEquiv_spec σ' h1 h2 x).symm
  have hτF : ∀ y : F, τ (algebraMap F K y) = algebraMap F K y := fun y => (algebraMap K Ω).injective (by
    rw [← hL, ← IsScalarTower.algebraMap_apply]
    exact AlgEquiv.commutes _ _)
  have hconj : ∀ s : G K Ω, c s = conjGal hL s := fun s => AlgEquiv.ext fun x => by
    rw [conjGal_apply, hsymm, hcx]
    rfl
  have hσA : ∀ A : ValuationSubring Ω, ∀ x, σ' x ∈ A ↔ x ∈ g • A := fun A x => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    rfl
  have hfrob : ∀ (A : ValuationSubring Ω) (q : ℕ) (s : G K Ω), IsFrob A q s → IsFrob (g • A) q (c s) :=
    fun A q s hs => by
      rw [hconj]
      refine ⟨conjGal_mem_Dec hL (hσA A) hs.1, fun x hx => ?_⟩
      rw [← val_lt_one (hσA A), map_sub, map_pow, apply_conjGal]
      exact hs.2 _ ((A.valuation_le_one_iff _).2 ((hσA A x).2 (((g • A).valuation_le_one_iff _).1 hx)))
  have hine : ∀ (A : ValuationSubring Ω) (s : G K Ω), s ∈ Ine (F := K) A → c s ∈ Ine (F := K) (g • A) :=
    fun A s hs => by
      rw [hconj]
      exact conjGal_mem_Ine hL (hσA A) hs
  set e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv τ with he
  have hunder : ∀ w : HeightOneSpectrum (𝓞 K), (preplace τ w).under (𝓞 F) = w.under (𝓞 F) := fun w => by
    apply HeightOneSpectrum.ext
    ext x
    have hx : e (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x := RingOfIntegers.ext (hτF (x : F))
    show algebraMap (𝓞 F) (𝓞 K) x ∈ (preplace τ w).asIdeal ↔ algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal
    rw [mem_preplace, ← he, hx]
  have hnorm : ∀ w : HeightOneSpectrum (𝓞 K), normV (preplace τ w) = normV w := fun w => by
    show Nat.card (𝓞 K ⧸ (w.asIdeal.comap (e : 𝓞 K →+* 𝓞 K))) = Nat.card (𝓞 K ⧸ w.asIdeal)
    exact Nat.card_congr (Ideal.quotientEquiv _ _ e
      (Ideal.map_comap_of_surjective (e : 𝓞 K →+* 𝓞 K) e.surjective _).symm).toEquiv
  have hinj : Function.Injective (preplace τ) := fun u v huv =>
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ)).symm.injective huv
  unfold AttRes at hr ⊢
  filter_upwards [hinj.tendsto_cofinite.eventually hr] with w hw f hf
  have hf' : normV (preplace τ w) = normV ((preplace τ w).under (𝓞 F)) ^ f := by
    rw [hnorm, hunder]
    exact hf
  obtain ⟨B, hB, hE⟩ := hw f hf'
  rw [hunder] at hB hE
  refine ⟨B, hB, fun A hA => ?_⟩
  obtain ⟨k1, k2⟩ := hE (g • A) (isPlaceOver_preplace hL (hσA A) hA)
  refine ⟨fun s hs => k1 _ (hine A s hs), fun s hs => ?_⟩
  have := k2 (c s) (by rw [hnorm]; exact hfrob A _ s hs)
  rw [MonoidHom.comp_apply, map_inv]
  exact this
