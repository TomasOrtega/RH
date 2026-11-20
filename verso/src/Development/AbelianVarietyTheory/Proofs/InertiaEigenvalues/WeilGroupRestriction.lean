import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilRestrict

open scoped Pointwise

section

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 K) (𝓞 L) x), IsScalarTower.algebraMap_apply K L Ω]`. Both sides reduce to the same expression.
-/
theorem comap_eq_of_isPlaceOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 K) (𝓞 L) x), IsScalarTower.algebraMap_apply K L Ω]
  rfl

/- English proof (translation)
Establish `hw` using `comap_eq_of_isPlaceOver h h'`. Establish `: v'.asIdeal.LiesOver v.asIdeal` using `⟨hw.symm⟩`. Use `⟨v'.asIdeal.inertiaDeg (𝓞 K), ?_⟩` and prove the remaining obligations. Simplify using `only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]`. Conclude with `(Ideal.absNorm_pow_inertiaDeg v.asIdeal v'.asIdeal).symm`.
-/
theorem normV_eq_pow_of_isPlaceOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    ∃ f : ℕ, normV v' = normV v ^ f := by
  have hw := comap_eq_of_isPlaceOver h h'
  have : v'.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K), ?_⟩
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal v'.asIdeal).symm

variable (K) in

def resG : G L Ω →* G K Ω where
  toFun σ := σ.restrictScalars K
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem resG_apply (σ : G L Ω) (z : Ω) : resG K σ z = σ z := rfl

/- English proof (translation)
Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_one]`. Introduce `s hs`. Rewrite using `[Filter.mem_map]`. Take `⟨E, hE, hEs⟩` from `(krullTopology_mem_nhds_one_iff K Ω s).1 hs`.

Set `b` to `Module.finBasis K E`. Establish `hU : IsOpen (⋂ i, (MulAction.stabilizer (G L Ω) (b i : Ω) : Set (G L Ω)))` using `isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral _`. Use `Filter.mem_of_superset (hU.mem_nhds (Set.mem_iInter.2 fun i => (MulAction.stabilizer (G L Ω) _).one_mem)) fun g hg => hEs ?_` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`.

Establish `hb : ∀ i, g (b i : Ω) = b i` using `fun i => by`. Use `Set.mem_iInter.1 hg i` as an intermediate fact. Rewrite `this` using `[SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`. Then use the resulting hypothesis. Establish `hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : Ω)`. Use `congrArg E.val (b.sum_repr ⟨x, hx⟩)` as an intermediate fact.

Rewrite `this` using `[map_sum]`. Simplify using `only [map_smul] at this`. Conclude with `this.symm`. Rewrite using `[hx', map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_smul, resG_apply, hb]`.
-/
theorem continuous_resG [Algebra.IsIntegral L Ω] : Continuous (resG (L := L) (Ω := Ω) K) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
  let b := Module.finBasis K E
  have hU : IsOpen (⋂ i, (MulAction.stabilizer (G L Ω) (b i : Ω) : Set (G L Ω))) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral _
  refine Filter.mem_of_superset (hU.mem_nhds (Set.mem_iInter.2 fun i =>
    (MulAction.stabilizer (G L Ω) _).one_mem)) fun g hg => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, g (b i : Ω) = b i := fun i => by
    have := Set.mem_iInter.1 hg i
    rwa [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : Ω) := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm
  rw [hx', map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, resG_apply, hb]

variable {A : ValuationSubring Ω}

/- English proof (translation)
Establish `h1 : σ • A = A` using `hσ`. Use `show (resG K σ) • A = A`. Conclude with `h1`.
-/
theorem resG_mem_Dec {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) : resG K σ ∈ Dec (F := K) A := by
  have h1 : σ • A = A := hσ
  show (resG K σ) • A = A
  exact h1

/- English proof (translation)
Assemble the required witnesses or components as `⟨resG_mem_Dec hσ.1, fun x hx => hσ.2 x hx⟩`.
-/
theorem resG_mem_Ine {σ : G L Ω} (hσ : σ ∈ Ine (F := L) A) : resG K σ ∈ Ine (F := K) A :=
  ⟨resG_mem_Dec hσ.1, fun x hx => hσ.2 x hx⟩

/- English proof (translation)
Use `⟨resG_mem_Dec hσ.1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `e1 : (q ^ f) ^ b = q ^ (f * b)` using `(pow_mul q f b).symm`. Establish `e2 : (q ^ f) ^ a = q ^ (f * a)` using `(pow_mul q f a).symm`. Use `hσ.2 x hx` as an intermediate fact. Rewrite `this` using `[e1, e2]`.

Conclude with `this`.
-/
theorem actsAs_resG {q f a b : ℕ} {σ : G L Ω} (hσ : ActsAs A (q ^ f) σ a b) :
    ActsAs A q (resG K σ) (f * a) (f * b) := by
  refine ⟨resG_mem_Dec hσ.1, fun x hx => ?_⟩
  have e1 : (q ^ f) ^ b = q ^ (f * b) := (pow_mul q f b).symm
  have e2 : (q ^ f) ^ a = q ^ (f * a) := (pow_mul q f a).symm
  have := hσ.2 x hx
  rw [e1, e2] at this
  exact this

variable {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

def resWeil (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : Weil h' →* Weil h :=
  ((resG K).comp (Weil h').subtype).codRestrict (Weil h) fun σ => by
    obtain ⟨f, hf⟩ := normV_eq_pow_of_isPlaceOver h h'
    obtain ⟨a, b, hab⟩ := (mem_Weil h').1 σ.2
    rw [hf] at hab
    exact (mem_Weil h).2 ⟨_, _, actsAs_resG hab⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem resWeil_apply (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h') (z : Ω) :
    (resWeil h h' σ : G K Ω) z = (σ : G L Ω) z := rfl

def resIne : Ine (F := L) A → Ine (F := K) A := fun σ => ⟨resG K (σ : G L Ω), resG_mem_Ine (K := K) (L := L) (σ := (σ : G L Ω)) σ.2⟩

/- English proof (translation)
The claim follows from `((continuous_resG (K := K)).comp continuous_subtype_val).subtype_mk _`.
-/
theorem continuous_resIne [Algebra.IsIntegral L Ω] : Continuous (resIne (K := K) (L := L) (A := A)) :=
  ((continuous_resG (K := K)).comp continuous_subtype_val).subtype_mk _

/- English proof (translation)
Establish `e : {σ : Ine (F` using `L) A | (f.comp (resWeil h h')) (ineIncl h' σ) = 1} = resIne ⁻¹' {τ : Ine (F := K) A | f (ineIncl h τ) = 1} := rfl`. Use `show IsOpen {σ : Ine (F := L) A | (f.comp (resWeil h h')) (ineIncl h' σ) = 1}`. Rewrite using `[e]`. Conclude with `hf.preimage continuous_resIne`.
-/
theorem isSmooth_comp_resWeil [Algebra.IsIntegral L Ω] (h : IsPlaceOver A v) (h' : IsPlaceOver A v')
    {M : Type*} [Monoid M] {f : Weil h →* M} (hf : IsSmooth f) : IsSmooth (f.comp (resWeil h h')) := by
  have e : {σ : Ine (F := L) A | (f.comp (resWeil h h')) (ineIncl h' σ) = 1} =
      resIne ⁻¹' {τ : Ine (F := K) A | f (ineIncl h τ) = 1} := rfl
  show IsOpen {σ : Ine (F := L) A | (f.comp (resWeil h h')) (ineIncl h' σ) = 1}
  rw [e]
  exact hf.preimage continuous_resIne

end

/- English proof (translation)
Introduce `K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h'`. Use `haveI : Algebra.IsIntegral L Ω := (IsAlgClosure.isAlgebraic (R := L) (K := Ω)).isIntegral`. Conclude with `⟨resWeil h h', resWeil_apply h h', fun M _ f hf => isSmooth_comp_resWeil h h' hf⟩`.
-/
theorem weil_restrict : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), ∃ r : Weil h' →* Weil h, (∀ (σ : Weil h') (z : Ω), (r σ : G K Ω) z = (σ : G L Ω) z) ∧ ∀ (M : Type) [Monoid M] (f : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth f → GlobalTheory.WeilDeligne.IsSmooth (f.comp r) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h'
  haveI : Algebra.IsIntegral L Ω := (IsAlgClosure.isAlgebraic (R := L) (K := Ω)).isIntegral
  exact ⟨resWeil h h', resWeil_apply h h', fun M _ f hf => isSmooth_comp_resWeil h h' hf⟩

end GlobalTheory.WeilRestrict
