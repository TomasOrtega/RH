import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsIntDim
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractRelevant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace BlockImage

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Introduce and unpack `⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h`. Simplify using `only [blockIncl, Sigma.mk.inj_iff, heq_iff_eq, true_and] at h`. Rewrite using `[h]`.
-/
theorem blockIncl_injective (k₀ : ι) : Function.Injective (blockIncl (n := n) k₀) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  simp only [blockIncl, Sigma.mk.inj_iff, heq_iff_eq, true_and] at h
  rw [h]

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
The claim follows from `fun _ _ _ ↦ rfl`.
-/
theorem const_injective (k₀ : ι) : Function.Injective (fun _ : Unit ↦ k₀) := fun _ _ _ ↦ rfl

omit [Fintype ι] in

/- English proof (translation)
The claim follows from `FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent (ι := blockIdx fun _ : Unit ↦ n k₀) (ι' := blockIdx n) (j := fun _ : Unit ↦ k₀) (g := blockIncl k₀) (fun _ ↦ rfl) (const_injective k₀) (blockIncl_injective k₀) m f`.
-/
theorem rename_component (k₀ : ι) (m : Unit → ℕ) (f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ) :
    rename (blockIncl k₀) (weightedHomogeneousComponent (coordDeg fun _ : Unit ↦ n k₀) m f) =
      weightedHomogeneousComponent (coordDeg n) (Function.extend (fun _ : Unit ↦ k₀) m 0)
        (rename (blockIncl k₀) f) :=
  FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent (ι := blockIdx fun _ : Unit ↦ n k₀)
    (ι' := blockIdx n) (j := fun _ : Unit ↦ k₀) (g := blockIncl k₀) (fun _ ↦ rfl)
    (const_injective k₀) (blockIncl_injective k₀) m f

def projVariety (P : ArithVariety n) (k₀ : ι) : ArithVariety (fun _ : Unit ↦ n k₀) where
  ideal := P.projIdeal k₀
  isPrime := by
    have := P.isPrime
    exact Ideal.comap_isPrime _ _
  homogeneous f hf m := by
    change rename (blockIncl k₀) _ ∈ P.ideal
    rw [rename_component]
    exact P.homogeneous _ hf _
  relevant k := by
    obtain ⟨i, hi⟩ := P.relevant k₀
    refine ⟨i, fun h ↦ hi ?_⟩
    change rename (blockIncl k₀) (X ⟨k, i⟩) ∈ P.ideal at h
    rwa [rename_X] at h
  horizontal a ha := by
    change rename (blockIncl k₀) (C a) ∈ P.ideal at ha
    rw [rename_C] at ha
    exact P.horizontal a ha

variable {Ω : Type} [Field Ω]

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Establish `h : ((Geo.mConeMap (ι` using `blockIdx n) y).comp (rename (blockIncl k₀))) = ((rename (R := Ω) (fun _ : Unit ↦ k₀)).restrictScalars ℤ).comp (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩)) := by`. Use `MvPolynomial.algHom_ext fun v ↦ ?_` and prove the remaining obligations. Simplify using `[Geo.mConeMap, blockIncl]`. Conclude with `congrArg (fun φ : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι Ω ↦ φ f) h`.
-/
theorem mConeMap_rename (y : Coord n → Ω) (k₀ : ι)
    (f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ) :
    Geo.mConeMap (ι := blockIdx n) y (rename (blockIncl k₀) f) =
      rename (fun _ : Unit ↦ k₀)
        (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) f) := by
  have h : ((Geo.mConeMap (ι := blockIdx n) y).comp (rename (blockIncl k₀))) =
      ((rename (R := Ω) (fun _ : Unit ↦ k₀)).restrictScalars ℤ).comp
        (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩)) := by
    refine MvPolynomial.algHom_ext fun v ↦ ?_
    simp [Geo.mConeMap, blockIncl]
  exact congrArg (fun φ : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι Ω ↦ φ f) h

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Use extensionality with `f`. Simplify using `only [Ideal.mem_comap, Geo.mCoordIdeal, RingHom.mem_ker]`. Rewrite using `[mConeMap_rename]`. Conclude with `map_eq_zero_iff _ (rename_injective _ (const_injective k₀))`.
-/
theorem comap_mCoordIdeal (y : Coord n → Ω) (k₀ : ι) :
    (Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀)) =
      Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) := by
  ext f
  simp only [Ideal.mem_comap, Geo.mCoordIdeal, RingHom.mem_ker]
  rw [mConeMap_rename]
  exact map_eq_zero_iff _ (rename_injective _ (const_injective k₀))

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Rewrite `ha` using `[← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]`. Establish `h' : a ∈ I.comap (C : ℤ →+* Geo.MRing κ)` using `ha`. Rewrite `h'` using `[show I.comap (C : ℤ →+* Geo.MRing κ) = ⊥ from h]`.

Conclude with `(Submodule.mem_bot ℤ).mp h'`.
-/
theorem algebraMap_injective {K : Type} {κ : K → Type} (I : Ideal (Geo.MRing κ))
    (h : Geo.IsHorizontal I) : Function.Injective (algebraMap ℤ (Geo.MRing κ ⧸ I)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem] at ha
  have h' : a ∈ I.comap (C : ℤ →+* Geo.MRing κ) := ha
  rw [show I.comap (C : ℤ →+* Geo.MRing κ) = ⊥ from h] at h'
  exact (Submodule.mem_bot ℤ).mp h'

omit [Fintype ι] in

/- English proof (translation)
Introduce `s`. Take `⟨d, g, h, hg, hh, hne, heq⟩` from `hB s`. Establish `hom : ∀ f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ, Geo.IsMultiHomog (ι` using `blockIdx fun _ : Unit ↦ n k₀) f d → Geo.IsMultiHomog (ι := blockIdx n) (rename (blockIncl k₀) f) (Function.extend (fun _ : Unit ↦ k₀) d 0) := by`. Introduce `f hf`. Rewrite `hf`, the goal using `[← Bridge.isMultiHomog_iff]`.

Establish `hf' : IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ n k₀) f d` using `hf`. Rewrite using `[← hf'.weightedHomogeneousComponent_same, rename_component]`. Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous _ _`. Use `⟨Function.extend (fun _ : Unit ↦ k₀) d 0, rename (blockIncl k₀) g, rename (blockIncl k₀) h, hom g hg, hom h hh, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_rename]`.

Conclude with `hne`. Rewrite using `[aeval_rename, aeval_rename]`. Conclude with `heq`.
-/
theorem birational_of_block (y : Coord n → Ω) (k₀ : ι)
    (hB : Geo.Birational (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩)) :
    Geo.Birational (ι := blockIdx n) y := by
  intro s
  obtain ⟨d, g, h, hg, hh, hne, heq⟩ := hB s
  have hom : ∀ f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ,
      Geo.IsMultiHomog (ι := blockIdx fun _ : Unit ↦ n k₀) f d →
      Geo.IsMultiHomog (ι := blockIdx n) (rename (blockIncl k₀) f)
        (Function.extend (fun _ : Unit ↦ k₀) d 0) := by
    intro f hf
    rw [← Bridge.isMultiHomog_iff] at hf ⊢
    have hf' : IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ n k₀) f d := hf
    rw [← hf'.weightedHomogeneousComponent_same, rename_component]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  refine ⟨Function.extend (fun _ : Unit ↦ k₀) d 0, rename (blockIncl k₀) g, rename (blockIncl k₀) h,
    hom g hg, hom h hh, ?_, ?_⟩
  · rw [aeval_rename]
    exact hne
  · rw [aeval_rename, aeval_rename]
    exact heq

end BlockImage

open BlockImage in

/- English proof (translation)
Use `⟨fun ι _ _ n P k₀ ↦ ⟨projVariety P k₀, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `ι _ _ n Ω _ y k₀ D hA`. Use `⟨comap_mCoordIdeal y k₀, fun hB ↦ ?_⟩` and prove the remaining obligations. Take `⟨-, hMP, hHor, hKd⟩` from `hA`. Rewrite using `[← comap_mCoordIdeal y k₀]`.

Establish `hMP' : Geo.IsMultiProjPrime (ι` using `blockIdx fun _ : Unit ↦ n k₀) ((Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀))) := by`. Rewrite `hMP`, the goal using `[← Bridge.isMultiProjPrime_iff]`. Use `FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (ι := blockIdx fun _ : Unit ↦ n k₀) (ι' := blockIdx n) (j := fun _ : Unit ↦ k₀) (g := blockIncl k₀) (fun _ ↦ rfl) (const_injective k₀) (blockIncl_injective k₀) ?_ hMP` and prove the remaining obligations. Introduce and unpack `⟨k, i⟩ ⟨u, hu⟩`. Take `rfl : k₀ = k` from `hu`.

Conclude with `⟨⟨(), i⟩, rfl⟩`. Establish `hHor' : Geo.IsHorizontal (ι` using `blockIdx fun _ : Unit ↦ n k₀) ((Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀))) := by`. Use `(Ideal.ext fun a ↦ ?_).trans hHor` and prove the remaining obligations. Simplify using `only [Ideal.mem_comap]`. Rewrite using `[rename_C]`.

Use `⟨inferInstance, hMP', hHor', ?_⟩` and prove the remaining obligations. Establish `hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`. Introduce `k`. Take `⟨i, hi⟩` from `hMP.2.2 k`. Use `⟨i, fun h0 ↦ hi ?_⟩` and prove the remaining obligations.

Rewrite using `[Geo.mCoordIdeal, RingHom.mem_ker]`. Simplify using `[Geo.mConeMap, h0]`. Rewrite `hHor'`, `hMP'`, the goal using `[comap_mCoordIdeal y k₀]`. Use `hMP.1` as an intermediate fact. Use `hMP'.1` as an intermediate fact.

Establish `dimA` using `hDim _ (algebraMap_injective _ hHor)`. Establish `dimA'` using `hDim _ (algebraMap_injective _ hHor')`. Rewrite `dimA` using `[hTr ι (blockIdx n) Ω y (birational_of_block y k₀ hB) hrel hHor]`. Rewrite `dimA'` using `[hTr Unit (blockIdx fun _ : Unit ↦ n k₀) Ω _ hB (fun _ ↦ hrel k₀) hHor']`. Rewrite `dimA` using `[hKd]`.

Establish `h1 : ((D + 1 + Fintype.card ι : ℕ) : ℕ∞) = (Algebra.trdeg ℤ Ω + Fintype.card ι).toENat + 1` using `by exact_mod_cast dimA`. Simplify using `only [map_add, map_natCast] at h1`. Establish `key : (Algebra.trdeg ℤ Ω).toENat = D`. Generalize the expression as in `(Algebra.trdeg ℤ Ω).toENat = t at h1 ⊢`. Proceed by induction on `t using ENat.recTopCoe with`.

Consider the case `top => simp at h1`. Consider the case `coe m`. Normalize the coercions in `at h1 ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite using `[dimA']`.

Simplify using `only [map_add, map_natCast, Fintype.card_unit, key]`. Use `norm_cast`.
-/
theorem BlockImage.proof (hDim : IntDomainDim.Statement) (hTr : ConeTrdeg.Statement) :
    BlockImage.Statement := by
  refine ⟨fun ι _ _ n P k₀ ↦ ⟨projVariety P k₀, rfl⟩, ?_⟩
  intro ι _ _ n Ω _ y k₀ D hA
  refine ⟨comap_mCoordIdeal y k₀, fun hB ↦ ?_⟩
  obtain ⟨-, hMP, hHor, hKd⟩ := hA
  rw [← comap_mCoordIdeal y k₀]
  have hMP' : Geo.IsMultiProjPrime (ι := blockIdx fun _ : Unit ↦ n k₀)
      ((Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀))) := by
    rw [← Bridge.isMultiProjPrime_iff] at hMP ⊢
    refine FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename
      (ι := blockIdx fun _ : Unit ↦ n k₀) (ι' := blockIdx n) (j := fun _ : Unit ↦ k₀)
      (g := blockIncl k₀) (fun _ ↦ rfl) (const_injective k₀) (blockIncl_injective k₀) ?_ hMP
    rintro ⟨k, i⟩ ⟨u, hu⟩
    obtain rfl : k₀ = k := hu
    exact ⟨⟨(), i⟩, rfl⟩
  have hHor' : Geo.IsHorizontal (ι := blockIdx fun _ : Unit ↦ n k₀)
      ((Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀))) := by
    refine (Ideal.ext fun a ↦ ?_).trans hHor
    simp only [Ideal.mem_comap]
    rw [rename_C]
  refine ⟨inferInstance, hMP', hHor', ?_⟩

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hMP.2.2 k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    rw [Geo.mCoordIdeal, RingHom.mem_ker]
    simp [Geo.mConeMap, h0]
  rw [comap_mCoordIdeal y k₀] at hHor' hMP' ⊢
  have := hMP.1
  have := hMP'.1
  have dimA := hDim _ (algebraMap_injective _ hHor)
  have dimA' := hDim _ (algebraMap_injective _ hHor')
  rw [hTr ι (blockIdx n) Ω y (birational_of_block y k₀ hB) hrel hHor] at dimA
  rw [hTr Unit (blockIdx fun _ : Unit ↦ n k₀) Ω _ hB (fun _ ↦ hrel k₀) hHor'] at dimA'
  rw [hKd] at dimA
  have h1 : ((D + 1 + Fintype.card ι : ℕ) : ℕ∞) =
      (Algebra.trdeg ℤ Ω + Fintype.card ι).toENat + 1 := by exact_mod_cast dimA
  simp only [map_add, map_natCast] at h1
  have key : (Algebra.trdeg ℤ Ω).toENat = D := by
    generalize (Algebra.trdeg ℤ Ω).toENat = t at h1 ⊢
    induction t using ENat.recTopCoe with
    | top => simp at h1
    | coe m =>
      norm_cast at h1 ⊢
      omega
  rw [dimA']
  simp only [map_add, map_natCast, Fintype.card_unit, key]
  norm_cast

end

end GroundTheory.Heights₂.Heights
