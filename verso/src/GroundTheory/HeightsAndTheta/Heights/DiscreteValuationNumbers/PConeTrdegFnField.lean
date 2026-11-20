import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsConeTrdegFnField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcMap mcIdeal fnField)

noncomputable section

/- English proof (translation)
Set `_ : Algebra S T` to `(Subalgebra.inclusion hST).toRingHom.toAlgebra`. Establish `_ : IsScalarTower O S T` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `_ : FaithfulSMul O S` using `(faithfulSMul_iff_algebraMap_injective O S).2 fun a b h => hinj (congrArg Subtype.val h)`. Establish `_ : FaithfulSMul S T` using `(faithfulSMul_iff_algebraMap_injective S T).2 (Subalgebra.inclusion_injective hST)`. Set `f : T →ₐ[S] B` to `{ T.val.toRingHom with commutes' := fun _ => rfl }`.

Establish `_ : Algebra.IsAlgebraic S T` using `⟨fun t => (isAlgebraic_algHom_iff f Subtype.val_injective).1 (halg t t.2)⟩`. Establish `h` using `trdeg_add_eq O S (A := T)`. Rewrite `h` using `[trdeg_eq_zero (R := S) (A := T), add_zero]`. Conclude with `h`.
-/
theorem ConeTrdegFnField.trdeg_eq_of_le_of_isAlgebraic {O B : Type} [CommRing O] [IsDomain O] [CommRing B]
    [IsDomain B] [Algebra O B] (hinj : Function.Injective (algebraMap O B)) {S T : Subalgebra O B}
    (hST : S ≤ T) (halg : ∀ t ∈ T, IsAlgebraic S t) : Algebra.trdeg O S = Algebra.trdeg O T := by
  let _ : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  have _ : IsScalarTower O S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : FaithfulSMul O S :=
    (faithfulSMul_iff_algebraMap_injective O S).2 fun a b h => hinj (congrArg Subtype.val h)
  have _ : FaithfulSMul S T :=
    (faithfulSMul_iff_algebraMap_injective S T).2 (Subalgebra.inclusion_injective hST)
  let f : T →ₐ[S] B := { T.val.toRingHom with commutes' := fun _ => rfl }
  have _ : Algebra.IsAlgebraic S T :=
    ⟨fun t => (isAlgebraic_algHom_iff f Subtype.val_injective).1 (halg t t.2)⟩
  have h := trdeg_add_eq O S (A := T)
  rw [trdeg_eq_zero (R := S) (A := T), add_zero] at h
  exact h

section Cone

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

/- English proof (translation)
Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)`. Consider the case `add x z _ _ hx hz => exact add_mem hx hz`. Consider the case `mul x z _ _ hx hz => exact mul_mem hx hz`.
-/
theorem ConeTrdegFnField.mem_fnField_of_mem_adjoin (y : (Σ k, ι k) → Ω) {a : Ω}
    (ha : a ∈ Algebra.adjoin O (fnField O y : Set Ω)) : a ∈ fnField O y := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hx
  | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

def ConeTrdegFnField.coneMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    MvPolynomial K (Algebra.adjoin O (fnField O y : Set Ω)) →ₐ[O] MvPolynomial K Ω :=
  ((aeval fun k => C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω).restrictScalars O).comp
    (MvPolynomial.mapAlgHom (Algebra.adjoin O (fnField O y : Set Ω)).val)

/- English proof (translation)
Simplify using `[ConeTrdegFnField.coneMap]`.
-/
theorem ConeTrdegFnField.coneMap_C (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (a : Algebra.adjoin O (fnField O y : Set Ω)) :
    ConeTrdegFnField.coneMap y c (C a) = C (a : Ω) := by
  simp [ConeTrdegFnField.coneMap]

/- English proof (translation)
Simplify using `[ConeTrdegFnField.coneMap]`.
-/
theorem ConeTrdegFnField.coneMap_X (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K) :
    ConeTrdegFnField.coneMap (O := O) y c (X k) = C (y ⟨k, c k⟩) * X k := by
  simp [ConeTrdegFnField.coneMap]

/- English proof (translation)
Simplify using `[mcMap]`.
-/
theorem ConeTrdegFnField.mcMap_X (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) :
    mcMap O y (X p) = C (y p) * X p.1 := by
  simp [mcMap]

/- English proof (translation)
Set `ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω` to `aeval fun k => C (y ⟨k, c k⟩) * X k`. Set `ψ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω` to `aeval fun k => C (y ⟨k, c k⟩)⁻¹ * X k`. Establish `hinv : ψ'.comp ψ = AlgHom.id Ω _`. Use `MvPolynomial.algHom_ext fun k => ?_` and prove the remaining obligations. Simplify using `only [ψ, ψ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply, MvPolynomial.algebraMap_eq]`.

Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc k), map_one, one_mul]`. Establish `hψ : Function.Injective ψ` using `Function.LeftInverse.injective (g := ψ') fun p => by`. Rewrite using `[← AlgHom.comp_apply, hinv, AlgHom.id_apply]`. Conclude with `hψ.comp (MvPolynomial.map_injective _ Subtype.val_injective)`.
-/
theorem ConeTrdegFnField.coneMap_injective (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Function.Injective (ConeTrdegFnField.coneMap (O := O) y c) := by
  let ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩) * X k
  let ψ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩)⁻¹ * X k
  have hinv : ψ'.comp ψ = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [ψ, ψ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc k), map_one, one_mul]
  have hψ : Function.Injective ψ := Function.LeftInverse.injective (g := ψ') fun p => by
    rw [← AlgHom.comp_apply, hinv, AlgHom.id_apply]
  exact hψ.comp (MvPolynomial.map_injective _ Subtype.val_injective)

end Cone

/- English proof (translation)
Introduce `O _ _ Ω _ _ hinj K _ ι _ y hy`. Use `choose c hc using hy`. Use `set F₀ := Algebra.adjoin O (fnField O y : Set Ω)`. Establish `hF : ∀ w ∈ fnField O y, w ∈ F₀` using `fun w hw => Algebra.subset_adjoin hw`. Establish `hu : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ F₀` using `fun p => hF _ (Subfield.subset_closure (Or.inr ⟨⟨p.1, (p.2, c p.1)⟩, rfl⟩))`.

Set `ρ : MRingOver O ι →ₐ[O] MvPolynomial K F₀` to `aeval fun p => C (⟨_, hu p⟩ : F₀) * X p.1`. Establish `hfac : mcMap O y = (ConeTrdegFnField.coneMap (O` using `O) y c).comp ρ := by`. Use `MvPolynomial.algHom_ext fun p => ?_` and prove the remaining obligations. Rewrite using `[ConeTrdegFnField.mcMap_X, AlgHom.comp_apply, aeval_X, map_mul, ConeTrdegFnField.coneMap_C, ConeTrdegFnField.coneMap_X, ← mul_assoc, ← map_mul]`. Simplify using `only [div_mul_cancel₀ _ (hc p.1)]`.

Use `set R := (mcMap O y).range`. Establish `hle : R ≤ (ConeTrdegFnField.coneMap (O` using `O) y c).range := by show (mcMap O y).range ≤ _`. Rewrite using `[hfac]`. Conclude with `AlgHom.range_comp_le_range _ _`. Establish `hXR : ∀ p : Σ k, ι k, (C (y p) * X p.1 : MvPolynomial K Ω) ∈ R` using `fun p => ⟨X p, ConeTrdegFnField.mcMap_X y p⟩`.

Establish `halgC : ∀ w ∈ fnField O y, IsAlgebraic R (C w : MvPolynomial K Ω)`. Introduce `w hw`. Proceed by induction on `hw using Subfield.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨r, rfl⟩ | ⟨q, rfl⟩` into its components or cases.

Establish `e : (C (algebraMap O Ω r) : MvPolynomial K Ω) = algebraMap O (MvPolynomial K Ω) r`. Rewrite using `[MvPolynomial.algebraMap_apply]`. Rewrite using `[e]`. Conclude with `isAlgebraic_algebraMap (⟨_, R.algebraMap_mem r⟩ : R)`. Simplify using `only`.

Distinguish the cases in `h0 : y ⟨q.1, q.2.2⟩ = 0`. Rewrite using `[h0, div_zero, map_zero]`. Conclude with `isAlgebraic_zero`. Use `IsAlgebraic.of_mul (y := C (y ⟨q.1, q.2.2⟩) * X q.1) (mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (C_ne_zero.2 h0) (X_ne_zero _))) (isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.2⟩⟩ : R)) ?_` and prove the remaining obligations. Establish `e : (C (y ⟨q.1, q.2.2⟩) * X q.1 : MvPolynomial K Ω) * C (y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) = C (y ⟨q.1, q.2.1⟩) * X q.1`.

Rewrite using `[mul_comm, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ h0]`. Rewrite using `[e]`. Conclude with `isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.1⟩⟩ : R)`. Consider the case `one => rw [map_one]`. Conclude with `isAlgebraic_one`.

Consider the case `add x z _ _ hx hz => rw [map_add]`. Conclude with `hx.add hz`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `hx.neg`. Consider the case `inv x _ hx`.

Distinguish the cases in `h0 : x = 0`. Rewrite using `[h0, inv_zero, map_zero]`. Conclude with `isAlgebraic_zero`. Use `IsAlgebraic.of_mul (y := C x) (mem_nonZeroDivisors_of_ne_zero (C_ne_zero.2 h0)) hx ?_` and prove the remaining obligations. Rewrite using `[← map_mul, mul_inv_cancel₀ h0, map_one]`.

Conclude with `isAlgebraic_one`. Consider the case `mul x z _ _ hx hz => rw [map_mul]`. Conclude with `hx.mul hz`. Establish `halg : ∀ t ∈ (ConeTrdegFnField.coneMap (O` using `O) y c).range, IsAlgebraic R t := by`. Introduce and unpack `_ ⟨q, rfl⟩`.

Express the relevant statement in the definitionally equal form `IsAlgebraic R (ConeTrdegFnField.coneMap (O := O) y c q)`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[ConeTrdegFnField.coneMap_C]`. Conclude with `halgC a (ConeTrdegFnField.mem_fnField_of_mem_adjoin y a.2)`.

Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p k hp`. Rewrite using `[map_mul, ConeTrdegFnField.coneMap_X]`. Conclude with `hp.mul (isAlgebraic_algebraMap (⟨_, hXR ⟨k, c k⟩⟩ : R))`.

Establish `hinjP : Function.Injective (algebraMap O (MvPolynomial K Ω))`. Rewrite using `[IsScalarTower.algebraMap_eq O Ω (MvPolynomial K Ω)]`. Conclude with `(C_injective K Ω).comp hinj`. Establish `h1 : Algebra.trdeg O (MRingOver O ι ⧸ mcIdeal O y) = Algebra.trdeg O R` using `(Ideal.quotientKerEquivRange (mcMap O y)).trdeg_eq`. Establish `h2 : Algebra.trdeg O (ConeTrdegFnField.coneMap (O` using `O) y c).range = Algebra.trdeg O (MvPolynomial K F₀) := (AlgEquiv.ofInjective (ConeTrdegFnField.coneMap (O := O) y c) (ConeTrdegFnField.coneMap_injective y c hc)).trdeg_eq.symm`.

Establish `_ : FaithfulSMul O F₀` using `(faithfulSMul_iff_algebraMap_injective O F₀).2 fun a b h => hinj (congrArg Subtype.val h)`. Establish `_ : FaithfulSMul F₀ (MvPolynomial K F₀)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (C_injective K _)`. Establish `h3 : Algebra.trdeg O (MvPolynomial K F₀) = Algebra.trdeg O F₀ + Fintype.card K`. Rewrite using `[← trdeg_add_eq O F₀ (A := MvPolynomial K F₀), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]`. Rewrite using `[h1, ConeTrdegFnField.trdeg_eq_of_le_of_isAlgebraic hinjP hle halg, h2, h3]`.
-/
theorem ConeTrdegFnField.proof : ConeTrdegFnField.Statement := by
  intro O _ _ Ω _ _ hinj K _ ι _ y hy
  choose c hc using hy
  set F₀ := Algebra.adjoin O (fnField O y : Set Ω)
  have hF : ∀ w ∈ fnField O y, w ∈ F₀ := fun w hw => Algebra.subset_adjoin hw
  have hu : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ F₀ := fun p =>
    hF _ (Subfield.subset_closure (Or.inr ⟨⟨p.1, (p.2, c p.1)⟩, rfl⟩))

  let ρ : MRingOver O ι →ₐ[O] MvPolynomial K F₀ := aeval fun p => C (⟨_, hu p⟩ : F₀) * X p.1
  have hfac : mcMap O y = (ConeTrdegFnField.coneMap (O := O) y c).comp ρ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    rw [ConeTrdegFnField.mcMap_X, AlgHom.comp_apply, aeval_X, map_mul, ConeTrdegFnField.coneMap_C,
      ConeTrdegFnField.coneMap_X, ← mul_assoc, ← map_mul]
    simp only [div_mul_cancel₀ _ (hc p.1)]
  set R := (mcMap O y).range
  have hle : R ≤ (ConeTrdegFnField.coneMap (O := O) y c).range := by
    show (mcMap O y).range ≤ _
    rw [hfac]; exact AlgHom.range_comp_le_range _ _
  have hXR : ∀ p : Σ k, ι k, (C (y p) * X p.1 : MvPolynomial K Ω) ∈ R := fun p =>
    ⟨X p, ConeTrdegFnField.mcMap_X y p⟩

  have halgC : ∀ w ∈ fnField O y, IsAlgebraic R (C w : MvPolynomial K Ω) := by
    intro w hw
    induction hw using Subfield.closure_induction with
    | mem x hx =>
      rcases hx with ⟨r, rfl⟩ | ⟨q, rfl⟩
      · have e : (C (algebraMap O Ω r) : MvPolynomial K Ω) = algebraMap O (MvPolynomial K Ω) r := by
          rw [MvPolynomial.algebraMap_apply]
        rw [e]
        exact isAlgebraic_algebraMap (⟨_, R.algebraMap_mem r⟩ : R)
      · dsimp only
        by_cases h0 : y ⟨q.1, q.2.2⟩ = 0
        · rw [h0, div_zero, map_zero]; exact isAlgebraic_zero
        · refine IsAlgebraic.of_mul (y := C (y ⟨q.1, q.2.2⟩) * X q.1)
            (mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (C_ne_zero.2 h0) (X_ne_zero _)))
            (isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.2⟩⟩ : R)) ?_
          have e : (C (y ⟨q.1, q.2.2⟩) * X q.1 : MvPolynomial K Ω) * C (y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) =
              C (y ⟨q.1, q.2.1⟩) * X q.1 := by
            rw [mul_comm, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ h0]
          rw [e]
          exact isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.1⟩⟩ : R)
    | one => rw [map_one]; exact isAlgebraic_one
    | add x z _ _ hx hz => rw [map_add]; exact hx.add hz
    | neg x _ hx => rw [map_neg]; exact hx.neg
    | inv x _ hx =>
      by_cases h0 : x = 0
      · rw [h0, inv_zero, map_zero]; exact isAlgebraic_zero
      · refine IsAlgebraic.of_mul (y := C x) (mem_nonZeroDivisors_of_ne_zero (C_ne_zero.2 h0)) hx ?_
        rw [← map_mul, mul_inv_cancel₀ h0, map_one]; exact isAlgebraic_one
    | mul x z _ _ hx hz => rw [map_mul]; exact hx.mul hz
  have halg : ∀ t ∈ (ConeTrdegFnField.coneMap (O := O) y c).range, IsAlgebraic R t := by
    rintro _ ⟨q, rfl⟩
    change IsAlgebraic R (ConeTrdegFnField.coneMap (O := O) y c q)
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [ConeTrdegFnField.coneMap_C]
      exact halgC a (ConeTrdegFnField.mem_fnField_of_mem_adjoin y a.2)
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p k hp =>
      rw [map_mul, ConeTrdegFnField.coneMap_X]
      exact hp.mul (isAlgebraic_algebraMap (⟨_, hXR ⟨k, c k⟩⟩ : R))
  have hinjP : Function.Injective (algebraMap O (MvPolynomial K Ω)) := by
    rw [IsScalarTower.algebraMap_eq O Ω (MvPolynomial K Ω)]
    exact (C_injective K Ω).comp hinj
  have h1 : Algebra.trdeg O (MRingOver O ι ⧸ mcIdeal O y) = Algebra.trdeg O R :=
    (Ideal.quotientKerEquivRange (mcMap O y)).trdeg_eq
  have h2 : Algebra.trdeg O (ConeTrdegFnField.coneMap (O := O) y c).range = Algebra.trdeg O (MvPolynomial K F₀) :=
    (AlgEquiv.ofInjective (ConeTrdegFnField.coneMap (O := O) y c)
      (ConeTrdegFnField.coneMap_injective y c hc)).trdeg_eq.symm
  have _ : FaithfulSMul O F₀ :=
    (faithfulSMul_iff_algebraMap_injective O F₀).2 fun a b h => hinj (congrArg Subtype.val h)
  have _ : FaithfulSMul F₀ (MvPolynomial K F₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (C_injective K _)
  have h3 : Algebra.trdeg O (MvPolynomial K F₀) = Algebra.trdeg O F₀ + Fintype.card K := by
    rw [← trdeg_add_eq O F₀ (A := MvPolynomial K F₀), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype]
  rw [h1, ConeTrdegFnField.trdeg_eq_of_le_of_isAlgebraic hinjP hle halg, h2, h3]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
