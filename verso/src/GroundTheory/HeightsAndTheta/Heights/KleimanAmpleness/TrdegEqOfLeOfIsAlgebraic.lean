import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)

section Trdeg

variable {F : Type} [Field F] {B : Type} [CommRing B] [IsDomain B] [Algebra F B]

/- English proof (translation)
Set `_ : Algebra S T` to `(Subalgebra.inclusion hST).toRingHom.toAlgebra`. Establish `_ : IsScalarTower F S T` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `_ : FaithfulSMul F S` using `(faithfulSMul_iff_algebraMap_injective F S).2 (algebraMap F S).injective`. Establish `_ : FaithfulSMul S T` using `(faithfulSMul_iff_algebraMap_injective S T).2 (Subalgebra.inclusion_injective hST)`. Set `f : T →ₐ[S] B` to `{ T.val.toRingHom with commutes' := fun _ => rfl }`.

Establish `_ : Algebra.IsAlgebraic S T` using `⟨fun t => (isAlgebraic_algHom_iff f Subtype.val_injective).1 (halg t t.2)⟩`. Establish `h` using `trdeg_add_eq F S (A := T)`. Rewrite `h` using `[trdeg_eq_zero (R := S) (A := T), add_zero]`. Conclude with `h`.
-/
theorem trdeg_eq_of_le_of_isAlgebraic {S T : Subalgebra F B} (hST : S ≤ T)
    (halg : ∀ t ∈ T, IsAlgebraic S t) : Algebra.trdeg F S = Algebra.trdeg F T := by
  let _ : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  have _ : IsScalarTower F S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : FaithfulSMul F S :=
    (faithfulSMul_iff_algebraMap_injective F S).2 (algebraMap F S).injective
  have _ : FaithfulSMul S T :=
    (faithfulSMul_iff_algebraMap_injective S T).2 (Subalgebra.inclusion_injective hST)
  let f : T →ₐ[S] B := { T.val.toRingHom with commutes' := fun _ => rfl }
  have _ : Algebra.IsAlgebraic S T :=
    ⟨fun t => (isAlgebraic_algHom_iff f Subtype.val_injective).1 (halg t t.2)⟩
  have h := trdeg_add_eq F S (A := T)
  rw [trdeg_eq_zero (R := S) (A := T), add_zero] at h
  exact h

/- English proof (translation)
Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hs x hx`. Consider the case `algebraMap r => exact isAlgebraic_algebraMap (⟨algebraMap F B r, S.algebraMap_mem r⟩ : S)`. Consider the case `add x y _ _ hx hy => exact hx.add hy`. Consider the case `mul x y _ _ hx hy => exact hx.mul hy`.
-/
theorem isAlgebraic_of_mem_adjoin (S : Subalgebra F B) {s : Set B} (hs : ∀ b ∈ s, IsAlgebraic S b)
    {b : B} (hb : b ∈ Algebra.adjoin F s) : IsAlgebraic S b := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap r => exact isAlgebraic_algebraMap (⟨algebraMap F B r, S.algebraMap_mem r⟩ : S)
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

/- English proof (translation)
Establish `hS : ∀ b ∈ S ⊔ T, IsAlgebraic S b` using `fun b hb => isAlgebraic_of_mem_adjoin S (fun b (hb : b ∈ (S : Set B) ∪ T) => Or.elim hb (fun h => isAlgebraic_algebraMap (⟨b, h⟩ : S)) (h₁ b)) (by rwa [Algebra.sup_def] at hb)`. Establish `hT : ∀ b ∈ S ⊔ T, IsAlgebraic T b` using `fun b hb => isAlgebraic_of_mem_adjoin T (fun b (hb : b ∈ (S : Set B) ∪ T) => Or.elim hb (h₂ b) (fun h => isAlgebraic_algebraMap (⟨b, h⟩ : T))) (by rwa [Algebra.sup_def] at hb)`. Rewrite using `[trdeg_eq_of_le_of_isAlgebraic le_sup_left hS, trdeg_eq_of_le_of_isAlgebraic le_sup_right hT]`.
-/
theorem trdeg_eq_of_isAlgebraic_both {S T : Subalgebra F B} (h₁ : ∀ t ∈ T, IsAlgebraic S t)
    (h₂ : ∀ s ∈ S, IsAlgebraic T s) : Algebra.trdeg F S = Algebra.trdeg F T := by
  have hS : ∀ b ∈ S ⊔ T, IsAlgebraic S b := fun b hb =>
    isAlgebraic_of_mem_adjoin S (fun b (hb : b ∈ (S : Set B) ∪ T) =>
      Or.elim hb (fun h => isAlgebraic_algebraMap (⟨b, h⟩ : S)) (h₁ b))
      (by rwa [Algebra.sup_def] at hb)
  have hT : ∀ b ∈ S ⊔ T, IsAlgebraic T b := fun b hb =>
    isAlgebraic_of_mem_adjoin T (fun b (hb : b ∈ (S : Set B) ∪ T) =>
      Or.elim hb (h₂ b) (fun h => isAlgebraic_algebraMap (⟨b, h⟩ : T)))
      (by rwa [Algebra.sup_def] at hb)
  rw [trdeg_eq_of_le_of_isAlgebraic le_sup_left hS, trdeg_eq_of_le_of_isAlgebraic le_sup_right hT]

end Trdeg

section LocalRings

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.Kleiman2.locIn at hu`. Proceed by induction on `hu using Subring.closure_induction with`. Consider the case `mem u hu`. Take `⟨a, b, hb, rfl⟩` from `hu`. Establish `hb0 : (b : Ω) ≠ 0` using `fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact p.zero_mem)`.

Use `IsAlgebraic.of_mul (y := (b : Ω)) (mem_nonZeroDivisors_of_ne_zero hb0) (isAlgebraic_algebraMap b) ?_` and prove the remaining obligations. Establish `e : (b : Ω) * ((a : Ω) / b) = algebraMap A Ω a`. Rewrite using `[mul_div_cancel₀ _ hb0]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `isAlgebraic_algebraMap a`. Consider the case `zero => exact isAlgebraic_zero`. Consider the case `one => exact isAlgebraic_one`. Consider the case `add x y _ _ hx hy => exact hx.add hy`. Consider the case `neg x _ hx => exact hx.neg`.

Consider the case `mul x y _ _ hx hy => exact hx.mul hy`.
-/
theorem isAlgebraic_of_mem_locIn (A : Subalgebra F Ω) (p : Ideal A) [p.IsPrime] {u : Ω}
    (hu : u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : IsAlgebraic A u := by
  unfold IndefiniteRowSideFullHecke.Kleiman2.locIn at hu
  induction hu using Subring.closure_induction with
  | mem u hu =>
    obtain ⟨a, b, hb, rfl⟩ := hu
    have hb0 : (b : Ω) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact p.zero_mem)
    refine IsAlgebraic.of_mul (y := (b : Ω)) (mem_nonZeroDivisors_of_ne_zero hb0)
      (isAlgebraic_algebraMap b) ?_
    have e : (b : Ω) * ((a : Ω) / b) = algebraMap A Ω a := by
      rw [mul_div_cancel₀ _ hb0]; rfl
    rw [e]
    exact isAlgebraic_algebraMap a
  | zero => exact isAlgebraic_zero
  | one => exact isAlgebraic_one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | mul x y _ _ hx hy => exact hx.mul hy

/- English proof (translation)
The claim follows from `Subring.subset_closure ⟨⟨a, ha⟩, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).2 h), by simp⟩`.
-/
theorem le_locIn (A : Subalgebra F Ω) (p : Ideal A) [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  Subring.subset_closure ⟨⟨a, ha⟩, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).2 h), by simp⟩

/- English proof (translation)
Establish `hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y c) ⊥ ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F y` using `⟨c, hc, ⊥, Ideal.isPrime_bot, rfl⟩`. Unfold `IndefiniteRowSideFullHecke.Kleiman2.SameModel at h`. Rewrite `hz` using `[h]`. Take `⟨c', hc', p', hp', hzeq⟩` from `hz`. Use `⟨c', hc', trdeg_eq_of_isAlgebraic_both (fun t ht => ?_) (fun s hs => ?_)⟩` and prove the remaining obligations.

Establish `ht' : t ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y c) ⊥`. Rewrite using `[hzeq]`. Conclude with `le_locIn _ p' ht`. Conclude with `isAlgebraic_of_mem_locIn _ ⊥ ht'`. Establish `hs' : s ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y' c') p'`.

Rewrite using `[← hzeq]`. Conclude with `le_locIn _ ⊥ hs`. Conclude with `isAlgebraic_of_mem_locIn _ p' hs'`.
-/
theorem exists_trdeg_chartRing_eq {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (h : IndefiniteRowSideFullHecke.Kleiman2.SameModel F y y') (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ c' : ∀ k, ι' k, (∀ k, y' ⟨k, c' k⟩ ≠ 0) ∧
      Algebra.trdeg F (chartRingOver F y c) = Algebra.trdeg F (chartRingOver F y' c') := by
  have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y c) ⊥ ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F y :=
    ⟨c, hc, ⊥, Ideal.isPrime_bot, rfl⟩
  unfold IndefiniteRowSideFullHecke.Kleiman2.SameModel at h
  rw [h] at hz
  obtain ⟨c', hc', p', hp', hzeq⟩ := hz
  refine ⟨c', hc', trdeg_eq_of_isAlgebraic_both (fun t ht => ?_) (fun s hs => ?_)⟩
  · have ht' : t ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y c) ⊥ := by
      rw [hzeq]; exact le_locIn _ p' ht
    exact isAlgebraic_of_mem_locIn _ ⊥ ht'
  · have hs' : s ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y' c') p' := by
      rw [← hzeq]; exact le_locIn _ ⊥ hs
    exact isAlgebraic_of_mem_locIn _ p' hs'

end LocalRings

section Cone

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
variable {K : Type} {ι : K → Type}

def chartConeMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    MvPolynomial K (chartRingOver F y c) →ₐ[F] MvPolynomial K Ω :=
  ((aeval fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω).restrictScalars
    F).comp (MvPolynomial.mapAlgHom (chartRingOver F y c).val)

/- English proof (translation)
Simplify using `[chartConeMap]`.
-/
theorem chartConeMap_C (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : chartRingOver F y c) :
    chartConeMap y c (MvPolynomial.C a) = MvPolynomial.C (a : Ω) := by
  simp [chartConeMap]

/- English proof (translation)
Simplify using `[chartConeMap]`.
-/
theorem chartConeMap_X (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K) :
    chartConeMap (F := F) y c (X k) = MvPolynomial.C (y ⟨k, c k⟩) * X k := by
  simp [chartConeMap]

/- English proof (translation)
Simplify using `[mConeMapOver]`.
-/
theorem mConeMapOver_X (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) :
    mConeMapOver F y (X p) = MvPolynomial.C (y p) * X p.1 := by
  simp [mConeMapOver]

/- English proof (translation)
Set `ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω` to `aeval fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k`. Set `ψ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω` to `aeval fun k => MvPolynomial.C (y ⟨k, c k⟩)⁻¹ * X k`. Establish `hinv : ψ'.comp ψ = AlgHom.id Ω _`. Use `MvPolynomial.algHom_ext fun k => ?_` and prove the remaining obligations. Simplify using `only [ψ, ψ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply, MvPolynomial.algebraMap_eq]`.

Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc k), map_one, one_mul]`. Establish `hψ : Function.Injective ψ` using `Function.LeftInverse.injective (g := ψ') fun p => by`. Rewrite using `[← AlgHom.comp_apply, hinv, AlgHom.id_apply]`. Conclude with `hψ.comp (MvPolynomial.map_injective _ Subtype.val_injective)`.
-/
theorem chartConeMap_injective (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Function.Injective (chartConeMap (F := F) y c) := by
  let ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k
  let ψ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => MvPolynomial.C (y ⟨k, c k⟩)⁻¹ * X k
  have hinv : ψ'.comp ψ = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [ψ, ψ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc k), map_one, one_mul]
  have hψ : Function.Injective ψ := Function.LeftInverse.injective (g := ψ') fun p => by
    rw [← AlgHom.comp_apply, hinv, AlgHom.id_apply]
  exact hψ.comp (MvPolynomial.map_injective _ Subtype.val_injective)

/- English proof (translation)
Establish `hu : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ chartRingOver F y c` using `fun p => Algebra.subset_adjoin ⟨p, rfl⟩`. Set `ρ : MvPolynomial (Σ k, ι k) F →ₐ[F] MvPolynomial K (chartRingOver F y c)` to `aeval fun p => MvPolynomial.C (⟨_, hu p⟩ : (chartRingOver F y c)) * X p.1`. Establish `hfac : mConeMapOver F y = (chartConeMap (F` using `F) y c).comp ρ := by`. Use `MvPolynomial.algHom_ext fun p => ?_` and prove the remaining obligations. Rewrite using `[mConeMapOver_X, AlgHom.comp_apply]`.

Rewrite using `[aeval_X, map_mul, chartConeMap_C, chartConeMap_X, ← mul_assoc, ← map_mul]`. Simplify using `only [div_mul_cancel₀ _ (hc p.1)]`. Use `set R := (mConeMapOver F y).range`. Establish `hle : R ≤ (chartConeMap (F` using `F) y c).range := by show (mConeMapOver F y).range ≤ _`. Rewrite using `[hfac]`.

Conclude with `AlgHom.range_comp_le_range _ _`. Establish `hUR : ∀ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ∈ R` using `fun k => ⟨X ⟨k, c k⟩, mConeMapOver_X y _⟩`. Establish `hU0 : ∀ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ≠ 0` using `fun k => mul_ne_zero (MvPolynomial.C_ne_zero.2 (hc k)) (MvPolynomial.X_ne_zero k)`. Establish `halgC : ∀ w ∈ (chartRingOver F y c), IsAlgebraic R (MvPolynomial.C w : MvPolynomial K Ω)`. Introduce `w hw`.

Proceed by induction on `hw using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Use `IsAlgebraic.of_mul (y := MvPolynomial.C (y ⟨p.1, c p.1⟩) * X p.1) (mem_nonZeroDivisors_of_ne_zero (hU0 p.1)) (isAlgebraic_algebraMap (⟨_, hUR p.1⟩ : R)) ?_` and prove the remaining obligations. Establish `e : (MvPolynomial.C (y ⟨p.1, c p.1⟩) * X p.1 : MvPolynomial K Ω) * MvPolynomial.C (y p / y ⟨p.1, c p.1⟩) = mConeMapOver F y (X p)`.

Rewrite using `[mConeMapOver_X, mul_comm, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (hc p.1)]`. Rewrite using `[e]`. Conclude with `isAlgebraic_algebraMap (⟨_, AlgHom.mem_range_self _ _⟩ : R)`. Consider the case `algebraMap r`. Conclude with `isAlgebraic_algebraMap (⟨algebraMap F _ r, R.algebraMap_mem r⟩ : R)`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `hx.add hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `hx.mul hy`. Establish `halg : ∀ t ∈ (chartConeMap (F` using `F) y c).range, IsAlgebraic R t := by`.

Introduce and unpack `_ ⟨q, rfl⟩`. Express the relevant statement in the definitionally equal form `IsAlgebraic R (chartConeMap (F := F) y c q)`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => rw [chartConeMap_C]`. Conclude with `halgC a a.2`.

Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p k hp`. Rewrite using `[map_mul, chartConeMap_X]`. Conclude with `hp.mul (isAlgebraic_algebraMap (⟨_, hUR k⟩ : R))`.

Establish `h1 : Algebra.trdeg F (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) = Algebra.trdeg F R` using `(Ideal.quotientKerEquivRange (mConeMapOver F y)).trdeg_eq`. Establish `h2 : Algebra.trdeg F (chartConeMap (F` using `F) y c).range = Algebra.trdeg F (MvPolynomial K (chartRingOver F y c)) := (AlgEquiv.ofInjective (chartConeMap (F := F) y c) (chartConeMap_injective y c hc)).trdeg_eq.symm`. Establish `_ : FaithfulSMul F (chartRingOver F y c)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F (chartRingOver F y c)).injective`. Establish `_ : FaithfulSMul (chartRingOver F y c) (MvPolynomial K (chartRingOver F y c))` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective K _)`. Establish `h3 : Algebra.trdeg F (MvPolynomial K (chartRingOver F y c)) = Algebra.trdeg F (chartRingOver F y c) + Fintype.card K`.

Rewrite using `[← trdeg_add_eq F (chartRingOver F y c) (A := MvPolynomial K (chartRingOver F y c)), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]`. Rewrite using `[h1, trdeg_eq_of_le_of_isAlgebraic hle halg, h2, h3]`.
-/
theorem trdeg_quotient_mIdealOver [Fintype K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Algebra.trdeg F (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) =
      Algebra.trdeg F (chartRingOver F y c) + Fintype.card K := by
  have hu : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ chartRingOver F y c := fun p =>
    Algebra.subset_adjoin ⟨p, rfl⟩

  let ρ : MvPolynomial (Σ k, ι k) F →ₐ[F] MvPolynomial K (chartRingOver F y c) :=
    aeval fun p => MvPolynomial.C (⟨_, hu p⟩ : (chartRingOver F y c)) * X p.1
  have hfac : mConeMapOver F y = (chartConeMap (F := F) y c).comp ρ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    rw [mConeMapOver_X, AlgHom.comp_apply]
    rw [aeval_X, map_mul, chartConeMap_C, chartConeMap_X, ← mul_assoc, ← map_mul]
    simp only [div_mul_cancel₀ _ (hc p.1)]
  set R := (mConeMapOver F y).range
  have hle : R ≤ (chartConeMap (F := F) y c).range := by
    show (mConeMapOver F y).range ≤ _
    rw [hfac]; exact AlgHom.range_comp_le_range _ _
  have hUR : ∀ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ∈ R := fun k =>
    ⟨X ⟨k, c k⟩, mConeMapOver_X y _⟩
  have hU0 : ∀ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ≠ 0 := fun k =>
    mul_ne_zero (MvPolynomial.C_ne_zero.2 (hc k)) (MvPolynomial.X_ne_zero k)

  have halgC : ∀ w ∈ (chartRingOver F y c), IsAlgebraic R (MvPolynomial.C w : MvPolynomial K Ω) := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      refine IsAlgebraic.of_mul (y := MvPolynomial.C (y ⟨p.1, c p.1⟩) * X p.1)
        (mem_nonZeroDivisors_of_ne_zero (hU0 p.1)) (isAlgebraic_algebraMap (⟨_, hUR p.1⟩ : R)) ?_
      have e : (MvPolynomial.C (y ⟨p.1, c p.1⟩) * X p.1 : MvPolynomial K Ω) *
          MvPolynomial.C (y p / y ⟨p.1, c p.1⟩) = mConeMapOver F y (X p) := by
        rw [mConeMapOver_X, mul_comm, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (hc p.1)]
      rw [e]
      exact isAlgebraic_algebraMap (⟨_, AlgHom.mem_range_self _ _⟩ : R)
    | algebraMap r =>
      exact isAlgebraic_algebraMap (⟨algebraMap F _ r, R.algebraMap_mem r⟩ : R)
    | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy
  have halg : ∀ t ∈ (chartConeMap (F := F) y c).range, IsAlgebraic R t := by
    rintro _ ⟨q, rfl⟩
    change IsAlgebraic R (chartConeMap (F := F) y c q)
    induction q using MvPolynomial.induction_on with
    | C a => rw [chartConeMap_C]; exact halgC a a.2
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p k hp =>
      rw [map_mul, chartConeMap_X]
      exact hp.mul (isAlgebraic_algebraMap (⟨_, hUR k⟩ : R))
  have h1 : Algebra.trdeg F (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) = Algebra.trdeg F R :=
    (Ideal.quotientKerEquivRange (mConeMapOver F y)).trdeg_eq
  have h2 : Algebra.trdeg F (chartConeMap (F := F) y c).range =
      Algebra.trdeg F (MvPolynomial K (chartRingOver F y c)) :=
    (AlgEquiv.ofInjective (chartConeMap (F := F) y c) (chartConeMap_injective y c hc)).trdeg_eq.symm
  have _ : FaithfulSMul F (chartRingOver F y c) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F (chartRingOver F y c)).injective
  have _ : FaithfulSMul (chartRingOver F y c) (MvPolynomial K (chartRingOver F y c)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective K _)
  have h3 : Algebra.trdeg F (MvPolynomial K (chartRingOver F y c)) =
      Algebra.trdeg F (chartRingOver F y c) + Fintype.card K := by
    rw [← trdeg_add_eq F (chartRingOver F y c) (A := MvPolynomial K (chartRingOver F y c)),
      MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
  rw [h1, trdeg_eq_of_le_of_isAlgebraic hle halg, h2, h3]

end Cone

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
