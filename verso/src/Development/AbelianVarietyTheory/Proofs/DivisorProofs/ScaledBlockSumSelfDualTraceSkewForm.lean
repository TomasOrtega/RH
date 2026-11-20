import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SkewLat.DualPair

variable {D : D7}

def hS (S : HSp D) (x y : Fin S.rank → D.host.E) : D.host.E := ∑ i, ∑ j, star (x i) * S.gram i j * y j

/- English proof (translation)
Unfold `hS`. Simplify using `only [Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hS_smul (S : HSp D) (c c' : D.host.E) (x y : Fin S.rank → D.host.E) :
    hS S (c • x) (c' • y) = star c * c' * hS S x y := by
  unfold hS
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `[hS]`.
-/
theorem hS_zero_left (S : HSp D) (y : Fin S.rank → D.host.E) : hS S 0 y = 0 := by
  simp [hS]

/- English proof (translation)
Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]`.
-/
theorem blk_e {R : Type} [Zero R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) R)
    (B : Matrix (Fin q) (Fin q) R) (s t : Fin p ⊕ Fin q) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B (e s) (e t) = fromBlocks A 0 0 B s t := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]

/- English proof (translation)
Establish `hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z` using `fun _ => rfl`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, skewGram, dotProduct, mulVec, Matrix.smul_apply, hσ, hS, smul_eq_mul]`. Rewrite using `[← Equiv.sum_comp e]`. Simplify using `only [← Equiv.sum_comp e, Fintype.sum_sum_type, blk_e, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_add, Finset.mul_sum]`. Use `congr 1`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_skewGram (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (x y : Fin d → D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (skewGram A B e) y x =
      D.host.xi0 * (hS A (fun k => x (e (.inl k))) (fun k => y (e (.inl k))) +
        hS B (fun k => x (e (.inr k))) (fun k => y (e (.inr k)))) := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, skewGram, dotProduct, mulVec, Matrix.smul_apply, hσ, hS, smul_eq_mul]
  rw [← Equiv.sum_comp e]
  simp only [← Equiv.sum_comp e, Fintype.sum_sum_type, blk_e, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply, Matrix.zero_apply, mul_zero,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_add, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

def IntTr (z : D.host.E) : Prop := ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * z))

/- English proof (translation)
Introduce `o` and use `by rw [mul_add, map_add]; exact (h o).add (h' o)`.
-/
theorem IntTr.add {z z' : D.host.E} (h : IntTr z) (h' : IntTr z') : IntTr (z + z') := fun o => by
  rw [mul_add, map_add]; exact (h o).add (h' o)

/- English proof (translation)
Introduce `o` and use `by have := h (o * b) rwa [show ((o * b : 𝓞 D.host.E) : D.host.E) * z = (o : D.host.E) * (z * b) by push_cast; ring] at this`.
-/
theorem IntTr.mul_int {z : D.host.E} (h : IntTr z) (b : 𝓞 D.host.E) : IntTr (z * (b : D.host.E)) := fun o => by
  have := h (o * b)
  rwa [show ((o * b : 𝓞 D.host.E) : D.host.E) * z = (o : D.host.E) * (z * b) by push_cast; ring] at this

/- English proof (translation)
Establish `hfp` using `Formalism.IndefR.Fin.factPrincipalDatum D.R D.host`. Establish `hdd` using `coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E)`. Use `eq_inv_of_mul_eq_one_left hfp` as an intermediate fact. Rewrite using `[this]`. Use `show (((differentIdeal ℤ (𝓞 D.host.E)) : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ = _`.

Rewrite using `[hdd, inv_inv]`.
-/
theorem hX : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar =
    FractionalIdeal.dual ℤ ℚ 1 := by
  have hfp := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  have hdd := coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E)
  have := eq_inv_of_mul_eq_one_left hfp
  rw [this]
  show (((differentIdeal ℤ (𝓞 D.host.E)) : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ = _
  rw [hdd, inv_inv]

/- English proof (translation)
Rewrite using `[← FractionalIdeal.coeIdeal_top]`. Conclude with `FractionalIdeal.coeIdeal_ne_zero.2 top_ne_bot`.
-/
theorem one_ne_zero' : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
  rw [← FractionalIdeal.coeIdeal_top]; exact FractionalIdeal.coeIdeal_ne_zero.2 top_ne_bot

/- English proof (translation)
Introduce `h`. Establish `hfp` using `Formalism.IndefR.Fin.factPrincipalDatum D.R D.host`. Rewrite `hfp` using `[h]`. Simplify using `at hfp`.
-/
theorem AA_ne : D.host.AA ≠ 0 := by
  intro h
  have hfp := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  rw [h] at hfp; simp at hfp

/- English proof (translation)
Introduce `h`. Establish `hfp` using `Formalism.IndefR.Fin.factPrincipalDatum D.R D.host`. Rewrite `hfp` using `[h]`. Simplify using `at hfp`.
-/
theorem AAbar_ne : D.host.AAbar ≠ 0 := by
  intro h
  have hfp := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  rw [h] at hfp; simp at hfp

/- English proof (translation)
Introduce `h`. Establish `hfp` using `Formalism.IndefR.Fin.factPrincipalDatum D.R D.host`. Rewrite `hfp` using `[h]`. Simplify using `at hfp`.
-/
theorem xi_ne : D.host.xi0 ≠ 0 := by
  intro h
  have hfp := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  rw [h] at hfp; simp at hfp

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_dual one_ne_zero']`. Prove the components needed by the constructor for the conclusion. Introduce `h a ha`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Take `⟨q, hq⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 (h o)`.

Use `⟨q, ?_⟩` and prove the remaining obligations. Rewrite using `[hq, Algebra.traceForm_apply, mul_comm]`. Introduce `h o`. Take `⟨q, hq⟩` from `h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)`. Rewrite `hq` using `[Algebra.traceForm_apply]`.

Rewrite using `[mul_comm]`. Establish `: Algebra.trace ℚ D.host.E (z * (o : D.host.E)) = algebraMap ℤ ℚ q` using `by rw [hq]`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`.
-/
theorem intTr_iff_mem_dual (z : D.host.E) : IntTr z ↔ z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  rw [FractionalIdeal.mem_dual one_ne_zero']
  constructor
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨q, hq⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 (h o)
    refine ⟨q, ?_⟩
    rw [hq, Algebra.traceForm_apply, mul_comm]
  · intro h o
    obtain ⟨q, hq⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply] at hq
    rw [mul_comm]
    have : Algebra.trace ℚ D.host.E (z * (o : D.host.E)) = algebraMap ℤ ℚ q := by rw [hq]
    rw [this]; exact isIntegral_algebraMap

end GlobalTheory.SkewLat.DualPair

namespace GlobalTheory.SkewLat.DualPair

variable {D : D7}

/- English proof (translation)
Use `hS_smul S c 1 x y` as an intermediate fact. Rewrite `this` using `[one_smul, mul_one]`. Then use the resulting hypothesis.
-/
theorem hS_smul_left (S : HSp D) (c : D.host.E) (x y : Fin S.rank → D.host.E) :
    hS S (c • x) y = star c * hS S x y := by
  have := hS_smul S c 1 x y
  rwa [one_smul, mul_one] at this

/- English proof (translation)
Use `hS_smul S 1 c x y` as an intermediate fact. Rewrite `this` using `[one_smul, star_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem hS_smul_right (S : HSp D) (c : D.host.E) (x y : Fin S.rank → D.host.E) :
    hS S x (c • y) = c * hS S x y := by
  have := hS_smul S 1 c x y
  rwa [one_smul, star_one, one_mul] at this

/- English proof (translation)
Rewrite using `[← hX]`. Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hc) (hs _ hc')`.
-/
theorem xi_mem (hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar) {c c' : D.host.E} (hc : c ∈ D.host.AA)
    (hc' : c' ∈ D.host.AA) :
    D.host.xi0 * c * star c' ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  rw [← hX]
  exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hc)
    (hs _ hc')

/- English proof (translation)
Rewrite using `[mul_inv_cancel₀ AA_ne]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩`.
-/
theorem one_mem_AA_mul : (1 : D.host.E) ∈ D.host.AA * D.host.AA⁻¹ := by
  rw [mul_inv_cancel₀ AA_ne]; exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩

/- English proof (translation)
Establish `h` using `FractionalIdeal.mul_mem_mul hc ha`. Rewrite `h` using `[inv_mul_cancel₀ AA_ne]`. Take `⟨b, hb⟩` from `(FractionalIdeal.mem_one_iff _).1 h`. Conclude with `⟨b, hb⟩`.
-/
theorem int_of_inv_mul {c a : D.host.E} (hc : c ∈ D.host.AA⁻¹) (ha : a ∈ D.host.AA) :
    ∃ b : 𝓞 D.host.E, (b : D.host.E) = c * a := by
  have h := FractionalIdeal.mul_mem_mul hc ha
  rw [inv_mul_cancel₀ AA_ne] at h
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact ⟨b, hb⟩

/- English proof (translation)
Introduce `c hc`. Take `⟨b, hb⟩` from `int_of_inv_mul hc ha`. Rewrite using `[smul_smul, ← hb]`. Conclude with `Λ.smul_mem b hs`.
-/
theorem smul_mem_scLat {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin n → D.host.E} (hs : s ∈ Λ) : a • s ∈ scLat D.host.AA Λ := by
  intro c hc
  obtain ⟨b, hb⟩ := int_of_inv_mul hc ha
  rw [smul_smul, ← hb]
  exact Λ.smul_mem b hs

/- English proof (translation)
Establish `key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, ∀ v ∈ D.host.AA * D.host.AA⁻¹, IntTr (D.host.xi0 * star u * v * hS S x y)`. Introduce `u hu`. Use `FractionalIdeal.mul_induction_on hu (C := fun u => ∀ v ∈ D.host.AA * D.host.AA⁻¹, IntTr (D.host.xi0 * star u * v * hS S x y)) ?_ ?_` and prove the remaining obligations. Introduce `a ha c hc v hv`. Use `FractionalIdeal.mul_induction_on hv (C := fun v => IntTr (D.host.xi0 * star (a * c) * v * hS S x y)) ?_ ?_` and prove the remaining obligations.

Introduce `a' ha' c' hc'`. Take `⟨b, hb⟩` from `(hΛ.2 (c' • y)).1 (hy c' hc') (c • x) (hx c hc)`. Establish `e1 : D.host.xi0 * star (a * c) * (a' * c') * hS S x y = D.host.xi0 * a' * star a * (b : D.host.E)`. Rewrite using `[hb, show (∑ i, ∑ j, star ((c • x) i) * S.gram i j * (c' • y) j) = hS S (c • x) (c' • y) from rfl, hS_smul, star_mul']`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Conclude with `((intTr_iff_mem_dual _).2 (xi_mem hs ha' ha)).mul_int b`. Introduce `v1 v2 h1 h2`. Rewrite using `[show D.host.xi0 * star (a * c) * (v1 + v2) * hS S x y = D.host.xi0 * star (a * c) * v1 * hS S x y + D.host.xi0 * star (a * c) * v2 * hS S x y by ring]`. Conclude with `h1.add h2`.

Introduce `u1 u2 h1 h2 v hv`. Rewrite using `[star_add, show D.host.xi0 * (star u1 + star u2) * v * hS S x y = D.host.xi0 * star u1 * v * hS S x y + D.host.xi0 * star u2 * v * hS S x y by ring]`. Conclude with `(h1 v hv).add (h2 v hv)`. Use `key 1 one_mem_AA_mul 1 one_mem_AA_mul` as an intermediate fact. Simplify using `using this`.
-/
theorem fwd (hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar) (S : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (hΛ : IsSelfDualC S Λ) {x y : Fin S.rank → D.host.E} (hx : x ∈ scLat D.host.AA Λ) (hy : y ∈ scLat D.host.AA Λ) :
    IntTr (D.host.xi0 * hS S x y) := by
  have key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, ∀ v ∈ D.host.AA * D.host.AA⁻¹,
      IntTr (D.host.xi0 * star u * v * hS S x y) := by
    intro u hu
    refine FractionalIdeal.mul_induction_on hu
      (C := fun u => ∀ v ∈ D.host.AA * D.host.AA⁻¹, IntTr (D.host.xi0 * star u * v * hS S x y)) ?_ ?_
    · intro a ha c hc v hv
      refine FractionalIdeal.mul_induction_on hv
        (C := fun v => IntTr (D.host.xi0 * star (a * c) * v * hS S x y)) ?_ ?_
      · intro a' ha' c' hc'
        obtain ⟨b, hb⟩ := (hΛ.2 (c' • y)).1 (hy c' hc') (c • x) (hx c hc)
        have e1 : D.host.xi0 * star (a * c) * (a' * c') * hS S x y = D.host.xi0 * a' * star a * (b : D.host.E) := by
          rw [hb, show (∑ i, ∑ j, star ((c • x) i) * S.gram i j * (c' • y) j) = hS S (c • x) (c' • y) from rfl,
            hS_smul, star_mul']
          ring
        rw [e1]
        exact ((intTr_iff_mem_dual _).2 (xi_mem hs ha' ha)).mul_int b
      · intro v1 v2 h1 h2
        rw [show D.host.xi0 * star (a * c) * (v1 + v2) * hS S x y =
          D.host.xi0 * star (a * c) * v1 * hS S x y + D.host.xi0 * star (a * c) * v2 * hS S x y by ring]
        exact h1.add h2
    · intro u1 u2 h1 h2 v hv
      rw [star_add, show D.host.xi0 * (star u1 + star u2) * v * hS S x y =
        D.host.xi0 * star u1 * v * hS S x y + D.host.xi0 * star u2 * v * hS S x y by ring]
      exact (h1 v hv).add (h2 v hv)
  have := key 1 one_mem_AA_mul 1 one_mem_AA_mul
  simpa using this

/- English proof (translation)
Introduce `c hcA`. Use `(hΛ.2 (c • y)).2 fun s hs => ?_` and prove the remaining obligations. Establish `hmem : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) ≤ D.host.AA * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar)`. Rewrite using `[show D.host.AA * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar by ring, hX, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.mul_le]`. Introduce `i hi j hj`.

Take `⟨z, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).1 hi`. Establish `h1` using `(intTr_iff_mem_dual _).1 (h (star j) (hc j hj) s hs)`. Rewrite `h1` using `[hS_smul_left, star_star]`. Rewrite using `[smul_mul_assoc, show hS S s y * D.host.xi0 * j = D.host.xi0 * (j * hS S s y) by ring]`. Conclude with `Submodule.smul_mem _ z h1`.

Establish `hXne : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar ≠ 0` using `mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 xi_ne) AAbar_ne`. Establish `hle : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) ≤ D.host.AA`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_inv_cancel₀ hXne, mul_one]`. Use `_ ≤ D.host.AA * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar)⁻¹ := by gcongr`.

Use `_ = D.host.AA := by rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]`. Take `⟨b, hb⟩` from `int_of_inv_mul hcA (hle (FractionalIdeal.mem_spanSingleton_self _ _))`. Conclude with `⟨b, by rw [hb, ← hS_smul_right]; rfl⟩`.
-/
theorem bwd (hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA) (S : HSp D)
    {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hΛ : IsSelfDualC S Λ) {y : Fin S.rank → D.host.E}
    (h : ∀ a ∈ D.host.AA, ∀ s ∈ Λ, IntTr (D.host.xi0 * hS S (a • s) y)) : y ∈ scLat D.host.AA Λ := by
  intro c hcA
  refine (hΛ.2 (c • y)).2 fun s hs => ?_
  have hmem : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) ≤ D.host.AA *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) := by
    rw [show D.host.AA * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) =
      FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar by ring, hX,
      ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    have h1 := (intTr_iff_mem_dual _).1 (h (star j) (hc j hj) s hs)
    rw [hS_smul_left, star_star] at h1
    rw [smul_mul_assoc, show hS S s y * D.host.xi0 * j = D.host.xi0 * (j * hS S s y) by ring]
    exact Submodule.smul_mem _ z h1
  have hXne : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar ≠ 0 :=
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 xi_ne) AAbar_ne
  have hle : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) ≤ D.host.AA := by
    calc FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y)
        = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]
      _ ≤ D.host.AA * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar)⁻¹ := by gcongr
      _ = D.host.AA := by rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]
  obtain ⟨b, hb⟩ := int_of_inv_mul hcA (hle (FractionalIdeal.mem_spanSingleton_self _ _))
  exact ⟨b, by rw [hb, ← hS_smul_right]; rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy x hx o`. Establish `hy'` using `GlobalTheory.SkewLat.mem_pairLat.1 hy`. Establish `hx'` using `GlobalTheory.SkewLat.mem_pairLat.1 hx`. Rewrite using `[form_skewGram, mul_add]`.

Conclude with `((fwd hs A hA hx'.1 hy'.1).add (fwd hs B hB hx'.2 hy'.2)) o`. Introduce `h`. Use `GlobalTheory.SkewLat.mem_pairLat.2 ⟨bwd hc A hA fun a ha s hs' => ?_, bwd hc B hB fun a ha s hs' => ?_⟩` and prove the remaining obligations. Set `x : Fin d → D.host.E` to `fun i => Sum.elim (fun k => a * s k) (fun _ => 0) (e.symm i)`. Establish `hxA : (fun k => x (e (.inl k))) = a • s` using `by ext k; simp [x]`.

Establish `hxB : (fun k => x (e (.inr k))) = 0` using `by ext k; simp [x]`. Establish `hx : x ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e`. Use `GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hxA]`. Conclude with `smul_mem_scLat ha hs'`.

Rewrite using `[hxB]`. Conclude with `zero_mem _`. Introduce `o`. Use `h x hx o` as an intermediate fact. Rewrite `this` using `[form_skewGram, hxA, hxB, hS_zero_left, add_zero]`. Then use the resulting hypothesis.

Set `x : Fin d → D.host.E` to `fun i => Sum.elim (fun _ => 0) (fun k => a * s k) (e.symm i)`. Establish `hxA : (fun k => x (e (.inl k))) = 0` using `by ext k; simp [x]`. Establish `hxB : (fun k => x (e (.inr k))) = a • s` using `by ext k; simp [x]`. Establish `hx : x ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e`. Use `GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hxA]`. Conclude with `zero_mem _`. Rewrite using `[hxB]`. Conclude with `smul_mem_scLat ha hs'`. Introduce `o`.

Use `h x hx o` as an intermediate fact. Rewrite `this` using `[form_skewGram, hxA, hxB, hS_zero_left, zero_add]`. Then use the resulting hypothesis.
-/
theorem main_of (hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar) (hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA) (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)}
    (hA : IsSelfDualC A ΛA) (hB : IsSelfDualC B ΛB) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E) :
    y ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e ↔
      ∀ x ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) y x)) := by
  constructor
  · intro hy x hx o
    have hy' := GlobalTheory.SkewLat.mem_pairLat.1 hy
    have hx' := GlobalTheory.SkewLat.mem_pairLat.1 hx
    rw [form_skewGram, mul_add]
    exact ((fwd hs A hA hx'.1 hy'.1).add (fwd hs B hB hx'.2 hy'.2)) o
  · intro h
    refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨bwd hc A hA fun a ha s hs' => ?_, bwd hc B hB fun a ha s hs' => ?_⟩
    · let x : Fin d → D.host.E := fun i => Sum.elim (fun k => a * s k) (fun _ => 0) (e.symm i)
      have hxA : (fun k => x (e (.inl k))) = a • s := by ext k; simp [x]
      have hxB : (fun k => x (e (.inr k))) = 0 := by ext k; simp [x]
      have hx : x ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e := by
        refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩
        · rw [hxA]; exact smul_mem_scLat ha hs'
        · rw [hxB]; exact zero_mem _
      intro o
      have := h x hx o
      rwa [form_skewGram, hxA, hxB, hS_zero_left, add_zero] at this
    · let x : Fin d → D.host.E := fun i => Sum.elim (fun _ => 0) (fun k => a * s k) (e.symm i)
      have hxA : (fun k => x (e (.inl k))) = 0 := by ext k; simp [x]
      have hxB : (fun k => x (e (.inr k))) = a • s := by ext k; simp [x]
      have hx : x ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e := by
        refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩
        · rw [hxA]; exact zero_mem _
        · rw [hxB]; exact smul_mem_scLat ha hs'
      intro o
      have := h x hx o
      rwa [form_skewGram, hxA, hxB, hS_zero_left, zero_add] at this

end GlobalTheory.SkewLat.DualPair

/- English proof (translation)
Introduce `D hc A B ΛA ΛB hA hB d e y`. Conclude with `GlobalTheory.SkewLat.DualPair.main_of (fun c h => by rw [Formalism.BasicNotions.Examples₂.star_eq_conj]; exact Formalism.L2.Pj.conj_mem_AAbar D h) hc A B hA hB e y`.
-/
theorem GlobalTheory.SkewLat.pairLat_trace_selfDual : ∀ {D : D7}, (∀ c ∈ D.host.AAbar, star c ∈ D.host.AA) → ∀ (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)},
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E),
    y ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e ↔
      ∀ x ∈ GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat D.host.AA ΛA) (GlobalTheory.SkewLat.scLat D.host.AA ΛB) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) y x)) := by
  intro D hc A B ΛA ΛB hA hB d e y
  exact GlobalTheory.SkewLat.DualPair.main_of (fun c h => by rw [Formalism.BasicNotions.Examples₂.star_eq_conj]; exact Formalism.L2.Pj.conj_mem_AAbar D h) hc A B hA hB e y
