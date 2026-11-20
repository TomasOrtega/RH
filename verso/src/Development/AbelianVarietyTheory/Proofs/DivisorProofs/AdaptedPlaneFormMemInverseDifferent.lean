import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

namespace GlobalTheory.PairDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h : (fun i => σ ((c • x) i)) = σ c • fun i => σ (x i)` using `funext fun i => by simp [map_mul]`. Rewrite using `[form, form, h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) (c : E) :
    form σ J y (c • x) = σ c * form σ J y x := by
  have h : (fun i => σ ((c • x) i)) = σ c • fun i => σ (x i) := funext fun i => by simp [map_mul]
  rw [form, form, h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Establish `h : (IsLocalization.map (S` using `E) E (GlobalTheory.UnrEuler.conjO σ) (GlobalTheory.UnrEuler.conjO_le σ) : E →+* E) = (σ : E →+* E) := by`. Use `IsLocalization.ringHom_ext (𝓞 E)⁰ ?_` and prove the remaining obligations. Rewrite using `[IsLocalization.map_comp]`. Use extensionality with `x`. Simplify using `[GlobalTheory.UnrEuler.conjO, RingOfIntegers.mapRingHom_apply]`.

Conclude with `congrArg (fun f : E →+* E => f c) h`.
-/
theorem map_conjO (σ : E →ₐ[F] E) (c : E) :
    IsLocalization.map (S := E) E (GlobalTheory.UnrEuler.conjO σ) (GlobalTheory.UnrEuler.conjO_le σ) c = σ c := by
  have h : (IsLocalization.map (S := E) E (GlobalTheory.UnrEuler.conjO σ) (GlobalTheory.UnrEuler.conjO_le σ) : E →+* E) =
      (σ : E →+* E) := by
    refine IsLocalization.ringHom_ext (𝓞 E)⁰ ?_
    rw [IsLocalization.map_comp]
    ext x
    simp [GlobalTheory.UnrEuler.conjO, RingOfIntegers.mapRingHom_apply]
  exact congrArg (fun f : E →+* E => f c) h

/- English proof (translation)
Rewrite using `[GlobalTheory.UnrEuler.diffE, coeIdeal_differentIdeal ℤ ℚ E, inv_inv, FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (𝓞 E)⁰ E) _ _ _)]`. Introduce `a ha`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Rewrite using `[Algebra.traceForm_apply, mul_comm]`. Conclude with `IsIntegrallyClosed.isIntegral_iff.1 (h o)`.
-/
theorem mem_inv_diffE {t : E} (h : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * t))) :
    t ∈ (GlobalTheory.UnrEuler.diffE E)⁻¹ := by
  rw [GlobalTheory.UnrEuler.diffE, coeIdeal_differentIdeal ℤ ℚ E, inv_inv,
    FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (𝓞 E)⁰ E) _ _ _)]
  intro a ha
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
  rw [Algebra.traceForm_apply, mul_comm]
  exact IsIntegrallyClosed.isIntegral_iff.1 (h o)

/- English proof (translation)
Establish `hx : x ∈ Submodule.span E (L : Set (Fin n → E))` using `by rw [hL.span_eq_top]; trivial`. Take `⟨m, f, g, hfg⟩` from `Submodule.mem_span_set'.1 hx`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ f`. Use `⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfg, Finset.smul_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨o, ho⟩` from `hb i (Finset.mem_univ i)`. Rewrite using `[← smul_assoc, ← ho, algebraMap_smul]`. Conclude with `L.smul_mem o (g i).2`.
-/
theorem exists_smul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (x : Fin n → E) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ b • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
  obtain ⟨m, f, g, hfg⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ f
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨o, ho⟩ := hb i (Finset.mem_univ i)
  rw [← smul_assoc, ← ho, algebraMap_smul]
  exact L.smul_mem o (g i).2

/- English proof (translation)
Introduce `y hy`. Use `set t := form σ W.J y H'.x with ht`. Establish `h1 : ∀ c ∈ H'.𝔟, σ c * t ∈ (diffE E)⁻¹`. Introduce `c hc`. Use `mem_inv_diffE fun o => ?_` and prove the remaining obligations.

Rewrite using `[← form_smul_right]`. Conclude with `(hS.dual y).1 hy _ ((hA.ideal c).1 hc) o`. Establish `h2 : ∀ j ∈ conjI σ H'.𝔟, t * j ∈ (diffE E)⁻¹`. Introduce `j hj`. Rewrite `hj` using `[conjI, FractionalIdeal.mem_extended_iff]`.

Proceed by induction on `hj using Submodule.span_induction with`. Consider the case `mem j hj`. Take `⟨c, hc, rfl⟩` from `hj`. Rewrite using `[map_conjO, mul_comm]`. Conclude with `h1 c hc`.

Consider the case `zero => rw [mul_zero]`. Conclude with `FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)`. Consider the case `add j j' _ _ h h'`. Rewrite using `[mul_add]`. Conclude with `FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 h) (FractionalIdeal.mem_coe.2 h'))`.

Consider the case `smul o j _ h`. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem _ o h`. Establish `h3 : FractionalIdeal.spanSingleton (𝓞 E)⁰ t * conjI σ H'.𝔟 ≤ (diffE E)⁻¹`. Use `FractionalIdeal.mul_le.2 fun i hi j hj => ?_` and prove the remaining obligations.

Take `⟨z, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).1 hi`. Rewrite using `[smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ z (h2 j hj)`. Establish `hx : H'.x ≠ 0`. Introduce `h0`.

Use `hA.xy` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `[form] at this`. Establish `h𝔠 : H'.𝔟 ≠ 0`. Take `⟨b, hb0, hb⟩` from `exists_smul_mem W.L hS.lat H'.x`.

Establish `hm : (b : E) ∈ H'.𝔟` using `(hA.ideal _).2 (by rwa [algebraMap_smul])`. Introduce `h0`. Rewrite `hm` using `[h0, FractionalIdeal.mem_zero_iff]`. Conclude with `hb0 (RingOfIntegers.coe_eq_zero_iff.1 hm)`. Establish `hI : conjI σ H'.𝔟 ≠ 0` using `conjI_ne_zero σ h𝔠`.

Establish `h4 : FractionalIdeal.spanSingleton (𝓞 E)⁰ t ≤ (conjI σ H'.𝔟)⁻¹ * (diffE E)⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_inv_cancel₀ hI, mul_one]`. Use `_ ≤ (diffE E)⁻¹ * (conjI σ H'.𝔟)⁻¹ := mul_le_mul_left h3 _`. Use `_ = (conjI σ H'.𝔟)⁻¹ * (diffE E)⁻¹ := mul_comm _ _`.

Conclude with `h4 (FractionalIdeal.mem_spanSingleton_self _ t)`.
-/
theorem form_mem_conjI_inv_mul_diffE_inv (σ : E →ₐ[F] E) (B : Base F E)
    {d d₁ r s j₀ j₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁)
    (hA : Plane.IsAdapted σ B H' W W₁ j₀ j₁) (hS : Spc.IsSkew σ B W r s) :
    ∀ y ∈ W.L, form σ W.J y H'.x ∈ (conjI σ H'.𝔟)⁻¹ * (diffE E)⁻¹ := by
  intro y hy
  set t := form σ W.J y H'.x with ht

  have h1 : ∀ c ∈ H'.𝔟, σ c * t ∈ (diffE E)⁻¹ := by
    intro c hc
    refine mem_inv_diffE fun o => ?_
    rw [← form_smul_right]
    exact (hS.dual y).1 hy _ ((hA.ideal c).1 hc) o

  have h2 : ∀ j ∈ conjI σ H'.𝔟, t * j ∈ (diffE E)⁻¹ := by
    intro j hj
    rw [conjI, FractionalIdeal.mem_extended_iff] at hj
    induction hj using Submodule.span_induction with
    | mem j hj =>
      obtain ⟨c, hc, rfl⟩ := hj
      rw [map_conjO, mul_comm]
      exact h1 c hc
    | zero => rw [mul_zero]; exact FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)
    | add j j' _ _ h h' =>
      rw [mul_add]
      exact FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 h) (FractionalIdeal.mem_coe.2 h'))
    | smul o j _ h =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ o h
  have h3 : FractionalIdeal.spanSingleton (𝓞 E)⁰ t * conjI σ H'.𝔟 ≤ (diffE E)⁻¹ := by
    refine FractionalIdeal.mul_le.2 fun i hi j hj => ?_
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ z (h2 j hj)

  have hx : H'.x ≠ 0 := by
    intro h0
    have := hA.xy
    rw [h0] at this
    simp [form] at this
  have h𝔠 : H'.𝔟 ≠ 0 := by
    obtain ⟨b, hb0, hb⟩ := exists_smul_mem W.L hS.lat H'.x
    have hm : (b : E) ∈ H'.𝔟 := (hA.ideal _).2 (by rwa [algebraMap_smul])
    intro h0
    rw [h0, FractionalIdeal.mem_zero_iff] at hm
    exact hb0 (RingOfIntegers.coe_eq_zero_iff.1 hm)
  have hI : conjI σ H'.𝔟 ≠ 0 := conjI_ne_zero σ h𝔠
  have h4 : FractionalIdeal.spanSingleton (𝓞 E)⁰ t ≤ (conjI σ H'.𝔟)⁻¹ * (diffE E)⁻¹ := by
    calc FractionalIdeal.spanSingleton (𝓞 E)⁰ t
        = FractionalIdeal.spanSingleton (𝓞 E)⁰ t * conjI σ H'.𝔟 * (conjI σ H'.𝔟)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ (diffE E)⁻¹ * (conjI σ H'.𝔟)⁻¹ := mul_le_mul_left h3 _
      _ = (conjI σ H'.𝔟)⁻¹ * (diffE E)⁻¹ := mul_comm _ _
  exact h4 (FractionalIdeal.mem_spanSingleton_self _ t)

end GlobalTheory.PairDual
