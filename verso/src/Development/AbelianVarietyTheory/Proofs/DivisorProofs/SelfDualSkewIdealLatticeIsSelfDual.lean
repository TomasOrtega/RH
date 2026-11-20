import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitInert
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.SkewLatSD

variable (D : D7)

local notation "FI" => FractionalIdeal (𝓞 D.host.E)⁰ D.host.E

/- English proof (translation)
Use `D.host.isCMField_hostE` as an intermediate fact. Conclude with `D.host.φ₀.injective ((NumberField.IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans (D.host.conjE_apply D.host.φ₀ x).symm)`.
-/
theorem star_eq_conj' (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  have := D.host.isCMField_hostE
  exact D.host.φ₀.injective ((NumberField.IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm)

/- English proof (translation)
Use `letI := D.host.cmStar`. Rewrite using `[← star_eq_conj', ← star_eq_conj', star_star]`.
-/
theorem conj_conj' (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  rw [← star_eq_conj', ← star_eq_conj', star_star]

/- English proof (translation)
The claim follows from `AlgEquiv.ext fun x => conj_conj' D x`.
-/
theorem conj_mul_conj : D.host.conj * D.host.conj = 1 :=
  AlgEquiv.ext fun x => conj_conj' D x

/- English proof (translation)
Rewrite using `[smul_smul, conj_mul_conj, one_smul]`.
-/
theorem conj_smul_conj_smul (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  rw [smul_smul, conj_mul_conj, one_smul]

variable {D}

/- English proof (translation)
Take `⟨j, hj, hj0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Introduce `e`. Use `Ideal.smul_mem_pointwise_smul g j I hj` as an intermediate fact. Rewrite `this` using `[e, Ideal.mem_bot, smul_eq_zero_iff_eq]`. Conclude with `hj0 this`.
-/
theorem smul_ne_bot (g : Gal(D.host.E/ℚ)) {I : Ideal (𝓞 D.host.E)} (h : I ≠ ⊥) : g • I ≠ ⊥ := by
  obtain ⟨j, hj, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  intro e
  have := Ideal.smul_mem_pointwise_smul g j I hj
  rw [e, Ideal.mem_bot, smul_eq_zero_iff_eq] at this
  exact hj0 this

/- English proof (translation)
Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]` and apply the resulting hypothesis.
-/
theorem coe_ne_zero {I : Ideal (𝓞 D.host.E)} (h : I ≠ ⊥) : (I : FI) ≠ 0 := by
  rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

/- English proof (translation)
Rewrite `hx` using `[FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero hJ)]`. Rewrite using `[FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero (smul_ne_bot g hJ))]`. Introduce `c hc`. Take `⟨c', hc', rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hc`. Establish `h1 : g⁻¹ • c' ∈ J` using `Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hc'`.

Take `⟨i, hi, e⟩` from `(FractionalIdeal.mem_coeIdeal _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, h1, rfl⟩))`. Use `(FractionalIdeal.mem_coeIdeal _).2 ⟨g • i, Ideal.smul_mem_pointwise_smul g i I hi, ?_⟩` and prove the remaining obligations. Establish `e' : ((i : 𝓞 D.host.E) : D.host.E) = x * ((g⁻¹ • c' : 𝓞 D.host.E) : D.host.E)` using `e`. Use `show ((g • i : 𝓞 D.host.E) : D.host.E) = g x * (c' : D.host.E)`. Establish `e2 : ((g • i : 𝓞 D.host.E) : D.host.E) = g (i : D.host.E)` using `rfl`.

Establish `e3 : ((g⁻¹ • c' : 𝓞 D.host.E) : D.host.E) = g⁻¹ (c' : D.host.E)` using `rfl`. Rewrite using `[e2, e', e3, map_mul, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]`.
-/
theorem map_mem_div (g : Gal(D.host.E/ℚ)) {I J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) {x : D.host.E}
    (hx : x ∈ (I : FI) / (J : FI)) : g x ∈ ((g • I : Ideal (𝓞 D.host.E)) : FI) / ((g • J : Ideal (𝓞 D.host.E)) : FI) := by
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero hJ)] at hx
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero (smul_ne_bot g hJ))]
  intro c hc
  obtain ⟨c', hc', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hc
  have h1 : g⁻¹ • c' ∈ J := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hc'
  obtain ⟨i, hi, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, h1, rfl⟩))
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨g • i, Ideal.smul_mem_pointwise_smul g i I hi, ?_⟩
  have e' : ((i : 𝓞 D.host.E) : D.host.E) = x * ((g⁻¹ • c' : 𝓞 D.host.E) : D.host.E) := e
  show ((g • i : 𝓞 D.host.E) : D.host.E) = g x * (c' : D.host.E)
  have e2 : ((g • i : 𝓞 D.host.E) : D.host.E) = g (i : D.host.E) := rfl
  have e3 : ((g⁻¹ • c' : 𝓞 D.host.E) : D.host.E) = g⁻¹ (c' : D.host.E) := rfl
  rw [e2, e', e3, map_mul, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

end GlobalTheory.SkewLatSD

namespace GlobalTheory.SkewLatSD

variable {D : D7}

/- English proof (translation)
Simplify using `only [GlobalTheory.FunObj.SqNum.skewLat, Submodule.mem_pi, Set.mem_univ, true_implies]`. Both sides reduce to the same expression.
-/
theorem mem_skewLat_iff {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} (y : Fin N → D.host.E) :
    y ∈ GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N ↔ ∀ i, y i ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  simp only [GlobalTheory.FunObj.SqNum.skewLat, Submodule.mem_pi, Set.mem_univ, true_implies]
  rfl

/- English proof (translation)
Introduce `D 𝔪 N h𝔪`. Use `letI := D.host.cmStar`. Use `set σ := D.host.conj`. Use `set 𝔫 : Ideal (𝓞 D.host.E) := σ • 𝔪 with h𝔫`. Establish `h𝔫0 : 𝔫 ≠ ⊥` using `smul_ne_bot σ h𝔪`.

Establish `hA0 : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0` using `div_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)`. Establish `hB0 : (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0` using `div_ne_zero (coe_ne_zero h𝔫0) (coe_ne_zero h𝔪)`. Establish `hBA : (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) = 1`. Rewrite using `[div_mul_div_comm, mul_comm (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), div_self (mul_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0))]`. Establish `hσ𝔫 : σ • 𝔫 = 𝔪` using `conj_smul_conj_smul D 𝔪`.

Establish `toB : ∀ x ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), σ x ∈ (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)` using `fun x hx => by`. Use `map_mem_div σ h𝔫0 hx` as an intermediate fact. Rewrite `this` using `[hσ𝔫]`. Then use the resulting hypothesis. Establish `toA : ∀ x ∈ (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), σ x ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)` using `fun x hx => by`. Use `map_mem_div σ h𝔪 hx` as an intermediate fact.

Rewrite `this` using `[hσ𝔫]`. Then use the resulting hypothesis. Establish `hmem` using `fun y => mem_skewLat_iff (D := D) (𝔪 := 𝔪) (N := N) y`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.FunObj.SqNum.skewLat`. Rewrite using `[← Submodule.iSup_map_single]`.

Conclude with `Submodule.fg_iSup _ fun i => (FractionalIdeal.fg_of_isNoetherianRing le_rfl _).map _`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (show (((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ from fun e => hA0 (FractionalIdeal.coeToSubmodule_injective …`. Establish `hs : ∀ i, (Pi.single i a : Fin N → D.host.E) ∈ GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N` using `fun i => by`. Rewrite using `[hmem]`. Introduce `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using ha`. Rewrite using `[Pi.single_eq_of_ne hj]`. Conclude with `FractionalIdeal.zero_mem _`.

Rewrite using `[Submodule.eq_top_iff']`. Introduce `v`. Establish `hv : v = ∑ i, (v i * a⁻¹) • (Pi.single i a : Fin N → D.host.E)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, ha0]`.

Rewrite using `[hv]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i))`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`.

Rewrite `hx`, `hy` using `[hmem]`. Unfold `Formalism.BasicNotions.stdH`. Use `Subring.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[star_eq_conj']`. Use `FractionalIdeal.mul_mem_mul (toB _ (hx i)) (hy i)` as an intermediate fact.

Rewrite `this` using `[hBA, FractionalIdeal.mem_one_iff]`. Take `⟨r, hr⟩` from `this`. Conclude with `⟨r, hr⟩`. Introduce `h`. Rewrite using `[hmem]`.

Introduce `i`. Rewrite using `[← one_div_div, FractionalIdeal.mem_div_iff_of_ne_zero hB0]`. Introduce `b hb`. Establish `ha` using `toA b hb`. Establish `hx : (Pi.single i (σ b) : Fin N → D.host.E) ∈ GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N`.

Rewrite using `[hmem]`. Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using ha`.

Rewrite using `[Pi.single_eq_of_ne hj]`. Conclude with `FractionalIdeal.zero_mem _`. Use `h _ hx` as an intermediate fact. Unfold `Formalism.BasicNotions.stdH at this`. Rewrite `this` using `[Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (fun hi => absurd (Finset.mem_univ i) hi)]`.

Rewrite `this` using `[Pi.single_eq_same, star_eq_conj', conj_conj']`. Take `⟨r, hr⟩` from `this`. Rewrite using `[FractionalIdeal.mem_one_iff]`. Conclude with `⟨r, by rw [hr, mul_comm]⟩`.
-/
theorem skewLat_sd : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ), 𝔪 ≠ ⊥ → SD D (GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N) := by
  intro D 𝔪 N h𝔪
  letI := D.host.cmStar
  set σ := D.host.conj
  set 𝔫 : Ideal (𝓞 D.host.E) := σ • 𝔪 with h𝔫
  have h𝔫0 : 𝔫 ≠ ⊥ := smul_ne_bot σ h𝔪
  have hA0 : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := div_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)
  have hB0 : (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := div_ne_zero (coe_ne_zero h𝔫0) (coe_ne_zero h𝔪)
  have hBA : (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) = 1 := by
    rw [div_mul_div_comm, mul_comm (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), div_self (mul_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0))]
  have hσ𝔫 : σ • 𝔫 = 𝔪 := conj_smul_conj_smul D 𝔪

  have toB : ∀ x ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), σ x ∈ (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := fun x hx => by
    have := map_mem_div σ h𝔫0 hx
    rwa [hσ𝔫] at this
  have toA : ∀ x ∈ (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), σ x ∈ (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := fun x hx => by
    have := map_mem_div σ h𝔪 hx
    rwa [hσ𝔫] at this
  have hmem := fun y => mem_skewLat_iff (D := D) (𝔪 := 𝔪) (N := N) y
  refine ⟨?_, ?_, ?_⟩
  · unfold GlobalTheory.FunObj.SqNum.skewLat
    rw [← Submodule.iSup_map_single]
    exact Submodule.fg_iSup _ fun i => (FractionalIdeal.fg_of_isNoetherianRing le_rfl _).map _
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (show (((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) / (𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ from fun e =>
        hA0 (FractionalIdeal.coeToSubmodule_injective (e.trans FractionalIdeal.coe_zero.symm)))
    have hs : ∀ i, (Pi.single i a : Fin N → D.host.E) ∈ GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N := fun i => by
      rw [hmem]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using ha
      · rw [Pi.single_eq_of_ne hj]; exact FractionalIdeal.zero_mem _
    rw [Submodule.eq_top_iff']
    intro v
    have hv : v = ∑ i, (v i * a⁻¹) • (Pi.single i a : Fin N → D.host.E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, ha0]
    rw [hv]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i))
  · intro y
    constructor
    · intro hy x hx
      rw [hmem] at hx hy
      unfold Formalism.BasicNotions.stdH
      refine Subring.sum_mem _ fun i _ => ?_
      rw [star_eq_conj']
      have := FractionalIdeal.mul_mem_mul (toB _ (hx i)) (hy i)
      rw [hBA, FractionalIdeal.mem_one_iff] at this
      obtain ⟨r, hr⟩ := this
      exact ⟨r, hr⟩
    · intro h
      rw [hmem]
      intro i
      rw [← one_div_div, FractionalIdeal.mem_div_iff_of_ne_zero hB0]
      intro b hb
      have ha := toA b hb
      have hx : (Pi.single i (σ b) : Fin N → D.host.E) ∈ GlobalTheory.FunObj.SqNum.skewLat D 𝔪 N := by
        rw [hmem]
        intro j
        by_cases hj : j = i
        · subst hj; simpa using ha
        · rw [Pi.single_eq_of_ne hj]; exact FractionalIdeal.zero_mem _
      have := h _ hx
      unfold Formalism.BasicNotions.stdH at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
        (fun hi => absurd (Finset.mem_univ i) hi)] at this
      rw [Pi.single_eq_same, star_eq_conj', conj_conj'] at this
      obtain ⟨r, hr⟩ := this
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨r, by rw [hr, mul_comm]⟩

end GlobalTheory.SkewLatSD
