import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfB
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CuspFlowEqTorusActionStatement

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

namespace GlobalTheory.MaxCuspKilled

open MeasureTheory GlobalTheory.TorusFourier

noncomputable def dotForm {ι : Type} [Fintype ι] (c : ℝ) (v : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun t := c * ∑ k, v k * t k
  map_add' s t := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a s := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dotForm_apply {ι : Type} [Fintype ι] (c : ℝ) (v t : ι → ℝ) :
    dotForm c v t = c * ∑ k, v k * t k := rfl

/- English proof (translation)
Establish `h : ∀ t : Fin N → ℝ, ∑ i, t i • Pi.basisFun ℝ (Fin N) i = t` using `fun t => (Pi.basisFun ℝ (Fin N)).sum_repr t`. Unfold `coefFn cubeCoeff cube`. Rewrite using `[← Set.pi_univ_Icc]`. Simplify using `only [h]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Simplify using `only [integrand, chr, eNeg, dotForm_apply, one_mul, mul_comm (ph _)]`.
-/
theorem coefFn_eq_cubeCoeff {Ω : Type} {N : ℕ} (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ)
    (P : Ω → ℂ) (x : Ω) :
    coefFn act ph P x =
      cubeCoeff (Pi.basisFun ℝ (Fin N)) (fun t => P (act t x)) (dotForm 1 ph) := by
  have h : ∀ t : Fin N → ℝ, ∑ i, t i • Pi.basisFun ℝ (Fin N) i = t := fun t =>
    (Pi.basisFun ℝ (Fin N)).sum_repr t
  unfold coefFn cubeCoeff cube
  rw [← Set.pi_univ_Icc]
  simp only [h]
  congr 1
  funext t
  simp only [integrand, chr, eNeg, dotForm_apply, one_mul, mul_comm (ph _)]

/- English proof (translation)
Establish `key : herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) = ∑ a, ∑ b, η a * cc (η b) * herm X.Gm (cu.e a) (cu.e b)`. Simplify using `only [herm, cc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm`.

Use `_ = ∑ b, ∑ a, ∑ k, ∑ l, η a * cu.e a k * X.Gm k l * (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) := Finset.sum_congr rfl fun b _ => Finset.sum_comm`. Use `_ = _ := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key]`. Simplify using `[cu.iso]`.
-/
theorem herm_comb {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ} {X : Data E r}
    (cu : CuspFD X ρ) (η : Fin ρ → E) :
    herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) = 0 := by
  have key : herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) =
      ∑ a, ∑ b, η a * cc (η b) * herm X.Gm (cu.e a) (cu.e b) := by
    simp only [herm, cc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      Finset.mul_sum, Finset.sum_mul]
    calc _ = ∑ k, ∑ b, ∑ l, ∑ a, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ b, ∑ k, ∑ a, ∑ l, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ b, ∑ a, ∑ k, ∑ l, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  rw [key]
  simp [cu.iso]

/- English proof (translation)
Introduce `E _ _ _ r ρ X hbas la hchi c P hP cu χ hχ hK x hx`. Take `⟨η, hη0, hηΛ, hηc⟩` from `hK`. Establish `hb : IsZBasis X cu (zBas X cu)` using `Classical.epsilon_spec (hbas cu)`. Establish `hsec : X.IsSec la P` using `hP.1.1.1`. Establish `hdom : ∀ u, zAct X cu u x ∈ X.dom` using `fun u => zAct_mem_dom X cu (zBas_skew X cu (hbas cu)) u x hx`.

Take `⟨L, hL1, hL2, hL3⟩` from `GlobalTheory.T.cuspFlow_eq_torusAction E r ρ X cu hb η hηΛ`. Establish `hiso : X.IsIso (∑ a, η a • cu.e a)` using `⟨hηΛ, herm_comb cu η, fun h => hη0 (funext (Fintype.linearIndependent_iff.1 cu.ind η h))⟩`. Use `set ν : X.Ψ → ℝ := fun τ => (τ.1 (hq χ η)).re with hν`. Use `set g : (Fin (nZ X ρ) → ℝ) → ℂ := fun t => P (zAct X cu t x) with hg`. Establish `hgc : Continuous g` using `hsec.1.continuousOn.comp_continuous (continuous_zAct X cu x) hdom`.

Establish `hper : ∀ l : Fin (nZ X ρ) → ℝ, (∀ k, ∃ z : ℤ, l k = z) → ∀ u, g (u + l) = g u`. Introduce `l hl u`. Use `choose n hn using hl`. Establish `: l = fun i => (n i : ℝ)` using `funext hn`. Rewrite using `[this]`.

Conclude with `maxCuspsA_periodic X cu hb la (hchi cu) P hsec x hx u n`. Establish `hcomp : dotForm 1 (phZ X cu χ) ∘ₗ L = dotForm 2 ν`. Use `LinearMap.ext fun s => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, dotForm_apply, dotForm_apply, one_mul, hL2 χ hχ.1 s]`. Establish `hfreq : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k`.

Introduce `p hp`. Use `choose n hn using hL3 la p hp`. Use `choose m hm using hχ.2`. Use `⟨∑ k, m k * n k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hL2 χ hχ.1 p]`.

Simplify using `only [hn, hm]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hex` using `PeriodLatticeCountable.fd_exists X la`. Take `⟨-, hD, h0, h1⟩` from `hex.choose_spec`.

Take `⟨H₁, -, -⟩` from `partialCoeff_spec_cube (Pi.basisFun ℝ (Fin (nZ X ρ))) hD h0.ne' h1.ne L hgc (fun i => hper _ fun k => ⟨if k = i then 1 else 0, by`. Apply the tactic sequence `by_cases h : k = i <;> simp [h]⟩)`. Use the proof step `(fun l hl => hper _ (hL3 la l hl))`. Take `⟨-, -, -, B⟩` from `H₁ (dotForm 2 ν) hfreq`. Rewrite using `[coefFn_eq_cubeCoeff]`.

Use `B.1 ?_ _ (fun i => ?_) hcomp` and prove the remaining obligations. Use function extensionality and compare the values at `b`. Establish `h` using `hP.2 _ hiso ν hηc _ (hdom b)`. Rewrite `h` using `[Data.fj, if_pos hfreq, dif_pos hex]`. Rewrite using `[partialCoeff, coeff_eq, Pi.zero_apply, ← h]`.

Use `congr 2`. Use function extensionality and compare the values at `s`. Rewrite using `[hL1, maxCuspsA_zAct_add, add_comm (L s), dotForm_apply]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨z, hz⟩` from `hχ.2 i`. Conclude with `⟨z, by simp [dotForm_apply, Pi.single_apply, hz]⟩`.
-/
theorem coefFn_eq_zero_of_killed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) → ∀ (la : Wt X.Ψ r), (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) → ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SSgt la c → ∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c → ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0 := by
  intro E _ _ _ r ρ X hbas la hchi c P hP cu χ hχ hK x hx
  obtain ⟨η, hη0, hηΛ, hηc⟩ := hK
  have hb : IsZBasis X cu (zBas X cu) := Classical.epsilon_spec (hbas cu)
  have hsec : X.IsSec la P := hP.1.1.1
  have hdom : ∀ u, zAct X cu u x ∈ X.dom := fun u =>
    zAct_mem_dom X cu (zBas_skew X cu (hbas cu)) u x hx
  obtain ⟨L, hL1, hL2, hL3⟩ := GlobalTheory.T.cuspFlow_eq_torusAction E r ρ X cu hb η hηΛ
  have hiso : X.IsIso (∑ a, η a • cu.e a) :=
    ⟨hηΛ, herm_comb cu η, fun h => hη0 (funext (Fintype.linearIndependent_iff.1 cu.ind η h))⟩
  set ν : X.Ψ → ℝ := fun τ => (τ.1 (hq χ η)).re with hν
  set g : (Fin (nZ X ρ) → ℝ) → ℂ := fun t => P (zAct X cu t x) with hg
  have hgc : Continuous g := hsec.1.continuousOn.comp_continuous (continuous_zAct X cu x) hdom
  have hper : ∀ l : Fin (nZ X ρ) → ℝ, (∀ k, ∃ z : ℤ, l k = z) → ∀ u, g (u + l) = g u := by
    intro l hl u
    choose n hn using hl
    have : l = fun i => (n i : ℝ) := funext hn
    rw [this]
    exact maxCuspsA_periodic X cu hb la (hchi cu) P hsec x hx u n
  have hcomp : dotForm 1 (phZ X cu χ) ∘ₗ L = dotForm 2 ν := by
    refine LinearMap.ext fun s => ?_
    rw [LinearMap.comp_apply, dotForm_apply, dotForm_apply, one_mul, hL2 χ hχ.1 s]
  have hfreq : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k := by
    intro p hp
    choose n hn using hL3 la p hp
    choose m hm using hχ.2
    refine ⟨∑ k, m k * n k, ?_⟩
    rw [← hL2 χ hχ.1 p]
    simp only [hn, hm]
    push_cast
    rfl
  have hex := PeriodLatticeCountable.fd_exists X la
  obtain ⟨-, hD, h0, h1⟩ := hex.choose_spec
  obtain ⟨H₁, -, -⟩ := partialCoeff_spec_cube (Pi.basisFun ℝ (Fin (nZ X ρ))) hD h0.ne' h1.ne L hgc
    (fun i => hper _ fun k => ⟨if k = i then 1 else 0, by
      by_cases h : k = i <;> simp [h]⟩)
    (fun l hl => hper _ (hL3 la l hl))
  obtain ⟨-, -, -, B⟩ := H₁ (dotForm 2 ν) hfreq
  rw [coefFn_eq_cubeCoeff]
  refine B.1 ?_ _ (fun i => ?_) hcomp
  · funext b
    have h := hP.2 _ hiso ν hηc _ (hdom b)
    rw [Data.fj, if_pos hfreq, dif_pos hex] at h
    rw [partialCoeff, coeff_eq, Pi.zero_apply, ← h]
    congr 2
    funext s
    rw [hL1, maxCuspsA_zAct_add, add_comm (L s), dotForm_apply]
    congr 2
    push_cast
    ring
  · obtain ⟨z, hz⟩ := hχ.2 i
    exact ⟨z, by simp [dotForm_apply, Pi.single_apply, hz]⟩

end GlobalTheory.MaxCuspKilled
