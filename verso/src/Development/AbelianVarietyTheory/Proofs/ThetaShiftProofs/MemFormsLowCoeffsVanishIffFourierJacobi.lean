import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsTie
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspsIffKilledCoeffVanish
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsMaximalMemSpan

set_option autoImplicit false

namespace GlobalTheory.LowCoeff

section Free

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open MeasureTheory GlobalTheory.TorusFourier GlobalTheory.MaxCuspKilled

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

/- English proof (translation)
Establish `h1 : ∀ a b, IsCMField.complexConj E (X.Gm a b) = X.Gm b a` using `X.Gm_herm`. Simplify using `only [herm, cc, map_sum, map_mul, h1, IsCMField.complexConj_apply_apply]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem herm_swap (X : Data E r) (v w : Fin r → E) : herm X.Gm w v = cc (herm X.Gm v w) := by
  have h1 : ∀ a b, IsCMField.complexConj E (X.Gm a b) = X.Gm b a := X.Gm_herm
  simp only [herm, cc, map_sum, map_mul, h1, IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Distinguish the cases in `hm : ξ ∈ Submodule.span E (Set.range cu.e)`. Conclude with `⟨cu, hm⟩`. Use `set I := Submodule.span E (Set.range cu.e) with hI`. Establish `hiso : GlobalTheory.MaxCusp.IsIsotropicSub X.Gm I` using `GlobalTheory.MaxCusp.isIsotropicSub_span (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact cu.iso a b)`. Set `f : I →ₗ[E] E` to `{ toFun := fun v => herm X.Gm v ξ map_add' := fun x y => by simp [herm, add_mul, Finset.sum_add_distrib] map_smul' := fun c x => by`.

Simplify using `only [herm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring }`. Establish `hIr : Module.finrank E I = n + 1`. Rewrite using `[hI, finrank_span_eq_card cu.ind, Fintype.card_fin]`. Establish `hk : n ≤ Module.finrank E (LinearMap.ker f)`.

Establish `h1` using `f.finrank_range_add_finrank_ker`. Establish `h2 : Module.finrank E (LinearMap.range f) ≤ 1`. Simplify using `using Submodule.finrank_le (LinearMap.range f)`. Use linear arithmetic over natural numbers and integers. Take `⟨u, hu⟩` from `exists_linearIndependent_of_le_finrank hk`.

Use `set w : Fin n → Fin r → E := fun i => ((u i : I) : Fin r → E) with hw`. Establish `hwi : LinearIndependent E w` using `(hu.map' _ (Submodule.ker_subtype _)).map' I.subtype (Submodule.ker_subtype _)`. Establish `hwI : ∀ i, w i ∈ I` using `fun i => (u i : I).2`. Establish `hwξ : ∀ i, herm X.Gm (w i) ξ = 0` using `fun i => (u i).2`. Establish `hns : ξ ∉ Submodule.span E (Set.range w)` using `fun h => hm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hwI i) h)`.

Use `⟨⟨Fin.cons ξ w, hwi.finCons hns, fun a b => ?_⟩, Submodule.subset_span ⟨0, rfl⟩⟩` and prove the remaining obligations. Apply the tactic sequence `refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b`. Conclude with `hξ`. Use `show herm X.Gm ξ (w b) = 0`. Rewrite using `[herm_swap, hwξ]`.

Simplify using `[cc]`. Conclude with `hwξ a`. Conclude with `hiso _ (hwI a) _ (hwI b)`.
-/
theorem exists_cusp_mem {n : ℕ} (X : Data E r) (cu : CuspFD X (n + 1)) {ξ : Fin r → E} (h0 : ξ ≠ 0)
    (hξ : herm X.Gm ξ ξ = 0) : ∃ cu' : CuspFD X (n + 1), ξ ∈ Submodule.span E (Set.range cu'.e) := by
  by_cases hm : ξ ∈ Submodule.span E (Set.range cu.e)
  · exact ⟨cu, hm⟩
  set I := Submodule.span E (Set.range cu.e) with hI
  have hiso : GlobalTheory.MaxCusp.IsIsotropicSub X.Gm I :=
    GlobalTheory.MaxCusp.isIsotropicSub_span (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact cu.iso a b)
  let f : I →ₗ[E] E :=
    { toFun := fun v => herm X.Gm v ξ
      map_add' := fun x y => by simp [herm, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [herm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring }
  have hIr : Module.finrank E I = n + 1 := by
    rw [hI, finrank_span_eq_card cu.ind, Fintype.card_fin]
  have hk : n ≤ Module.finrank E (LinearMap.ker f) := by
    have h1 := f.finrank_range_add_finrank_ker
    have h2 : Module.finrank E (LinearMap.range f) ≤ 1 := by
      simpa using Submodule.finrank_le (LinearMap.range f)
    omega
  obtain ⟨u, hu⟩ := exists_linearIndependent_of_le_finrank hk
  set w : Fin n → Fin r → E := fun i => ((u i : I) : Fin r → E) with hw
  have hwi : LinearIndependent E w :=
    (hu.map' _ (Submodule.ker_subtype _)).map' I.subtype (Submodule.ker_subtype _)
  have hwI : ∀ i, w i ∈ I := fun i => (u i : I).2
  have hwξ : ∀ i, herm X.Gm (w i) ξ = 0 := fun i => (u i).2
  have hns : ξ ∉ Submodule.span E (Set.range w) := fun h =>
    hm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hwI i) h)
  refine ⟨⟨Fin.cons ξ w, hwi.finCons hns, fun a b => ?_⟩, Submodule.subset_span ⟨0, rfl⟩⟩
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · exact hξ
  · show herm X.Gm ξ (w b) = 0
    rw [herm_swap, hwξ]; simp [cc]
  · exact hwξ a
  · exact hiso _ (hwI a) _ (hwI b)

/- English proof (translation)
Introduce `x hx`. Establish `hb : IsZBasis X cu (zBas X cu)` using `Classical.epsilon_spec hbas`. Establish `hdom : ∀ u, zAct X cu u x ∈ X.dom` using `fun u => zAct_mem_dom X cu (zBas_skew X cu hbas) u x hx`. Take `⟨L, hL1, hL2, hL3⟩` from `GlobalTheory.T.cuspFlow_eq_torusAction E r ρ X cu hb η hηΛ`. Use `set ν : X.Ψ → ℝ := fun τ => (τ.1 (hq χ η)).re with hν`.

Use `set g : (Fin (nZ X ρ) → ℝ) → ℂ := fun t => P (zAct X cu t x) with hg`. Establish `hgc : Continuous g` using `hsec.1.continuousOn.comp_continuous (continuous_zAct X cu x) hdom`. Establish `hper : ∀ l : Fin (nZ X ρ) → ℝ, (∀ k, ∃ z : ℤ, l k = z) → ∀ u, g (u + l) = g u`. Introduce `l hl u`. Use `choose n hn using hl`.

Establish `: l = fun i => (n i : ℝ)` using `funext hn`. Rewrite using `[this]`. Conclude with `maxCuspsA_periodic X cu hb la hchi P hsec x hx u n`. Establish `hcomp : dotForm 1 (phZ X cu χ) ∘ₗ L = dotForm 2 ν`. Use `LinearMap.ext fun s => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, dotForm_apply, dotForm_apply, one_mul, hL2 χ hχ.1 s]`. Establish `hfreq : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k`. Introduce `p hp`. Use `choose n hn using hL3 la p hp`. Use `choose m hm using hχ.2`.

Use `⟨∑ k, m k * n k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hL2 χ hχ.1 p]`. Simplify using `only [hn, hm]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hex` using `PeriodLatticeCountable.fd_exists X la`. Take `⟨-, hD, h0, h1⟩` from `hex.choose_spec`. Take `⟨H₁, -, -⟩` from `partialCoeff_spec_cube (Pi.basisFun ℝ (Fin (nZ X ρ))) hD h0.ne' h1.ne L hgc (fun i => hper _ fun k => ⟨if k = i then 1 else 0, by`. Apply the tactic sequence `by_cases h : k = i <;> simp [h]⟩)`. Use the proof step `(fun l hl => hper _ (hL3 la l hl))`.

Take `⟨-, -, -, B⟩` from `H₁ (dotForm 2 ν) hfreq`. Rewrite using `[coefFn_eq_cubeCoeff]`. Use `B.1 ?_ _ (fun i => ?_) hcomp` and prove the remaining obligations. Use function extensionality and compare the values at `b`. Establish `h` using `hP _ (hdom b)`.

Rewrite `h` using `[Data.fj, if_pos hfreq, dif_pos hex]`. Rewrite using `[partialCoeff, coeff_eq, Pi.zero_apply, ← h]`. Use `congr 2`. Use function extensionality and compare the values at `s`. Rewrite using `[hL1, maxCuspsA_zAct_add, add_comm (L s), dotForm_apply]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨z, hz⟩` from `hχ.2 i`. Conclude with `⟨z, by simp [dotForm_apply, Pi.single_apply, hz]⟩`.
-/
theorem coefFn_eq_zero_of_fj (X : Data E r) (cu : CuspFD X ρ) (hbas : ∃ bs, IsZBasis X cu bs) (la : Wt X.Ψ r)
    (hchi : ∀ β ∈ zGam X cu, ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1)
    (P : Frame X.Ψ r → ℂ) (hsec : X.IsSec la P) (χ : Matrix (Fin ρ) (Fin ρ) E) (hχ : IsExpoFD X cu χ)
    (η : Fin ρ → E) (hηΛ : (∑ a, η a • cu.e a) ∈ X.Λ)
    (hP : ∀ y ∈ X.dom, X.fj la (∑ a, η a • cu.e a) (fun τ => (τ.1 (hq χ η)).re) P y = 0) :
    ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0 := by
  intro x hx
  have hb : IsZBasis X cu (zBas X cu) := Classical.epsilon_spec hbas
  have hdom : ∀ u, zAct X cu u x ∈ X.dom := fun u =>
    zAct_mem_dom X cu (zBas_skew X cu hbas) u x hx
  obtain ⟨L, hL1, hL2, hL3⟩ := GlobalTheory.T.cuspFlow_eq_torusAction E r ρ X cu hb η hηΛ
  set ν : X.Ψ → ℝ := fun τ => (τ.1 (hq χ η)).re with hν
  set g : (Fin (nZ X ρ) → ℝ) → ℂ := fun t => P (zAct X cu t x) with hg
  have hgc : Continuous g := hsec.1.continuousOn.comp_continuous (continuous_zAct X cu x) hdom
  have hper : ∀ l : Fin (nZ X ρ) → ℝ, (∀ k, ∃ z : ℤ, l k = z) → ∀ u, g (u + l) = g u := by
    intro l hl u
    choose n hn using hl
    have : l = fun i => (n i : ℝ) := funext hn
    rw [this]
    exact maxCuspsA_periodic X cu hb la hchi P hsec x hx u n
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
    have h := hP _ (hdom b)
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

/- English proof (translation)
Establish `h1 : ∀ a b, IsCMField.complexConj E (χ a b) = χ b a` using `hχ`. Simplify using `only [hq, cc, map_sum, map_mul, h1, IsCMField.complexConj_apply_apply]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hq_real {χ : Matrix (Fin ρ) (Fin ρ) E} (hχ : IsHermE χ) (η : Fin ρ → E) : cc (hq χ η) = hq χ η := by
  have h1 : ∀ a b, IsCMField.complexConj E (χ a b) = χ b a := hχ
  simp only [hq, cc, map_sum, map_mul, h1, IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `only [hq, cc, Pi.smul_apply, smul_eq_mul, map_mul, map_intCast, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hq_zsmul (χ : Matrix (Fin ρ) (Fin ρ) E) (n : ℤ) (η : Fin ρ → E) :
    hq χ ((n : E) • η) = (n : E) ^ 2 * hq χ η := by
  simp only [hq, cc, Pi.smul_apply, smul_eq_mul, map_mul, map_intCast, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Establish `key : ∀ η : Fin ρ → E, η ≠ 0 → (∑ a, η a • cu.e a) ∈ X.Λ → ∀ τ : X.Ψ, 0 < (τ.1 (hq χ η)).re`. Introduce `η hη0 hηΛ τ`. Establish `hiso : X.IsIso (∑ a, η a • cu.e a)` using `⟨hηΛ, herm_comb cu η, fun h => hη0 (funext (Fintype.linearIndependent_iff.1 cu.ind η h))⟩`. Establish `h1 : ∃ y ∈ X.dom, X.fj la (∑ a, η a • cu.e a) (fun τ => (τ.1 (hq χ η)).re) P y ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hne (coefFn_eq_zero_of_fj X cu hbas la hchi P hP.1.1 χ hχ η hηΛ h x hx)`. Take `⟨y, hy, hfj⟩` from `h1`. Establish `hnn` using `BoundedSectionAlgebra.sign_of_bdd X moderateCoefficientPositivity_holds hP.1 hiso _ hy hfj τ`. Use `lt_of_le_of_ne hnn fun h0 => ?_` and prove the remaining obligations.

Establish `hre : (starRingEnd ℂ) (τ.1 (hq χ η)) = τ.1 (hq χ η)`. Rewrite using `[← emb_cc', hq_real hχ.1]`. Establish `hz : hq χ η = 0`. Apply `τ.1.injective` to reduce the goal to its premises. Rewrite using `[map_zero, ← Complex.conj_eq_iff_re.1 hre, ← h0, Complex.ofReal_zero]`.

Apply `hfj` to reduce the goal to its premises. Establish `: (fun τ : X.Ψ => (τ.1 (hq χ η)).re) = 0` using `by funext τ; simp [hz]`. Rewrite using `[this]`. Conclude with `hP.2 _ hiso y hy`. Take `⟨n, hn0, hn⟩` from `GlobalTheory.MaxCusp.exists_smul_mem X (∑ a, η a • cu.e a)`.

Establish `hn' : (n : E) ≠ 0` using `Int.cast_ne_zero.2 hn0`. Establish `key2 : ∀ τ : X.Ψ, 0 < (τ.1 (hq χ η)).re`. Introduce `τ`. Establish `h` using `key ((n : E) • η) (smul_ne_zero hn' hη) (by simpa [Finset.smul_sum, smul_smul] using hn) τ`. Rewrite `h` using `[hq_zsmul, map_mul, map_pow, map_intCast, ← Complex.ofReal_intCast, ← Complex.ofReal_pow, Complex.re_ofReal_mul]`.

Conclude with `pos_of_mul_pos_left (by rwa [mul_comm] at h) (sq_nonneg _)`. Distinguish the cases in `hσ : σ ∈ X.Ψ`. Conclude with `key2 ⟨σ, hσ⟩`. Establish `h2 : ComplexEmbedding.conjugate σ ∈ X.Ψ`. Assume the negation of the conclusion as `h`.

Conclude with `hσ ((X.cmType σ).2 h)`. Simplify using `using key2 ⟨_, h2⟩`.
-/
theorem posDef_of_coefFn_ne_zero (X : Data E r) (cu : CuspFD X ρ) (hbas : ∃ bs, IsZBasis X cu bs) (la : Wt X.Ψ r)
    (hchi : ∀ β ∈ zGam X cu, ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1)
    (P : Frame X.Ψ r → ℂ) (hP : P ∈ X.SS la) (χ : Matrix (Fin ρ) (Fin ρ) E) (hχ : IsExpoFD X cu χ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hne : coefFn (zAct X cu) (phZ X cu χ) P x ≠ 0)
    (η : Fin ρ → E) (hη : η ≠ 0) (σ : E →+* ℂ) : 0 < (σ (hq χ η)).re := by
  have key : ∀ η : Fin ρ → E, η ≠ 0 → (∑ a, η a • cu.e a) ∈ X.Λ → ∀ τ : X.Ψ, 0 < (τ.1 (hq χ η)).re := by
    intro η hη0 hηΛ τ
    have hiso : X.IsIso (∑ a, η a • cu.e a) :=
      ⟨hηΛ, herm_comb cu η, fun h => hη0 (funext (Fintype.linearIndependent_iff.1 cu.ind η h))⟩
    have h1 : ∃ y ∈ X.dom, X.fj la (∑ a, η a • cu.e a) (fun τ => (τ.1 (hq χ η)).re) P y ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (coefFn_eq_zero_of_fj X cu hbas la hchi P hP.1.1 χ hχ η hηΛ h x hx)
    obtain ⟨y, hy, hfj⟩ := h1
    have hnn := BoundedSectionAlgebra.sign_of_bdd X moderateCoefficientPositivity_holds hP.1 hiso _ hy hfj τ
    refine lt_of_le_of_ne hnn fun h0 => ?_
    have hre : (starRingEnd ℂ) (τ.1 (hq χ η)) = τ.1 (hq χ η) := by
      rw [← emb_cc', hq_real hχ.1]
    have hz : hq χ η = 0 := by
      apply τ.1.injective
      rw [map_zero, ← Complex.conj_eq_iff_re.1 hre, ← h0, Complex.ofReal_zero]
    apply hfj
    have : (fun τ : X.Ψ => (τ.1 (hq χ η)).re) = 0 := by funext τ; simp [hz]
    rw [this]
    exact hP.2 _ hiso y hy
  obtain ⟨n, hn0, hn⟩ := GlobalTheory.MaxCusp.exists_smul_mem X (∑ a, η a • cu.e a)
  have hn' : (n : E) ≠ 0 := Int.cast_ne_zero.2 hn0
  have key2 : ∀ τ : X.Ψ, 0 < (τ.1 (hq χ η)).re := by
    intro τ
    have h := key ((n : E) • η) (smul_ne_zero hn' hη) (by simpa [Finset.smul_sum, smul_smul] using hn) τ
    rw [hq_zsmul, map_mul, map_pow, map_intCast, ← Complex.ofReal_intCast, ← Complex.ofReal_pow,
      Complex.re_ofReal_mul] at h
    exact pos_of_mul_pos_left (by rwa [mul_comm] at h) (sq_nonneg _)
  by_cases hσ : σ ∈ X.Ψ
  · exact key2 ⟨σ, hσ⟩
  · have h2 : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      by_contra h; exact hσ ((X.cmType σ).2 h)
    simpa using key2 ⟨_, h2⟩

/- English proof (translation)
Establish `hb : IsZBasis X cu (zBas X cu)` using `Classical.epsilon_spec hbas`. Use `and_congr_right' ⟨fun h β hβ => ?_, fun h k => h _ ((hb.2 _).2 (Submodule.subset_span ⟨k, rfl⟩))⟩` and prove the remaining obligations. Rewrite `hβ` using `[hb.2]`. Set `φ : Matrix (Fin ρ) (Fin ρ) E →+ ℝ` to `AddMonoidHom.mk' (prE X χ) fun a b => by`. Simplify using `[prE, Matrix.mul_add, add_div, Finset.sum_add_distrib]`.

Express the relevant statement in the definitionally equal form `∃ n : ℤ, φ β = n`. Proceed by induction on `hβ using Submodule.span_induction with`. Consider the case `mem v hv => obtain ⟨k, rfl⟩ := hv`. Conclude with `h k`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨m, hm⟩` from `ha`. Take `⟨n, hn⟩` from `hb`. Conclude with `⟨m + n, by rw [map_add, hm, hn]; push_cast; rfl⟩`. Consider the case `smul c a _ ha`.

Take `⟨m, hm⟩` from `ha`. Conclude with `⟨c * m, by rw [map_zsmul, hm]; simp⟩`.
-/
theorem isExpoFD_iff (X : Data E r) (cu : CuspFD X ρ) (hbas : ∃ bs, IsZBasis X cu bs)
    (χ : Matrix (Fin ρ) (Fin ρ) E) :
    IsExpoFD X cu χ ↔ IsHermE χ ∧ ∀ β ∈ zGam X cu, ∃ n : ℤ, prE X χ β = n := by
  have hb : IsZBasis X cu (zBas X cu) := Classical.epsilon_spec hbas
  refine and_congr_right' ⟨fun h β hβ => ?_, fun h k => h _ ((hb.2 _).2 (Submodule.subset_span ⟨k, rfl⟩))⟩
  rw [hb.2] at hβ
  let φ : Matrix (Fin ρ) (Fin ρ) E →+ ℝ := AddMonoidHom.mk' (prE X χ) fun a b => by
    simp [prE, Matrix.mul_add, add_div, Finset.sum_add_distrib]
  change ∃ n : ℤ, φ β = n
  induction hβ using Submodule.span_induction with
  | mem v hv => obtain ⟨k, rfl⟩ := hv; exact h k
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, by rw [map_add, hm, hn]; push_cast; rfl⟩
  | smul c a _ ha =>
    obtain ⟨m, hm⟩ := ha
    exact ⟨c * m, by rw [map_zsmul, hm]; simp⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨a, ha, x, hx, h⟩` from `hv`.

Take `⟨a', rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Rewrite using `[← h]`. Conclude with `X.Λ.smul_mem a' hx.1`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Simplify using `only [Pi.add_apply, add_smul, Finset.sum_add_distrib]`. Conclude with `X.Λ.add_mem hx hy`. Consider the case `smul c x _ hx`. Establish `: (∑ i, (c • x) i • cu.e i) = c • ∑ i, x i • cu.e i`. Simplify using `[Finset.smul_sum, smul_assoc]`.

Rewrite using `[this]`. Conclude with `X.Λ.smul_mem c hx`. Introduce `hv`. Use `Submodule.subset_span ⟨1, (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩, _, Submodule.mem_inf.2 ⟨hv, ?_⟩, one_smul _ _⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem mem_crdI_one_iff (X : Data E r) (cu : CuspFD X ρ) (v : Fin ρ → E) :
    v ∈ crdI 1 cu ↔ (∑ i, v i • cu.e i) ∈ X.Λ := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, x, hx, h⟩ := hv
      obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      rw [← h]
      exact X.Λ.smul_mem a' hx.1
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      exact X.Λ.add_mem hx hy
    | smul c x _ hx =>
      have : (∑ i, (c • x) i • cu.e i) = c • ∑ i, x i • cu.e i := by
        simp [Finset.smul_sum, smul_assoc]
      rw [this]
      exact X.Λ.smul_mem c hx
  · intro hv
    refine Submodule.subset_span ⟨1, (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩, _,
      Submodule.mem_inf.2 ⟨hv, ?_⟩, one_smul _ _⟩
    rw [Submodule.restrictScalars_mem]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Free

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[WeightFamilies.emb_conj, FJ.emb_cc']`. Both sides reduce to the same expression.
-/
theorem cc_eq_conj (D : D7) (z : D.host.E) : FD.cc z = D.host.conj z := by
  apply D.host.φ₀.injective
  rw [WeightFamilies.emb_conj, FJ.emb_cc']
  rfl

/- English proof (translation)
Simplify using `only [WeightFamilies.hform, hq, cc_eq_conj]`.
-/
theorem hform_eq_hq (D : D7) {n : ℕ} (χ : Matrix (Fin n) (Fin n) D.host.E) (η : Fin n → D.host.E) :
    WeightFamilies.hform D χ η η = hq χ η := by
  simp only [WeightFamilies.hform, hq, cc_eq_conj]

/- English proof (translation)
Use `Fintype.sum_bijective (fun t => (⟨DV.tauEmb D t, hX t⟩ : X.Ψ)) ⟨fun s t hst => ?_, fun τ => ?_⟩ _ _ fun _ => rfl` and prove the remaining obligations. Establish `h1 : DV.tauEmb D s = DV.tauEmb D t` using `congrArg Subtype.val hst`. Conclude with `D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h1))`. Take `⟨g, hg⟩` from `(factEmb D.R D.host).1.2 τ.1`. Distinguish the cases in `hP : g ∈ D.R.Psi`.

Take `⟨t, ht⟩` from `(Formalism.L2.Geo.exists_tauEmb_iff D g).2 hP`. Conclude with `⟨t, Subtype.ext (by rw [← hg, ht])⟩`. Rewrite `hP` using `[Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem, not_not]`. Take `⟨t, ht⟩` from `(Formalism.L2.Geo.exists_tauEmb_iff D _).2 hP`. Use `absurd ?_ ((X.cmType τ.1).1 τ.2)` and prove the remaining obligations.

Establish `: ComplexEmbedding.conjugate τ.1 = DV.tauEmb D t`. Rewrite using `[← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg]`. Use extensionality with `z`. Conclude with `(WeightFamilies.emb_conj D τ.1 z).symm`. Rewrite using `[this]`.

Conclude with `hX t`.
-/
theorem trF_eq_sum (D : D7) {r : ℕ} (X : Data D.host.E r) (hX : ∀ t, DV.tauEmb D t ∈ X.Ψ) (z : D.host.E) :
    WeightFamilies.trF D z = ∑ τ : X.Ψ, (τ.1 z).re := by
  refine Fintype.sum_bijective (fun t => (⟨DV.tauEmb D t, hX t⟩ : X.Ψ)) ⟨fun s t hst => ?_, fun τ => ?_⟩ _ _
    fun _ => rfl
  · have h1 : DV.tauEmb D s = DV.tauEmb D t := congrArg Subtype.val hst
    exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h1))
  · obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ.1
    by_cases hP : g ∈ D.R.Psi
    · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hP
      exact ⟨t, Subtype.ext (by rw [← hg, ht])⟩
    · rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem, not_not] at hP
      obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D _).2 hP
      refine absurd ?_ ((X.cmType τ.1).1 τ.2)
      have : ComplexEmbedding.conjugate τ.1 = DV.tauEmb D t := by
        rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg]
        ext z
        exact (WeightFamilies.emb_conj D τ.1 z).symm
      rw [this]
      exact hX t

/- English proof (translation)
Introduce `D T h j ka CR Tt c hj hjm F`. Establish `hF : F.1 ∈ T.C j ka` using `cutR_le T.C j ka F.2`. Establish `hSS : ∀ k, rdU (T.U j T.σ₀) F.1 k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA ka) ka.n k)` using `abelian₂.holSub_SS siegelSpaceAlgebra_holds _ _ (((mem_cusp _ _ _ _ _ _).1 hF).2 T.σ₀ T.good_σ₀)`. Use `⟨hSS, ?_⟩` and prove the remaining obligations. Establish `hbas : ∀ k (cu : FJ.CuspFD (T.X₀ j k) (WeightFamilies.rho D j)), ∃ bs, FJ.IsZBasis (T.X₀ j k) cu bs` using `fun k cu => h.latZ j hj ⟨k, cu⟩`.

Establish `hchi : ∀ k, ∀ γ ∈ (T.X₀ j k).Γ, (T.X₀ j k).χ (laU (T.U j T.σ₀) (wtA ka) ka.n k) γ = 1` using `fun k => h.chiTriv j hj T.σ₀ T.good_σ₀ _ _ (dom_wtA ka) k`. Establish `hΨ : ∀ k t, DV.tauEmb D t ∈ (T.X₀ j k).Ψ` using `fun k t => (((h.unf j hj T.σ₀ T.good_σ₀).2.1 k).2 _).2 (h.pins.1.2.2.2 t)`. Establish `hspan : ∀ k ξ, (T.X₀ j k).IsIso ξ → ∃ cu : FJ.CuspFD (T.X₀ j k) (WeightFamilies.rho D j), ξ ∈ Submodule.span D.host.E (Set.range cu.e)`. Introduce `k ξ hξ`. Take `⟨cu⟩` from `h.cuNe j hj k`.

Take `⟨n, hn⟩ : ∃ n, WeightFamilies.rho D j = n + 1` from `⟨D.R.m - j - 1, by show D.R.m - j = _ omega⟩`. Use `revert cu`. Rewrite using `[hn]`. Conclude with `fun cu => exists_cusp_mem _ cu hξ.2.2 hξ.2.1`. Establish `hmain` using `fun k => GlobalTheory.maxCusps_iff_killed_coeff_vanish D.host.E D.R.r (WeightFamilies.rho D j) (T.X₀ j k) (hspan k) (hbas k) (laU (T.U j T.σ₀) (wtA ka) ka.n k) (fun _ _ _ γ hγ _ => hchi k γ hγ) (WeightFamilies.c1 D CR Tt c j) _ (hSS k)`.

Establish `hherm : ∀ χ : Matrix (Fin (WeightFamilies.rho D j)) (Fin (WeightFamilies.rho D j)) D.host.E, WeightFamilies.IsHerm D χ ↔ FJ.IsHermE χ` using `fun χ => forall_congr' fun a => forall_congr' fun b => by rw [cc_eq_conj, eq_comm]`. Establish `hexpo : ∀ (cu : T.Cu j) χ, IsExpoFD (T.X₀ j cu.1.1) cu.1.2 χ ↔ WeightFamilies.IsHerm D χ ∧ WeightFamilies.IntOn D (T.Xc j cu) χ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E)`. Introduce `cu χ`. Rewrite using `[isExpoFD_iff _ _ (hbas _ _), hherm]`. Use `and_congr_right fun hχ => ?_` and prove the remaining obligations.

Rewrite using `[h.expo j hj cu.1 χ hχ]`. Simplify using `only [cc_eq_conj]`. Both sides reduce to the same expression. Establish `hkill : ∀ (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)), WeightFamilies.Killed (recB h) CR Tt c (j` using `j) cu χ ↔ KilledFD (T.X₀ j cu.1.1) cu.1.2 χ.1 (WeightFamilies.c1 D CR Tt c j) := by`. Introduce `cu χ`.

Use `exists_congr fun η => ?_` and prove the remaining obligations. Establish `h1 : η ∈ WeightFamilies.dualZ D (T.Xc j cu) ↔ (∑ i, η i • cu.1.2.e i) ∈ (T.X₀ j cu.1.1).Λ`. Rewrite using `[maxCuspsTieStatement_holds D T j cu, SetLike.mem_coe, mem_crdI_one_iff]`. Rewrite using `[← h1, ← trF_eq_sum D _ (hΨ _), ← hform_eq_hq]`. Conclude with `and_left_comm`.

Establish `hsg : ∀ (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)), (recB h).sg j cu χ ka F = 0 ↔ ∀ x ∈ (T.X₀ j cu.1.1).dom, FJ.coefFn (FJ.zAct _ cu.1.2) (FJ.phZ _ cu.1.2 χ.1) (rdU (T.U j T.σ₀) F.1 cu.1.1) x = 0`. Introduce `cu χ`. Establish `e : ((recB h).sg j cu χ ka F : Frame (T.X₀ j cu.1.1).Ψ D.R.r → ℂ) = fun x => open Classical in if x ∈ (T.X₀ j cu.1.1).dom then FJ.coefFn (FJ.zAct _ cu.1.2) (FJ.phZ _ cu.1.2 χ.1) (rdU (T.U j T.σ₀) F.1 cu.1.1) x else 0` using `rfl`. Prove the components needed by the constructor for the conclusion. Introduce `h0 x hx`.

Use `congrFun (e.symm.trans h0) x` as an intermediate fact. Rewrite `this` using `[if_pos hx]`. Then use the resulting hypothesis. Introduce `h0`. Use `e.trans (funext fun x => ?_)` and prove the remaining obligations. Use `split_ifs with hx`.

Conclude with `h0 x hx`. Both sides reduce to the same expression. Simplify using `only [WeightFamilies.MggK, Submodule.mem_iInf, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `H k`.

Use `(hmain k).2 fun cu χ hχ hK x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Set `cu' : T.Cu j` to `⟨⟨k, cu⟩, hj⟩`. Establish `h1` using `(hexpo cu' χ).1 hχ`. Establish `hpos : WeightFamilies.PosDefE D χ` using `fun l hl σ => by`.

Rewrite using `[hform_eq_hq]`. Conclude with `posDef_of_coefFn_ne_zero _ cu (hbas k cu) _ (fun _ _ γ hγ _ => hchi k γ hγ) _ (hSS k) χ hχ hx hne l hl σ`. Set `χ' : WeightFamilies.ExpoSet D (T.Xc j cu')` to `⟨χ, h1.1, hpos, h1.2⟩`. Conclude with `hne ((hsg cu' χ').1 (H cu' χ' ((hkill cu' χ').2 hK)) x hx)`. Introduce `H cu χ hK`.

Conclude with `(hsg cu χ).2 ((hmain cu.1.1).1 (H _) cu.1.2 χ.1 ((hexpo cu χ.1).2 ⟨χ.2.1, χ.2.2.2⟩) ((hkill cu χ).1 hK))`.
-/
theorem mem_iff_low_coeff_vanish : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), InR D j → j < D.R.m → ∀ F : (recB h).Cusp j ka, (∀ k, rdU (T.U j T.σ₀) F.1 k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA ka) ka.n k)) ∧ (F ∈ WeightFamilies.MggK (recB h) CR Tt cc j ka ↔ ∀ k, rdU (T.U j T.σ₀) F.1 k ∈ ((T.U j T.σ₀).X k).SSgt (laU (T.U j T.σ₀) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt cc j)) := by
  intro D T h j ka CR Tt c hj hjm F
  have hF : F.1 ∈ T.C j ka := cutR_le T.C j ka F.2
  have hSS : ∀ k, rdU (T.U j T.σ₀) F.1 k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA ka) ka.n k) :=
    abelian₂.holSub_SS siegelSpaceAlgebra_holds _ _ (((mem_cusp _ _ _ _ _ _).1 hF).2 T.σ₀ T.good_σ₀)
  refine ⟨hSS, ?_⟩
  have hbas : ∀ k (cu : FJ.CuspFD (T.X₀ j k) (WeightFamilies.rho D j)), ∃ bs, FJ.IsZBasis (T.X₀ j k) cu bs :=
    fun k cu => h.latZ j hj ⟨k, cu⟩
  have hchi : ∀ k, ∀ γ ∈ (T.X₀ j k).Γ, (T.X₀ j k).χ (laU (T.U j T.σ₀) (wtA ka) ka.n k) γ = 1 :=
    fun k => h.chiTriv j hj T.σ₀ T.good_σ₀ _ _ (dom_wtA ka) k
  have hΨ : ∀ k t, DV.tauEmb D t ∈ (T.X₀ j k).Ψ := fun k t =>
    (((h.unf j hj T.σ₀ T.good_σ₀).2.1 k).2 _).2 (h.pins.1.2.2.2 t)
  have hspan : ∀ k ξ, (T.X₀ j k).IsIso ξ → ∃ cu : FJ.CuspFD (T.X₀ j k) (WeightFamilies.rho D j),
      ξ ∈ Submodule.span D.host.E (Set.range cu.e) := by
    intro k ξ hξ
    obtain ⟨cu⟩ := h.cuNe j hj k
    obtain ⟨n, hn⟩ : ∃ n, WeightFamilies.rho D j = n + 1 := ⟨D.R.m - j - 1, by
      show D.R.m - j = _
      omega⟩
    revert cu
    rw [hn]
    exact fun cu => exists_cusp_mem _ cu hξ.2.2 hξ.2.1
  have hmain := fun k => GlobalTheory.maxCusps_iff_killed_coeff_vanish D.host.E D.R.r (WeightFamilies.rho D j) (T.X₀ j k) (hspan k)
    (hbas k) (laU (T.U j T.σ₀) (wtA ka) ka.n k) (fun _ _ _ γ hγ _ => hchi k γ hγ) (WeightFamilies.c1 D CR Tt c j) _ (hSS k)
  have hherm : ∀ χ : Matrix (Fin (WeightFamilies.rho D j)) (Fin (WeightFamilies.rho D j)) D.host.E,
      WeightFamilies.IsHerm D χ ↔ FJ.IsHermE χ := fun χ =>
    forall_congr' fun a => forall_congr' fun b => by rw [cc_eq_conj, eq_comm]
  have hexpo : ∀ (cu : T.Cu j) χ, IsExpoFD (T.X₀ j cu.1.1) cu.1.2 χ ↔
      WeightFamilies.IsHerm D χ ∧ WeightFamilies.IntOn D (T.Xc j cu) χ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) := by
    intro cu χ
    rw [isExpoFD_iff _ _ (hbas _ _), hherm]
    refine and_congr_right fun hχ => ?_
    rw [h.expo j hj cu.1 χ hχ]
    simp only [cc_eq_conj]
    rfl
  have hkill : ∀ (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)), WeightFamilies.Killed (recB h) CR Tt c (j := j) cu χ ↔
      KilledFD (T.X₀ j cu.1.1) cu.1.2 χ.1 (WeightFamilies.c1 D CR Tt c j) := by
    intro cu χ
    refine exists_congr fun η => ?_
    have h1 : η ∈ WeightFamilies.dualZ D (T.Xc j cu) ↔ (∑ i, η i • cu.1.2.e i) ∈ (T.X₀ j cu.1.1).Λ := by
      rw [maxCuspsTieStatement_holds D T j cu, SetLike.mem_coe, mem_crdI_one_iff]
    rw [← h1, ← trF_eq_sum D _ (hΨ _), ← hform_eq_hq]
    exact and_left_comm
  have hsg : ∀ (cu : T.Cu j) (χ : WeightFamilies.ExpoSet D (T.Xc j cu)), (recB h).sg j cu χ ka F = 0 ↔
      ∀ x ∈ (T.X₀ j cu.1.1).dom, FJ.coefFn (FJ.zAct _ cu.1.2) (FJ.phZ _ cu.1.2 χ.1)
        (rdU (T.U j T.σ₀) F.1 cu.1.1) x = 0 := by
    intro cu χ
    have e : ((recB h).sg j cu χ ka F : Frame (T.X₀ j cu.1.1).Ψ D.R.r → ℂ) = fun x =>
        open Classical in if x ∈ (T.X₀ j cu.1.1).dom then FJ.coefFn (FJ.zAct _ cu.1.2) (FJ.phZ _ cu.1.2 χ.1)
        (rdU (T.U j T.σ₀) F.1 cu.1.1) x else 0 := rfl
    constructor
    · intro h0 x hx
      have := congrFun (e.symm.trans h0) x
      rwa [if_pos hx] at this
    · intro h0
      refine e.trans (funext fun x => ?_)
      split_ifs with hx
      · exact h0 x hx
      · rfl
  simp only [WeightFamilies.MggK, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro H k
    refine (hmain k).2 fun cu χ hχ hK x hx => ?_
    by_contra hne
    let cu' : T.Cu j := ⟨⟨k, cu⟩, hj⟩
    have h1 := (hexpo cu' χ).1 hχ
    have hpos : WeightFamilies.PosDefE D χ := fun l hl σ => by
      rw [hform_eq_hq]
      exact posDef_of_coefFn_ne_zero _ cu (hbas k cu) _ (fun _ _ γ hγ _ => hchi k γ hγ) _ (hSS k) χ hχ hx hne l hl σ
    let χ' : WeightFamilies.ExpoSet D (T.Xc j cu') := ⟨χ, h1.1, hpos, h1.2⟩
    exact hne ((hsg cu' χ').1 (H cu' χ' ((hkill cu' χ').2 hK)) x hx)
  · intro H cu χ hK
    exact (hsg cu χ).2 ((hmain cu.1.1).1 (H _) cu.1.2 χ.1 ((hexpo cu χ.1).2 ⟨χ.2.1, χ.2.2.2⟩) ((hkill cu χ).1 hK))

end GlobalTheory.LowCoeff
