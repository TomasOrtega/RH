import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLocalDimUpperZariski
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsContainOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearFormCut
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

/- English proof (translation)
Set `_` to `f.toAlgebra`. Establish `: Module.Finite R S` using `hf`. Establish `: Algebra.IsIntegral R S` using `Algebra.IsIntegral.of_finite R S`. Use `Order.krullDim_le_of_strictMono (fun p : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) p) ?_` and prove the remaining obligations. Introduce `p p' h`.

Establish `h' : p.asIdeal < p'.asIdeal` using `h`. Conclude with `Ideal.IsIntegral.comap_lt_comap (R := R) h'`.
-/
theorem SliceLocalDimUpperZariski.ringKrullDim_le_of_finite {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) : ringKrullDim S ≤ ringKrullDim R := by
  let _ := f.toAlgebra
  have : Module.Finite R S := hf
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  refine Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) p) ?_
  intro p p' h
  have h' : p.asIdeal < p'.asIdeal := h
  exact Ideal.IsIntegral.comap_lt_comap (R := R) h'

/- English proof (translation)
Use `set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)`. Establish `hIM : I ≤ M` using `fun f hf => RingHom.mem_ker.mpr (hq f hf)`. Set `m : Ideal (MvPolynomial (Fin n) ℂ ⧸ I)` to `M.map (Ideal.Quotient.mk I)`. Establish `hm : m.IsMaximal` using `Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIM)`. Establish `hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ I) M.primeCompl = m.primeCompl`.

Use extensionality with `x`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hzy⟩`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I y ∉ m`.

Rewrite using `[← hzy]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I z ∉ M.map (Ideal.Quotient.mk I)`. Rewrite using `[Ideal.mem_quotient_iff_mem hIM]`. Conclude with `hz`. Introduce `h`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I y ∉ M.map (Ideal.Quotient.mk I) at h`. Rewrite `h` using `[Ideal.mem_quotient_iff_mem hIM]`. Conclude with `⟨y, h, rfl⟩`. Establish `: m.IsPrime` using `hm.isPrime`. Establish `: IsLocalization.AtPrime (localRingAt I q) m`.

Unfold `IsLocalization.AtPrime`. Rewrite using `[← hsub]`. Unfold `localRingAt`. Use `infer_instance`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt I q)]`.

Conclude with `Ideal.height_le_ringKrullDim_of_isPrime`.
-/
theorem SliceLocalDimUpperZariski.localDim_le {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (q : Fin n → ℂ) (hq : q ∈ zeroSet I) :
    ringKrullDim (localRingAt I q) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) := by
  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hIM : I ≤ M := fun f hf => RingHom.mem_ker.mpr (hq f hf)
  let m : Ideal (MvPolynomial (Fin n) ℂ ⧸ I) := M.map (Ideal.Quotient.mk I)
  have hm : m.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIM)
  have hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ I) M.primeCompl =
      m.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      change Ideal.Quotient.mk I y ∉ m
      rw [← hzy]
      change Ideal.Quotient.mk I z ∉ M.map (Ideal.Quotient.mk I)
      rw [Ideal.mem_quotient_iff_mem hIM]
      exact hz
    · intro h
      change Ideal.Quotient.mk I y ∉ M.map (Ideal.Quotient.mk I) at h
      rw [Ideal.mem_quotient_iff_mem hIM] at h
      exact ⟨y, h, rfl⟩
  have : m.IsPrime := hm.isPrime
  have : IsLocalization.AtPrime (localRingAt I q) m := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    unfold localRingAt
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt I q)]
  exact Ideal.height_le_ringKrullDim_of_isPrime

/- English proof (translation)
Use `set I := sliceIdeal J L q with hI`. Establish `hJI : J ≤ I` using `le_sup_left`. Set `g : MvPolynomial (Fin (d + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I` to `(Ideal.Quotient.factor hJI).comp (projHom J M).toRingHom`. Establish `hg : g.Finite` using `RingHom.Finite.comp (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJI)) hfin`. Set `π : MvPolynomial (Fin (d + 1)) ℂ →+* Polynomial ℂ` to `(aeval (Fin.lastCases (motive := fun _ => Polynomial ℂ) Polynomial.X (fun k => Polynomial.C ((L *ᵥ q) k)))).toRingHom`.

Set `ψ : Polynomial ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I` to `Polynomial.eval₂RingHom (algebraMap ℂ _) (Ideal.Quotient.mk I (linPoly M (Fin.last d)))`. Establish `hlin : ∀ k : Fin d, linPoly M k.castSucc = linPoly L k`. Introduce `k`. Simplify using `only [linPoly, hML]`. Establish `hCI : ∀ c : ℂ, algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) c = Ideal.Quotient.mk I (C c)` using `fun c => rfl`.

Establish `hcomp : ψ.comp π = g`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[π, ψ, g, projHom, pullback, hCI]`. Introduce `i`.

Use `Fin.lastCases ?_ (fun k => ?_) i` and prove the remaining obligations. Simplify using `[π, ψ, g, projHom, pullback]`. Establish `hmem : linPoly L k - C ((L *ᵥ q) k) ∈ I` using `Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)`. Establish `hq : Ideal.Quotient.mk I (linPoly L k) = Ideal.Quotient.mk I (C ((L *ᵥ q) k))` using `Ideal.Quotient.eq.mpr hmem`. Simplify using `[π, ψ, g, projHom, pullback, hlin, hq, hCI]`.

Establish `hψ : ψ.Finite` using `RingHom.Finite.of_comp_finite (f := π) (by rw [hcomp]; exact hg)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`. Both sides reduce to the same expression.
-/
theorem SliceLocalDimUpperZariski.quotient_dim_le_one {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) (M : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (hML : ∀ i j, M (Fin.castSucc i) j = L i j) (hfin : (projHom J M).toRingHom.Finite) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q) ≤ (1 : ℕ) := by
  set I := sliceIdeal J L q with hI
  have hJI : J ≤ I := le_sup_left
  let g : MvPolynomial (Fin (d + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    (Ideal.Quotient.factor hJI).comp (projHom J M).toRingHom
  have hg : g.Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJI)) hfin
  let π : MvPolynomial (Fin (d + 1)) ℂ →+* Polynomial ℂ :=
    (aeval (Fin.lastCases (motive := fun _ => Polynomial ℂ) Polynomial.X
      (fun k => Polynomial.C ((L *ᵥ q) k)))).toRingHom
  let ψ : Polynomial ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    Polynomial.eval₂RingHom (algebraMap ℂ _) (Ideal.Quotient.mk I (linPoly M (Fin.last d)))
  have hlin : ∀ k : Fin d, linPoly M k.castSucc = linPoly L k := by
    intro k
    simp only [linPoly, hML]
  have hCI : ∀ c : ℂ, algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) c = Ideal.Quotient.mk I (C c) :=
    fun c => rfl
  have hcomp : ψ.comp π = g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [π, ψ, g, projHom, pullback, hCI]
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp [π, ψ, g, projHom, pullback]
      · have hmem : linPoly L k - C ((L *ᵥ q) k) ∈ I :=
          Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
        have hq : Ideal.Quotient.mk I (linPoly L k) = Ideal.Quotient.mk I (C ((L *ᵥ q) k)) :=
          Ideal.Quotient.eq.mpr hmem
        simp [π, ψ, g, projHom, pullback, hlin, hq, hCI]
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (f := π) (by rw [hcomp]; exact hg)
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ringKrullDim (Polynomial ℂ) :=
        SliceLocalDimUpperZariski.ringKrullDim_le_of_finite ψ hψ
    _ = (1 : ℕ) := by
        rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        rfl

/- English proof (translation)
Introduce `n d J q hJ hdim hq`. Take `⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hWfin⟩` from `ComplexSets.FiniteProjectionsContainOpen.proof ComplexSets.ConeAvoidsFinite.proof ComplexSets.FiniteProjHomInjective.proof ComplexSets.ConeAvoidsOpen.proof (ComplexSets.ConeAvoidsExists.proof ComplexSets.LeadIdealDim.proof ComplexSets.LinearFormCut.proof ComplexSets.HomogDimZeroP …`. Rewrite `hA₀` using `[hS]`. Take `⟨G, hGS, hG⟩` from `hA₀`. Set `ext : Matrix (Fin d) (Fin n) ℂ → Matrix (Fin (d + 1)) (Fin n) ℂ` to `fun L i j => if h : (i : ℕ) < d then L ⟨i, h⟩ j else A₀ i j`.

Set `F : MvPolynomial (Fin d × Fin n) ℂ` to `bind₁ (fun ij : Fin (d + 1) × Fin n => if h : (ij.1 : ℕ) < d then X (⟨ij.1, h⟩, ij.2) else C (A₀ ij.1 ij.2)) G`. Establish `hevF : ∀ L : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F = eval (fun ij : Fin (d + 1) × Fin n => ext L ij.1 ij.2) G`. Introduce `L`. Express the relevant statement in the definitionally equal form `eval₂Hom (RingHom.id ℂ) _ (bind₁ _ G) = _`. Rewrite using `[eval₂Hom_bind₁]`.

Express the relevant statement in the definitionally equal form `eval _ G = _`. Use `congrArg (fun f => eval f G) (funext fun ij => ?_)` and prove the remaining obligations. Simplify using `only [ext]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hext0 : ext (fun i j => A₀ i.castSucc j) = A₀`.

Use function extensionality and compare the values at `i j`. Simplify using `only [ext]`. Use `split_ifs with h`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Use `⟨F, fun h0 => hG ?_, fun L hL => ?_⟩` and prove the remaining obligations. Establish `h1` using `hevF (fun i j => A₀ i.castSucc j)`. Rewrite `h1` using `[hext0, h0, map_zero]`. Conclude with `h1.symm`. Establish `hmem : ext L ∈ W`.

Rewrite using `[hS]`. Conclude with `⟨G, hGS, (hevF L) ▸ hL⟩`. Establish `hfp : IsFiniteProjection J (ext L)` using `hWfin hmem`. Establish `hq' : q ∈ zeroSet (sliceIdeal J L q)`. Rewrite using `[zeroSet_sliceIdeal]`.

Conclude with `⟨hq, rfl⟩`. Use `(SliceLocalDimUpperZariski.localDim_le _ q hq').trans (SliceLocalDimUpperZariski.quotient_dim_le_one J L q (ext L) (fun i j => ?_) hfp.finite)` and prove the remaining obligations. Simplify using `[ext, i.isLt]`.
-/
theorem SliceLocalDimUpperZariski.proof : SliceLocalDimUpperZariski.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hWfin⟩ :=
    ComplexSets.FiniteProjectionsContainOpen.proof ComplexSets.ConeAvoidsFinite.proof
      ComplexSets.FiniteProjHomInjective.proof ComplexSets.ConeAvoidsOpen.proof
      (ComplexSets.ConeAvoidsExists.proof ComplexSets.LeadIdealDim.proof
        ComplexSets.LinearFormCut.proof ComplexSets.HomogDimZeroPow.proof) n (d + 1) J hJ hdim
  rw [hS] at hA₀
  obtain ⟨G, hGS, hG⟩ := hA₀
  let ext : Matrix (Fin d) (Fin n) ℂ → Matrix (Fin (d + 1)) (Fin n) ℂ :=
    fun L i j => if h : (i : ℕ) < d then L ⟨i, h⟩ j else A₀ i j
  let F : MvPolynomial (Fin d × Fin n) ℂ :=
    bind₁ (fun ij : Fin (d + 1) × Fin n =>
      if h : (ij.1 : ℕ) < d then X (⟨ij.1, h⟩, ij.2) else C (A₀ ij.1 ij.2)) G
  have hevF : ∀ L : Matrix (Fin d) (Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F =
        eval (fun ij : Fin (d + 1) × Fin n => ext L ij.1 ij.2) G := by
    intro L
    change eval₂Hom (RingHom.id ℂ) _ (bind₁ _ G) = _
    rw [eval₂Hom_bind₁]
    change eval _ G = _
    refine congrArg (fun f => eval f G) (funext fun ij => ?_)
    simp only [ext]
    split_ifs <;> simp
  have hext0 : ext (fun i j => A₀ i.castSucc j) = A₀ := by
    funext i j
    simp only [ext]
    split_ifs with h
    · rfl
    · rfl
  refine ⟨F, fun h0 => hG ?_, fun L hL => ?_⟩
  · have h1 := hevF (fun i j => A₀ i.castSucc j)
    rw [hext0, h0, map_zero] at h1
    exact h1.symm
  · have hmem : ext L ∈ W := by
      rw [hS]
      exact ⟨G, hGS, (hevF L) ▸ hL⟩
    have hfp : IsFiniteProjection J (ext L) := hWfin hmem
    have hq' : q ∈ zeroSet (sliceIdeal J L q) := by
      rw [zeroSet_sliceIdeal]
      exact ⟨hq, rfl⟩
    refine (SliceLocalDimUpperZariski.localDim_le _ q hq').trans
      (SliceLocalDimUpperZariski.quotient_dim_le_one J L q (ext L) (fun i j => ?_) hfp.finite)
    simp [ext, i.isLt]

end

end GroundTheory.Heights₂.Heights
