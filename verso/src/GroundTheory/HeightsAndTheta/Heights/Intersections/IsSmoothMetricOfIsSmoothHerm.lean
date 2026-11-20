import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[MvPolynomial.map_map]`. Use `congr 1`.
-/
theorem map_rat_complex (f : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) :
    MvPolynomial.map (algebraMap ℚ ℂ) (MvPolynomial.map (Int.castRingHom ℚ) f) =
      MvPolynomial.map (Int.castRingHom ℂ) f := by
  rw [MvPolynomial.map_map]
  congr 1

omit [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `h : {w : MCone ι | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {w : MCone ι | w ⟨k, i⟩ ≠ 0}`. Use extensionality with `w`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const`.
-/
theorem isOpen_blockNonzero : IsOpen {w : MCone ι | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
  have h : {w : MCone ι | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {w : MCone ι | w ⟨k, i⟩ ≠ 0} := by
    ext w
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

omit [DecidableEq K] in

/- English proof (translation)
Introduce `z hz`. Use `⟨_, isOpen_blockNonzero.mem_nhds hz.1, logH L, ?_, fun w _ => rfl⟩` and prove the remaining obligations. Conclude with `h.log fun w hw => (L.pos w hw).ne'`.
-/
theorem isSmoothMetric_of_isSmoothHerm (P : Ideal (MRing ι ℂ)) (L : HLine ι)
    (h : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm L) : IsSmoothMetric P L := by
  intro z hz
  refine ⟨_, isOpen_blockNonzero.mem_nhds hz.1, logH L, ?_, fun w _ => rfl⟩
  exact h.log fun w hw => (L.pos w hw).ne'

/- English proof (translation)
Take `⟨-, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩` from `hP`. Use `hprime` as an intermediate fact. Establish `hch : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0`. Introduce `m hm`. Establish `hm' : m ∈ P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)` using `Ideal.mem_comap.mpr hm`.

Rewrite `hm'` using `[show P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) = ⊥ from hhor, Ideal.mem_bot]`. Conclude with `hm'`. Take `⟨hQ, hcomap, hd⟩` from `ReciprocityTheory.AnForm.R.extQ_spec P hch`. Use `⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mpr ⟨hQ, ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Take `⟨a, ha⟩` from `hS f hf`. Conclude with `⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩`. Rewrite using `[hPS, Ideal.map_span]`. Introduce `k`. Take `⟨i, hi⟩` from `hrel k`.

Use `⟨i, fun h => hi ?_⟩` and prove the remaining obligations. Rewrite using `[← hcomap, Ideal.mem_comap, MvPolynomial.map_X]`. Conclude with `h`. Establish `hd' : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) + 1 = ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Rewrite using `[← hdim]`.

Conclude with `hd`. Use `show ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)`. Generalize the expression as in `ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) = d at hd'`. Proceed by induction on `d using WithBot.recBotCoe with`. Consider the case `bot`.

Rewrite `hd'` using `[WithBot.bot_add]`. Conclude with `absurd hd' (WithBot.bot_ne_coe)`. Consider the case `coe d`. Proceed by induction on `d using ENat.recTopCoe with`. Consider the case `top`.

Establish `h3 : (⊤ : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞)` using `by exact_mod_cast hd'`. Rewrite `h3` using `[top_add]`. Conclude with `absurd h3.symm (ENat.natCast_ne_top _)`. Consider the case `coe n`. Establish `h1 : n + 1 = e + 1 + Fintype.card K` using `by exact_mod_cast hd'`.

Establish `h2 : n = e + Fintype.card K` using `by omega`. Rewrite using `[h2]`. Both sides reduce to the same expression.
-/
theorem isProjVarQ_of_isArithVar {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {e : ℕ}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) :
    IsProjVarQ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) e := by
  obtain ⟨-, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have := hprime
  have hch : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have hm' : m ∈ P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := Ideal.mem_comap.mpr hm
    rw [show P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) = ⊥ from hhor, Ideal.mem_bot] at hm'
    exact hm'
  obtain ⟨hQ, hcomap, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mpr
    ⟨hQ, ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, MvPolynomial.map_X]
    exact h
  · have hd' : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
        P.map (MvPolynomial.map (Int.castRingHom ℚ))) + 1 =
        ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← hdim]
      exact hd
    show ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
      ((e + Fintype.card K : ℕ) : WithBot ℕ∞)
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
      P.map (MvPolynomial.map (Int.castRingHom ℚ))) = d at hd'
    induction d using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.bot_add] at hd'
      exact absurd hd' (WithBot.bot_ne_coe)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        have h3 : (⊤ : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast hd'
        rw [top_add] at h3
        exact absurd h3.symm (ENat.natCast_ne_top _)
      | coe n =>
        have h1 : n + 1 = e + 1 + Fintype.card K := by exact_mod_cast hd'
        have h2 : n = e + Fintype.card K := by omega
        rw [h2]
        rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
