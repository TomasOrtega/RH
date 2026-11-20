import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesDominatesStalkOfRegular
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep.Centre

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/- English proof (translation)
Use `⟨by rintro _ ⟨a, rfl⟩; exact h.1 a, ?_⟩` and prove the remaining obligations. Introduce and unpack `f ⟨a, ha⟩ h0`. Establish `hinv : ((f⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring` using `(E.ord_nonneg_iff f⁻¹).1 (by rw [E.ord_inv, h0]; simp)`. Establish `hu : IsUnit a`. Assume the negation of the conclusion as `hu`.

Establish `h1` using `(E.ring.coe_mem_nonunits_iff (a := ⟨_, h.1 a⟩)).mp (h.2 a hu)`. Use `h1 (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap _ X.functionField a * _ = 1`. Rewrite using `[ha]`. Conclude with `f.mul_inv`.

Take `⟨u, rfl⟩` from `hu`. Use `⟨((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z), ?_⟩` and prove the remaining obligations. Establish `e : algebraMap _ X.functionField ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) * (f : X.functionField) = 1`. Rewrite using `[← ha, ← map_mul, Units.inv_mul, map_one]`. Conclude with `(Units.inv_eq_of_mul_eq_one_left e).symm`.
-/
theorem centreAt_of_dominatesStalk {E : DivOver p} {z : X} (h : DominatesStalk E.ring z) :
    CentreAt E z := by
  refine ⟨by rintro _ ⟨a, rfl⟩; exact h.1 a, ?_⟩
  rintro f ⟨a, ha⟩ h0
  have hinv : ((f⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring :=
    (E.ord_nonneg_iff f⁻¹).1 (by rw [E.ord_inv, h0]; simp)
  have hu : IsUnit a := by
    by_contra hu
    have h1 := (E.ring.coe_mem_nonunits_iff (a := ⟨_, h.1 a⟩)).mp (h.2 a hu)
    refine h1 (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_))
    change algebraMap _ X.functionField a * _ = 1
    rw [ha]
    exact f.mul_inv
  obtain ⟨u, rfl⟩ := hu
  refine ⟨((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z), ?_⟩
  have e : algebraMap _ X.functionField
      ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) * (f : X.functionField) = 1 := by
    rw [← ha, ← map_mul, Units.inv_mul, map_one]
  exact (Units.inv_eq_of_mul_eq_one_left e).symm

/- English proof (translation)
The claim follows from `have ⟨z, hz, hd⟩ := exists_specializes_dominatesStalk_of_regAt X E.ring x h ⟨z, hz, centreAt_of_dominatesStalk hd⟩`.
-/
theorem exists_centreAt {E : DivOver p} {x : X} (h : E.Through x) :
    ∃ z, z ⤳ x ∧ CentreAt E z :=
  have ⟨z, hz, hd⟩ := exists_specializes_dominatesStalk_of_regAt X E.ring x h
  ⟨z, hz, centreAt_of_dominatesStalk hd⟩

/- English proof (translation)
Take `⟨r, D₀, hr, -, rfl⟩` from `hD`. Take `⟨d, hd⟩` from `D₀.exists_isEqn x`. Take `⟨V, hV, hdV⟩` from `hd.exists_nhds`. Use `⟨m * r, g ^ r * d ^ m, Nat.mul_pos hm hr, fun z hz E hE => ?_⟩` and prove the remaining obligations. Establish `h1` using `(hdV z (hz.mem_open V.isOpen hV)).mult_eq`.

Rewrite `h1` using `[← hE.ord_eq]`. Establish `h2` using `hg z hz E hE`. Establish `: (r : ℚ) ≠ 0` using `by exact_mod_cast hr.ne'`. Rewrite using `[E.ord_mul, E.ord_pow, E.ord_pow, Pi.add_apply, qWeil, h1]`. Use `push_cast`.

Rewrite using `[← h2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_isLogEqn_add [IsLocallyNoetherian X] {n : ℕ} {Δ D : X → ℚ} {η : RatForms p n}
    {x : X} {m : ℕ} {g : X.functionFieldˣ} (hD : IsQCart D) (hm : 0 < m)
    (hg : IsLogEqn p Δ η x m g) :
    ∃ (m' : ℕ) (g' : X.functionFieldˣ), 0 < m' ∧ IsLogEqn p (Δ + D) η x m' g' := by
  obtain ⟨r, D₀, hr, -, rfl⟩ := hD
  obtain ⟨d, hd⟩ := D₀.exists_isEqn x
  obtain ⟨V, hV, hdV⟩ := hd.exists_nhds
  refine ⟨m * r, g ^ r * d ^ m, Nat.mul_pos hm hr, fun z hz E hE => ?_⟩
  have h1 := (hdV z (hz.mem_open V.isOpen hV)).mult_eq
  rw [← hE.ord_eq] at h1
  have h2 := hg z hz E hE
  have : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [E.ord_mul, E.ord_pow, E.ord_pow, Pi.add_apply, qWeil, h1]
  push_cast
  rw [← h2]
  field_simp
  ring

/- English proof (translation)
Introduce `X _ _ _ p n hp hn Δ D x hD hk hnk`. Use `haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1`. Take `⟨η, m, g, hη, hm, hg, -⟩` from `hk`. Take `⟨m', g', hm', hg'⟩` from `exists_isLogEqn_add hD hm hg`. Rewrite `hnk` using `[hg'.kltAt_iff hn hη hm']`.

Use `push_neg at hnk`. Take `⟨E, hE, hd⟩` from `hnk`. Take `⟨z, hz, hc⟩` from `exists_centreAt hE`. Conclude with `⟨z, hz, E, η, m', g', hη, hm', fun w hw => hg' w (hw.trans hz), hc, hd⟩`.
-/
theorem exists_isNkltCentre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ KltAt p n (Δ + D) x →
    ∃ z, z ⤳ x ∧ IsNkltCentre p n (Δ + D) z := by
  intro X _ _ _ p n hp hn Δ D x hD hk hnk
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨η, m, g, hη, hm, hg, -⟩ := hk
  obtain ⟨m', g', hm', hg'⟩ := exists_isLogEqn_add hD hm hg
  rw [hg'.kltAt_iff hn hη hm'] at hnk
  push_neg at hnk
  obtain ⟨E, hE, hd⟩ := hnk
  obtain ⟨z, hz, hc⟩ := exists_centreAt hE
  exact ⟨z, hz, E, η, m', g', hη, hm', fun w hw => hg' w (hw.trans hz), hc, hd⟩

end GlobalTheory.PairStep.Centre
