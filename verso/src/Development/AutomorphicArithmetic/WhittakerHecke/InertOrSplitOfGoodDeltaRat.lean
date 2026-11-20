import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

open private UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.inert_of UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.split_of UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.notSq
  UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.sq_of_near UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.finrank_two UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.iota_delta
  from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe

namespace UpperTheory.PlacesAboveInertOrSplit

open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange UpperTheory.ConvolutionTheory.R2.H

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (D : Dat F E) (v : P F) (w : P E) [hl : w.asIdeal.LiesOver v.asIdeal]

local notation "ι" => completionMap v w
local notation "θw" => algebraMap E (Kv w) D.θ

/- English proof (translation)
Break down `lt_trichotomy x 1 with h1 | h1 | h1` into its components or cases. Conclude with `absurd h (pow_lt_one' h1 hn).ne`. Conclude with `h1`. Conclude with `absurd h (one_lt_pow' h1 hn).ne'`.
-/
private theorem pow1 {x : WithZero (Multiplicative ℤ)} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one' h1 hn).ne
  · exact h1
  · exact absurd h (one_lt_pow' h1 hn).ne'

/- English proof (translation)
The claim follows from `(Ideal.ramificationIdx_pos w.asIdeal (𝓞 F)).ne'`.
-/
private theorem e_ne : w.asIdeal.ramificationIdx (𝓞 F) ≠ 0 :=
  (Ideal.ramificationIdx_pos w.asIdeal (𝓞 F)).ne'

/- English proof (translation)
Establish `h` using `congrArg Valued.v (UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.iota_delta D v w)`. Rewrite `h` using `[valued_completionMap, hd, one_pow, map_pow]`. Conclude with `pow1 two_ne_zero h.symm`.
-/
private theorem theta_unit (hd : Valued.v (algebraMap F (Kv v) D.δ) = 1) : Valued.v θw = 1 := by
  have h := congrArg Valued.v (UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.iota_delta D v w)
  rw [valued_completionMap, hd, one_pow, map_pow] at h
  exact pow1 two_ne_zero h.symm

/- English proof (translation)
Establish `hle : Valued.v (ι c + θw) ≤ 1` using `(Valuation.map_add _ _ _).trans (max_le hc hθ.le)`. Use `le_antisymm hle (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Establish `hc1 : Valued.v (ι c) = 1`. Use `le_antisymm hc (not_lt.1 fun h => ?_)` and prove the remaining obligations. Establish `: Valued.v (ι c) < Valued.v θw` using `by rw [hθ]; exact h`.

Rewrite `hlt` using `[add_comm, Valuation.map_add_eq_of_lt_left _ this, hθ]`. Conclude with `lt_irrefl _ hlt`. Establish `hc2 : Valued.v c = 1`. Rewrite `hc1` using `[valued_completionMap]`. Conclude with `pow1 (e_ne (F := F) w) hc1`.

Use `UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.notSq D v w hu (UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.sq_of_near v _ c h2 hc2 ?_)` and prove the remaining obligations. Establish `h3 : Valued.v (ι (algebraMap F (Kv v) D.δ - c ^ 2)) < 1`. Rewrite using `[map_sub, UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.iota_delta, map_pow, show θw ^ 2 - ι c ^ 2 = (ι c + θw) * (θw - ι c) by ring, map_mul]`. Use `mul_lt_one_of_lt_of_le hlt ?_` and prove the remaining obligations. Conclude with `(Valuation.map_sub _ _ _).trans (max_le hθ.le hc)`.

Rewrite `h3` using `[valued_completionMap]`. Assume the negation of the conclusion as `hn`. Conclude with `absurd h3 (not_lt.2 (one_le_pow_of_one_le' (not_lt.1 hn) _))`.
-/
private theorem c_add (h2 : Valued.v (2 : Kv v) = 1)
    (hθ : Valued.v θw = 1) (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w)
    (c : Kv v) (hc : Valued.v (ι c) ≤ 1) : Valued.v (ι c + θw) = 1 := by
  have hle : Valued.v (ι c + θw) ≤ 1 :=
    (Valuation.map_add _ _ _).trans (max_le hc hθ.le)
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  have hc1 : Valued.v (ι c) = 1 := by
    refine le_antisymm hc (not_lt.1 fun h => ?_)
    have : Valued.v (ι c) < Valued.v θw := by rw [hθ]; exact h
    rw [add_comm, Valuation.map_add_eq_of_lt_left _ this, hθ] at hlt
    exact lt_irrefl _ hlt
  have hc2 : Valued.v c = 1 := by
    rw [valued_completionMap] at hc1
    exact pow1 (e_ne (F := F) w) hc1
  refine UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.notSq D v w hu (UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.sq_of_near v _ c h2 hc2 ?_)
  have h3 : Valued.v (ι (algebraMap F (Kv v) D.δ - c ^ 2)) < 1 := by
    rw [map_sub, UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.iota_delta, map_pow,
      show θw ^ 2 - ι c ^ 2 = (ι c + θw) * (θw - ι c) by ring, map_mul]
    refine mul_lt_one_of_lt_of_le hlt ?_
    exact (Valuation.map_sub _ _ _).trans (max_le hθ.le hc)
  rw [valued_completionMap] at h3
  by_contra hn
  exact absurd h3 (not_lt.2 (one_le_pow_of_one_le' (not_lt.1 hn) _))

/- English proof (translation)
Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `hut : Valued.v (ι u) ≤ Valued.v (ι t)`. Establish `h1 : Valued.v (ι (u / t)) ≤ 1`.

Rewrite using `[map_div₀, map_div₀]`. Conclude with `div_le_one_of_le₀ hut zero_le`. Establish `h3` using `c_add D v w h2 hθ hu (u / t) h1`. Establish `h4 : ι u + ι t * θw = ι t * (ι (u / t) + θw)`. Rewrite using `[mul_add, ← map_mul, show t * (u / t) = u by field_simp]`.

Rewrite using `[h4, map_mul, h3, mul_one, max_eq_right hut]`. Establish `hlt : Valued.v (ι t) < Valued.v (ι u)` using `not_le.1 hut`. Establish `h5 : Valued.v (ι t * θw) < Valued.v (ι u)`. Rewrite using `[map_mul, hθ, mul_one]`. Conclude with `hlt`.

Rewrite using `[Valuation.map_add_eq_of_lt_left _ h5, max_eq_left hlt.le]`.
-/
private theorem coord (h2 : Valued.v (2 : Kv v) = 1)
    (hθ : Valued.v θw = 1) (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w)
    (u t : Kv v) : Valued.v (ι u + ι t * θw) = max (Valued.v (ι u)) (Valued.v (ι t)) := by
  by_cases ht : t = 0
  · subst ht; simp
  by_cases hut : Valued.v (ι u) ≤ Valued.v (ι t)
  · have h1 : Valued.v (ι (u / t)) ≤ 1 := by
      rw [map_div₀, map_div₀]; exact div_le_one_of_le₀ hut zero_le
    have h3 := c_add D v w h2 hθ hu (u / t) h1
    have h4 : ι u + ι t * θw = ι t * (ι (u / t) + θw) := by
      rw [mul_add, ← map_mul, show t * (u / t) = u by field_simp]
    rw [h4, map_mul, h3, mul_one, max_eq_right hut]
  · have hlt : Valued.v (ι t) < Valued.v (ι u) := not_le.1 hut
    have h5 : Valued.v (ι t * θw) < Valued.v (ι u) := by
      rw [map_mul, hθ, mul_one]; exact hlt
    rw [Valuation.map_add_eq_of_lt_left _ h5, max_eq_left hlt.le]

/- English proof (translation)
Establish `hval` using `coord D v w h2 hθ hu`. Establish `hr : Module.finrank (Kv v) (Kv w) = 2`. Rewrite using `[finrank_eq_ramificationIdx_mul_inertiaDeg, hef]`. Use `haveI : Module.Finite (Kv v) (Kv w) := Module.finite_of_finrank_pos (by omega)`. Set `L : (Kv v × Kv v) →ₗ[Kv v] Kv w` to `{ toFun := fun p => ι p.1 + ι p.2 * θw map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring map_smul' := fun c p => by`.

Express the relevant statement in the definitionally equal form `ι (c * p.1) + ι (c * p.2) * θw = c • (ι p.1 + ι p.2 * θw)`. Rewrite using `[Algebra.smul_def, algebraMap_completion_eq, map_mul, map_mul]`. Use `ring }`. Establish `hinj : Function.Injective L`. Use `(injective_iff_map_eq_zero L).2 fun p hp => ?_` and prove the remaining obligations.

Establish `h` using `hval p.1 p.2`. Rewrite `h` using `[show ι p.1 + ι p.2 * θw = 0 from hp, map_zero]`. Establish `h1 : Valued.v (ι p.1) = 0` using `le_antisymm (h ▸ le_max_left _ _) zero_le`. Establish `h3 : Valued.v (ι p.2) = 0` using `le_antisymm (h ▸ le_max_right _ _) zero_le`. Conclude with `Prod.ext ((map_eq_zero ι).1 ((Valuation.zero_iff _).1 h1)) ((map_eq_zero ι).1 ((Valuation.zero_iff _).1 h3))`.

Establish `hsurj : Function.Surjective L` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by`. Rewrite using `[Module.finrank_prod, Module.finrank_self, hr])).1 hinj`. Take `⟨π, hπ⟩` from `w.valuation_exists_uniformizer E`. Take `⟨p, hp⟩` from `hsurj (algebraMap E (Kv w) π)`. Establish `h` using `hval p.1 p.2`.

Rewrite `h` using `[show ι p.1 + ι p.2 * θw = algebraMap E (Kv w) π from hp, valued_algebraMap_field, hπ]`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : Kv v, WithZero.exp (-1 : ℤ) = Valued.v (ι x) := by`. Break down `max_choice (Valued.v (ι p.1)) (Valued.v (ι p.2)) with h' | h'` into its components or cases. Conclude with `⟨_, h.trans h'⟩`. Conclude with `⟨_, h.trans h'⟩`.

Rewrite `hx` using `[valued_completionMap]`. Establish `he0` using `e_ne (F := F) w`. Establish `hx0 : Valued.v x ≠ 0` using `fun h0 => by`. Rewrite `hx` using `[h0, zero_pow he0]`. Conclude with `WithZero.exp_ne_zero hx`.

Rewrite `hx` using `[← WithZero.exp_log hx0, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul]`. Establish `hd : ((w.asIdeal.ramificationIdx (𝓞 F) : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ)` using `⟨-WithZero.log (Valued.v x), by rw [mul_neg, ← hx]; simp⟩`. Conclude with `Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 hd)`.
-/
private theorem e_one (h2 : Valued.v (2 : Kv v) = 1)
    (hθ : Valued.v θw = 1) (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w)
    (hef : w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 2) :
    w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  have hval := coord D v w h2 hθ hu
  have hr : Module.finrank (Kv v) (Kv w) = 2 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg, hef]
  haveI : Module.Finite (Kv v) (Kv w) := Module.finite_of_finrank_pos (by omega)
  let L : (Kv v × Kv v) →ₗ[Kv v] Kv w :=
    { toFun := fun p => ι p.1 + ι p.2 * θw
      map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring
      map_smul' := fun c p => by
        change ι (c * p.1) + ι (c * p.2) * θw = c • (ι p.1 + ι p.2 * θw)
        rw [Algebra.smul_def, algebraMap_completion_eq, map_mul, map_mul]
        ring }
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun p hp => ?_
    have h := hval p.1 p.2
    rw [show ι p.1 + ι p.2 * θw = 0 from hp, map_zero] at h
    have h1 : Valued.v (ι p.1) = 0 := le_antisymm (h ▸ le_max_left _ _) zero_le
    have h3 : Valued.v (ι p.2) = 0 := le_antisymm (h ▸ le_max_right _ _) zero_le
    exact Prod.ext ((map_eq_zero ι).1 ((Valuation.zero_iff _).1 h1))
      ((map_eq_zero ι).1 ((Valuation.zero_iff _).1 h3))
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_prod, Module.finrank_self, hr])).1 hinj
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  obtain ⟨p, hp⟩ := hsurj (algebraMap E (Kv w) π)
  have h := hval p.1 p.2
  rw [show ι p.1 + ι p.2 * θw = algebraMap E (Kv w) π from hp, valued_algebraMap_field, hπ] at h
  obtain ⟨x, hx⟩ : ∃ x : Kv v, WithZero.exp (-1 : ℤ) = Valued.v (ι x) := by
    rcases max_choice (Valued.v (ι p.1)) (Valued.v (ι p.2)) with h' | h'
    · exact ⟨_, h.trans h'⟩
    · exact ⟨_, h.trans h'⟩
  rw [valued_completionMap] at hx
  have he0 := e_ne (F := F) w
  have hx0 : Valued.v x ≠ 0 := fun h0 => by
    rw [h0, zero_pow he0] at hx
    exact WithZero.exp_ne_zero hx
  rw [← WithZero.exp_log hx0, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at hx
  have hd : ((w.asIdeal.ramificationIdx (𝓞 F) : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) :=
    ⟨-WithZero.log (Valued.v x), by rw [mul_neg, ← hx]; simp⟩
  exact Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 hd)

omit hl in
/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨by rw [← h]; rfl⟩, fun h => HeightOneSpectrum.ext h.over.symm⟩`.
-/
private theorem under_iff : w.under (𝓞 F) = v ↔ w.asIdeal.LiesOver v.asIdeal :=
  ⟨fun h => ⟨by rw [← h]; rfl⟩, fun h => HeightOneSpectrum.ext h.over.symm⟩

omit hl in
/- English proof (translation)
Establish `hs` using `sum_ramificationIdx_mul_inertiaDeg E v`. Rewrite `hs` using `[UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.finrank_two D]`. Use `set g : PlacesOver E v → ℕ := fun x => x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) with hg'`. Establish `hs' : ∑ x, g x = 2` using `hs`. Establish `hpos : ∀ x, 1 ≤ g x` using `fun x => Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)`.

Establish `hne : Nonempty (PlacesOver E v)`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`. Simplify using `at hs'`. Take `⟨a⟩` from `hne`.

Distinguish the cases in `hu : ∀ b : PlacesOver E v, b = a`. Use `left haveI := a.2`. Establish `h2 : g a = 2`. Rewrite using `[← hs', Finset.sum_eq_single a (fun b _ hb => absurd (hu b) hb) (fun h => absurd (Finset.mem_univ _) h)]`. Establish `hu' : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = a.1` using `fun w' hw' => congrArg Subtype.val (hu ⟨w', hw'⟩)`.

Establish `hθ` using `theta_unit D v a.1 hg.del`. Establish `he` using `e_one D v a.1 hg.two hθ hu' h2`. Establish `hf : a.1.asIdeal.inertiaDeg (𝓞 F) = 2` using `by simpa only [hg', he, one_mul] using h2`. Conclude with `⟨a.1, (under_iff v a.1).2 a.2, UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.inert_of D v a.1 he hg.two hθ hu' hf⟩`. Use `right`.

Take `⟨b, hb⟩` from `not_forall.1 hu`. Establish `h1 : g b + g a ≤ 2`. Rewrite using `[← hs', ← Finset.sum_pair hb]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`. Establish `ha1` using `hpos a`.

Establish `hb1` using `hpos b`. Establish `hsp : ∀ x : PlacesOver E v, g x = 1 → SplitAt v x.1` using `fun x hx => by haveI := x.2`. Conclude with `UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.split_of v x.1 (Nat.eq_one_of_mul_eq_one_right hx) (Nat.eq_one_of_mul_eq_one_left hx)`. Use `⟨b.1, a.1, fun h => hb (Subtype.ext h), (under_iff v b.1).2 b.2, (under_iff v a.1).2 a.2, hsp b (by omega), hsp a (by omega), fun w'' hw => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Rewrite `hn` using `[not_or]`. Set `c : PlacesOver E v` to `⟨w'', (under_iff v w'').1 hw⟩`. Establish `hcb : c ≠ b` using `fun h => hn.1 (congrArg Subtype.val h)`. Establish `hca : c ≠ a` using `fun h => hn.2 (congrArg Subtype.val h)`. Establish `h3 : g c + (g b + g a) ≤ 2`.

Rewrite using `[← hs', ← Finset.sum_pair hb, ← Finset.sum_insert (by simp [hcb, hca])]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`. Use `hpos c` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem main (hg : Gd D.δ v) :
    (∃ w : P E, w.under (𝓞 F) = v ∧ Inert D v w) ∨
      (∃ w w' : P E, w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v ∧ SplitAt v w ∧ SplitAt v w' ∧
        ∀ w'' : P E, w''.under (𝓞 F) = v → w'' = w ∨ w'' = w') := by
  have hs := sum_ramificationIdx_mul_inertiaDeg E v
  rw [UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.finrank_two D] at hs
  set g : PlacesOver E v → ℕ := fun x => x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) with hg'
  have hs' : ∑ x, g x = 2 := hs
  have hpos : ∀ x, 1 ≤ g x := fun x =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hne : Nonempty (PlacesOver E v) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hs'
  obtain ⟨a⟩ := hne
  by_cases hu : ∀ b : PlacesOver E v, b = a
  · left
    haveI := a.2
    have h2 : g a = 2 := by
      rw [← hs', Finset.sum_eq_single a (fun b _ hb => absurd (hu b) hb) (fun h => absurd (Finset.mem_univ _) h)]
    have hu' : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = a.1 := fun w' hw' =>
      congrArg Subtype.val (hu ⟨w', hw'⟩)
    have hθ := theta_unit D v a.1 hg.del
    have he := e_one D v a.1 hg.two hθ hu' h2
    have hf : a.1.asIdeal.inertiaDeg (𝓞 F) = 2 := by simpa only [hg', he, one_mul] using h2
    exact ⟨a.1, (under_iff v a.1).2 a.2, UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.inert_of D v a.1 he hg.two hθ hu' hf⟩
  · right
    obtain ⟨b, hb⟩ := not_forall.1 hu
    have h1 : g b + g a ≤ 2 := by
      rw [← hs', ← Finset.sum_pair hb]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have ha1 := hpos a
    have hb1 := hpos b
    have hsp : ∀ x : PlacesOver E v, g x = 1 → SplitAt v x.1 := fun x hx => by
      haveI := x.2
      exact UpperTheory.ConvolutionTheory.R2.H.nearSquareValuations.split_of v x.1 (Nat.eq_one_of_mul_eq_one_right hx) (Nat.eq_one_of_mul_eq_one_left hx)
    refine ⟨b.1, a.1, fun h => hb (Subtype.ext h), (under_iff v b.1).2 b.2, (under_iff v a.1).2 a.2,
      hsp b (by omega), hsp a (by omega), fun w'' hw => ?_⟩
    by_contra hn
    rw [not_or] at hn
    let c : PlacesOver E v := ⟨w'', (under_iff v w'').1 hw⟩
    have hcb : c ≠ b := fun h => hn.1 (congrArg Subtype.val h)
    have hca : c ≠ a := fun h => hn.2 (congrArg Subtype.val h)
    have h3 : g c + (g b + g a) ≤ 2 := by
      rw [← hs', ← Finset.sum_pair hb, ← Finset.sum_insert (by simp [hcb, hca])]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := hpos c
    omega

end UpperTheory.PlacesAboveInertOrSplit

/- English proof (translation)
Introduce `E _ _ D v hg`. Conclude with `UpperTheory.PlacesAboveInertOrSplit.main D v hg`.
-/
theorem UpperTheory.inert_or_split_of_good_delta_rat :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ), H.Gd D.δ v →
          (∃ w : H.P E, w.under (𝓞 ℚ) = v ∧ H.Inert D v w) ∨
          (∃ w w' : H.P E, w ≠ w' ∧ w.under (𝓞 ℚ) = v ∧ w'.under (𝓞 ℚ) = v ∧ H.SplitAt v w ∧ H.SplitAt v w' ∧
            ∀ w'' : H.P E, w''.under (𝓞 ℚ) = v → w'' = w ∨ w'' = w') := by
  intro E _ _ D v hg
  exact UpperTheory.PlacesAboveInertOrSplit.main D v hg
