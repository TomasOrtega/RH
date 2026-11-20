import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUTestNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceEmb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegral
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.ReadExist

/- English proof (translation)
Establish `h1 : IsIntegral (PadicAlgCl p) z` using `(hz.tower_top (PadicAlgCl p)).isIntegral`. Establish `h2 : (minpoly (PadicAlgCl p) z).degree = 1` using `IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible h1)`. Conclude with `minpoly.mem_range_of_degree_eq_one _ _ h2`.
-/
theorem exists_algCl {p : ℕ} [Fact p.Prime] {z : ℂ_[p]} (hz : IsAlgebraic ℚ_[p] z) :
    ∃ y : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] y = z := by
  have h1 : IsIntegral (PadicAlgCl p) z := (hz.tower_top (PadicAlgCl p)).isIntegral
  have h2 : (minpoly (PadicAlgCl p) z).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible h1)
  exact minpoly.mem_range_of_degree_eq_one _ _ h2

/- English proof (translation)
Establish `hex : ∀ x : F, ∃ y : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] y = φ x` using `fun x => by`. Apply `exists_algCl` to reduce the goal to its premises. Establish `h1 : IsAlgebraic ℚ (φ x)`. Use `(Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom` as an intermediate fact. Simplify using `using this`.

Conclude with `h1.tower_top ℚ_[p]`. Use `choose f hf using hex`. Establish `hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p])` using `(algebraMap (PadicAlgCl p) ℂ_[p]).injective`. Use `⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[hf]`. Simplify using the standard rewrite rules. Introduce `x y`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, hf, hf, hf]`.

Conclude with `map_mul φ x y`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hf]`. Simplify using the standard rewrite rules. Introduce `x y`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_add, hf, hf, hf]`. Conclude with `map_add φ x y`.
-/
theorem exists_factor_algCl {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) :
    ∃ b : F →+* PadicAlgCl p, ∀ x, algebraMap (PadicAlgCl p) ℂ_[p] (b x) = φ x := by
  have hex : ∀ x : F, ∃ y : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] y = φ x := fun x => by
    apply exists_algCl
    have h1 : IsAlgebraic ℚ (φ x) := by
      have := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom
      simpa using this
    exact h1.tower_top ℚ_[p]
  choose f hf using hex
  have hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p]) :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_mul, hf, hf, hf]; exact map_mul φ x y
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_add, hf, hf, hf]; exact map_add φ x y

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

/- English proof (translation)
Establish `h` using `vV_mul (V := V) hx (inv_ne_zero hx)`. Establish `h1 : vV V (1 : K) = 0` using `by simp [vV]`. Rewrite `h` using `[mul_inv_cancel₀ hx, h1]`. Use linear arithmetic over natural numbers and integers.
-/
theorem vV_inv {x : K} (hx : x ≠ 0) : vV V x⁻¹ = - vV V x := by
  have h := vV_mul (V := V) hx (inv_ne_zero hx)
  have h1 : vV V (1 : K) = 0 := by simp [vV]
  rw [mul_inv_cancel₀ hx, h1] at h
  omega

/- English proof (translation)
Establish `key : ∀ x, ‖c x‖ ≤ 1 ↔ 0 ≤ vV V x` using `fun x => (hn x).trans (Set.mem_range.trans (GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff (V := V) x))`. Establish `h0 : 0 < ‖c y‖` using `norm_pos_iff.2 ((map_ne_zero c).2 hy)`. Establish `hi` using `key y⁻¹`. Rewrite `hi` using `[map_inv₀, norm_inv, vV_inv hy, inv_le_one₀ h0]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Assume the negation of the conclusion as `h'`. Use `hi.2 (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h`.

Assume the negation of the conclusion as `h'`. Use `hi.1 (not_lt.1 h')` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem norm_lt_one_iff_vV_pos {C : Type} [NormedField C] (c : K →+* C)
    (hn : ∀ x, ‖c x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V K)) {y : K} (hy : y ≠ 0) :
    ‖c y‖ < 1 ↔ 0 < vV V y := by
  have key : ∀ x, ‖c x‖ ≤ 1 ↔ 0 ≤ vV V x := fun x =>
    (hn x).trans (Set.mem_range.trans (GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff (V := V) x))
  have h0 : 0 < ‖c y‖ := norm_pos_iff.2 ((map_ne_zero c).2 hy)
  have hi := key y⁻¹
  rw [map_inv₀, norm_inv, vV_inv hy, inv_le_one₀ h0] at hi
  constructor
  · intro h
    by_contra h'
    have := hi.2 (by omega)
    linarith
  · intro h
    by_contra h'
    have := hi.1 (not_lt.1 h')
    omega

end Val

/- English proof (translation)
Rewrite using `[← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]`. Establish `h0 : la.valuation F (x : F) ≠ 0` using `(la.valuation F).ne_zero_iff.2 hx`. Establish `e` using `WithZero.log_lt_log h0 one_ne_zero`. Rewrite `e` using `[WithZero.log_one]`. Express the relevant statement in the definitionally equal form `_ ↔ 0 < -WithZero.log (la.valuation F (x : F))`.

Rewrite using `[← e]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_iff_vLa_pos {F : Type} [Field F] [NumberField F] (la : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F)
    (hx : (x : F) ≠ 0) : x ∈ la.asIdeal ↔ 0 < vLa la (x : F) := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
  have h0 : la.valuation F (x : F) ≠ 0 := (la.valuation F).ne_zero_iff.2 hx
  have e := WithZero.log_lt_log h0 one_ne_zero
  rw [WithZero.log_one] at e
  change _ ↔ 0 < -WithZero.log (la.valuation F (x : F))
  rw [← e]
  omega

/- English proof (translation)
Introduce `p _ F _ _ φ T io e ho hT`. Take `⟨q, hq, c, hn⟩` from `GlobalTheory.DegenerateTest.exists_padic_embedding T.V hT`. Establish `ha : ∀ x : 𝓞 F, ‖c (io (x : F))‖ < 1 ↔ x ∈ (placeAt φ).asIdeal`. Introduce `x`. Distinguish the cases in `hx : (x : F) = 0`.

Establish `hx' : x = 0` using `by exact_mod_cast hx`. Substitute `hx'` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[norm_lt_one_iff_vV_pos c hn ((map_ne_zero io).2 hx), ho.2, mem_iff_vLa_pos _ x hx]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `pos_of_mul_pos_right h (by positivity)`. Introduce `h`. Conclude with `mul_pos (by exact_mod_cast ho.1) h`. Establish `hqp : q = p`.

Establish `h1` using `(ha (p : 𝓞 F)).2 (natCast_mem_placeAt φ)`. Establish `e1 : c (io (((p : ℕ) : 𝓞 F) : F)) = algebraMap ℚ_[q] (PadicAlgCl q) (p : ℚ_[q])` using `by simp`. Rewrite `h1` using `[e1, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff]`. Conclude with `(Nat.prime_dvd_prime_iff_eq hq.out (Fact.out : p.Prime)).1 h1`. Substitute `hqp` using the available equality.

Take `⟨b, hb⟩` from `exists_factor_algCl φ`. Establish `hbn : ∀ x, ‖b x‖ = ‖φ x‖` using `fun x => by`. Rewrite using `[← hb, ← PadicComplex.coe_eq, PadicComplex.norm_extends]`. Take `⟨g, hg⟩` from `GlobalTheory.EmbThroughCompletion.exists_conj (c.comp io) b (GlobalTheory.EmbThroughCompletion.norm_lt_one_iff (placeAt φ) _ _ ha (fun x => by rw [hbn]; exact (mem_placeAt φ x).symm))`. Use `⟨(algebraMap (PadicAlgCl q) ℂ_[q]).comp ((g : PadicAlgCl q →+* PadicAlgCl q).comp c), ?_, ?_⟩` and prove the remaining obligations.

Introduce `a`. Simplify using `only [RingHom.comp_apply]`. Use `hg a` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Rewrite using `[RingHom.coe_coe, this, hb]`.

Introduce `x`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← PadicComplex.coe_eq, PadicComplex.norm_extends, RingHom.coe_coe, ← PadicAlgCl.spectralNorm_eq, ← spectralNorm_eq_of_equiv g, PadicAlgCl.spectralNorm_eq, hn]`. Both sides reduce to the same expression.
-/
theorem exists_isReading : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p])
    (T : CDVR) (io : F →+* T.Fr) (e : ℕ), OverLa (placeAt φ) T.V io e → T.FinRes →
    ∃ k : T.Fr →+* ℂ_[p], IsReading φ T io k := by
  intro p _ F _ _ φ T io e ho hT
  obtain ⟨q, hq, c, hn⟩ := GlobalTheory.DegenerateTest.exists_padic_embedding T.V hT

  have ha : ∀ x : 𝓞 F, ‖c (io (x : F))‖ < 1 ↔ x ∈ (placeAt φ).asIdeal := by
    intro x
    by_cases hx : (x : F) = 0
    · have hx' : x = 0 := by exact_mod_cast hx
      subst hx'
      simp
    rw [norm_lt_one_iff_vV_pos c hn ((map_ne_zero io).2 hx), ho.2, mem_iff_vLa_pos _ x hx]
    constructor
    · intro h
      exact pos_of_mul_pos_right h (by positivity)
    · intro h
      exact mul_pos (by exact_mod_cast ho.1) h

  have hqp : q = p := by
    have h1 := (ha (p : 𝓞 F)).2 (natCast_mem_placeAt φ)
    have e1 : c (io (((p : ℕ) : 𝓞 F) : F)) = algebraMap ℚ_[q] (PadicAlgCl q) (p : ℚ_[q]) := by simp
    rw [e1, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
    exact (Nat.prime_dvd_prime_iff_eq hq.out (Fact.out : p.Prime)).1 h1
  subst hqp
  obtain ⟨b, hb⟩ := exists_factor_algCl φ
  have hbn : ∀ x, ‖b x‖ = ‖φ x‖ := fun x => by
    rw [← hb, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  obtain ⟨g, hg⟩ := GlobalTheory.EmbThroughCompletion.exists_conj (c.comp io) b
    (GlobalTheory.EmbThroughCompletion.norm_lt_one_iff (placeAt φ) _ _ ha
      (fun x => by rw [hbn]; exact (mem_placeAt φ x).symm))
  refine ⟨(algebraMap (PadicAlgCl q) ℂ_[q]).comp ((g : PadicAlgCl q →+* PadicAlgCl q).comp c), ?_, ?_⟩
  · intro a
    simp only [RingHom.comp_apply]
    have := hg a
    simp only [RingHom.comp_apply] at this
    rw [RingHom.coe_coe, this, hb]
  · intro x
    simp only [RingHom.comp_apply]
    rw [← PadicComplex.coe_eq, PadicComplex.norm_extends, RingHom.coe_coe, ← PadicAlgCl.spectralNorm_eq,
      ← spectralNorm_eq_of_equiv g, PadicAlgCl.spectralNorm_eq, hn]
    rfl

end GlobalTheory.GeoTie.ReadExist

end
