import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PatchAtSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameAtOfLocalizationEq
import Formalism.LocalRingCardinality.SpanPowerMembership.Places
import Formalism.LocalToGlobal.Columns.TwQCmp
import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

noncomputable section

namespace GlobalTheory.CartanInertPf

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Use extensionality with `r`. Use `Formalism.BasicNotions.Examples₂.PlacesToy.mem_conjW_pow P r 1` as an intermediate fact. Rewrite `this` using `[pow_one, pow_one]`. Rewrite using `[this, mem_conjP]`. Both sides reduce to the same expression.
-/
theorem conjP_eq_conjW (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ P = Formalism.BasicNotions.Examples₂.PlacesToy.conjW P := by
  ext r
  have := Formalism.BasicNotions.Examples₂.PlacesToy.mem_conjW_pow P r 1
  rw [pow_one, pow_one] at this
  rw [this, mem_conjP]
  rfl

/- English proof (translation)
Establish `h` using `Formalism.BasicNotions.Examples₂.PlacesToy.valuation_conjW P x`. Rewrite `h` using `[← conjP_eq_conjW, hP]`. Conclude with `h.symm`.
-/
theorem valuation_star (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P = P) (x : E) :
    P.valuation E (star x) = P.valuation E x := by
  have h := Formalism.BasicNotions.Examples₂.PlacesToy.valuation_conjW P x
  rw [← conjP_eq_conjW, hP] at h
  exact h.symm

/- English proof (translation)
Take `⟨x, hx⟩` from `hin`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : 𝓞 E, u + cO E u ∉ P.asIdeal := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hx` to reduce the goal to its premises.

Establish `h1` using `h 1`. Establish `h2` using `h x`. Rewrite `h1` using `[map_one]`. Establish `e : cO E x - x = (x + cO E x) - x * (1 + 1)` using `by ring`. Rewrite using `[e]`.

Conclude with `sub_mem h2 (Ideal.mul_mem_left _ _ h1)`. Establish `e1 : ((u : E) + star (u : E)) = algebraMap (𝓞 E) E (u + cO E u)`. Rewrite using `[map_add, algebraMap_cO]`. Establish `hv : P.valuation E ((u : E) + star (u : E)) = 1`. Rewrite using `[e1]`.

Conclude with `(P.valuation_eq_one_iff_notMem (K := E)).2 hu`. Establish `hne : ((u : E) + star (u : E)) ≠ 0`. Introduce `h`. Rewrite `hv` using `[h, map_zero]`. Conclude with `zero_ne_one hv`.

Use `⟨(u : E) / ((u : E) + star (u : E)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, hv, div_one]`. Conclude with `HeightOneSpectrum.valuation_le_one (K := E) P u`. Rewrite using `[star_div₀, star_add, star_star, add_comm (star (u : E)) (u : E), ← add_div, div_self hne]`.
-/
theorem exists_trace_one (P : HeightOneSpectrum (𝓞 E)) (hin : ∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) :
    ∃ τ : E, P.valuation E τ ≤ 1 ∧ τ + star τ = 1 := by
  obtain ⟨x, hx⟩ := hin
  obtain ⟨u, hu⟩ : ∃ u : 𝓞 E, u + cO E u ∉ P.asIdeal := by
    by_contra h
    push_neg at h
    apply hx
    have h1 := h 1
    have h2 := h x
    rw [map_one] at h1
    have e : cO E x - x = (x + cO E x) - x * (1 + 1) := by ring
    rw [e]
    exact sub_mem h2 (Ideal.mul_mem_left _ _ h1)
  have e1 : ((u : E) + star (u : E)) = algebraMap (𝓞 E) E (u + cO E u) := by
    rw [map_add, algebraMap_cO]
  have hv : P.valuation E ((u : E) + star (u : E)) = 1 := by
    rw [e1]; exact (P.valuation_eq_one_iff_notMem (K := E)).2 hu
  have hne : ((u : E) + star (u : E)) ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact zero_ne_one hv
  refine ⟨(u : E) / ((u : E) + star (u : E)), ?_, ?_⟩
  · rw [map_div₀, hv, div_one]
    exact HeightOneSpectrum.valuation_le_one (K := E) P u
  · rw [star_div₀, star_add, star_star, add_comm (star (u : E)) (u : E), ← add_div, div_self hne]

/- English proof (translation)
Take `⟨x, hx⟩` from `hin`. Take `⟨a, ha⟩` from `P.valuation_exists_uniformizer' E`. Establish `hlt : WithZero.exp (-1 : ℤ) < 1`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions.

Establish `hcP : ∀ r : 𝓞 E, r ∈ P.asIdeal → cO E r ∈ P.asIdeal`. Introduce `r hr`. Establish `: r ∈ (conjPrime₂ P).asIdeal` using `by rw [hP]; exact hr`. Conclude with `(mem_conjP P r).1 this`. Establish `haP : a ∈ P.asIdeal` using `(P.valuation_lt_one_iff_mem (K := E) a).1 (by rw [ha]; exact hlt)`.

Establish `hmem : ∀ r : 𝓞 E, r ∈ P.asIdeal → P.valuation E (r : E) ≤ WithZero.exp (-1 : ℤ)`. Introduce `r hr`. Use `(P.intValuation_le_pow_iff_mem r 1).2 (by rw [pow_one]; exact hr)` as an intermediate fact. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Simplify using `using this`.

Use `set r1 : 𝓞 E := a + cO E a with hr1`. Use `set r2 : 𝓞 E := x * a + cO E (x * a) with hr2`. Establish `h1P : r1 ∈ P.asIdeal` using `add_mem haP (hcP a haP)`. Establish `h2P : r2 ∈ P.asIdeal` using `add_mem (Ideal.mul_mem_left _ _ haP) (hcP _ (Ideal.mul_mem_left _ _ haP))`. Establish `hfix : ∀ r : 𝓞 E, star ((r + cO E r : 𝓞 E) : E) = ((r + cO E r : 𝓞 E) : E)`.

Introduce `r`. Express the relevant statement in the definitionally equal form `star (algebraMap (𝓞 E) E (r + cO E r)) = algebraMap (𝓞 E) E (r + cO E r)`. Rewrite using `[map_add, algebraMap_cO, star_add, star_star, add_comm]`. Distinguish the cases in `h1 : P.valuation E (r1 : E) = WithZero.exp (-1 : ℤ)`. Conclude with `⟨r1, hfix a, h1⟩`.

Distinguish the cases in `h2 : P.valuation E (r2 : E) = WithZero.exp (-1 : ℤ)`. Conclude with `⟨r2, hfix (x * a), h2⟩`. It suffices to derive a contradiction. Establish `l1 : P.valuation E (r1 : E) < WithZero.exp (-1 : ℤ)` using `lt_of_le_of_ne (hmem r1 h1P) h1`. Establish `l2 : P.valuation E (r2 : E) < WithZero.exp (-1 : ℤ)` using `lt_of_le_of_ne (hmem r2 h2P) h2`.

Establish `key : (x : E) * (r1 : E) - (r2 : E) = ((x : E) - star (x : E)) * star (a : E)`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E (a + cO E a) - algebraMap (𝓞 E) E (x * a + cO E (x * a)) = (algebraMap (𝓞 E) E x - star (algebraMap (𝓞 E) E x)) * star (algebraMap (𝓞 E) E a)`. Simplify using `only [map_add, map_mul, algebraMap_cO, star_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hvx : P.valuation E ((x : E) - star (x : E)) = 1`.

Establish `e : ((x : E) - star (x : E)) = -(algebraMap (𝓞 E) E (cO E x - x))`. Rewrite using `[map_sub, algebraMap_cO]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Valuation.map_neg]`. Conclude with `(P.valuation_eq_one_iff_notMem (K := E)).2 hx`.

Establish `hv1 : P.valuation E ((x : E) * (r1 : E) - (r2 : E)) = WithZero.exp (-1 : ℤ)`. Rewrite using `[key, map_mul, hvx, one_mul, valuation_star P hP]`. Conclude with `ha`. Establish `hv2 : P.valuation E ((x : E) * (r1 : E) - (r2 : E)) < WithZero.exp (-1 : ℤ)`. Use `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ l2)` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (HeightOneSpectrum.valuation_le_one (K := E) P x)) l1`. Rewrite `hv2` using `[hv1]`. Conclude with `lt_irrefl _ hv2`.
-/
theorem exists_unif_star (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P = P)
    (hin : ∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) :
    ∃ ϖ : 𝓞 E, star (ϖ : E) = ϖ ∧ P.valuation E (ϖ : E) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨x, hx⟩ := hin
  obtain ⟨a, ha⟩ := P.valuation_exists_uniformizer' E
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hcP : ∀ r : 𝓞 E, r ∈ P.asIdeal → cO E r ∈ P.asIdeal := by
    intro r hr
    have : r ∈ (conjPrime₂ P).asIdeal := by rw [hP]; exact hr
    exact (mem_conjP P r).1 this
  have haP : a ∈ P.asIdeal := (P.valuation_lt_one_iff_mem (K := E) a).1 (by rw [ha]; exact hlt)
  have hmem : ∀ r : 𝓞 E, r ∈ P.asIdeal → P.valuation E (r : E) ≤ WithZero.exp (-1 : ℤ) := by
    intro r hr
    have := (P.intValuation_le_pow_iff_mem r 1).2 (by rw [pow_one]; exact hr)
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    simpa using this
  set r1 : 𝓞 E := a + cO E a with hr1
  set r2 : 𝓞 E := x * a + cO E (x * a) with hr2
  have h1P : r1 ∈ P.asIdeal := add_mem haP (hcP a haP)
  have h2P : r2 ∈ P.asIdeal := add_mem (Ideal.mul_mem_left _ _ haP) (hcP _ (Ideal.mul_mem_left _ _ haP))
  have hfix : ∀ r : 𝓞 E, star ((r + cO E r : 𝓞 E) : E) = ((r + cO E r : 𝓞 E) : E) := by
    intro r
    change star (algebraMap (𝓞 E) E (r + cO E r)) = algebraMap (𝓞 E) E (r + cO E r)
    rw [map_add, algebraMap_cO, star_add, star_star, add_comm]
  by_cases h1 : P.valuation E (r1 : E) = WithZero.exp (-1 : ℤ)
  · exact ⟨r1, hfix a, h1⟩
  by_cases h2 : P.valuation E (r2 : E) = WithZero.exp (-1 : ℤ)
  · exact ⟨r2, hfix (x * a), h2⟩
  exfalso
  have l1 : P.valuation E (r1 : E) < WithZero.exp (-1 : ℤ) := lt_of_le_of_ne (hmem r1 h1P) h1
  have l2 : P.valuation E (r2 : E) < WithZero.exp (-1 : ℤ) := lt_of_le_of_ne (hmem r2 h2P) h2
  have key : (x : E) * (r1 : E) - (r2 : E) = ((x : E) - star (x : E)) * star (a : E) := by
    change algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E (a + cO E a) - algebraMap (𝓞 E) E (x * a + cO E (x * a)) =
      (algebraMap (𝓞 E) E x - star (algebraMap (𝓞 E) E x)) * star (algebraMap (𝓞 E) E a)
    simp only [map_add, map_mul, algebraMap_cO, star_mul]
    ring
  have hvx : P.valuation E ((x : E) - star (x : E)) = 1 := by
    have e : ((x : E) - star (x : E)) = -(algebraMap (𝓞 E) E (cO E x - x)) := by
      rw [map_sub, algebraMap_cO]; ring
    rw [e, Valuation.map_neg]
    exact (P.valuation_eq_one_iff_notMem (K := E)).2 hx
  have hv1 : P.valuation E ((x : E) * (r1 : E) - (r2 : E)) = WithZero.exp (-1 : ℤ) := by
    rw [key, map_mul, hvx, one_mul, valuation_star P hP]
    exact ha
  have hv2 : P.valuation E ((x : E) * (r1 : E) - (r2 : E)) < WithZero.exp (-1 : ℤ) := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ l2)
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (HeightOneSpectrum.valuation_le_one (K := E) P x)) l1
  rw [hv1] at hv2
  exact lt_irrefl _ hv2

end GlobalTheory.CartanInertPf

namespace GlobalTheory.CartanInertPf

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Rewrite using `[← algebraMap_smul E r x, ← algebraMap_smul E s y, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hStd_osmul {n : ℕ} (r s : 𝓞 E) (x y : Sp E n) :
    hStd E n (r • x) (s • y) = star (algebraMap (𝓞 E) E r) * algebraMap (𝓞 E) E s * hStd E n x y := by
  rw [← algebraMap_smul E r x, ← algebraMap_smul E s y, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul,
    smul_eq_mul, starRingEnd_apply]
  ring

/- English proof (translation)
Simplify using `only [hStd_apply, star_sum, star_mul, star_star]`.
-/
theorem hStd_star {n : ℕ} (x y : Sp E n) : star (hStd E n x y) = hStd E n y x := by
  simp only [hStd_apply, star_sum, star_mul, star_star]

/- English proof (translation)
Establish `hcP : ∀ t : 𝓞 E, t ∉ P.asIdeal → cO E t ∉ P.asIdeal`. Introduce `t ht h`. Apply `ht` to reduce the goal to its premises. Establish `: t ∈ (conjPrime₂ P).asIdeal` using `(mem_conjP P t).2 h`. Rewrite `this` using `[hP]`. Then use the resulting hypothesis.

Establish `hval1 : ∀ t : 𝓞 E, t ∉ P.asIdeal → P.valuation E (algebraMap (𝓞 E) E t) = 1` using `fun t ht => (P.valuation_eq_one_iff_notMem (K := E)).2 ht`. Establish `hNd : ∀ x, x ∈ N ↔ ∀ y ∈ N, hStd E n y x ∈ (1 : Submodule (𝓞 E) E)`. Introduce `x`. Establish `h` using `mem_dual N x`. Rewrite `h` using `[show dual (hStd E n) N = N from hNu]`. Then use the resulting hypothesis.

Prove the components needed by the constructor for the conclusion. Introduce `hv w hw`. Take `⟨s, hs, hsv⟩` from `(mem_locP P N v).1 hv`. Take `⟨t, ht, htw⟩` from `(mem_locP P N w).1 hw`. Take `⟨r, hr⟩` from `Submodule.mem_one.1 ((hNd _).1 htw _ hsv)`.

Establish `e` using `hStd_osmul s t v w`. Rewrite `e` using `[← hr, ← algebraMap_cO]`. Establish `e2` using `congrArg (P.valuation E) e`. Rewrite `e2` using `[map_mul, map_mul, hval1 _ (hcP s hs), hval1 t ht, one_mul, one_mul]`. Rewrite using `[← e2]`.

Conclude with `HeightOneSpectrum.valuation_le_one (K := E) P r`. Introduce `H`. Take `⟨S, hS⟩` from `hN.fg`. Establish `hy : ∀ y ∈ S, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∃ a : 𝓞 E, hStd E n v y * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E a`. Introduce `y hyS`.

Establish `hyN : y ∈ N` using `hS ▸ Submodule.subset_span hyS`. Take `⟨a, t, ht, e⟩` from `qsp_frac P _ (H y (le_locP P N hyN))`. Conclude with `⟨t, ht, a, e⟩`. Use `choose! t ht a ha using hy`. Use `set T := ∏ y ∈ S, t y with hTdef`.

Establish `hT : T ∉ P.asIdeal`. Establish `: T ∈ P.asIdeal.primeCompl` using `Submonoid.prod_mem _ fun y hy => ht y hy`. Conclude with `this`. Use `(mem_locP P N v).2 ⟨cO E T, hcP T hT, ?_⟩` and prove the remaining obligations. Rewrite using `[hNd]`.

Introduce `y hyN`. Rewrite `hyN` using `[← hS]`. Proceed by induction on `hyN using Submodule.span_induction with`. Consider the case `mem y hyS`. Use `Submodule.mem_one.2 ⟨cO E (∏ z ∈ S.erase y, t z) * cO E (a y), ?_⟩` and prove the remaining obligations.

Establish `eT : T = t y * ∏ z ∈ S.erase y, t z` using `(Finset.mul_prod_erase S t hyS).symm`. Rewrite using `[← algebraMap_smul E (cO E T) v, LinearMap.map_smul, smul_eq_mul, ← hStd_star, map_mul, algebraMap_cO, algebraMap_cO, ← ha y hyS, eT, algebraMap_cO, map_mul, star_mul, star_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz`.

Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `add_mem hx hz`. Consider the case `smul r x _ hx`. Rewrite using `[← algebraMap_smul E r x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← algebraMap_cO, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem mem_localization_iff_of_isUnimodular {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (hP : conjPrime₂ P = P) (N : Submodule (𝓞 E) (Sp E n))
    (hN : Submodule.IsLattice E N) (hNu : IsUnimodular (hStd E n) N) (v : Sp E n) :
    v ∈ localization₂ P.asIdeal N ↔ ∀ w ∈ localization₂ P.asIdeal N, P.valuation E (hStd E n v w) ≤ 1 := by
  have hcP : ∀ t : 𝓞 E, t ∉ P.asIdeal → cO E t ∉ P.asIdeal := by
    intro t ht h
    apply ht
    have : t ∈ (conjPrime₂ P).asIdeal := (mem_conjP P t).2 h
    rwa [hP] at this
  have hval1 : ∀ t : 𝓞 E, t ∉ P.asIdeal → P.valuation E (algebraMap (𝓞 E) E t) = 1 :=
    fun t ht => (P.valuation_eq_one_iff_notMem (K := E)).2 ht
  have hNd : ∀ x, x ∈ N ↔ ∀ y ∈ N, hStd E n y x ∈ (1 : Submodule (𝓞 E) E) := by
    intro x
    have h := mem_dual N x
    rwa [show dual (hStd E n) N = N from hNu] at h
  constructor
  · intro hv w hw
    obtain ⟨s, hs, hsv⟩ := (mem_locP P N v).1 hv
    obtain ⟨t, ht, htw⟩ := (mem_locP P N w).1 hw
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 ((hNd _).1 htw _ hsv)
    have e := hStd_osmul s t v w
    rw [← hr, ← algebraMap_cO] at e
    have e2 := congrArg (P.valuation E) e
    rw [map_mul, map_mul, hval1 _ (hcP s hs), hval1 t ht, one_mul, one_mul] at e2
    rw [← e2]
    exact HeightOneSpectrum.valuation_le_one (K := E) P r
  · intro H
    obtain ⟨S, hS⟩ := hN.fg
    have hy : ∀ y ∈ S, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧
        ∃ a : 𝓞 E, hStd E n v y * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E a := by
      intro y hyS
      have hyN : y ∈ N := hS ▸ Submodule.subset_span hyS
      obtain ⟨a, t, ht, e⟩ := qsp_frac P _ (H y (le_locP P N hyN))
      exact ⟨t, ht, a, e⟩
    choose! t ht a ha using hy
    set T := ∏ y ∈ S, t y with hTdef
    have hT : T ∉ P.asIdeal := by
      have : T ∈ P.asIdeal.primeCompl := Submonoid.prod_mem _ fun y hy => ht y hy
      exact this
    refine (mem_locP P N v).2 ⟨cO E T, hcP T hT, ?_⟩
    rw [hNd]
    intro y hyN
    rw [← hS] at hyN
    induction hyN using Submodule.span_induction with
    | mem y hyS =>
      refine Submodule.mem_one.2 ⟨cO E (∏ z ∈ S.erase y, t z) * cO E (a y), ?_⟩
      have eT : T = t y * ∏ z ∈ S.erase y, t z := (Finset.mul_prod_erase S t hyS).symm
      rw [← algebraMap_smul E (cO E T) v, LinearMap.map_smul, smul_eq_mul, ← hStd_star, map_mul, algebraMap_cO,
        algebraMap_cO, ← ha y hyS, eT, algebraMap_cO, map_mul, star_mul, star_mul]
      ring
    | zero => simp
    | add x z _ _ hx hz =>
      rw [map_add, LinearMap.add_apply]
      exact add_mem hx hz
    | smul r x _ hx =>
      rw [← algebraMap_smul E r x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
        ← algebraMap_cO, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `u hu`. Use `(hStd_nondeg (E := E) (n := n)).1 u fun v => ?_` and prove the remaining obligations. Rewrite using `[← hs, hu, map_zero, LinearMap.zero_apply]`.
-/
theorem isom_injective {n : ℕ} (s : Sp E n →ₗ[E] Sp E n) (hs : ∀ u v, hStd E n (s u) (s v) = hStd E n u v) :
    Function.Injective s := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  refine (hStd_nondeg (E := E) (n := n)).1 u fun v => ?_
  rw [← hs, hu, map_zero, LinearMap.zero_apply]

/- English proof (translation)
Introduce `E _ _ _ n P hP hin N N' hN hN' hNu hN'u hQ`. Use `letI vE : Valued E (WithZero (Multiplicative ℤ)) := P.adicValued`. Establish `hv : ∀ x : E, Valued.v x = P.valuation E x` using `fun x => HeightOneSpectrum.adicValued_apply P`. Take `⟨τ, hτ, hτ1⟩` from `exists_trace_one P hin`. Take `⟨ϖ, hϖs, hϖv⟩` from `exists_unif_star P hP hin`.

Establish `Dn` using `mem_localization_iff_of_isUnimodular P hP N hN hNu`. Establish `Dn'` using `mem_localization_iff_of_isUnimodular P hP N' hN' hN'u`. Establish `hSD : ∀ M : Submodule (𝓞 E) (Sp E n), (∀ v, v ∈ localization₂ P.asIdeal M ↔ ∀ w ∈ localization₂ P.asIdeal M, P.valuation E (hStd E n v w) ≤ 1) → GlobalTheory.UnitarySwap.SelfDual (hStd E n) ⊤ (localization₂ P.asIdeal M : Set (Sp E n))`. Introduce `M hM v`. Rewrite using `[SetLike.mem_coe, hM v]`.

Simplify using `only [Submodule.mem_top, true_and, SetLike.mem_coe, GlobalTheory.UnitarySwap.mem_int, hv]`. Take `⟨d, hd0, hd⟩` from `exists_smul_le_of_lattice (K := E) hN'.fg hN`. Establish `hdE : algebraMap (𝓞 E) E d ≠ 0` using `by rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]`. Establish `hV0 : P.valuation E (algebraMap (𝓞 E) E d) ≠ 0` using `(Valuation.ne_zero_iff _).2 hdE`. Use `set k : ℕ := (-WithZero.log (P.valuation E (algebraMap (𝓞 E) E d))).toNat with hkdef`.

Establish `hle : P.valuation E ((ϖ : E) ^ k / algebraMap (𝓞 E) E d) ≤ 1`. Rewrite using `[map_div₀, map_pow, hϖv, ← WithZero.exp_nsmul, div_le_one₀ (zero_lt_iff.2 hV0), ← WithZero.exp_log hV0, WithZero.exp_le_exp]`. Use `Int.self_le_toNat (-WithZero.log (P.valuation E (algebraMap (𝓞 E) E d)))` as an intermediate fact. Rewrite `this` using `[← hkdef]`. Rewrite using `[nsmul_eq_mul, mul_neg, mul_one]`.

Use linear arithmetic over natural numbers and integers. Take `⟨a, t, ht, hat⟩` from `qsp_frac P _ hle`. Establish `hkey : (ϖ : E) ^ k * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E d`. Rewrite using `[← hat]`. Clear the denominators using the available nonvanishing facts.

Establish `hcomm : ∃ K : ℕ, ∀ v ∈ (localization₂ P.asIdeal N' : Set (Sp E n)), (ϖ : E) ^ K • v ∈ (localization₂ P.asIdeal N : Set (Sp E n))`. Use `⟨k, fun v hv' => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hsv⟩` from `(mem_locP P N' v).1 hv'`. Use `(mem_locP P N _).2 ⟨t * s, fun h => (P.isPrime.mem_or_mem h).elim ht hs, ?_⟩` and prove the remaining obligations. Establish `e : (t * s) • ((ϖ : E) ^ k • v) = a • d • s • v`.

Rewrite using `[← algebraMap_smul E (t * s), ← algebraMap_smul E a, ← algebraMap_smul E d, ← algebraMap_smul E s, smul_smul, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[map_mul]`. Take the linear combination `(algebraMap (𝓞 E) E s) * hkey`. Rewrite using `[e]`.

Conclude with `N.smul_mem a (hd _ hsv)`. Establish `hσ : ∀ x : E, Valued.v (starRingEnd E x) = Valued.v x` using `fun x => by`. Rewrite using `[hv, hv, starRingEnd_apply, valuation_star P hP]`. Establish `hB : ∀ u v : Sp E n, starRingEnd E (hStd E n u v) = hStd E n v u` using `fun u v => by`. Simplify using `only [hStd_apply, map_sum, starRingEnd_apply, star_mul, star_star]`.

Establish `hτO : τ ∈ Formalism.UG.intL E` using `by rw [GlobalTheory.UnitarySwap.mem_int, hv]; exact hτ`. Establish `hϖ' : Valued.v (ϖ : E) = WithZero.exp (-1 : ℤ)` using `by rw [hv]; exact hϖv`. Take `⟨s, hs, -, hs1, hs2⟩` from `GlobalTheory.UnitarySwap.exists_swap (L := E) (V := Sp E n) (B := hStd E n) hσ hB hτO hτ1 hϖs hϖ' (n + 1) ⊤ (by rw [finrank_top, Module.finrank_fin_fun]; omega) _ _ (hSD N Dn) (hSD N' Dn') hcomm`. Use `set g : Sp E n ≃ₗ[E] Sp E n := LinearEquiv.ofInjectiveEndo s (isom_injective s hs) with hg`. Establish `hgs : ∀ x, g x = s x` using `fun x => rfl`.

Establish `hgU : ∀ a b, hStd E n (g a) (g b) = hStd E n a b` using `fun a b => by rw [hgs, hgs, hs]`. Establish `key : ∀ (A B : Submodule (𝓞 E) (Sp E n)), (∀ v, v ∈ localization₂ P.asIdeal A ↔ ∀ w ∈ localization₂ P.asIdeal A, P.valuation E (hStd E n v w) ≤ 1) → (∀ v, v ∈ localization₂ P.asIdeal B ↔ ∀ w ∈ localization₂ P.asIdeal B, P.valuation E (hStd E n v w) ≤ 1) → (∀ v ∈ (localization₂ P. …`. Introduce `A B hA hB h1`. Use extensionality with `x`. Rewrite using `[mem_localization_gmap]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `h1 _ hx` as an intermediate fact. Rewrite `this` using `[← hgs, LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Introduce `hx`.

Rewrite using `[hA]`. Introduce `w hw`. Establish `e : hStd E n (g.symm x) w = hStd E n x (g w)`. Rewrite using `[← hgU (g.symm x) w, LinearEquiv.apply_symm_apply]`. Rewrite using `[e, hgs]`.

Conclude with `(hB x).1 hx _ (h1 w hw)`. Use `⟨g, hgU, ?_, ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.sameAt_of_localized_eq P _ _ (gmap_lattice g N hN) hN' (key N N' Dn Dn' hs1)`. Conclude with `GlobalTheory.sameAt_of_localized_eq P _ _ (gmap_lattice g N' hN') hN (key N' N Dn' Dn hs2)`.
-/
theorem cartanInert : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (n : ℕ), CartanInert E n := by
  intro E _ _ _ n P hP hin N N' hN hN' hNu hN'u hQ
  letI vE : Valued E (WithZero (Multiplicative ℤ)) := P.adicValued
  have hv : ∀ x : E, Valued.v x = P.valuation E x := fun x => HeightOneSpectrum.adicValued_apply P
  obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one P hin
  obtain ⟨ϖ, hϖs, hϖv⟩ := exists_unif_star P hP hin
  have Dn := mem_localization_iff_of_isUnimodular P hP N hN hNu
  have Dn' := mem_localization_iff_of_isUnimodular P hP N' hN' hN'u
  have hSD : ∀ M : Submodule (𝓞 E) (Sp E n),
      (∀ v, v ∈ localization₂ P.asIdeal M ↔ ∀ w ∈ localization₂ P.asIdeal M, P.valuation E (hStd E n v w) ≤ 1) →
      GlobalTheory.UnitarySwap.SelfDual (hStd E n) ⊤ (localization₂ P.asIdeal M : Set (Sp E n)) := by
    intro M hM v
    rw [SetLike.mem_coe, hM v]
    simp only [Submodule.mem_top, true_and, SetLike.mem_coe, GlobalTheory.UnitarySwap.mem_int, hv]
  obtain ⟨d, hd0, hd⟩ := exists_smul_le_of_lattice (K := E) hN'.fg hN
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := by rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  have hV0 : P.valuation E (algebraMap (𝓞 E) E d) ≠ 0 := (Valuation.ne_zero_iff _).2 hdE
  set k : ℕ := (-WithZero.log (P.valuation E (algebraMap (𝓞 E) E d))).toNat with hkdef
  have hle : P.valuation E ((ϖ : E) ^ k / algebraMap (𝓞 E) E d) ≤ 1 := by
    rw [map_div₀, map_pow, hϖv, ← WithZero.exp_nsmul, div_le_one₀ (zero_lt_iff.2 hV0),
      ← WithZero.exp_log hV0, WithZero.exp_le_exp]
    have := Int.self_le_toNat (-WithZero.log (P.valuation E (algebraMap (𝓞 E) E d)))
    rw [← hkdef] at this
    rw [nsmul_eq_mul, mul_neg, mul_one]
    omega
  obtain ⟨a, t, ht, hat⟩ := qsp_frac P _ hle
  have hkey : (ϖ : E) ^ k * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E d := by
    rw [← hat]; field_simp
  have hcomm : ∃ K : ℕ, ∀ v ∈ (localization₂ P.asIdeal N' : Set (Sp E n)),
      (ϖ : E) ^ K • v ∈ (localization₂ P.asIdeal N : Set (Sp E n)) := by
    refine ⟨k, fun v hv' => ?_⟩
    obtain ⟨s, hs, hsv⟩ := (mem_locP P N' v).1 hv'
    refine (mem_locP P N _).2 ⟨t * s, fun h => (P.isPrime.mem_or_mem h).elim ht hs, ?_⟩
    have e : (t * s) • ((ϖ : E) ^ k • v) = a • d • s • v := by
      rw [← algebraMap_smul E (t * s), ← algebraMap_smul E a, ← algebraMap_smul E d, ← algebraMap_smul E s,
        smul_smul, smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      linear_combination (algebraMap (𝓞 E) E s) * hkey
    rw [e]
    exact N.smul_mem a (hd _ hsv)
  have hσ : ∀ x : E, Valued.v (starRingEnd E x) = Valued.v x := fun x => by
    rw [hv, hv, starRingEnd_apply, valuation_star P hP]
  have hB : ∀ u v : Sp E n, starRingEnd E (hStd E n u v) = hStd E n v u := fun u v => by
    simp only [hStd_apply, map_sum, starRingEnd_apply, star_mul, star_star]
  have hτO : τ ∈ Formalism.UG.intL E := by rw [GlobalTheory.UnitarySwap.mem_int, hv]; exact hτ
  have hϖ' : Valued.v (ϖ : E) = WithZero.exp (-1 : ℤ) := by rw [hv]; exact hϖv
  obtain ⟨s, hs, -, hs1, hs2⟩ := GlobalTheory.UnitarySwap.exists_swap (L := E) (V := Sp E n) (B := hStd E n)
    hσ hB hτO hτ1 hϖs hϖ' (n + 1) ⊤ (by rw [finrank_top, Module.finrank_fin_fun]; omega)
    _ _ (hSD N Dn) (hSD N' Dn') hcomm
  set g : Sp E n ≃ₗ[E] Sp E n := LinearEquiv.ofInjectiveEndo s (isom_injective s hs) with hg
  have hgs : ∀ x, g x = s x := fun x => rfl
  have hgU : ∀ a b, hStd E n (g a) (g b) = hStd E n a b := fun a b => by rw [hgs, hgs, hs]
  have key : ∀ (A B : Submodule (𝓞 E) (Sp E n)),
      (∀ v, v ∈ localization₂ P.asIdeal A ↔ ∀ w ∈ localization₂ P.asIdeal A, P.valuation E (hStd E n v w) ≤ 1) →
      (∀ v, v ∈ localization₂ P.asIdeal B ↔ ∀ w ∈ localization₂ P.asIdeal B, P.valuation E (hStd E n v w) ≤ 1) →
      (∀ v ∈ (localization₂ P.asIdeal A : Set (Sp E n)), s v ∈ (localization₂ P.asIdeal B : Set (Sp E n))) →
      localization₂ P.asIdeal (gmap g A) = localization₂ P.asIdeal B := by
    intro A B hA hB h1
    ext x
    rw [mem_localization_gmap]
    constructor
    · intro hx
      have := h1 _ hx
      rwa [← hgs, LinearEquiv.apply_symm_apply] at this
    · intro hx
      rw [hA]
      intro w hw
      have e : hStd E n (g.symm x) w = hStd E n x (g w) := by
        rw [← hgU (g.symm x) w, LinearEquiv.apply_symm_apply]
      rw [e, hgs]
      exact (hB x).1 hx _ (h1 w hw)
  refine ⟨g, hgU, ?_, ?_⟩
  · exact GlobalTheory.sameAt_of_localized_eq P _ _ (gmap_lattice g N hN) hN' (key N N' Dn Dn' hs1)
  · exact GlobalTheory.sameAt_of_localized_eq P _ _ (gmap_lattice g N' hN') hN (key N' N Dn' Dn hs2)

end GlobalTheory.CartanInertPf
