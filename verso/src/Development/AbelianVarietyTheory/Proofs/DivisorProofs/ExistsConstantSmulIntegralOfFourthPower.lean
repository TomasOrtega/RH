import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.RuleIntegral

/- English proof (translation)
Unfold `vLa`. Establish `h1` using `w.valuation_le_one (K := K) r`. Establish `h2 : (w.valuation K) (r : K) ≠ 0` using `(Valuation.ne_zero_iff _).mpr hr`. Establish `h3` using `(WithZero.log_le_log h2 one_ne_zero).mpr h1`. Rewrite `h3` using `[WithZero.log_one]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem vLa_int_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K}
    (hr : (r : K) ≠ 0) : 0 ≤ vLa w (r : K) := by
  unfold vLa
  have h1 := w.valuation_le_one (K := K) r
  have h2 : (w.valuation K) (r : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  omega

/- English proof (translation)
Proceed by induction on `x using EReal.rec with`. Consider the case `bot => exact absurd rfl hx`. Consider the case `top => exact le_top`. Consider the case `coe r`. Establish `: (0 : EReal) ≤ ((r + r + r + r : ℝ) : EReal)` using `by simpa [EReal.coe_add] using h`.

Establish `h' : (0 : ℝ) ≤ r + r + r + r` using `EReal.coe_nonneg.1 this`. Conclude with `EReal.coe_nonneg.2 (by linarith)`.
-/
theorem nonneg_of_four {x : EReal} (hx : x ≠ ⊥) (h : 0 ≤ x + x + x + x) : 0 ≤ x := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => exact le_top
  | coe r =>
    have : (0 : EReal) ≤ ((r + r + r + r : ℝ) : EReal) := by simpa [EReal.coe_add] using h
    have h' : (0 : ℝ) ≤ r + r + r + r := EReal.coe_nonneg.1 this
    exact EReal.coe_nonneg.2 (by linarith)

/- English proof (translation)
Proceed by induction on `x using EReal.rec with`. Consider the case `bot => exact absurd rfl hx`. Consider the case `top => exact Or.inr rfl`. Consider the case `coe r => left`. Establish `h' : r = r + r` using `by exact_mod_cast h`.

Establish `: r = 0` using `by linarith`. Simplify using `[this]`.
-/
theorem eq_zero_or_top_of_double {x : EReal} (hx : x ≠ ⊥) (h : x = x + x) : x = 0 ∨ x = ⊤ := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => exact Or.inr rfl
  | coe r =>
    left
    have h' : r = r + r := by exact_mod_cast h
    have : r = 0 := by linarith
    simp [this]

/- English proof (translation)
Establish `h` using `fun i => IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) (a i)`. Use `choose d hd using h`. Use `⟨∏ i, (d i : 𝓞 K), ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `hm : (∏ i, (d i : 𝓞 K)) ∈ nonZeroDivisors (𝓞 K)` using `Submonoid.prod_mem _ fun i _ => (d i).2`. Conclude with `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm`.

Take `⟨r, hr⟩` from `hd i`. Use `⟨(∏ j ∈ Finset.univ.erase i, (d j : 𝓞 K)) * r, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun j => (d j : 𝓞 K)) (Finset.mem_univ i)]`. Establish `e1 : ∀ x : 𝓞 K, (x : K) = algebraMap (𝓞 K) K x` using `fun _ => rfl`. Rewrite using `[e1, e1, map_mul, map_mul, hr, Algebra.smul_def]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_common_denom {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (a : ι → K) :
    ∃ s : 𝓞 K, (s : K) ≠ 0 ∧ ∀ i, ∃ r : 𝓞 K, (r : K) = (s : K) * a i := by
  classical
  have h := fun i => IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) (a i)
  choose d hd using h
  refine ⟨∏ i, (d i : 𝓞 K), ?_, fun i => ?_⟩
  · have hm : (∏ i, (d i : 𝓞 K)) ∈ nonZeroDivisors (𝓞 K) :=
      Submonoid.prod_mem _ fun i _ => (d i).2
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
  · obtain ⟨r, hr⟩ := hd i
    refine ⟨(∏ j ∈ Finset.univ.erase i, (d j : 𝓞 K)) * r, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (d j : 𝓞 K)) (Finset.mem_univ i)]
    have e1 : ∀ x : 𝓞 K, (x : K) = algebraMap (𝓞 K) K x := fun _ => rfl
    rw [e1, e1, map_mul, map_mul, hr, Algebra.smul_def]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨y, rfl⟩` from `hv`. Establish `h1 : vAtV y 1 = 0`. Break down `y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩` into its components or cases. Use `show nval T.V e (evI y 1) = 0`. Establish `h1 : evI y 1 = 1`.

Use `letI := io.toAlgebra`. Conclude with `evalAt_one _ _ y.1 y.2.1`. Rewrite using `[h1, nval_of_ne one_ne_zero]`. Simplify using `[vV]`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Establish `htop : ∀ Z, vAtV y (GlobalTheory.FlatLine.idem Z) = ⊤` using `fun Z => by`. Establish `hd` using `vAtV_mul y (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z)`. Rewrite `hd` using `[GlobalTheory.FlatLine.idem_mul_idem]`. Conclude with `(eq_zero_or_top_of_double (vAtV_ne_bot y _) hd).resolve_left (hne Z)`.

Use `haveI := CompFin.finite_comp Xo c`. Use `haveI := Fintype.ofFinite (Comp Xo c)`. Establish `hs : ∀ s : Finset (Comp Xo c), vAtV y (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z) = ⊤`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simpa using vAtV_zero y`. Consider the case `insert Z s hZ ih`. Rewrite using `[Finset.sum_insert hZ]`. Use `vAtV_add y (GlobalTheory.FlatLine.idem Z) (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z)` as an intermediate fact. Rewrite `this` using `[htop Z, ih, min_self]`.

Conclude with `top_le_iff.1 this`. Establish `h2` using `hs Finset.univ`. Rewrite `h2` using `[GlobalTheory.FlatLine.sum_idem]`. Rewrite `h1` using `[h2]`. Conclude with `EReal.top_ne_zero h1`.
-/
theorem exists_idem_zero {w : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal}
    (hv : v ∈ valSet Xo c (algCls Xo c) w) : ∃ Z, v (GlobalTheory.FlatLine.idem Z) = 0 := by
  obtain ⟨y, rfl⟩ := hv
  have h1 : vAtV y 1 = 0 := by
    rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
    show nval T.V e (evI y 1) = 0
    have h1 : evI y 1 = 1 := by
      letI := io.toAlgebra
      exact evalAt_one _ _ y.1 y.2.1
    rw [h1, nval_of_ne one_ne_zero]
    simp [vV]
  by_contra hne
  push_neg at hne
  have htop : ∀ Z, vAtV y (GlobalTheory.FlatLine.idem Z) = ⊤ := fun Z => by
    have hd := vAtV_mul y (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z)
    rw [GlobalTheory.FlatLine.idem_mul_idem] at hd
    exact (eq_zero_or_top_of_double (vAtV_ne_bot y _) hd).resolve_left (hne Z)
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  classical
  have hs : ∀ s : Finset (Comp Xo c), vAtV y (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z) = ⊤ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using vAtV_zero y
    | insert Z s hZ ih =>
      rw [Finset.sum_insert hZ]
      have := vAtV_add y (GlobalTheory.FlatLine.idem Z) (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z)
      rw [htop Z, ih, min_self] at this
      exact top_le_iff.1 this
  have h2 := hs Finset.univ
  rw [GlobalTheory.FlatLine.sum_idem] at h2
  rw [h2] at h1
  exact EReal.top_ne_zero h1

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c K ρ a ha hρ hK`. Use `haveI := CompFin.finite_comp Xo c`. Use `haveI := Fintype.ofFinite (Comp Xo c)`. Take `⟨s, hs0, hsa⟩` from `exists_common_denom a`. Use `⟨(s : c.F), hs0, fun w v hv => ?_⟩` and prove the remaining obligations.

Establish `hKv` using `hK w v hv`. Take `⟨Z, hZ⟩` from `exists_idem_zero hv`. Take `⟨y, rfl⟩` from `hv`. Take `⟨r, hr⟩` from `hsa Z`. Establish `hb : (((s ^ 3 * r : 𝓞 c.F)) : c.F) = (s : c.F) ^ 4 * a Z`.

Establish `hr' : algebraMap (𝓞 c.F) c.F r = algebraMap (𝓞 c.F) c.F s * a Z` using `hr`. Use `show algebraMap (𝓞 c.F) c.F (s ^ 3 * r) = (algebraMap (𝓞 c.F) c.F s) ^ 4 * a Z`. Rewrite using `[map_mul, map_pow, hr']`. Expand and normalize the polynomial expressions, which then agree. Establish `hb0 : (((s ^ 3 * r : 𝓞 c.F)) : c.F) ≠ 0`.

Rewrite using `[hb]`. Conclude with `mul_ne_zero (pow_ne_zero _ hs0) (ha Z)`. Establish `hid : GlobalTheory.FlatLine.idem Z * ((s : c.F) • ρ) ^ 4 = (((s ^ 3 * r : 𝓞 c.F)) : c.F) • (GlobalTheory.FlatLine.idem Z * K)`. Rewrite using `[smul_pow, mul_smul_comm, hρ Z, smul_smul, hb]`. Establish `h4 : ∀ x : Rul Xo c, x ^ 4 = x * x * x * x` using `fun x => by ring`.

Establish `e` using `congrArg (vAtV y) hid`. Rewrite `e` using `[h4, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_smul _ _ _ hb0, vAtV_mul, hZ, zero_add, zero_add]`. Use `nonneg_of_four (vAtV_ne_bot _ _) ?_` and prove the remaining obligations. Rewrite using `[e]`. Use `add_nonneg ?_ hKv` and prove the remaining obligations.

Conclude with `EReal.coe_nonneg.2 (by exact_mod_cast vLa_int_nonneg w hb0)`.
-/
theorem exists_smul_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K ρ : Rul Xo c) (a : Comp Xo c → c.F), (∀ Z, a Z ≠ 0) → (∀ Z, GlobalTheory.FlatLine.idem Z * ρ ^ 4 = a Z • (GlobalTheory.FlatLine.idem Z * K)) → (∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v K) → ∃ t : c.F, t ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (t • ρ) := by
  intro E _ _ _ H Dw l Xo c K ρ a ha hρ hK
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  obtain ⟨s, hs0, hsa⟩ := exists_common_denom a
  refine ⟨(s : c.F), hs0, fun w v hv => ?_⟩
  have hKv := hK w v hv
  obtain ⟨Z, hZ⟩ := exists_idem_zero hv
  obtain ⟨y, rfl⟩ := hv
  obtain ⟨r, hr⟩ := hsa Z
  have hb : (((s ^ 3 * r : 𝓞 c.F)) : c.F) = (s : c.F) ^ 4 * a Z := by
    have hr' : algebraMap (𝓞 c.F) c.F r = algebraMap (𝓞 c.F) c.F s * a Z := hr
    show algebraMap (𝓞 c.F) c.F (s ^ 3 * r) = (algebraMap (𝓞 c.F) c.F s) ^ 4 * a Z
    rw [map_mul, map_pow, hr']; ring
  have hb0 : (((s ^ 3 * r : 𝓞 c.F)) : c.F) ≠ 0 := by
    rw [hb]; exact mul_ne_zero (pow_ne_zero _ hs0) (ha Z)
  have hid : GlobalTheory.FlatLine.idem Z * ((s : c.F) • ρ) ^ 4 =
      (((s ^ 3 * r : 𝓞 c.F)) : c.F) • (GlobalTheory.FlatLine.idem Z * K) := by
    rw [smul_pow, mul_smul_comm, hρ Z, smul_smul, hb]
  have h4 : ∀ x : Rul Xo c, x ^ 4 = x * x * x * x := fun x => by ring
  have e := congrArg (vAtV y) hid
  rw [h4, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_smul _ _ _ hb0, vAtV_mul, hZ, zero_add, zero_add] at e
  refine nonneg_of_four (vAtV_ne_bot _ _) ?_
  rw [e]
  refine add_nonneg ?_ hKv
  exact EReal.coe_nonneg.2 (by exact_mod_cast vLa_int_nonneg w hb0)

end GlobalTheory.RuleIntegral
