import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Use `⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Simplify using `only`. Rewrite using `[inv_mul_cancel_left₀ (hc q.1)]`.
-/
theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  simp only
  rw [inv_mul_cancel_left₀ (hc q.1)]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Take `⟨d, hd, rfl⟩` from `h'`. Use `⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Simplify using `only`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  refine ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), ?_⟩
  funext q
  simp only
  ring

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Use function extensionality and compare the values at `⟨k, i, j⟩`. Simplify using `only [proj]`. Establish `hN : (∑ l, ‖c k * z' ⟨k, l⟩‖ ^ 2 : ℝ) = ‖c k‖ ^ 2 * ∑ l, ‖z' ⟨k, l⟩‖ ^ 2`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun l _ => by rw [norm_mul, mul_pow]`. Establish `hcc : c k * starRingEnd ℂ (c k) ≠ 0` using `mul_ne_zero (hc k) ((map_ne_zero _).2 (hc k))`. Rewrite using `[hN, map_mul]`. Use `push_cast`. Rewrite using `[← Complex.mul_conj', show c k * z' ⟨k, i⟩ * (starRingEnd ℂ (c k) * starRingEnd ℂ (z' ⟨k, j⟩)) = (c k * starRingEnd ℂ (c k)) * (z' ⟨k, i⟩ * starRingEnd ℂ (z' ⟨k, j⟩)) by ring]`.

Conclude with `mul_div_mul_left _ _ hcc`.
-/
theorem proj_eq_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : proj z = proj z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext ⟨k, i, j⟩
  simp only [proj]
  have hN : (∑ l, ‖c k * z' ⟨k, l⟩‖ ^ 2 : ℝ) = ‖c k‖ ^ 2 * ∑ l, ‖z' ⟨k, l⟩‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [norm_mul, mul_pow]
  have hcc : c k * starRingEnd ℂ (c k) ≠ 0 :=
    mul_ne_zero (hc k) ((map_ne_zero _).2 (hc k))
  rw [hN, map_mul]
  push_cast
  rw [← Complex.mul_conj', show c k * z' ⟨k, i⟩ * (starRingEnd ℂ (c k) * starRingEnd ℂ (z' ⟨k, j⟩)) =
    (c k * starRingEnd ℂ (c k)) * (z' ⟨k, i⟩ * starRingEnd ℂ (z' ⟨k, j⟩)) by ring]
  exact mul_div_mul_left _ _ hcc

/- English proof (translation)
Establish `h1 : 0 < ‖z ⟨k, j⟩‖ ^ 2` using `by positivity`. Establish `h2 : ‖z ⟨k, j⟩‖ ^ 2 ≤ ∑ l, ‖z ⟨k, l⟩‖ ^ 2` using `Finset.single_le_sum (f := fun l => ‖z ⟨k, l⟩‖ ^ 2) (fun l _ => by positivity) (Finset.mem_univ j)`. Conclude with `Complex.ofReal_ne_zero.2 (lt_of_lt_of_le h1 h2).ne'`.
-/
theorem blockNorm_ne_zero {z : (Σ k, ι k) → ℂ} {k : K} {j : ι k} (hj : z ⟨k, j⟩ ≠ 0) :
    ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
  have h1 : 0 < ‖z ⟨k, j⟩‖ ^ 2 := by positivity
  have h2 : ‖z ⟨k, j⟩‖ ^ 2 ≤ ∑ l, ‖z ⟨k, l⟩‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ‖z ⟨k, l⟩‖ ^ 2) (fun l _ => by positivity) (Finset.mem_univ j)
  exact Complex.ofReal_ne_zero.2 (lt_of_lt_of_le h1 h2).ne'

/- English proof (translation)
Establish `key : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ ∀ i, z ⟨k, i⟩ = c * z' ⟨k, i⟩`. Introduce `k`. Take `⟨j, hj⟩` from `hz k`. Take `⟨j', hj'⟩` from `hz' k`. Establish `hN` using `blockNorm_ne_zero hj`.

Establish `hN'` using `blockNorm_ne_zero hj'`. Establish `hp : ∀ a b, z ⟨k, a⟩ * starRingEnd ℂ (z ⟨k, b⟩) / ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) = z' ⟨k, a⟩ * starRingEnd ℂ (z' ⟨k, b⟩) / ((∑ l, ‖z' ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ)` using `fun a b => congrFun h ⟨k, a, b⟩`. Establish `hcj : starRingEnd ℂ (z ⟨k, j⟩) ≠ 0` using `(map_ne_zero _).2 hj`. Establish `hw : z' ⟨k, j⟩ ≠ 0`. Introduce `h0`.

Use `hp j j` as an intermediate fact. Rewrite `this` using `[h0, zero_mul, zero_div, div_eq_zero_iff]`. Break down `this with h1 | h1` into its components or cases. Conclude with `(mul_ne_zero hj hcj) h1`. Conclude with `hN h1`.

Establish `hcw : starRingEnd ℂ (z' ⟨k, j⟩) ≠ 0` using `(map_ne_zero _).2 hw`. Use `⟨starRingEnd ℂ (z' ⟨k, j⟩) * ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) / (((∑ l, ‖z' ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (z ⟨k, j⟩)), div_ne_zero (mul_ne_zero hcw hN) (mul_ne_zero hN' hcj), fun i => ?_⟩` and prove the remaining obligations. Use `hp i j` as an intermediate fact. Rewrite `this` using `[div_eq_div_iff hN hN']`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `this`. Use `choose c hc hci using key`. Conclude with `⟨c, hc, funext fun q => hci q.1 q.2⟩`.
-/
theorem sameOrbit_of_proj_eq {z z' : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : proj z = proj z') : SameOrbit z z' := by
  have key : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ ∀ i, z ⟨k, i⟩ = c * z' ⟨k, i⟩ := by
    intro k
    obtain ⟨j, hj⟩ := hz k
    obtain ⟨j', hj'⟩ := hz' k
    have hN := blockNorm_ne_zero hj
    have hN' := blockNorm_ne_zero hj'
    have hp : ∀ a b, z ⟨k, a⟩ * starRingEnd ℂ (z ⟨k, b⟩) / ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) =
        z' ⟨k, a⟩ * starRingEnd ℂ (z' ⟨k, b⟩) / ((∑ l, ‖z' ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) :=
      fun a b => congrFun h ⟨k, a, b⟩
    have hcj : starRingEnd ℂ (z ⟨k, j⟩) ≠ 0 := (map_ne_zero _).2 hj
    have hw : z' ⟨k, j⟩ ≠ 0 := by
      intro h0
      have := hp j j
      rw [h0, zero_mul, zero_div, div_eq_zero_iff] at this
      rcases this with h1 | h1
      · exact (mul_ne_zero hj hcj) h1
      · exact hN h1
    have hcw : starRingEnd ℂ (z' ⟨k, j⟩) ≠ 0 := (map_ne_zero _).2 hw
    refine ⟨starRingEnd ℂ (z' ⟨k, j⟩) * ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) /
      (((∑ l, ‖z' ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (z ⟨k, j⟩)),
      div_ne_zero (mul_ne_zero hcw hN) (mul_ne_zero hN' hcj), fun i => ?_⟩
    have := hp i j
    rw [div_eq_div_iff hN hN'] at this
    field_simp
    linear_combination this
  choose c hc hci using key
  exact ⟨c, hc, funext fun q => hci q.1 q.2⟩

/- English proof (translation)
The claim follows from `funext (eval_lift p x hx)`.
-/
theorem lift_vec {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k) (x : Pts P)
    (hx : x ∈ src P p) :
    (fun q => eval (coord P p x) (lift p q)) = affCoord p (rep x) :=
  funext (eval_lift p x hx)

/- English proof (translation)
Rewrite using `[lift_vec p x hx]`. Conclude with `sameOrbit_affCoord p (rep x) hx`.
-/
theorem orbit_rep_lift {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k) (x : Pts P)
    (hx : x ∈ src P p) :
    SameOrbit (rep x) (fun q => eval (coord P p x) (lift p q)) := by
  rw [lift_vec p x hx]
  exact sameOrbit_affCoord p (rep x) hx

/- English proof (translation)
Rewrite using `[lift_vec p x hx]`. Conclude with `(conePts_of_chartIdeal hP p _ ((mem_conePts_iff_chartIdeal hP p (rep x) hx).1 (rep_mem x))).1`.
-/
theorem lift_mem_conePts {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    (fun q => eval (coord P p x) (lift p q)) ∈ conePts P := by
  rw [lift_vec p x hx]
  exact (conePts_of_chartIdeal hP p _
    ((mem_conePts_iff_chartIdeal hP p (rep x) hx).1 (rep_mem x))).1

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hP`. Take `⟨T, hT, rfl⟩` from `hD`. Use `⟨S ∪ T, ?_, (Ideal.span_union S T).symm⟩` and prove the remaining obligations. Introduce and unpack `f (hf | hf)`. Conclude with `hS f hf`.

Conclude with `hT f hf`.
-/
theorem isMultiHomogIdeal_sup {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (hD : IsMultiHomogIdeal D) : IsMultiHomogIdeal (P ⊔ D) := by
  obtain ⟨S, hS, rfl⟩ := hP
  obtain ⟨T, hT, rfl⟩ := hD
  refine ⟨S ∪ T, ?_, (Ideal.span_union S T).symm⟩
  rintro f (hf | hf)
  · exact hS f hf
  · exact hT f hf

/- English proof (translation)
Establish `hmem` using `lift_mem_conePts hP p x hx`. Rewrite `hmem`, the goal using `[lift_vec p x hx]`. Establish `hone : ∀ k, affCoord p (rep x) ⟨k, p k⟩ = 1` using `fun k => by`. Simplify using `[affCoord, hx k]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `hz : ∀ f ∈ chartIdeal (P ⊔ D) p, eval (affCoord p (rep x)) f = 0`. Introduce `f hf`. Rewrite using `[← eval_renC]`. Conclude with `h _ (Ideal.le_radical (Ideal.mem_map_of_mem _ hf))`.

Use `(conePts_of_chartIdeal (isMultiHomogIdeal_sup hP hD) p _ hz).1` as an intermediate fact. Conclude with `⟨this.1, fun f hf => this.2 f (Ideal.mem_sup_right hf)⟩`. Introduce `hDm g hg`. Establish `hle : chartIdeal (P ⊔ D) p ≤ RingHom.ker (eval (affCoord p (rep x)))`. Use `sup_le (sup_le (fun f hf => hmem.2 f hf) (fun f hf => hDm.2 f hf)) ?_` and prove the remaining obligations.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `show eval _ _ = 0`. Simplify using `[hone k]`. Take `⟨n, hn⟩` from `hg`.

Establish `h0` using `renPt_zero (chartIdeal (P ⊔ D) p) (affCoord p (rep x)) (fun f hf => hle hf) _ hn`. Rewrite `h0` using `[map_pow]`. Conclude with `eq_zero_of_pow_eq_zero h0`.
-/
theorem zero_bd_iff {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    (∀ h ∈ bd P D p, eval (coord P p x) h = 0) ↔
      (fun q => eval (coord P p x) (lift p q)) ∈ conePts D := by
  have hmem := lift_mem_conePts hP p x hx
  rw [lift_vec p x hx] at hmem ⊢
  have hone : ∀ k, affCoord p (rep x) ⟨k, p k⟩ = 1 := fun k => by
    simp [affCoord, hx k]
  constructor
  · intro h
    have hz : ∀ f ∈ chartIdeal (P ⊔ D) p, eval (affCoord p (rep x)) f = 0 := by
      intro f hf
      rw [← eval_renC]
      exact h _ (Ideal.le_radical (Ideal.mem_map_of_mem _ hf))
    have := (conePts_of_chartIdeal (isMultiHomogIdeal_sup hP hD) p _ hz).1
    exact ⟨this.1, fun f hf => this.2 f (Ideal.mem_sup_right hf)⟩
  · intro hDm g hg
    have hle : chartIdeal (P ⊔ D) p ≤ RingHom.ker (eval (affCoord p (rep x))) := by
      refine sup_le (sup_le (fun f hf => hmem.2 f hf) (fun f hf => hDm.2 f hf)) ?_
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show eval _ _ = 0
      simp [hone k]
    obtain ⟨n, hn⟩ := hg
    have h0 := renPt_zero (chartIdeal (P ⊔ D) p) (affCoord p (rep x)) (fun f hf => hle hf) _ hn
    rw [map_pow] at h0
    exact eq_zero_of_pow_eq_zero h0

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

/- English proof (translation)
Introduce `K _ ι _ P D hP hD`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Take `⟨p, hp, -⟩` from `ReciprocityTheory.AnForm.R.exists_chart (rep x) (rep_mem x).1`. Conclude with `⟨p, hp⟩`.

Conclude with `fun p x hx => SncRes.lift_mem_conePts hP p x hx`. Introduce `p p' x hx`. Conclude with `SncRes.sameOrbit_trans (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p x hx.1)) (SncRes.orbit_rep_lift p' x hx.2)`. Introduce `z hz`. Take `⟨p, hp, -⟩` from `ReciprocityTheory.AnForm.R.exists_chart z hz.1`.

Set `x : SncRes.Pts P` to `⟨SncRes.proj z, z, hz, rfl⟩`. Establish `hrz : ReciprocityTheory.AnForm.R.SameOrbit (SncRes.rep x) z` using `SncRes.sameOrbit_of_proj_eq (SncRes.rep_mem x).1 hz.1 (SncRes.proj_rep x)`. Establish `hx : x ∈ SncRes.src P p`. Take `⟨c, hc, he⟩` from `hrz`. Introduce `k`.

Rewrite using `[he]`. Conclude with `mul_ne_zero (hc k) (hp k)`. Conclude with `⟨p, x, hx, SncRes.sameOrbit_trans (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p x hx)) hrz⟩`. Introduce `p p' x hx x' hx' h`. Establish `h1 : ReciprocityTheory.AnForm.R.SameOrbit (SncRes.rep x) (SncRes.rep x')` using `SncRes.sameOrbit_trans (SncRes.orbit_rep_lift p x hx) (SncRes.sameOrbit_trans h (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p' x' hx')))`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← SncRes.proj_rep x, ← SncRes.proj_rep x']`. Conclude with `SncRes.proj_eq_of_sameOrbit h1`. Conclude with `fun p x hx => SncRes.zero_bd_iff hP hD p x hx`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ReciprocityTheory.AnForm.R.IsMultiHomogIdeal D → (∀ x : SncRes.Pts P, ∃ p : (k : K) → ι k, x ∈ SncRes.src P p) ∧ (∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts P) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x) (SncRes.lift p' q))) ∧ (∀ z ∈ ReciprocityTheory.AnForm.R.conePts P, ∃ p : (k : K) → ι k, ∃ x ∈ SncRes.src P p, ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) z) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ x' ∈ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x') (SncRes.lift p' q)) → x = x') ∧ ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ((∀ h ∈ SncRes.bd P D p, eval (SncRes.coord P p x) h = 0) ↔ (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts D) := by
  intro K _ ι _ P D hP hD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart (rep x) (rep_mem x).1
    exact ⟨p, hp⟩
  · exact fun p x hx => SncRes.lift_mem_conePts hP p x hx
  · intro p p' x hx
    exact SncRes.sameOrbit_trans (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p x hx.1))
      (SncRes.orbit_rep_lift p' x hx.2)
  · intro z hz
    obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart z hz.1
    let x : SncRes.Pts P := ⟨SncRes.proj z, z, hz, rfl⟩
    have hrz : ReciprocityTheory.AnForm.R.SameOrbit (SncRes.rep x) z :=
      SncRes.sameOrbit_of_proj_eq (SncRes.rep_mem x).1 hz.1 (SncRes.proj_rep x)
    have hx : x ∈ SncRes.src P p := by
      obtain ⟨c, hc, he⟩ := hrz
      intro k
      rw [he]
      exact mul_ne_zero (hc k) (hp k)
    exact ⟨p, x, hx, SncRes.sameOrbit_trans
      (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p x hx)) hrz⟩
  · intro p p' x hx x' hx' h
    have h1 : ReciprocityTheory.AnForm.R.SameOrbit (SncRes.rep x) (SncRes.rep x') :=
      SncRes.sameOrbit_trans (SncRes.orbit_rep_lift p x hx)
        (SncRes.sameOrbit_trans h (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p' x' hx')))
    apply Subtype.ext
    rw [← SncRes.proj_rep x, ← SncRes.proj_rep x']
    exact SncRes.proj_eq_of_sameOrbit h1
  · exact fun p x hx => SncRes.zero_bd_iff hP hD p x hx
