import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

/- English proof (translation)
Simplify using `[nu]`.
-/
private lemma nu_mul' (x y : ℂ) : nu ι (x * y) = nu ι x * nu ι y := by
  simp [nu]

/- English proof (translation)
The claim follows from `norm_nonneg _`.
-/
private lemma nu_nonneg' (x : ℂ) : 0 ≤ nu ι x := norm_nonneg _

/- English proof (translation)
Unfold `nu`. Conclude with `norm_pos_iff.mpr (by simpa using h)`.
-/
private lemma nu_pos' {x : ℂ} (h : x ≠ 0) : 0 < nu ι x := by
  unfold nu
  exact norm_pos_iff.mpr (by simpa using h)

/- English proof (translation)
Unfold `nu`. Rewrite using `[map_sum]`. Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hb (fun x hx => h x hx)`.
-/
private lemma nu_sum_le' {α : Type*} (t : Finset α) (f : α → ℂ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x ∈ t, nu ι (f x) ≤ b) : nu ι (∑ x ∈ t, f x) ≤ b := by
  unfold nu
  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hb (fun x hx => h x hx)

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Use `nu_sum_le' ι _ _ _ (mul_nonneg hp hq) fun j _ => ?_` and prove the remaining obligations. Rewrite using `[nu_mul']`. Conclude with `mul_le_mul (hA i j) (hv j) (nu_nonneg' ι _) hp`.
-/
private lemma nu_mulVec_le {I : Type} [Fintype I] (A : Matrix I I ℂ) (v : I → ℂ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hA : ∀ i j, nu ι (A i j) ≤ p) (hv : ∀ j, nu ι (v j) ≤ q) (i : I) :
    nu ι ((A *ᵥ v) i) ≤ p * q := by
  simp only [Matrix.mulVec, dotProduct]
  refine nu_sum_le' ι _ _ _ (mul_nonneg hp hq) fun j _ => ?_
  rw [nu_mul']
  exact mul_le_mul (hA i j) (hv j) (nu_nonneg' ι _) hp

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `l _ ι G _ Γ K I _ R F s a c C hc hfin hF hΓ hK heig hRK hRL`. Use `set Nf : G → I → ℂ := fun g => R g⁻¹ *ᵥ F g with hN`. Establish `Rinv : ∀ g, R g⁻¹ * R g = 1` using `fun g => by rw [← map_mul, inv_mul_cancel, map_one]`. Establish `Rinv' : ∀ g, R g * R g⁻¹ = 1` using `fun g => by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `hNΓ : ∀ γ ∈ Γ, ∀ g, Nf (γ * g) = Nf g`.

Introduce `γ hγ g`. Simplify using `only [hN, hΓ γ hγ g, _root_.mul_inv_rev, map_mul, mulVec_mulVec]`. Rewrite using `[mul_assoc, Rinv, mul_one]`. Establish `hNK : ∀ k ∈ K, ∀ g, Nf (g * k) = R k⁻¹ *ᵥ Nf g`. Introduce `k hk g`.

Simplify using `only [hN, hK k hk g, _root_.mul_inv_rev, map_mul, mulVec_mulVec]`. Establish `hNeig : ∀ h, a • Nf h = ∑ x ∈ s, R x *ᵥ Nf (h * x)`. Introduce `h`. Establish `h1 : ∀ x, R x *ᵥ Nf (h * x) = R h⁻¹ *ᵥ F (h * x)`. Introduce `x`.

Simplify using `only [hN, _root_.mul_inv_rev, map_mul, mulVec_mulVec]`. Rewrite using `[← mul_assoc, Rinv', one_mul]`. Simplify using `only [h1]`. Simplify using `only [hN]`. Rewrite using `[← Matrix.mulVec_smul, ← heig h, Matrix.mulVec_sum]`.

Choose the witnesses or unpack the hypotheses as in `⟨g0, i0, h0⟩ : ∃ g i, Nf g i ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hF` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Establish `: F g = R g *ᵥ Nf g`. Simplify using `only [hN, mulVec_mulVec, Rinv', one_mulVec]`. Rewrite using `[this, show Nf g = 0 from funext (hcon g)]`. Simplify using the standard rewrite rules. Establish `hC : 0 ≤ C` using `(nu_nonneg' ι _).trans (hRK 1 K.one_mem i0 i0)`.

Take `⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ g i, nu ι (Nf g i) ≤ B` from `by haveI := hfin`. Use `letI := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))`. Use `set B0 : ℝ := ∑ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G), ∑ i, nu ι (Nf q.out i) with hB0`. Establish `hB0n : 0 ≤ B0` using `Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun i _ => nu_nonneg' ι _`. Establish `hle : ∀ (q : DoubleCoset.Quotient (Γ : Set G) (K : Set G)) j, nu ι (Nf q.out j) ≤ B0`.

Introduce `q j`. Combine the equalities or inequalities in the displayed calculation. Use `⟨C * B0, mul_nonneg hC hB0n, fun g i => ?_⟩` and prove the remaining obligations. Take `⟨h, k, hh, hk, e⟩` from `DoubleCoset.mk_out_eq_mul Γ K g`. Establish `hg : g = h⁻¹ * ((DoubleCoset.mk Γ K g).out * k⁻¹)`.

Rewrite using `[e]`. Use `group`. Establish `hNg : Nf g = R (k⁻¹)⁻¹ *ᵥ Nf (DoubleCoset.mk Γ K g).out` using `by conv_lhs => rw [hg]`. Rewrite using `[hNΓ _ (Γ.inv_mem hh), hNK _ (K.inv_mem hk)]`. Rewrite using `[hNg]`.

Conclude with `nu_mulVec_le ι _ _ C B0 hC hB0n (hRK _ (K.inv_mem (K.inv_mem hk))) (hle _) i`. Establish `hstep : ∀ (L : List G), a • (R L.prod *ᵥ Nf (g0 * L.prod)) = ∑ x ∈ s, R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod)`. Introduce `L`. Rewrite using `[← Matrix.mulVec_smul, hNeig, Matrix.mulVec_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Simplify using `only [List.prod_append, List.prod_singleton, map_mul, mulVec_mulVec, mul_assoc]`. Establish `hit : ∀ (n : ℕ) (L : List G), (∀ x ∈ L, x ∈ s) → ∀ i, nu ι a ^ n * nu ι ((R L.prod *ᵥ Nf (g0 * L.prod)) i) ≤ C * B * c ^ (L.length + n)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `L hL i`. Use `nu_mulVec_le ι (R L.prod) (Nf (g0 * L.prod)) (C * c ^ L.length) B (mul_nonneg hC (pow_nonneg hc _)) hB0 (hRL L hL) (hB _) i` as an intermediate fact. Simplify using `only [pow_zero, one_mul, add_zero]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `succ n ih`.

Introduce `L hL i`. Establish `e : a * (R L.prod *ᵥ Nf (g0 * L.prod)) i = ∑ x ∈ s, (R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod)) i`. Use `congrFun (hstep L) i` as an intermediate fact. Simplify `this` using `[Finset.sum_apply]`. Establish `hD : 0 ≤ C * B * c ^ (L.length + (n + 1))` using `mul_nonneg (mul_nonneg hC hB0) (pow_nonneg hc _)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[nu_mul']`. Expand and normalize the polynomial expressions, which then agree. Use `_ = nu ι a ^ n * nu ι (∑ x ∈ s, (R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod)) i) := by rw [e]`. Use `_ ≤ C * B * c ^ (L.length + (n + 1)) := by`.

Distinguish the cases in `hz : nu ι a ^ n = 0`. Rewrite using `[hz, zero_mul]`. Conclude with `hD`. Establish `hp : 0 < nu ι a ^ n` using `lt_of_le_of_ne (pow_nonneg (nu_nonneg' ι _) _) (Ne.symm hz)`. Rewrite using `[← le_div_iff₀' hp]`.

Use `nu_sum_le' ι _ _ _ (div_nonneg hD hp.le) fun x hx => ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀' hp]`. Use `ih (L ++ [x]) (fun y hy => by` as an intermediate fact. Break down `List.mem_append.mp hy with h | h` into its components or cases. Conclude with `hL y h`.

Simplify using `at h`. Conclude with `h ▸ hx) i`. Simplify `this` using `[List.length_append, add_assoc, add_comm 1 n]`. Establish `hfinal : ∀ n : ℕ, nu ι a ^ n * nu ι (Nf g0 i0) ≤ C * B * c ^ n`. Introduce `n`.

Use `hit n [] (by simp) i0` as an intermediate fact. Simplify `this` using `[hN]`. Establish `hd : 0 < nu ι (Nf g0 i0)` using `nu_pos' ι h0`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Break down `hc.eq_or_lt with h0c | hcpos` into its components or cases. Use `hfinal 1` as an intermediate fact. Rewrite `this`, `hlt` using `[← h0c]`. Simplify using `only [pow_one, mul_zero] at this`. Establish `: 0 < nu ι a * nu ι (Nf g0 i0)` using `mul_pos hlt hd`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr : 1 < nu ι a / c` using `(one_lt_div hcpos).mpr hlt`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (C * B / nu ι (Nf g0 i0)) hr`. Rewrite `hn` using `[div_lt_iff₀ hd, div_pow, div_mul_eq_mul_div, lt_div_iff₀ (pow_pos hcpos n)]`. Combine the linear relations using `[hfinal n]`.
-/
theorem absBound :
    UpperTheory.V.Z.Int.AbsBound := by
  intro l _ ι G _ Γ K I _ R F s a c C hc hfin hF hΓ hK heig hRK hRL
  set Nf : G → I → ℂ := fun g => R g⁻¹ *ᵥ F g with hN
  have Rinv : ∀ g, R g⁻¹ * R g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have Rinv' : ∀ g, R g * R g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hNΓ : ∀ γ ∈ Γ, ∀ g, Nf (γ * g) = Nf g := by
    intro γ hγ g
    simp only [hN, hΓ γ hγ g, _root_.mul_inv_rev, map_mul, mulVec_mulVec]
    rw [mul_assoc, Rinv, mul_one]
  have hNK : ∀ k ∈ K, ∀ g, Nf (g * k) = R k⁻¹ *ᵥ Nf g := by
    intro k hk g
    simp only [hN, hK k hk g, _root_.mul_inv_rev, map_mul, mulVec_mulVec]
  have hNeig : ∀ h, a • Nf h = ∑ x ∈ s, R x *ᵥ Nf (h * x) := by
    intro h
    have h1 : ∀ x, R x *ᵥ Nf (h * x) = R h⁻¹ *ᵥ F (h * x) := by
      intro x
      simp only [hN, _root_.mul_inv_rev, map_mul, mulVec_mulVec]
      rw [← mul_assoc, Rinv', one_mul]
    simp only [h1]
    simp only [hN]
    rw [← Matrix.mulVec_smul, ← heig h, Matrix.mulVec_sum]

  obtain ⟨g0, i0, h0⟩ : ∃ g i, Nf g i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hF
    funext g
    have : F g = R g *ᵥ Nf g := by
      simp only [hN, mulVec_mulVec, Rinv', one_mulVec]
    rw [this, show Nf g = 0 from funext (hcon g)]
    simp
  have hC : 0 ≤ C := (nu_nonneg' ι _).trans (hRK 1 K.one_mem i0 i0)

  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ g i, nu ι (Nf g i) ≤ B := by
    haveI := hfin
    letI := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))
    set B0 : ℝ := ∑ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G), ∑ i, nu ι (Nf q.out i) with hB0
    have hB0n : 0 ≤ B0 := Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun i _ => nu_nonneg' ι _
    have hle : ∀ (q : DoubleCoset.Quotient (Γ : Set G) (K : Set G)) j, nu ι (Nf q.out j) ≤ B0 := by
      intro q j
      calc nu ι (Nf q.out j) ≤ ∑ i, nu ι (Nf q.out i) :=
            Finset.single_le_sum (f := fun i => nu ι (Nf q.out i)) (fun i _ => nu_nonneg' ι _) (Finset.mem_univ j)
        _ ≤ B0 := Finset.single_le_sum (f := fun q : DoubleCoset.Quotient (Γ : Set G) (K : Set G) => ∑ i, nu ι (Nf q.out i))
            (fun q _ => Finset.sum_nonneg fun i _ => nu_nonneg' ι _) (Finset.mem_univ q)
    refine ⟨C * B0, mul_nonneg hC hB0n, fun g i => ?_⟩
    obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K g
    have hg : g = h⁻¹ * ((DoubleCoset.mk Γ K g).out * k⁻¹) := by
      rw [e]; group
    have hNg : Nf g = R (k⁻¹)⁻¹ *ᵥ Nf (DoubleCoset.mk Γ K g).out := by
      conv_lhs => rw [hg]
      rw [hNΓ _ (Γ.inv_mem hh), hNK _ (K.inv_mem hk)]
    rw [hNg]
    exact nu_mulVec_le ι _ _ C B0 hC hB0n (hRK _ (K.inv_mem (K.inv_mem hk))) (hle _) i

  have hstep : ∀ (L : List G), a • (R L.prod *ᵥ Nf (g0 * L.prod)) =
      ∑ x ∈ s, R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod) := by
    intro L
    rw [← Matrix.mulVec_smul, hNeig, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [List.prod_append, List.prod_singleton, map_mul, mulVec_mulVec, mul_assoc]
  have hit : ∀ (n : ℕ) (L : List G), (∀ x ∈ L, x ∈ s) → ∀ i,
      nu ι a ^ n * nu ι ((R L.prod *ᵥ Nf (g0 * L.prod)) i) ≤ C * B * c ^ (L.length + n) := by
    intro n
    induction n with
    | zero =>
      intro L hL i
      have := nu_mulVec_le ι (R L.prod) (Nf (g0 * L.prod)) (C * c ^ L.length) B
        (mul_nonneg hC (pow_nonneg hc _)) hB0 (hRL L hL) (hB _) i
      simp only [pow_zero, one_mul, add_zero]
      calc _ ≤ _ := this
        _ = _ := by ring
    | succ n ih =>
      intro L hL i
      have e : a * (R L.prod *ᵥ Nf (g0 * L.prod)) i =
          ∑ x ∈ s, (R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod)) i := by
        have := congrFun (hstep L) i
        simpa [Finset.sum_apply] using this
      have hD : 0 ≤ C * B * c ^ (L.length + (n + 1)) :=
        mul_nonneg (mul_nonneg hC hB0) (pow_nonneg hc _)
      calc nu ι a ^ (n + 1) * nu ι ((R L.prod *ᵥ Nf (g0 * L.prod)) i)
          = nu ι a ^ n * nu ι (a * (R L.prod *ᵥ Nf (g0 * L.prod)) i) := by
            rw [nu_mul']; ring
        _ = nu ι a ^ n * nu ι (∑ x ∈ s, (R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod)) i) := by rw [e]
        _ ≤ C * B * c ^ (L.length + (n + 1)) := by
            by_cases hz : nu ι a ^ n = 0
            · rw [hz, zero_mul]; exact hD
            have hp : 0 < nu ι a ^ n := lt_of_le_of_ne (pow_nonneg (nu_nonneg' ι _) _) (Ne.symm hz)
            rw [← le_div_iff₀' hp]
            refine nu_sum_le' ι _ _ _ (div_nonneg hD hp.le) fun x hx => ?_
            rw [le_div_iff₀' hp]
            have := ih (L ++ [x]) (fun y hy => by
              rcases List.mem_append.mp hy with h | h
              · exact hL y h
              · simp at h; exact h ▸ hx) i
            simpa [List.length_append, add_assoc, add_comm 1 n] using this
  have hfinal : ∀ n : ℕ, nu ι a ^ n * nu ι (Nf g0 i0) ≤ C * B * c ^ n := by
    intro n
    have := hit n [] (by simp) i0
    simpa [hN] using this
  have hd : 0 < nu ι (Nf g0 i0) := nu_pos' ι h0
  by_contra hlt
  push_neg at hlt
  rcases hc.eq_or_lt with h0c | hcpos
  · have := hfinal 1
    rw [← h0c] at this hlt
    simp only [pow_one, mul_zero] at this
    have : 0 < nu ι a * nu ι (Nf g0 i0) := mul_pos hlt hd
    linarith
  · have hr : 1 < nu ι a / c := (one_lt_div hcpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C * B / nu ι (Nf g0 i0)) hr
    rw [div_lt_iff₀ hd, div_pow, div_mul_eq_mul_div, lt_div_iff₀ (pow_pos hcpos n)] at hn
    linarith [hfinal n]

end UpperTheory.V.Z.Int
