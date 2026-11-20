import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `ht : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)`. Rewrite using `[Submodule.mem_traceDual]`. Introduce `a ha`. Take `⟨γ, rfl⟩` from `Submodule.mem_one.1 ha`. Take `⟨k, hk⟩` from `h γ`.

Use `RingHom.mem_range.2 ⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply]`. Simplify using `using hk.symm`. Establish `h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E)` using `Submodule.mem_one.2 ⟨1, map_one _⟩`. Establish `hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i)` using `fun i => by`.

Rewrite using `[NumberField.integralBasis_apply]`. Conclude with `NumberField.RingOfIntegers.isIntegral_coe _`. Establish `key` using `isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (1 : Submodule (𝓞 E) E) hb h1 ht`. Establish `e : Algebra.discr ℚ (NumberField.integralBasis E) • (1 : E) * t = (NumberField.discr E : E) * t`. Rewrite using `[← NumberField.coe_discr, Algebra.smul_def, mul_one]`.

Simplify using the standard rewrite rules. Rewrite `key` using `[e]`. Then use the resulting hypothesis.
-/
theorem d4l2_dual_int (t : E) (h : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (t * γ) = k) :
    IsIntegral ℤ ((NumberField.discr E : E) * t) := by
  classical
  have ht : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨γ, rfl⟩ := Submodule.mem_one.1 ha
    obtain ⟨k, hk⟩ := h γ
    refine RingHom.mem_range.2 ⟨k, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hk.symm
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i) := fun i => by
    rw [NumberField.integralBasis_apply]
    exact NumberField.RingOfIntegers.isIntegral_coe _
  have key := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 ht
  have e : Algebra.discr ℚ (NumberField.integralBasis E) • (1 : E) * t =
      (NumberField.discr E : E) * t := by
    rw [← NumberField.coe_discr, Algebra.smul_def, mul_one]
    simp
  rwa [e] at key

/- English proof (translation)
Establish `key` using `d4l2_dual_int t h`. Break down `Int.natAbs_eq (NumberField.discr E) with hd | hd` into its components or cases. Establish `e : ((NumberField.discr E).natAbs : E) = (NumberField.discr E : E)` using `by conv_rhs => rw [hd]`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `key`. Establish `e : ((NumberField.discr E).natAbs : E) = -(NumberField.discr E : E)` using `by conv_rhs => rw [hd]`. Simplify using the standard rewrite rules. Rewrite using `[e, neg_mul]`. Conclude with `key.neg`.
-/
theorem d4l2_dual_int' (t : E) (h : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (t * γ) = k) :
    IsIntegral ℤ (((NumberField.discr E).natAbs : E) * t) := by
  have key := d4l2_dual_int t h
  rcases Int.natAbs_eq (NumberField.discr E) with hd | hd
  · have e : ((NumberField.discr E).natAbs : E) = (NumberField.discr E : E) := by
      conv_rhs => rw [hd]
      simp
    rw [e]
    exact key
  · have e : ((NumberField.discr E).natAbs : E) = -(NumberField.discr E : E) := by
      conv_rhs => rw [hd]
      simp
    rw [e, neg_mul]
    exact key.neg

namespace Data

variable {r : ℕ} (X : Data E r)

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]`.
-/
theorem conjugate_conjugate' (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

/- English proof (translation)
Rewrite using `[X.cmType (ComplexEmbedding.conjugate φ), conjugate_conjugate']`.
-/
theorem conj_mem_iff (φ : E →+* ℂ) : ComplexEmbedding.conjugate φ ∈ X.Ψ ↔ φ ∉ X.Ψ := by
  rw [X.cmType (ComplexEmbedding.conjugate φ), conjugate_conjugate']

/- English proof (translation)
Establish `h2 : ∑ φ ∈ X.Ψ, f (ComplexEmbedding.conjugate φ) = ∑ φ ∈ X.Ψᶜ, f φ` using `Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate (fun a ha => Finset.mem_compl.2 fun hc => (X.conj_mem_iff a).1 hc ha) (fun a ha => (X.conj_mem_iff a).2 (Finset.mem_compl.1 ha)) (fun a _ => conjugate_conjugate' a) (fun a _ => conjugate_conjugate' a) (fun a _ …`. Establish `h2' : ∑ x : X.Ψ, f (ComplexEmbedding.conjugate x.1) = ∑ φ ∈ X.Ψᶜ, f φ`. Rewrite using `[← h2]`. Conclude with `Finset.sum_coe_sort X.Ψ (fun φ => f (ComplexEmbedding.conjugate φ))`. Rewrite using `[Finset.sum_add_distrib, h2', Finset.sum_coe_sort X.Ψ f, Finset.sum_add_sum_compl]`.
-/
theorem sum_emb_split (f : (E →+* ℂ) → ℂ) :
    ∑ φ : E →+* ℂ, f φ = ∑ τ : X.Ψ, (f τ.1 + f (ComplexEmbedding.conjugate τ.1)) := by
  classical
  have h2 : ∑ φ ∈ X.Ψ, f (ComplexEmbedding.conjugate φ) = ∑ φ ∈ X.Ψᶜ, f φ :=
    Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate
      (fun a ha => Finset.mem_compl.2 fun hc => (X.conj_mem_iff a).1 hc ha)
      (fun a ha => (X.conj_mem_iff a).2 (Finset.mem_compl.1 ha))
      (fun a _ => conjugate_conjugate' a) (fun a _ => conjugate_conjugate' a) (fun a _ => rfl)
  have h2' : ∑ x : X.Ψ, f (ComplexEmbedding.conjugate x.1) = ∑ φ ∈ X.Ψᶜ, f φ := by
    rw [← h2]
    exact Finset.sum_coe_sort X.Ψ (fun φ => f (ComplexEmbedding.conjugate φ))
  rw [Finset.sum_add_distrib, h2', Finset.sum_coe_sort X.Ψ f, Finset.sum_add_sum_compl]

/- English proof (translation)
Establish `h1 : ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ y`. Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := y)`. Rewrite `h` using `[eq_ratCast]`. Rewrite using `[h]`. Conclude with `Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ fun σ => rfl`.

Rewrite using `[h1, X.sum_emb_split (fun φ => φ y)]`. Both sides reduce to the same expression.
-/
theorem trace_eq_Psi (y : E) :
    ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ τ : X.Ψ, (τ.1 y + conj (τ.1 y)) := by
  have h1 : ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ y := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := y)
    rw [eq_ratCast] at h
    rw [h]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ fun σ => rfl
  rw [h1, X.sum_emb_split (fun φ => φ y)]
  rfl

/- English proof (translation)
Establish `h` using `congrArg Complex.re (X.trace_eq_Psi y)`. Simplify using `only [Complex.ratCast_re, Complex.re_sum, Complex.add_re, Complex.conj_re] at h`. Rewrite using `[Complex.re_sum, h, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem re_sum_Psi (y : E) : (∑ τ : X.Ψ, τ.1 y).re = (Algebra.trace ℚ E y : ℝ) / 2 := by
  have h := congrArg Complex.re (X.trace_eq_Psi y)
  simp only [Complex.ratCast_re, Complex.re_sum, Complex.add_re, Complex.conj_re] at h
  rw [Complex.re_sum, h, Finset.sum_add_distrib]
  ring

/- English proof (translation)
Establish `h` using `X.sum_emb_split (fun _ => (1 : ℂ))`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h`. Rewrite using `[← NumberField.Embeddings.card E ℂ]`. Establish `h' : ((Fintype.card (E →+* ℂ) : ℕ) : ℂ) = ((2 * Fintype.card X.Ψ : ℕ) : ℂ)`. Use `push_cast`.

Take the linear combination `h`. Conclude with `(Nat.cast_injective h').symm`.
-/
theorem card_Psi : 2 * Fintype.card X.Ψ = finrank ℚ E := by
  have h := X.sum_emb_split (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [← NumberField.Embeddings.card E ℂ]
  have h' : ((Fintype.card (E →+* ℂ) : ℕ) : ℂ) = ((2 * Fintype.card X.Ψ : ℕ) : ℂ) := by
    push_cast
    linear_combination h
  exact (Nat.cast_injective h').symm

/- English proof (translation)
Set `P : (X.Ψ → ℂ) → E →ₗ[ℚ] ℝ` to `fun w => { toFun := fun x => (∑ τ : X.Ψ, w τ * τ.1 x).re map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib] map_smul' := fun q x => by`. Simplify using `only [Rat.smul_def, map_mul, map_ratCast, RingHom.id_apply]`. Rewrite using `[show ∑ τ : X.Ψ, w τ * ((q : ℂ) * τ.1 x) = (q : ℂ) * ∑ τ : X.Ψ, w τ * τ.1 x by`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun τ _ => by ring]`.

Rewrite using `[← Complex.ofReal_ratCast, Complex.re_ofReal_mul] }`. Use `set b := NumberField.integralBasis E with hbdef`. Establish `hnd` using `traceForm_nondegenerate ℚ E`. Use `set d := (Algebra.traceForm ℚ E).dualBasis hnd b with hddef`. Use `choose q hq using fun i => hz (NumberField.RingOfIntegers.basis E i)`.

Use `set ω : E := ∑ i, (2 * q i) • d i with hωdef`. Establish `htr : ∀ j, Algebra.trace ℚ E (ω * b j) = 2 * q j`. Introduce `j`. Establish `h : Algebra.traceForm ℚ E ω (b j) = 2 * q j`. Simplify using `only [hωdef, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hddef, LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Simplify `h` using `[Algebra.traceForm_apply]`. Establish `hbj : ∀ j, (b j : E) = ((NumberField.RingOfIntegers.basis E j : 𝓞 E) : E)` using `fun j => by`. Rewrite using `[hbdef, NumberField.integralBasis_apply]`. Use `set w : X.Ψ → ℂ := fun τ => z τ - τ.1 ω with hwdef`. Establish `hPb : ∀ j, P w (b j) = 0`.

Introduce `j`. Use `show (∑ τ : X.Ψ, (z τ - τ.1 ω) * τ.1 (b j)).re = 0`. Simplify using `only [sub_mul, Finset.sum_sub_distrib, Complex.sub_re]`. Establish `e1 : (∑ τ : X.Ψ, z τ * τ.1 (b j)).re = q j`. Rewrite using `[hbj]`.

Conclude with `hq j`. Establish `e2 : (∑ τ : X.Ψ, τ.1 ω * τ.1 (b j)).re = q j`. Rewrite using `[show ∑ τ : X.Ψ, τ.1 ω * τ.1 (b j) = ∑ τ : X.Ψ, τ.1 (ω * b j) from Finset.sum_congr rfl fun τ _ => (map_mul τ.1 ω (b j)).symm]`. Rewrite using `[X.re_sum_Psi, htr]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, sub_self]`. Establish `hP0 : P w = 0` using `b.ext fun j => by rw [hPb j, LinearMap.zero_apply]`. Establish `hPw : ∀ x : E, (∑ τ : X.Ψ, w τ * τ.1 x).re = 0` using `fun x => LinearMap.congr_fun hP0 x`. Set `W : (E →+* ℂ) → ℂ` to `fun φ => if h : φ ∈ X.Ψ then w ⟨φ, h⟩ else conj (w ⟨ComplexEmbedding.conjugate φ, (X.conj_mem_iff φ).2 h⟩)`.

Establish `hW1 : ∀ τ : X.Ψ, W τ.1 = w τ` using `fun τ => by`. Simplify using `only [W, dif_pos τ.2]`. Establish `hW2 : ∀ τ : X.Ψ, W (ComplexEmbedding.conjugate τ.1) = conj (w τ)` using `fun τ => by`. Establish `hn : ComplexEmbedding.conjugate τ.1 ∉ X.Ψ` using `fun hc => (X.conj_mem_iff τ.1).1 hc τ.2`. Simplify using `only [W, dif_neg hn]`.

Conclude with `congrArg (fun σ : X.Ψ => conj (w σ)) (Subtype.ext (conjugate_conjugate' τ.1))`. Establish `hW : ∀ x : E, ∑ φ : E →+* ℂ, W φ * φ x = 0`. Introduce `x`. Rewrite using `[X.sum_emb_split (fun φ => W φ * φ x)]`. Simplify using `only [hW1, hW2, ComplexEmbedding.conjugate_coe_eq, ← map_mul (starRingEnd ℂ), Complex.add_conj]`.

Rewrite using `[← Complex.ofReal_sum, ← Finset.mul_sum, ← Complex.re_sum, hPw x, mul_zero, Complex.ofReal_zero]`. Establish `hli : LinearIndependent ℂ (fun φ : E →+* ℂ => (φ : E → ℂ))` using `(linearIndependent_monoidHom E ℂ).comp (fun φ : E →+* ℂ => (φ : E →* ℂ)) (fun a a' h => RingHom.ext fun x => congrArg (fun f : E →* ℂ => f x) h)`. Establish `hsumfun : ∑ φ : E →+* ℂ, W φ • (φ : E → ℂ) = 0`. Use function extensionality and compare the values at `x`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`.

Conclude with `hW x`. Use `⟨ω, fun τ => ?_⟩` and prove the remaining obligations. Establish `h0` using `Fintype.linearIndependent_iff.1 hli W hsumfun τ.1`. Rewrite `h0` using `[hW1]`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem exists_emb_eq (z : X.Ψ → ℂ)
    (hz : ∀ γ : 𝓞 E, ∃ q : ℚ, (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = q) :
    ∃ ω : E, ∀ τ : X.Ψ, z τ = τ.1 ω := by
  classical
  let P : (X.Ψ → ℂ) → E →ₗ[ℚ] ℝ := fun w =>
    { toFun := fun x => (∑ τ : X.Ψ, w τ * τ.1 x).re
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun q x => by
        simp only [Rat.smul_def, map_mul, map_ratCast, RingHom.id_apply]
        rw [show ∑ τ : X.Ψ, w τ * ((q : ℂ) * τ.1 x) = (q : ℂ) * ∑ τ : X.Ψ, w τ * τ.1 x by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun τ _ => by ring]
        rw [← Complex.ofReal_ratCast, Complex.re_ofReal_mul] }
  set b := NumberField.integralBasis E with hbdef
  have hnd := traceForm_nondegenerate ℚ E
  set d := (Algebra.traceForm ℚ E).dualBasis hnd b with hddef
  choose q hq using fun i => hz (NumberField.RingOfIntegers.basis E i)
  set ω : E := ∑ i, (2 * q i) • d i with hωdef
  have htr : ∀ j, Algebra.trace ℚ E (ω * b j) = 2 * q j := by
    intro j
    have h : Algebra.traceForm ℚ E ω (b j) = 2 * q j := by
      simp only [hωdef, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hddef,
        LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simpa [Algebra.traceForm_apply] using h
  have hbj : ∀ j, (b j : E) = ((NumberField.RingOfIntegers.basis E j : 𝓞 E) : E) := fun j => by
    rw [hbdef, NumberField.integralBasis_apply]
  set w : X.Ψ → ℂ := fun τ => z τ - τ.1 ω with hwdef
  have hPb : ∀ j, P w (b j) = 0 := by
    intro j
    show (∑ τ : X.Ψ, (z τ - τ.1 ω) * τ.1 (b j)).re = 0
    simp only [sub_mul, Finset.sum_sub_distrib, Complex.sub_re]
    have e1 : (∑ τ : X.Ψ, z τ * τ.1 (b j)).re = q j := by
      rw [hbj]
      exact hq j
    have e2 : (∑ τ : X.Ψ, τ.1 ω * τ.1 (b j)).re = q j := by
      rw [show ∑ τ : X.Ψ, τ.1 ω * τ.1 (b j) = ∑ τ : X.Ψ, τ.1 (ω * b j) from
        Finset.sum_congr rfl fun τ _ => (map_mul τ.1 ω (b j)).symm]
      rw [X.re_sum_Psi, htr]
      push_cast
      ring
    rw [e1, e2, sub_self]
  have hP0 : P w = 0 := b.ext fun j => by rw [hPb j, LinearMap.zero_apply]
  have hPw : ∀ x : E, (∑ τ : X.Ψ, w τ * τ.1 x).re = 0 := fun x => LinearMap.congr_fun hP0 x
  let W : (E →+* ℂ) → ℂ := fun φ =>
    if h : φ ∈ X.Ψ then w ⟨φ, h⟩ else conj (w ⟨ComplexEmbedding.conjugate φ, (X.conj_mem_iff φ).2 h⟩)
  have hW1 : ∀ τ : X.Ψ, W τ.1 = w τ := fun τ => by
    simp only [W, dif_pos τ.2]
  have hW2 : ∀ τ : X.Ψ, W (ComplexEmbedding.conjugate τ.1) = conj (w τ) := fun τ => by
    have hn : ComplexEmbedding.conjugate τ.1 ∉ X.Ψ := fun hc => (X.conj_mem_iff τ.1).1 hc τ.2
    simp only [W, dif_neg hn]
    exact congrArg (fun σ : X.Ψ => conj (w σ)) (Subtype.ext (conjugate_conjugate' τ.1))
  have hW : ∀ x : E, ∑ φ : E →+* ℂ, W φ * φ x = 0 := by
    intro x
    rw [X.sum_emb_split (fun φ => W φ * φ x)]
    simp only [hW1, hW2, ComplexEmbedding.conjugate_coe_eq, ← map_mul (starRingEnd ℂ),
      Complex.add_conj]
    rw [← Complex.ofReal_sum, ← Finset.mul_sum, ← Complex.re_sum, hPw x, mul_zero,
      Complex.ofReal_zero]
  have hli : LinearIndependent ℂ (fun φ : E →+* ℂ => (φ : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun φ : E →+* ℂ => (φ : E →* ℂ))
      (fun a a' h => RingHom.ext fun x => congrArg (fun f : E →* ℂ => f x) h)
  have hsumfun : ∑ φ : E →+* ℂ, W φ • (φ : E → ℂ) = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hW x
  refine ⟨ω, fun τ => ?_⟩
  have h0 := Fintype.linearIndependent_iff.1 hli W hsumfun τ.1
  rw [hW1] at h0
  exact sub_eq_zero.1 h0

/- English proof (translation)
Establish `h` using `X.card_Psi`. Establish `hpos : 0 < finrank ℚ E` using `Module.finrank_pos`. Rewrite using `[← Fintype.card_pos_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nonempty_Psi : Nonempty X.Ψ := by
  have h := X.card_Psi
  have hpos : 0 < finrank ℚ E := Module.finrank_pos
  rw [← Fintype.card_pos_iff]
  omega

/- English proof (translation)
Establish `hN : ∀ γ : 𝓞 E, ∃ q : ℚ, (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = q`. Introduce `γ`. Take `⟨k, hk⟩` from `hz γ`. Establish `hne : ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hg.ne') (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)))`. Use `⟨(k : ℚ) / ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℚ), ?_⟩` and prove the remaining obligations.

Rewrite using `[Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, eq_div_iff hne, mul_comm]`. Conclude with `hk`. Take `⟨ω, hω⟩` from `X.exists_emb_eq z hN`. Use `⟨ω, hω, ?_⟩` and prove the remaining obligations. Establish `key : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω * γ) = k`.

Introduce `γ`. Take `⟨k, hk⟩` from `hz γ`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hs : ∑ τ : X.Ψ, z τ * τ.1 (γ : E) = ∑ τ : X.Ψ, τ.1 (ω * γ)` using `Finset.sum_congr rfl fun τ _ => by rw [hω τ, map_mul]`. Rewrite `hk` using `[hs, X.re_sum_Psi]`.

Establish `htr : Algebra.trace ℚ E (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω * γ) = ((g * (NumberField.discr E).natAbs : ℕ) : ℚ) * Algebra.trace ℚ E (ω * γ)`. Rewrite using `[mul_assoc, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]`. Rewrite using `[htr]`. Establish `h2 : ((((g * (NumberField.discr E).natAbs : ℕ) : ℚ) * Algebra.trace ℚ E (ω * γ) : ℚ) : ℝ) = ((k : ℚ) : ℝ)`. Move the coercions through the operations in `at hk ⊢`.

Take the linear combination `hk`. Conclude with `h2` after adjusting the coercions. Establish `hint` using `d4l2_dual_int' (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω) key`. Establish `e : (((g * (NumberField.discr E).natAbs ^ 2 : ℕ)) : E) * ω = ((NumberField.discr E).natAbs : E) * (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω)`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hint`.
-/
theorem exists_emb_int (z : X.Ψ → ℂ) (g : ℕ) (hg : 0 < g)
    (hz : ∀ γ : 𝓞 E, ∃ k : ℤ, ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℝ) *
      (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = k) :
    ∃ ω : E, (∀ τ : X.Ψ, z τ = τ.1 ω) ∧
      IsIntegral ℤ (((g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by
  have hN : ∀ γ : 𝓞 E, ∃ q : ℚ, (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = q := by
    intro γ
    obtain ⟨k, hk⟩ := hz γ
    have hne : ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hg.ne')
        (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)))
    refine ⟨(k : ℚ) / ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℚ), ?_⟩
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, eq_div_iff hne, mul_comm]
    exact hk
  obtain ⟨ω, hω⟩ := X.exists_emb_eq z hN
  refine ⟨ω, hω, ?_⟩
  have key : ∀ γ : 𝓞 E, ∃ k : ℤ,
      Algebra.trace ℚ E (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω * γ) = k := by
    intro γ
    obtain ⟨k, hk⟩ := hz γ
    refine ⟨k, ?_⟩
    have hs : ∑ τ : X.Ψ, z τ * τ.1 (γ : E) = ∑ τ : X.Ψ, τ.1 (ω * γ) :=
      Finset.sum_congr rfl fun τ _ => by rw [hω τ, map_mul]
    rw [hs, X.re_sum_Psi] at hk
    have htr : Algebra.trace ℚ E (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω * γ) =
        ((g * (NumberField.discr E).natAbs : ℕ) : ℚ) * Algebra.trace ℚ E (ω * γ) := by
      rw [mul_assoc, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    rw [htr]
    have h2 : ((((g * (NumberField.discr E).natAbs : ℕ) : ℚ) * Algebra.trace ℚ E (ω * γ) : ℚ) : ℝ) =
        ((k : ℚ) : ℝ) := by
      push_cast at hk ⊢
      linear_combination hk
    exact_mod_cast h2
  have hint := d4l2_dual_int' (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω) key
  have e : (((g * (NumberField.discr E).natAbs ^ 2 : ℕ)) : E) * ω =
      ((NumberField.discr E).natAbs : E) * (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω) := by
    push_cast
    ring
  rw [e]
  exact hint

end Data

end ReciprocityTheory.ChartRestriction.G.FD
