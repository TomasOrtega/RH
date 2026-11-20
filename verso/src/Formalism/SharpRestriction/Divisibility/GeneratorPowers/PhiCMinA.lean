import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open NumberField Module FractionalIdeal
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Rewrite using `[show ((Algebra.trace ℚ E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E z) from (eq_ratCast _ _).symm, trace_eq_sum_embeddings ℂ]`. Conclude with `Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)`.
-/
theorem trace_sum (z : E) : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ z := by
  rw [show ((Algebra.trace ℚ E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E z) from (eq_ratCast _ _).symm,
    trace_eq_sum_embeddings ℂ]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)

/- English proof (translation)
Conclude with `⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩`.
-/
theorem emb_nonempty : Nonempty (E →+* ℂ) := by
  exact ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩

/- English proof (translation)
Take `⟨σ⟩` from `emb_nonempty (E := E)`. Conclude with `σ.injective (h σ)`.
-/
theorem eq_of_emb {a b : E} (h : ∀ σ : E →+* ℂ, σ a = σ b) : a = b := by
  obtain ⟨σ⟩ := emb_nonempty (E := E)
  exact σ.injective (h σ)

section Conj

variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj

/- English proof (translation)
The claim follows from `eq_of_emb fun φ => by rw [hcj, map_add, star_add, map_add, hcj, hcj]`.
-/
theorem cj_add (a b : E) : cj (a + b) = cj a + cj b := eq_of_emb fun φ => by rw [hcj, map_add, star_add, map_add, hcj, hcj]

/- English proof (translation)
The claim follows from `eq_of_emb fun φ => by rw [hcj, map_mul, star_mul', map_mul, hcj, hcj]`.
-/
theorem cj_mul (a b : E) : cj (a * b) = cj a * cj b := eq_of_emb fun φ => by rw [hcj, map_mul, star_mul', map_mul, hcj, hcj]

/- English proof (translation)
The claim follows from `eq_of_emb fun φ => by rw [hcj, map_one, star_one]`.
-/
theorem cj_one : cj 1 = 1 := eq_of_emb fun φ => by rw [hcj, map_one, star_one]

/- English proof (translation)
The claim follows from `eq_of_emb fun φ => by rw [hcj, map_zero, star_zero]`.
-/
theorem cj_zero : cj 0 = 0 := eq_of_emb fun φ => by rw [hcj, map_zero, star_zero]

/- English proof (translation)
The claim follows from `eq_of_emb fun φ => by rw [hcj, hcj, star_star]`.
-/
theorem cj_cj (a : E) : cj (cj a) = a := eq_of_emb fun φ => by rw [hcj, hcj, star_star]

def cjR : E →+* E where
  toFun := cj
  map_one' := cj_one hcj
  map_mul' := cj_mul hcj
  map_zero' := cj_zero hcj
  map_add' := cj_add hcj

/- English proof (translation)
Apply `Rat.cast_injective (α := ℂ)` to reduce the goal to its premises. Rewrite using `[trace_sum, trace_sum]`. Repeatedly rewrite using `[hcj]`. Rewrite using `[← star_sum, ← trace_sum]`. Conclude with `map_ratCast (starRingEnd ℂ) _`.
-/
theorem trace_cj (z : E) : Algebra.trace ℚ E (cj z) = Algebra.trace ℚ E z := by
  apply Rat.cast_injective (α := ℂ)
  rw [trace_sum, trace_sum]
  simp_rw [hcj]
  rw [← star_sum, ← trace_sum]
  exact map_ratCast (starRingEnd ℂ) _

/- English proof (translation)
Conclude with `⟨⟨cj c, c.isIntegral_coe.map (cjR hcj).toIntAlgHom⟩, rfl⟩`.
-/
theorem cj_integral (c : 𝓞 E) : ∃ c' : 𝓞 E, (c' : E) = cj c := by
  exact ⟨⟨cj c, c.isIntegral_coe.map (cjR hcj).toIntAlgHom⟩, rfl⟩

/- English proof (translation)
The claim follows from `eq_of_emb fun φ => by rw [hcj, map_ratCast]; exact map_ratCast (starRingEnd ℂ) q`.
-/
theorem cj_ratCast (q : ℚ) : cj (q : E) = q := eq_of_emb fun φ => by rw [hcj, map_ratCast]; exact map_ratCast (starRingEnd ℂ) q

/- English proof (translation)
Rewrite using `[Rat.smul_def, Rat.smul_def, cj_mul hcj, cj_ratCast hcj]`.
-/
theorem cj_smul (q : ℚ) (a : E) : cj (q • a) = q • cj a := by
  rw [Rat.smul_def, Rat.smul_def, cj_mul hcj, cj_ratCast hcj]

/- English proof (translation)
The claim follows from `eq_of_emb fun φ => by rw [hcj, map_neg, star_neg, map_neg, hcj]`.
-/
theorem cj_neg (a : E) : cj (-a) = -cj a := eq_of_emb fun φ => by rw [hcj, map_neg, star_neg, map_neg, hcj]

/- English proof (translation)
Take `⟨z, hz⟩` from `hne`. Establish `hex : ∃ c : 𝓞 E, cj (c : E) ≠ c`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Apply `hz` to reduce the goal to its premises.

Set `f : E →ₗ[ℚ] E` to `{ toFun := cj, map_add' := cj_add hcj, map_smul' := fun q a => cj_smul hcj q a }`. Establish `hf : f = LinearMap.id` using `(integralBasis E).ext fun i => by show cj (integralBasis E i) = integralBasis E i`. Rewrite using `[integralBasis_apply]`. Conclude with `hall _`. Conclude with `LinearMap.congr_fun hf z`.

Take `⟨c, hc⟩` from `hex`. Take `⟨c', hc'⟩` from `cj_integral hcj c`. Establish `hθ : ((c - c' : 𝓞 E) : E) = (c : E) - cj (c : E)`. Rewrite using `[← hc']`. Apply the tactic sequence `first | rfl | (push_cast; rfl) | norm_cast`.

Use `⟨c - c', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hθ]`. Conclude with `sub_ne_zero.mpr (Ne.symm hc)`. Rewrite using `[hθ, sub_eq_add_neg, cj_add hcj, cj_neg hcj, cj_cj hcj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_theta (hne : ∃ z : E, cj z ≠ z) :
    ∃ θ : 𝓞 E, (θ : E) ≠ 0 ∧ cj (θ : E) = -(θ : E) := by
  obtain ⟨z, hz⟩ := hne
  have hex : ∃ c : 𝓞 E, cj (c : E) ≠ c := by
    by_contra hall
    push_neg at hall
    apply hz
    let f : E →ₗ[ℚ] E :=
      { toFun := cj, map_add' := cj_add hcj, map_smul' := fun q a => cj_smul hcj q a }
    have hf : f = LinearMap.id := (integralBasis E).ext fun i => by
      show cj (integralBasis E i) = integralBasis E i
      rw [integralBasis_apply]
      exact hall _
    exact LinearMap.congr_fun hf z
  obtain ⟨c, hc⟩ := hex
  obtain ⟨c', hc'⟩ := cj_integral hcj c
  have hθ : ((c - c' : 𝓞 E) : E) = (c : E) - cj (c : E) := by
    rw [← hc']
    first | rfl | (push_cast; rfl) | norm_cast
  refine ⟨c - c', ?_, ?_⟩
  · rw [hθ]
    exact sub_ne_zero.mpr (Ne.symm hc)
  · rw [hθ, sub_eq_add_neg, cj_add hcj, cj_neg hcj, cj_cj hcj]
    ring

end Conj

def ed (E : Type) [Field E] [NumberField E] : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)

/- English proof (translation)
Establish `h` using `LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E) (integralBasis E) i j`. Rewrite `h` using `[Algebra.traceForm_apply]`. Conclude with `h`.
-/
theorem tr_ed_eb (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (ed E i * integralBasis E j) = if j = i then 1 else 0 := by
  have h := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E) (integralBasis E) i j
  rw [Algebra.traceForm_apply] at h
  exact h

/- English proof (translation)
Establish `h : (integralBasis E).coord i = (Algebra.trace ℚ E).comp (LinearMap.mulLeft ℚ (ed E i))` using `(integralBasis E).ext fun j => by show (integralBasis E).repr (integralBasis E j) i = Algebra.trace ℚ E (ed E i * integralBasis E j)`. Rewrite using `[Module.Basis.repr_self, tr_ed_eb, Finsupp.single_apply]`. Conclude with `LinearMap.congr_fun h z`.
-/
theorem eb_repr (z : E) (i : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (integralBasis E).repr z i = Algebra.trace ℚ E (ed E i * z) := by
  have h : (integralBasis E).coord i =
      (Algebra.trace ℚ E).comp (LinearMap.mulLeft ℚ (ed E i)) := (integralBasis E).ext fun j => by
    show (integralBasis E).repr (integralBasis E j) i = Algebra.trace ℚ E (ed E i * integralBasis E j)
    rw [Module.Basis.repr_self, tr_ed_eb, Finsupp.single_apply]
  exact LinearMap.congr_fun h z

/- English proof (translation)
Rewrite using `[← eb_repr]`. Establish `h` using `integralBasis_repr_apply E c i`. Simplify using `using h`.
-/
theorem tr_ed_int (c : 𝓞 E) (i : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (ed E i * (c : E)) = ((RingOfIntegers.basis E).repr c i : ℚ) := by
  rw [← eb_repr]
  have h := integralBasis_repr_apply E c i
  simpa using h

open scoped Classical in

/- English proof (translation)
Set `P : Matrix (E →+* ℂ) (Free.ChooseBasisIndex ℤ (𝓞 E)) ℂ` to `Matrix.of fun ρ i => ρ (integralBasis E i)`. Set `Q : Matrix (Free.ChooseBasisIndex ℤ (𝓞 E)) (E →+* ℂ) ℂ` to `Matrix.of fun i ρ => ρ (ed E i)`. Establish `hQP : Q * P = 1`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Q, P, Matrix.of_apply, Matrix.one_apply]`.

Repeatedly rewrite using `[← map_mul]`. Rewrite using `[← trace_sum, tr_ed_eb]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`. Establish `hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* ℂ)`. Rewrite using `[← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, NumberField.Embeddings.card]`. Establish `hPQ : P * Q = 1` using `(Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hQP`. Establish `h` using `congrFun (congrFun hPQ τ) σ`.

Simplify using `only [Matrix.mul_apply, P, Q, Matrix.of_apply, Matrix.one_apply] at h`. Use `h using 1` and compare the differences between its conclusion and the goal. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Conclude with `if_congr eq_comm rfl rfl`.
-/
theorem ortho (σ τ : E →+* ℂ) :
    ∑ i, σ (ed E i) * τ (integralBasis E i) = if σ = τ then 1 else 0 := by
  classical
  let P : Matrix (E →+* ℂ) (Free.ChooseBasisIndex ℤ (𝓞 E)) ℂ := Matrix.of fun ρ i => ρ (integralBasis E i)
  let Q : Matrix (Free.ChooseBasisIndex ℤ (𝓞 E)) (E →+* ℂ) ℂ := Matrix.of fun i ρ => ρ (ed E i)
  have hQP : Q * P = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Q, P, Matrix.of_apply, Matrix.one_apply]
    simp_rw [← map_mul]
    rw [← trace_sum, tr_ed_eb]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* ℂ) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, NumberField.Embeddings.card]
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hQP
  have h := congrFun (congrFun hPQ τ) σ
  simp only [Matrix.mul_apply, P, Q, Matrix.of_apply, Matrix.one_apply] at h
  convert h using 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · exact if_congr eq_comm rfl rfl

open scoped Classical in
/- English proof (translation)
Use `eq_of_emb fun σ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, map_one]`. Repeatedly rewrite using `[map_mul]`. Rewrite using `[ortho σ σ, if_pos rfl]`.
-/
theorem casimir : ∑ i, ed E i * integralBasis E i = 1 := by
  refine eq_of_emb fun σ => ?_
  rw [map_sum, map_one]
  simp_rw [map_mul]
  rw [ortho σ σ, if_pos rfl]

abbrev Dinv (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]`. Prove the components needed by the constructor for the conclusion. Introduce `h c`. Take `⟨m, hm⟩` from `h (c : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨c, rfl⟩)`. Conclude with `⟨m, by rw [← Algebra.traceForm_apply, ← hm, eq_intCast]⟩`.

Introduce `h a ha`. Take `⟨c, rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp ha`. Take `⟨m, hm⟩` from `h c`. Conclude with `⟨m, by rw [eq_intCast, Algebra.traceForm_apply]; exact hm.symm⟩`.
-/
theorem mem_Dinv {z : E} : z ∈ Dinv E ↔ ∀ c : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (z * c) = m := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]
  constructor
  · intro h c
    obtain ⟨m, hm⟩ := h (c : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨c, rfl⟩)
    exact ⟨m, by rw [← Algebra.traceForm_apply, ← hm, eq_intCast]⟩
  · intro h a ha
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨m, hm⟩ := h c
    exact ⟨m, by rw [eq_intCast, Algebra.traceForm_apply]; exact hm.symm⟩

/- English proof (translation)
The claim follows from `mem_Dinv.mpr fun c => ⟨_, tr_ed_int c i⟩`.
-/
theorem ed_mem (i : Free.ChooseBasisIndex ℤ (𝓞 E)) : ed E i ∈ Dinv E := mem_Dinv.mpr fun c => ⟨_, tr_ed_int c i⟩

/- English proof (translation)
Rewrite `hz`, the goal using `[mem_Dinv]`. Introduce `c`. Take `⟨c', hc'⟩` from `cj_integral hcj c`. Take `⟨m, hm⟩` from `hz c'`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hm, hc', ← trace_cj hcj (z * cj c), cj_mul hcj, cj_cj hcj]`.
-/
theorem cj_mem_Dinv {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
    {z : E} (hz : z ∈ Dinv E) : cj z ∈ Dinv E := by
  rw [mem_Dinv] at hz ⊢
  intro c
  obtain ⟨c', hc'⟩ := cj_integral hcj c
  obtain ⟨m, hm⟩ := hz c'
  refine ⟨m, ?_⟩
  rw [← hm, hc', ← trace_cj hcj (z * cj c), cj_mul hcj, cj_cj hcj]

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
