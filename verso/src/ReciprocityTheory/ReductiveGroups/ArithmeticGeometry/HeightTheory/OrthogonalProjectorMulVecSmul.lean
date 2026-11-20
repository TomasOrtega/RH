import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OrthogonalProjectorMulEmbeddingColumns

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder

section Real

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

abbrev hIdx (K : Type) [Field K] [NumberField K] (r : ℕ) : Type := (K →+* ℂ) × Fin r × Fin 2

noncomputable def hReF (x : (K →+* ℂ) → Fin r → ℂ) : hIdx K r → ℝ :=
  fun p => if p.2.2 = 0 then (x p.1 p.2.1).re else (x p.1 p.2.1).im

noncomputable def hRe (x : (K →+* ℂ) → Fin r → ℂ) : EuclideanSpace ℝ (hIdx K r) :=
  WithLp.toLp 2 (hReF x)

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [hReF, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem realCoordsFun_add (x y : (K →+* ℂ) → Fin r → ℂ) : hReF (x + y) = hReF x + hReF y := by
  funext p
  simp only [hReF, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [hRe, PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.re_sum, dotProduct, Pi.star_apply, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, hReF]`. Use `Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_hRe (x y : (K →+* ℂ) → Fin r → ℂ) :
    inner ℝ (hRe x) (hRe y) = (∑ σ, star (x σ) ⬝ᵥ y σ).re := by
  simp only [hRe, PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.re_sum, dotProduct, Pi.star_apply,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, hReF]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun l _ => ?_
  simp
  ring

/- English proof (translation)
Simplify using `only [dotProduct, Complex.re_sum, hns, Pi.star_apply, Complex.star_def]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem star_dotProduct_self_re {r : ℕ} (v : Fin r → ℂ) : (star v ⬝ᵥ v).re = hns v := by
  simp only [dotProduct, Complex.re_sum, hns, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Rewrite using `[← real_inner_self_eq_norm_sq, inner_hRe, Complex.re_sum]`. Conclude with `Finset.sum_congr rfl fun σ _ => star_dotProduct_self_re _`.
-/
theorem norm_realCoords_sq (x : (K →+* ℂ) → Fin r → ℂ) : ‖hRe x‖ ^ 2 = ∑ σ, hns (x σ) := by
  rw [← real_inner_self_eq_norm_sq, inner_hRe, Complex.re_sum]
  exact Finset.sum_congr rfl fun σ _ => star_dotProduct_self_re _

noncomputable def hpv (b : Fin k → Fin r → K) (q : Fin r → K) : EuclideanSpace ℝ (hIdx K r) :=
  hRe fun σ => hPm σ b *ᵥ fun l => σ (q l)

/- English proof (translation)
Establish `e : (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ ((q + q') l)) = (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) + (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q' l))`. Use function extensionality and compare the values at `σ`. Rewrite using `[Pi.add_apply, ← mulVec_add]`. Use `congr 1`. Use function extensionality and compare the values at `l`.

Simplify using the standard rewrite rules. Simplify using `only [hpv, hRe, e, realCoordsFun_add, WithLp.toLp_add]`.
-/
theorem projectedVector_add (b : Fin k → Fin r → K) (q q' : Fin r → K) :
    hpv b (q + q') = hpv b q + hpv b q' := by
  have e : (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ ((q + q') l)) =
      (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) +
        (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q' l)) := by
    funext σ
    rw [Pi.add_apply, ← mulVec_add]
    congr 1
    funext l
    simp
  simp only [hpv, hRe, e, realCoordsFun_add, WithLp.toLp_add]

/- English proof (translation)
Establish `e : hReF (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ ((0 : Fin r → K) l)) = 0`. Use function extensionality and compare the values at `p`. Simplify using `only [hReF, Pi.zero_apply, map_zero]`. Rewrite using `[show (fun _ : Fin r => (0 : ℂ)) = 0 from rfl, mulVec_zero]`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `only [hpv, hRe, e, WithLp.toLp_zero]`.
-/
theorem projectedVector_zero (b : Fin k → Fin r → K) : hpv b 0 = 0 := by
  have e : hReF (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ ((0 : Fin r → K) l)) = 0 := by
    funext p
    simp only [hReF, Pi.zero_apply, map_zero]
    rw [show (fun _ : Fin r => (0 : ℂ)) = 0 from rfl, mulVec_zero]
    split_ifs <;> simp
  simp only [hpv, hRe, e, WithLp.toLp_zero]

noncomputable def hpvHom (b : Fin k → Fin r → K) : (Fin r → K) →+ EuclideanSpace ℝ (hIdx K r) where
  toFun := hpv b
  map_zero' := projectedVector_zero b
  map_add' := projectedVector_add b

/- English proof (translation)
Take `⟨l, hl⟩` from `Function.ne_iff.mp hv`. Establish `h1 : 0 < ‖v l‖ ^ 2` using `by positivity`. Conclude with `lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ l))`.
-/
theorem normSqSum_pos {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) : 0 < hns v := by
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hv
  have h1 : 0 < ‖v l‖ ^ 2 := by positivity
  exact lt_of_lt_of_le h1
    (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ l))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h0`. Assume the negation of the conclusion as `hq`. Establish `hpos : Fintype.card (K →+* ℂ) ≠ 0`. Rewrite using `[NumberField.Embeddings.card K ℂ]`.

Conclude with `Module.finrank_pos.ne'`. Take `⟨σ0⟩` from `Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hpos)`. Establish `h1` using `norm_realCoords_sq (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l))`. Rewrite `h1` using `[← hpv, h0, norm_zero]`. Establish `h2 : 0 < ∑ σ, hns (hPm σ b *ᵥ fun l => σ (q l))` using `lt_of_lt_of_le (normSqSum_pos (orthogonalProjector_mulVec_ne_zero σ0 hb hq)) (Finset.single_le_sum (f := fun σ => hns (hPm σ b *ᵥ fun l => σ (q l))) (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ σ0))`.

Rewrite `h2` using `[← h1]`. Evaluate the numerical expressions using `at h2`. Introduce `hq`. Establish `e : (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) = 0`. Use function extensionality and compare the values at `σ`.

Conclude with `orthogonalProjector_mulVec_eq_zero σ hb hq`. Establish `e2 : hReF (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) = 0`. Rewrite using `[e]`. Use function extensionality and compare the values at `p`. Simplify using `[hReF]`.

Simplify using `only [hpv, hRe, e2, WithLp.toLp_zero]`.
-/
theorem projectedVector_eq_zero_iff {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (q : Fin r → K) : hpv b q = 0 ↔ q ∈ Submodule.span K (Set.range b) := by
  constructor
  · intro h0
    by_contra hq
    have hpos : Fintype.card (K →+* ℂ) ≠ 0 := by
      rw [NumberField.Embeddings.card K ℂ]; exact Module.finrank_pos.ne'
    obtain ⟨σ0⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hpos)
    have h1 := norm_realCoords_sq (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l))
    rw [← hpv, h0, norm_zero] at h1
    have h2 : 0 < ∑ σ, hns (hPm σ b *ᵥ fun l => σ (q l)) :=
      lt_of_lt_of_le (normSqSum_pos (orthogonalProjector_mulVec_ne_zero σ0 hb hq))
        (Finset.single_le_sum (f := fun σ => hns (hPm σ b *ᵥ fun l => σ (q l)))
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ σ0))
    rw [← h1] at h2
    norm_num at h2
  · intro hq
    have e : (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) = 0 := by
      funext σ
      exact orthogonalProjector_mulVec_eq_zero σ hb hq
    have e2 : hReF (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) = 0 := by
      rw [e]; funext p; simp [hReF]
    simp only [hpv, hRe, e2, WithLp.toLp_zero]

/- English proof (translation)
Rewrite using `[← mulVec_smul]`. Use `congr 1`. Use function extensionality and compare the values at `l`. Simplify using the standard rewrite rules.
-/
theorem orthogonalProjector_mulVec_smul (σ : K →+* ℂ) (b : Fin k → Fin r → K) (a : K) (x : Fin r → K) :
    (hPm σ b *ᵥ fun l => σ ((a • x) l)) = σ a • (hPm σ b *ᵥ fun l => σ (x l)) := by
  rw [← mulVec_smul]
  congr 1
  funext l
  simp

/- English proof (translation)
Rewrite using `[hpv, hpv, inner_hRe]`. Use `congr 1`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[orthogonalProjector_mulVec_smul, orthogonalProjector_mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_projectedVector_smul (b : Fin k → Fin r → K) (a a' : K) (x y : Fin r → K) :
    inner ℝ (hpv b (a • x)) (hpv b (a' • y)) =
      (∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l)))).re := by
  rw [hpv, hpv, inner_hRe]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [orthogonalProjector_mulVec_smul, orthogonalProjector_mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, Complex.star_def]
  ring

end Real

end ReciprocityTheory.ChartRestriction.G.T0
