import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.SemistableReduction.ShareBallA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.TraceMemPrimeOfPowMulVecMemSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped Matrix

noncomputable section

namespace GlobalTheory.SmallElement

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Rewrite using `[eq_top_iff, ← X.Λ_span, Submodule.span_le]`. Introduce `x hx`. Establish `h1` using `X.NA_sub x hx`. Establish `hNA : (X.NA : E) ≠ 0` using `by exact_mod_cast X.NA_pos.ne'`. Establish `e : x = (X.NA : E)⁻¹ • ((X.NA : E) • x)` using `by rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h1)`.
-/
theorem span_L' {r : ℕ} (X : DataX E r) :
    Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by
  rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
  intro x hx
  have h1 := X.NA_sub x hx
  have hNA : (X.NA : E) ≠ 0 := by exact_mod_cast X.NA_pos.ne'
  have e : x = (X.NA : E)⁻¹ • ((X.NA : E) • x) := by rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

/- English proof (translation)
Use `set N : Matrix (Fin r) (Fin r) E := (δ : Matrix (Fin r) (Fin r) E) - 1 with hNdef`. Establish `htr : N.trace = (δ : Matrix (Fin r) (Fin r) E).trace - r`. Simplify using `[hNdef, Matrix.trace_sub]`. Establish `hN : ∀ x ∈ X.L', N.mulVec x ∈ X.L'` using `fun x hx => by`. Rewrite using `[hNdef, Matrix.sub_mulVec, Matrix.one_mulVec]`.

Conclude with `X.L'.sub_mem ((hδ.2 x).1 hx) hx`. Establish `hP : ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), ∃ z ∈ P, ((z : 𝓞 E) : E) = N.trace` using `fun P hP => by`. Take `⟨k, hk⟩` from `hu P hP`. Conclude with `GlobalTheory.trace_mem_prime_of_pow_mulVec_mem_smul E r X.L' N P k X.L'_fg (span_L' X) hP.1 hN hk`. Establish `hne : ((Ideal.span {(g : ℤ)}).primesOver (𝓞 E)).Nonempty`.

Apply `Set.nonempty_of_ncard_ne_zero` to reduce the goal to its premises. Rewrite using `[hg.2]`. Conclude with `(Module.finrank_pos (R := ℚ) (M := E)).ne'`. Take `⟨P0, hP0⟩` from `hne`. Take `⟨t, -, ht⟩` from `hP P0 hP0`.

Establish `hall : ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), t ∈ P` using `fun P hP' => by`. Take `⟨z, hz, hzt⟩` from `hP P hP'`. Establish `: z = t` using `RingOfIntegers.ext (hzt.trans ht.symm)`. Conclude with `this ▸ hz`. Establish `hpZ : Prime (g : ℤ)` using `Nat.prime_iff_prime_int.1 hg.1`.

Use `haveI hpr : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ`. Establish `hmax : (Ideal.span {(g : ℤ)}).IsMaximal` using `hpr.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)`. Establish `hrad` using `GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver E g hg.1 hg.2`. Establish `hmem : t ∈ Ideal.span {(g : 𝓞 E)}`. Apply `hrad` to reduce the goal to its premises.

Rewrite using `[Ideal.radical_eq_sInf]`. Use `Submodule.mem_sInf.2 fun J hJ => ?_` and prove the remaining obligations. Take `⟨hJle, hJp⟩` from `hJ`. Apply `hall J` to reduce the goal to its premises. Use `⟨hJp, ⟨?_⟩⟩` and prove the remaining obligations.

Establish `hle : Ideal.span {(g : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 E)) J`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Use `show algebraMap ℤ (𝓞 E) (g : ℤ) ∈ J`. Rewrite using `[map_natCast]`. Conclude with `hJle (Ideal.mem_span_singleton_self _)`.

Conclude with `hmax.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)) hle`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 hmem`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← htr, ← ht, ← hz]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_sub_mem {r : ℕ} (X : DataX E r) (g : ℕ) (hg : IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g)
    (δ : GL (Fin r) E) (hδ : IsUStab X.Gm X.L' δ)
    (hu : IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g δ) :
    ∃ z : 𝓞 E, (δ : Matrix (Fin r) (Fin r) E).trace - r = (g : E) * z := by
  classical
  set N : Matrix (Fin r) (Fin r) E := (δ : Matrix (Fin r) (Fin r) E) - 1 with hNdef
  have htr : N.trace = (δ : Matrix (Fin r) (Fin r) E).trace - r := by
    simp [hNdef, Matrix.trace_sub]
  have hN : ∀ x ∈ X.L', N.mulVec x ∈ X.L' := fun x hx => by
    rw [hNdef, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact X.L'.sub_mem ((hδ.2 x).1 hx) hx
  have hP : ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), ∃ z ∈ P, ((z : 𝓞 E) : E) = N.trace :=
    fun P hP => by
      obtain ⟨k, hk⟩ := hu P hP
      exact GlobalTheory.trace_mem_prime_of_pow_mulVec_mem_smul E r X.L' N P k X.L'_fg (span_L' X) hP.1 hN hk
  have hne : ((Ideal.span {(g : ℤ)}).primesOver (𝓞 E)).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hg.2]
    exact (Module.finrank_pos (R := ℚ) (M := E)).ne'
  obtain ⟨P0, hP0⟩ := hne
  obtain ⟨t, -, ht⟩ := hP P0 hP0
  have hall : ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), t ∈ P := fun P hP' => by
    obtain ⟨z, hz, hzt⟩ := hP P hP'
    have : z = t := RingOfIntegers.ext (hzt.trans ht.symm)
    exact this ▸ hz
  have hpZ : Prime (g : ℤ) := Nat.prime_iff_prime_int.1 hg.1
  haveI hpr : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
    hpr.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hrad := GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver E g hg.1 hg.2
  have hmem : t ∈ Ideal.span {(g : 𝓞 E)} := by
    apply hrad
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J hJ => ?_
    obtain ⟨hJle, hJp⟩ := hJ
    apply hall J
    refine ⟨hJp, ⟨?_⟩⟩
    have hle : Ideal.span {(g : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 E)) J := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) (g : ℤ) ∈ J
      rw [map_natCast]
      exact hJle (Ideal.mem_span_singleton_self _)
    exact hmax.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)) hle
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨z, ?_⟩
  rw [← htr, ← ht, ← hz]
  push_cast
  ring

end GlobalTheory.SmallElement

namespace GlobalTheory.SmallElement

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`.
-/
theorem map_conj_mulVec {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    (M.map (starRingEnd ℂ)) *ᵥ u = star (M *ᵥ star u) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

/- English proof (translation)
Simplify using `[ReciprocityTheory.MultiplicativeHeights.normSq]`.
-/
theorem normSq_star {r : ℕ} (u : Fin r → ℂ) : ReciprocityTheory.MultiplicativeHeights.normSq (star u) = ReciprocityTheory.MultiplicativeHeights.normSq u := by
  simp [ReciprocityTheory.MultiplicativeHeights.normSq]

/- English proof (translation)
Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_sq (r : ℕ) : Real.exp (1 / (3 * (r : ℝ))) ^ 2 = Real.exp (2 / (3 * (r : ℝ))) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/- English proof (translation)
Introduce `h0`. Use `congrArg Matrix.det h` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one this`.
-/
theorem det_ne_of_mul_eq_one {r : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ} (h : A * B = 1) : A.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem map_conj_mul_eq_one {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ} (hA : IsUnit A.det) :
    (A⁻¹).map (starRingEnd ℂ) * A.map (starRingEnd ℂ) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.SmallElement

namespace GlobalTheory.SmallElement

/- English proof (translation)
Introduce `E _ _ _ r X g hg hgr Γo hstab hunip x hx hNC γ hγ hs`. Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Conclude with `Units.ext (Matrix.ext fun i => i.elim0)`. Take `⟨x1, h1, b, hb, rfl⟩` from `ortho_holds r X.toData x hx`. Establish `hx1` using `ModeHalfA.dom_of_orth X.toData h1`.

Establish `hu : ∀ τ : X.Ψ, IsUnit (mat x1 τ).det` using `fun τ => isUnit_iff_ne_zero.2 (LUPf.orthogonalFrame_det_ne_zero X.toData x1 h1 τ)`. Establish `hmaj : ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (rmul x1 b) τ v = ReciprocityTheory.MultiplicativeHeights.normSq ((mat x1 τ)⁻¹ *ᵥ v)` using `fun τ v => by`. Rewrite using `[GlobalTheory.MajInv.maj_rmul X.toData hx1 hb, ModeHalfA.maj_orth X.toData h1]`. Both sides reduce to the same expression. Establish `hcΨ : ∀ σ : E →+* ℂ, σ ∉ X.Ψ → ComplexEmbedding.conjugate σ ∈ X.Ψ` using `fun σ hσ => not_not.1 fun h' => hσ ((X.cmType σ).2 h')`.

Set `Q : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ` to `fun σ => if hσ : σ ∈ X.Ψ then (mat x1 ⟨σ, hσ⟩)⁻¹ else ((mat x1 ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩)⁻¹).map (starRingEnd ℂ)`. Establish `hQpos : ∀ σ (hσ : σ ∈ X.Ψ), Q σ = (mat x1 ⟨σ, hσ⟩)⁻¹` using `fun σ hσ => dif_pos hσ`. Establish `hQneg : ∀ σ (hσ : σ ∉ X.Ψ), Q σ = ((mat x1 ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩)⁻¹).map (starRingEnd ℂ)` using `fun σ hσ => dif_neg hσ`. Use `set G : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hG`. Establish `hposB : ∀ (τ : X.Ψ) (u : Fin r → ℂ), ReciprocityTheory.MultiplicativeHeights.normSq (((mat x1 τ)⁻¹ * G.map τ.1 * ((mat x1 τ)⁻¹)⁻¹) *ᵥ u) ≤ Real.exp (2 / (3 * (r : ℝ))) * ReciprocityTheory.MultiplicativeHeights.normSq u`.

Introduce `τ u`. Establish `h` using `hs τ (mat x1 τ *ᵥ u)`. Establish `e : (mat x1 τ)⁻¹ *ᵥ (mat x1 τ *ᵥ u) = u`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hu τ), Matrix.one_mulVec]`. Rewrite `h` using `[hmaj, hmaj, e, exp_sq]`.

Rewrite using `[Matrix.nonsing_inv_nonsing_inv _ (hu τ), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Conclude with `h`. Establish `hQdet : ∀ σ, (Q σ).det ≠ 0`. Introduce `σ`. Distinguish the cases in `hσ : σ ∈ X.Ψ`.

Rewrite using `[hQpos σ hσ]`. Conclude with `det_ne_of_mul_eq_one (Matrix.nonsing_inv_mul _ (hu _))`. Rewrite using `[hQneg σ hσ]`. Conclude with `det_ne_of_mul_eq_one (map_conj_mul_eq_one (hu _))`. Establish `hop : ∀ σ (u : Fin r → ℂ), ReciprocityTheory.MultiplicativeHeights.normSq ((Q σ * G.map σ * (Q σ)⁻¹) *ᵥ u) ≤ Real.exp (2 / (3 * (r : ℝ))) * ReciprocityTheory.MultiplicativeHeights.normSq u`.

Introduce `σ u`. Distinguish the cases in `hσ : σ ∈ X.Ψ`. Rewrite using `[hQpos σ hσ]`. Conclude with `hposB ⟨σ, hσ⟩ u`. Rewrite using `[hQneg σ hσ] set τ : X.Ψ := ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩ with hτ`.

Establish `hinv : (((mat x1 τ)⁻¹).map (starRingEnd ℂ))⁻¹ = (mat x1 τ).map (starRingEnd ℂ)` using `Matrix.inv_eq_right_inv (map_conj_mul_eq_one (hu τ))`. Establish `hGm : G.map σ = (G.map τ.1).map (starRingEnd ℂ)`. Use extensionality with `i j`. Simplify using `[hτ, ComplexEmbedding.conjugate_coe_eq]`. Establish `e : ((mat x1 τ)⁻¹).map (starRingEnd ℂ) * G.map σ * (((mat x1 τ)⁻¹).map (starRingEnd ℂ))⁻¹ = ((mat x1 τ)⁻¹ * G.map τ.1 * ((mat x1 τ)⁻¹)⁻¹).map (starRingEnd ℂ)`.

Rewrite using `[hinv, hGm, Matrix.nonsing_inv_nonsing_inv _ (hu τ), Matrix.map_mul, Matrix.map_mul]`. Rewrite using `[e, map_conj_mulVec, normSq_star, ← normSq_star u]`. Conclude with `hposB τ (star u)`. Establish `htr : ∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 E, (G ^ n).trace - r = (g : E) * z`. Introduce `n _ _`.

Establish `hm` using `Γo.pow_mem hγ n`. Use `trace_sub_mem X g hg (γ ^ n) (hstab _ hm) (hunip _ hm)` as an intermediate fact. Rewrite `this` using `[Units.val_pow_eq_pow_val]`. Then use the resulting hypothesis. Establish `hg' : (Real.exp (1 / 3) + 1) * r < g`. Establish `h3` using `ReciprocityTheory.MultiplicativeHeights.sb_exp_third_lt_two`.

Establish `hr' : (0 : ℝ) < r` using `by exact_mod_cast hr`. Establish `hg3 : (3 * r : ℝ) < g` using `by exact_mod_cast hgr`. Use the polynomial consequences of the given equalities and inequalities. Establish `hU` using `ReciprocityTheory.MultiplicativeHeights.unipotent_holds E r g G Q htr hg' hQdet hop`. Establish `hN : G - 1 = 0`.

Use `hNC (G - 1) (fun v hv => ?_) (fun τ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `X.L'.sub_mem (((hstab γ hγ).2 v).1 hv) hv`. Use `set S := ∑ a, ∑ b, ‖(Q τ.1 * (G.map τ.1 - 1) * (Q τ.1)⁻¹) a b‖ ^ 2 with hS`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _`.

Establish `hS1 : S < 1` using `hU.2 τ.1`. Use `⟨Real.sqrt S, Real.sqrt_nonneg _, (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hS1), fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[Real.sq_sqrt hS0, hmaj, hmaj]`. Establish `hmap : (G - 1).map τ.1 = G.map τ.1 - 1`. Rewrite using `[← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply]`.

Establish `hQτ : Q τ.1 = (mat x1 τ)⁻¹` using `hQpos τ.1 τ.2`. Establish `e2 : (mat x1 τ)⁻¹ *ᵥ ((G.map τ.1 - 1) *ᵥ u) = ((mat x1 τ)⁻¹ * (G.map τ.1 - 1) * ((mat x1 τ)⁻¹)⁻¹) *ᵥ ((mat x1 τ)⁻¹ *ᵥ u)`. Rewrite using `[Matrix.nonsing_inv_nonsing_inv _ (hu τ)]`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ), Matrix.mul_one]`. Rewrite using `[hmap, e2, hS, hQτ]`.

Conclude with `ReciprocityTheory.MultiplicativeHeights.sb_normSq_mulVec_le _ _`. Conclude with `Units.ext (sub_eq_zero.1 hN)`.
-/
theorem smallElement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    IndefiniteRowSideFullHecke.SmallUnipotentElements.SmallElementStatement E := by
  intro E _ _ _ r X g hg hgr Γo hstab hunip x hx hNC γ hγ hs
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Units.ext (Matrix.ext fun i => i.elim0)
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X.toData x hx
  have hx1 := ModeHalfA.dom_of_orth X.toData h1
  have hu : ∀ τ : X.Ψ, IsUnit (mat x1 τ).det :=
    fun τ => isUnit_iff_ne_zero.2 (LUPf.orthogonalFrame_det_ne_zero X.toData x1 h1 τ)
  have hmaj : ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      X.maj (rmul x1 b) τ v = ReciprocityTheory.MultiplicativeHeights.normSq ((mat x1 τ)⁻¹ *ᵥ v) := fun τ v => by
    rw [GlobalTheory.MajInv.maj_rmul X.toData hx1 hb, ModeHalfA.maj_orth X.toData h1]
    rfl
  have hcΨ : ∀ σ : E →+* ℂ, σ ∉ X.Ψ → ComplexEmbedding.conjugate σ ∈ X.Ψ := fun σ hσ =>
    not_not.1 fun h' => hσ ((X.cmType σ).2 h')
  let Q : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ := fun σ =>
    if hσ : σ ∈ X.Ψ then (mat x1 ⟨σ, hσ⟩)⁻¹
    else ((mat x1 ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩)⁻¹).map (starRingEnd ℂ)
  have hQpos : ∀ σ (hσ : σ ∈ X.Ψ), Q σ = (mat x1 ⟨σ, hσ⟩)⁻¹ := fun σ hσ => dif_pos hσ
  have hQneg : ∀ σ (hσ : σ ∉ X.Ψ),
      Q σ = ((mat x1 ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩)⁻¹).map (starRingEnd ℂ) :=
    fun σ hσ => dif_neg hσ
  set G : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hG
  have hposB : ∀ (τ : X.Ψ) (u : Fin r → ℂ),
      ReciprocityTheory.MultiplicativeHeights.normSq (((mat x1 τ)⁻¹ * G.map τ.1 * ((mat x1 τ)⁻¹)⁻¹) *ᵥ u) ≤
        Real.exp (2 / (3 * (r : ℝ))) * ReciprocityTheory.MultiplicativeHeights.normSq u := by
    intro τ u
    have h := hs τ (mat x1 τ *ᵥ u)
    have e : (mat x1 τ)⁻¹ *ᵥ (mat x1 τ *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hu τ), Matrix.one_mulVec]
    rw [hmaj, hmaj, e, exp_sq] at h
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu τ), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h
  have hQdet : ∀ σ, (Q σ).det ≠ 0 := by
    intro σ
    by_cases hσ : σ ∈ X.Ψ
    · rw [hQpos σ hσ]
      exact det_ne_of_mul_eq_one (Matrix.nonsing_inv_mul _ (hu _))
    · rw [hQneg σ hσ]
      exact det_ne_of_mul_eq_one (map_conj_mul_eq_one (hu _))
  have hop : ∀ σ (u : Fin r → ℂ), ReciprocityTheory.MultiplicativeHeights.normSq ((Q σ * G.map σ * (Q σ)⁻¹) *ᵥ u) ≤
      Real.exp (2 / (3 * (r : ℝ))) * ReciprocityTheory.MultiplicativeHeights.normSq u := by
    intro σ u
    by_cases hσ : σ ∈ X.Ψ
    · rw [hQpos σ hσ]
      exact hposB ⟨σ, hσ⟩ u
    · rw [hQneg σ hσ]
      set τ : X.Ψ := ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩ with hτ
      have hinv : (((mat x1 τ)⁻¹).map (starRingEnd ℂ))⁻¹ = (mat x1 τ).map (starRingEnd ℂ) :=
        Matrix.inv_eq_right_inv (map_conj_mul_eq_one (hu τ))
      have hGm : G.map σ = (G.map τ.1).map (starRingEnd ℂ) := by
        ext i j
        simp [hτ, ComplexEmbedding.conjugate_coe_eq]
      have e : ((mat x1 τ)⁻¹).map (starRingEnd ℂ) * G.map σ *
          (((mat x1 τ)⁻¹).map (starRingEnd ℂ))⁻¹ =
          ((mat x1 τ)⁻¹ * G.map τ.1 * ((mat x1 τ)⁻¹)⁻¹).map (starRingEnd ℂ) := by
        rw [hinv, hGm, Matrix.nonsing_inv_nonsing_inv _ (hu τ), Matrix.map_mul, Matrix.map_mul]
      rw [e, map_conj_mulVec, normSq_star, ← normSq_star u]
      exact hposB τ (star u)
  have htr : ∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 E, (G ^ n).trace - r = (g : E) * z := by
    intro n _ _
    have hm := Γo.pow_mem hγ n
    have := trace_sub_mem X g hg (γ ^ n) (hstab _ hm) (hunip _ hm)
    rwa [Units.val_pow_eq_pow_val] at this
  have hg' : (Real.exp (1 / 3) + 1) * r < g := by
    have h3 := ReciprocityTheory.MultiplicativeHeights.sb_exp_third_lt_two
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hg3 : (3 * r : ℝ) < g := by exact_mod_cast hgr
    nlinarith
  have hU := ReciprocityTheory.MultiplicativeHeights.unipotent_holds E r g G Q htr hg' hQdet hop
  have hN : G - 1 = 0 := by
    refine hNC (G - 1) (fun v hv => ?_) (fun τ => ?_)
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact X.L'.sub_mem (((hstab γ hγ).2 v).1 hv) hv
    · set S := ∑ a, ∑ b, ‖(Q τ.1 * (G.map τ.1 - 1) * (Q τ.1)⁻¹) a b‖ ^ 2 with hS
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hS1 : S < 1 := hU.2 τ.1
      refine ⟨Real.sqrt S, Real.sqrt_nonneg _, (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hS1),
        fun u => ?_⟩
      rw [Real.sq_sqrt hS0, hmaj, hmaj]
      have hmap : (G - 1).map τ.1 = G.map τ.1 - 1 := by
        rw [← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply]
      have hQτ : Q τ.1 = (mat x1 τ)⁻¹ := hQpos τ.1 τ.2
      have e2 : (mat x1 τ)⁻¹ *ᵥ ((G.map τ.1 - 1) *ᵥ u) =
          ((mat x1 τ)⁻¹ * (G.map τ.1 - 1) * ((mat x1 τ)⁻¹)⁻¹) *ᵥ ((mat x1 τ)⁻¹ *ᵥ u) := by
        rw [Matrix.nonsing_inv_nonsing_inv _ (hu τ)]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ),
          Matrix.mul_one]
      rw [hmap, e2, hS, hQτ]
      exact ReciprocityTheory.MultiplicativeHeights.sb_normSq_mulVec_le _ _
  exact Units.ext (sub_eq_zero.1 hN)

end GlobalTheory.SmallElement
