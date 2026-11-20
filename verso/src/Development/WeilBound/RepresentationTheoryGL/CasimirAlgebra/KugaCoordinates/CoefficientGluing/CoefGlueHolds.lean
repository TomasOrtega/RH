import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CoefficientGluing.SumFinVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitesimalCharacterQuantumDet

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct Classical

set_option linter.unusedSimpArgs false

namespace PositivityTheory.Rg.Cz.CGlue

/- English proof (translation)
Establish `hne : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ`. Introduce `τ h`. Establish `h1 : (InfinitePlace.mk τ).IsReal` using `InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h)`. Conclude with `(InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h1`. Establish `hu : k.1.det * star k.1.det = 1`.

Establish `h2 : k.1 * star k.1 = 1` using `Unitary.mul_star_self_of_mem k.2`. Establish `h3` using `congrArg Matrix.det h2`. Rewrite `h3` using `[Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one]`. Then use the resulting hypothesis. Use `Finset.prod_involution (fun τ _ => ComplexEmbedding.conjugate τ) (fun τ _ => ?_) (fun τ _ _ => hne τ) (fun τ _ => Finset.mem_univ _) (fun τ _ => by simp [ComplexEmbedding.conjugate])` and prove the remaining obligations. Rewrite using `[J.coord_conjugate, ← J.coord_star, ← map_mul, hu, map_one]`.
-/
theorem prod_coord_det {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (k : Kinf E a) :
    ∏ τ : E →+* ℂ, coord τ (k.1.det) = 1 := by
  have hne : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ := by
    intro τ h
    have h1 : (InfinitePlace.mk τ).IsReal :=
      InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h1
  have hu : k.1.det * star k.1.det = 1 := by
    have h2 : k.1 * star k.1 = 1 := Unitary.mul_star_self_of_mem k.2
    have h3 := congrArg Matrix.det h2
    rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at h3
  refine Finset.prod_involution (fun τ _ => ComplexEmbedding.conjugate τ) (fun τ _ => ?_) (fun τ _ _ => hne τ)
    (fun τ _ => Finset.mem_univ _) (fun τ _ => by simp [ComplexEmbedding.conjugate])
  rw [J.coord_conjugate, ← J.coord_star, ← map_mul, hu, map_one]

/- English proof (translation)
Use extensionality with `I J`. Simplify using `only [bigM, Matrix.of_apply, kap, Matrix.map_apply]`. Rewrite using `[show ((Unitary.toUnits k : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = k.1 from rfl, prod_coord_det k, _root_.one_zpow, one_mul]`.
-/
theorem bigM_kap {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Q : Type} [Fintype Q]
    [DecidableEq Q] (lab : Q → (E →+* ℂ)) (s : ℤ) (k : Kinf E a) :
    bigM lab s (Unitary.toUnits k) = Matrix.of (fun I J : Q → Fin a => ∏ p, kap E a (lab p) k (I p) (J p)) := by
  ext I J
  simp only [bigM, Matrix.of_apply, kap, Matrix.map_apply]
  rw [show ((Unitary.toUnits k : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = k.1 from rfl,
    prod_coord_det k, _root_.one_zpow, one_mul]

/- English proof (translation)
Simplify using `only [cx, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h]`.
-/
theorem cx_mul {E : Type} [Field E] {a : ℕ} {A B : Type} [Fintype A] [Fintype B] (τ : E →+* ℂ)
    (φ : Lie E a → Matrix A A ℂ) (ψ : Lie E a → Matrix B B ℂ) (J : Matrix A B ℂ) (h : ∀ X, φ X * J = J * ψ X)
    (i j : Fin a) : cx τ φ i j * J = J * cx τ ψ i j := by
  simp only [cx, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h]

/- English proof (translation)
Introduce `i j k l`. Use `LinearMap.ext fun φ => Subtype.ext ?_` and prove the remaining obligations. Establish `key : ∀ i j (ψ : π.V), ((cx τ (lieOp π) i j) ψ).1 = Eop τ i j ψ.1` using `fun i j ψ => by`. Rewrite using `[← GlobalTheory.WigCap.res_Eop]`. Both sides reduce to the same expression.

Establish `h` using `LinearMap.congr_fun (glRel_Eop (a := a) τ i j k l) φ.1`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, key] at h ⊢`. Apply the tactic sequence `split_ifs at h ⊢ <;> simpa [key] using h`.
-/
theorem glRel_cx {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (τ : E →+* ℂ) : GlRel (cx τ (lieOp π)) := by
  intro i j k l
  refine LinearMap.ext fun φ => Subtype.ext ?_
  have key : ∀ i j (ψ : π.V), ((cx τ (lieOp π) i j) ψ).1 = Eop τ i j ψ.1 := fun i j ψ => by
    rw [← GlobalTheory.WigCap.res_Eop]; rfl
  have h := LinearMap.congr_fun (glRel_Eop (a := a) τ i j k l) φ.1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, key] at h ⊢
  split_ifs at h ⊢ <;> simpa [key] using h

end PositivityTheory.Rg.Cz.CGlue

namespace PositivityTheory.Rg.Cz

open CGlue

/- English proof (translation)
Introduce `hCB hBR hBC hSum hCo hCV E _ _ _ a π l s hch hKT`. Take `⟨q, N, lab, col, b, tl, η, hcl, htab, htl, hw, hinv, hanti, halt⟩` from `hKT`. Take `⟨ω₀, hω0, hcoc, hω0a⟩` from `hCo E a π.V (fun k => π.op (.cpt k)) q N lab tl η htl hinv halt`. Choose the witnesses or unpack the hypotheses as in `⟨X, hX⟩ : ∃ X, ω₀ X ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hω0 (AlternatingMap.ext h)`. Choose the witnesses or unpack the hypotheses as in `⟨I₀, hI⟩ : ∃ I, ω₀ X I ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hX (funext h)`. Choose the witnesses or unpack the hypotheses as in `⟨lam, hlam⟩ : ∃ lam : π.V →ₗ[ℂ] ℂ, lam (ω₀ X I₀) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hI ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)`.

Use `set v₀ : TV a ℂ (Fin q) := fun I => lam (ω₀ X I) with hv₀`. Establish `hv₀D : v₀ ∈ colAnti (n` using `a) col := by`. Introduce `p p' h1 h2`. Use function extensionality and compare the values at `I`. Use `congrFun (hω0a p p' (hanti p p' h1 h2) X) I` as an intermediate fact.

Simplify using `only [pm_apply'] at this ⊢`. Simplify using `[hv₀, this]`. Establish `hv₀0 : v₀ ≠ 0` using `fun h => hlam (congrFun h I₀)`. Establish `hDst : ∀ y, ∀ v ∈ colAnti (n` using `a) col, bigM lab s y *ᵥ v ∈ colAnti (n := a) col := by`. Introduce `y v hv p p' h1 h2`.

Rewrite using `[← (hBC E a (Fin q) lab s).2 y p p' (hcl p p' h1) v, hv p p' h1 h2, Matrix.mulVec_neg]`. Establish `hrep` using `hBR E a (Fin q) lab s`. Take `⟨Ξ, J, hJJ, hJD, hJv, hRJ, hJR, hdJ⟩` from `hSum E a (Fin q → Fin a) (bigM lab s) (bigD lab s) hrep (colAnti col) hDst v₀ hv₀D hv₀0`. Establish `hdm : ∀ Y, Ξ.dmat Y = Jᴴ * bigD lab s Y * J`. Introduce `Y`.

Rewrite using `[Matrix.mul_assoc, hdJ, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]`. Establish `hcx : ∀ τ i j, cx τ (⇑Ξ.dmat) i j = Jᴴ * cx τ (bigD lab s) i j * J`. Introduce `τ i j`. Rewrite using `[Matrix.mul_assoc, cx_mul τ (bigD lab s) (⇑Ξ.dmat) J hdJ, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]`. Set `ω : Herm E a [⋀^Fin N]→ₗ[ℝ] (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))` to `((tmap Jᴴ).restrictScalars ℝ).compAlternatingMap ω₀`.

Use `⟨Ξ, N, ω, ⟨?_, fun τ => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `Y`. Rewrite using `[hdm, hdm, hrep.dstar]`. Simplify using `[Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Establish `hBC1` using `(hBC E a (Fin q) lab s).1 τ`.

Take `⟨htr, hcas⟩` from `hCV a π.V (cx τ (lieOp π)) (fun k => (l τ k : ℂ)) (glRel_cx π τ) (hch τ)`. Take `⟨w, hw'⟩` from `hw τ`. Use `set ν : Fin a → ℕ := fun i => ((fib lab τ).filter fun p => b p = i).card with hν`. Establish `hνeq : ∀ i, s - l τ (w i) = (ν i : ℤ) + (i : ℕ)`. Introduce `i`.

Rewrite using `[hw' i, hν]`. Simplify using `only [fib, Finset.filter_filter]`. Establish `hsumν : ∑ i, (ν i : ℝ) = (fib lab τ).card`. Rewrite using `[hν]`. Conclude with `(Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ (b p))).symm` after adjusting the coercions.

Establish `ht : ∑ k, ((l τ k : ℝ) + (k : ℕ)) = a * s - (fib lab τ).card`. Rewrite using `[sum_shift a s ν (l τ) w hνeq, hsumν]`. Use `⟨∑ k, (((l τ k : ℝ) + ((a : ℝ) - 1) / 2) ^ 2 - (((a : ℝ) - 1) / 2 - (k : ℕ)) ^ 2), ∑ k, ((l τ k : ℝ) + (k : ℕ)), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcas]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[htr]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hsumB : ∑ i, cx τ (bigD lab s) i i = (((fib lab τ).card : ℂ) - a * s) • (1 : Matrix (Fin q → Fin a) (Fin q → Fin a) ℂ)`.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Simplify using `only [Matrix.toLin'_apply, Matrix.sum_mulVec, hBC1, Finset.sum_sub_distrib, tE_diag_sum, Matrix.smul_mulVec, Matrix.one_mulVec]`. Simplify using `only [if_pos rfl, if_true, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ]`.

Use `module`. Rewrite using `[Finset.sum_congr rfl fun i _ => hcx τ i i, ← Matrix.sum_mul, ← Matrix.mul_sum, hsumB, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hJJ, Algebra.algebraMap_eq_smul_one, ht]`. Use `push_cast`. Put the polynomial expressions in normal form. Introduce `v`.

Establish `hfD : J *ᵥ v ∈ colAnti (n` using `a) col := hJD v`. Use `set Cb : Matrix (Fin q → Fin a) (Fin q → Fin a) ℂ := ∑ i, ∑ j, cx τ (bigD lab s) i j * cx τ (bigD lab s) j i with hCb`. Establish `hCasM : ∑ i, ∑ j, cx τ (⇑Ξ.dmat) i j * cx τ (⇑Ξ.dmat) j i = Jᴴ * Cb * J`. Rewrite using `[hCb]`. Simplify using `only [Matrix.mul_sum, Matrix.sum_mul]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hcx τ i j, Matrix.mul_assoc, ← cx_mul τ (bigD lab s) (⇑Ξ.dmat) J hdJ j i]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hvv : star v ⬝ᵥ v = star (J *ᵥ v) ⬝ᵥ (J *ᵥ v)`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]`.

Establish `hquad : ∀ C : Matrix (Fin q → Fin a) (Fin q → Fin a) ℂ, star v ⬝ᵥ ((Jᴴ * C * J) *ᵥ v) = star (J *ᵥ v) ⬝ᵥ (C *ᵥ (J *ᵥ v))`. Introduce `C`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]`. Establish `hC : Cb *ᵥ (J *ᵥ v) = (∑ i, ∑ j, tE (fib lab τ) (0 : Fin a → Fin a → Module.End ℂ ℂ) i j * tE (fib lab τ) 0 j i : Module.End ℂ (TV a ℂ (Fin q))) (J *ᵥ v) - (2 * (s : ℂ) * (fib lab τ).card - a * (s : ℂ) ^ 2) • (J *ᵥ v)`. Rewrite using `[← cas_shift, hCb]`.

Simplify using `only [Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, hBC1]`. Establish `hcolS : ∀ p p', col p = col p' → (p ∈ fib lab τ ↔ p' ∈ fib lab τ)`. Introduce `p p' h`. Simplify using `[fib, hcl p p' h]`. Establish `hb` using `hCB a (Fin q) ℕ col b (fib lab τ) htab hcolS (J *ᵥ v) hfD`.

Establish `har` using `arith a s ν (l τ) w hνeq`. Rewrite using `[hCasM, hquad, hvv, hC, dotProduct_sub, dotProduct_smul, ← har, hsumν]`. Rewrite using `[show (2 * (s : ℂ) * (fib lab τ).card - a * (s : ℂ) ^ 2) = ((2 * (s : ℝ) * (fib lab τ).card - a * (s : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring]`. Rewrite using `[Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul, sub_mul]`. Combine the linear relations using `[hb]`.

Introduce `k Y`. Express the relevant statement in the definitionally equal form `tmap Jᴴ (ω₀ fun i => adHerm k (Y i)) = tensorK π Ξ k (tmap Jᴴ (ω₀ Y))`. Rewrite using `[hcoc k Y]`. Use `tmap_actT lab (kap E a) (fun k => π.op (.cpt k)) k Jᴴ _ ?_ (ω₀ Y)` and prove the remaining obligations. Rewrite using `[← bigM_kap lab s k]`.

Conclude with `hJR _`. Introduce `h0`. Conclude with `tmap_ne Jᴴ (ω₀ X) lam hJv (by simpa [ω] using congrArg (fun f => f X) h0)`.
-/
theorem coefGlue_holds : CoefGlue := by
  intro hCB hBR hBC hSum hCo hCV E _ _ _ a π l s hch hKT
  obtain ⟨q, N, lab, col, b, tl, η, hcl, htab, htl, hw, hinv, hanti, halt⟩ := hKT
  obtain ⟨ω₀, hω0, hcoc, hω0a⟩ := hCo E a π.V (fun k => π.op (.cpt k)) q N lab tl η htl hinv halt
  obtain ⟨X, hX⟩ : ∃ X, ω₀ X ≠ 0 := by
    by_contra h; push_neg at h; exact hω0 (AlternatingMap.ext h)
  obtain ⟨I₀, hI⟩ : ∃ I, ω₀ X I ≠ 0 := by
    by_contra h; push_neg at h; exact hX (funext h)
  obtain ⟨lam, hlam⟩ : ∃ lam : π.V →ₗ[ℂ] ℂ, lam (ω₀ X I₀) ≠ 0 := by
    by_contra h; push_neg at h; exact hI ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  set v₀ : TV a ℂ (Fin q) := fun I => lam (ω₀ X I) with hv₀
  have hv₀D : v₀ ∈ colAnti (n := a) col := by
    intro p p' h1 h2
    funext I
    have := congrFun (hω0a p p' (hanti p p' h1 h2) X) I
    simp only [pm_apply'] at this ⊢
    simp [hv₀, this]
  have hv₀0 : v₀ ≠ 0 := fun h => hlam (congrFun h I₀)
  have hDst : ∀ y, ∀ v ∈ colAnti (n := a) col, bigM lab s y *ᵥ v ∈ colAnti (n := a) col := by
    intro y v hv p p' h1 h2
    rw [← (hBC E a (Fin q) lab s).2 y p p' (hcl p p' h1) v, hv p p' h1 h2, Matrix.mulVec_neg]
  have hrep := hBR E a (Fin q) lab s
  obtain ⟨Ξ, J, hJJ, hJD, hJv, hRJ, hJR, hdJ⟩ :=
    hSum E a (Fin q → Fin a) (bigM lab s) (bigD lab s) hrep (colAnti col) hDst v₀ hv₀D hv₀0
  have hdm : ∀ Y, Ξ.dmat Y = Jᴴ * bigD lab s Y * J := by
    intro Y; rw [Matrix.mul_assoc, hdJ, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hcx : ∀ τ i j, cx τ (⇑Ξ.dmat) i j = Jᴴ * cx τ (bigD lab s) i j * J := by
    intro τ i j
    rw [Matrix.mul_assoc, cx_mul τ (bigD lab s) (⇑Ξ.dmat) J hdJ, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  let ω : Herm E a [⋀^Fin N]→ₗ[ℝ] (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
    ((tmap Jᴴ).restrictScalars ℝ).compAlternatingMap ω₀
  refine ⟨Ξ, N, ω, ⟨?_, fun τ => ?_⟩, ?_, ?_⟩
  · intro Y
    rw [hdm, hdm, hrep.dstar]
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · have hBC1 := (hBC E a (Fin q) lab s).1 τ
    obtain ⟨htr, hcas⟩ := hCV a π.V (cx τ (lieOp π)) (fun k => (l τ k : ℂ)) (glRel_cx π τ) (hch τ)
    obtain ⟨w, hw'⟩ := hw τ
    set ν : Fin a → ℕ := fun i => ((fib lab τ).filter fun p => b p = i).card with hν
    have hνeq : ∀ i, s - l τ (w i) = (ν i : ℤ) + (i : ℕ) := by
      intro i; rw [hw' i, hν]; simp only [fib, Finset.filter_filter]
    have hsumν : ∑ i, (ν i : ℝ) = (fib lab τ).card := by
      rw [hν]; exact_mod_cast (Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ (b p))).symm
    have ht : ∑ k, ((l τ k : ℝ) + (k : ℕ)) = a * s - (fib lab τ).card := by
      rw [sum_shift a s ν (l τ) w hνeq, hsumν]
    refine ⟨∑ k, (((l τ k : ℝ) + ((a : ℝ) - 1) / 2) ^ 2 - (((a : ℝ) - 1) / 2 - (k : ℕ)) ^ 2),
      ∑ k, ((l τ k : ℝ) + (k : ℕ)), ?_, ?_, ?_, ?_⟩
    · rw [hcas]; push_cast; rfl
    · rw [htr]; push_cast; rfl
    · have hsumB : ∑ i, cx τ (bigD lab s) i i = (((fib lab τ).card : ℂ) - a * s) • (1 : Matrix (Fin q → Fin a) (Fin q → Fin a) ℂ) := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun f => ?_
        simp only [Matrix.toLin'_apply, Matrix.sum_mulVec, hBC1, Finset.sum_sub_distrib, tE_diag_sum,
          Matrix.smul_mulVec, Matrix.one_mulVec]
        simp only [if_pos rfl, if_true, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [← Nat.cast_smul_eq_nsmul ℂ]
        module
      rw [Finset.sum_congr rfl fun i _ => hcx τ i i, ← Matrix.sum_mul, ← Matrix.mul_sum, hsumB, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul, hJJ, Algebra.algebraMap_eq_smul_one, ht]
      push_cast
      ring_nf
    · intro v
      have hfD : J *ᵥ v ∈ colAnti (n := a) col := hJD v
      set Cb : Matrix (Fin q → Fin a) (Fin q → Fin a) ℂ :=
        ∑ i, ∑ j, cx τ (bigD lab s) i j * cx τ (bigD lab s) j i with hCb
      have hCasM : ∑ i, ∑ j, cx τ (⇑Ξ.dmat) i j * cx τ (⇑Ξ.dmat) j i = Jᴴ * Cb * J := by
        rw [hCb]
        simp only [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hcx τ i j, Matrix.mul_assoc, ← cx_mul τ (bigD lab s) (⇑Ξ.dmat) J hdJ j i]
        simp only [Matrix.mul_assoc]
      have hvv : star v ⬝ᵥ v = star (J *ᵥ v) ⬝ᵥ (J *ᵥ v) := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]
      have hquad : ∀ C : Matrix (Fin q → Fin a) (Fin q → Fin a) ℂ,
          star v ⬝ᵥ ((Jᴴ * C * J) *ᵥ v) = star (J *ᵥ v) ⬝ᵥ (C *ᵥ (J *ᵥ v)) := by
        intro C
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
      have hC : Cb *ᵥ (J *ᵥ v) =
          (∑ i, ∑ j, tE (fib lab τ) (0 : Fin a → Fin a → Module.End ℂ ℂ) i j * tE (fib lab τ) 0 j i :
            Module.End ℂ (TV a ℂ (Fin q))) (J *ᵥ v) -
            (2 * (s : ℂ) * (fib lab τ).card - a * (s : ℂ) ^ 2) • (J *ᵥ v) := by
        rw [← cas_shift, hCb]
        simp only [Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, hBC1]
      have hcolS : ∀ p p', col p = col p' → (p ∈ fib lab τ ↔ p' ∈ fib lab τ) := by
        intro p p' h; simp [fib, hcl p p' h]
      have hb := hCB a (Fin q) ℕ col b (fib lab τ) htab hcolS (J *ᵥ v) hfD
      have har := arith a s ν (l τ) w hνeq
      rw [hCasM, hquad, hvv, hC, dotProduct_sub, dotProduct_smul, ← har, hsumν]
      rw [show (2 * (s : ℂ) * (fib lab τ).card - a * (s : ℂ) ^ 2) =
        ((2 * (s : ℝ) * (fib lab τ).card - a * (s : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul, sub_mul]
      linarith [hb]
  · intro k Y
    change tmap Jᴴ (ω₀ fun i => adHerm k (Y i)) = tensorK π Ξ k (tmap Jᴴ (ω₀ Y))
    rw [hcoc k Y]
    refine tmap_actT lab (kap E a) (fun k => π.op (.cpt k)) k Jᴴ _ ?_ (ω₀ Y)
    rw [← bigM_kap lab s k]
    exact hJR _
  · intro h0
    exact tmap_ne Jᴴ (ω₀ X) lam hJv (by simpa [ω] using congrArg (fun f => f X) h0)

end PositivityTheory.Rg.Cz
