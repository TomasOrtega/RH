import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.InvAlgConstr

/- English proof (translation)
Introduce `E _ _ _ w hw K e he t ht Q hQ hcsr`. Use `set Q' : K.E[X] := Q.map e.symm.toRingHom with hQ'`. Establish `hinj : Function.Injective (e.symm.toRingHom)` using `e.symm.injective`. Establish `hQ'm : Q'.Monic` using `hQ.map _`. Establish `hdeg : Q'.natDegree = Q.natDegree` using `natDegree_map_eq_of_injective hinj _`.

Establish `hc` using `hcsr.resolve_left hw`. Establish `hQ0 : Q.coeff 0 ≠ 0`. Introduce `h0`. Rewrite `hc` using `[h0, map_zero, C_0, zero_mul]`. Conclude with `(hQ.map (cj w)).ne_zero (reverse_eq_zero.mp hc.symm)`.

Establish `hQ'0 : Q'.coeff 0 ≠ 0`. Rewrite using `[hQ', coeff_map]`. Conclude with `fun h => hQ0 (hinj (by rw [h, map_zero]))`. Set `A` to `AdjoinRoot Q'`. Set `r : A` to `AdjoinRoot.root Q'`.

Set `pb` to `AdjoinRoot.powerBasis' hQ'm`. Use `haveI : Module.Finite K.E A := pb.finite`. Establish `hr0 : aeval r Q' = 0`. Rewrite using `[aeval_def, AdjoinRoot.algebraMap_eq]`. Conclude with `AdjoinRoot.eval₂_root Q'`.

Use `set v : A := -(aeval r (divX Q')) * algebraMap K.E A (Q'.coeff 0)⁻¹ with hv`. Establish `hrv : r * v = 1`. Establish `h1` using `congrArg (aeval r) (X_mul_divX_add Q')`. Rewrite `h1` using `[map_add, map_mul, aeval_X, aeval_C, hr0]`. Establish `h2 : algebraMap K.E A (Q'.coeff 0) * algebraMap K.E A (Q'.coeff 0)⁻¹ = 1`.

Rewrite using `[← map_mul, mul_inv_cancel₀ hQ'0, map_one]`. Take the linear combination `(-(algebraMap K.E A (Q'.coeff 0)⁻¹)) * h1 + h2`. Use `letI : Invertible v := ⟨r, hrv, by rw [mul_comm]; exact hrv⟩`. Establish `hce : ∀ y, K.c (e.symm y) = e.symm (cj w y)`. Introduce `y`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`. Establish `hmapc : Q'.map K.c.toRingHom = (Q.map (cj w)).map e.symm.toRingHom`. Rewrite using `[hQ', Polynomial.map_map, Polynomial.map_map]`. Use `congr 1`.

Use extensionality with `y`. Conclude with `hce y`. Establish `hrev : (Q'.map K.c.toRingHom).reverse = C (e.symm (cj w (Q.coeff 0))) * Q'`. Rewrite using `[hmapc]`. Unfold `reverse`.

Rewrite using `[natDegree_map_eq_of_injective hinj, reflect_map, ← reverse, ← hc, Polynomial.map_mul, map_C]`. Both sides reduce to the same expression. Establish `hev : eval₂ ((algebraMap K.E A).comp K.c.toRingHom) v Q' = 0`. Rewrite using `[← eval₂_map, ← eval₂_reverse_mul_pow (algebraMap K.E A) v, hrev]`. Use `show eval₂ (algebraMap K.E A) r (C (e.symm (cj w (Q.coeff 0))) * Q') * _ = 0`.

Establish `hev0 : eval₂ (algebraMap K.E A) r Q' = 0` using `by rw [← aeval_def]; exact hr0`. Rewrite using `[eval₂_mul, hev0, mul_zero, zero_mul]`. Set `σ0 : A →+* A` to `AdjoinRoot.lift ((algebraMap K.E A).comp K.c.toRingHom) v hev`. Establish `hσr : σ0 r = v` using `AdjoinRoot.lift_root hev`. Establish `hσof : ∀ a, σ0 (algebraMap K.E A a) = algebraMap K.E A (K.c a)` using `fun a => AdjoinRoot.lift_of hev`.

Establish `hσv : σ0 v = r`. Combine the equalities or inequalities in the displayed calculation. Establish `hcomp : σ0.comp σ0 = RingHom.id A`. Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `a show σ0 (σ0 (algebraMap K.E A a)) = algebraMap K.E A a`. Rewrite using `[hσof, hσof]`. Simplify using `[K.c_c]`. Use `show σ0 (σ0 r) = r`. Rewrite using `[hσr, hσv]`.

Establish `hσσ : ∀ y, σ0 (σ0 y) = y` using `fun y => RingHom.congr_fun hcomp y`. Set `σ : A ≃+* A` to `{ toFun := σ0, invFun := σ0, left_inv := hσσ, right_inv := hσσ, map_mul' := map_mul σ0, map_add' := map_add σ0 }`. Use `set tE : K.E := algebraMap K.O K.E t`. Establish `htE : tE ≠ 0` using `fun h => ht ((IsFractionRing.injective K.O K.E) (by rw [map_zero]; exact h))`. Set `B : GlobalTheory.UnitLemma.InvAlg K` to `{ A := A, σ := σ, σ_σ := hσσ, σ_alg := hσof, g := (r - 1) * algebraMap K.E A tE⁻¹ }`.

Establish `hu : (1 + algebraMap K.O B.A t * B.g) = r` using `by show (1 + algebraMap K.O A t * ((r - 1) * algebraMap K.E A tE⁻¹)) = r`. Rewrite using `[IsScalarTower.algebraMap_apply K.O K.E A t]`. Establish `h3 : algebraMap K.E A tE * algebraMap K.E A tE⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ htE, map_one]`. Take the linear combination `(r - 1) * h3`.

Use `⟨B, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hu]`. Conclude with `AdjoinRoot.adjoinRoot_eq_top`. Rewrite using `[hu]`. Conclude with `hr0`.

Use `show Module.finrank K.E A = Q.natDegree`. Rewrite using `[pb.finrank, AdjoinRoot.powerBasis'_dim, hdeg]`. Rewrite using `[hu] show r * σ0 r = 1`. Rewrite using `[hσr, hrv]`.
-/
theorem exists_invAlg_adjoinRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (t : K.O), t ≠ 0 → ∀ Q : (w.adicCompletion E)[X], Q.Monic → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ ∧ aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 ∧ Module.finrank K.E B.A = Q.natDegree ∧ (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 := by
  intro E _ _ _ w hw K e he t ht Q hQ hcsr
  set Q' : K.E[X] := Q.map e.symm.toRingHom with hQ'
  have hinj : Function.Injective (e.symm.toRingHom) := e.symm.injective
  have hQ'm : Q'.Monic := hQ.map _
  have hdeg : Q'.natDegree = Q.natDegree := natDegree_map_eq_of_injective hinj _
  have hc := hcsr.resolve_left hw
  have hQ0 : Q.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero, C_0, zero_mul] at hc
    exact (hQ.map (cj w)).ne_zero (reverse_eq_zero.mp hc.symm)
  have hQ'0 : Q'.coeff 0 ≠ 0 := by
    rw [hQ', coeff_map]
    exact fun h => hQ0 (hinj (by rw [h, map_zero]))
  let A := AdjoinRoot Q'
  let r : A := AdjoinRoot.root Q'
  let pb := AdjoinRoot.powerBasis' hQ'm
  haveI : Module.Finite K.E A := pb.finite
  have hr0 : aeval r Q' = 0 := by
    rw [aeval_def, AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.eval₂_root Q'
  set v : A := -(aeval r (divX Q')) * algebraMap K.E A (Q'.coeff 0)⁻¹ with hv
  have hrv : r * v = 1 := by
    have h1 := congrArg (aeval r) (X_mul_divX_add Q')
    rw [map_add, map_mul, aeval_X, aeval_C, hr0] at h1
    have h2 : algebraMap K.E A (Q'.coeff 0) * algebraMap K.E A (Q'.coeff 0)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hQ'0, map_one]
    linear_combination (-(algebraMap K.E A (Q'.coeff 0)⁻¹)) * h1 + h2
  letI : Invertible v := ⟨r, hrv, by rw [mul_comm]; exact hrv⟩
  have hce : ∀ y, K.c (e.symm y) = e.symm (cj w y) := by
    intro y; apply e.injective; rw [he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hmapc : Q'.map K.c.toRingHom = (Q.map (cj w)).map e.symm.toRingHom := by
    rw [hQ', Polynomial.map_map, Polynomial.map_map]; congr 1; ext y; exact hce y
  have hrev : (Q'.map K.c.toRingHom).reverse = C (e.symm (cj w (Q.coeff 0))) * Q' := by
    rw [hmapc]
    unfold reverse
    rw [natDegree_map_eq_of_injective hinj, reflect_map, ← reverse, ← hc, Polynomial.map_mul, map_C]
    rfl
  have hev : eval₂ ((algebraMap K.E A).comp K.c.toRingHom) v Q' = 0 := by
    rw [← eval₂_map, ← eval₂_reverse_mul_pow (algebraMap K.E A) v, hrev]
    show eval₂ (algebraMap K.E A) r (C (e.symm (cj w (Q.coeff 0))) * Q') * _ = 0
    have hev0 : eval₂ (algebraMap K.E A) r Q' = 0 := by rw [← aeval_def]; exact hr0
    rw [eval₂_mul, hev0, mul_zero, zero_mul]
  let σ0 : A →+* A := AdjoinRoot.lift ((algebraMap K.E A).comp K.c.toRingHom) v hev
  have hσr : σ0 r = v := AdjoinRoot.lift_root hev
  have hσof : ∀ a, σ0 (algebraMap K.E A a) = algebraMap K.E A (K.c a) := fun a => AdjoinRoot.lift_of hev
  have hσv : σ0 v = r := by
    calc σ0 v = σ0 v * (r * v) := by rw [hrv, mul_one]
      _ = σ0 (r * v) * r := by rw [map_mul σ0 r v, hσr]; ring
      _ = r := by rw [hrv, map_one, one_mul]
  have hcomp : σ0.comp σ0 = RingHom.id A := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro a
      show σ0 (σ0 (algebraMap K.E A a)) = algebraMap K.E A a
      rw [hσof, hσof]; simp [K.c_c]
    · show σ0 (σ0 r) = r
      rw [hσr, hσv]
  have hσσ : ∀ y, σ0 (σ0 y) = y := fun y => RingHom.congr_fun hcomp y
  let σ : A ≃+* A :=
    { toFun := σ0, invFun := σ0, left_inv := hσσ, right_inv := hσσ, map_mul' := map_mul σ0, map_add' := map_add σ0 }
  set tE : K.E := algebraMap K.O K.E t
  have htE : tE ≠ 0 := fun h => ht ((IsFractionRing.injective K.O K.E) (by rw [map_zero]; exact h))
  let B : GlobalTheory.UnitLemma.InvAlg K :=
    { A := A, σ := σ, σ_σ := hσσ, σ_alg := hσof, g := (r - 1) * algebraMap K.E A tE⁻¹ }
  have hu : (1 + algebraMap K.O B.A t * B.g) = r := by
    show (1 + algebraMap K.O A t * ((r - 1) * algebraMap K.E A tE⁻¹)) = r
    rw [IsScalarTower.algebraMap_apply K.O K.E A t]
    have h3 : algebraMap K.E A tE * algebraMap K.E A tE⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ htE, map_one]
    linear_combination (r - 1) * h3
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · rw [hu]; exact AdjoinRoot.adjoinRoot_eq_top
  · rw [hu]; exact hr0
  · show Module.finrank K.E A = Q.natDegree
    rw [pb.finrank, AdjoinRoot.powerBasis'_dim, hdeg]
  · rw [hu]
    show r * σ0 r = 1
    rw [hσr, hrv]

end GlobalTheory.InvAlgConstr
