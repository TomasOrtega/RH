import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

/- English proof (translation)
Introduce `l _ Ω _ _ W c hO z z' y y' hy hy' hz hz' ⟨m, hm⟩`. Establish `hlift : ∀ i, ∃ x : Qbar l, ∃ hx : x ∈ c.O, redL c x = m i`. Introduce `i`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (m i : ResL c)`. Conclude with `⟨a.1, a.2, by rw [redL_of_mem c a.2]; exact ha⟩`.

Use `choose u hu hum using hlift`. Establish `hl0 : (l : Qbar l) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Establish `hWu : ∀ s i, (mat W s *ᵥ u) i ∈ c.O`. Introduce `s i`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]`.

Conclude with `c.O.add_mem (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1))`. Establish `hWuR : ∀ s i, redL c ((mat W s *ᵥ u) i) = (resAct c W hO s m) i`. Introduce `s i`. Rewrite using `[resAct_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, wRed]`.

Rewrite using `[redL_add c (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1)), redL_mul c (hO _ _ _) (hu 0), redL_mul c (hO _ _ _) (hu 1), hum 0, hum 1]`. Establish `key : ∀ s i, ∃ o ∈ c.O, ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) - ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i) = (l : Qbar l) * o`. Introduce `s i`. Establish `h1` using `hz s i`. Establish `h2` using `hz' s i`.

Establish `h3 : (mat W s *ᵥ u) i - u i ∈ c.O` using `c.O.sub_mem (hWu s i) (hu i)`. Establish `hmem` using `c.O.sub_mem (c.O.sub_mem h1 h2) h3`. Use `(redL_eq_zero_iff c hmem).1 ?_` and prove the remaining obligations. Establish `e` using `congrFun (hm s) i`. Rewrite using `[redL_sub c (c.O.sub_mem h1 h2) h3, redL_sub c h1 h2, redL_sub c (hWu s i) (hu i), hWuR, hum]`.

Establish `e' : redL c ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) - redL c ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) = (resAct c W hO s m) i - m i` using `e`. Rewrite using `[e', sub_self]`. Use `choose o ho hoe using key`. Use `⟨(l : Qbar l)⁻¹ • (y - y' + u), ?_, fun s i => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hy`.

Take `⟨k', hk'⟩` from `hy'`. Use `⟨k + k' + 1, fun i => ?_⟩` and prove the remaining obligations. Establish `e : (l : Qbar l) ^ (k + k' + 1) * ((l : Qbar l)⁻¹ • (y - y' + u)) i = (l : Qbar l) ^ k' * ((l : Qbar l) ^ k * y i) - (l : Qbar l) ^ k * ((l : Qbar l) ^ k' * y' i) + (l : Qbar l) ^ (k + k') * u i`. Simplify using `only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]`. Rewrite using `[pow_succ]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `c.O.add_mem (c.O.sub_mem (c.O.mul_mem (natPow_mem c _) (hk i)) (c.O.mul_mem (natPow_mem c _) (hk' i))) (c.O.mul_mem (natPow_mem c _) (hu i))`. Establish `e : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i = o s i`.

Establish `h` using `hoe s i`. Establish `e2 : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i = (l : Qbar l)⁻¹ * (((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) - ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i))`. Simplify using `only [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_sub, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2, h, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]`. Rewrite using `[e]`. Conclude with `ho s i`.
-/
theorem divCob_of_resCoc_cohom : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (z z' : G ℚ Ω → Fin 2 → Qbar l) (y y' : Fin 2 → Qbar l),
    VecE c y → VecE c y' → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) →
    (∀ s i, (l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i ∈ c.O) →
    (∃ m : ResPlane c, ∀ s, resCoc c W z y s - resCoc c W z' y' s = resAct c W hO s m - m) →
    z - z' ∈ divCob c W := by
  intro l _ Ω _ _ W c hO z z' y y' hy hy' hz hz' ⟨m, hm⟩

  have hlift : ∀ i, ∃ x : Qbar l, ∃ hx : x ∈ c.O, redL c x = m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (m i : ResL c)
    exact ⟨a.1, a.2, by rw [redL_of_mem c a.2]; exact ha⟩
  choose u hu hum using hlift
  have hl0 : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hWu : ∀ s i, (mat W s *ᵥ u) i ∈ c.O := by
    intro s i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1))
  have hWuR : ∀ s i, redL c ((mat W s *ᵥ u) i) = (resAct c W hO s m) i := by
    intro s i
    rw [resAct_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, wRed]
    rw [redL_add c (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1)),
      redL_mul c (hO _ _ _) (hu 0), redL_mul c (hO _ _ _) (hu 1), hum 0, hum 1]
  have key : ∀ s i, ∃ o ∈ c.O, ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
      ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i) = (l : Qbar l) * o := by
    intro s i
    have h1 := hz s i
    have h2 := hz' s i
    have h3 : (mat W s *ᵥ u) i - u i ∈ c.O := c.O.sub_mem (hWu s i) (hu i)
    have hmem := c.O.sub_mem (c.O.sub_mem h1 h2) h3
    refine (redL_eq_zero_iff c hmem).1 ?_
    have e := congrFun (hm s) i
    rw [redL_sub c (c.O.sub_mem h1 h2) h3, redL_sub c h1 h2, redL_sub c (hWu s i) (hu i), hWuR, hum]
    have e' : redL c ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
        redL c ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) = (resAct c W hO s m) i - m i := e
    rw [e', sub_self]
  choose o ho hoe using key
  refine ⟨(l : Qbar l)⁻¹ • (y - y' + u), ?_, fun s i => ?_⟩
  · obtain ⟨k, hk⟩ := hy
    obtain ⟨k', hk'⟩ := hy'
    refine ⟨k + k' + 1, fun i => ?_⟩
    have e : (l : Qbar l) ^ (k + k' + 1) * ((l : Qbar l)⁻¹ • (y - y' + u)) i =
        (l : Qbar l) ^ k' * ((l : Qbar l) ^ k * y i) - (l : Qbar l) ^ k * ((l : Qbar l) ^ k' * y' i)
          + (l : Qbar l) ^ (k + k') * u i := by
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      rw [pow_succ]; field_simp; ring
    rw [e]
    exact c.O.add_mem (c.O.sub_mem (c.O.mul_mem (natPow_mem c _) (hk i)) (c.O.mul_mem (natPow_mem c _) (hk' i)))
      (c.O.mul_mem (natPow_mem c _) (hu i))
  · have e : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i = o s i := by
      have h := hoe s i
      have e2 : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i =
          (l : Qbar l)⁻¹ * (((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
            ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i)) := by
        simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_sub, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        field_simp; ring
      rw [e2, h, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
    rw [e]; exact ho s i

end GlobalTheory.Ord2
