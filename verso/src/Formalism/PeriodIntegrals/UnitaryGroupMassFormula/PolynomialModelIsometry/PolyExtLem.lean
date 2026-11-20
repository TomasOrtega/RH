import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.IsPolyMon

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

/- English proof (translation)
Unfold `evM detPoly`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
lemma pe_evM_detPoly {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) : evM g (detPoly N) = g.det := by
  unfold evM detPoly
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

/- English proof (translation)
Use `⟨one_mem _, by simp⟩` and prove the remaining obligations.
-/
lemma pe_one_mem (N : ℕ) : (1 : Matrix (Fin N) (Fin N) ℂ) ∈ Kset (allPos N) := by
  refine ⟨one_mem _, by simp⟩

/- English proof (translation)
Use `⟨mul_mem hg.1 hh.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]`.
-/
lemma pe_mul_mem {N : ℕ} {g h : Matrix (Fin N) (Fin N) ℂ} (hg : g ∈ Kset (allPos N)) (hh : h ∈ Kset (allPos N)) :
    g * h ∈ Kset (allPos N) := by
  refine ⟨mul_mem hg.1 hh.1, ?_⟩
  rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]

/- English proof (translation)
Establish `hJ : Jm (allPos N) = 1`. Unfold `Jm allPos`. Simplify using the standard rewrite rules. Use `⟨?_, by rw [hJ]; simp⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff']`.

Conclude with `hu`.
-/
lemma pe_unitary_mem {N : ℕ} (u : Matrix (Fin N) (Fin N) ℂ) (hu : uᴴ * u = 1) : u ∈ Kset (allPos N) := by
  have hJ : Jm (allPos N) = 1 := by
    unfold Jm allPos
    simp
  refine ⟨?_, by rw [hJ]; simp⟩
  rw [Matrix.mem_unitaryGroup_iff']
  exact hu

/- English proof (translation)
Use `⟨bind₁ (fun pq : Fin N × Fin N => ∑ r, X (pq.1, r) * C (h r pq.2)) Q, fun g => ?_⟩` and prove the remaining obligations. Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a => simp [evM]`. Consider the case `add p q hp hq => simp only [map_add, evM] at *`. Rewrite using `[hp, hq]`.

Consider the case `mul_X p n hp`. Simplify using `only [map_mul, evM, bind₁_X_right] at *`. Rewrite using `[hp]`. Simplify using `[Matrix.mul_apply]`.
-/
lemma pe_right {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ Q' : MvPolynomial (Fin N × Fin N) ℂ, ∀ g, evM g Q' = evM (g * h) Q := by
  refine ⟨bind₁ (fun pq : Fin N × Fin N => ∑ r, X (pq.1, r) * C (h r pq.2)) Q, fun g => ?_⟩
  induction Q using MvPolynomial.induction_on with
  | C a => simp [evM]
  | add p q hp hq => simp only [map_add, evM] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, evM, bind₁_X_right] at *
    rw [hp]
    simp [Matrix.mul_apply]

/- English proof (translation)
Use `⟨bind₁ (fun pq : Fin N × Fin N => ∑ r, C (g pq.1 r) * X (r, pq.2)) Q, fun h => ?_⟩` and prove the remaining obligations. Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C a => simp [evM]`. Consider the case `add p q hp hq => simp only [map_add, evM] at *`. Rewrite using `[hp, hq]`.

Consider the case `mul_X p n hp`. Simplify using `only [map_mul, evM, bind₁_X_right] at *`. Rewrite using `[hp]`. Simplify using `[Matrix.mul_apply]`.
-/
lemma pe_left {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    ∃ Q' : MvPolynomial (Fin N × Fin N) ℂ, ∀ h, evM h Q' = evM (g * h) Q := by
  refine ⟨bind₁ (fun pq : Fin N × Fin N => ∑ r, C (g pq.1 r) * X (r, pq.2)) Q, fun h => ?_⟩
  induction Q using MvPolynomial.induction_on with
  | C a => simp [evM]
  | add p q hp hq => simp only [map_add, evM] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, evM, bind₁_X_right] at *
    rw [hp]
    simp [Matrix.mul_apply]

end PI.WMI
