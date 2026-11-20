import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

noncomputable section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa.Det

section Ep

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem epM_mul_epM (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) : DD.epM Z * DD.epM Z' = 0 := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem epM_add (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM (fun j => Z j + Z' j) = DD.epM Z + DD.epM Z' := by
  ext a b <;> simp [DD.epM]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem epM_zero : DD.epM (fun _ : Fin g => (0 : Matrix (Fin n) (Fin n) X)) = 0 := by
  ext a b <;> simp [DD.epM]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem mul_epM (M : Matrix (Fin n) (Fin n) A) (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    M.map (algebraMap A (DD X g)) * DD.epM Z = DD.epM fun j => M.map (algebraMap A X) * Z j := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem epM_mul (M : Matrix (Fin n) (Fin n) A) (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * M.map (algebraMap A (DD X g)) = DD.epM fun j => Z j * M.map (algebraMap A X) := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
private theorem add_mul_sub_epM (Z : Fin g → Matrix (Fin n) (Fin n) X) : (1 + DD.epM Z) * (1 - DD.epM Z) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one, epM_mul_epM]; abel

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
private theorem sub_mul_add_epM (Z : Fin g → Matrix (Fin n) (Fin n) X) : (1 - DD.epM Z) * (1 + DD.epM Z) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, epM_mul_epM]; abel

end Ep

section Rho

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X] [Algebra x.A X]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem ρX_one : x.ρX X 1 = 1 := by
  simp [NP.ρX, mat]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem ρX_mul (g h : F.G₀) : x.ρX X (g * h) = x.ρX X g * x.ρX X h := by
  simp [NP.ρX, mat, Matrix.map_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem w_wi (v : F.Vl) : x.wX X v * x.wiX X v = 1 := by
  rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem wi_w (v : F.Vl) : x.wiX X v * x.wX X v = 1 := by
  rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp

variable {x} (k : Kap x)

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem coc (j) (g h : F.G₀) : k.κ j (g * h) = k.κ j g + mat x.ρ g * k.κ j h * mat x.ρ g⁻¹ := by
  have := (k.mem j).2.2.1 g h
  simpa [NP.ρX] using this

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem κ_one (j) : k.κ j 1 = 0 := by
  have := coc k j 1 1
  simpa [mat] using this

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem ρ1_one : k.ρ1 X 1 = 1 := by
  simp [Kap.ρ1, κ_one, ρX_one, epM_zero]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable.

Chain the equalities or inequalities of the calculation.
-/
private theorem ρ1_mul (g h : F.G₀) : k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h := by
  have e : (DD.epM fun j => (k.κ j (g * h)).map (algebraMap x.A X)) =
      (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) +
        x.ρX (DD X k.g) g * (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) * x.ρX (DD X k.g) g⁻¹ := by
    rw [NP.ρX, NP.ρX, mul_epM, epM_mul, ← epM_add]
    congr 1
    funext j
    rw [coc, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul]
  have i : x.ρX (DD X k.g) g⁻¹ * x.ρX (DD X k.g) g = 1 := by rw [← ρX_mul, inv_mul_cancel, ρX_one]
  have z : (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) * x.ρX (DD X k.g) g *
      (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) = 0 := by
    rw [NP.ρX, epM_mul, epM_mul_epM]
  simp only [Kap.ρ1]
  rw [e, ρX_mul]
  generalize (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) = P at *
  generalize (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) = Q at *
  generalize x.ρX (DD X k.g) g⁻¹ = s at *
  generalize x.ρX (DD X k.g) g = r at *
  generalize x.ρX (DD X k.g) h = r' at *
  calc (1 + (P + r * Q * s)) * (r * r') = r * r' + P * r * r' + r * Q * (s * r) * r' := by noncomm_ring
    _ = r * r' + P * r * r' + r * Q * r' + P * r * Q * r' := by rw [i, z]; noncomm_ring
    _ = _ := by noncomm_ring

end Rho

end UpperTheory.V.Pa.Det

open IsLocalRing UpperTheory.V.Pa

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Pa.Det.rho1Hom :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], k.ρ1 X 1 = 1 ∧ (∀ g h, k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h) ∧ (∀ g, k.ρ1 X g⁻¹ = x.ρX (DD X k.g) g⁻¹ * (1 - DD.epM fun j => (k.κ j g).map (algebraMap x.A X))) ∧ ∀ v, k.w1 X v * k.wi1 X v = 1 ∧ k.wi1 X v * k.w1 X v = 1 := by
  intro l _ F n x k X _ _
  refine ⟨ρ1_one X k, ρ1_mul X k, fun g => ?_, fun v => ⟨?_, ?_⟩⟩
  · have h1 : k.ρ1 X g * k.ρ1 X g⁻¹ = 1 := by rw [← ρ1_mul, mul_inv_cancel, ρ1_one]
    have h2 : x.ρX (DD X k.g) g⁻¹ * (1 - DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) * k.ρ1 X g = 1 := by
      rw [Kap.ρ1, mul_assoc, ← mul_assoc (1 - _), sub_mul_add_epM, one_mul, ← ρX_mul, inv_mul_cancel, ρX_one]
    exact (left_inv_eq_right_inv h2 h1).symm
  · rw [Kap.w1, Kap.wi1, mul_assoc, ← mul_assoc (x.wX _ v), w_wi, one_mul, sub_mul_add_epM]
  · rw [Kap.w1, Kap.wi1, mul_assoc, ← mul_assoc (1 + _), add_mul_sub_epM, one_mul, wi_w]
