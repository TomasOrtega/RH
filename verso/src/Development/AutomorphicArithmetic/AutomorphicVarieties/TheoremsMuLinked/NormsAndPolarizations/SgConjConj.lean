import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

namespace UpperTheory.V.Th.Nm

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g`. Establish `h : F.c⁻¹ = F.c` using `inv_eq_of_mul_eq_one_right F.c_sq`. Rewrite using `[h, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]`.
-/
private theorem sg_conj_conj (g : F.G₀) : F.conj (F.conj g) = g := by
  apply Subtype.ext
  change F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g
  have h : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  rw [h, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]

/- English proof (translation)
Establish `h : F.ε (F.c * g * F.c⁻¹) = F.ε g`. Rewrite using `[map_mul, map_mul, map_inv, mul_inv_cancel_comm]`. Conclude with `congrArg (Units.map (((algebraMap O R).comp (algebraMap ℤ_[l] O) : ℤ_[l] →+* R) : ℤ_[l] →* R)) h`.
-/
private theorem sg_eps_conj (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) :
    F.eps O R (F.conj g) = F.eps O R g := by
  have h : F.ε (F.c * g * F.c⁻¹) = F.ε g := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  exact congrArg (Units.map (((algebraMap O R).comp (algebraMap ℤ_[l] O) : ℤ_[l] →+* R) : ℤ_[l] →* R)) h

end

/- English proof (translation)
Establish `h3 : Aᵀ * Pᵀ * B = e • Pᵀ`. Use `congrArg transpose h2` as an intermediate fact. Rewrite `this` using `[transpose_mul, transpose_mul, transpose_transpose, transpose_smul, ← mul_assoc]`. Then use the resulting hypothesis. Establish `hu : IsUnit (Aᵀ * P)` using `((isUnit_transpose A).2 hA).mul hP`. Apply `hu.mul_left_cancel` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem sg_comm {K : Type} [Field K] {n : ℕ} (A B P Q : Matrix (Fin n) (Fin n) K) (e : K) (hA : IsUnit A)
    (hP : IsUnit P) (hQ : P * Q = 1) (h1 : Aᵀ * P * B = e • P) (h2 : Bᵀ * P * A = e • P) :
    B * (Q * Pᵀ) = (Q * Pᵀ) * B := by
  have h3 : Aᵀ * Pᵀ * B = e • Pᵀ := by
    have := congrArg transpose h2
    rwa [transpose_mul, transpose_mul, transpose_transpose, transpose_smul, ← mul_assoc] at this
  have hu : IsUnit (Aᵀ * P) := ((isUnit_transpose A).2 hA).mul hP
  apply hu.mul_left_cancel
  calc Aᵀ * P * (B * (Q * Pᵀ)) = (Aᵀ * P * B) * Q * Pᵀ := by simp only [mul_assoc]
    _ = e • Pᵀ := by rw [h1, smul_mul_assoc, hQ, smul_mul_assoc, one_mul]
    _ = Aᵀ * (P * Q) * Pᵀ * B := by rw [hQ, mul_one, h3]
    _ = Aᵀ * P * (Q * Pᵀ * B) := by simp only [mul_assoc]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `Or.inl (Subsingleton.elim _ _)`. Take `⟨s, hs⟩` from `Matrix.mem_range_scalar_of_commute_single (M := Q * Pᵀ) (fun i j _ => h _)`. Establish `h1 : Pᵀ = s • P`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : P = (s * s) • P`. Use `congrArg transpose h1` as an intermediate fact. Rewrite `this` using `[transpose_transpose, transpose_smul, h1, smul_smul]`. Then use the resulting hypothesis. Establish `h3 : s * s = 1`. Establish `h4 : (1 : Matrix (Fin n) (Fin n) K) = (s * s) • 1`.

Combine the equalities or inequalities in the displayed calculation. Establish `h5` using `congrFun (congrFun h4 ⟨0, hn⟩) ⟨0, hn⟩`. Simplify using `using h5.symm`. Break down `mul_self_eq_one_iff.1 h3 with rfl | rfl` into its components or cases. Conclude with `Or.inl (by rw [h1, one_smul])`.

Conclude with `Or.inr (by rw [h1, neg_smul, one_smul])`.
-/
private theorem sg_end {K : Type} [Field K] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) K) (hQ : P * Q = 1)
    (h : ∀ Z : Matrix (Fin n) (Fin n) K, Z * (Q * Pᵀ) = (Q * Pᵀ) * Z) : Pᵀ = P ∨ Pᵀ = -P := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl (Subsingleton.elim _ _)
  obtain ⟨s, hs⟩ := Matrix.mem_range_scalar_of_commute_single (M := Q * Pᵀ) (fun i j _ => h _)
  have h1 : Pᵀ = s • P := by
    calc Pᵀ = P * (Q * Pᵀ) := by rw [← mul_assoc, hQ, one_mul]
      _ = s • P := by rw [← hs, scalar_apply, ← smul_eq_mul_diagonal]
  have h2 : P = (s * s) • P := by
    have := congrArg transpose h1
    rwa [transpose_transpose, transpose_smul, h1, smul_smul] at this
  have h3 : s * s = 1 := by
    have h4 : (1 : Matrix (Fin n) (Fin n) K) = (s * s) • 1 := by
      calc (1 : Matrix (Fin n) (Fin n) K) = P * Q := hQ.symm
        _ = ((s * s) • P) * Q := by rw [← h2]
        _ = (s * s) • 1 := by rw [smul_mul_assoc, hQ]
    have h5 := congrFun (congrFun h4 ⟨0, hn⟩) ⟨0, hn⟩
    simpa using h5.symm
  rcases mul_self_eq_one_iff.1 h3 with rfl | rfl
  · exact Or.inl (by rw [h1, one_smul])
  · exact Or.inr (by rw [h1, neg_smul, one_smul])

end UpperTheory.V.Th.Nm

/- English proof (translation)
Introduce `l _ n F c ρ P hsp hf`. Establish `hQ : (P : Matrix (Fin n) (Fin n) (Qbar l)) * ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = 1` using `Units.mul_inv P`. Use `sg_end _ _ hQ fun Z => ?_` and prove the remaining obligations. Establish `hZ : Z ∈ Submodule.span (Qbar l) (Set.range (mat ρ))` using `hsp ▸ Submodule.mem_top`. Proceed by induction on `hZ using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `hx`. Establish `h1` using `hf (F.conj g)`. Rewrite `h1` using `[sg_conj_conj, sg_eps_conj]`. Conclude with `sg_comm _ _ _ _ _ (ρ (F.conj g)).isUnit P.isUnit hQ h1 (hf g)`.

Consider the case `zero => rw [zero_mul, mul_zero]`. Consider the case `add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]`. Consider the case `smul a x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]`.
-/
theorem UpperTheory.V.Th.Nm.sign :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → F.IsForm c.O n ρ P → (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P := by
  intro l _ n F c ρ P hsp hf
  have hQ : (P : Matrix (Fin n) (Fin n) (Qbar l)) * ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = 1 :=
    Units.mul_inv P
  refine sg_end _ _ hQ fun Z => ?_
  have hZ : Z ∈ Submodule.span (Qbar l) (Set.range (mat ρ)) := hsp ▸ Submodule.mem_top
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    have h1 := hf (F.conj g)
    rw [sg_conj_conj, sg_eps_conj] at h1
    exact sg_comm _ _ _ _ _ (ρ (F.conj g)).isUnit P.isUnit hQ h1 (hf g)
  | zero => rw [zero_mul, mul_zero]
  | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
  | smul a x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
