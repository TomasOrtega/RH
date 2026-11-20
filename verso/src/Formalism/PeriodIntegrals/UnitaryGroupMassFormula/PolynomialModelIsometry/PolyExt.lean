import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.PolyExtLem

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

/- English proof (translation)
Introduce `N H _ _ σ S hσ hfin hS`. Set `d` to `Module.finrank ℂ S`. Set `b : OrthonormalBasis (Fin d) ℂ S` to `stdOrthonormalBasis ℂ S`. Establish `hc : ∀ i j : Fin d, ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ), ∀ g ∈ Kset (allPos N), inner ℂ ((b i : S) : H) (σ g ((b j : S) : H)) * g.det ^ k = MvPolynomial.eval (fun ij => g ij.1 ij.2) P` using `fun i j => hp N H σ S hσ hfin hS ((b j : S) : H) (b j).2 ((b i : S) : H)`. Use `choose k P hkP using hc`.

Set `K : ℕ` to `∑ p : Fin d × Fin d, k p.1 p.2`. Establish `hk : ∀ i j, k i j ≤ K` using `fun i j => Finset.single_le_sum (f := fun p : Fin d × Fin d => k p.1 p.2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))`. Set `Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) ℂ` to `fun i j => P i j * detPoly N ^ (K - k i j)`. Establish `hQ : ∀ g ∈ Kset (allPos N), ∀ i j, evM g (Q i j) = g.det ^ K * ⟪((b i : S) : H), σ g ((b j : S) : H)⟫_ℂ`. Introduce `g hg i j`.

Establish `e1 : evM g (Q i j) = evM g (P i j) * g.det ^ (K - k i j)`. Rewrite using `[← pe_evM_detPoly g]`. Simplify using `only [Q, evM, map_mul, map_pow]`. Rewrite using `[e1, show evM g (P i j) = _ from (hkP i j g hg).symm, mul_assoc, ← pow_add, Nat.add_sub_cancel' (hk i j), mul_comm]`. Set `Pm : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin d) (Fin d) ℂ` to `fun g => Matrix.of fun i j => evM g (Q i j)`.

Set `Pl : Matrix (Fin N) (Fin N) ℂ → (S →ₗ[ℂ] S)` to `fun g => Matrix.toLin b.toBasis b.toBasis (Pm g)`. Establish `hA : ∀ g ∈ Kset (allPos N), ∀ x : S, ((Pl g x : S) : H) = g.det ^ K • σ g (x : H)`. Introduce `g hg x`. Establish `key : S.subtype ∘ₗ Pl g = g.det ^ K • ((σ g : H →ₗ[ℂ] H) ∘ₗ S.subtype)`. Use `b.toBasis.ext fun j => ?_` and prove the remaining obligations.

Establish `hmem : σ g ((b j : S) : H) ∈ S` using `hS g hg _ (b j).2`. Establish `hsum` using `b.sum_repr' (⟨σ g ((b j : S) : H), hmem⟩ : S)`. Establish `hsumH` using `congrArg (fun y : S => (y : H)) hsum`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hsumH`. Use `show ((Matrix.toLin b.toBasis b.toBasis (Pm g) (b.toBasis j) : S) : H) = g.det ^ K • σ g ((b.toBasis j : S) : H)`.

Rewrite using `[Matrix.toLin_self]`. Simplify using `only [OrthonormalBasis.coe_toBasis, Submodule.coe_sum, Submodule.coe_smul, Pm, Matrix.of_apply]`. Use `conv_rhs => rw [← hsumH]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hQ g hg i j, smul_smul]`. Conclude with `congrArg (fun f : S →ₗ[ℂ] H => f x) key`. Establish `hPlmul : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pl (g * h) = Pl g ∘ₗ Pl h`. Introduce `g hg h hh`. Use extensionality with `x`.

Rewrite using `[LinearMap.comp_apply, hA _ (pe_mul_mem hg hh), hA g hg, hA h hh, hσ.1.2 g hg h hh, ContinuousLinearMap.comp_apply, map_smul, smul_smul, Matrix.det_mul, mul_pow]`. Establish `hB : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pm (g * h) = Pm g * Pm h`. Introduce `g hg h hh`. Apply `(Matrix.toLin b.toBasis b.toBasis).injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]`.

Conclude with `hPlmul g hg h hh`. Establish `hC1 : ∀ h ∈ Kset (allPos N), ∀ g, Pm (g * h) = Pm g * Pm h`. Introduce `h hh g`. Use extensionality with `i j`. Take `⟨Q', hQ'⟩` from `pe_right h (Q i j)`.

Set `D` to `Q' - ∑ r, Q i r * C (Pm h r j)`. Establish `hD : ∀ g', evM g' D = (Pm (g' * h) - Pm g' * Pm h) i j`. Introduce `g'`. Simplify using `only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢`. Rewrite using `[hQ']`.

Simplify using `[Pm, evM, Matrix.mul_apply]`. Establish `hD0 : D = 0` using `hu N D fun u hu' => by`. Rewrite using `[← evM, hD u, hB u (pe_unitary_mem u hu') h hh, sub_self, Matrix.zero_apply]`. Use `hD g` as an intermediate fact. Rewrite `this` using `[hD0]`.

Simplify using `only [evM, map_zero, Matrix.sub_apply] at this`. Conclude with `sub_eq_zero.mp this.symm`. Establish `hC2 : ∀ g h, Pm (g * h) = Pm g * Pm h`. Introduce `g h`. Use extensionality with `i j`.

Take `⟨Q', hQ'⟩` from `pe_left g (Q i j)`. Set `D` to `Q' - ∑ r, C (Pm g i r) * Q r j`. Establish `hD : ∀ h', evM h' D = (Pm (g * h') - Pm g * Pm h') i j`. Introduce `h'`. Simplify using `only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢`.

Rewrite using `[hQ']`. Simplify using `[Pm, evM, Matrix.mul_apply]`. Establish `hD0 : D = 0` using `hu N D fun u hu' => by`. Rewrite using `[← evM, hD u, hC1 u (pe_unitary_mem u hu') g, sub_self, Matrix.zero_apply]`. Use `hD h` as an intermediate fact.

Rewrite `this` using `[hD0]`. Simplify using `only [evM, map_zero, Matrix.sub_apply] at this`. Conclude with `sub_eq_zero.mp this.symm`. Use `⟨K, Pl, ⟨?_, ?_, ?_⟩, hA⟩` and prove the remaining obligations. Introduce `g h show Matrix.toLin b.toBasis b.toBasis (Pm (g * h)) = _`.

Rewrite using `[hC2, Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]`. Use extensionality with `x`. Rewrite using `[hA 1 (pe_one_mem N), hσ.1.1]`. Simplify using the standard rewrite rules. Introduce `x y`.

Set `fL : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ` to `(innerₛₗ ℂ y).comp ((LinearMap.applyₗ x).comp (Matrix.toLin b.toBasis b.toBasis).toLinearMap)`. Use `⟨∑ i, ∑ j, Q i j * C (fL (Matrix.single i j 1)), fun g => ?_⟩` and prove the remaining obligations. Establish `hf : ⟪y, Pl g x⟫_ℂ = fL (Pm g)` using `rfl`. Rewrite using `[hf, Matrix.matrix_eq_sum_single (Pm g)]`. Simplify using `only [map_sum, evM, map_mul, eval_C]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[show Matrix.single i j (Pm g i j) = Pm g i j • Matrix.single i j (1 : ℂ) by`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem polyExt_of (hp : PI.PolyCoef) (hu : PI.UnitaryDense) : PolyExt := by
  intro N H _ _ σ S hσ hfin hS
  classical
  let d := Module.finrank ℂ S
  let b : OrthonormalBasis (Fin d) ℂ S := stdOrthonormalBasis ℂ S
  have hc : ∀ i j : Fin d, ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ), ∀ g ∈ Kset (allPos N),
      inner ℂ ((b i : S) : H) (σ g ((b j : S) : H)) * g.det ^ k =
        MvPolynomial.eval (fun ij => g ij.1 ij.2) P :=
    fun i j => hp N H σ S hσ hfin hS ((b j : S) : H) (b j).2 ((b i : S) : H)
  choose k P hkP using hc
  let K : ℕ := ∑ p : Fin d × Fin d, k p.1 p.2
  have hk : ∀ i j, k i j ≤ K := fun i j =>
    Finset.single_le_sum (f := fun p : Fin d × Fin d => k p.1 p.2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (i, j))
  let Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) ℂ := fun i j => P i j * detPoly N ^ (K - k i j)
  have hQ : ∀ g ∈ Kset (allPos N), ∀ i j,
      evM g (Q i j) = g.det ^ K * ⟪((b i : S) : H), σ g ((b j : S) : H)⟫_ℂ := by
    intro g hg i j
    have e1 : evM g (Q i j) = evM g (P i j) * g.det ^ (K - k i j) := by
      rw [← pe_evM_detPoly g]
      simp only [Q, evM, map_mul, map_pow]
    rw [e1, show evM g (P i j) = _ from (hkP i j g hg).symm, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (hk i j), mul_comm]
  let Pm : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin d) (Fin d) ℂ := fun g => Matrix.of fun i j => evM g (Q i j)
  let Pl : Matrix (Fin N) (Fin N) ℂ → (S →ₗ[ℂ] S) := fun g => Matrix.toLin b.toBasis b.toBasis (Pm g)
  have hA : ∀ g ∈ Kset (allPos N), ∀ x : S, ((Pl g x : S) : H) = g.det ^ K • σ g (x : H) := by
    intro g hg x
    have key : S.subtype ∘ₗ Pl g = g.det ^ K • ((σ g : H →ₗ[ℂ] H) ∘ₗ S.subtype) := by
      refine b.toBasis.ext fun j => ?_
      have hmem : σ g ((b j : S) : H) ∈ S := hS g hg _ (b j).2
      have hsum := b.sum_repr' (⟨σ g ((b j : S) : H), hmem⟩ : S)
      have hsumH := congrArg (fun y : S => (y : H)) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hsumH
      show ((Matrix.toLin b.toBasis b.toBasis (Pm g) (b.toBasis j) : S) : H) =
        g.det ^ K • σ g ((b.toBasis j : S) : H)
      rw [Matrix.toLin_self]
      simp only [OrthonormalBasis.coe_toBasis, Submodule.coe_sum, Submodule.coe_smul, Pm, Matrix.of_apply]
      conv_rhs => rw [← hsumH]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hQ g hg i j, smul_smul]
    exact congrArg (fun f : S →ₗ[ℂ] H => f x) key
  have hPlmul : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pl (g * h) = Pl g ∘ₗ Pl h := by
    intro g hg h hh
    ext x
    rw [LinearMap.comp_apply, hA _ (pe_mul_mem hg hh), hA g hg, hA h hh, hσ.1.2 g hg h hh,
      ContinuousLinearMap.comp_apply, map_smul, smul_smul, Matrix.det_mul, mul_pow]
  have hB : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pm (g * h) = Pm g * Pm h := by
    intro g hg h hh
    apply (Matrix.toLin b.toBasis b.toBasis).injective
    rw [Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]
    exact hPlmul g hg h hh
  have hC1 : ∀ h ∈ Kset (allPos N), ∀ g, Pm (g * h) = Pm g * Pm h := by
    intro h hh g
    ext i j
    obtain ⟨Q', hQ'⟩ := pe_right h (Q i j)
    let D := Q' - ∑ r, Q i r * C (Pm h r j)
    have hD : ∀ g', evM g' D = (Pm (g' * h) - Pm g' * Pm h) i j := by
      intro g'
      simp only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢
      rw [hQ']
      simp [Pm, evM, Matrix.mul_apply]
    have hD0 : D = 0 := hu N D fun u hu' => by
      rw [← evM, hD u, hB u (pe_unitary_mem u hu') h hh, sub_self, Matrix.zero_apply]
    have := hD g
    rw [hD0] at this
    simp only [evM, map_zero, Matrix.sub_apply] at this
    exact sub_eq_zero.mp this.symm
  have hC2 : ∀ g h, Pm (g * h) = Pm g * Pm h := by
    intro g h
    ext i j
    obtain ⟨Q', hQ'⟩ := pe_left g (Q i j)
    let D := Q' - ∑ r, C (Pm g i r) * Q r j
    have hD : ∀ h', evM h' D = (Pm (g * h') - Pm g * Pm h') i j := by
      intro h'
      simp only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢
      rw [hQ']
      simp [Pm, evM, Matrix.mul_apply]
    have hD0 : D = 0 := hu N D fun u hu' => by
      rw [← evM, hD u, hC1 u (pe_unitary_mem u hu') g, sub_self, Matrix.zero_apply]
    have := hD h
    rw [hD0] at this
    simp only [evM, map_zero, Matrix.sub_apply] at this
    exact sub_eq_zero.mp this.symm
  refine ⟨K, Pl, ⟨?_, ?_, ?_⟩, hA⟩
  · intro g h
    show Matrix.toLin b.toBasis b.toBasis (Pm (g * h)) = _
    rw [hC2, Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]
  · ext x
    rw [hA 1 (pe_one_mem N), hσ.1.1]
    simp
  · intro x y
    let fL : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ :=
      (innerₛₗ ℂ y).comp ((LinearMap.applyₗ x).comp (Matrix.toLin b.toBasis b.toBasis).toLinearMap)
    refine ⟨∑ i, ∑ j, Q i j * C (fL (Matrix.single i j 1)), fun g => ?_⟩
    have hf : ⟪y, Pl g x⟫_ℂ = fL (Pm g) := rfl
    rw [hf, Matrix.matrix_eq_sum_single (Pm g)]
    simp only [map_sum, evM, map_mul, eval_C]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Matrix.single i j (Pm g i j) = Pm g i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    rfl

end PI.WMI
