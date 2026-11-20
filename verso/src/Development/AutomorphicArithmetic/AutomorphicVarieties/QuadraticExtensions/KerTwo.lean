import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.SubqLen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CocycleZeroMemInvariants
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResSmul

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Break down `(Nat.dvd_prime Nat.prime_two).1 h with h1 | h2` into its components or cases. Rewrite `h1` using `[Subgroup.index_eq_one]`. Substitute `h1` using the available equality. Conclude with `⟨inferInstance, 1, fun u => Or.inl trivial⟩`. Take `⟨a, ha⟩` from `Subgroup.index_eq_two_iff.1 h2`.

Conclude with `⟨Subgroup.normal_of_index_eq_two h2, a, fun u => (ha u).or.symm⟩`.
-/
private theorem gen_of_dvd_two {Q : Type} [Group Q] (H : Subgroup Q) (h : H.index ∣ 2) :
    H.Normal ∧ ∃ γ : Q, ∀ u : Q, u ∈ H ∨ u * γ ∈ H := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    subst h1
    exact ⟨inferInstance, 1, fun u => Or.inl trivial⟩
  · obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2
    exact ⟨Subgroup.normal_of_index_eq_two h2, a, fun u => (ha u).or.symm⟩

/- English proof (translation)
Introduce `Γ _ _ _ ρ U' U h hρ hd`. Take `⟨hN, γ, hγ⟩` from `gen_of_dvd_two (U'.subgroupOf U) hd`. Establish `hcl : U ≤ (Subgroup.zpowers γ.1 ⊔ U').topologicalClosure`. Use `le_trans (fun u hu => ?_) (Subgroup.le_topologicalClosure _)` and prove the remaining obligations. Break down `hγ ⟨u, hu⟩ with h1 | h1` into its components or cases.

Conclude with `Subgroup.mem_sup_right h1`. Establish `h2 : u * γ.1 ∈ Subgroup.zpowers γ.1 ⊔ U'` using `Subgroup.mem_sup_right h1`. Conclude with `(Subgroup.mul_mem_cancel_right _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))).1 h2`. Establish `hstab : ∀ m ∈ H0U ρ U', ρ γ m - m ∈ H0U ρ U'`. Introduce `m hm`.

Use `Submodule.sub_mem _ ?_ hm` and prove the remaining obligations. Introduce `u`. Establish `h1 : γ⁻¹ * ⟨u.1, h u.2⟩ * γ⁻¹⁻¹ ∈ U'.subgroupOf U` using `hN.conj_mem _ (by simp [Subgroup.mem_subgroupOf]) _`. Establish `h2 : γ.1⁻¹ * u.1 * γ.1 ∈ U'` using `by simpa [Subgroup.mem_subgroupOf] using h1`. Establish `h3 : ρ (γ.1⁻¹ * u.1 * γ.1) m = m` using `hm ⟨_, h2⟩`.

Use `show ρ u.1 (ρ γ m) = ρ γ m`. Use `conv_rhs => rw [← h3]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Simplify using `[mul_assoc]`. Set `T : H0U ρ U' →ₗ[ℤ_[2]] H0U ρ U'` to `(ρ γ - LinearMap.id).restrict (p := H0U ρ U') (q := H0U ρ U') hstab`.

Take `⟨φ, hφ⟩` from `kerResGen1 _ Γ _ ρ hρ U' U h γ γ.2 hcl T fun _ => rfl`. Use `subqLen 2 (H0U ρ U') _ _ (LinearMap.range T).mkQ φ (Submodule.mkQ_surjective _) hφ fun x => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `hd`. Establish `h1` using `kerResSmul _ Γ _ ρ U' U h x.1 x.2`. Use `Subtype.ext ?_` and prove the remaining obligations.

Use `show ((2 : ℕ) : ℤ_[2]) • x.1 = 0`. Establish `h2 : (U'.relIndex U * k) • x.1 = 0` using `by rw [mul_comm, mul_smul, h1, smul_zero]`. Rewrite `h2` using `[← hk]`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `h2`.
-/
theorem UpperTheory.V.Two.kerTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (ρ : Representation ℤ_[2] Γ (QZ 2)) (U' U : Subgroup Γ) (h : U' ≤ U), ContAction ρ → U'.relIndex U ∣ 2 → Module.length ℤ_[2] (LinearMap.ker (resU ρ h)) ≤ 1 := by
  intro Γ _ _ _ ρ U' U h hρ hd
  obtain ⟨hN, γ, hγ⟩ := gen_of_dvd_two (U'.subgroupOf U) hd
  have hcl : U ≤ (Subgroup.zpowers γ.1 ⊔ U').topologicalClosure := by
    refine le_trans (fun u hu => ?_) (Subgroup.le_topologicalClosure _)
    rcases hγ ⟨u, hu⟩ with h1 | h1
    · exact Subgroup.mem_sup_right h1
    · have h2 : u * γ.1 ∈ Subgroup.zpowers γ.1 ⊔ U' := Subgroup.mem_sup_right h1
      exact (Subgroup.mul_mem_cancel_right _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))).1 h2
  have hstab : ∀ m ∈ H0U ρ U', ρ γ m - m ∈ H0U ρ U' := by
    intro m hm
    refine Submodule.sub_mem _ ?_ hm
    intro u
    have h1 : γ⁻¹ * ⟨u.1, h u.2⟩ * γ⁻¹⁻¹ ∈ U'.subgroupOf U :=
      hN.conj_mem _ (by simp [Subgroup.mem_subgroupOf]) _
    have h2 : γ.1⁻¹ * u.1 * γ.1 ∈ U' := by simpa [Subgroup.mem_subgroupOf] using h1
    have h3 : ρ (γ.1⁻¹ * u.1 * γ.1) m = m := hm ⟨_, h2⟩
    show ρ u.1 (ρ γ m) = ρ γ m
    conv_rhs => rw [← h3]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  let T : H0U ρ U' →ₗ[ℤ_[2]] H0U ρ U' := (ρ γ - LinearMap.id).restrict (p := H0U ρ U') (q := H0U ρ U') hstab
  obtain ⟨φ, hφ⟩ := kerResGen1 _ Γ _ ρ hρ U' U h γ γ.2 hcl T fun _ => rfl
  refine subqLen 2 (H0U ρ U') _ _ (LinearMap.range T).mkQ φ (Submodule.mkQ_surjective _) hφ fun x => ?_
  obtain ⟨k, hk⟩ := hd
  have h1 := kerResSmul _ Γ _ ρ U' U h x.1 x.2
  refine Subtype.ext ?_
  show ((2 : ℕ) : ℤ_[2]) • x.1 = 0
  have h2 : (U'.relIndex U * k) • x.1 = 0 := by rw [mul_comm, mul_smul, h1, smul_zero]
  rw [← hk] at h2
  rw [Nat.cast_smul_eq_nsmul]
  exact h2
