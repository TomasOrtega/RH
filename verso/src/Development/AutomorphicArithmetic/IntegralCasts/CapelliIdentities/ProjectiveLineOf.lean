import Mathlib

noncomputable def UpperTheory.Reformulated.B.ProjectiveLineOf.P1 :
    Prop :=
    ∀ (k : Type) [inst : NontriviallyNormedField k] [LocallyCompactSpace k] [CharZero k] (n : ℕ) (γ : GL (Fin n) k),
      (↑γ : Matrix (Fin n) (Fin n) k).charpoly.Separable →
        ∀ (D : Set (GL (Fin n) k)),
          IsCompact D →
            ∃ (C : Set (GL (Fin n) k)),
              IsCompact C ∧ ∀ (x : GL (Fin n) k), x⁻¹ * γ * x ∈ D → ∃ (t : GL (Fin n) k), t * γ = γ * t ∧ ∃ y ∈ C, x = t * y

section

open Polynomial Matrix

/- English proof (translation)
Distinguish the cases in `hp0 : p = 0`. Simplify using `[hp0]`. Set `K` to `AlgebraicClosure k`. Set `f` to `algebraMap k K`. Rewrite using `[← Polynomial.map_dvd_map' f]`.

Establish `hsep : (A.charpoly.map f).Separable` using `hA.map`. Use `(IsAlgClosed.splits _).dvd_of_roots_le_roots hsep.ne_zero ?_` and prove the remaining obligations. Rewrite using `[Multiset.le_iff_subset (nodup_roots hsep)]`. Introduce `r hr`. Establish `hr' : (A.map f).charpoly.IsRoot r`.

Rewrite using `[Matrix.charpoly_map]`. Conclude with `isRoot_of_mem_roots hr`. Rewrite `hr'` using `[← Matrix.mem_spectrum_iff_isRoot_charpoly]`. Establish `h1` using `spectrum.subset_polynomial_aeval (A.map f) (p.map f) ⟨r, hr', rfl⟩`. Establish `h2 : aeval (A.map f) (p.map f) = 0`.

Establish `h3 : aeval ((Algebra.ofId k K).mapMatrix A) p = 0`. Rewrite using `[aeval_algHom_apply, hp, map_zero]`. Rewrite using `[aeval_map_algebraMap]`. Conclude with `h3`. Rewrite using `[mem_roots (Polynomial.map_ne_zero hp0)]`.

Assume the negation of the conclusion as `hne`. Rewrite `h1` using `[h2, spectrum.mem_iff, sub_zero]`. Conclude with `h1 ((IsUnit.mk0 _ hne).map _)`.
-/
private theorem charpoly_dvd_of_aeval {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (hA : A.charpoly.Separable) (p : k[X]) (hp : aeval A p = 0) : A.charpoly ∣ p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  let K := AlgebraicClosure k
  let f := algebraMap k K
  rw [← Polynomial.map_dvd_map' f]
  have hsep : (A.charpoly.map f).Separable := hA.map
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots hsep.ne_zero ?_
  rw [Multiset.le_iff_subset (nodup_roots hsep)]
  intro r hr
  have hr' : (A.map f).charpoly.IsRoot r := by
    rw [Matrix.charpoly_map]; exact isRoot_of_mem_roots hr
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly] at hr'
  have h1 := spectrum.subset_polynomial_aeval (A.map f) (p.map f) ⟨r, hr', rfl⟩
  have h2 : aeval (A.map f) (p.map f) = 0 := by
    have h3 : aeval ((Algebra.ofId k K).mapMatrix A) p = 0 := by
      rw [aeval_algHom_apply, hp, map_zero]
    rw [aeval_map_algebraMap]
    exact h3
  rw [mem_roots (Polynomial.map_ne_zero hp0)]
  by_contra hne
  rw [h2, spectrum.mem_iff, sub_zero] at h1
  exact h1 ((IsUnit.mk0 _ hne).map _)

private def krylov {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i j => ((A ^ (j : ℕ)) *ᵥ v) i

/- English proof (translation)
Establish `h : aeval A p = ∑ j : Fin n, p.coeff j • A ^ (j : ℕ)` using `by conv_lhs => rw [← p.sum_C_mul_X_pow_eq, ← Polynomial.sum_fin _ (by simp) hp]`. Simplify using `[Algebra.smul_def]`. Rewrite using `[h, Matrix.sum_mulVec]`. Use extensionality with `i`. Simplify using `[krylov, Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]`.
-/
private theorem krylov_mulVec {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) (p : k[X]) (hp : p.degree < n) :
    krylov A v *ᵥ (fun j => p.coeff j) = aeval A p *ᵥ v := by
  have h : aeval A p = ∑ j : Fin n, p.coeff j • A ^ (j : ℕ) := by
    conv_lhs => rw [← p.sum_C_mul_X_pow_eq, ← Polynomial.sum_fin _ (by simp) hp]
    simp [Algebra.smul_def]
  rw [h, Matrix.sum_mulVec]
  ext i
  simp [krylov, Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm,
    mul_assoc]

/- English proof (translation)
Take `⟨x, hx⟩` from `Module.exists_ker_toSpanSingleton_eq_annihilator k[X] (Module.AEval' (Matrix.toLin' A))`. Take `⟨v, rfl⟩` from `(Module.AEval'.of _).surjective x`. Use `⟨v, fun hdet => ?_⟩` and prove the remaining obligations. Take `⟨c, hc0, hc⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Set `p : k[X]` to `(degreeLTEquiv k n).symm c`.

Establish `hpdeg : p.degree < n` using `mem_degreeLT.mp ((degreeLTEquiv k n).symm c).2`. Establish `hpc : (fun j : Fin n => p.coeff j) = c` using `(degreeLTEquiv k n).apply_symm_apply c`. Establish `hlin : aeval (Matrix.toLin' A) p = Matrix.toLin' (aeval A p)` using `aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)) A p`. Establish `h1 : aeval A p *ᵥ v = 0` using `by rw [← krylov_mulVec A v p hpdeg, hpc, hc]`. Establish `h2 : p ∈ Module.annihilator k[X] (Module.AEval' (Matrix.toLin' A))`.

Rewrite using `[← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Module.AEval.of_aeval_smul, Module.End.smul_def, hlin, Matrix.toLin'_apply, h1, map_zero]`. Rewrite `h2` using `[Module.AEval.annihilator_eq_ker_aeval, RingHom.mem_ker, hlin, map_eq_zero_iff _ Matrix.toLin'.injective]`. Establish `h3` using `charpoly_dvd_of_aeval A hA p h2`. Establish `h4 : p = 0`. Use `eq_zero_of_dvd_of_degree_lt h3 ?_` and prove the remaining obligations.

Simplify `hpdeg` using `[Matrix.charpoly_degree_eq_dim]`. Apply `hc0` to reduce the goal to its premises. Rewrite using `[← hpc, h4]`. Both sides reduce to the same expression.
-/
private theorem exists_krylov_det_ne_zero {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (hA : A.charpoly.Separable) :
    ∃ v, (krylov A v).det ≠ 0 := by
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator k[X]
    (Module.AEval' (Matrix.toLin' A))
  obtain ⟨v, rfl⟩ := (Module.AEval'.of _).surjective x
  refine ⟨v, fun hdet => ?_⟩
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : k[X] := (degreeLTEquiv k n).symm c
  have hpdeg : p.degree < n := mem_degreeLT.mp ((degreeLTEquiv k n).symm c).2
  have hpc : (fun j : Fin n => p.coeff j) = c := (degreeLTEquiv k n).apply_symm_apply c
  have hlin : aeval (Matrix.toLin' A) p = Matrix.toLin' (aeval A p) :=
    aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)) A p
  have h1 : aeval A p *ᵥ v = 0 := by rw [← krylov_mulVec A v p hpdeg, hpc, hc]
  have h2 : p ∈ Module.annihilator k[X] (Module.AEval' (Matrix.toLin' A)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      ← Module.AEval.of_aeval_smul, Module.End.smul_def, hlin, Matrix.toLin'_apply, h1, map_zero]
  rw [Module.AEval.annihilator_eq_ker_aeval, RingHom.mem_ker, hlin, map_eq_zero_iff _ Matrix.toLin'.injective] at h2
  have h3 := charpoly_dvd_of_aeval A hA p h2
  have h4 : p = 0 := by
    refine eq_zero_of_dvd_of_degree_lt h3 ?_
    simpa [Matrix.charpoly_degree_eq_dim] using hpdeg
  apply hc0
  rw [← hpc, h4]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Establish `hdeg : (X ^ ((j : ℕ) + 1) %ₘ A.charpoly).degree < n`. Simplify `degree_modByMonic_lt (X ^ ((j : ℕ) + 1)) A.charpoly_monic` using `[Matrix.charpoly_degree_eq_dim]`. Establish `h` using `congrFun (krylov_mulVec A v _ hdeg) i`. Rewrite `h` using `[← Matrix.pow_eq_aeval_mod_charpoly, pow_succ' A, ← Matrix.mulVec_mulVec]`.

Conclude with `h.symm`.
-/
private theorem mul_krylov {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) :
    A * krylov A v = krylov A v *
      Matrix.of fun i j : Fin n => (X ^ ((j : ℕ) + 1) %ₘ A.charpoly).coeff i := by
  ext i j
  have hdeg : (X ^ ((j : ℕ) + 1) %ₘ A.charpoly).degree < n := by
    simpa [Matrix.charpoly_degree_eq_dim] using
      degree_modByMonic_lt (X ^ ((j : ℕ) + 1)) A.charpoly_monic
  have h := congrFun (krylov_mulVec A v _ hdeg) i
  rw [← Matrix.pow_eq_aeval_mod_charpoly, pow_succ' A, ← Matrix.mulVec_mulVec] at h
  exact h.symm

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Conclude with `(continuous_apply i).comp ((Units.continuous_val.pow _).matrix_mulVec continuous_const)`.
-/
private theorem continuous_krylov {k : Type} [NontriviallyNormedField k] {n : ℕ} (v : Fin n → k) :
    Continuous fun δ : GL (Fin n) k => krylov (δ : Matrix (Fin n) (Fin n) k) v := by
  refine continuous_matrix fun i j => ?_
  exact (continuous_apply i).comp ((Units.continuous_val.pow _).matrix_mulVec continuous_const)

/- English proof (translation)
Establish `: CompactSpace S` using `isCompact_iff_compactSpace.mp hS`. Set `Φ : S → GL (Fin n) k` to `fun δ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (h δ.1 δ.2)`. Establish `hval : ∀ δ : S, (Φ δ : Matrix (Fin n) (Fin n) k) = krylov (δ.1 : Matrix (Fin n) (Fin n) k) v` using `fun δ => rfl`. Establish `hc : Continuous fun δ : S => krylov (δ.1 : Matrix (Fin n) (Fin n) k) v` using `(continuous_krylov v).comp continuous_subtype_val`. Establish `hΦ : Continuous Φ`.

Rewrite using `[Units.continuous_iff]`. Use `⟨hc, ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[Matrix.coe_units_inv, hval, Matrix.inv_def, Ring.inverse_eq_inv']`. Conclude with `(hc.matrix_det.inv₀ fun δ => h δ.1 δ.2).smul hc.matrix_adjugate`. Conclude with `⟨Set.range Φ, isCompact_range hΦ, fun δ hδ => ⟨Φ ⟨δ, hδ⟩, ⟨_, rfl⟩, rfl⟩⟩`.
-/
private theorem exists_compact_krylov {k : Type} [NontriviallyNormedField k] {n : ℕ}
    (v : Fin n → k) (S : Set (GL (Fin n) k)) (hS : IsCompact S)
    (h : ∀ δ ∈ S, (krylov (δ : Matrix (Fin n) (Fin n) k) v).det ≠ 0) :
    ∃ C : Set (GL (Fin n) k), IsCompact C ∧
      ∀ δ ∈ S, ∃ u ∈ C, (u : Matrix (Fin n) (Fin n) k) = krylov (δ : Matrix (Fin n) (Fin n) k) v := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let Φ : S → GL (Fin n) k := fun δ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (h δ.1 δ.2)
  have hval : ∀ δ : S, (Φ δ : Matrix (Fin n) (Fin n) k) =
      krylov (δ.1 : Matrix (Fin n) (Fin n) k) v := fun δ => rfl
  have hc : Continuous fun δ : S => krylov (δ.1 : Matrix (Fin n) (Fin n) k) v :=
    (continuous_krylov v).comp continuous_subtype_val
  have hΦ : Continuous Φ := by
    rw [Units.continuous_iff]
    refine ⟨hc, ?_⟩
    simp_rw [Matrix.coe_units_inv, hval, Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hc.matrix_det.inv₀ fun δ => h δ.1 δ.2).smul hc.matrix_adjugate
  exact ⟨Set.range Φ, isCompact_range hΦ, fun δ hδ => ⟨Φ ⟨δ, hδ⟩, ⟨_, rfl⟩, rfl⟩⟩

/- English proof (translation)
Establish `h : {δ : GL (Fin n) k | (δ : Matrix (Fin n) (Fin n) k).charpoly = χ} = ⋂ r : k, {δ : GL (Fin n) k | (Matrix.scalar (Fin n) r - (δ : Matrix (Fin n) (Fin n) k)).det = χ.eval r}`. Use extensionality with `δ`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter, ← Matrix.eval_charpoly]`. Conclude with `⟨fun h r => by rw [h], Polynomial.funext⟩`. Rewrite using `[h]`.

Conclude with `isClosed_iInter fun r => isClosed_eq (continuous_const.sub Units.continuous_val).matrix_det continuous_const`.
-/
private theorem isClosed_charpoly_eq {k : Type} [NontriviallyNormedField k] [CharZero k] {n : ℕ}
    (χ : k[X]) :
    IsClosed {δ : GL (Fin n) k | (δ : Matrix (Fin n) (Fin n) k).charpoly = χ} := by
  have h : {δ : GL (Fin n) k | (δ : Matrix (Fin n) (Fin n) k).charpoly = χ} =
      ⋂ r : k, {δ : GL (Fin n) k |
        (Matrix.scalar (Fin n) r - (δ : Matrix (Fin n) (Fin n) k)).det = χ.eval r} := by
    ext δ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, ← Matrix.eval_charpoly]
    exact ⟨fun h r => by rw [h], Polynomial.funext⟩
  rw [h]
  exact isClosed_iInter fun r =>
    isClosed_eq (continuous_const.sub Units.continuous_val).matrix_det continuous_const

end

/- English proof (translation)
Introduce `k _ _ _ n γ hγ D hD`. Use `set χ := (γ : Matrix (Fin n) (Fin n) k).charpoly with hχ`. Establish `hD'` using `hD.inter_right (isClosed_charpoly_eq (n := n) χ)`. Set `U : (Fin n → k) → Set (GL (Fin n) k)` to `fun v => {δ | (krylov (δ : Matrix (Fin n) (Fin n) k) v).det ≠ 0}`. Establish `hU : ∀ v, IsOpen (U v)` using `fun v => isOpen_ne_fun (continuous_krylov v).matrix_det continuous_const`.

Take `⟨s, hs⟩` from `hD'.elim_finite_subcover U hU (by`. Introduce and unpack `δ ⟨-, hδ⟩`. Conclude with `Set.mem_iUnion.mpr (exists_krylov_det_ne_zero _ (by rw [hδ]; exact hγ)))`. Take `⟨S, hSc, hSU, hS⟩` from `hD'.finite_compact_cover s U (fun v _ => hU v) hs`. Use `choose C hCc hC using fun v => exists_compact_krylov v (S v) (hSc v) (hSU v)`.

Take `⟨v₀, hv₀⟩` from `exists_krylov_det_ne_zero _ hγ`. Set `u₀ : GL (Fin n) k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero _ hv₀`. Establish `hu₀ : (u₀ : Matrix (Fin n) (Fin n) k) = krylov (γ : Matrix (Fin n) (Fin n) k) v₀` using `rfl`. Use `⟨⋃ v ∈ s, (fun u => u₀ * u⁻¹) '' C v, s.isCompact_biUnion fun v _ => (hCc v).image (by fun_prop), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hch : ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = χ`.

Rewrite using `[Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]`. Establish `hmem : x⁻¹ * γ * x ∈ ⋃ v ∈ s, S v` using `hS ▸ ⟨hx, hch⟩`. Take `⟨v, hv, hxv⟩` from `Set.mem_iUnion₂.mp hmem`. Take `⟨u, huC, hu⟩` from `hC v _ hxv`. Establish `h1` using `mul_krylov ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) v`.

Establish `h2` using `mul_krylov (γ : Matrix (Fin n) (Fin n) k) v₀`. Rewrite `h1` using `[← hu, hch]`. Rewrite `h2` using `[← hu₀, ← hχ]`. Establish `h3 : u⁻¹ * (x⁻¹ * γ * x) * u = u₀⁻¹ * γ * u₀`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[mul_assoc, mul_assoc u₀⁻¹, Units.val_mul, Units.val_mul, h1, Units.val_mul, Units.val_mul, h2, Units.inv_mul_cancel_left, Units.inv_mul_cancel_left]`. Use `⟨x * u * u₀⁻¹, ?_, u₀ * u⁻¹, Set.mem_iUnion₂.mpr ⟨v, hv, u, huC, rfl⟩, by group⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Reformulated.B.ProjectiveLineOf.p1_holds :
    UpperTheory.Reformulated.B.ProjectiveLineOf.P1 := by
  intro k _ _ _ n γ hγ D hD
  classical
  set χ := (γ : Matrix (Fin n) (Fin n) k).charpoly with hχ
  have hD' := hD.inter_right (isClosed_charpoly_eq (n := n) χ)
  let U : (Fin n → k) → Set (GL (Fin n) k) := fun v =>
    {δ | (krylov (δ : Matrix (Fin n) (Fin n) k) v).det ≠ 0}
  have hU : ∀ v, IsOpen (U v) := fun v =>
    isOpen_ne_fun (continuous_krylov v).matrix_det continuous_const
  obtain ⟨s, hs⟩ := hD'.elim_finite_subcover U hU (by
    rintro δ ⟨-, hδ⟩
    exact Set.mem_iUnion.mpr (exists_krylov_det_ne_zero _ (by rw [hδ]; exact hγ)))
  obtain ⟨S, hSc, hSU, hS⟩ := hD'.finite_compact_cover s U (fun v _ => hU v) hs
  choose C hCc hC using fun v => exists_compact_krylov v (S v) (hSc v) (hSU v)
  obtain ⟨v₀, hv₀⟩ := exists_krylov_det_ne_zero _ hγ
  let u₀ : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hv₀
  have hu₀ : (u₀ : Matrix (Fin n) (Fin n) k) = krylov (γ : Matrix (Fin n) (Fin n) k) v₀ := rfl
  refine ⟨⋃ v ∈ s, (fun u => u₀ * u⁻¹) '' C v,
    s.isCompact_biUnion fun v _ => (hCc v).image (by fun_prop), fun x hx => ?_⟩
  have hch : ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = χ := by
    rw [Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]
  have hmem : x⁻¹ * γ * x ∈ ⋃ v ∈ s, S v := hS ▸ ⟨hx, hch⟩
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨u, huC, hu⟩ := hC v _ hxv
  have h1 := mul_krylov ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) v
  have h2 := mul_krylov (γ : Matrix (Fin n) (Fin n) k) v₀
  rw [← hu, hch] at h1
  rw [← hu₀, ← hχ] at h2
  have h3 : u⁻¹ * (x⁻¹ * γ * x) * u = u₀⁻¹ * γ * u₀ := by
    apply Units.ext
    rw [mul_assoc, mul_assoc u₀⁻¹, Units.val_mul, Units.val_mul, h1, Units.val_mul,
      Units.val_mul, h2, Units.inv_mul_cancel_left, Units.inv_mul_cancel_left]
  refine ⟨x * u * u₀⁻¹, ?_, u₀ * u⁻¹, Set.mem_iUnion₂.mpr ⟨v, hv, u, huC, rfl⟩, by group⟩
  calc x * u * u₀⁻¹ * γ = x * u * (u₀⁻¹ * γ * u₀) * u₀⁻¹ := by group
    _ = γ * (x * u * u₀⁻¹) := by rw [← h3]; group
