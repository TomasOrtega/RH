import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero

open Module Topology

/- English proof (translation)
Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : Nat.Prime l).one_lt`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt C hl`. Set `φ : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℚ_[l])` to `{ toFun := fun c i => ((l : ℚ_[l]) ^ (-(k : ℤ))) * (c i : ℚ_[l]) map_add' := by`. Introduce `a b`. Use extensionality with `i`.

Simplify using `[mul_add]`. Use the proof step `map_smul' := by`. Introduce `r a`. Use extensionality with `i`. Simplify using `[Algebra.smul_def]`.

Use `ring }`. Use `Submodule.FG.of_le (Submodule.fg_range φ) ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce `v hv`. Establish `hbound : ∀ i, ‖(l : ℚ_[l]) ^ (k : ℤ) * v i‖ ≤ 1`.

Introduce `i`. Rewrite using `[norm_mul, Padic.norm_p_zpow]`. Establish `h1 : ‖v i‖ ≤ (l : ℝ) ^ k` using `(norm_le_pi_norm v i).trans ((hS v hv).trans hk.le)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[zpow_neg, ← zpow_natCast, inv_mul_cancel₀]`.

Conclude with `(zpow_pos (by linarith) _).ne'`. Use `⟨fun i => ⟨(l : ℚ_[l]) ^ (k : ℤ) * v i, hbound i⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Use `show ((l : ℚ_[l]) ^ (-(k : ℤ))) * ((l : ℚ_[l]) ^ (k : ℤ) * v i) = v i`. Establish `hne : (l : ℚ_[l]) ≠ 0` using `by exact_mod_cast (Fact.out : Nat.Prime l).ne_zero`.

Rewrite using `[← mul_assoc, ← zpow_add₀ hne]`. Simplify using the standard rewrite rules.
-/
private theorem span_padicInt_fg_of_bounded {l : ℕ} [Fact (Nat.Prime l)] {n : ℕ} (S : Set (Fin n → ℚ_[l])) (C : ℝ)
    (hS : ∀ v ∈ S, ‖v‖ ≤ C) : (Submodule.span ℤ_[l] S).FG := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : Nat.Prime l).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hl
  let φ : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℚ_[l]) :=
    { toFun := fun c i => ((l : ℚ_[l]) ^ (-(k : ℤ))) * (c i : ℚ_[l])
      map_add' := by
        intro a b
        ext i
        simp [mul_add]
      map_smul' := by
        intro r a
        ext i
        simp [Algebra.smul_def]
        ring }
  refine Submodule.FG.of_le (Submodule.fg_range φ) ?_
  rw [Submodule.span_le]
  intro v hv
  have hbound : ∀ i, ‖(l : ℚ_[l]) ^ (k : ℤ) * v i‖ ≤ 1 := by
    intro i
    rw [norm_mul, Padic.norm_p_zpow]
    have h1 : ‖v i‖ ≤ (l : ℝ) ^ k := (norm_le_pi_norm v i).trans ((hS v hv).trans hk.le)
    calc (l : ℝ) ^ (-(k : ℤ)) * ‖v i‖ ≤ (l : ℝ) ^ (-(k : ℤ)) * (l : ℝ) ^ k := by gcongr
      _ = 1 := by
        rw [zpow_neg, ← zpow_natCast, inv_mul_cancel₀]
        exact (zpow_pos (by linarith) _).ne'
  refine ⟨fun i => ⟨(l : ℚ_[l]) ^ (k : ℤ) * v i, hbound i⟩, ?_⟩
  ext i
  show ((l : ℚ_[l]) ^ (-(k : ℤ))) * ((l : ℚ_[l]) ^ (k : ℤ) * v i) = v i
  have hne : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
  rw [← mul_assoc, ← zpow_add₀ hne]
  simp

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr y]`. Rewrite using `[Submodule.coe_sum, map_sum, Finset.sum_apply']`. Repeatedly rewrite using `[Submodule.coe_smul_of_tower]`. Establish `h : ∀ j, (b.repr y j • (b j : Fin n → ℚ_[l])) = ((b.repr y j : ℚ_[l]) • b.extendOfIsLattice ℚ_[l] j)`. Introduce `j`.

Rewrite using `[Module.Basis.extendOfIsLattice_apply, algebra_compatible_smul ℚ_[l]]`. Both sides reduce to the same expression. Repeatedly rewrite using `[h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]`. Simplify using the standard rewrite rules.
-/
private theorem extendOfIsLattice_repr_eq_repr {l : ℕ} [Fact (Nat.Prime l)] {n m : ℕ}
    (L : Submodule ℤ_[l] (Fin n → ℚ_[l])) [Submodule.IsLattice ℚ_[l] L]
    (b : Module.Basis (Fin m) ℤ_[l] L) (y : L) (i : Fin m) :
    (b.extendOfIsLattice ℚ_[l]).repr (y : Fin n → ℚ_[l]) i = (b.repr y i : ℚ_[l]) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [Submodule.coe_sum, map_sum, Finset.sum_apply']
  simp_rw [Submodule.coe_smul_of_tower]
  have h : ∀ j, (b.repr y j • (b j : Fin n → ℚ_[l])) = ((b.repr y j : ℚ_[l]) • b.extendOfIsLattice ℚ_[l] j) := by
    intro j
    rw [Module.Basis.extendOfIsLattice_apply, algebra_compatible_smul ℚ_[l]]
    rfl
  simp_rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  simp

/- English proof (translation)
Introduce `l _ Γ _ _ _ V _ _ _ _ _ ρ hρ`. Use `set n := Module.finrank ℚ_[l] V`. Set `e0 : Module.Basis (Fin n) ℚ_[l] V` to `Module.finBasis ℚ_[l] V`. Set `E : V ≃ₗ[ℚ_[l]] (Fin n → ℚ_[l])` to `e0.equivFun`. Set `A : Γ → (Fin n → ℚ_[l]) →ₗ[ℚ_[l]] (Fin n → ℚ_[l])` to `fun g => E.toLinearMap ∘ₗ ρ g ∘ₗ E.symm.toLinearMap`.

Establish `hA1 : ∀ x, A 1 x = x`. Introduce `x`. Simplify using `[A]`. Establish `hAmul : ∀ g h x, A (g * h) x = A g (A h x)`. Introduce `g h x`.

Simplify using `[A, map_mul, Module.End.mul_apply]`. Establish `hEc : Continuous E` using `IsModuleTopology.continuous_of_linearMap E.toLinearMap`. Set `f : Γ → Fin n → (Fin n → ℚ_[l])` to `fun g j => A g (Pi.single j 1)`. Establish `hf : Continuous f`. Use `continuous_pi fun j => ?_` and prove the remaining obligations.

Establish `: (fun g => f g j) = fun g => E (ρ g (E.symm (Pi.single j 1)))` using `rfl`. Rewrite using `[this]`. Conclude with `hEc.comp (hρ _)`. Take `⟨C, hC⟩` from `(isCompact_range hf).isBounded.exists_norm_le`. Set `S : Set (Fin n → ℚ_[l])` to `Set.range fun p : Γ × Fin n => A p.1 (Pi.single p.2 1)`.

Set `L : Submodule ℤ_[l] (Fin n → ℚ_[l])` to `Submodule.span ℤ_[l] S`. Establish `hfg : L.FG`. Use `span_padicInt_fg_of_bounded S C ?_` and prove the remaining obligations. Introduce and unpack `v ⟨⟨g, j⟩, rfl⟩`. Conclude with `(norm_le_pi_norm (f g) j).trans (hC _ ⟨g, rfl⟩)`.

Establish `hsingle : ∀ j : Fin n, (Pi.single j 1 : Fin n → ℚ_[l]) ∈ L`. Introduce `j`. Establish `: (Pi.single j 1 : Fin n → ℚ_[l]) = A 1 (Pi.single j 1)` using `(hA1 _).symm`. Rewrite using `[this]`. Conclude with `Submodule.subset_span ⟨(1, j), rfl⟩`.

Establish `hspan : Submodule.span ℚ_[l] (L : Set (Fin n → ℚ_[l])) = ⊤`. Rewrite using `[eq_top_iff, ← (Pi.basisFun ℚ_[l] (Fin n)).span_eq]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `v ⟨j, rfl⟩`. Simplify using `using hsingle j`.

Use `haveI hlat : Submodule.IsLattice ℚ_[l] L := ⟨hfg, hspan⟩`. Establish `hstab : ∀ g, ∀ x ∈ L, (A g).restrictScalars ℤ_[l] x ∈ L`. Introduce `g`. Establish `: L ≤ L.comap ((A g).restrictScalars ℤ_[l])`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `v ⟨⟨h, j⟩, rfl⟩`. Use `show A g (A h (Pi.single j 1)) ∈ L`. Rewrite using `[← hAmul]`. Conclude with `Submodule.subset_span ⟨(g * h, j), rfl⟩`. Conclude with `fun x hx => this hx`.

Use `haveI : Module.Free ℤ_[l] L := Submodule.IsLattice.free ℚ_[l] L`. Use `haveI : Module.Finite ℤ_[l] L := Submodule.IsLattice.finite ℚ_[l] L`. Set `b0` to `Module.Free.chooseBasis ℤ_[l] L`. Set `b : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ_[l] L))) ℤ_[l] L` to `b0.reindex (Fintype.equivFin _)`. Set `e'` to `b.extendOfIsLattice ℚ_[l]`.

Set `e` to `e'.map E.symm`. Set `R : Γ →* Module.End ℤ_[l] L` to `{ toFun := fun g => ((A g).restrictScalars ℤ_[l]).restrict (hstab g) map_one' := by`. Use extensionality with `x`. Simplify using `[LinearMap.restrict_apply, hA1]`. Use the proof step `map_mul' := by`.

Introduce `g h`. Use extensionality with `x`. Simplify using `[LinearMap.restrict_apply, hAmul, Module.End.mul_apply] }`. Set `M : Γ →* Matrix _ _ ℤ_[l]` to `(LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp R`. Establish `key : ∀ (g : Γ) (i j), ((M g i j : ℤ_[l]) : ℚ_[l]) = (e.repr ((ρ g) (e j))) i`.

Introduce `g i j`. Establish `h1 : M g i j = b.repr (R g (b j)) i`. Simplify using `[M, LinearMap.toMatrixAlgEquiv_apply]`. Establish `h2 : e.repr ((ρ g) (e j)) i = e'.repr (A g (b j)) i`. Simplify using `[e, e', A, Module.Basis.map_repr, Module.Basis.map_apply]`.

Establish `h3 : (A g (b j : Fin n → ℚ_[l])) = ((R g (b j) : L) : Fin n → ℚ_[l])` using `rfl`. Rewrite using `[h1, h2, h3, extendOfIsLattice_repr_eq_repr]`. Use `⟨_, e, M, ?_, key⟩` and prove the remaining obligations. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Use `(isometry_subtype_coe.isEmbedding.continuous_iff).2 ?_` and prove the remaining obligations.

Establish `: (fun g => ((M g i j : ℤ_[l]) : ℚ_[l])) = fun g => e.coord i (ρ g (e j))`. Use function extensionality and compare the values at `g`. Rewrite using `[key]`. Both sides reduce to the same expression. Use `show Continuous (fun g => ((M g i j : ℤ_[l]) : ℚ_[l]))`.

Rewrite using `[this]`. Conclude with `(IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hρ _)`.
-/
theorem UpperTheory.galois_representation_integral_lattice :
    UpperTheory.V.Af.Wd.IntBasis := by
  intro l _ Γ _ _ _ V _ _ _ _ _ ρ hρ
  set n := Module.finrank ℚ_[l] V
  let e0 : Module.Basis (Fin n) ℚ_[l] V := Module.finBasis ℚ_[l] V
  let E : V ≃ₗ[ℚ_[l]] (Fin n → ℚ_[l]) := e0.equivFun
  let A : Γ → (Fin n → ℚ_[l]) →ₗ[ℚ_[l]] (Fin n → ℚ_[l]) := fun g =>
    E.toLinearMap ∘ₗ ρ g ∘ₗ E.symm.toLinearMap
  have hA1 : ∀ x, A 1 x = x := by
    intro x
    simp [A]
  have hAmul : ∀ g h x, A (g * h) x = A g (A h x) := by
    intro g h x
    simp [A, map_mul, Module.End.mul_apply]
  have hEc : Continuous E := IsModuleTopology.continuous_of_linearMap E.toLinearMap
  let f : Γ → Fin n → (Fin n → ℚ_[l]) := fun g j => A g (Pi.single j 1)
  have hf : Continuous f := by
    refine continuous_pi fun j => ?_
    have : (fun g => f g j) = fun g => E (ρ g (E.symm (Pi.single j 1))) := rfl
    rw [this]
    exact hEc.comp (hρ _)
  obtain ⟨C, hC⟩ := (isCompact_range hf).isBounded.exists_norm_le
  let S : Set (Fin n → ℚ_[l]) := Set.range fun p : Γ × Fin n => A p.1 (Pi.single p.2 1)
  let L : Submodule ℤ_[l] (Fin n → ℚ_[l]) := Submodule.span ℤ_[l] S
  have hfg : L.FG := by
    refine span_padicInt_fg_of_bounded S C ?_
    rintro v ⟨⟨g, j⟩, rfl⟩
    exact (norm_le_pi_norm (f g) j).trans (hC _ ⟨g, rfl⟩)
  have hsingle : ∀ j : Fin n, (Pi.single j 1 : Fin n → ℚ_[l]) ∈ L := by
    intro j
    have : (Pi.single j 1 : Fin n → ℚ_[l]) = A 1 (Pi.single j 1) := (hA1 _).symm
    rw [this]
    exact Submodule.subset_span ⟨(1, j), rfl⟩
  have hspan : Submodule.span ℚ_[l] (L : Set (Fin n → ℚ_[l])) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ_[l] (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro v ⟨j, rfl⟩
    simpa using hsingle j
  haveI hlat : Submodule.IsLattice ℚ_[l] L := ⟨hfg, hspan⟩
  have hstab : ∀ g, ∀ x ∈ L, (A g).restrictScalars ℤ_[l] x ∈ L := by
    intro g
    have : L ≤ L.comap ((A g).restrictScalars ℤ_[l]) := by
      rw [Submodule.span_le]
      rintro v ⟨⟨h, j⟩, rfl⟩
      show A g (A h (Pi.single j 1)) ∈ L
      rw [← hAmul]
      exact Submodule.subset_span ⟨(g * h, j), rfl⟩
    exact fun x hx => this hx
  haveI : Module.Free ℤ_[l] L := Submodule.IsLattice.free ℚ_[l] L
  haveI : Module.Finite ℤ_[l] L := Submodule.IsLattice.finite ℚ_[l] L
  let b0 := Module.Free.chooseBasis ℤ_[l] L
  let b : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ_[l] L))) ℤ_[l] L :=
    b0.reindex (Fintype.equivFin _)
  let e' := b.extendOfIsLattice ℚ_[l]
  let e := e'.map E.symm
  let R : Γ →* Module.End ℤ_[l] L :=
    { toFun := fun g => ((A g).restrictScalars ℤ_[l]).restrict (hstab g)
      map_one' := by
        ext x
        simp [LinearMap.restrict_apply, hA1]
      map_mul' := by
        intro g h
        ext x
        simp [LinearMap.restrict_apply, hAmul, Module.End.mul_apply] }
  let M : Γ →* Matrix _ _ ℤ_[l] := (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp R
  have key : ∀ (g : Γ) (i j), ((M g i j : ℤ_[l]) : ℚ_[l]) = (e.repr ((ρ g) (e j))) i := by
    intro g i j
    have h1 : M g i j = b.repr (R g (b j)) i := by
      simp [M, LinearMap.toMatrixAlgEquiv_apply]
    have h2 : e.repr ((ρ g) (e j)) i = e'.repr (A g (b j)) i := by
      simp [e, e', A, Module.Basis.map_repr, Module.Basis.map_apply]
    have h3 : (A g (b j : Fin n → ℚ_[l])) = ((R g (b j) : L) : Fin n → ℚ_[l]) := rfl
    rw [h1, h2, h3, extendOfIsLattice_repr_eq_repr]
  refine ⟨_, e, M, ?_, key⟩
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (isometry_subtype_coe.isEmbedding.continuous_iff).2 ?_
  have : (fun g => ((M g i j : ℤ_[l]) : ℚ_[l])) = fun g => e.coord i (ρ g (e j)) := by
    funext g
    rw [key]
    rfl
  show Continuous (fun g => ((M g i j : ℤ_[l]) : ℚ_[l]))
  rw [this]
  exact (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hρ _)
