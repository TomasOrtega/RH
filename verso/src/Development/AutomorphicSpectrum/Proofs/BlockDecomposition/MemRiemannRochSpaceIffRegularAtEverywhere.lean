import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapAbsOf

noncomputable section

open Matrix Classical PositivityTheory.Rg.Rs

namespace GlobalTheory.CompanionTheory.GLFirstBasisOrbit

variable {k : Type} [Field k] {n : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_gmap {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) (x : Fin N → k) :
    x ∈ gmap g M ↔ (g⁻¹).val *ᵥ x ∈ M := by
  unfold gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
    exact hz
  · intro h
    refine ⟨_, h, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem smul_mem_gmap {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) (x : Fin N → k) :
    g.val *ᵥ x ∈ gmap g M ↔ x ∈ M := by
  rw [mem_gmap, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem gmap_mul {N : ℕ} (g h : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    gmap (g * h) M = gmap g (gmap h M) := by
  ext x
  rw [mem_gmap, mem_gmap, mem_gmap, Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem gmap_one {N : ℕ} (M : Submodule k (Fin N → k)) : gmap (1 : GL (Fin N) k) M = M := by
  ext x
  rw [mem_gmap, inv_one, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem gmap_top {N : ℕ} (g : GL (Fin N) k) : gmap g ⊤ = ⊤ := by
  ext x
  simp [mem_gmap]

def gmapEquiv {N : ℕ} (g : GL (Fin N) k) : Submodule k (Fin N → k) ≃ Submodule k (Fin N → k) where
  toFun := gmap g
  invFun := gmap g⁻¹
  left_inv M := by rw [← gmap_mul, inv_mul_cancel, gmap_one]
  right_inv M := by rw [← gmap_mul, mul_inv_cancel, gmap_one]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem finrank_gmap {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    Module.finrank k (gmap g M) = Module.finrank k M := by
  have hinj : Function.Injective (Matrix.toLin' g.val) := by
    intro x y h
    have := congrArg (fun z => (g⁻¹).val *ᵥ z) h
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using this
  exact (Submodule.equivMapOfInjective _ hinj M).finrank_eq.symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem first_basis_ne_zero : e0 k n ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [e0] at this

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem star_e0_dotProduct (x : Fin (n + 1) → k) : e0 k n ⬝ᵥ x = x 0 := by
  simp [e0]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_riemannRochSpace_iff_regularAt_everywhere (x : Fin (n + 1) → k) : x ∈ H0 k n ↔ x 0 = 0 := by
  simp [H0]

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem exists_GL_first_basis_eq (x : Fin (n + 1) → k) (hx : x ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, g.val *ᵥ e0 k n = x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) k := (1 : Matrix _ _ k).updateCol i x
  have hA : A.det = x i := by
    have := Matrix.cramer_apply (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) x i
    rw [← show (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol i x = A from rfl, ← this]
    simp
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) k := A.submatrix id (Equiv.swap 0 i)
  have hG : G.det ≠ 0 := by
    have := Matrix.det_permute' (Equiv.swap 0 i) A
    rw [show G = A.submatrix id (Equiv.swap 0 i) from rfl, this, hA]
    refine mul_ne_zero ?_ hi
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) i)) with h | h <;> rw [h] <;> simp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero G hG, ?_⟩
  ext a
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, e0, G, A]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_gl_cov (a : Fin (n + 1) → k) (ha : a ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, ∀ x, a ⬝ᵥ (g.val *ᵥ x) = x 0 := by
  obtain ⟨h, hh⟩ := exists_GL_first_basis_eq a ha
  have hd : (h.val)ᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnits_det_units h).ne_zero
  let T : GL (Fin (n + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (h.val)ᵀ hd
  refine ⟨T⁻¹, fun x => ?_⟩
  have hT : T.val = (h.val)ᵀ := rfl
  have h1 : a = e0 k n ᵥ* T.val := by rw [hT, Matrix.vecMul_transpose, hh]
  rw [Matrix.dotProduct_mulVec, h1, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.vecMul_one, star_e0_dotProduct]

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities.
-/
theorem mem_GL_image_hyperplane_iff (g : GL (Fin (n + 1)) k) (a : Fin (n + 1) → k)
    (h : ∀ x, a ⬝ᵥ (g.val *ᵥ x) = x 0) (z : Fin (n + 1) → k) :
    z ∈ gmap g (H0 k n) ↔ a ⬝ᵥ z = 0 := by
  rw [mem_gmap, mem_riemannRochSpace_iff_regularAt_everywhere, ← h ((g⁻¹).val *ᵥ z), Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_scalar_stabilizer_line (g : GL (Fin (n + 1)) k)
    (h : gmap g (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n}) :
    ∃ s : k, s ≠ 0 ∧ g.val *ᵥ e0 k n = s • e0 k n := by
  have h1 : g.val *ᵥ e0 k n ∈ Submodule.span k {e0 k n} := by
    rw [← h, smul_mem_gmap]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp h1
  refine ⟨s, ?_, hs.symm⟩
  rintro rfl
  have h2 : g.val *ᵥ e0 k n = 0 := by rw [← hs, zero_smul]
  have h3 := congrArg (fun z => (g⁻¹).val *ᵥ z) h2
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h3
  exact first_basis_ne_zero h3

section Lat

variable {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]

def stabV (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) : Submodule ℂ V where
  carrier := {y | ∀ γ, gmap (red γ) (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n} → ρ γ y = y}
  add_mem' := by
    intro a b ha hb γ h
    rw [map_add, ha γ h, hb γ h]
  zero_mem' := by
    intro γ _
    simp
  smul_mem' := by
    intro c a ha γ h
    rw [map_smul, ha γ h]

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_stabV (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) (y : V) :
    y ∈ stabV red ρ ↔
      ∀ γ, gmap (red γ) (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n} → ρ γ y = y := Iff.rfl

variable [Fintype k]

def zx (v : Submodule k (Fin (n + 1) → k) → V) (x : Fin (n + 1) → k) (j : ℕ) : V :=
  ∑ M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) => x ∈ M ∧ Module.finrank k M + j = n + 1), v M

def IsCov (red : Γ →* GL (Fin (n + 1)) k) (gam : (Fin (n + 1) → k) → Γ) : Prop :=
  ∀ a, a ≠ 0 → ∀ x, a ⬝ᵥ ((red (gam a)).val *ᵥ x) = x 0

def uop (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V) (gam : (Fin (n + 1) → k) → Γ) : Module.End ℂ V :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1), ρ (gam a) * t

end Lat

end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
end
