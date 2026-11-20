import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

open Matrix UpperTheory.V.Af

/- English proof (translation)
Take `⟨x, hx⟩` from `Module.End.exists_eigenvalue (Matrix.toLin' N)`. Establish `htop : Module.End.eigenspace (Matrix.toLin' N) x = ⊤`. Use `(h.2.2 _ le_top fun g v hv => ?_).resolve_left hx` and prove the remaining obligations. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`. Rewrite using `[Matrix.mulVec_mulVec, hN g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]`.

Use `⟨x, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩` and prove the remaining obligations. Establish `: v ∈ Module.End.eigenspace (Matrix.toLin' N) x` using `by rw [htop]; trivial`. Rewrite using `[Module.End.mem_eigenspace_iff.1 this]`. Simplify using the standard rewrite rules.
-/
private theorem schur2 {G κ : Type} [Group G] [Field κ] [IsAlgClosed κ] (ρ : G →* GL (Fin 2) κ)
    (h : IsIrr ρ) (N : Matrix (Fin 2) (Fin 2) κ)
    (hN : ∀ g, N * (ρ g : Matrix (Fin 2) (Fin 2) κ) = (ρ g : Matrix (Fin 2) (Fin 2) κ) * N) : ∃ x : κ, N = x • 1 := by
  obtain ⟨x, hx⟩ := Module.End.exists_eigenvalue (Matrix.toLin' N)
  have htop : Module.End.eigenspace (Matrix.toLin' N) x = ⊤ := by
    refine (h.2.2 _ le_top fun g v hv => ?_).resolve_left hx
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hN g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  refine ⟨x, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
  have : v ∈ Module.End.eigenspace (Matrix.toLin' N) x := by rw [htop]; trivial
  rw [Module.End.mem_eigenspace_iff.1 this]
  simp

/- English proof (translation)
Introduce `k Γ _ _ _ ρ ρ' H' M hirr hM s hs hdet`. Use `set N : GL (Fin 2) k := (ρ s)⁻¹ * (M⁻¹ * ρ' s * M) with hN`. Establish `hcomm : ∀ h ∈ H', N * ρ h = ρ h * N`. Introduce `h hh`. Establish `e1` using `hM h hh`.

Establish `e2` using `hM _ (hs h hh)`. Simplify using `only [map_mul, map_inv, e1] at e2`. Establish `e3 : ρ' s * (M * ρ h * M⁻¹) = M * (ρ s * ρ h * (ρ s)⁻¹) * M⁻¹ * ρ' s`. Rewrite using `[← e2]`. Use `group`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨x, hx⟩` from `schur2 _ hirr (N : Matrix (Fin 2) (Fin 2) k) (fun g => by`. Use `congrArg Units.val (hcomm g g.2)` as an intermediate fact. Simplify using `using this)`. Establish `hd : Matrix.GeneralLinearGroup.det N = 1`.

Rewrite using `[hN]`. Simplify using `only [map_mul, map_inv, hdet]`. Rewrite using `[mul_right_comm, inv_mul_cancel, one_mul, inv_mul_cancel]`. Establish `hx2 : x * x = 1`. Establish `h1 : (N : Matrix (Fin 2) (Fin 2) k).det = 1` using `congrArg Units.val hd`.

Rewrite `h1` using `[hx]`. Simplify `h1` using `[pow_two]`. Establish `hc : ∀ A : GL (Fin 2) k, N * A = A * N` using `fun A => Units.ext (by simp [hx])`. Establish `hNN : N * N = 1` using `Units.ext (by simp [hx, smul_smul, hx2])`. Establish `e : ρ' s = M * (ρ s * N) * M⁻¹` using `by rw [hN]; group`.

Use `clear_value N`. Rewrite using `[map_mul, map_mul, e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.mix_sign_twist :
    UpperTheory.V.Sd.S2.SignTw := by
  intro k Γ _ _ _ ρ ρ' H' M hirr hM s hs hdet
  set N : GL (Fin 2) k := (ρ s)⁻¹ * (M⁻¹ * ρ' s * M) with hN
  have hcomm : ∀ h ∈ H', N * ρ h = ρ h * N := by
    intro h hh
    have e1 := hM h hh
    have e2 := hM _ (hs h hh)
    simp only [map_mul, map_inv, e1] at e2
    have e3 : ρ' s * (M * ρ h * M⁻¹) = M * (ρ s * ρ h * (ρ s)⁻¹) * M⁻¹ * ρ' s := by
      rw [← e2]; group
    calc N * ρ h = (ρ s)⁻¹ * M⁻¹ * (ρ' s * (M * ρ h * M⁻¹)) * M := by rw [hN]; group
      _ = ρ h * N := by rw [e3, hN]; group
  obtain ⟨x, hx⟩ := schur2 _ hirr (N : Matrix (Fin 2) (Fin 2) k) (fun g => by
    have := congrArg Units.val (hcomm g g.2)
    simpa using this)
  have hd : Matrix.GeneralLinearGroup.det N = 1 := by
    rw [hN]
    simp only [map_mul, map_inv, hdet]
    rw [mul_right_comm, inv_mul_cancel, one_mul, inv_mul_cancel]
  have hx2 : x * x = 1 := by
    have h1 : (N : Matrix (Fin 2) (Fin 2) k).det = 1 := congrArg Units.val hd
    rw [hx] at h1
    simpa [pow_two] using h1
  have hc : ∀ A : GL (Fin 2) k, N * A = A * N := fun A => Units.ext (by simp [hx])
  have hNN : N * N = 1 := Units.ext (by simp [hx, smul_smul, hx2])
  have e : ρ' s = M * (ρ s * N) * M⁻¹ := by rw [hN]; group
  clear_value N
  rw [map_mul, map_mul, e]
  calc M * (ρ s * N) * M⁻¹ * (M * (ρ s * N) * M⁻¹) = M * (ρ s * (N * ρ s) * N) * M⁻¹ := by group
    _ = M * (ρ s * ρ s * (N * N)) * M⁻¹ := by rw [hc]; simp only [mul_assoc]
    _ = _ := by rw [hNN, mul_one]
