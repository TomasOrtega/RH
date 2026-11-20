import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CtrlEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul

open IsLocalRing Matrix UpperTheory.V.Hi

/- English proof (translation)
Rewrite using `[Matrix.mulVec, dotProduct]`. Use `Submodule.sum_mem L fun j _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `hM k j`. Rewrite using `[← hr, ← Algebra.smul_def]`. Conclude with `L.smul_mem r (hv j)`.
-/
private theorem detd_mulVec {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {n : ℕ} (L : Submodule O Ω)
    (M : Matrix (Fin n) (Fin n) Ω) (hM : ∀ i j, M i j ∈ (algebraMap O Ω).range) (v : Fin n → Ω)
    (hv : ∀ k, v k ∈ L) (k : Fin n) : (M *ᵥ v) k ∈ L := by
  rw [Matrix.mulVec, dotProduct]
  refine Submodule.sum_mem L fun j _ => ?_
  obtain ⟨r, hr⟩ := hM k j
  rw [← hr, ← Algebra.smul_def]
  exact L.smul_mem r (hv j)

/- English proof (translation)
Introduce `Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c hc N x hx F hF Λ hΛ`. Simplify using `only [Frame.ClO, Frame.Cl, Submodule.mem_inf] at hF`. Take `⟨⟨hA, hU⟩, hE⟩` from `hF`. Take `⟨hN, hNm, hT⟩` from `hE`. Establish `hA' : ∀ i γ g, F i (X.glob γ * g) = ((W.ξ (X.glob γ).2 : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ F i g` using `fun i γ g => (Submodule.mem_pi.mp hA i (Set.mem_univ i)) γ g`.

Establish `hU' : ∀ u ∈ U, ∀ i g k, (((((GeneralLinearGroup.map (algebraMap O Ω)).comp τ) u : GL _ Ω) : Matrix (Fin m) (Fin m) Ω) *ᵥ (fun j => F j (g * ((u : Ga), 1)) k)) i = F i g k` using `fun u hu i g k => congrFun (congrFun (congrFun (hU u hu) i) g) k`. Establish `key : ∀ (h : Ga × Gp) (b : Gp) (s : O), (∀ i j, ((W.ξ b⁻¹ : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) i j ∈ (algebraMap O Ω).range) → (∀ i, F i (h * (1, b)) = algebraMap O Ω s • F i h) → (∀ i k, X.unt m W F i h k ∈ Λ) → ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ`. Introduce `h b s hMb hFb hG i k`. Establish `e : X.unt m W F i (h * (1, b)) = ((W.ξ b⁻¹ : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ (algebraMap O Ω s • X.unt m W F i h)`. Simplify using `only [Frame.unt_apply, hFb i, Prod.snd_mul, map_mul, map_inv, _root_.mul_inv_rev, GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul]`.

Rewrite using `[e]`. Use `detd_mulVec Λ _ hMb _ (fun j => ?_) k` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]`. Conclude with `Λ.smul_mem s (hG i j)`. Establish `stepN : ∀ h, ∀ b ∈ X.I.N, (∀ i k, X.unt m W F i h k ∈ Λ) → ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ`.

Introduce `h b hb hG`. Use `key h b 1 (W.int_N _ (X.I.N.inv_mem hb)) (fun i => ?_) hG` and prove the remaining obligations. Rewrite using `[map_one, one_smul]`. Conclude with `congrFun (congrFun (hN b hb) i) h`. Establish `stepM : ∀ h, ∀ b ∈ X.I.Nm c, (∀ i k, X.unt m W F i h k ∈ Λ) → ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ`.

Introduce `h b hb hG`. Use `key h b 1 (W.int_Nm _ (X.I.Nm_anti hc ((X.I.Nm c).inv_mem hb))) (fun i => ?_) hG` and prove the remaining obligations. Rewrite using `[map_one, one_smul]`. Conclude with `congrFun (congrFun (hNm b hb) i) h`. Establish `stepT : ∀ h, ∀ b ∈ X.I.T, (∀ i k, X.unt m W F i h k ∈ Λ) → ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ`.

Introduce `h b hb hG`. Use `key h b ((φ ⟨b, hb⟩)⁻¹ : Oˣ) (W.integral_torusCharacter _ (X.I.T.inv_mem hb)) (fun i => ?_) hG` and prove the remaining obligations. Use `congrFun (congrFun (hT ⟨b, hb⟩) i) h` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `stepU : ∀ h, ∀ u ∈ U, (∀ i k, X.unt m W F i h k ∈ Λ) → ∀ i k, X.unt m W F i (h * ((u : Ga), 1)) k ∈ Λ`. Introduce `h u hu hG i k`. Establish `hv : ∀ i, F i (h * ((u : Ga), 1)) = fun l => ∑ j, algebraMap O Ω (((τ u⁻¹ : GL _ O) : Matrix (Fin m) (Fin m) O) i j) * F j h l`. Introduce `i`. Use function extensionality and compare the values at `l`.

Use `hU' u⁻¹ (U.inv_mem hu) i (h * ((u : Ga), 1)) l` as an intermediate fact. Rewrite using `[← this]`. Establish `hh : h * ((u : Ga), 1) * (((u⁻¹ : X.Ub) : Ga), (1 : Gp)) = h`. Apply the tactic sequence `ext <;> simp`. Simplify using `only [Matrix.mulVec, dotProduct, hh]`.

Both sides reduce to the same expression. Establish `e : X.unt m W F i (h * ((u : Ga), 1)) k = ((Matrix.of fun a b => algebraMap O Ω (((τ u⁻¹ : GL _ O) : Matrix (Fin m) (Fin m) O) a b)) *ᵥ fun j => X.unt m W F j h k) i`. Simplify using `only [Frame.unt_apply, Prod.snd_mul, mul_one, hv, Matrix.mulVec, dotProduct, Finset.mul_sum, Matrix.of_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `detd_mulVec Λ _ (fun a b => ⟨_, rfl⟩) _ (fun j => hG j k) i`. Establish `stepG : ∀ γ h, (∀ i k, X.unt m W F i h k ∈ Λ) → ∀ i k, X.unt m W F i (X.glob γ * h) k ∈ Λ`. Introduce `γ h hG i k`.

Establish `e : X.unt m W F i (X.glob γ * h) = X.unt m W F i h`. Rewrite using `[Frame.unt_apply, Frame.unt_apply, hA' i γ h]`. Simplify using `[Prod.snd_mul, Matrix.mulVec_mulVec, _root_.mul_inv_rev, GeneralLinearGroup.coe_mul, mul_assoc]`. Rewrite using `[e]`. Conclude with `hG i k`.

Use `show ∀ i g k, X.unt m W F i g k ∈ Λ`. Introduce `i g k`. Take `⟨γ, n, u, hu, b, hb, rfl⟩` from `hx g`. Take `⟨y1, hy1, t, ht, y2, hy2, rfl⟩` from `((iwMem Gp X.I c b).1).1 hb`. Establish `eq : X.glob γ * x n * ((u : Ga), y1 * t * y2) = X.glob γ * (x n * ((u : Ga), 1) * (1, y1) * (1, t) * (1, y2))`.

Apply the tactic sequence `ext <;> simp [mul_assoc]`. Rewrite using `[eq]`. Conclude with `stepG γ _ (stepM _ y2 hy2 (stepT _ t ht (stepN _ y1 hy1 (stepU _ u hu (fun i k => hΛ n i k))))) i k`.
-/
theorem UpperTheory.mem_lattice_of_values_at_double_coset_reps :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ), W.c0 ≤ c → ∀ (N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → ∀ F ∈ X.ClO W τ U c φ, ∀ Λ : Submodule O Ω, (∀ n i k, X.unt m W F i (x n) k ∈ Λ) → F ∈ X.Lat m W Λ := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c hc N x hx F hF Λ hΛ
  simp only [Frame.ClO, Frame.Cl, Submodule.mem_inf] at hF
  obtain ⟨⟨hA, hU⟩, hE⟩ := hF
  obtain ⟨hN, hNm, hT⟩ := hE
  have hA' : ∀ i γ g, F i (X.glob γ * g) =
      ((W.ξ (X.glob γ).2 : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ F i g :=
    fun i γ g => (Submodule.mem_pi.mp hA i (Set.mem_univ i)) γ g
  have hU' : ∀ u ∈ U, ∀ i g k,
      (((((GeneralLinearGroup.map (algebraMap O Ω)).comp τ) u : GL _ Ω) : Matrix (Fin m) (Fin m) Ω) *ᵥ
        (fun j => F j (g * ((u : Ga), 1)) k)) i = F i g k :=
    fun u hu i g k => congrFun (congrFun (congrFun (hU u hu) i) g) k
  have key : ∀ (h : Ga × Gp) (b : Gp) (s : O),
      (∀ i j, ((W.ξ b⁻¹ : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) i j ∈
        (algebraMap O Ω).range) →
      (∀ i, F i (h * (1, b)) = algebraMap O Ω s • F i h) →
      (∀ i k, X.unt m W F i h k ∈ Λ) → ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b s hMb hFb hG i k
    have e : X.unt m W F i (h * (1, b)) =
        ((W.ξ b⁻¹ : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ
          (algebraMap O Ω s • X.unt m W F i h) := by
      simp only [Frame.unt_apply, hFb i, Prod.snd_mul, map_mul, map_inv, _root_.mul_inv_rev,
        GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul]
    rw [e]
    refine detd_mulVec Λ _ hMb _ (fun j => ?_) k
    rw [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]
    exact Λ.smul_mem s (hG i j)
  have stepN : ∀ h, ∀ b ∈ X.I.N, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b hb hG
    refine key h b 1 (W.int_N _ (X.I.N.inv_mem hb)) (fun i => ?_) hG
    rw [map_one, one_smul]
    exact congrFun (congrFun (hN b hb) i) h
  have stepM : ∀ h, ∀ b ∈ X.I.Nm c, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b hb hG
    refine key h b 1 (W.int_Nm _ (X.I.Nm_anti hc ((X.I.Nm c).inv_mem hb))) (fun i => ?_) hG
    rw [map_one, one_smul]
    exact congrFun (congrFun (hNm b hb) i) h
  have stepT : ∀ h, ∀ b ∈ X.I.T, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b hb hG
    refine key h b ((φ ⟨b, hb⟩)⁻¹ : Oˣ) (W.integral_torusCharacter _ (X.I.T.inv_mem hb)) (fun i => ?_) hG
    have := congrFun (congrFun (hT ⟨b, hb⟩) i) h
    refine this.trans ?_
    simp
  have stepU : ∀ h, ∀ u ∈ U, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * ((u : Ga), 1)) k ∈ Λ := by
    intro h u hu hG i k
    have hv : ∀ i, F i (h * ((u : Ga), 1)) =
        fun l => ∑ j, algebraMap O Ω (((τ u⁻¹ : GL _ O) : Matrix (Fin m) (Fin m) O) i j) * F j h l := by
      intro i
      funext l
      have := hU' u⁻¹ (U.inv_mem hu) i (h * ((u : Ga), 1)) l
      rw [← this]
      have hh : h * ((u : Ga), 1) * (((u⁻¹ : X.Ub) : Ga), (1 : Gp)) = h := by
        ext <;> simp
      simp only [Matrix.mulVec, dotProduct, hh]
      rfl
    have e : X.unt m W F i (h * ((u : Ga), 1)) k =
        ((Matrix.of fun a b => algebraMap O Ω (((τ u⁻¹ : GL _ O) : Matrix (Fin m) (Fin m) O) a b)) *ᵥ
          fun j => X.unt m W F j h k) i := by
      simp only [Frame.unt_apply, Prod.snd_mul, mul_one, hv, Matrix.mulVec, dotProduct, Finset.mul_sum,
        Matrix.of_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact detd_mulVec Λ _ (fun a b => ⟨_, rfl⟩) _ (fun j => hG j k) i
  have stepG : ∀ γ h, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (X.glob γ * h) k ∈ Λ := by
    intro γ h hG i k
    have e : X.unt m W F i (X.glob γ * h) = X.unt m W F i h := by
      rw [Frame.unt_apply, Frame.unt_apply, hA' i γ h]
      simp [Prod.snd_mul, Matrix.mulVec_mulVec, _root_.mul_inv_rev, GeneralLinearGroup.coe_mul, mul_assoc]
    rw [e]
    exact hG i k
  show ∀ i g k, X.unt m W F i g k ∈ Λ
  intro i g k
  obtain ⟨γ, n, u, hu, b, hb, rfl⟩ := hx g
  obtain ⟨y1, hy1, t, ht, y2, hy2, rfl⟩ := ((iwMem Gp X.I c b).1).1 hb
  have eq : X.glob γ * x n * ((u : Ga), y1 * t * y2) =
      X.glob γ * (x n * ((u : Ga), 1) * (1, y1) * (1, t) * (1, y2)) := by
    ext <;> simp [mul_assoc]
  rw [eq]
  exact stepG γ _ (stepM _ y2 hy2 (stepT _ t ht (stepN _ y1 hy1
    (stepU _ u hu (fun i k => hΛ n i k))))) i k
