import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

section aux

variable {G K V : Type} [Group G] [Field K] [CharZero K] [AddCommGroup V] [Module K V]

omit [CharZero K] in
/- English proof (translation)
Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
private theorem pn_rmul (R : Representation K G V) (g h : G) (X : V) : R (g * h) X = R g (R h X) := by
  rw [map_mul]; rfl

/- English proof (translation)
Establish `h1 : z 1 = 0`. Use `hz 1 1` as an intermediate fact. Simplify using `using this`. Establish `h2 : R c (z c) = -z c`. Use `hz c c` as an intermediate fact.

Rewrite `this` using `[hc, h1]`. Conclude with `eq_neg_of_add_eq_zero_right this.symm`. Use `⟨-((2 : K)⁻¹ • z c), ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, map_smul, h2]`. Establish `h3 : z c = (2 : K)⁻¹ • z c + (2 : K)⁻¹ • z c`.

Rewrite using `[← add_smul]`. Evaluate the numerical expressions. Rewrite using `[smul_neg, neg_neg, sub_neg_eq_add, ← h3, sub_self]`.
-/
private theorem pn_norm (R : Representation K G V) (c : G) (hc : c * c = 1) (z : G → V)
    (hz : ∀ g h, z (g * h) = z g + R g (z h)) : ∃ X₀ : V, z c - (R c X₀ - X₀) = 0 := by
  have h1 : z 1 = 0 := by
    have := hz 1 1
    simpa using this
  have h2 : R c (z c) = -z c := by
    have := hz c c
    rw [hc, h1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  refine ⟨-((2 : K)⁻¹ • z c), ?_⟩
  rw [map_neg, map_smul, h2]
  have h3 : z c = (2 : K)⁻¹ • z c + (2 : K)⁻¹ • z c := by
    rw [← add_smul]; norm_num
  rw [smul_neg, neg_neg, sub_neg_eq_add, ← h3, sub_self]

omit [CharZero K] in
/- English proof (translation)
Rewrite using `[inv_eq_of_mul_eq_one_right hc, hz, hz, h0, map_zero, zero_add, add_zero]`.
-/
private theorem pn_conj (R : Representation K G V) (c : G) (hc : c * c = 1) (z : G → V)
    (hz : ∀ g h, z (g * h) = z g + R g (z h)) (h0 : z c = 0) (g : G) : z (c * g * c⁻¹) = R c (z g) := by
  rw [inv_eq_of_mul_eq_one_right hc, hz, hz, h0, map_zero, zero_add, add_zero]

/- English proof (translation)
Establish `hi : c⁻¹ = c` using `inv_eq_of_mul_eq_one_right hc`. Establish `hcc : ∀ X, R c (R c X) = X` using `fun X => by rw [← pn_rmul, hc, map_one]; rfl`. Establish `hY' : ∀ g, η g = 1 → z g = R g (R c Y) - R c Y` using `fun g hg => by`. Establish `e : g = c * (c * g * c) * c⁻¹`. Rewrite using `[hi, ← mul_assoc, ← mul_assoc, hc, one_mul, mul_assoc, hc, mul_one]`.

Establish `h1 : η (c * g * c) = 1` using `by rw [map_mul, map_mul, hη, hg]; simp`. Establish `h2` using `pn_conj R c hc z hz h0 (c * g * c)`. Rewrite `h2` using `[← e, hY _ h1, map_sub, pn_rmul, pn_rmul, hcc]`. Conclude with `h2`. Establish `hA : ∀ g, η g = 1 → z g = R g ((2 : K)⁻¹ • (Y + R c Y)) - (2 : K)⁻¹ • (Y + R c Y)` using `fun g hg => by`.

Establish `h3 : z g = (2 : K)⁻¹ • (z g + z g)`. Rewrite using `[smul_add, ← add_smul]`. Evaluate the numerical expressions. Rewrite using `[map_smul, ← smul_sub, map_add, h3]`. Use `congr 1`.

Use `nth_rewrite 1 [hY g hg]`. Rewrite using `[hY' g hg]`. Normalize the expressions using the abelian group laws. Use `⟨(2 : K)⁻¹ • (Y + R c Y), fun g => ?_⟩` and prove the remaining obligations. Break down `Int.units_eq_one_or (η g) with hg | hg` into its components or cases.

Conclude with `hA g hg`. Establish `h1 : η (g * c) = 1` using `by rw [map_mul, hg, hη]; simp`. Establish `h2` using `hA _ h1`. Rewrite `h2` using `[hz, h0, map_zero, add_zero, pn_rmul]`. Rewrite using `[h2, map_smul (R c), map_add (R c), hcc, add_comm (R c Y)]`.
-/
private theorem pn_ext (R : Representation K G V) (η : G →* ℤˣ) (c : G) (hc : c * c = 1) (hη : η c = -1)
    (z : G → V) (hz : ∀ g h, z (g * h) = z g + R g (z h)) (h0 : z c = 0) (Y : V)
    (hY : ∀ g, η g = 1 → z g = R g Y - Y) : ∃ X, ∀ g, z g = R g X - X := by
  have hi : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hcc : ∀ X, R c (R c X) = X := fun X => by rw [← pn_rmul, hc, map_one]; rfl
  have hY' : ∀ g, η g = 1 → z g = R g (R c Y) - R c Y := fun g hg => by
    have e : g = c * (c * g * c) * c⁻¹ := by
      rw [hi, ← mul_assoc, ← mul_assoc, hc, one_mul, mul_assoc, hc, mul_one]
    have h1 : η (c * g * c) = 1 := by rw [map_mul, map_mul, hη, hg]; simp
    have h2 := pn_conj R c hc z hz h0 (c * g * c)
    rw [← e, hY _ h1, map_sub, pn_rmul, pn_rmul, hcc] at h2
    exact h2
  have hA : ∀ g, η g = 1 → z g = R g ((2 : K)⁻¹ • (Y + R c Y)) - (2 : K)⁻¹ • (Y + R c Y) := fun g hg => by
    have h3 : z g = (2 : K)⁻¹ • (z g + z g) := by
      rw [smul_add, ← add_smul]; norm_num
    rw [map_smul, ← smul_sub, map_add, h3]
    congr 1
    nth_rewrite 1 [hY g hg]
    rw [hY' g hg]
    abel
  refine ⟨(2 : K)⁻¹ • (Y + R c Y), fun g => ?_⟩
  rcases Int.units_eq_one_or (η g) with hg | hg
  · exact hA g hg
  · have h1 : η (g * c) = 1 := by rw [map_mul, hg, hη]; simp
    have h2 := hA _ h1
    rw [hz, h0, map_zero, add_zero, pn_rmul] at h2
    rw [h2, map_smul (R c), map_add (R c), hcc, add_comm (R c Y)]

end aux

/- English proof (translation)
Introduce `l _ F K _ _ n ρ P R z hR hz`. Take `⟨X₀, h0⟩` from `pn_norm R F.c F.c_sq z hz`. Establish `hd : ∀ (Y : Matrix (Fin n) (Fin n) K) (g : F.G₀), Pa.dY F (W.mat ρ) Y g = R g Y - Y` using `fun Y g => by`. Rewrite using `[hR.ad]`. Express the relevant statement in the definitionally equal form `(ρ g : Matrix (Fin n) (Fin n) K) * Y * (ρ g⁻¹ : GL (Fin n) K) - Y = _`.

Rewrite using `[map_inv]`. Both sides reduce to the same expression. Establish `hz' : ∀ g h, (z (g * h) - (R (g * h) X₀ - X₀)) = (z g - (R g X₀ - X₀)) + R g (z h - (R h X₀ - X₀))` using `fun g h => by`. Rewrite using `[hz, pn_rmul, map_sub, map_sub]`. Normalize the expressions using the abelian group laws.

Use `⟨X₀, fun g => ?_, fun Y hY => ?_⟩` and prove the remaining obligations. Rewrite using `[hd, hd]`. Establish `h1` using `pn_conj R F.c F.c_sq (fun g => z g - (R g X₀ - X₀)) hz' h0 g`. Establish `h2 : ((F.conj g : F.G₀) : F.Γ) = F.c * g * F.c⁻¹` using `rfl`. Rewrite using `[h2, h1, hR.c, Matrix.mul_neg, Matrix.mul_assoc, ← Matrix.mul_assoc (P : Matrix (Fin n) (Fin n) K), Units.mul_inv, Matrix.one_mul]`.

Take `⟨X, hX⟩` from `pn_ext R F.η F.c F.c_sq F.η_c (fun g => z g - (R g X₀ - X₀)) hz' h0 Y fun g hg => by`. Use `hY ⟨g, hg⟩` as an intermediate fact. Rewrite `this` using `[hd, hd]`. Then use the resulting hypothesis. Use `⟨X₀ + X, fun g => ?_⟩` and prove the remaining obligations. Use `hX g` as an intermediate fact.

Rewrite using `[map_add, add_sub_add_comm, ← this]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.V.Th.Det.polNorm :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) {K : Type} [Field K] [CharZero K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K) (R : Representation K F.Γ (Matrix (Fin n) (Fin n) K)) (z : F.Γ → Matrix (Fin n) (Fin n) K), Ws.Eb.IsAdExt F ρ P R → (∀ g h, z (g * h) = z g + R g (z h)) → ∃ X₀ : Matrix (Fin n) (Fin n) K, (∀ g : F.G₀, (P : Matrix (Fin n) (Fin n) K) * (z (F.conj g) - Pa.dY F (W.mat ρ) X₀ (F.conj g)) = -((z g - Pa.dY F (W.mat ρ) X₀ g)ᵀ * P)) ∧ ∀ Y, (∀ g : F.G₀, z g - Pa.dY F (W.mat ρ) X₀ g = Pa.dY F (W.mat ρ) Y g) → ∃ X, ∀ g, z g = R g X - X := by
  intro l _ F K _ _ n ρ P R z hR hz
  obtain ⟨X₀, h0⟩ := pn_norm R F.c F.c_sq z hz
  have hd : ∀ (Y : Matrix (Fin n) (Fin n) K) (g : F.G₀), Pa.dY F (W.mat ρ) Y g = R g Y - Y := fun Y g => by
    rw [hR.ad]
    change (ρ g : Matrix (Fin n) (Fin n) K) * Y * (ρ g⁻¹ : GL (Fin n) K) - Y = _
    rw [map_inv]
    rfl
  have hz' : ∀ g h, (z (g * h) - (R (g * h) X₀ - X₀)) = (z g - (R g X₀ - X₀)) + R g (z h - (R h X₀ - X₀)) :=
    fun g h => by
      rw [hz, pn_rmul, map_sub, map_sub]
      abel
  refine ⟨X₀, fun g => ?_, fun Y hY => ?_⟩
  · rw [hd, hd]
    have h1 := pn_conj R F.c F.c_sq (fun g => z g - (R g X₀ - X₀)) hz' h0 g
    have h2 : ((F.conj g : F.G₀) : F.Γ) = F.c * g * F.c⁻¹ := rfl
    rw [h2, h1, hR.c, Matrix.mul_neg, Matrix.mul_assoc, ← Matrix.mul_assoc (P : Matrix (Fin n) (Fin n) K),
      Units.mul_inv, Matrix.one_mul]
  · obtain ⟨X, hX⟩ := pn_ext R F.η F.c F.c_sq F.η_c (fun g => z g - (R g X₀ - X₀)) hz' h0 Y fun g hg => by
      have := hY ⟨g, hg⟩
      rwa [hd, hd] at this
    refine ⟨X₀ + X, fun g => ?_⟩
    have := hX g
    rw [map_add, add_sub_add_comm, ← this]
    abel
