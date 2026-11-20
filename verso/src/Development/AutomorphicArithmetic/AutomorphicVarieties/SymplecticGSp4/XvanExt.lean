import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Distinguish the cases in `ha : ∀ g, a g = 1`. Use `⟨0, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_zero, sub_zero]`. Use `(Module.forall_dual_apply_eq_zero_iff k₀ (z g)).1 fun φ => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `h φ`.

Rewrite using `[hm g, ha g, one_mul, sub_self]`. Use `push_neg at ha`. Take `⟨g₀, hg₀⟩` from `ha`. Establish `hne : a g₀ - 1 ≠ 0` using `sub_ne_zero.2 hg₀`. Use `⟨(a g₀ - 1)⁻¹ • z g₀, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[← Algebra.smul_def, ← sub_eq_zero]`. Use `(Module.forall_dual_apply_eq_zero_iff k₀ _).1 fun φ => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `h φ`. Establish `key : φ ((a g₀ - 1)⁻¹ • z g₀) = m`. Rewrite using `[map_smul, hm g₀, smul_eq_mul, ← sub_one_mul, inv_mul_cancel_left₀ hne]`.

Rewrite using `[map_sub, map_sub, map_smul, key, hm g, smul_eq_mul, sub_self]`.
-/
private theorem cob_of_coord {H k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k] (a : H → k₀) (z : H → k)
    (h : ∀ φ : k →ₗ[k₀] k₀, ∃ m, ∀ g, φ (z g) = a g * m - m) :
    ∃ m, ∀ g, z g = algebraMap k₀ k (a g) * m - m := by
  by_cases ha : ∀ g, a g = 1
  · refine ⟨0, fun g => ?_⟩
    rw [mul_zero, sub_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ (z g)).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    rw [hm g, ha g, one_mul, sub_self]
  · push_neg at ha
    obtain ⟨g₀, hg₀⟩ := ha
    have hne : a g₀ - 1 ≠ 0 := sub_ne_zero.2 hg₀
    refine ⟨(a g₀ - 1)⁻¹ • z g₀, fun g => ?_⟩
    rw [← Algebra.smul_def, ← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ _).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    have key : φ ((a g₀ - 1)⁻¹ • z g₀) = m := by
      rw [map_smul, hm g₀, smul_eq_mul, ← sub_one_mul, inv_mul_cancel_left₀ hne]
    rw [map_sub, map_sub, map_smul, key, hm g, smul_eq_mul, sub_self]

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD k _ red hred γ hγ z hz hcoc hunr hloc`. Establish `hlh : IsLocalHom red` using `⟨fun a ha => by`. Assume the negation of the conclusion as `hn`. Establish `h0` using `hred a ((mem_maximalIdeal a).2 hn)`. Rewrite `ha` using `[h0]`.

Conclude with `not_isUnit_zero ha⟩`. Use `letI : Algebra (ResidueField c.O) k := (ResidueField.lift red).toAlgebra`. Establish `hι : ∀ a : c.O, red a = algebraMap (ResidueField c.O) k (residue c.O a)` using `fun a => (ResidueField.lift_residue_apply red a).symm`. Establish `hX : D.XVan γ`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hγ`.

Break down `hγ with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Conclude with `(hD.xvan D.al (by simp)).1`. Conclude with `(hD.xvan D.be (by simp)).1`. Conclude with `(hD.xvan D.th (by simp)).1`. Conclude with `(hD.xvan D.al (by simp)).2`.

Conclude with `(hD.xvan D.be (by simp)).2`. Conclude with `(hD.xvan D.th (by simp)).2`. Simplify using `only [hι]`. Apply `cob_of_coord (fun g => Raw.bar γ g) z` to reduce the goal to its premises. Introduce `φ`.

Establish `h1 : ∀ g h, φ (z (g * h)) = φ (z g) + Raw.bar γ g * φ (z h)`. Introduce `g h`. Rewrite using `[hcoc g h, map_add, hι, ← Algebra.smul_def, map_smul, smul_eq_mul]`. Establish `h2 : D.UnrT (fun g => φ (z g)) 0`. Introduce `A hA g hg hb`.

Simplify using `only [hunr A hA g hg hb, map_zero]`. Establish `h3 : ∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, φ (z g) = Raw.bar γ g * m - m`. Introduce `v hv`. Take `⟨m, hm⟩` from `hloc v hv`. Use `⟨φ m, fun g hg => ?_⟩` and prove the remaining obligations.

Rewrite using `[hm g hg, hι, ← Algebra.smul_def, map_sub, map_smul, smul_eq_mul]`. Conclude with `hX (fun g => φ (z g)) (hz.comp fun x => φ x) h1 h2 h3`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.xvanExt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (k : Type) [Field k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) → ∀ γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹], ∀ z : G ℚ Ω → k, IsLocallyConstant z → (∀ g h, z (g * h) = z g + red (γ g : c.O) * z h) → D.UnrT z 0 → (∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, z g = red (γ g : c.O) * m - m) → ∃ m, ∀ g, z g = red (γ g : c.O) * m - m := by
  intro Ω _ _ _ l _ c D hD k _ red hred γ hγ z hz hcoc hunr hloc
  have hlh : IsLocalHom red := ⟨fun a ha => by
    by_contra hn
    have h0 := hred a ((mem_maximalIdeal a).2 hn)
    rw [h0] at ha
    exact not_isUnit_zero ha⟩
  letI : Algebra (ResidueField c.O) k := (ResidueField.lift red).toAlgebra
  have hι : ∀ a : c.O, red a = algebraMap (ResidueField c.O) k (residue c.O a) := fun a =>
    (ResidueField.lift_residue_apply red a).symm
  have hX : D.XVan γ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hD.xvan D.al (by simp)).1
    · exact (hD.xvan D.be (by simp)).1
    · exact (hD.xvan D.th (by simp)).1
    · exact (hD.xvan D.al (by simp)).2
    · exact (hD.xvan D.be (by simp)).2
    · exact (hD.xvan D.th (by simp)).2
  simp only [hι]
  apply cob_of_coord (fun g => Raw.bar γ g) z
  intro φ
  have h1 : ∀ g h, φ (z (g * h)) = φ (z g) + Raw.bar γ g * φ (z h) := by
    intro g h
    rw [hcoc g h, map_add, hι, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have h2 : D.UnrT (fun g => φ (z g)) 0 := by
    intro A hA g hg hb
    simp only [hunr A hA g hg hb, map_zero]
  have h3 : ∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, φ (z g) = Raw.bar γ g * m - m := by
    intro v hv
    obtain ⟨m, hm⟩ := hloc v hv
    refine ⟨φ m, fun g hg => ?_⟩
    rw [hm g hg, hι, ← Algebra.smul_def, map_sub, map_smul, smul_eq_mul]
  exact hX (fun g => φ (z g)) (hz.comp fun x => φ x) h1 h2 h3
