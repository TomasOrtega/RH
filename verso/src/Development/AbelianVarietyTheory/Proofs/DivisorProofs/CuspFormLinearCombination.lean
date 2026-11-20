import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspFormLin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {d : ℕ}

/- English proof (translation)
Take `⟨C, N, h⟩` from `h`. Take `⟨C', N', h'⟩` from `h'`. Use `⟨‖c‖ * |C| + |C'|, N + N', fun y => ?_⟩` and prove the remaining obligations. Establish `h1` using `one_le_height y`. Establish `e : ‖f y‖ ≤ |C| * height y ^ (N + N')` using `(h y).trans (mul_le_mul (le_abs_self C) (pow_le_pow_right₀ h1 (Nat.le_add_right N N')) (by positivity) (abs_nonneg C))`.

Establish `e' : ‖f' y‖ ≤ |C'| * height y ^ (N + N')` using `(h' y).trans (mul_le_mul (le_abs_self C') (pow_le_pow_right₀ h1 (Nat.le_add_left N' N)) (by positivity) (abs_nonneg C'))`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, add_mul, mul_assoc]`. Conclude with `add_le_add (mul_le_mul_of_nonneg_left e (norm_nonneg c)) e'`.
-/
theorem growth_smul_add (c : ℂ) {f f' : GL (Fin d) (Cinf E) → ℂ}
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N)
    (h' : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f' y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖c * f y + f' y‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, h⟩ := h
  obtain ⟨C', N', h'⟩ := h'
  refine ⟨‖c‖ * |C| + |C'|, N + N', fun y => ?_⟩
  have h1 := one_le_height y
  have e : ‖f y‖ ≤ |C| * height y ^ (N + N') :=
    (h y).trans (mul_le_mul (le_abs_self C) (pow_le_pow_right₀ h1 (Nat.le_add_right N N'))
      (by positivity) (abs_nonneg C))
  have e' : ‖f' y‖ ≤ |C'| * height y ^ (N + N') :=
    (h' y).trans (mul_le_mul (le_abs_self C') (pow_le_pow_right₀ h1 (Nat.le_add_left N' N))
      (by positivity) (abs_nonneg C'))
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, add_mul, mul_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_left e (norm_nonneg c)) e'

/- English proof (translation)
Express the relevant statement in the definitionally equal form `c * φ.1 _ + ψ.1 _ = c * φ.1 _ + ψ.1 _`. Rewrite using `[h.left, h'.left]`. Use `level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset ((h.level.inter h'.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => by`. Establish `h1 : finRep E d k φ = φ` using `hk.1`. Establish `h2 : finRep E d k ψ = ψ` using `hk.2`.

Express the relevant statement in the definitionally equal form `finRep E d k (c • φ + ψ) = c • φ + ψ`. Rewrite using `[map_add, map_smul, h1, h2]`. Use `kfin := by`. Use `h.kfin` as an intermediate fact. Use `h'.kfin` as an intermediate fact.

Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E d k φ) ⊔ Submodule.span ℂ (Set.range fun k => cptRep E d k ψ)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Express the relevant statement in the definitionally equal form `cptRep E d k (c • φ + ψ) ∈ _`. Rewrite using `[map_add, map_smul]`. Conclude with `Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)) (Submodule.subset_span ⟨k, rfl⟩)`.

Use `zfin := by`. Use `h.zfin` as an intermediate fact. Use `h'.zfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z φ) '' Zalg E d) ⊔ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z ψ) '' Zalg E d)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Express the relevant statement in the definitionally equal form `z (c • φ + ψ) ∈ _`. Rewrite using `[map_add, map_smul]`. Conclude with `Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩)) (Submodule.subset_span ⟨z, hz, rfl⟩)`. Use `growth g := growth_smul_add c (h.growth g) (h'.growth g)`.
-/
theorem isAutForm_smul_add (c : ℂ) {φ ψ : Sm E d} (h : IsAutForm φ) (h' : IsAutForm ψ) :
    IsAutForm (c • φ + ψ) where
  left γ g := by
    change c * φ.1 _ + ψ.1 _ = c * φ.1 _ + ψ.1 _
    rw [h.left, h'.left]
  level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
    ((h.level.inter h'.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
      have h1 : finRep E d k φ = φ := hk.1
      have h2 : finRep E d k ψ = ψ := hk.2
      change finRep E d k (c • φ + ψ) = c • φ + ψ
      rw [map_add, map_smul, h1, h2]
  kfin := by
    have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E d k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E d k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change cptRep E d k (c • φ + ψ) ∈ _
    rw [map_add, map_smul]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
      (Submodule.subset_span ⟨k, rfl⟩)
  zfin := by
    have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z φ) '' Zalg E d) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z ψ) '' Zalg E d)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    change z (c • φ + ψ) ∈ _
    rw [map_add, map_smul]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩))
      (Submodule.subset_span ⟨z, hz, rfl⟩)
  growth g := growth_smul_add c (h.growth g) (h'.growth g)

/- English proof (translation)
Use `⟨isAutForm_smul_add c h.1 h'.1, fun r h0 h1 _ _ ν 𝓕 hν h𝓕 g => ?_⟩` and prove the remaining obligations. Establish `i` using `CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d φ h.1.level) h.1.left ν h𝓕 g`. Establish `i'` using `CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d ψ h'.1.level) h'.1.left ν h𝓕 g`. Express the relevant statement in the definitionally equal form `∫ x in 𝓕, (c * φ.1 (unip x * g) + ψ.1 (unip x * g)) ∂ν = 0`. Rewrite using `[integral_add (i.const_mul c) i', integral_const_mul, h.2 r h0 h1 ν 𝓕 hν h𝓕 g, h'.2 r h0 h1 ν 𝓕 hν h𝓕 g, mul_zero, add_zero]`.
-/
theorem isCuspForm_smul_add (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (d : ℕ) (c : ℂ)
    (φ ψ : Sm E d) (h : IsCuspForm φ) (h' : IsCuspForm ψ) : IsCuspForm (c • φ + ψ) := by
  refine ⟨isAutForm_smul_add c h.1 h'.1, fun r h0 h1 _ _ ν 𝓕 hν h𝓕 g => ?_⟩
  have i := CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d φ h.1.level) h.1.left ν h𝓕 g
  have i' := CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d ψ h'.1.level) h'.1.left ν h𝓕 g
  change ∫ x in 𝓕, (c * φ.1 (unip x * g) + ψ.1 (unip x * g)) ∂ν = 0
  rw [integral_add (i.const_mul c) i', integral_const_mul, h.2 r h0 h1 ν 𝓕 hν h𝓕 g, h'.2 r h0 h1 ν 𝓕 hν h𝓕 g,
    mul_zero, add_zero]

end GlobalTheory.CuspFormLin
