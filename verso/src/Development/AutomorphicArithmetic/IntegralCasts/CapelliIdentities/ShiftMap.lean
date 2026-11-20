import Mathlib

private def UpperTheory.Reformulated.B.ShiftMap.shift {G H : Type} [Group G] [Group H] (p : G →* H) :
    G →* ((H → ℂ) →ₗ[ℂ] (H → ℂ)) where
  toFun g := LinearMap.funLeft ℂ ℂ (fun z => (p g)⁻¹ * z)
  map_one' := by
    ext φ z
    simp [LinearMap.funLeft]
  map_mul' g h := by
    ext φ z
    simp [LinearMap.funLeft, mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma UpperTheory.Reformulated.B.ShiftMap.shift_apply {G H : Type} [Group G] [Group H] (p : G →* H)
    (g : G) (φ : H → ℂ) (z : H) : UpperTheory.Reformulated.B.ShiftMap.shift p g φ z = φ ((p g)⁻¹ * z) := rfl

/- English proof (translation)
Introduce `G H _ _ _ _ _ _ p hp f hf hfd`. Use `set V : Submodule ℂ (H → ℂ) := Submodule.span ℂ (Set.range fun (k : G) (z : H) ↦ f ((p k)⁻¹ * z)) with hV`. Establish `hinv : ∀ g : G, ∀ φ ∈ V, UpperTheory.Reformulated.B.ShiftMap.shift p g φ ∈ V`. Introduce `g`. Establish `h : V ≤ V.comap (UpperTheory.Reformulated.B.ShiftMap.shift p g)`.

Rewrite using `[hV, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `Submodule.subset_span ⟨g * k, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Simplify using `[UpperTheory.Reformulated.B.ShiftMap.shift_apply, mul_assoc]`.

Conclude with `fun φ hφ => h hφ`. Establish `hcont : ∀ φ ∈ V, Continuous φ`. Introduce `φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem φ h`.

Take `⟨k, rfl⟩` from `h`. Conclude with `hf.comp (continuous_const.mul continuous_id)`. Consider the case `zero => exact continuous_zero`. Consider the case `add a b _ _ ha hb => exact ha.add hb`. Consider the case `smul c a _ ha => exact ha.const_smul c`.

Establish `hfV : f ∈ V` using `Submodule.subset_span ⟨1, by funext z; simp⟩`. Set `σ : G →* (V →ₗ[ℂ] V)` to `{ toFun := fun g => (UpperTheory.Reformulated.B.ShiftMap.shift p g).restrict (hinv g) map_one' := by`. Use extensionality with `φ z`. Simplify using `[UpperTheory.Reformulated.B.ShiftMap.shift_apply]`. Use the proof step `map_mul' := by`.

Introduce `g h`. Use extensionality with `φ z`. Simplify using `[UpperTheory.Reformulated.B.ShiftMap.shift_apply, mul_assoc] }`. Establish `hσ : ∀ (g : G) (φ : V) (z : H), (σ g φ : H → ℂ) z = (φ : H → ℂ) ((p g)⁻¹ * z)` using `fun _ _ _ => rfl`. Set `b` to `Module.finBasis ℂ V`.

Set `e` to `LinearMap.toMatrixAlgEquiv b`. Use `⟨Module.finrank ℂ V, (e.toAlgHom.toRingHom.toMonoidHom).comp σ, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun g : G => σ g (b j)`. Use `Continuous.subtype_mk (continuous_pi fun z => ?_) _` and prove the remaining obligations.

Conclude with `(hcont _ (b j).2).comp (hp.inv.mul continuous_const)`. Establish `h2 : Continuous (b.coord i)` using `LinearMap.continuous_of_finiteDimensional _`. Use `(h2.comp h1).congr fun g => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = LinearMap.toMatrixAlgEquiv b (σ g) i j`. Rewrite using `[LinearMap.toMatrixAlgEquiv_apply]`.

Both sides reduce to the same expression. Introduce `x hx z`. Establish `h1 : (x.sum fun k c => c • σ k) = 0`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_zero, ← hx, Finsupp.sum, Finsupp.sum, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Both sides reduce to the same expression. Establish `h2` using `congrArg (fun T : V →ₗ[ℂ] V => (T ⟨f, hfV⟩ : H → ℂ) z) h1`. Simplify `h2` using `[Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply, hσ]`.
-/
theorem UpperTheory.Reformulated.B.ShiftMap.finite_translates_matrix_coefficient :
    ∀ (G H : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
    [inst_3 : Group H] [inst_4 : TopologicalSpace H] [IsTopologicalGroup H] (p : G →* H),
    Continuous (⇑p : G → H) →
      ∀ (f : H → ℂ),
        Continuous f →
          FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun (k : G) (z : H) ↦ f (((p : G → H) k)⁻¹ * z))) →
            ∃ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ),
              Continuous (⇑ρ : G → Matrix (Fin d) (Fin d) ℂ) ∧
                ∀ (x : G →₀ ℂ),
                  (x.sum fun (k : G) (c : ℂ) ↦ c • (ρ : G → Matrix (Fin d) (Fin d) ℂ) k) =
                      (0 : Matrix (Fin d) (Fin d) ℂ) →
                    ∀ (z : H), (x.sum fun (k : G) (c : ℂ) ↦ c * f (((p : G → H) k)⁻¹ * z)) = (0 : ℂ) := by
  intro G H _ _ _ _ _ _ p hp f hf hfd
  set V : Submodule ℂ (H → ℂ) :=
    Submodule.span ℂ (Set.range fun (k : G) (z : H) ↦ f ((p k)⁻¹ * z)) with hV
  have hinv : ∀ g : G, ∀ φ ∈ V, UpperTheory.Reformulated.B.ShiftMap.shift p g φ ∈ V := by
    intro g
    have h : V ≤ V.comap (UpperTheory.Reformulated.B.ShiftMap.shift p g) := by
      rw [hV, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨g * k, ?_⟩
      funext z
      simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply, mul_assoc]
    exact fun φ hφ => h hφ
  have hcont : ∀ φ ∈ V, Continuous φ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨k, rfl⟩ := h
      exact hf.comp (continuous_const.mul continuous_id)
    | zero => exact continuous_zero
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  have hfV : f ∈ V := Submodule.subset_span ⟨1, by funext z; simp⟩
  let σ : G →* (V →ₗ[ℂ] V) :=
    { toFun := fun g => (UpperTheory.Reformulated.B.ShiftMap.shift p g).restrict (hinv g)
      map_one' := by
        ext φ z
        simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply]
      map_mul' := by
        intro g h
        ext φ z
        simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply, mul_assoc] }
  have hσ : ∀ (g : G) (φ : V) (z : H), (σ g φ : H → ℂ) z = (φ : H → ℂ) ((p g)⁻¹ * z) :=
    fun _ _ _ => rfl
  let b := Module.finBasis ℂ V
  let e := LinearMap.toMatrixAlgEquiv b
  refine ⟨Module.finrank ℂ V, (e.toAlgHom.toRingHom.toMonoidHom).comp σ, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    have h1 : Continuous fun g : G => σ g (b j) := by
      refine Continuous.subtype_mk (continuous_pi fun z => ?_) _
      exact (hcont _ (b j).2).comp (hp.inv.mul continuous_const)
    have h2 : Continuous (b.coord i) := LinearMap.continuous_of_finiteDimensional _
    refine (h2.comp h1).congr fun g => ?_
    change _ = LinearMap.toMatrixAlgEquiv b (σ g) i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    rfl
  · intro x hx z
    have h1 : (x.sum fun k c => c • σ k) = 0 := by
      apply e.injective
      rw [map_zero, ← hx, Finsupp.sum, Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      rfl
    have h2 := congrArg (fun T : V →ₗ[ℂ] V => (T ⟨f, hfV⟩ : H → ℂ) z) h1
    simpa [Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply, hσ] using h2
