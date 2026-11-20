import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private noncomputable def piB {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] : MonoidAlgebra B G →ₐ[B] (Fin n → B) :=
  MonoidAlgebra.lift B (Fin n → B) G
    { toFun := fun g i => algebraMap k B (χ i g)
      map_one' := by ext i; simp
      map_mul' := fun g h => by ext i; simp }

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem piB_single {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (g : G) (b : B) (i : Fin n) :
    piB χ B (MonoidAlgebra.single g b) i = b * algebraMap k B (χ i g) := by
  simp [piB]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.
-/
private theorem piB_map {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (y : MonoidAlgebra k G) (i : Fin n) :
    piB χ B (MonoidAlgebra.mapRingHom G (algebraMap k B) y) i = algebraMap k B (piB χ k y i) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  | single g r => rw [MonoidAlgebra.mapRingHom_single, piB_single, piB_single]; simp

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Proceed by induction. Treat this case separately.

Treat this case separately. Both sides reduce to the same expression. Treat this case separately. By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
private theorem D_eq {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (x : MonoidAlgebra B G) :
    (GDet.ofChars χ).D B x = ∏ i, piB χ B x i := by
  change (GDet.repAlg (GDet.diagRep χ) B x).det = _
  rw [← Matrix.det_diagonal]
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [Pi.zero_def]
  | add a b ha hb => simp only [map_add, ha, hb, Matrix.diagonal_add]; rfl
  | single g r =>
    ext i j
    by_cases h : i = j
    · subst h; simp [GDet.repAlg, GDet.diagRep, piB_single]
    · simp [GDet.repAlg, GDet.diagRep, Matrix.diagonal_apply_ne _ h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.CA.f_chars :
    ∀ {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ), Function.Injective χ → ∃ π : MonoidAlgebra k G →ₐ[k] (Fin n → k), Function.Surjective π ∧ (∀ g i, π (MonoidAlgebra.single g 1) i = χ i g) ∧ (∀ y, (GDet.ofChars χ).Kills y ↔ π y = 0) ∧ ∀ y, (GDet.ofChars χ).chi y = ∏ i, (X - C (π y i)) := by
  intro n k G _ _ χ hχ
  have hs : ∀ g i, piB χ k (MonoidAlgebra.single g 1) i = χ i g := fun g i => by simp [piB_single]
  have hsurj : Function.Surjective (piB χ k) := by
    have hinj : Function.Injective fun i => (Units.coeHom k).comp (χ i) := fun i j h =>
      hχ (MonoidHom.ext fun g => Units.ext (DFunLike.congr_fun h g))
    have hli : LinearIndependent k fun i (g : G) => (χ i g : k) :=
      (linearIndependent_monoidHom G k).comp _ hinj
    have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
    have : LinearMap.range (piB χ k).toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, funext (hs g)⟩
    exact LinearMap.range_eq_top.1 this
  refine ⟨piB χ k, hsurj, hs, fun y => ⟨fun h => ?_, fun h B _ _ z => ?_⟩, fun y => ?_⟩
  · ext i
    by_contra hi
    obtain ⟨z, hz⟩ := hsurj fun _ => -(piB χ k y i)⁻¹
    have := h k z
    rw [D_eq, Finset.prod_eq_zero (Finset.mem_univ i)] at this
    · exact zero_ne_one this
    · rw [map_add, map_mul, map_one, Pi.add_apply, Pi.mul_apply, piB_map, hz]
      have hi' : piB χ k y i ≠ 0 := hi
      simp [hi']
  · rw [D_eq]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [map_add, map_mul, map_one, Pi.add_apply, Pi.mul_apply, piB_map, h]
    simp
  · unfold GDet.chi
    rw [D_eq]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sub, Pi.sub_apply, piB_single]
    have := piB_map χ k[X] y i
    rw [Polynomial.algebraMap_eq] at this
    rw [this]
    simp
