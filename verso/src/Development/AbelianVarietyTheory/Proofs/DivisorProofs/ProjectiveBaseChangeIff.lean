import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
open GlobalTheory.RingChain GlobalTheory.PerfdLat
open scoped TensorProduct Pointwise

namespace GlobalTheory.CokerProj

/- English proof (translation)
Establish `hker : LinearMap.ker π = LinearMap.range f` using `hex.linearMap_ker_eq`. Prove the components needed by the constructor for the conclusion. Introduce `hP`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`. Establish `hs' : ∀ x, π (s x) = x` using `fun x => LinearMap.congr_fun hs x`.

Establish `hmem : ∀ x, (LinearMap.id - s ∘ₗ π : F₀ →ₗ[S] F₀) x ∈ LinearMap.range f`. Introduce `x`. Rewrite using `[← hker, LinearMap.mem_ker]`. Simplify using `[hs']`. Take `⟨w, hw⟩` from `Module.projective_lifting_property f.rangeRestrict (LinearMap.codRestrict _ _ hmem) f.surjective_rangeRestrict`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `h1` using `congrArg Subtype.val (LinearMap.congr_fun hw (f x))`. Establish `h2 : π (f x) = 0` using `hex.apply_apply_eq_zero x`. Simplify `h1` using `[h2]`.

Introduce and unpack `⟨w, hw⟩`. Establish `hw' : ∀ x, f (w (f x)) = f x` using `fun x => LinearMap.congr_fun hw x`. Establish `hle : LinearMap.ker π ≤ LinearMap.ker (LinearMap.id - f ∘ₗ w : F₀ →ₗ[S] F₀)`. Rewrite using `[hker]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Simplify using `[hw']`. Set `e` to `π.quotKerEquivOfSurjective hπ`. Set `s : P →ₗ[S] F₀` to `(LinearMap.ker π).liftQ _ hle ∘ₗ e.symm.toLinearMap`. Use `Module.Projective.of_split s π ?_` and prove the remaining obligations. Use extensionality with `y`.

Take `⟨x, rfl⟩` from `hπ y`. Establish `h1 : e.symm (π x) = Submodule.Quotient.mk x`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Establish `h2 : π (f (w x)) = 0` using `hex.apply_apply_eq_zero _`.

Simplify using `[s, h1, h2]`.
-/
theorem projective_iff_of_exact {S : Type} [CommRing S] {F₁ F₀ P : Type}
    [AddCommGroup F₁] [Module S F₁] [AddCommGroup F₀] [Module S F₀] [AddCommGroup P] [Module S P]
    [Module.Projective S F₀] (f : F₁ →ₗ[S] F₀) (π : F₀ →ₗ[S] P) (hπ : Function.Surjective π)
    (hex : Function.Exact f π) :
    Module.Projective S P ↔ ∃ w : F₀ →ₗ[S] F₁, f ∘ₗ w ∘ₗ f = f := by
  have hker : LinearMap.ker π = LinearMap.range f := hex.linearMap_ker_eq
  constructor
  · intro hP
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    have hs' : ∀ x, π (s x) = x := fun x => LinearMap.congr_fun hs x
    have hmem : ∀ x, (LinearMap.id - s ∘ₗ π : F₀ →ₗ[S] F₀) x ∈ LinearMap.range f := by
      intro x
      rw [← hker, LinearMap.mem_ker]
      simp [hs']
    obtain ⟨w, hw⟩ := Module.projective_lifting_property f.rangeRestrict
      (LinearMap.codRestrict _ _ hmem) f.surjective_rangeRestrict
    refine ⟨w, ?_⟩
    ext x
    have h1 := congrArg Subtype.val (LinearMap.congr_fun hw (f x))
    have h2 : π (f x) = 0 := hex.apply_apply_eq_zero x
    simpa [h2] using h1
  · rintro ⟨w, hw⟩
    have hw' : ∀ x, f (w (f x)) = f x := fun x => LinearMap.congr_fun hw x
    have hle : LinearMap.ker π ≤ LinearMap.ker (LinearMap.id - f ∘ₗ w : F₀ →ₗ[S] F₀) := by
      rw [hker]
      rintro _ ⟨x, rfl⟩
      simp [hw']
    let e := π.quotKerEquivOfSurjective hπ
    let s : P →ₗ[S] F₀ := (LinearMap.ker π).liftQ _ hle ∘ₗ e.symm.toLinearMap
    refine Module.Projective.of_split s π ?_
    ext y
    obtain ⟨x, rfl⟩ := hπ y
    have h1 : e.symm (π x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    have h2 : π (f (w x)) = 0 := hex.apply_apply_eq_zero _
    simp [s, h1, h2]

/- English proof (translation)
Establish `hsurj` using `(LinearMap.range (Matrix.mulVecLin R)).mkQ_surjective`. Establish `hex : Function.Exact (Matrix.mulVecLin R) (LinearMap.range (Matrix.mulVecLin R)).mkQ` using `LinearMap.exact_map_mkQ_range _`. Establish `hex' : Function.Exact ((Matrix.mulVecLin R).baseChange S) ((LinearMap.range (Matrix.mulVecLin R)).mkQ.baseChange S)` using `lTensor_exact S hex hsurj`. Establish `hsurj' : Function.Surjective ((LinearMap.range (Matrix.mulVecLin R)).mkQ.baseChange S)` using `LinearMap.lTensor_surjective S hsurj`. Rewrite using `[projective_iff_of_exact _ _ hsurj' hex']`.

Set `b₁` to `Algebra.TensorProduct.basis S (Pi.basisFun A (Fin r))`. Set `b₀` to `Algebra.TensorProduct.basis S (Pi.basisFun A (Fin m))`. Establish `hR : LinearMap.toMatrix b₁ b₀ ((Matrix.mulVecLin R).baseChange S) = R.map (algebraMap A S)`. Rewrite using `[LinearMap.toMatrix_baseChange]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[LinearMap.toMatrix_apply, Pi.single_apply, Matrix.mulVec, dotProduct]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw⟩`. Use `⟨LinearMap.toMatrix b₀ b₁ w, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hR, Matrix.mul_assoc, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, hw]`. Introduce and unpack `⟨W, hW⟩`. Use `⟨Matrix.toLin b₀ b₁ W, ?_⟩` and prove the remaining obligations. Apply `(LinearMap.toMatrix b₁ b₀).injective` to reduce the goal to its premises. Rewrite using `[LinearMap.toMatrix_comp b₁ b₁ b₀, LinearMap.toMatrix_comp b₁ b₀ b₁, LinearMap.toMatrix_toLin, hR, ← Matrix.mul_assoc, hW]`.
-/
theorem projective_baseChange_iff (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (m r : ℕ)
    (R : Matrix (Fin m) (Fin r) A) :
    Module.Projective S (S ⊗[A] ((Fin m → A) ⧸ LinearMap.range (Matrix.mulVecLin R))) ↔
      ∃ W : Matrix (Fin r) (Fin m) S,
        R.map (algebraMap A S) * W * R.map (algebraMap A S) = R.map (algebraMap A S) := by
  have hsurj := (LinearMap.range (Matrix.mulVecLin R)).mkQ_surjective
  have hex : Function.Exact (Matrix.mulVecLin R) (LinearMap.range (Matrix.mulVecLin R)).mkQ :=
    LinearMap.exact_map_mkQ_range _
  have hex' : Function.Exact ((Matrix.mulVecLin R).baseChange S)
      ((LinearMap.range (Matrix.mulVecLin R)).mkQ.baseChange S) :=
    lTensor_exact S hex hsurj
  have hsurj' : Function.Surjective ((LinearMap.range (Matrix.mulVecLin R)).mkQ.baseChange S) :=
    LinearMap.lTensor_surjective S hsurj
  rw [projective_iff_of_exact _ _ hsurj' hex']
  let b₁ := Algebra.TensorProduct.basis S (Pi.basisFun A (Fin r))
  let b₀ := Algebra.TensorProduct.basis S (Pi.basisFun A (Fin m))
  have hR : LinearMap.toMatrix b₁ b₀ ((Matrix.mulVecLin R).baseChange S)
      = R.map (algebraMap A S) := by
    rw [LinearMap.toMatrix_baseChange]
    congr 1
    ext i j
    simp [LinearMap.toMatrix_apply, Pi.single_apply, Matrix.mulVec, dotProduct]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨LinearMap.toMatrix b₀ b₁ w, ?_⟩
    rw [← hR, Matrix.mul_assoc, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, hw]
  · rintro ⟨W, hW⟩
    refine ⟨Matrix.toLin b₀ b₁ W, ?_⟩
    apply (LinearMap.toMatrix b₁ b₀).injective
    rw [LinearMap.toMatrix_comp b₁ b₁ b₀, LinearMap.toMatrix_comp b₁ b₀ b₁,
      LinearMap.toMatrix_toLin, hR, ← Matrix.mul_assoc, hW]

/- English proof (translation)
Rewrite using `[projective_baseChange_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨W, hW⟩ choose W' hW' using fun i j => Ideal.Quotient.mk_surjective (W i j)`. Establish `hWW : (Matrix.of W').map (algebraMap A (A ⧸ Ideal.span {a})) = W`. Use extensionality with `i j`.

Conclude with `hW' i j`. Rewrite `hW` using `[← hWW, ← Matrix.map_mul, ← Matrix.map_mul]`. Establish `h : ∀ i j, ∃ z, z * a = (R * Matrix.of W' * R) i j - R i j`. Introduce `i j`. Rewrite using `[← Ideal.mem_span_singleton', ← Ideal.Quotient.eq]`.

Conclude with `congrFun (congrFun hW i) j`. Use `choose Z hZ using h`. Use `⟨Matrix.of W', Matrix.of Z, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`.

Take the linear combination `-(hZ i j)`. Introduce and unpack `⟨W, Z, h⟩`. Use `⟨W.map (algebraMap A _), ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, h]`. Use extensionality with `i j`.

Establish `: Ideal.Quotient.mk (Ideal.span {a}) a = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self a)`. Simplify using `[this]`.
-/
theorem projective_mod_iff (A : Type) [CommRing A] (m r : ℕ)
    (R : Matrix (Fin m) (Fin r) A) (a : A) :
    Module.Projective (A ⧸ Ideal.span {a}) ((A ⧸ Ideal.span {a}) ⊗[A]
        ((Fin m → A) ⧸ LinearMap.range (Matrix.mulVecLin R))) ↔
      ∃ (W : Matrix (Fin r) (Fin m) A) (Z : Matrix (Fin m) (Fin r) A),
        R * W * R = R + a • Z := by
  rw [projective_baseChange_iff]
  constructor
  · rintro ⟨W, hW⟩
    choose W' hW' using fun i j => Ideal.Quotient.mk_surjective (W i j)
    have hWW : (Matrix.of W').map (algebraMap A (A ⧸ Ideal.span {a})) = W := by
      ext i j; exact hW' i j
    rw [← hWW, ← Matrix.map_mul, ← Matrix.map_mul] at hW
    have h : ∀ i j, ∃ z, z * a = (R * Matrix.of W' * R) i j - R i j := by
      intro i j
      rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq]
      exact congrFun (congrFun hW i) j
    choose Z hZ using h
    refine ⟨Matrix.of W', Matrix.of Z, ?_⟩
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination -(hZ i j)
  · rintro ⟨W, Z, h⟩
    refine ⟨W.map (algebraMap A _), ?_⟩
    rw [← Matrix.map_mul, ← Matrix.map_mul, h]
    ext i j
    have : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self a)
    simp [this]

/- English proof (translation)
Take `⟨W, Z, hWZ⟩` from `(projective_mod_iff B m₁ r₁ R₁ a).1 h`. Use `⟨Set.range (fun p : Fin r₁ × Fin m₁ => W p.1 p.2) ∪ Set.range (fun p : Fin m₁ × Fin r₁ => Z p.1 p.2), (Set.finite_range _).union (Set.finite_range _), ?_⟩` and prove the remaining obligations. Introduce `A' _ g hg hT R' a' hR ha`. Establish `h1 : ∀ i j, ∃ x, g x = W i j` using `fun i j => hT (Or.inl ⟨(i, j), rfl⟩)`. Establish `h2 : ∀ i j, ∃ x, g x = Z i j` using `fun i j => hT (Or.inr ⟨(i, j), rfl⟩)`.

Use `choose W' hW' using h1`. Use `choose Z' hZ' using h2`. Establish `hW : (Matrix.of W').map g = W` using `by ext i j; exact hW' i j`. Rewrite using `[projective_mod_iff]`. Use `⟨Matrix.of W', Matrix.of Z', ?_⟩` and prove the remaining obligations.

Apply `Matrix.map_injective hg` to reduce the goal to its premises. Use `show (R' * Matrix.of W' * R').map g = (R' + a' • Matrix.of Z').map g`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hR, hW, hWZ, ← hR]`. Use extensionality with `i j`. Simplify using `[ha, hZ']`.
-/
theorem projective_coker_descends (B : Type) [CommRing B] (m₁ r₁ : ℕ)
    (R₁ : Matrix (Fin m₁) (Fin r₁) B) (a : B)
    (h : Module.Projective (B ⧸ Ideal.span {a}) ((B ⧸ Ideal.span {a}) ⊗[B]
      ((Fin m₁ → B) ⧸ LinearMap.range (Matrix.mulVecLin R₁)))) :
    ∃ T : Set B, T.Finite ∧ ∀ (A' : Type) [CommRing A'] (g : A' →+* B), Function.Injective g →
      T ⊆ Set.range g → ∀ (R₁' : Matrix (Fin m₁) (Fin r₁) A') (a' : A'), R₁'.map g = R₁ →
      g a' = a → Module.Projective (A' ⧸ Ideal.span {a'}) ((A' ⧸ Ideal.span {a'}) ⊗[A']
        ((Fin m₁ → A') ⧸ LinearMap.range (Matrix.mulVecLin R₁'))) := by
  obtain ⟨W, Z, hWZ⟩ := (projective_mod_iff B m₁ r₁ R₁ a).1 h
  refine ⟨Set.range (fun p : Fin r₁ × Fin m₁ => W p.1 p.2) ∪
    Set.range (fun p : Fin m₁ × Fin r₁ => Z p.1 p.2),
    (Set.finite_range _).union (Set.finite_range _), ?_⟩
  intro A' _ g hg hT R' a' hR ha
  have h1 : ∀ i j, ∃ x, g x = W i j := fun i j => hT (Or.inl ⟨(i, j), rfl⟩)
  have h2 : ∀ i j, ∃ x, g x = Z i j := fun i j => hT (Or.inr ⟨(i, j), rfl⟩)
  choose W' hW' using h1
  choose Z' hZ' using h2
  have hW : (Matrix.of W').map g = W := by ext i j; exact hW' i j
  rw [projective_mod_iff]
  refine ⟨Matrix.of W', Matrix.of Z', ?_⟩
  apply Matrix.map_injective hg
  show (R' * Matrix.of W' * R').map g = (R' + a' • Matrix.of Z').map g
  rw [Matrix.map_mul, Matrix.map_mul, hR, hW, hWZ, ← hR]
  ext i j
  simp [ha, hZ']

end GlobalTheory.CokerProj
