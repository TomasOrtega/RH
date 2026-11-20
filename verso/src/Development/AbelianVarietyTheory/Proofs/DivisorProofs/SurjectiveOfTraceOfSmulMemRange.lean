import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrIsUnit
open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleCoker

/- English proof (translation)
Establish `htf : ∀ b : B, s • b = 0 → b = 0`. Introduce `b hb`. Set `e` to `Module.Free.chooseBasis S B`. Apply `e.repr.injective` to reduce the goal to its premises. Use extensionality with `i`.

Use `congrArg (fun x => e.repr x i) hb` as an intermediate fact. Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this`. Simplify using `using (mul_eq_zero.mp this).resolve_left hs`. Set `L : A →ₗ[S] B` to `φ.toLinearMap`. Establish `hL : Function.Injective L` using `hφ`.

Set `E : A ≃ₗ[S] LinearMap.range L` to `LinearEquiv.ofInjective L hL`. Set `g : B →ₗ[S] LinearMap.range L` to `{ toFun := fun b => ⟨s • b, by obtain ⟨a, ha⟩ := hcok b; exact ⟨a, ha⟩⟩ map_add' := fun x y => by ext; simp [smul_add] map_smul' := fun c x => by ext; simp [smul_comm s c] }`. Establish `hg : Function.Injective g`. Introduce `x y hxy`. Establish `: s • x = s • y` using `congrArg Subtype.val hxy`.

Establish `h0 : s • (x - y) = 0` using `by rw [smul_sub, this, sub_self]`. Conclude with `sub_eq_zero.mp (htf _ h0)`. Establish `h1 : Module.finrank S A ≤ Module.finrank S B` using `LinearMap.finrank_le_finrank_of_injective hL`. Establish `h2 : Module.finrank S B ≤ Module.finrank S A` using `LinearMap.finrank_le_finrank_of_injective (f := E.symm.toLinearMap ∘ₗ g) (E.symm.injective.comp hg)`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex S A) = Fintype.card (Module.Free.ChooseBasisIndex S B)`.

Rewrite using `[← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex]`. Use linear arithmetic over natural numbers and integers. Set `eι` to `Fintype.equivOfCardEq hcard`. Set `a` to `(Module.Free.chooseBasis S A).reindex eι`. Set `bB` to `Module.Free.chooseBasis S B`.

Set `v : Module.Free.ChooseBasisIndex S B → B` to `fun i => φ (a i)`. Establish `htm : Algebra.traceMatrix S v = Algebra.traceMatrix S a`. Use extensionality with `i j`. Simplify using `only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, v, ← map_mul, htr]`. Establish `hdv : Algebra.discr S v = Algebra.discr S a`.

Rewrite using `[Algebra.discr_def, Algebra.discr_def, htm]`. Set `P` to `bB.toMatrix v`. Establish `hv : Matrix.vecMul (⇑bB) (P.map (algebraMap S B)) = v`. Use function extensionality and compare the values at `j`. Rewrite using `[← bB.sum_toMatrix_smul_self v j]`.

Simplify using `[Matrix.vecMul, dotProduct, P, Algebra.smul_def, mul_comm]`. Establish `hdisc : Algebra.discr S v = P.det ^ 2 * Algebra.discr S bB`. Rewrite using `[← hv, Algebra.discr_of_matrix_vecMul]`. Establish `hu : IsUnit (P.det ^ 2 * Algebra.discr S bB)`. Rewrite using `[← hdisc, hdv]`.

Conclude with `discr_isUnit S A a`. Establish `hPu : IsUnit P.det` using `(isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_left hu)`. Establish `hbd : IsUnit (bB.det v)` using `by rw [Module.Basis.det_apply]; exact hPu`. Establish `hspan` using `((Module.Basis.is_basis_iff_det bB).mpr hbd).2`. Introduce `y`.

Establish `hy : y ∈ Submodule.span S (Set.range v)` using `by rw [hspan]; trivial`. Establish `hle : Submodule.span S (Set.range v) ≤ LinearMap.range L`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨a i, rfl⟩`.

Take `⟨x, hx⟩` from `hle hy`. Conclude with `⟨x, hx⟩`.
-/
theorem surjective_of_trace_of_smul_mem_range (S A B : Type) [CommRing S] [IsLocalRing S]
    [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A]
    [Algebra.Etale S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B]
    [Algebra.Etale S B] (φ : A →ₐ[S] B) (hφ : Function.Injective φ) (s : S) (hs : s ≠ 0)
    (hcok : ∀ b : B, s • b ∈ φ.range)
    (htr : ∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x) : Function.Surjective φ := by
  classical
  have htf : ∀ b : B, s • b = 0 → b = 0 := by
    intro b hb
    let e := Module.Free.chooseBasis S B
    apply e.repr.injective
    ext i
    have := congrArg (fun x => e.repr x i) hb
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
    simpa using (mul_eq_zero.mp this).resolve_left hs
  let L : A →ₗ[S] B := φ.toLinearMap
  have hL : Function.Injective L := hφ
  let E : A ≃ₗ[S] LinearMap.range L := LinearEquiv.ofInjective L hL
  let g : B →ₗ[S] LinearMap.range L :=
    { toFun := fun b => ⟨s • b, by obtain ⟨a, ha⟩ := hcok b; exact ⟨a, ha⟩⟩
      map_add' := fun x y => by ext; simp [smul_add]
      map_smul' := fun c x => by ext; simp [smul_comm s c] }
  have hg : Function.Injective g := by
    intro x y hxy
    have : s • x = s • y := congrArg Subtype.val hxy
    have h0 : s • (x - y) = 0 := by rw [smul_sub, this, sub_self]
    exact sub_eq_zero.mp (htf _ h0)
  have h1 : Module.finrank S A ≤ Module.finrank S B :=
    LinearMap.finrank_le_finrank_of_injective hL
  have h2 : Module.finrank S B ≤ Module.finrank S A :=
    LinearMap.finrank_le_finrank_of_injective (f := E.symm.toLinearMap ∘ₗ g)
      (E.symm.injective.comp hg)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex S A) =
      Fintype.card (Module.Free.ChooseBasisIndex S B) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex]
    omega
  let eι := Fintype.equivOfCardEq hcard
  let a := (Module.Free.chooseBasis S A).reindex eι
  let bB := Module.Free.chooseBasis S B
  let v : Module.Free.ChooseBasisIndex S B → B := fun i => φ (a i)
  have htm : Algebra.traceMatrix S v = Algebra.traceMatrix S a := by
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, v, ← map_mul, htr]
  have hdv : Algebra.discr S v = Algebra.discr S a := by
    rw [Algebra.discr_def, Algebra.discr_def, htm]
  let P := bB.toMatrix v
  have hv : Matrix.vecMul (⇑bB) (P.map (algebraMap S B)) = v := by
    funext j
    rw [← bB.sum_toMatrix_smul_self v j]
    simp [Matrix.vecMul, dotProduct, P, Algebra.smul_def, mul_comm]
  have hdisc : Algebra.discr S v = P.det ^ 2 * Algebra.discr S bB := by
    rw [← hv, Algebra.discr_of_matrix_vecMul]
  have hu : IsUnit (P.det ^ 2 * Algebra.discr S bB) := by
    rw [← hdisc, hdv]; exact discr_isUnit S A a
  have hPu : IsUnit P.det := (isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_left hu)
  have hbd : IsUnit (bB.det v) := by rw [Module.Basis.det_apply]; exact hPu
  have hspan := ((Module.Basis.is_basis_iff_det bB).mpr hbd).2
  intro y
  have hy : y ∈ Submodule.span S (Set.range v) := by rw [hspan]; trivial
  have hle : Submodule.span S (Set.range v) ≤ LinearMap.range L := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact ⟨a i, rfl⟩
  obtain ⟨x, hx⟩ := hle hy
  exact ⟨x, hx⟩

end GlobalTheory.EtaleCoker
