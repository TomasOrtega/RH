import Mathlib

namespace GlobalTheory

open scoped ComplexConjugate

/- English proof (translation)
Set `cd : InnerProductSpace.Core ℂ S` to `{ inner := fun x y => Bf x y conj_inner_symm := fun x y => by show starRingEnd ℂ (Bf y x) = Bf x y`. Rewrite using `[hsym x y, Complex.conj_conj]`. Use `re_inner_nonneg := fun x => by`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality.

Simplify using the standard rewrite rules. Conclude with `(hpos x hx).le`. Use `add_left := fun x y z => by show Bf (x + y) z = Bf x z + Bf y z`. Simplify using the standard rewrite rules. Use `smul_left := fun x y r => by show Bf (r • x) y = starRingEnd ℂ r * Bf x y`.

Simplify using the standard rewrite rules. Use `definite := fun x hx => by`. Assume the negation of the conclusion as `h`. Use `hpos x h` as an intermediate fact. Establish `hx' : Bf x x = 0` using `hx`.

Rewrite `this` using `[hx']`. Simplify using `at this }`. Use `letI : NormedAddCommGroup S := cd.toNormedAddCommGroup`. Use `letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore cd.toCore`. Establish `hin : ∀ x y : S, (inner ℂ x y : ℂ) = Bf x y` using `fun _ _ => rfl`.

Set `ob` to `stdOrthonormalBasis ℂ S`. Establish `horth : ∀ i j, Bf (ob i) (ob j) = if i = j then 1 else 0`. Introduce `i j`. Rewrite using `[← hin]`. Conclude with `orthonormal_iff_ite.mp ob.orthonormal i j`.

Use `⟨Module.finrank ℂ S, ob, horth, ?_, ?_⟩` and prove the remaining obligations. Use `ob.toBasis.span_eq` as an intermediate fact. Rewrite `this` using `[OrthonormalBasis.coe_toBasis]`. Then use the resulting hypothesis. Introduce `T hT`. Use `⟨fun j => ?_, ?_⟩` and prove the remaining obligations.

Use `(ob.sum_repr' (T (ob j))).symm` as an intermediate fact. Simplify `this` using `only [hin]`. Rewrite using `[Matrix.mem_unitaryGroup_iff']`. Use extensionality with `j l`. Simplify using `only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]`.

Establish `h1 : ∀ i, star (Bf (ob i) (T (ob j))) = Bf (T (ob j)) (ob i)`. Introduce `i`. Rewrite using `[hsym (ob i) (T (ob j))]`. Both sides reduce to the same expression. Simplify using `only [h1]`.

Use `ob.sum_inner_mul_inner (T (ob j)) (T (ob l))` as an intermediate fact. Simplify using `only [hin] at this`. Rewrite using `[this, hT, horth]`.
-/
theorem hermitian_onb_unitary (Wt : Type) [AddCommGroup Wt] [Module ℂ Wt] (S : Submodule ℂ Wt)
    [FiniteDimensional ℂ S] (Bf : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ)
    (hsym : ∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) (hpos : ∀ x, x ≠ 0 → 0 < (Bf x x).re) :
    ∃ (m : ℕ) (b : Fin m → S), (∀ i j, Bf (b i) (b j) = if i = j then 1 else 0) ∧
      Submodule.span ℂ (Set.range b) = ⊤ ∧
      ∀ T : S →ₗ[ℂ] S, (∀ x y, Bf (T x) (T y) = Bf x y) →
        (∀ j, T (b j) = ∑ i, Bf (b i) (T (b j)) • b i) ∧
        Matrix.of (fun i j => Bf (b i) (T (b j))) ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  let cd : InnerProductSpace.Core ℂ S :=
    { inner := fun x y => Bf x y
      conj_inner_symm := fun x y => by
        show starRingEnd ℂ (Bf y x) = Bf x y
        rw [hsym x y, Complex.conj_conj]
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · subst hx; simp
        · exact (hpos x hx).le
      add_left := fun x y z => by
        show Bf (x + y) z = Bf x z + Bf y z
        simp
      smul_left := fun x y r => by
        show Bf (r • x) y = starRingEnd ℂ r * Bf x y
        simp
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        have hx' : Bf x x = 0 := hx
        rw [hx'] at this
        simp at this }
  letI : NormedAddCommGroup S := cd.toNormedAddCommGroup
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore cd.toCore
  have hin : ∀ x y : S, (inner ℂ x y : ℂ) = Bf x y := fun _ _ => rfl
  let ob := stdOrthonormalBasis ℂ S
  have horth : ∀ i j, Bf (ob i) (ob j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hin]
    exact orthonormal_iff_ite.mp ob.orthonormal i j
  refine ⟨Module.finrank ℂ S, ob, horth, ?_, ?_⟩
  · have := ob.toBasis.span_eq
    rwa [OrthonormalBasis.coe_toBasis] at this
  · intro T hT
    refine ⟨fun j => ?_, ?_⟩
    · have := (ob.sum_repr' (T (ob j))).symm
      simpa only [hin] using this
    · rw [Matrix.mem_unitaryGroup_iff']
      ext j l
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
      have h1 : ∀ i, star (Bf (ob i) (T (ob j))) = Bf (T (ob j)) (ob i) := by
        intro i
        rw [hsym (ob i) (T (ob j))]; rfl
      simp only [h1]
      have := ob.sum_inner_mul_inner (T (ob j)) (T (ob l))
      simp only [hin] at this
      rw [this, hT, horth]

end GlobalTheory
