import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ArchFinSplit

section Idem
variable {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {ι : Type} [Fintype ι] [DecidableEq ι]

def pr (e : A) (M : Matrix ι ι R) : Matrix ι ι R := e • M + (1 - e) • (1 : Matrix ι ι R)

/- English proof (translation)
Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he.eq, sub_self]`. Establish `h2 : (1 - e) * e = 0` using `by rw [mul_comm, h1]`. Establish `h3 : (1 - e) * (1 - e) = 1 - e` using `he.one_sub.eq`. Simplify using `only [pr, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, Matrix.mul_one, Matrix.one_mul, he.eq, h1, h2, h3, zero_smul, add_zero, zero_add]`.
-/
theorem pr_mul {e : A} (he : IsIdempotentElem e) (M N : Matrix ι ι R) : pr e M * pr e N = pr e (M * N) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  simp only [pr, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, Matrix.mul_one,
    Matrix.one_mul, he.eq, h1, h2, h3, zero_smul, add_zero, zero_add]

/- English proof (translation)
Simplify using `[pr, sub_smul]`.
-/
theorem pr_one (e : A) : pr e (1 : Matrix ι ι R) = 1 := by
  simp [pr, sub_smul]

/- English proof (translation)
Simplify using `only [pr, sub_smul, one_smul, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem pr_sub_one (e : A) (M : Matrix ι ι R) : pr e M - 1 = e • (M - 1) := by
  simp only [pr, sub_smul, one_smul, smul_sub]; abel

/- English proof (translation)
Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he.eq, sub_self]`. Establish `h2 : (1 - e) * e = 0` using `by rw [mul_comm, h1]`. Establish `h3 : (1 - e) * (1 - e) = 1 - e` using `he.one_sub.eq`. Simplify using `only [pr, sub_sub_cancel, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, Matrix.mul_one, Matrix.one_mul, he.eq, h1, h2, h3, zero_smul, add_zero, zero_add]`. Rewrite using `[← add_smul, sub_add_cancel, one_smul]`.
-/
theorem pr_mul_pr_compl {e : A} (he : IsIdempotentElem e) (M : Matrix ι ι R) : pr e M * pr (1 - e) M = M := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  simp only [pr, sub_sub_cancel, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add,
    Matrix.mul_one, Matrix.one_mul, he.eq, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

def prU {e : A} (he : IsIdempotentElem e) (g : GL ι R) : GL ι R where
  val := pr e (g : Matrix ι ι R)
  inv := pr e ((g⁻¹ : GL ι R) : Matrix ι ι R)
  val_inv := by rw [pr_mul he, Units.mul_inv, pr_one]
  inv_val := by rw [pr_mul he, Units.inv_mul, pr_one]

/- English proof (translation)
Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he.eq, sub_self]`. Establish `h2 : (1 - e) * e = 0` using `by rw [mul_comm, h1]`. Establish `h3 : (1 - e) * (1 - e) = 1 - e` using `he.one_sub.eq`. Establish `hg' : (g : Matrix ι ι R)ᵀ * J * (g : Matrix ι ι R).map c = J` using `hg`. Use `show (pr e (g : Matrix ι ι R))ᵀ * J * (pr e (g : Matrix ι ι R)).map c = J`.

Establish `hm : (pr e (g : Matrix ι ι R)).map c = pr e ((g : Matrix ι ι R).map c)`. Apply the tactic sequence `ext i j; simp [pr, Matrix.one_apply, map_add, map_smul]; split_ifs <;> simp`. Rewrite using `[hm]`. Simplify using `only [pr, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, Matrix.mul_one, Matrix.one_mul, he.eq, h1, h2, h3, zero_smul, add_zero, zero_add, hg']`. Rewrite using `[← add_smul, add_sub_cancel, one_smul]`.
-/
theorem prU_mem {e : A} (he : IsIdempotentElem e) (c : R →ₐ[A] R) (J : Matrix ι ι R) (g : GL ι R)
    (hg : g ∈ UG c J) : prU he g ∈ UG c J := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := he.one_sub.eq
  have hg' : (g : Matrix ι ι R)ᵀ * J * (g : Matrix ι ι R).map c = J := hg
  show (pr e (g : Matrix ι ι R))ᵀ * J * (pr e (g : Matrix ι ι R)).map c = J
  have hm : (pr e (g : Matrix ι ι R)).map c = pr e ((g : Matrix ι ι R).map c) := by
    ext i j; simp [pr, Matrix.one_apply, map_add, map_smul]; split_ifs <;> simp
  rw [hm]
  simp only [pr, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, Matrix.mul_one, Matrix.one_mul, he.eq, h1, h2, h3, zero_smul,
    add_zero, zero_add, hg']
  rw [← add_smul, add_sub_cancel, one_smul]

end Idem
end GlobalTheory.ArchFinSplit

open GlobalTheory.ArchFinSplit in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n W g`. Set `a : AF F` to `((1 : Ainf F), (0 : Af F))`. Establish `ha : IsIdempotentElem a`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : Ainf F) * 1 = 1`.

Rewrite using `[mul_one]`. Express the relevant statement in the definitionally equal form `(0 : Af F) * 0 = 0`. Rewrite using `[mul_zero]`. Set `gi : UA σ W.J` to `⟨prU ha g.1, prU_mem ha _ _ g.1 g.2⟩`. Set `gf : UA σ W.J` to `⟨prU ha.one_sub g.1, prU_mem ha.one_sub _ _ g.1 g.2⟩`.

Use `⟨gi, ?_, gf, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Establish `hu1 : u.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu`. Use `show u • (pr a (g.1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0`. Rewrite using `[pr_sub_one, smul_smul]`.

Establish `: u * a = 0`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.1 * 1 = 0`. Rewrite using `[hu1, zero_mul]`. Express the relevant statement in the definitionally equal form `u.2 * 0 = 0`.

Rewrite using `[mul_zero]`. Rewrite using `[this, zero_smul]`. Introduce `u hu show u • (pr (1 - a) (g.1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0`. Rewrite using `[pr_sub_one, smul_smul]`. Establish `: u * (1 - a) = 0`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.1 * (1 - 1) = 0`. Rewrite using `[sub_self, mul_zero]`. Establish `hu2 : u.2 = 0` using `hu`. Express the relevant statement in the definitionally equal form `u.2 * (1 - 0) = 0`.

Rewrite using `[hu2, zero_mul]`. Rewrite using `[this, zero_smul]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext show (g.1 : Matrix (Fin n) (Fin n) (AE F E)) = pr a (g.1 : Matrix _ _ _) * pr (1 - a) (g.1 : Matrix _ _ _)` to reduce the goal to its premises. Rewrite using `[pr_mul_pr_compl ha]`.
-/
theorem GlobalTheory.ArchFinSplit.split_arch_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (W : Spc F E n) (g : UA σ W.J), ∃ gi ∈ UAt σ W (evI F), ∃ gf ∈ UAt σ W (fun u : AF F => u.2), g = gi * gf := by
  intro F E _ _ _ _ _ σ n W g
  let a : AF F := ((1 : Ainf F), (0 : Af F))
  have ha : IsIdempotentElem a := by
    refine Prod.ext ?_ ?_
    · change (1 : Ainf F) * 1 = 1; rw [mul_one]
    · change (0 : Af F) * 0 = 0; rw [mul_zero]
  let gi : UA σ W.J := ⟨prU ha g.1, prU_mem ha _ _ g.1 g.2⟩
  let gf : UA σ W.J := ⟨prU ha.one_sub g.1, prU_mem ha.one_sub _ _ g.1 g.2⟩
  refine ⟨gi, ?_, gf, ?_, ?_⟩
  · intro u hu
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
    show u • (pr a (g.1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
    rw [pr_sub_one, smul_smul]
    have : u * a = 0 := by
      refine Prod.ext ?_ ?_
      · change u.1 * 1 = 0; rw [hu1, zero_mul]
      · change u.2 * 0 = 0; rw [mul_zero]
    rw [this, zero_smul]
  · intro u hu
    show u • (pr (1 - a) (g.1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
    rw [pr_sub_one, smul_smul]
    have : u * (1 - a) = 0 := by
      refine Prod.ext ?_ ?_
      · change u.1 * (1 - 1) = 0; rw [sub_self, mul_zero]
      · have hu2 : u.2 = 0 := hu
        change u.2 * (1 - 0) = 0; rw [hu2, zero_mul]
    rw [this, zero_smul]
  · apply Subtype.ext; apply Units.ext
    show (g.1 : Matrix (Fin n) (Fin n) (AE F E)) = pr a (g.1 : Matrix _ _ _) * pr (1 - a) (g.1 : Matrix _ _ _)
    rw [pr_mul_pr_compl ha]
