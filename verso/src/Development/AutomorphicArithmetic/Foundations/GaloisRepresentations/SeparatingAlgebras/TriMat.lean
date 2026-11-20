import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
open UpperTheory.Gal.Gen

/- English proof (translation)
Establish `hv : v = ∑ x, v x • (Pi.single x 1 : X → k)`. Use extensionality with `y`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_rhs => rw [hv]`. Simplify using `[map_sum, Finsupp.finset_sum_apply, mul_comm]`.
-/
private lemma repr_sum_mul {k X ι : Type*} [Field k] [Fintype X] [DecidableEq X]
    (b : Module.Basis ι k (X → k)) (v : X → k) (i : ι) :
    ∑ x, b.repr (Pi.single x 1) i * v x = b.repr v i := by
  have hv : v = ∑ x, v x • (Pi.single x 1 : X → k) := by
    ext y
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  simp [map_sum, Finsupp.finset_sum_apply, mul_comm]

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, Matrix.mul_apply, ← repr_sum_mul b]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
private lemma conj_apply {k X ι : Type*} [Field k] [Fintype X] [DecidableEq X] [Fintype ι]
    (b : Module.Basis ι k (X → k)) (M : Matrix X X k) (i j : ι) :
    ((Matrix.of fun i x => b.repr (Pi.single x 1) i : Matrix ι X k) * M *
      (Matrix.of fun x j => b j x : Matrix X ι k)) i j = b.repr (M.mulVec (b j)) i := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, ← repr_sum_mul b]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/- English proof (translation)
Introduce `hF l _ H _ hH X _ _ ρ`. Set `ρ' : Representation (ZMod l) H (X → ZMod l)` to `((Matrix.toLinAlgEquiv' (R := ZMod l) (n := X)).toAlgHom.toRingHom.toMonoidHom).comp (((Int.castRingHom (ZMod l)).mapMatrix (m := X)).toMonoidHom.comp ρ)`. Establish `hρ' : ∀ h v, ρ' h v = ((ρ h).map (Int.castRingHom (ZMod l))).mulVec v`. Introduce `h v`. Both sides reduce to the same expression.

Take `⟨b₀, hb₀⟩` from `hF l H hH (X → ZMod l) ρ'`. Establish `hcard : Module.finrank (ZMod l) (X → ZMod l) = Fintype.card X` using `Module.finrank_fintype_fun_eq_card _`. Set `e : Fin (Module.finrank (ZMod l) (X → ZMod l)) ≃ Fin (Fintype.card X)` to `finCongr hcard`. Set `b` to `b₀.reindex e`. Establish `hb : ∀ h i j, j ≤ i → b.repr (ρ' h (b j) - b j) i = 0`.

Introduce `h i j hij`. Use `hb₀ h (e.symm i) (e.symm j) (by simpa [e] using hij)` as an intermediate fact. Simplify `this` using `[b]`. Set `Q : Matrix (Fin (Fintype.card X)) X ℤ` to `fun i x => ((b.repr (Pi.single x 1) i).val : ℤ)`. Set `P : Matrix X (Fin (Fintype.card X)) ℤ` to `fun x j => ((b j x).val : ℤ)`.

Use `⟨Q, P, fun h i j hij => ?_⟩` and prove the remaining obligations. Apply `(ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1` to reduce the goal to its premises. Establish `hQ : Q.map (Int.castRingHom (ZMod l)) = (Matrix.of fun i x => b.repr (Pi.single x 1) i : Matrix _ X (ZMod l))`. Use extensionality with `i x`. Express the relevant statement in the definitionally equal form `((((b.repr (Pi.single x 1) i).val : ℤ)) : ZMod l) = b.repr (Pi.single x 1) i`.

Rewrite using `[Int.cast_natCast, ZMod.natCast_zmod_val]`. Establish `hP : P.map (Int.castRingHom (ZMod l)) = (Matrix.of fun x j => b j x : Matrix X _ (ZMod l))`. Use extensionality with `x j`. Express the relevant statement in the definitionally equal form `((((b j x).val : ℤ)) : ZMod l) = b j x`. Rewrite using `[Int.cast_natCast, ZMod.natCast_zmod_val]`.

Establish `hc : (((Q * ρ h * P) i j : ℤ) : ZMod l) = b.repr (ρ' h (b j)) i`. Establish `h1 : (((Q * ρ h * P) i j : ℤ) : ZMod l) = ((Q * ρ h * P).map (Int.castRingHom (ZMod l))) i j` using `rfl`. Rewrite using `[h1, Matrix.map_mul, Matrix.map_mul, hQ, hP, conj_apply, hρ']`. Establish `hd` using `hb h i j hij`. Rewrite `hd` using `[map_sub, Finsupp.sub_apply, sub_eq_zero, Module.Basis.repr_self, Finsupp.single_apply]`.

Rewrite using `[Int.cast_sub, hc, hd]`. Distinguish the cases in `hij' : i = j`. Substitute `hij'` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij', Ne.symm hij']`.
-/
theorem UpperTheory.Gal.Gen.triMat_pf :
    UpperTheory.Gal.Gen.Flag → UpperTheory.Gal.Gen.TriMat := by
  intro hF l _ H _ hH X _ _ ρ
  let ρ' : Representation (ZMod l) H (X → ZMod l) :=
    ((Matrix.toLinAlgEquiv' (R := ZMod l) (n := X)).toAlgHom.toRingHom.toMonoidHom).comp
      (((Int.castRingHom (ZMod l)).mapMatrix (m := X)).toMonoidHom.comp ρ)
  have hρ' : ∀ h v, ρ' h v = ((ρ h).map (Int.castRingHom (ZMod l))).mulVec v := by
    intro h v
    rfl
  obtain ⟨b₀, hb₀⟩ := hF l H hH (X → ZMod l) ρ'
  have hcard : Module.finrank (ZMod l) (X → ZMod l) = Fintype.card X :=
    Module.finrank_fintype_fun_eq_card _
  let e : Fin (Module.finrank (ZMod l) (X → ZMod l)) ≃ Fin (Fintype.card X) := finCongr hcard
  let b := b₀.reindex e
  have hb : ∀ h i j, j ≤ i → b.repr (ρ' h (b j) - b j) i = 0 := by
    intro h i j hij
    have := hb₀ h (e.symm i) (e.symm j) (by simpa [e] using hij)
    simpa [b] using this
  let Q : Matrix (Fin (Fintype.card X)) X ℤ := fun i x => ((b.repr (Pi.single x 1) i).val : ℤ)
  let P : Matrix X (Fin (Fintype.card X)) ℤ := fun x j => ((b j x).val : ℤ)
  refine ⟨Q, P, fun h i j hij => ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1
  have hQ : Q.map (Int.castRingHom (ZMod l)) =
      (Matrix.of fun i x => b.repr (Pi.single x 1) i : Matrix _ X (ZMod l)) := by
    ext i x
    change ((((b.repr (Pi.single x 1) i).val : ℤ)) : ZMod l) = b.repr (Pi.single x 1) i
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hP : P.map (Int.castRingHom (ZMod l)) =
      (Matrix.of fun x j => b j x : Matrix X _ (ZMod l)) := by
    ext x j
    change ((((b j x).val : ℤ)) : ZMod l) = b j x
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hc : (((Q * ρ h * P) i j : ℤ) : ZMod l) = b.repr (ρ' h (b j)) i := by
    have h1 : (((Q * ρ h * P) i j : ℤ) : ZMod l) =
        ((Q * ρ h * P).map (Int.castRingHom (ZMod l))) i j := rfl
    rw [h1, Matrix.map_mul, Matrix.map_mul, hQ, hP, conj_apply, hρ']
  have hd := hb h i j hij
  rw [map_sub, Finsupp.sub_apply, sub_eq_zero, Module.Basis.repr_self, Finsupp.single_apply] at hd
  rw [Int.cast_sub, hc, hd]
  by_cases hij' : i = j
  · subst hij'
    simp
  · simp [hij', Ne.symm hij']
