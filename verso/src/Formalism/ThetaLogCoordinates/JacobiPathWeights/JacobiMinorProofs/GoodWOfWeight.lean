import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.CorA3primeB
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LemmaA2indepOf
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.JacobiMinorProof
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.GenSpace
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace DominanceOrderLemmas

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl, fun _ => le_rfl⟩`.
-/
theorem domLe_refl {n : ℕ} (ν : Fin n → ℤ) : DomLe ν ν := ⟨rfl, fun _ => le_rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h1.1.trans h2.1, fun j => (h1.2 j).trans (h2.2 j)⟩`.
-/
theorem domLe_trans {n : ℕ} {a b c : Fin n → ℤ} (h1 : DomLe a b) (h2 : DomLe b c) : DomLe a c :=
  ⟨h1.1.trans h2.1, fun j => (h1.2 j).trans (h2.2 j)⟩

/- English proof (translation)
Introduce `x hx`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hGi` using `(Submodule.mem_iInf _).mp hG x.1`. Rewrite `hGi` using `[if_neg (not_lt.mpr hlt), mem_weightedHomogeneousSubmodule]`.

Take `⟨e, he, hex⟩` from `(MvPolynomial.mem_vars x).mp hx`. Establish `h0` using `hGi (mem_support_iff.mp he)`. Establish `hpos : 0 < e x` using `Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hex)`. Rewrite `h0` using `[Finsupp.weight_apply, Finsupp.sum]`. Establish `hle` using `Finset.single_le_sum (f := fun y => e y • (if y.1 = x.1 then 1 else 0 : ℕ)) (fun _ _ => Nat.zero_le _) hex`.

Simplify using `only [if_true, smul_eq_mul, mul_ite, mul_one, mul_zero] at hle h0`. Use linear arithmetic over natural numbers and integers.
-/
theorem vars_of_polB {R : Type*} [CommRing R] {n N : ℕ} {B : ℕ → ℕ} {G : MvPolynomial (ℕ × Fin n) R}
    (hG : G ∈ polB R n N B) : ∀ x ∈ G.vars, x.1 < N := by
  intro x hx
  by_contra hlt
  push_neg at hlt
  have hGi := (Submodule.mem_iInf _).mp hG x.1
  rw [if_neg (not_lt.mpr hlt), mem_weightedHomogeneousSubmodule] at hGi
  obtain ⟨e, he, hex⟩ := (MvPolynomial.mem_vars x).mp hx
  have h0 := hGi (mem_support_iff.mp he)
  have hpos : 0 < e x := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hex)
  rw [Finsupp.weight_apply, Finsupp.sum] at h0
  have hle := Finset.single_le_sum (f := fun y => e y • (if y.1 = x.1 then 1 else 0 : ℕ))
    (fun _ _ => Nat.zero_le _) hex
  simp only [if_true, smul_eq_mul, mul_ite, mul_one, mul_zero] at hle h0
  omega

/- English proof (translation)
Unfold `actAll`. Rewrite using `[aeval_X]`. Apply the tactic sequence `split_ifs <;> simp [Matrix.vecMul, dotProduct]`.
-/
theorem actAll_X {L : Type*} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (g gi : Matrix (Fin n) (Fin n) L)
    (i : ℕ) (a : Fin n) :
    actAll isVec g gi (X (i, a)) =
      if isVec i then ∑ b, X (i, b) * C (g b a) else ∑ b, X (i, b) * C (gi a b) := by
  unfold actAll
  rw [aeval_X]
  split_ifs <;> simp [Matrix.vecMul, dotProduct]

/- English proof (translation)
Introduce `y hy`. Rewrite `hy` using `[actAll_X]`. Apply the tactic sequence `split_ifs at hy <;>`. Take `⟨b, -, hb⟩` from `Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hy)`. Establish `h'` using `MvPolynomial.vars_mul _ _ hb`.

Rewrite `h'` using `[Finset.mem_union, vars_X, vars_C]`. Simplify using `only [Finset.mem_singleton, Finset.notMem_empty, or_false] at h'`. Rewrite using `[h']`.
-/
theorem vars_actX {L : Type*} [CommRing L] [Nontrivial L] {n : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) (x : ℕ × Fin n) :
    ∀ y ∈ (actAll isVec g gi (X x)).vars, y.1 = x.1 := by
  intro y hy
  rw [actAll_X] at hy
  split_ifs at hy <;>
  · obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hy)
    have h' := MvPolynomial.vars_mul _ _ hb
    rw [Finset.mem_union, vars_X, vars_C] at h'
    simp only [Finset.mem_singleton, Finset.notMem_empty, or_false] at h'
    rw [h']

/- English proof (translation)
Introduce `y hy`. Establish `heq : actAll isVec g gi P = bind₁ (fun x => actAll isVec g gi (X x)) P`. Simplify using `only [actAll, bind₁, aeval_X]`. Rewrite `hy` using `[heq]`. Take `⟨x, hx, hyx⟩` from `Finset.mem_biUnion.mp (MvPolynomial.vars_bind₁ _ _ hy)`.

Rewrite using `[vars_actX isVec g gi x y hyx]`. Conclude with `hv x hx`.
-/
theorem vars_act {L : Type*} [CommRing L] [Nontrivial L] {n N : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) {P : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ P.vars, x.1 < N) :
    ∀ y ∈ (actAll isVec g gi P).vars, y.1 < N := by
  intro y hy
  have heq : actAll isVec g gi P = bind₁ (fun x => actAll isVec g gi (X x)) P := by
    simp only [actAll, bind₁, aeval_X]
  rw [heq] at hy
  obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_bind₁ _ _ hy)
  rw [vars_actX isVec g gi x y hyx]
  exact hv x hx

/- English proof (translation)
Establish `h` using `MvPolynomial.hom_congr_vars (f₁ := ((rename (Sum.inl : ℕ × Fin n → ℕ × Fin n ⊕ Empty)).comp (actAll isVec g gi)).toRingHom) (f₂ := ((sharpHom (ζ := Empty) isVec {j : ℕ | j < N} g gi).comp (rename (Sum.inl : ℕ × Fin n → ℕ × Fin n ⊕ Empty))).toRingHom) (p₁ := P) (p₂ := P) ?_ ?_ rfl`. Simplify using `using h`. Conclude with `RingHom.ext fun a => by simp`. Introduce and unpack `⟨i, a⟩ hi _`. Establish `hiN : i < N` using `hv _ hi`.

Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, rename_X, actAll_X]`. Simplify using `only [sharpHom, aeval_X, Set.mem_setOf_eq, hiN, if_true]`. Apply the tactic sequence `split_ifs <;> simp [Matrix.vecMul, dotProduct]`.
-/
private lemma rename_actAll_eq_sharpHom {L : Type*} [CommRing L] {n N : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) (P : MvPolynomial (ℕ × Fin n) L) (hv : ∀ x ∈ P.vars, x.1 < N) :
    rename (Sum.inl : ℕ × Fin n → ℕ × Fin n ⊕ Empty) (actAll isVec g gi P) =
      sharpHom (ζ := Empty) isVec {j : ℕ | j < N} g gi (rename Sum.inl P) := by
  have h := MvPolynomial.hom_congr_vars
    (f₁ := ((rename (Sum.inl : ℕ × Fin n → ℕ × Fin n ⊕ Empty)).comp (actAll isVec g gi)).toRingHom)
    (f₂ := ((sharpHom (ζ := Empty) isVec {j : ℕ | j < N} g gi).comp
      (rename (Sum.inl : ℕ × Fin n → ℕ × Fin n ⊕ Empty))).toRingHom) (p₁ := P) (p₂ := P) ?_ ?_ rfl
  · simpa using h
  · exact RingHom.ext fun a => by simp
  · rintro ⟨i, a⟩ hi _
    have hiN : i < N := hv _ hi
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, rename_X, actAll_X]
    simp only [sharpHom, aeval_X, Set.mem_setOf_eq, hiN, if_true]
    split_ifs <;> simp [Matrix.vecMul, dotProduct]

/- English proof (translation)
Rewrite using `[GS.genPoint_eq]`. Establish `ha` using `GS.act_eq (ζ := Empty) (isVec := isVec) (S := {j : ℕ | j < N}) (genMat k n) GS.genMat_isUnit (rename Sum.inl G)`. Use `Eq.trans ?_ ha` and prove the remaining obligations. Rewrite using `[map_rename]`. Conclude with `rename_actAll_eq_sharpHom isVec _ _ _ (fun x hx => hv x (vars_map _ _ hx))`.
-/
theorem bridge (k : Type) [Field k] {n N : ℕ} (isVec : ℕ → Bool) {G : MvPolynomial (ℕ × Fin n) k}
    (hv : ∀ x ∈ G.vars, x.1 < N) :
    rename Sum.inl (actAll isVec (genMat k n) (genMat k n)⁻¹ (map (algebraMap k (GenField k n)) G)) =
      genPoint (ζ := Empty) isVec {j : ℕ | j < N} (rename Sum.inl G) := by
  rw [GS.genPoint_eq]
  have ha := GS.act_eq (ζ := Empty) (isVec := isVec) (S := {j : ℕ | j < N}) (genMat k n)
    GS.genMat_isUnit (rename Sum.inl G)
  refine Eq.trans ?_ ha
  rw [map_rename]
  exact rename_actAll_eq_sharpHom isVec _ _ _ (fun x hx => hv x (vars_map _ _ hx))

end DominanceOrderLemmas

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
