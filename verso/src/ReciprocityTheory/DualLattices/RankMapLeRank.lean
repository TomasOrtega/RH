import Mathlib

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.RankA

variable {S : Type} [CommRing S]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Pi.single y 1, by ext x; simp⟩`.
-/
lemma col_mem_range {m n : Type} [Fintype n] [DecidableEq n] (A : Matrix m n S) (y : n) :
    (fun x => A x y) ∈ LinearMap.range A.mulVecLin :=
  ⟨Pi.single y 1, by ext x; simp⟩

/- English proof (translation)
Use extensionality with `x y`. Establish `h` using `congrArg (fun z : M => (z : m → S) x) (b.sum_repr ⟨fun x => A x y, hA y⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`.

Rewrite using `[← h]`. Conclude with `Finset.sum_congr rfl fun l _ => mul_comm _ _`.
-/
lemma factor_of_basis {m n ι : Type} [Fintype ι] (A : Matrix m n S)
    (M : Submodule S (m → S)) (b : Module.Basis ι S M) (hA : ∀ y, (fun x => A x y) ∈ M) :
    A = (Matrix.of fun x l => (b l : m → S) x) *
      Matrix.of fun l y => b.repr ⟨fun x => A x y, hA y⟩ l := by
  ext x y
  have h := congrArg (fun z : M => (z : m → S) x) (b.sum_repr ⟨fun x => A x y, hA y⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/- English proof (translation)
Take `⟨N, hN, P, Q, hPQ⟩ : ∃ N, N = Module.finrank S (LinearMap.range A.mulVecLin) ∧ ∃ (P : Matrix m (Fin N) S) (Q : Matrix (Fin N) n S), A = P * Q` from `⟨_, rfl, _, _, factor_of_basis A _ (Module.finBasis S _) (col_mem_range A)⟩`. Rewrite using `[← hN]`. Establish `h : A.map f = P.map f * Q.map f` using `by rw [hPQ, Matrix.map_mul]`. Rewrite using `[h]`. Conclude with `(Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))`.
-/
lemma rank_map_le [StrongRankCondition S] {K : Type} [Field K] (f : S →+* K) {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n S) [Module.Free S (LinearMap.range A.mulVecLin)]
    [Module.Finite S (LinearMap.range A.mulVecLin)] :
    (A.map f).rank ≤ Module.finrank S (LinearMap.range A.mulVecLin) := by
  obtain ⟨N, hN, P, Q, hPQ⟩ : ∃ N, N = Module.finrank S (LinearMap.range A.mulVecLin) ∧
      ∃ (P : Matrix m (Fin N) S) (Q : Matrix (Fin N) n S), A = P * Q :=
    ⟨_, rfl, _, _, factor_of_basis A _ (Module.finBasis S _) (col_mem_range A)⟩
  rw [← hN]
  have h : A.map f = P.map f * Q.map f := by rw [hPQ, Matrix.map_mul]
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))

/- English proof (translation)
Set `M : m → Submodule S (ι → S)` to `fun i => LinearMap.range (e i).mulVecLin`. Establish `hmem : ∀ i j (y : M j), e i *ᵥ (y : ι → S) = if i = j then (y : ι → S) else 0`. Introduce `i j y`. Take `⟨z, hz⟩` from `y.2`. Simplify using `only [Matrix.mulVecLin_apply] at hz`.

Rewrite using `[← hz, mulVec_mulVec, horth]`. Use `split_ifs with h`. Substitute `h` using the available equality. Both sides reduce to the same expression. Conclude with `zero_mulVec _`.

Establish `hsum' : ∀ x : ι → S, ∑ i, e i *ᵥ x = x`. Introduce `x`. Rewrite using `[← Matrix.sum_mulVec, hsum, one_mulVec]`. Set `E : (ι → S) ≃ₗ[S] ((i : m) → M i)` to `{ toFun := fun x i => ⟨e i *ᵥ x, x, rfl⟩ map_add' := fun x y => by ext i : 1; apply Subtype.ext; simp [mulVec_add] map_smul' := fun c x => by ext i : 1; apply Subtype.ext; simp [mulVec_smul] invFun := fun y => ∑ i, (y i : ι → S) left_inv := fun x => hsum' x right_inv := fun y => …`. Use extensionality with `i : 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Matrix.mulVec_sum, hmem, Finset.sum_ite_eq, Finset.mem_univ, if_true] }`. Establish `h1` using `E.finrank_eq`. Rewrite `h1` using `[Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype]`. Conclude with `h1.symm`.
-/
lemma sum_finrank {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    [StrongRankCondition S] (e : m → Matrix ι ι S)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hsum : ∑ i, e i = 1)
    [∀ i, Module.Free S (LinearMap.range (e i).mulVecLin)]
    [∀ i, Module.Finite S (LinearMap.range (e i).mulVecLin)] :
    ∑ i, Module.finrank S (LinearMap.range (e i).mulVecLin) = Fintype.card ι := by
  let M : m → Submodule S (ι → S) := fun i => LinearMap.range (e i).mulVecLin
  have hmem : ∀ i j (y : M j), e i *ᵥ (y : ι → S) = if i = j then (y : ι → S) else 0 := by
    intro i j y
    obtain ⟨z, hz⟩ := y.2
    simp only [Matrix.mulVecLin_apply] at hz
    rw [← hz, mulVec_mulVec, horth]
    split_ifs with h
    · subst h; rfl
    · exact zero_mulVec _
  have hsum' : ∀ x : ι → S, ∑ i, e i *ᵥ x = x := by
    intro x
    rw [← Matrix.sum_mulVec, hsum, one_mulVec]
  let E : (ι → S) ≃ₗ[S] ((i : m) → M i) :=
    { toFun := fun x i => ⟨e i *ᵥ x, x, rfl⟩
      map_add' := fun x y => by ext i : 1; apply Subtype.ext; simp [mulVec_add]
      map_smul' := fun c x => by ext i : 1; apply Subtype.ext; simp [mulVec_smul]
      invFun := fun y => ∑ i, (y i : ι → S)
      left_inv := fun x => hsum' x
      right_inv := fun y => by
        ext i : 1; apply Subtype.ext
        simp only [Matrix.mulVec_sum, hmem, Finset.sum_ite_eq, Finset.mem_univ, if_true] }
  have h1 := E.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype] at h1
  exact h1.symm

/- English proof (translation)
Set `s : (ι → S) →ₗ[S] LinearMap.range e.mulVecLin` to `e.mulVecLin.rangeRestrict`. Establish `hs : s ∘ₗ (LinearMap.range e.mulVecLin).subtype = LinearMap.id`. Use `LinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Take `⟨_, y, rfl⟩` from `x`. Simplify using `[s, Matrix.mulVec_mulVec, he]`.

Establish `: Module.Projective S (LinearMap.range e.mulVecLin)` using `Module.Projective.of_split (LinearMap.range e.mulVecLin).subtype s hs`. Establish `: Module.Finite S (LinearMap.range e.mulVecLin)` using `Module.Finite.of_surjective s (LinearMap.surjective_rangeRestrict _)`. Conclude with `⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩`.
-/
lemma free_range_idem [IsLocalRing S] {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι S)
    (he : e * e = e) :
    Module.Free S (LinearMap.range e.mulVecLin) ∧ Module.Finite S (LinearMap.range e.mulVecLin) := by
  let s : (ι → S) →ₗ[S] LinearMap.range e.mulVecLin := e.mulVecLin.rangeRestrict
  have hs : s ∘ₗ (LinearMap.range e.mulVecLin).subtype = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨_, y, rfl⟩ := x
    simp [s, Matrix.mulVec_mulVec, he]
  have : Module.Projective S (LinearMap.range e.mulVecLin) :=
    Module.Projective.of_split (LinearMap.range e.mulVecLin).subtype s hs
  have : Module.Finite S (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_surjective s (LinearMap.surjective_rangeRestrict _)
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

end ReciprocityTheory.PGsh.Up.RankA
