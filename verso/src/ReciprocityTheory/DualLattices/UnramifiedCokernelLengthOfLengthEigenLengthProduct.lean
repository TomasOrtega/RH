import ReciprocityTheory.DualLattices.EigenLengthFrobeniusStatement
import ReciprocityTheory.DualLattices.FrobEqOfLe
import ReciprocityTheory.DualLattices.StdJForm
import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Unram

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨a, ha⟩` from `U.distinct _ _ h`. Rewrite `ha` using `[U.conj (U.cj i) a, U.conj i (σ a), hS.invol a, sub_self, map_zero, map_zero]`. Conclude with `zero_ne_one ha`.
-/
private lemma cj_cj_dual_lattices (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) : U.cj (U.cj i) = i := by
  by_contra h
  obtain ⟨a, ha⟩ := U.distinct _ _ h
  rw [U.conj (U.cj i) a, U.conj i (σ a), hS.invol a, sub_self, map_zero, map_zero] at ha
  exact zero_ne_one ha

/- English proof (translation)
Use `hS.integers.isUnit_of_one ?_ hx` and prove the remaining obligations. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Rewrite `hx` using `[h0, map_zero]`. Conclude with `zero_ne_one hx`.
-/
private lemma isUnit_of_valuation_eq_one' (hS : HodgeTateSetting p v R O σ cp) {x : R} (hx : v (algebraMap R C x) = 1) :
    IsUnit x := by
  refine hS.integers.isUnit_of_one ?_ hx
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, map_zero] at hx
  exact zero_ne_one hx

/- English proof (translation)
Establish `hinv : ∀ a, ((H.ρ a).map (algebraMap ℤ_[p] R))ᵀ * H.E.map (algebraMap ℤ_[p] R) = H.E.map (algebraMap ℤ_[p] R) * (H.ρ (σ a)).map (algebraMap ℤ_[p] R)`. Introduce `a`. Rewrite using `[← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H.E_equivariant a]`. Establish `key : ∀ a, U.sg k a • ((U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j) = U.sg (U.cj j) a • ((U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j)`. Introduce `a`.

Establish `h1 : (U.εT k)ᵀ * ((H.ρ a).map (algebraMap ℤ_[p] R))ᵀ = U.sg k a • (U.εT k)ᵀ`. Rewrite using `[← Matrix.transpose_mul, U.εT_eig a k, Matrix.transpose_smul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.smul_mul, Matrix.smul_mul]`. Use `_ = (U.εT k)ᵀ * ((H.ρ a).map (algebraMap ℤ_[p] R))ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j := by rw [h1]`.

Use `_ = (U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * ((H.ρ (σ a)).map (algebraMap ℤ_[p] R) * U.εT j) := by`. Rewrite using `[Matrix.mul_assoc ((U.εT k)ᵀ), hinv a]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = U.sg (U.cj j) a • ((U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j) := by`. Rewrite using `[U.εT_eig (σ a) j, ← U.conj j a, Matrix.mul_smul]`.

Take `⟨a, ha⟩` from `U.distinct k (U.cj j) (Ne.symm hkj)`. Establish `hu` using `isUnit_of_valuation_eq_one' hS ha`. Establish `h2` using `key a`. Rewrite `h2` using `[← sub_eq_zero, ← sub_smul]`. Conclude with `hu.smul_eq_zero.mp h2`.
-/
private lemma E_block_zero (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (k j : Fin U.m) (hkj : U.cj j ≠ k) :
    (U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j = 0 := by
  have hinv : ∀ a, ((H.ρ a).map (algebraMap ℤ_[p] R))ᵀ * H.E.map (algebraMap ℤ_[p] R) =
      H.E.map (algebraMap ℤ_[p] R) * (H.ρ (σ a)).map (algebraMap ℤ_[p] R) := by
    intro a
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H.E_equivariant a]
  have key : ∀ a, U.sg k a • ((U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j) =
      U.sg (U.cj j) a • ((U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j) := by
    intro a
    have h1 : (U.εT k)ᵀ * ((H.ρ a).map (algebraMap ℤ_[p] R))ᵀ = U.sg k a • (U.εT k)ᵀ := by
      rw [← Matrix.transpose_mul, U.εT_eig a k, Matrix.transpose_smul]
    calc U.sg k a • ((U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j)
        = (U.sg k a • (U.εT k)ᵀ) * H.E.map (algebraMap ℤ_[p] R) * U.εT j := by
          rw [Matrix.smul_mul, Matrix.smul_mul]
      _ = (U.εT k)ᵀ * ((H.ρ a).map (algebraMap ℤ_[p] R))ᵀ * H.E.map (algebraMap ℤ_[p] R) *
            U.εT j := by rw [h1]
      _ = (U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) *
            ((H.ρ (σ a)).map (algebraMap ℤ_[p] R) * U.εT j) := by
          rw [Matrix.mul_assoc ((U.εT k)ᵀ), hinv a]
          simp only [Matrix.mul_assoc]
      _ = U.sg (U.cj j) a • ((U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j) := by
          rw [U.εT_eig (σ a) j, ← U.conj j a, Matrix.mul_smul]
  obtain ⟨a, ha⟩ := U.distinct k (U.cj j) (Ne.symm hkj)
  have hu := isUnit_of_valuation_eq_one' hS ha
  have h2 := key a
  rw [← sub_eq_zero, ← sub_smul] at h2
  exact hu.smul_eq_zero.mp h2

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← U.εT_sum, Matrix.mul_sum]`. Use `_ = (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by`. Use `Finset.sum_eq_single (U.cj i) (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)` and prove the remaining obligations. Use `E_block_zero hS H U i b (fun h => hb ?_)` and prove the remaining obligations.

Rewrite using `[← h, cj_cj_dual_lattices hS U b]`. Use `_ = ∑ k, (U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by`. Use `symm`. Use `Finset.sum_eq_single i (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)` and prove the remaining obligations. Use `E_block_zero hS H U b (U.cj i) ?_` and prove the remaining obligations.

Rewrite using `[cj_cj_dual_lattices hS U i]`. Conclude with `Ne.symm hb`. Use `_ = (∑ k, U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by`. Rewrite using `[Matrix.transpose_sum, Matrix.sum_mul, Matrix.sum_mul]`. Use `_ = H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by`.

Rewrite using `[U.εT_sum, Matrix.transpose_one, Matrix.one_mul]`.
-/
lemma εT_E (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) :
    (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) = H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by
  calc (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R)
        = (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) * 1 := (Matrix.mul_one _).symm
    _ = ∑ j, (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT j := by
        rw [← U.εT_sum, Matrix.mul_sum]
    _ = (U.εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by
        refine Finset.sum_eq_single (U.cj i) (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
        refine E_block_zero hS H U i b (fun h => hb ?_)
        rw [← h, cj_cj_dual_lattices hS U b]
    _ = ∑ k, (U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by
        symm
        refine Finset.sum_eq_single i (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
        refine E_block_zero hS H U b (U.cj i) ?_
        rw [cj_cj_dual_lattices hS U i]
        exact Ne.symm hb
    _ = (∑ k, U.εT k)ᵀ * H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by
        rw [Matrix.transpose_sum, Matrix.sum_mul, Matrix.sum_mul]
    _ = H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i) := by
        rw [U.εT_sum, Matrix.transpose_one, Matrix.one_mul]

/- English proof (translation)
Establish `key : ∀ a, U.sg i a • ((U.εL k)ᵀ * H.Ht * U.εT i) = U.sg (U.cj k) a • ((U.εL k)ᵀ * H.Ht * U.εT i)`. Introduce `a`. Establish `h1 : (U.εL k)ᵀ * (H.ρL (σ a))ᵀ = U.sg (U.cj k) a • (U.εL k)ᵀ`. Rewrite using `[← Matrix.transpose_mul, U.εL_eig (σ a) k, Matrix.transpose_smul, ← U.conj k a]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[U.εT_eig a i, Matrix.mul_smul]`. Use `_ = (U.εL k)ᵀ * (H.Ht * (H.ρ a).map (algebraMap ℤ_[p] R)) * U.εT i := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (U.εL k)ᵀ * (H.ρL (σ a))ᵀ * H.Ht * U.εT i := by`. Rewrite using `[H.Ht_equivariant.1 a]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = U.sg (U.cj k) a • ((U.εL k)ᵀ * H.Ht * U.εT i) := by`. Rewrite using `[h1, Matrix.smul_mul, Matrix.smul_mul]`. Take `⟨a, ha⟩` from `U.distinct i (U.cj k) (Ne.symm hki)`. Establish `hu` using `isUnit_of_valuation_eq_one' hS ha`.

Establish `h2` using `key a`. Rewrite `h2` using `[← sub_eq_zero, ← sub_smul]`. Conclude with `hu.smul_eq_zero.mp h2`.
-/
private lemma epsL_transpose_mul_Ht_mul_epsT_eq_zero_of_ne (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (k i : Fin U.m) (hki : U.cj k ≠ i) :
    (U.εL k)ᵀ * H.Ht * U.εT i = 0 := by
  have key : ∀ a, U.sg i a • ((U.εL k)ᵀ * H.Ht * U.εT i) =
      U.sg (U.cj k) a • ((U.εL k)ᵀ * H.Ht * U.εT i) := by
    intro a
    have h1 : (U.εL k)ᵀ * (H.ρL (σ a))ᵀ = U.sg (U.cj k) a • (U.εL k)ᵀ := by
      rw [← Matrix.transpose_mul, U.εL_eig (σ a) k, Matrix.transpose_smul, ← U.conj k a]
    calc U.sg i a • ((U.εL k)ᵀ * H.Ht * U.εT i)
        = (U.εL k)ᵀ * H.Ht * ((H.ρ a).map (algebraMap ℤ_[p] R) * U.εT i) := by
          rw [U.εT_eig a i, Matrix.mul_smul]
      _ = (U.εL k)ᵀ * (H.Ht * (H.ρ a).map (algebraMap ℤ_[p] R)) * U.εT i := by
          simp only [Matrix.mul_assoc]
      _ = (U.εL k)ᵀ * (H.ρL (σ a))ᵀ * H.Ht * U.εT i := by
          rw [H.Ht_equivariant.1 a]
          simp only [Matrix.mul_assoc]
      _ = U.sg (U.cj k) a • ((U.εL k)ᵀ * H.Ht * U.εT i) := by
          rw [h1, Matrix.smul_mul, Matrix.smul_mul]
  obtain ⟨a, ha⟩ := U.distinct i (U.cj k) (Ne.symm hki)
  have hu := isUnit_of_valuation_eq_one' hS ha
  have h2 := key a
  rw [← sub_eq_zero, ← sub_smul] at h2
  exact hu.smul_eq_zero.mp h2

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.transpose_sum, Matrix.sum_mul, Matrix.sum_mul]`. Use `_ = (U.εL (U.cj i))ᵀ * H.Ht * U.εT i := by`. Use `Finset.sum_eq_single (U.cj i) (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)` and prove the remaining obligations. Use `epsL_transpose_mul_Ht_mul_epsT_eq_zero_of_ne hS H U b i (fun h => hb ?_)` and prove the remaining obligations.

Rewrite using `[← h, cj_cj_dual_lattices hS U b]`. Use `_ = ∑ j, (U.εL (U.cj i))ᵀ * H.Ht * U.εT j := by`. Use `symm`. Use `Finset.sum_eq_single i (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)` and prove the remaining obligations. Use `epsL_transpose_mul_Ht_mul_epsT_eq_zero_of_ne hS H U (U.cj i) b ?_` and prove the remaining obligations.

Rewrite using `[cj_cj_dual_lattices hS U i]`. Conclude with `Ne.symm hb`. Use `_ = (U.εL (U.cj i))ᵀ * H.Ht := by rw [← Matrix.mul_sum, U.εT_sum, Matrix.mul_one]`.
-/
lemma ht_εT (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) :
    H.Ht * U.εT i = (U.εL (U.cj i))ᵀ * H.Ht := by
  calc H.Ht * U.εT i = (1 : Matrix (Fin g) (Fin g) R) * H.Ht * U.εT i := by rw [Matrix.one_mul]
    _ = (∑ k, U.εL k)ᵀ * H.Ht * U.εT i := by rw [U.εL_sum, Matrix.transpose_one]
    _ = ∑ k, (U.εL k)ᵀ * H.Ht * U.εT i := by
        rw [Matrix.transpose_sum, Matrix.sum_mul, Matrix.sum_mul]
    _ = (U.εL (U.cj i))ᵀ * H.Ht * U.εT i := by
        refine Finset.sum_eq_single (U.cj i) (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
        refine epsL_transpose_mul_Ht_mul_epsT_eq_zero_of_ne hS H U b i (fun h => hb ?_)
        rw [← h, cj_cj_dual_lattices hS U b]
    _ = ∑ j, (U.εL (U.cj i))ᵀ * H.Ht * U.εT j := by
        symm
        refine Finset.sum_eq_single i (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
        refine epsL_transpose_mul_Ht_mul_epsT_eq_zero_of_ne hS H U (U.cj i) b ?_
        rw [cj_cj_dual_lattices hS U i]
        exact Ne.symm hb
    _ = (U.εL (U.cj i))ᵀ * H.Ht := by rw [← Matrix.mul_sum, U.εT_sum, Matrix.mul_one]

/- English proof (translation)
Use `haveI : Nontrivial R := (algebraMap R C).domain_nontrivial`. Establish `hproj : ∀ i j (w : Fin g → R), w ∈ LinearMap.range (Matrix.mulVecLin (U.εL j)) → Matrix.mulVecLin (U.εL i) w = if i = j then w else 0`. Introduce and unpack `i j w ⟨z, rfl⟩`. Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, U.εL_orth]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Both sides reduce to the same expression. Conclude with `Matrix.zero_mulVec z`. Set `F : (Fin g → R) →ₗ[R] ((i : Fin U.m) → LinearMap.range (Matrix.mulVecLin (U.εL i)))` to `LinearMap.pi fun i => (Matrix.mulVecLin (U.εL i)).rangeRestrict`. Set `G : ((i : Fin U.m) → LinearMap.range (Matrix.mulVecLin (U.εL i))) →ₗ[R] (Fin g → R)` to `∑ i, (LinearMap.range (Matrix.mulVecLin (U.εL i))).subtype ∘ₗ LinearMap.proj i`.

Establish `hG : ∀ y, G y = ∑ i, ((y i : LinearMap.range (Matrix.mulVecLin (U.εL i))) : Fin g → R)`. Introduce `y`. Simplify using `only [G, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval, Submodule.coe_subtype]`. Establish `hFG : F ∘ₗ G = LinearMap.id`. Use `LinearMap.ext fun y => funext fun i => Subtype.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Matrix.mulVecLin (U.εL i) (G y) = (y i : Fin g → R)`. Rewrite using `[hG, map_sum, Finset.sum_eq_single i]`. Rewrite using `[hproj i i _ (y i).2, if_pos rfl]`. Introduce `b _ hb`. Rewrite using `[hproj i b _ (y b).2, if_neg (Ne.symm hb)]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hGF : G ∘ₗ F = LinearMap.id`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `G (F x) = x`.

Rewrite using `[hG]`. Express the relevant statement in the definitionally equal form `∑ i, Matrix.mulVecLin (U.εL i) x = x`. Rewrite using `[← LinearMap.sum_apply, ← map_sum, U.εL_sum]`. Conclude with `Matrix.one_mulVec x`. Set `e : (Fin g → R) ≃ₗ[R] ((i : Fin U.m) → LinearMap.range (Matrix.mulVecLin (U.εL i)))` to `LinearEquiv.ofLinear F G hFG hGF`.

Use `haveI : ∀ i, Module.Free R (LinearMap.range (Matrix.mulVecLin (U.εL i))) := fun i => Module.Free.of_equiv (U.rank i).some.symm`. Use `haveI : ∀ i, Module.Finite R (LinearMap.range (Matrix.mulVecLin (U.εL i))) := fun i => Module.Finite.equiv (U.rank i).some.symm`. Establish `h1` using `e.finrank_eq`. Rewrite `h1` using `[Module.finrank_fin_fun, Module.finrank_pi_fintype]`. Use `(Finset.sum_congr rfl fun i _ => ?_).trans h1.symm` and prove the remaining obligations.

Rewrite using `[(U.rank i).some.finrank_eq, Module.finrank_fin_fun]`.
-/
lemma sum_r (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) : ∑ i, U.r i = g := by
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  have hproj : ∀ i j (w : Fin g → R), w ∈ LinearMap.range (Matrix.mulVecLin (U.εL j)) →
      Matrix.mulVecLin (U.εL i) w = if i = j then w else 0 := by
    rintro i j w ⟨z, rfl⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, U.εL_orth]
    split_ifs with h
    · subst h; rfl
    · exact Matrix.zero_mulVec z
  let F : (Fin g → R) →ₗ[R] ((i : Fin U.m) → LinearMap.range (Matrix.mulVecLin (U.εL i))) :=
    LinearMap.pi fun i => (Matrix.mulVecLin (U.εL i)).rangeRestrict
  let G : ((i : Fin U.m) → LinearMap.range (Matrix.mulVecLin (U.εL i))) →ₗ[R] (Fin g → R) :=
    ∑ i, (LinearMap.range (Matrix.mulVecLin (U.εL i))).subtype ∘ₗ LinearMap.proj i
  have hG : ∀ y, G y = ∑ i, ((y i : LinearMap.range (Matrix.mulVecLin (U.εL i))) : Fin g → R) := by
    intro y
    simp only [G, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.coe_proj,
      Function.eval, Submodule.coe_subtype]
  have hFG : F ∘ₗ G = LinearMap.id := by
    refine LinearMap.ext fun y => funext fun i => Subtype.ext ?_
    change Matrix.mulVecLin (U.εL i) (G y) = (y i : Fin g → R)
    rw [hG, map_sum, Finset.sum_eq_single i]
    · rw [hproj i i _ (y i).2, if_pos rfl]
    · intro b _ hb
      rw [hproj i b _ (y b).2, if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hGF : G ∘ₗ F = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    change G (F x) = x
    rw [hG]
    change ∑ i, Matrix.mulVecLin (U.εL i) x = x
    rw [← LinearMap.sum_apply, ← map_sum, U.εL_sum]
    exact Matrix.one_mulVec x
  let e : (Fin g → R) ≃ₗ[R] ((i : Fin U.m) → LinearMap.range (Matrix.mulVecLin (U.εL i))) :=
    LinearEquiv.ofLinear F G hFG hGF
  haveI : ∀ i, Module.Free R (LinearMap.range (Matrix.mulVecLin (U.εL i))) :=
    fun i => Module.Free.of_equiv (U.rank i).some.symm
  haveI : ∀ i, Module.Finite R (LinearMap.range (Matrix.mulVecLin (U.εL i))) :=
    fun i => Module.Finite.equiv (U.rank i).some.symm
  have h1 := e.finrank_eq
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype] at h1
  refine (Finset.sum_congr rfl fun i _ => ?_).trans h1.symm
  rw [(U.rank i).some.finrank_eq, Module.finrank_fin_fun]

end Unram

/- English proof (translation)
Establish `hq0 : 0 < q` using `lt_trans one_pos hq`. Establish `hqne : q ≠ 0` using `hq0.ne'`. Establish `hterm : ∀ n : ℕ, q ^ (-((n : ℝ) + 1)) = (q ^ (n + 1))⁻¹`. Introduce `n`. Rewrite using `[Real.rpow_neg hq0.le, show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]`.

Establish `hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, q ^ (-((n : ℝ) + 1)) * (r ((φ ^ (n + 1)) j) : ℝ) = y j - y ((φ ^ N) j) / q ^ N`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`.

Rewrite using `[Finset.sum_range_succ, ih, hterm, hy ((φ ^ N) j), pow_succ' φ N, Equiv.Perm.mul_apply]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hasSum_iff_tendsto_nat_of_nonneg (fun n => mul_nonneg (Real.rpow_nonneg hq0.le _) (Nat.cast_nonneg _))]`. Repeatedly rewrite using `[hpart]`.

Establish `hB : ∀ k, |y k| ≤ ∑ k, |y k|` using `fun k => Finset.single_le_sum (fun k _ => abs_nonneg (y k)) (Finset.mem_univ k)`. Establish `h0 : Filter.Tendsto (fun N : ℕ => y ((φ ^ N) j) / q ^ N) Filter.atTop (nhds 0)`. Establish `hlim : Filter.Tendsto (fun N : ℕ => (∑ k, |y k|) * (q ^ N)⁻¹) Filter.atTop (nhds 0)`. Simplify using `using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hq)).const_mul (∑ k, |y k|)`. Use `squeeze_zero_norm (fun N => ?_) hlim` and prove the remaining obligations.

Rewrite using `[Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hq0 N), div_eq_mul_inv]`. Conclude with `mul_le_mul_of_nonneg_right (hB _) (inv_nonneg.mpr (pow_pos hq0 N).le)`. Simplify using `using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => y j) Filter.atTop (nhds (y j))).sub h0`.
-/
private lemma hasSum_rpow_mul_of_frobenius_recursion {m : ℕ} (q : ℝ) (hq : 1 < q) (φ : Equiv.Perm (Fin m)) (r : Fin m → ℕ)
    (y : Fin m → ℝ) (hy : ∀ j, y j = (y (φ j) + r (φ j)) / q) (j : Fin m) :
    HasSum (fun n : ℕ => q ^ (-((n : ℝ) + 1)) * (r ((φ ^ (n + 1)) j) : ℝ)) (y j) := by
  have hq0 : 0 < q := lt_trans one_pos hq
  have hqne : q ≠ 0 := hq0.ne'
  have hterm : ∀ n : ℕ, q ^ (-((n : ℝ) + 1)) = (q ^ (n + 1))⁻¹ := by
    intro n
    rw [Real.rpow_neg hq0.le, show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, q ^ (-((n : ℝ) + 1)) * (r ((φ ^ (n + 1)) j) : ℝ) =
      y j - y ((φ ^ N) j) / q ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hterm, hy ((φ ^ N) j), pow_succ' φ N, Equiv.Perm.mul_apply]
      field_simp
      ring
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun n => mul_nonneg (Real.rpow_nonneg hq0.le _) (Nat.cast_nonneg _))]
  simp_rw [hpart]
  have hB : ∀ k, |y k| ≤ ∑ k, |y k| := fun k =>
    Finset.single_le_sum (fun k _ => abs_nonneg (y k)) (Finset.mem_univ k)
  have h0 : Filter.Tendsto (fun N : ℕ => y ((φ ^ N) j) / q ^ N) Filter.atTop (nhds 0) := by
    have hlim : Filter.Tendsto (fun N : ℕ => (∑ k, |y k|) * (q ^ N)⁻¹) Filter.atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hq)).const_mul
        (∑ k, |y k|)
    refine squeeze_zero_norm (fun N => ?_) hlim
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hq0 N), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hB _) (inv_nonneg.mpr (pow_pos hq0 N).le)
  simpa using
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => y j) Filter.atTop (nhds (y j))).sub h0

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U i V1 V2 hV1 hV2`. Establish `hR` using `hS.integers`. Establish `hpp : p.Prime` using `Fact.out`. Establish `hcj : ∀ j, U.cj (U.cj j) = j` using `cj_cj_dual_lattices hS U`. Establish `hE` using `εT_E hS H U`.

Establish `hHt` using `ht_εT hS H U`. Establish `hEu : IsUnit (H.E.map (algebraMap ℤ_[p] R)).det`. Establish `h` using `H.isUnit_det_E.map (algebraMap ℤ_[p] R)`. Rewrite `h` using `[RingHom.map_det]`. Conclude with `h`.

Establish `hcv : v (algebraMap R C cp) ≠ 0`. Introduce `h0`. Establish `h5` using `hS.cp_val`. Rewrite `h5` using `[h0, zero_pow (Nat.sub_pos_of_lt hpp.one_lt).ne']`. Conclude with `hS.p_ne h5.symm`.

Establish `hcp : cp ≠ 0`. Introduce `h0`. Apply `hcv` to reduce the goal to its premises. Rewrite using `[h0, map_zero, map_zero]`. Take `⟨hform, hcomm, hdet⟩` from `u1 R g U.m H.Ht H.Bt (H.E.map (algebraMap ℤ_[p] R)) cp U.εT U.εL U.cj hcj U.εT_orth U.εT_sum U.εL_orth U.εL_sum hHt hE H.form_eq_alt`.

Establish `hform' : (bt2 H U)ᵀ * H.Ht - H.Htᵀ * bt2 H U = cp • H.E.map (algebraMap ℤ_[p] R)` using `hform`. Establish `hcomm' : ∀ j, bt2 H U * U.εT j = U.εL j * bt2 H U` using `hcomm`. Establish `hdv : v (algebraMap R C (Matrix.fromRows H.Ht (bt2 H U)).det) = v (algebraMap R C cp) ^ g`. Establish `h1` using `congrArg (fun x => v (algebraMap R C x)) hdet`. Simplify using `only [map_pow, map_mul, hR.one_of_isUnit hEu, mul_one] at h1`.

Rewrite `h1` using `[pow_mul']`. Conclude with `(pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1`. Establish `hEx1 : ∀ j k, ∃ x, HasLen v R (cokE H.Ht U.εT U.εL j k) x` using `fun j k => hEx C v R hR g H.Ht (U.εL j) (U.εT k)`. Use `choose cc hcc using hEx1`. Establish `hL : ∀ j c₁ c₂, HasLen v R (cokE H.Ht U.εT U.εL j (U.cj j)) c₁ → HasLen v R (cokE H.Ht U.εT U.εL (U.cj j) j) c₂ → ∃ X : NNReal, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj j) X ∧ X * c₁ = v (algebraMap R C cp) ^ U.r j * c₂` using `fun j c₁ c₂ h1 h2 => hLen C v R hR g U.m H.Ht (bt2 H U) (H.E.map (algebraMap ℤ_[p] R)) cp hcp hEu hform' U.εT U.εL U.cj hcj U.εT_orth U.εT_sum U.εL_orth U.εL_sum hHt hcomm' hE j (U.r j) (U.rank j) c₁ c₂ h1 h2`.

Establish `hX : ∀ j, ∃ X : NNReal, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj j) X ∧ (j = i → X * V1 = v (algebraMap R C cp) ^ U.r j * V2)`. Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Take `⟨X, h1, h2⟩` from `hL j V1 V2 hV1 hV2`.

Conclude with `⟨X, h1, fun _ => h2⟩`. Take `⟨X, h1, _⟩` from `hL j (cc j (U.cj j)) (cc (U.cj j) j) (hcc _ _) (hcc _ _)`. Conclude with `⟨X, h1, fun h => absurd h hj⟩`. Use `choose X hXl hXe using hX`. Establish `hprod : ∏ j, X j = v (algebraMap R C cp) ^ g` using `(hTot C v R hR g U.m H.Ht (bt2 H U) U.εT U.εL U.cj hcj U.εT_orth U.εT_sum U.εL_orth U.εL_sum hHt hcomm' X hXl).trans hdv`.

Establish `hineq` using `hCore p g C v R O σ cp hp2 hS H U X hXl hprod`. Take `⟨a, ha_def⟩ : ∃ a : ℝ, a = (v (algebraMap R C (p : R)) : ℝ)` from `⟨_, rfl⟩`. Take `⟨c, hc_def⟩ : ∃ c : ℝ, c = (v (algebraMap R C cp) : ℝ)` from `⟨_, rfl⟩`. Establish `ha0 : 0 < a` using `by rw [ha_def]; exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hS.p_ne)`. Establish `ha1 : a < 1` using `by rw [ha_def]; exact_mod_cast hS.p_lt`.

Establish `hc0 : 0 < c` using `by rw [hc_def]; exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hcv)`. Establish `hL0 : Real.log a < 0` using `Real.log_neg ha0 ha1`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hpp.one_lt`. Establish `hXpos : ∀ j, 0 < (X j : ℝ)`. Introduce `j`.

Establish `h1 : ∏ j, X j ≠ 0` using `by rw [hprod]; exact pow_ne_zero _ hcv`. Conclude with `NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mp h1 j (Finset.mem_univ j)))`. Establish `hlogcv : ((p : ℝ) - 1) * Real.log c = Real.log a`. Establish `h` using `congrArg (fun x : NNReal => Real.log (x : ℝ)) hS.cp_val`. Simplify using `only [NNReal.coe_pow, Real.log_pow] at h`.

Rewrite `h` using `[Nat.cast_sub hpp.one_lt.le, Nat.cast_one]`. Rewrite using `[hc_def, ha_def]`. Conclude with `h`. Take `⟨y, hy_def⟩ : ∃ y : Fin U.m → ℝ, ∀ j, y j = Real.log (X j : ℝ) / Real.log a` from `⟨_, fun j => rfl⟩`. Establish `hlogX : ∀ j, Real.log (X j : ℝ) = y j * Real.log a` using `fun j => by`.

Rewrite using `[hy_def, div_mul_cancel₀ _ hL0.ne]`. Establish `hS1 : (∑ j, y j) * Real.log a = g * Real.log c`. Rewrite using `[Finset.sum_mul]`. Repeatedly rewrite using `[← hlogX]`. Rewrite using `[← Real.log_prod (fun j _ => (hXpos j).ne'), ← Real.log_pow]`.

Use `congr 1`. Rewrite using `[hc_def]`. Conclude with `hprod` after adjusting the coercions. Establish `hS2 : (∑ j, y j) * ((p : ℝ) - 1) = g`. Establish `h1 : (∑ j, y j) * ((p : ℝ) - 1) * Real.log a = g * Real.log a`.

Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = g * (((p : ℝ) - 1) * Real.log c) := by rw [hS1]; ring`. Use `_ = g * Real.log a := by rw [hlogcv]`. Conclude with `mul_right_cancel₀ hL0.ne h1`.

Establish `hI : ∀ j, y (U.φ j) + U.r (U.φ j) ≤ p * y j`. Introduce `j`. Establish `h2 : (X j : ℝ) ^ p ≤ (X (U.φ j) : ℝ) * a ^ U.r (U.φ j)`. Rewrite using `[ha_def]`. Conclude with `hineq j` after adjusting the coercions.

Establish `h3` using `Real.log_le_log (pow_pos (hXpos j) p) h2`. Rewrite `h3` using `[Real.log_pow, Real.log_mul (hXpos _).ne' (pow_pos ha0 _).ne', Real.log_pow, hlogX, hlogX]`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h4` using `mul_lt_mul_of_neg_right hc hL0`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr : ∑ j, (U.r j : ℝ) = g` using `by exact_mod_cast sum_r hS H U`. Establish `e1 : ∑ j, y (U.φ j) = ∑ j, y j` using `Equiv.sum_comp U.φ y`. Establish `e2 : ∑ j, (U.r (U.φ j) : ℝ) = ∑ j, (U.r j : ℝ)` using `Equiv.sum_comp U.φ (fun j => (U.r j : ℝ))`. Establish `hsumdiff : ∑ j, ((p : ℝ) * y j - (y (U.φ j) + U.r (U.φ j))) = 0`.

Rewrite using `[Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2, hr]`. Combine the linear relations using `[hS2]`. Establish `hEq : ∀ j, y j = (y (U.φ j) + U.r (U.φ j)) / p`. Introduce `j`. Establish `hnn : ∀ k ∈ Finset.univ, 0 ≤ (p : ℝ) * y k - (y (U.φ k) + U.r (U.φ k))` using `fun k _ => by linarith [hI k]`.

Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsumdiff j (Finset.mem_univ j)`. Establish `hp0 : (p : ℝ) ≠ 0` using `by positivity`. Rewrite using `[eq_div_iff hp0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfs : frobSum U i = y i`.

Unfold `frobSum`. Conclude with `(hasSum_rpow_mul_of_frobenius_recursion (p : ℝ) hp1 U.φ U.r y hEq i).tsum_eq`. Establish `hXi : (X i : ℝ) = a ^ (y i)`. Rewrite using `[Real.rpow_def_of_pos ha0, mul_comm, ← hlogX, Real.exp_log (hXpos i)]`. Establish `hp1' : (p : ℝ) - 1 ≠ 0` using `by linarith`.

Establish `hcpow : a ^ ((U.r i : ℝ) / ((p : ℝ) - 1)) = c ^ U.r i`. Rewrite using `[Real.rpow_def_of_pos ha0, ← hlogcv, ← Real.rpow_natCast, Real.rpow_def_of_pos hc0]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hXe' : (X i : ℝ) * V1 = c ^ U.r i * V2`.

Rewrite using `[hc_def]`. Conclude with `hXe i rfl` after adjusting the coercions. Rewrite using `[← ha_def, hfs, Real.rpow_sub ha0, ← hXi, hcpow, mul_div_assoc', eq_comm, div_eq_iff (hXpos i).ne']`. Combine the linear relations using `[hXe']`.
-/
theorem unramifiedCokernelLength_of_length_eigenLengthProduct (hLen : LenIdStatement) (hEx : LenExStatement) (hTot : EigenLengthProductStatement)
    (hCore : EigenLengthFrobeniusStatement) : UnramifiedCokernelLengthStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U i V1 V2 hV1 hV2
  have hR := hS.integers
  have hpp : p.Prime := Fact.out
  have hcj : ∀ j, U.cj (U.cj j) = j := cj_cj_dual_lattices hS U
  have hE := εT_E hS H U
  have hHt := ht_εT hS H U
  have hEu : IsUnit (H.E.map (algebraMap ℤ_[p] R)).det := by
    have h := H.isUnit_det_E.map (algebraMap ℤ_[p] R)
    rw [RingHom.map_det] at h
    exact h
  have hcv : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h5 := hS.cp_val
    rw [h0, zero_pow (Nat.sub_pos_of_lt hpp.one_lt).ne'] at h5
    exact hS.p_ne h5.symm
  have hcp : cp ≠ 0 := by
    intro h0
    apply hcv
    rw [h0, map_zero, map_zero]
  obtain ⟨hform, hcomm, hdet⟩ := u1 R g U.m H.Ht H.Bt (H.E.map (algebraMap ℤ_[p] R)) cp U.εT U.εL
    U.cj hcj U.εT_orth U.εT_sum U.εL_orth U.εL_sum hHt hE H.form_eq_alt
  have hform' : (bt2 H U)ᵀ * H.Ht - H.Htᵀ * bt2 H U = cp • H.E.map (algebraMap ℤ_[p] R) := hform
  have hcomm' : ∀ j, bt2 H U * U.εT j = U.εL j * bt2 H U := hcomm
  have hdv : v (algebraMap R C (Matrix.fromRows H.Ht (bt2 H U)).det) = v (algebraMap R C cp) ^ g := by
    have h1 := congrArg (fun x => v (algebraMap R C x)) hdet
    simp only [map_pow, map_mul, hR.one_of_isUnit hEu, mul_one] at h1
    rw [pow_mul'] at h1
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have hEx1 : ∀ j k, ∃ x, HasLen v R (cokE H.Ht U.εT U.εL j k) x := fun j k =>
    hEx C v R hR g H.Ht (U.εL j) (U.εT k)
  choose cc hcc using hEx1
  have hL : ∀ j c₁ c₂, HasLen v R (cokE H.Ht U.εT U.εL j (U.cj j)) c₁ →
      HasLen v R (cokE H.Ht U.εT U.εL (U.cj j) j) c₂ →
      ∃ X : NNReal, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj j) X ∧
        X * c₁ = v (algebraMap R C cp) ^ U.r j * c₂ := fun j c₁ c₂ h1 h2 =>
    hLen C v R hR g U.m H.Ht (bt2 H U) (H.E.map (algebraMap ℤ_[p] R)) cp hcp hEu hform' U.εT U.εL
      U.cj hcj U.εT_orth U.εT_sum U.εL_orth U.εL_sum hHt hcomm' hE j (U.r j) (U.rank j) c₁ c₂ h1 h2
  have hX : ∀ j, ∃ X : NNReal, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj j) X ∧
      (j = i → X * V1 = v (algebraMap R C cp) ^ U.r j * V2) := by
    intro j
    by_cases hj : j = i
    · subst hj
      obtain ⟨X, h1, h2⟩ := hL j V1 V2 hV1 hV2
      exact ⟨X, h1, fun _ => h2⟩
    · obtain ⟨X, h1, _⟩ := hL j (cc j (U.cj j)) (cc (U.cj j) j) (hcc _ _) (hcc _ _)
      exact ⟨X, h1, fun h => absurd h hj⟩
  choose X hXl hXe using hX
  have hprod : ∏ j, X j = v (algebraMap R C cp) ^ g :=
    (hTot C v R hR g U.m H.Ht (bt2 H U) U.εT U.εL U.cj hcj U.εT_orth U.εT_sum U.εL_orth U.εL_sum
      hHt hcomm' X hXl).trans hdv
  have hineq := hCore p g C v R O σ cp hp2 hS H U X hXl hprod
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = (v (algebraMap R C (p : R)) : ℝ) := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (v (algebraMap R C cp) : ℝ) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha_def]; exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hS.p_ne)
  have ha1 : a < 1 := by rw [ha_def]; exact_mod_cast hS.p_lt
  have hc0 : 0 < c := by rw [hc_def]; exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hcv)
  have hL0 : Real.log a < 0 := Real.log_neg ha0 ha1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hXpos : ∀ j, 0 < (X j : ℝ) := by
    intro j
    have h1 : ∏ j, X j ≠ 0 := by rw [hprod]; exact pow_ne_zero _ hcv
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mp h1 j (Finset.mem_univ j)))
  have hlogcv : ((p : ℝ) - 1) * Real.log c = Real.log a := by
    have h := congrArg (fun x : NNReal => Real.log (x : ℝ)) hS.cp_val
    simp only [NNReal.coe_pow, Real.log_pow] at h
    rw [Nat.cast_sub hpp.one_lt.le, Nat.cast_one] at h
    rw [hc_def, ha_def]
    exact h
  obtain ⟨y, hy_def⟩ : ∃ y : Fin U.m → ℝ, ∀ j, y j = Real.log (X j : ℝ) / Real.log a :=
    ⟨_, fun j => rfl⟩
  have hlogX : ∀ j, Real.log (X j : ℝ) = y j * Real.log a := fun j => by
    rw [hy_def, div_mul_cancel₀ _ hL0.ne]
  have hS1 : (∑ j, y j) * Real.log a = g * Real.log c := by
    rw [Finset.sum_mul]
    simp_rw [← hlogX]
    rw [← Real.log_prod (fun j _ => (hXpos j).ne'), ← Real.log_pow]
    congr 1
    rw [hc_def]
    exact_mod_cast hprod
  have hS2 : (∑ j, y j) * ((p : ℝ) - 1) = g := by
    have h1 : (∑ j, y j) * ((p : ℝ) - 1) * Real.log a = g * Real.log a := by
      calc (∑ j, y j) * ((p : ℝ) - 1) * Real.log a = ((∑ j, y j) * Real.log a) * ((p : ℝ) - 1) := by
            ring
        _ = g * (((p : ℝ) - 1) * Real.log c) := by rw [hS1]; ring
        _ = g * Real.log a := by rw [hlogcv]
    exact mul_right_cancel₀ hL0.ne h1
  have hI : ∀ j, y (U.φ j) + U.r (U.φ j) ≤ p * y j := by
    intro j
    have h2 : (X j : ℝ) ^ p ≤ (X (U.φ j) : ℝ) * a ^ U.r (U.φ j) := by
      rw [ha_def]
      exact_mod_cast hineq j
    have h3 := Real.log_le_log (pow_pos (hXpos j) p) h2
    rw [Real.log_pow, Real.log_mul (hXpos _).ne' (pow_pos ha0 _).ne', Real.log_pow, hlogX,
      hlogX] at h3
    by_contra hc
    push_neg at hc
    have h4 := mul_lt_mul_of_neg_right hc hL0
    linarith
  have hr : ∑ j, (U.r j : ℝ) = g := by exact_mod_cast sum_r hS H U
  have e1 : ∑ j, y (U.φ j) = ∑ j, y j := Equiv.sum_comp U.φ y
  have e2 : ∑ j, (U.r (U.φ j) : ℝ) = ∑ j, (U.r j : ℝ) := Equiv.sum_comp U.φ (fun j => (U.r j : ℝ))
  have hsumdiff : ∑ j, ((p : ℝ) * y j - (y (U.φ j) + U.r (U.φ j))) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2, hr]
    linarith [hS2]
  have hEq : ∀ j, y j = (y (U.φ j) + U.r (U.φ j)) / p := by
    intro j
    have hnn : ∀ k ∈ Finset.univ, 0 ≤ (p : ℝ) * y k - (y (U.φ k) + U.r (U.φ k)) :=
      fun k _ => by linarith [hI k]
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsumdiff j (Finset.mem_univ j)
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    rw [eq_div_iff hp0]
    linarith
  have hfs : frobSum U i = y i := by
    unfold frobSum
    exact (hasSum_rpow_mul_of_frobenius_recursion (p : ℝ) hp1 U.φ U.r y hEq i).tsum_eq
  have hXi : (X i : ℝ) = a ^ (y i) := by
    rw [Real.rpow_def_of_pos ha0, mul_comm, ← hlogX, Real.exp_log (hXpos i)]
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hcpow : a ^ ((U.r i : ℝ) / ((p : ℝ) - 1)) = c ^ U.r i := by
    rw [Real.rpow_def_of_pos ha0, ← hlogcv, ← Real.rpow_natCast, Real.rpow_def_of_pos hc0]
    congr 1
    field_simp
  have hXe' : (X i : ℝ) * V1 = c ^ U.r i * V2 := by
    rw [hc_def]
    exact_mod_cast hXe i rfl
  rw [← ha_def, hfs, Real.rpow_sub ha0, ← hXi, hcpow, mul_div_assoc', eq_comm,
    div_eq_iff (hXpos i).ne']
  linarith [hXe']

end ReciprocityTheory.PGsh.Up
