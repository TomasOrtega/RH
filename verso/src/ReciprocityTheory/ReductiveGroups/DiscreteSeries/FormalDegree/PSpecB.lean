import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Simplify using `[pmat, h]`.
-/
theorem pmat_eq_zero_of_eq {ε : Fin n → Bool} (z : PCoord ε → ℂ) {a b : Fin n} (h : ε a = ε b) :
    pmat z a b = 0 := by
  simp [pmat, h]

/- English proof (translation)
Establish `hU` using `((pmat_isHermitian z).eigenvectorUnitary).2`. Use `first`. Consider the case `exact Matrix.mem_unitaryGroup_iff'.mp hU`. Consider the case `exact Unitary.star_mul_self_of_mem hU`. Consider the case `exact unitary.star_mul_self_of_mem hU`.

Consider the case `simp`.
-/
private lemma pmat_eigenvectorUnitary_star_mul_self {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    star ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have hU := ((pmat_isHermitian z).eigenvectorUnitary).2
  first
  | exact Matrix.mem_unitaryGroup_iff'.mp hU
  | exact Unitary.star_mul_self_of_mem hU
  | exact unitary.star_mul_self_of_mem hU
  | simp

/- English proof (translation)
Use `conv_lhs => rw [(pmat_isHermitian z).spectral_theorem]`. Use `first`. Consider the case `rfl`. Consider the case `(congr 2; ext i j; simp [pev, Matrix.diagonal_apply])`. Consider the case `simp [pev, Function.comp_def]`.
-/
private lemma pmat_eq_eigenvectorUnitary_mul_diagonal_mul_star {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    pmat z = ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagonal (fun a => (pev z a : ℂ)) *
        star ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
  conv_lhs => rw [(pmat_isHermitian z).spectral_theorem]
  first
  | rfl
  | (congr 2; ext i j; simp [pev, Matrix.diagonal_apply])
  | simp [pev, Function.comp_def]

/- English proof (translation)
Establish `h` using `congrArg (fun M => M * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) (pmat_eq_eigenvectorUnitary_mul_diagonal_mul_star z)`. Rewrite using `[h, Matrix.mul_assoc, pmat_eigenvectorUnitary_star_mul_self, Matrix.mul_one]`.
-/
theorem pmat_mul_evU {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    pmat z * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        diagonal (fun a => (pev z a : ℂ)) := by
  have h := congrArg (fun M => M * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))
    (pmat_eq_eigenvectorUnitary_mul_diagonal_mul_star z)
  rw [h, Matrix.mul_assoc, pmat_eigenvectorUnitary_star_mul_self, Matrix.mul_one]

/- English proof (translation)
Establish `h` using `congrArg Neg.neg (pmat_eq_eigenvectorUnitary_mul_diagonal_mul_star z)`. Rewrite using `[h]`. Establish `hd : diagonal (fun a => ((-pev z a : ℝ) : ℂ)) = -diagonal (fun a => (pev z a : ℂ))`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [diagonal_apply, hij]`.

Rewrite using `[hd]`. Use `first`. Consider the case `rw [Matrix.mul_neg, Matrix.neg_mul]`. Consider the case `simp [Matrix.mul_neg, Matrix.neg_mul]`. Consider the case `noncomm_ring`.
-/
theorem neg_pmat_eq {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    -pmat z = ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        diagonal (fun a => ((-pev z a : ℝ) : ℂ)) *
        star ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
  have h := congrArg Neg.neg (pmat_eq_eigenvectorUnitary_mul_diagonal_mul_star z)
  rw [h]
  have hd : diagonal (fun a => ((-pev z a : ℝ) : ℂ)) = -diagonal (fun a => (pev z a : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [diagonal_apply, hij]
  rw [hd]
  first
  | rw [Matrix.mul_neg, Matrix.neg_mul]
  | simp [Matrix.mul_neg, Matrix.neg_mul]
  | noncomm_ring

/- English proof (translation)
Unfold `Jm`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases h : ε a <;> simp [h]`.
-/
theorem jm_mul_jm (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

/- English proof (translation)
Use extensionality with `a b`. Unfold `Jm`. Simplify using `only [diagonal_mul, mul_diagonal, Matrix.neg_apply]`. Distinguish the cases in `h : ε a = ε b`. Rewrite using `[pmat_eq_zero_of_eq z h]`.

Simplify using the standard rewrite rules. Apply the tactic sequence `rcases hA : ε a <;> rcases hB : ε b <;> simp_all`.
-/
theorem jm_conj_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) : Jm ε * (pmat z * Jm ε) = -pmat z := by
  ext a b
  unfold Jm
  simp only [diagonal_mul, mul_diagonal, Matrix.neg_apply]
  by_cases h : ε a = ε b
  · rw [pmat_eq_zero_of_eq z h]; simp
  · rcases hA : ε a <;> rcases hB : ε b <;> simp_all

/- English proof (translation)
Rewrite using `[Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, pmat_eigenvectorUnitary_star_mul_self, Matrix.one_mul]`.
-/
private lemma charpoly_eigenvectorUnitary_conj_eq {ε : Fin n → Bool} (z : PCoord ε → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * M *
      star ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).charpoly = M.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, pmat_eigenvectorUnitary_star_mul_self, Matrix.one_mul]

/- English proof (translation)
Establish `h1 : (diagonal d).charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i))`. Unfold `Matrix.charpoly`. Establish `hc : (diagonal d).charmatrix = diagonal (fun i => Polynomial.X - Polynomial.C (d i))`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij first` using the available equality. Consider the case `simp [Matrix.charmatrix_apply]`. Consider the case `simp [Matrix.charmatrix]`. Use `first`. Consider the case `simp [Matrix.charmatrix_apply, hij]`.

Consider the case `simp [Matrix.charmatrix, hij]`. Rewrite using `[hc, det_diagonal]`. Rewrite using `[h1, Finset.prod_eq_multiset_prod]`. Establish `hm : (univ.val.map fun i => Polynomial.X - Polynomial.C (d i)) = (univ.val.map d).map (fun a => Polynomial.X - Polynomial.C a)`. Rewrite using `[Multiset.map_map]`.

Both sides reduce to the same expression. Rewrite using `[hm, Polynomial.roots_multiset_prod_X_sub_C]`.
-/
private lemma charpoly_roots_diagonal (d : Fin n → ℂ) :
    (diagonal d).charpoly.roots = univ.val.map d := by
  have h1 : (diagonal d).charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i)) := by
    unfold Matrix.charpoly
    have hc : (diagonal d).charmatrix = diagonal (fun i => Polynomial.X - Polynomial.C (d i)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        first
        | simp [Matrix.charmatrix_apply]
        | simp [Matrix.charmatrix]
      · first
        | simp [Matrix.charmatrix_apply, hij]
        | simp [Matrix.charmatrix, hij]
    rw [hc, det_diagonal]
  rw [h1, Finset.prod_eq_multiset_prod]
  have hm : (univ.val.map fun i => Polynomial.X - Polynomial.C (d i)) =
      (univ.val.map d).map (fun a => Polynomial.X - Polynomial.C a) := by
    rw [Multiset.map_map]; rfl
  rw [hm, Polynomial.roots_multiset_prod_X_sub_C]

/- English proof (translation)
Establish `hcp : (-pmat z).charpoly = (pmat z).charpoly`. Rewrite using `[← jm_conj_pmat z, Matrix.charpoly_mul_comm, Matrix.mul_assoc, jm_mul_jm, Matrix.mul_one]`. Establish `h1 : (pmat z).charpoly = (diagonal fun a => (pev z a : ℂ)).charpoly` using `by conv_lhs => rw [pmat_eq_eigenvectorUnitary_mul_diagonal_mul_star z]`. Conclude with `charpoly_eigenvectorUnitary_conj_eq z _`. Establish `h2 : (-pmat z).charpoly = (diagonal fun a => ((-pev z a : ℝ) : ℂ)).charpoly`.

Rewrite using `[neg_pmat_eq z]`. Conclude with `charpoly_eigenvectorUnitary_conj_eq z _`. Establish `h3` using `congrArg Polynomial.roots (h2.symm.trans (hcp.trans h1))`. Rewrite `h3` using `[charpoly_roots_diagonal, charpoly_roots_diagonal]`. Establish `h4 : (univ.val.map fun a => -pev z a).map (fun x : ℝ => (x : ℂ)) = (univ.val.map (pev z)).map (fun x : ℝ => (x : ℂ))` using `by first`.

Consider the case `(rw [Multiset.map_map, Multiset.map_map]; exact h3)`. Consider the case `simpa [Multiset.map_map, Function.comp_def] using h3`. Conclude with `Multiset.map_injective Complex.ofReal_injective h4`.
-/
theorem pev_neg_multiset {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    Multiset.map (fun a => -pev z a) univ.val = Multiset.map (pev z) univ.val := by
  have hcp : (-pmat z).charpoly = (pmat z).charpoly := by
    rw [← jm_conj_pmat z, Matrix.charpoly_mul_comm, Matrix.mul_assoc, jm_mul_jm, Matrix.mul_one]
  have h1 : (pmat z).charpoly = (diagonal fun a => (pev z a : ℂ)).charpoly := by
    conv_lhs => rw [pmat_eq_eigenvectorUnitary_mul_diagonal_mul_star z]
    exact charpoly_eigenvectorUnitary_conj_eq z _
  have h2 : (-pmat z).charpoly = (diagonal fun a => ((-pev z a : ℝ) : ℂ)).charpoly := by
    rw [neg_pmat_eq z]
    exact charpoly_eigenvectorUnitary_conj_eq z _
  have h3 := congrArg Polynomial.roots (h2.symm.trans (hcp.trans h1))
  rw [charpoly_roots_diagonal, charpoly_roots_diagonal] at h3
  have h4 : (univ.val.map fun a => -pev z a).map (fun x : ℝ => (x : ℂ)) =
      (univ.val.map (pev z)).map (fun x : ℝ => (x : ℂ)) := by
    first
    | (rw [Multiset.map_map, Multiset.map_map]; exact h3)
    | simpa [Multiset.map_map, Function.comp_def] using h3
  exact Multiset.map_injective Complex.ofReal_injective h4

/- English proof (translation)
Establish `h` using `congrArg (fun s => (s.map g).sum) (pev_neg_multiset z)`. Simplify using `only [Multiset.map_map, Function.comp_def] at h`. Rewrite using `[Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]`. Conclude with `h`.
-/
theorem sum_pev_neg {ε : Fin n → Bool} (z : PCoord ε → ℂ) (g : ℝ → ℝ) :
    ∑ a, g (-pev z a) = ∑ a, g (pev z a) := by
  have h := congrArg (fun s => (s.map g).sum) (pev_neg_multiset z)
  simp only [Multiset.map_map, Function.comp_def] at h
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact h

def pevU {ε : Fin n → Bool} (z : PCoord ε → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)

/- English proof (translation)
Establish `hAU` using `pmat_mul_evU z`. Unfold `pevU`. Rewrite using `[Matrix.mulVec_mulVec, hAU, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose, pmat_eigenvectorUnitary_star_mul_self, Matrix.vecMul_one]`. Simplify using `only [dotProduct, mulVec_diagonal, Pi.star_apply]`. Use `push_cast`.

Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Establish `h1 : star (c a) * c a = ((‖c a‖ : ℂ)) ^ 2` using `by first`. Consider the case `exact Complex.conj_mul' (c a)`. Consider the case `simp [← Complex.conj_mul']`. Rewrite using `[← h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_evU {ε : Fin n → Bool} (z : PCoord ε → ℂ) (c : Fin n → ℂ) :
    star (pevU z *ᵥ c) ⬝ᵥ (pmat z *ᵥ (pevU z *ᵥ c)) = ((∑ a, ‖c a‖ ^ 2 * pev z a : ℝ) : ℂ) := by
  have hAU := pmat_mul_evU z
  unfold pevU
  rw [Matrix.mulVec_mulVec, hAU, ← Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose,
    pmat_eigenvectorUnitary_star_mul_self, Matrix.vecMul_one]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h1 : star (c a) * c a = ((‖c a‖ : ℂ)) ^ 2 := by
    first
    | exact Complex.conj_mul' (c a)
    | simp [← Complex.conj_mul']
  rw [← h1]
  ring

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, Finset.mul_sum]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`.

Distinguish the cases in `hi : ε i = b`. Simplify using `[hv i hi]`. Distinguish the cases in `hj : ε j = b`. Simplify using `[hv j hj]`. Establish `hij : ε i = ε j`.

Apply the tactic sequence `cases h1 : ε i <;> cases h2 : ε j <;> cases b <;> simp_all`. Simplify using `[pmat_eq_zero_of_eq z hij]`.
-/
theorem quad_zero_of_support {ε : Fin n → Bool} (z : PCoord ε → ℂ) (b : Bool) (v : Fin n → ℂ)
    (hv : ∀ j, ε j = b → v j = 0) : star v ⬝ᵥ (pmat z *ᵥ v) = 0 := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hi : ε i = b
  · simp [hv i hi]
  by_cases hj : ε j = b
  · simp [hv j hj]
  have hij : ε i = ε j := by
    cases h1 : ε i <;> cases h2 : ε j <;> cases b <;> simp_all
  simp [pmat_eq_zero_of_eq z hij]

def pevExt {ε : Fin n → Bool} (z : PCoord ε → ℂ) : ({a // 0 < pev z a} → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun c a := if h : 0 < pev z a then c ⟨a, h⟩ else 0
  map_add' c d := by
    funext a; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r c := by
    funext a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

/- English proof (translation)
Set `Φ : ({a // 0 < pev z a} → ℂ) →ₗ[ℂ] ({j // ε j = b} → ℂ)` to `(LinearMap.funLeft ℂ ℂ (Subtype.val : {j // ε j = b} → Fin n)) ∘ₗ ((Matrix.mulVecLin (pevU z)) ∘ₗ pevExt z)`. Establish `hinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `c hc`. Rewrite `hc` using `[LinearMap.mem_ker]`.

Rewrite using `[Submodule.mem_bot]`. Establish `hv : ∀ j, ε j = b → (pevU z *ᵥ pevExt z c) j = 0`. Introduce `j hj`. Establish `e` using `congrFun hc ⟨j, hj⟩`. Simplify `e` using `[Φ, LinearMap.funLeft_apply]`.

Establish `h0` using `quad_zero_of_support z b _ hv`. Rewrite `h0` using `[quad_evU]`. Establish `h1 : ∑ a, ‖pevExt z c a‖ ^ 2 * pev z a = 0` using `by exact_mod_cast h0`. Establish `hterm : ∀ a, 0 ≤ ‖pevExt z c a‖ ^ 2 * pev z a`. Introduce `a`.

Distinguish the cases in `ha : 0 < pev z a`. Conclude with `mul_nonneg (sq_nonneg _) ha.le`. Establish `e : pevExt z c a = 0` using `by simp [pevExt, ha]`. Simplify using `[e]`. Establish `hz` using `(Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hterm a)).mp h1`.

Use function extensionality and compare the values at `x`. Take `⟨a, ha⟩` from `x`. Establish `e` using `hz a (Finset.mem_univ a)`. Establish `hext : pevExt z c a = c ⟨a, ha⟩` using `by simp [pevExt, ha]`. Rewrite `e` using `[hext]`.

Establish `e2 : ‖c ⟨a, ha⟩‖ ^ 2 = 0`. Break down `mul_eq_zero.mp e with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h ha.ne'`. Simplify using `using e2`.

Establish `hle` using `LinearMap.finrank_le_finrank_of_injective hinj`. Use `first`. Consider the case `simpa [Fintype.card_subtype] using hle`. Consider the case `(simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype] at hle; convert hle using 2)`.
-/
theorem card_pos_le {ε : Fin n → Bool} (z : PCoord ε → ℂ) (b : Bool) :
    (univ.filter (fun a => 0 < pev z a)).card ≤ (univ.filter fun a => ε a = b).card := by
  classical
  let Φ : ({a // 0 < pev z a} → ℂ) →ₗ[ℂ] ({j // ε j = b} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {j // ε j = b} → Fin n)) ∘ₗ
      ((Matrix.mulVecLin (pevU z)) ∘ₗ pevExt z)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    rw [Submodule.mem_bot]
    have hv : ∀ j, ε j = b → (pevU z *ᵥ pevExt z c) j = 0 := by
      intro j hj
      have e := congrFun hc ⟨j, hj⟩
      simpa [Φ, LinearMap.funLeft_apply] using e
    have h0 := quad_zero_of_support z b _ hv
    rw [quad_evU] at h0
    have h1 : ∑ a, ‖pevExt z c a‖ ^ 2 * pev z a = 0 := by exact_mod_cast h0
    have hterm : ∀ a, 0 ≤ ‖pevExt z c a‖ ^ 2 * pev z a := by
      intro a
      by_cases ha : 0 < pev z a
      · exact mul_nonneg (sq_nonneg _) ha.le
      · have e : pevExt z c a = 0 := by simp [pevExt, ha]
        simp [e]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hterm a)).mp h1
    funext x
    obtain ⟨a, ha⟩ := x
    have e := hz a (Finset.mem_univ a)
    have hext : pevExt z c a = c ⟨a, ha⟩ := by simp [pevExt, ha]
    rw [hext] at e
    have e2 : ‖c ⟨a, ha⟩‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp e with h | h
      · exact h
      · exact absurd h ha.ne'
    simpa using e2
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  first
  | simpa [Fintype.card_subtype] using hle
  | (simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype] at hle; convert hle using 2)

/- English proof (translation)
Conclude with `le_min (card_pos_le z true) (card_pos_le z false)`.
-/
theorem pev_card_pos {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    (univ.filter (fun a => 0 < pev z a)).card ≤ q0 ε := by
  exact le_min (card_pos_le z true) (card_pos_le z false)

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, pmat_eigenvectorUnitary_star_mul_self, Matrix.one_mul]`.
-/
private lemma eigenvectorUnitary_star_mul_mul_cancel {ε : Fin n → Bool} (z : PCoord ε → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    star ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * M) = M := by
  rw [← Matrix.mul_assoc, pmat_eigenvectorUnitary_star_mul_self, Matrix.one_mul]

/- English proof (translation)
Establish `h1 : (pmat z * pmat z).trace = ∑ a, ((pev z a : ℂ)) ^ 2` using `by conv_lhs => rw [pmat_eq_eigenvectorUnitary_mul_diagonal_mul_star z]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[eigenvectorUnitary_star_mul_mul_cancel, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, pmat_eigenvectorUnitary_star_mul_self, Matrix.mul_one, diagonal_mul_diagonal, trace_diagonal]`. Simplify using `only [sq]`. Establish `h2 : (pmat z * pmat z).trace = ((∑ i, ∑ j, ‖pmat z i j‖ ^ 2 : ℝ) : ℂ)`.

Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply]`. Use `push_cast`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Establish `hh : pmat z j i = star (pmat z i j)` using `by first`. Consider the case `exact ((pmat_isHermitian z).apply j i).symm`.

Consider the case `(have e := congrFun (congrFun (pmat_isHermitian z).eq j) i`. Rewrite `e` using `[Matrix.conjTranspose_apply]`. Conclude with `e.symm)`. Rewrite using `[hh]`. Use `first`.

Consider the case `exact Complex.mul_conj' _`. Consider the case `(rw [mul_comm]; exact Complex.conj_mul' _)`. Establish `hsum : ∑ a, pev z a ^ 2 = ∑ i, ∑ j, ‖pmat z i j‖ ^ 2`. Establish `e` using `h1.symm.trans h2`. Conclude with `e` after adjusting the coercions.

Establish `hsplit : ∑ a, pev z a ^ 2 = ∑ a ∈ univ.filter (fun a => 0 < pev z a), pev z a ^ 2 + ∑ a, (if pev z a < 0 then pev z a ^ 2 else 0)`. Rewrite using `[Finset.sum_filter, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Break down `lt_trichotomy (pev z a) 0 with h | h | h` into its components or cases. Simplify using `[h, lt_asymm h]`.

Simplify using `[h]`. Simplify using `[h, lt_asymm h]`. Establish `hneg : ∑ a, (if pev z a < 0 then pev z a ^ 2 else 0) = ∑ a ∈ univ.filter (fun a => 0 < pev z a), pev z a ^ 2`. Establish `e` using `sum_pev_neg z (fun x => if x < 0 then x ^ 2 else 0)`. Rewrite using `[Finset.sum_filter]`.

Use `Eq.trans e.symm ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Simplify using `only [neg_lt_zero, neg_sq]`. Unfold `hs`. Rewrite using `[← hsum, hsplit, hneg]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pev_pos_sum_sq {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∑ a ∈ univ.filter (fun a => 0 < pev z a), pev z a ^ 2 = hs (pmat z) / 2 := by
  have h1 : (pmat z * pmat z).trace = ∑ a, ((pev z a : ℂ)) ^ 2 := by
    conv_lhs => rw [pmat_eq_eigenvectorUnitary_mul_diagonal_mul_star z]
    simp only [Matrix.mul_assoc]
    rw [eigenvectorUnitary_star_mul_mul_cancel, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, pmat_eigenvectorUnitary_star_mul_self,
      Matrix.mul_one, diagonal_mul_diagonal, trace_diagonal]
    simp only [sq]
  have h2 : (pmat z * pmat z).trace = ((∑ i, ∑ j, ‖pmat z i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hh : pmat z j i = star (pmat z i j) := by
      first
      | exact ((pmat_isHermitian z).apply j i).symm
      | (have e := congrFun (congrFun (pmat_isHermitian z).eq j) i
         rw [Matrix.conjTranspose_apply] at e
         exact e.symm)
    rw [hh]
    first
    | exact Complex.mul_conj' _
    | (rw [mul_comm]; exact Complex.conj_mul' _)
  have hsum : ∑ a, pev z a ^ 2 = ∑ i, ∑ j, ‖pmat z i j‖ ^ 2 := by
    have e := h1.symm.trans h2
    exact_mod_cast e
  have hsplit : ∑ a, pev z a ^ 2 = ∑ a ∈ univ.filter (fun a => 0 < pev z a), pev z a ^ 2 +
      ∑ a, (if pev z a < 0 then pev z a ^ 2 else 0) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rcases lt_trichotomy (pev z a) 0 with h | h | h
    · simp [h, lt_asymm h]
    · simp [h]
    · simp [h, lt_asymm h]
  have hneg : ∑ a, (if pev z a < 0 then pev z a ^ 2 else 0) =
      ∑ a ∈ univ.filter (fun a => 0 < pev z a), pev z a ^ 2 := by
    have e := sum_pev_neg z (fun x => if x < 0 then x ^ 2 else 0)
    rw [Finset.sum_filter]
    refine Eq.trans e.symm ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [neg_lt_zero, neg_sq]
  unfold hs
  rw [← hsum, hsplit, hneg]
  ring

/- English proof (translation)
Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `max_eq_left h.le`. Conclude with `max_eq_right (not_lt.mp h)`.
-/
theorem sum_max_pev {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∑ a, max (pev z a) 0 = ∑ a ∈ univ.filter (fun a => 0 < pev z a), pev z a := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with h
  · exact max_eq_left h.le
  · exact max_eq_right (not_lt.mp h)

/- English proof (translation)
Use `set S := ∑ a ∈ univ.filter (fun a => 0 < pev z a), pev z a with hS`. Establish `hcs : S ^ 2 ≤ ((univ.filter (fun a => 0 < pev z a)).card : ℝ) * ∑ a ∈ univ.filter (fun a => 0 < pev z a), pev z a ^ 2` using `by first`. Consider the case `exact sq_sum_le_card_mul_sum_sq`. Consider the case `(have e := Finset.sum_mul_sq_le_sq_mul_sq (univ.filter (fun a => 0 < pev z a)) (fun _ => (1 : ℝ)) (pev z)`. Simplify using `using e)`.

Rewrite `hcs` using `[pev_pos_sum_sq]`. Establish `hq : ((univ.filter (fun a => 0 < pev z a)).card : ℝ) ≤ q0 ε` using `by exact_mod_cast pev_card_pos z`. Establish `hhs : 0 ≤ hs (pmat z)` using `by unfold hs; positivity`. Establish `hR : (rhoP z / 2) ^ 2 = (q0 ε : ℝ) * (hs (pmat z) / 2)`. Unfold `rhoP`.

Rewrite using `[div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hhs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hRnn : 0 ≤ rhoP z / 2` using `by unfold rhoP; positivity`. Establish `h2 : S ^ 2 ≤ (rhoP z / 2) ^ 2`. Rewrite using `[hR]`.

Conclude with `hcs.trans (mul_le_mul_of_nonneg_right hq (div_nonneg hhs zero_le_two))`. Establish `h3` using `Real.sqrt_le_sqrt h2`. Rewrite `h3` using `[Real.sqrt_sq_eq_abs, Real.sqrt_sq hRnn]`. Conclude with `(le_abs_self S).trans h3`.
-/
theorem sum_pos_pev_le {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∑ a ∈ univ.filter (fun a => 0 < pev z a), pev z a ≤ rhoP z / 2 := by
  set S := ∑ a ∈ univ.filter (fun a => 0 < pev z a), pev z a with hS
  have hcs : S ^ 2 ≤ ((univ.filter (fun a => 0 < pev z a)).card : ℝ) *
      ∑ a ∈ univ.filter (fun a => 0 < pev z a), pev z a ^ 2 := by
    first
    | exact sq_sum_le_card_mul_sum_sq
    | (have e := Finset.sum_mul_sq_le_sq_mul_sq (univ.filter (fun a => 0 < pev z a)) (fun _ => (1 : ℝ)) (pev z)
       simpa using e)
  rw [pev_pos_sum_sq] at hcs
  have hq : ((univ.filter (fun a => 0 < pev z a)).card : ℝ) ≤ q0 ε := by exact_mod_cast pev_card_pos z
  have hhs : 0 ≤ hs (pmat z) := by unfold hs; positivity
  have hR : (rhoP z / 2) ^ 2 = (q0 ε : ℝ) * (hs (pmat z) / 2) := by
    unfold rhoP
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hhs]
    ring
  have hRnn : 0 ≤ rhoP z / 2 := by unfold rhoP; positivity
  have h2 : S ^ 2 ≤ (rhoP z / 2) ^ 2 := by
    rw [hR]
    exact hcs.trans (mul_le_mul_of_nonneg_right hq (div_nonneg hhs zero_le_two))
  have h3 := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq hRnn] at h3
  exact (le_abs_self S).trans h3

/- English proof (translation)
The claim follows from `|∑ s ∈ S, pev z s| ≤ rhoP z / 2 := by have hup : ∀ T : Finset (Fin n), ∑ s ∈ T, pev z s ≤ rhoP z / 2 := by intro T calc ∑ s ∈ T, pev z s ≤ ∑ s ∈ T, max (pev z s) 0 := Finset.sum_le_sum (fun s _ => le_max_left _ _) _ ≤ ∑ s, max (pev z s) 0 := Finset.sum_le_sum_of_subset_of_nonneg …`.
-/
theorem abs_sum_pev_le {ε : Fin n → Bool} (z : PCoord ε → ℂ) (S : Finset (Fin n)) :
    |∑ s ∈ S, pev z s| ≤ rhoP z / 2 := by
  have hup : ∀ T : Finset (Fin n), ∑ s ∈ T, pev z s ≤ rhoP z / 2 := by
    intro T
    calc ∑ s ∈ T, pev z s ≤ ∑ s ∈ T, max (pev z s) 0 := Finset.sum_le_sum (fun s _ => le_max_left _ _)
      _ ≤ ∑ s, max (pev z s) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun s _ _ => le_max_right _ _)
      _ = _ := sum_max_pev z
      _ ≤ rhoP z / 2 := sum_pos_pev_le z
  have hdown : ∀ T : Finset (Fin n), ∑ s ∈ T, -pev z s ≤ rhoP z / 2 := by
    intro T
    calc ∑ s ∈ T, -pev z s ≤ ∑ s ∈ T, max (-pev z s) 0 := Finset.sum_le_sum (fun s _ => le_max_left _ _)
      _ ≤ ∑ s, max (-pev z s) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun s _ _ => le_max_right _ _)
      _ = ∑ s, max (pev z s) 0 := sum_pev_neg z (fun x => max x 0)
      _ = _ := sum_max_pev z
      _ ≤ rhoP z / 2 := sum_pos_pev_le z
  rw [abs_le]
  constructor
  · have e := hdown S
    rw [Finset.sum_neg_distrib] at e
    linarith
  · exact hup S

end ReciprocityTheory.ChartRestriction.DS
