import Formalism.MahlerMeasure.IsFrozenInv

namespace Formalism.GM.M.FB

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def evVal (p : ℕ) [Fact p.Prime] {N r : ℕ} (ρ : Fin r) :
    Fin (N + 1) × Fin r → MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  fun v => Fin.lastCases (motive := fun _ => MvPolynomial (Fin N × Fin r) ℚ_[p])
    (if v.2 = ρ then 1 else 0) (fun i => X (i, v.2)) v.1

noncomputable def ev (p : ℕ) [Fact p.Prime] {N r : ℕ} (ρ : Fin r) :
    MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  aeval (evVal p ρ)

/- English proof (translation)
Simplify using `[evVal]`.
-/
@[simp] lemma evVal_last (ρ c : Fin r) :
    evVal p (N := N) ρ (Fin.last N, c) = if c = ρ then 1 else 0 := by
  simp [evVal]

/- English proof (translation)
Simplify using `[evVal]`.
-/
@[simp] lemma evVal_castSucc (ρ c : Fin r) (i : Fin N) :
    evVal p ρ (Fin.castSucc i, c) = X (i, c) := by
  simp [evVal]

/- English proof (translation)
Break down `v with ⟨i, c⟩` into its components or cases. Apply the tactic sequence `by_cases hv : LL.vec i <;> by_cases hc : c = ρ <;>`. Simplify using `[freezeSub, ev, hv, hc, mul_ite, Finset.sum_ite_eq']`.
-/
lemma ev_freezeSub (LL : Letters N) (ρ : Fin r) (v : Fin N × Fin r) :
    ev p ρ (freezeSub p LL ρ v) = X v := by
  rcases v with ⟨i, c⟩
  by_cases hv : LL.vec i <;> by_cases hc : c = ρ <;>
    simp [freezeSub, ev, hv, hc, mul_ite, Finset.sum_ite_eq']

/- English proof (translation)
Simplify using `only [freeze, map_mul, map_pow]`. Establish `h1 : ev p ρ (X (Fin.last N, ρ)) = 1` using `by simp [ev]`. Establish `h2 : ev p ρ (aeval (freezeSub p LL ρ) f) = f`. Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Establish `: (fun i => (ev p ρ) (freezeSub p LL ρ i)) = X` using `funext (ev_freezeSub LL ρ)`.

Rewrite using `[this, MvPolynomial.aeval_X_left_apply]`. Rewrite using `[h1, h2, one_pow, one_mul]`.
-/
lemma ev_freeze (LL : Letters N) (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ev p ρ (freeze p LL ρ n f) = f := by
  simp only [freeze, map_mul, map_pow]
  have h1 : ev p ρ (X (Fin.last N, ρ)) = 1 := by simp [ev]
  have h2 : ev p ρ (aeval (freezeSub p LL ρ) f) = f := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have : (fun i => (ev p ρ) (freezeSub p LL ρ i)) = X := funext (ev_freezeSub LL ρ)
    rw [this, MvPolynomial.aeval_X_left_apply]
  rw [h1, h2, one_pow, one_mul]

noncomputable def res (m : Fin (N + 1) × Fin r →₀ ℕ) : Fin N × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => m (Fin.castSucc v.1, v.2))

/- English proof (translation)
Simplify using `[res]`.
-/
@[simp] lemma res_apply (m : Fin (N + 1) × Fin r →₀ ℕ) (v : Fin N × Fin r) :
    res m v = m (Fin.castSucc v.1, v.2) := by
  simp [res]

noncomputable def ext (n : ℕ) (ρ : Fin r) (m : Fin N × Fin r →₀ ℕ) : Fin (N + 1) × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => Fin.lastCases (motive := fun _ => ℕ)
    (if v.2 = ρ then n else 0) (fun i => m (i, v.2)) v.1)

/- English proof (translation)
Simplify using `[ext]`.
-/
@[simp] lemma ext_last (n : ℕ) (ρ c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    ext n ρ m (Fin.last N, c) = if c = ρ then n else 0 := by
  simp [ext]

/- English proof (translation)
Simplify using `[ext]`.
-/
@[simp] lemma ext_castSucc (n : ℕ) (ρ c : Fin r) (m : Fin N × Fin r →₀ ℕ) (i : Fin N) :
    ext n ρ m (Fin.castSucc i, c) = m (i, c) := by
  simp [ext]

/- English proof (translation)
Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
@[simp] lemma res_ext (n : ℕ) (ρ : Fin r) (m : Fin N × Fin r →₀ ℕ) : res (ext n ρ m) = m := by
  ext v
  simp

/- English proof (translation)
Rewrite using `[ev, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_castSucc]`. Simplify using `only [evVal_castSucc, evVal_last]`. Use `split_ifs with h`. Establish `hlast : ∏ c : Fin r, (if c = ρ then (1 : MvPolynomial (Fin N × Fin r) ℚ_[p]) else 0) ^ m (Fin.last N, c) = 1`. Use `Finset.prod_eq_one (fun c _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hc : c = ρ`. Simplify using `[hc]`. Simplify using `[hc, h c hc]`. Rewrite using `[hlast, mul_one, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]`. Simplify using `only [res_apply, MvPolynomial.algebraMap_eq]`.

Use `push_neg at h`. Take `⟨c, hc, hc0⟩` from `h`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ c) (by simp [hc, hc0]), mul_zero, mul_zero]`.
-/
lemma ev_monomial (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) (a : ℚ_[p]) :
    ev p ρ (monomial m a) =
      if (∀ c, c ≠ ρ → m (Fin.last N, c) = 0) then monomial (res m) a else 0 := by
  classical
  rw [ev, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
    Fin.prod_univ_castSucc]
  simp only [evVal_castSucc, evVal_last]
  split_ifs with h
  · have hlast : ∏ c : Fin r, (if c = ρ then (1 : MvPolynomial (Fin N × Fin r) ℚ_[p]) else 0) ^
        m (Fin.last N, c) = 1 := by
      refine Finset.prod_eq_one (fun c _ => ?_)
      by_cases hc : c = ρ
      · simp [hc]
      · simp [hc, h c hc]
    rw [hlast, mul_one, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fintype.prod_prod_type]
    simp only [res_apply, MvPolynomial.algebraMap_eq]
  · push_neg at h
    obtain ⟨c, hc, hc0⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ c) (by simp [hc, hc0]), mul_zero, mul_zero]

/- English proof (translation)
Use `conv_lhs => rw [F.as_sum]`. Rewrite using `[map_sum, MvPolynomial.coeff_sum]`. Simplify using `only [ev_monomial]`. Rewrite using `[Finset.sum_eq_single (ext n ρ m')]`. Rewrite using `[if_pos (fun c hc => by rw [ext_last, if_neg hc]), res_ext, MvPolynomial.coeff_monomial, if_pos rfl]`.

Introduce `m hm hne split_ifs with hcond`. Rewrite using `[MvPolynomial.coeff_monomial, if_neg]`. Introduce `hres`. Apply `hne` to reduce the goal to its premises. Establish `heq : m = ext n ρ (res m)`.

Use extensionality with `⟨i, c⟩`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Distinguish the cases in `hc : c = ρ`. Substitute `hc` using the available equality. Rewrite using `[ext_last, if_pos rfl, ← hF m hm, Finset.sum_eq_single c]`.

Introduce `b _ hb`. Conclude with `hcond b hb`. Introduce `h`. Conclude with `absurd (Finset.mem_univ c) h`. Rewrite using `[ext_last, if_neg hc, hcond c hc]`.

Rewrite using `[ext_castSucc, res_apply]`. Rewrite using `[heq, hres]`. Conclude with `MvPolynomial.coeff_zero _`. Introduce `hnot`. Establish `h0 : coeff (ext n ρ m') F = 0` using `by simpa using hnot`.

Rewrite using `[h0]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma coeff_ev (ρ : Fin r) (n : ℕ) (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hF : ∀ m ∈ F.support, ∑ c, m (Fin.last N, c) = n) (m' : Fin N × Fin r →₀ ℕ) :
    coeff m' (ev p ρ F) = coeff (ext n ρ m') F := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  simp only [ev_monomial]
  rw [Finset.sum_eq_single (ext n ρ m')]
  · rw [if_pos (fun c hc => by rw [ext_last, if_neg hc]), res_ext, MvPolynomial.coeff_monomial, if_pos rfl]
  · intro m hm hne
    split_ifs with hcond
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro hres
      apply hne
      have heq : m = ext n ρ (res m) := by
        ext ⟨i, c⟩
        refine Fin.lastCases ?_ (fun j => ?_) i
        · by_cases hc : c = ρ
          · subst hc
            rw [ext_last, if_pos rfl, ← hF m hm, Finset.sum_eq_single c]
            · intro b _ hb
              exact hcond b hb
            · intro h
              exact absurd (Finset.mem_univ c) h
          · rw [ext_last, if_neg hc, hcond c hc]
        · rw [ext_castSucc, res_apply]
      rw [heq, hres]
    · exact MvPolynomial.coeff_zero _
  · intro hnot
    have h0 : coeff (ext n ρ m') F = 0 := by simpa using hnot
    rw [h0]
    split_ifs <;> simp

end Formalism.GM.M.FB

namespace Formalism.GM.M.FB

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Simplify using `only [glAct, LinearMap.sum_apply]`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [Derivation.leibniz, smul_eq_mul] <;> ring`.
-/
lemma glAct_mul {M : ℕ} (LL : Letters M) (j : ℕ) (c d : Fin r)
    (a b : MvPolynomial (Fin M × Fin r) ℚ_[p]) :
    glAct p LL j c d (a * b) = a * glAct p LL j c d b + b * glAct p LL j c d a := by
  simp only [glAct, LinearMap.sum_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Derivation.leibniz, smul_eq_mul] <;> ring

/- English proof (translation)
Simplify using `only [glAct, LinearMap.sum_apply]`. Rewrite using `[Finset.sum_eq_single j]`. Apply the tactic sequence `by_cases hv : LL.vec j <;> by_cases ha : a = d <;> by_cases hc : a = c <;>`. Apply the tactic sequence `simp [hv, ha, hc, MvPolynomial.pderiv_X, Pi.single_apply, j.isLt] <;> split_ifs <;> simp_all`. Apply the tactic sequence `intro i _ hij split_ifs <;> simp [MvPolynomial.pderiv_X, Pi.single_apply, Ne.symm hij]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.
-/
lemma glAct_X {M : ℕ} (LL : Letters M) (c d : Fin r) (j : Fin M) (a : Fin r) :
    glAct p LL M c d (X (j, a)) =
      if LL.vec j then (if a = d then X (j, c) else 0) else (if a = c then -X (j, d) else 0) := by
  simp only [glAct, LinearMap.sum_apply]
  rw [Finset.sum_eq_single j]
  · by_cases hv : LL.vec j <;> by_cases ha : a = d <;> by_cases hc : a = c <;>
      simp [hv, ha, hc, MvPolynomial.pderiv_X, Pi.single_apply, j.isLt] <;> split_ifs <;> simp_all
  · intro i _ hij
    split_ifs <;> simp [MvPolynomial.pderiv_X, Pi.single_apply, Ne.symm hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

/- English proof (translation)
Simplify using `[Letters.snoc]`.
-/
@[simp] lemma snoc_vec_last (LL : Letters N) (n : ℕ) : (LL.snoc n).vec (Fin.last N) = false := by
  simp [Letters.snoc]

/- English proof (translation)
Simplify using `[Letters.snoc]`.
-/
@[simp] lemma snoc_vec_castSucc (LL : Letters N) (n : ℕ) (i : Fin N) :
    (LL.snoc n).vec (Fin.castSucc i) = LL.vec i := by
  simp [Letters.snoc]

/- English proof (translation)
Simplify using `[Letters.snoc]`.
-/
@[simp] lemma snoc_deg_last (LL : Letters N) (n : ℕ) : (LL.snoc n).deg (Fin.last N) = n := by
  simp [Letters.snoc]

/- English proof (translation)
Simplify using `[Letters.snoc]`.
-/
@[simp] lemma snoc_deg_castSucc (LL : Letters N) (n : ℕ) (i : Fin N) :
    (LL.snoc n).deg (Fin.castSucc i) = LL.deg i := by
  simp [Letters.snoc]

/- English proof (translation)
Break down `v with ⟨i, c0⟩` into its components or cases. Apply the tactic sequence `by_cases hv : LL.vec i <;> by_cases hc0 : c0 = ρ <;>`. Apply the tactic sequence `simp [freezeSub, hv, hc0, glAct_mul, glAct_X, map_sum, map_sub, Ne.symm hc, hc, mul_ite, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq] <;> ring`.
-/
lemma glAct_freezeSub (LL : Letters N) (n : ℕ) (ρ c : Fin r) (hc : c ≠ ρ) (v : Fin N × Fin r) :
    glAct p (LL.snoc n) (N + 1) c ρ (freezeSub p LL ρ v) = 0 := by
  rcases v with ⟨i, c0⟩
  by_cases hv : LL.vec i <;> by_cases hc0 : c0 = ρ <;>
    simp [freezeSub, hv, hc0, glAct_mul, glAct_X, map_sum, map_sub, Ne.symm hc, hc, mul_ite,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq] <;> ring

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h1 : glAct p (LL.snoc n) (N + 1) c ρ (1 : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) = 0`. Simplify using `only [glAct, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.C_eq_smul_one, map_smul, h1, smul_zero]`. Consider the case `add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]`. Consider the case `mul_X f v hf`. Rewrite using `[map_mul, MvPolynomial.aeval_X, glAct_mul, hf, glAct_freezeSub LL n ρ c hc v, mul_zero, mul_zero, add_zero]`.
-/
lemma glAct_aeval_freezeSub (LL : Letters N) (n : ℕ) (ρ c : Fin r) (hc : c ≠ ρ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p (LL.snoc n) (N + 1) c ρ (aeval (freezeSub p LL ρ) f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h1 : glAct p (LL.snoc n) (N + 1) c ρ (1 : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) = 0 := by
      simp only [glAct, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs <;> simp
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.C_eq_smul_one, map_smul, h1, smul_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | mul_X f v hf =>
    rw [map_mul, MvPolynomial.aeval_X, glAct_mul, hf, glAct_freezeSub LL n ρ c hc v, mul_zero, mul_zero,
      add_zero]

end Formalism.GM.M.FB

set_option linter.unusedSimpArgs false

namespace Formalism.GM.M.FB

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

def wL (N r : ℕ) : Fin (N + 1) × Fin r → ℕ := fun v => if v.1 = Fin.last N then 1 else 0

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Rewrite using `[Fintype.sum_prod_type, Fin.sum_univ_castSucc]`. Simplify using `[wL, Fin.castSucc_ne_last]`.
-/
lemma weight_wL (m : Fin (N + 1) × Fin r →₀ ℕ) :
    Finsupp.weight (wL N r) m = ∑ c, m (Fin.last N, c) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  simp [wL, Fin.castSucc_ne_last]

/- English proof (translation)
Use `(MvPolynomial.isWeightedHomogeneous_X ℚ_[p] (wL N r) u).mul (MvPolynomial.isWeightedHomogeneous_X ℚ_[p] (wL N r) v)` as an intermediate fact. Rewrite `this` using `[h]`. Then use the resulting hypothesis.
-/
lemma hom_XX (u v : Fin (N + 1) × Fin r) (h : wL N r u + wL N r v = 1) :
    IsWeightedHomogeneous (wL N r) (X u * X v : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1 := by
  have := (MvPolynomial.isWeightedHomogeneous_X ℚ_[p] (wL N r) u).mul
    (MvPolynomial.isWeightedHomogeneous_X ℚ_[p] (wL N r) v)
  rwa [h] at this

/- English proof (translation)
Break down `v with ⟨i, c⟩` into its components or cases. Establish `hw : ∀ c1 c2, IsWeightedHomogeneous (wL N r) (X (Fin.castSucc i, c1) * X (Fin.last N, c2) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1` using `fun c1 c2 => hom_XX _ _ (by simp [wL, Fin.castSucc_ne_last])`. Establish `hw' : ∀ c1 c2, IsWeightedHomogeneous (wL N r) (X (Fin.last N, c2) * X (Fin.castSucc i, c1) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1` using `fun c1 c2 => hom_XX _ _ (by simp [wL, Fin.castSucc_ne_last])`. Simplify using `only [freezeSub]`. Use `split_ifs`.

Rewrite using `[← MvPolynomial.mem_weightedHomogeneousSubmodule]`. Conclude with `Submodule.sum_mem _ fun c' _ => (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw c' c')`. Conclude with `hw' c ρ`. Conclude with `hw' ρ ρ`. Rewrite using `[← MvPolynomial.mem_weightedHomogeneousSubmodule]`.

Conclude with `Submodule.sub_mem _ ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw' c ρ)) ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw ρ c))`.
-/
lemma hom_freezeSub (LL : Letters N) (ρ : Fin r) (v : Fin N × Fin r) :
    IsWeightedHomogeneous (wL N r) (freezeSub p LL ρ v) 1 := by
  rcases v with ⟨i, c⟩
  have hw : ∀ c1 c2, IsWeightedHomogeneous (wL N r)
      (X (Fin.castSucc i, c1) * X (Fin.last N, c2) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1 :=
    fun c1 c2 => hom_XX _ _ (by simp [wL, Fin.castSucc_ne_last])
  have hw' : ∀ c1 c2, IsWeightedHomogeneous (wL N r)
      (X (Fin.last N, c2) * X (Fin.castSucc i, c1) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) 1 :=
    fun c1 c2 => hom_XX _ _ (by simp [wL, Fin.castSucc_ne_last])
  simp only [freezeSub]
  split_ifs
  · rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact Submodule.sum_mem _ fun c' _ => (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw c' c')
  · exact hw' c ρ
  · exact hw' ρ ρ
  · rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact Submodule.sub_mem _ ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw' c ρ))
      ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 (hw ρ c))

/- English proof (translation)
Establish `hsupp` using `(MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hf`. Rewrite using `[f.as_sum, map_sum, ← MvPolynomial.mem_weightedHomogeneousSubmodule]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_weightedHomogeneousSubmodule, MvPolynomial.aeval_monomial]`. Establish `hdeg : MultiDeg LL m` using `hsupp (Finset.mem_coe.2 hm)`.

Establish `hpr : IsWeightedHomogeneous (wL N r) (m.prod fun v k => (freezeSub p LL ρ v) ^ k) (∑ v ∈ m.support, m v • 1)` using `MvPolynomial.IsWeightedHomogeneous.prod _ _ _ (fun v _ => (hom_freezeSub LL ρ v).pow (m v))`. Establish `hC` using `MvPolynomial.isWeightedHomogeneous_C (R := ℚ_[p]) (wL N r) (coeff m f)`. Establish `key` using `hC.mul hpr`. Establish `hs : ∑ v ∈ m.support, m v • 1 = ∑ v, m v`. Simplify using `only [smul_eq_mul, mul_one]`.

Conclude with `Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simpa using hv)`. Use `key using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Rewrite using `[hs, zero_add, Fintype.sum_prod_type]`. Simplify using `only [Letters.total]`.

Conclude with `(Finset.sum_congr rfl fun i _ => hdeg i).symm`.
-/
lemma hom_aeval (LL : Letters N) (ρ : Fin r) (f : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hf : f ∈ Pol p r LL) :
    IsWeightedHomogeneous (wL N r) (aeval (freezeSub p LL ρ) f) LL.total := by
  have hsupp := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hf
  rw [f.as_sum, map_sum, ← MvPolynomial.mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule, MvPolynomial.aeval_monomial]
  have hdeg : MultiDeg LL m := hsupp (Finset.mem_coe.2 hm)
  have hpr : IsWeightedHomogeneous (wL N r)
      (m.prod fun v k => (freezeSub p LL ρ v) ^ k) (∑ v ∈ m.support, m v • 1) :=
    MvPolynomial.IsWeightedHomogeneous.prod _ _ _
      (fun v _ => (hom_freezeSub LL ρ v).pow (m v))
  have hC := MvPolynomial.isWeightedHomogeneous_C (R := ℚ_[p]) (wL N r) (coeff m f)
  have key := hC.mul hpr
  have hs : ∑ v ∈ m.support, m v • 1 = ∑ v, m v := by
    simp only [smul_eq_mul, mul_one]
    exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simpa using hv)
  convert key using 1
  · rfl
  · rw [hs, zero_add, Fintype.sum_prod_type]
    simp only [Letters.total]
    exact (Finset.sum_congr rfl fun i _ => hdeg i).symm

/- English proof (translation)
Unfold `freeze`. Establish `key` using `((MvPolynomial.isWeightedHomogeneous_X ℚ_[p] (wL N r) (Fin.last N, ρ)).pow (n - LL.total)).mul (hom_aeval LL ρ f hf)`. Use `key using 1` and compare the differences between its conclusion and the goal. Simplify using `[wL]`. Use linear arithmetic over natural numbers and integers.
-/
lemma hom_freeze (LL : Letters N) (ρ : Fin r) (n : ℕ) (hS : LL.total ≤ n)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : f ∈ Pol p r LL) :
    IsWeightedHomogeneous (wL N r) (freeze p LL ρ n f) n := by
  unfold freeze
  have key := ((MvPolynomial.isWeightedHomogeneous_X ℚ_[p] (wL N r) (Fin.last N, ρ)).pow (n - LL.total)).mul
    (hom_aeval LL ρ f hf)
  convert key using 1
  simp [wL]
  omega

/- English proof (translation)
Simplify using `only [glAct, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma glAct_one (LL : Letters N) (n : ℕ) (ρ c : Fin r) :
    glAct p (LL.snoc n) (N + 1) c ρ (1 : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) = 0 := by
  simp only [glAct, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Introduce `c hc`. Establish `hXρ : glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ)) = 0`. Rewrite using `[glAct_X]`. Simplify using `[Ne.symm hc]`. Establish `hpow : ∀ k, glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ) ^ k) = 0`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero]`. Conclude with `glAct_one LL n ρ c`. Consider the case `succ k ih => rw [pow_succ, glAct_mul, ih, hXρ, mul_zero, mul_zero, add_zero]`.

Unfold `freeze`. Rewrite using `[glAct_mul, hpow, glAct_aeval_freezeSub LL n ρ c hc, mul_zero, mul_zero, add_zero]`.
-/
lemma freeze_inv (LL : Letters N) (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    IsFrozenInv p LL ρ n (freeze p LL ρ n f) := by
  intro c hc
  have hXρ : glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ)) = 0 := by
    rw [glAct_X]
    simp [Ne.symm hc]
  have hpow : ∀ k, glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ) ^ k) = 0 := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact glAct_one LL n ρ c
    | succ k ih => rw [pow_succ, glAct_mul, ih, hXρ, mul_zero, mul_zero, add_zero]
  unfold freeze
  rw [glAct_mul, hpow, glAct_aeval_freezeSub LL n ρ c hc, mul_zero, mul_zero, add_zero]

end Formalism.GM.M.FB

set_option linter.unusedSimpArgs false

namespace Formalism.GM.M.FB

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

def kk (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) : ℕ :=
  ∑ c ∈ Finset.univ.erase ρ, m (Fin.last N, c)

/- English proof (translation)
Rewrite using `[MvPolynomial.coeff_X_mul']`. Use `split_ifs with h`. Rewrite using `[MvPolynomial.coeff_pderiv, hG _ ?_, zero_mul]`. Simplify using `only [kk]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Simplify using `[Finsupp.single_apply, Fin.castSucc_ne_last]`. Both sides reduce to the same expression.
-/
lemma coeff_X_pderiv_castSucc (ρ : Fin r) (G : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (m : Fin (N + 1) × Fin r →₀ ℕ)
    (hG : ∀ ν : Fin (N + 1) × Fin r →₀ ℕ, kk ρ ν = kk ρ m → coeff ν G = 0)
    (i : Fin N) (a b : Fin r) :
    coeff m (X (Fin.castSucc i, a) * pderiv (Fin.castSucc i, b) G) = 0 := by
  classical
  rw [MvPolynomial.coeff_X_mul']
  split_ifs with h
  · rw [MvPolynomial.coeff_pderiv, hG _ ?_, zero_mul]
    simp only [kk]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Finsupp.single_apply, Fin.castSucc_ne_last]
  · rfl

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hex : ∃ k, ∃ m, kk ρ m = k ∧ coeff m G ≠ 0`. Take `⟨m, hm⟩` from `MvPolynomial.ne_zero_iff.1 hne`. Conclude with `⟨_, m, rfl, hm⟩`. Take `⟨m, hmk, hm⟩` from `Nat.find_spec hex`.

Establish `hmin : ∀ ν, kk ρ ν < Nat.find hex → coeff ν G = 0` using `fun ν hν => by`. Assume the negation of the conclusion as `h`. Conclude with `Nat.find_min hex hν ⟨ν, rfl, h⟩`. Choose the witnesses or unpack the hypotheses as in `⟨c, hcρ, hc⟩ : ∃ c, c ≠ ρ ∧ m (Fin.last N, c) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Apply `hm` to reduce the goal to its premises. Apply `h0` to reduce the goal to its premises. Simplify using `only [kk]`. Conclude with `Finset.sum_eq_zero fun c' hc' => hcon c' (Finset.ne_of_mem_erase hc')`.

Use `set m' := m - Finsupp.single (Fin.last N, c) 1 + Finsupp.single (Fin.last N, ρ) 1 with hm'`. Establish `hval : ∀ c', c' ≠ ρ → m' (Fin.last N, c') = m (Fin.last N, c') - (if c = c' then 1 else 0)`. Introduce `c' hc'`. Simplify using `[hm', Finsupp.single_apply, Ne.symm hc']`. Establish `hlt : kk ρ m' < kk ρ m`.

Simplify using `only [kk]`. Use `Finset.sum_lt_sum (fun c' hc' => ?_) ⟨c, Finset.mem_erase.2 ⟨hcρ, Finset.mem_univ _⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hval c' (Finset.ne_of_mem_erase hc')]`. Conclude with `Nat.sub_le _ _`. Rewrite using `[hval c hcρ, if_pos rfl]`.

Use linear arithmetic over natural numbers and integers. Establish `hG' : ∀ ν, kk ρ ν = kk ρ m' → coeff ν G = 0` using `fun ν hν => hmin ν (hν ▸ hmk ▸ hlt)`. Establish `hc0` using `congrArg (coeff m') (hinv c hcρ)`. Simplify using `only [glAct, LinearMap.sum_apply, MvPolynomial.coeff_sum, coeff_zero] at hc0`. Rewrite `hc0` using `[Fin.sum_univ_castSucc, Finset.sum_eq_zero (fun i _ => ?_), zero_add]`.

Establish `hl : ((Fin.last N : Fin (N + 1)) : ℕ) < N + 1` using `(Fin.last N).isLt`. Rewrite `hc0` using `[if_pos hl]`. Simplify using `only [snoc_vec_last, Bool.false_eq_true, ↓reduceIte, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, coeff_neg, neg_eq_zero] at hc0`. Rewrite `hc0` using `[MvPolynomial.coeff_X_mul', if_pos (by simp [hm'])]`. Use `erw [MvPolynomial.coeff_pderiv] at hc0`.

Establish `e1 : m' - Finsupp.single (Fin.last N, ρ) 1 + Finsupp.single (Fin.last N, c) 1 = m`. Rewrite using `[hm', add_tsub_cancel_right, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hc))]`. Establish `e2 : ((m' - Finsupp.single (Fin.last N, ρ) 1 : Fin (N + 1) × Fin r →₀ ℕ) (Fin.last N, c)) + 1 = m (Fin.last N, c)`. Rewrite using `[hm', add_tsub_cancel_right, Finsupp.tsub_apply, Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers.

Rewrite `hc0` using `[e1]`. Establish `e3 : ((((m' - Finsupp.single (Fin.last N, ρ) 1 : Fin (N + 1) × Fin r →₀ ℕ) (Fin.last N, c) : ℕ) : ℚ_[p]) + 1) = ((m (Fin.last N, c) : ℕ) : ℚ_[p])` using `by exact_mod_cast e2`. Rewrite `hc0` using `[e3]`. Break down `mul_eq_zero.1 hc0 with h | h` into its components or cases. Conclude with `hm h`.

Conclude with `hc (by exact_mod_cast h)`. Establish `hci : ((Fin.castSucc i : Fin (N + 1)) : ℕ) < N + 1` using `(Fin.castSucc i).isLt`. Rewrite using `[if_pos hci]`. Use `split_ifs`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply]`.

Conclude with `coeff_X_pderiv_castSucc ρ G m' hG' i c ρ`. Simplify using `only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, coeff_neg, neg_eq_zero]`. Conclude with `coeff_X_pderiv_castSucc ρ G m' hG' i ρ c`.
-/
theorem vanish (LL : Letters N) (n : ℕ) (ρ : Fin r) (G : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hinv : IsFrozenInv p LL ρ n G) (h0 : ∀ m, kk ρ m = 0 → coeff m G = 0) : G = 0 := by
  classical
  by_contra hne
  have hex : ∃ k, ∃ m, kk ρ m = k ∧ coeff m G ≠ 0 := by
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hne
    exact ⟨_, m, rfl, hm⟩
  obtain ⟨m, hmk, hm⟩ := Nat.find_spec hex
  have hmin : ∀ ν, kk ρ ν < Nat.find hex → coeff ν G = 0 := fun ν hν => by
    by_contra h
    exact Nat.find_min hex hν ⟨ν, rfl, h⟩
  obtain ⟨c, hcρ, hc⟩ : ∃ c, c ≠ ρ ∧ m (Fin.last N, c) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hm
    apply h0
    simp only [kk]
    exact Finset.sum_eq_zero fun c' hc' => hcon c' (Finset.ne_of_mem_erase hc')
  set m' := m - Finsupp.single (Fin.last N, c) 1 + Finsupp.single (Fin.last N, ρ) 1 with hm'
  have hval : ∀ c', c' ≠ ρ → m' (Fin.last N, c') = m (Fin.last N, c') - (if c = c' then 1 else 0) := by
    intro c' hc'
    simp [hm', Finsupp.single_apply, Ne.symm hc']
  have hlt : kk ρ m' < kk ρ m := by
    simp only [kk]
    refine Finset.sum_lt_sum (fun c' hc' => ?_) ⟨c, Finset.mem_erase.2 ⟨hcρ, Finset.mem_univ _⟩, ?_⟩
    · rw [hval c' (Finset.ne_of_mem_erase hc')]
      exact Nat.sub_le _ _
    · rw [hval c hcρ, if_pos rfl]
      omega
  have hG' : ∀ ν, kk ρ ν = kk ρ m' → coeff ν G = 0 := fun ν hν => hmin ν (hν ▸ hmk ▸ hlt)
  have hc0 := congrArg (coeff m') (hinv c hcρ)
  simp only [glAct, LinearMap.sum_apply, MvPolynomial.coeff_sum, coeff_zero] at hc0
  rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (fun i _ => ?_), zero_add] at hc0
  · have hl : ((Fin.last N : Fin (N + 1)) : ℕ) < N + 1 := (Fin.last N).isLt
    rw [if_pos hl] at hc0
    simp only [snoc_vec_last, Bool.false_eq_true, ↓reduceIte, LinearMap.neg_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, coeff_neg, neg_eq_zero] at hc0
    rw [MvPolynomial.coeff_X_mul', if_pos (by simp [hm'])] at hc0
    erw [MvPolynomial.coeff_pderiv] at hc0
    have e1 : m' - Finsupp.single (Fin.last N, ρ) 1 + Finsupp.single (Fin.last N, c) 1 = m := by
      rw [hm', add_tsub_cancel_right,
        tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hc))]
    have e2 : ((m' - Finsupp.single (Fin.last N, ρ) 1 : Fin (N + 1) × Fin r →₀ ℕ) (Fin.last N, c)) + 1 =
        m (Fin.last N, c) := by
      rw [hm', add_tsub_cancel_right, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    rw [e1] at hc0
    have e3 : ((((m' - Finsupp.single (Fin.last N, ρ) 1 : Fin (N + 1) × Fin r →₀ ℕ) (Fin.last N, c) : ℕ) :
        ℚ_[p]) + 1) = ((m (Fin.last N, c) : ℕ) : ℚ_[p]) := by exact_mod_cast e2
    rw [e3] at hc0
    rcases mul_eq_zero.1 hc0 with h | h
    · exact hm h
    · exact hc (by exact_mod_cast h)
  · have hci : ((Fin.castSucc i : Fin (N + 1)) : ℕ) < N + 1 := (Fin.castSucc i).isLt
    rw [if_pos hci]
    split_ifs
    · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact coeff_X_pderiv_castSucc ρ G m' hG' i c ρ
    · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, coeff_neg, neg_eq_zero]
      exact coeff_X_pderiv_castSucc ρ G m' hG' i ρ c

end Formalism.GM.M.FB

set_option linter.unusedSimpArgs false

namespace Formalism.GM.M.FB

open MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Use extensionality with `⟨i, c⟩`. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Distinguish the cases in `hc : c = ρ`. Substitute `hc` using the available equality. Rewrite using `[ext_last, if_pos rfl, ← hrow, Finset.sum_eq_single c]`.

Introduce `b _ hb`. Conclude with `hZ b hb`. Introduce `h`. Conclude with `absurd (Finset.mem_univ c) h`. Rewrite using `[ext_last, if_neg hc, hZ c hc]`.

Rewrite using `[ext_castSucc, res_apply]`.
-/
lemma eq_ext_res (n : ℕ) (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ)
    (hZ : ∀ c, c ≠ ρ → m (Fin.last N, c) = 0) (hrow : ∑ c, m (Fin.last N, c) = n) :
    m = ext n ρ (res m) := by
  ext ⟨i, c⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · by_cases hc : c = ρ
    · subst hc
      rw [ext_last, if_pos rfl, ← hrow, Finset.sum_eq_single c]
      · intro b _ hb
        exact hZ b hb
      · intro h
        exact absurd (Finset.mem_univ c) h
    · rw [ext_last, if_neg hc, hZ c hc]
  · rw [ext_castSucc, res_apply]

/- English proof (translation)
Rewrite using `[← MvPolynomial.mem_range_map_iff_coeffs_subset]`. Conclude with `Iff.rfl`.
-/
lemma mem_IntPol_iff {σ : Type} (x : MvPolynomial σ ℚ_[p]) :
    x ∈ IntPol p σ ↔ (x.coeffs : Set ℚ_[p]) ⊆ Set.range (algebraMap ℤ_[p] ℚ_[p]) := by
  rw [← MvPolynomial.mem_range_map_iff_coeffs_subset]
  exact Iff.rfl

end Formalism.GM.M.FB

namespace Formalism.GM

open MvPolynomial Finset M.FB

/- English proof (translation)
Introduce `p _ N r LL ρ n hS`. Use `⟨fun f _ g _ h => ?_, fun F hF hinv => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Take `⟨hFpol, hFint⟩` from `Submodule.mem_inf.1 hF`. Establish `hFsupp` using `(MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hFpol`.

Establish `hFn : ∀ m ∈ F.support, ∑ c, m (Fin.last N, c) = n` using `fun m hm => by`. Use `(hFsupp (Finset.mem_coe.2 hm)) (Fin.last N)` as an intermediate fact. Rewrite `this` using `[snoc_deg_last]`. Then use the resulting hypothesis. Take `⟨f, hf⟩ : ∃ f, f = ev p ρ F` from `⟨_, rfl⟩`. Establish `hcf : ∀ m', coeff m' f = coeff (ext n ρ m') F` using `fun m' => by rw [hf]; exact coeff_ev ρ n F hFn m'`.

Establish `hfpol : f ∈ M.Pol p r LL`. Rewrite using `[M.Pol, MvPolynomial.mem_restrictSupport_iff]`. Introduce `m' hm'`. Establish `hne : coeff (ext n ρ m') F ≠ 0`. Rewrite using `[← hcf]`.

Conclude with `MvPolynomial.mem_support_iff.1 hm'`. Establish `hmd` using `hFsupp (Finset.mem_coe.2 (MvPolynomial.mem_support_iff.2 hne))`. Introduce `i`. Use `hmd (Fin.castSucc i)` as an intermediate fact. Simplify `this` using `[snoc_deg_castSucc, ext_castSucc]`.

Establish `hfint : f ∈ M.IntPol p (Fin N × Fin r)`. Rewrite `hFint`, the goal using `[mem_IntPol_iff]`. Introduce `x hx`. Take `⟨m', hm', rfl⟩` from `MvPolynomial.mem_coeffs_iff.1 hx`. Rewrite using `[hcf]`.

Apply `hFint` to reduce the goal to its premises. Conclude with `MvPolynomial.coeff_mem_coeffs _ (by rw [← hcf]; exact MvPolynomial.mem_support_iff.1 hm')`. Use `⟨f, Submodule.mem_inf.2 ⟨hfpol, hfint⟩, ?_⟩` and prove the remaining obligations. Establish `hfz : ∀ m ∈ (M.freeze p LL ρ n f).support, ∑ c, m (Fin.last N, c) = n`. Introduce `m hm`.

Use `hom_freeze LL ρ n hS f hfpol (MvPolynomial.mem_support_iff.1 hm)` as an intermediate fact. Rewrite `this` using `[weight_wL]`. Then use the resulting hypothesis. Establish `hG` using `vanish LL n ρ (M.freeze p LL ρ n f - F) (fun c hc => by rw [map_sub, freeze_inv LL ρ n f c hc, hinv c hc, sub_zero]) (fun m hkk => ?_)`. Conclude with `sub_eq_zero.1 hG`. Rewrite using `[MvPolynomial.coeff_sub, sub_eq_zero]`.

Distinguish the cases in `hrow : ∑ c, m (Fin.last N, c) = n`. Establish `hZ : ∀ c, c ≠ ρ → m (Fin.last N, c) = 0` using `fun c hc => by`. Simplify using `only [kk] at hkk`. Conclude with `(Finset.sum_eq_zero_iff.1 hkk) c (Finset.mem_erase.2 ⟨hc, Finset.mem_univ _⟩)`. Rewrite using `[eq_ext_res n ρ m hZ hrow, ← coeff_ev ρ n _ hfz, ← coeff_ev ρ n F hFn, ev_freeze, hf]`.

Establish `h1 : coeff m (M.freeze p LL ρ n f) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hrow (hfz m (MvPolynomial.mem_support_iff.2 h))`. Establish `h2 : coeff m F = 0`. Assume the negation of the conclusion as `h`.

Conclude with `hrow (hFn m (MvPolynomial.mem_support_iff.2 h))`. Rewrite using `[h1, h2]`.
-/
theorem extendBijOn : M.FreezeBij := by
  intro p _ N r LL ρ n hS
  refine ⟨fun f _ g _ h => ?_, fun F hF hinv => ?_⟩
  · calc f = ev p ρ (M.freeze p LL ρ n f) := (ev_freeze LL ρ n f).symm
      _ = ev p ρ (M.freeze p LL ρ n g) := by rw [h]
      _ = g := ev_freeze LL ρ n g
  · obtain ⟨hFpol, hFint⟩ := Submodule.mem_inf.1 hF
    have hFsupp := (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hFpol
    have hFn : ∀ m ∈ F.support, ∑ c, m (Fin.last N, c) = n := fun m hm => by
      have := (hFsupp (Finset.mem_coe.2 hm)) (Fin.last N)
      rwa [snoc_deg_last] at this
    obtain ⟨f, hf⟩ : ∃ f, f = ev p ρ F := ⟨_, rfl⟩
    have hcf : ∀ m', coeff m' f = coeff (ext n ρ m') F := fun m' => by rw [hf]; exact coeff_ev ρ n F hFn m'
    have hfpol : f ∈ M.Pol p r LL := by
      rw [M.Pol, MvPolynomial.mem_restrictSupport_iff]
      intro m' hm'
      have hne : coeff (ext n ρ m') F ≠ 0 := by
        rw [← hcf]
        exact MvPolynomial.mem_support_iff.1 hm'
      have hmd := hFsupp (Finset.mem_coe.2 (MvPolynomial.mem_support_iff.2 hne))
      intro i
      have := hmd (Fin.castSucc i)
      simpa [snoc_deg_castSucc, ext_castSucc] using this
    have hfint : f ∈ M.IntPol p (Fin N × Fin r) := by
      rw [mem_IntPol_iff] at hFint ⊢
      intro x hx
      obtain ⟨m', hm', rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hx
      rw [hcf]
      apply hFint
      exact MvPolynomial.coeff_mem_coeffs _ (by rw [← hcf]; exact MvPolynomial.mem_support_iff.1 hm')
    refine ⟨f, Submodule.mem_inf.2 ⟨hfpol, hfint⟩, ?_⟩
    have hfz : ∀ m ∈ (M.freeze p LL ρ n f).support, ∑ c, m (Fin.last N, c) = n := by
      intro m hm
      have := hom_freeze LL ρ n hS f hfpol (MvPolynomial.mem_support_iff.1 hm)
      rwa [weight_wL] at this
    have hG := vanish LL n ρ (M.freeze p LL ρ n f - F)
      (fun c hc => by rw [map_sub, freeze_inv LL ρ n f c hc, hinv c hc, sub_zero]) (fun m hkk => ?_)
    · exact sub_eq_zero.1 hG
    · rw [MvPolynomial.coeff_sub, sub_eq_zero]
      by_cases hrow : ∑ c, m (Fin.last N, c) = n
      · have hZ : ∀ c, c ≠ ρ → m (Fin.last N, c) = 0 := fun c hc => by
          simp only [kk] at hkk
          exact (Finset.sum_eq_zero_iff.1 hkk) c (Finset.mem_erase.2 ⟨hc, Finset.mem_univ _⟩)
        rw [eq_ext_res n ρ m hZ hrow, ← coeff_ev ρ n _ hfz, ← coeff_ev ρ n F hFn, ev_freeze, hf]
      · have h1 : coeff m (M.freeze p LL ρ n f) = 0 := by
          by_contra h
          exact hrow (hfz m (MvPolynomial.mem_support_iff.2 h))
        have h2 : coeff m F = 0 := by
          by_contra h
          exact hrow (hFn m (MvPolynomial.mem_support_iff.2 h))
        rw [h1, h2]

end Formalism.GM
