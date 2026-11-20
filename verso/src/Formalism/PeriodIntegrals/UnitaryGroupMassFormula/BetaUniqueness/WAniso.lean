import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Skeleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaLUniq

section SigLemmas

variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, conjTranspose_apply]`.
-/
theorem wa_cT_conj_eq {m k : Type} (M : Matrix m k ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, conjTranspose_apply]

/- English proof (translation)
Take `⟨e, P, hP⟩` from `h`. Use `⟨by rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin], ?_⟩` and prove the remaining obligations. Use `⟨(P : Matrix _ _ ℂ).submatrix e id, ?_⟩` and prove the remaining obligations. Rewrite `hP` using `[wa_cT_conj_eq]`. Establish `hJ : J = (J.reindex e e).submatrix e e`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[hJ, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]`. Simplify using `using hP`.
-/
theorem wa_sig_data (J : Matrix n n ℂ) (p q : ℕ) (h : Formalism.UG.HasSignature J p q) :
    Fintype.card n = p + q ∧ ∃ Q : Matrix n (Fin p ⊕ Fin q) ℂ, Qᴴ * J * Q = Formalism.UG.Jpq p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin], ?_⟩
  refine ⟨(P : Matrix _ _ ℂ).submatrix e id, ?_⟩
  rw [wa_cT_conj_eq] at hP
  have hJ : J = (J.reindex e e).submatrix e e := by
    ext i j; simp
  rw [hJ, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
  simpa using hP

/- English proof (translation)
Establish `: star (Q *ᵥ x) ⬝ᵥ (J *ᵥ (Q *ᵥ x)) = star x ⬝ᵥ ((Qᴴ * J * Q) *ᵥ x)`. Rewrite using `[star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, Matrix.mul_assoc]`. Rewrite using `[this, hQ]`. Simplify using `[Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg, neg_mulVec]`.
-/
theorem wa_sig_quad {p q : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Formalism.UG.Jpq p q) (x : Fin p ⊕ Fin q → ℂ) :
    star (Q *ᵥ x) ⬝ᵥ (J *ᵥ (Q *ᵥ x)) =
      (∑ i, star (x (Sum.inl i)) * x (Sum.inl i)) - ∑ j, star (x (Sum.inr j)) * x (Sum.inr j) := by
  have : star (Q *ᵥ x) ⬝ᵥ (J *ᵥ (Q *ᵥ x)) = star x ⬝ᵥ ((Qᴴ * J * Q) *ᵥ x) := by
    rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec,
      Matrix.mul_assoc]
  rw [this, hQ]
  simp [Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg, neg_mulVec]

/- English proof (translation)
Set `M : Matrix n (Fin p ⊕ Fin m) ℂ` to `Matrix.of fun i k => Sum.elim (fun a => Q i (Sum.inl a)) (fun b => V b i) k`. Establish `hinj : Function.Injective M.mulVecLin`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Rewrite `hx` using `[Matrix.mulVecLin_apply]`.

Set `u : Fin p ⊕ Fin q → ℂ` to `Sum.elim (x ∘ Sum.inl) 0`. Establish `hM : M *ᵥ x = Q *ᵥ u + ∑ k, x (Sum.inr k) • V k`. Use function extensionality and compare the values at `i`. Simplify using `[M, u, mulVec, dotProduct, Fintype.sum_sum_type, Finset.sum_apply, mul_comm]`. Rewrite `hx` using `[hM]`.

Establish `hv : ∑ k, x (Sum.inr k) • V k = -(Q *ᵥ u)` using `eq_neg_of_add_eq_zero_right hx`. Establish `h1` using `wa_sig_quad J Q hQ u`. Establish `hn` using `hneg (fun k => x (Sum.inr k))`. Rewrite `hn` using `[hv]`. Simplify using `only [star_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg] at hn`.

Rewrite `hn` using `[h1]`. Simplify using `only [u, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.zero_apply, star_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hn`. Establish `hre : ∀ z : ℂ, (star z * z).re = Complex.normSq z`. Introduce `z`. Simplify using `[Complex.normSq_apply, Complex.mul_re]`.

Simplify using `only [Complex.re_sum, hre] at hn`. Establish `hA` using `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (x (Sum.inl i)))).1 (le_antisymm hn (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)))`. Establish `hxl : ∀ a, x (Sum.inl a) = 0` using `fun a => Complex.normSq_eq_zero.1 (hA a (Finset.mem_univ _))`. Establish `hu0 : u = 0`. Use function extensionality and compare the values at `k`.

Break down `k with a | b` into its components or cases. Simplify using `[u, hxl a]`. Simplify using `[u]`. Rewrite `hv` using `[hu0, mulVec_zero, neg_zero]`. Establish `hxr` using `hV (fun k => x (Sum.inr k)) hv`.

Use function extensionality and compare the values at `k`. Break down `k with a | b` into its components or cases. Conclude with `hxl a`. Conclude with `congrFun hxr b`. Use `LinearMap.finrank_le_finrank_of_injective hinj` as an intermediate fact.

Simplify using `[Module.finrank_fintype_fun_eq_card] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem wa_neg_dim {p q m : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Formalism.UG.Jpq p q) (hc : Fintype.card n = p + q) (V : Fin m → n → ℂ)
    (hV : ∀ x : Fin m → ℂ, ∑ k, x k • V k = 0 → x = 0)
    (hneg : ∀ x : Fin m → ℂ, (star (∑ k, x k • V k) ⬝ᵥ (J *ᵥ ∑ k, x k • V k)).re ≤ 0) :
    m ≤ q := by
  let M : Matrix n (Fin p ⊕ Fin m) ℂ :=
    Matrix.of fun i k => Sum.elim (fun a => Q i (Sum.inl a)) (fun b => V b i) k
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [Matrix.mulVecLin_apply] at hx
    let u : Fin p ⊕ Fin q → ℂ := Sum.elim (x ∘ Sum.inl) 0
    have hM : M *ᵥ x = Q *ᵥ u + ∑ k, x (Sum.inr k) • V k := by
      funext i
      simp [M, u, mulVec, dotProduct, Fintype.sum_sum_type, Finset.sum_apply, mul_comm]
    rw [hM] at hx
    have hv : ∑ k, x (Sum.inr k) • V k = -(Q *ᵥ u) := eq_neg_of_add_eq_zero_right hx
    have h1 := wa_sig_quad J Q hQ u
    have hn := hneg (fun k => x (Sum.inr k))
    rw [hv] at hn
    simp only [star_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg] at hn
    rw [h1] at hn
    simp only [u, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.zero_apply, star_zero,
      mul_zero, Finset.sum_const_zero, sub_zero] at hn
    have hre : ∀ z : ℂ, (star z * z).re = Complex.normSq z := by
      intro z; simp [Complex.normSq_apply, Complex.mul_re]
    simp only [Complex.re_sum, hre] at hn
    have hA := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (x (Sum.inl i)))).1
      (le_antisymm hn (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)))
    have hxl : ∀ a, x (Sum.inl a) = 0 := fun a => Complex.normSq_eq_zero.1 (hA a (Finset.mem_univ _))
    have hu0 : u = 0 := by
      funext k; rcases k with a | b
      · simp [u, hxl a]
      · simp [u]
    rw [hu0, mulVec_zero, neg_zero] at hv
    have hxr := hV (fun k => x (Sum.inr k)) hv
    funext k
    rcases k with a | b
    · exact hxl a
    · exact congrFun hxr b
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simp [Module.finrank_fintype_fun_eq_card] at this
  omega

end SigLemmas

section Emb

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (τ : E →+* ℂ)

def wa_cv (v : S.V) : Fin S.rank → ℂ := fun i => τ (S.frame.repr v i)

variable {S τ}

/- English proof (translation)
Establish `hu` using `S.frame.sum_repr u`. Establish `hv` using `S.frame.sum_repr v`. Use `conv_lhs => rw [← hu, ← hv]`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, map_mul, starRingEnd_apply, hτ]`. Simplify using `only [dotProduct, mulVec, wa_cv, HSpace.gram, Matrix.map_apply, Pi.star_apply, Finset.mul_sum]`.

Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wa_form (hτ : ∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) (u v : S.V) :
    τ (S.hT u v) = star (wa_cv S τ u) ⬝ᵥ ((S.gram.map τ) *ᵥ wa_cv S τ v) := by
  have hu := S.frame.sum_repr u
  have hv := S.frame.sum_repr v
  conv_lhs => rw [← hu, ← hv]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, map_mul, starRingEnd_apply, hτ]
  simp only [dotProduct, mulVec, wa_cv, HSpace.gram, Matrix.map_apply, Pi.star_apply, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/- English proof (translation)
Simplify using `only [star_sum, star_smul, mulVec_sum, mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, ← wa_form hτ]`. Simplify using `only [Finset.mul_sum]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))` and prove the remaining obligations. Rewrite using `[Complex.star_def]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem wa_comb (hτ : ∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) {m : ℕ} (x : Fin m → ℂ)
    (u : Fin m → S.V) :
    star (∑ k, x k • wa_cv S τ (u k)) ⬝ᵥ ((S.gram.map τ) *ᵥ ∑ l, x l • wa_cv S τ (u l)) =
      ∑ k, ∑ l, starRingEnd ℂ (x k) * x l * τ (S.hT (u k) (u l)) := by
  simp only [star_sum, star_smul, mulVec_sum, mulVec_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, ← wa_form hτ]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [Complex.star_def]
  ring

/- English proof (translation)
Set `f` to `Fintype.linearCombination E u`. Establish `hker : LinearMap.ker f = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `c hc`. Rewrite `hc` using `[Fintype.linearCombination_apply]`.

Use function extensionality and compare the values at `k`. Conclude with `Fintype.linearIndependent_iff.1 hu c hc k`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective f hker`. Establish `hgu : ∀ k, g (u k) = Pi.single k 1`. Introduce `k`.

Establish `h1 : f (Pi.single k 1) = u k`. Simplify using `[f, Fintype.linearCombination_apply, Pi.single_apply]`. Rewrite using `[← h1]`. Conclude with `LinearMap.congr_fun hg _`. Use function extensionality and compare the values at `l`.

Establish `hφ : ∀ v : S.V, g v l = ∑ i, S.frame.repr v i * g (S.frame i) l`. Introduce `v`. Use `conv_lhs => rw [← S.frame.sum_repr v]`. Simplify using `only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Establish `key : ∀ k, ∑ i, wa_cv S τ (u k) i * τ (g (S.frame i) l) = if l = k then 1 else 0`.

Introduce `k`. Establish `h2` using `congrArg τ (hφ (u k))`. Rewrite `h2` using `[hgu k]`. Simplify using `only [map_sum, map_mul] at h2`. Simplify using `only [wa_cv]`.

Rewrite using `[← h2]`. Distinguish the cases in `h : l = k`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.

Establish `h0 : ∑ i, (∑ k, x k • wa_cv S τ (u k)) i * τ (g (S.frame i) l) = 0`. Rewrite using `[hx]`. Simplify using the standard rewrite rules. Establish `h3 : ∑ i, (∑ k, x k • wa_cv S τ (u k)) i * τ (g (S.frame i) l) = ∑ k, x k * ∑ i, wa_cv S τ (u k) i * τ (g (S.frame i) l)`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite `h0` using `[h3]`. Simplify using `only [key, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h0`.

Simplify using `using h0`.
-/
theorem wa_indep {m : ℕ} (u : Fin m → S.V) (hu : LinearIndependent E u) (x : Fin m → ℂ)
    (hx : ∑ k, x k • wa_cv S τ (u k) = 0) : x = 0 := by
  classical
  let f := Fintype.linearCombination E u
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [Fintype.linearCombination_apply] at hc
    funext k
    exact Fintype.linearIndependent_iff.1 hu c hc k
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  have hgu : ∀ k, g (u k) = Pi.single k 1 := by
    intro k
    have h1 : f (Pi.single k 1) = u k := by
      simp [f, Fintype.linearCombination_apply, Pi.single_apply]
    rw [← h1]
    exact LinearMap.congr_fun hg _
  funext l
  have hφ : ∀ v : S.V, g v l = ∑ i, S.frame.repr v i * g (S.frame i) l := by
    intro v
    conv_lhs => rw [← S.frame.sum_repr v]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have key : ∀ k, ∑ i, wa_cv S τ (u k) i * τ (g (S.frame i) l) = if l = k then 1 else 0 := by
    intro k
    have h2 := congrArg τ (hφ (u k))
    rw [hgu k] at h2
    simp only [map_sum, map_mul] at h2
    simp only [wa_cv]
    rw [← h2]
    by_cases h : l = k
    · subst h; simp
    · simp [h]
  have h0 : ∑ i, (∑ k, x k • wa_cv S τ (u k)) i * τ (g (S.frame i) l) = 0 := by
    rw [hx]; simp
  have h3 : ∑ i, (∑ k, x k • wa_cv S τ (u k)) i * τ (g (S.frame i) l) =
      ∑ k, x k * ∑ i, wa_cv S τ (u k) i * τ (g (S.frame i) l) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  rw [h3] at h0
  simp only [key, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h0
  simpa using h0

end Emb

section D7

open PI.BetaLUniq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D u' F' w hw hww`. Assume the negation of the conclusion as `hwX`. Take `⟨τ⟩ : Nonempty (D.host.E →+* ℂ)` from `inferInstance`. Establish `hτ : ∀ a : D.host.E, τ (star a) = starRingEnd ℂ (τ a)` using `D.sp.cm.cmUnram.2.1 τ`. Establish `hTpos : 0 < Tu D u'` using `(D.mem u').A.T_prime.pos`.

Establish `hTE : ((Tu D u' : ℕ) : D.host.E) ≠ 0` using `by exact_mod_cast hTpos.ne'`. Establish `hsymm : ∀ x y : (hS D).V, (hS D).hT y x = star ((hS D).hT x y)`. Introduce `x y`. Rewrite using `[← (hS D).herm.eq x y, starRingEnd_apply]`. Establish `horth` using `(mem_orth (hS D)).1 hw`.

Establish `hez : ∀ a, (hS D).hT (F'.fl.e a) F'.fl.z = 0` using `F'.fl.z_orth`. Establish `hze : ∀ a, (hS D).hT F'.fl.z (F'.fl.e a) = 0`. Introduce `a`. Rewrite using `[hsymm, hez, star_zero]`. Establish `hXz : ∀ x ∈ Xsp F', (hS D).hT x F'.fl.z = 0`.

Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, rfl⟩` from `hy`. Conclude with `hez a`.

Consider the case `zero => simp`. Consider the case `add y y' _ _ h1 h2 => simp [h1, h2]`. Consider the case `smul c y _ h1 => simp [h1]`. Establish `hzX : ∀ x ∈ Xsp F', (hS D).hT F'.fl.z x = 0`. Introduce `x hx`.

Rewrite using `[hsymm, hXz x hx, star_zero]`. Establish `hzz : (hS D).hT F'.fl.z F'.fl.z = -((Tu D u' : ℕ) : D.host.E)` using `F'.fl.z_norm`. Establish `he_mem : ∀ a, F'.fl.e a ∈ Xplus F'` using `fun a => Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)`. Establish `hz_mem : F'.fl.z ∈ Xplus F'` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Establish `hew : ∀ a, (hS D).hT (F'.fl.e a) w = 0` using `fun a => horth _ (he_mem a)`.

Establish `hzw : (hS D).hT F'.fl.z w = 0` using `horth _ hz_mem`. Establish `hwe : ∀ a, (hS D).hT w (F'.fl.e a) = 0` using `by intro a; rw [hsymm, hew, star_zero]`. Establish `hwz : (hS D).hT w F'.fl.z = 0` using `by rw [hsymm, hzw, star_zero]`. Establish `hzX' : F'.fl.z ∉ Submodule.span D.host.E (Set.range F'.fl.e)`. Introduce `h`.

Use `hXz _ h` as an intermediate fact. Rewrite `this` using `[hzz]`. Conclude with `hTE (neg_eq_zero.1 this)`. Establish `hwX' : w ∉ Submodule.span D.host.E (Set.range (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V))`. Introduce `h`.

Establish `hle : Submodule.span D.host.E (Set.range (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V)) ≤ Xsp F' ⊔ Submodule.span D.host.E {F'.fl.z}`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`.

Simplify using `only [Fin.snoc_last]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Consider the case `cast a`. Simplify using `only [Fin.snoc_castSucc]`. Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)`.

Take `⟨x, hx, y, hy, hxy⟩` from `Submodule.mem_sup.1 (hle h)`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Establish `h0 : (hS D).hT F'.fl.z (x + c • F'.fl.z) = 0` using `by rw [hxy]; exact hzw`. Rewrite `h0` using `[map_add, hzX x hx, map_smul, hzz, zero_add, smul_eq_mul]`. Establish `hc : c = 0`.

Break down `mul_eq_zero.1 h0 with h' | h'` into its components or cases. Conclude with `h'`. Conclude with `absurd (neg_eq_zero.1 h') hTE`. Apply `hwX` to reduce the goal to its premises. Rewrite using `[← hxy, hc, zero_smul, add_zero]`.

Conclude with `hx`. Set `u : Fin (D.R.rS + 1 + 1) → (hS D).V` to `Fin.snoc (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V) w`. Establish `hu : LinearIndependent D.host.E u` using `linearIndependent_finSnoc.2 ⟨linearIndependent_finSnoc.2 ⟨F'.fl.e_indep, hzX'⟩, hwX'⟩`. Set `zi : Fin (D.R.rS + 1 + 1)` to `Fin.castSucc (Fin.last D.R.rS)`. Establish `huz : u zi = F'.fl.z` using `by simp [u, zi]`.

Establish `hk : ∀ k, k ≠ zi → ∀ l, (hS D).hT (u k) (u l) = 0`. Introduce `k hk l`. Proceed by induction on `k using Fin.lastCases with`. Consider the case `last`. Simplify using `only [u, Fin.snoc_last]`.

Proceed by induction on `l using Fin.lastCases with`. Consider the case `last => simpa [Fin.snoc_last] using hww`. Consider the case `cast l'`. Proceed by induction on `l' using Fin.lastCases with`. Consider the case `last => simpa [Fin.snoc_castSucc, Fin.snoc_last] using hwz`.

Consider the case `cast b => simpa [Fin.snoc_castSucc] using hwe b`. Consider the case `cast k'`. Proceed by induction on `k' using Fin.lastCases with`. Consider the case `last => exact absurd rfl hk`. Consider the case `cast a`.

Simplify using `only [u, Fin.snoc_castSucc]`. Proceed by induction on `l using Fin.lastCases with`. Consider the case `last => simpa [Fin.snoc_last] using hew a`. Consider the case `cast l'`. Proceed by induction on `l' using Fin.lastCases with`.

Consider the case `last => simpa [Fin.snoc_castSucc, Fin.snoc_last] using hez a`. Consider the case `cast b => simpa [Fin.snoc_castSucc] using F'.fl.e_iso a b`. Establish `hl : ∀ l, l ≠ zi → (hS D).hT F'.fl.z (u l) = 0`. Introduce `l hl`. Proceed by induction on `l using Fin.lastCases with`.

Consider the case `last => simpa [u, Fin.snoc_last] using hzw`. Consider the case `cast l'`. Proceed by induction on `l' using Fin.lastCases with`. Consider the case `last => exact absurd rfl hl`. Consider the case `cast b => simpa [u, Fin.snoc_castSucc] using hze b`.

Establish `hsig : Formalism.UG.HasSignature (((hS D).gram).map τ) (D.R.k + D.R.rS) (D.R.rS + 1)`. Establish `h` using `D.sp.Y_sig 0 τ`. Rewrite `h` using `[D.sp.baseSpace_signature_eq τ]`. Conclude with `h`. Take `⟨hcard, Q, hQ⟩` from `wa_sig_data _ _ _ hsig`.

Establish `hdim` using `wa_neg_dim (((hS D).gram).map τ) Q hQ hcard (fun k => wa_cv (hS D) τ (u k)) (fun x hx => wa_indep u hu x hx) (by`. Introduce `x`. Rewrite using `[wa_comb hτ x u]`. Rewrite using `[Fintype.sum_eq_single zi (fun k hk' => Finset.sum_eq_zero (fun l _ => by`. Rewrite using `[hk k hk' l, map_zero, mul_zero]))]`.

Rewrite using `[Fintype.sum_eq_single zi (fun l hl' => by rw [huz, hl l hl', map_zero, mul_zero])]`. Rewrite using `[huz, hzz, map_neg, map_natCast]`. Establish `h1 : starRingEnd ℂ (x zi) * x zi = (Complex.normSq (x zi) : ℂ)`. Rewrite using `[mul_comm]`. Conclude with `Complex.mul_conj (x zi)`.

Rewrite using `[h1]`. Establish `h2 : ((Complex.normSq (x zi) : ℂ) * -((Tu D u' : ℕ) : ℂ)).re = -(Complex.normSq (x zi) * (Tu D u' : ℝ))`. Simplify using `[Complex.mul_re]`. Rewrite using `[h2]`. Use `Complex.normSq_nonneg (x zi)` as an intermediate fact.

Establish `: (0 : ℝ) ≤ (Tu D u' : ℝ)` using `Nat.cast_nonneg _`. Use the proof step `nlinarith)`. Use linear arithmetic over natural numbers and integers.
-/
theorem weight_space_anisotropic : WAniso := by
  intro D u' F' w hw hww
  by_contra hwX
  classical
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hτ : ∀ a : D.host.E, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have hTpos : 0 < Tu D u' := (D.mem u').A.T_prime.pos
  have hTE : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTpos.ne'
  have hsymm : ∀ x y : (hS D).V, (hS D).hT y x = star ((hS D).hT x y) := by
    intro x y
    rw [← (hS D).herm.eq x y, starRingEnd_apply]
  have horth := (mem_orth (hS D)).1 hw
  have hez : ∀ a, (hS D).hT (F'.fl.e a) F'.fl.z = 0 := F'.fl.z_orth
  have hze : ∀ a, (hS D).hT F'.fl.z (F'.fl.e a) = 0 := by
    intro a; rw [hsymm, hez, star_zero]
  have hXz : ∀ x ∈ Xsp F', (hS D).hT x F'.fl.z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact hez a
    | zero => simp
    | add y y' _ _ h1 h2 => simp [h1, h2]
    | smul c y _ h1 => simp [h1]
  have hzX : ∀ x ∈ Xsp F', (hS D).hT F'.fl.z x = 0 := by
    intro x hx; rw [hsymm, hXz x hx, star_zero]
  have hzz : (hS D).hT F'.fl.z F'.fl.z = -((Tu D u' : ℕ) : D.host.E) := F'.fl.z_norm
  have he_mem : ∀ a, F'.fl.e a ∈ Xplus F' := fun a =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  have hz_mem : F'.fl.z ∈ Xplus F' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hew : ∀ a, (hS D).hT (F'.fl.e a) w = 0 := fun a => horth _ (he_mem a)
  have hzw : (hS D).hT F'.fl.z w = 0 := horth _ hz_mem
  have hwe : ∀ a, (hS D).hT w (F'.fl.e a) = 0 := by intro a; rw [hsymm, hew, star_zero]
  have hwz : (hS D).hT w F'.fl.z = 0 := by rw [hsymm, hzw, star_zero]
  have hzX' : F'.fl.z ∉ Submodule.span D.host.E (Set.range F'.fl.e) := by
    intro h
    have := hXz _ h
    rw [hzz] at this
    exact hTE (neg_eq_zero.1 this)
  have hwX' : w ∉ Submodule.span D.host.E
      (Set.range (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V)) := by
    intro h
    have hle : Submodule.span D.host.E
        (Set.range (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V)) ≤
        Xsp F' ⊔ Submodule.span D.host.E {F'.fl.z} := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      | cast a =>
        simp only [Fin.snoc_castSucc]
        exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hle h)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have h0 : (hS D).hT F'.fl.z (x + c • F'.fl.z) = 0 := by rw [hxy]; exact hzw
    rw [map_add, hzX x hx, map_smul, hzz, zero_add, smul_eq_mul] at h0
    have hc : c = 0 := by
      rcases mul_eq_zero.1 h0 with h' | h'
      · exact h'
      · exact absurd (neg_eq_zero.1 h') hTE
    apply hwX
    rw [← hxy, hc, zero_smul, add_zero]
    exact hx
  let u : Fin (D.R.rS + 1 + 1) → (hS D).V :=
    Fin.snoc (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V) w
  have hu : LinearIndependent D.host.E u :=
    linearIndependent_finSnoc.2 ⟨linearIndependent_finSnoc.2 ⟨F'.fl.e_indep, hzX'⟩, hwX'⟩
  let zi : Fin (D.R.rS + 1 + 1) := Fin.castSucc (Fin.last D.R.rS)
  have huz : u zi = F'.fl.z := by simp [u, zi]
  have hk : ∀ k, k ≠ zi → ∀ l, (hS D).hT (u k) (u l) = 0 := by
    intro k hk l
    induction k using Fin.lastCases with
    | last =>
      simp only [u, Fin.snoc_last]
      induction l using Fin.lastCases with
      | last => simpa [Fin.snoc_last] using hww
      | cast l' =>
        induction l' using Fin.lastCases with
        | last => simpa [Fin.snoc_castSucc, Fin.snoc_last] using hwz
        | cast b => simpa [Fin.snoc_castSucc] using hwe b
    | cast k' =>
      induction k' using Fin.lastCases with
      | last => exact absurd rfl hk
      | cast a =>
        simp only [u, Fin.snoc_castSucc]
        induction l using Fin.lastCases with
        | last => simpa [Fin.snoc_last] using hew a
        | cast l' =>
          induction l' using Fin.lastCases with
          | last => simpa [Fin.snoc_castSucc, Fin.snoc_last] using hez a
          | cast b => simpa [Fin.snoc_castSucc] using F'.fl.e_iso a b
  have hl : ∀ l, l ≠ zi → (hS D).hT F'.fl.z (u l) = 0 := by
    intro l hl
    induction l using Fin.lastCases with
    | last => simpa [u, Fin.snoc_last] using hzw
    | cast l' =>
      induction l' using Fin.lastCases with
      | last => exact absurd rfl hl
      | cast b => simpa [u, Fin.snoc_castSucc] using hze b
  have hsig : Formalism.UG.HasSignature (((hS D).gram).map τ) (D.R.k + D.R.rS) (D.R.rS + 1) := by
    have h := D.sp.Y_sig 0 τ
    rw [D.sp.baseSpace_signature_eq τ] at h
    exact h
  obtain ⟨hcard, Q, hQ⟩ := wa_sig_data _ _ _ hsig
  have hdim := wa_neg_dim (((hS D).gram).map τ) Q hQ hcard (fun k => wa_cv (hS D) τ (u k))
    (fun x hx => wa_indep u hu x hx) (by
      intro x
      rw [wa_comb hτ x u]
      rw [Fintype.sum_eq_single zi (fun k hk' => Finset.sum_eq_zero (fun l _ => by
        rw [hk k hk' l, map_zero, mul_zero]))]
      rw [Fintype.sum_eq_single zi (fun l hl' => by rw [huz, hl l hl', map_zero, mul_zero])]
      rw [huz, hzz, map_neg, map_natCast]
      have h1 : starRingEnd ℂ (x zi) * x zi = (Complex.normSq (x zi) : ℂ) := by
        rw [mul_comm]; exact Complex.mul_conj (x zi)
      rw [h1]
      have h2 : ((Complex.normSq (x zi) : ℂ) * -((Tu D u' : ℕ) : ℂ)).re =
          -(Complex.normSq (x zi) * (Tu D u' : ℝ)) := by
        simp [Complex.mul_re]
      rw [h2]
      have := Complex.normSq_nonneg (x zi)
      have : (0 : ℝ) ≤ (Tu D u' : ℝ) := Nat.cast_nonneg _
      nlinarith)
  omega

end D7

end PI.UnitaryGroupMassFormula.BetaLUniq
