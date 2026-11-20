import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

/- English proof (translation)
Establish `hspan : Submodule.span K (Set.range fun i => M i) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Establish `hfx : ∀ x : Fin r → K, f x = ∑ k, x k * f (Pi.single k 1)`. Introduce `x`.

Use `conv_lhs => rw [← (Pi.basisFun K (Fin r)).sum_repr x]`. Simplify using `[map_sum, smul_eq_mul]`. Establish `hc : M.mulVec (fun k => f (Pi.single k 1)) = 0`. Use function extensionality and compare the values at `i`. Establish `hi : M i ∈ LinearMap.ker f` using `hf (Submodule.subset_span ⟨i, rfl⟩)`.

Rewrite `hi` using `[LinearMap.mem_ker, hfx]`. Conclude with `hi`. Establish `hc0` using `hM _ hc`. Apply `hf0` to reduce the goal to its premises. Apply `(Pi.basisFun K (Fin r)).ext` to reduce the goal to its premises.

Introduce `k`. Establish `hk` using `congrFun hc0 k`. Simplify using `using hk`. Take `⟨κ, a, ha, hsp, hli⟩` from `exists_linearIndependent' K (fun i => M i)`. Establish `hsp' : Submodule.span K (Set.range ((fun i => M i) ∘ a)) = ⊤` using `hsp.trans hspan`.

Use `haveI : Finite κ := Finite.of_injective a ha`. Use `haveI : Fintype κ := Fintype.ofFinite κ`. Set `B` to `Module.Basis.mk hli hsp'.ge`. Establish `hcard : Fintype.card κ = r`. Establish `h` using `Module.finrank_eq_card_basis B`.

Simplify using `using h.symm`. Set `e : Fin r ≃ κ` to `(Fintype.equivFinOfCardEq hcard).symm`. Use `⟨a ∘ e, ?_⟩` and prove the remaining obligations. Establish `hli2 : LinearIndependent K (Matrix.row (M.submatrix (a ∘ e) id))` using `hli.comp e e.injective`. Rewrite `hli2` using `[Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`.

Conclude with `hli2`.
-/
theorem gs_exists_rows_det_ne_zero {K : Type*} [Field K] {t r : ℕ} (M : Matrix (Fin t) (Fin r) K)
    (hM : ∀ c : Fin r → K, M.mulVec c = 0 → c = 0) :
    ∃ a : Fin r → Fin t, (M.submatrix a id).det ≠ 0 := by
  classical

  have hspan : Submodule.span K (Set.range fun i => M i) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hfx : ∀ x : Fin r → K, f x = ∑ k, x k * f (Pi.single k 1) := by
      intro x
      conv_lhs => rw [← (Pi.basisFun K (Fin r)).sum_repr x]
      simp [map_sum, smul_eq_mul]
    have hc : M.mulVec (fun k => f (Pi.single k 1)) = 0 := by
      funext i
      have hi : M i ∈ LinearMap.ker f := hf (Submodule.subset_span ⟨i, rfl⟩)
      rw [LinearMap.mem_ker, hfx] at hi
      exact hi
    have hc0 := hM _ hc
    apply hf0
    apply (Pi.basisFun K (Fin r)).ext
    intro k
    have hk := congrFun hc0 k
    simpa using hk

  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K (fun i => M i)
  have hsp' : Submodule.span K (Set.range ((fun i => M i) ∘ a)) = ⊤ := hsp.trans hspan
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  let B := Module.Basis.mk hli hsp'.ge
  have hcard : Fintype.card κ = r := by
    have h := Module.finrank_eq_card_basis B
    simpa using h.symm
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hli2 : LinearIndependent K (Matrix.row (M.submatrix (a ∘ e) id)) :=
    hli.comp e e.injective
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero] at hli2
  exact hli2

/- English proof (translation)
Establish `key : ∀ m ∈ (pderiv j p).support, ∃ m' ∈ p.support, m = m' - Finsupp.single j 1`. Introduce `m hm`. Rewrite `hm` using `[p.as_sum, map_sum]`. Take `⟨m', hm', hmm⟩` from `Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)`. Rewrite `hmm` using `[pderiv_monomial]`.

Conclude with `⟨m', hm', Finset.mem_singleton.1 (support_monomial_subset hmm)⟩`. Establish `hdeg : ∀ m ∈ (pderiv j p).support, m j < degreeOf j p`. Introduce `m hm`. Take `⟨m', hm', rfl⟩` from `key m hm`. Establish `h1` using `monomial_le_degreeOf j hm'`.

Establish `h2 : (m' - Finsupp.single j 1 : σ →₀ ℕ) j = m' j - 1` using `by simp`. Rewrite using `[h2]`. Use linear arithmetic over natural numbers and integers. Use `⟨?_, (degreeOf_lt_iff hj).2 hdeg, ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨m', hm', hm'j⟩ : ∃ m' ∈ p.support, 0 < m' j := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `h3 : degreeOf j p < 1` using `(degreeOf_lt_iff one_pos).2 (fun m hm => by have := hcon m hm; omega)`. Use linear arithmetic over natural numbers and integers. Introduce `h0`.

Establish `hc : coeff (m' - Finsupp.single j 1) (pderiv j p) = coeff m' p * (m' j : ℚ)` using `by conv_lhs => rw [p.as_sum]`. Rewrite using `[map_sum, coeff_sum]`. Simplify using `only [pderiv_monomial, coeff_monomial]`. Rewrite using `[Finset.sum_eq_single m']`. Simplify using the standard rewrite rules.

Introduce `b _ hne split_ifs with h`. Establish `hbj : b j = 0`. Assume the negation of the conclusion as `hbj`. Apply `hne` to reduce the goal to its premises. Establish `e1 : b - Finsupp.single j 1 + Finsupp.single j 1 = b` using `tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))`.

Establish `e2 : m' - Finsupp.single j 1 + Finsupp.single j 1 = m'` using `tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))`. Rewrite using `[← e1, ← e2, h]`. Simplify using `[hbj]`. Both sides reduce to the same expression. Introduce `h`.

Conclude with `absurd hm' h`. Rewrite `hc` using `[h0, coeff_zero]`. Establish `hne : coeff m' p ≠ 0` using `mem_support_iff.1 hm'`. Establish `hne2 : (m' j : ℚ) ≠ 0` using `by exact_mod_cast hm'j.ne'`. Conclude with `mul_ne_zero hne hne2 hc.symm`.

Introduce `i hi`. Rewrite `hi`, the goal using `[mem_vars]`. Take `⟨m, hm, him⟩` from `hi`. Take `⟨m', hm', rfl⟩` from `key m hm`. Use `⟨m', hm', ?_⟩` and prove the remaining obligations.

Rewrite `him`, the goal using `[Finsupp.mem_support_iff]`. Introduce `h0`. Apply `him` to reduce the goal to its premises. Simplify using `[h0]`.
-/
theorem gs_pderiv_facts {σ : Type*} (p : MvPolynomial σ ℚ) (j : σ) (hj : 0 < degreeOf j p) :
    pderiv j p ≠ 0 ∧ degreeOf j (pderiv j p) < degreeOf j p ∧
      (pderiv j p).vars ⊆ p.vars := by
  classical

  have key : ∀ m ∈ (pderiv j p).support, ∃ m' ∈ p.support, m = m' - Finsupp.single j 1 := by
    intro m hm
    rw [p.as_sum, map_sum] at hm
    obtain ⟨m', hm', hmm⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
    rw [pderiv_monomial] at hmm
    exact ⟨m', hm', Finset.mem_singleton.1 (support_monomial_subset hmm)⟩
  have hdeg : ∀ m ∈ (pderiv j p).support, m j < degreeOf j p := by
    intro m hm
    obtain ⟨m', hm', rfl⟩ := key m hm
    have h1 := monomial_le_degreeOf j hm'
    have h2 : (m' - Finsupp.single j 1 : σ →₀ ℕ) j = m' j - 1 := by simp
    rw [h2]
    omega
  refine ⟨?_, (degreeOf_lt_iff hj).2 hdeg, ?_⟩
  · obtain ⟨m', hm', hm'j⟩ : ∃ m' ∈ p.support, 0 < m' j := by
      by_contra hcon
      push_neg at hcon
      have h3 : degreeOf j p < 1 :=
        (degreeOf_lt_iff one_pos).2 (fun m hm => by have := hcon m hm; omega)
      omega
    intro h0
    have hc : coeff (m' - Finsupp.single j 1) (pderiv j p) = coeff m' p * (m' j : ℚ) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum, coeff_sum]
      simp only [pderiv_monomial, coeff_monomial]
      rw [Finset.sum_eq_single m']
      · simp
      · intro b _ hne
        split_ifs with h
        · have hbj : b j = 0 := by
            by_contra hbj
            apply hne
            have e1 : b - Finsupp.single j 1 + Finsupp.single j 1 = b :=
              tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))
            have e2 : m' - Finsupp.single j 1 + Finsupp.single j 1 = m' :=
              tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))
            rw [← e1, ← e2, h]
          simp [hbj]
        · rfl
      · intro h
        exact absurd hm' h
    rw [h0, coeff_zero] at hc
    have hne : coeff m' p ≠ 0 := mem_support_iff.1 hm'
    have hne2 : (m' j : ℚ) ≠ 0 := by exact_mod_cast hm'j.ne'
    exact mul_ne_zero hne hne2 hc.symm
  · intro i hi
    rw [mem_vars] at hi ⊢
    obtain ⟨m, hm, him⟩ := hi
    obtain ⟨m', hm', rfl⟩ := key m hm
    refine ⟨m', hm', ?_⟩
    rw [Finsupp.mem_support_iff] at him ⊢
    intro h0
    apply him
    simp [h0]

/- English proof (translation)
Set `A` to `MvPolynomial σ ℚ ⧸ 𝔭`. Use `haveI : IsDomain A := Ideal.Quotient.isDomain 𝔭`. Set `K` to `FractionRing A`. Set `π : MvPolynomial σ ℚ →+* K` to `(algebraMap A K).comp (Ideal.Quotient.mk 𝔭)`. Establish `hπ : ∀ f, π f = 0 ↔ f ∈ 𝔭`.

Introduce `f`. Simplify using `only [π, RingHom.comp_apply]`. Rewrite using `[IsFractionRing.to_map_eq_zero_iff (R := A) (K := K), Ideal.Quotient.eq_zero_iff_mem]`. Set `xb : σ → A` to `fun s => Ideal.Quotient.mk 𝔭 (X s)`. Establish `hmk : Ideal.Quotient.mkₐ ℚ 𝔭 = aeval xb` using `MvPolynomial.algHom_ext fun s => by`.

Rewrite using `[aeval_X, Ideal.Quotient.mkₐ_eq_mk]`. Establish `hmk' : ∀ f, Ideal.Quotient.mk 𝔭 f = aeval xb f` using `fun f => by`. Rewrite using `[← hmk, Ideal.Quotient.mkₐ_eq_mk]`. Use `haveI : Algebra.FiniteType ℚ A := inferInstance`. Take `⟨s0, hs1, hs2⟩` from `ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℚ) (A := A)`.

Establish `hs0 : s0 = d`. Establish `: (s0 : WithBot ℕ∞) = (d : WithBot ℕ∞)` using `hs1.symm.trans hd`. Conclude with `this` after adjusting the coercions. Substitute `hs0` using the available equality. Use `haveI : FaithfulSMul ℚ A := (faithfulSMul_iff_algebraMap_injective ℚ A).mpr (algebraMap ℚ A).injective`.

Establish `hadj : Algebra.adjoin ℚ (Set.range xb) = ⊤`. Rewrite using `[Algebra.adjoin_range_eq_range_aeval, ← hmk]`. Use `eq_top_iff.mpr fun x _ => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Ideal.Quotient.mkₐ_surjective ℚ 𝔭 x`. Conclude with `⟨y, rfl⟩`.

Use `haveI : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range xb)) A := by`. Prove the components needed by the constructor for the conclusion. Introduce `a`. Establish `ha : a ∈ Algebra.adjoin ℚ (Set.range xb)` using `by rw [hadj]; trivial`. Conclude with `isAlgebraic_algebraMap (R := Algebra.adjoin ℚ (Set.range xb)) (A := A) (⟨a, ha⟩ : Algebra.adjoin ℚ (Set.range xb))`.

Take `⟨u, hu, hub⟩` from `exists_isTranscendenceBasis_subset (R := ℚ) (Set.range xb)`. Use `haveI : Finite u := ((Set.finite_range xb).subset hu).to_subtype`. Use `haveI : Fintype u := Fintype.ofFinite u`. Establish `hcardu : Fintype.card u = s0`. Establish `h1` using `hub.cardinalMk_eq_trdeg`.

Rewrite `h1` using `[hs2, Cardinal.mk_fintype]`. Conclude with `h1` after adjusting the coercions. Set `g : u → σ` to `fun y => (hu y.2).choose`. Establish `hg : ∀ y, xb (g y) = y` using `fun y => (hu y.2).choose_spec`. Establish `hginj : Function.Injective g`.

Introduce `y y' h`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hg y, ← hg y', h]`. Establish `hind : ∀ Q : MvPolynomial σ ℚ, (↑Q.vars : Set σ) ⊆ Set.range g → Q ∈ 𝔭 → Q = 0`. Introduce `Q hQ hQp`.

Take `⟨q, rfl⟩` from `exists_rename_eq_of_vars_subset_range Q g hginj hQ`. Establish `h0 : aeval ((↑) : u → A) q = 0`. Rewrite `hQp` using `[← Ideal.Quotient.eq_zero_iff_mem, hmk', aeval_rename]`. Establish `hfun : ((↑) : u → A) = xb ∘ g` using `funext fun y => (hg y).symm`. Rewrite using `[hfun]`.

Conclude with `hQp`. Rewrite using `[hub.1.eq_zero_of_aeval_eq_zero q h0, map_zero]`. Establish `hrel : ∀ j, j ∉ Set.range g → ∃ Q : MvPolynomial σ ℚ, Q ∈ 𝔭 ∧ Q ≠ 0 ∧ (↑Q.vars : Set σ) ⊆ insert j (Set.range g)`. Introduce `j hj`. Set `w : Option u → A` to `fun o => o.elim (xb j) ((↑) : u → A)`.

Establish `hw : ¬ AlgebraicIndependent ℚ w`. Introduce `h`. Rewrite `h` using `[AlgebraicIndependent.option_iff]`. Conclude with `h.2 (hub.isAlgebraic.isAlgebraic (xb j))`. Rewrite `hw` using `[algebraicIndependent_iff]`.

Use `push_neg at hw`. Take `⟨p, hp0, hp⟩` from `hw`. Set `h : Option u → σ` to `fun o => o.elim j g`. Establish `hinj : Function.Injective h`. Introduce and unpack `(_ | y) (_ | y') hyy`.

Both sides reduce to the same expression. Conclude with `absurd ⟨y', hyy.symm⟩ hj`. Conclude with `absurd ⟨y, hyy⟩ hj`. Conclude with `congr_arg some (hginj hyy)`. Use `⟨rename h p, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, hmk', aeval_rename]`. Establish `hfun : xb ∘ h = w`. Use function extensionality and compare the values at `o`. Consider the cases of `o with`. Consider the case `none => rfl`.

Consider the case `some y => exact hg y`. Rewrite using `[hfun]`. Conclude with `hp0`. Conclude with `fun h0 => hp ((rename_injective h hinj) (h0.trans (map_zero _).symm))`. Introduce `i hi`.

Use `vars_rename h p (Finset.mem_coe.mp hi)` as an intermediate fact. Take `⟨o, -, rfl⟩` from `Finset.mem_image.mp this`. Consider the cases of `o with`. Consider the case `none => exact Set.mem_insert _ _`. Consider the case `some y => exact Set.mem_insert_of_mem _ ⟨y, rfl⟩`.

Establish `hT : Fintype.card {j // j ∉ Set.range g} = Fintype.card σ - s0`. Rewrite using `[Fintype.card_subtype_compl, ← hcardu]`. Use `congr 1`. Rewrite using `[← Set.card_range_of_injective hginj]`. Set `e : {j // j ∉ Set.range g} ≃ Fin (Fintype.card σ - s0)` to `Fintype.equivFinOfCardEq hT`.

Set `b : Fin (Fintype.card σ - s0) → σ` to `fun k => (e.symm k).1`. Establish `hb : ∀ k, b k ∉ Set.range g` using `fun k => (e.symm k).2`. Establish `hbinj : Function.Injective b` using `fun k k' h => e.symm.injective (Subtype.ext h)`. Set `M : Matrix (Fin t) (Fin (Fintype.card σ - s0)) K` to `Matrix.of fun i k => π (pderiv (b k) (G i))`. Establish `hM : ∀ c, M.mulVec c = 0 → c = 0`.

Introduce `c hc`. Set `D : MvPolynomial σ ℚ → K` to `fun f => ∑ k, π (pderiv (b k) f) * c k`. Establish `hDG : ∀ i, D (G i) = 0` using `fun i => by`. Use `congr_fun hc i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, M, D]`.

Establish `hDp : ∀ f ∈ 𝔭, D f = 0`. Introduce `f hf`. Rewrite `hf` using `[← hG]`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨i, rfl⟩` from `hx`. Conclude with `hDG i`. Consider the case `zero => simp [D]`. Consider the case `add x y _ _ hx hy`. Establish `: D (x + y) = D x + D y`.

Simplify using `only [D, map_add, add_mul, Finset.sum_add_distrib]`. Rewrite using `[this, hx, hy, add_zero]`. Consider the case `smul a x hx' hx`. Establish `hx0 : π x = 0` using `(hπ x).2 (hG ▸ hx')`. Establish `: D (a • x) = π a * D x`.

Simplify using `only [D, smul_eq_mul, Derivation.leibniz, map_add, map_mul, hx0, zero_mul, add_zero, Finset.mul_sum, mul_assoc]`. Rewrite using `[this, hx, mul_zero]`. Use function extensionality and compare the values at `k0`. Set `j` to `b k0`. Establish `hj : j ∉ Set.range g` using `hb k0`.

Establish `hex : ∃ n, ∃ Q : MvPolynomial σ ℚ, Q ∈ 𝔭 ∧ Q ≠ 0 ∧ (↑Q.vars : Set σ) ⊆ insert j (Set.range g) ∧ degreeOf j Q = n`. Take `⟨Q, h1, h2, h3⟩` from `hrel j hj`. Conclude with `⟨_, Q, h1, h2, h3, rfl⟩`. Take `⟨Q, hQp, hQ0, hQv, hQd⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ Q' : MvPolynomial σ ℚ, Q' ∈ 𝔭 → Q' ≠ 0 → (↑Q'.vars : Set σ) ⊆ insert j (Set.range g) → degreeOf j Q ≤ degreeOf j Q'`.

Introduce `Q' h1 h2 h3`. Rewrite using `[hQd]`. Conclude with `Nat.find_min' hex ⟨Q', h1, h2, h3, rfl⟩`. Establish `hpos : 0 < degreeOf j Q`. Assume the negation of the conclusion as `h0`.

Use `push_neg at h0`. Apply `hQ0` to reduce the goal to its premises. Apply `hind Q _ hQp` to reduce the goal to its premises. Introduce `i hi`. Break down `hQv hi with rfl | hi'` into its components or cases.

It suffices to derive a contradiction. Rewrite `hi` using `[Finset.mem_coe, mem_vars]`. Take `⟨m, hm, him⟩` from `hi`. Use `monomial_le_degreeOf j hm` as an intermediate fact. Rewrite `him` using `[Finsupp.mem_support_iff]`.

Use linear arithmetic over natural numbers and integers. Conclude with `hi'`. Take `⟨hd0, hdlt, hdv⟩` from `gs_pderiv_facts Q j hpos`. Establish `hnot : π (pderiv j Q) ≠ 0`. Rewrite using `[Ne, hπ]`.

Introduce `hmem`. Use `hmin _ hmem hd0 (fun i hi => hQv (Finset.mem_coe.mpr (hdv (Finset.mem_coe.mp hi))))` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hDQ : D Q = π (pderiv j Q) * c k0`. Simplify using `only [D]`.

Rewrite using `[Finset.sum_eq_single k0]`. Introduce `k _ hk`. Establish `: pderiv (b k) Q = 0`. Apply `pderiv_eq_zero_of_notMem_vars` to reduce the goal to its premises. Introduce `hv`.

Break down `hQv (Finset.mem_coe.mpr hv) with h | h` into its components or cases. Conclude with `hk (hbinj h)`. Conclude with `hb k h`. Rewrite using `[this, map_zero, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ k0) h`. Use `hDp Q hQp` as an intermediate fact. Rewrite `this` using `[hDQ]`. Simplify using `using (mul_eq_zero.mp this).resolve_left hnot`. Take `⟨a, ha⟩` from `gs_exists_rows_det_ne_zero M hM`.

Use `⟨a, b, fun hmem => ha ?_⟩` and prove the remaining obligations. Establish `h1` using `(hπ _).2 hmem`. Rewrite `h1` using `[RingHom.map_det]`. Establish `hM' : M.submatrix a id = π.mapMatrix (Matrix.of fun i j => pderiv (b j) (G (a i)))`. Use extensionality with `i k`.

Both sides reduce to the same expression. Rewrite using `[hM']`. Conclude with `h1`.
-/
theorem exists_jacobian_minor_not_mem' {σ : Type} [Fintype σ]
    (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] {t : ℕ}
    (G : Fin t → MvPolynomial σ ℚ) (hG : Ideal.span (Set.range G) = 𝔭) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) = d) :
    ∃ (a : Fin (Fintype.card σ - d) → Fin t) (b : Fin (Fintype.card σ - d) → σ),
      Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∉ 𝔭 := by
  classical
  let A := MvPolynomial σ ℚ ⧸ 𝔭
  haveI : IsDomain A := Ideal.Quotient.isDomain 𝔭
  let K := FractionRing A
  let π : MvPolynomial σ ℚ →+* K := (algebraMap A K).comp (Ideal.Quotient.mk 𝔭)
  have hπ : ∀ f, π f = 0 ↔ f ∈ 𝔭 := by
    intro f
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff (R := A) (K := K), Ideal.Quotient.eq_zero_iff_mem]
  let xb : σ → A := fun s => Ideal.Quotient.mk 𝔭 (X s)
  have hmk : Ideal.Quotient.mkₐ ℚ 𝔭 = aeval xb := MvPolynomial.algHom_ext fun s => by
    rw [aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  have hmk' : ∀ f, Ideal.Quotient.mk 𝔭 f = aeval xb f := fun f => by
    rw [← hmk, Ideal.Quotient.mkₐ_eq_mk]

  haveI : Algebra.FiniteType ℚ A := inferInstance
  obtain ⟨s0, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℚ) (A := A)
  have hs0 : s0 = d := by
    have : (s0 : WithBot ℕ∞) = (d : WithBot ℕ∞) := hs1.symm.trans hd
    exact_mod_cast this
  subst hs0

  haveI : FaithfulSMul ℚ A :=
    (faithfulSMul_iff_algebraMap_injective ℚ A).mpr (algebraMap ℚ A).injective
  have hadj : Algebra.adjoin ℚ (Set.range xb) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, ← hmk]
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℚ 𝔭 x
    exact ⟨y, rfl⟩
  haveI : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range xb)) A := by
    constructor
    intro a
    have ha : a ∈ Algebra.adjoin ℚ (Set.range xb) := by rw [hadj]; trivial
    exact isAlgebraic_algebraMap (R := Algebra.adjoin ℚ (Set.range xb)) (A := A)
      (⟨a, ha⟩ : Algebra.adjoin ℚ (Set.range xb))
  obtain ⟨u, hu, hub⟩ := exists_isTranscendenceBasis_subset (R := ℚ) (Set.range xb)
  haveI : Finite u := ((Set.finite_range xb).subset hu).to_subtype
  haveI : Fintype u := Fintype.ofFinite u
  have hcardu : Fintype.card u = s0 := by
    have h1 := hub.cardinalMk_eq_trdeg
    rw [hs2, Cardinal.mk_fintype] at h1
    exact_mod_cast h1
  let g : u → σ := fun y => (hu y.2).choose
  have hg : ∀ y, xb (g y) = y := fun y => (hu y.2).choose_spec
  have hginj : Function.Injective g := by
    intro y y' h
    apply Subtype.ext
    rw [← hg y, ← hg y', h]

  have hind : ∀ Q : MvPolynomial σ ℚ, (↑Q.vars : Set σ) ⊆ Set.range g → Q ∈ 𝔭 → Q = 0 := by
    intro Q hQ hQp
    obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range Q g hginj hQ
    have h0 : aeval ((↑) : u → A) q = 0 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, hmk', aeval_rename] at hQp
      have hfun : ((↑) : u → A) = xb ∘ g := funext fun y => (hg y).symm
      rw [hfun]
      exact hQp
    rw [hub.1.eq_zero_of_aeval_eq_zero q h0, map_zero]

  have hrel : ∀ j, j ∉ Set.range g → ∃ Q : MvPolynomial σ ℚ,
      Q ∈ 𝔭 ∧ Q ≠ 0 ∧ (↑Q.vars : Set σ) ⊆ insert j (Set.range g) := by
    intro j hj
    let w : Option u → A := fun o => o.elim (xb j) ((↑) : u → A)
    have hw : ¬ AlgebraicIndependent ℚ w := by
      intro h
      rw [AlgebraicIndependent.option_iff] at h
      exact h.2 (hub.isAlgebraic.isAlgebraic (xb j))
    rw [algebraicIndependent_iff] at hw
    push_neg at hw
    obtain ⟨p, hp0, hp⟩ := hw
    let h : Option u → σ := fun o => o.elim j g
    have hinj : Function.Injective h := by
      rintro (_ | y) (_ | y') hyy
      · rfl
      · exact absurd ⟨y', hyy.symm⟩ hj
      · exact absurd ⟨y, hyy⟩ hj
      · exact congr_arg some (hginj hyy)
    refine ⟨rename h p, ?_, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, hmk', aeval_rename]
      have hfun : xb ∘ h = w := by
        funext o
        cases o with
        | none => rfl
        | some y => exact hg y
      rw [hfun]
      exact hp0
    · exact fun h0 => hp ((rename_injective h hinj) (h0.trans (map_zero _).symm))
    · intro i hi
      have := vars_rename h p (Finset.mem_coe.mp hi)
      obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp this
      cases o with
      | none => exact Set.mem_insert _ _
      | some y => exact Set.mem_insert_of_mem _ ⟨y, rfl⟩

  have hT : Fintype.card {j // j ∉ Set.range g} = Fintype.card σ - s0 := by
    rw [Fintype.card_subtype_compl, ← hcardu]
    congr 1
    rw [← Set.card_range_of_injective hginj]
  let e : {j // j ∉ Set.range g} ≃ Fin (Fintype.card σ - s0) := Fintype.equivFinOfCardEq hT
  let b : Fin (Fintype.card σ - s0) → σ := fun k => (e.symm k).1
  have hb : ∀ k, b k ∉ Set.range g := fun k => (e.symm k).2
  have hbinj : Function.Injective b := fun k k' h => e.symm.injective (Subtype.ext h)
  let M : Matrix (Fin t) (Fin (Fintype.card σ - s0)) K := Matrix.of fun i k => π (pderiv (b k) (G i))
  have hM : ∀ c, M.mulVec c = 0 → c = 0 := by
    intro c hc
    let D : MvPolynomial σ ℚ → K := fun f => ∑ k, π (pderiv (b k) f) * c k
    have hDG : ∀ i, D (G i) = 0 := fun i => by
      have := congr_fun hc i
      simpa [Matrix.mulVec, dotProduct, M, D] using this
    have hDp : ∀ f ∈ 𝔭, D f = 0 := by
      intro f hf
      rw [← hG] at hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hDG i
      | zero => simp [D]
      | add x y _ _ hx hy =>
        have : D (x + y) = D x + D y := by
          simp only [D, map_add, add_mul, Finset.sum_add_distrib]
        rw [this, hx, hy, add_zero]
      | smul a x hx' hx =>
        have hx0 : π x = 0 := (hπ x).2 (hG ▸ hx')
        have : D (a • x) = π a * D x := by
          simp only [D, smul_eq_mul, Derivation.leibniz, map_add, map_mul, hx0, zero_mul,
            add_zero, Finset.mul_sum, mul_assoc]
        rw [this, hx, mul_zero]
    funext k0
    let j := b k0
    have hj : j ∉ Set.range g := hb k0
    have hex : ∃ n, ∃ Q : MvPolynomial σ ℚ, Q ∈ 𝔭 ∧ Q ≠ 0 ∧
        (↑Q.vars : Set σ) ⊆ insert j (Set.range g) ∧ degreeOf j Q = n := by
      obtain ⟨Q, h1, h2, h3⟩ := hrel j hj
      exact ⟨_, Q, h1, h2, h3, rfl⟩
    obtain ⟨Q, hQp, hQ0, hQv, hQd⟩ := Nat.find_spec hex
    have hmin : ∀ Q' : MvPolynomial σ ℚ, Q' ∈ 𝔭 → Q' ≠ 0 →
        (↑Q'.vars : Set σ) ⊆ insert j (Set.range g) → degreeOf j Q ≤ degreeOf j Q' := by
      intro Q' h1 h2 h3
      rw [hQd]
      exact Nat.find_min' hex ⟨Q', h1, h2, h3, rfl⟩
    have hpos : 0 < degreeOf j Q := by
      by_contra h0
      push_neg at h0
      apply hQ0
      apply hind Q _ hQp
      intro i hi
      rcases hQv hi with rfl | hi'
      · exfalso
        rw [Finset.mem_coe, mem_vars] at hi
        obtain ⟨m, hm, him⟩ := hi
        have := monomial_le_degreeOf j hm
        rw [Finsupp.mem_support_iff] at him
        omega
      · exact hi'
    obtain ⟨hd0, hdlt, hdv⟩ := gs_pderiv_facts Q j hpos
    have hnot : π (pderiv j Q) ≠ 0 := by
      rw [Ne, hπ]
      intro hmem
      have := hmin _ hmem hd0 (fun i hi => hQv (Finset.mem_coe.mpr (hdv (Finset.mem_coe.mp hi))))
      omega
    have hDQ : D Q = π (pderiv j Q) * c k0 := by
      simp only [D]
      rw [Finset.sum_eq_single k0]
      · intro k _ hk
        have : pderiv (b k) Q = 0 := by
          apply pderiv_eq_zero_of_notMem_vars
          intro hv
          rcases hQv (Finset.mem_coe.mpr hv) with h | h
          · exact hk (hbinj h)
          · exact hb k h
        rw [this, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ k0) h
    have := hDp Q hQp
    rw [hDQ] at this
    simpa using (mul_eq_zero.mp this).resolve_left hnot
  obtain ⟨a, ha⟩ := gs_exists_rows_det_ne_zero M hM
  refine ⟨a, b, fun hmem => ha ?_⟩
  have h1 := (hπ _).2 hmem
  rw [RingHom.map_det] at h1
  have hM' : M.submatrix a id = π.mapMatrix (Matrix.of fun i j => pderiv (b j) (G (a i))) := by
    ext i k
    rfl
  rw [hM']
  exact h1

/- English proof (translation)
The claim follows from `exists_jacobian_minor_not_mem' 𝔭 G hG d hd`.
-/
theorem exists_jacobian_minor_not_mem {σ : Type} [Fintype σ]
    (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] {t : ℕ}
    (G : Fin t → MvPolynomial σ ℚ) (hG : Ideal.span (Set.range G) = 𝔭) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) = d) :
    ∃ (a : Fin (Fintype.card σ - d) → Fin t) (b : Fin (Fintype.card σ - d) → σ),
      Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∉ 𝔭 :=
  exists_jacobian_minor_not_mem' 𝔭 G hG d hd

end ReciprocityTheory.AnForm.R
