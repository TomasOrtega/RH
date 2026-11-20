import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherTail
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogFirstCoordinate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

section Pull

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

/- English proof (translation)
Take `⟨i', hi'⟩` from `hz (κ k)`. Take `⟨p, hp⟩` from `hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩`. Establish `h2 : p.1 = k` using `hv.1 (by rw [← hv.2.2.1 p, hp])`. Take `⟨pk, pi⟩` from `p`. Simplify using `only at h2`.

Substitute `h2` using the available equality. Conclude with `⟨pi, by rw [hp]; exact hi'⟩`.
-/
theorem blocks_ne_zero_restrict {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {z : (Σ k', ι' k') → ℂ} (hz : ∀ k', ∃ i', z ⟨k', i'⟩ ≠ 0) (k : K) : ∃ i, z (v ⟨k, i⟩) ≠ 0 := by
  obtain ⟨i', hi'⟩ := hz (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

/- English proof (translation)
Establish `e : A'.h = A.h ∘ fun (z : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z (v p)` using `funext h.2`. Establish `hR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun (z : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z (v p))` using `contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (v p)`. Unfold `IsSmoothHerm`. Rewrite using `[e]`. Conclude with `hA.comp hR.contDiffOn fun z hz => blocks_ne_zero_restrict hv hz`.
-/
theorem IsPullHerm.isSmoothHerm {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (h : IsPullHerm κ v A A') (hA : IsSmoothHerm A) :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun (z : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z (v p) := funext h.2
  have hR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun (z : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z (v p)) :=
    contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (v p)
  unfold IsSmoothHerm
  rw [e]
  exact hA.comp hR.contDiffOn fun z hz => blocks_ne_zero_restrict hv hz

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ A hv` and use `⟨IndefiniteRowSideFullHecke.Inter.pullHerm hv A, IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hv A, IsPullHerm.isSmoothHerm hv (IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hv A)⟩`.
-/
theorem pullExists : PullExistsStatement := fun _ _ _ _ _ _ _ _ _ _ A hv =>
  ⟨IndefiniteRowSideFullHecke.Inter.pullHerm hv A, IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hv A,
    IsPullHerm.isSmoothHerm hv (IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hv A)⟩

omit [Fintype K] [Fintype K'] in
/- English proof (translation)
Use function extensionality and compare the values at `k'`. Simplify using `only [pullDeg, Function.extend, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem pullDeg_add (κ : K → K') (a b : K → ℤ) : pullDeg κ (a + b) = pullDeg κ a + pullDeg κ b := by
  classical
  funext k'
  simp only [pullDeg, Function.extend, Pi.add_apply]
  split_ifs <;> simp

omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in

/- English proof (translation)
Use `⟨?_, fun z => ?_⟩` and prove the remaining obligations. Use `show A'.a + B'.a = pullDeg κ (A.a + B.a)`. Rewrite using `[hA.1, hB.1, pullDeg_add]`. Use `show A'.h z * B'.h z = A.h _ * B.h _`. Rewrite using `[hA.2, hB.2]`.
-/
theorem IsPullHerm.tensor {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {A B : HermLine ι}
    {A' B' : HermLine ι'} (hA : IsPullHerm κ v A A') (hB : IsPullHerm κ v B B') :
    IsPullHerm κ v (A.tensor B) (A'.tensor B') := by
  refine ⟨?_, fun z => ?_⟩
  · show A'.a + B'.a = pullDeg κ (A.a + B.a)
    rw [hA.1, hB.1, pullDeg_add]
  · show A'.h z * B'.h z = A.h _ * B.h _
    rw [hA.2, hB.2]

end Pull

section Algebra

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

omit [Fintype K] in

/- English proof (translation)
Establish `hm : (∏ j, X (q j) ^ e j : MRing ι) = monomial (∑ j, Finsupp.single (q j) (e j)) 1`. Rewrite using `[monomial_sum_one]`. Simplify using `[X_pow_eq_monomial]`. Introduce `m hm' k`. Rewrite `hm'` using `[hm]`.

Use `Finset.mem_singleton.1 (support_monomial_subset hm')` as an intermediate fact. Substitute `this` using the available equality. Use `beta_reduce`. Rewrite using `[Finset.sum_filter]`. Simplify using `only [Finsupp.coe_finsetSum, Finset.sum_apply]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Take `⟨k0, i0⟩` from `q j`. Distinguish the cases in `h : k0 = k`. Substitute `h` using the available equality.

Simplify using `[Finsupp.single_apply]`. Simplify using `[h]`.
-/
theorem isMultiHomog_prod_X_pow [DecidableEq K] {J : Type*} [Fintype J] (q : J → Σ k, ι k) (e : J → ℕ) :
    IsMultiHomog (∏ j, X (q j) ^ e j : MRing ι)
      (fun k => ∑ j ∈ Finset.univ.filter (fun j => (q j).1 = k), e j) := by
  classical
  have hm : (∏ j, X (q j) ^ e j : MRing ι) = monomial (∑ j, Finsupp.single (q j) (e j)) 1 := by
    rw [monomial_sum_one]
    simp [X_pow_eq_monomial]
  intro m hm' k
  rw [hm] at hm'
  have := Finset.mem_singleton.1 (support_monomial_subset hm')
  subst this
  beta_reduce
  rw [Finset.sum_filter]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨k0, i0⟩ := q j
  by_cases h : k0 = k
  · subst h
    simp [Finsupp.single_apply]
  · simp [h]

/- English proof (translation)
Establish `hr : Ideal.Quotient.mk Q x ∈ nonZeroDivisors (R ⧸ Q)` using `mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Use `le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)` and prove the remaining obligations. Use `gcongr`. Use `ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_) (Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hle))` and prove the remaining obligations. Introduce `y hy`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Rewrite using `[map_mul]`. Take `⟨c', rfl⟩` from `Ideal.Quotient.mk_surjective c`. Simplify using `only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, mul_zero]`.
-/
theorem krullDim_quot_add_one_le {R : Type*} [CommRing R] {Q Q₂ : Ideal R} [Q.IsPrime] (hle : Q ≤ Q₂)
    {x : R} (hx : x ∈ Q₂) (hxQ : x ∉ Q) : ringKrullDim (R ⧸ Q₂) + 1 ≤ ringKrullDim (R ⧸ Q) := by
  have hr : Ideal.Quotient.mk Q x ∈ nonZeroDivisors (R ⧸ Q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_)
    (Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hle))
  intro y hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul]
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, mul_zero]

end Algebra

section Proof

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro _ d _ _ _ _ h`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`.

Introduce `P' d L L' hP' hQ hdn hL hLL`. Establish `hL' : ∀ j, IsSmoothHerm (L' j)` using `fun j => IsPullHerm.isSmoothHerm hv (hLL j) (hL j)`. Establish `hL0 : ∀ j, IsSmoothHerm (Fin.init L j)` using `fun j => hL _`. Establish `hL0' : ∀ j, IsSmoothHerm (Fin.init L' j)` using `fun j => hL' _`. Establish `hLL0 : ∀ j, IsPullHerm κ v (Fin.init L j) (Fin.init L' j)` using `fun j => hLL _`.

Establish `hQp : (imageZ v P').IsPrime` using `hQ.2.1.1`. Establish `key : ∀ (B : HermLine ι) (B' : HermLine ι'), IsSmoothHerm B' → IsPullHerm κ v B B' → (∀ k, 0 ≤ B.a k) → I K' ι' P' (n + 1) (Fin.snoc (Fin.init L') B') = 0`. Introduce `B B' hB' hBB hBa`. Use `choose i hi using hQ.2.1.2.2`. Set `b : K → ℕ` to `fun k => (B.a k).toNat`.

Set `t : MRing ι` to `∏ k, X ⟨k, i k⟩ ^ b k`. Establish `ht : t ∉ imageZ v P'`. Introduce `h`. Take `⟨k, -, hk⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := hQp)).1 h`. Conclude with `hi k (hQp.mem_of_pow_mem _ hk)`.

Establish `htm : IsMultiHomog t b`. Use `isMultiHomog_prod_X_pow (fun k => (⟨k, i k⟩ : Σ k, ι k)) b using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_filter]`. Set `s : MRing ι'` to `rename v t`.

Establish `hs : s ∉ P'` using `ht`. Set `b' : K' → ℕ` to `fun k' => ∑ k ∈ Finset.univ.filter (fun k => κ k = k'), b k`. Establish `hsm : IsMultiHomog s b'`. Establish `e : s = ∏ k, X (v ⟨k, i k⟩) ^ b k` using `by simp [s, t, map_prod]`. Rewrite using `[e]`.

Use `isMultiHomog_prod_X_pow (fun k => v ⟨k, i k⟩) b using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k'`. Simplify using `only [hv.2.2.1, b']`. Establish `hBa' : ∀ k', B'.a k' = b' k'`. Introduce `k'`.

Rewrite using `[hBB.1]`. Distinguish the cases in `hk : ∃ k, κ k = k'`. Take `⟨k0, rfl⟩` from `hk`. Establish `hf : Finset.univ.filter (fun k => κ k = κ k0) = {k0}`. Use extensionality with `k`.

Simplify using `[hv.1.eq_iff]`. Simplify using `only [b', hf, Finset.sum_singleton, pullDeg, hv.1.extend_apply, b]`. Conclude with `(Int.toNat_of_nonneg (hBa k0)).symm`. Establish `hf : Finset.univ.filter (fun k => κ k = k') = ∅`. Use extensionality with `k`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]`. Conclude with `fun h => hk ⟨k, h⟩`. Simplify using `only [b', hf, Finset.sum_empty, pullDeg, Function.extend_apply' _ _ _ hk]`. Both sides reduce to the same expression. Establish `hsec : IsSectionOn P' B' s` using `⟨b', hBa', hsm, hs⟩`.

Rewrite using `[(hI K' ι').2.2 P' n (Fin.init L') B' s b' hP' hL0' hB' hBa' hsm hs, recR_eq]`. Establish `h1 : arInt P' s B' (Fin.init L') = 0` using `hF K ι K' ι' κ v P' d n (Fin.init L) (Fin.init L') (logNorm B' s) hv hP' hQ hdn hL0 hLL0`. Establish `h2 : cycR (I K' ι') P' (Fin.init L') s = vertR P' (Fin.init L') s`. Unfold `cycR vertR`. Use `finsum_mem_congr rfl fun W hW => ?_` and prove the remaining obligations.

Use `split_ifs with hH`. Establish `hWn : IsArithVar W n` using `(divSuppArith K' ι' P' n B' s W hP' hsec hW).1 hH`. Take `⟨dW, -, hQW⟩` from `hIm K ι K' ι' κ v W n hQ.1 hv hWn`. Establish `hPW : P' ≤ W` using `le_sup_left.trans hW.1.1.2`. Establish `hsW : s ∈ W` using `hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))`.

Establish `hdim` using `krullDim_quot_add_one_le (Q := imageZ v P') (Q₂ := imageZ v W) (Ideal.comap_mono hPW) (show t ∈ imageZ v W from hsW) ht`. Rewrite `hdim` using `[hQW.2.2.2, hQ.2.2.2]`. Establish `hlt : dW + Fintype.card K + 1 ≤ d + Fintype.card K` using `by exact_mod_cast hdim`. Rewrite using `[ih W dW (Fin.init L) (Fin.init L') hWn hQW (by omega) hL0 hLL0]`. Both sides reduce to the same expression.

Rewrite using `[h1, h2, hV K ι K' ι' κ v P' d n (Fin.init L) (Fin.init L') t b hv hP' hQ hdn hLL0 htm ht, sub_zero]`. Set `A` to `L (Fin.last n)`. Set `A'` to `L' (Fin.last n)`. Set `M : HermLine ι` to `HermLine.sqMetric fun k => (-(A.a k)).toNat`. Set `M'` to `IndefiniteRowSideFullHecke.Inter.pullHerm hv M`.

Establish `hM : IsSmoothHerm M` using `isSmoothHerm_sqMetric _`. Establish `hMM : IsPullHerm κ v M M'` using `IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hv M`. Establish `hM' : IsSmoothHerm M'` using `IsPullHerm.isSmoothHerm hv hMM hM`. Establish `hA' : IsSmoothHerm A'` using `hL' _`. Establish `hadd` using `(hI K' ι').2.1 P' n (Fin.init L') A' M' hP' hL0' hA' hM'`.

Establish `h3` using `key (A.tensor M) (A'.tensor M') (isSmoothHerm_tensor hA' hM') (IsPullHerm.tensor (hLL _) hMM) fun k => by show 0 ≤ A.a k + ((-(A.a k)).toNat : ℤ)`. Use linear arithmetic over natural numbers and integers. Establish `h4` using `key M M' hM' hMM fun k => by show (0 : ℤ) ≤ ((-(A.a k)).toNat : ℤ)`. Use linear arithmetic over natural numbers and integers. Establish `e : L' = Fin.snoc (Fin.init L') A'` using `(Fin.snoc_init_self L').symm`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem contract_intersection_number (hIm : ImageArithStatement) (hF : pointForm_holds.Statement) (hV : ProjectivePointVertical.Statement)
    (I : AllFam) (hI : I.IsFamily) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n : ℕ) (P' : Ideal (MRing ι')) (d : ℕ) (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι'),
      IsArithVar P' n → IsArithVar (imageZ v P') d → d < n → (∀ j, IsSmoothHerm (L j)) →
      (∀ j, IsPullHerm κ v (L j) (L' j)) → I K' ι' P' n L' = 0 := by
  intro n
  induction n with
  | zero => intro _ d _ _ _ _ h; omega
  | succ n ih =>
    intro P' d L L' hP' hQ hdn hL hLL
    classical
    have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => IsPullHerm.isSmoothHerm hv (hLL j) (hL j)
    have hL0 : ∀ j, IsSmoothHerm (Fin.init L j) := fun j => hL _
    have hL0' : ∀ j, IsSmoothHerm (Fin.init L' j) := fun j => hL' _
    have hLL0 : ∀ j, IsPullHerm κ v (Fin.init L j) (Fin.init L' j) := fun j => hLL _
    have hQp : (imageZ v P').IsPrime := hQ.2.1.1

    have key : ∀ (B : HermLine ι) (B' : HermLine ι'), IsSmoothHerm B' → IsPullHerm κ v B B' →
        (∀ k, 0 ≤ B.a k) → I K' ι' P' (n + 1) (Fin.snoc (Fin.init L') B') = 0 := by
      intro B B' hB' hBB hBa
      choose i hi using hQ.2.1.2.2
      let b : K → ℕ := fun k => (B.a k).toNat
      let t : MRing ι := ∏ k, X ⟨k, i k⟩ ^ b k
      have ht : t ∉ imageZ v P' := by
        intro h
        obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hQp)).1 h
        exact hi k (hQp.mem_of_pow_mem _ hk)
      have htm : IsMultiHomog t b := by
        convert isMultiHomog_prod_X_pow (fun k => (⟨k, i k⟩ : Σ k, ι k)) b using 1
        funext k
        simp [Finset.sum_filter]
      let s : MRing ι' := rename v t
      have hs : s ∉ P' := ht
      let b' : K' → ℕ := fun k' => ∑ k ∈ Finset.univ.filter (fun k => κ k = k'), b k
      have hsm : IsMultiHomog s b' := by
        have e : s = ∏ k, X (v ⟨k, i k⟩) ^ b k := by simp [s, t, map_prod]
        rw [e]
        convert isMultiHomog_prod_X_pow (fun k => v ⟨k, i k⟩) b using 1
        funext k'
        simp only [hv.2.2.1, b']
      have hBa' : ∀ k', B'.a k' = b' k' := by
        intro k'
        rw [hBB.1]
        by_cases hk : ∃ k, κ k = k'
        · obtain ⟨k0, rfl⟩ := hk
          have hf : Finset.univ.filter (fun k => κ k = κ k0) = {k0} := by
            ext k
            simp [hv.1.eq_iff]
          simp only [b', hf, Finset.sum_singleton, pullDeg, hv.1.extend_apply, b]
          exact (Int.toNat_of_nonneg (hBa k0)).symm
        · have hf : Finset.univ.filter (fun k => κ k = k') = ∅ := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            exact fun h => hk ⟨k, h⟩
          simp only [b', hf, Finset.sum_empty, pullDeg, Function.extend_apply' _ _ _ hk]
          rfl
      have hsec : IsSectionOn P' B' s := ⟨b', hBa', hsm, hs⟩
      rw [(hI K' ι').2.2 P' n (Fin.init L') B' s b' hP' hL0' hB' hBa' hsm hs, recR_eq]
      have h1 : arInt P' s B' (Fin.init L') = 0 :=
        hF K ι K' ι' κ v P' d n (Fin.init L) (Fin.init L') (logNorm B' s) hv hP' hQ hdn hL0 hLL0
      have h2 : cycR (I K' ι') P' (Fin.init L') s = vertR P' (Fin.init L') s := by
        unfold cycR vertR
        refine finsum_mem_congr rfl fun W hW => ?_
        split_ifs with hH
        · have hWn : IsArithVar W n := (divSuppArith K' ι' P' n B' s W hP' hsec hW).1 hH
          obtain ⟨dW, -, hQW⟩ := hIm K ι K' ι' κ v W n hQ.1 hv hWn
          have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
          have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
          have hdim := krullDim_quot_add_one_le (Q := imageZ v P') (Q₂ := imageZ v W) (Ideal.comap_mono hPW)
            (show t ∈ imageZ v W from hsW) ht
          rw [hQW.2.2.2, hQ.2.2.2] at hdim
          have hlt : dW + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast hdim
          rw [ih W dW (Fin.init L) (Fin.init L') hWn hQW (by omega) hL0 hLL0]
        · rfl
      rw [h1, h2, hV K ι K' ι' κ v P' d n (Fin.init L) (Fin.init L') t b hv hP' hQ hdn hLL0 htm ht,
        sub_zero]

    let A := L (Fin.last n)
    let A' := L' (Fin.last n)
    let M : HermLine ι := HermLine.sqMetric fun k => (-(A.a k)).toNat
    let M' := IndefiniteRowSideFullHecke.Inter.pullHerm hv M
    have hM : IsSmoothHerm M := isSmoothHerm_sqMetric _
    have hMM : IsPullHerm κ v M M' := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hv M
    have hM' : IsSmoothHerm M' := IsPullHerm.isSmoothHerm hv hMM hM
    have hA' : IsSmoothHerm A' := hL' _
    have hadd := (hI K' ι').2.1 P' n (Fin.init L') A' M' hP' hL0' hA' hM'
    have h3 := key (A.tensor M) (A'.tensor M') (isSmoothHerm_tensor hA' hM')
      (IsPullHerm.tensor (hLL _) hMM) fun k => by
        show 0 ≤ A.a k + ((-(A.a k)).toNat : ℤ)
        omega
    have h4 := key M M' hM' hMM fun k => by
      show (0 : ℤ) ≤ ((-(A.a k)).toNat : ℤ)
      omega
    have e : L' = Fin.snoc (Fin.init L') A' := (Fin.snoc_init_self L').symm
    rw [e]
    linarith

/- English proof (translation)
Introduce `I hI K _ ι _ K' _ ι' _ κ v P' d d' L L' hv hP' hQ hdd hL hLL`. Conclude with `contract_intersection_number hIm hF hV I hI hv d' P' d L L' hP' hQ hdd hL hLL`.
-/
theorem PushforwardProjectivePoint.proof (hIm : ImageArithStatement) (hF : pointForm_holds.Statement) (hV : ProjectivePointVertical.Statement) :
    PushforwardProjectivePoint.Statement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d d' L L' hv hP' hQ hdd hL hLL
  exact contract_intersection_number hIm hF hV I hI hv d' P' d L L' hP' hQ hdd hL hLL

/- English proof (translation)
The claim follows from `PushforwardProjectivePoint.proof hIm hF hV`.
-/
theorem contract_of (hIm : ImageArithStatement) (hF : pointForm_holds.Statement) (hV : ProjectivePointVertical.Statement) :
    ContractStatement :=
  PushforwardProjectivePoint.proof hIm hF hV

end Proof

end GroundTheory.Heights₂.Heights.Inter
