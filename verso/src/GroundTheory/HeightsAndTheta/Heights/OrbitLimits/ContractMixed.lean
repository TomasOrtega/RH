import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFIntZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFVert
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter

namespace ContractMixed

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def PrefixPull (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (p : ℕ) {n : ℕ} (L' : Fin n → HermLine ι') :
    Prop :=
  ∃ (h : p ≤ n) (L : Fin p → HermLine ι), (∀ j, IsSmoothHerm (L j)) ∧
    ∀ j, IsPullHerm κ v (L j) (L' (Fin.castLE h j))

omit [∀ k, Fintype (ι' k)] in

/- English proof (translation)
Take `⟨hpn, L, hL, hLL⟩` from `h`. Conclude with `⟨hqp.trans hpn, fun j => L (Fin.castLE hqp j), fun j => hL _, fun j => hLL (Fin.castLE hqp j)⟩`.
-/
theorem PrefixPull.mono {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {p q n : ℕ} {L' : Fin n → HermLine ι'}
    (h : PrefixPull κ v p L') (hqp : q ≤ p) : PrefixPull κ v q L' := by
  obtain ⟨hpn, L, hL, hLL⟩ := h
  exact ⟨hqp.trans hpn, fun j => L (Fin.castLE hqp j), fun j => hL _, fun j => hLL (Fin.castLE hqp j)⟩

omit [∀ k, Fintype (ι' k)] in

/- English proof (translation)
Take `⟨_, L, hL, hLL⟩` from `h`. Conclude with `⟨hpn, L, hL, fun j => hLL j⟩`.
-/
theorem PrefixPull.init {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {p n : ℕ} {L' : Fin (n + 1) → HermLine ι'}
    (h : PrefixPull κ v p L') (hpn : p ≤ n) : PrefixPull κ v p (Fin.init L') := by
  obtain ⟨_, L, hL, hLL⟩ := h
  exact ⟨hpn, L, hL, fun j => hLL j⟩

/- English proof (translation)
Take `⟨h, L, hL, hLL⟩` from `hpre`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le h`. Rewrite using `[← Fin.append_castAdd_natAdd (f := L')]`. Conclude with `hInt K ι K' ι' κ v P' d₀ m L _ _ A s hv hP' hQ hL hLL`.
-/
theorem arInt_eq_zero (hInt : PFIntZero.Statement) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d₀ n : ℕ} (hP' : IsArithVar P' (n + 1))
    (hQ : IsArithVar (imageZ v P') d₀) {L' : Fin n → HermLine ι'} (hpre : PrefixPull κ v d₀ L')
    (A : HermLine ι') (s : MRing ι') : arInt P' s A L' = 0 := by
  obtain ⟨h, L, hL, hLL⟩ := hpre
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fin.append_castAdd_natAdd (f := L')]
  exact hInt K ι K' ι' κ v P' d₀ m L _ _ A s hv hP' hQ hL hLL

/- English proof (translation)
Take `⟨h, L, -, hLL⟩` from `hpre`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le h`. Rewrite using `[← Fin.append_castAdd_natAdd (f := L')]`. Conclude with `hVert K ι K' ι' κ v P' d₀ m L _ _ s a W hv hP' hQ hLL hs hsP hW hh`.
-/
theorem geoNum_eq_zero (hVert : PFVert.Statement) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d₀ n : ℕ} (hP' : IsArithVar P' (n + 1))
    (hQ : IsArithVar (imageZ v P') d₀) {L' : Fin n → HermLine ι'} (hpre : PrefixPull κ v d₀ L')
    {s : MRing ι'} {a : K' → ℕ} (hs : IsMultiHomog s a) (hsP : s ∉ P') {W : Ideal (MRing ι')}
    (hW : W ∈ divSupp P' s) (hh : ¬ IsHorizontal W) : geoNum n W (fun j => (L' j).a) = 0 := by
  obtain ⟨h, L, -, hLL⟩ := hpre
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fin.append_castAdd_natAdd (f := L')]
  exact hVert K ι K' ι' κ v P' d₀ m L _ _ s a W hv hP' hQ hLL hs hsP hW hh

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p _ d₀ _ _ _ hdp hpre _`. Take `⟨h, -⟩` from `hpre`.

Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`. Introduce `p P' d₀ L' hP' hQ hdp hpre hL'`. Break down `Nat.lt_or_ge n p with hnp | hpn` into its components or cases. Take `⟨h, L, hL, hLL⟩` from `hpre`.

Establish `hp : p = n + 1` using `by omega`. Substitute `hp` using the available equality. Establish `e : (fun j => L' (Fin.castLE h j)) = L'` using `funext fun j => congrArg L' (Fin.ext rfl)`. Establish `key` using `hC I hI K ι K' ι' κ v P' d₀ (n + 1) L (fun j => L' (Fin.castLE h j)) hv hP' hQ hdp hL hLL`. Rewrite `key` using `[e]`. Then use the resulting hypothesis.

Establish `hpre0 : PrefixPull κ v p (Fin.init L')` using `hpre.init hpn`. Establish `hL0 : ∀ j, IsSmoothHerm (Fin.init L' j)` using `fun j => hL' _`. Establish `hPp : P'.IsPrime` using `hP'.2.1.1`. Use `choose i hi using hP'.2.1.2.2`. Establish `key : ∀ B' : HermLine ι', IsSmoothHerm B' → (∀ k, 0 ≤ B'.a k) → I K' ι' P' (n + 1) (Fin.snoc (Fin.init L') B') = 0`.

Introduce `B' hB' hBa`. Set `b : K' → ℕ` to `fun k => (B'.a k).toNat`. Set `s : MRing ι'` to `∏ k, X ⟨k, i k⟩ ^ b k`. Establish `hs : s ∉ P'`. Introduce `h`.

Take `⟨k, -, hk⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := hPp)).1 h`. Conclude with `hi k (hPp.mem_of_pow_mem _ hk)`. Establish `hsm : IsMultiHomog s b`. Use `isMultiHomog_prod_X_pow (fun k => (⟨k, i k⟩ : Σ k, ι' k)) b using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Simplify using `[Finset.sum_filter]`. Establish `hBa' : ∀ k, B'.a k = b k` using `fun k => (Int.toNat_of_nonneg (hBa k)).symm`. Establish `hsec : IsSectionOn P' B' s` using `⟨b, hBa', hsm, hs⟩`. Rewrite using `[(hI K' ι').2.2 P' n (Fin.init L') B' s b hP' hL0 hB' hBa' hsm hs, recR_eq]`. Establish `h1 : arInt P' s B' (Fin.init L') = 0` using `arInt_eq_zero hInt hv hP' hQ (hpre0.mono hdp.le) B' s`.

Establish `h2 : cycR (I K' ι') P' (Fin.init L') s = 0`. Unfold `cycR`. Use `(finsum_mem_congr rfl fun W hW => ?_).trans (finsum_mem_zero _)` and prove the remaining obligations. Use `split_ifs with hH`. Establish `hWn : IsArithVar W n` using `(divSuppArith K' ι' P' n B' s W hP' hsec hW).1 hH`.

Take `⟨dW, -, hQW⟩` from `hIm K ι K' ι' κ v W n hQ.1 hv hWn`. Establish `hPW : P' ≤ W` using `le_sup_left.trans hW.1.1.2`. Establish `hle : imageZ v P' ≤ imageZ v W` using `Ideal.comap_mono hPW`. Establish `hdim` using `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)`. Rewrite `hdim` using `[hQW.2.2.2, hQ.2.2.2]`.

Establish `hlt : dW + Fintype.card K ≤ d₀ + Fintype.card K` using `by exact_mod_cast hdim`. Rewrite using `[ih p W dW (Fin.init L') hWn hQW (by omega) hpre0 hL0, mul_zero]`. Rewrite using `[geoNum_eq_zero hVert hv hP' hQ (hpre0.mono hdp.le) hsm hs hW hH]`. Simplify using the standard rewrite rules. Rewrite using `[h1, h2, sub_zero]`.

Set `A'` to `L' (Fin.last n)`. Set `M : HermLine ι'` to `HermLine.sqMetric fun k => (-(A'.a k)).toNat`. Establish `hM : IsSmoothHerm M` using `isSmoothHerm_sqMetric _`. Establish `hA' : IsSmoothHerm A'` using `hL' _`. Establish `hadd` using `(hI K' ι').2.1 P' n (Fin.init L') A' M hP' hL0 hA' hM`.

Establish `h3` using `key (A'.tensor M) (isSmoothHerm_tensor hA' hM) fun k => by show 0 ≤ A'.a k + ((-(A'.a k)).toNat : ℤ)`. Use linear arithmetic over natural numbers and integers. Establish `h4` using `key M hM fun k => by show (0 : ℤ) ≤ ((-(A'.a k)).toNat : ℤ)`. Use linear arithmetic over natural numbers and integers. Establish `e : L' = Fin.snoc (Fin.init L') A'` using `(Fin.snoc_init_self L').symm`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem aux (hC : ContractStatement) (hIm : ImageArithStatement) (hInt : PFIntZero.Statement)
    (hVert : PFVert.Statement) (I : AllFam) (hI : I.IsFamily) {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n p : ℕ) (P' : Ideal (MRing ι')) (d₀ : ℕ) (L' : Fin n → HermLine ι'),
      IsArithVar P' n → IsArithVar (imageZ v P') d₀ → d₀ < p → PrefixPull κ v p L' →
      (∀ j, IsSmoothHerm (L' j)) → I K' ι' P' n L' = 0 := by
  intro n
  induction n with
  | zero =>
    intro p _ d₀ _ _ _ hdp hpre _
    obtain ⟨h, -⟩ := hpre
    omega
  | succ n ih =>
    intro p P' d₀ L' hP' hQ hdp hpre hL'
    classical
    rcases Nat.lt_or_ge n p with hnp | hpn
    ·
      obtain ⟨h, L, hL, hLL⟩ := hpre
      have hp : p = n + 1 := by omega
      subst hp
      have e : (fun j => L' (Fin.castLE h j)) = L' := funext fun j => congrArg L' (Fin.ext rfl)
      have key := hC I hI K ι K' ι' κ v P' d₀ (n + 1) L (fun j => L' (Fin.castLE h j)) hv hP' hQ hdp hL hLL
      rwa [e] at key
    ·
      have hpre0 : PrefixPull κ v p (Fin.init L') := hpre.init hpn
      have hL0 : ∀ j, IsSmoothHerm (Fin.init L' j) := fun j => hL' _
      have hPp : P'.IsPrime := hP'.2.1.1
      choose i hi using hP'.2.1.2.2

      have key : ∀ B' : HermLine ι', IsSmoothHerm B' → (∀ k, 0 ≤ B'.a k) →
          I K' ι' P' (n + 1) (Fin.snoc (Fin.init L') B') = 0 := by
        intro B' hB' hBa
        let b : K' → ℕ := fun k => (B'.a k).toNat
        let s : MRing ι' := ∏ k, X ⟨k, i k⟩ ^ b k
        have hs : s ∉ P' := by
          intro h
          obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).1 h
          exact hi k (hPp.mem_of_pow_mem _ hk)
        have hsm : IsMultiHomog s b := by
          convert isMultiHomog_prod_X_pow (fun k => (⟨k, i k⟩ : Σ k, ι' k)) b using 1
          funext k
          simp [Finset.sum_filter]
        have hBa' : ∀ k, B'.a k = b k := fun k => (Int.toNat_of_nonneg (hBa k)).symm
        have hsec : IsSectionOn P' B' s := ⟨b, hBa', hsm, hs⟩
        rw [(hI K' ι').2.2 P' n (Fin.init L') B' s b hP' hL0 hB' hBa' hsm hs, recR_eq]
        have h1 : arInt P' s B' (Fin.init L') = 0 :=
          arInt_eq_zero hInt hv hP' hQ (hpre0.mono hdp.le) B' s
        have h2 : cycR (I K' ι') P' (Fin.init L') s = 0 := by
          unfold cycR
          refine (finsum_mem_congr rfl fun W hW => ?_).trans (finsum_mem_zero _)
          split_ifs with hH
          · have hWn : IsArithVar W n := (divSuppArith K' ι' P' n B' s W hP' hsec hW).1 hH
            obtain ⟨dW, -, hQW⟩ := hIm K ι K' ι' κ v W n hQ.1 hv hWn
            have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
            have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono hPW
            have hdim := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
              (Ideal.Quotient.factor_surjective hle)
            rw [hQW.2.2.2, hQ.2.2.2] at hdim
            have hlt : dW + Fintype.card K ≤ d₀ + Fintype.card K := by exact_mod_cast hdim
            rw [ih p W dW (Fin.init L') hWn hQW (by omega) hpre0 hL0, mul_zero]
          · rw [geoNum_eq_zero hVert hv hP' hQ (hpre0.mono hdp.le) hsm hs hW hH]
            simp
        rw [h1, h2, sub_zero]

      let A' := L' (Fin.last n)
      let M : HermLine ι' := HermLine.sqMetric fun k => (-(A'.a k)).toNat
      have hM : IsSmoothHerm M := isSmoothHerm_sqMetric _
      have hA' : IsSmoothHerm A' := hL' _
      have hadd := (hI K' ι').2.1 P' n (Fin.init L') A' M hP' hL0 hA' hM
      have h3 := key (A'.tensor M) (isSmoothHerm_tensor hA' hM) fun k => by
        show 0 ≤ A'.a k + ((-(A'.a k)).toNat : ℤ)
        omega
      have h4 := key M hM fun k => by
        show (0 : ℤ) ≤ ((-(A'.a k)).toNat : ℤ)
        omega
      have e : L' = Fin.snoc (Fin.init L') A' := (Fin.snoc_init_self L').symm
      rw [e]
      linarith

/- English proof (translation)
Introduce `I hI K _ ι _ K' _ ι' _ κ v P' d₀ d r L L' N hv hP' hQ hdd hL hLL hN`. Use `aux hC hIm hInt hVert I hI hv (d + r) d P' d₀ (Fin.append L' N) hP' hQ hdd ?_ ?_` and prove the remaining obligations. Use `⟨Nat.le_add_right d r, L, hL, fun j => ?_⟩` and prove the remaining obligations. Establish `e : Fin.castLE (Nat.le_add_right d r) j = Fin.castAdd r j` using `rfl`. Rewrite using `[e, Fin.append_left]`.

Conclude with `hLL j`. Introduce `j`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Rewrite using `[Fin.append_left]`. Conclude with `IsPullHerm.isSmoothHerm hv (hLL i) (hL i)`.

Rewrite using `[Fin.append_right]`. Conclude with `hN i`.
-/
theorem of_contract (hC : ContractStatement) (hIm : ImageArithStatement) (hInt : PFIntZero.Statement)
    (hVert : PFVert.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d₀ d r L L' N hv hP' hQ hdd hL hLL hN
  refine aux hC hIm hInt hVert I hI hv (d + r) d P' d₀ (Fin.append L' N) hP' hQ hdd ?_ ?_
  · refine ⟨Nat.le_add_right d r, L, hL, fun j => ?_⟩
    have e : Fin.castLE (Nat.le_add_right d r) j = Fin.castAdd r j := rfl
    rw [e, Fin.append_left]
    exact hLL j
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      exact IsPullHerm.isSmoothHerm hv (hLL i) (hL i)
    · rw [Fin.append_right]
      exact hN i

/- English proof (translation)
The claim follows from `of_contract (contract_of hIm hF hV) hIm hInt hVert`.
-/
theorem of_found (hIm : ImageArithStatement) (hF : pointForm_holds.Statement) (hV : ProjectivePointVertical.Statement)
    (hInt : PFIntZero.Statement) (hVert : PFVert.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedStatement :=
  of_contract (contract_of hIm hF hV) hIm hInt hVert

end ContractMixed

end GroundTheory.Heights₂.Heights.Targets
