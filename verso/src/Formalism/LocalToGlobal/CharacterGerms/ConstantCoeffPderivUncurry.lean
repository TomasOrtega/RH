import Formalism.LocalToGlobal.CharacterGerms.RowTieChar
import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfUnitGerm
import Formalism.LocalToGlobal.CharacterGerms.MfactMulCoeffMvExpLinF

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ChG

section Uniq

variable {K : Type} [Field K] [CharZero K] {τ : Type} [Fintype τ]

/- English proof (translation)
Establish `step : ∀ (w : τ) (m : τ →₀ ℕ), MvPowerSeries.coeff (m + Finsupp.single w 1) Ψ * ((m w : K) + 1) = y w * MvPowerSeries.coeff m Ψ`. Introduce `w m`. Establish `h` using `congrArg (MvPowerSeries.coeff m) (hd w)`. Rewrite `h` using `[MvPowerSeries.coeff_pderiv, mul_comm Ψ, MvPowerSeries.coeff_C_mul]`. Conclude with `h`.

Establish `key : ∀ (n : ℕ) (m : τ →₀ ℕ), m.degree = n → MvPowerSeries.coeff m Ψ = MvPowerSeries.coeff m (mvExp (linF y))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `m hm`.

Establish `hm0 : m = 0` using `(Finsupp.degree_eq_zero_iff m).1 hm`. Substitute `hm0` using the available equality. Rewrite using `[coeff_zero_mvExp, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]`. Consider the case `succ n ih`. Introduce `m hm`.

Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w, m w ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_not] at hcon`. Establish `: m = 0` using `Finsupp.ext hcon`. Rewrite `hm` using `[this]`.

Simplify using `at hm`. Choose the witnesses or unpack the hypotheses as in `⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by`. Use `⟨m - Finsupp.single w 1, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Distinguish the cases in `hx : x = w`.

Substitute `hx` using the available equality. Simplify using `only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers. Simplify using `[Ne.symm hx]`. Establish `hdeg : m'.degree = n`.

Rewrite `hm` using `[map_add, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers. Establish `hne : ((m' w : K) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero (m' w)`. Establish `e1` using `step w m'`. Establish `e2` using `coeff_mvExp_linF_step y w m'`.

Rewrite `e1` using `[ih m' hdeg, ← e2]`. Conclude with `mul_right_cancel₀ hne e1`. Use extensionality with `m`. Conclude with `key _ m rfl`.
-/
theorem exp_unique (y : τ → K) (Ψ : MvPowerSeries τ K) (h0 : MvPowerSeries.constantCoeff Ψ = 1)
    (hd : ∀ w, MvPowerSeries.pderiv K w Ψ = Ψ * MvPowerSeries.C (y w)) : Ψ = mvExp (linF y) := by
  have step : ∀ (w : τ) (m : τ →₀ ℕ), MvPowerSeries.coeff (m + Finsupp.single w 1) Ψ * ((m w : K) + 1) =
      y w * MvPowerSeries.coeff m Ψ := by
    intro w m
    have h := congrArg (MvPowerSeries.coeff m) (hd w)
    rw [MvPowerSeries.coeff_pderiv, mul_comm Ψ, MvPowerSeries.coeff_C_mul] at h
    exact h
  have key : ∀ (n : ℕ) (m : τ →₀ ℕ), m.degree = n →
      MvPowerSeries.coeff m Ψ = MvPowerSeries.coeff m (mvExp (linF y)) := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 hm
      subst hm0
      rw [coeff_zero_mvExp, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    | succ n ih =>
      intro m hm
      obtain ⟨w, hw⟩ : ∃ w, m w ≠ 0 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        have : m = 0 := Finsupp.ext hcon
        rw [this] at hm
        simp at hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
        refine ⟨m - Finsupp.single w 1, ?_⟩
        ext x
        by_cases hx : x = w
        · subst hx
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]
          omega
        · simp [Ne.symm hx]
      have hdeg : m'.degree = n := by
        rw [map_add, Finsupp.degree_single] at hm
        omega
      have hne : ((m' w : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m' w)
      have e1 := step w m'
      have e2 := coeff_mvExp_linF_step y w m'
      rw [ih m' hdeg, ← e2] at e1
      exact mul_right_cancel₀ hne e1
  ext m
  exact key _ m rfl

end Uniq

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

open VP

/- English proof (translation)
Establish `h` using `hχ.2.2`. Rewrite `h` using `[eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst]`. Rewrite using `[subst_singlePointUncurry (cc_F Y), subst_singlePointUncurry (fun _ => cc_X _), subst_singlePointUncurry (fun _ => cc_X _)]`. Establish `h2 : (fun p : Fin 1 × Fin dd => addOf Y.B.G.F (pt C dd 0) (pt C dd 1) p.2) = fun p : Fin 1 × Fin dd => Y.B.G.F p.2`. Use function extensionality and compare the values at `p`.

Conclude with `ev_id _`. Rewrite `h` using `[h2]`. Conclude with `h`.
-/
theorem chi_mul {χ : PS C 1 dd} (hχ : Y.IsChar χ) :
    MvPowerSeries.subst (fun k => Y.B.G.F k) (un1 χ) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ) *
        MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (un1 χ) := by
  have h := hχ.2.2
  rw [eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst] at h
  rw [subst_singlePointUncurry (cc_F Y), subst_singlePointUncurry (fun _ => cc_X _), subst_singlePointUncurry (fun _ => cc_X _)]
  have h2 : (fun p : Fin 1 × Fin dd => addOf Y.B.G.F (pt C dd 0) (pt C dd 1) p.2) =
      fun p : Fin 1 × Fin dd => Y.B.G.F p.2 := by
    funext p
    exact ev_id _
  rw [h2] at h
  exact h

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]`. Establish `h1 : MvPowerSeries.coeff (Finsupp.single i 1) (un1 χ) = dlogC χ i` using `by show MvPowerSeries.coeff ((Finsupp.single i 1).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) χ = _`. Rewrite using `[Finsupp.mapDomain_single]`. Both sides reduce to the same expression. Simplify using `[h1]`.
-/
theorem constantCoeff_pderiv_uncurry (χ : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv C i (un1 χ)) = dlogC χ i := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  have h1 : MvPowerSeries.coeff (Finsupp.single i 1) (un1 χ) = dlogC χ i := by
    show MvPowerSeries.coeff ((Finsupp.single i 1).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) χ = _
    rw [Finsupp.mapDomain_single]
    rfl
  simp [h1]

def Psi (χ : PS C 1 dd) : MvPowerSeries (Fin dd) C := MvPowerSeries.subst (e Y) (un1 χ)

/- English proof (translation)
Establish `hFK : ∀ k, Y.B.FK C k = Y.B.G.F k`. Introduce `k`. Use `show MvPowerSeries.map (algebraMap C C) (Y.B.G.F k) = _`. Rewrite using `[Algebra.algebraMap_self, MvPowerSeries.map_id]`. Both sides reduce to the same expression.

Establish `hL : MvPowerSeries.pderiv C i (Psi Y χ) = ∑ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F k)) * MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv C k (un1 χ))`. Unfold `Psi`. Rewrite using `[pderiv_subst (og (cc_e Y))]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `expODE Y i k` as an intermediate fact.

Rewrite `this` using `[hFK]`. Use `show MvPowerSeries.pderiv C i (un1 (Y.ex k)) * _ = _`. Rewrite using `[this]`. Establish `h` using `congrArg (fun G => MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) G)) (chi_mul Y hχ)`. Use `beta_reduce at h`.

Rewrite `h` using `[Derivation.leibniz, pderiv_subst (og (cc_F Y)), pderiv_subst (og fun _ => cc_X _), pderiv_subst (og fun _ => cc_X _), MvPowerSeries.subst_add (hs (cc_exZero Y)), subst_sum (cc_exZero Y), smul_eq_mul, smul_eq_mul, subst_mul (cc_exZero Y), subst_mul (cc_exZero Y), subst_sum (cc_ex …`. Establish `h1 : ∀ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F k) * MvPowerSeries.subst (fun k => Y.B.G.F k) (MvPowerSeries.pderiv C k (un1 χ))) = MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F k)) * MvPowerSeries.subs …`. Introduce `k`. Rewrite using `[subst_mul (cc_exZero Y), subst_subst (cc_F Y) (cc_exZero Y)]`. Use `congr 2`.

Use function extensionality and compare the values at `k'`. Conclude with `F_exZero Y k'`. Establish `h2 : ∀ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd) * MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (MvPowerSeries.pderiv C k (un1 χ))) = 0`. Introduce `k`. Rewrite using `[MvPowerSeries.pderiv_X_of_ne (fun hh => by simpa using (Prod.ext_iff.1 hh).1), zero_mul, subst_zero' (cc_exZero Y)]`.

Establish `h3 : ∀ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd) * MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (MvPowerSeries.pderiv C k (un1 χ))) = if k = i then MvPowerSer …`. Introduce `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Rewrite using `[MvPowerSeries.pderiv_X_self, one_mul, subst_subst (fun _ => cc_X _) (cc_exZero Y), if_pos rfl]`.

Establish `: (fun s : Fin dd => MvPowerSeries.subst (exZero Y) (MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) = fun _ => 0`. Use function extensionality and compare the values at `s`. Rewrite using `[subst_X (cc_exZero Y)]`. Both sides reduce to the same expression. Rewrite using `[this, subst_zeroPt, constantCoeff_pderiv_uncurry]`.

Rewrite using `[MvPowerSeries.pderiv_X_of_ne (fun hh => hk (Prod.ext_iff.1 hh).2), zero_mul, subst_zero' (cc_exZero Y), if_neg hk]`. Establish `h4 : MvPowerSeries.subst (exZero Y) (MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ)) = Psi Y χ`. Rewrite using `[subst_subst (fun _ => cc_X _) (cc_exZero Y)]`. Unfold `Psi`. Use `congr 1`.

Use function extensionality and compare the values at `s`. Rewrite using `[subst_X (cc_exZero Y)]`. Both sides reduce to the same expression. Rewrite `h` using `[Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_congr rfl fun k _ => h2 k, Finset.sum_congr rfl fun k _ => h3 k, Finset.sum_const_zero, mul_zero, add_zero, Finset.sum_ite_eq', h4]`. Rewrite using `[hL, h]`.

Simplify using the standard rewrite rules.
-/
theorem chi_ode {χ : PS C 1 dd} (hχ : Y.IsChar χ) (i : Fin dd) :
    MvPowerSeries.pderiv C i (Psi Y χ) = Psi Y χ * MvPowerSeries.C (dlogC χ i) := by
  have hFK : ∀ k, Y.B.FK C k = Y.B.G.F k := by
    intro k
    show MvPowerSeries.map (algebraMap C C) (Y.B.G.F k) = _
    rw [Algebra.algebraMap_self, MvPowerSeries.map_id]
    rfl

  have hL : MvPowerSeries.pderiv C i (Psi Y χ) =
      ∑ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F k)) *
        MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv C k (un1 χ)) := by
    unfold Psi
    rw [pderiv_subst (og (cc_e Y))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := expODE Y i k
    rw [hFK] at this
    show MvPowerSeries.pderiv C i (un1 (Y.ex k)) * _ = _
    rw [this]

  have h := congrArg (fun G => MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) G)) (chi_mul Y hχ)
  beta_reduce at h
  rw [Derivation.leibniz, pderiv_subst (og (cc_F Y)), pderiv_subst (og fun _ => cc_X _), pderiv_subst (og fun _ => cc_X _),
    MvPowerSeries.subst_add (hs (cc_exZero Y)), subst_sum (cc_exZero Y), smul_eq_mul, smul_eq_mul,
    subst_mul (cc_exZero Y), subst_mul (cc_exZero Y), subst_sum (cc_exZero Y), subst_sum (cc_exZero Y)] at h
  have h1 : ∀ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F k) *
      MvPowerSeries.subst (fun k => Y.B.G.F k) (MvPowerSeries.pderiv C k (un1 χ))) =
      MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F k)) *
        MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv C k (un1 χ)) := by
    intro k
    rw [subst_mul (cc_exZero Y), subst_subst (cc_F Y) (cc_exZero Y)]
    congr 2
    funext k'
    exact F_exZero Y k'
  have h2 : ∀ k, MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.pderiv C ((1 : Fin 2), i) (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv C k (un1 χ))) = 0 := by
    intro k
    rw [MvPowerSeries.pderiv_X_of_ne (fun hh => by simpa using (Prod.ext_iff.1 hh).1), zero_mul,
      subst_zero' (cc_exZero Y)]
  have h3 : ∀ k, MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.pderiv C ((1 : Fin 2), i) (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv C k (un1 χ))) = if k = i then MvPowerSeries.C (dlogC χ i) else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk
      rw [MvPowerSeries.pderiv_X_self, one_mul, subst_subst (fun _ => cc_X _) (cc_exZero Y), if_pos rfl]
      have : (fun s : Fin dd => MvPowerSeries.subst (exZero Y) (MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) =
          fun _ => 0 := by
        funext s
        rw [subst_X (cc_exZero Y)]
        rfl
      rw [this, subst_zeroPt, constantCoeff_pderiv_uncurry]
    · rw [MvPowerSeries.pderiv_X_of_ne (fun hh => hk (Prod.ext_iff.1 hh).2), zero_mul, subst_zero' (cc_exZero Y),
        if_neg hk]
  have h4 : MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ)) = Psi Y χ := by
    rw [subst_subst (fun _ => cc_X _) (cc_exZero Y)]
    unfold Psi
    congr 1
    funext s
    rw [subst_X (cc_exZero Y)]
    rfl
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_congr rfl fun k _ => h2 k,
    Finset.sum_congr rfl fun k _ => h3 k, Finset.sum_const_zero, mul_zero, add_zero, Finset.sum_ite_eq', h4] at h
  rw [hL, h]
  simp

/- English proof (translation)
Take `⟨-, hχ1, -⟩` from `hχ`. Establish `hu : ∀ f : PS C 1 dd, MvPowerSeries.constantCoeff (un1 f) = MvPowerSeries.constantCoeff f`. Introduce `f`. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Use `show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = _`.

Rewrite using `[Finsupp.mapDomain_zero]`. Establish `he0 : ∀ k, MvPowerSeries.constantCoeff (e Y k) = 0` using `fun k => (hu _).trans (Y.ex_const k)`. Establish `hA : MvPowerSeries.HasSubst (e Y)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero he0`. Unfold `Psi`. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hA, finsum_eq_single _ 0]`.

Simplify using `[hu, hχ1]`. Introduce `d hd`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, d s ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hd (Finsupp.ext h)`. Rewrite using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs), smul_zero]`. Rewrite using `[map_pow, he0, zero_pow hs]`.
-/
theorem cc_Psi {χ : PS C 1 dd} (hχ : Y.IsChar χ) : MvPowerSeries.constantCoeff (Psi Y χ) = 1 := by
  obtain ⟨-, hχ1, -⟩ := hχ
  have hu : ∀ f : PS C 1 dd, MvPowerSeries.constantCoeff (un1 f) = MvPowerSeries.constantCoeff f := by
    intro f
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = _
    rw [Finsupp.mapDomain_zero]
  have he0 : ∀ k, MvPowerSeries.constantCoeff (e Y k) = 0 := fun k => (hu _).trans (Y.ex_const k)
  have hA : MvPowerSeries.HasSubst (e Y) := MvPowerSeries.hasSubst_of_constantCoeff_zero he0
  unfold Psi
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hA, finsum_eq_single _ 0]
  · simp [hu, hχ1]
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs), smul_zero]
    rw [map_pow, he0, zero_pow hs]

/- English proof (translation)
The claim follows from `exp_unique (dlogC χ) (Psi Y χ) (cc_Psi Y hχ) (chi_ode Y hχ)`.
-/
theorem chi_exp {χ : PS C 1 dd} (hχ : Y.IsChar χ) : Psi Y χ = mvExp (linF (dlogC χ)) := exp_unique (dlogC χ) (Psi Y χ) (cc_Psi Y hχ) (chi_ode Y hχ)

end ChG

end Formalism.L2.FormalSeriesBounds
