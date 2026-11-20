import Formalism.SharpRestriction.LevelLetterCocycles.RingDataOfIdempotents

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology.J8

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.MainNotions.N
  Formalism.MainNotions.N.RepresentationBoundsCohomology

section Gen

/- English proof (translation)
Conclude with `Matrix.rank_submatrix_le M f g`.
-/
theorem rank_submatrix_le' {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (M : Matrix n n K) (f g : m → n) : (M.submatrix f g).rank ≤ M.rank := by
  exact Matrix.rank_submatrix_le M f g

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg Fin.val h`. Simplify using `only [Fin.coe_castAdd, Fin.coe_natAdd] at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem castAdd_ne_natAdd {r t : ℕ} (b : Fin r) (c : Fin t) : Fin.castAdd t b ≠ Fin.natAdd r c := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h1
  omega

/- English proof (translation)
Set `f : Fin (t + 1) → Fin (r + t)` to `Fin.cons (Fin.castAdd t a) (Fin.natAdd r)`. Set `g : Fin (t + 1) → Fin (r + t)` to `Fin.cons (Fin.castAdd t b) (Fin.natAdd r)`. Set `w : Fin (t + 1) → K` to `Fin.cons (M (Fin.castAdd t a) (Fin.castAdd t b)) (fun _ => 1)`. Establish `h1 : M.submatrix f g = Matrix.diagonal w`. Use extensionality with `p q`.

Consider the cases of `p using Fin.cases with`. Consider the case `zero`. Consider the cases of `q using Fin.cases with`. Consider the case `zero => simp [f, g, w]`. Consider the case `succ q => simp [f, g, w, hac, (Fin.succ_ne_zero q).symm]`.

Consider the case `succ p`. Consider the cases of `q using Fin.cases with`. Consider the case `zero => simp [f, g, w, hcb, Fin.succ_ne_zero p]`. Consider the case `succ q`. Distinguish the cases in `hpq : p = q`.

Substitute `hpq` using the available equality. Simplify using `[f, g, w, hc]`. Simplify using `[f, g, w, hc, hpq]`. Establish `h2` using `rank_submatrix_le' M f g`. Rewrite `h2` using `[h1, Matrix.rank_diagonal]`.

Establish `hw : ∀ p, w p ≠ 0`. Introduce `p`. Consider the cases of `p using Fin.cases with`. Consider the case `zero => simpa [w] using hab`. Consider the case `succ p => simp [w]`.

Establish `h3 : Fintype.card {p // w p ≠ 0} = t + 1`. Rewrite using `[Fintype.card_congr (Equiv.subtypeUnivEquiv hw), Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lt_rank_of {K : Type} [Field K] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) K)
    (hc : ∀ c d : Fin t, M (Fin.natAdd r c) (Fin.natAdd r d) = if c = d then 1 else 0)
    (hcb : ∀ (c : Fin t) (b : Fin r), M (Fin.natAdd r c) (Fin.castAdd t b) = 0)
    (hac : ∀ (a : Fin r) (c : Fin t), M (Fin.castAdd t a) (Fin.natAdd r c) = 0)
    (a b : Fin r) (hab : M (Fin.castAdd t a) (Fin.castAdd t b) ≠ 0) : t + 1 ≤ M.rank := by
  classical
  let f : Fin (t + 1) → Fin (r + t) := Fin.cons (Fin.castAdd t a) (Fin.natAdd r)
  let g : Fin (t + 1) → Fin (r + t) := Fin.cons (Fin.castAdd t b) (Fin.natAdd r)
  let w : Fin (t + 1) → K := Fin.cons (M (Fin.castAdd t a) (Fin.castAdd t b)) (fun _ => 1)
  have h1 : M.submatrix f g = Matrix.diagonal w := by
    ext p q
    cases p using Fin.cases with
    | zero =>
      cases q using Fin.cases with
      | zero => simp [f, g, w]
      | succ q => simp [f, g, w, hac, (Fin.succ_ne_zero q).symm]
    | succ p =>
      cases q using Fin.cases with
      | zero => simp [f, g, w, hcb, Fin.succ_ne_zero p]
      | succ q =>
        by_cases hpq : p = q
        · subst hpq
          simp [f, g, w, hc]
        · simp [f, g, w, hc, hpq]
  have h2 := rank_submatrix_le' M f g
  rw [h1, Matrix.rank_diagonal] at h2
  have hw : ∀ p, w p ≠ 0 := by
    intro p
    cases p using Fin.cases with
    | zero => simpa [w] using hab
    | succ p => simp [w]
  have h3 : Fintype.card {p // w p ≠ 0} = t + 1 := by
    rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hw), Fintype.card_fin]
  omega

/- English proof (translation)
Establish `hent : ∀ x y, (M *ᵥ Pi.single y (1 : K)) x = M x y`. Introduce `x y`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `h2 : ∀ (d : Fin t) y, M (Fin.natAdd r d) y = if Fin.natAdd r d = y then 1 else 0`. Introduce `d y`.

Establish `h` using `congrFun (congrArg Prod.snd (hM (Pi.single y 1))) d`. Simplify using `only [eG_apply] at h`. Rewrite using `[← hent, h, Pi.single_apply]`. Establish `h1 : ∀ a y, M (Fin.castAdd t a) y = (B *ᵥ fun b => (Pi.single y (1 : K) : Fin (r + t) → K) (Fin.castAdd t b)) a`. Introduce `a y`.

Establish `h` using `congrFun (congrArg Prod.fst (hM (Pi.single y 1))) a`. Simplify using `only [eG_apply] at h`. Rewrite using `[← hent, h]`. Establish `hac : ∀ (a : Fin r) (c : Fin t), M (Fin.castAdd t a) (Fin.natAdd r c) = 0`. Introduce `a c`.

Rewrite using `[h1]`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, castAdd_ne_natAdd]`. Establish `hc : ∀ c d : Fin t, M (Fin.natAdd r c) (Fin.natAdd r d) = if c = d then 1 else 0`. Introduce `c d`. Rewrite using `[h2]`.

Distinguish the cases in `hcd : c = d`. Substitute `hcd` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hcd, if_neg]`. Introduce `h`.

Apply `hcd` to reduce the goal to its premises. Establish `h3` using `congrArg Fin.val h`. Simplify using `at h3`. Conclude with `Fin.ext h3`. Establish `hcb : ∀ (c : Fin t) (b : Fin r), M (Fin.natAdd r c) (Fin.castAdd t b) = 0`.

Introduce `c b`. Rewrite using `[h2, if_neg (fun h => castAdd_ne_natAdd b c h.symm)]`. Establish `hB0 : ∀ a b, M (Fin.castAdd t a) (Fin.castAdd t b) = 0`. Introduce `a b`. Assume the negation of the conclusion as `hab`.

Use `lt_rank_of M hc hcb hac a b hab` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use extensionality with `x y`. Consider the cases of `x using Fin.addCases with`. Consider the case `left a`.

Consider the cases of `y using Fin.addCases with`. Consider the case `left b => simp [hB0, Matrix.diagonal_apply, blkG_castAdd]`. Consider the case `right c => simp [hac, Matrix.diagonal_apply, blkG_castAdd]`. Consider the case `right c`. Rewrite using `[h2]`.

Simplify using `[Matrix.diagonal_apply, blkG_natAdd, Fin.succ_ne_zero]`.
-/
theorem eq_diag_of {K : Type} [Field K] {r t : ℕ} (M : Matrix (Fin (r + t)) (Fin (r + t)) K)
    (B : Matrix (Fin r) (Fin r) K)
    (hM : ∀ u, eG r t K (M *ᵥ u) = (B *ᵥ (eG r t K u).1, (eG r t K u).2)) (hrk : M.rank = t) :
    M = Matrix.diagonal fun a => if blkG r t a = 0 then (0 : K) else 1 := by
  classical
  have hent : ∀ x y, (M *ᵥ Pi.single y (1 : K)) x = M x y := by
    intro x y
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h2 : ∀ (d : Fin t) y, M (Fin.natAdd r d) y = if Fin.natAdd r d = y then 1 else 0 := by
    intro d y
    have h := congrFun (congrArg Prod.snd (hM (Pi.single y 1))) d
    simp only [eG_apply] at h
    rw [← hent, h, Pi.single_apply]
  have h1 : ∀ a y, M (Fin.castAdd t a) y = (B *ᵥ fun b => (Pi.single y (1 : K) : Fin (r + t) → K) (Fin.castAdd t b)) a := by
    intro a y
    have h := congrFun (congrArg Prod.fst (hM (Pi.single y 1))) a
    simp only [eG_apply] at h
    rw [← hent, h]
  have hac : ∀ (a : Fin r) (c : Fin t), M (Fin.castAdd t a) (Fin.natAdd r c) = 0 := by
    intro a c
    rw [h1]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, castAdd_ne_natAdd]
  have hc : ∀ c d : Fin t, M (Fin.natAdd r c) (Fin.natAdd r d) = if c = d then 1 else 0 := by
    intro c d
    rw [h2]
    by_cases hcd : c = d
    · subst hcd
      simp
    · rw [if_neg hcd, if_neg]
      intro h
      apply hcd
      have h3 := congrArg Fin.val h
      simp at h3
      exact Fin.ext h3
  have hcb : ∀ (c : Fin t) (b : Fin r), M (Fin.natAdd r c) (Fin.castAdd t b) = 0 := by
    intro c b
    rw [h2, if_neg (fun h => castAdd_ne_natAdd b c h.symm)]
  have hB0 : ∀ a b, M (Fin.castAdd t a) (Fin.castAdd t b) = 0 := by
    intro a b
    by_contra hab
    have := lt_rank_of M hc hcb hac a b hab
    omega
  ext x y
  cases x using Fin.addCases with
  | left a =>
    cases y using Fin.addCases with
    | left b => simp [hB0, Matrix.diagonal_apply, blkG_castAdd]
    | right c => simp [hac, Matrix.diagonal_apply, blkG_castAdd]
  | right c =>
    rw [h2]
    simp [Matrix.diagonal_apply, blkG_natAdd, Fin.succ_ne_zero]

/- English proof (translation)
Establish `hF : ∀ w, Hm w = F w`. Introduce `w`. Take `⟨u, rfl⟩` from `L.surjective w`. Rewrite using `[← h1, h3]`. Introduce `u`.

Rewrite using `[h2, hF]`.
-/
theorem transfer {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (L L' : V ≃ₗ[K] W) (φ : V → V) (F Hm : W → W)
    (h1 : ∀ u, L (φ u) = Hm (L u)) (h2 : ∀ u, L' (φ u) = Hm (L' u)) (h3 : ∀ u, L (φ u) = F (L u)) :
    ∀ u, L' (φ u) = F (L' u) := by
  have hF : ∀ w, Hm w = F w := by
    intro w
    obtain ⟨u, rfl⟩ := L.surjective w
    rw [← h1, h3]
  intro u
  rw [h2, hF]

end Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
  (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i)

def Dg (γ : GE N) (z : (Fin R.r → KK N i) × (Fin R.t → KK N i)) : (Fin R.r → KK N i) × (Fin R.t → KK N i) :=
  ((mapM (toK N i) (rhoO N i ρ π) γ).mulVec z.1,
    fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) γ : (N.O i)ˣ) : N.O i) * z.2 c)

/- English proof (translation)
Take `⟨m, f, g, -, rfl⟩` from `ha`. Use `⟨fun z => ∑ k, toK N i (f k π) • Dg N ρ π (g k) z, fun L hL u => ?_⟩` and prove the remaining obligations. Establish `h : (((∑ k, fun x => f k x • rO N i r x (g k)) π).map (toK N i)).mulVec u = ∑ k, toK N i (f k π) • (mapM (toK N i) (rO N i r π) (g k)).mulVec u`. Rewrite using `[Finset.sum_apply]`. Express the relevant statement in the definitionally equal form `((toK N i).mapMatrix (∑ k, f k π • rO N i r π (g k))).mulVec u = _`.

Rewrite using `[map_sum, Matrix.sum_mulVec]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[← Matrix.smul_mulVec]`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `[mapM, Matrix.smul_apply]`. Rewrite using `[h, map_sum]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, hL]`.
-/
theorem act_inR {a : N.X i → MatN N i} (ha : InR N i r a) :
    ∃ Hm : (Fin R.r → KK N i) × (Fin R.t → KK N i) → (Fin R.r → KK N i) × (Fin R.t → KK N i),
      ∀ L : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
      (∀ γ u, L ((mapM (toK N i) (rO N i r π) γ).mulVec u) = Dg N ρ π γ (L u)) →
      ∀ u, L (((a π).map (toK N i)).mulVec u) = Hm (L u) := by
  obtain ⟨m, f, g, -, rfl⟩ := ha
  refine ⟨fun z => ∑ k, toK N i (f k π) • Dg N ρ π (g k) z, fun L hL u => ?_⟩
  have h : (((∑ k, fun x => f k x • rO N i r x (g k)) π).map (toK N i)).mulVec u =
      ∑ k, toK N i (f k π) • (mapM (toK N i) (rO N i r π) (g k)).mulVec u := by
    rw [Finset.sum_apply]
    change ((toK N i).mapMatrix (∑ k, f k π • rO N i r π (g k))).mulVec u = _
    rw [map_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Matrix.smul_mulVec]
    congr 1
    ext a b
    simp [mapM, Matrix.smul_apply]
  rw [h, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, hL]

/- English proof (translation)
Establish `h` using `Inst.inSpan_tSpan N i (N.T i) (rO N i r) (N.O i) ha`. Establish `e1 : (fun x => (a x).map (algebraMap (N.O i) (N.O i))) = a`. Use function extensionality and compare the values at `x`. Conclude with `Inst.map_self _`. Establish `e2 : Inst.repF N i (rO N i r) (N.O i) = repX N r`.

Use extensionality with `γ x : 2`. Rewrite using `[Inst.repF_apply, Inst.map_self]`. Both sides reduce to the same expression. Rewrite `h` using `[e1, e2]`. Conclude with `h`.
-/
theorem tSpan_of_inR {a : N.X i → MatN N i} (ha : InR N i r a) : a ∈ tSpan (N.T i) (repX N r) := by
  have h := Inst.inSpan_tSpan N i (N.T i) (rO N i r) (N.O i) ha
  have e1 : (fun x => (a x).map (algebraMap (N.O i) (N.O i))) = a := by
    funext x
    exact Inst.map_self _
  have e2 : Inst.repF N i (rO N i r) (N.O i) = repX N r := by
    ext γ x : 2
    rw [Inst.repF_apply, Inst.map_self]
    rfl
  rw [e1, e2] at h
  exact h

/- English proof (translation)
Take `⟨b, hbT, -, hind⟩` from `Inst.descent_hyps N hG`. Establish `hG'` using `hG`. Take `⟨-, -, -, -, -, -, -, ⟨-, -, -, -, hcard⟩, hroots, -⟩` from `hG'`. Establish `hcF : Fintype.card {y // S.p y = S.p x'} = R.t.factorial`. Rewrite using `[← Nat.card_eq_fintype_card]`.

Conclude with `hcard (S.p x')`. Set `Φ : {y // S.p y = S.p x'} → (Fin R.t → N.O i)` to `fun y c => S.rr (1 + (c : ℕ)) y.1`. Establish `hinj : Function.Injective Φ`. Introduce `y z hyz`. Apply `Inst.sep_of_indep hcF (fun k (y : {y // S.p y = S.p x'}) => b k y.1) (fun a ha => hind (S.p x') a (fun y hy => ha ⟨y, hy⟩)) y z` to reduce the goal to its premises.

Introduce `k`. Use `Inst.T'_eq_of_rr N hG (y.2.trans z.2.symm) (fun c hc => ?_) (b k) (hbT k)` and prove the remaining obligations. Establish `hc'` using `Finset.mem_Icc.mp hc`. Establish `h1` using `congrFun hyz ⟨c - 1, by omega⟩`. Simplify `h1` using `[Φ, show 1 + (c - 1) = c by omega]`.

Establish `hP : ∀ y : {y // S.p y = S.p x'}, ∏ c, (Polynomial.X - Polynomial.C (Φ y c)) = ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x'))`. Introduce `y`. Establish `h1 : ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c y.1)) = ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x'))`. Rewrite using `[hroots y.1, hroots x', y.2]`. Rewrite using `[← h1]`.

Establish `h2 : Finset.Icc 1 R.t = Finset.Ico 1 (R.t + 1)`. Use extensionality with `c`. Simplify using `[Finset.mem_Icc, Finset.mem_Ico]`. Rewrite using `[h2, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, ← Fin.prod_univ_eq_prod_range (fun c => (Polynomial.X : Polynomial (N.O i)) - Polynomial.C (S.rr (1 + c) y.1))]`. Conclude with `Inst.inj_of_card Φ hinj _ hP hcF.ge ⟨x', rfl⟩`.
-/
theorem rr_inj {S : IdempotentChoiceData N i} (hG : GoodCongruenceObjects N r ρ π S) (x' : S.X') :
    Function.Injective (fun c : Fin R.t => S.rr (1 + (c : ℕ)) x') := by
  classical
  obtain ⟨b, hbT, -, hind⟩ := Inst.descent_hyps N hG
  have hG' := hG
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, -, hcard⟩, hroots, -⟩ := hG'
  have hcF : Fintype.card {y // S.p y = S.p x'} = R.t.factorial := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard (S.p x')
  let Φ : {y // S.p y = S.p x'} → (Fin R.t → N.O i) := fun y c => S.rr (1 + (c : ℕ)) y.1
  have hinj : Function.Injective Φ := by
    intro y z hyz
    apply Inst.sep_of_indep hcF (fun k (y : {y // S.p y = S.p x'}) => b k y.1)
      (fun a ha => hind (S.p x') a (fun y hy => ha ⟨y, hy⟩)) y z
    intro k
    refine Inst.T'_eq_of_rr N hG (y.2.trans z.2.symm) (fun c hc => ?_) (b k) (hbT k)
    have hc' := Finset.mem_Icc.mp hc
    have h1 := congrFun hyz ⟨c - 1, by omega⟩
    simpa [Φ, show 1 + (c - 1) = c by omega] using h1
  have hP : ∀ y : {y // S.p y = S.p x'}, ∏ c, (Polynomial.X - Polynomial.C (Φ y c)) =
      ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) := by
    intro y
    have h1 : ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c y.1)) =
        ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (S.rr c x')) := by
      rw [hroots y.1, hroots x', y.2]
    rw [← h1]
    have h2 : Finset.Icc 1 R.t = Finset.Ico 1 (R.t + 1) := by
      ext c
      simp [Finset.mem_Icc, Finset.mem_Ico]
    rw [h2, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
      ← Fin.prod_univ_eq_prod_range
        (fun c => (Polynomial.X : Polynomial (N.O i)) - Polynomial.C (S.rr (1 + c) y.1))]
  exact Inst.inj_of_card Φ hinj _ hP hcF.ge ⟨x', rfl⟩

/- English proof (translation)
Rewrite using `[Fin.prod_univ_eq_prod_range (fun c => F (1 + c)) t, Finset.range_eq_Ico]`. Repeatedly rewrite using `[add_comm 1]`. Rewrite using `[Finset.prod_Ico_add' F 0 t 1, zero_add]`. Both sides reduce to the same expression.
-/
theorem prod_Icc_fin (t : ℕ) (F : ℕ → Polynomial (N.O i)) :
    ∏ c ∈ Finset.Icc 1 t, F c = ∏ c : Fin t, F (1 + (c : ℕ)) := by
  rw [Fin.prod_univ_eq_prod_range (fun c => F (1 + c)) t, Finset.range_eq_Ico]
  simp_rw [add_comm 1]
  rw [Finset.prod_Ico_add' F 0 t 1, zero_add]
  rfl

def sOf (S : IdempotentChoiceData N i) : N.X i → MatN N i := S.X0 - S.eB * repX N r S.g0 * S.eB

section Comp

open Formalism.NG

end Comp

end Formalism.MainNotions.N.RepresentationBoundsCohomology.J8

end
