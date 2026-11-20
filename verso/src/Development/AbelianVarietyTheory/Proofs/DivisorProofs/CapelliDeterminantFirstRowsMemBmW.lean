import Mathlib
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Development.AbelianVarietyTheory.Definitions.Foundations.TracePowApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaPhiBranchOperator

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck

noncomputable section

namespace GlobalTheory.BrCompare

def rE (K : Type) [Field K] (n m : ℕ) (i j : Fin n) : Module.End K (MvPolynomial (Fin (n + 1) × Fin m) K) :=
  rowE K (n + 1) m i.castSucc j.castSucc

def rCap (K : Type) [Field K] (n m : ℕ) (u : ℤ) : Module.End K (MvPolynomial (Fin (n + 1) × Fin m) K) :=
  capDet (rE K n m) u

def lamN {n : ℕ} (lam : DomWeight (n + 1)) : Fin n → ℕ := fun i => lam.natW i.castSucc

def incl (K : Type) [Field K] (n : ℕ) :
    MvPolynomial (Fin (n + 1) × Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1) × Fin (n + 1)) K :=
  rename (Prod.map id Fin.castSucc)

def bfact {n : ℕ} (b : Fin n → ℕ) : ℕ := ∏ s, (b s).factorial

def coefOne (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ) (x : MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :
    MvPolynomial (Fin n × Fin n) K :=
  rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)
    (Formalism.L2.Col.Br.coefLast (rfl : n + 1 = n + 1) (fun _ : Unit => b)
      (rename (fun v : Fin (n + 1) × Fin (n + 1) => (((), v) : Unit × Fin (n + 1) × Fin (n + 1))) x))

def zList {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n) : List ℤ :=
  (List.ofFn fun i : Fin n => (((GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.rangeSet lam sg i).erase (sg.w i)).toList).map fun v =>
    v - lam.w (Fin.last n) - (i.val : ℤ)).flatten

section Basic

variable {K : Type} [Field K]

/- English proof (translation)
The claim follows from `@fockSHerm K _ starRingOfComm _ g f`.
-/
theorem fockB_symm {σ : Type} (f g : MvPolynomial σ K) : fockB f g = fockB g f :=
  @fockSHerm K _ starRingOfComm _ g f

/- English proof (translation)
Conclude with `@fockL_X_pderiv K _ starRingOfComm σ _ v f g`.
-/
theorem fockB_X_mul {σ : Type} (v : σ) (f g : MvPolynomial σ K) : fockB (X v * f) g = fockB f (pderiv v g) := by
  classical
  exact @fockL_X_pderiv K _ starRingOfComm σ _ v f g

/- English proof (translation)
Rewrite using `[rowE_apply, rowE_apply, ← fockBL_apply, ← fockBL_apply, map_sum, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[fockBL_apply, fockBL_apply, fockB_X_mul, fockB_symm f, fockB_X_mul, fockB_symm]`.
-/
theorem fockB_rowE {r m : ℕ} (a b : Fin r) (f g : MvPolynomial (Fin r × Fin m) K) :
    fockB (rowE K r m a b f) g = fockB f (rowE K r m b a g) := by
  rw [rowE_apply, rowE_apply, ← fockBL_apply, ← fockBL_apply, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [fockBL_apply, fockBL_apply, fockB_X_mul, fockB_symm f, fockB_X_mul, fockB_symm]

/- English proof (translation)
Establish `h` using `glRel_rowE K (n + 1) m i.castSucc j.castSucc k.castSucc l.castSucc`. Simplify using `only [Fin.castSucc_inj] at h`. Simplify using `only [rE, h, eq_comm (a := l)]`.
-/
theorem rE_rel (n m : ℕ) (i j k l : Fin n) :
    rE K n m i j * rE K n m k l - rE K n m k l * rE K n m i j =
      (if j = k then rE K n m i l else 0) - (if i = l then rE K n m k j else 0) := by
  have h := glRel_rowE K (n + 1) m i.castSucc j.castSucc k.castSucc l.castSucc
  simp only [Fin.castSucc_inj] at h
  simp only [rE, h, eq_comm (a := l)]

/- English proof (translation)
Rewrite `h` using `[← two_smul K x]`. Conclude with `(smul_eq_zero.1 h).resolve_left two_ne_zero`.
-/
theorem end_two [CharZero K] {M : Type} [AddCommGroup M] [Module K M] (x : Module.End K M) (h : x + x = 0) : x = 0 := by
  rw [← two_smul K x] at h
  exact (smul_eq_zero.1 h).resolve_left two_ne_zero

/- English proof (translation)
The claim follows from `capDet_central _ u (rE_rel n m) end_two k l`.
-/
theorem rE_comm_rCap [CharZero K] (n m : ℕ) (u : ℤ) (k l : Fin n) : Commute (rE K n m k l) (rCap K n m u) :=
  capDet_central _ u (rE_rel n m) end_two k l

/- English proof (translation)
The claim follows from `capDet_commute_of _ v _ fun i j => (rE_comm_rCap n m u i j).symm`.
-/
theorem rCap_comm [CharZero K] (n m : ℕ) (u v : ℤ) : Commute (rCap K n m u) (rCap K n m v) :=
  capDet_commute_of _ v _ fun i j => (rE_comm_rCap n m u i j).symm

/- English proof (translation)
Rewrite using `[(rowE_eq_rowDiv K r m a b f).1]`. Conclude with `rowDivStable K r m ν a b 1 f hf`.
-/
theorem rowE_mem {r m : ℕ} {ν : Fin m → ℕ} (a b : Fin r) {f : MvPolynomial (Fin r × Fin m) K}
    (hf : f ∈ dualWeyl K r m ν) : rowE K r m a b f ∈ dualWeyl K r m ν := by
  rw [(rowE_eq_rowDiv K r m a b f).1]
  exact rowDivStable K r m ν a b 1 f hf

/- English proof (translation)
Establish `h1 : ∀ (k a i : Fin n) x, bmF E' u k a i (φ x) = φ (bmF E u k a i x)`. Introduce `k a i x`. Unfold `bmF`. Use `split_ifs`. Simplify using `only [LinearMap.sub_apply, Module.End.intCast_apply, h, map_sub, map_zsmul]`.

Simplify using `[h]`. Establish `h2 : ∀ (l : List (Fin n)) (α β : Fin n → Fin n) x, (l.map fun k => bmF E' u k (α k) (β k)).prod (φ x) = φ ((l.map fun k => bmF E u k (α k) (β k)).prod x)`. Introduce `l α β x`. Proceed by induction on `l with`. Consider the case `nil => simp`.

Consider the case `cons a l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, h1]`. Simplify using `only [capDet, bmPi, bmM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, List.ofFn_eq_map, h2]`.
-/
theorem capDet_intertwine {M M' : Type} [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M'] {n : ℕ}
    (E : Fin n → Fin n → Module.End K M) (E' : Fin n → Fin n → Module.End K M') (φ : M →ₗ[K] M')
    (h : ∀ i j x, E' i j (φ x) = φ (E i j x)) (u : ℤ) (x : M) : capDet E' u (φ x) = φ (capDet E u x) := by
  have h1 : ∀ (k a i : Fin n) x, bmF E' u k a i (φ x) = φ (bmF E u k a i x) := by
    intro k a i x
    unfold bmF
    split_ifs
    · simp only [LinearMap.sub_apply, Module.End.intCast_apply, h, map_sub, map_zsmul]
    · simp [h]
  have h2 : ∀ (l : List (Fin n)) (α β : Fin n → Fin n) x, (l.map fun k => bmF E' u k (α k) (β k)).prod (φ x) =
      φ ((l.map fun k => bmF E u k (α k) (β k)).prod x) := by
    intro l α β x
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, h1]
  simp only [capDet, bmPi, bmM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, List.ofFn_eq_map, h2]

/- English proof (translation)
Use `capDet_intertwine (fun i j => (E i j).restrict (h i j)) E W.subtype (fun _ _ _ => rfl) u ⟨x, hx⟩` as an intermediate fact. Rewrite using `[show x = W.subtype ⟨x, hx⟩ from rfl, this]`. Conclude with `Subtype.property _`.
-/
theorem capDet_mem {M : Type} [AddCommGroup M] [Module K M] {n : ℕ} (E : Fin n → Fin n → Module.End K M)
    (W : Submodule K M) (h : ∀ i j, ∀ x ∈ W, E i j x ∈ W) (u : ℤ) {x : M} (hx : x ∈ W) : capDet E u x ∈ W := by
  have := capDet_intertwine (fun i j => (E i j).restrict (h i j)) E W.subtype (fun _ _ _ => rfl) u ⟨x, hx⟩
  rw [show x = W.subtype ⟨x, hx⟩ from rfl, this]
  exact Subtype.property _

/- English proof (translation)
Unfold `rE`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [emb, rowE_C]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`.

Take `⟨a, s⟩` from `v`. Rewrite using `[map_mul, rowE_mul, rowE_mul, hp, map_add, map_mul, map_mul, bmF_emb_X, rowE_X, rowE_X]`. Apply the tactic sequence `by_cases h : j = a <;> simp [h, bmF_emb_X]`.
-/
theorem rE_emb (n : ℕ) (i j : Fin n) (f : MvPolynomial (Fin n × Fin n) K) :
    rE K n n i j (emb K n f) = emb K n (rowE K n n i j f) := by
  unfold rE
  induction f using MvPolynomial.induction_on with
  | C a => simp [emb, rowE_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    rw [map_mul, rowE_mul, rowE_mul, hp, map_add, map_mul, map_mul, bmF_emb_X, rowE_X, rowE_X]
    by_cases h : j = a <;> simp [h, bmF_emb_X]

/- English proof (translation)
Unfold `rE zmon`. Use `Finset.prod_induction _ (fun P => rowE K (n + 1) n i.castSucc j.castSucc P = 0) ?_ ?_ ?_` and prove the remaining obligations. Introduce `a b ha hb`. Rewrite using `[rowE_mul, ha, hb]`. Simplify using the standard rewrite rules.

Conclude with `rowE_C K _ _ _ _ 1`. Introduce `s _`. Proceed by induction on `b s with`. Consider the case `zero => exact rowE_C K _ _ _ _ 1`. Consider the case `succ k ih => rw [pow_succ, rowE_mul, ih, rowE_X, if_neg (Fin.castSucc_lt_last j).ne]`.

Simplify using the standard rewrite rules.
-/
theorem rE_zmon (n : ℕ) (i j : Fin n) (b : Fin n → ℕ) : rE K n n i j (zmon K n b) = 0 := by
  unfold rE zmon
  refine Finset.prod_induction _ (fun P => rowE K (n + 1) n i.castSucc j.castSucc P = 0) ?_ ?_ ?_
  · intro a b ha hb
    rw [rowE_mul, ha, hb]; simp
  · exact rowE_C K _ _ _ _ 1
  · intro s _
    induction b s with
    | zero => exact rowE_C K _ _ _ _ 1
    | succ k ih => rw [pow_succ, rowE_mul, ih, rowE_X, if_neg (Fin.castSucc_lt_last j).ne]; simp

/- English proof (translation)
Establish `h1` using `rE_zmon (K := K) n i j b`. Establish `h2` using `rE_emb n i j f`. Unfold `rE at *`. Rewrite using `[rowE_mul, h1, h2, zero_mul, zero_add]`.
-/
theorem rE_lead (n : ℕ) (i j : Fin n) (b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) K) :
    rE K n n i j (zmon K n b * emb K n f) = zmon K n b * emb K n (rowE K n n i j f) := by
  have h1 := rE_zmon (K := K) n i j b
  have h2 := rE_emb n i j f
  unfold rE at *
  rw [rowE_mul, h1, h2, zero_mul, zero_add]

/- English proof (translation)
The claim follows from `capDet_intertwine (fun i j => rowE K n n i j) (rE K n n) (LinearMap.mulLeft K (zmon K n b) ∘ₗ (emb K n).toLinearMap) (fun i j x => rE_lead n i j b x) u f`.
-/
theorem rCap_lead (n : ℕ) (u : ℤ) (b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) K) :
    rCap K n n u (zmon K n b * emb K n f) = zmon K n b * emb K n (capDet (fun i j => rowE K n n i j) u f) :=
  capDet_intertwine (fun i j => rowE K n n i j) (rE K n n)
    (LinearMap.mulLeft K (zmon K n b) ∘ₗ (emb K n).toLinearMap) (fun i j x => rE_lead n i j b x) u f

/- English proof (translation)
Unfold `rE`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [incl, rowE_C]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`.

Take `⟨a, s⟩` from `v`. Establish `hX : ∀ a s, incl K n (X (a, s)) = X (a, s.castSucc)` using `fun a s => rename_X _ _`. Rewrite using `[map_mul, rowE_mul, rowE_mul, hp, map_add, map_mul, map_mul, hX, rowE_X, rowE_X]`. Apply the tactic sequence `by_cases h : j.castSucc = a <;> simp [h, hX]`.
-/
theorem rE_incl (n : ℕ) (i j : Fin n) (f : BP K n) :
    rE K n (n + 1) i j (incl K n f) = incl K n (rE K n n i j f) := by
  unfold rE
  induction f using MvPolynomial.induction_on with
  | C a => simp [incl, rowE_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    have hX : ∀ a s, incl K n (X (a, s)) = X (a, s.castSucc) := fun a s => rename_X _ _
    rw [map_mul, rowE_mul, rowE_mul, hp, map_add, map_mul, map_mul, hX, rowE_X, rowE_X]
    by_cases h : j.castSucc = a <;> simp [h, hX]

/- English proof (translation)
The claim follows from `capDet_intertwine (rE K n n) (rE K n (n + 1)) (incl K n).toLinearMap (rE_incl n) u f`.
-/
theorem rCap_incl (n : ℕ) (u : ℤ) (f : BP K n) : rCap K n (n + 1) u (incl K n f) = incl K n (rCap K n n u f) :=
  capDet_intertwine (rE K n n) (rE K n (n + 1)) (incl K n).toLinearMap (rE_incl n) u f

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c => rw [rowE_C, derivation_C]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Take `⟨c, s⟩` from `v`.

Rewrite using `[rowE_mul, hp, Derivation.leibniz, mkDerivation_X, rowE_X]`. Simplify using `only [smul_eq_mul, eq_comm (a := b)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rowE_eq_deriv {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) K) :
    rowE K r m a b f = mkDerivation K (fun v : Fin r × Fin m =>
      if v.1 = b then (X (a, v.2) : MvPolynomial (Fin r × Fin m) K) else 0) f := by
  induction f using MvPolynomial.induction_on with
  | C c => rw [rowE_C, derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    obtain ⟨c, s⟩ := v
    rw [rowE_mul, hp, Derivation.leibniz, mkDerivation_X, rowE_X]
    simp only [smul_eq_mul, eq_comm (a := b)]
    ring

/- English proof (translation)
Use `commute_weightedComponent_of_monomial w _ (fun μ => ?_) β` and prove the remaining obligations. Establish `h` using `bm_deriv_monomial_WH (R := K) w 0 (fun v : Fin (n + 1) × Fin m => if v.1 = j.castSucc then (X (i.castSucc, v.2) : MvPolynomial (Fin (n + 1) × Fin m) K) else 0) (fun v => by split_ifs with hv`. Take `⟨a, s⟩` from `v`. Take `rfl : a = j.castSucc` from `hv`. Rewrite using `[add_zero, hw j i]`.

Conclude with `isWeightedHomogeneous_X K w _`. Conclude with `isWeightedHomogeneous_zero K w _) μ`. Rewrite `h` using `[add_zero, ← rowE_eq_deriv]`. Then use the resulting hypothesis.
-/
theorem comp_comm_rE {B : Type} [AddCommMonoid B] [IsRightCancelAdd B] (n m : ℕ) (w : Fin (n + 1) × Fin m → B)
    (hw : ∀ (a a' : Fin n) s, w (a.castSucc, s) = w (a'.castSucc, s)) (β : B) (i j : Fin n) :
    Commute (weightedHomogeneousComponent w β : Module.End K (MvPolynomial (Fin (n + 1) × Fin m) K)) (rE K n m i j) := by
  refine commute_weightedComponent_of_monomial w _ (fun μ => ?_) β
  have h := bm_deriv_monomial_WH (R := K) w 0 (fun v : Fin (n + 1) × Fin m =>
      if v.1 = j.castSucc then (X (i.castSucc, v.2) : MvPolynomial (Fin (n + 1) × Fin m) K) else 0)
    (fun v => by
      split_ifs with hv
      · obtain ⟨a, s⟩ := v
        obtain rfl : a = j.castSucc := hv
        rw [add_zero, hw j i]
        exact isWeightedHomogeneous_X K w _
      · exact isWeightedHomogeneous_zero K w _) μ
  rwa [add_zero, ← rowE_eq_deriv] at h

/- English proof (translation)
The claim follows from `comp_comm_rE n n (zW n) (fun a a' s => by rw [bmF_zW_castSucc, bmF_zW_castSucc]) β i j`.
-/
theorem zcomp_comm_rE (n : ℕ) (β : Fin n → ℤ) (i j : Fin n) : Commute (zcomp K n β) (rE K n n i j) :=
  comp_comm_rE n n (zW n) (fun a a' s => by rw [bmF_zW_castSucc, bmF_zW_castSucc]) β i j

/- English proof (translation)
The claim follows from `comp_comm_rE n n (lastW n) (fun a a' s => by rw [bmF_lastW_castSucc, bmF_lastW_castSucc]) d i j`.
-/
theorem lastcomp_comm_rE (n d : ℕ) (i j : Fin n) :
    Commute (weightedHomogeneousComponent (lastW n) d : Module.End K (BP K n)) (rE K n n i j) :=
  comp_comm_rE n n (lastW n) (fun a a' s => by rw [bmF_lastW_castSucc, bmF_lastW_castSucc]) d i j

/- English proof (translation)
Rewrite `hG`, the goal using `[bmK_mem_alt]`. Conclude with `⟨rowE_mem _ _ hG.1, bm_isWH_of_comm (lastW n) d _ (lastcomp_comm_rE n d i j) G hG.2⟩`.
-/
theorem glOperatorFirstRows_mem_bmW {n d : ℕ} {lam : Fin n → ℕ} (i j : Fin n) {G : BP K n} (hG : G ∈ bmW K n lam d) :
    rE K n n i j G ∈ bmW K n lam d := by
  rw [bmK_mem_alt] at hG ⊢
  exact ⟨rowE_mem _ _ hG.1, bm_isWH_of_comm (lastW n) d _ (lastcomp_comm_rE n d i j) G hG.2⟩

/- English proof (translation)
The claim follows from `capDet_mem _ _ (fun i j _ hx => glOperatorFirstRows_mem_bmW i j hx) u hG`.
-/
theorem capelliDeterminantFirstRows_mem_bmW {n d : ℕ} {lam : Fin n → ℕ} (u : ℤ) {G : BP K n} (hG : G ∈ bmW K n lam d) :
    rCap K n n u G ∈ bmW K n lam d :=
  capDet_mem _ _ (fun i j _ hx => glOperatorFirstRows_mem_bmW i j hx) u hG

/- English proof (translation)
The claim follows from `capDet_commute_of _ u _ (zcomp_comm_rE n β)`.
-/
theorem zcomp_comm_rCap (n : ℕ) (β : Fin n → ℤ) (u : ℤ) : Commute (zcomp K n β) (rCap K n n u) :=
  capDet_commute_of _ u _ (zcomp_comm_rE n β)

/- English proof (translation)
Rewrite using `[rowE_apply, coeff_sum, rowDeg, Nat.cast_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_X_mul']`. Use `split_ifs with h`. Establish `h1 : Finsupp.single (a, s) 1 ≤ μ`.

Rewrite using `[Finsupp.single_le_iff]`. Conclude with `Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)`. Rewrite using `[coeff_pderiv, tsub_add_cancel_of_le h1, mul_comm]`. Use `congr 1`. Establish `h2 : 1 ≤ μ (a, s)` using `Finsupp.single_le_iff.1 h1`.

Simplify using `[Nat.cast_sub h2]`. Rewrite using `[Finsupp.notMem_support_iff.1 h]`. Simplify using the standard rewrite rules.
-/
theorem coeff_rowE_self {r m : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin m) K) (μ : Fin r × Fin m →₀ ℕ) :
    coeff μ (rowE K r m a a f) = (rowDeg μ a : K) * coeff μ f := by
  classical
  rw [rowE_apply, coeff_sum, rowDeg, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_X_mul']
  split_ifs with h
  · have h1 : Finsupp.single (a, s) 1 ≤ μ := by
      rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
    rw [coeff_pderiv, tsub_add_cancel_of_le h1, mul_comm]
    congr 1
    have h2 : 1 ≤ μ (a, s) := Finsupp.single_le_iff.1 h1
    simp [Nat.cast_sub h2]
  · rw [Finsupp.notMem_support_iff.1 h]; simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h a`. Use extensionality with `μ`. Rewrite using `[coeff_rowE_self, coeff_smul, smul_eq_mul]`. Distinguish the cases in `h0 : coeff μ f = 0`.

Simplify using `[h0]`. Rewrite using `[← bm_weight_rowW, h h0]`. Introduce `h μ h0`. Use function extensionality and compare the values at `a`. Use `congrArg (coeff μ) (h a)` as an intermediate fact.

Rewrite `this` using `[coeff_rowE_self, coeff_smul, smul_eq_mul]`. Rewrite using `[bm_weight_rowW]`. Conclude with `mul_right_cancel₀ h0 this` after adjusting the coercions.
-/
theorem rowWeight_iff [CharZero K] {r m : ℕ} (ρ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin m) K) :
    IsWeightedHomogeneous (rowW r m) f ρ ↔ ∀ a, rowE K r m a a f = (ρ a : K) • f := by
  constructor
  · intro h a
    ext μ
    rw [coeff_rowE_self, coeff_smul, smul_eq_mul]
    by_cases h0 : coeff μ f = 0
    · simp [h0]
    · rw [← bm_weight_rowW, h h0]
  · intro h μ h0
    funext a
    have := congrArg (coeff μ) (h a)
    rw [coeff_rowE_self, coeff_smul, smul_eq_mul] at this
    rw [bm_weight_rowW]
    exact_mod_cast mul_right_cancel₀ h0 this

/- English proof (translation)
The claim follows from `Finset.sum_eq_zero fun μ hμ => by rw [h μ (mem_support_iff.1 hμ)]; simp`.
-/
theorem fockB_eq_zero {σ : Type} (f g : MvPolynomial σ K) (h : ∀ μ, coeff μ f ≠ 0 → coeff μ g = 0) : fockB f g = 0 :=
  Finset.sum_eq_zero fun μ hμ => by rw [h μ (mem_support_iff.1 hμ)]; simp

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on generalizing g with`. Consider the case `C a`. Establish `h1 : ∀ {σ : Type} (g : MvPolynomial σ K), fockB (C a) g = a * constantCoeff g` using `fun g => @fockL_C_left K _ starRingOfComm _ a g`. Rewrite using `[rename_C, h1, h1, constantCoeff_rename]`. Consider the case `add p q hp hq => simp only [← fockBL_apply, map_add, LinearMap.add_apply] at *`.

Rewrite using `[hp, hq]`. Consider the case `mul_X p v hp => rw [mul_comm, map_mul, rename_X, fockB_X_mul, fockB_X_mul, pderiv_rename he, hp]`.
-/
theorem fockB_rename {σ τ : Type} {e : σ → τ} (he : Function.Injective e) (f g : MvPolynomial σ K) :
    fockB (rename e f) (rename e g) = fockB f g := by
  classical
  induction f using MvPolynomial.induction_on generalizing g with
  | C a =>
    have h1 : ∀ {σ : Type} (g : MvPolynomial σ K), fockB (C a) g = a * constantCoeff g :=
      fun g => @fockL_C_left K _ starRingOfComm _ a g
    rw [rename_C, h1, h1, constantCoeff_rename]
  | add p q hp hq => simp only [← fockBL_apply, map_add, LinearMap.add_apply] at *; rw [hp, hq]
  | mul_X p v hp => rw [mul_comm, map_mul, rename_X, fockB_X_mul, fockB_X_mul, pderiv_rename he, hp]

/- English proof (translation)
The claim follows from `fockB_rename (Function.injective_id.prodMap (Fin.castSucc_injective n)) f g`.
-/
theorem fockB_incl (n : ℕ) (f g : BP K n) : fockB (incl K n f) (incl K n g) = fockB f g :=
  fockB_rename (Function.injective_id.prodMap (Fin.castSucc_injective n)) f g

end Basic

end GlobalTheory.BrCompare
