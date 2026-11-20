import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementD
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResInto
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.FiltrationBotHolds

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section U
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eulW_eq : eulW p K r = ProjS.eulL (fun c : Fin r => (Fin.last K, c)) := rfl

/- English proof (translation)
Simplify using `only [Uop, Wm, eulW_eq, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.sum_apply]`.
-/
theorem Uop_apply (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    Uop p LL c Cs a F =
      X (Fin.last K, a) * (((c : ℤ) : ℚ_[p]) • F - ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F) -
        ∑ b ∈ Cs, X (Fin.last K, b) * glAct p LL K a b F := by
  simp only [Uop, Wm, eulW_eq, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.smul_apply, LinearMap.id_apply, LinearMap.sum_apply]

/- English proof (translation)
Rewrite using `[glAct_split LL K (K + 1) s t]`. Simplify using `only [LinearMap.add_apply, map_add]`. Rewrite using `[glRest_comm LL K (K + 1) (Nat.le_succ K) s t a b F, ← glAct_comm LL K s t a b F]`. Normalize the expressions using the abelian group laws.
-/
theorem glAct_succ_comm (LL : Letters (K + 1)) (s t a b : Fin r) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL (K + 1) s t (glAct p LL K a b F) - glAct p LL K a b (glAct p LL (K + 1) s t F) =
      (if t = a then glAct p LL K s b F else 0) - (if b = s then glAct p LL K a t F else 0) := by
  rw [glAct_split LL K (K + 1) s t]
  simp only [LinearMap.add_apply, map_add]
  rw [glRest_comm LL K (K + 1) (Nat.le_succ K) s t a b F, ← glAct_comm LL K s t a b F]
  abel

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[mem_restrictSupport_iff]`. Introduce `m hm`. Apply `hx` to reduce the goal to its premises. Rewrite `hm`, the goal using `[Finset.mem_coe, mem_support_iff]`.

Rewrite `hm` using `[ProjS.coeff_eulL]`. Conclude with `left_ne_zero_of_mul hm`.
-/
theorem eulL_keep_supp {σ : Type} {s : ℕ} (t : Fin s → σ) (Q : Set (σ →₀ ℕ)) :
    ∀ x ∈ restrictSupport ℚ_[p] Q, ProjS.eulL t x ∈ restrictSupport ℚ_[p] Q := by
  intro x hx
  rw [mem_restrictSupport_iff] at hx ⊢
  intro m hm
  apply hx
  rw [Finset.mem_coe, mem_support_iff] at hm ⊢
  rw [ProjS.coeff_eulL] at hm
  exact left_ne_zero_of_mul hm

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[resL_apply, resL_apply, coeff_initPart, ProjS.coeff_eulL, ProjS.coeff_eulL, coeff_initPart]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem resL_eulL {σ : Type} {s : ℕ} (t : Fin s → σ) (v : σ) (e : ℕ) (x : MvPolynomial σ ℚ_[p]) :
    resL p v e (ProjS.eulL t x) = ProjS.eulL t (resL p v e x) := by
  ext m
  rw [resL_apply, resL_apply, coeff_initPart, ProjS.coeff_eulL, ProjS.coeff_eulL, coeff_initPart]
  split_ifs <;> simp

/- English proof (translation)
Establish `e : setLast (setLast LL (o + 1)) ((setLast LL (o + 1)).deg (Fin.last K) - 1) = setLast LL o`. Simplify using `[setLast]`. Establish `h` using `(pol_pow (p := p) (setLast LL (o + 1)) a 1 (by simp [setLast]) G).mpr (by rw [e]; exact hG)`. Rewrite `h` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem X_mul_pol (LL : Letters (K + 1)) (a : Fin r) (o : ℕ) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hG : G ∈ Pol p r (setLast LL o)) : X (Fin.last K, a) * G ∈ Pol p r (setLast LL (o + 1)) := by
  have e : setLast (setLast LL (o + 1)) ((setLast LL (o + 1)).deg (Fin.last K) - 1) = setLast LL o := by
    simp [setLast]
  have h := (pol_pow (p := p) (setLast LL (o + 1)) a 1 (by simp [setLast]) G).mpr (by rw [e]; exact hG)
  rwa [pow_one] at h

/- English proof (translation)
Establish `hdisj : Disjoint {v : Fin N × Fin r | j ≤ (v.1 : ℕ)} {v : Fin N × Fin r | (v.1 : ℕ) < j}`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `v h1 h2`. Simplify using `only [Set.mem_ofPred_eq] at h1 h2`. Use linear arithmetic over natural numbers and integers.

Introduce `x hx`. Use `ycond_keep LL j Mt T (fun a b y => FockB.ops_apply_comm hdisj hT (glAct_mem LL j a b) y) (fun y hy => ops_keep_supp {v : Fin N × Fin r | j ≤ (v.1 : ℕ)} _ (fun m m' hmm hm => ?_) hT y hy) x hx` and prove the remaining obligations. Establish `: wt LL j 0 m = wt LL j 0 m'` using `wt_congr LL j 0 m m' (fun i hi => hmm (i, 0) (by simp only [Set.mem_ofPred_eq]; omega))`. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[← this]`.

Conclude with `hm`.
-/
theorem ops_ycond {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (T : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hT : T ∈ FockB.Ops {v : Fin N × Fin r | j ≤ (v.1 : ℕ)}) :
    ∀ x ∈ YCond p LL j Mt, T x ∈ YCond p LL j Mt := by
  have hdisj : Disjoint {v : Fin N × Fin r | j ≤ (v.1 : ℕ)} {v : Fin N × Fin r | (v.1 : ℕ) < j} := by
    rw [Set.disjoint_left]; rintro v h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2; omega
  intro x hx
  refine ycond_keep LL j Mt T
    (fun a b y => FockB.ops_apply_comm hdisj hT (glAct_mem LL j a b) y)
    (fun y hy => ops_keep_supp {v : Fin N × Fin r | j ≤ (v.1 : ℕ)} _ (fun m m' hmm hm => ?_) hT y hy) x hx
  have : wt LL j 0 m = wt LL j 0 m' :=
    wt_congr LL j 0 m m' (fun i hi => hmm (i, 0) (by simp only [Set.mem_ofPred_eq]; omega))
  simp only [Set.mem_ofPred_eq] at hm ⊢
  rw [← this]; exact hm

/- English proof (translation)
Use `congr 1`. Use extensionality with `m`. Simplify using `only [Set.mem_ofPred_eq, WithTop.coe_le_coe]`.
-/
theorem supp_coe {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (k : ℤ) :
    restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((k : ℤ) : WithTop ℤ)} =
      restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | wt LL j 0 m ≤ k} := by
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]

/- English proof (translation)
Rewrite using `[Uop_apply]`. Use `Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[X_mul_mem p]`. Use `restrictSupport_mono ℚ_[p] ?_ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hF) (eulL_keep_supp _ _ F hF))` and prove the remaining obligations. Introduce `m hm`.

Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[last_wt LL (K + 1) le_rfl hv]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[X_mul_mem p]`. Use `glAct_keep LL K a b _ _ ?_ ?_ F hF` and prove the remaining obligations.

Introduce `i hi hvi m hm hb`. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[last_wt LL (K + 1) le_rfl hv, (wt_shift LL (K + 1) a b 0 i (by omega) m).1 hvi hb]`. Use linear arithmetic over natural numbers and integers. Introduce `i hi hvi m hm hb`.

Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[last_wt LL (K + 1) le_rfl hv, (wt_shift LL (K + 1) a b 0 i (by omega) m).2 hvi hb]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Uop_supp [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c k : ℤ)
    (Cs : Finset (Fin r)) (a : Fin r) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hF : F ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ k}) :
    Uop p LL c Cs a F ∈ restrictSupport ℚ_[p]
      {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ k + (if a = 0 then 1 else 0)} := by
  rw [Uop_apply]
  refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun b _ => ?_)
  · rw [X_mul_mem p]
    refine restrictSupport_mono ℚ_[p] ?_ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hF) (eulL_keep_supp _ _ F hF))
    intro m hm
    simp only [Set.mem_ofPred_eq] at hm ⊢
    rw [last_wt LL (K + 1) le_rfl hv]
    omega
  · rw [X_mul_mem p]
    refine glAct_keep LL K a b _ _ ?_ ?_ F hF
    · intro i hi hvi m hm hb
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [last_wt LL (K + 1) le_rfl hv, (wt_shift LL (K + 1) a b 0 i (by omega) m).1 hvi hb]
      omega
    · intro i hi hvi m hm hb
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [last_wt LL (K + 1) le_rfl hv, (wt_shift LL (K + 1) a b 0 i (by omega) m).2 hvi hb]
      omega

/- English proof (translation)
Rewrite using `[Uop_apply]`. Establish `e : ∀ b, glAct p LL K 0 b G = glAct p LL (K + 1) 0 b G - X (Fin.last K, 0) * pderiv (Fin.last K, b) G`. Introduce `b`. Rewrite using `[glAct_succ LL hv]`. Normalize the expressions using the abelian group laws.

Simplify using `only [e, mul_sub, Finset.sum_sub_distrib]`. Establish `h1 : ∑ b, X (Fin.last K, b) * glAct p LL (K + 1) 0 b G = X (Fin.last K, 0) * (((c : ℤ) : ℚ_[p]) • G)`. Rewrite using `[Finset.sum_eq_single 0, h0]`. Introduce `b _ hb'`. Rewrite using `[hb b hb', mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `h2 : ∑ b, X (Fin.last K, b) * (X (Fin.last K, 0) * pderiv (Fin.last K, b) G) = X (Fin.last K, 0) * ProjS.eulL (fun c : Fin r => (Fin.last K, c)) G`. Rewrite using `[ProjS.eulL_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun b _ => by ring`.

Rewrite using `[h1, h2]`. Normalize the expressions using the abelian group laws.
-/
theorem Uop_top [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c : ℤ)
    (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (h0 : glAct p LL (K + 1) 0 0 G = ((c : ℤ) : ℚ_[p]) • G)
    (hb : ∀ b : Fin r, b ≠ 0 → glAct p LL (K + 1) 0 b G = 0) : Uop p LL c univ 0 G = 0 := by
  rw [Uop_apply]
  have e : ∀ b, glAct p LL K 0 b G =
      glAct p LL (K + 1) 0 b G - X (Fin.last K, 0) * pderiv (Fin.last K, b) G := by
    intro b; rw [glAct_succ LL hv]; abel
  simp only [e, mul_sub, Finset.sum_sub_distrib]
  have h1 : ∑ b, X (Fin.last K, b) * glAct p LL (K + 1) 0 b G = X (Fin.last K, 0) * (((c : ℤ) : ℚ_[p]) • G) := by
    rw [Finset.sum_eq_single 0, h0]
    · intro b _ hb'; rw [hb b hb', mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : ∑ b, X (Fin.last K, b) * (X (Fin.last K, 0) * pderiv (Fin.last K, b) G) =
      X (Fin.last K, 0) * ProjS.eulL (fun c : Fin r => (Fin.last K, c)) G := by
    rw [ProjS.eulL_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h1, h2]
  abel

end U

/- English proof (translation)
Introduce `p _ K r LL c Cs a s t F hv hs ht`. Establish `hlt : ((Fin.last K : Fin (K + 1)) : ℕ) < K + 1` using `(Fin.last K).isLt`. Establish `hX : ∀ (b : Fin r) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), glAct p LL (K + 1) s t (X (Fin.last K, b) * G) = (if t = b then X (Fin.last K, s) * G else 0) + X (Fin.last K, b) * glAct p LL (K + 1) s t G`. Introduce `b G`. Rewrite using `[glAct_mul, glAct_X, if_pos hlt, if_pos hv]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hc : ∀ b, glAct p LL (K + 1) s t (glAct p LL K a b F) = glAct p LL K a b (glAct p LL (K + 1) s t F) + ((if t = a then glAct p LL K s b F else 0) - (if b = s then glAct p LL K a t F else 0))`. Introduce `b`. Rewrite using `[← glAct_succ_comm]`. Normalize the expressions using the abelian group laws.

Rewrite using `[Uop_apply, Uop_apply, map_sub, map_sum, hX, map_sub, map_smul, eul_glAct]`. Simplify using `only [hX, hc, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Establish `h1 : ∑ b ∈ Cs, (if t = b then X (Fin.last K, s) * glAct p LL K a b F else 0) = X (Fin.last K, s) * glAct p LL K a t F`. Rewrite using `[Finset.sum_ite_eq, if_pos ht]`. Establish `h2 : ∑ b ∈ Cs, X (Fin.last K, b) * (if b = s then glAct p LL K a t F else 0) = X (Fin.last K, s) * glAct p LL K a t F`.

Simplify using `only [mul_ite, mul_zero]`. Rewrite using `[Finset.sum_ite_eq', if_pos hs]`. Rewrite using `[h1, h2]`. Use `split_ifs with hta`. Rewrite using `[Uop_apply]`.

Simplify using `only [mul_sub]`. Normalize the expressions using the abelian group laws. Simplify using `only [mul_zero, Finset.sum_const_zero]`. Normalize the expressions using the abelian group laws.
-/
theorem raising_comm_holds : UComm := by
  intro p _ K r LL c Cs a s t F hv hs ht
  classical
  have hlt : ((Fin.last K : Fin (K + 1)) : ℕ) < K + 1 := (Fin.last K).isLt
  have hX : ∀ (b : Fin r) (G : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      glAct p LL (K + 1) s t (X (Fin.last K, b) * G) =
        (if t = b then X (Fin.last K, s) * G else 0) + X (Fin.last K, b) * glAct p LL (K + 1) s t G := by
    intro b G
    rw [glAct_mul, glAct_X, if_pos hlt, if_pos hv]
    split_ifs <;> simp
  have hc : ∀ b, glAct p LL (K + 1) s t (glAct p LL K a b F) = glAct p LL K a b (glAct p LL (K + 1) s t F) +
      ((if t = a then glAct p LL K s b F else 0) - (if b = s then glAct p LL K a t F else 0)) := by
    intro b; rw [← glAct_succ_comm]; abel
  rw [Uop_apply, Uop_apply, map_sub, map_sum, hX, map_sub, map_smul, eul_glAct]
  simp only [hX, hc, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ b ∈ Cs, (if t = b then X (Fin.last K, s) * glAct p LL K a b F else 0) =
      X (Fin.last K, s) * glAct p LL K a t F := by
    rw [Finset.sum_ite_eq, if_pos ht]
  have h2 : ∑ b ∈ Cs, X (Fin.last K, b) * (if b = s then glAct p LL K a t F else 0) =
      X (Fin.last K, s) * glAct p LL K a t F := by
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', if_pos hs]
  rw [h1, h2]
  split_ifs with hta
  · rw [Uop_apply]
    simp only [mul_sub]
    abel
  · simp only [mul_zero, Finset.sum_const_zero]
    abel

/- English proof (translation)
Introduce `p _ K r LL c Cs a o F hF`. Rewrite using `[Uop_apply]`. Use `Submodule.sub_mem _ (X_mul_pol LL a o _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hF) ?_)) (Submodule.sum_mem _ fun b _ => X_mul_pol LL b o _ ?_)` and prove the remaining obligations. Rewrite using `[(pol_iff_eul _ F).mp hF (Fin.last K)]`. Conclude with `Submodule.smul_mem _ _ hF`.

Use `glAct_pol (setLast LL o) K a b F hF` as an intermediate fact. Rewrite `this` using `[glAct_setLast]`. Then use the resulting hypothesis.
-/
theorem raising_degree_holds : UDeg := by
  intro p _ K r LL c Cs a o F hF
  rw [Uop_apply]
  refine Submodule.sub_mem _ (X_mul_pol LL a o _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hF) ?_))
    (Submodule.sum_mem _ fun b _ => X_mul_pol LL b o _ ?_)
  · rw [(pol_iff_eul _ F).mp hF (Fin.last K)]
    exact Submodule.smul_mem _ _ hF
  · have := glAct_pol (setLast LL o) K a b F hF
    rwa [glAct_setLast] at this

/- English proof (translation)
Introduce `p _ K r LL c ρ a F ha`. Express the relevant statement in the definitionally equal form `resL p (Fin.last K, ρ) 0 _ = Uop p LL c (univ.erase ρ) a (resL p (Fin.last K, ρ) 0 F)`. Establish `hne : ∀ b : Fin r, b ≠ ρ → ((Fin.last K, b) : Fin (K + 1) × Fin r) ≠ (Fin.last K, ρ)` using `fun b hb h => hb (Prod.mk.inj h).2`. Rewrite using `[Uop_apply, Uop_apply, map_sub, map_sum, resL_X_mul _ _ (hne a ha), map_sub, map_smul, resL_eulL]`. Use `congr 1`.

Rewrite using `[← Finset.add_sum_erase univ _ (Finset.mem_univ ρ), resL_apply, initPart_zero_X_mul, zero_add]`. Use `Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Rewrite using `[resL_X_mul _ _ (hne b (Finset.mem_erase.mp hb).1), resL_glAct LL K a b (Fin.last K, ρ) 0 (fun i hi => ⟨fun h' => last_ne_of_lt i hi (Prod.mk.inj h').1.symm, fun h' => last_ne_of_lt i hi (Prod.mk.inj h').1.symm⟩)]`.
-/
theorem restriction_raising_holds : ResU := by
  intro p _ K r LL c ρ a F ha
  change resL p (Fin.last K, ρ) 0 _ = Uop p LL c (univ.erase ρ) a (resL p (Fin.last K, ρ) 0 F)
  have hne : ∀ b : Fin r, b ≠ ρ → ((Fin.last K, b) : Fin (K + 1) × Fin r) ≠ (Fin.last K, ρ) :=
    fun b hb h => hb (Prod.mk.inj h).2
  rw [Uop_apply, Uop_apply, map_sub, map_sum, resL_X_mul _ _ (hne a ha), map_sub, map_smul, resL_eulL]
  congr 1
  rw [← Finset.add_sum_erase univ _ (Finset.mem_univ ρ), resL_apply, initPart_zero_X_mul, zero_add]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [resL_X_mul _ _ (hne b (Finset.mem_erase.mp hb).1), resL_glAct LL K a b (Fin.last K, ρ) 0 (fun i hi =>
    ⟨fun h' => last_ne_of_lt i hi (Prod.mk.inj h').1.symm, fun h' => last_ne_of_lt i hi (Prod.mk.inj h').1.symm⟩)]

/- English proof (translation)
Introduce `p _ K r _ LL c Cs a j M hj F hF`. Establish `hl : ∀ b : Fin r, ((Fin.last K, b) : Fin (K + 1) × Fin r) ∈ {v : Fin (K + 1) × Fin r | j ≤ (v.1 : ℕ)}`. Introduce `b`. Simplify using `only [Set.mem_ofPred_eq, Fin.val_last]`. Conclude with `hj`.

Establish `hX : ∀ (b : Fin r), ∀ x ∈ YCond p LL j M, X (Fin.last K, b) * x ∈ YCond p LL j M` using `fun b => ops_ycond LL j M (LinearMap.mulLeft ℚ_[p] (X (Fin.last K, b))) (FockB.mulLeftX_mem (hl b))`. Establish `hD : ∀ (b : Fin r), ∀ x ∈ YCond p LL j M, pderiv (Fin.last K, b) x ∈ YCond p LL j M` using `fun b => ops_ycond LL j M (pderiv (Fin.last K, b)).toLinearMap (FockB.pderiv_mem (hl b))`. Rewrite using `[Uop_apply]`. Use `Submodule.sub_mem _ (hX a _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hF) ?_)) (Submodule.sum_mem _ fun b _ => hX b _ ?_)` and prove the remaining obligations. Rewrite using `[ProjS.eulL_apply]`.

Conclude with `Submodule.sum_mem _ fun b _ => hX b _ (hD b F hF)`. Rewrite using `[glAct_split LL j K a b, LinearMap.add_apply]`. Conclude with `Submodule.add_mem _ (ycond_glStable LL j M a b F hF) (ops_ycond LL j M (glRest p LL j K a b) (glRest_mem LL j K hj a b) F hF)`.
-/
theorem raising_keeps_early_letters : UKeepsEarly := by
  intro p _ K r _ LL c Cs a j M hj F hF
  have hl : ∀ b : Fin r, ((Fin.last K, b) : Fin (K + 1) × Fin r) ∈ {v : Fin (K + 1) × Fin r | j ≤ (v.1 : ℕ)} := by
    intro b
    simp only [Set.mem_ofPred_eq, Fin.val_last]; exact hj
  have hX : ∀ (b : Fin r), ∀ x ∈ YCond p LL j M, X (Fin.last K, b) * x ∈ YCond p LL j M := fun b =>
    ops_ycond LL j M (LinearMap.mulLeft ℚ_[p] (X (Fin.last K, b))) (FockB.mulLeftX_mem (hl b))
  have hD : ∀ (b : Fin r), ∀ x ∈ YCond p LL j M, pderiv (Fin.last K, b) x ∈ YCond p LL j M := fun b =>
    ops_ycond LL j M (pderiv (Fin.last K, b)).toLinearMap (FockB.pderiv_mem (hl b))
  rw [Uop_apply]
  refine Submodule.sub_mem _ (hX a _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hF) ?_))
    (Submodule.sum_mem _ fun b _ => hX b _ ?_)
  · rw [ProjS.eulL_apply]
    exact Submodule.sum_mem _ fun b _ => hX b _ (hD b F hF)
  · rw [glAct_split LL j K a b, LinearMap.add_apply]
    exact Submodule.add_mem _ (ycond_glStable LL j M a b F hF)
      (ops_ycond LL j M (glRest p LL j K a b) (glRest_mem LL j K hj a b) F hF)

/- English proof (translation)
Introduce `p _ K r _ LL c a hv`. Use `set Yc : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) := YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ) with hYc`. Establish `hYs : ∀ F ∈ Yc, F ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ c}`. Introduce `F hF`. Rewrite using `[← supp_coe]`.

Conclude with `ycond_le_supp LL (K + 1) _ hF`. Establish `hsupp : ∀ (a : Fin r), ∀ F ∈ Yc, Uop p LL c univ a F ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ c}`. Introduce `a F hF`. Distinguish the cases in `ha : a = 0`. Substitute `ha set G := compP (fun m => wt LL (K + 1) 0 m = c) F with hG` using the available equality.

Establish `hGY : G ∈ Yc` using `vdm (glAct p LL (K + 1) 0 0) (wt LL (K + 1) 0) (fun x m => coeff_cartan LL (K + 1) 0 x m) Yc (ycond_glStable LL (K + 1) _ 0 0) F hF c`. Establish `h0 : glAct p LL (K + 1) 0 0 G = ((c : ℤ) : ℚ_[p]) • G`. Use extensionality with `m`. Rewrite using `[coeff_cartan, coeff_smul, smul_eq_mul, hG, coeff_compP]`. Use `split_ifs with h`.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Establish `hb : ∀ b : Fin r, b ≠ 0 → glAct p LL (K + 1) 0 b G = 0`. Introduce `b hb`. Assume the negation of the conclusion as `hne`.

Take `⟨m, hm⟩` from `(MvPolynomial.ne_zero_iff.mp hne)`. Establish `hm' : m ∈ (glAct p LL (K + 1) 0 b G).support` using `mem_support_iff.mpr hm`. Establish `h1` using `hYs _ (ycond_glStable LL (K + 1) _ 0 b G hGY)`. Rewrite `h1` using `[mem_restrictSupport_iff]`. Establish `h2` using `h1 (Finset.mem_coe.mpr hm')`.

Establish `h3 : glAct p LL (K + 1) 0 0 (glAct p LL (K + 1) 0 b G) = (((c + 1 : ℤ)) : ℚ_[p]) • glAct p LL (K + 1) 0 b G`. Use `glAct_comm LL (K + 1) 0 0 0 b G` as an intermediate fact. Rewrite `this` using `[if_pos rfl, if_neg hb, sub_zero, h0, map_smul]`. Rewrite using `[sub_eq_iff_eq_add.mp this]`. Use `push_cast`.

Rewrite using `[add_smul, one_smul]`. Normalize the expressions using the abelian group laws. Establish `h4` using `eig_supp LL (K + 1) 0 (c + 1) _ h3`. Rewrite `h4` using `[mem_restrictSupport_iff]`. Establish `h5` using `h4 (Finset.mem_coe.mpr hm')`.

Simplify using `only [Set.mem_ofPred_eq] at h2 h5`. Use linear arithmetic over natural numbers and integers. Establish `hR : F - G ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ c - 1}`. Establish `hF'` using `hYs F hF`. Rewrite `hF'`, the goal using `[mem_restrictSupport_iff]`.

Introduce `m hm`. Rewrite `hm` using `[Finset.mem_coe, mem_support_iff, coeff_sub, hG, coeff_compP]`. Use `split_ifs at hm with h`. Conclude with `absurd (sub_self _) hm`. Rewrite `hm` using `[sub_zero]`.

Use `hF' (Finset.mem_coe.mpr (mem_support_iff.mpr hm))` as an intermediate fact. Simplify using `only [Set.mem_ofPred_eq] at this ⊢`. Use linear arithmetic over natural numbers and integers. Establish `e : Uop p LL c univ 0 F = Uop p LL c univ 0 (F - G)`. Rewrite using `[map_sub, Uop_top LL hv c G h0 hb, sub_zero]`.

Rewrite using `[e]`. Use `Uop_supp LL hv c (c - 1) univ 0 (F - G) hR` as an intermediate fact. Rewrite `this` using `[if_pos rfl, sub_add_cancel]`. Conclude with `this`. Use `Uop_supp LL hv c c univ a F (hYs F hF)` as an intermediate fact.

Rewrite `this` using `[if_neg ha, add_zero]`. Conclude with `this`. Use `set B : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) := ⨆ a : Fin r, Yc.map (Uop p LL c univ a) with hB`. Establish `hmem : ∀ (a : Fin r), ∀ x ∈ Yc, Uop p LL c univ a x ∈ B` using `fun a x hx => Submodule.mem_iSup_of_mem a (Submodule.mem_map_of_mem hx)`. Establish `hle : B ≤ Yc`.

Use `le_ycond LL (K + 1) _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[supp_coe]`. Conclude with `iSup_le fun a => Submodule.map_le_iff_le_comap.mpr fun x hx => hsupp a x hx`. Introduce `s t`. Establish `: B ≤ B.comap (glAct p LL (K + 1) s t)`.

Use `iSup_le fun a => ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hy`. Use `show glAct p LL (K + 1) s t (Uop p LL c univ a x) ∈ B`. Establish `e` using `raising_comm_holds p K r LL c univ a s t x hv (Finset.mem_univ _) (Finset.mem_univ _)`.

Rewrite using `[sub_eq_iff_eq_add.mp e]`. Use `Submodule.add_mem _ ?_ (hmem a _ (ycond_glStable LL (K + 1) _ s t x hx))` and prove the remaining obligations. Use `split_ifs`. Conclude with `hmem s x hx`. Conclude with `Submodule.zero_mem _`.

Conclude with `fun y hy => this hy`. Introduce `F hF`. Conclude with `hle (hmem a F hF)`.
-/
theorem raising_keeps_last_letter : UKeepsLast := by
  intro p _ K r _ LL c a hv
  set Yc : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ) with hYc
  have hYs : ∀ F ∈ Yc, F ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ c} := by
    intro F hF
    rw [← supp_coe]
    exact ycond_le_supp LL (K + 1) _ hF
  have hsupp : ∀ (a : Fin r), ∀ F ∈ Yc, Uop p LL c univ a F ∈
      restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ c} := by
    intro a F hF
    by_cases ha : a = 0
    · subst ha
      set G := compP (fun m => wt LL (K + 1) 0 m = c) F with hG
      have hGY : G ∈ Yc := vdm (glAct p LL (K + 1) 0 0) (wt LL (K + 1) 0) (fun x m => coeff_cartan LL (K + 1) 0 x m) Yc
        (ycond_glStable LL (K + 1) _ 0 0) F hF c
      have h0 : glAct p LL (K + 1) 0 0 G = ((c : ℤ) : ℚ_[p]) • G := by
        ext m
        rw [coeff_cartan, coeff_smul, smul_eq_mul, hG, coeff_compP]
        split_ifs with h
        · rw [h]
        · simp
      have hb : ∀ b : Fin r, b ≠ 0 → glAct p LL (K + 1) 0 b G = 0 := by
        intro b hb
        by_contra hne
        obtain ⟨m, hm⟩ := (MvPolynomial.ne_zero_iff.mp hne)
        have hm' : m ∈ (glAct p LL (K + 1) 0 b G).support := mem_support_iff.mpr hm
        have h1 := hYs _ (ycond_glStable LL (K + 1) _ 0 b G hGY)
        rw [mem_restrictSupport_iff] at h1
        have h2 := h1 (Finset.mem_coe.mpr hm')
        have h3 : glAct p LL (K + 1) 0 0 (glAct p LL (K + 1) 0 b G) =
            (((c + 1 : ℤ)) : ℚ_[p]) • glAct p LL (K + 1) 0 b G := by
          have := glAct_comm LL (K + 1) 0 0 0 b G
          rw [if_pos rfl, if_neg hb, sub_zero, h0, map_smul] at this
          rw [sub_eq_iff_eq_add.mp this]
          push_cast
          rw [add_smul, one_smul]
          abel
        have h4 := eig_supp LL (K + 1) 0 (c + 1) _ h3
        rw [mem_restrictSupport_iff] at h4
        have h5 := h4 (Finset.mem_coe.mpr hm')
        simp only [Set.mem_ofPred_eq] at h2 h5
        omega
      have hR : F - G ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | wt LL (K + 1) 0 m ≤ c - 1} := by
        have hF' := hYs F hF
        rw [mem_restrictSupport_iff] at hF' ⊢
        intro m hm
        rw [Finset.mem_coe, mem_support_iff, coeff_sub, hG, coeff_compP] at hm
        split_ifs at hm with h
        · exact absurd (sub_self _) hm
        · rw [sub_zero] at hm
          have := hF' (Finset.mem_coe.mpr (mem_support_iff.mpr hm))
          simp only [Set.mem_ofPred_eq] at this ⊢
          omega
      have e : Uop p LL c univ 0 F = Uop p LL c univ 0 (F - G) := by
        rw [map_sub, Uop_top LL hv c G h0 hb, sub_zero]
      rw [e]
      have := Uop_supp LL hv c (c - 1) univ 0 (F - G) hR
      rw [if_pos rfl, sub_add_cancel] at this
      exact this
    · have := Uop_supp LL hv c c univ a F (hYs F hF)
      rw [if_neg ha, add_zero] at this
      exact this
  set B : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    ⨆ a : Fin r, Yc.map (Uop p LL c univ a) with hB
  have hmem : ∀ (a : Fin r), ∀ x ∈ Yc, Uop p LL c univ a x ∈ B := fun a x hx =>
    Submodule.mem_iSup_of_mem a (Submodule.mem_map_of_mem hx)
  have hle : B ≤ Yc := by
    refine le_ycond LL (K + 1) _ _ ?_ ?_
    · rw [supp_coe]
      exact iSup_le fun a => Submodule.map_le_iff_le_comap.mpr fun x hx => hsupp a x hx
    · intro s t
      have : B ≤ B.comap (glAct p LL (K + 1) s t) := by
        refine iSup_le fun a => ?_
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
        show glAct p LL (K + 1) s t (Uop p LL c univ a x) ∈ B
        have e := raising_comm_holds p K r LL c univ a s t x hv (Finset.mem_univ _) (Finset.mem_univ _)
        rw [sub_eq_iff_eq_add.mp e]
        refine Submodule.add_mem _ ?_ (hmem a _ (ycond_glStable LL (K + 1) _ s t x hx))
        split_ifs
        · exact hmem s x hx
        · exact Submodule.zero_mem _
      exact fun y hy => this hy
  intro F hF
  exact hle (hmem a F hF)

end Formalism.InvariantFactorPaths.L4
