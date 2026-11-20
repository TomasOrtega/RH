import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaDegreeMapDomain

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

/- English proof (translation)
Establish `hc : ∀ n, MvPolynomial.coeff n ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P) = (q : MvPolynomial τ ℤ) ^ E * MvPolynomial.coeff n P`. Introduce `n`. Establish `: (q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E = MvPolynomial.C ((q : MvPolynomial τ ℤ) ^ E)`. Rewrite using `[map_pow, map_natCast]`. Rewrite using `[this, MvPolynomial.coeff_C_mul]`.

Establish `hsub : ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P).support ⊆ P.support`. Introduce `n hn`. Rewrite `hn` using `[MvPolynomial.mem_support_iff, hc]`. Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h0`.

Rewrite `hn` using `[h0, mul_zero]`. Conclude with `hn rfl`. Unfold `applyD`. Rewrite using `[Finset.sum_subset hsub (fun n _ hn => by`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hn, map_zero, smul_zero]), Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[hc, map_mul, map_pow, map_natCast, smul_comm]`. Use `congr 1`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_pow, map_natCast]`.
-/
theorem ea_applyD_scale {σ τ K : Type} [Field K] (q E : ℕ) (P : MvPolynomial σ (MvPolynomial τ ℤ))
    (f : MvPowerSeries σ K) :
    applyD ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P) f = ((q : K) ^ E) • applyD P f := by
  classical
  have hc : ∀ n, MvPolynomial.coeff n ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P) =
      (q : MvPolynomial τ ℤ) ^ E * MvPolynomial.coeff n P := by
    intro n
    have : (q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E = MvPolynomial.C ((q : MvPolynomial τ ℤ) ^ E) := by
      rw [map_pow, map_natCast]
    rw [this, MvPolynomial.coeff_C_mul]
  have hsub : ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P).support ⊆ P.support := by
    intro n hn
    rw [MvPolynomial.mem_support_iff, hc] at hn
    rw [MvPolynomial.mem_support_iff]
    intro h0
    rw [h0, mul_zero] at hn
    exact hn rfl
  unfold applyD
  rw [Finset.sum_subset hsub (fun n _ hn => by
    rw [MvPolynomial.notMem_support_iff.1 hn, map_zero, smul_zero]), Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hc, map_mul, map_pow, map_natCast, smul_comm]
  congr 1
  rw [MvPolynomial.smul_eq_C_mul, map_pow, map_natCast]

/- English proof (translation)
Unfold `applyD`. Rewrite using `[MvPolynomial.support_zero, Finset.sum_empty]`.
-/
theorem ea_applyD_zero {σ τ K : Type} [Field K] (f : MvPowerSeries σ K) :
    applyD (0 : MvPolynomial σ (MvPolynomial τ ℤ)) f = 0 := by
  unfold applyD
  rw [MvPolynomial.support_zero, Finset.sum_empty]

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

/- English proof (translation)
Unfold `PIvS Sys.PIv`. Simplify using `only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`.
-/
theorem ea_PIvS_eq (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    PIvS X j I i0 v = (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^
      (∑ s : Fin (X.G.P.n' v), ∑ c ∈ range (X.nuv v (j + 1) s 1).toNat, X.colExp j I i0 v s c) * X.PIv j I v := by
  unfold PIvS Sys.PIv
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/- English proof (translation)
Unfold `Function.Injective at h`. Use `push Not at h`. Take `⟨x, y, hxy, hne⟩` from `h`. Unfold `Sys.colFac`. Use `Matrix.det_zero_of_column_eq hne fun k => ?_` and prove the remaining obligations.

Use `show (∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c x.val)⟩ : X.ZA j)) = ∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c y.val)⟩ : X.ZA j)`. Establish `hxy' : I v s c x.val = I v s c y.val` using `hxy`. Rewrite using `[hxy']`.
-/
theorem ea_colFac_zero (j : ℕ) (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ)
    (h : ¬ Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val) : X.colFac j I v s c = 0 := by
  unfold Function.Injective at h
  push Not at h
  obtain ⟨x, y, hxy, hne⟩ := h
  unfold Sys.colFac
  refine Matrix.det_zero_of_column_eq hne fun k => ?_
  show (∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c x.val)⟩ : X.ZA j)) =
    ∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c y.val)⟩ : X.ZA j)
  have hxy' : I v s c x.val = I v s c y.val := hxy
  rw [hxy']

/- English proof (translation)
Rewrite using `[← Finset.card_image_of_injective _ hg]`. Use `congr 1`. Use extensionality with `b`. Simplify using `only [mem_inter, mem_image, mem_filter, mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨x, rfl⟩, hb⟩`. Conclude with `⟨x, hb, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨⟨x, rfl⟩, hx⟩`.
-/
theorem ea_card_img {H N : ℕ} (g : Fin H → Fin N) (hg : Function.Injective g) (i : ℕ) :
    ((univ.image g) ∩ univ.filter (fun b : Fin N => b.val < i)).card =
      (univ.filter fun x : Fin H => (g x).val < i).card := by
  rw [← Finset.card_image_of_injective _ hg]
  congr 1
  ext b
  simp only [mem_inter, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨x, rfl⟩, hb⟩
    exact ⟨x, hb, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩

/- English proof (translation)
Unfold `ea_Exp`. Use `(Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm` and prove the remaining obligations. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `e1` using `ea_card_img (ea_Ic X v j I s' c) (h ((ea_e X v).symm s') c.val) i`.

Establish `e2` using `ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val) (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)`. Establish `e3 : ((univ.image (ea_Ic X v j I s' c)) ∩ univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card = ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card` using `e1.trans e2`. Rewrite using `[e3]`. Unfold `Sys.colExp`. Establish `hv : ((ea_e X v).symm s').val = s'.val` using `rfl`.

Distinguish the cases in `hodd : s'.val % 2 = 0`. Rewrite using `[if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]`. Both sides reduce to the same expression. Rewrite using `[if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]`.
-/
theorem ea_Exp_eq (v : X.Pl) (j i : ℕ) (I : X.ColCh j)
    (h : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val) :
    ∑ s : Fin (X.G.P.n' v), ∑ c ∈ range (X.nuv v (j + 1) s 1).toNat, X.colExp j I (fun _ => i) v s c =
      ea_Exp X v j i I := by
  unfold ea_Exp
  refine (Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm
  rw [← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 := ea_card_img (ea_Ic X v j I s' c) (h ((ea_e X v).symm s') c.val) i
  have e2 := ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)
    (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)
  have e3 : ((univ.image (ea_Ic X v j I s' c)) ∩
      univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card =
      ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter
        fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card := e1.trans e2
  rw [e3]
  unfold Sys.colExp
  have hv : ((ea_e X v).symm s').val = s'.val := rfl
  by_cases hodd : s'.val % 2 = 0
  · rw [if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]
    rfl
  · rw [if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]

/- English proof (translation)
Introduce `v j i K' _ F I n`. Distinguish the cases in `h : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), c ∈ range (X.nuv v (j + 1) s 1).toNat → X.colFac j I v s c ≠ 0`. Distinguish the cases in `h2 : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val`. Use `right`. Rewrite using `[ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul, ea_Exp_eq X v j i I h2]`.

Use `right`. Rewrite using `[ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul]`. Use `congr 2`. Unfold `ea_Exp`. Use `(Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm` and prove the remaining obligations.

Rewrite using `[← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `hinj : Function.Injective fun i' : Fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val) => I v ((ea_e X v).symm s') c.val i'.val`. Assume the negation of the conclusion as `hni`. Conclude with `h _ c.val (mem_range.2 c.isLt) (ea_colFac_zero X j I v _ _ hni)`.

Establish `e1` using `ea_card_img (ea_Ic X v j I s' c) hinj i`. Establish `e2` using `ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val) (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)`. Establish `e3 : ((univ.image (ea_Ic X v j I s' c)) ∩ univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card = ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card` using `e1.trans e2`. Rewrite using `[e3]`. Unfold `Sys.colExp`.

Establish `hv : ((ea_e X v).symm s').val = s'.val` using `rfl`. Distinguish the cases in `hodd : s'.val % 2 = 0`. Rewrite using `[if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]`. Both sides reduce to the same expression. Rewrite using `[if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]`.

Use `left push Not at h`. Take `⟨s, c, hc, h0⟩` from `h`. Establish `hz : PIvS X j I (fun _ => i) v = 0`. Unfold `PIvS`. Use `Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero hc ?_)` and prove the remaining obligations.

Rewrite using `[h0, mul_zero]`. Rewrite using `[hz, ea_applyD_zero, MvPolynomial.coeff_zero]`.
-/
theorem ea_brScale : ea_BrScale X := by
  intro v j i K' _ F I n
  by_cases h : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), c ∈ range (X.nuv v (j + 1) s 1).toNat →
      X.colFac j I v s c ≠ 0
  · by_cases h2 : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ),
        Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val
    · right
      rw [ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul, ea_Exp_eq X v j i I h2]
    ·
      right
      rw [ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul]
      congr 2
      unfold ea_Exp
      refine (Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm
      rw [← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hinj : Function.Injective fun i' : Fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val) =>
          I v ((ea_e X v).symm s') c.val i'.val := by
        by_contra hni
        exact h _ c.val (mem_range.2 c.isLt) (ea_colFac_zero X j I v _ _ hni)
      have e1 := ea_card_img (ea_Ic X v j I s' c) hinj i
      have e2 := ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)
        (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)
      have e3 : ((univ.image (ea_Ic X v j I s' c)) ∩
          univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card =
          ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter
            fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card := e1.trans e2
      rw [e3]
      unfold Sys.colExp
      have hv : ((ea_e X v).symm s').val = s'.val := rfl
      by_cases hodd : s'.val % 2 = 0
      · rw [if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]
        rfl
      · rw [if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]
  · left
    push Not at h
    obtain ⟨s, c, hc, h0⟩ := h
    have hz : PIvS X j I (fun _ => i) v = 0 := by
      unfold PIvS
      refine Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero hc ?_)
      rw [h0, mul_zero]
    rw [hz, ea_applyD_zero, MvPolynomial.coeff_zero]

end Formalism.MainNotions.FormalGroupSystem.Pf
