import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.OwnerNoneIff

namespace ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Col
variable {dim : (E →+* ℂ) → ℕ}

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem iteratedDeriv_cast (s : (Fin 1 → Vsp dim) → ℂ) {N M : ℕ} (h : N = M) (v : Fin N → Vsp dim) :
    d1 s N v = d1 s M (fun k => v (k.cast h.symm)) := by
  subst h
  rfl

/- English proof (translation)
Establish `hlen : l.length = c`. Use `congrArg Multiset.card hl` as an intermediate fact. Simplify using `using this`. Substitute `hlen` using the available equality. Establish `hmem : ∀ j : Fin l.length, InPart σ (l.get j) ∧ ‖l.get j‖ = 1`.

Introduce `j`. Establish `: l.get j ∈ Multiset.map g Finset.univ.val`. Rewrite using `[← hl]`. Conclude with `Multiset.mem_coe.2 (List.get_mem l j)`. Take `⟨r, -, hr⟩` from `Multiset.mem_map.1 this`.

Rewrite using `[← hr]`. Conclude with `hg r`. Establish `hm : Finset.univ.val.map (fun j : Fin l.length => l.get j) = (l : Multiset (Vsp dim))`. Rewrite using `[Fin.univ_val_map]`. Use `congr 1`.

Use `first`. Consider the case `exact List.ofFn_get l`. Consider the case `exact List.ofFn_getElem l`. Consider the case `simp`. Establish `hprod : ∏ j : Fin l.length, Hf (l.get j) y = ∏ r, Hf (g r) y`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Multiset.map_map]`. Both sides reduce to the same expression. Use `_ = ∏ r, Hf (g r) y := by`. Rewrite using `[hm, hl, Multiset.map_map]`.

Both sides reduce to the same expression. Use `hbd (fun j => l.get j) hmem` as an intermediate fact. Rewrite `this` using `[hprod]`. Conclude with `this`.
-/
theorem iteratedDeriv_list_bound (s : (Fin 1 → Vsp dim) → ℂ) (c : ℕ) (μ : ℂ) (y : Vsp dim) (ε : ℝ)
    (σ : E →+* ℂ)
    (hbd : ∀ xs : Fin c → Vsp dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
      ‖d1 s c xs - μ * ∏ k, Hf (xs k) y‖ ≤ ε)
    (l : List (Vsp dim)) (g : Fin c → Vsp dim)
    (hl : (l : Multiset (Vsp dim)) = Multiset.map g Finset.univ.val)
    (hg : ∀ r, InPart σ (g r) ∧ ‖g r‖ = 1) :
    ‖d1 s l.length (fun j => l.get j) - μ * ∏ r, Hf (g r) y‖ ≤ ε := by
  have hlen : l.length = c := by
    have := congrArg Multiset.card hl
    simpa using this
  subst hlen
  have hmem : ∀ j : Fin l.length, InPart σ (l.get j) ∧ ‖l.get j‖ = 1 := by
    intro j
    have : l.get j ∈ Multiset.map g Finset.univ.val := by
      rw [← hl]; exact Multiset.mem_coe.2 (List.get_mem l j)
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.1 this
    rw [← hr]; exact hg r
  have hm : Finset.univ.val.map (fun j : Fin l.length => l.get j) = (l : Multiset (Vsp dim)) := by
    rw [Fin.univ_val_map]
    congr 1
    first
    | exact List.ofFn_get l
    | exact List.ofFn_getElem l
    | simp
  have hprod : ∏ j : Fin l.length, Hf (l.get j) y = ∏ r, Hf (g r) y := by
    calc ∏ j : Fin l.length, Hf (l.get j) y
        = ((Finset.univ.val.map (fun j : Fin l.length => l.get j)).map (fun x => Hf x y)).prod := by
          rw [Multiset.map_map]; rfl
      _ = ∏ r, Hf (g r) y := by
          rw [hm, hl, Multiset.map_map]; rfl
  have := hbd (fun j => l.get j) hmem
  rw [hprod] at this
  exact this

/- English proof (translation)
Unfold `d1`. Conclude with `iteratedFDeriv_zero_apply _`.
-/
theorem d1_zero (s : (Fin 1 → Vsp dim) → ℂ) (v : Fin 0 → Vsp dim) : d1 s 0 v = s 0 := by
  unfold d1
  exact iteratedFDeriv_zero_apply _

end Col

section Main
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

open Classical in

def eU (j : Fin nb) (a : Fin (bs j).i) : Vsp dim :=
  EuclideanSpace.single (⟨(bs j).τ, Fin.castLE (bs j).hi a⟩ : Idx dim) (1 : ℂ)

def idealA (μ : (Σ j : Fin nb, Fin (bs j).i) → ℂ) (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim)
    (ee : Fin n → ℂ) (T : Choice bs) (k : Fin n) : ℂ :=
  match owner bs k with
  | some p => μ p * ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)
  | none => ee k

def blockM (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim) (j : Fin nb) :
    Matrix (Fin (bs j).i) (Fin (bs j).i) ℂ :=
  Matrix.of fun a b => Hf (eU bs j a) (y ⟨j, b⟩)

/- English proof (translation)
Establish `hinj : Function.Injective (colB bs)`. Introduce and unpack `⟨j, a⟩ ⟨j', a'⟩ h`. Simplify using `only [colB] at h`. Distinguish the cases in `hj : j = j'`. Substitute `hj` using the available equality.

Use `(bs j).col_inj h` as an intermediate fact. Substitute `this` using the available equality. Both sides reduce to the same expression. Conclude with `absurd h (hD j j' hj a a')`. Establish `hown : ∀ p, owner bs (colB bs p) = some p`.

Introduce `p`. Establish `hex : ∃ p', colB bs p' = colB bs p` using `⟨p, rfl⟩`. Unfold `owner`. Rewrite using `[dif_pos hex]`. Conclude with `congrArg some (hinj hex.choose_spec)`.

Establish `hnone : ∀ k, owner bs k = none ↔ k ∉ Finset.univ.image (colB bs)`. Introduce `k`. Prove the components needed by the constructor for the conclusion. Introduce `h hk`. Take `⟨p, -, rfl⟩` from `Finset.mem_image.mp hk`.

Rewrite `h` using `[hown]`. Conclude with `Option.some_ne_none _ h`. Introduce `h`. Unfold `owner`. Rewrite using `[dif_neg]`.

Introduce and unpack `⟨p, rfl⟩`. Conclude with `h (Finset.mem_image_of_mem _ (Finset.mem_univ p))`. Establish `hT : ∀ T : Choice bs, ∏ k, idealA bs μ y ee T k = (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * ∏ p, (μ p * ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p))`. Introduce `T`. Rewrite using `[← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => owner bs k = none)]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `h` using `(Finset.mem_filter.mp hk).2`. Simplify using `only [idealA, h]`. Establish `hset : Finset.univ.filter (fun k => ¬ owner bs k = none) = Finset.univ.image (colB bs)`.

Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[hnone]`. Conclude with `not_not`. Rewrite using `[hset, Finset.prod_image (fun p _ q _ h => hinj h)]`.

Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `only [idealA, hown]`. Establish `hdet : ∀ j, (blockM bs y j).det ^ (bs j).c = ∏ r : Fin (bs j).c, ∑ σ : Equiv.Perm (Fin (bs j).i), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ b, Hf (eU bs j (σ b)) (y ⟨j, b⟩)`. Introduce `j`. Rewrite using `[Fin.prod_const, Matrix.det_apply]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, zsmul_eq_mul]`. Both sides reduce to the same expression. Establish `hsum : ∑ T : Choice bs, sgnT bs T * ∏ p, ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p) = ∏ j, (blockM bs y j).det ^ (bs j).c`.

Repeatedly rewrite using `[hdet]`. Use `first`. Consider the case `simp_rw [Fintype.prod_sum]`. Consider the case `simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `Finset.sum_congr rfl fun T _ => ?_` and prove the remaining obligations.

Simplify using `only [Finset.prod_mul_distrib, sgnT]`. Use `congr 1`. Use `first`. Consider the case `rw [Fintype.prod_sigma]`. Consider the case `rw [← Finset.univ_sigma_univ, Finset.prod_sigma]`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `first`. Consider the case `rw [Finset.prod_comm]`. Consider the case `exact Finset.prod_comm.symm`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun T _ => ?_` and prove the remaining obligations. Rewrite using `[hT, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [← Finset.mul_sum, hsum]`.
-/
theorem main_term (hD : Disj bs) (μ : (Σ j : Fin nb, Fin (bs j).i) → ℂ)
    (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim) (ee : Fin n → ℂ) :
    ∑ T : Choice bs, sgnT bs T * ∏ k, idealA bs μ y ee T k =
      (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * (∏ p, μ p) *
        ∏ j, (blockM bs y j).det ^ (bs j).c := by
  have hinj : Function.Injective (colB bs) := by
    rintro ⟨j, a⟩ ⟨j', a'⟩ h
    simp only [colB] at h
    by_cases hj : j = j'
    · subst hj
      have := (bs j).col_inj h
      subst this
      rfl
    · exact absurd h (hD j j' hj a a')
  have hown : ∀ p, owner bs (colB bs p) = some p := by
    intro p
    have hex : ∃ p', colB bs p' = colB bs p := ⟨p, rfl⟩
    unfold owner
    rw [dif_pos hex]
    exact congrArg some (hinj hex.choose_spec)
  have hnone : ∀ k, owner bs k = none ↔ k ∉ Finset.univ.image (colB bs) := by
    intro k
    constructor
    · intro h hk
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hk
      rw [hown] at h
      exact Option.some_ne_none _ h
    · intro h
      unfold owner
      rw [dif_neg]
      rintro ⟨p, rfl⟩
      exact h (Finset.mem_image_of_mem _ (Finset.mem_univ p))
  have hT : ∀ T : Choice bs, ∏ k, idealA bs μ y ee T k =
      (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) *
        ∏ p, (μ p * ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)) := by
    intro T
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => owner bs k = none)]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      have h := (Finset.mem_filter.mp hk).2
      simp only [idealA, h]
    · have hset : Finset.univ.filter (fun k => ¬ owner bs k = none) = Finset.univ.image (colB bs) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hnone]
        exact not_not
      rw [hset, Finset.prod_image (fun p _ q _ h => hinj h)]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [idealA, hown]
  have hdet : ∀ j, (blockM bs y j).det ^ (bs j).c =
      ∏ r : Fin (bs j).c, ∑ σ : Equiv.Perm (Fin (bs j).i),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ b, Hf (eU bs j (σ b)) (y ⟨j, b⟩) := by
    intro j
    rw [Fin.prod_const, Matrix.det_apply]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  have hsum : ∑ T : Choice bs, sgnT bs T * ∏ p, ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p) =
      ∏ j, (blockM bs y j).det ^ (bs j).c := by
    simp_rw [hdet]
    first
    | simp_rw [Fintype.prod_sum]
    | simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [Finset.prod_mul_distrib, sgnT]
    congr 1
    first
    | rw [Fintype.prod_sigma]
    | rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    first
    | rw [Finset.prod_comm]
    | exact Finset.prod_comm.symm
  calc ∑ T, sgnT bs T * ∏ k, idealA bs μ y ee T k
      = ∑ T : Choice bs, ((∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * ∏ p, μ p) *
          (sgnT bs T * ∏ p, ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [hT, Finset.prod_mul_distrib]
        ring
    _ = _ := by rw [← Finset.mul_sum, hsum]

end Main

end

end ReciprocityTheory.ChartRestriction.G.I2
