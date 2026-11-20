import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConnectionSecondOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val

open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

/- English proof (translation)
Use `first`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha`. Consider the case `exact ⟨fun s => by simp [ha s], fun d => Set.toFinite _⟩`.
-/
private theorem hasSubst_lemma {σ τ k : Type} [CommRing k] [Finite σ] {a : σ → MvPowerSeries τ k}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact ⟨fun s => by simp [ha s], fun d => Set.toFinite _⟩

/- English proof (translation)
Establish `e : ∀ (ρ : Type), (C c : MvPowerSeries ρ k) = c • (1 : MvPowerSeries ρ k)` using `fun ρ => by first`. Consider the case `rw [MvPowerSeries.smul_eq_C_mul, mul_one]`. Consider the case `simp [MvPowerSeries.smul_eq_C_mul]`. Rewrite using `[e σ, e τ, ← coe_substAlgHom hs, map_smul, map_one]`.
-/
private theorem mvPowerSeries_subst_C {σ τ k : Type} [CommRing k] {a : σ → MvPowerSeries τ k} (hs : HasSubst a) (c : k) :
    subst a (C c : MvPowerSeries σ k) = (C c : MvPowerSeries τ k) := by
  have e : ∀ (ρ : Type), (C c : MvPowerSeries ρ k) = c • (1 : MvPowerSeries ρ k) := fun ρ => by
    first
    | rw [MvPowerSeries.smul_eq_C_mul, mul_one]
    | simp [MvPowerSeries.smul_eq_C_mul]
  rw [e σ, e τ, ← coe_substAlgHom hs, map_smul, map_one]

/- English proof (translation)
Establish `hs : HasSubst a` using `hasSubst_lemma ha`. Establish `h0 : constantCoeff (G - C (constantCoeff G)) = 0` using `by simp`. Establish `h1 : constantCoeff (subst a (G - C (constantCoeff G))) = 0` using `by first`. Consider the case `exact constantCoeff_subst_eq_zero hs _ h0`. Consider the case `exact constantCoeff_subst_eq_zero hs h0`.

Consider the case `(apply constantCoeff_subst_eq_zero <;> assumption)`. Establish `e : subst a (G - C (constantCoeff G)) = subst a G - C (constantCoeff G)`. Rewrite using `[← coe_substAlgHom hs, map_sub, coe_substAlgHom hs, mvPowerSeries_subst_C hs]`. Rewrite `h1` using `[e, map_sub, constantCoeff_C, sub_eq_zero]`. Conclude with `h1`.
-/
theorem const_subst {σ τ k : Type} [CommRing k] [Finite σ] {a : σ → MvPowerSeries τ k}
    (ha : ∀ s, constantCoeff (a s) = 0) (G : MvPowerSeries σ k) : constantCoeff (subst a G) = constantCoeff G := by
  have hs : HasSubst a := hasSubst_lemma ha
  have h0 : constantCoeff (G - C (constantCoeff G)) = 0 := by simp
  have h1 : constantCoeff (subst a (G - C (constantCoeff G))) = 0 := by
    first
    | exact constantCoeff_subst_eq_zero hs _ h0
    | exact constantCoeff_subst_eq_zero hs h0
    | (apply constantCoeff_subst_eq_zero <;> assumption)
  have e : subst a (G - C (constantCoeff G)) = subst a G - C (constantCoeff G) := by
    rw [← coe_substAlgHom hs, map_sub, coe_substAlgHom hs, mvPowerSeries_subst_C hs]
  rw [e, map_sub, constantCoeff_C, sub_eq_zero] at h1
  exact h1

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

def bE (h : PS k 2 d) : Fin d ⊕ Fin d → PS k 1 d := Sum.elim (fun j => X ((0 : Fin 1), j)) (fun i => sgOf k h i)

/- English proof (translation)
Unfold `sgOf`. Rewrite using `[map_neg, ← coeff_zero_eq_constantCoeff_apply, coeff_ev_zero_right, Finsupp.embDomain_zero, coeff_pderiv]`. Rewrite using `[coeff_eq_zero_of_vanish_first_axis h hax _ (fun i' => by simp [Finsupp.single_apply])]`. Simplify using the standard rewrite rules.
-/
theorem sg_const (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (i : Fin d) :
    constantCoeff (sgOf k h i) = 0 := by
  unfold sgOf
  rw [map_neg, ← coeff_zero_eq_constantCoeff_apply, coeff_ev_zero_right, Finsupp.embDomain_zero, coeff_pderiv]
  rw [coeff_eq_zero_of_vanish_first_axis h hax _ (fun i' => by simp [Finsupp.single_apply])]
  simp

/- English proof (translation)
Introduce `t`. Break down `t with j | i` into its components or cases. Use `show constantCoeff (X ((0 : Fin 1), j) : PS k 1 d) = 0`. Simplify using the standard rewrite rules. Conclude with `sg_const k h hax i`.
-/
theorem bE_const (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) : ∀ t, constantCoeff (bE k h t) = 0 := by
  intro t
  rcases t with j | i
  · show constantCoeff (X ((0 : Fin 1), j) : PS k 1 d) = 0
    simp
  · exact sg_const k h hax i

/- English proof (translation)
Establish `hb : HasSubst (bE k h)` using `hasSubst_lemma (bE_const k h hax)`. Establish `hl : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d))` using `hasSubst_lemma (fun p => by simp)`. Unfold `liftX`. Use `first`. Consider the case `rw [subst_comp_subst_apply hl hb]`.

Consider the case `rw [subst_comp_subst_apply hb hl]`. Establish `e : (fun p : Fin 1 × Fin d => subst (bE k h) (X (Sum.inl p.2) : AA k d)) = (X : Fin 1 × Fin d → PS k 1 d)`. Use function extensionality and compare the values at `p`. Rewrite using `[subst_X hb]`. Break down `p with ⟨q, j⟩` into its components or cases.

Establish `hq : q = 0` using `Subsingleton.elim _ _`. Substitute `hq` using the available equality. Both sides reduce to the same expression. Rewrite using `[e]`. Use `first`.

Consider the case `(rw [subst_self]; rfl)`. Consider the case `exact congrFun subst_self f`. Consider the case `simp [subst_self]`. Consider the case `(rw [← map_algebraMap_eq_subst_X]; simp)`.
-/
theorem E_liftX (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (f : PS k 1 d) :
    subst (bE k h) (liftX k f) = f := by
  have hb : HasSubst (bE k h) := hasSubst_lemma (bE_const k h hax)
  have hl : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) := hasSubst_lemma (fun p => by simp)
  unfold liftX
  first
  | rw [subst_comp_subst_apply hl hb]
  | rw [subst_comp_subst_apply hb hl]
  have e : (fun p : Fin 1 × Fin d => subst (bE k h) (X (Sum.inl p.2) : AA k d)) =
      (X : Fin 1 × Fin d → PS k 1 d) := by
    funext p
    rw [subst_X hb]
    rcases p with ⟨q, j⟩
    have hq : q = 0 := Subsingleton.elim _ _
    subst hq
    rfl
  rw [e]
  first
  | (rw [subst_self]; rfl)
  | exact congrFun subst_self f
  | simp [subst_self]
  | (rw [← map_algebraMap_eq_subst_X]; simp)

section Inter

variable {k}

/- English proof (translation)
Establish `hc` using `bE_const k h hax`. Establish `hb : HasSubst (bE k h)` using `hasSubst_of_constantCoeff_zero hc`. Establish `hfm : subst (bE k h) (fm k h u) = 0`. Unfold `fm`. Rewrite using `[← coe_substAlgHom hb, map_sum]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_sub, coe_substAlgHom hb, subst_X hb, E_liftX k h hax]`. Simplify using `[bE]`. Establish `hE : ∀ t, subst (bE k h) (cf k B h u 0 t) = Dof (B.FK k) u (bE k h t)`. Introduce and unpack `(j | i)`.

Rewrite using `[cf_inl, E_liftX k h hax]`. Conclude with `(Dof_X k (B.FK k) u j).symm`. Rewrite using `[cf_inr, Pi.zero_apply, map_zero, add_zero, E_liftX k h hax]`. Both sides reduce to the same expression. Rewrite using `[nabla_eq, vf, ← coe_substAlgHom hb, map_sub, map_sum]`.

Simplify using `only [map_mul, coe_substAlgHom hb, hfm, hE, mul_zero, zero_mul, sub_zero]`. Unfold `Dof`. Simplify using `only [LogPf.pderiv_subst hc, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem E_nabla (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) (u : Fin d → k)
    (G : AA k d) : subst (bE k h) (nabla k B h m u 0 G) = Dof (B.FK k) u (subst (bE k h) G) := by
  have hc := bE_const k h hax
  have hb : HasSubst (bE k h) := hasSubst_of_constantCoeff_zero hc
  have hfm : subst (bE k h) (fm k h u) = 0 := by
    unfold fm
    rw [← coe_substAlgHom hb, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, map_sub, coe_substAlgHom hb, subst_X hb, E_liftX k h hax]
    simp [bE]
  have hE : ∀ t, subst (bE k h) (cf k B h u 0 t) = Dof (B.FK k) u (bE k h t) := by
    rintro (j | i)
    · rw [cf_inl, E_liftX k h hax]
      exact (Dof_X k (B.FK k) u j).symm
    · rw [cf_inr, Pi.zero_apply, map_zero, add_zero, E_liftX k h hax]
      rfl
  rw [nabla_eq, vf, ← coe_substAlgHom hb, map_sub, map_sum]
  simp only [map_mul, coe_substAlgHom hb, hfm, hE, mul_zero, zero_mul, sub_zero]
  unfold Dof
  simp only [LogPf.pderiv_subst hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Proceed by induction on `n generalizing G with`. Consider the case `zero => rfl`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', E_nabla B h hax m u, ih]`.
-/
theorem E_iter (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) (u : Fin d → k)
    (n : ℕ) (G : AA k d) :
    subst (bE k h) ((nabla k B h m u 0)^[n] G) = (Dof (B.FK k) u)^[n] (subst (bE k h) G) := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', E_nabla B h hax m u, ih]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => rfl`. Consider the case `cons l L ih`. Simplify using `only [List.foldr_cons]`. Rewrite using `[E_iter B h hax m (u l) (n l), ih]`.
-/
theorem E_foldr (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι : Type}
    (u : ι → Fin d → k) (n : ι →₀ ℕ) (L : List ι) (G : AA k d) :
    subst (bE k h) (L.foldr (fun l g => (nabla k B h m (u l) 0)^[n l] g) G) =
      L.foldr (fun l g => (Dof (B.FK k) (u l))^[n l] g) (subst (bE k h) G) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons]
    rw [E_iter B h hax m (u l) (n l), ih]

/- English proof (translation)
Establish `hb : HasSubst (bE k h)` using `hasSubst_lemma (bE_const k h hax)`. Unfold `nablaPoly DpolyOf DmonOf`. Rewrite using `[← coe_substAlgHom hb, map_sum]`. Use `Finset.sum_congr rfl (fun n _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, coe_substAlgHom hb, mvPowerSeries_subst_C hb, E_foldr B h hax m u n]`.
-/
theorem E_nablaPoly (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι : Type}
    [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial ι k) (G : AA k d) :
    subst (bE k h) (nablaPoly k B h m u P G) = DpolyOf (B.FK k) u P (subst (bE k h) G) := by
  have hb : HasSubst (bE k h) := hasSubst_lemma (bE_const k h hax)
  unfold nablaPoly DpolyOf DmonOf
  rw [← coe_substAlgHom hb, map_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [map_mul, coe_substAlgHom hb, mvPowerSeries_subst_C hb, E_foldr B h hax m u n]

end Inter

/- English proof (translation)
Introduce `R _ d O _ _ k _ _ _ B h hax m ι _ u P g`. Rewrite using `[← const_subst (bE_const k h hax) (nablaPoly k B h m u P (liftX k g)), E_nablaPoly B h hax m u P, E_liftX k h hax g]`.
-/
theorem harmonic_value_integral : ReciprocityTheory.ChartRestriction.G.TB.ValueSt := by
  intro R _ d O _ _ k _ _ _ B h hax m ι _ u P g
  rw [← const_subst (bE_const k h hax) (nablaPoly k B h m u P (liftX k g)), E_nablaPoly B h hax m u P,
    E_liftX k h hax g]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
