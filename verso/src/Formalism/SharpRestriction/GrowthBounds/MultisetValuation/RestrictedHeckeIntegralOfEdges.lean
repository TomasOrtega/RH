import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HeckeValueEstimateOfRecordValue
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulUpdate
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RamifiedLatticeOfChainEstimates
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GShiftRowGenMonomial

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

def RestWeylEdge : Prop :=
  ∀ (v : Fin P.nV) (i : ℕ) (L : P.Tup) (L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)),
    P.IsLatTup L → IsEdge p (P.n' v) i ⟨L'', L v⟩ →
    ∀ x ∈ P.HtupW (Function.update L v L''), ((p : Kf) ^ (Ar i (P.lam0 v))) • x ∈ P.HtupW L

/- English proof (translation)
Introduce `u`. Distinguish the cases in `h : u = v`. Substitute `h` using the available equality. Establish `e : Function.update (β` using `fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L u A u = A := Function.update_self u A L`. Conclude with `e.symm ▸ hA`.

Establish `e : Function.update (β` using `fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A u = L u := Function.update_of_ne h A L`. Conclude with `e.symm ▸ hL u`.
-/
theorem latTup_update {L : P.Tup} (hL : P.IsLatTup L) {v : Fin P.nV}
    {A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} (hA : IsLattice (P.W v) A) :
    P.IsLatTup (Function.update L v A) := by
  intro u
  by_cases h : u = v
  · subst h
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L u A u = A :=
      Function.update_self u A L
    exact e.symm ▸ hA
  · have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A u = L u :=
      Function.update_of_ne h A L
    exact e.symm ▸ hL u

/- English proof (translation)
Rewrite using `[Tminus_eq, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun L'' hL'' => ?_` and prove the remaining obligations. Establish `hE` using `(mem_EE P).1 hL''`. Conclude with `h v i L L'' hL hE _ (hF _ (latTup_update P hL hE.1))`.
-/
theorem Tminus_mem (h : RestWeylEdge P) (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp)
    (hF : ∀ L, P.IsLatTup L → F L ∈ P.HtupW L) (L : P.Tup) (hL : P.IsLatTup L) :
    ((p : Kf) ^ (Ar i (P.lam0 v))) • P.Tminus v i F L ∈ P.HtupW L := by
  rw [Tminus_eq, Finset.smul_sum]
  refine Submodule.sum_mem _ fun L'' hL'' => ?_
  have hE := (mem_EE P).1 hL''
  exact h v i L L'' hL hE _ (hF _ (latTup_update P hL hE.1))

end PlacesLevel

section Num

variable {n' k1 : ℕ} {p t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ}
  {lam0 : Fin n' → Fin (k1 + 1) → ℤ} {w : ℕ → Fin n' → ℤ}

/- English proof (translation)
Unfold `liftWt`. Use `split_ifs with hx`. Establish `e1` using `h.dom s (Fin.le_last (⟨x.val, hx⟩ : Fin (k1 + 1)))`. Establish `e2` using `(h.w_low s).2`. Establish `e3` using `w_le h s (l := 1) (l' := j + 1) le_rfl (by omega) hj`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[neg_neg]`. Use `w_le h s (Nat.le_add_left 1 _) ?_ hj` and prove the remaining obligations. Establish `hx2` using `x.isLt`. Establish `: (x.val - (k1 + 1)) / (t + 1) < j + 1`.

Rewrite using `[Nat.div_lt_iff_lt_mul (by omega)]`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem neg_liftWt_le (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (j : ℕ) (hj : j + 1 ≤ m)
    (x : Fin (k1 + (j + 1) * (t + 1) + 1)) :
    -liftWt t k1 (lam0 s) (fun l => w l s) (j + 1) x ≤ w (j + 1) s := by
  unfold liftWt
  split_ifs with hx
  · have e1 := h.dom s (Fin.le_last (⟨x.val, hx⟩ : Fin (k1 + 1)))
    have e2 := (h.w_low s).2
    have e3 := w_le h s (l := 1) (l' := j + 1) le_rfl (by omega) hj
    linarith
  · rw [neg_neg]
    refine w_le h s (Nat.le_add_left 1 _) ?_ hj
    have hx2 := x.isLt
    have : (x.val - (k1 + 1)) / (t + 1) < j + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega

/- English proof (translation)
Use `Finset.card_le_card_of_injOn (s := univ.filter fun x : Fin N => x.val < i) (t := range i) (fun x => x.val) (fun x hx => by` as an intermediate fact. Establish `hx'` using `(mem_filter.1 (Finset.mem_coe.1 hx)).2`. Conclude with `Finset.mem_coe.2 (mem_range.2 hx')) (fun x _ y _ hxy => Fin.ext hxy)`. Rewrite `this` using `[card_range]`. Then use the resulting hypothesis.
-/
theorem card_filter_lt_le (N i : ℕ) : (univ.filter fun x : Fin N => x.val < i).card ≤ i := by
  have := Finset.card_le_card_of_injOn (s := univ.filter fun x : Fin N => x.val < i) (t := range i)
    (fun x => x.val) (fun x hx => by
      have hx' := (mem_filter.1 (Finset.mem_coe.1 hx)).2
      exact Finset.mem_coe.2 (mem_range.2 hx')) (fun x _ y _ hxy => Fin.ext hxy)
  rwa [card_range] at this

/- English proof (translation)
Unfold `Ar Nprime`. Rewrite using `[← Finset.sum_filter_not_add_sum_filter univ (fun s : Fin n' => IsOddPos s), Finset.mul_sum]`. Use `add_le_add (le_of_eq ?_) ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite `hs` using `[mem_filter]`.

Establish `he : Even s.val`. Rewrite using `[Nat.even_iff]`. Use `hs.2` as an intermediate fact. Unfold `IsOddPos at this`. Use linear arithmetic over natural numbers and integers.

Use `Finset.sum_bij (fun x _ => x.val + 1) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[mem_filter]`. Rewrite using `[mem_Icc]`. Use linear arithmetic over natural numbers and integers.

Introduce `x _ x' _ hxx`. Conclude with `Fin.ext (by omega)`. Introduce `y hy`. Rewrite `hy` using `[mem_Icc]`. Conclude with `⟨⟨y - 1, by omega⟩, by rw [mem_filter]; exact ⟨mem_univ _, by show y - 1 < i; omega⟩, by show y - 1 + 1 = y; omega⟩`.

Introduce `x hx`. Rewrite `hx` using `[mem_filter]`. Unfold `lamAt`. Rewrite using `[if_pos he]`. Use `show liftWt t k1 (lam0 s) (fun l => w l s) (j + 1) x = _`.

Unfold `liftWt`. Rewrite using `[dif_pos (by omega : x.val < k1 + 1)]`. Conclude with `(lamI_fin lam0 s ⟨x.val, by omega⟩).symm`. Use `Finset.sum_le_sum fun s hs => ?_` and prove the remaining obligations. Rewrite `hs` using `[mem_filter]`.

Establish `he : ¬ Even s.val`. Rewrite using `[Nat.even_iff]`. Use `hs.2` as an intermediate fact. Unfold `IsOddPos at this`. Use linear arithmetic over natural numbers and integers.

Establish `hw0 : 0 ≤ w (j + 1) s`. Establish `e2` using `(h.w_low s).1`. Establish `e3` using `w_le h s (l := 1) (l' := j + 1) le_rfl (by omega) hj`. Establish `: (0 : ℤ) ≤ c` using `Int.natCast_nonneg c`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : ∑ x : Fin (k1 + (j + 1) * (t + 1) + 1) with x.val < i, lamAt (fun s => liftWt t k1 (lam0 s) (fun l => w l s) (j + 1)) s x ≤ (univ.filter fun x : Fin (k1 + (j + 1) * (t + 1) + 1) => x.val < i).card • w (j + 1) s`. Use `Finset.sum_le_card_nsmul _ _ _ fun x _ => ?_` and prove the remaining obligations. Unfold `lamAt`. Rewrite using `[if_neg he]`. Conclude with `neg_liftWt_le h s j hj x.rev`.

Use `le_trans h1 ?_` and prove the remaining obligations. Rewrite using `[nsmul_eq_mul]`. Establish `h2 : ((univ.filter fun x : Fin (k1 + (j + 1) * (t + 1) + 1) => x.val < i).card : ℤ) ≤ i`. Conclude with `card_filter_lt_le _ i` after adjusting the coercions. Conclude with `mul_le_mul_of_nonneg_right h2 hw0`.
-/
theorem Ar_lift_le (h : Std p n' k1 t m c r TT a b lam0 w) (j i : ℕ) (hj : j + 1 ≤ m) (hi : i ≤ k1 + 1) :
    Ar i (fun s => liftWt t k1 (lam0 s) (fun l => w l s) (j + 1)) ≤ Nprime lam0 w (j + 1) i := by
  unfold Ar Nprime
  rw [← Finset.sum_filter_not_add_sum_filter univ (fun s : Fin n' => IsOddPos s), Finset.mul_sum]
  refine add_le_add (le_of_eq ?_) ?_
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [mem_filter] at hs
    have he : Even s.val := by
      rw [Nat.even_iff]
      have := hs.2
      unfold IsOddPos at this
      omega
    refine Finset.sum_bij (fun x _ => x.val + 1) ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_filter] at hx
      rw [mem_Icc]
      omega
    · intro x _ x' _ hxx
      exact Fin.ext (by omega)
    · intro y hy
      rw [mem_Icc] at hy
      exact ⟨⟨y - 1, by omega⟩, by rw [mem_filter]; exact ⟨mem_univ _, by show y - 1 < i; omega⟩,
        by show y - 1 + 1 = y; omega⟩
    · intro x hx
      rw [mem_filter] at hx
      unfold lamAt
      rw [if_pos he]
      show liftWt t k1 (lam0 s) (fun l => w l s) (j + 1) x = _
      unfold liftWt
      rw [dif_pos (by omega : x.val < k1 + 1)]
      exact (lamI_fin lam0 s ⟨x.val, by omega⟩).symm
  · refine Finset.sum_le_sum fun s hs => ?_
    rw [mem_filter] at hs
    have he : ¬ Even s.val := by
      rw [Nat.even_iff]
      have := hs.2
      unfold IsOddPos at this
      omega
    have hw0 : 0 ≤ w (j + 1) s := by
      have e2 := (h.w_low s).1
      have e3 := w_le h s (l := 1) (l' := j + 1) le_rfl (by omega) hj
      have : (0 : ℤ) ≤ c := Int.natCast_nonneg c
      linarith
    have h1 : ∑ x : Fin (k1 + (j + 1) * (t + 1) + 1) with x.val < i,
        lamAt (fun s => liftWt t k1 (lam0 s) (fun l => w l s) (j + 1)) s x ≤
        (univ.filter fun x : Fin (k1 + (j + 1) * (t + 1) + 1) => x.val < i).card • w (j + 1) s := by
      refine Finset.sum_le_card_nsmul _ _ _ fun x _ => ?_
      unfold lamAt
      rw [if_neg he]
      exact neg_liftWt_le h s j hj x.rev
    refine le_trans h1 ?_
    rw [nsmul_eq_mul]
    have h2 : ((univ.filter fun x : Fin (k1 + (j + 1) * (t + 1) + 1) => x.val < i).card : ℤ) ≤ i := by
      exact_mod_cast card_filter_lt_le _ i
    exact mul_le_mul_of_nonneg_right h2 hw0

end Num

section SysLevel

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

/- English proof (translation)
Rewrite `hF`, the goal using `[mem_Int_iff]`. Conclude with `⟨fun c L hL => Tminus_mem (X.Pj j) h (X.vJ j v) i (F c) (hF.1 c) L hL, Eqv_smul X _ (restTmEquiv X j v i F hF.2)⟩`.
-/
theorem TmInt {j : ℕ} (h : RestWeylEdge (X.Pj j)) (v : X.Pl) (i : ℕ) {F : X.Fm j} (hF : F ∈ X.Int j) :
    ((p : X.G.Kf) ^ (Ar i ((X.Pj j).lam0 (X.vJ j v)))) • X.Tm v i j F ∈ X.Int j := by
  rw [mem_Int_iff] at hF ⊢
  exact ⟨fun c L hL => Tminus_mem (X.Pj j) h (X.vJ j v) i (F c) (hF.1 c) L hL,
    Eqv_smul X _ (restTmEquiv X j v i F hF.2)⟩

/- English proof (translation)
The claim follows from `Rep.ne_zero X (frac_of_place X v) (Rep.ofP X)`.
-/
theorem p_ne_zero (v : X.Pl) : (p : X.G.Kf) ≠ 0 := Rep.ne_zero X (frac_of_place X v) (Rep.ofP X)

/- English proof (translation)
Introduce `v i j F hF`. Establish `hp` using `p_ne_zero X v`. Establish `hle : X.FQ j ≤ (X.FQ j).comap (TmLin X v i j)`. Use `Submodule.span_le.2 fun G hG => ?_` and prove the remaining obligations. Use `show X.Tm v i j G ∈ X.FQ j`.

Establish `h1` using `TmInt X (h j) v i hG`. Establish `h2 : ((p : X.G.Kf) ^ (Ar i ((X.Pj j).lam0 (X.vJ j v))))⁻¹ • (((p : X.G.Kf) ^ (Ar i ((X.Pj j).lam0 (X.vJ j v)))) • X.Tm v i j G) ∈ X.FQ j` using `Submodule.smul_mem _ _ (Submodule.subset_span h1)`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hp), one_smul]`. Then use the resulting hypothesis. Conclude with `hle hF`.
-/
theorem restTmFQ_of (h : ∀ j, RestWeylEdge (X.Pj j)) : RestTmFQ X := by
  intro v i j F hF
  have hp := p_ne_zero X v
  have hle : X.FQ j ≤ (X.FQ j).comap (TmLin X v i j) := by
    refine Submodule.span_le.2 fun G hG => ?_
    show X.Tm v i j G ∈ X.FQ j
    have h1 := TmInt X (h j) v i hG
    have h2 : ((p : X.G.Kf) ^ (Ar i ((X.Pj j).lam0 (X.vJ j v))))⁻¹ •
        (((p : X.G.Kf) ^ (Ar i ((X.Pj j).lam0 (X.vJ j v)))) • X.Tm v i j G) ∈ X.FQ j :=
      Submodule.smul_mem _ _ (Submodule.subset_span h1)
    rwa [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hp), one_smul] at h2
  exact hle hF

/- English proof (translation)
Introduce `v j hj i hi F hF`. Rewrite `hi` using `[mem_Icc]`. Establish `hp` using `p_ne_zero X v`. Unfold `Sys.Tt`. Rewrite using `[if_neg (by omega)]`.

Establish `h1` using `TmInt X (h (j + 1)) v i hF`. Establish `hle : Ar i ((X.Pj (j + 1)).lam0 (X.vJ (j + 1) v)) ≤ Nprime (X.G.P.lam0 v) (X.w v) (j + 1) i` using `Ar_lift_le (X.std v) j i hj (by have := (X.std v).two_r; omega)`. Take `⟨d, hd⟩` from `Int.le.dest hle`. Rewrite using `[← hd, zpow_add₀ hp, zpow_natCast, mul_comm, mul_smul]`. Establish `e : ∀ y : X.Fm (j + 1), ((p : X.G.Kf) ^ d) • y = ((p : X.G.O) ^ d) • y`.

Introduce `y`. Rewrite using `[← algebraMap_smul X.G.Kf ((p : X.G.O) ^ d) y, map_pow, map_natCast]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ h1`.
-/
theorem restricted_hecke_integral_of_edges (h : ∀ j, RestWeylEdge (X.Pj j)) : HeckeIntegralLevel X := by
  intro v j hj i hi F hF
  rw [mem_Icc] at hi
  have hp := p_ne_zero X v
  unfold Sys.Tt
  rw [if_neg (by omega)]
  have h1 := TmInt X (h (j + 1)) v i hF
  have hle : Ar i ((X.Pj (j + 1)).lam0 (X.vJ (j + 1) v)) ≤ Nprime (X.G.P.lam0 v) (X.w v) (j + 1) i :=
    Ar_lift_le (X.std v) j i hj (by have := (X.std v).two_r; omega)
  obtain ⟨d, hd⟩ := Int.le.dest hle
  rw [← hd, zpow_add₀ hp, zpow_natCast, mul_comm, mul_smul]
  have e : ∀ y : X.Fm (j + 1), ((p : X.G.Kf) ^ d) • y = ((p : X.G.O) ^ d) • y := by
    intro y
    rw [← algebraMap_smul X.G.Kf ((p : X.G.O) ^ d) y, map_pow, map_natCast]
  rw [e]
  exact Submodule.smul_mem _ _ h1

end SysLevel

section EdgeProof

open Formalism.MainNotions.G.LatticeSystems MvPolynomial

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

/- English proof (translation)
Establish `key : P.tenV M ≤ (P.tenV M').comap ((LinearMap.lsmul Kf P.Xsp c).restrictScalars O)`. Unfold `Places.tenV`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨Function.update F v (c • F v), ?_, ?_⟩` and prove the remaining obligations. Introduce `u`. Distinguish the cases in `h : u = v`. Substitute `h` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `hv _ (hF u)`. Rewrite using `[Function.update_of_ne h]`. Conclude with `hu u h (hF u)`. Use `show c • ∏ u, P.vEmb u (F u) = ∏ u, P.vEmb u (Function.update F v (c • F v) u)`. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun u => P.vEmb u (F u)) (Finset.mem_univ v), ← Finset.mul_prod_erase Finset.univ (fun u => P.vEmb u (Function.update F v (c • F v) u)) (Finset.mem_univ v), Function.update_self, map_smul, smul_mul_assoc]`.

Use `congr 2`. Use `Finset.prod_congr rfl fun u hu' => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hu')]`. Conclude with `fun x hx => key hx`.
-/
theorem tenV_scale (v : Fin P.nV)
    (M M' : ∀ u, Submodule O (MvPolynomial (Fin (P.n' u) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)) (c : Kf)
    (hv : ∀ F ∈ M v, c • F ∈ M' v) (hu : ∀ u, u ≠ v → M u ≤ M' u) :
    ∀ x ∈ P.tenV M, c • x ∈ P.tenV M' := by
  classical
  have key : P.tenV M ≤ (P.tenV M').comap ((LinearMap.lsmul Kf P.Xsp c).restrictScalars O) := by
    unfold Places.tenV
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    apply Submodule.subset_span
    refine ⟨Function.update F v (c • F v), ?_, ?_⟩
    · intro u
      by_cases h : u = v
      · subst h
        rw [Function.update_self]
        exact hv _ (hF u)
      · rw [Function.update_of_ne h]
        exact hu u h (hF u)
    · show c • ∏ u, P.vEmb u (F u) = ∏ u, P.vEmb u (Function.update F v (c • F v) u)
      rw [← Finset.mul_prod_erase Finset.univ (fun u => P.vEmb u (F u)) (Finset.mem_univ v),
        ← Finset.mul_prod_erase Finset.univ (fun u => P.vEmb u (Function.update F v (c • F v) u))
          (Finset.mem_univ v), Function.update_self, map_smul, smul_mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun u hu' => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hu')]
  exact fun x hx => key hx

/- English proof (translation)
Establish `hS` using `P.setting v`. Use `hS.frac_alt` as an intermediate fact. Establish `h1 : (p : P.Qq v) ≠ 0`. Establish `h2 : algebraMap (P.W v) (P.Qq v) (p : P.W v) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (P.W v) (P.Qq v))).2 hS.p_unif.ne_zero`. Rewrite `h2` using `[map_natCast]`. Then use the resulting hypothesis.

Establish `h3 : P.ι v (p : P.Qq v) ≠ 0` using `(map_ne_zero (P.ι v)).2 h1`. Rewrite `h3` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem pKf_ne_of_place (v : Fin P.nV) : (p : Kf) ≠ 0 := by
  have hS := P.setting v
  have := hS.frac_alt
  have h1 : (p : P.Qq v) ≠ 0 := by
    have h2 : algebraMap (P.W v) (P.Qq v) (p : P.W v) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (P.W v) (P.Qq v))).2 hS.p_unif.ne_zero
    rwa [map_natCast] at h2
  have h3 : P.ι v (p : P.Qq v) ≠ 0 := (map_ne_zero (P.ι v)).2 h1
  rwa [map_natCast] at h3

/- English proof (translation)
Unfold `la_tw lb_D`. Rewrite using `[map_mul]`. Use `congr 1`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]`. Use `congr 1`.

Use function extensionality and compare the values at `c`. Use `show (P.ι v).comp ((P.σ v ^ s : P.Qq v ≃+* P.Qq v) : P.Qq v →+* P.Qq v) (if c.val < i then ((p : P.Qq v))⁻¹ else 1) = _`. Use `split_ifs`. Rewrite using `[map_inv₀, map_natCast, map_natCast]`. Rewrite using `[map_one]`.
-/
theorem la_tw_diag (v : Fin P.nV) (s i : ℕ) (g : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) :
    la_tw (P.ι v) (P.σ v) s (g * Matrix.diagonal fun c => if c.val < i then ((p : P.Qq v))⁻¹ else 1) =
      la_tw (P.ι v) (P.σ v) s g * lb_D (P.m + 1) i (algebraMap O Kf (p : O)) := by
  unfold la_tw lb_D
  rw [map_mul]
  congr 1
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext c
  show (P.ι v).comp ((P.σ v ^ s : P.Qq v ≃+* P.Qq v) : P.Qq v →+* P.Qq v) (if c.val < i then ((p : P.Qq v))⁻¹ else 1) = _
  split_ifs
  · rw [map_inv₀, map_natCast, map_natCast]
  · rw [map_one]

/- English proof (translation)
Introduce `v i L L'' hL hE x hx`. Establish `hS` using `P.setting v`. Use `hS.frac_alt` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap O Kf)`. Use `hS.frac_O` as an intermediate fact.

Conclude with `IsFractionRing.injective O Kf`. Establish `hp` using `pKf_ne_of_place P v`. Establish `hw : algebraMap O Kf (p : O) ≠ 0` using `by rwa [map_natCast]`. Take `⟨g, hg, hsrc, htgt⟩` from `lc_main p (P.n' v) i (P.m + 1) hS.p_unif hS.res_card (by have := hS.five_le; omega) (by have := hS.two_le; omega) ⟨L'', L v⟩ hE`. Establish `hsrc' : L'' = colSpan (P.W v) g` using `hsrc`.

Establish `htgt' : L v = colSpan (P.W v) (g * Matrix.diagonal fun c => if c.val < i then ((p : P.Qq v))⁻¹ else 1)` using `htgt`. Establish `hfrob : ∀ x : P.W v, ∃ y : P.W v, P.σ v (algebraMap (P.W v) (P.Qq v) x) = algebraMap (P.W v) (P.Qq v) y`. Introduce `x`. Take `⟨y, hy⟩` from `hS.frob x`. Conclude with `⟨_, hy⟩`.

Establish `hloc : ∀ y ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val L''), ((p : Kf) ^ (Ar i (P.lam0 v))) • y ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (L v))`. Introduce `y hy`. Establish `h1` using `lb_tensor O Kf (fun s => Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val L'')) (fun s => Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (L v))) (fun s => (p : Kf) ^ (∑ t : Fin (P.m + 1) with t.val < i, lamAt (P.lam0 v) s t)) (by`. Introduce `s F hF`. Rewrite `hF` using `[hsrc', la_extO (P.ι v) (P.σ v) (P.j v) hfrob hS.ι_comp]`.

Rewrite using `[htgt', la_extO (P.ι v) (P.σ v) (P.j v) hfrob hS.ι_comp, la_tw_diag]`. Establish `h2` using `dl_pos O Kf hinj P.m i (lamAt (P.lam0 v) s) (p : O) hw _ (la_tw_det _ _ s.val g hg) F hF`. Rewrite using `[map_natCast] at h2 ⊢) y hy` and apply the resulting hypothesis. Rewrite `h1` using `[lb_zpow_sum _ hp]`. Conclude with `h1`.

Unfold `Places.HtupW at hx ⊢`. Use `tenV_scale P v _ _ _ ?_ ?_ x hx` and prove the remaining obligations. Introduce `F hF`. Establish `e : Function.update (β` using `fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' v = L'' := Function.update_self v L'' L`. Establish `hF' : F ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val L'')`.

Establish `h0 : F ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (Function.update (β` using `fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' v)) := hF`. Rewrite `h0` using `[e]`. Then use the resulting hypothesis. Conclude with `hloc F hF'`. Introduce `u hu F hF`. Establish `e : Function.update (β` using `fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' u = L u := Function.update_of_ne hu L'' L`.

Establish `h0 : F ∈ HtenW O (P.lam0 u) (fun s => extO O (P.ι u) (P.σ u) s.val (Function.update (β` using `fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' u)) := hF`. Rewrite `h0` using `[e]`. Then use the resulting hypothesis.
-/
theorem restWeylEdge : RestWeylEdge P := by
  intro v i L L'' hL hE x hx
  have hS := P.setting v
  have := hS.frac_alt
  have hinj : Function.Injective (algebraMap O Kf) := by
    have := hS.frac_O
    exact IsFractionRing.injective O Kf
  have hp := pKf_ne_of_place P v
  have hw : algebraMap O Kf (p : O) ≠ 0 := by rwa [map_natCast]
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p (P.n' v) i (P.m + 1) hS.p_unif hS.res_card
    (by have := hS.five_le; omega) (by have := hS.two_le; omega) ⟨L'', L v⟩ hE
  have hsrc' : L'' = colSpan (P.W v) g := hsrc
  have htgt' : L v = colSpan (P.W v) (g * Matrix.diagonal fun c => if c.val < i then ((p : P.Qq v))⁻¹ else 1) := htgt
  have hfrob : ∀ x : P.W v, ∃ y : P.W v, P.σ v (algebraMap (P.W v) (P.Qq v) x) = algebraMap (P.W v) (P.Qq v) y := by
    intro x
    obtain ⟨y, hy⟩ := hS.frob x
    exact ⟨_, hy⟩
  have hloc : ∀ y ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val L''),
      ((p : Kf) ^ (Ar i (P.lam0 v))) • y ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (L v)) := by
    intro y hy
    have h1 := lb_tensor O Kf (fun s => Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val L''))
      (fun s => Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (L v)))
      (fun s => (p : Kf) ^ (∑ t : Fin (P.m + 1) with t.val < i, lamAt (P.lam0 v) s t)) (by
        intro s F hF
        rw [hsrc', la_extO (P.ι v) (P.σ v) (P.j v) hfrob hS.ι_comp] at hF
        rw [htgt', la_extO (P.ι v) (P.σ v) (P.j v) hfrob hS.ι_comp, la_tw_diag]
        have h2 := dl_pos O Kf hinj P.m i (lamAt (P.lam0 v) s) (p : O) hw _ (la_tw_det _ _ s.val g hg) F hF
        rwa [map_natCast] at h2 ⊢) y hy
    rw [lb_zpow_sum _ hp] at h1
    exact h1
  unfold Places.HtupW at hx ⊢
  refine tenV_scale P v _ _ _ ?_ ?_ x hx
  · intro F hF
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' v = L'' :=
      Function.update_self v L'' L
    have hF' : F ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val L'') := by
      have h0 : F ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val
        (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' v)) := hF
      rwa [e] at h0
    exact hloc F hF'
  · intro u hu F hF
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' u = L u :=
      Function.update_of_ne hu L'' L
    have h0 : F ∈ HtenW O (P.lam0 u) (fun s => extO O (P.ι u) (P.σ u) s.val
      (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' u)) := hF
    rwa [e] at h0

end EdgeProof

section Final

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

/- English proof (translation)
The claim follows from `restTmFQ_of X fun j => restWeylEdge (X.Pj j)`.
-/
theorem restTmFQ : RestTmFQ X := restTmFQ_of X fun j => restWeylEdge (X.Pj j)

/- English proof (translation)
The claim follows from `restricted_hecke_integral_of_edges X fun j => restWeylEdge (X.Pj j)`.
-/
theorem restricted_hecke_integral : HeckeIntegralLevel X := restricted_hecke_integral_of_edges X fun j => restWeylEdge (X.Pj j)

end Final

end Formalism.MainNotions.FormalGroupSystem.Pf
