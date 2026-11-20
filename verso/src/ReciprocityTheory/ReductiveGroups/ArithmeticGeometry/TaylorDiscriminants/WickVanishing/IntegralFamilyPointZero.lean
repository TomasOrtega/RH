import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofComm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section Int

variable (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]

def Ig (σ : Type) : Subring (MvPowerSeries σ k) := (MvPowerSeries.map (σ := σ) (algebraMap R k)).range

variable {R k}

/- English proof (translation)
The claim follows from `RingHom.mem_range.mpr ⟨f, rfl⟩`.
-/
theorem ig_map {σ : Type} (f : MvPowerSeries σ R) : MvPowerSeries.map (algebraMap R k) f ∈ Ig R k σ := RingHom.mem_range.mpr ⟨f, rfl⟩

/- English proof (translation)
The claim follows from `RingHom.mem_range.mpr ⟨C r, by simp⟩`.
-/
theorem ig_C {σ : Type} (r : R) : (C (algebraMap R k r) : MvPowerSeries σ k) ∈ Ig R k σ := RingHom.mem_range.mpr ⟨C r, by simp⟩

/- English proof (translation)
The claim follows from `RingHom.mem_range.mpr ⟨X s, by simp⟩`.
-/
theorem ig_X {σ : Type} (s : σ) : (X s : MvPowerSeries σ k) ∈ Ig R k σ := RingHom.mem_range.mpr ⟨X s, by simp⟩

/- English proof (translation)
Use extensionality with `n`. Use `show coeff n (MvPowerSeries.map (algebraMap R k) (pderivFun v f)) = coeff n (pderivFun v (MvPowerSeries.map (algebraMap R k) f))`. Unfold `pderivFun`. Use `show algebraMap R k (coeff (n + Finsupp.single v 1) f * ((n v : R) + 1)) = algebraMap R k (coeff (n + Finsupp.single v 1) f) * ((n v : k) + 1)`. Rewrite using `[map_mul, map_add, map_one, map_natCast]`.
-/
theorem map_pderiv' {σ : Type} (f : MvPowerSeries σ R) (v : σ) :
    MvPowerSeries.map (algebraMap R k) (pderiv R v f) = pderiv k v (MvPowerSeries.map (algebraMap R k) f) := by
  ext n
  show coeff n (MvPowerSeries.map (algebraMap R k) (pderivFun v f)) =
    coeff n (pderivFun v (MvPowerSeries.map (algebraMap R k) f))
  unfold pderivFun
  show algebraMap R k (coeff (n + Finsupp.single v 1) f * ((n v : R) + 1)) =
    algebraMap R k (coeff (n + Finsupp.single v 1) f) * ((n v : k) + 1)
  rw [map_mul, map_add, map_one, map_natCast]

/- English proof (translation)
Take `⟨g, rfl⟩` from `RingHom.mem_range.mp hf`. Conclude with `RingHom.mem_range.mpr ⟨pderiv R v g, map_pderiv' g v⟩`.
-/
theorem ig_pderiv {σ : Type} {f : MvPowerSeries σ k} (hf : f ∈ Ig R k σ) (v : σ) : pderiv k v f ∈ Ig R k σ := by
  obtain ⟨g, rfl⟩ := RingHom.mem_range.mp hf
  exact RingHom.mem_range.mpr ⟨pderiv R v g, map_pderiv' g v⟩

/- English proof (translation)
Use `choose a' ha' using fun s => RingHom.mem_range.1 (ha s)`. Take `⟨f', rfl⟩` from `RingHom.mem_range.1 hf`. Use `set b : σ → MvPowerSeries τ R := fun s => a' s - C (constantCoeff (a' s)) with hb`. Establish `hbc : ∀ s, constantCoeff (b s) = 0` using `fun s => by simp [hb]`. Establish `hmap : ∀ s, MvPowerSeries.map (algebraMap R k) (b s) = a s` using `fun s => by`.

Establish `e1 : algebraMap R k (constantCoeff (a' s)) = 0`. Rewrite using `[← hc s, ← ha' s, constantCoeff_map]`. Simplify using `[hb, ha' s, e1]`. Use `RingHom.mem_range.2 ⟨subst b f', ?_⟩` and prove the remaining obligations. Rewrite using `[MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero hbc)]`.

Simplify using `only [hmap]`.
-/
theorem ig_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, a s ∈ Ig R k τ)
    (hc : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ k} (hf : f ∈ Ig R k σ) : subst a f ∈ Ig R k τ := by
  choose a' ha' using fun s => RingHom.mem_range.1 (ha s)
  obtain ⟨f', rfl⟩ := RingHom.mem_range.1 hf
  set b : σ → MvPowerSeries τ R := fun s => a' s - C (constantCoeff (a' s)) with hb
  have hbc : ∀ s, constantCoeff (b s) = 0 := fun s => by simp [hb]
  have hmap : ∀ s, MvPowerSeries.map (algebraMap R k) (b s) = a s := fun s => by
    have e1 : algebraMap R k (constantCoeff (a' s)) = 0 := by
      rw [← hc s, ← ha' s, constantCoeff_map]
    simp [hb, ha' s, e1]
  refine RingHom.mem_range.2 ⟨subst b f', ?_⟩
  rw [MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero hbc)]
  simp only [hmap]

/- English proof (translation)
Unfold `ev`. Use `ig_subst (a := fun p : Fin m × Fin d => a p.1 p.2) ?_ ?_ hf` and prove the remaining obligations. Introduce `p`. Conclude with `ha p.1 p.2`. Introduce `p`.

Conclude with `hc p.1 p.2`.
-/
theorem ig_ev {m n d : ℕ} {a : Fin m → Pt k n d} (hc : CZ a) (ha : ∀ j i, a j i ∈ Ig R k (Fin n × Fin d))
    {f : PS k m d} (hf : f ∈ Ig R k (Fin m × Fin d)) : ev a f ∈ Ig R k (Fin n × Fin d) := by
  unfold ev
  refine ig_subst (a := fun p : Fin m × Fin d => a p.1 p.2) ?_ ?_ hf
  · intro p
    exact ha p.1 p.2
  · intro p
    exact hc p.1 p.2

/- English proof (translation)
Unfold `liftX`. Use `ig_subst ?_ ?_ hf` and prove the remaining obligations. Introduce `p`. Conclude with `ig_X _`. Introduce `p`.

Conclude with `MvPowerSeries.constantCoeff_X _`.
-/
theorem ig_liftX [Algebra ℚ k] {d : ℕ} {f : PS k 1 d} (hf : f ∈ Ig R k (Fin 1 × Fin d)) :
    liftX k f ∈ Ig R k (Fin d ⊕ Fin d) := by
  unfold liftX
  refine ig_subst ?_ ?_ hf
  · intro p
    exact ig_X _
  · intro p
    exact MvPowerSeries.constantCoeff_X _

/- English proof (translation)
Unfold `IntAA`. Introduce `n`. Take `⟨g, rfl⟩` from `RingHom.mem_range.mp hG`. Conclude with `⟨coeff n g, (MvPowerSeries.coeff_map _ _ _).symm⟩`.
-/
theorem intAA_of_ig {σ : Type} {G : MvPowerSeries σ k} (hG : G ∈ Ig R k σ) : IntAA (R := R) k G := by
  unfold IntAA
  intro n
  obtain ⟨g, rfl⟩ := RingHom.mem_range.mp hG
  exact ⟨coeff n g, (MvPowerSeries.coeff_map _ _ _).symm⟩

/- English proof (translation)
Unfold `IntAA at hG`. Use `RingHom.mem_range.mpr ⟨(fun n => (hG n).choose : MvPowerSeries σ R), ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Conclude with `(hG n).choose_spec`.
-/
theorem ig_of_intAA {σ : Type} {G : MvPowerSeries σ k} (hG : IntAA (R := R) k G) : G ∈ Ig R k σ := by
  unfold IntAA at hG
  refine RingHom.mem_range.mpr ⟨(fun n => (hG n).choose : MvPowerSeries σ R), ?_⟩
  ext n
  exact (hG n).choose_spec

/- English proof (translation)
Unfold `ev`. Establish `hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2)` using `by first`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => ha p.1 p.2)`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)`.

Rewrite using `[MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `e he`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `he (Finsupp.ext h)`. Rewrite using `[Finsupp.prod, map_prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs'), smul_zero]`. Rewrite using `[map_pow, ha s.1 s.2, zero_pow hs']`.
-/
theorem cc_ev' {K : Type} [CommRing K] {m n d : ℕ} {a : Fin m → Pt K n d} (ha : CZ a) (f : PS K m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => ha p.1 p.2)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
          (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs'),
      smul_zero]
    rw [map_pow, ha s.1 s.2, zero_pow hs']

/- English proof (translation)
Rewrite using `[FB.expS, Formalism.G.LogCR.pderiv_psubst hf, PowerSeries.derivative_exp]`.
-/
theorem pderiv_expS [Algebra ℚ k] {n d : ℕ} {f : PS k n d} (hf : constantCoeff f = 0) (v : Fin n × Fin d) :
    pderiv k v (FB.expS k f) = FB.expS k f * pderiv k v f := by
  rw [FB.expS, Formalism.G.LogCR.pderiv_psubst hf, PowerSeries.derivative_exp]

/- English proof (translation)
Establish `h1 : pderiv k v (MvPowerSeries.map (algebraMap R k) U) = MvPowerSeries.map (algebraMap R k) U * pderiv k v H`. Rewrite using `[he]`. Conclude with `pderiv_expS hH v`. Establish `hinv : U * MvPowerSeries.invOfUnit U 1 = 1` using `MvPowerSeries.mul_invOfUnit U 1 (by rw [hU, Units.val_one])`. Establish `h2 : pderiv k v H = MvPowerSeries.map (algebraMap R k) (MvPowerSeries.invOfUnit U 1 * pderiv R v U)`.

Rewrite using `[map_mul, map_pderiv', h1, ← mul_assoc, ← map_mul, mul_comm (MvPowerSeries.invOfUnit U 1) U, hinv, map_one, one_mul]`. Rewrite using `[h2]`. Conclude with `ig_map _`.
-/
theorem ig_dlog [Algebra ℚ k] {n d : ℕ} (U : PS R n d) (hU : constantCoeff U = 1) (H : PS k n d)
    (hH : constantCoeff H = 0) (he : MvPowerSeries.map (algebraMap R k) U = FB.expS k H) (v : Fin n × Fin d) :
    pderiv k v H ∈ Ig R k (Fin n × Fin d) := by
  have h1 : pderiv k v (MvPowerSeries.map (algebraMap R k) U) =
      MvPowerSeries.map (algebraMap R k) U * pderiv k v H := by
    rw [he]
    exact pderiv_expS hH v
  have hinv : U * MvPowerSeries.invOfUnit U 1 = 1 :=
    MvPowerSeries.mul_invOfUnit U 1 (by rw [hU, Units.val_one])
  have h2 : pderiv k v H =
      MvPowerSeries.map (algebraMap R k) (MvPowerSeries.invOfUnit U 1 * pderiv R v U) := by
    rw [map_mul, map_pderiv', h1, ← mul_assoc, ← map_mul, mul_comm (MvPowerSeries.invOfUnit U 1) U,
      hinv, map_one, one_mul]
  rw [h2]
  exact ig_map _

end Int

section Fam

variable {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] {d : ℕ}

/- English proof (translation)
Unfold `pt`. Conclude with `ig_X _`.
-/
theorem ig_pt {n : ℕ} (j : Fin n) (i : Fin d) : pt k d j i ∈ Ig R k (Fin n × Fin d) := by
  unfold pt
  exact ig_X _

/- English proof (translation)
Introduce `j i`. Use `fin_cases j`. Use `first`. Consider the case `exact ig_pt 0 i`. Consider the case `simpa using ig_pt (R := R) (k := k) (0 : Fin 1) i`.

Use `first`. Consider the case `exact (Ig R k _).zero_mem`. Consider the case `simpa using (Ig R k (Fin 1 × Fin d)).zero_mem`.
-/
theorem integral_family_point_zero : ∀ j i, (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) j i ∈ Ig R k (Fin 1 × Fin d) := by
  intro j i
  fin_cases j
  · first
      | exact ig_pt 0 i
      | simpa using ig_pt (R := R) (k := k) (0 : Fin 1) i
  · first
      | exact (Ig R k _).zero_mem
      | simpa using (Ig R k (Fin 1 × Fin d)).zero_mem

/- English proof (translation)
Introduce `j i`. Use `fin_cases j`. Use `first`. Consider the case `exact ig_pt 0 i`. Consider the case `simpa using ig_pt (R := R) (k := k) (0 : Fin 2) i`.

Use `first`. Consider the case `exact ig_pt 1 i`. Consider the case `simpa using ig_pt (R := R) (k := k) (1 : Fin 2) i`. Use `first`. Consider the case `exact (Ig R k _).zero_mem`.

Consider the case `simpa using (Ig R k (Fin 2 × Fin d)).zero_mem`.
-/
theorem integral_family_pair_zero : ∀ j i, (![pt k (n := 2) d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) j i ∈ Ig R k (Fin 2 × Fin d) := by
  intro j i
  fin_cases j
  · first
      | exact ig_pt 0 i
      | simpa using ig_pt (R := R) (k := k) (0 : Fin 2) i
  · first
      | exact ig_pt 1 i
      | simpa using ig_pt (R := R) (k := k) (1 : Fin 2) i
  · first
      | exact (Ig R k _).zero_mem
      | simpa using (Ig R k (Fin 2 × Fin d)).zero_mem

end Fam

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
