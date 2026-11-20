import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {d m n : ℕ}

def CZ (a : Fin m → Pt k n d) : Prop := ∀ j i, constantCoeff (a j i) = 0

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)`.
-/
theorem CZ.hasSubst {a : Fin m → Pt k n d} (ha : CZ a) : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

/- English proof (translation)
Establish `h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F` using `fun F => by`. Rewrite using `[MvPowerSeries.coe_substAlgHom]`. Both sides reduce to the same expression. Rewrite using `[h, h, h, map_add]`.
-/
theorem ev_add {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f + g) = ev a f + ev a g := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, h, h, map_add]

/- English proof (translation)
Establish `h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F` using `fun F => by`. Rewrite using `[MvPowerSeries.coe_substAlgHom]`. Both sides reduce to the same expression. Rewrite using `[h, h, h, map_mul]`.
-/
theorem ev_mul {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f * g) = ev a f * ev a g := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, h, h, map_mul]

def evHom {a : Fin m → Pt k n d} (ha : CZ a) : PS k m d →+* PS k n d :=
  (substAlgHom ha.hasSubst).toRingHom

/- English proof (translation)
Conclude with `congrFun (MvPowerSeries.coe_substAlgHom ha.hasSubst) f`.
-/
theorem evHom_apply {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : evHom ha f = ev a f := by
  exact congrFun (MvPowerSeries.coe_substAlgHom ha.hasSubst) f

/- English proof (translation)
Rewrite using `[← evHom_apply ha, ← evHom_apply ha, ← evHom_apply ha, map_sub]`.
-/
theorem ev_sub {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f - g) = ev a f - ev a g := by
  rw [← evHom_apply ha, ← evHom_apply ha, ← evHom_apply ha, map_sub]

/- English proof (translation)
Rewrite using `[← evHom_apply ha, ← evHom_apply ha, map_neg]`.
-/
theorem ev_neg {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : ev a (-f) = -ev a f := by
  rw [← evHom_apply ha, ← evHom_apply ha, map_neg]

/- English proof (translation)
Rewrite using `[← evHom_apply ha, map_sum]`. Conclude with `Finset.sum_congr rfl (fun x _ => evHom_apply ha (f x))`.
-/
theorem ev_sum {a : Fin m → Pt k n d} (ha : CZ a) {ι : Type} (s : Finset ι) (f : ι → PS k m d) :
    ev a (∑ x ∈ s, f x) = ∑ x ∈ s, ev a (f x) := by
  rw [← evHom_apply ha, map_sum]
  exact Finset.sum_congr rfl (fun x _ => evHom_apply ha (f x))

/- English proof (translation)
Establish `h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F` using `fun F => by`. Rewrite using `[MvPowerSeries.coe_substAlgHom]`. Both sides reduce to the same expression. Rewrite using `[h, show (C c : PS k m d) = algebraMap k (PS k m d) c from rfl, AlgHom.commutes]`. Both sides reduce to the same expression.
-/
theorem ev_C {a : Fin m → Pt k n d} (ha : CZ a) (c : k) : ev a (C c : PS k m d) = C c := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, show (C c : PS k m d) = algebraMap k (PS k m d) c from rfl, AlgHom.commutes]
  rfl

/- English proof (translation)
The claim follows from `MvPowerSeries.subst_X ha.hasSubst (j, i)`.
-/
theorem ev_X {a : Fin m → Pt k n d} (ha : CZ a) (j : Fin m) (i : Fin d) : ev a (X (j, i) : PS k m d) = a j i :=
  MvPowerSeries.subst_X ha.hasSubst (j, i)

/- English proof (translation)
Rewrite using `[← evHom_apply ha, map_zero]`.
-/
theorem ev_zero' {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by
  rw [← evHom_apply ha, map_zero]

/- English proof (translation)
The claim follows from `MvPowerSeries.constantCoeff_subst_eq_zero ha.hasSubst (fun p => ha p.1 p.2) hf`.
-/
theorem constantCoeff_ev {a : Fin m → Pt k n d} (ha : CZ a) {f : PS k m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero ha.hasSubst (fun p => ha p.1 p.2) hf

/- English proof (translation)
Introduce `j i` and use `constantCoeff_ev ha (hb j i)`.
-/
theorem CZ.ev {a : Fin m → Pt k n d} (ha : CZ a) {l : ℕ} {b : Fin l → Pt k m d} (hb : CZ b) :
    CZ (fun j i => ev a (b j i)) := fun j i => constantCoeff_ev ha (hb j i)

/- English proof (translation)
Conclude with `MvPowerSeries.subst_comp_subst_apply hb.hasSubst ha.hasSubst f`.
-/
theorem ev_ev {l : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) {b : Fin l → Pt k m d} (hb : CZ b) (f : PS k l d) :
    ev a (ev b f) = ev (fun j i => ev a (b j i)) f := by
  exact MvPowerSeries.subst_comp_subst_apply hb.hasSubst ha.hasSubst f

/- English proof (translation)
Use `show MvPowerSeries.subst (fun p : Fin m × Fin d => (X p : PS k m d)) f = f`. Rewrite using `[show (fun p : Fin m × Fin d => (X p : PS k m d)) = X from rfl, MvPowerSeries.subst_self]`. Both sides reduce to the same expression.
-/
theorem ev_pt (f : PS k m d) : ev (fun j => pt k (n := m) d j) f = f := by
  show MvPowerSeries.subst (fun p : Fin m × Fin d => (X p : PS k m d)) f = f
  rw [show (fun p : Fin m × Fin d => (X p : PS k m d)) = X from rfl, MvPowerSeries.subst_self]
  rfl

/- English proof (translation)
Introduce `j i` and use `MvPowerSeries.constantCoeff_X _`.
-/
theorem CZ.pt : CZ (fun j => pt k (n := n) d j) := fun j i => MvPowerSeries.constantCoeff_X _

/- English proof (translation)
Unfold `ev`. Conclude with `pderiv_subst (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f v`.
-/
theorem pderiv_ev {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d) :
    pderiv k v (ev a f) = ∑ p : Fin m × Fin d, ev a (pderiv k p f) * pderiv k v (a p.1 p.2) := by
  unfold ev
  exact pderiv_subst (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f v

/- English proof (translation)
Establish `hz : CZ (fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d))` using `fun _ _ => map_zero _`. Use extensionality with `e`. Unfold `ev`. Rewrite using `[coeff_subst hz.hasSubst, finsum_eq_single _ 0]`. Simplify using `[coeff_C, coeff_one]`.

Introduce `x hx`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p, x p ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hx (Finsupp.ext hc)`.

Rewrite using `[Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp) (zero_pow hp), map_zero, smul_zero]`.
-/
theorem ev_zeroFam (f : PS k m d) : ev (fun _ _ => (0 : PS k n d)) f = C (constantCoeff f) := by
  classical
  have hz : CZ (fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d)) := fun _ _ => map_zero _
  ext e
  unfold ev
  rw [coeff_subst hz.hasSubst, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro x hx
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp) (zero_pow hp), map_zero, smul_zero]

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
