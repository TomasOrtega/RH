import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.OneCosetBF

variable {D : D7}

/- English proof (translation)
Break down `eq_or_ne i j with rfl | hij` into its components or cases. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]`. Rewrite using `[Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]`.
-/
theorem one_quot_apply {n : ℕ} (I : Ideal (AE D)) (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (AE D ⧸ I)) i j = Ideal.Quotient.mk I ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

/- English proof (translation)
Simplify using `only [GlobalTheory.FinPl.congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff, Units.val_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Rewrite `this` using `[one_quot_apply]`.

Conclude with `Ideal.Quotient.eq.1 this`. Introduce `h`. Use extensionality with `i j`. Rewrite using `[one_quot_apply]`. Conclude with `Ideal.Quotient.eq.2 (h i j)`.
-/
theorem mem_congGrp_iff {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ GlobalTheory.FinPl.congGrp V I ↔
      ∀ i j, Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  simp only [GlobalTheory.FinPl.congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff, Units.val_one]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rw [one_quot_apply] at this
    exact Ideal.Quotient.eq.1 this
  · intro h
    ext i j
    rw [one_quot_apply]
    exact Ideal.Quotient.eq.2 (h i j)

end GlobalTheory.OneCosetBF

namespace GlobalTheory.OneCosetBF

variable {D : D7}

open GlobalTheory.FinPl in
/- English proof (translation)
Introduce `a ha`. Simplify using `only [idAt, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢`. Conclude with `⟨ha.1, fun w => ha.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩`.
-/
theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  simp only [idAt, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩

open GlobalTheory.FinPl in
/- English proof (translation)
Introduce `a ha`. Simplify using `only [idOff, Ideal.mem_iInf] at ha ⊢`. Conclude with `fun w => ha ⟨w.1, h _ w.2⟩`.
-/
theorem idOff_mono {P Q : Pl D → Prop} (h : ∀ w, Q w → P w) : idOff D P ≤ idOff D Q := by
  intro a ha
  simp only [idOff, Ideal.mem_iInf] at ha ⊢
  exact fun w => ha ⟨w.1, h _ w.2⟩

open GlobalTheory.FinPl in
/- English proof (translation)
Introduce `a ha`. Simplify using `only [idAt, idOff, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢`. Conclude with `fun w => ha.2 ⟨w.1, h _ w.2⟩`.
-/
theorem idAt_le_idOff {P Q : Pl D → Prop} (h : ∀ w, Q w → ¬ P w) : idAt D P ≤ idOff D Q := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, h _ w.2⟩

open GlobalTheory.FinPl in
/- English proof (translation)
Introduce `a ha`. Simplify using `only [idAt, idOff, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢`. Use `⟨ha.1.1, fun w => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hq : Q w.1`. Conclude with `ha.2 ⟨w.1, hq⟩`.

Conclude with `ha.1.2 ⟨w.1, fun hp => w.2 (h _ hp hq)⟩`.
-/
theorem idAt_inf_idOff {P Q R : Pl D → Prop} (h : ∀ w, P w → ¬ Q w → R w) : idAt D P ⊓ idOff D Q ≤ idAt D R := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  refine ⟨ha.1.1, fun w => ?_⟩
  by_cases hq : Q w.1
  · exact ha.2 ⟨w.1, hq⟩
  · exact ha.1.2 ⟨w.1, fun hp => w.2 (h _ hp hq)⟩

/- English proof (translation)
Introduce `_ hg` and use `mem_congGrp_iff.2 fun i j => h (mem_congGrp_iff.1 hg i j)`.
-/
theorem congGrp_mono {V : HSp D} {I J : Ideal (AE D)} (h : I ≤ J) : GlobalTheory.FinPl.congGrp V I ≤ GlobalTheory.FinPl.congGrp V J :=
  fun _ hg => mem_congGrp_iff.2 fun i j => h (mem_congGrp_iff.1 hg i j)

/- English proof (translation)
The claim follows from `mem_congGrp_iff.2 fun i j => ⟨mem_congGrp_iff.1 hI i j, mem_congGrp_iff.1 hJ i j⟩`.
-/
theorem congGrp_inf {V : HSp D} {I J : Ideal (AE D)} {g : GA D V} (hI : g ∈ GlobalTheory.FinPl.congGrp V I)
    (hJ : g ∈ GlobalTheory.FinPl.congGrp V J) : g ∈ GlobalTheory.FinPl.congGrp V (I ⊓ J) :=
  mem_congGrp_iff.2 fun i j => ⟨mem_congGrp_iff.1 hI i j, mem_congGrp_iff.1 hJ i j⟩

/- English proof (translation)
Establish `e : N ⬝ M ⬝ Y - N ⬝ Y = N ⬝ (M - 1) ⬝ Y`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]`. Rewrite using `[e]`. Simplify using `only [Matrix.mul_apply]`. Use `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ ?_)` and prove the remaining obligations.

Simplify `hM q l` using `only [Matrix.sub_apply]`.
-/
theorem mul_sub_mem {I : Ideal (AE D)} {k m n : ℕ} {M : Matrix (Fin m) (Fin m) (AE D)}
    (hM : ∀ i j, M i j - (1 : Matrix (Fin m) (Fin m) (AE D)) i j ∈ I) (N : Matrix (Fin k) (Fin m) (AE D))
    (Y : Matrix (Fin m) (Fin n) (AE D)) (i : Fin k) (j : Fin n) : (N ⬝ M ⬝ Y - N ⬝ Y) i j ∈ I := by
  have e : N ⬝ M ⬝ Y - N ⬝ Y = N ⬝ (M - 1) ⬝ Y := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [e]
  simp only [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ ?_)
  simpa only [Matrix.sub_apply] using hM q l

variable {W : HSp D} {ρ : ℕ}

/- English proof (translation)
Introduce `i j`. Establish `h1` using `mul_sub_mem (mem_congGrp_iff.1 (inv_mem hg')) (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) (Formalism.L2.Theta.mt W gv⁻¹ ⬝ X) i j`. Simplify using `only [Matrix.one_mul] at h1`. Establish `e : Formalism.L2.Theta.mt W gv⁻¹ ⬝ X - x - a = (Formalism.L2.Theta.mt W (gv * g')⁻¹ ⬝ X - x - a) - (Formalism.L2.Theta.mt W g'⁻¹ ⬝ (Formalism.L2.Theta.mt W gv⁻¹ ⬝ X) - Formalism.L2.Theta.mt W gv⁻¹ ⬝ X)`. Rewrite using `[_root_.mul_inv_rev, mt_mul, Matrix.mul_assoc]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e, Matrix.sub_apply]`. Conclude with `Ideal.sub_mem _ (h i j) h1`.
-/
theorem off_left {P : GlobalTheory.FinPl.Pl D → Prop} {gv g' : GA D W} (hg' : g' ∈ GlobalTheory.FinPl.congGrp W (GlobalTheory.FinPl.idOff D P))
    {X x a : Mx D W.rank ρ} (h : MxOff P (Formalism.L2.Theta.mt W (gv * g')⁻¹ ⬝ X - x - a)) :
    MxOff P (Formalism.L2.Theta.mt W gv⁻¹ ⬝ X - x - a) := by
  intro i j
  have h1 := mul_sub_mem (mem_congGrp_iff.1 (inv_mem hg')) (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) (Formalism.L2.Theta.mt W gv⁻¹ ⬝ X) i j
  simp only [Matrix.one_mul] at h1
  have e : Formalism.L2.Theta.mt W gv⁻¹ ⬝ X - x - a =
      (Formalism.L2.Theta.mt W (gv * g')⁻¹ ⬝ X - x - a) -
        (Formalism.L2.Theta.mt W g'⁻¹ ⬝ (Formalism.L2.Theta.mt W gv⁻¹ ⬝ X) - Formalism.L2.Theta.mt W gv⁻¹ ⬝ X) := by
    rw [_root_.mul_inv_rev, mt_mul, Matrix.mul_assoc]; abel
  rw [e, Matrix.sub_apply]
  exact Ideal.sub_mem _ (h i j) h1

/- English proof (translation)
Introduce `i j`. Establish `h1` using `mul_sub_mem (mem_congGrp_iff.1 (inv_mem hgv)) (Formalism.L2.Theta.mt W g'⁻¹) X i j`. Establish `e : Formalism.L2.Theta.mt W g'⁻¹ ⬝ X - x - a = (Formalism.L2.Theta.mt W (gv * g')⁻¹ ⬝ X - x - a) - (Formalism.L2.Theta.mt W g'⁻¹ * Formalism.L2.Theta.mt W gv⁻¹ ⬝ X - Formalism.L2.Theta.mt W g'⁻¹ ⬝ X)`. Rewrite using `[_root_.mul_inv_rev, mt_mul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e, Matrix.sub_apply]`. Conclude with `Ideal.sub_mem _ (h i j) h1`.
-/
theorem off_right {P : GlobalTheory.FinPl.Pl D → Prop} {gv g' : GA D W} (hgv : gv ∈ GlobalTheory.FinPl.congGrp W (GlobalTheory.FinPl.idOff D P))
    {X x a : Mx D W.rank ρ} (h : MxOff P (Formalism.L2.Theta.mt W (gv * g')⁻¹ ⬝ X - x - a)) :
    MxOff P (Formalism.L2.Theta.mt W g'⁻¹ ⬝ X - x - a) := by
  intro i j
  have h1 := mul_sub_mem (mem_congGrp_iff.1 (inv_mem hgv)) (Formalism.L2.Theta.mt W g'⁻¹) X i j
  have e : Formalism.L2.Theta.mt W g'⁻¹ ⬝ X - x - a =
      (Formalism.L2.Theta.mt W (gv * g')⁻¹ ⬝ X - x - a) -
        (Formalism.L2.Theta.mt W g'⁻¹ * Formalism.L2.Theta.mt W gv⁻¹ ⬝ X - Formalism.L2.Theta.mt W g'⁻¹ ⬝ X) := by
    rw [_root_.mul_inv_rev, mt_mul]; abel
  rw [e, Matrix.sub_apply]
  exact Ideal.sub_mem _ (h i j) h1

/- English proof (translation)
Introduce `i j` and use `idOff_mono h (hy i j)`.
-/
theorem mxOff_mono {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ w, Q w → P w) {m n : ℕ} {y : Mx D m n} (hy : MxOff P y) :
    MxOff Q y := fun i j => idOff_mono h (hy i j)

end GlobalTheory.OneCosetBF

namespace GlobalTheory.OneCosetBF

variable {D : D7}

/- English proof (translation)
Use `revert loc`. Proceed by induction on `ht using Finset.Nonempty.cons_induction with`. Consider the case `singleton v`. Introduce `loc g hg hc`. Simplify using `only [Finset.mem_singleton] at hg hc loc ⊢`.

Conclude with `loc v rfl g hg hc`. Consider the case `cons v t hv ht ih`. Introduce `loc g hg hc`. Take `⟨u, a, ha, hc⟩` from `hc`. Take `⟨gv, hgv, g', hg', rfl⟩` from `((GlobalTheory.FinPl.localComponents D (· = v)).2 W).1 g`.

Establish `hcomm` using `((GlobalTheory.FinPl.localComponents D (· = v)).2 W).2.1`. Establish `hsub : ∀ w, w ∈ t → ¬ (w = v)` using `fun w hw e => hv (e ▸ hw)`. Establish `hvt : grpAt W (· = v) ≤ grpAt W (· ∈ Finset.cons v t hv)` using `congGrp_mono (idAt_mono fun w hw => hw ▸ Finset.mem_cons_self v t)`. Establish `htt : grpAt W (· ∈ t) ≤ grpAt W (· ∈ Finset.cons v t hv)` using `congGrp_mono (idAt_mono fun w hw => Finset.mem_cons.2 (Or.inr hw))`. Establish `ht_off : grpAt W (· ∈ t) ≤ grpOff W (· = v)` using `congGrp_mono (idAt_le_idOff fun w hw hwt => hsub w hwt hw)`.

Establish `hv_off : grpAt W (· = v) ≤ grpOff W (· ∈ t)` using `congGrp_mono (idAt_le_idOff fun w hw hwv => hsub w hw hwv)`. Establish `hg'1 : g' ∈ grpAt W (· ∈ t)`. Establish `h1 : g' ∈ grpAt W (· ∈ Finset.cons v t hv)`. Use `mul_mem (inv_mem (hvt hgv)) hg` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_left]`. Then use the resulting hypothesis.

Conclude with `congGrp_mono (idAt_inf_idOff fun w hw hnv => (Finset.mem_cons.1 hw).resolve_left hnv) (congGrp_inf h1 hg')`. Establish `hcv : MxOff (· = v) (Formalism.L2.Theta.mt W gv⁻¹ ⬝ (x ⬝ u.1.1) - x - a)` using `off_left hg' (mxOff_mono (fun w hw => hw ▸ Finset.mem_cons_self v t) hc)`. Establish `hct : MxOff (· ∈ t) (Formalism.L2.Theta.mt W g'⁻¹ ⬝ (x ⬝ u.1.1) - x - a)` using `off_right (hv_off hgv) (mxOff_mono (fun w hw => Finset.mem_cons.2 (Or.inr hw)) hc)`. Take `⟨rv, hrv, hrv', kv, hkv, hkv', rfl⟩` from `loc v (Finset.mem_cons_self v t) gv hgv ⟨u, a, ha, hcv⟩`. Take `⟨r', hr', hr'', k', hk', hk'', rfl⟩` from `ih (fun w hw => loc w (Finset.mem_cons.2 (Or.inr hw))) g' hg'1 ⟨u, a, ha, hct⟩`.

Use `⟨rv * r', mul_mem hrv hr', mul_mem (hvt hrv') (htt hr''), kv * k', mul_mem hkv hk', mul_mem (hvt hkv') (htt hk''), ?_⟩` and prove the remaining obligations. Establish `hc'` using `hcomm kv hkv' r' (ht_off hr'')`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem assemble (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (A : AddSubgroup (Mx D W.rank ρ)) (K : Subgroup (GA D W))
    (t : Finset (GlobalTheory.FinPl.Pl D)) (ht : t.Nonempty)
    (loc : ∀ v ∈ t, ∀ g ∈ grpAt W (· = v),
      (∃ u : UX D ρ, ∃ a ∈ A, MxOff (· = v) (Formalism.L2.Theta.mt W g⁻¹ ⬝ (x ⬝ u.1.1) - x - a)) →
        ∃ r ∈ Rgrp W x, r ∈ grpAt W (· = v) ∧ ∃ k ∈ K, k ∈ grpAt W (· = v) ∧ g = r * k) :
    ∀ g ∈ grpAt W (· ∈ t),
      (∃ u : UX D ρ, ∃ a ∈ A, MxOff (· ∈ t) (Formalism.L2.Theta.mt W g⁻¹ ⬝ (x ⬝ u.1.1) - x - a)) →
        ∃ r ∈ Rgrp W x, r ∈ grpAt W (· ∈ t) ∧ ∃ k ∈ K, k ∈ grpAt W (· ∈ t) ∧ g = r * k := by
  revert loc
  induction ht using Finset.Nonempty.cons_induction with
  | singleton v =>
    intro loc g hg hc
    simp only [Finset.mem_singleton] at hg hc loc ⊢
    exact loc v rfl g hg hc
  | cons v t hv ht ih =>
    intro loc g hg hc
    obtain ⟨u, a, ha, hc⟩ := hc
    obtain ⟨gv, hgv, g', hg', rfl⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).1 g
    have hcomm := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).2.1
    have hsub : ∀ w, w ∈ t → ¬ (w = v) := fun w hw e => hv (e ▸ hw)
    have hvt : grpAt W (· = v) ≤ grpAt W (· ∈ Finset.cons v t hv) :=
      congGrp_mono (idAt_mono fun w hw => hw ▸ Finset.mem_cons_self v t)
    have htt : grpAt W (· ∈ t) ≤ grpAt W (· ∈ Finset.cons v t hv) :=
      congGrp_mono (idAt_mono fun w hw => Finset.mem_cons.2 (Or.inr hw))
    have ht_off : grpAt W (· ∈ t) ≤ grpOff W (· = v) :=
      congGrp_mono (idAt_le_idOff fun w hw hwt => hsub w hwt hw)
    have hv_off : grpAt W (· = v) ≤ grpOff W (· ∈ t) :=
      congGrp_mono (idAt_le_idOff fun w hw hwv => hsub w hw hwv)
    have hg'1 : g' ∈ grpAt W (· ∈ t) := by
      have h1 : g' ∈ grpAt W (· ∈ Finset.cons v t hv) := by
        have := mul_mem (inv_mem (hvt hgv)) hg
        rwa [inv_mul_cancel_left] at this
      exact congGrp_mono (idAt_inf_idOff fun w hw hnv => (Finset.mem_cons.1 hw).resolve_left hnv)
        (congGrp_inf h1 hg')
    have hcv : MxOff (· = v) (Formalism.L2.Theta.mt W gv⁻¹ ⬝ (x ⬝ u.1.1) - x - a) :=
      off_left hg' (mxOff_mono (fun w hw => hw ▸ Finset.mem_cons_self v t) hc)
    have hct : MxOff (· ∈ t) (Formalism.L2.Theta.mt W g'⁻¹ ⬝ (x ⬝ u.1.1) - x - a) :=
      off_right (hv_off hgv) (mxOff_mono (fun w hw => Finset.mem_cons.2 (Or.inr hw)) hc)
    obtain ⟨rv, hrv, hrv', kv, hkv, hkv', rfl⟩ := loc v (Finset.mem_cons_self v t) gv hgv ⟨u, a, ha, hcv⟩
    obtain ⟨r', hr', hr'', k', hk', hk'', rfl⟩ :=
      ih (fun w hw => loc w (Finset.mem_cons.2 (Or.inr hw))) g' hg'1 ⟨u, a, ha, hct⟩
    refine ⟨rv * r', mul_mem hrv hr', mul_mem (hvt hrv') (htt hr''), kv * k', mul_mem hkv hk',
      mul_mem (hvt hkv') (htt hk''), ?_⟩
    have hc' := hcomm kv hkv' r' (ht_off hr'')
    calc rv * kv * (r' * k') = rv * (kv * r') * k' := by simp only [mul_assoc]
      _ = rv * (r' * kv) * k' := by rw [hc']
      _ = rv * r' * (kv * k') := by simp only [mul_assoc]

end GlobalTheory.OneCosetBF
