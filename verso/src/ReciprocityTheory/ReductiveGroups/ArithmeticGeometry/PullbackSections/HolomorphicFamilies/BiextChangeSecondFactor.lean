import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogInv

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA

section Map

variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}

def mP {n : ℕ} (x : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map φ (x i)

def mV {m n : ℕ} (a : Fin m → Pt R n d) : Fin m → Pt k n d := fun j => mP φ (a j)

/- English proof (translation)
Introduce `f g h`. Use extensionality with `n`. Apply `hφ` to reduce the goal to its premises. Rewrite using `[← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, h]`.
-/
theorem mapInj (hφ : Function.Injective φ) {σ : Type} :
    Function.Injective (MvPowerSeries.map (σ := σ) φ) := by
  intro f g h
  ext n
  apply hφ
  rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, h]

/- English proof (translation)
Introduce `x y h`. Use function extensionality and compare the values at `i`. Conclude with `mapInj φ hφ (congrFun h i)`.
-/
theorem mPInj (hφ : Function.Injective φ) {n : ℕ} : Function.Injective (mP φ (n := n) (d := d)) := by
  intro x y h
  funext i
  exact mapInj φ hφ (congrFun h i)

/- English proof (translation)
Unfold `ev`. Rewrite using `[MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2))]`. Both sides reduce to the same expression.
-/
theorem map_ev' {m n : ℕ} {a : Fin m → Pt R n d} (ha : CZ a) (f : PS R m d) :
    MvPowerSeries.map φ (ev a f) = ev (mV φ a) (MvPowerSeries.map φ f) := by
  unfold ev
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2))]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `only [mV, Matrix.cons_val_zero]`. Simplify using `only [mV, Matrix.cons_val_succ]`.
-/
theorem mV_cons {m n : ℕ} (x : Pt R n d) (a : Fin m → Pt R n d) :
    mV φ (Matrix.vecCons x a) = Matrix.vecCons (mP φ x) (mV φ a) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [mV, Matrix.cons_val_zero]
  · simp only [mV, Matrix.cons_val_succ]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Conclude with `Fin.elim0 j`.
-/
theorem mV_nil {n : ℕ} : mV φ (![] : Fin 0 → Pt R n d) = ![] := by
  funext j
  exact Fin.elim0 j

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [mP, pt, MvPowerSeries.map_X]`.
-/
theorem mapPoint_pt {n : ℕ} (j : Fin n) : mP φ (pt R d j) = pt k d j := by
  funext i
  simp only [mP, pt, MvPowerSeries.map_X]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [mP, Pi.zero_apply, map_zero]`.
-/
theorem mapPoint_zero {n : ℕ} : mP φ (0 : Pt R n d) = 0 := by
  funext i
  simp only [mP, Pi.zero_apply, map_zero]

/- English proof (translation)
Simplify using `only [pt, MvPowerSeries.constantCoeff_X]`.
-/
theorem cc_pt' {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp only [pt, MvPowerSeries.constantCoeff_X]

/- English proof (translation)
Establish `hs` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2)`. Unfold `ev`. Rewrite using `[MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `e he`.

Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p, e p ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `he (Finsupp.ext hc)`. Rewrite using `[Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp), smul_zero]`.

Simplify using `[ha p.1 p.2, hp]`.
-/
private theorem cc_ev_lemma {m n : ℕ} {a : Fin m → Pt R n d} (ha : CZ a) (f : PS R m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2)
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact he (Finsupp.ext hc)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp), smul_zero]
    simp [ha p.1 p.2, hp]

/- English proof (translation)
Establish `hcz : CZ ![x]`. Introduce `j i`. Use `Fin.cases ?_ (fun j => Fin.elim0 j) j` and prove the remaining obligations. Simplify using `using hx i`. Use `show constantCoeff (ev ![x] (ψ i)) = 0`.

Rewrite using `[cc_ev_lemma hcz, hψ]`.
-/
theorem cc_comp1' {n : ℕ} {ψ : Pt R 1 d} {x : Pt R n d} (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (hx : ∀ i, constantCoeff (x i) = 0) (i : Fin d) : constantCoeff (comp1 ψ x i) = 0 := by
  have hcz : CZ ![x] := by
    intro j i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simpa using hx i
  show constantCoeff (ev ![x] (ψ i)) = 0
  rw [cc_ev_lemma hcz, hψ]

/- English proof (translation)
Establish `hcz : CZ ![x, y]`. Introduce `j i`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `using hx i`. Use `Fin.cases ?_ (fun j => Fin.elim0 j) j` and prove the remaining obligations.

Simplify using `using hy i`. Use `show constantCoeff (ev ![x, y] (F i)) = 0`. Rewrite using `[cc_ev_lemma hcz, hF]`.
-/
theorem cc_addOf' {n : ℕ} {F : Fin d → PS R 2 d} {x y : Pt R n d} (hF : ∀ i, constantCoeff (F i) = 0)
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0) (i : Fin d) :
    constantCoeff (addOf F x y i) = 0 := by
  have hcz : CZ ![x, y] := by
    intro j i
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hx i
    · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simpa using hy i
  show constantCoeff (ev ![x, y] (F i)) = 0
  rw [cc_ev_lemma hcz, hF]

/- English proof (translation)
Simplify using `only [CZ, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]`.
-/
theorem cz_cons_iff {m n : ℕ} {p : Pt R n d} {a : Fin m → Pt R n d} :
    CZ (Matrix.vecCons p a) ↔ (∀ i, constantCoeff (p i) = 0) ∧ CZ a := by
  simp only [CZ, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]

/- English proof (translation)
Conclude with `⟨fun _ => trivial, fun _ j => Fin.elim0 j⟩`.
-/
theorem cz_nil' {n : ℕ} : CZ (![] : Fin 0 → Pt R n d) ↔ True := by
  exact ⟨fun _ => trivial, fun _ j => Fin.elim0 j⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hcz : CZ ![x]` using `cz_cons_iff.2 ⟨hx, cz_nil'.2 trivial⟩`. Use `show MvPowerSeries.map φ (ev ![x] (ψ i)) = ev ![mP φ x] (MvPowerSeries.map φ (ψ i))`. Rewrite using `[map_ev' φ hcz, mV_cons, mV_nil]`.
-/
theorem mapPoint_comp1 {n : ℕ} (ψ : Pt R 1 d) {x : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0) :
    mP φ (comp1 ψ x) = comp1 (mP φ ψ) (mP φ x) := by
  funext i
  have hcz : CZ ![x] := cz_cons_iff.2 ⟨hx, cz_nil'.2 trivial⟩
  show MvPowerSeries.map φ (ev ![x] (ψ i)) = ev ![mP φ x] (MvPowerSeries.map φ (ψ i))
  rw [map_ev' φ hcz, mV_cons, mV_nil]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hcz : CZ ![x, y]` using `cz_cons_iff.2 ⟨hx, cz_cons_iff.2 ⟨hy, cz_nil'.2 trivial⟩⟩`. Use `show MvPowerSeries.map φ (ev ![x, y] (F i)) = ev ![mP φ x, mP φ y] (MvPowerSeries.map φ (F i))`. Rewrite using `[map_ev' φ hcz, mV_cons, mV_cons, mV_nil]`.
-/
theorem mapPoint_addOf {n : ℕ} (F : Fin d → PS R 2 d) {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) : mP φ (addOf F x y) = addOf (mP φ F) (mP φ x) (mP φ y) := by
  funext i
  have hcz : CZ ![x, y] := cz_cons_iff.2 ⟨hx, cz_cons_iff.2 ⟨hy, cz_nil'.2 trivial⟩⟩
  show MvPowerSeries.map φ (ev ![x, y] (F i)) = ev ![mP φ x, mP φ y] (MvPowerSeries.map φ (F i))
  rw [map_ev' φ hcz, mV_cons, mV_cons, mV_nil]

end Map

section Comparison₂

variable {R k O : Type} [CommRing R] [CommRing k] [CommRing O] [StarRing O] (φ : R →+* k) {d : ℕ}

structure IntTie (B : FB k d O) where
  FT : Pt R 2 d
  actT : O → Pt R 1 d
  ph1T : PS R 3 d
  ph2T : PS R 3 d
  syT : PS R 2 d
  adT : O → PS R 2 d
  hF : mP φ FT = B.G.F
  hA : ∀ a, mP φ (actT a) = B.A.act a
  h1 : MvPowerSeries.map φ ph1T = B.ph1
  h2 : MvPowerSeries.map φ ph2T = B.ph2
  hs : MvPowerSeries.map φ syT = B.sy
  had : ∀ a, MvPowerSeries.map φ (adT a) = B.ad a

variable {φ} {B : FB k d O} (t : IntTie φ B) (hφ : Function.Injective φ)

include hφ in
/- English proof (translation)
Establish `h1 : MvPowerSeries.map φ (t.FT i) = B.G.F i` using `congrFun t.hF i`. Establish `h2` using `congrArg (fun f => MvPowerSeries.constantCoeff f) h1`. Simplify using `only [MvPowerSeries.constantCoeff_map, B.G.const i] at h2`. Conclude with `hφ (h2.trans (map_zero φ).symm)`.
-/
theorem IntTie.hFc (i : Fin d) : constantCoeff (t.FT i) = 0 := by
  have h1 : MvPowerSeries.map φ (t.FT i) = B.G.F i := congrFun t.hF i
  have h2 := congrArg (fun f => MvPowerSeries.constantCoeff f) h1
  simp only [MvPowerSeries.constantCoeff_map, B.G.const i] at h2
  exact hφ (h2.trans (map_zero φ).symm)

include hφ in
/- English proof (translation)
Establish `h1 : MvPowerSeries.map φ (t.actT a i) = B.A.act a i` using `congrFun (t.hA a) i`. Establish `h2` using `congrArg (fun f => MvPowerSeries.constantCoeff f) h1`. Simplify using `only [MvPowerSeries.constantCoeff_map, B.A.const a i] at h2`. Conclude with `hφ (h2.trans (map_zero φ).symm)`.
-/
theorem IntTie.hAc (a : O) (i : Fin d) : constantCoeff (t.actT a i) = 0 := by
  have h1 : MvPowerSeries.map φ (t.actT a i) = B.A.act a i := congrFun (t.hA a) i
  have h2 := congrArg (fun f => MvPowerSeries.constantCoeff f) h1
  simp only [MvPowerSeries.constantCoeff_map, B.A.const a i] at h2
  exact hφ (h2.trans (map_zero φ).symm)

/- English proof (translation)
Conclude with `congrFun t.hF i`.
-/
theorem IntTie.hFi (i : Fin d) : MvPowerSeries.map φ (t.FT i) = B.G.F i := by
  exact congrFun t.hF i

end Comparison₂

section Pull

variable {R k O : Type} [CommRing R] [CommRing k] [CommRing O] [StarRing O] {φ : R →+* k} {d : ℕ}
variable {B : FB k d O} (t : IntTie φ B) (hφ : Function.Injective φ)

def lawOf : FGLaw R d where
  F := t.FT
  const := t.hFc hφ
  unit i := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, ]
    exact B.G.unit i
  comm i := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, ]
    exact B.G.comm i
  assoc i := by
    show ev (n := 3) ![addOf t.FT (pt R d 0) (pt R d 1), pt R d 2] (t.FT i) =
      ev (n := 3) ![pt R d 0, addOf t.FT (pt R d 1) (pt R d 2)] (t.FT i)
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, ]
    exact B.G.assoc i

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lawOf_F : (lawOf t hφ).F = t.FT := rfl

def actOf : OAct O (lawOf t hφ) where
  act := t.actT
  const := t.hAc hφ
  hom a := by
    apply mPInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, ]
    exact B.A.hom a
  add_act a b := by
    apply mPInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, ]
    exact B.A.add_act a b
  mul_act a b := by
    apply mPInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, ]
    exact B.A.mul_act a b
  one_act := by
    apply mPInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, ]
    exact B.A.one_act

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem actOf_act : (actOf t hφ).act = t.actT := rfl

def fbOf : FB R d O where
  G := lawOf t hφ
  A := actOf t hφ
  ph1 := t.ph1T
  ph2 := t.ph2T
  sy := t.syT
  ad := t.adT
  cocycleLeft_zero_fst := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleLeft_zero_fst
  cocycleLeft_zero_snd := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleLeft_zero_snd
  cocycleLeft_zero_thd := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleLeft_zero_thd
  cocycleRight_zero_fst := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleRight_zero_fst
  cocycleRight_zero_snd := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleRight_zero_snd
  cocycleRight_zero_thd := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleRight_zero_thd
  symmetry_zero_fst := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.symmetry_zero_fst
  symmetry_zero_snd := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.symmetry_zero_snd
  adjoint_zero_fst a := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.adjoint_zero_fst a
  adjoint_zero_snd a := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.adjoint_zero_snd a
  cocycleLeft_assoc := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleLeft_assoc
  cocycleLeft_comm := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleLeft_comm
  cocycleRight_assoc := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleRight_assoc
  cocycleRight_comm := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.cocycleRight_comm
  interchange := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.interchange
  sy_inv := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.sy_inv
  sy_law := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.sy_law
  adjoint_compat_left a := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.adjoint_compat_left a
  adjoint_compat_right a := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.adjoint_compat_right a
  ad_sy a := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.ad_sy a
  ad_one := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.ad_one
  ad_mul a b := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.ad_mul a b
  ad_add a b := by
    apply mapInj φ hφ
    simp (disch := simp [cz_cons_iff, cz_nil', cc_pt', cc_addOf', cc_comp1', t.hFc hφ, t.hAc hφ]) only
      [map_mul, map_one, map_X, map_ev' φ, mV_cons, mV_nil, mapPoint_pt, mapPoint_zero, mapPoint_comp1 φ, mapPoint_addOf φ, t.hF, t.hA,
        t.hFi, t.h1, t.h2, t.hs, t.had, FGLaw.add, lawOf_F, actOf_act]
    exact B.ad_add a b

end Pull

section Gauge

variable {R k O : Type} [CommRing R] [CommRing k] [Algebra ℚ k] [Algebra R k] [CommRing O] [StarRing O] {d : ℕ}
variable {B : FB k d O} (t : IntTie (algebraMap R k) B) (hφ : Function.Injective (algebraMap R k))

/- English proof (translation)
Use extensionality with `n`. Simplify using `[MvPowerSeries.coeff_map]`.
-/
theorem map_self {n : ℕ} (f : PS k n d) : MvPowerSeries.map (algebraMap k k) f = f := by
  ext n
  simp [MvPowerSeries.coeff_map]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `map_self (B.G.F i)`.
-/
theorem FK_self (B : FB k d O) : B.FK k = B.G.F := by
  funext i
  exact map_self (B.G.F i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `map_self (B.A.act a i)`.
-/
theorem actK_self (B : FB k d O) (a : O) : B.actK k a = B.A.act a := by
  funext i
  exact map_self (B.A.act a i)

/- English proof (translation)
Rewrite using `[FK_self B]`. Use function extensionality and compare the values at `i`. Conclude with `t.hFi i`.
-/
theorem fbOf_FK : (fbOf t hφ).FK k = B.FK k := by
  rw [FK_self B]
  funext i
  exact t.hFi i

/- English proof (translation)
Rewrite using `[actK_self B]`. Use function extensionality and compare the values at `i`. Conclude with `congrFun (t.hA a) i`.
-/
theorem fbOf_actK (a : O) : (fbOf t hφ).actK k a = B.actK k a := by
  rw [actK_self B]
  funext i
  exact congrFun (t.hA a) i

/- English proof (translation)
Use `show MvPowerSeries.map (algebraMap R k) t.ph1T = MvPowerSeries.map (algebraMap k k) B.ph1`. Rewrite using `[map_self]`. Conclude with `t.h1`.
-/
theorem biext_change_first_factor : FB.toK k (fbOf t hφ).ph1 = FB.toK k B.ph1 := by
  show MvPowerSeries.map (algebraMap R k) t.ph1T = MvPowerSeries.map (algebraMap k k) B.ph1
  rw [map_self]
  exact t.h1

/- English proof (translation)
Use `show MvPowerSeries.map (algebraMap R k) t.ph2T = MvPowerSeries.map (algebraMap k k) B.ph2`. Rewrite using `[map_self]`. Conclude with `t.h2`.
-/
theorem biext_change_second_factor : FB.toK k (fbOf t hφ).ph2 = FB.toK k B.ph2 := by
  show MvPowerSeries.map (algebraMap R k) t.ph2T = MvPowerSeries.map (algebraMap k k) B.ph2
  rw [map_self]
  exact t.h2

/- English proof (translation)
Use `show MvPowerSeries.map (algebraMap R k) t.syT = MvPowerSeries.map (algebraMap k k) B.sy`. Rewrite using `[map_self]`. Conclude with `t.hs`.
-/
theorem fbOf_toKs : FB.toK k (fbOf t hφ).sy = FB.toK k B.sy := by
  show MvPowerSeries.map (algebraMap R k) t.syT = MvPowerSeries.map (algebraMap k k) B.sy
  rw [map_self]
  exact t.hs

/- English proof (translation)
Use `show MvPowerSeries.map (algebraMap R k) (t.adT a) = MvPowerSeries.map (algebraMap k k) (B.ad a)`. Rewrite using `[map_self]`. Conclude with `t.had a`.
-/
theorem fbOf_toKad (a : O) : FB.toK k ((fbOf t hφ).ad a) = FB.toK k (B.ad a) := by
  show MvPowerSeries.map (algebraMap R k) (t.adT a) = MvPowerSeries.map (algebraMap k k) (B.ad a)
  rw [map_self]
  exact t.had a

/- English proof (translation)
Unfold `FB.nabVal FB.hL`. Rewrite using `[fbOf_FK, fbOf_actK]`.
-/
theorem fbOf_nabVal (h : PS k 2 d) (w0 : O) (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) : (fbOf t hφ).nabVal k h w0 m f u P = B.nabVal k h w0 m f u P := by
  unfold FB.nabVal FB.hL
  rw [fbOf_FK, fbOf_actK]

/- English proof (translation)
Use `⟨hB.ax0, hB.ax1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[biext_change_first_factor, fbOf_FK]`. Conclude with `hB.ph1`. Rewrite using `[biext_change_second_factor, fbOf_FK]`. Conclude with `hB.ph2`.

Rewrite using `[fbOf_toKs]`. Conclude with `hB.sy`. Introduce `a`. Rewrite using `[fbOf_toKad, fbOf_actK, fbOf_actK]`. Conclude with `hB.ad a`.
-/
theorem fbOf_canon (h : PS k 2 d) (hB : B.IsCanonGauge k h) : (fbOf t hφ).IsCanonGauge k h := by
  refine ⟨hB.ax0, hB.ax1, ?_, ?_, ?_, ?_⟩
  · rw [biext_change_first_factor, fbOf_FK]; exact hB.ph1
  · rw [biext_change_second_factor, fbOf_FK]; exact hB.ph2
  · rw [fbOf_toKs]; exact hB.sy
  · intro a; rw [fbOf_toKad, fbOf_actK, fbOf_actK]; exact hB.ad a

end Gauge

end ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
