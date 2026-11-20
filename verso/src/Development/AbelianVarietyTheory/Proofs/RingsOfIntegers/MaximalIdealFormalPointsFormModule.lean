import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AddCharMemValuationSubring
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

set_option autoImplicit false
noncomputable section
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.PlaceInt.FormalPts

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {d : ℕ}

def SmallPt {n : ℕ} (x : Pt V n d) : Prop := ∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V

def subPt {m n : ℕ} (a : Fin m → Pt V n d) (p : Pt V m d) : Pt V n d := fun i => evV a (p i)

/- English proof (translation)
Introduce `j`. Use `fin_cases j`. Simplify using `using hx`.
-/
theorem small_one {n : ℕ} {x : Pt V n d} (hx : SmallPt x) : ∀ j, SmallPt (![x] j) := by
  intro j
  fin_cases j
  simpa using hx

/- English proof (translation)
Introduce `j`. Use `fin_cases j`. Simplify using `using hx`. Simplify using `using hy`.
-/
theorem small_two {n : ℕ} {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) : ∀ j, SmallPt (![x, y] j) := by
  intro j
  fin_cases j
  · simpa using hx
  · simpa using hy

/- English proof (translation)
Introduce `j`. Use `fin_cases j`. Simplify using `using hx`. Simplify using `using hy`. Simplify using `using hz`.
-/
theorem small_three {n : ℕ} {x y z : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) (hz : SmallPt z) :
    ∀ j, SmallPt (![x, y, z] j) := by
  intro j
  fin_cases j
  · simpa using hx
  · simpa using hy
  · simpa using hz

variable [IsAdicComplete (maximalIdeal V) V] [CharZero V]

/- English proof (translation)
Establish `S` using `evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)`. Conclude with `S.2.1 f (by rw [hf]; exact zero_mem _)`.
-/
theorem small_evV {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (f : PS V m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (evV a f) ∈ maximalIdeal V := by
  have S := evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  exact S.2.1 f (by rw [hf]; exact zero_mem _)

/- English proof (translation)
Establish `hb' : ∀ p : Fin l × Fin d, MvPowerSeries.constantCoeff (b p.1 p.2) ∈ maximalIdeal V` using `fun p => by`. Rewrite using `[hb p.1 p.2]`. Conclude with `zero_mem _`. Establish `S` using `evC_spec V (Fin l × Fin d) (Fin m × Fin d) (Fin n × Fin d) (fun p => b p.1 p.2) hb'`. Establish `e1 : ev b f = evC (fun p : Fin l × Fin d => b p.1 p.2) f` using `(S.2.2.1 (fun p => hb p.1 p.2) f).symm`.

Rewrite using `[e1]`. Conclude with `S.2.2.2 (fun p => a p.1 p.2) (fun p => ha p.1 p.2) f`.
-/
theorem evV_ev {l m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (b : Fin l → Pt V m d)
    (hb : ∀ j, GP (b j)) (f : PS V l d) : evV a (ev b f) = evV (fun j => subPt a (b j)) f := by
  have hb' : ∀ p : Fin l × Fin d, MvPowerSeries.constantCoeff (b p.1 p.2) ∈ maximalIdeal V := fun p => by
    rw [hb p.1 p.2]
    exact zero_mem _
  have S := evC_spec V (Fin l × Fin d) (Fin m × Fin d) (Fin n × Fin d) (fun p => b p.1 p.2) hb'
  have e1 : ev b f = evC (fun p : Fin l × Fin d => b p.1 p.2) f := (S.2.2.1 (fun p => hb p.1 p.2) f).symm
  rw [e1]
  exact S.2.2.2 (fun p => a p.1 p.2) (fun p => ha p.1 p.2) f

/- English proof (translation)
Use function extensionality and compare the values at `i`. Take `⟨⟨ψ, hX, hψ⟩, -⟩` from `evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)`. Use `show evC (fun p : Fin m × Fin d => a p.1 p.2) (MvPowerSeries.X (j, i)) = a j i`. Rewrite using `[hψ, hX]`.
-/
theorem subPt_pt {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (j : Fin m) :
    subPt a (pt V d j) = a j := by
  funext i
  obtain ⟨⟨ψ, hX, hψ⟩, -⟩ :=
    evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  show evC (fun p : Fin m × Fin d => a p.1 p.2) (MvPowerSeries.X (j, i)) = a j i
  rw [hψ, hX]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Take `⟨⟨ψ, -, hψ⟩, -⟩` from `evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)`. Use `show evC (fun p : Fin m × Fin d => a p.1 p.2) 0 = 0`. Rewrite using `[hψ, map_zero]`.
-/
theorem subPt_zero {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) :
    subPt a (0 : Pt V m d) = 0 := by
  funext i
  obtain ⟨⟨ψ, -, hψ⟩, -⟩ :=
    evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  show evC (fun p : Fin m × Fin d => a p.1 p.2) 0 = 0
  rw [hψ, map_zero]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show evV a (ev ![p, q] (F i)) = evV ![subPt a p, subPt a q] (F i)`. Rewrite using `[evV_ev a ha ![p, q] (pair_points_zero_constant hp hq) (F i)]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Apply the tactic sequence `fin_cases j <;> rfl`.
-/
theorem subPt_addOf {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (F : Fin d → PS V 2 d)
    (p q : Pt V m d) (hp : GP p) (hq : GP q) :
    subPt a (addOf F p q) = addV F (subPt a p) (subPt a q) := by
  funext i
  show evV a (ev ![p, q] (F i)) = evV ![subPt a p, subPt a q] (F i)
  rw [evV_ev a ha ![p, q] (pair_points_zero_constant hp hq) (F i)]
  congr 1
  funext j
  fin_cases j <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show evV a (ev ![p] (φ i)) = evV ![subPt a p] (φ i)`. Rewrite using `[evV_ev a ha ![p] (single_point_zero_constant hp) (φ i)]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Use `fin_cases j`. Both sides reduce to the same expression.
-/
theorem subPt_comp1 {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (φ : Pt V 1 d)
    (p : Pt V m d) (hp : GP p) : subPt a (comp1 φ p) = compV φ (subPt a p) := by
  funext i
  show evV a (ev ![p] (φ i)) = evV ![subPt a p] (φ i)
  rw [evV_ev a ha ![p] (single_point_zero_constant hp) (φ i)]
  congr 1
  funext j
  fin_cases j
  rfl

variable (G : FGLaw V d) {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h2` using `small_two hx hy`. Establish `g0 : GP (pt V (n` using `2) d 0) := gp_pt 0`. Establish `g1 : GP (pt V (n` using `2) d 1) := gp_pt 1`. Establish `key` using `congrArg (evV ![x, y]) (G.comm i)`.

Rewrite `key` using `[evV_ev _ h2 _ (pair_points_zero_constant g1 g0)]`. Use `key.symm.trans ?_` and prove the remaining obligations. Use `show evV (fun j => subPt ![x, y] (![pt V (n := 2) d 1, pt V (n := 2) d 0] j)) (G.F i) = evV ![y, x] (G.F i)`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Use `fin_cases j`. Conclude with `subPt_pt _ h2 1`. Conclude with `subPt_pt _ h2 0`.
-/
theorem addV_comm {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) : addV G.F x y = addV G.F y x := by
  funext i
  have h2 := small_two hx hy
  have g0 : GP (pt V (n := 2) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 2) d 1) := gp_pt 1
  have key := congrArg (evV ![x, y]) (G.comm i)
  rw [evV_ev _ h2 _ (pair_points_zero_constant g1 g0)] at key
  refine key.symm.trans ?_
  show evV (fun j => subPt ![x, y] (![pt V (n := 2) d 1, pt V (n := 2) d 0] j)) (G.F i) = evV ![y, x] (G.F i)
  congr 1
  funext j
  fin_cases j
  · exact subPt_pt _ h2 1
  · exact subPt_pt _ h2 0

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h3` using `small_three hx hy hz`. Establish `g0 : GP (pt V (n` using `3) d 0) := gp_pt 0`. Establish `g1 : GP (pt V (n` using `3) d 1) := gp_pt 1`. Establish `g2 : GP (pt V (n` using `3) d 2) := gp_pt 2`.

Establish `e0 : subPt ![x, y, z] (pt V (n` using `3) d 0) = x := subPt_pt _ h3 0`. Establish `e1 : subPt ![x, y, z] (pt V (n` using `3) d 1) = y := subPt_pt _ h3 1`. Establish `e2 : subPt ![x, y, z] (pt V (n` using `3) d 2) = z := subPt_pt _ h3 2`. Establish `key` using `congrArg (evV ![x, y, z]) (G.assoc i)`. Establish `hl : evV ![x, y, z] (ev ![addOf G.F (pt V (n` using `3) d 0) (pt V (n := 3) d 1), pt V (n := 3) d 2] (G.F i)) = addV G.F (addV G.F x y) z i := by`.

Rewrite using `[evV_ev _ h3 _ (pair_points_zero_constant (gp_addOf G.F G.const _ _ g0 g1) g2)]`. Use `show evV _ (G.F i) = evV ![addV G.F x y, z] (G.F i)`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `fin_cases j`.

Use `show subPt ![x, y, z] (addOf G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1)) = addV G.F x y`. Rewrite using `[subPt_addOf _ h3 _ _ _ g0 g1, e0, e1]`. Conclude with `e2`. Establish `hr : evV ![x, y, z] (ev ![pt V (n` using `3) d 0, addOf G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)] (G.F i)) = addV G.F x (addV G.F y z) i := by`. Rewrite using `[evV_ev _ h3 _ (pair_points_zero_constant g0 (gp_addOf G.F G.const _ _ g1 g2))]`.

Use `show evV _ (G.F i) = evV ![x, addV G.F y z] (G.F i)`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Conclude with `e0`.

Use `show subPt ![x, y, z] (addOf G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)) = addV G.F y z`. Rewrite using `[subPt_addOf _ h3 _ _ _ g1 g2, e1, e2]`. Conclude with `hl.symm.trans (key.trans hr)`.
-/
theorem addV_assoc {x y z : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) (hz : SmallPt z) :
    addV G.F (addV G.F x y) z = addV G.F x (addV G.F y z) := by
  funext i
  have h3 := small_three hx hy hz
  have g0 : GP (pt V (n := 3) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 3) d 1) := gp_pt 1
  have g2 : GP (pt V (n := 3) d 2) := gp_pt 2
  have e0 : subPt ![x, y, z] (pt V (n := 3) d 0) = x := subPt_pt _ h3 0
  have e1 : subPt ![x, y, z] (pt V (n := 3) d 1) = y := subPt_pt _ h3 1
  have e2 : subPt ![x, y, z] (pt V (n := 3) d 2) = z := subPt_pt _ h3 2
  have key := congrArg (evV ![x, y, z]) (G.assoc i)
  have hl : evV ![x, y, z] (ev ![addOf G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1), pt V (n := 3) d 2] (G.F i)) =
      addV G.F (addV G.F x y) z i := by
    rw [evV_ev _ h3 _ (pair_points_zero_constant (gp_addOf G.F G.const _ _ g0 g1) g2)]
    show evV _ (G.F i) = evV ![addV G.F x y, z] (G.F i)
    congr 1
    funext j
    fin_cases j
    · show subPt ![x, y, z] (addOf G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1)) = addV G.F x y
      rw [subPt_addOf _ h3 _ _ _ g0 g1, e0, e1]
    · exact e2
  have hr : evV ![x, y, z] (ev ![pt V (n := 3) d 0, addOf G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)] (G.F i)) =
      addV G.F x (addV G.F y z) i := by
    rw [evV_ev _ h3 _ (pair_points_zero_constant g0 (gp_addOf G.F G.const _ _ g1 g2))]
    show evV _ (G.F i) = evV ![x, addV G.F y z] (G.F i)
    congr 1
    funext j
    fin_cases j
    · exact e0
    · show subPt ![x, y, z] (addOf G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)) = addV G.F y z
      rw [subPt_addOf _ h3 _ _ _ g1 g2, e1, e2]
  exact hl.symm.trans (key.trans hr)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h1` using `small_one hx`. Establish `g0 : GP (pt V (n` using `1) d 0) := gp_pt 0`. Establish `e : subPt ![x] (pt V (n` using `1) d 0) = x := subPt_pt _ h1 0`. Establish `key` using `congrArg (evV ![x]) (G.unit i)`.

Rewrite `key` using `[evV_ev _ h1 _ (pair_points_zero_constant gp_zero₂ g0)]`. Use `Eq.trans ?_ (key.trans (congrFun e i))` and prove the remaining obligations. Use `show evV ![0, x] (G.F i) = _`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Use `fin_cases j`. Conclude with `(subPt_zero _ h1).symm`. Conclude with `e.symm`.
-/
theorem zero_addV {x : Pt V n d} (hx : SmallPt x) : addV G.F 0 x = x := by
  funext i
  have h1 := small_one hx
  have g0 : GP (pt V (n := 1) d 0) := gp_pt 0
  have e : subPt ![x] (pt V (n := 1) d 0) = x := subPt_pt _ h1 0
  have key := congrArg (evV ![x]) (G.unit i)
  rw [evV_ev _ h1 _ (pair_points_zero_constant gp_zero₂ g0)] at key
  refine Eq.trans ?_ (key.trans (congrFun e i))
  show evV ![0, x] (G.F i) = _
  congr 1
  funext j
  fin_cases j
  · exact (subPt_zero _ h1).symm
  · exact e.symm

/- English proof (translation)
Establish `h0 : SmallPt (0 : Pt V n d)` using `fun i => by show MvPowerSeries.constantCoeff (0 : PS V n d) ∈ maximalIdeal V`. Rewrite using `[map_zero]`. Conclude with `zero_mem _`. Rewrite using `[addV_comm G hx h0]`. Conclude with `zero_addV G hx`.
-/
theorem addV_zero {x : Pt V n d} (hx : SmallPt x) : addV G.F x 0 = x := by
  have h0 : SmallPt (0 : Pt V n d) := fun i => by
    show MvPowerSeries.constantCoeff (0 : PS V n d) ∈ maximalIdeal V
    rw [map_zero]
    exact zero_mem _
  rw [addV_comm G hx h0]
  exact zero_addV G hx

variable {O : Type} [CommRing O] {G} (A : OAct O G)

/- English proof (translation)
Establish `h2` using `small_two hx hy`. Establish `g0 : GP (pt V (n` using `2) d 0) := gp_pt 0`. Establish `g1 : GP (pt V (n` using `2) d 1) := gp_pt 1`. Establish `e0 : subPt ![x, y] (pt V (n` using `2) d 0) = x := subPt_pt _ h2 0`. Establish `e1 : subPt ![x, y] (pt V (n` using `2) d 1) = y := subPt_pt _ h2 1`.

Establish `hφ : GP (A.act a)` using `A.const a`. Establish `key` using `congrArg (subPt ![x, y]) (A.hom a)`. Unfold `FGLaw.add at key`. Rewrite `key` using `[subPt_comp1 _ h2 _ _ (gp_addOf _ G.const _ _ g0 g1), subPt_addOf _ h2 _ _ _ g0 g1, subPt_addOf _ h2 _ _ _ (gp_comp1 _ _ hφ g0) (gp_comp1 _ _ hφ g1), subPt_comp1 _ h2 _ _ g0, subPt_comp1 _ h2 _ _ g1, e0, e1]`. Conclude with `key`.
-/
theorem act_addV (a : O) {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) :
    compV (A.act a) (addV G.F x y) = addV G.F (compV (A.act a) x) (compV (A.act a) y) := by
  have h2 := small_two hx hy
  have g0 : GP (pt V (n := 2) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 2) d 1) := gp_pt 1
  have e0 : subPt ![x, y] (pt V (n := 2) d 0) = x := subPt_pt _ h2 0
  have e1 : subPt ![x, y] (pt V (n := 2) d 1) = y := subPt_pt _ h2 1
  have hφ : GP (A.act a) := A.const a
  have key := congrArg (subPt ![x, y]) (A.hom a)
  unfold FGLaw.add at key
  rw [subPt_comp1 _ h2 _ _ (gp_addOf _ G.const _ _ g0 g1), subPt_addOf _ h2 _ _ _ g0 g1,
    subPt_addOf _ h2 _ _ _ (gp_comp1 _ _ hφ g0) (gp_comp1 _ _ hφ g1), subPt_comp1 _ h2 _ _ g0,
    subPt_comp1 _ h2 _ _ g1, e0, e1] at key
  exact key

/- English proof (translation)
Use `show subPt ![x] (A.act (a + b)) = addV G.F (subPt ![x] (A.act a)) (subPt ![x] (A.act b))`. Rewrite using `[A.add_act a b]`. Unfold `FGLaw.add`. Conclude with `subPt_addOf _ (small_one hx) _ _ _ (A.const a) (A.const b)`.
-/
theorem add_actV (a b : O) {x : Pt V n d} (hx : SmallPt x) :
    compV (A.act (a + b)) x = addV G.F (compV (A.act a) x) (compV (A.act b) x) := by
  show subPt ![x] (A.act (a + b)) = addV G.F (subPt ![x] (A.act a)) (subPt ![x] (A.act b))
  rw [A.add_act a b]
  unfold FGLaw.add
  exact subPt_addOf _ (small_one hx) _ _ _ (A.const a) (A.const b)

/- English proof (translation)
Use `show subPt ![x] (A.act (a * b)) = compV (A.act a) (subPt ![x] (A.act b))`. Rewrite using `[A.mul_act a b]`. Conclude with `subPt_comp1 _ (small_one hx) _ _ (A.const b)`.
-/
theorem mul_actV (a b : O) {x : Pt V n d} (hx : SmallPt x) :
    compV (A.act (a * b)) x = compV (A.act a) (compV (A.act b) x) := by
  show subPt ![x] (A.act (a * b)) = compV (A.act a) (subPt ![x] (A.act b))
  rw [A.mul_act a b]
  exact subPt_comp1 _ (small_one hx) _ _ (A.const b)

/- English proof (translation)
Use `show subPt ![x] (A.act 1) = x`. Rewrite using `[A.one_act]`. Conclude with `subPt_pt _ (small_one hx) 0`.
-/
theorem one_actV {x : Pt V n d} (hx : SmallPt x) : compV (A.act 1) x = x := by
  show subPt ![x] (A.act 1) = x
  rw [A.one_act]
  exact subPt_pt _ (small_one hx) 0

/- English proof (translation)
Use `show subPt ![x] (A.act 0) = 0`. Rewrite using `[GlobalTheory.FourierChainCompare.act_zero A]`. Conclude with `subPt_zero _ (small_one hx)`.
-/
theorem zero_actV {x : Pt V n d} (hx : SmallPt x) : compV (A.act 0) x = 0 := by
  show subPt ![x] (A.act 0) = 0
  rw [GlobalTheory.FourierChainCompare.act_zero A]
  exact subPt_zero _ (small_one hx)

/- English proof (translation)
Establish `h` using `add_actV A 1 (-1) hx`. Rewrite `h` using `[one_actV A hx, add_neg_cancel, zero_actV A hx]`. Conclude with `h.symm`.
-/
theorem addV_neg_actV {x : Pt V n d} (hx : SmallPt x) : addV G.F x (compV (A.act (-1)) x) = 0 := by
  have h := add_actV A 1 (-1) hx
  rw [one_actV A hx, add_neg_cancel, zero_actV A hx] at h
  exact h.symm

end GlobalTheory.PlaceInt.FormalPts

namespace GlobalTheory.PlaceInt
open FormalPts

/- English proof (translation)
Introduce `V _ _ _ _ _ d O _ _ B n x y z hx hy hz`. Use `⟨fun i => small_evV ![x, y] (small_two hx hy) (B.G.F i) (B.G.const i), addV_comm B.G hx hy, addV_assoc B.G hx hy hz, addV_zero B.G hx, addV_neg_actV B.A hx, one_actV B.A hx, zero_actV B.A hx, fun a b => ⟨fun i => small_evV ![x] (small_one hx) (B.A.act a i) (B.A.const a i), act_ad …` and prove the remaining obligations.
-/
theorem smallPts_module : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (x y z : Pt V n d), (∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (y i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (z i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (addV B.G.F x y i) ∈ maximalIdeal V) ∧ addV B.G.F x y = addV B.G.F y x ∧ addV B.G.F (addV B.G.F x y) z = addV B.G.F x (addV B.G.F y z) ∧ addV B.G.F x 0 = x ∧ addV B.G.F x (compV (B.A.act (-1)) x) = 0 ∧ compV (B.A.act 1) x = x ∧ compV (B.A.act 0) x = 0 ∧ ∀ a b : O, (∀ i, MvPowerSeries.constantCoeff (compV (B.A.act a) x i) ∈ maximalIdeal V) ∧ compV (B.A.act a) (addV B.G.F x y) = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act a) y) ∧ compV (B.A.act (a + b)) x = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act b) x) ∧ compV (B.A.act (a * b)) x = compV (B.A.act a) (compV (B.A.act b) x) := by
  intro V _ _ _ _ _ d O _ _ B n x y z hx hy hz
  refine ⟨fun i => small_evV ![x, y] (small_two hx hy) (B.G.F i) (B.G.const i), addV_comm B.G hx hy,
    addV_assoc B.G hx hy hz, addV_zero B.G hx, addV_neg_actV B.A hx, one_actV B.A hx, zero_actV B.A hx,
    fun a b => ⟨fun i => small_evV ![x] (small_one hx) (B.A.act a i) (B.A.const a i), act_addV B.A a hx hy,
      add_actV B.A a b hx, mul_actV B.A a b hx⟩⟩

end GlobalTheory.PlaceInt
