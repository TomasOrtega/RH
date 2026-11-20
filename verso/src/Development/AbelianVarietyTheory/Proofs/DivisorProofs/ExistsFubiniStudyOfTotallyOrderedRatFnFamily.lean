import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.FSExist

variable {X : Scheme.{0}} [IsIntegral X] {J : Type} {f : J → X.functionField}

/- English proof (translation)
Take `⟨U, hx, a, rfl⟩` from `h.exists_fnOf`. Conclude with `⟨U, hx, fun y hy => regAt_fnOf hy _ a⟩`.
-/
theorem regAt_nhds {x : X} {g : X.functionField} (h : RegAt x g) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, RegAt y g := by
  obtain ⟨U, hx, a, rfl⟩ := h.exists_fnOf
  exact ⟨U, hx, fun y hy => regAt_fnOf hy _ a⟩

/- English proof (translation)
Establish `key : ∀ s : Finset J, s.Nonempty → ∃ j, ∀ l ∈ s, RegAt x (f l / f j)`. Introduce `s hs`. Proceed by induction on `hs using Finset.Nonempty.cons_induction with`. Consider the case `singleton a`. Use `⟨a, fun l hl => ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.mem_singleton.1 hl, div_self (hf.1 a)]`. Conclude with `(unitAt_one x).regAt`. Consider the case `cons a s ha hs ih`. Take `⟨j, hj⟩` from `ih`. Break down `hf.2 x a j with h | h` into its components or cases.

Use `⟨j, fun l hl => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_cons.1 hl with rfl | hl` into its components or cases. Conclude with `h`. Conclude with `hj l hl`. Use `⟨a, fun l hl => ?_⟩` and prove the remaining obligations.

Break down `Finset.mem_cons.1 hl with rfl | hl` into its components or cases. Rewrite using `[div_self (hf.1 l)]`. Conclude with `(unitAt_one x).regAt`. Establish `e : f l / f a = f l / f j * (f j / f a)`. Rewrite using `[div_mul_div_cancel₀ (hf.1 j)]`.

Rewrite using `[e]`. Conclude with `(hj l hl).mul h`. Take `⟨j, hj⟩` from `key Finset.univ Finset.univ_nonempty`. Conclude with `⟨j, fun l => hj l (Finset.mem_univ l)⟩`.
-/
theorem exists_min [Fintype J] [Nonempty J] (hf : Total f) (x : X) :
    ∃ j, ∀ l, RegAt x (f l / f j) := by
  have key : ∀ s : Finset J, s.Nonempty → ∃ j, ∀ l ∈ s, RegAt x (f l / f j) := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a =>
      refine ⟨a, fun l hl => ?_⟩
      rw [Finset.mem_singleton.1 hl, div_self (hf.1 a)]
      exact (unitAt_one x).regAt
    | cons a s ha hs ih =>
      obtain ⟨j, hj⟩ := ih
      rcases hf.2 x a j with h | h
      ·
        refine ⟨j, fun l hl => ?_⟩
        rcases Finset.mem_cons.1 hl with rfl | hl
        · exact h
        · exact hj l hl
      ·
        refine ⟨a, fun l hl => ?_⟩
        rcases Finset.mem_cons.1 hl with rfl | hl
        · rw [div_self (hf.1 l)]; exact (unitAt_one x).regAt
        · have e : f l / f a = f l / f j * (f j / f a) := by
            rw [div_mul_div_cancel₀ (hf.1 j)]
          rw [e]; exact (hj l hl).mul h
  obtain ⟨j, hj⟩ := key Finset.univ Finset.univ_nonempty
  exact ⟨j, fun l => hj l (Finset.mem_univ l)⟩

def inv (hf : Total f) (j : J) : X.functionFieldˣ := Units.mk0 (f j)⁻¹ (inv_ne_zero (hf.1 j))

/- English proof (translation)
Rewrite using `[germOf_eq_iff]`. Express the relevant statement in the definitionally equal form `UnitAt x ((f j')⁻¹ / (f j)⁻¹)`. Rewrite using `[inv_div_inv]`. Use `(unitAt_iff (div_ne_zero (hf.1 j) (hf.1 j'))).2 ⟨hj' j, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_div]`.

Conclude with `hj j'`.
-/
theorem germOf_inv_eq (hf : Total f) {x : X} {j j' : J} (hj : ∀ l, RegAt x (f l / f j))
    (hj' : ∀ l, RegAt x (f l / f j')) : germOf x (inv hf j) = germOf x (inv hf j') := by
  rw [germOf_eq_iff]
  change UnitAt x ((f j')⁻¹ / (f j)⁻¹)
  rw [inv_div_inv]
  refine (unitAt_iff (div_ne_zero (hf.1 j) (hf.1 j'))).2 ⟨hj' j, ?_⟩
  rw [inv_div]
  exact hj j'

/- English proof (translation)
Use `isOpen_iff_forall_mem_open.2 fun y hy => ?_` and prove the remaining obligations. Use `choose V hV hV' using fun l => regAt_nhds (hy l)`. Conclude with `⟨⋂ l, (V l : Set X), fun z hz l => hV' l z (Set.mem_iInter.1 hz l), isOpen_iInter_of_finite fun l => (V l).isOpen, Set.mem_iInter.2 hV⟩`.
-/
theorem isOpen_minSet [Finite J] (hf : Total f) (j : J) :
    IsOpen {y : X | ∀ l, RegAt y (f l / f j)} := by
  refine isOpen_iff_forall_mem_open.2 fun y hy => ?_
  choose V hV hV' using fun l => regAt_nhds (hy l)
  exact ⟨⋂ l, (V l : Set X), fun z hz l => hV' l z (Set.mem_iInter.1 hz l),
    isOpen_iInter_of_finite fun l => (V l).isOpen, Set.mem_iInter.2 hV⟩

variable [Fintype J] [Nonempty J]

def fsDiv (hf : Total f) : CartierDiv X :=
  show cartierGroup X from ⟨fun x => germOf x (inv hf (exists_min hf x).choose), fun x =>
    ⟨⟨_, isOpen_minSet hf (exists_min hf x).choose⟩, (exists_min hf x).choose_spec,
      inv hf (exists_min hf x).choose, fun y hy =>
        germOf_inv_eq hf (exists_min hf y).choose_spec hy⟩⟩

/- English proof (translation)
The claim follows from `germOf_inv_eq hf (exists_min hf x).choose_spec hj`.
-/
theorem isEqn_inv (hf : Total f) {x : X} {j : J} (hj : ∀ l, RegAt x (f l / f j)) :
    (fsDiv hf).IsEqn x (inv hf j) :=
  germOf_inv_eq hf (exists_min hf x).choose_spec hj

/- English proof (translation)
The claim follows from `CartierDiv.mem_sections.2 fun x => ⟨_, isEqn_inv hf (exists_min hf x).choose_spec, by change RegAt x (f l * (f _)⁻¹) rw [← div_eq_mul_inv] exact (exists_min hf x).choose_spec l⟩`.
-/
theorem mem_sections (hf : Total f) (l : J) : f l ∈ (fsDiv hf).sections :=
  CartierDiv.mem_sections.2 fun x =>
    ⟨_, isEqn_inv hf (exists_min hf x).choose_spec, by
      change RegAt x (f l * (f _)⁻¹)
      rw [← div_eq_mul_inv]
      exact (exists_min hf x).choose_spec l⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, isEqn_inv hf hj, by change UnitAt x (f j * (f j)⁻¹) rw [mul_inv_cancel₀ (hf.1 j)] exact unitAt_one x⟩`.
-/
theorem generatesAt (hf : Total f) {x : X} {j : J} (hj : ∀ l, RegAt x (f l / f j)) :
    (fsDiv hf).GeneratesAt x (f j) :=
  ⟨_, isEqn_inv hf hj, by
    change UnitAt x (f j * (f j)⁻¹)
    rw [mul_inv_cancel₀ (hf.1 j)]
    exact unitAt_one x⟩

end GlobalTheory.HSNef.FSExist

namespace GlobalTheory.HSNef.FSExist

variable {X : Scheme.{0}} [IsIntegral X] {J : Type} [Fintype J] [Nonempty J] {f : J → X.functionField}
  [DecidableEq J]

def sec (hf : Total f) (l : J) : (toLB (fsDiv hf)).Sec :=
  ((presents_toLB (fsDiv hf)).exists_rat_eq (mem_sections hf l)).choose

/- English proof (translation)
The claim follows from `((presents_toLB (fsDiv hf)).exists_rat_eq (mem_sections hf l)).choose_spec`.
-/
theorem rat_sec (hf : Total f) (l : J) : (presents_toLB (fsDiv hf)).rat (sec hf l) = f l :=
  ((presents_toLB (fsDiv hf)).exists_rat_eq (mem_sections hf l)).choose_spec

/- English proof (translation)
The claim follows from `eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨(exists_min hf x).choose, ((presents_toLB (fsDiv hf)).generatesAt_rat_iff _).1 (by rw [rat_sec]; exact generatesAt hf (exists_min hf x).choose_spec)⟩`.
-/
theorem iSup_sec (hf : Total f) : ⨆ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (sec hf j) = ⊤ :=
  eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨(exists_min hf x).choose,
    ((presents_toLB (fsDiv hf)).generatesAt_rat_iff _).1 (by
      rw [rat_sec]; exact generatesAt hf (exists_min hf x).choose_spec)⟩

def expDiag (w : J → ℝ) : Matrix J J ℂ := Matrix.diagonal fun j => ((Real.exp (w j) : ℝ) : ℂ)

/- English proof (translation)
Rewrite using `[expDiag, Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.2 fun j _ => Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'`.
-/
theorem det_expDiag (w : J → ℝ) : (expDiag w).det ≠ 0 := by
  classical
  rw [expDiag, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun j _ => Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.map_apply, expDiag, Matrix.diagonal_apply_eq, Complex.conj_ofReal]`. Simplify using `[expDiag, Matrix.diagonal_apply_ne _ h]`.
-/
theorem map_expDiag (w : J → ℝ) : (expDiag w).map (starRingEnd ℂ) = expDiag w := by
  ext i j
  by_cases h : i = j
  · subst h; rw [Matrix.map_apply, expDiag, Matrix.diagonal_apply_eq, Complex.conj_ofReal]
  · simp [expDiag, Matrix.diagonal_apply_ne _ h]

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single a (fun j _ hj => by simp [expDiag, Matrix.diagonal_apply_ne _ hj]) (fun h => (h (Finset.mem_univ a)).elim)]`. Simplify using `[expDiag]`.
-/
theorem sum_expDiag (w : J → ℝ) (v : J → ℂ) (a : J) :
    ∑ j, expDiag w j a * v j = ((Real.exp (w a) : ℝ) : ℂ) * v a := by
  classical
  rw [Finset.sum_eq_single a (fun j _ hj => by simp [expDiag, Matrix.diagonal_apply_ne _ hj])
    (fun h => (h (Finset.mem_univ a)).elim)]
  simp [expDiag]

end GlobalTheory.HSNef.FSExist

open GlobalTheory.HSNef.FSExist in

/- English proof (translation)
Introduce `k _ X _ p J _ _ f w hf`. Set `h` to `presents_toLB (fsDiv hf)`. Use `⟨HermLB.fs p (isLB_toLB (fsDiv hf)) (sec hf) (iSup_sec hf) (fun _ => expDiag w) (fun _ => det_expDiag w) (fun _ => ⟨1, one_mem _, by rw [mul_one, map_expDiag]⟩), ?_⟩` and prove the remaining obligations. Use `⟨fun i => i.1.2, h.isRatSec, fun x c hx => ⟨fun j => ?_, ?_⟩, fun σ y (c : (toLB (fsDiv hf)).ι) (hy : y ∈ ptsIn p σ ((toLB (fsDiv hf)).U c)) => ?_⟩` and prove the remaining obligations. Conclude with `(c.2.2 x hx).regularAt_iff.1 (CartierDiv.mem_sections.1 (mem_sections hf j) x)`.

Conclude with `⟨_, (c.2.2 x hx).generatesAt_iff.1 (generatesAt hf (exists_min hf x).choose_spec)⟩`. Use `(Weight.fsBasis_φ (p := p) (σ := σ) (isLB_toLB (fsDiv hf)) (sec hf) (iSup_sec hf) (expDiag w) (det_expDiag w) c y).trans ?_` and prove the remaining obligations. Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[sum_expDiag]`.

Establish `e : f a * (c.1.2 : X.functionField) = fnOf _ c.2.1 ((sec hf a).f c)`. Rewrite using `[← rat_sec hf a]`. Conclude with `h.rat_mul (sec hf a) c c.2.1`. Establish `e2 : ratVal (f a * (c.1.2 : X.functionField)) y = valR y.1 ((toLB (fsDiv hf)).U c) ((sec hf a).f c)`. Rewrite using `[e]`.

Conclude with `ratVal_fnOf (U := (toLB (fsDiv hf)).U c) hy c.2.1 _`. Rewrite using `[e2]`. Rewrite using `[norm_mul, mul_pow, mul_comm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]`. Evaluate the numerical expressions.
-/
theorem GlobalTheory.HSNef.exists_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (J : Type) [Fintype J] [Nonempty J] (f : J → X.functionField) (w : J → ℝ), Total f →
      ∃ M : HermLB p, IsFS M f w := by
  intro k _ X _ p J _ _ f w hf
  classical
  let h := presents_toLB (fsDiv hf)
  refine ⟨HermLB.fs p (isLB_toLB (fsDiv hf)) (sec hf) (iSup_sec hf) (fun _ => expDiag w)
    (fun _ => det_expDiag w) (fun _ => ⟨1, one_mem _, by rw [mul_one, map_expDiag]⟩), ?_⟩
  refine ⟨fun i => i.1.2, h.isRatSec, fun x c hx => ⟨fun j => ?_, ?_⟩, fun σ y (c : (toLB (fsDiv hf)).ι) (hy : y ∈ ptsIn p σ ((toLB (fsDiv hf)).U c)) => ?_⟩
  · exact (c.2.2 x hx).regularAt_iff.1 (CartierDiv.mem_sections.1 (mem_sections hf j) x)
  · exact ⟨_, (c.2.2 x hx).generatesAt_iff.1 (generatesAt hf (exists_min hf x).choose_spec)⟩
  · refine (Weight.fsBasis_φ (p := p) (σ := σ) (isLB_toLB (fsDiv hf)) (sec hf) (iSup_sec hf) (expDiag w)
      (det_expDiag w) c y).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_expDiag]
    have e : f a * (c.1.2 : X.functionField) = fnOf _ c.2.1 ((sec hf a).f c) := by
      rw [← rat_sec hf a]; exact h.rat_mul (sec hf a) c c.2.1
    have e2 : ratVal (f a * (c.1.2 : X.functionField)) y =
        valR y.1 ((toLB (fsDiv hf)).U c) ((sec hf a).f c) := by
      rw [e]; exact ratVal_fnOf (U := (toLB (fsDiv hf)).U c) hy c.2.1 _
    rw [e2]
    rw [norm_mul, mul_pow, mul_comm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    norm_num
