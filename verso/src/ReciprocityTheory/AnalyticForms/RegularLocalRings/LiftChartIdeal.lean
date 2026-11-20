import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjBCompl
import ReciprocityTheory.AnalyticForms.RegularLocalRings.EvalValChartCoord

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

variable (w : WData P D hP)

abbrev Idx : Type := Σ p : ((k : K) → ι k), Fin (w.m p)

def M : Type := {x : w.W // IsClosed ({x} : Set w.W)}

def src (c : w.Idx) : Set w.M := {x | x.1 ∈ (w.pres c.1 c.2).V}

open Classical in

def coord (c : w.Idx) (x : w.M) : Fin (w.pres c.1 c.2).n → ℂ :=
  if h : x.1 ∈ (w.pres c.1 c.2).V then (w.pres c.1 c.2).coord x.1 h else 0

instance topology : TopologicalSpace w.M :=
  TopologicalSpace.generateFrom
    {S | ∃ (c : w.Idx) (O : Set (Fin (w.pres c.1 c.2).n → ℂ)), IsOpen O ∧ S = w.src c ∩ w.coord c ⁻¹' O}

open Classical in

def lift (c : w.Idx) (q : Σ k, ι k) : MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ :=
  if q.2 = c.1 q.1 then 1 else X (w.yq c.1 c.2 q)

/- English proof (translation)
Unfold `coord`. Conclude with `dif_pos hx`.
-/
theorem coord_of_mem (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    w.coord c x = (w.pres c.1 c.2).coord x.1 hx := by
  unfold coord; exact dif_pos hx

/- English proof (translation)
Use `w.lft` as an intermediate fact. Rewrite using `[w.coord_of_mem c x hx]`. Conclude with `(w.pres c.1 c.2).eval_coord_eq_val x.1 hx x.2 f`.
-/
theorem eval_coord_val (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) (f : MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ) :
    eval (w.coord c x) f = val (w.π ≫ toSpecC hP) ((w.pres c.1 c.2).secHom f) x.1 hx := by
  have := w.lft
  rw [w.coord_of_mem c x hx]
  exact (w.pres c.1 c.2).eval_coord_eq_val x.1 hx x.2 f

/- English proof (translation)
Rewrite using `[(w.pres c.1 c.2).mem_basicOpen_secHom_iff x.1 hx f, (w.pres c.1 c.2).ptOf_eq_ptIdeal x.1 hx x.2, ptIdeal, RingHom.mem_ker, w.coord_of_mem c x hx]`.
-/
theorem mem_basicOpen_iff (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) (f : MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ) :
    x.1 ∈ w.W.basicOpen ((w.pres c.1 c.2).secHom f) ↔ eval (w.coord c x) f ≠ 0 := by
  rw [(w.pres c.1 c.2).mem_basicOpen_secHom_iff x.1 hx f, (w.pres c.1 c.2).ptOf_eq_ptIdeal x.1 hx x.2,
    ptIdeal, RingHom.mem_ker, w.coord_of_mem c x hx]

/- English proof (translation)
Use `w.lft` as an intermediate fact. Take `⟨O, hxO, hO, q0, F0, hq0, hF0⟩` from `exists_coord_fwd (𝟙 w.W) (Category.id_comp _) (w.pres c.1 c.2) (w.pres c'.1 c'.2).V (fun l => (w.pres c'.1 c'.2).secHom (X l)) x.1 hx.1 hx.2 x.2`. Take `⟨f, hfO, hxf⟩` from `(w.pres c.1 c.2).isAffineOpen_V'.exists_basicOpen_le ⟨x.1, hxO⟩ hx.1`. Take `⟨h, rfl⟩` from `(w.pres c.1 c.2).secHom_surj f`. Establish `hxh` using `(w.mem_basicOpen_iff c x hx.1 h).mp hxf`.

Use `⟨q0 * h, fun l => F0 l * h, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eval_mul]`. Rewrite `hxh`, the goal using `[w.coord_of_mem c x hx.1]`. Conclude with `mul_ne_zero hq0 hxh`. Introduce `y hy hne`.

Rewrite `hne` using `[eval_mul]`. Establish `hyh : y.1 ∈ w.W.basicOpen ((w.pres c.1 c.2).secHom h)` using `(w.mem_basicOpen_iff c y hy h).mpr (right_ne_zero_of_mul hne)`. Establish `hyO : y.1 ∈ O` using `hfO hyh`. Establish `hy' : y.1 ∈ (w.pres c'.1 c'.2).V` using `(hO hyO).2`. Use `⟨hy', fun l => ?_⟩` and prove the remaining obligations.

Establish `e1 : val (w.π ≫ toSpecC hP) ((w.pres c'.1 c'.2).secHom (X l)) y.1 hy' * eval ((w.pres c.1 c.2).coord y.1 hy) q0 = eval ((w.pres c.1 c.2).coord y.1 hy) (F0 l)` using `(hF0 y.1 hy hy' hyO y.2).2 l`. Rewrite `e1` using `[← (w.pres c'.1 c'.2).eval_coord_eq_val y.1 hy' y.2, eval_X]`. Rewrite using `[w.coord_of_mem c y hy, w.coord_of_mem c' y hy', eval_mul, eval_mul, ← e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trans_strong (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c ∩ w.src c') :
    ∃ (q : MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ)
      (F : Fin (w.pres c'.1 c'.2).n → MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ),
      eval (w.coord c x) q ≠ 0 ∧ ∀ y ∈ w.src c, eval (w.coord c y) q ≠ 0 →
        y ∈ w.src c' ∧ ∀ l, w.coord c' y l * eval (w.coord c y) q = eval (w.coord c y) (F l) := by
  have := w.lft
  obtain ⟨O, hxO, hO, q0, F0, hq0, hF0⟩ := exists_coord_fwd (𝟙 w.W) (Category.id_comp _)
    (w.pres c.1 c.2) (w.pres c'.1 c'.2).V (fun l => (w.pres c'.1 c'.2).secHom (X l)) x.1 hx.1 hx.2 x.2
  obtain ⟨f, hfO, hxf⟩ := (w.pres c.1 c.2).isAffineOpen_V'.exists_basicOpen_le ⟨x.1, hxO⟩ hx.1
  obtain ⟨h, rfl⟩ := (w.pres c.1 c.2).secHom_surj f
  have hxh := (w.mem_basicOpen_iff c x hx.1 h).mp hxf
  refine ⟨q0 * h, fun l => F0 l * h, ?_, ?_⟩
  · rw [eval_mul]
    rw [w.coord_of_mem c x hx.1] at hxh ⊢
    exact mul_ne_zero hq0 hxh
  · intro y hy hne
    rw [eval_mul] at hne
    have hyh : y.1 ∈ w.W.basicOpen ((w.pres c.1 c.2).secHom h) :=
      (w.mem_basicOpen_iff c y hy h).mpr (right_ne_zero_of_mul hne)
    have hyO : y.1 ∈ O := hfO hyh
    have hy' : y.1 ∈ (w.pres c'.1 c'.2).V := (hO hyO).2
    refine ⟨hy', fun l => ?_⟩
    have e1 : val (w.π ≫ toSpecC hP) ((w.pres c'.1 c'.2).secHom (X l)) y.1 hy' *
        eval ((w.pres c.1 c.2).coord y.1 hy) q0 = eval ((w.pres c.1 c.2).coord y.1 hy) (F0 l) :=
      (hF0 y.1 hy hy' hyO y.2).2 l
    rw [← (w.pres c'.1 c'.2).eval_coord_eq_val y.1 hy' y.2, eval_X] at e1
    rw [w.coord_of_mem c y hy, w.coord_of_mem c' y hy', eval_mul, eval_mul, ← e1]
    ring

/- English proof (translation)
The claim follows from `w.le_pres c.1 c.2 hx`.
-/
theorem pi_mem (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) : w.π.base x.1 ∈ (chartOpen hP c.1).1 :=
  w.le_pres c.1 c.2 hx

/- English proof (translation)
Use `w.lft` as an intermediate fact. Conclude with `isClosed_image_of_closed (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl x.1 x.2`.
-/
theorem pi_closed (x : w.M) : IsClosed ({w.π.base x.1} : Set (projX P hP)) := by
  have := w.lft
  exact isClosed_image_of_closed (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl x.1 x.2

/- English proof (translation)
Use `w.lft` as an intermediate fact. Distinguish the cases in `hq : q.2 = c.1 q.1`. Establish `e : w.lift c q = 1` using `by simp [lift, hq]`. Rewrite using `[e, map_one]`. Take `⟨k, i⟩` from `q`.

Simplify using `only at hq`. Substitute `hq` using the available equality. Establish `e1 : Ideal.Quotient.mk (chartIdeal P c.1) (X ⟨k, c.1 k⟩) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk (chartIdeal P c.1)), Ideal.Quotient.eq]`. Conclude with `Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)`.

Establish `e2 : chartCoord hP c.1 ⟨k, c.1 k⟩ = 1`. Rewrite using `[chartCoord, e1, map_one]`. Rewrite using `[e2]`. Take `⟨φ, hφ⟩` from `val_ringHom (toSpecC hP) (chartOpen hP c.1).1 _ (w.pi_mem c x hx) (w.pi_closed x)`. Rewrite using `[← hφ, map_one]`.

Establish `e : w.lift c q = X (w.yq c.1 c.2 q)` using `by simp [lift, hq]`. Rewrite using `[e, w.eval_coord_val c x hx, w.sec_yq c.1 c.2 q]`. Conclude with `(val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (w.le_pres c.1 c.2) (chartCoord hP c.1 q) x.1 hx x.2).2`.
-/
theorem lift_val (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) (q : Σ k, ι k) :
    eval (w.coord c x) (w.lift c q) =
      val (toSpecC hP) (chartCoord hP c.1 q) (w.π.base x.1) (w.pi_mem c x hx) := by
  have := w.lft
  by_cases hq : q.2 = c.1 q.1
  · have e : w.lift c q = 1 := by simp [lift, hq]
    rw [e, map_one]
    obtain ⟨k, i⟩ := q
    simp only at hq
    subst hq
    have e1 : Ideal.Quotient.mk (chartIdeal P c.1) (X ⟨k, c.1 k⟩) = 1 := by
      rw [← map_one (Ideal.Quotient.mk (chartIdeal P c.1)), Ideal.Quotient.eq]
      exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    have e2 : chartCoord hP c.1 ⟨k, c.1 k⟩ = 1 := by
      rw [chartCoord, e1, map_one]
    rw [e2]
    obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP c.1).1 _ (w.pi_mem c x hx) (w.pi_closed x)
    rw [← hφ, map_one]
  · have e : w.lift c q = X (w.yq c.1 c.2 q) := by simp [lift, hq]
    rw [e, w.eval_coord_val c x hx, w.sec_yq c.1 c.2 q]
    exact (val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (w.le_pres c.1 c.2)
      (chartCoord hP c.1 q) x.1 hx x.2).2

/- English proof (translation)
Apply `TopologicalSpace.isOpen_generateFrom_of_mem` to reduce the goal to its premises. Conclude with `⟨c, Set.univ, isOpen_univ, by rw [Set.preimage_univ, Set.inter_univ]⟩`.
-/
theorem isOpen_alt_bis (c : w.Idx) : IsOpen (w.src c) := by
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  exact ⟨c, Set.univ, isOpen_univ, by rw [Set.preimage_univ, Set.inter_univ]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `chartOpen_cover hP (w.π.base x.1)`. Establish `h1 : x.1 ∈ w.π ⁻¹ᵁ (chartOpen hP p).1` using `hp`. Rewrite `h1` using `[← w.iSup_pres p]`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp h1`. Conclude with `⟨⟨p, i⟩, hi⟩`.
-/
theorem cover (x : w.M) : ∃ c, x ∈ w.src c := by
  obtain ⟨p, hp⟩ := chartOpen_cover hP (w.π.base x.1)
  have h1 : x.1 ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hp
  rw [← w.iSup_pres p] at h1
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h1
  exact ⟨⟨p, i⟩, hi⟩

/- English proof (translation)
Establish `hcont : Continuous fun y : w.src c => w.coord c y`. Rewrite using `[continuous_def]`. Introduce `O hO`. Establish `h1 : IsOpen (w.src c ∩ w.coord c ⁻¹' O)` using `TopologicalSpace.isOpen_generateFrom_of_mem ⟨c, O, hO, rfl⟩`. Conclude with `isOpen_induced_iff.mpr ⟨_, h1, Set.ext fun y => ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩⟩`.

Use `⟨⟨le_antisymm (continuous_iff_le_induced.mp hcont) ?_⟩, ?_⟩` and prove the remaining obligations. Use `show TopologicalSpace.induced _ _ ≤ TopologicalSpace.induced Subtype.val (TopologicalSpace.generateFrom _)`. Rewrite using `[induced_generateFrom_eq]`. Apply `le_generateFrom` to reduce the goal to its premises. Introduce and unpack `_ ⟨S, ⟨c', O', hO', rfl⟩, rfl⟩`.

Establish `hloc : ∀ y : w.src c, y.1 ∈ w.src c' ∩ w.coord c' ⁻¹' O' → ∃ U : Set (Fin (w.pres c.1 c.2).n → ℂ), IsOpen U ∧ w.coord c y.1 ∈ U ∧ ∀ z : w.src c, w.coord c z.1 ∈ U → z.1 ∈ w.src c' ∩ w.coord c' ⁻¹' O'`. Introduce and unpack `y ⟨hy1, hy2⟩`. Take `⟨q, F, hq, hF⟩` from `w.trans_strong c c' y.1 ⟨y.2, hy1⟩`. Set `g : (Fin (w.pres c.1 c.2).n → ℂ) → (Fin (w.pres c'.1 c'.2).n → ℂ)` to `fun a l => eval a (F l) / eval a q`. Establish `hg : ContinuousOn g {a | eval a q ≠ 0}` using `continuousOn_pi.mpr fun l => (MvPolynomial.continuous_eval _).continuousOn.div (MvPolynomial.continuous_eval _).continuousOn fun a ha => ha`.

Establish `hU : IsOpen ({a | eval a q ≠ 0} ∩ g ⁻¹' O')` using `hg.isOpen_inter_preimage (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const) hO'`. Establish `hval : ∀ z ∈ w.src c, eval (w.coord c z) q ≠ 0 → z ∈ w.src c' ∧ w.coord c' z = g (w.coord c z)`. Introduce `z hz hzq`. Take `⟨h1, h2⟩` from `hF z hz hzq`. Conclude with `⟨h1, funext fun l => eq_div_of_mul_eq hzq (h2 l)⟩`.

Use `⟨{a | eval a q ≠ 0} ∩ g ⁻¹' O', hU, ⟨hq, ?_⟩, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨-, h2⟩` from `hval y.1 y.2 hq show g (w.coord c y.1) ∈ O'`. Rewrite using `[← h2]`. Conclude with `hy2`. Take `⟨hz1, hz2⟩` from `hz`.

Take `⟨h1, h2⟩` from `hval z.1 z.2 hz1`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `show w.coord c' z.1 ∈ O'`. Rewrite using `[h2]`. Conclude with `hz2`.

Use `choose U hUo hyU hUS using hloc`. Use `isOpen_induced_iff.mpr ⟨⋃ (y : w.src c) (hy : y.1 ∈ w.src c' ∩ w.coord c' ⁻¹' O'), U y hy, isOpen_iUnion fun y => isOpen_iUnion fun hy => hUo y hy, ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Simplify using `only [Set.mem_preimage, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, hz⟩`. Conclude with `hUS y hy z hz`. Introduce `hz`. Conclude with `⟨z, hz, hyU z hz⟩`. Introduce `y y' h`.

Establish `hy : w.coord c y.1 = w.coord c y'.1` using `h`. Rewrite `hy` using `[w.coord_of_mem c y.1 y.2, w.coord_of_mem c y'.1 y'.2]`. Establish `hzero : ∀ h ∈ (w.pres c.1 c.2).K, eval ((w.pres c.1 c.2).coord y.1.1 y.2) h = 0` using `(w.pres c.1 c.2).eval_coord_eq_zero y.1.1 y.2 y.1.2`. Take `⟨x0, -, huniq⟩` from `(w.pres c.1 c.2).existsUnique_closed_coord _ hzero`. Establish `e1` using `huniq y.1.1 ⟨y.2, y.1.2, rfl⟩`.

Establish `e2` using `huniq y'.1.1 ⟨y'.2, y'.1.2, hy.symm⟩`. Conclude with `Subtype.ext (Subtype.ext (e1.trans e2.symm))`.
-/
theorem isEmbedding (c : w.Idx) : Topology.IsEmbedding fun y : w.src c => w.coord c y := by
  have hcont : Continuous fun y : w.src c => w.coord c y := by
    rw [continuous_def]
    intro O hO
    have h1 : IsOpen (w.src c ∩ w.coord c ⁻¹' O) :=
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨c, O, hO, rfl⟩
    exact isOpen_induced_iff.mpr ⟨_, h1, Set.ext fun y => ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩⟩
  refine ⟨⟨le_antisymm (continuous_iff_le_induced.mp hcont) ?_⟩, ?_⟩
  · show TopologicalSpace.induced _ _ ≤ TopologicalSpace.induced Subtype.val
      (TopologicalSpace.generateFrom _)
    rw [induced_generateFrom_eq]
    apply le_generateFrom
    rintro _ ⟨S, ⟨c', O', hO', rfl⟩, rfl⟩
    have hloc : ∀ y : w.src c, y.1 ∈ w.src c' ∩ w.coord c' ⁻¹' O' →
        ∃ U : Set (Fin (w.pres c.1 c.2).n → ℂ), IsOpen U ∧ w.coord c y.1 ∈ U ∧
          ∀ z : w.src c, w.coord c z.1 ∈ U → z.1 ∈ w.src c' ∩ w.coord c' ⁻¹' O' := by
      rintro y ⟨hy1, hy2⟩
      obtain ⟨q, F, hq, hF⟩ := w.trans_strong c c' y.1 ⟨y.2, hy1⟩
      let g : (Fin (w.pres c.1 c.2).n → ℂ) → (Fin (w.pres c'.1 c'.2).n → ℂ) :=
        fun a l => eval a (F l) / eval a q
      have hg : ContinuousOn g {a | eval a q ≠ 0} := continuousOn_pi.mpr fun l =>
        (MvPolynomial.continuous_eval _).continuousOn.div (MvPolynomial.continuous_eval _).continuousOn
          fun a ha => ha
      have hU : IsOpen ({a | eval a q ≠ 0} ∩ g ⁻¹' O') :=
        hg.isOpen_inter_preimage (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const) hO'
      have hval : ∀ z ∈ w.src c, eval (w.coord c z) q ≠ 0 →
          z ∈ w.src c' ∧ w.coord c' z = g (w.coord c z) := by
        intro z hz hzq
        obtain ⟨h1, h2⟩ := hF z hz hzq
        exact ⟨h1, funext fun l => eq_div_of_mul_eq hzq (h2 l)⟩
      refine ⟨{a | eval a q ≠ 0} ∩ g ⁻¹' O', hU, ⟨hq, ?_⟩, fun z hz => ?_⟩
      · obtain ⟨-, h2⟩ := hval y.1 y.2 hq
        show g (w.coord c y.1) ∈ O'
        rw [← h2]
        exact hy2
      · obtain ⟨hz1, hz2⟩ := hz
        obtain ⟨h1, h2⟩ := hval z.1 z.2 hz1
        refine ⟨h1, ?_⟩
        show w.coord c' z.1 ∈ O'
        rw [h2]
        exact hz2
    choose U hUo hyU hUS using hloc
    refine isOpen_induced_iff.mpr ⟨⋃ (y : w.src c) (hy : y.1 ∈ w.src c' ∩ w.coord c' ⁻¹' O'), U y hy,
      isOpen_iUnion fun y => isOpen_iUnion fun hy => hUo y hy, ?_⟩
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, hz⟩
      exact hUS y hy z hz
    · intro hz
      exact ⟨z, hz, hyU z hz⟩
  · intro y y' h
    have hy : w.coord c y.1 = w.coord c y'.1 := h
    rw [w.coord_of_mem c y.1 y.2, w.coord_of_mem c y'.1 y'.2] at hy
    have hzero : ∀ h ∈ (w.pres c.1 c.2).K, eval ((w.pres c.1 c.2).coord y.1.1 y.2) h = 0 :=
      (w.pres c.1 c.2).eval_coord_eq_zero y.1.1 y.2 y.1.2
    obtain ⟨x0, -, huniq⟩ := (w.pres c.1 c.2).existsUnique_closed_coord _ hzero
    have e1 := huniq y.1.1 ⟨y.2, y.1.2, rfl⟩
    have e2 := huniq y'.1.1 ⟨y'.2, y'.1.2, hy.symm⟩
    exact Subtype.ext (Subtype.ext (e1.trans e2.symm))

/- English proof (translation)
Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩ h hh`. Rewrite using `[w.coord_of_mem c y hy]`. Conclude with `(w.pres c.1 c.2).eval_coord_eq_zero y.1 hy y.2 h hh`.

Introduce `ha`. Take `⟨x, ⟨hxV, hcl, hco⟩, -⟩` from `(w.pres c.1 c.2).existsUnique_closed_coord a ha`. Use `⟨⟨x, hcl⟩, hxV, ?_⟩` and prove the remaining obligations. Rewrite using `[w.coord_of_mem c ⟨x, hcl⟩ hxV]`. Conclude with `hco`.
-/
theorem image (c : w.Idx) :
    w.coord c '' w.src c = {y | ∀ h ∈ (w.pres c.1 c.2).K, eval y h = 0} := by
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩ h hh
    rw [w.coord_of_mem c y hy]
    exact (w.pres c.1 c.2).eval_coord_eq_zero y.1 hy y.2 h hh
  · intro ha
    obtain ⟨x, ⟨hxV, hcl, hco⟩, -⟩ := (w.pres c.1 c.2).existsUnique_closed_coord a ha
    refine ⟨⟨x, hcl⟩, hxV, ?_⟩
    rw [w.coord_of_mem c ⟨x, hcl⟩ hxV]
    exact hco

/- English proof (translation)
Take `⟨q, F, hq, hF⟩` from `w.trans_strong c c' x hx`. Conclude with `⟨q, F, hq, fun y hy hne => (hF y hy.1 hne).2⟩`.
-/
theorem trans (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c ∩ w.src c') :
    ∃ (q : MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ)
      (F : Fin (w.pres c'.1 c'.2).n → MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ),
      eval (w.coord c x) q ≠ 0 ∧ ∀ y ∈ w.src c ∩ w.src c', eval (w.coord c y) q ≠ 0 →
        ∀ l, w.coord c' y l * eval (w.coord c y) q = eval (w.coord c y) (F l) := by
  obtain ⟨q, F, hq, hF⟩ := w.trans_strong c c' x hx
  exact ⟨q, F, hq, fun y hy hne => (hF y hy.1 hne).2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨c.1, fun k => by simp [lift]⟩`.
-/
theorem lift_one (c : w.Idx) : ∃ p : (k : K) → ι k, ∀ k, w.lift c ⟨k, p k⟩ = 1 :=
  ⟨c.1, fun k => by simp [lift]⟩

/- English proof (translation)
Introduce `h hh`. Establish `e : (fun q => eval (w.coord c x) (w.lift c q)) = fun q => val (toSpecC hP) (chartCoord hP c.1 q) (w.π.base x.1) (w.pi_mem c x hx)`. Use function extensionality and compare the values at `(w.lift_val c x hx)`. Rewrite using `[e, eval_val_chartCoord hP c.1 _ _ (w.pi_closed x), Ideal.Quotient.eq_zero_iff_mem.mpr hh, map_zero]`. Take `⟨φ, hφ⟩` from `val_ringHom (toSpecC hP) (chartOpen hP c.1).1 _ (w.pi_mem c x hx) (w.pi_closed x)`.

Rewrite using `[← hφ, map_zero]`.
-/
theorem lift_chartIdeal (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    ∀ h ∈ chartIdeal P c.1, eval (fun q => eval (w.coord c x) (w.lift c q)) h = 0 := by
  intro h hh
  have e : (fun q => eval (w.coord c x) (w.lift c q)) =
      fun q => val (toSpecC hP) (chartCoord hP c.1 q) (w.π.base x.1) (w.pi_mem c x hx) :=
    funext (w.lift_val c x hx)
  rw [e, eval_val_chartCoord hP c.1 _ _ (w.pi_closed x), Ideal.Quotient.eq_zero_iff_mem.mpr hh, map_zero]
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP c.1).1 _ (w.pi_mem c x hx) (w.pi_closed x)
  rw [← hφ, map_zero]

/- English proof (translation)
Conclude with `(conePts_of_chartIdeal hP c.1 _ (w.lift_chartIdeal c x hx)).1`.
-/
theorem lift_mem (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    (fun q => eval (w.coord c x) (w.lift c q)) ∈ conePts P := by
  exact (conePts_of_chartIdeal hP c.1 _ (w.lift_chartIdeal c x hx)).1

/- English proof (translation)
Use `w.lft` as an intermediate fact. Establish `hpp : w.π.base x.1 ∈ (chartOpen hP c.1).1 ⊓ (chartOpen hP c'.1).1` using `⟨w.pi_mem c x hx.1, w.pi_mem c' x hx.2⟩`. Take `⟨φ, hφ⟩` from `val_ringHom (toSpecC hP) _ _ hpp (w.pi_closed x)`. Establish `key : ∀ q, eval (w.coord c x) (w.lift c q) * eval (w.coord c' x) (w.lift c' ⟨q.1, c.1 q.1⟩) = eval (w.coord c' x) (w.lift c' q)`. Introduce `q`.

Rewrite using `[w.lift_val c x hx.1, w.lift_val c' x hx.2, w.lift_val c' x hx.2]`. Establish `e` using `congrArg φ (chartCoord_overlap hP c.1 c'.1 q)`. Rewrite `e` using `[map_mul, hφ, hφ, hφ, val_restrict, val_restrict, val_restrict]`. Conclude with `e`. Establish `one' : ∀ k, eval (w.coord c' x) (w.lift c' ⟨k, c'.1 k⟩) = 1` using `fun k => by simp [lift]`.

Establish `hd : ∀ k, eval (w.coord c' x) (w.lift c' ⟨k, c.1 k⟩) ≠ 0`. Introduce `k h0`. Establish `e` using `key ⟨k, c'.1 k⟩`. Rewrite `e` using `[h0, mul_zero, one' k]`. Conclude with `zero_ne_one e`.

Use `⟨fun k => (eval (w.coord c' x) (w.lift c' ⟨k, c.1 k⟩))⁻¹, fun k => inv_ne_zero (hd k),` and prove the remaining obligations. Use function extensionality and compare the values at `fun q => ?_⟩`. Use `show eval (w.coord c x) (w.lift c q) = (eval (w.coord c' x) (w.lift c' ⟨q.1, c.1 q.1⟩))⁻¹ * eval (w.coord c' x) (w.lift c' q)`. Rewrite using `[eq_inv_mul_iff_mul_eq₀ (hd q.1), mul_comm]`. Conclude with `key q`.
-/
theorem compat (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c ∩ w.src c') :
    SameOrbit (fun q => eval (w.coord c x) (w.lift c q)) (fun q => eval (w.coord c' x) (w.lift c' q)) := by
  have := w.lft
  have hpp : w.π.base x.1 ∈ (chartOpen hP c.1).1 ⊓ (chartOpen hP c'.1).1 :=
    ⟨w.pi_mem c x hx.1, w.pi_mem c' x hx.2⟩
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) _ _ hpp (w.pi_closed x)
  have key : ∀ q, eval (w.coord c x) (w.lift c q) * eval (w.coord c' x) (w.lift c' ⟨q.1, c.1 q.1⟩) =
      eval (w.coord c' x) (w.lift c' q) := by
    intro q
    rw [w.lift_val c x hx.1, w.lift_val c' x hx.2, w.lift_val c' x hx.2]
    have e := congrArg φ (chartCoord_overlap hP c.1 c'.1 q)
    rw [map_mul, hφ, hφ, hφ, val_restrict, val_restrict, val_restrict] at e
    exact e
  have one' : ∀ k, eval (w.coord c' x) (w.lift c' ⟨k, c'.1 k⟩) = 1 := fun k => by simp [lift]
  have hd : ∀ k, eval (w.coord c' x) (w.lift c' ⟨k, c.1 k⟩) ≠ 0 := by
    intro k h0
    have e := key ⟨k, c'.1 k⟩
    rw [h0, mul_zero, one' k] at e
    exact zero_ne_one e
  refine ⟨fun k => (eval (w.coord c' x) (w.lift c' ⟨k, c.1 k⟩))⁻¹, fun k => inv_ne_zero (hd k),
    funext fun q => ?_⟩
  show eval (w.coord c x) (w.lift c q) =
    (eval (w.coord c' x) (w.lift c' ⟨q.1, c.1 q.1⟩))⁻¹ * eval (w.coord c' x) (w.lift c' q)
  rw [eq_inv_mul_iff_mul_eq₀ (hd q.1), mul_comm]
  exact key q

/- English proof (translation)
Rewrite using `[w.coord_of_mem c x hx]`. Conclude with `((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x.1 hx x.2).mp (w.regular x.1)`.
-/
theorem regular_coord (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    IsRegularLocalRing (locRing (w.pres c.1 c.2).K (w.coord c x)) := by
  rw [w.coord_of_mem c x hx]
  exact ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x.1 hx x.2).mp (w.regular x.1)

end WData

end

end ReciprocityTheory.AnForm.R
