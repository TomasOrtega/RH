import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalDiscPointsValuationIntegers
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MulFConstAndMap

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalPts

variable {O : Type} [CommRing O] {d : ℕ}

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.1 q.2)`.
-/
private theorem hasSub {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.1 q.2)

private def evA {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) : PS O m d →ₐ[O] PS O n d :=
  MvPowerSeries.substAlgHom (hasSub a ha)

/- English proof (translation)
Unfold `evA ev`. Rewrite using `[MvPowerSeries.coe_substAlgHom]`.
-/
private theorem evA_apply {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS O m d) : evA a ha f = ev a f := by
  unfold evA ev
  rw [MvPowerSeries.coe_substAlgHom]

/- English proof (translation)
Unfold `ev`. Rewrite using `[MvPowerSeries.subst_X (hasSub a ha)]`.
-/
private theorem ev_X {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (q : Fin m × Fin d) :
    ev a (MvPowerSeries.X q) = a q.1 q.2 := by
  unfold ev
  rw [MvPowerSeries.subst_X (hasSub a ha)]

/- English proof (translation)
The claim follows from `MvPowerSeries.constantCoeff_subst_eq_zero (hasSub a ha) (fun q => ha q.1 q.2) hf`.
-/
private theorem const_ev {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS O m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSub a ha) (fun q => ha q.1 q.2) hf

/- English proof (translation)
Introduce `i j`. Use `fin_cases i`. Conclude with `ha j`.
-/
private theorem c1 {n : ℕ} {a : Pt O n d} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) :
    ∀ i j, MvPowerSeries.constantCoeff ((![a] : Fin 1 → Pt O n d) i j) = 0 := by
  intro i j
  fin_cases i
  exact ha j

/- English proof (translation)
Introduce `i j`. Use `fin_cases i`. Conclude with `ha j`. Conclude with `hb j`.
-/
private theorem c2 {n : ℕ} {a b : Pt O n d} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) :
    ∀ i j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt O n d) i j) = 0 := by
  intro i j
  fin_cases i
  · exact ha j
  · exact hb j

/- English proof (translation)
Introduce `j`. Simplify using `[pt]`.
-/
private theorem cpt {n : ℕ} (i : Fin n) : ∀ j, MvPowerSeries.constantCoeff (pt O d i j) = 0 := by
  intro j
  simp [pt]

private def origin (O : Type) [CommRing O] (d : ℕ) : PS O 1 d →ₐ[O] O :=
  { (MvPowerSeries.constantCoeff : PS O 1 d →+* O) with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

/- English proof (translation)
Establish `hX : ∀ (n : ℕ) (Φ : PS O n d →ₐ[O] O) q, ¬ IsUnit (Φ (MvPowerSeries.X q))` using `fun n Φ q => hN n Φ _ (by simp)`. Establish `hext : ∀ (n : ℕ) (Φ Ψ : PS O n d →ₐ[O] O), (∀ i j, Φ (MvPowerSeries.X (i, j)) = Ψ (MvPowerSeries.X (i, j))) → Φ = Ψ` using `fun n Φ Ψ h => (hE n _ (hX n Ψ)).unique (fun q => h q.1 q.2) (fun _ => rfl)`. Establish `hext1 : ∀ (Φ Ψ : PS O 1 d →ₐ[O] O), (∀ j, Φ (MvPowerSeries.X (0, j)) = Ψ (MvPowerSeries.X (0, j))) → Φ = Ψ` using `fun Φ Ψ h => hext 1 Φ Ψ (fun i j => by rw [Subsingleton.elim i 0]; exact h j)`. Establish `hK : ∀ (m n : ℕ) (Φ : PS O n d →ₐ[O] O) (Ψ : PS O m d →ₐ[O] O) (a : Fin m → Pt O n d), (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) → (∀ i j, Ψ (MvPowerSeries.X (i, j)) = Φ (a i j)) → ∀ f, Ψ f = Φ (ev a f)`. Introduce `m n Φ Ψ a ha h f`.

Establish `: Ψ = Φ.comp (evA a ha)` using `hext m _ _ (fun i j => by`. Rewrite using `[AlgHom.comp_apply, evA_apply, ev_X a ha, h])`. Rewrite using `[this, AlgHom.comp_apply, evA_apply]`. Establish `hP : ∀ (n : ℕ) (φ : Fin n → (PS O 1 d →ₐ[O] O)), ∃ Φ : PS O n d →ₐ[O] O, ∀ i j, Φ (MvPowerSeries.X (i, j)) = φ i (MvPowerSeries.X (0, j))`. Introduce `n φ`.

Take `⟨Φ, h, -⟩` from `hE n (fun q => φ q.1 (MvPowerSeries.X (0, q.2))) (fun q => hX 1 _ _)`. Conclude with `⟨Φ, fun i j => h (i, j)⟩`. Use `choose P hP using hP`. Establish `cF : ∀ i j, MvPowerSeries.constantCoeff ((![F.F] : Fin 1 → Pt O 2 d) i j) = 0` using `c1 F.const`. Set `add : (PS O 1 d →ₐ[O] O) → (PS O 1 d →ₐ[O] O) → (PS O 1 d →ₐ[O] O)` to `fun φ φ' => (P 2 ![φ, φ']).comp (evA ![F.F] cF)`.

Establish `hadd : ∀ φ φ' f, add φ φ' f = P 2 ![φ, φ'] (ev (n` using `2) ![F.F] f) := by`. Introduce `φ φ' f`. Simplify using `only [add, AlgHom.comp_apply, evA_apply]`. Establish `haddX : ∀ φ φ' j, add φ φ' (MvPowerSeries.X (0, j)) = P 2 ![φ, φ'] (F.F j)`. Introduce `φ φ' j`.

Rewrite using `[hadd, ev_X _ cF]`. Both sides reduce to the same expression. Establish `hS : ∀ (n : ℕ) (Φ : PS O n d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O) (a b : Pt O n d), (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → (∀ j, MvPowerSeries.constantCoeff (b j) = 0) → (∀ j, φ (MvPowerSeries.X (0, j)) = Φ (a j)) → (∀ j, φ' (MvPowerSeries.X (0, j)) = Φ (b j)) → ∀ j, add φ …`. Introduce `n Φ φ φ' a b ha hb h h' j`. Rewrite using `[haddX]`.

Use `hK 2 n Φ _ _ (c2 ha hb) (fun i k => ?_) _` and prove the remaining obligations. Rewrite using `[hP]`. Use `fin_cases i`. Conclude with `h k`. Conclude with `h' k`.

Establish `h0 : ∀ f, origin O d f = MvPowerSeries.constantCoeff f` using `fun _ => rfl`. Establish `hcomm : ∀ φ φ', add φ φ' = add φ' φ`. Introduce `φ φ'`. Use `hext1 _ _ (fun j => ?_)` and prove the remaining obligations. Rewrite using `[hS 2 (P 2 ![φ, φ']) φ' φ (pt O d 1) (pt O d 0) (cpt 1) (cpt 0) (fun k => (hP 2 ![φ, φ'] 1 k).symm) (fun k => (hP 2 ![φ, φ'] 0 k).symm), F.comm, haddX]`.

Establish `hzero : ∀ φ, add (origin O d) φ = φ`. Introduce `φ`. Use `hext1 _ _ (fun j => ?_)` and prove the remaining obligations. Rewrite using `[hS 1 φ (origin O d) φ 0 (pt O d 0) (fun _ => by simp) (cpt 0) (fun k => by simp [h0]) (fun k => rfl), F.unit]`. Establish `hassoc : ∀ φ φ' φ'', add (add φ φ') φ'' = add φ (add φ' φ'')`.

Introduce `φ φ' φ''`. Use `hext1 _ _ (fun j => ?_)` and prove the remaining obligations. Establish `e0` using `fun k => (hP 3 ![φ, φ', φ''] 0 k).symm`. Establish `e1` using `fun k => (hP 3 ![φ, φ', φ''] 1 k).symm`. Establish `e2` using `fun k => (hP 3 ![φ, φ', φ''] 2 k).symm`.

Rewrite using `[hS 3 (P 3 ![φ, φ', φ'']) (add φ φ') φ'' (fun l => ev (n := 3) ![pt O d 0, pt O d 1] (F.F l)) (pt O d 2) (fun l => const_ev _ (c2 (cpt 0) (cpt 1)) _ (F.const l)) (cpt 2) (hS 3 _ φ φ' _ _ (cpt 0) (cpt 1) e0 e1) e2, hS 3 (P 3 ![φ, φ', φ'']) φ (add φ' φ'') (pt O d 0) (fun l => ev (n …`. Use `letI : Add (PS O 1 d →ₐ[O] O) := ⟨add⟩`. Use `letI : Zero (PS O 1 d →ₐ[O] O) := ⟨origin O d⟩`. Use `letI inst : AddCommMonoid (PS O 1 d →ₐ[O] O) := { add_assoc := hassoc zero_add := hzero add_zero := fun φ => (hcomm φ _).trans (hzero φ) add_comm := hcomm nsmul := nsmulRec }`. Use `⟨inst, ?_, h0, ?_⟩` and prove the remaining obligations.

Introduce `φ φ' ψ`. Express the relevant statement in the definitionally equal form `_ ↔ ψ = add φ φ'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Φ, h1, h2, h3⟩`. Establish `: Φ = P 2 ![φ, φ']`.

Use `hext 2 _ _ (fun i j => ?_)` and prove the remaining obligations. Rewrite using `[hP]`. Use `fin_cases i`. Use `h1 (MvPowerSeries.X (0, j))` as an intermediate fact. Rewrite `this` using `[ev_X _ (c1 (cpt 0))]`.

Conclude with `this`. Use `h2 (MvPowerSeries.X (0, j))` as an intermediate fact. Rewrite `this` using `[ev_X _ (c1 (cpt 1))]`. Conclude with `this`. Use `ext1 f`.

Rewrite using `[hadd, ← this, h3]`. Introduce and unpack `rfl`. Use `⟨P 2 ![φ, φ'], fun f => ?_, fun f => ?_, fun f => (hadd φ φ' f).symm⟩` and prove the remaining obligations. Use `(hK 1 2 _ φ _ (c1 (cpt 0)) (fun i j => ?_) f).symm fin_cases i` and prove the remaining obligations. Conclude with `(hP 2 ![φ, φ'] 0 j).symm`.

Use `(hK 1 2 _ φ' _ (c1 (cpt 1)) (fun i j => ?_) f).symm fin_cases i` and prove the remaining obligations. Conclude with `(hP 2 ![φ, φ'] 1 j).symm`. Introduce `N φ`. Establish `hmul : ∀ (N : ℕ) j, (N • φ) (MvPowerSeries.X (0, j)) = φ (mulF F.F N j)`. Introduce `N`.

Proceed by induction on `N with`. Consider the case `zero`. Introduce `j`. Rewrite using `[zero_nsmul]`. Express the relevant statement in the definitionally equal form `origin O d _ = φ 0`.

Simplify using `[h0]`. Consider the case `succ n ih`. Introduce `j`. Rewrite using `[succ_nsmul]`. Conclude with `hS 1 φ (n • φ) φ (mulF F.F n) (pt O d 0) (GlobalTheory.FormalMul.constantCoeff_mulF F.F F.const n) (cpt 0) ih (fun _ => rfl) j`.

Establish `hz : ∀ j, (0 : PS O 1 d →ₐ[O] O) (MvPowerSeries.X (0, j)) = 0`. Introduce `j`. Express the relevant statement in the definitionally equal form `origin O d _ = 0`. Simplify using `[h0]`. Prove the components needed by the constructor for the conclusion.

Introduce `h j`. Rewrite using `[← hmul, h, hz]`. Introduce `h`. Conclude with `hext1 _ _ (fun j => by rw [hmul, hz, h j])`.
-/
private theorem general
    (hE : ∀ (n : ℕ) (c : Fin n × Fin d → O), (∀ q, ¬ IsUnit (c q)) →
      ∃! Φ : PS O n d →ₐ[O] O, ∀ q, Φ (MvPowerSeries.X q) = c q)
    (hN : ∀ (n : ℕ) (Φ : PS O n d →ₐ[O] O) (f : PS O n d), MvPowerSeries.constantCoeff f = 0 → ¬ IsUnit (Φ f))
    (F : FGLaw O d) :
    ∃ inst : AddCommMonoid (PS O 1 d →ₐ[O] O), letI := inst
      (∀ φ φ' ψ, IsSum F.F φ φ' ψ ↔ ψ = φ + φ') ∧
      (∀ f, (0 : PS O 1 d →ₐ[O] O) f = MvPowerSeries.constantCoeff f) ∧
      ∀ (N : ℕ) (φ : PS O 1 d →ₐ[O] O), N • φ = 0 ↔ Killed F.F N φ := by
  have hX : ∀ (n : ℕ) (Φ : PS O n d →ₐ[O] O) q, ¬ IsUnit (Φ (MvPowerSeries.X q)) :=
    fun n Φ q => hN n Φ _ (by simp)
  have hext : ∀ (n : ℕ) (Φ Ψ : PS O n d →ₐ[O] O),
      (∀ i j, Φ (MvPowerSeries.X (i, j)) = Ψ (MvPowerSeries.X (i, j))) → Φ = Ψ :=
    fun n Φ Ψ h => (hE n _ (hX n Ψ)).unique (fun q => h q.1 q.2) (fun _ => rfl)
  have hext1 : ∀ (Φ Ψ : PS O 1 d →ₐ[O] O),
      (∀ j, Φ (MvPowerSeries.X (0, j)) = Ψ (MvPowerSeries.X (0, j))) → Φ = Ψ :=
    fun Φ Ψ h => hext 1 Φ Ψ (fun i j => by rw [Subsingleton.elim i 0]; exact h j)
  have hK : ∀ (m n : ℕ) (Φ : PS O n d →ₐ[O] O) (Ψ : PS O m d →ₐ[O] O) (a : Fin m → Pt O n d),
      (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) →
      (∀ i j, Ψ (MvPowerSeries.X (i, j)) = Φ (a i j)) → ∀ f, Ψ f = Φ (ev a f) := by
    intro m n Φ Ψ a ha h f
    have : Ψ = Φ.comp (evA a ha) := hext m _ _ (fun i j => by
      rw [AlgHom.comp_apply, evA_apply, ev_X a ha, h])
    rw [this, AlgHom.comp_apply, evA_apply]
  have hP : ∀ (n : ℕ) (φ : Fin n → (PS O 1 d →ₐ[O] O)), ∃ Φ : PS O n d →ₐ[O] O,
      ∀ i j, Φ (MvPowerSeries.X (i, j)) = φ i (MvPowerSeries.X (0, j)) := by
    intro n φ
    obtain ⟨Φ, h, -⟩ := hE n (fun q => φ q.1 (MvPowerSeries.X (0, q.2))) (fun q => hX 1 _ _)
    exact ⟨Φ, fun i j => h (i, j)⟩
  choose P hP using hP
  have cF : ∀ i j, MvPowerSeries.constantCoeff ((![F.F] : Fin 1 → Pt O 2 d) i j) = 0 := c1 F.const
  let add : (PS O 1 d →ₐ[O] O) → (PS O 1 d →ₐ[O] O) → (PS O 1 d →ₐ[O] O) :=
    fun φ φ' => (P 2 ![φ, φ']).comp (evA ![F.F] cF)
  have hadd : ∀ φ φ' f, add φ φ' f = P 2 ![φ, φ'] (ev (n := 2) ![F.F] f) := by
    intro φ φ' f
    simp only [add, AlgHom.comp_apply, evA_apply]
  have haddX : ∀ φ φ' j, add φ φ' (MvPowerSeries.X (0, j)) = P 2 ![φ, φ'] (F.F j) := by
    intro φ φ' j
    rw [hadd, ev_X _ cF]
    rfl
  have hS : ∀ (n : ℕ) (Φ : PS O n d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O) (a b : Pt O n d),
      (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → (∀ j, MvPowerSeries.constantCoeff (b j) = 0) →
      (∀ j, φ (MvPowerSeries.X (0, j)) = Φ (a j)) → (∀ j, φ' (MvPowerSeries.X (0, j)) = Φ (b j)) →
      ∀ j, add φ φ' (MvPowerSeries.X (0, j)) = Φ (ev ![a, b] (F.F j)) := by
    intro n Φ φ φ' a b ha hb h h' j
    rw [haddX]
    refine hK 2 n Φ _ _ (c2 ha hb) (fun i k => ?_) _
    rw [hP]
    fin_cases i
    · exact h k
    · exact h' k
  have h0 : ∀ f, origin O d f = MvPowerSeries.constantCoeff f := fun _ => rfl
  have hcomm : ∀ φ φ', add φ φ' = add φ' φ := by
    intro φ φ'
    refine hext1 _ _ (fun j => ?_)
    rw [hS 2 (P 2 ![φ, φ']) φ' φ (pt O d 1) (pt O d 0) (cpt 1) (cpt 0)
      (fun k => (hP 2 ![φ, φ'] 1 k).symm) (fun k => (hP 2 ![φ, φ'] 0 k).symm), F.comm, haddX]
  have hzero : ∀ φ, add (origin O d) φ = φ := by
    intro φ
    refine hext1 _ _ (fun j => ?_)
    rw [hS 1 φ (origin O d) φ 0 (pt O d 0) (fun _ => by simp) (cpt 0)
      (fun k => by simp [h0]) (fun k => rfl), F.unit]
  have hassoc : ∀ φ φ' φ'', add (add φ φ') φ'' = add φ (add φ' φ'') := by
    intro φ φ' φ''
    refine hext1 _ _ (fun j => ?_)
    have e0 := fun k => (hP 3 ![φ, φ', φ''] 0 k).symm
    have e1 := fun k => (hP 3 ![φ, φ', φ''] 1 k).symm
    have e2 := fun k => (hP 3 ![φ, φ', φ''] 2 k).symm
    rw [hS 3 (P 3 ![φ, φ', φ'']) (add φ φ') φ'' (fun l => ev (n := 3) ![pt O d 0, pt O d 1] (F.F l)) (pt O d 2)
        (fun l => const_ev _ (c2 (cpt 0) (cpt 1)) _ (F.const l)) (cpt 2)
        (hS 3 _ φ φ' _ _ (cpt 0) (cpt 1) e0 e1) e2,
      hS 3 (P 3 ![φ, φ', φ'']) φ (add φ' φ'') (pt O d 0) (fun l => ev (n := 3) ![pt O d 1, pt O d 2] (F.F l))
        (cpt 0) (fun l => const_ev _ (c2 (cpt 1) (cpt 2)) _ (F.const l))
        e0 (hS 3 _ φ' φ'' _ _ (cpt 1) (cpt 2) e1 e2), F.assoc]
  letI : Add (PS O 1 d →ₐ[O] O) := ⟨add⟩
  letI : Zero (PS O 1 d →ₐ[O] O) := ⟨origin O d⟩
  letI inst : AddCommMonoid (PS O 1 d →ₐ[O] O) :=
    { add_assoc := hassoc
      zero_add := hzero
      add_zero := fun φ => (hcomm φ _).trans (hzero φ)
      add_comm := hcomm
      nsmul := nsmulRec }
  refine ⟨inst, ?_, h0, ?_⟩
  · intro φ φ' ψ
    change _ ↔ ψ = add φ φ'
    constructor
    · rintro ⟨Φ, h1, h2, h3⟩
      have : Φ = P 2 ![φ, φ'] := by
        refine hext 2 _ _ (fun i j => ?_)
        rw [hP]
        fin_cases i
        · have := h1 (MvPowerSeries.X (0, j))
          rw [ev_X _ (c1 (cpt 0))] at this
          exact this
        · have := h2 (MvPowerSeries.X (0, j))
          rw [ev_X _ (c1 (cpt 1))] at this
          exact this
      ext1 f
      rw [hadd, ← this, h3]
    · rintro rfl
      refine ⟨P 2 ![φ, φ'], fun f => ?_, fun f => ?_, fun f => (hadd φ φ' f).symm⟩
      · refine (hK 1 2 _ φ _ (c1 (cpt 0)) (fun i j => ?_) f).symm
        fin_cases i
        exact (hP 2 ![φ, φ'] 0 j).symm
      · refine (hK 1 2 _ φ' _ (c1 (cpt 1)) (fun i j => ?_) f).symm
        fin_cases i
        exact (hP 2 ![φ, φ'] 1 j).symm
  · intro N φ
    have hmul : ∀ (N : ℕ) j, (N • φ) (MvPowerSeries.X (0, j)) = φ (mulF F.F N j) := by
      intro N
      induction N with
      | zero =>
        intro j
        rw [zero_nsmul]
        change origin O d _ = φ 0
        simp [h0]
      | succ n ih =>
        intro j
        rw [succ_nsmul]
        exact hS 1 φ (n • φ) φ (mulF F.F n) (pt O d 0)
          (GlobalTheory.FormalMul.constantCoeff_mulF F.F F.const n) (cpt 0) ih (fun _ => rfl) j
    have hz : ∀ j, (0 : PS O 1 d →ₐ[O] O) (MvPowerSeries.X (0, j)) = 0 := by
      intro j
      change origin O d _ = 0
      simp [h0]
    constructor
    · intro h j
      rw [← hmul, h, hz]
    · intro h
      exact hext1 _ _ (fun j => by rw [hmul, hz, h j])

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ hv _ _ d F`. Conclude with `general (fun n => (GlobalTheory.ChF.formalDisc_points_integers p C v O hv (Fin n × Fin d)).1) (fun n => (GlobalTheory.ChF.formalDisc_points_integers p C v O hv (Fin n × Fin d)).2.1) F`.
-/
theorem points_addCommMonoid : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), ∃ inst : AddCommMonoid (PS O 1 d →ₐ[O] O), letI := inst; (∀ φ φ' ψ, IsSum F.F φ φ' ψ ↔ ψ = φ + φ') ∧ (∀ f, (0 : PS O 1 d →ₐ[O] O) f = MvPowerSeries.constantCoeff f) ∧ ∀ (N : ℕ) (φ : PS O 1 d →ₐ[O] O), N • φ = 0 ↔ Killed F.F N φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F
  exact general (fun n => (GlobalTheory.ChF.formalDisc_points_integers p C v O hv (Fin n × Fin d)).1)
    (fun n => (GlobalTheory.ChF.formalDisc_points_integers p C v O hv (Fin n × Fin d)).2.1) F

end GlobalTheory.FormalPts
