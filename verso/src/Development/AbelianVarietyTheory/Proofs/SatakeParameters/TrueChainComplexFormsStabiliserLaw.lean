import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv.FormsStd

section Gen

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}

/- English proof (translation)
Unfold `CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat`. Use `congr 1`. Use extensionality with `p`. Simplify using `only [Set.mem_ofPred_eq, nablaSq_eq_delSq]`. Both sides reduce to the same expression.
-/
theorem cSpan_eq_VV (lam : ι → DomWeight n) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, nablaSq_eq_delSq]
  rfl

/- English proof (translation)
Establish `key : ∀ P : Pol ℂ ι n, fnOf (Gr emb σ n) (shiftOf lam) 1 P = evG (fun y : Fr emb σ n => y.1) (fun τ => (lam τ).detShift) (RingHom.id ℂ) P`. Introduce `P`. Use function extensionality and compare the values at `y`. Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, evG, shiftOf]`. Both sides reduce to the same expression.

Unfold `ValC GlobalTheory.KerJ.IsVal`. Rewrite using `[Submodule.mem_map, cSpan_eq_VV]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨P, hP, rfl⟩`. Conclude with `⟨P, hP, key P⟩`.

Introduce and unpack `⟨P, hP, rfl⟩`. Conclude with `⟨P, hP, key P⟩`.
-/
theorem mem_ValC_iff_isVal (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (f : Fr emb σ n → ℂ) :
    f ∈ ValC (Gr emb σ n) lam ↔ GlobalTheory.KerJ.IsVal (fun y : Fr emb σ n => y.1) lam (RingHom.id ℂ) f := by
  have key : ∀ P : Pol ℂ ι n, fnOf (Gr emb σ n) (shiftOf lam) 1 P = evG (fun y : Fr emb σ n => y.1) (fun τ => (lam τ).detShift)
      (RingHom.id ℂ) P := by
    intro P
    funext y
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, evG, shiftOf]
    rfl
  unfold ValC GlobalTheory.KerJ.IsVal
  rw [Submodule.mem_map, cSpan_eq_VV]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, hP, key P⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, hP, key P⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h y y' hy`. Establish `hy' : y = frMul emb σ (S.gam b g) y'` using `Subtype.ext (funext hy)`. Establish `e` using `congrFun h y`. Rewrite `e` using `[GStep.tr, trFr_apply, hy', ← GlobalTheory.Mem.Col2.frMul_mul, inv_mul_cancel, GlobalTheory.Mem.Col2.frMul_one]`.

Rewrite using `[hy']`. Conclude with `e.symm`. Introduce `h`. Use function extensionality and compare the values at `y`. Rewrite using `[GStep.tr, trFr_apply]`.

Use `(h y (frMul emb σ (S.gam b g)⁻¹ y) fun τ => ?_).symm` and prove the remaining obligations. Use `show y.1 τ = _ * ((((S.gam b g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) * y.1 τ)`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`.
-/
theorem tr_eq_iff (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (b : S.β) (g : S.G b) (f : Fr emb σ n → ℂ) :
    S.tr emb σ b g f = f ↔ ∀ y y' : Fr emb σ n,
      (∀ τ, y.1 τ = ((S.gam b g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) * y'.1 τ) →
        f y = σ ((S.chr b g : Kˣ) : K) * f y' := by
  constructor
  · intro h y y' hy
    have hy' : y = frMul emb σ (S.gam b g) y' := Subtype.ext (funext hy)
    have e := congrFun h y
    rw [GStep.tr, trFr_apply, hy', ← GlobalTheory.Mem.Col2.frMul_mul, inv_mul_cancel, GlobalTheory.Mem.Col2.frMul_one] at e
    rw [hy']
    exact e.symm
  · intro h
    funext y
    rw [GStep.tr, trFr_apply]
    refine (h y (frMul emb σ (S.gam b g)⁻¹ y) fun τ => ?_).symm
    show y.1 τ = _ * ((((S.gam b g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) * y.1 τ)
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end Gen

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use extensionality with `y`. Use `show B.host.φ₀ _ = _`. Rewrite using `[← B.embE_φ₀]`. Both sides reduce to the same expression.
-/
theorem embT_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) :
    TaylorLogMetric.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
  funext τ
  ext y
  show B.host.φ₀ _ = _
  rw [← B.embE_φ₀]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Take `⟨c, hc⟩` from `B.R.t_odd`. Establish `h : (((i * ((I.rec7 l Z).R.t + 1) / 2 : ℕ) : ℤ)) = (i : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)` using `by show (((i * (B.R.t + 1) / 2 : ℕ) : ℤ)) = _`. Rewrite using `[hc, show 2 * c + 1 + 1 = 2 * (c + 1) by ring, mul_left_comm, Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _`. Unfold `Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW`. Use `congr 1`. Use function extensionality and compare the values at `r`.

Establish `hx : (((I.tw l l0 Z).fm u a).lam i τ).w r = (Examples₂.lamOf (B.hcW u τ) i).w r` using `rfl`. Rewrite using `[hx, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamTG_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word)
    (a : I.ι) (i : ℕ) : lamTG ((I.tw l l0 Z).fm u a) i = lamT (B.hcW u) i := by
  funext τ
  obtain ⟨c, hc⟩ := B.R.t_odd
  have h : (((i * ((I.rec7 l Z).R.t + 1) / 2 : ℕ) : ℤ)) = (i : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
    show (((i * (B.R.t + 1) / 2 : ℕ) : ℤ)) = _
    rw [hc, show 2 * c + 1 + 1 = 2 * (c + 1) by ring, mul_left_comm, Nat.mul_div_cancel_left _ two_pos,
      Nat.mul_div_cancel_left _ two_pos]
    push_cast
    ring
  show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
  unfold Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
  congr 1
  funext r
  have hx : (((I.tw l l0 Z).fm u a).lam i τ).w r = (Examples₂.lamOf (B.hcW u τ) i).w r := rfl
  rw [hx, h]
  ring

/- English proof (translation)
Introduce `B X I _hOk _hP l Z l0 Qp O hO u a`. Establish `hfr : ∀ i, (O u a).frm i = fun y => y.1` using `fun i => funext (hO.frm u a i)`. Establish `hemb` using `embT_eq I l Z`. Establish `hlaw : ∀ i (c : (I.stp u a i).Cl) (s : (I.stp u a i).Stab c) (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ), (I.stp u a i).tr B.fields.emb B.embLL c.1 s.1 f = f ↔ GlobalTheory.KerJ.LawAt (O u a) i ((((I.stp u a i).gam c.1 s.1 : GL (Fin (B.R.N i)) B.host.E) : Matrix (Fin (B.R.N i)) ( …`. Introduce `i c s f`.

Rewrite using `[tr_eq_iff]`. Unfold `GlobalTheory.KerJ.LawAt`. Simplify using `only [hfr i, hemb]`. Conclude with `Iff.rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `i _ φ hφ c`. Establish `hφ' : ∀ c, φ c ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) ∧ ∀ g : (I.stp u a i).Stab c, (I.stp u a i).tr B.fields.emb B.embLL c.1 g.1 (φ c) = φ c` using `hφ`. Rewrite using `[hfr i, lamTG_eq I l Z l0 u a i]`. Conclude with `(mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).1 (hφ' c).1`. Introduce `i _ _ φ`.

Rewrite using `[hfr i, lamTG_eq I l Z l0 u a i]`. Use `show (∀ c, φ c ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) ∧ ∀ g : (I.stp u a i).Stab c, (I.stp u a i).tr B.fields.emb B.embLL c.1 g.1 (φ c) = φ c) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `hφ c`. Use `⟨(mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).1 (hφ c).1, ?_⟩` and prove the remaining obligations.

Introduce and unpack `g ⟨s, rfl⟩`. Conclude with `(hlaw i c s (φ c)).1 ((hφ c).2 s)`. Introduce `hφ c`. Use `⟨(mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).2 (hφ c).1, fun s => ?_⟩` and prove the remaining obligations. Conclude with `(hlaw i c s (φ c)).2 ((hφ c).2 _ ⟨s, rfl⟩)`.
-/
theorem formsAre_stabStd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ u a, GlobalTheory.KerJ.FormsAre ((I.tw l l0 Z).fm u a) (O u a) (GlobalTheory.Pdv.stabStd I l Z u a) := by
  intro B X I _hOk _hP l Z l0 Qp O hO u a
  have hfr : ∀ i, (O u a).frm i = fun y => y.1 := fun i => funext (hO.frm u a i)
  have hemb := embT_eq I l Z
  have hlaw : ∀ i (c : (I.stp u a i).Cl) (s : (I.stp u a i).Stab c) (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
      (I.stp u a i).tr B.fields.emb B.embLL c.1 s.1 f = f ↔
        GlobalTheory.KerJ.LawAt (O u a) i ((((I.stp u a i).gam c.1 s.1 : GL (Fin (B.R.N i)) B.host.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E),
          B.embLL (((I.stp u a i).chr c.1 s.1 : B.LLˣ) : B.LL)) f := by
    intro i c s f
    rw [tr_eq_iff]
    unfold GlobalTheory.KerJ.LawAt
    simp only [hfr i, hemb]
    exact Iff.rfl
  refine ⟨?_, ?_⟩
  · intro i _ φ hφ c
    have hφ' : ∀ c, φ c ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) ∧
        ∀ g : (I.stp u a i).Stab c, (I.stp u a i).tr B.fields.emb B.embLL c.1 g.1 (φ c) = φ c := hφ
    rw [hfr i, lamTG_eq I l Z l0 u a i]
    exact (mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).1 (hφ' c).1
  · intro i _ _ φ
    rw [hfr i, lamTG_eq I l Z l0 u a i]
    show (∀ c, φ c ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) ∧
        ∀ g : (I.stp u a i).Stab c, (I.stp u a i).tr B.fields.emb B.embLL c.1 g.1 (φ c) = φ c) ↔ _
    constructor
    · intro hφ c
      refine ⟨(mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).1 (hφ c).1, ?_⟩
      rintro g ⟨s, rfl⟩
      exact (hlaw i c s (φ c)).1 ((hφ c).2 s)
    · intro hφ c
      refine ⟨(mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).2 (hφ c).1, fun s => ?_⟩
      exact (hlaw i c s (φ c)).2 ((hφ c).2 _ ⟨s, rfl⟩)

end GlobalTheory.Pdv.FormsStd
