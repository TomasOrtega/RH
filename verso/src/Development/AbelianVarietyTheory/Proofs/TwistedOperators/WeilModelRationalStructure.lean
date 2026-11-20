import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHermitianLogUnitaryBlockDiagonal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CtxExists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfThetaHeisenbergTranslates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstMemFg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.RealDict.CompactCoinv

/- English proof (translation)
Rewrite using `[← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]`. Introduce `l hl`. Set `U : Submodule ℂ Q` to `V ⊔ V.map L`. Use `haveI : FiniteDimensional ℂ U := Module.Finite.iff_fg.2 (hV.sup (hV.map L))`. Establish `h1 : ∀ t, p t ∈ U` using `fun t => Submodule.mem_sup_left (hp t)`.

Establish `h2 : ∀ t, L (p t) ∈ U` using `fun t => Submodule.mem_sup_right ⟨_, hp t, rfl⟩`. Set `ev : Z → (U →ₗ[ℂ] ℂ)` to `fun z => (LinearMap.proj z) ∘ₗ E ∘ₗ U.subtype`. Establish `key : ∀ K ∈ Submodule.span ℂ (Set.range ev), ∀ t, HasDerivAt (fun s => K ⟨p s, h1 s⟩) (K ⟨L (p t), h2 t⟩) t`. Introduce `K hK t`. Proceed by induction on `hK using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨z, rfl⟩` from `hx`. Conclude with `hd t z`. Consider the case `zero => exact hasDerivAt_const _ _`. Consider the case `add x y _ _ hx hy => exact hx.add hy`.

Consider the case `smul a x _ hx => exact hx.const_mul a`. Establish `hm : l ∘ₗ U.subtype ∈ Submodule.span ℂ (Set.range ev)`. Use `FiniteDimensional.mem_span_of_iInf_ker_le_ker fun x hx => ?_` and prove the remaining obligations. Establish `h0 : E x.1 = 0` using `funext fun z => (Submodule.mem_iInf _).1 hx z`. Establish `h3 : x.1 = 0` using `hE (h0.trans (map_zero E).symm)`.

Use `show l x.1 = 0`. Rewrite using `[h3, map_zero]`. Establish `h4 : ∀ t, HasDerivAt (fun s => l (p s)) 0 t` using `fun t => by`. Establish `h5` using `key _ hm t`. Establish `h6 : l (L (p t)) = 0` using `(Submodule.mem_dualAnnihilator l).1 hl _ (hL _)`.

Rewrite using `[← h6]`. Conclude with `h5`. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `is_const_of_deriv_eq_zero (fun t => (h4 t).differentiableAt) (fun t => (h4 t).deriv) 1 0`.
-/
theorem sub_mem_of_path {Q Z : Type} [AddCommGroup Q] [Module ℂ Q] (E : Q →ₗ[ℂ] (Z → ℂ)) (hE : Function.Injective E)
    (C V : Submodule ℂ Q) (hV : V.FG) (L : Q →ₗ[ℂ] Q) (hL : ∀ x, L x ∈ C) (p : ℝ → Q) (hp : ∀ t, p t ∈ V)
    (hd : ∀ t z, HasDerivAt (fun s => E (p s) z) (E (L (p t)) z) t) : p 1 - p 0 ∈ C := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  let U : Submodule ℂ Q := V ⊔ V.map L
  haveI : FiniteDimensional ℂ U := Module.Finite.iff_fg.2 (hV.sup (hV.map L))
  have h1 : ∀ t, p t ∈ U := fun t => Submodule.mem_sup_left (hp t)
  have h2 : ∀ t, L (p t) ∈ U := fun t => Submodule.mem_sup_right ⟨_, hp t, rfl⟩
  let ev : Z → (U →ₗ[ℂ] ℂ) := fun z => (LinearMap.proj z) ∘ₗ E ∘ₗ U.subtype
  have key : ∀ K ∈ Submodule.span ℂ (Set.range ev), ∀ t,
      HasDerivAt (fun s => K ⟨p s, h1 s⟩) (K ⟨L (p t), h2 t⟩) t := by
    intro K hK t
    induction hK using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact hd t z
    | zero => exact hasDerivAt_const _ _
    | add x y _ _ hx hy => exact hx.add hy
    | smul a x _ hx => exact hx.const_mul a
  have hm : l ∘ₗ U.subtype ∈ Submodule.span ℂ (Set.range ev) := by
    refine FiniteDimensional.mem_span_of_iInf_ker_le_ker fun x hx => ?_
    have h0 : E x.1 = 0 := funext fun z => (Submodule.mem_iInf _).1 hx z
    have h3 : x.1 = 0 := hE (h0.trans (map_zero E).symm)
    show l x.1 = 0
    rw [h3, map_zero]
  have h4 : ∀ t, HasDerivAt (fun s => l (p s)) 0 t := fun t => by
    have h5 := key _ hm t
    have h6 : l (L (p t)) = 0 := (Submodule.mem_dualAnnihilator l).1 hl _ (hL _)
    rw [← h6]
    exact h5
  rw [map_sub, sub_eq_zero]
  exact is_const_of_deriv_eq_zero (fun t => (h4 t).differentiableAt) (fun t => (h4 t).deriv) 1 0

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg`. Consider the case `exact _root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg`. Consider the case `(apply _root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg ..)`.
-/
theorem exists_fg_subst {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (P : PolF D b a) :
    ∃ V : Submodule ℂ (PolF D b a), V.FG ∧ ∀ g k, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' g k P ∈ V := by
  first
  | exact @_root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg
  | exact _root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg
  | (apply _root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubstitutionFinitelyGenerated.subst_mem_fg ..)

section Oriented

variable {D : D7} {V W : HSp D} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

/- English proof (translation)
Use `set J := Formalism.REAL.Jm ε with hJ`. Establish `hJJ : J * J = 1` using `GlobalTheory.LieFock.Jm_mul_self ε`. Establish `hJH : Jᴴ = J` using `Formalism.REAL.Jm_conjTranspose ε`. Establish `a1 : F * F⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hF`. Establish `a2 : F⁻¹ * F = 1` using `Matrix.nonsing_inv_mul _ hF`.

Establish `a3 : (F⁻¹)ᴴ * Fᴴ = 1` using `by rw [← conjTranspose_mul, a1, conjTranspose_one]`. Establish `a4 : Fᴴ * (F⁻¹)ᴴ = 1` using `by rw [← conjTranspose_mul, a2, conjTranspose_one]`. Use `set h := F * g * F⁻¹ with hh`. Establish `c1 : Commute h J`. Combine the equalities or inequalities in the displayed calculation.

Establish `c2 : hᴴ * J * h = J`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hh, conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = ((F⁻¹)ᴴ * Fᴴ) * J * (F * F⁻¹) := by rw [hG, hg, ← hG]; simp only [Matrix.mul_assoc]`. Use `_ = J := by rw [a1, a3, Matrix.one_mul, Matrix.mul_one]`.

Establish `c3 : star h * h = 1`. Rewrite using `[Matrix.star_eq_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨H, hH, -, hexp, hcomH⟩` from `GlobalTheory.CartanInt.UnitLog.exists_log h (Matrix.mem_unitaryGroup_iff'.2 c3)`. Establish `hstar : Commute (star h) J`.

Use `c1.star_star` as an intermediate fact. Rewrite `this` using `[Matrix.star_eq_conjTranspose J, hJH]`. Then use the resulting hypothesis. Establish `hK : Commute H J` using `hcomH _ c1 hstar`. Use `set Y := Complex.I • H with hY`. Establish `y1 : Yᴴ = -Y`.

Rewrite using `[hY, conjTranspose_smul, hH, Complex.star_def, Complex.conj_I, neg_smul]`. Establish `y2 : Commute Y J` using `hK.smul_left _`. Establish `y3 : F * (F⁻¹ * Y * F) * F⁻¹ = Y`. Combine the equalities or inequalities in the displayed calculation. Use `⟨F⁻¹ * Y * F, ?_, ?_, fun t => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hG]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Fᴴ * (J * Y - Y * J) * F := by`. Rewrite using `[a1, a3, y1]`.

Simplify using `only [Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_neg]`. Normalize the expressions using the abelian group laws. Use `_ = 0 := by rw [y2.eq, sub_self, Matrix.mul_zero, Matrix.zero_mul]`. Rewrite using `[← GlobalTheory.LieScalar.exp_frame hF, y3, one_smul, ← hexp, hh]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[y3]`. Establish `h1 : (t • Y)ᴴ = -(t • Y)` using `by rw [conjTranspose_smul, star_trivial, y1, smul_neg]`. Use `⟨Matrix.mem_unitaryGroup_iff'.2 ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, h1, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Y)).neg_left, neg_add_cancel, NormedSpace.exp_zero]`. Use `(GlobalTheory.LieScalar.exp_conj_self hJJ ?_).symm` and prove the remaining obligations.

Establish `e : J * Y * J = Y` using `by rw [← y2.eq, Matrix.mul_assoc, hJJ, Matrix.mul_one]`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, e]`.
-/
theorem exists_gen {n : ℕ} {F G g : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (hF : IsUnit F.det)
    (hG : Fᴴ * Formalism.REAL.Jm ε * F = G) (hg : gᴴ * G * g = G) (hc : Commute g (F⁻¹ * Formalism.REAL.Jm ε * F)) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 ∧ NormedSpace.exp ((1 : ℝ) • X) = g ∧
      ∀ t : ℝ, NormedSpace.exp (t • (F * X * F⁻¹)) ∈ Formalism.REAL.Kset ε := by
  set J := Formalism.REAL.Jm ε with hJ
  have hJJ : J * J = 1 := GlobalTheory.LieFock.Jm_mul_self ε
  have hJH : Jᴴ = J := Formalism.REAL.Jm_conjTranspose ε
  have a1 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv _ hF
  have a2 : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul _ hF
  have a3 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← conjTranspose_mul, a1, conjTranspose_one]
  have a4 : Fᴴ * (F⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, a2, conjTranspose_one]
  set h := F * g * F⁻¹ with hh
  have c1 : Commute h J := by
    calc h * J = F * g * F⁻¹ * J * (F * F⁻¹) := by rw [a1, Matrix.mul_one]
      _ = F * (g * (F⁻¹ * J * F)) * F⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (F * F⁻¹) * J * (F * g * F⁻¹) := by rw [hc.eq]; simp only [Matrix.mul_assoc]
      _ = J * h := by rw [a1, Matrix.one_mul]
  have c2 : hᴴ * J * h = J := by
    calc hᴴ * J * h = (F⁻¹)ᴴ * (gᴴ * (Fᴴ * J * F) * g) * F⁻¹ := by
          simp only [hh, conjTranspose_mul, Matrix.mul_assoc]
      _ = ((F⁻¹)ᴴ * Fᴴ) * J * (F * F⁻¹) := by rw [hG, hg, ← hG]; simp only [Matrix.mul_assoc]
      _ = J := by rw [a1, a3, Matrix.one_mul, Matrix.mul_one]
  have c3 : star h * h = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    calc hᴴ * h = hᴴ * h * (J * J) := by rw [hJJ, Matrix.mul_one]
      _ = hᴴ * (h * J) * J := by simp only [Matrix.mul_assoc]
      _ = hᴴ * J * h * J := by rw [c1.eq]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [c2, hJJ]
  obtain ⟨H, hH, -, hexp, hcomH⟩ := GlobalTheory.CartanInt.UnitLog.exists_log h (Matrix.mem_unitaryGroup_iff'.2 c3)
  have hstar : Commute (star h) J := by
    have := c1.star_star
    rwa [Matrix.star_eq_conjTranspose J, hJH] at this
  have hK : Commute H J := hcomH _ c1 hstar
  set Y := Complex.I • H with hY
  have y1 : Yᴴ = -Y := by
    rw [hY, conjTranspose_smul, hH, Complex.star_def, Complex.conj_I, neg_smul]
  have y2 : Commute Y J := hK.smul_left _
  have y3 : F * (F⁻¹ * Y * F) * F⁻¹ = Y := by
    calc _ = (F * F⁻¹) * Y * (F * F⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [a1, Matrix.one_mul, Matrix.mul_one]
  refine ⟨F⁻¹ * Y * F, ?_, ?_, fun t => ?_⟩
  · rw [← hG]
    calc _ = Fᴴ * Yᴴ * ((F⁻¹)ᴴ * Fᴴ) * J * F + Fᴴ * J * (F * F⁻¹) * Y * F := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Fᴴ * (J * Y - Y * J) * F := by
          rw [a1, a3, y1]
          simp only [Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.neg_mul, Matrix.mul_neg]
          abel
      _ = 0 := by rw [y2.eq, sub_self, Matrix.mul_zero, Matrix.zero_mul]
  · rw [← GlobalTheory.LieScalar.exp_frame hF, y3, one_smul, ← hexp, hh]
    calc _ = (F⁻¹ * F) * g * (F⁻¹ * F) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [a2, Matrix.one_mul, Matrix.mul_one]
  · rw [y3]
    have h1 : (t • Y)ᴴ = -(t • Y) := by rw [conjTranspose_smul, star_trivial, y1, smul_neg]
    refine ⟨Matrix.mem_unitaryGroup_iff'.2 ?_, ?_⟩
    · rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, h1,
        ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Y)).neg_left, neg_add_cancel, NormedSpace.exp_zero]
    · refine (GlobalTheory.LieScalar.exp_conj_self hJJ ?_).symm
      have e : J * Y * J = Y := by rw [← y2.eq, Matrix.mul_assoc, hJJ, Matrix.mul_one]
      rw [Matrix.mul_smul, Matrix.smul_mul, e]

def Moves (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (C : Submodule ℂ (PolF D W.rank V.rank))
    (g : GA D V) : Prop :=
  ∀ P, ∃ P', ω (g, 1) (ptF ψ θ A B f P) = ptF ψ θ A B f P' ∧ P' - P ∈ C

/- English proof (translation)
Introduce `P`. Take `⟨P', e', m'⟩` from `h' P`. Take `⟨P'', e, m⟩` from `h P'`. Use `⟨P'', ?_, ?_⟩` and prove the remaining obligations. Establish `: ((g * g', 1) : GA D V × GA D W) = (g, 1) * (g', 1)` using `by rw [Prod.mk_mul_mk, one_mul]`.

Rewrite using `[this, map_mul, Module.End.mul_apply, e', e]`. Rewrite using `[← sub_add_sub_cancel P'' P' P]`. Conclude with `C.add_mem m m'`.
-/
theorem Moves.mul {A : Fr V} {B : Fr W} {f : WO V W → ℂ} {C : Submodule ℂ (PolF D W.rank V.rank)} {g g' : GA D V}
    (h : Moves ψ θ A B ω f C g) (h' : Moves ψ θ A B ω f C g') : Moves ψ θ A B ω f C (g * g') := by
  intro P
  obtain ⟨P', e', m'⟩ := h' P
  obtain ⟨P'', e, m⟩ := h P'
  refine ⟨P'', ?_, ?_⟩
  · have : ((g * g', 1) : GA D V × GA D W) = (g, 1) * (g', 1) := by rw [Prod.mk_mul_mk, one_mul]
    rw [this, map_mul, Module.End.mul_apply, e', e]
  · rw [← sub_add_sub_cancel P'' P' P]
    exact C.add_mem m m'

/- English proof (translation)
Establish `hF : IsUnit (A.fr τ).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)`. Take `⟨X, hX, hg1, hK⟩` from `exists_gen hF (A.fr_gram τ) hg hc`. Establish `hX' : X ∈ lieAt V τ` using `hX`. Take `⟨hL, -⟩` from `GlobalTheory.LieScalar.lieFockAll D V W A B θ ψ χS χT ω f τ aS aT hθ hω hS hT hf`. Take `⟨x, y, -, -, hcf⟩` from `GlobalTheory.CompactFockAction.compactFockAll D V W A B θ ψ χS χT ω f τ aS aT hθ hω hS hT hf h0`.

Set `E` to `pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f`. Establish `hE : Function.Injective E` using `GlobalTheory.LieScalar.ptF_injective hθ hω.std A B hf h0`. Introduce `P`. Take `⟨U, hU, hUm⟩` from `exists_fg_subst τ (A.ε τ) (B.ε τ) P`. Establish `hex : ∀ t : ℝ, ∃ Q ∈ U, ω (oneP θ V τ X t, 1) (E P) = E Q`.

Introduce `t`. Establish `h1` using `hcf _ (hK t) 1 (GlobalTheory.LieScalar.one_mem_K _) P`. Rewrite `h1` using `[GlobalTheory.LieScalar.elt_one hθ B τ, Fr.elt, GlobalTheory.LieScalar.exp_frame hF]`. Conclude with `⟨_, U.smul_mem _ (hUm _ _), h1.trans (map_smul E _ _).symm⟩`. Use `choose p hp hpE using hex`.

Set `L : Module.End ℂ (PolF D W.rank V.rank)` to `GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) - ((aT : ℂ) * X.trace) • 1`. Establish `hm` using `sub_mem_of_path E hE C U hU L (fun Q => hC X hX' Q) p hp fun t z => by`. Establish `h1` using `hL X hX' (p t) z`. Establish `h2 : ∀ s : ℝ, E (p s) z = ω (oneP θ V τ X (s - t), 1) (ptF ψ θ A B f (p t)) z`. Introduce `s`.

Establish `e : ((oneP θ V τ X s, 1) : GA D V × GA D W) = (oneP θ V τ X (s - t), 1) * (oneP θ V τ X t, 1)`. Rewrite using `[Prod.mk_mul_mk, one_mul, ← GlobalTheory.Mem.Lift.oneP_add hθ hX', sub_add_cancel]`. Rewrite using `[← hpE s, e, map_mul, Module.End.mul_apply, hpE t]`. Both sides reduce to the same expression. Simplify using `only [h2]`.

Establish `h3 : E (L (p t)) z = ptF ψ θ A B f (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) (p t) + -((aT : ℂ) * X.trace) • p t) z`. Rewrite using `[neg_smul, ← sub_eq_add_neg]`. Both sides reduce to the same expression. Rewrite using `[h3]`. Rewrite `h1` using `[← sub_self t]`.

Conclude with `HasDerivAt.comp_sub_const t t h1`. Establish `hp0 : p 0 = P`. Use `hE ?_` and prove the remaining obligations. Rewrite using `[← hpE 0, oneP, zero_smul, NormedSpace.exp_zero, GlobalTheory.PointAtPlaceHom.atTau_one hθ]`. Conclude with `LinearMap.congr_fun (map_one ω) _`.

Use `⟨p 1, ?_, hp0 ▸ hm⟩` and prove the remaining obligations. Rewrite using `[← hg1]`. Conclude with `hpE 1`.
-/
theorem moves_atTau (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (A : Fr V) (B : Fr W) {f : WO V W → ℂ}
    (hf : IsVacF ψ θ A B f) (h0 : f ≠ 0) (τ : D.what₂.Tau) {aS aT : ℚ} (hS : HasInfExp D χS τ aS)
    (hT : HasInfExp D χT τ aT) (C : Submodule ℂ (PolF D W.rank V.rank))
    (hC : ∀ X ∈ lieAt V τ, ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (A.ε τ) (B.ε τ)
      ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * X.trace) • P ∈ C)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hc : Commute g (A.cart τ)) :
    Moves ψ θ A B ω f C (atTau θ V τ g) := by
  have hF : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  obtain ⟨X, hX, hg1, hK⟩ := exists_gen hF (A.fr_gram τ) hg hc
  have hX' : X ∈ lieAt V τ := hX
  obtain ⟨hL, -⟩ := GlobalTheory.LieScalar.lieFockAll D V W A B θ ψ χS χT ω f τ aS aT hθ hω hS hT hf
  obtain ⟨x, y, -, -, hcf⟩ := GlobalTheory.CompactFockAction.compactFockAll D V W A B θ ψ χS χT ω f τ aS aT hθ hω hS hT hf h0
  let E := pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f
  have hE : Function.Injective E := GlobalTheory.LieScalar.ptF_injective hθ hω.std A B hf h0
  intro P
  obtain ⟨U, hU, hUm⟩ := exists_fg_subst τ (A.ε τ) (B.ε τ) P
  have hex : ∀ t : ℝ, ∃ Q ∈ U, ω (oneP θ V τ X t, 1) (E P) = E Q := by
    intro t
    have h1 := hcf _ (hK t) 1 (GlobalTheory.LieScalar.one_mem_K _) P
    rw [GlobalTheory.LieScalar.elt_one hθ B τ, Fr.elt, GlobalTheory.LieScalar.exp_frame hF] at h1
    exact ⟨_, U.smul_mem _ (hUm _ _), h1.trans (map_smul E _ _).symm⟩
  choose p hp hpE using hex
  let L : Module.End ℂ (PolF D W.rank V.rank) := GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (A.ε τ) (B.ε τ)
      ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) - ((aT : ℂ) * X.trace) • 1
  have hm := sub_mem_of_path E hE C U hU L (fun Q => hC X hX' Q) p hp fun t z => by
    have h1 := hL X hX' (p t) z
    have h2 : ∀ s : ℝ, E (p s) z = ω (oneP θ V τ X (s - t), 1) (ptF ψ θ A B f (p t)) z := by
      intro s
      have e : ((oneP θ V τ X s, 1) : GA D V × GA D W) = (oneP θ V τ X (s - t), 1) * (oneP θ V τ X t, 1) := by
        rw [Prod.mk_mul_mk, one_mul, ← GlobalTheory.Mem.Lift.oneP_add hθ hX', sub_add_cancel]
      rw [← hpE s, e, map_mul, Module.End.mul_apply, hpE t]
      rfl
    simp only [h2]
    have h3 : E (L (p t)) z = ptF ψ θ A B f (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (A.ε τ) (B.ε τ)
        ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) (p t) + -((aT : ℂ) * X.trace) • p t) z := by
      rw [neg_smul, ← sub_eq_add_neg]
      rfl
    rw [h3]
    rw [← sub_self t] at h1
    exact HasDerivAt.comp_sub_const t t h1
  have hp0 : p 0 = P := by
    refine hE ?_
    rw [← hpE 0, oneP, zero_smul, NormedSpace.exp_zero, GlobalTheory.PointAtPlaceHom.atTau_one hθ]
    exact LinearMap.congr_fun (map_one ω) _
  refine ⟨p 1, ?_, hp0 ▸ hm⟩
  rw [← hg1]
  exact hpE 1

/- English proof (translation)
Establish `key : ∀ s : Finset D.what₂.Tau, ∀ g ∈ GinfC V, (∀ τ, Commute (infMat D.sp.cm.sig V.gram (θ τ) g) (A.cart τ)) → (∀ τ ∉ s, infMat D.sp.cm.sig V.gram (θ τ) g = 1) → Moves ψ θ A B ω f C g`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `g hg _ h1`.

Take `⟨w⟩ : Nonempty (InfinitePlace D.host.F)` from `inferInstance`. Take `⟨τ, -⟩` from `(GlobalTheory.CMTypePlaces.places_bijective D).2 w`. Establish `e : g = 1` using `(GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ 1 (GlobalTheory.PointAtPlaceHom.one_mem_UH _)).unique ⟨hg, h1 _ (Finset.notMem_empty _), fun τ' _ => h1 _ (Finset.notMem_empty _)⟩ ⟨one_mem _, GlobalTheory.PointAtPlaceHom.infMat_one V _, fun _ _ => GlobalTheory.PointAtPlac …`. Substitute `e` using the available equality. Conclude with `fun P => ⟨P, LinearMap.congr_fun (map_one ω) _, by rw [sub_self]; exact C.zero_mem⟩`.

Consider the case `insert τ s hτ ih`. Introduce `g hg hc h1`. Establish `hu` using `GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ`. Establish `ha` using `GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hu`. Use `set a := atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) g) with hadef`.

Establish `k : ∀ φ, infMat D.sp.cm.sig V.gram φ a⁻¹ * infMat D.sp.cm.sig V.gram φ a = 1` using `fun φ => by`. Rewrite using `[← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel, GlobalTheory.PointAtPlaceHom.infMat_one]`. Establish `e1 : infMat D.sp.cm.sig V.gram (θ τ) (a⁻¹ * g) = 1`. Rewrite using `[GlobalTheory.PointAtPlaceHom.infMat_mul, ← ha.2.1, k]`. Establish `e2 : ∀ τ' ≠ τ, infMat D.sp.cm.sig V.gram (θ τ') (a⁻¹ * g) = infMat D.sp.cm.sig V.gram (θ τ') g`.

Introduce `τ' h`. Use `k (θ τ')` as an intermediate fact. Rewrite `this` using `[ha.2.2 τ' h, Matrix.mul_one]`. Rewrite using `[GlobalTheory.PointAtPlaceHom.infMat_mul, this, Matrix.one_mul]`. Rewrite using `[← mul_inv_cancel_left a g]`.

Use `(moves_atTau hθ hω A B hf h0 τ (he τ).1 (he τ).2 C (hC τ) hu (hc τ)).mul (ih _ (mul_mem (inv_mem ha.1) hg) (fun τ' => ?_) fun τ' h => ?_)` and prove the remaining obligations. Distinguish the cases in `c : τ' = τ`. Rewrite using `[c, e1]`. Conclude with `Commute.one_left _`. Rewrite using `[e2 τ' c]`.

Conclude with `hc τ'`. Distinguish the cases in `c : τ' = τ`. Rewrite using `[c, e1]`. Rewrite using `[e2 τ' c]`. Conclude with `h1 τ' fun h' => (Finset.mem_insert.1 h').elim c h`.

Conclude with `key Finset.univ g hg hc fun τ h => absurd (Finset.mem_univ τ) h`.
-/
theorem moves_of_commute (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (A : Fr V) (B : Fr W) {f : WO V W → ℂ}
    (hf : IsVacF ψ θ A B f) (h0 : f ≠ 0) {eS eT : D.what₂.Tau → ℚ}
    (he : ∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) (C : Submodule ℂ (PolF D W.rank V.rank))
    (hC : ∀ τ, ∀ X ∈ lieAt V τ, ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (A.ε τ) (B.ε τ)
      ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P - ((eT τ : ℂ) * X.trace) • P ∈ C)
    (g : GA D V) (hg : g ∈ GinfC V) (hc : ∀ τ, Commute (infMat D.sp.cm.sig V.gram (θ τ) g) (A.cart τ)) :
    Moves ψ θ A B ω f C g := by
  classical
  have key : ∀ s : Finset D.what₂.Tau, ∀ g ∈ GinfC V, (∀ τ, Commute (infMat D.sp.cm.sig V.gram (θ τ) g) (A.cart τ)) →
      (∀ τ ∉ s, infMat D.sp.cm.sig V.gram (θ τ) g = 1) → Moves ψ θ A B ω f C g := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg _ h1
      obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
      obtain ⟨τ, -⟩ := (GlobalTheory.CMTypePlaces.places_bijective D).2 w
      have e : g = 1 := (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ 1 (GlobalTheory.PointAtPlaceHom.one_mem_UH _)).unique
        ⟨hg, h1 _ (Finset.notMem_empty _), fun τ' _ => h1 _ (Finset.notMem_empty _)⟩
        ⟨one_mem _, GlobalTheory.PointAtPlaceHom.infMat_one V _, fun _ _ => GlobalTheory.PointAtPlaceHom.infMat_one V _⟩
      subst e
      exact fun P => ⟨P, LinearMap.congr_fun (map_one ω) _, by rw [sub_self]; exact C.zero_mem⟩
    | insert τ s hτ ih =>
      intro g hg hc h1
      have hu := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
      have ha := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hu
      set a := atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) g) with hadef
      have k : ∀ φ, infMat D.sp.cm.sig V.gram φ a⁻¹ * infMat D.sp.cm.sig V.gram φ a = 1 := fun φ => by
        rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel, GlobalTheory.PointAtPlaceHom.infMat_one]
      have e1 : infMat D.sp.cm.sig V.gram (θ τ) (a⁻¹ * g) = 1 := by
        rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← ha.2.1, k]
      have e2 : ∀ τ' ≠ τ, infMat D.sp.cm.sig V.gram (θ τ') (a⁻¹ * g) = infMat D.sp.cm.sig V.gram (θ τ') g := by
        intro τ' h
        have := k (θ τ')
        rw [ha.2.2 τ' h, Matrix.mul_one] at this
        rw [GlobalTheory.PointAtPlaceHom.infMat_mul, this, Matrix.one_mul]
      rw [← mul_inv_cancel_left a g]
      refine (moves_atTau hθ hω A B hf h0 τ (he τ).1 (he τ).2 C (hC τ) hu (hc τ)).mul
        (ih _ (mul_mem (inv_mem ha.1) hg) (fun τ' => ?_) fun τ' h => ?_)
      · by_cases c : τ' = τ
        · rw [c, e1]; exact Commute.one_left _
        · rw [e2 τ' c]; exact hc τ'
      · by_cases c : τ' = τ
        · rw [c, e1]
        · rw [e2 τ' c]
          exact h1 τ' fun h' => (Finset.mem_insert.1 h').elim c h
  exact key Finset.univ g hg hc fun τ h => absurd (Finset.mem_univ τ) h

end Oriented

section Theta

open scoped Classical in

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Set `A : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)` to `(LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) σ).toContinuousLinearEquiv`. Set `B : (κ' → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ≃ₜ (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)` to `(Homeomorph.piCongrLeft (Y := fun _ => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ).symm`.

Use `Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f, g ∘ B, ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2`. Consider the case `smul c Φ _ h => exact Submodule.smul_mem _ c h`.
-/
theorem rename_mem_schA {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : κ ≃ κ')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : (fun x : κ' → AF F => Φ (x ∘ σ)) ∈ GlobalTheory.WeilM.schA F κ' := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let A : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
      (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) σ).toContinuousLinearEquiv
    let B : (κ' → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ≃ₜ (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := (Homeomorph.piCongrLeft (Y := fun _ => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ).symm
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f, g ∘ B,
      ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩, ?_⟩
    rfl
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h => exact Submodule.smul_mem _ c h

/- English proof (translation)
Set `σ` to `Fintype.equivFin κ`. Establish `e : ∀ (Φ : (κ → AF F) → ℂ) (x y : Fin (Fintype.card κ) → AF F), GlobalTheory.ThetaTransform.thV ψ (fun x => Φ (x ∘ σ)) (x, y) = thetaSum F (schr ψ (x ∘ σ, y ∘ σ) Φ)`. Introduce `Φ x y`. Simplify using `only [GlobalTheory.ThetaTransform.thV, GlobalTheory.WeilM.thetaSum]`. Rewrite using `[← (Equiv.arrowCongr σ.symm (Equiv.refl F)).tsum_eq]`.

Use `tsum_congr fun η => ?_` and prove the remaining obligations. Establish `e : (fun i => algebraMap F (AF F) (Equiv.arrowCongr σ.symm (Equiv.refl F) η i)) = (fun i => algebraMap F (AF F) (η i)) ∘ σ` using `rfl`. Rewrite using `[e]`. Simplify using `only [GlobalTheory.WeilM.schr, comp_equiv_dotProduct_comp_equiv]`. Both sides reduce to the same expression.

Take `⟨lam, ν, hC⟩` from `GlobalTheory.SWQ.ctx_exists F hR ψ hψ (Fintype.card κ) (GlobalTheory.ThetaTransform.half F _) GlobalTheory.ThetaTransform.half_ne_zero`. Establish `h2` using `GlobalTheory.SWQ.eq_of_theta_rho F _ ψ lam ν _ hC _ _ (GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (rename_mem_schA σ hΦ)) (GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (rename_mem_schA σ hΦ')) fun x y => by`. Use `(e Φ x y).trans ((h _).trans (e Φ' x y).symm)` as an intermediate fact. Rewrite `this` using `[GlobalTheory.ThetaTransform.thV_eq_th, GlobalTheory.ThetaTransform.thV_eq_th]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `x`.

Simplify `congrFun h2 (x ∘ σ.symm)` using `[Function.comp_def]`.
-/
theorem eq_of_theta_schr {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}
    (hR : IsTotallyReal F) (hψ : IsCharAF F ψ) {κ : Type} [Fintype κ] {Φ Φ' : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (hΦ' : Φ' ∈ GlobalTheory.WeilM.schA F κ)
    (h : ∀ w, thetaSum F (schr ψ w Φ) = thetaSum F (schr ψ w Φ')) : Φ = Φ' := by
  let σ := Fintype.equivFin κ
  have e : ∀ (Φ : (κ → AF F) → ℂ) (x y : Fin (Fintype.card κ) → AF F),
      GlobalTheory.ThetaTransform.thV ψ (fun x => Φ (x ∘ σ)) (x, y) = thetaSum F (schr ψ (x ∘ σ, y ∘ σ) Φ) := by
    intro Φ x y
    simp only [GlobalTheory.ThetaTransform.thV, GlobalTheory.WeilM.thetaSum]
    rw [← (Equiv.arrowCongr σ.symm (Equiv.refl F)).tsum_eq]
    refine tsum_congr fun η => ?_
    have e : (fun i => algebraMap F (AF F) (Equiv.arrowCongr σ.symm (Equiv.refl F) η i)) =
        (fun i => algebraMap F (AF F) (η i)) ∘ σ := rfl
    rw [e]
    simp only [GlobalTheory.WeilM.schr, comp_equiv_dotProduct_comp_equiv]
    rfl
  obtain ⟨lam, ν, hC⟩ := GlobalTheory.SWQ.ctx_exists F hR ψ hψ (Fintype.card κ) (GlobalTheory.ThetaTransform.half F _)
    GlobalTheory.ThetaTransform.half_ne_zero
  have h2 := GlobalTheory.SWQ.eq_of_theta_rho F _ ψ lam ν _ hC _ _
    (GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (rename_mem_schA σ hΦ))
    (GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (rename_mem_schA σ hΦ')) fun x y => by
      have := (e Φ x y).trans ((h _).trans (e Φ' x y).symm)
      rwa [GlobalTheory.ThetaTransform.thV_eq_th, GlobalTheory.ThetaTransform.thV_eq_th] at this
  funext x
  simpa [Function.comp_def] using congrFun h2 (x ∘ σ.symm)

/- English proof (translation)
Assemble the required witnesses or components as `⟨uᵀ * G, by rw [Matrix.mul_assoc, h, Matrix.mul_one]; rfl⟩`.
-/
theorem exists_transpose_mul {R : Type} [CommRing R] {m d : ℕ} (u : Matrix (Fin m) (Fin d) R)
    {G H : Matrix (Fin m) (Fin m) R} (h : G * H = 1) :
    ∃ x : Matrix (Fin d) (Fin m) R, ((x * H)ᵀ).submatrix id (Equiv.refl (Fin d)) = u :=
  ⟨uᵀ * G, by rw [Matrix.mul_assoc, h, Matrix.mul_one]; rfl⟩

/- English proof (translation)
Use `letI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.invTwo (F := D.host.F)`. Use `eq_of_theta_schr inferInstance hψ.1 hΦ hΦ' fun w => ?_` and prove the remaining obligations. Establish `hGH : G.map (incA D) * (G⁻¹).map (incA D) = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hG.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]`. Take `⟨x, hx⟩` from `exists_transpose_mul (Mo.co.e.symm w) hGH`.

Establish `h2 : GlobalTheory.TripleRead.ptO G (Equiv.refl _) x = Mo.co.e.symm w` using `hx`. Establish `h1` using `congrFun h x`. Simplify using `only [GlobalTheory.TripleRead.thO, h2, Darboux.rho, LinearEquiv.apply_symm_apply] at h1`. Conclude with `h1`.
-/
theorem thO_inj {D : D7} {m d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {G : Matrix (Fin m) (Fin m) D.host.E} (hG : G.det ≠ 0)
    {Φ Φ' : (Fin m × Fin d → AF D.host.F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin d))
    (hΦ' : Φ' ∈ GlobalTheory.WeilM.schA D.host.F (Fin m × Fin d))
    (h : GlobalTheory.TripleRead.thO Mo ψ G (Equiv.refl _) Φ = GlobalTheory.TripleRead.thO Mo ψ G (Equiv.refl _) Φ') : Φ = Φ' := by
  letI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.invTwo (F := D.host.F)
  refine eq_of_theta_schr inferInstance hψ.1 hΦ hΦ' fun w => ?_
  have hGH : G.map (incA D) * (G⁻¹).map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hG.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨x, hx⟩ := exists_transpose_mul (Mo.co.e.symm w) hGH
  have h2 : GlobalTheory.TripleRead.ptO G (Equiv.refl _) x = Mo.co.e.symm w := hx
  have h1 := congrFun h x
  simp only [GlobalTheory.TripleRead.thO, h2, Darboux.rho, LinearEquiv.apply_symm_apply] at h1
  exact h1

/- English proof (translation)
Take `⟨x, hx⟩` from `Function.ne_iff.1 h0`. Use function extensionality and compare the values at `y`. Set `e` to `InfiniteAdeleRing.ringEquiv_mixedSpace F`. Set `z : κ → AF F` to `fun i => (e.symm (y i) - (x i).1, 0)`. Establish `hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z`.

Introduce `u hu`. Establish `hu1 : u.1 = 0` using `e.injective (hu.trans (map_zero e).symm)`. Use function extensionality and compare the values at `i`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show u.1 * _ = 0`.

Rewrite using `[hu1, zero_mul]`. Use `show u.2 * 0 = 0`. Rewrite using `[mul_zero]`. Establish `h1` using `congrFun h (x + z)`. Establish `h2 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + z) i)) = y`.

Use function extensionality and compare the values at `i`. Use `show e ((x i).1 + (e.symm (y i) - (x i).1)) = y i`. Rewrite using `[add_sub_cancel, RingEquiv.apply_symm_apply]`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, h2, hr x z hz] at h1`. Conclude with `mul_right_cancel₀ hx h1`.
-/
theorem eq_of_tens {F : Type} [Field F] [NumberField F] {κ : Type} {f f' : (κ → mixedEmbedding.mixedSpace F) → ℂ}
    {r : (κ → AF F) → ℂ} (hr : ∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → r (x + z) = r x) (h0 : r ≠ 0)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f' r) :
    f = f' := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  funext y
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let z : κ → AF F := fun i => (e.symm (y i) - (x i).1, 0)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
    intro u hu
    have hu1 : u.1 = 0 := e.injective (hu.trans (map_zero e).symm)
    funext i
    refine Prod.ext ?_ ?_
    · show u.1 * _ = 0
      rw [hu1, zero_mul]
    · show u.2 * 0 = 0
      rw [mul_zero]
  have h1 := congrFun h (x + z)
  have h2 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + z) i)) = y := by
    funext i
    show e ((x i).1 + (e.symm (y i) - (x i).1)) = y i
    rw [add_sub_cancel, RingEquiv.apply_symm_apply]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, h2, hr x z hz] at h1
  exact mul_right_cancel₀ hx h1

end Theta

section Reading

variable {D : D7}

/- English proof (translation)
Establish `e : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D)).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k` using `Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _`. Establish `hk : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.in …` using `k.2`. Establish `hu : IsUnit (incA D c)` using `(IsUnit.mk0 c hc).map _`. Establish `hk2 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugat …`. Generalize the expression as in `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k = m at hk`.

Rewrite `hk` using `[h, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul]`. Conclude with `hu.smul_left_cancel.1 hk`. Use `⟨⟨GeneralLinearGroup.map (cA D) k.1, ?_⟩, Subtype.ext (Units.ext e), rfl⟩` and prove the remaining obligations. Use `show (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D)).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) = GlobalTheory.IndefiniteRowSide …`. Rewrite using `[e, hk2]`.
-/
theorem exists_conjU (M : HSp D) {J : Matrix (Fin M.rank) (Fin M.rank) D.host.E} {c : D.host.E} (hc : c ≠ 0)
    (h : J = c • M.gram) (k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    ∃ g : GA D M, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M c h g = k ∧ Formalism.L2.Theta.mt M g = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) := by
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D)).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k :=
    Matrix.ext fun _ _ => Formalism.L2.Theta.cA_cA _
  have hk : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := k.2
  have hu : IsUnit (incA D c) := (IsUnit.mk0 c hc).map _
  have hk2 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram := by
    generalize GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k = m at hk
    rw [h, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hk
    exact hu.smul_left_cancel.1 hk
  refine ⟨⟨GeneralLinearGroup.map (cA D) k.1, ?_⟩, Subtype.ext (Units.ext e), rfl⟩
  show (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D)).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram *
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM M.gram
  rw [e, hk2]

/- English proof (translation)
Consider the cases of `ε`. Establish `h' : Commute x (A.cart τ)` using `by simpa using h.neg_right`. Establish `e : (frSgn false A).cart τ = A.cart τ` using `by show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor false (A.ε τ a)) * A.fr τ = _`. Simplify using `only [Bool.false_xor]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `h'`. Establish `h' : Commute x (A.cart τ)` using `by simpa using h`. Establish `e' : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ)`. Use extensionality with `a b`.

Distinguish the cases in `h : a = b`. Apply the tactic sequence `subst h; cases h' : A.ε τ a <;> simp [Formalism.REAL.Jm, h']`. Simplify using `[Formalism.REAL.Jm, h]`. Establish `e : (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = -A.cart τ`. Rewrite using `[e', Matrix.mul_neg, Matrix.neg_mul]`.

Both sides reduce to the same expression. Use `show Commute x ((A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ)`. Rewrite using `[e]`. Conclude with `h'.neg_right`.
-/
theorem commute_cart_frSgn (ε : Bool) {M : HSp D} (A : Fr M) (τ : D.what₂.Tau) {x : Matrix (Fin M.rank) (Fin M.rank) ℂ}
    (h : Commute x ((if ε then 1 else -1 : ℂ) • A.cart τ)) : Commute x ((frSgn ε A).cart τ) := by
  cases ε
  · have h' : Commute x (A.cart τ) := by simpa using h.neg_right
    have e : (frSgn false A).cart τ = A.cart τ := by
      show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor false (A.ε τ a)) * A.fr τ = _
      simp only [Bool.false_xor]
      rfl
    rw [e]
    exact h'
  · have h' : Commute x (A.cart τ) := by simpa using h
    have e' : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
      ext a b
      by_cases h : a = b
      · subst h; cases h' : A.ε τ a <;> simp [Formalism.REAL.Jm, h']
      · simp [Formalism.REAL.Jm, h]
    have e : (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = -A.cart τ := by
      rw [e', Matrix.mul_neg, Matrix.neg_mul]
      rfl
    show Commute x ((A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ)
    rw [e]
    exact h'.neg_right

/- English proof (translation)
Establish `h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (1 + cA D ((m - 1) i j) - 1)`. Introduce `u hu`. Establish `h2 : u • (m - 1) i j = 0` using `congrFun (congrFun (hm u hu) i) j`. Rewrite using `[add_sub_cancel_left]`. Establish `h3 : cA D (u • (m - 1) i j) = u • cA D ((m - 1) i j)` using `map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) u _`.

Rewrite using `[← h3, h2, RingHom.map_zero]`. Establish `h4` using `GlobalTheory.ConjInfExp.finPart_eq_one _ h1`. Establish `h5 : cA D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) = (1 : Matrix (Fin n) (Fin n) (AE D)) i j` using `congrFun (congrFun (Matrix.map_one (cA D) (RingHom.map_zero _) (RingHom.map_one _)) i) j`. Rewrite `h4` using `[RingHom.map_add, RingHom.map_one, add_eq_left, Matrix.sub_apply, RingHom.map_sub, h5, RingHom.map_sub, sub_eq_zero]`. Conclude with `h4`.
-/
theorem map_finPart_conj {n : ℕ} (m : Matrix (Fin n) (Fin n) (AE D))
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (m - 1)) (i j : Fin n) :
    finPart D (cA D (m i j)) = finPart D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) := by
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (1 + cA D ((m - 1) i j) - 1) := by
    intro u hu
    have h2 : u • (m - 1) i j = 0 := congrFun (congrFun (hm u hu) i) j
    rw [add_sub_cancel_left]
    have h3 : cA D (u • (m - 1) i j) = u • cA D ((m - 1) i j) :=
      map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) u _
    rw [← h3, h2, RingHom.map_zero]
  have h4 := GlobalTheory.ConjInfExp.finPart_eq_one _ h1
  have h5 : cA D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) = (1 : Matrix (Fin n) (Fin n) (AE D)) i j :=
    congrFun (congrFun (Matrix.map_one (cA D) (RingHom.map_zero _) (RingHom.map_one _)) i) j
  rw [RingHom.map_add, RingHom.map_one, add_eq_left, Matrix.sub_apply, RingHom.map_sub, h5, RingHom.map_sub,
    sub_eq_zero] at h4
  exact h4

/- English proof (translation)
Use `show finHom M g = 1`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Establish `h1 : (finHom M g).1 i j = finPart D (Formalism.L2.Theta.mt M g i j)` using `rfl`. Establish `h2 : (finHom M 1).1 i j = finPart D ((1 : Matrix (Fin M.rank) (Fin M.rank) (AE D)) i j)` using `rfl`. Rewrite using `[← map_one (finHom M), h1, h2, hg]`.

Conclude with `map_finPart_conj _ hm i j`.
-/
theorem mem_GinfC_of_conj {M : HSp D} (g : GA D M) (m : Matrix (Fin M.rank) (Fin M.rank) (AE D))
    (hg : Formalism.L2.Theta.mt M g = m.map (cA D))
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (m - 1)) : g ∈ GinfC M := by
  show finHom M g = 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 : (finHom M g).1 i j = finPart D (Formalism.L2.Theta.mt M g i j) := rfl
  have h2 : (finHom M 1).1 i j = finPart D ((1 : Matrix (Fin M.rank) (Fin M.rank) (AE D)) i j) := rfl
  rw [← map_one (finHom M), h1, h2, hg]
  exact map_finPart_conj _ hm i j

/- English proof (translation)
Establish `e1 : τ.1 = (starRingEnd ℂ).comp (tauE D t)` using `RingHom.ext h1`. Establish `e2 : ((starRingEnd ℂ).comp (tauE D t)).comp (algebraMap D.host.F D.host.E) = w.embedding` using `e1 ▸ τ.2`. Establish `e4 : τ = ⟨_, e2⟩` using `Subtype.ext e1`. Use extensionality with `i j`. Establish `h3 : infMat D.sp.cm.sig M.gram (θ t) g i j = θ t (infPart D (Formalism.L2.Theta.mt M g i j))` using `rfl`.

Establish `h4` using `GlobalTheory.RealLift.KLineProof.piInf_cA hCM τ (m i j)`. Establish `h5` using `GlobalTheory.ConjInfExp.piInf_eq θ hθ t w e2 (cA D (m i j))`. Rewrite `h5` using `[← e4]`. Rewrite using `[h3, hg, Matrix.map_apply, Matrix.map_apply]`. Conclude with `star_injective (h5.symm.trans h4)`.
-/
theorem infMat_of_conj {θ : InfFam D} (hθ : IsInfFam θ) (hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig) {M : HSp D}
    (g : GA D M) (m : Matrix (Fin M.rank) (Fin M.rank) (AE D)) (hg : Formalism.L2.Theta.mt M g = m.map (cA D))
    {w : InfinitePlace D.host.F} (τ : GlobalTheory.AdelicU.EmbOver D.host.E w) (t : D.what₂.Tau)
    (h1 : ∀ x, τ.1 x = conj (tauE D t x)) :
    infMat D.sp.cm.sig M.gram (θ t) g = m.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) := by
  have e1 : τ.1 = (starRingEnd ℂ).comp (tauE D t) := RingHom.ext h1
  have e2 : ((starRingEnd ℂ).comp (tauE D t)).comp (algebraMap D.host.F D.host.E) = w.embedding := e1 ▸ τ.2
  have e4 : τ = ⟨_, e2⟩ := Subtype.ext e1
  ext i j
  have h3 : infMat D.sp.cm.sig M.gram (θ t) g i j = θ t (infPart D (Formalism.L2.Theta.mt M g i j)) := rfl
  have h4 := GlobalTheory.RealLift.KLineProof.piInf_cA hCM τ (m i j)
  have h5 := GlobalTheory.ConjInfExp.piInf_eq θ hθ t w e2 (cA D (m i j))
  rw [← e4] at h5
  rw [h3, hg, Matrix.map_apply, Matrix.map_apply]
  exact star_injective (h5.symm.trans h4)

/- English proof (translation)
Establish `e1 : τ.1 = (starRingEnd ℂ).comp (tauE D t')` using `RingHom.ext h1`. Establish `e2` using `τ.2`. Rewrite `e2` using `[e1]`. Use `(GlobalTheory.CMTypePlaces.places_bijective D).1 ?_` and prove the remaining obligations. Use `show InfinitePlace.mk _ = InfinitePlace.mk _`.

Rewrite using `[← InfinitePlace.mk_embedding (InfinitePlace.mk ((tauE D t).comp (algebraMap D.host.F D.host.E))), ← e2, ← InfinitePlace.mk_conjugate_eq]`. Both sides reduce to the same expression.
-/
theorem eq_of_conj_over (t t' : D.what₂.Tau)
    (τ : GlobalTheory.AdelicU.EmbOver D.host.E (InfinitePlace.mk ((tauE D t).comp (algebraMap D.host.F D.host.E))))
    (h1 : ∀ x, τ.1 x = conj (tauE D t' x)) : t' = t := by
  have e1 : τ.1 = (starRingEnd ℂ).comp (tauE D t') := RingHom.ext h1
  have e2 := τ.2
  rw [e1] at e2
  refine (GlobalTheory.CMTypePlaces.places_bijective D).1 ?_
  show InfinitePlace.mk _ = InfinitePlace.mk _
  rw [← InfinitePlace.mk_embedding (InfinitePlace.mk ((tauE D t).comp (algebraMap D.host.F D.host.E))), ← e2,
    ← InfinitePlace.mk_conjugate_eq]
  rfl

/- English proof (translation)
Use `moves_of_commute hθ hω (frSgn ε A) B hvac h0 he _ (fun t Z hZ Q => ?_) _ hg fun t => commute_cart_frSgn ε A t (hc t)` and prove the remaining obligations. Rewrite `hZ` using `[GlobalTheory.SgnIdent.lieAt_sgn ε M t]`. Conclude with `Submodule.subset_span ⟨t, Z, hZ, Q, rfl⟩`.
-/
theorem moves_sgn {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {ε : Bool} {M X : HSp D} (A : Fr M)
    (B : Fr X) {χS χT : (AE D)ˣ →* Circle} {ω : WRep M X} {eS eT : D.what₂.Tau → ℚ} (hω : IsWeil ψ ε M X χS χT ω)
    (he : ∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) {f₀ : WO (sgn ε M) X → ℂ}
    (hvac : IsVacF ψ θ (frSgn ε A) B f₀) (h0 : f₀ ≠ 0) (g : GA D M) (hg : g ∈ GinfC M)
    (hc : ∀ t, Commute (infMat D.sp.cm.sig M.gram (θ t) g) ((if ε then 1 else -1 : ℂ) • A.cart t)) :
    Moves ψ θ (frSgn ε A) B (ω.toSgn ε) f₀ (GlobalTheory.RealQuot.coinv (M := M) ε A B eT) ((ofSgn ε M).symm g) := by
  refine moves_of_commute hθ hω (frSgn ε A) B hvac h0 he _ (fun t Z hZ Q => ?_) _ hg
    fun t => commute_cart_frSgn ε A t (hc t)
  rw [GlobalTheory.SgnIdent.lieAt_sgn ε M t] at hZ
  exact Submodule.subset_span ⟨t, Z, hZ, Q, rfl⟩

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

/- English proof (translation)
The claim follows from `(IsUWeilPair.isUSplitting h).pres p Φ hΦ`.
-/
theorem om_mem_schA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} {Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W}
    {ψ : AddChar (AF F) ℂ} {χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W}
    (h : Mo.IsWeil ψ χX χW om) (p) {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    om p Φ ∈ schA F (Fin n × Fin d) :=
  (IsUWeilPair.isUSplitting h).pres p Φ hΦ

end Reading

end GlobalTheory.RealDict.CompactCoinv

namespace GlobalTheory.RealDict

open GlobalTheory.RealDict.CompactCoinv

/- English proof (translation)
Introduce `_ D ψ θ hψ hθ ε M X A B χS χT ω eS eT hω he Xs Ws Mo ψ' χX χW om τ hP hR Φ _ hrange hΦ k hk f hf f₁ hA`. Take `⟨f₀, r, hvac, h0, hr⟩` from `hΦ`. Take `⟨hCM, -, -, -, -, -, -, -, -, -, hW, -⟩` from `hP`. Rewrite `hf` using `[← hrange]`. Take `⟨P, rfl⟩` from `hf`.

Apply the tactic sequence `have hc : sgE (D := D) ε ≠ 0 := by cases ε <;> simp [sgE]`. Take `⟨g, hgk, hg⟩` from `exists_conjU M hc hR.JX k`. Take `⟨P', hP', hm⟩` from `moves_sgn hθ A B hω he hvac h0 g (mem_GinfC_of_conj g _ hg hk.1) (fun t => by`. Take `⟨t', h1, h2, -⟩` from `hR.cart (InfinitePlace.mk ((tauE D t).comp (algebraMap D.host.F D.host.E)))`. Take `rfl` from `eq_of_conj_over t t' _ h1`.

Rewrite using `[infMat_of_conj hθ hCM g _ hg _ _ h1, ← h2]`. Conclude with `hk.2 _) P`. Establish `h1 : GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hR.JW 1 = 1` using `Subtype.ext (Units.ext rfl)`. Establish `h2` using `hR.transp _ (hr P).1.2 g 1`. Rewrite `h2` using `[hgk, h1, (hr P).2]`.

Establish `h3` using `thO_inj Mo hψ (Formalism.L2.Theta.gram_det_ne (sgn ε M)) (om_mem_schA hW (k, 1) (hr P).1.2) (hr P').1.2 (h2.trans (Eq.trans hP' (hr P').2.symm))`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← GlobalTheory.LieScalar.ptF_one (ψ := ψ) (θ := θ) (frSgn ε A) B f₀, ← (hr 1).2]`.

Use function extensionality and compare the values at `x`. Simplify using `[GlobalTheory.TripleRead.thO, thetaSum, Darboux.rho, schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]`. Establish `h4 : (f₁ : _ → ℂ) = Φ P'` using `eq_of_tens (hr P).1.1 hr0 ((hA r (hr P).1).symm.trans h3)`. Rewrite using `[DFunLike.coe_injective h4, ← map_sub]`. Conclude with `⟨_, hm, rfl⟩`.
-/
theorem sub_mem_map_coinv : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Xs τ, ∀ f ∈ Mo.Pol ψ' τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (k, 1)) f f₁ → f₁ - f ∈ (GlobalTheory.RealQuot.coinv ε A B eT).map Φ := by
  intro _ D ψ θ hψ hθ ε M X A B χS χT ω eS eT hω he Xs Ws Mo ψ' χX χW om τ hP hR Φ _ hrange hΦ k hk f hf f₁ hA
  obtain ⟨f₀, r, hvac, h0, hr⟩ := hΦ
  obtain ⟨hCM, -, -, -, -, -, -, -, -, -, hW, -⟩ := hP
  rw [← hrange] at hf
  obtain ⟨P, rfl⟩ := hf
  have hc : sgE (D := D) ε ≠ 0 := by cases ε <;> simp [sgE]
  obtain ⟨g, hgk, hg⟩ := exists_conjU M hc hR.JX k
  obtain ⟨P', hP', hm⟩ := moves_sgn hθ A B hω he hvac h0 g (mem_GinfC_of_conj g _ hg hk.1) (fun t => by
    obtain ⟨t', h1, h2, -⟩ := hR.cart (InfinitePlace.mk ((tauE D t).comp (algebraMap D.host.F D.host.E)))
    obtain rfl := eq_of_conj_over t t' _ h1
    rw [infMat_of_conj hθ hCM g _ hg _ _ h1, ← h2]
    exact hk.2 _) P
  have h1 : GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hR.JW 1 = 1 := Subtype.ext (Units.ext rfl)
  have h2 := hR.transp _ (hr P).1.2 g 1
  rw [hgk, h1, (hr P).2] at h2
  have h3 := thO_inj Mo hψ (Formalism.L2.Theta.gram_det_ne (sgn ε M))
    (om_mem_schA hW (k, 1) (hr P).1.2) (hr P').1.2 (h2.trans (Eq.trans hP' (hr P').2.symm))
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply h0
    rw [← GlobalTheory.LieScalar.ptF_one (ψ := ψ) (θ := θ) (frSgn ε A) B f₀, ← (hr 1).2]
    funext x
    simp [GlobalTheory.TripleRead.thO, thetaSum, Darboux.rho, schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  have h4 : (f₁ : _ → ℂ) = Φ P' := eq_of_tens (hr P).1.1 hr0 ((hA r (hr P).1).symm.trans h3)
  rw [DFunLike.coe_injective h4, ← map_sub]
  exact ⟨_, hm, rfl⟩

end GlobalTheory.RealDict

end
