import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceParahoricSubgroupCharacter
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.ParaOpp

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

/- English proof (translation)
Establish `cc : ∀ x : L, IsCMField.complexConj L (IsCMField.complexConj L x) = x` using `fun x => IsCMField.complexConj_apply_apply L x`. Establish `fix : ∀ z : L, IsCMField.complexConj L z = z → φ z = ψ z`. Introduce `z hz`. Establish `hm` using `(IsCMField.complexConj_eq_self_iff L z).1 hz`. Establish `e : algebraMap L⁺ L ⟨z, hm⟩ = z` using `rfl`.

Rewrite using `[← e, AlgHom.commutes, AlgHom.commutes]`. Establish `h2 : (2 : F) ≠ 0`. Use `(algebraMap L⁺ F).injective.ne (two_ne_zero (α := L⁺))` as an intermediate fact. Rewrite `this` using `[map_ofNat, map_zero]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨x0, hx0⟩ : ∃ x, IsCMField.complexConj L x ≠ x := by`.

Take `⟨a, ha⟩` from `DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)`. Conclude with `⟨a, ha⟩`. Use `set y := x0 - IsCMField.complexConj L x0 with hy`. Establish `hyc : IsCMField.complexConj L y = -y`. Rewrite using `[hy, map_sub, cc]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hy0 : y ≠ 0`. Introduce `h`. Apply `hx0` to reduce the goal to its premises. Rewrite `h` using `[hy, sub_eq_zero]`.

Conclude with `h.symm`. Establish `hyy : φ y * φ y = ψ y * ψ y`. Rewrite using `[← map_mul, ← map_mul]`. Conclude with `fix _ (by rw [map_mul, hyc]; ring)`. Establish `fp : ∀ x : L, IsCMField.complexConj L (x + IsCMField.complexConj L x) = x + IsCMField.complexConj L x`.

Introduce `x`. Rewrite using `[map_add, cc, add_comm]`. Establish `fq : ∀ x : L, IsCMField.complexConj L ((x - IsCMField.complexConj L x) * y⁻¹) = (x - IsCMField.complexConj L x) * y⁻¹`. Introduce `x`. Rewrite using `[map_mul, map_inv₀, hyc, map_sub, cc]`.

Put the polynomial expressions in normal form. Establish `two : ∀ (χ : L →ₐ[L⁺] F), χ (2 : L) = 2` using `fun χ => map_ofNat χ 2`. Establish `dec : ∀ (χ : L →ₐ[L⁺] F) (x : L), 2 * χ x = χ (x + IsCMField.complexConj L x) + χ ((x - IsCMField.complexConj L x) * y⁻¹) * χ y`. Introduce `χ x`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [map_add, map_mul]`. Establish `decc : ∀ (χ : L →ₐ[L⁺] F) (x : L), 2 * χ (IsCMField.complexConj L x) = χ (x + IsCMField.complexConj L x) - χ ((x - IsCMField.complexConj L x) * y⁻¹) * χ y`.

Introduce `χ x`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := by rw [map_sub, map_mul]`. Establish `hfac : (φ y - ψ y) * (φ y + ψ y) = 0` using `by linear_combination hyy`. Break down `mul_eq_zero.1 hfac with h | h` into its components or cases. Use `left`. Use extensionality with `x`.

Establish `e1` using `dec φ x`. Rewrite `e1` using `[fix _ (fp x), fix _ (fq x), show φ y = ψ y from sub_eq_zero.1 h, ← dec ψ x]`. Conclude with `mul_left_cancel₀ h2 e1`. Use `right`. Introduce `x`.

Establish `e1` using `dec φ x`. Rewrite `e1` using `[fix _ (fp x), fix _ (fq x), show φ y = -ψ y from eq_neg_of_add_eq_zero_left h]`. Establish `: 2 * φ x = 2 * ψ (IsCMField.complexConj L x)` using `by rw [e1, decc ψ x]; ring`. Conclude with `mul_left_cancel₀ h2 this`.
-/
theorem algHom_eq_or_conj {F : Type} [Field F] [Algebra L⁺ F] (φ ψ : L →ₐ[L⁺] F) :
    φ = ψ ∨ ∀ x, φ x = ψ (IsCMField.complexConj L x) := by
  have cc : ∀ x : L, IsCMField.complexConj L (IsCMField.complexConj L x) = x :=
    fun x => IsCMField.complexConj_apply_apply L x
  have fix : ∀ z : L, IsCMField.complexConj L z = z → φ z = ψ z := by
    intro z hz
    have hm := (IsCMField.complexConj_eq_self_iff L z).1 hz
    have e : algebraMap L⁺ L ⟨z, hm⟩ = z := rfl
    rw [← e, AlgHom.commutes, AlgHom.commutes]
  have h2 : (2 : F) ≠ 0 := by
    have := (algebraMap L⁺ F).injective.ne (two_ne_zero (α := L⁺))
    rwa [map_ofNat, map_zero] at this
  obtain ⟨x0, hx0⟩ : ∃ x, IsCMField.complexConj L x ≠ x := by
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
    exact ⟨a, ha⟩
  set y := x0 - IsCMField.complexConj L x0 with hy
  have hyc : IsCMField.complexConj L y = -y := by
    rw [hy, map_sub, cc]; ring
  have hy0 : y ≠ 0 := by
    intro h; apply hx0; rw [hy, sub_eq_zero] at h; exact h.symm
  have hyy : φ y * φ y = ψ y * ψ y := by
    rw [← map_mul, ← map_mul]
    exact fix _ (by rw [map_mul, hyc]; ring)
  have fp : ∀ x : L, IsCMField.complexConj L (x + IsCMField.complexConj L x) = x + IsCMField.complexConj L x := by
    intro x; rw [map_add, cc, add_comm]
  have fq : ∀ x : L, IsCMField.complexConj L ((x - IsCMField.complexConj L x) * y⁻¹) =
      (x - IsCMField.complexConj L x) * y⁻¹ := by
    intro x; rw [map_mul, map_inv₀, hyc, map_sub, cc]; ring_nf
  have two : ∀ (χ : L →ₐ[L⁺] F), χ (2 : L) = 2 := fun χ => map_ofNat χ 2
  have dec : ∀ (χ : L →ₐ[L⁺] F) (x : L), 2 * χ x = χ (x + IsCMField.complexConj L x) +
      χ ((x - IsCMField.complexConj L x) * y⁻¹) * χ y := by
    intro χ x
    calc 2 * χ x = χ (2 * x) := by rw [map_mul, two]
      _ = χ ((x + IsCMField.complexConj L x) + ((x - IsCMField.complexConj L x) * y⁻¹) * y) := by
          congr 1; field_simp; ring
      _ = _ := by rw [map_add, map_mul]
  have decc : ∀ (χ : L →ₐ[L⁺] F) (x : L), 2 * χ (IsCMField.complexConj L x) = χ (x + IsCMField.complexConj L x) -
      χ ((x - IsCMField.complexConj L x) * y⁻¹) * χ y := by
    intro χ x
    calc 2 * χ (IsCMField.complexConj L x) = χ (2 * IsCMField.complexConj L x) := by rw [map_mul, two]
      _ = χ ((x + IsCMField.complexConj L x) - ((x - IsCMField.complexConj L x) * y⁻¹) * y) := by
          congr 1; field_simp; ring
      _ = _ := by rw [map_sub, map_mul]
  have hfac : (φ y - ψ y) * (φ y + ψ y) = 0 := by linear_combination hyy
  rcases mul_eq_zero.1 hfac with h | h
  · left
    ext x
    have e1 := dec φ x
    rw [fix _ (fp x), fix _ (fq x), show φ y = ψ y from sub_eq_zero.1 h, ← dec ψ x] at e1
    exact mul_left_cancel₀ h2 e1
  · right
    intro x
    have e1 := dec φ x
    rw [fix _ (fp x), fix _ (fq x), show φ y = -ψ y from eq_neg_of_add_eq_zero_left h] at e1
    have : 2 * φ x = 2 * ψ (IsCMField.complexConj L x) := by rw [e1, decc ψ x]; ring
    exact mul_left_cancel₀ h2 this

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Simplify using `[SplitPlace.proj, conjAL, Algebra.TensorProduct.map_tmul, hij]`. Consider the case `add a b ha hb => rw [map_add, map_add, map_add, ha, hb]`.
-/
theorem proj_conj {v : HeightOneSpectrum (𝓞 L⁺)} (i j : L →ₐ[L⁺] v.adicCompletion L⁺)
    (hij : ∀ x, j x = i (IsCMField.complexConj L x)) (x : AL L) :
    (SplitPlace.mk v j).proj x = (SplitPlace.mk v i).proj (conjAL L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.map_tmul, hij]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/- English proof (translation)
Establish `e1 : (((SplitPlace.mk v j).loc n κ : GL (Fin n) (v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) a b = (SplitPlace.mk v j).proj ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) a b)` using `rfl`. Establish `e2 : (((SplitPlace.mk v i).loc n κ⁻¹ : GL (Fin n) (v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) b a = (SplitPlace.mk v i).proj ((((κ⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) b a)` using `rfl`. Rewrite using `[e1, e2, GlobalTheory.FinTypCount.inv_val, proj_conj i j hij]`. Both sides reduce to the same expression.
-/
theorem loc_conj {v : HeightOneSpectrum (𝓞 L⁺)} (i j : L →ₐ[L⁺] v.adicCompletion L⁺)
    (hij : ∀ x, j x = i (IsCMField.complexConj L x)) {n : ℕ} (κ : GAf L n) (a b : Fin n) :
    (((SplitPlace.mk v j).loc n κ : GL (Fin n) (v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) a b =
      (((SplitPlace.mk v i).loc n κ⁻¹ : GL (Fin n) (v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) b a := by
  have e1 : (((SplitPlace.mk v j).loc n κ : GL (Fin n) (v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) a b =
      (SplitPlace.mk v j).proj ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) a b) := rfl
  have e2 : (((SplitPlace.mk v i).loc n κ⁻¹ : GL (Fin n) (v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) b a =
      (SplitPlace.mk v i).proj ((((κ⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) b a) := rfl
  rw [e1, e2, GlobalTheory.FinTypCount.inv_val, proj_conj i j hij]
  rfl

def resO (w : HeightOneSpectrum (𝓞 L⁺)) :
    (w.adicCompletionIntegers L⁺).toSubring →+* IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺) :=
  (IsLocalRing.residue (w.adicCompletionIntegers L⁺)).comp
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }

/- English proof (translation)
Unfold `resO`. Rewrite using `[RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]`. Conclude with `Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (w.adicCompletion L⁺) (WithZero (Multiplicative ℤ))))`.
-/
theorem resO_eq_zero_iff {w : HeightOneSpectrum (𝓞 L⁺)} (x : (w.adicCompletionIntegers L⁺).toSubring) :
    resO w x = 0 ↔ Valued.v (x : w.adicCompletion L⁺) < 1 := by
  unfold resO
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (w.adicCompletion L⁺) (WithZero (Multiplicative ℤ))))

/- English proof (translation)
Introduce `g h e`. Apply `Units.ext` to reduce the goal to its premises. Use `congrArg (fun u : GL (Fin n) (w.adicCompletion L⁺) => (u : Matrix (Fin n) (Fin n) (w.adicCompletion L⁺))) e` as an intermediate fact. Conclude with `Matrix.map_injective Subtype.val_injective this`.
-/
theorem intMap_injective {w : HeightOneSpectrum (𝓞 L⁺)} {n : ℕ} : Function.Injective
    (Formalism.UG.bc (w.adicCompletionIntegers L⁺).toSubring.subtype : GL (Fin n) (w.adicCompletionIntegers L⁺).toSubring →* GL (Fin n) (w.adicCompletion L⁺)) := by
  intro g h e
  apply Units.ext
  have := congrArg (fun u : GL (Fin n) (w.adicCompletion L⁺) => (u : Matrix (Fin n) (Fin n) (w.adicCompletion L⁺))) e
  exact Matrix.map_injective Subtype.val_injective this

def intEquiv (w : HeightOneSpectrum (𝓞 L⁺)) (n : ℕ) :
    GL (Fin n) (w.adicCompletionIntegers L⁺).toSubring ≃*
      (Formalism.UG.bc (w.adicCompletionIntegers L⁺).toSubring.subtype : GL (Fin n) (w.adicCompletionIntegers L⁺).toSubring →* GL (Fin n) (w.adicCompletion L⁺)).range :=
  MonoidHom.ofInjective intMap_injective

def intLoc {w : HeightOneSpectrum (𝓞 L⁺)} (i : L →ₐ[L⁺] w.adicCompletion L⁺) (n : ℕ) :
    GlobalTheory.HeckeScalarSph.locK n w →* (Formalism.UG.bc (w.adicCompletionIntegers L⁺).toSubring.subtype : GL (Fin n) (w.adicCompletionIntegers L⁺).toSubring →* GL (Fin n) (w.adicCompletion L⁺)).range :=
  (((SplitPlace.mk w i).loc n).comp (GlobalTheory.HeckeScalarSph.locK n w).subtype).codRestrict _
    (fun κ => (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff (SplitPlace.mk w i) κ.2.2).2 κ.2.1)

def redLoc {w : HeightOneSpectrum (𝓞 L⁺)} (i : L →ₐ[L⁺] w.adicCompletion L⁺) (n : ℕ) :
    GlobalTheory.HeckeScalarSph.locK n w →* GL (Fin n) (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) :=
  (Matrix.GeneralLinearGroup.map (resO w)).comp ((intEquiv w n).symm.toMonoidHom.comp (intLoc i n))

/- English proof (translation)
Use `set g := (intEquiv w n).symm (intLoc i n κ) with hg`. Establish `h1 : Formalism.UG.bc (w.adicCompletionIntegers L⁺).toSubring.subtype g = (SplitPlace.mk w i).loc n κ.1`. Use `congrArg Subtype.val ((intEquiv w n).apply_symm_apply (intLoc i n κ))` as an intermediate fact. Conclude with `this`. Establish `he : (((g : Matrix (Fin n) (Fin n) _) a b : (w.adicCompletionIntegers L⁺).toSubring) : w.adicCompletion L⁺) = (((SplitPlace.mk w i).loc n κ.1 : GL (Fin n) (w.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (w.adicCompletion L⁺)) a b`.

Rewrite using `[← h1]`. Both sides reduce to the same expression. Use `show resO w ((g : Matrix (Fin n) (Fin n) _) a b) = 0 ↔ _`. Rewrite using `[resO_eq_zero_iff, he]`.
-/
theorem redLoc_eq_zero_iff {w : HeightOneSpectrum (𝓞 L⁺)} {n : ℕ} (i : L →ₐ[L⁺] w.adicCompletion L⁺)
    (κ : GlobalTheory.HeckeScalarSph.locK n w) (a b : Fin n) :
    ((redLoc i n κ : GL (Fin n) (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺))) : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺))) a b = 0 ↔
      Valued.v ((((SplitPlace.mk w i).loc n κ.1 : GL (Fin n) (w.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (w.adicCompletion L⁺)) a b) < 1 := by
  set g := (intEquiv w n).symm (intLoc i n κ) with hg
  have h1 : Formalism.UG.bc (w.adicCompletionIntegers L⁺).toSubring.subtype g = (SplitPlace.mk w i).loc n κ.1 := by
    have := congrArg Subtype.val ((intEquiv w n).apply_symm_apply (intLoc i n κ))
    exact this
  have he : (((g : Matrix (Fin n) (Fin n) _) a b : (w.adicCompletionIntegers L⁺).toSubring) : w.adicCompletion L⁺) =
      (((SplitPlace.mk w i).loc n κ.1 : GL (Fin n) (w.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (w.adicCompletion L⁺)) a b := by
    rw [← h1]; rfl
  show resO w ((g : Matrix (Fin n) (Fin n) _) a b) = 0 ↔ _
  rw [resO_eq_zero_iff, he]

def wLow (r : ℕ) : ℕ → ℕ := fun m => if m < r then 0 else 1

def wUp (r : ℕ) : ℕ → ℕ := fun m => if m < r then 1 else 0

/- English proof (translation)
Rewrite using `[Col.mem_btG]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff (SplitPlace.mk w i) κ.2.2).2 κ.2.1, fun a b ha hb => ?_⟩` and prove the remaining obligations. Use `(redLoc_eq_zero_iff i κ a b).1 (h a b ?_)` and prove the remaining obligations.

Simplify using `only [wLow]`. Rewrite using `[if_pos hb, if_neg (Nat.not_lt.2 ha)]`. Conclude with `Nat.zero_lt_one`. Introduce and unpack `⟨-, h⟩ a b hab`. Establish `key : r ≤ a.val ∧ b.val < r`.

Simplify using `only [wLow] at hab`. Apply the tactic sequence `split_ifs at hab <;> omega`. Conclude with `(redLoc_eq_zero_iff i κ a b).2 (h a b key.1 key.2)`.
-/
theorem mem_low_iff {w : HeightOneSpectrum (𝓞 L⁺)} {n r : ℕ} (i : L →ₐ[L⁺] w.adicCompletion L⁺)
    (κ : GlobalTheory.HeckeScalarSph.locK n w) :
    redLoc i n κ ∈ Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wLow r) ↔
      NG.ParaRT (SplitPlace.mk w i) r ((SplitPlace.mk w i).loc n κ.1) := by
  rw [Col.mem_btG]
  constructor
  · intro h
    refine ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff (SplitPlace.mk w i) κ.2.2).2 κ.2.1, fun a b ha hb => ?_⟩
    refine (redLoc_eq_zero_iff i κ a b).1 (h a b ?_)
    simp only [wLow]
    rw [if_pos hb, if_neg (Nat.not_lt.2 ha)]
    exact Nat.zero_lt_one
  · rintro ⟨-, h⟩ a b hab
    have key : r ≤ a.val ∧ b.val < r := by
      simp only [wLow] at hab
      split_ifs at hab <;> omega
    exact (redLoc_eq_zero_iff i κ a b).2 (h a b key.1 key.2)

/- English proof (translation)
Take `⟨-, h⟩` from `hP`. Establish `hinv : redLoc i n κ⁻¹ ∈ Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wUp r)`. Rewrite using `[Col.mem_btG]`. Introduce `a b hab`. Establish `key : a.val < r ∧ r ≤ b.val`.

Simplify using `only [wUp] at hab`. Apply the tactic sequence `split_ifs at hab <;> omega`. Establish `h1` using `h b a key.2 key.1`. Rewrite `h1` using `[loc_conj i j hij]`. Conclude with `(redLoc_eq_zero_iff i κ⁻¹ a b).2 h1`.

Use `Subgroup.inv_mem _ hinv` as an intermediate fact. Rewrite `this` using `[← map_inv, inv_inv]`. Then use the resulting hypothesis.
-/
theorem mem_up_of {w : HeightOneSpectrum (𝓞 L⁺)} {n r : ℕ} (i j : L →ₐ[L⁺] w.adicCompletion L⁺)
    (hij : ∀ x, j x = i (IsCMField.complexConj L x)) (κ : GlobalTheory.HeckeScalarSph.locK n w)
    (hP : NG.ParaRT (SplitPlace.mk w j) r ((SplitPlace.mk w j).loc n κ.1)) :
    redLoc i n κ ∈ Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wUp r) := by
  obtain ⟨-, h⟩ := hP
  have hinv : redLoc i n κ⁻¹ ∈ Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wUp r) := by
    rw [Col.mem_btG]
    intro a b hab
    have key : a.val < r ∧ r ≤ b.val := by
      simp only [wUp] at hab
      split_ifs at hab <;> omega
    have h1 := h b a key.2 key.1
    rw [loc_conj i j hij] at h1
    exact (redLoc_eq_zero_iff i κ⁻¹ a b).2 h1
  have := Subgroup.inv_mem _ hinv
  rwa [← map_inv, inv_inv] at this

def restr {w : HeightOneSpectrum (𝓞 L⁺)} {n : ℕ} (θ : GAf L n ≃* GAf L n) (hθ : FrameAut θ) :
    GlobalTheory.HeckeScalarSph.locK n w →* GlobalTheory.HeckeScalarSph.locK n w :=
  (θ.toMonoidHom.comp (GlobalTheory.HeckeScalarSph.locK n w).subtype).codRestrict _ fun κ =>
    show θ κ.1 ∈ Umax L n ∧ TrivOutside {w} (θ κ.1) from ⟨(hθ.1 κ.1).2 κ.2.1, (hθ.2 w κ.1).2 κ.2.2⟩

/- English proof (translation)
Introduce `y`. Establish `hx : θ.symm y.1 ∈ GlobalTheory.HeckeScalarSph.locK n w`. Establish `h1` using `y.2.1`. Establish `h2` using `y.2.2`. Rewrite `h1`, `h2` using `[← θ.apply_symm_apply y.1]`.

Conclude with `⟨(hθ.1 _).1 h1, (hθ.2 w _).1 h2⟩`. Conclude with `⟨⟨_, hx⟩, Subtype.ext (θ.apply_symm_apply y.1)⟩`.
-/
theorem restr_surjective {w : HeightOneSpectrum (𝓞 L⁺)} {n : ℕ} (θ : GAf L n ≃* GAf L n) (hθ : FrameAut θ) :
    Function.Surjective (restr (w := w) θ hθ) := by
  intro y
  have hx : θ.symm y.1 ∈ GlobalTheory.HeckeScalarSph.locK n w := by
    have h1 := y.2.1
    have h2 := y.2.2
    rw [← θ.apply_symm_apply y.1] at h1 h2
    exact ⟨(hθ.1 _).1 h1, (hθ.2 w _).1 h2⟩
  exact ⟨⟨_, hx⟩, Subtype.ext (θ.apply_symm_apply y.1)⟩

/- English proof (translation)
Use `haveI : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) := Formalism.UG.P.tjcosets_finite w`. Use `set A := (Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wLow r)).comap (redLoc i n) with hA`. Use `set Q := (Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wLow r) ⊓ Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wUp r)).comap (redLoc i n) with hQ`. Establish `hQA : Q ≤ A` using `Subgroup.comap_mono inf_le_left`. Establish `hAQ : A ≤ Q.comap (restr θ hθ)`.

Introduce `κ hκ`. Establish `hP` using `(mem_low_iff i κ).1 hκ`. Take `⟨h1, h2⟩` from `H κ.1 κ.2.2 hP`. Conclude with `⟨(mem_low_iff i (restr θ hθ κ)).2 h1, mem_up_of i j hij (restr θ hθ κ) h2⟩`. Establish `hker : (redLoc i n).ker ≤ A` using `fun κ hκ => Subgroup.mem_comap.2 (by rw [MonoidHom.mem_ker.1 hκ]; exact Subgroup.one_mem _)`.

Establish `hA0 : A.index ≠ 0`. Introduce `h0`. Establish `hd` using `Subgroup.index_dvd_of_le hker`. Rewrite `hd` using `[h0, zero_dvd_iff, Subgroup.index_ker]`. Conclude with `(Nat.card_pos (α := (redLoc i n).range)).ne' hd`.

Establish `heq : Q.index = A.index`. Use `Nat.dvd_antisymm ?_ (Subgroup.index_dvd_of_le hQA)` and prove the remaining obligations. Use `Subgroup.index_dvd_of_le hAQ` as an intermediate fact. Rewrite `this` using `[Subgroup.index_comap_of_surjective _ (restr_surjective θ hθ)]`. Then use the resulting hypothesis. Establish `hrel : Q.relIndex A = 1`.

Use `Subgroup.relIndex_mul_index hQA` as an intermediate fact. Rewrite `this` using `[heq]`. Conclude with `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hA0) (this.trans (one_mul _).symm)`. Establish `hAleQ : A ≤ Q` using `Subgroup.relIndex_eq_one.1 hrel`. Use `set i0 : Fin n := ⟨0, by omega⟩ with hi0`.

Use `set ir : Fin n := ⟨r, hrn⟩ with hir`. Establish `hne : i0 ≠ ir`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[hi0, hir] at this`.

Use linear arithmetic over natural numbers and integers. Set `u : GL (Fin n) (w.adicCompletion L⁺)` to `⟨Matrix.transvection i0 ir 1, Matrix.transvection i0 ir (-1), by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp, by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp⟩`. Establish `hent : ∀ (c : w.adicCompletion L⁺) (a b : Fin n), Matrix.transvection i0 ir c a b = (if a = b then 1 else 0) + (if i0 = a ∧ ir = b then c else 0)`. Introduce `c a b`. Use `show (1 + Matrix.single i0 ir c) a b = _`.

Rewrite using `[Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]`. Establish `hint : ∀ (c : w.adicCompletion L⁺), c ∈ (w.adicCompletionIntegers L⁺).toSubring → ∀ a b : Fin n, Matrix.transvection i0 ir c a b ∈ (w.adicCompletionIntegers L⁺).toSubring`. Introduce `c hc a b`. Rewrite using `[hent]`. Use `Subring.add_mem _ ?_ ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`. Use `split_ifs`. Conclude with `hc`.

Conclude with `Subring.zero_mem _`. Establish `hu : u ∈ Formalism.UG.GLint (Fin n) (w.adicCompletionIntegers L⁺).toSubring` using `GlobalTheory.HeckeScalarSph.mem_GLint_iff.2 ⟨hint 1 (Subring.one_mem _), hint (-1) (Subring.neg_mem _ (Subring.one_mem _))⟩`. Take `⟨x, hx, hxu⟩` from `GlobalTheory.SplitLift.exists_trivOutside_loc_eq n (SplitPlace.mk w i) u`. Establish `hxU : x ∈ Umax L n` using `(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff (SplitPlace.mk w i) hx).1 (by rw [hxu]; exact hu)`. Set `κ0 : GlobalTheory.HeckeScalarSph.locK n w` to `⟨x, hxU, hx⟩`.

Establish `hκA : κ0 ∈ A`. Use `(mem_low_iff i κ0).2 ?_` and prove the remaining obligations. Use `show NG.ParaRT (SplitPlace.mk w i) r ((SplitPlace.mk w i).loc n x)`. Rewrite using `[hxu]`. Use `⟨hu, fun a b ha hb => ?_⟩` and prove the remaining obligations.

Use `show Valued.v (Matrix.transvection i0 ir (1 : w.adicCompletion L⁺) a b) < 1`. Rewrite using `[hent, if_neg, if_neg, add_zero, map_zero]`. Conclude with `zero_lt_one`. Introduce and unpack `⟨-, h⟩`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `[hir] at this`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hκQ : redLoc i n κ0 ∈ Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wUp r)` using `(Subgroup.mem_inf.1 (Subgroup.mem_comap.1 (hAleQ hκA))).2`.

Rewrite `hκQ` using `[Col.mem_btG]`. Establish `h0` using `hκQ i0 ir (by simp [wUp, hi0, hir, hr0])`. Rewrite `h0` using `[redLoc_eq_zero_iff]`. Establish `e : (((SplitPlace.mk w i).loc n κ0.1 : GL (Fin n) (w.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (w.adicCompletion L⁺)) i0 ir = 1` using `by show (((SplitPlace.mk w i).loc n x : GL (Fin n) (w.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (w.adicCompletion L⁺)) i0 ir = 1`. Rewrite using `[hxu]`.

Use `show Matrix.transvection i0 ir (1 : w.adicCompletion L⁺) i0 ir = 1`. Rewrite using `[hent, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]`. Rewrite `h0` using `[e, map_one]`. Conclude with `lt_irrefl _ h0`.
-/
theorem core {w : HeightOneSpectrum (𝓞 L⁺)} (i j : L →ₐ[L⁺] w.adicCompletion L⁺)
    (hij : ∀ x, j x = i (IsCMField.complexConj L x)) {n r : ℕ} (hr0 : 0 < r) (hrn : r < n)
    {θ : GAf L n ≃* GAf L n} (hθ : FrameAut θ)
    (H : ∀ κ, TrivOutside {w} κ → NG.ParaRT (SplitPlace.mk w i) r ((SplitPlace.mk w i).loc n κ) →
      NG.ParaRT (SplitPlace.mk w i) r ((SplitPlace.mk w i).loc n (θ κ)) ∧
        NG.ParaRT (SplitPlace.mk w j) r ((SplitPlace.mk w j).loc n (θ κ))) : False := by
  classical
  haveI : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) := Formalism.UG.P.tjcosets_finite w
  set A := (Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wLow r)).comap (redLoc i n) with hA
  set Q := (Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wLow r) ⊓
    Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wUp r)).comap (redLoc i n) with hQ
  have hQA : Q ≤ A := Subgroup.comap_mono inf_le_left
  have hAQ : A ≤ Q.comap (restr θ hθ) := by
    intro κ hκ
    have hP := (mem_low_iff i κ).1 hκ
    obtain ⟨h1, h2⟩ := H κ.1 κ.2.2 hP
    exact ⟨(mem_low_iff i (restr θ hθ κ)).2 h1, mem_up_of i j hij (restr θ hθ κ) h2⟩
  have hker : (redLoc i n).ker ≤ A := fun κ hκ =>
    Subgroup.mem_comap.2 (by rw [MonoidHom.mem_ker.1 hκ]; exact Subgroup.one_mem _)
  have hA0 : A.index ≠ 0 := by
    intro h0
    have hd := Subgroup.index_dvd_of_le hker
    rw [h0, zero_dvd_iff, Subgroup.index_ker] at hd
    exact (Nat.card_pos (α := (redLoc i n).range)).ne' hd
  have heq : Q.index = A.index := by
    refine Nat.dvd_antisymm ?_ (Subgroup.index_dvd_of_le hQA)
    have := Subgroup.index_dvd_of_le hAQ
    rwa [Subgroup.index_comap_of_surjective _ (restr_surjective θ hθ)] at this
  have hrel : Q.relIndex A = 1 := by
    have := Subgroup.relIndex_mul_index hQA
    rw [heq] at this
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hA0) (this.trans (one_mul _).symm)
  have hAleQ : A ≤ Q := Subgroup.relIndex_eq_one.1 hrel

  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set ir : Fin n := ⟨r, hrn⟩ with hir
  have hne : i0 ≠ ir := by
    intro h
    have := congrArg Fin.val h
    simp [hi0, hir] at this
    omega
  let u : GL (Fin n) (w.adicCompletion L⁺) :=
    ⟨Matrix.transvection i0 ir 1, Matrix.transvection i0 ir (-1),
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp,
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp⟩
  have hent : ∀ (c : w.adicCompletion L⁺) (a b : Fin n), Matrix.transvection i0 ir c a b =
      (if a = b then 1 else 0) + (if i0 = a ∧ ir = b then c else 0) := by
    intro c a b
    show (1 + Matrix.single i0 ir c) a b = _
    rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have hint : ∀ (c : w.adicCompletion L⁺), c ∈ (w.adicCompletionIntegers L⁺).toSubring → ∀ a b : Fin n,
      Matrix.transvection i0 ir c a b ∈ (w.adicCompletionIntegers L⁺).toSubring := by
    intro c hc a b
    rw [hent]
    refine Subring.add_mem _ ?_ ?_
    · split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · split_ifs
      · exact hc
      · exact Subring.zero_mem _
  have hu : u ∈ Formalism.UG.GLint (Fin n) (w.adicCompletionIntegers L⁺).toSubring :=
    GlobalTheory.HeckeScalarSph.mem_GLint_iff.2 ⟨hint 1 (Subring.one_mem _), hint (-1) (Subring.neg_mem _ (Subring.one_mem _))⟩
  obtain ⟨x, hx, hxu⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n (SplitPlace.mk w i) u
  have hxU : x ∈ Umax L n := (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff (SplitPlace.mk w i) hx).1 (by rw [hxu]; exact hu)
  let κ0 : GlobalTheory.HeckeScalarSph.locK n w := ⟨x, hxU, hx⟩
  have hκA : κ0 ∈ A := by
    refine (mem_low_iff i κ0).2 ?_
    show NG.ParaRT (SplitPlace.mk w i) r ((SplitPlace.mk w i).loc n x)
    rw [hxu]
    refine ⟨hu, fun a b ha hb => ?_⟩
    show Valued.v (Matrix.transvection i0 ir (1 : w.adicCompletion L⁺) a b) < 1
    rw [hent, if_neg, if_neg, add_zero, map_zero]
    · exact zero_lt_one
    · rintro ⟨-, h⟩
      have := congrArg Fin.val h
      simp [hir] at this
      omega
    · rintro rfl
      omega
  have hκQ : redLoc i n κ0 ∈ Col.btG n (IsLocalRing.ResidueField (w.adicCompletionIntegers L⁺)) (wUp r) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 (hAleQ hκA))).2
  rw [Col.mem_btG] at hκQ
  have h0 := hκQ i0 ir (by simp [wUp, hi0, hir, hr0])
  rw [redLoc_eq_zero_iff] at h0
  have e : (((SplitPlace.mk w i).loc n κ0.1 : GL (Fin n) (w.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (w.adicCompletion L⁺)) i0 ir = 1 := by
    show (((SplitPlace.mk w i).loc n x : GL (Fin n) (w.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (w.adicCompletion L⁺)) i0 ir = 1
    rw [hxu]
    show Matrix.transvection i0 ir (1 : w.adicCompletion L⁺) i0 ir = 1
    rw [hent, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]
  rw [e, map_one] at h0
  exact lt_irrefl _ h0

end GlobalTheory.ParaOpp

/- English proof (translation)
Introduce `L _ _ _ n r s s' s₁ θ hr0 hrn hv' hv1 hθ H`. Take `⟨v, i⟩` from `s`. Take `⟨v', i'⟩` from `s'`. Take `⟨v1, i1⟩` from `s₁`. Simplify using `only at hv' hv1`.

Substitute `hv' hv1` using the available equality. Assume the negation of the conclusion as `hne`. Establish `hc : ∀ x, i' x = i (IsCMField.complexConj L x)` using `(GlobalTheory.ParaOpp.algHom_eq_or_conj i' i).resolve_left (fun h => hne (by rw [h]))`. Break down `GlobalTheory.ParaOpp.algHom_eq_or_conj i1 i with h1 | h1` into its components or cases. Substitute `h1` using the available equality.

Conclude with `GlobalTheory.ParaOpp.core i1 i' hc hr0 hrn hθ H`. Establish `e : i1 = i'` using `AlgHom.ext fun x => (h1 x).trans (hc x).symm`. Substitute `e` using the available equality. Establish `hc' : ∀ x, i x = i1 (IsCMField.complexConj L x)` using `fun x => by`. Rewrite using `[hc, IsCMField.complexConj_apply_apply]`.

Conclude with `GlobalTheory.ParaOpp.core i1 i hc' hr0 hrn hθ (fun κ hκ hP => (H κ hκ hP).symm)`.
-/
theorem GlobalTheory.ParaOpp.splitPlace_eq_of_para : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s s' s₁ : SplitPlace L) (θ : GAf L n ≃* GAf L n), 0 < r → r < n → s'.v = s.v → s₁.v = s.v → FrameAut θ → (∀ κ, TrivOutside {s.v} κ → NG.ParaRT s₁ r (s₁.loc n κ) → NG.ParaRT s r (s.loc n (θ κ)) ∧ NG.ParaRT s' r (s'.loc n (θ κ))) → s' = s := by
  intro L _ _ _ n r s s' s₁ θ hr0 hrn hv' hv1 hθ H
  obtain ⟨v, i⟩ := s
  obtain ⟨v', i'⟩ := s'
  obtain ⟨v1, i1⟩ := s₁
  dsimp only at hv' hv1
  subst hv' hv1
  by_contra hne
  have hc : ∀ x, i' x = i (IsCMField.complexConj L x) :=
    (GlobalTheory.ParaOpp.algHom_eq_or_conj i' i).resolve_left (fun h => hne (by rw [h]))
  rcases GlobalTheory.ParaOpp.algHom_eq_or_conj i1 i with h1 | h1
  · subst h1
    exact GlobalTheory.ParaOpp.core i1 i' hc hr0 hrn hθ H
  · have e : i1 = i' := AlgHom.ext fun x => (h1 x).trans (hc x).symm
    subst e
    have hc' : ∀ x, i x = i1 (IsCMField.complexConj L x) := fun x => by
      rw [hc, IsCMField.complexConj_apply_apply]
    exact GlobalTheory.ParaOpp.core i1 i hc' hr0 hrn hθ (fun κ hκ hP => (H κ hκ hP).symm)
