import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `p (Matrix.diagonal (fun _ => (u : R)) i j) = Matrix.diagonal (fun _ => p u) i j`. Simplify using `[Matrix.diagonal_apply, apply_ite p]`.
-/
theorem map_scalar {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (u : Rˣ) :
    GeneralLinearGroup.map p (GeneralLinearGroup.scalar (Fin a) u) =
      GeneralLinearGroup.scalar (Fin a) (Units.map p.toMonoidHom u) := by
  ext i j
  change p (Matrix.diagonal (fun _ => (u : R)) i j) = Matrix.diagonal (fun _ => p u) i j
  simp [Matrix.diagonal_apply, apply_ite p]

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (Matrix.diagonal (fun _ => (u : R)) i j) = Matrix.diagonal (fun _ => 1 - s 1 + s u) i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`.
-/
theorem cornerGL_scalar {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (u : Rˣ) :
    cornerGL a s (GeneralLinearGroup.scalar (Fin a) u) =
      GeneralLinearGroup.scalar (Fin a) (Units.map (corner s) u) := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) +
    s (Matrix.diagonal (fun _ => (u : R)) i j) = Matrix.diagonal (fun _ => 1 - s 1 + s u) i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/- English proof (translation)
The claim follows from `Units.ext (Matrix.scalar_commute (u : R) (fun _ => Commute.all _ _) g.val).eq`.
-/
theorem scalar_comm {R : Type} [CommRing R] (u : Rˣ) (g : GL (Fin a) R) :
    GeneralLinearGroup.scalar (Fin a) u * g = g * GeneralLinearGroup.scalar (Fin a) u :=
  Units.ext (Matrix.scalar_commute (u : R) (fun _ => Commute.all _ _) g.val).eq

/- English proof (translation)
Establish `h` using `congrArg GeneralLinearGroup.det (infGL_mul_finGL (GeneralLinearGroup.scalar (Fin 1) z))`. Rewrite `h` using `[map_mul, det_infGL, det_finGL, map_scalar, map_scalar]`. Conclude with `(congrArg₂ (fun x y => infId E x * finId E y) (CG.det_oneByOne _) (CG.det_oneByOne _)).symm.trans (h.trans (CG.det_oneByOne z))`.
-/
theorem infId_mul_finId (z : Ideles E) :
    infId E (Units.map (pInf E).toMonoidHom z) * finId E (Units.map (pFin E).toMonoidHom z) = z := by
  have h := congrArg GeneralLinearGroup.det (infGL_mul_finGL (GeneralLinearGroup.scalar (Fin 1) z))
  rw [map_mul, det_infGL, det_finGL, map_scalar, map_scalar] at h
  exact (congrArg₂ (fun x y => infId E x * finId E y) (CG.det_oneByOne _) (CG.det_oneByOne _)).symm.trans
    (h.trans (CG.det_oneByOne z))

namespace CuspSub

variable {π π' : CuspSub E a} {ω ω' : HChar E}

variable (π) in

def HasCentral (ω : HChar E) : Prop :=
  ∀ z : Ideles E, ∀ φ ∈ π.V, rt E a (GeneralLinearGroup.scalar (Fin a) z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ

/- English proof (translation)
Use `⟨fun h u φ => Subtype.ext ?_, fun h => ?_⟩` and prove the remaining obligations. Conclude with `(congrArg (fun g => rt E a g φ.1) (cornerGL_scalar (sFin E) u)).trans (h (finId E u) φ.1 φ.2)`. Establish `hf : ∀ u, ∀ φ ∈ π.V, rt E a (GeneralLinearGroup.scalar (Fin a) (finId E u)) φ = ((ω.1 (finId E u) : ℂˣ) : ℂ) • φ` using `fun u φ hφ => (congrArg (fun g => rt E a g φ) (cornerGL_scalar (sFin E) u)).symm.trans (congrArg Subtype.val (h u ⟨φ, hφ⟩))`. Establish `hi : ∀ y, ∀ φ ∈ π.V, rt E a (GeneralLinearGroup.scalar (Fin a) (infId E y)) φ = ((ω.1 (infId E y) : ℂˣ) : ℂ) • φ` using `fun y φ hφ => Subtype.ext <| funext fun g => by`. Use `congrFun (InfType.denseRange_units.equalizer (g := fun y => φ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E y))) (h := fun y => ((ω.1 (infId E y) : ℂˣ) : ℂ) * φ.1 g) ?_ ((Units.continuous_val.comp (continuous_chiInf ω)).mul continuous_const) (funext fun k => ?_)) y` and prove the remaining obligations.

Establish `e : (fun y => φ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E y))) = fun y : (Cinf E)ˣ => chart φ.1 g (toL (GeneralLinearGroup.scalar (Fin a) y).val)`. Use function extensionality and compare the values at `y`. Rewrite using `[chart_val]`. Conclude with `congrArg (fun x => φ.1 (g * x)) (cornerGL_scalar (sInf E) y).symm`. Rewrite using `[e]`.

Use `(φ.2 g).continuousOn.comp_continuous ?_ fun y => val_mem_invSet _` and prove the remaining obligations. Conclude with `(continuous_pi fun _ => Units.continuous_val).matrix_diagonal`. Establish `e : infId E (Units.map (InfType.diagInf E).toMonoidHom k) = diagUnits E k * finId E (Units.map (pFin E).toMonoidHom (diagUnits E k))⁻¹`. Rewrite using `[map_inv, eq_mul_inv_iff_mul_eq]`. Conclude with `infId_mul_finId (diagUnits E k)`.

Establish `e2 : GeneralLinearGroup.scalar (Fin a) (diagUnits E k) = ratGL E a (GeneralLinearGroup.scalar (Fin a) k)` using `(map_scalar _ k).symm`. Simplify using `only [Function.comp_apply]`. Rewrite using `[e, map_mul, map_mul, ω.2.2, one_mul, ← mul_assoc, ← scalar_comm (diagUnits E k), e2, mul_assoc, (π.cusp φ hφ).1.left]`. Conclude with `congrFun (congrArg Subtype.val (hf _ φ hφ)) g`. Introduce `z φ hφ`.

Rewrite using `[← infId_mul_finId z, map_mul, map_mul, map_mul, Module.End.mul_apply, hf _ φ hφ, map_smul, hi _ φ hφ, smul_smul, Units.val_mul, mul_comm]`.
-/
theorem hasCentral_iff : π.HasCentral ω ↔ π.HasCentChar ω := by
  refine ⟨fun h u φ => Subtype.ext ?_, fun h => ?_⟩
  · exact (congrArg (fun g => rt E a g φ.1) (cornerGL_scalar (sFin E) u)).trans (h (finId E u) φ.1 φ.2)
  have hf : ∀ u, ∀ φ ∈ π.V, rt E a (GeneralLinearGroup.scalar (Fin a) (finId E u)) φ =
      ((ω.1 (finId E u) : ℂˣ) : ℂ) • φ := fun u φ hφ =>
    (congrArg (fun g => rt E a g φ) (cornerGL_scalar (sFin E) u)).symm.trans (congrArg Subtype.val (h u ⟨φ, hφ⟩))
  have hi : ∀ y, ∀ φ ∈ π.V, rt E a (GeneralLinearGroup.scalar (Fin a) (infId E y)) φ =
      ((ω.1 (infId E y) : ℂˣ) : ℂ) • φ := fun y φ hφ => Subtype.ext <| funext fun g => by
    refine congrFun (InfType.denseRange_units.equalizer
      (g := fun y => φ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E y)))
      (h := fun y => ((ω.1 (infId E y) : ℂˣ) : ℂ) * φ.1 g) ?_
      ((Units.continuous_val.comp (continuous_chiInf ω)).mul continuous_const) (funext fun k => ?_)) y
    · have e : (fun y => φ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E y))) =
          fun y : (Cinf E)ˣ => chart φ.1 g (toL (GeneralLinearGroup.scalar (Fin a) y).val) := by
        funext y
        rw [chart_val]
        exact congrArg (fun x => φ.1 (g * x)) (cornerGL_scalar (sInf E) y).symm
      rw [e]
      refine (φ.2 g).continuousOn.comp_continuous ?_ fun y => val_mem_invSet _
      exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
    · have e : infId E (Units.map (InfType.diagInf E).toMonoidHom k) = diagUnits E k *
          finId E (Units.map (pFin E).toMonoidHom (diagUnits E k))⁻¹ := by
        rw [map_inv, eq_mul_inv_iff_mul_eq]
        exact infId_mul_finId (diagUnits E k)
      have e2 : GeneralLinearGroup.scalar (Fin a) (diagUnits E k) = ratGL E a (GeneralLinearGroup.scalar (Fin a) k) :=
        (map_scalar _ k).symm
      simp only [Function.comp_apply]
      rw [e, map_mul, map_mul, ω.2.2, one_mul, ← mul_assoc, ← scalar_comm (diagUnits E k), e2, mul_assoc, (π.cusp φ hφ).1.left]
      exact congrFun (congrArg Subtype.val (hf _ φ hφ)) g
  intro z φ hφ
  rw [← infId_mul_finId z, map_mul, map_mul, map_mul, Module.End.mul_apply, hf _ φ hφ, map_smul, hi _ φ hφ, smul_smul,
    Units.val_mul, mul_comm]

/- English proof (translation)
The claim follows from `hasCentral_iff.2 (h.hasCentChar (hasCentral_iff.1 hω))`.
-/
theorem Iso.hasCentral (h : Iso π π') (hω : π.HasCentral ω) : π'.HasCentral ω :=
  hasCentral_iff.2 (h.hasCentChar (hasCentral_iff.1 hω))

/- English proof (translation)
Take `⟨φ, hφ, h0⟩` from `(Submodule.ne_bot_iff _).1 π.ne_bot`. Conclude with `Subtype.ext (MonoidHom.ext fun z => Units.ext (smul_left_injective ℂ h0 ((h z φ hφ).symm.trans (h' z φ hφ))))`.
-/
theorem HasCentral.unique (h : π.HasCentral ω) (h' : π.HasCentral ω') : ω = ω' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  exact Subtype.ext (MonoidHom.ext fun z => Units.ext (smul_left_injective ℂ h0 ((h z φ hφ).symm.trans (h' z φ hφ))))

/- English proof (translation)
The claim follows from `hasCentral_iff.2 ((hasCentral_iff.1 h).twist χ)`.
-/
theorem HasCentral.twist (h : π.HasCentral ω) (χ : HChar E) : (π.twist χ).HasCentral (ω * χ ^ a) :=
  hasCentral_iff.2 ((hasCentral_iff.1 h).twist χ)

/- English proof (translation)
Rewrite using `[scalar_comm]`. Conclude with `congrFun (congrArg Subtype.val (h z φ hφ)) g`.
-/
theorem HasCentral.apply (h : π.HasCentral ω) {φ : Sm E a} (hφ : φ ∈ π.V) (z : Ideles E) (g : GA E a) :
    φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g := by
  rw [scalar_comm]
  exact congrFun (congrArg Subtype.val (h z φ hφ)) g

variable (π) in

def IsUnitary : Prop := ∃ ω : HChar E, ω.IsUnitary ∧ π.HasCentral ω

/- English proof (translation)
The claim follows from `hu.imp fun _ hω => ⟨hω.1, h.hasCentral hω.2⟩`.
-/
theorem Iso.isUnitary (h : Iso π π') (hu : π.IsUnitary) : π'.IsUnitary :=
  hu.imp fun _ hω => ⟨hω.1, h.hasCentral hω.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨_, h1, h2⟩ => h2.unique h ▸ h1, fun h1 => ⟨ω, h1, h⟩⟩`.
-/
theorem HasCentral.isUnitary_iff (h : π.HasCentral ω) : π.IsUnitary ↔ ω.IsUnitary :=
  ⟨fun ⟨_, h1, h2⟩ => h2.unique h ▸ h1, fun h1 => ⟨ω, h1, h⟩⟩

/- English proof (translation)
Take `⟨ω, h1, h2⟩` from `h`. Rewrite using `[h2.apply hφ, norm_mul, h1, one_mul]`.
-/
theorem IsUnitary.norm_eq (h : π.IsUnitary) {φ : Sm E a} (hφ : φ ∈ π.V) (z : Ideles E) (g : GA E a) :
    ‖φ.1 (GeneralLinearGroup.scalar (Fin a) z * g)‖ = ‖φ.1 g‖ := by
  obtain ⟨ω, h1, h2⟩ := h
  rw [h2.apply hφ, norm_mul, h1, one_mul]

end CuspSub

omit [IsTotallyComplex E] in

/- English proof (translation)
Introduce `_` and use `norm_one`.
-/
theorem isUnitary_one : (1 : HChar E).IsUnitary := fun _ => norm_one

omit [IsTotallyComplex E] in

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `isUnitary_one`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul h`.
-/
theorem isUnitary_pow {χ : HChar E} (h : χ.IsUnitary) (n : ℕ) : (χ ^ n).IsUnitary := by
  induction n with
  | zero => rw [pow_zero]; exact isUnitary_one
  | succ n ih => rw [pow_succ]; exact ih.mul h

omit [IsTotallyComplex E] in

/- English proof (translation)
Introduce `x` and use `by have h1 : ‖(((χ ^ n).1 x : ℂˣ) : ℂ)‖ = 1 := h x rw [show (χ ^ n).1 x = χ.1 x ^ n from MonoidHom.pow_apply χ.1 n x, Units.val_pow_eq_pow_val, norm_pow] at h1 exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h1`.
-/
theorem isUnitary_of_pow {χ : HChar E} {n : ℕ} (hn : n ≠ 0) (h : (χ ^ n).IsUnitary) : χ.IsUnitary := fun x => by
  have h1 : ‖(((χ ^ n).1 x : ℂˣ) : ℂ)‖ = 1 := h x
  rw [show (χ ^ n).1 x = χ.1 x ^ n from MonoidHom.pow_apply χ.1 n x, Units.val_pow_eq_pow_val, norm_pow] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h1

namespace CG

variable {π : CG E a} {ω ω' : HChar E}

/- English proof (translation)
The claim follows from `exists_congr fun _ => and_congr_right fun _ => CuspSub.hasCentral_iff.symm`.
-/
@[simp] theorem isUnitary_mk (π : CuspSub E a) : (mk π).IsUnitary ↔ π.IsUnitary :=
  exists_congr fun _ => and_congr_right fun _ => CuspSub.hasCentral_iff.symm

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn with`. Consider the case `_ π => exact (CuspSub.hasCentral_iff.2 h).unique (CuspSub.hasCentral_iff.2 h')`.
-/
theorem HasCentChar.unique (h : π.HasCentChar ω) (h' : π.HasCentChar ω') : ω = ω' := by
  induction π using Quotient.inductionOn with
  | _ π => exact (CuspSub.hasCentral_iff.2 h).unique (CuspSub.hasCentral_iff.2 h')

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨_, h1, h2⟩ => h2.unique h ▸ h1, fun h1 => ⟨ω, h1, h⟩⟩`.
-/
theorem HasCentChar.isUnitary_iff (h : π.HasCentChar ω) : π.IsUnitary ↔ ω.IsUnitary :=
  ⟨fun ⟨_, h1, h2⟩ => h2.unique h ▸ h1, fun h1 => ⟨ω, h1, h⟩⟩

/- English proof (translation)
The claim follows from `(hasCentChar_ofChar χ).isUnitary_iff`.
-/
@[simp] theorem isUnitary_ofChar_iff (χ : HChar E) : (ofChar χ).IsUnitary ↔ χ.IsUnitary :=
  (hasCentChar_ofChar χ).isUnitary_iff

/- English proof (translation)
Take `⟨ω, h1, h2⟩` from `h`. Conclude with `⟨_, h1.mul (isUnitary_pow hχ a), h2.twist χ⟩`.
-/
theorem IsUnitary.twist (h : π.IsUnitary) {χ : HChar E} (hχ : χ.IsUnitary) : (π.twist χ).IsUnitary := by
  obtain ⟨ω, h1, h2⟩ := h
  exact ⟨_, h1.mul (isUnitary_pow hχ a), h2.twist χ⟩

/- English proof (translation)
The claim follows from `Function.rightInverse_invFun (RankOne.ofChar_bijective E).2 σ`.
-/
@[simp] theorem ofChar_toChar (σ : CG E 1) : ofChar (toChar σ) = σ :=
  Function.rightInverse_invFun (RankOne.ofChar_bijective E).2 σ

/- English proof (translation)
Rewrite using `[← isUnitary_ofChar_iff, ofChar_toChar]`.
-/
theorem isUnitary_toChar_iff (σ : CG E 1) : (toChar σ).IsUnitary ↔ σ.IsUnitary := by
  rw [← isUnitary_ofChar_iff, ofChar_toChar]

/- English proof (translation)
The claim follows from `h.twist ((isUnitary_toChar_iff σ).2 hσ)`.
-/
theorem IsUnitary.tw (h : π.IsUnitary) {σ : CG E 1} (hσ : σ.IsUnitary) : (π.tw σ).IsUnitary :=
  h.twist ((isUnitary_toChar_iff σ).2 hσ)

/- English proof (translation)
Introduce `h'` and use `hs (exponent_unique ha h h' hν (ν' := 1) (s' := 0) ⟨fun _ _ _ => rfl, fun _ => by simp [HChar.val, HChar.locK, HChar.loc], fun _ => by simp [HChar.inf]⟩ (twist_one _).symm)`.
-/
theorem IsUnitary.not_twist_absPow (ha : 1 ≤ a) (h : π.IsUnitary) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) (hs : s ≠ 0) :
    ¬ (π.twist ν).IsUnitary := fun h' =>
  hs (exponent_unique ha h h' hν (ν' := 1) (s' := 0)
    ⟨fun _ _ _ => rfl, fun _ => by simp [HChar.val, HChar.locK, HChar.loc], fun _ => by simp [HChar.inf]⟩
    (twist_one _).symm)

end CG

variable (E a) in

abbrev CGu : Type := {π : CG E a // π.IsUnitary}

namespace CGu

variable (π : CGu E a)

def twist (χ : {χ : HChar E // χ.IsUnitary}) : CGu E a := ⟨π.1.twist χ.1, π.2.twist χ.2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem twist_val (χ : {χ : HChar E // χ.IsUnitary}) : (π.twist χ).1 = π.1.twist χ.1 := rfl

def tw (σ : CGu E 1) : CGu E a := ⟨π.1.tw σ.1, π.2.tw σ.2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem tw_val (σ : CGu E 1) : (π.tw σ).1 = π.1.tw σ.1 := rfl

abbrev infChar (τ : E →+* ℂ) : Multiset ℂ := π.1.infChar τ

abbrev loc (w : HeightOneSpectrum (𝓞 E)) : Irr (GL (Fin a) (w.adicCompletion E)) := π.1.loc w

abbrev IsRegAlg : Prop := π.1.IsRegAlg

abbrev IsCsd {L : Type} [Field L] [NumberField L] [IsCMField L] (π : CGu L a) : Prop := π.1.IsCsd

def centChar : {χ : HChar E // χ.IsUnitary} := ⟨π.2.choose, π.2.choose_spec.1⟩

/- English proof (translation)
The claim follows from `π.2.choose_spec.2`.
-/
theorem hasCentChar_centChar : π.1.HasCentChar π.centChar.1 := π.2.choose_spec.2

/- English proof (translation)
The claim follows from `(π.twist χ).hasCentChar_centChar.unique (π.hasCentChar_centChar.twist χ.1)`.
-/
theorem centChar_twist (χ : {χ : HChar E // χ.IsUnitary}) : (π.twist χ).centChar.1 = π.centChar.1 * χ.1 ^ a :=
  (π.twist χ).hasCentChar_centChar.unique (π.hasCentChar_centChar.twist χ.1)

variable (E) in

def equivChar : CGu E 1 ≃ {χ : HChar E // χ.IsUnitary} where
  toFun σ := ⟨σ.1.toChar, (CG.isUnitary_toChar_iff _).2 σ.2⟩
  invFun χ := ⟨CG.ofChar χ.1, CG.isUnitary_ofChar χ.2⟩
  left_inv σ := Subtype.ext (CG.ofChar_toChar σ.1)
  right_inv χ := Subtype.ext (CG.toChar_ofChar χ.1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem equivChar_val (σ : CGu E 1) : (equivChar E σ).1 = σ.1.toChar := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem equivChar_symm_val (χ : {χ : HChar E // χ.IsUnitary}) : ((equivChar E).symm χ).1 = CG.ofChar χ.1 := rfl

/- English proof (translation)
The claim follows from `CG.ofChar_toChar σ.1`.
-/
theorem ofChar_equivChar (σ : CGu E 1) : CG.ofChar (equivChar E σ).1 = σ.1 := CG.ofChar_toChar σ.1

/- English proof (translation)
Apply `CG.ofChar_injective` to reduce the goal to its premises. Rewrite using `[ofChar_equivChar, ← CG.twist_ofChar, ofChar_equivChar]`. Both sides reduce to the same expression.
-/
theorem equivChar_tw (σ σ' : CGu E 1) : (equivChar E (σ.tw σ')).1 = (equivChar E σ).1 * (equivChar E σ').1 := by
  apply CG.ofChar_injective
  rw [ofChar_equivChar, ← CG.twist_ofChar, ofChar_equivChar]
  rfl

/- English proof (translation)
The claim follows from `Subtype.ext ((π.1.twist_mul _ _).symm.trans (congrArg π.1.twist (equivChar_tw σ σ').symm))`.
-/
theorem tw_tw (σ σ' : CGu E 1) : (π.tw σ).tw σ' = π.tw (σ.tw σ') :=
  Subtype.ext ((π.1.twist_mul _ _).symm.trans (congrArg π.1.twist (equivChar_tw σ σ').symm))

instance : Inhabited (CGu E 1) := ⟨(equivChar E).symm ⟨1, isUnitary_one⟩⟩

instance : Nontrivial (CGu E 1) := by
  obtain ⟨t, ht⟩ := GlobalTheory.HeckeOne.exists_normChar_ne_one (K := E)
  exact ⟨(equivChar E).symm ⟨_, GlobalTheory.HeckeOne.isUnitary_normChar t⟩, default,
    fun h => ht (congrArg Subtype.val ((equivChar E).symm.injective h))⟩

instance : Inhabited (CGu E 0) :=
  ⟨CG.mk (CuspSub.triv E zero_le_one), (CG.isUnitary_mk _).2 ⟨1, isUnitary_one, fun z φ _ => by
    rw [Subsingleton.elim (GeneralLinearGroup.scalar (Fin 0) z) 1, map_one]
    exact (one_smul ℂ φ).symm⟩⟩

end CGu

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, (default : CGu E 1).2.not_twist_absPow le_rfl (ν := ⟨GlobalTheory.Mem.Chr.CharModel.absHom E 1, (GlobalTheory.Mem.Chr.CharModel.absChar E 1).2⟩) (GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) 1) one_ne_zero⟩`.
-/
theorem exists_not_isUnitary : ∃ σ : CG E 1, ¬ σ.IsUnitary :=
  ⟨_, (default : CGu E 1).2.not_twist_absPow le_rfl
    (ν := ⟨GlobalTheory.Mem.Chr.CharModel.absHom E 1, (GlobalTheory.Mem.Chr.CharModel.absChar E 1).2⟩)
    (GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) 1) one_ne_zero⟩

abbrev HostCGu {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (a : ℕ) : Type :=
  haveI := host_isCMField H; CGu H.E a

/- English proof (translation)
Rewrite using `[CGu.centChar_twist, sq, mul_assoc]`.
-/
example (π : CGu E 2) (χ : {χ : HChar E // χ.IsUnitary}) : (π.twist χ).centChar.1 = π.centChar.1 * χ.1 * χ.1 := by
  rw [CGu.centChar_twist, sq, mul_assoc]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(CG.isRegAlg_ofChar 1).2 fun τ => ⟨0, by simp [CG.expo_one]⟩, by rw [← CG.expo_one τ]; exact CG.infChar_ofChar 1 τ⟩`.
-/
example (τ : E →+* ℂ) : (default : CGu E 1).IsRegAlg ∧ (default : CGu E 1).infChar τ = {0} :=
  ⟨(CG.isRegAlg_ofChar 1).2 fun τ => ⟨0, by simp [CG.expo_one]⟩, by rw [← CG.expo_one τ]; exact CG.infChar_ofChar 1 τ⟩

/- English proof (translation)
The claim follows from `haveI := host_isCMField H; ⟨CGu.equivChar H.E⟩`.
-/
example {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) : Nonempty (HostCGu H 1 ≃ {χ : HChar H.E // χ.IsUnitary}) :=
  haveI := host_isCMField H; ⟨CGu.equivChar H.E⟩

end GlobalTheory.CuspRep
