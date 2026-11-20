import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockUpperOfConjGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrame
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.CenFrameGen

open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.CenFrame

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

local notation3 "E⁺" => NumberField.maximalRealSubfield E

abbrev incl (s : SplitPlace E) : Os s →+* s.v.adicCompletion E⁺ :=
  (s.v.adicCompletionIntegers E⁺).subtype

/- English proof (translation)
Introduce `y y' h`. Use `Matrix.GeneralLinearGroup.ext fun a c => ?_` and prove the remaining obligations. Use `congrArg (fun g : GL (Fin n) (s.v.adicCompletion E⁺) => g.val a c) h` as an intermediate fact. Conclude with `Subtype.ext this`.
-/
theorem map_incl_injective (s : SplitPlace E) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) (incl s)) := by
  intro y y' h
  refine Matrix.GeneralLinearGroup.ext fun a c => ?_
  have := congrArg (fun g : GL (Fin n) (s.v.adicCompletion E⁺) => g.val a c) h
  exact Subtype.ext this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Matrix.GeneralLinearGroup.ext fun a c => h a c`. Introduce `h a c`. Rewrite using `[← h]`.

Both sides reduce to the same expression.
-/
theorem isCompOf_iff (s : SplitPlace E) (κ : GAf E n) (y : GL (Fin n) (Os s)) :
    IsCompOf s κ y ↔ Matrix.GeneralLinearGroup.map (incl s) y = s.loc n κ := by
  constructor
  · intro h; exact Matrix.GeneralLinearGroup.ext fun a c => h a c
  · intro h a c; rw [← h]; rfl

/- English proof (translation)
Set `Y : Matrix (Fin n) (Fin n) (Os s)` to `fun a c => Function.surjInv hφ.surj ((g : Matrix (Fin n) (Fin n) k) a c)`. Establish `hY : Y.map φ = (g : Matrix (Fin n) (Fin n) k)`. Use extensionality with `a c`. Conclude with `Function.surjInv_eq hφ.surj _`. Establish `hdet : IsUnit Y.det`.

Establish `hmax : (RingHom.ker φ).IsMaximal` using `RingHom.ker_isMaximal_of_surjective φ hφ.surj`. Establish `heq` using `IsLocalRing.eq_maximalIdeal hmax`. Establish `h1 : φ Y.det ≠ 0`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hY]`. Conclude with `(Matrix.isUnits_det_units g).ne_zero`.

Assume the negation of the conclusion as `hnu`. Establish `h2 : Y.det ∈ IsLocalRing.maximalIdeal (Os s)` using `hnu`. Rewrite `h2` using `[← heq, RingHom.mem_ker]`. Conclude with `h1 h2`. Use `⟨Matrix.nonsingInvUnit Y hdet, ?_⟩` and prove the remaining obligations.

Use extensionality with `a c`. Conclude with `congrFun (congrFun hY a) c`.
-/
theorem exists_lift {s : SplitPlace E} {k : Type} [Field k] {φ : Os s →+* k} (hφ : IsResidue s φ)
    (g : GL (Fin n) k) : ∃ y : GL (Fin n) (Os s), Matrix.GeneralLinearGroup.map φ y = g := by
  let Y : Matrix (Fin n) (Fin n) (Os s) := fun a c => Function.surjInv hφ.surj ((g : Matrix (Fin n) (Fin n) k) a c)
  have hY : Y.map φ = (g : Matrix (Fin n) (Fin n) k) := by
    ext a c; exact Function.surjInv_eq hφ.surj _
  have hdet : IsUnit Y.det := by
    have hmax : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφ.surj
    have heq := IsLocalRing.eq_maximalIdeal hmax
    have h1 : φ Y.det ≠ 0 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hY]
      exact (Matrix.isUnits_det_units g).ne_zero
    by_contra hnu
    have h2 : Y.det ∈ IsLocalRing.maximalIdeal (Os s) := hnu
    rw [← heq, RingHom.mem_ker] at h2
    exact h1 h2
  refine ⟨Matrix.nonsingInvUnit Y hdet, ?_⟩
  ext a c
  exact congrFun (congrFun hY a) c

/- English proof (translation)
Take `⟨κ, hκ, hl⟩` from `GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s (Matrix.GeneralLinearGroup.map (incl s) y)`. Use `⟨κ, GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ hκ ?_ ?_, hκ, hl⟩` and prove the remaining obligations. Introduce `i j`. Rewrite using `[hl]`. Use `(y.val i j).2` as an intermediate fact.

Rewrite `this` using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Then use the resulting hypothesis. Introduce `i j`. Rewrite using `[map_inv, hl, ← map_inv]`. Use `((y⁻¹).val i j).2` as an intermediate fact. Rewrite `this` using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Then use the resulting hypothesis.
-/
theorem exists_pt (s : SplitPlace E) (y : GL (Fin n) (Os s)) :
    ∃ κ : GAf E n, κ ∈ Umax E n ∧ TrivOutside {s.v} κ ∧
      s.loc n κ = Matrix.GeneralLinearGroup.map (incl s) y := by
  obtain ⟨κ, hκ, hl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s (Matrix.GeneralLinearGroup.map (incl s) y)
  refine ⟨κ, GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ hκ ?_ ?_, hκ, hl⟩
  · intro i j
    rw [hl]
    have := (y.val i j).2
    rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this
  · intro i j
    rw [map_inv, hl, ← map_inv]
    have := ((y⁻¹).val i j).2
    rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this

/- English proof (translation)
Establish `key : ∀ x : Os s, φ x = 0 → Valued.v ((x : s.v.adicCompletion E⁺)) < 1` using `fun x hx => (hφ.ker x).1 hx`. Use `⟨⟨⟨y, rfl⟩, fun a b ha hb => ?_⟩, fun a b ha hb => ⟨fun hba => ?_, fun hab => ?_⟩⟩` and prove the remaining obligations. Conclude with `key _ ((hy a b).1 ha hb)`. Conclude with `key _ ((hy a b).2.1 ha hba)`. Substitute `hab` using the available equality.

Establish `h1 : φ (y.val a a - 1) = 0`. Use `(hy a a).2.2 ha rfl` as an intermediate fact. Rewrite using `[map_sub, map_one]`. Conclude with `sub_eq_zero.2 this`. Use `key _ h1` as an intermediate fact.

Simplify using `using this`.
-/
theorem uniRT_of_red {s : SplitPlace E} {k : Type} [Field k] {φ : Os s →+* k} (hφ : IsResidue s φ) (r : ℕ)
    (y : GL (Fin n) (Os s))
    (hy : ∀ i j : Fin n, (r ≤ i.val → j.val < r → (Matrix.GeneralLinearGroup.map φ y).val i j = 0) ∧
        (i.val < r → j.val < i.val → (Matrix.GeneralLinearGroup.map φ y).val i j = 0) ∧
        (i.val < r → i = j → (Matrix.GeneralLinearGroup.map φ y).val i j = 1)) :
    Formalism.L2.NG.UniRT s r (Matrix.GeneralLinearGroup.map (incl s) y) := by
  have key : ∀ x : Os s, φ x = 0 → Valued.v ((x : s.v.adicCompletion E⁺)) < 1 := fun x hx => (hφ.ker x).1 hx
  refine ⟨⟨⟨y, rfl⟩, fun a b ha hb => ?_⟩, fun a b ha hb => ⟨fun hba => ?_, fun hab => ?_⟩⟩
  · exact key _ ((hy a b).1 ha hb)
  · exact key _ ((hy a b).2.1 ha hba)
  · subst hab
    have h1 : φ (y.val a a - 1) = 0 := by
      have := (hy a a).2.2 ha rfl
      rw [map_sub, map_one]
      exact sub_eq_zero.2 this
    have := key _ h1
    simpa using this

/- English proof (translation)
Use extensionality with `a e`. Simplify using `only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_transv {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (i j : Fin n) (c : R) :
    (Matrix.transvection i j c).map ψ = Matrix.transvection i j (ψ c) := by
  ext a e
  simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `a e`. Simplify using `only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff]`. Use `⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg (by omega), if_neg (by omega), add_zero]`. Rewrite using `[if_neg (by omega), if_neg (by omega), add_zero]`.

Rewrite using `[if_pos h2, if_neg (by omega), add_zero]`.
-/
theorem transv_blockUni {R : Type} [CommRing R] {r : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val) (c : R) :
    ∀ a e : Fin n, (r ≤ a.val → e.val < r → Matrix.transvection i j c a e = 0) ∧
      (a.val < r → e.val < a.val → Matrix.transvection i j c a e = 0) ∧
      (a.val < r → a = e → Matrix.transvection i j c a e = 1) := by
  intro a e
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [if_neg (by omega), if_neg (by omega), add_zero]
  · rw [if_neg (by omega), if_neg (by omega), add_zero]
  · rw [if_pos h2, if_neg (by omega), add_zero]

/- English proof (translation)
Establish `h : ∀ a b : Fin n, (if a.val + 1 = b.val ∧ b.val < r then Matrix.transvection i j x a b else 0) = if j = b then (if i = a then x else 0) else 0`. Introduce `a b`. Simplify using `only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | omega | simp`. Unfold `Formalism.L2.NG.supDiag`.

Rewrite using `[hM]`. Simplify using `only [h, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem supDiag_transv (s : SplitPlace E) {r : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val) (hj : j.val < r)
    (x : s.v.adicCompletion E⁺) (M : GL (Fin n) (s.v.adicCompletion E⁺)) (hM : M.val = Matrix.transvection i j x) :
    Formalism.L2.NG.supDiag s r M = x := by
  have h : ∀ a b : Fin n, (if a.val + 1 = b.val ∧ b.val < r then Matrix.transvection i j x a b else 0) =
      if j = b then (if i = a then x else 0) else 0 := by
    intro a b
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  unfold Formalism.L2.NG.supDiag
  rw [hM]
  simp only [h, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Unfold `Formalism.L2.NG.detDD`. Rewrite using `[hM]`. Establish `h : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => Matrix.transvection i j x a.1 b.1) = 1`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Establish `ha` using `a.2`.

Simplify using `only [Matrix.of_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Subtype.ext_iff]`. Rewrite using `[if_neg (c := i = a.1 ∧ j = b.1) (fun h => by rw [← h.1] at ha; omega), add_zero]`. Rewrite using `[h, Matrix.det_one]`.
-/
theorem detDD_transv (s : SplitPlace E) {r : ℕ} (i j : Fin n) (hi : i.val < r)
    (x : s.v.adicCompletion E⁺) (M : GL (Fin n) (s.v.adicCompletion E⁺)) (hM : M.val = Matrix.transvection i j x) :
    Formalism.L2.NG.detDD s r M = 1 := by
  unfold Formalism.L2.NG.detDD
  rw [hM]
  have h : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => Matrix.transvection i j x a.1 b.1) = 1 := by
    refine Matrix.ext fun a b => ?_
    have ha := a.2
    simp only [Matrix.of_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      Subtype.ext_iff]
    rw [if_neg (c := i = a.1 ∧ j = b.1) (fun h => by rw [← h.1] at ha; omega), add_zero]
  rw [h, Matrix.det_one]

def eigGrp (s : SplitPlace E) (f : GAf E n → ℂ) : Subgroup (GAf E n) where
  carrier := {κ | κ ∈ Umax E n ∧ TrivOutside {s.v} κ ∧ ∃ c : ℂ, c ≠ 0 ∧ ∀ g, f (g * κ) = c * f g}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, c, hc, hac⟩ ⟨hb1, hb2, d, hd, hbd⟩
    refine ⟨mul_mem ha1 hb1, GlobalTheory.HeckeStdFacts.triv_mul ha2 hb2, d * c, mul_ne_zero hd hc, fun g => ?_⟩
    rw [← mul_assoc, hbd, hac, mul_assoc]
  one_mem' := ⟨one_mem _, GlobalTheory.HeckeStdFacts.triv_one, 1, one_ne_zero, fun g => by rw [mul_one, one_mul]⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2, c, hc, hac⟩
    refine ⟨inv_mem ha1, GlobalTheory.HeckeStdFacts.triv_inv ha2, c⁻¹, inv_ne_zero hc, fun g => ?_⟩
    have := hac (g * a⁻¹)
    rw [inv_mul_cancel_right] at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/- English proof (translation)
Rewrite using `[hc, mul_div_assoc, div_self h0, mul_one]`.
-/
theorem ratio_eq {G : Type} [Group G] {f : G → ℂ} {g₀ κ : G} (h0 : f g₀ ≠ 0) {c : ℂ} (hc : ∀ g, f (g * κ) = c * f g) :
    f (g₀ * κ) / f g₀ = c := by
  rw [hc, mul_div_assoc, div_self h0, mul_one]

def eigChar (s : SplitPlace E) (f : GAf E n → ℂ) (g₀ : GAf E n) (h0 : f g₀ ≠ 0) : eigGrp s f →* ℂˣ where
  toFun κ := Units.mk0 (f (g₀ * κ.1) / f g₀) (by
    obtain ⟨_, _, c, hc0, hc⟩ := κ.2
    rw [ratio_eq h0 hc]; exact hc0)
  map_one' := by
    refine Units.ext ?_
    show f (g₀ * 1) / f g₀ = 1
    rw [mul_one, div_self h0]
  map_mul' a b := by
    refine Units.ext ?_
    show f (g₀ * (a.1 * b.1)) / f g₀ = f (g₀ * a.1) / f g₀ * (f (g₀ * b.1) / f g₀)
    obtain ⟨_, _, c, _, hc⟩ := b.2
    rw [ratio_eq h0 hc, ← mul_assoc, hc]
    ring

/- English proof (translation)
The claim follows from `ratio_eq h0 hc`.
-/
theorem eigChar_val (s : SplitPlace E) (f : GAf E n → ℂ) (g₀ : GAf E n) (h0 : f g₀ ≠ 0) (κ : eigGrp s f) {c : ℂ}
    (hc : ∀ g, f (g * κ.1) = c * f g) : ((eigChar s f g₀ h0 κ : ℂˣ) : ℂ) = c :=
  ratio_eq h0 hc

/- English proof (translation)
Take `⟨y, hy⟩` from `GlobalTheory.BlockLiftFrame.exists_isCompOf s hκ`. Conclude with `⟨y, (isCompOf_iff s κ y).1 hy⟩`.
-/
theorem loc_mem_range (s : SplitPlace E) {κ : GAf E n} (hκ : κ ∈ Umax E n) :
    s.loc n κ ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (incl s)).range := by
  obtain ⟨y, hy⟩ := GlobalTheory.BlockLiftFrame.exists_isCompOf s hκ
  exact ⟨y, (isCompOf_iff s κ y).1 hy⟩

def compHom (s : SplitPlace E) (f : GAf E n → ℂ) : eigGrp s f →* GL (Fin n) (Os s) :=
  (MonoidHom.ofInjective (map_incl_injective s)).symm.toMonoidHom.comp
    (((s.loc n).comp (eigGrp s f).subtype).codRestrict _ fun κ => loc_mem_range s κ.2.1)

/- English proof (translation)
Use `show (MonoidHom.ofInjective (map_incl_injective s)).symm _ = y`. Rewrite using `[MulEquiv.symm_apply_eq]`. Conclude with `Subtype.ext hy`.
-/
theorem compHom_eq (s : SplitPlace E) (f : GAf E n → ℂ) (κ : eigGrp s f) (y : GL (Fin n) (Os s))
    (hy : s.loc n κ.1 = Matrix.GeneralLinearGroup.map (incl s) y) : compHom s f κ = y := by
  show (MonoidHom.ofInjective (map_incl_injective s)).symm _ = y
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext hy

def red (s : SplitPlace E) (f : GAf E n → ℂ) {k : Type} [Field k] (φ : Os s →+* k) (b : GL (Fin n) k) :
    eigGrp s f →* GL (Fin n) k :=
  (MulAut.conj b).toMonoidHom.comp ((Matrix.GeneralLinearGroup.map φ).comp (compHom s f))

/- English proof (translation)
Rewrite using `[← compHom_eq s f κ y hy]`. Both sides reduce to the same expression.
-/
theorem red_eq (s : SplitPlace E) (f : GAf E n → ℂ) {k : Type} [Field k] (φ : Os s →+* k) (b : GL (Fin n) k)
    (κ : eigGrp s f) (y : GL (Fin n) (Os s)) (hy : s.loc n κ.1 = Matrix.GeneralLinearGroup.map (incl s) y) :
    red s f φ b κ = b * Matrix.GeneralLinearGroup.map φ y * b⁻¹ := by
  rw [← compHom_eq s f κ y hy]
  rfl

end Local

/- English proof (translation)
Use `⟨(QuotientGroup.lift p.ker q h).comp (QuotientGroup.quotientKerEquivRange p).symm.toMonoidHom, fun g => ?_⟩` and prove the remaining obligations. Establish `: (QuotientGroup.quotientKerEquivRange p).symm (p.rangeRestrict g) = (g : G ⧸ p.ker)`. Rewrite using `[MulEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, QuotientGroup.lift_mk]`.
-/
theorem exists_descend {G M A : Type} [Group G] [Group M] [CommGroup A] (p : G →* M) (q : G →* A)
    (h : p.ker ≤ q.ker) : ∃ χ : p.range →* A, ∀ g, χ (p.rangeRestrict g) = q g := by
  refine ⟨(QuotientGroup.lift p.ker q h).comp (QuotientGroup.quotientKerEquivRange p).symm.toMonoidHom, fun g => ?_⟩
  have : (QuotientGroup.quotientKerEquivRange p).symm (p.rangeRestrict g) = (g : G ⧸ p.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, QuotientGroup.lift_mk]

/- English proof (translation)
Introduce `E _ _ _ n r t hn hr s k _ φ hφ hc f hf J χ ψ₀ ξ hψ hLU hJ b hb`. Take `⟨g₀, hg₀⟩ : ∃ g₀, f g₀ ≠ 0` from `Function.ne_iff.1 hf`. Establish `cne : ∀ κ (c : ℂ), (∀ g, f (g * κ) = c * f g) → c ≠ 0`. Introduce `κ c hc h0`. Use `hc (g₀ * κ⁻¹)` as an intermediate fact.

Rewrite `this` using `[inv_mul_cancel_right, h0, zero_mul]`. Conclude with `hg₀ this`. Establish `hker : (red s f φ b).ker ≤ (eigChar s f g₀ hg₀).ker`. Introduce `κ hκ`. Rewrite `hκ`, the goal using `[MonoidHom.mem_ker]`.

Take `⟨y, hy⟩` from `GlobalTheory.BlockLiftFrame.exists_isCompOf s κ.2.1`. Rewrite `hκ` using `[red_eq s f φ b κ y ((isCompOf_iff s κ.1 y).1 hy).symm]`. Establish `h1 : Matrix.GeneralLinearGroup.map φ y = 1` using `conj_eq_one_iff.1 hκ`. Establish `h2` using `(hb κ.1 κ.2.1 κ.2.2.1 y hy).2 h1`. Conclude with `Units.ext (eigChar_val s f g₀ hg₀ κ (c := 1) fun g => by rw [h2, one_mul])`.

Take `⟨χH, hχH⟩` from `exists_descend _ _ hker`. Substitute `hn` using the available equality. Establish `main` using `GlobalTheory.GenericCharBlockConj.block_upper_of_conj_generic r t hr hc b (red s f φ b).range χH ?_ ?_`. Rewrite using `[Formalism.L2.DIV.mem_blockTri]`. Introduce `i j hij`.

Unfold `Formalism.L2.DIV.blk2 at hij`. Apply the tactic sequence `refine main i j ?_ ?_ <;> split_ifs at hij <;> omega`. Introduce `g hg`. Prove the components needed by the constructor for the conclusion. Take `⟨y, hy⟩` from `exists_lift hφ (b⁻¹ * g * b)`.

Take `⟨κ, hU, hT, hl⟩` from `exists_pt s y`. Establish `hg' : b * Matrix.GeneralLinearGroup.map φ y * b⁻¹ = g` using `by rw [hy]; group`. Take `⟨c, hc'⟩` from `(hb κ hU hT y ((isCompOf_iff s κ y).2 hl.symm)).1 (by rw [hg']; exact hg)`. Establish `hmem : κ ∈ eigGrp s f` using `⟨hU, hT, c, cne κ c hc', hc'⟩`. Conclude with `MonoidHom.mem_range.2 ⟨⟨κ, hmem⟩, by rw [red_eq s f φ b ⟨κ, hmem⟩ y hl, hg']⟩`.

Take `⟨y, hy⟩` from `exists_lift hφ g`. Take `⟨κ, hU, hT, hl⟩` from `exists_pt s y`. Establish `hJκ : κ ∈ J` using `(hLU.mem κ hT).2 (by rw [hl]; exact uniRT_of_red hφ r y (by rw [hy]; exact hg))`. Establish `hmem : κ ∈ eigGrp s f` using `⟨hU, hT, _, Units.ne_zero _, hJ κ hJκ⟩`. Conclude with `MonoidHom.mem_range.2 ⟨⟨κ, hmem⟩, by rw [red_eq s f φ b ⟨κ, hmem⟩ y hl, hy]⟩`.

Introduce `i j hij hj`. Take `⟨_, x₀, hx₀, hψx⟩` from `hψ`. Establish `hx₁ : x₀ ∈ s.v.adicCompletionIntegers (NumberField.maximalRealSubfield E)`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]` and apply the resulting hypothesis. Set `x' : Os s` to `⟨x₀, hx₁⟩`.

Establish `hij' : i ≠ j` using `by intro h; rw [h] at hij; omega`. Set `y : GL (Fin (r + t)) (Os s)` to `Matrix.nonsingInvUnit (Matrix.transvection i j x') (by rw [Matrix.det_transvection_of_ne i j hij']; exact isUnit_one)`. Establish `hyφ : (Matrix.GeneralLinearGroup.map φ y).val = Matrix.transvection i j (φ x')` using `map_transv φ i j x'`. Establish `hyι : (Matrix.GeneralLinearGroup.map (incl s) y).val = Matrix.transvection i j x₀` using `map_transv (incl s) i j x'`. Take `⟨κ, hU, hT, hl⟩` from `exists_pt s y`.

Establish `hJκ : κ ∈ J` using `(hLU.mem κ hT).2 (by`. Rewrite using `[hl]; exact uniRT_of_red hφ r y (by rw [hyφ]; exact transv_blockUni i j hij _))`. Establish `hmem : κ ∈ eigGrp s f` using `⟨hU, hT, _, Units.ne_zero _, hJ κ hJκ⟩`. Establish `hM : (s.loc (r + t) κ).val = Matrix.transvection i j x₀` using `by rw [hl]; exact hyι`. Use `⟨φ x', (red s f φ b).rangeRestrict ⟨κ, hmem⟩, ?_, ?_⟩` and prove the remaining obligations.

Use `show (red s f φ b ⟨κ, hmem⟩).val = _`. Rewrite using `[red_eq s f φ b ⟨κ, hmem⟩ y hl, Units.val_mul, Units.val_mul, hyφ]`. Rewrite using `[hχH]`. Introduce `h1`. Establish `h2` using `eigChar_val s f g₀ hg₀ ⟨κ, hmem⟩ (hJ κ hJκ)`.

Rewrite `h2` using `[h1, hLU.chr κ hJκ hT 1 (detDD_transv s i j (by omega) x₀ _ hM).symm, supDiag_transv s i j hij hj x₀ _ hM, map_one, Units.val_one, mul_one]`. Conclude with `hψx h2.symm`.
-/
theorem block_upper_of_eigen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {n r t : ℕ}, n = r + t → 2 ≤ r →
    ∀ (s : ReciprocityTheory.Aut.SplitPlace E) {k : Type} [Field k] (φ : GlobalTheory.CenFrame.Os s →+* k), GlobalTheory.CenFrame.IsResidue s φ →
    (∃ c : k, c ≠ 0 ∧ c ≠ 1) → ∀ (f : Formalism.AUTREP.GAf E n → ℂ), f ≠ 0 →
    ∀ (J : Subgroup (Formalism.AUTREP.GAf E n)) (χ : J →* ℂˣ)
    (ψ₀ : AddChar (s.v.adicCompletion (NumberField.maximalRealSubfield E)) ℂ)
    (ξ : (s.v.adicCompletion (NumberField.maximalRealSubfield E))ˣ →* ℂˣ),
    Formalism.L2.NG.IsPsi0 s ψ₀ → Formalism.L2.NG.LevelUni J χ s r ψ₀ ξ →
    (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) →
    ∀ (b : GL (Fin n) k),
    (∀ κ ∈ ReciprocityTheory.Aut.Umax E n, ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ y : GL (Fin n) (GlobalTheory.CenFrame.Os s),
        GlobalTheory.CenFrame.IsCompOf s κ y →
      ((∀ i j : Fin n, (r ≤ i.val → j.val < r → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < r → j.val < i.val → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < r → i = j → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 1)) →
        ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
      (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g)) →
    b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  intro E _ _ _ n r t hn hr s k _ φ hφ hc f hf J χ ψ₀ ξ hψ hLU hJ b hb
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, f g₀ ≠ 0 := Function.ne_iff.1 hf
  have cne : ∀ κ (c : ℂ), (∀ g, f (g * κ) = c * f g) → c ≠ 0 := by
    intro κ c hc h0
    have := hc (g₀ * κ⁻¹)
    rw [inv_mul_cancel_right, h0, zero_mul] at this
    exact hg₀ this
  have hker : (red s f φ b).ker ≤ (eigChar s f g₀ hg₀).ker := by
    intro κ hκ
    rw [MonoidHom.mem_ker] at hκ ⊢
    obtain ⟨y, hy⟩ := GlobalTheory.BlockLiftFrame.exists_isCompOf s κ.2.1
    rw [red_eq s f φ b κ y ((isCompOf_iff s κ.1 y).1 hy).symm] at hκ
    have h1 : Matrix.GeneralLinearGroup.map φ y = 1 := conj_eq_one_iff.1 hκ
    have h2 := (hb κ.1 κ.2.1 κ.2.2.1 y hy).2 h1
    exact Units.ext (eigChar_val s f g₀ hg₀ κ (c := 1) fun g => by rw [h2, one_mul])
  obtain ⟨χH, hχH⟩ := exists_descend _ _ hker
  subst hn
  have main := GlobalTheory.GenericCharBlockConj.block_upper_of_conj_generic r t hr hc b (red s f φ b).range χH ?_ ?_
  · rw [Formalism.L2.DIV.mem_blockTri]
    intro i j hij
    unfold Formalism.L2.DIV.blk2 at hij
    refine main i j ?_ ?_ <;> split_ifs at hij <;> omega
  · intro g hg
    constructor
    · obtain ⟨y, hy⟩ := exists_lift hφ (b⁻¹ * g * b)
      obtain ⟨κ, hU, hT, hl⟩ := exists_pt s y
      have hg' : b * Matrix.GeneralLinearGroup.map φ y * b⁻¹ = g := by rw [hy]; group
      obtain ⟨c, hc'⟩ := (hb κ hU hT y ((isCompOf_iff s κ y).2 hl.symm)).1 (by rw [hg']; exact hg)
      have hmem : κ ∈ eigGrp s f := ⟨hU, hT, c, cne κ c hc', hc'⟩
      exact MonoidHom.mem_range.2 ⟨⟨κ, hmem⟩, by rw [red_eq s f φ b ⟨κ, hmem⟩ y hl, hg']⟩
    · obtain ⟨y, hy⟩ := exists_lift hφ g
      obtain ⟨κ, hU, hT, hl⟩ := exists_pt s y
      have hJκ : κ ∈ J := (hLU.mem κ hT).2 (by rw [hl]; exact uniRT_of_red hφ r y (by rw [hy]; exact hg))
      have hmem : κ ∈ eigGrp s f := ⟨hU, hT, _, Units.ne_zero _, hJ κ hJκ⟩
      exact MonoidHom.mem_range.2 ⟨⟨κ, hmem⟩, by rw [red_eq s f φ b ⟨κ, hmem⟩ y hl, hy]⟩
  · intro i j hij hj
    obtain ⟨_, x₀, hx₀, hψx⟩ := hψ
    have hx₁ : x₀ ∈ s.v.adicCompletionIntegers (NumberField.maximalRealSubfield E) := by
      rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    let x' : Os s := ⟨x₀, hx₁⟩
    have hij' : i ≠ j := by intro h; rw [h] at hij; omega
    let y : GL (Fin (r + t)) (Os s) := Matrix.nonsingInvUnit (Matrix.transvection i j x')
      (by rw [Matrix.det_transvection_of_ne i j hij']; exact isUnit_one)
    have hyφ : (Matrix.GeneralLinearGroup.map φ y).val = Matrix.transvection i j (φ x') := map_transv φ i j x'
    have hyι : (Matrix.GeneralLinearGroup.map (incl s) y).val = Matrix.transvection i j x₀ :=
      map_transv (incl s) i j x'
    obtain ⟨κ, hU, hT, hl⟩ := exists_pt s y
    have hJκ : κ ∈ J := (hLU.mem κ hT).2 (by
      rw [hl]; exact uniRT_of_red hφ r y (by rw [hyφ]; exact transv_blockUni i j hij _))
    have hmem : κ ∈ eigGrp s f := ⟨hU, hT, _, Units.ne_zero _, hJ κ hJκ⟩
    have hM : (s.loc (r + t) κ).val = Matrix.transvection i j x₀ := by rw [hl]; exact hyι
    refine ⟨φ x', (red s f φ b).rangeRestrict ⟨κ, hmem⟩, ?_, ?_⟩
    · show (red s f φ b ⟨κ, hmem⟩).val = _
      rw [red_eq s f φ b ⟨κ, hmem⟩ y hl, Units.val_mul, Units.val_mul, hyφ]
    · rw [hχH]
      intro h1
      have h2 := eigChar_val s f g₀ hg₀ ⟨κ, hmem⟩ (hJ κ hJκ)
      rw [h1, hLU.chr κ hJκ hT 1 (detDD_transv s i j (by omega) x₀ _ hM).symm,
        supDiag_transv s i j hij hj x₀ _ hM, map_one, Units.val_one, mul_one] at h2
      exact hψx h2.symm

end GlobalTheory.CenFrameGen

end
