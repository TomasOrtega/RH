import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtAComap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

open Formalism.L2.Host

variable {D : D7} {T N : Type}

/- English proof (translation)
Rewrite using `[SubgroupClass.coe_pow, MonoidHom.pow_apply]`.
-/
theorem pow_apply' {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (x) : (χ ^ a).1 x = χ.1 x ^ a := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

/- English proof (translation)
The claim follows from `pow_apply' χ a _`.
-/
theorem loc_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).loc v x = χ.loc v x ^ a :=
  pow_apply' χ a _

/- English proof (translation)
The claim follows from `pow_apply' χ a _`.
-/
theorem locK_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).locK v x = χ.locK v x ^ a :=
  pow_apply' χ a _

/- English proof (translation)
Use `⟨fun v k => ?_, fun w k => ?_⟩` and prove the remaining obligations. Establish `h1` using `h.1 v k`. Simplify using `only [HChar.resFin, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢`. Simplify using `only [locK_pow]`. Rewrite using `[Finset.prod_pow, h1, one_pow]`.

Establish `h1` using `h.2 w k`. Simplify using `only [HChar.resInf, HChar.locInf, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢`. Simplify using `only [pow_apply']`. Rewrite using `[Finset.prod_pow, h1, one_pow]`.
-/
theorem trivOn_pow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ : HChar E}
    (h : χ.TrivOn F) (a : ℕ) : (χ ^ a).TrivOn F := by
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · have h1 := h.1 v k
    simp only [HChar.resFin, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [locK_pow]
    rw [Finset.prod_pow, h1, one_pow]
  · have h1 := h.2 w k
    simp only [HChar.resInf, HChar.locInf, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [pow_apply']
    rw [Finset.prod_pow, h1, one_pow]

/- English proof (translation)
Introduce `x hx` and use `by rw [loc_pow, h x hx, one_pow]`.
-/
theorem unrAt_pow {E : Type} [Field E] [NumberField E] {χ : HChar E} {v} (h : χ.UnrAt v) (a : ℕ) : (χ ^ a).UnrAt v :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

/- English proof (translation)
Use `⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩` and prove the remaining obligations. Establish `: ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `h.1.1.pow a`. Establish `h1` using `h.1.2 x`. Simplify using `only [MonoidHom.pow_apply, h1, one_pow]`. Rewrite using `[MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]`. Conclude with `map_pow Circle.coeHom _ _`.
-/
theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) : ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · rw [MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

/- English proof (translation)
Establish `h1` using `chrEq_pow h n`. Rewrite `h1` using `[show χ ^ n = 1 from hn]`. Conclude with `MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x`.
-/
theorem pow_eq_one_of_chrEq {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) {n : ℕ} (hn : χ.OrderDvd n) :
    c ^ n = 1 := by
  have h1 := chrEq_pow h n
  rw [show χ ^ n = 1 from hn] at h1
  exact MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x

/- English proof (translation)
Use `haveI : NeZero n := ⟨hn.ne'⟩`. Establish `hζ` using `Complex.isPrimitiveRoot_exp n hn.ne'`. Take `⟨a, ha, h⟩` from `hζ.eq_pow_of_pow_eq_one (ξ := τ (Complex.exp (2 * Real.pi * Complex.I / n))) (by rw [← map_pow, hζ.pow_eq_one, map_one])`. Use `⟨a, ha, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨b, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hz`.

Rewrite using `[map_pow, ← h, ← pow_mul, ← pow_mul, mul_comm a b]`.
-/
theorem exists_pow_aut (τ : ℂ ≃+* ℂ) {n : ℕ} (hn : 0 < n) : ∃ a, a < n ∧ ∀ z : ℂ, z ^ n = 1 → τ z = z ^ a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨a, ha, h⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ (Complex.exp (2 * Real.pi * Complex.I / n)))
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  refine ⟨a, ha, fun z hz => ?_⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  rw [map_pow, ← h, ← pow_mul, ← pow_mul, mul_comm a b]

/- English proof (translation)
Take `⟨n, hn, ho⟩` from `hL.xi_fin t`. Establish `h1 : ∀ x, ((L.xi t x : Circle) : ℂ) ^ n = 1` using `fun x => by`. Use `DFunLike.congr_fun (pow_eq_one_of_chrEq (hL.xi t) ho) x` as an intermediate fact. Rewrite `this` using `[MonoidHom.pow_apply, MonoidHom.one_apply]`. Conclude with `(map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)`.

Establish `h2 : ∀ a x, (((L.xi t ^ a) x : Circle) : ℂ) = ((L.xi t x : Circle) : ℂ) ^ a` using `fun a x => by`. Rewrite using `[MonoidHom.pow_apply]`. Conclude with `map_pow Circle.coeHom _ _`. Use `⟨n, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, h⟩` from `exists_pow_aut τ hn`.

Take `⟨b, -, h'⟩` from `exists_pow_aut τ.symm hn`. Use `⟨a, ha, fun x => by rw [h2, h _ (h1 x)], b, ?_⟩` and prove the remaining obligations. Establish `e : (L.xi t ^ a) ^ b = L.xi t` using `MonoidHom.ext fun x => Circle.ext (by`. Rewrite using `[← pow_mul, h2, pow_mul, ← h _ (h1 x), ← h' _ (by rw [← map_pow, h1, map_one]), RingEquiv.symm_apply_apply])`. Conclude with `GlobalTheory.ChrEqUnique.hchar_unique D (L.xi t) _ _ (e ▸ chrEq_pow (chrEq_pow (hL.xi t) a) b) (hL.xi t)`.
-/
theorem exists_conj_pow {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) : ∃ n : ℕ, ∀ τ : ℂ ≃+* ℂ, ∃ a, a < n ∧
    (∀ x, (((L.xi t ^ a) x : Circle) : ℂ) = τ ((L.xi t x : Circle) : ℂ)) ∧ ∃ b, (L.xiH t ^ a) ^ b = L.xiH t := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 : ∀ x, ((L.xi t x : Circle) : ℂ) ^ n = 1 := fun x => by
    have := DFunLike.congr_fun (pow_eq_one_of_chrEq (hL.xi t) ho) x
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    exact (map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)
  have h2 : ∀ a x, (((L.xi t ^ a) x : Circle) : ℂ) = ((L.xi t x : Circle) : ℂ) ^ a := fun a x => by
    rw [MonoidHom.pow_apply]; exact map_pow Circle.coeHom _ _
  refine ⟨n, fun τ => ?_⟩
  obtain ⟨a, ha, h⟩ := exists_pow_aut τ hn
  obtain ⟨b, -, h'⟩ := exists_pow_aut τ.symm hn
  refine ⟨a, ha, fun x => by rw [h2, h _ (h1 x)], b, ?_⟩
  have e : (L.xi t ^ a) ^ b = L.xi t := MonoidHom.ext fun x => Circle.ext (by
    rw [← pow_mul, h2, pow_mul, ← h _ (h1 x), ← h' _ (by rw [← map_pow, h1, map_one]), RingEquiv.symm_apply_apply])
  exact GlobalTheory.ChrEqUnique.hchar_unique D (L.xi t) _ _ (e ▸ chrEq_pow (chrEq_pow (hL.xi t) a) b) (hL.xi t)

def SamePlaces (L : LevCh D T) (S : Set (ℂ ≃+* ℂ)) : Prop :=
  ∀ (t t' : T) (τ τ' : ℂ ≃+* ℂ), τ ∈ S → (τ' ∈ S ∨ τ' = RingEquiv.refl ℂ) →
    (∀ x, τ ((L.xi t x : Circle) : ℂ) = τ' ((L.xi t' x : Circle) : ℂ)) → L.Q t' = L.Q t

end GlobalTheory.ConjExt

end
