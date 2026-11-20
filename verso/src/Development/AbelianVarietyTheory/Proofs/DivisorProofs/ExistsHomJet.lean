import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SquareLiftLemmas

open CategoryTheory GlobalTheory.AnPer GlobalTheory.AnPer.Charts

def liftSq {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) : TrivSqZeroExt O (Fin g → O) →+* C where
  toFun x := ρ x.fst + ∑ a, ρ (x.snd a) * n a
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, Pi.add_apply, map_add, add_mul,
      Finset.sum_add_distrib]
    ring
  map_mul' x y := by
    have h0 : (∑ a, ρ (x.snd a) * n a) * (∑ b, ρ (y.snd b) * n b) = 0 := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
      rw [mul_mul_mul_comm, hn, mul_zero]
    have h1 : ∀ a, ρ ((x * y).snd a) * n a =
        ρ x.fst * (ρ (y.snd a) * n a) + (ρ (x.snd a) * n a) * ρ y.fst := fun a ↦ by
      have : (x * y).snd a = x.fst * y.snd a + x.snd a * y.fst := by
        simp [TrivSqZeroExt.snd_mul, mul_comm]
      rw [this, map_add, map_mul, map_mul]; ring
    rw [add_mul, mul_add, mul_add, h0, add_zero, TrivSqZeroExt.fst_mul, map_mul]
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftSq_apply {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (x : TrivSqZeroExt O (Fin g → O)) :
    liftSq ρ n hn x = ρ x.fst + ∑ a, ρ (x.snd a) * n a := rfl

/- English proof (translation)
Simplify using `[liftSq_apply]`.
-/
theorem liftSq_inl {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (h : O) : liftSq ρ n hn (TrivSqZeroExt.inl h) = ρ h := by
  simp [liftSq_apply]

/- English proof (translation)
Rewrite using `[liftSq_apply, fst_tszeSec]`. Simplify using `only [snd_tszeSec]`.
-/
theorem liftSq_sec {g : ℕ} {O C : Type} [CommRing O] [Algebra ℂ O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (D : Fin g → Derivation ℂ O O) (h : O) :
    liftSq ρ n hn (tszeSec D h) = ρ h + ∑ a, ρ (D a h) * n a := by
  rw [liftSq_apply, fst_tszeSec]
  simp only [snd_tszeSec]

/- English proof (translation)
Set `ρ : Hol (K.W k) →+* T.C` to `(Hom.φ f₁ : (K.triv k).C →+* T.C)`. Use `letI := (K.jet k).alg`. Use `letI := (K.triv k).alg`. Set `φ : (K.jet k).C →ₐ[Hol F.V] T.C` to `{ liftSq ρ n hn with commutes' := fun f ↦ (liftSq_inl ρ n hn (K.cst k f)).trans ((Hom.φ f₁).commutes f) }`. Establish `hφ : ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), φ x = liftSq ρ n hn x` using `fun _ ↦ rfl`.

Establish `hcomp : (φ : (K.jet k).C →+* T.C).comp (K.jet k).ρ = (Hom.φ f₁ : (K.triv k).C →+* T.C).comp (K.triv k).ρ` using `RingHom.ext fun x ↦ liftSq_inl ρ n hn x`. Set `χ : K.jet k ⟶ T` to `{ φ := φ deg := Hom.deg f₁ le := Hom.le f₁ mem := fun c hc ↦ by`. Establish `hc' : TrivSqZeroExt.fst c = 0` using `hc`. Rewrite using `[hφ, liftSq_apply, hc', map_zero, zero_add]`. Conclude with `T.J.sum_mem fun a _ ↦ T.J.mul_mem_left _ (hJ a)`.

Use `close := by rw [hcomp]; exact Hom.close f₁ }`. Use `⟨χ, rfl, hom_ext (fun c ↦ ?_) (zero_add _), hom_ext (fun c ↦ ?_) ((zero_add _).trans hdeg), fun _ ↦ rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `liftSq ρ n hn (TrivSqZeroExt.inl (sh (K.le_refl k) c)) = _`. Rewrite using `[sh_refl, liftSq_inl]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `liftSq ρ n hn (tszeSec dw c) = _`. Use `Eq.trans ?_ (h c).symm` and prove the remaining obligations. Conclude with `liftSq_sec ρ n hn dw c`.
-/
theorem exists_hom_jet {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C)
    (hdeg : Hom.deg f₁ = Hom.deg f₂) (hJ : ∀ a, n a ∈ T.J) (hn : ∀ a b, n a * n b = 0)
    (h : ∀ x : Hol (K.W k), Hom.φ f₂ x = Hom.φ f₁ x + ∑ a, Hom.φ f₁ (dw a x) * n a) :
    ∃ χ : K.jet k ⟶ T, Hom.deg χ = Hom.deg f₁ ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        Hom.φ χ x = Hom.φ f₁ x.fst + ∑ a, Hom.φ f₁ (x.snd a) * n a := by
  let ρ : Hol (K.W k) →+* T.C := (Hom.φ f₁ : (K.triv k).C →+* T.C)
  letI := (K.jet k).alg
  letI := (K.triv k).alg
  let φ : (K.jet k).C →ₐ[Hol F.V] T.C :=
    { liftSq ρ n hn with
      commutes' := fun f ↦ (liftSq_inl ρ n hn (K.cst k f)).trans ((Hom.φ f₁).commutes f) }
  have hφ : ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), φ x = liftSq ρ n hn x := fun _ ↦ rfl
  have hcomp : (φ : (K.jet k).C →+* T.C).comp (K.jet k).ρ = (Hom.φ f₁ : (K.triv k).C →+* T.C).comp (K.triv k).ρ :=
    RingHom.ext fun x ↦ liftSq_inl ρ n hn x
  let χ : K.jet k ⟶ T :=
    { φ := φ
      deg := Hom.deg f₁
      le := Hom.le f₁
      mem := fun c hc ↦ by
        have hc' : TrivSqZeroExt.fst c = 0 := hc
        rw [hφ, liftSq_apply, hc', map_zero, zero_add]
        exact T.J.sum_mem fun a _ ↦ T.J.mul_mem_left _ (hJ a)
      close := by rw [hcomp]; exact Hom.close f₁ }
  refine ⟨χ, rfl, hom_ext (fun c ↦ ?_) (zero_add _), hom_ext (fun c ↦ ?_) ((zero_add _).trans hdeg), fun _ ↦ rfl⟩
  · change liftSq ρ n hn (TrivSqZeroExt.inl (sh (K.le_refl k) c)) = _
    rw [sh_refl, liftSq_inl]; rfl
  · change liftSq ρ n hn (tszeSec dw c) = _
    refine Eq.trans ?_ (h c).symm
    exact liftSq_sec ρ n hn dw c

end GlobalTheory.SquareLiftLemmas
