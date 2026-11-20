import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NLev

section Calc

variable (I : AutInst)

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hA_add_right (y z z' : VA I) : hA I y (z + z') = hA I y z + hA I y z' := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hA_add_left (y y' z : VA I) : hA I (y + y') z = hA I y z + hA I y' z := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem hA_sub_right (y z z' : VA I) : hA I y (z - z') = hA I y z - hA I y z' := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]`.
-/
theorem hA_sub_left (y y' z : VA I) : hA I (y - y') z = hA I y z - hA I y' z := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[hA, Formalism.UG.hform]`.
-/
theorem hA_zero_left (z : VA I) : hA I 0 z = 0 := by
  simp [hA, Formalism.UG.hform]

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hA_smul_right (y z : VA I) (r : I.E ⊗[I.F] Af I.F) : hA I y (r • z) = r * hA I y z := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hA_smul_left (y z : VA I) (r : I.E ⊗[I.F] Af I.F) :
    hA I (r • y) z = Formalism.UG.sigR I.cm.sig (Af I.F) r * hA I y z := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Rewrite using `[hA_smul_left, map_natCast]`.
-/
theorem hA_nat_left (y z : VA I) (c : ℕ) :
    hA I ((c : I.E ⊗[I.F] Af I.F) • y) z = (c : I.E ⊗[I.F] Af I.F) * hA I y z := by
  rw [hA_smul_left, map_natCast]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hA, Formalism.UG.hform]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hA_add_right, ih]`.
-/
theorem hA_sum_right {ι : Type} (s : Finset ι) (y : VA I) (v : ι → VA I) :
    hA I y (∑ i ∈ s, v i) = ∑ i ∈ s, hA I y (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hA, Formalism.UG.hform]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hA_add_right, ih]

/- English proof (translation)
Use `show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (e ⊗ₜ[I.F] (1 : Af I.F)) = star e ⊗ₜ[I.F] (1 : Af I.F)`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression.
-/
theorem sigR_inclE (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star e) := by
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (e ⊗ₜ[I.F] (1 : Af I.F)) =
    star e ⊗ₜ[I.F] (1 : Af I.F)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

/- English proof (translation)
Use `show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) ((1 : I.E) ⊗ₜ[I.F] a) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression.
-/
theorem sigR_one_tmul (a : Af I.F) :
    Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] a) = (1 : I.E) ⊗ₜ[I.F] a := by
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) ((1 : I.E) ⊗ₜ[I.F] a) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

/- English proof (translation)
Unfold `hA Formalism.UG.hform incl`. Simplify using `only [Matrix.map_apply, sigR_inclE, map_sum, map_mul, starRingEnd_apply]`.
-/
theorem hA_incl (v w : Fin I.n → I.E) :
    hA I (incl I v) (incl I w) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J v w) := by
  unfold hA Formalism.UG.hform incl
  simp only [Matrix.map_apply, sigR_inclE, map_sum, map_mul, starRingEnd_apply]

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)`.
-/
theorem inclE_int {e : I.E} (he : e ∈ (algebraMap (𝓞 I.E) I.E).range) :
    Formalism.UG.inclE (F := I.F) (Af I.F) e ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)

/- English proof (translation)
Assemble the required witnesses or components as `⟨RingOfIntegers.mapRingHom (starRingEnd I.E) a, RingOfIntegers.mapRingHom_apply _ _⟩`.
-/
theorem star_int (a : 𝓞 I.E) : star (algebraMap (𝓞 I.E) I.E a) ∈ (algebraMap (𝓞 I.E) I.E).range :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd I.E) a, RingOfIntegers.mapRingHom_apply _ _⟩

/- English proof (translation)
Establish `key : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F))` using `by show Subring.closure _ ≤ _`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)`. Use `show Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a)) ∈ IntAf I.F I.E`. Rewrite using `[sigR_inclE]`.

Conclude with `inclE_int I (star_int I a)`. Use `show Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] y) ∈ IntAf I.F I.E`. Rewrite using `[sigR_one_tmul]`. Conclude with `Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)`. Conclude with `key hr`.
-/
theorem sigR_int {r : I.E ⊗[I.F] Af I.F} (hr : r ∈ IntAf I.F I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) r ∈ IntAf I.F I.E := by
  have key : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F)) := by
    show Subring.closure _ ≤ _
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a)) ∈
        IntAf I.F I.E
      rw [sigR_inclE]
      exact inclE_int I (star_int I a)
    · show Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] y) ∈ IntAf I.F I.E
      rw [sigR_one_tmul]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key hr

/- English proof (translation)
The claim follows from `natCast_mem _ c`.
-/
theorem natCast_int (c : ℕ) : (c : I.E ⊗[I.F] Af I.F) ∈ IntAf I.F I.E := natCast_mem _ c

/- English proof (translation)
The claim follows from `P.smul_mem ⟨t, ht⟩ hv`.
-/
theorem sm {P : Submodule (IntAf I.F I.E) (VA I)} {t : I.E ⊗[I.F] Af I.F} (ht : t ∈ IntAf I.F I.E)
    {v : VA I} (hv : v ∈ P) : t • v ∈ P :=
  P.smul_mem ⟨t, ht⟩ hv

/- English proof (translation)
Use `show Submodule.span _ _ ≤ p`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨⟨l, hl⟩, rfl⟩`. Conclude with `h l hl`.
-/
theorem Lf_le (p : Submodule (IntAf I.F I.E) (VA I)) (h : ∀ l ∈ I.L, incl I l ∈ p) : I.Lf ≤ p := by
  show Submodule.span _ _ ≤ p
  rw [Submodule.span_le]
  rintro _ ⟨⟨l, hl⟩, rfl⟩
  exact h l hl

/- English proof (translation)
Establish `gen : ∀ l ∈ I.L, ∀ z ∈ I.Lf, hA I (incl I l) z ∈ IntAf I.F I.E`. Introduce `l hl`. Use `Lf_le I { carrier := {z | hA I (incl I l) z ∈ IntAf I.F I.E} add_mem' := fun {a b} ha hb => by show hA I (incl I l) (a + b) ∈ IntAf I.F I.E` and prove the remaining obligations. Rewrite using `[hA_add_right]`. Conclude with `add_mem ha hb`.

Use the proof step `zero_mem' := by show hA I (incl I l) 0 ∈ IntAf I.F I.E`. Simplify using `[hA, Formalism.UG.hform]`. Use the proof step `smul_mem' := fun r z hz => by show hA I (incl I l) ((r : I.E ⊗[I.F] Af I.F) • z) ∈ IntAf I.F I.E`. Rewrite using `[hA_smul_right]`. Conclude with `mul_mem r.2 hz } ?_`.

Introduce `l' hl'`. Use `show hA I (incl I l) (incl I l') ∈ IntAf I.F I.E`. Rewrite using `[hA_incl]`. Conclude with `inclE_int I (((I.L_dual l').1 hl') l hl)`. Introduce `y hy z hz`.

Use `Lf_le I { carrier := {y | hA I y z ∈ IntAf I.F I.E} add_mem' := fun {a b} ha hb => by show hA I (a + b) z ∈ IntAf I.F I.E` and prove the remaining obligations. Rewrite using `[hA_add_left]`. Conclude with `add_mem ha hb`. Use the proof step `zero_mem' := by show hA I 0 z ∈ IntAf I.F I.E`. Rewrite using `[hA_zero_left]`.

Conclude with `zero_mem _`. Use the proof step `smul_mem' := fun r y hy => by show hA I ((r : I.E ⊗[I.F] Af I.F) • y) z ∈ IntAf I.F I.E`. Rewrite using `[hA_smul_left]`. Conclude with `mul_mem (sigR_int I r.2) hy } (fun l hl => gen l hl z hz) hy`.
-/
theorem hA_int : ∀ y ∈ I.Lf, ∀ z ∈ I.Lf, hA I y z ∈ IntAf I.F I.E := by
  have gen : ∀ l ∈ I.L, ∀ z ∈ I.Lf, hA I (incl I l) z ∈ IntAf I.F I.E := by
    intro l hl
    refine Lf_le I
      { carrier := {z | hA I (incl I l) z ∈ IntAf I.F I.E}
        add_mem' := fun {a b} ha hb => by
          show hA I (incl I l) (a + b) ∈ IntAf I.F I.E
          rw [hA_add_right]; exact add_mem ha hb
        zero_mem' := by
          show hA I (incl I l) 0 ∈ IntAf I.F I.E
          simp [hA, Formalism.UG.hform]
        smul_mem' := fun r z hz => by
          show hA I (incl I l) ((r : I.E ⊗[I.F] Af I.F) • z) ∈ IntAf I.F I.E
          rw [hA_smul_right]; exact mul_mem r.2 hz } ?_
    intro l' hl'
    show hA I (incl I l) (incl I l') ∈ IntAf I.F I.E
    rw [hA_incl]
    exact inclE_int I (((I.L_dual l').1 hl') l hl)
  intro y hy z hz
  refine Lf_le I
    { carrier := {y | hA I y z ∈ IntAf I.F I.E}
      add_mem' := fun {a b} ha hb => by
        show hA I (a + b) z ∈ IntAf I.F I.E
        rw [hA_add_left]; exact add_mem ha hb
      zero_mem' := by
        show hA I 0 z ∈ IntAf I.F I.E
        rw [hA_zero_left]; exact zero_mem _
      smul_mem' := fun r y hy => by
        show hA I ((r : I.E ⊗[I.F] Af I.F) • y) z ∈ IntAf I.F I.E
        rw [hA_smul_left]; exact mul_mem (sigR_int I r.2) hy } (fun l hl => gen l hl z hz) hy

/- English proof (translation)
Establish `hs : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat s) * (I.J.map (Formalism.UG.inclE (F` using `I.F) (Af I.F))) * I.fmat s = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := s.2`. Unfold `hA`. Rewrite using `[Formalism.UG.P.hform_mulVec, hs]`.
-/
theorem hA_fmat (s : I.Gf) (x y : VA I) : hA I (I.fmat s *ᵥ x) (I.fmat s *ᵥ y) = hA I x y := by
  have hs : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat s) *
      (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) * I.fmat s =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := s.2
  unfold hA
  rw [Formalism.UG.P.hform_mulVec, hs]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨x, hx, rfl⟩`.
-/
theorem smul_mem_mL (m : ℕ) {x : VA I} (hx : x ∈ I.Lf) : (m : I.E ⊗[I.F] Af I.F) • x ∈ mL I m :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/- English proof (translation)
Use `show Submodule.span _ _ ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `sm I (natCast_int I m) hx`.
-/
theorem mL_le_Lf (m : ℕ) : mL I m ≤ I.Lf := by
  show Submodule.span _ _ ≤ _
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact sm I (natCast_int I m) hx

/- English proof (translation)
Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Rewrite using `[Matrix.mulVec_smul]`.

Conclude with `smul_mem_mL I m (hM y hy)`. Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul r x _ hx => show M *ᵥ ((r : I.E ⊗[I.F] Af I.F) • x) ∈ _`. Rewrite using `[Matrix.mulVec_smul]`. Conclude with `sm I r.2 hx`.
-/
theorem mulVec_mL (m : ℕ) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hM : ∀ v ∈ I.Lf, M *ᵥ v ∈ I.Lf) : ∀ v ∈ mL I m, M *ᵥ v ∈ mL I m := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Matrix.mulVec_smul]
    exact smul_mem_mL I m (hM y hy)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul r x _ hx =>
    show M *ᵥ ((r : I.E ⊗[I.F] Af I.F) • x) ∈ _
    rw [Matrix.mulVec_smul]
    exact sm I r.2 hx

/- English proof (translation)
Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Introduce `w hw`.

Conclude with `⟨hA I y w, hA_int I y hy w hw, hA_nat_left I y w m⟩`. Consider the case `zero => intro w _; exact ⟨0, zero_mem _, by rw [hA_zero_left, mul_zero]⟩`. Consider the case `add x y _ _ hx hy`. Introduce `w hw`. Take `⟨t, ht, he⟩` from `hx w hw`.

Take `⟨t', ht', he'⟩` from `hy w hw`. Conclude with `⟨t + t', add_mem ht ht', by rw [hA_add_left, he, he', mul_add]⟩`. Consider the case `smul r x _ hx`. Introduce `w hw`. Take `⟨t, ht, he⟩` from `hx w hw`.

Use `⟨Formalism.UG.sigR I.cm.sig (Af I.F) r * t, mul_mem (sigR_int I r.2) ht, ?_⟩` and prove the remaining obligations. Use `show hA I ((r : I.E ⊗[I.F] Af I.F) • x) w = _`. Rewrite using `[hA_smul_left, he]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_mL_left (m : ℕ) : ∀ v ∈ mL I m, ∀ w ∈ I.Lf, ZMod' I m (hA I v w) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    intro w hw
    exact ⟨hA I y w, hA_int I y hy w hw, hA_nat_left I y w m⟩
  | zero => intro w _; exact ⟨0, zero_mem _, by rw [hA_zero_left, mul_zero]⟩
  | add x y _ _ hx hy =>
    intro w hw
    obtain ⟨t, ht, he⟩ := hx w hw
    obtain ⟨t', ht', he'⟩ := hy w hw
    exact ⟨t + t', add_mem ht ht', by rw [hA_add_left, he, he', mul_add]⟩
  | smul r x _ hx =>
    intro w hw
    obtain ⟨t, ht, he⟩ := hx w hw
    refine ⟨Formalism.UG.sigR I.cm.sig (Af I.F) r * t, mul_mem (sigR_int I r.2) ht, ?_⟩
    show hA I ((r : I.E ⊗[I.F] Af I.F) • x) w = _
    rw [hA_smul_left, he]; ring

/- English proof (translation)
Take `⟨a, b, hab⟩ : IsCoprime (c : ℤ) (m : ℤ)` from `Nat.isCoprime_iff_coprime.2 hc`. Establish `h1 : (((a * c + b * m : ℤ)) : I.E ⊗[I.F] Af I.F) = 1` using `by rw [hab]; simp`. Establish `hv' : v = a • ((c : I.E ⊗[I.F] Af I.F) • v) + b • ((m : I.E ⊗[I.F] Af I.F) • v)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Int.cast_smul_eq_zsmul (I.E ⊗[I.F] Af I.F) a, ← Int.cast_smul_eq_zsmul (I.E ⊗[I.F] Af I.F) b, smul_smul, smul_smul, ← add_smul]`.

Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[hv']`. Conclude with `add_mem (zsmul_mem hcv a) (zsmul_mem (hmP (smul_mem_mL I m hv)) b)`.
-/
theorem bezout {P : Submodule (IntAf I.F I.E) (VA I)} {m c : ℕ} (hc : Nat.Coprime c m) (hmP : mL I m ≤ P)
    {v : VA I} (hv : v ∈ I.Lf) (hcv : (c : I.E ⊗[I.F] Af I.F) • v ∈ P) : v ∈ P := by
  obtain ⟨a, b, hab⟩ : IsCoprime (c : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  have h1 : (((a * c + b * m : ℤ)) : I.E ⊗[I.F] Af I.F) = 1 := by rw [hab]; simp
  have hv' : v = a • ((c : I.E ⊗[I.F] Af I.F) • v) + b • ((m : I.E ⊗[I.F] Af I.F) • v) := by
    calc v = (((a * c + b * m : ℤ)) : I.E ⊗[I.F] Af I.F) • v := by rw [h1, one_smul]
      _ = _ := by
        rw [← Int.cast_smul_eq_zsmul (I.E ⊗[I.F] Af I.F) a, ← Int.cast_smul_eq_zsmul (I.E ⊗[I.F] Af I.F) b,
          smul_smul, smul_smul, ← add_smul]
        push_cast; ring_nf
  rw [hv']
  exact add_mem (zsmul_mem hcv a) (zsmul_mem (hmP (smul_mem_mL I m hv)) b)

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Rewrite using `[Nat.cast_mul, mul_comm, mul_smul]`. Conclude with `sm I (natCast_int I k) hv`.
-/
theorem dvd_smul {P : Submodule (IntAf I.F I.E) (VA I)} {c d : ℕ} (h : c ∣ d) {v : VA I}
    (hv : (c : I.E ⊗[I.F] Af I.F) • v ∈ P) : (d : I.E ⊗[I.F] Af I.F) • v ∈ P := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm, mul_smul]
  exact sm I (natCast_int I k) hv

/- English proof (translation)
Use `bezout I (hk.mul hc) hmP hv ?_` and prove the remaining obligations. Rewrite using `[hvr, smul_add, Nat.cast_mul]`. Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `sm I (natCast_int I c) hw`.

Rewrite using `[mul_smul]`. Conclude with `hmP (sm I (natCast_int I k) hr)`.
-/
theorem close {P : Submodule (IntAf I.F I.E) (VA I)} {m : ℕ} (hmP : mL I m ≤ P) {v w r : VA I}
    (hv : v ∈ I.Lf) (hvr : v = w + r) {c k : ℕ} (hc : Nat.Coprime c m) (hk : Nat.Coprime k m)
    (hw : (k : I.E ⊗[I.F] Af I.F) • w ∈ P) (hr : (c : I.E ⊗[I.F] Af I.F) • r ∈ mL I m) : v ∈ P := by
  refine bezout I (hk.mul hc) hmP hv ?_
  rw [hvr, smul_add, Nat.cast_mul]
  refine add_mem ?_ ?_
  · rw [mul_comm, mul_smul]; exact sm I (natCast_int I c) hw
  · rw [mul_smul]; exact hmP (sm I (natCast_int I k) hr)

end Calc

end MassDataMassesW.NLev
