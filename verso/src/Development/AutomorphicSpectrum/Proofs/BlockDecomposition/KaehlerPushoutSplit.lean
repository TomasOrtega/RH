import Mathlib
open TensorProduct

namespace GlobalTheory.CompanionTheory.KaehlerPushout

open KaehlerDifferential

/- English proof (translation)
Set `e` to `KaehlerDifferential.tensorKaehlerEquiv K B A R`. Use `⟨e.symm.toLinearMap ∘ₗ KaehlerDifferential.map K B R R, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Establish `key : KaehlerDifferential.map K B R R (KaehlerDifferential.mapBaseChange K A R x) = e x`. Proceed by induction on `x with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul s w`. Establish `hw : w ∈ Submodule.span A (Set.range (KaehlerDifferential.D K A))`. Rewrite using `[KaehlerDifferential.span_range_derivation]`.

Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hw using Submodule.span_induction generalizing s with`. Consider the case `mem w hw`. Take `⟨a, rfl⟩` from `hw`. Simplify using `[e, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]`.

Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => simp only [tmul_add, map_add, hu, hv]`. Consider the case `smul a u _ hu`. Rewrite using `[← TensorProduct.smul_tmul]`. Conclude with `hu _`.

Simplify using `[key]`. Introduce `y`. Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, add_zero]`.

Consider the case `tmul s w`. Establish `hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D K B))`. Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hw using Submodule.span_induction generalizing s with`.

Consider the case `mem w hw`. Take `⟨b, rfl⟩` from `hw`. Simplify using `[KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => simp only [tmul_add, map_add, hu, hv, add_zero]`.

Consider the case `smul b u _ hu`. Rewrite using `[← TensorProduct.smul_tmul]`. Conclude with `hu _`.
-/
theorem exists_retraction (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K B A R] :
    ∃ r : Ω[R⁄K] →ₗ[R] R ⊗[A] Ω[A⁄K],
      (∀ x, r (KaehlerDifferential.mapBaseChange K A R x) = x) ∧
      (∀ y, r (KaehlerDifferential.mapBaseChange K B R y) = 0) := by
  let e := KaehlerDifferential.tensorKaehlerEquiv K B A R
  refine ⟨e.symm.toLinearMap ∘ₗ KaehlerDifferential.map K B R R, ?_, ?_⟩
  · intro x
    have key : KaehlerDifferential.map K B R R (KaehlerDifferential.mapBaseChange K A R x) = e x := by
      induction x with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul s w =>
        have hw : w ∈ Submodule.span A (Set.range (KaehlerDifferential.D K A)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hw using Submodule.span_induction generalizing s with
        | mem w hw =>
          obtain ⟨a, rfl⟩ := hw
          simp [e, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
        | zero => simp
        | add u v _ _ hu hv => simp only [tmul_add, map_add, hu, hv]
        | smul a u _ hu =>
          rw [← TensorProduct.smul_tmul]
          exact hu _
    simp [key]
  · intro y
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    | tmul s w =>
      have hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D K B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hw using Submodule.span_induction generalizing s with
      | mem w hw =>
        obtain ⟨b, rfl⟩ := hw
        simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
      | zero => simp
      | add u v _ _ hu hv => simp only [tmul_add, map_add, hu, hv, add_zero]
      | smul b u _ hu =>
        rw [← TensorProduct.smul_tmul]
        exact hu _

/- English proof (translation)
Use `set S := LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔ LinearMap.range (KaehlerDifferential.mapBaseChange K B R) with hS`. Establish `hA : ∀ a : A, KaehlerDifferential.D K R (algebraMap A R a) ∈ S` using `fun a => Submodule.mem_sup_left ⟨1 ⊗ₜ KaehlerDifferential.D K A a, by`. Simplify using `[KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩`. Establish `hB : ∀ b : B, KaehlerDifferential.D K R (algebraMap B R b) ∈ S` using `fun b => Submodule.mem_sup_right ⟨1 ⊗ₜ KaehlerDifferential.D K B b, by`. Simplify using `[KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩`.

Establish `hD : ∀ r : R, KaehlerDifferential.D K R r ∈ S`. Introduce `r`. Proceed by induction on `r using h.out.inductionOn with`. Consider the case `zero => simp`. Consider the case `tmul b => exact hB b`.

Consider the case `smul a y hy`. Rewrite using `[Algebra.smul_def, Derivation.leibniz]`. Conclude with `S.add_mem (S.smul_mem _ hy) (S.smul_mem _ (hA a))`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `S.add_mem hx hy`.

Rewrite using `[eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]`. Introduce and unpack `_ ⟨r, rfl⟩`. Conclude with `hD r`.
-/
theorem range_sup_range (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [h : Algebra.IsPushout K A B R] :
    LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔
      LinearMap.range (KaehlerDifferential.mapBaseChange K B R) = ⊤ := by
  set S := LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔
      LinearMap.range (KaehlerDifferential.mapBaseChange K B R) with hS
  have hA : ∀ a : A, KaehlerDifferential.D K R (algebraMap A R a) ∈ S := fun a =>
    Submodule.mem_sup_left ⟨1 ⊗ₜ KaehlerDifferential.D K A a, by
      simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩
  have hB : ∀ b : B, KaehlerDifferential.D K R (algebraMap B R b) ∈ S := fun b =>
    Submodule.mem_sup_right ⟨1 ⊗ₜ KaehlerDifferential.D K B b, by
      simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩
  have hD : ∀ r : R, KaehlerDifferential.D K R r ∈ S := by
    intro r
    induction r using h.out.inductionOn with
    | zero => simp
    | tmul b => exact hB b
    | smul a y hy =>
      rw [Algebra.smul_def, Derivation.leibniz]
      exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ (hA a))
    | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  exact hD r

/- English proof (translation)
Introduce `K A B R _ _ _ _ _ _ _ _ _ _ _ h`. Use `haveI hs : Algebra.IsPushout K B A R := h.symm`. Take `⟨r, hr₁, hr₂⟩` from `exists_retraction K A B R`. Take `⟨π, hπ₁, hπ₂⟩` from `exists_retraction K B A R`. Conclude with `⟨r, π, hr₁, hr₂, hπ₂, hπ₁, range_sup_range K A B R⟩`.
-/
theorem kaehler_pushout_split : ∀ (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R] [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R] [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K A B R], ∃ (r : Ω[R⁄K] →ₗ[R] R ⊗[A] Ω[A⁄K]) (π : Ω[R⁄K] →ₗ[R] R ⊗[B] Ω[B⁄K]), (∀ x, r (KaehlerDifferential.mapBaseChange K A R x) = x) ∧ (∀ y, r (KaehlerDifferential.mapBaseChange K B R y) = 0) ∧ (∀ x, π (KaehlerDifferential.mapBaseChange K A R x) = 0) ∧ (∀ y, π (KaehlerDifferential.mapBaseChange K B R y) = y) ∧ LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔ LinearMap.range (KaehlerDifferential.mapBaseChange K B R) = ⊤ := by
  intro K A B R _ _ _ _ _ _ _ _ _ _ _ h
  haveI hs : Algebra.IsPushout K B A R := h.symm
  obtain ⟨r, hr₁, hr₂⟩ := exists_retraction K A B R
  obtain ⟨π, hπ₁, hπ₂⟩ := exists_retraction K B A R
  exact ⟨r, π, hr₁, hr₂, hπ₂, hπ₁, range_sup_range K A B R⟩

end GlobalTheory.CompanionTheory.KaehlerPushout
