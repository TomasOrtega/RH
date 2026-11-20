import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TensIrr

/- English proof (translation)
Set `A` to `Algebra.adjoin ℂ SV`. Set `ev : V → (A →ₗ[ℂ] V)` to `fun y => { toFun := fun a => (a : Module.End ℂ V) y map_add' := fun a b => by simp map_smul' := fun c a => by simp }`. Establish `hev : ∀ y (a : A), ev y a = (a : Module.End ℂ V) y` using `fun _ _ => rfl`. Establish `hsurj : Function.Surjective (ev v₀)`. Rewrite using `[← LinearMap.range_eq_top]`.

Break down `hirr (LinearMap.range (ev v₀)) (fun s hs x hx => by` into its components or cases. Take `⟨a, rfl⟩` from `hx`. Conclude with `⟨⟨s * a, mul_mem (Algebra.subset_adjoin hs) a.2⟩, rfl⟩) with h0 | h0`. It suffices to derive a contradiction. Apply `hv₀` to reduce the goal to its premises.

Establish `h1 : ev v₀ 1 ∈ LinearMap.range (ev v₀)` using `LinearMap.mem_range_self _ _`. Rewrite `h1` using `[h0, Submodule.mem_bot]`. Simplify `h1` using `[hev]`. Conclude with `h0`. Establish `hker : LinearMap.ker (ev v₀) ≤ LinearMap.ker (ev w)` using `fun a ha => by`.

Rewrite `ha`, the goal using `[LinearMap.mem_ker, hev]`. Conclude with `h a a.2 ha`. Set `φ : Module.End ℂ V` to `((LinearMap.ker (ev v₀)).liftQ (ev w) hker).comp (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm.toLinearMap`. Establish `hφ : ∀ a : A, φ ((a : Module.End ℂ V) v₀) = (a : Module.End ℂ V) w`. Introduce `a`.

Establish `h2 : (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm (ev v₀ a) = Submodule.Quotient.mk a`. Rewrite using `[LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]`. Simplify using `only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[← hev v₀, h2, Submodule.liftQ_apply, hev]`. Take `⟨c, hc⟩` from `GlobalTheory.dixmier_commutant_scalar SV V (fun s => s.1) hrank (fun N hN => hirr N (fun a ha x hx => hN ⟨a, ha⟩ x hx)) φ (fun s => by`.

Use extensionality with `y`. Take `⟨a, rfl⟩` from `hsurj y`. Establish `h1 : φ ((s.1 * (a : Module.End ℂ V)) v₀) = (s.1 * (a : Module.End ℂ V)) w` using `hφ ⟨s.1 * a, mul_mem (Algebra.subset_adjoin s.2) a.2⟩`. Simplify using `only [Module.End.mul_apply, hev] at h1 ⊢`. Rewrite using `[h1, hφ a])`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `h3` using `hφ 1`. Simplify using `only [OneMemClass.coe_one, Module.End.one_apply] at h3`. Rewrite using `[← h3, hc]`. Simplify using the standard rewrite rules.
-/
theorem eq_smul_of_ann {V : Type} [AddCommGroup V] [Module ℂ V] (SV : Set (Module.End ℂ V))
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤)
    (v₀ w : V) (hv₀ : v₀ ≠ 0)
    (h : ∀ a ∈ Algebra.adjoin ℂ SV, a v₀ = 0 → a w = 0) : ∃ c : ℂ, w = c • v₀ := by
  let A := Algebra.adjoin ℂ SV
  let ev : V → (A →ₗ[ℂ] V) := fun y =>
    { toFun := fun a => (a : Module.End ℂ V) y
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hev : ∀ y (a : A), ev y a = (a : Module.End ℂ V) y := fun _ _ => rfl
  have hsurj : Function.Surjective (ev v₀) := by
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range (ev v₀)) (fun s hs x hx => by
      obtain ⟨a, rfl⟩ := hx
      exact ⟨⟨s * a, mul_mem (Algebra.subset_adjoin hs) a.2⟩, rfl⟩) with h0 | h0
    · exfalso; apply hv₀
      have h1 : ev v₀ 1 ∈ LinearMap.range (ev v₀) := LinearMap.mem_range_self _ _
      rw [h0, Submodule.mem_bot] at h1
      simpa [hev] using h1
    · exact h0
  have hker : LinearMap.ker (ev v₀) ≤ LinearMap.ker (ev w) := fun a ha => by
    rw [LinearMap.mem_ker, hev] at ha ⊢
    exact h a a.2 ha
  let φ : Module.End ℂ V := ((LinearMap.ker (ev v₀)).liftQ (ev w) hker).comp
    (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm.toLinearMap
  have hφ : ∀ a : A, φ ((a : Module.End ℂ V) v₀) = (a : Module.End ℂ V) w := by
    intro a
    have h2 : (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm (ev v₀ a) =
        Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hev v₀, h2, Submodule.liftQ_apply, hev]
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar SV V (fun s => s.1) hrank
    (fun N hN => hirr N (fun a ha x hx => hN ⟨a, ha⟩ x hx)) φ (fun s => by
      ext y
      obtain ⟨a, rfl⟩ := hsurj y
      have h1 : φ ((s.1 * (a : Module.End ℂ V)) v₀) = (s.1 * (a : Module.End ℂ V)) w :=
        hφ ⟨s.1 * a, mul_mem (Algebra.subset_adjoin s.2) a.2⟩
      simp only [Module.End.mul_apply, hev] at h1 ⊢
      rw [h1, hφ a])
  refine ⟨c, ?_⟩
  have h3 := hφ 1
  simp only [OneMemClass.coe_one, Module.End.one_apply] at h3
  rw [← h3, hc]
  simp

/- English proof (translation)
Introduce `a ha`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem a ha => exact hN a ha`. Consider the case `algebraMap r`. Introduce `x hx`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, LinearMap.rTensor_smul, Module.End.one_eq_id, LinearMap.rTensor_id]`. Simplify using `using N.smul_mem r hx`. Consider the case `add a b _ _ ha hb`. Introduce `x hx`. Rewrite using `[LinearMap.rTensor_add, LinearMap.add_apply]`.

Conclude with `N.add_mem (ha x hx) (hb x hx)`. Consider the case `mul a b _ _ ha hb`. Introduce `x hx`. Rewrite using `[LinearMap.rTensor_mul, Module.End.mul_apply]`. Conclude with `ha _ (hb x hx)`.
-/
theorem rTensor_mem_adjoin {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (SV : Set (Module.End ℂ V)) (N : Submodule ℂ (V ⊗[ℂ] U))
    (hN : ∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) :
    ∀ a ∈ Algebra.adjoin ℂ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact hN a ha
  | algebraMap r =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.rTensor_smul, Module.End.one_eq_id,
      LinearMap.rTensor_id]
    simpa using N.smul_mem r hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.rTensor_add, LinearMap.add_apply]
    exact N.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.rTensor_mul, Module.End.mul_apply]
    exact ha _ (hb x hx)

/- English proof (translation)
Introduce `V U _ _ _ _ SV SU hrank _ hV hU N hNV hNU`. Distinguish the cases in `hN : N = ⊥`. Conclude with `Or.inl hN`. Use `right`. Take `⟨x₁, hx₁N, hx₁⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hN`.

Set `b` to `Module.Free.chooseBasis ℂ U`. Set `e` to `TensorProduct.equivFinsuppOfBasisRight (M := V) b`. Establish `he : ∀ (a : Module.End ℂ V) y j, e (LinearMap.rTensor U a y) j = a (e y j)`. Introduce `a y j`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul m n => simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]`. Consider the case `add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]`. Establish `hex : ∃ n, ∃ y ∈ N, y ≠ 0 ∧ (e y).support.card = n` using `⟨_, x₁, hx₁N, hx₁, rfl⟩`. Take `⟨x, hxN, hx0, hxc⟩` from `Nat.find_spec hex`.

Establish `hmin : ∀ y ∈ N, (e y).support.card < (e x).support.card → y = 0`. Introduce `y hy hlt`. Assume the negation of the conclusion as `hy0`. Conclude with `Nat.find_min hex (hxc ▸ hlt) ⟨y, hy, hy0, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨j₀, hj₀⟩ : (e x).support.Nonempty := by`.

Rewrite using `[Finsupp.support_nonempty_iff]`. Conclude with `(LinearEquiv.map_ne_zero_iff e).mpr hx0`. Use `set v₀ := e x j₀ with hv₀def`. Establish `hv₀ : v₀ ≠ 0` using `Finsupp.mem_support_iff.mp hj₀`. Establish `hA` using `rTensor_mem_adjoin SV N hNV`.

Establish `hcol : ∀ j, ∃ c : ℂ, e x j = c • v₀`. Introduce `j`. Use `eq_smul_of_ann SV hrank hV v₀ (e x j) hv₀ (fun a ha hav => ?_)` and prove the remaining obligations. Establish `hy` using `hmin _ (hA a ha x hxN) (by`. Apply `Finset.card_lt_card` to reduce the goal to its premises.

Rewrite using `[Finset.ssubset_iff_of_subset]`. Use `⟨j₀, hj₀, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.mem_support_iff, not_not, he]`. Conclude with `hav`. Introduce `i hi`.

Rewrite `hi`, the goal using `[Finsupp.mem_support_iff]`. Introduce `h0`. Apply `hi` to reduce the goal to its premises. Rewrite using `[he, h0, map_zero])`. Establish `h5` using `he a x j`.

Rewrite `h5` using `[hy, map_zero, Finsupp.zero_apply]`. Conclude with `h5.symm`. Take `⟨ℓ, hℓ⟩` from `Module.Projective.exists_dual_eq_one ℂ hv₀`. Set `u : U` to `b.repr.symm ((e x).mapRange ℓ (map_zero ℓ))`. Establish `hxu : x = v₀ ⊗ₜ u`.

Apply `e.injective` to reduce the goal to its premises. Use extensionality with `j`. Rewrite using `[TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]`. Simplify using `only [u, LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]`. Take `⟨c, hc⟩` from `hcol j`.

Rewrite using `[hc, map_smul, hℓ, smul_eq_mul, mul_one]`. Establish `hu : u ≠ 0`. Introduce `hu0`. Apply `hx0` to reduce the goal to its premises. Rewrite using `[hxu, hu0, TensorProduct.tmul_zero]`.

Establish `hP : N.comap ((TensorProduct.mk ℂ V U).flip u) = ⊤`. Break down `hV (N.comap ((TensorProduct.mk ℂ V U).flip u)) (fun a ha v hv => by` into its components or cases. Simplify using `only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply] at hv ⊢`. Establish `h6` using `hNV a ha _ hv`. Rewrite using `[LinearMap.rTensor_tmul] at h6) with h0 | h0` and apply the resulting hypothesis.

It suffices to derive a contradiction. Establish `h7 : v₀ ∈ N.comap ((TensorProduct.mk ℂ V U).flip u)`. Simplify using `only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply]`. Rewrite using `[← hxu]`. Conclude with `hxN`.

Rewrite `h7` using `[h0, Submodule.mem_bot]`. Conclude with `hv₀ h7`. Conclude with `h0`. Establish `hQ : ∀ v : V, N.comap (TensorProduct.mk ℂ V U v) = ⊤`. Introduce `v`.

Break down `hU (N.comap (TensorProduct.mk ℂ V U v)) (fun c hc y hy => by` into its components or cases. Simplify using `only [Submodule.mem_comap, TensorProduct.mk_apply] at hy ⊢`. Establish `h6` using `hNU c hc _ hy`. Rewrite using `[LinearMap.lTensor_tmul] at h6) with h0 | h0` and apply the resulting hypothesis. It suffices to derive a contradiction.

Establish `h7 : u ∈ N.comap (TensorProduct.mk ℂ V U v)`. Establish `h8 : v ∈ N.comap ((TensorProduct.mk ℂ V U).flip u)` using `by rw [hP]; trivial`. Simplify using `using h8`. Rewrite `h7` using `[h0, Submodule.mem_bot]`. Conclude with `hu h7`.

Conclude with `h0`. Rewrite using `[eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]`. Introduce and unpack `_ ⟨m, n, rfl⟩`. Establish `h9 : n ∈ N.comap (TensorProduct.mk ℂ V U m)` using `by rw [hQ m]; trivial`. Simplify using `using h9`.
-/
theorem tensor_irreducible : ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (SV : Set (Module.End ℂ V))
    (SU : Set (Module.End ℂ U)), Module.rank ℂ V ≤ Cardinal.aleph0 → Nontrivial V →
    (∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤) →
    (∀ N : Submodule ℂ U, (∀ b ∈ SU, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ N : Submodule ℂ (V ⊗[ℂ] U), (∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) →
      (∀ b ∈ SU, ∀ x ∈ N, LinearMap.lTensor V b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro V U _ _ _ _ SV SU hrank _ hV hU N hNV hNU
  classical
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨x₁, hx₁N, hx₁⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  let b := Module.Free.chooseBasis ℂ U
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have he : ∀ (a : Module.End ℂ V) y j, e (LinearMap.rTensor U a y) j = a (e y j) := by
    intro a y j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  have hex : ∃ n, ∃ y ∈ N, y ≠ 0 ∧ (e y).support.card = n := ⟨_, x₁, hx₁N, hx₁, rfl⟩
  obtain ⟨x, hxN, hx0, hxc⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ N, (e y).support.card < (e x).support.card → y = 0 := by
    intro y hy hlt
    by_contra hy0
    exact Nat.find_min hex (hxc ▸ hlt) ⟨y, hy, hy0, rfl⟩
  obtain ⟨j₀, hj₀⟩ : (e x).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact (LinearEquiv.map_ne_zero_iff e).mpr hx0
  set v₀ := e x j₀ with hv₀def
  have hv₀ : v₀ ≠ 0 := Finsupp.mem_support_iff.mp hj₀
  have hA := rTensor_mem_adjoin SV N hNV
  have hcol : ∀ j, ∃ c : ℂ, e x j = c • v₀ := by
    intro j
    refine eq_smul_of_ann SV hrank hV v₀ (e x j) hv₀ (fun a ha hav => ?_)
    have hy := hmin _ (hA a ha x hxN) (by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨j₀, hj₀, ?_⟩
        rw [Finsupp.mem_support_iff, not_not, he]
        exact hav
      · intro i hi
        rw [Finsupp.mem_support_iff] at hi ⊢
        intro h0
        apply hi
        rw [he, h0, map_zero])
    have h5 := he a x j
    rw [hy, map_zero, Finsupp.zero_apply] at h5
    exact h5.symm
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one ℂ hv₀
  let u : U := b.repr.symm ((e x).mapRange ℓ (map_zero ℓ))
  have hxu : x = v₀ ⊗ₜ u := by
    apply e.injective
    ext j
    rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    simp only [u, LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]
    obtain ⟨c, hc⟩ := hcol j
    rw [hc, map_smul, hℓ, smul_eq_mul, mul_one]
  have hu : u ≠ 0 := by
    intro hu0
    apply hx0
    rw [hxu, hu0, TensorProduct.tmul_zero]
  have hP : N.comap ((TensorProduct.mk ℂ V U).flip u) = ⊤ := by
    rcases hV (N.comap ((TensorProduct.mk ℂ V U).flip u)) (fun a ha v hv => by
      simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply] at hv ⊢
      have h6 := hNV a ha _ hv
      rwa [LinearMap.rTensor_tmul] at h6) with h0 | h0
    · exfalso
      have h7 : v₀ ∈ N.comap ((TensorProduct.mk ℂ V U).flip u) := by
        simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply]
        rw [← hxu]; exact hxN
      rw [h0, Submodule.mem_bot] at h7
      exact hv₀ h7
    · exact h0
  have hQ : ∀ v : V, N.comap (TensorProduct.mk ℂ V U v) = ⊤ := by
    intro v
    rcases hU (N.comap (TensorProduct.mk ℂ V U v)) (fun c hc y hy => by
      simp only [Submodule.mem_comap, TensorProduct.mk_apply] at hy ⊢
      have h6 := hNU c hc _ hy
      rwa [LinearMap.lTensor_tmul] at h6) with h0 | h0
    · exfalso
      have h7 : u ∈ N.comap (TensorProduct.mk ℂ V U v) := by
        have h8 : v ∈ N.comap ((TensorProduct.mk ℂ V U).flip u) := by rw [hP]; trivial
        simpa using h8
      rw [h0, Submodule.mem_bot] at h7
      exact hu h7
    · exact h0
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨m, n, rfl⟩
  have h9 : n ∈ N.comap (TensorProduct.mk ℂ V U m) := by rw [hQ m]; trivial
  simpa using h9

end GlobalTheory.TensIrr
