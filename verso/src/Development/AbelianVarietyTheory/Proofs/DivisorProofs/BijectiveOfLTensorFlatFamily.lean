import Mathlib
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hM`. Rewrite `hM` using `[not_subsingleton_iff_nontrivial]`. Take `⟨x, hx⟩` from `exists_ne (0 : M)`. Use `set g : R →ₗ[R] M := LinearMap.toSpanSingleton R M x with hg`. Use `set I : Ideal R := LinearMap.ker g with hIdef`.

Establish `hI : I ≠ ⊤`. Introduce `hT`. Establish `h1 : (1 : R) ∈ I` using `hT ▸ Submodule.mem_top`. Rewrite `h1` using `[hIdef, LinearMap.mem_ker, hg, LinearMap.toSpanSingleton_apply, one_smul]`. Conclude with `hx h1`.

Take `⟨m, hm, hIm⟩` from `I.exists_le_maximal hI`. Take `⟨i, hi⟩` from `hmax m hm`. Set `e : (R ⧸ I) →ₗ[R] M` to `(LinearMap.ker g).liftQ g le_rfl`. Establish `he : Function.Injective e`. Rewrite using `[← LinearMap.ker_eq_bot]`.

Conclude with `Submodule.ker_liftQ_eq_bot _ _ _ le_rfl`. Establish `hinj : Function.Injective (e.lTensor (B i))` using `Module.Flat.lTensor_preserves_injective_linearMap e he`. Use `haveI := h i`. Use `haveI : Subsingleton (B i ⊗[R] (R ⧸ I)) := hinj.subsingleton`. Use `haveI : Subsingleton ((R ⧸ I) ⊗[R] B i) := (TensorProduct.comm R (R ⧸ I) (B i)).toEquiv.injective.subsingleton`.

Use `haveI : Subsingleton (B i ⧸ (I • (⊤ : Submodule R (B i)))) := (TensorProduct.quotTensorEquivQuotSMul (B i) I).symm.toEquiv.injective.subsingleton`. Establish `htop : I • (⊤ : Submodule R (B i)) = ⊤` using `Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩`. Rewrite `htop` using `[Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff]`. Conclude with `hi (top_le_iff.mp (htop ▸ Ideal.map_mono hIm))`.
-/
theorem subsingleton_of_lTensor_flat_family (R : Type) [CommRing R] (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)] (hflat : ∀ i, Module.Flat R (B i))
    (hmax : ∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤)
    (M : Type) [AddCommGroup M] [Module R M] (h : ∀ i, Subsingleton (B i ⊗[R] M)) :
    Subsingleton M := by
  by_contra hM
  rw [not_subsingleton_iff_nontrivial] at hM
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  set g : R →ₗ[R] M := LinearMap.toSpanSingleton R M x with hg
  set I : Ideal R := LinearMap.ker g with hIdef
  have hI : I ≠ ⊤ := by
    intro hT
    have h1 : (1 : R) ∈ I := hT ▸ Submodule.mem_top
    rw [hIdef, LinearMap.mem_ker, hg, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hx h1
  obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
  obtain ⟨i, hi⟩ := hmax m hm
  let e : (R ⧸ I) →ₗ[R] M := (LinearMap.ker g).liftQ g le_rfl
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hinj : Function.Injective (e.lTensor (B i)) :=
    Module.Flat.lTensor_preserves_injective_linearMap e he
  haveI := h i
  haveI : Subsingleton (B i ⊗[R] (R ⧸ I)) := hinj.subsingleton
  haveI : Subsingleton ((R ⧸ I) ⊗[R] B i) := (TensorProduct.comm R (R ⧸ I) (B i)).toEquiv.injective.subsingleton
  haveI : Subsingleton (B i ⧸ (I • (⊤ : Submodule R (B i)))) :=
    (TensorProduct.quotTensorEquivQuotSMul (B i) I).symm.toEquiv.injective.subsingleton
  have htop : I • (⊤ : Submodule R (B i)) = ⊤ :=
    Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at htop
  exact hi (top_le_iff.mp (htop ▸ Ideal.map_mono hIm))

/- English proof (translation)
Introduce `R _ N N' _ _ _ _ f J B _ _ hflat hmax hbij`. Prove the components needed by the constructor for the conclusion. Use `set K := LinearMap.ker f`. Establish `hK : ∀ i, Subsingleton (B i ⊗[R] K)`. Introduce `i`.

Establish `hinjK : Function.Injective (K.subtype.lTensor (B i))` using `Module.Flat.lTensor_preserves_injective_linearMap K.subtype K.injective_subtype`. Establish `hz : (f.lTensor (B i)).comp (K.subtype.lTensor (B i)) = 0`. Rewrite using `[← LinearMap.lTensor_comp]`. Establish `: f ∘ₗ K.subtype = 0`. Use extensionality with `x`.

Conclude with `LinearMap.mem_ker.mp x.2`. Rewrite using `[this, LinearMap.lTensor_zero]`. Use `⟨fun a b => hinjK ((hbij i).1 ?_)⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.comp_apply, hz]`. Both sides reduce to the same expression.

Use `subsingleton_of_lTensor_flat_family R J B hflat hmax K hK` as an intermediate fact. Rewrite using `[← LinearMap.ker_eq_bot]`. Conclude with `Submodule.eq_bot_of_subsingleton`. Use `set q := (LinearMap.range f).mkQ`. Establish `hQ : ∀ i, Subsingleton (B i ⊗[R] (N' ⧸ LinearMap.range f))`.

Introduce `i`. Establish `hsurj : Function.Surjective (q.lTensor (B i))` using `LinearMap.lTensor_surjective (B i) (Submodule.mkQ_surjective _)`. Establish `hz : (q.lTensor (B i)).comp (f.lTensor (B i)) = 0`. Rewrite using `[← LinearMap.lTensor_comp]`. Establish `: q ∘ₗ f = 0`.

Use extensionality with `x`. Simplify using `[q]`. Rewrite using `[this, LinearMap.lTensor_zero]`. Use `subsingleton_of_forall_eq 0 fun y => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `hsurj y`.

Take `⟨w, rfl⟩` from `(hbij i).2 z`. Rewrite using `[← LinearMap.comp_apply, hz]`. Both sides reduce to the same expression. Use `subsingleton_of_lTensor_flat_family R J B hflat hmax _ hQ` as an intermediate fact. Establish `htop : LinearMap.range f = ⊤` using `Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩`.

Conclude with `LinearMap.range_eq_top.mp htop`.
-/
theorem bijective_of_lTensor_flat_family : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) →
    (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) →
    (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by
  intro R _ N N' _ _ _ _ f J B _ _ hflat hmax hbij
  constructor
  · set K := LinearMap.ker f
    have hK : ∀ i, Subsingleton (B i ⊗[R] K) := by
      intro i
      have hinjK : Function.Injective (K.subtype.lTensor (B i)) :=
        Module.Flat.lTensor_preserves_injective_linearMap K.subtype K.injective_subtype
      have hz : (f.lTensor (B i)).comp (K.subtype.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : f ∘ₗ K.subtype = 0 := by
          ext x
          exact LinearMap.mem_ker.mp x.2
        rw [this, LinearMap.lTensor_zero]
      refine ⟨fun a b => hinjK ((hbij i).1 ?_)⟩
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax K hK
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.eq_bot_of_subsingleton
  · set q := (LinearMap.range f).mkQ
    have hQ : ∀ i, Subsingleton (B i ⊗[R] (N' ⧸ LinearMap.range f)) := by
      intro i
      have hsurj : Function.Surjective (q.lTensor (B i)) :=
        LinearMap.lTensor_surjective (B i) (Submodule.mkQ_surjective _)
      have hz : (q.lTensor (B i)).comp (f.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : q ∘ₗ f = 0 := by
          ext x
          simp [q]
        rw [this, LinearMap.lTensor_zero]
      refine subsingleton_of_forall_eq 0 fun y => ?_
      obtain ⟨z, rfl⟩ := hsurj y
      obtain ⟨w, rfl⟩ := (hbij i).2 z
      rw [← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax _ hQ
    have htop : LinearMap.range f = ⊤ :=
      Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩
    exact LinearMap.range_eq_top.mp htop

end GlobalTheory
