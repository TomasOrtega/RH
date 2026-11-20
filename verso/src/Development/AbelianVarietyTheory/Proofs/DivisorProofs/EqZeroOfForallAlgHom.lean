import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCA

open TensorProduct

noncomputable section
namespace GlobalTheory.CxPointsSep

/- English proof (translation)
Use `haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)`. Establish `hrad : (⊥ : Ideal A).IsRadical`. Rewrite using `[Ideal.isRadical_bot_iff]`. Use `infer_instance`. Establish `hj : (⊥ : Ideal A).jacobson = ⊥` using `IsJacobsonRing.out inferInstance hrad`.

Rewrite using `[← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]`. Introduce and unpack `m ⟨-, hm⟩`. Use `letI : Field (A ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)`. Establish `hb : Function.Bijective (algebraMap k (A ⧸ m))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`.

Set `i : k ≃ₐ[k] (A ⧸ m)` to `AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hb`. Use `h ((i.symm : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m))` as an intermediate fact. Rewrite `this` using `[AlgHom.comp_apply]`. Establish `h2 : Ideal.Quotient.mkₐ k m a = 0`. Apply `i.symm.injective` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Conclude with `this`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h2`.
-/
theorem eq_zero_of_forall_algHom {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [IsReduced A] [Algebra.FiniteType k A] (a : A) (h : ∀ e : A →ₐ[k] k, e a = 0) : a = 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal A).IsRadical := by
    rw [Ideal.isRadical_bot_iff]; infer_instance
  have hj : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance hrad
  rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hb : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hb
  have := h ((i.symm : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m))
  rw [AlgHom.comp_apply] at this
  have h2 : Ideal.Quotient.mkₐ k m a = 0 := by
    apply i.symm.injective
    rw [map_zero]; exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

/- English proof (translation)
Use `set K := FractionRing D`. Establish `: Algebra.EssFiniteType ℚ K` using `inferInstanceAs (Algebra.EssFiniteType ℚ (Localization _))`. Establish `h1 : IsReduced (K ⊗[ℚ] ℂ)` using `ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_of_essFiniteType K ℂ`. Establish `h2 : IsReduced (ℂ ⊗[ℚ] K)` using `isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ K).toRingEquiv.toRingHom (Algebra.TensorProduct.comm ℚ ℂ K).injective`. Establish `hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ) (IsScalarTower.toAlgHom ℚ D K))` using `Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)`.

Conclude with `isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ) (IsScalarTower.toAlgHom ℚ D K)).toRingHom hinj`.
-/
theorem isReduced_complex_tensor (D : Type) [CommRing D] [IsDomain D] [Algebra ℚ D]
    [Algebra.FiniteType ℚ D] : IsReduced (ℂ ⊗[ℚ] D) := by
  set K := FractionRing D
  have : Algebra.EssFiniteType ℚ K := inferInstanceAs (Algebra.EssFiniteType ℚ (Localization _))
  have h1 : IsReduced (K ⊗[ℚ] ℂ) := ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_of_essFiniteType K ℂ
  have h2 : IsReduced (ℂ ⊗[ℚ] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ K).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm ℚ ℂ K).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ D K)).toRingHom hinj

/- English proof (translation)
Set `K` to `FractionRing B`. Take `⟨s, hs⟩` from `(Algebra.FiniteType.out : (⊤ : Subalgebra ℤ B).FG)`. Set `D : Subalgebra ℚ K` to `Algebra.adjoin ℚ ((algebraMap B K) '' (s : Set B))`. Establish `hmem : ∀ b : B, algebraMap B K b ∈ D`. Introduce `b`.

Establish `hb : b ∈ Algebra.adjoin ℤ (s : Set B)` using `by rw [hs]; trivial`. Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩`. Consider the case `algebraMap n => rw [eq_intCast, map_intCast]`. Conclude with `intCast_mem D n`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`. Use `haveI : Algebra.FiniteType ℚ D := by`.

Rewrite using `[← Subalgebra.fg_iff_finiteType]`. Use `Subalgebra.fg_adjoin_finset (R := ℚ) (s.image (algebraMap B K))` as an intermediate fact. Simplify `this` using `[D]`. Set `g : B →+* D` to `(algebraMap B K).codRestrict D hmem`. Establish `hg : Function.Injective g` using `fun a b h => IsFractionRing.injective B K (congrArg Subtype.val h)`.

Establish `hD : LinearIndependent ℚ (fun j => g (f j))`. Rewrite using `[← LinearIndependent.iff_fractionRing ℤ ℚ]`. Conclude with `hf.map' g.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.mpr hg)`. Establish `hT : LinearIndependent ℂ (fun j => (1 : ℂ) ⊗ₜ[ℚ] g (f j))` using `Module.Flat.linearIndependent_one_tmul hD`. Use `haveI : IsReduced (ℂ ⊗[ℚ] D) := isReduced_complex_tensor D`.

Set `pt : ((ℂ ⊗[ℚ] D) →ₐ[ℂ] ℂ) → (B →+* ℂ)` to `fun φ => (φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℂ) (B := D)).toRingHom).comp g`. Set `S : Set (Fin r → ℂ)` to `Set.range fun x : B →+* ℂ => fun j => x (f j)`. Establish `hspan : Submodule.span ℂ S = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨ℓ, hℓ, hle⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)`.

Set `c : Fin r → ℂ` to `fun i => ℓ (fun j => if i = j then 1 else 0)`. Establish `hℓv : ∀ v, ℓ v = ∑ i, v i * c i` using `fun v => by`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ ℓ v]`. Both sides reduce to the same expression. Establish `hu : ∑ i, c i • ((1 : ℂ) ⊗ₜ[ℚ] g (f i)) = 0`.

Apply `eq_zero_of_forall_algHom (k := ℂ)` to reduce the goal to its premises. Introduce `φ`. Establish `h0 : ℓ (fun j => pt φ (f j)) = 0` using `hle (Submodule.subset_span ⟨pt φ, rfl⟩)`. Rewrite `h0` using `[hℓv]`. Rewrite using `[map_sum, ← h0]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression. Establish `hc : c = 0` using `funext fun i => Fintype.linearIndependent_iff.mp hT c hu i`. Apply `hℓ` to reduce the goal to its premises.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[hℓv, hc]`. Simplify using the standard rewrite rules. Take `⟨b, hbS, hbspan, hli⟩` from `exists_linearIndependent ℂ S`. Establish `hb_top : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Fin r → ℂ))`.

Rewrite using `[Subtype.range_coe, hbspan, hspan]`. Set `bb` to `Module.Basis.mk hli hb_top`. Set `e : b ≃ Fin r` to `bb.indexEquiv (Pi.basisFun ℂ (Fin r))`. Establish `hx : ∀ i : Fin r, ∃ x : B →+* ℂ, (fun j => x (f j)) = ((e.symm i : b) : Fin r → ℂ)` using `fun i => hbS (e.symm i).2`. Use `choose x hx using hx`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `hrows : LinearIndependent ℂ (fun i => (Matrix.of fun i j => x i (f j)) i)`. Establish `: (fun i => (Matrix.of fun i j => x i (f j)) i) = (fun v : b => (v : Fin r → ℂ)) ∘ e.symm`. Use function extensionality and compare the values at `i`. Conclude with `hx i`.

Rewrite using `[this]`. Conclude with `hli.comp _ e.symm.injective`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero`.
-/
theorem exists_det_ne_zero (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (r : ℕ) (f : Fin r → B) (hf : LinearIndependent ℤ f) :
    ∃ x : Fin r → (B →+* ℂ), (Matrix.of fun i j => x i (f j)).det ≠ 0 := by
  classical
  let K := FractionRing B
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ B).FG)
  let D : Subalgebra ℚ K := Algebra.adjoin ℚ ((algebraMap B K) '' (s : Set B))
  have hmem : ∀ b : B, algebraMap B K b ∈ D := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (s : Set B) := by rw [hs]; trivial
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap n => rw [eq_intCast, map_intCast]; exact intCast_mem D n
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  haveI : Algebra.FiniteType ℚ D := by
    rw [← Subalgebra.fg_iff_finiteType]
    have := Subalgebra.fg_adjoin_finset (R := ℚ) (s.image (algebraMap B K))
    simpa [D] using this
  let g : B →+* D := (algebraMap B K).codRestrict D hmem
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective B K (congrArg Subtype.val h)
  have hD : LinearIndependent ℚ (fun j => g (f j)) := by
    rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
    exact hf.map' g.toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.mpr hg)
  have hT : LinearIndependent ℂ (fun j => (1 : ℂ) ⊗ₜ[ℚ] g (f j)) :=
    Module.Flat.linearIndependent_one_tmul hD
  haveI : IsReduced (ℂ ⊗[ℚ] D) := isReduced_complex_tensor D
  let pt : ((ℂ ⊗[ℚ] D) →ₐ[ℂ] ℂ) → (B →+* ℂ) := fun φ =>
    (φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℂ) (B := D)).toRingHom).comp g
  let S : Set (Fin r → ℂ) := Set.range fun x : B →+* ℂ => fun j => x (f j)
  have hspan : Submodule.span ℂ S = ⊤ := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let c : Fin r → ℂ := fun i => ℓ (fun j => if i = j then 1 else 0)
    have hℓv : ∀ v, ℓ v = ∑ i, v i * c i := fun v => by
      rw [LinearMap.pi_apply_eq_sum_univ ℓ v]; rfl
    have hu : ∑ i, c i • ((1 : ℂ) ⊗ₜ[ℚ] g (f i)) = 0 := by
      apply eq_zero_of_forall_algHom (k := ℂ)
      intro φ
      have h0 : ℓ (fun j => pt φ (f j)) = 0 := hle (Submodule.subset_span ⟨pt φ, rfl⟩)
      rw [hℓv] at h0
      rw [map_sum, ← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl
    have hc : c = 0 := funext fun i => Fintype.linearIndependent_iff.mp hT c hu i
    apply hℓ
    refine LinearMap.ext fun v => ?_
    rw [hℓv, hc]
    simp
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent ℂ S
  have hb_top : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Fin r → ℂ)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let bb := Module.Basis.mk hli hb_top
  let e : b ≃ Fin r := bb.indexEquiv (Pi.basisFun ℂ (Fin r))
  have hx : ∀ i : Fin r, ∃ x : B →+* ℂ, (fun j => x (f j)) = ((e.symm i : b) : Fin r → ℂ) :=
    fun i => hbS (e.symm i).2
  choose x hx using hx
  refine ⟨x, ?_⟩
  have hrows : LinearIndependent ℂ (fun i => (Matrix.of fun i j => x i (f j)) i) := by
    have : (fun i => (Matrix.of fun i j => x i (f j)) i) = (fun v : b => (v : Fin r → ℂ)) ∘ e.symm := by
      funext i; exact hx i
    rw [this]; exact hli.comp _ e.symm.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

end GlobalTheory.CxPointsSep
