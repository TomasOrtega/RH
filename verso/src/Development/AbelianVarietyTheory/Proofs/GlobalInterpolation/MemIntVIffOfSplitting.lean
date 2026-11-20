import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.SplitIntegers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conj_tmul (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] (a : E) (y : R) :
    Formalism.UG.sigR hc.sig R (a ⊗ₜ[F] y) = star a ⊗ₜ[F] y := rfl

omit [NumberField F] [NumberField E] [StarRing E] in
/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]`.
-/
theorem algebraMap_tmul {R : Type} [CommRing R] [Algebra F R] (c : F) (y : R) :
    (algebraMap F E c) ⊗ₜ[F] y = (1 : E) ⊗ₜ[F] (algebraMap F R c * y) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul a y`. Take `⟨c, h⟩` from `(hc.fixed (a + star a)).1 (by simp [add_comm])`. Conclude with `⟨algebraMap F R c * y, by rw [conj_tmul, ← TensorProduct.add_tmul, ← h, algebraMap_tmul]⟩`.

Consider the case `add x y hx hy`. Take `⟨p, hp⟩` from `hx`. Take `⟨q, hq⟩` from `hy`. Use `⟨p + q, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, TensorProduct.tmul_add, ← hp, ← hq]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_add_conj (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    ∃ p : R, z + Formalism.UG.sigR hc.sig R z = (1 : E) ⊗ₜ[F] p := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a y =>
    obtain ⟨c, h⟩ := (hc.fixed (a + star a)).1 (by simp [add_comm])
    exact ⟨algebraMap F R c * y, by rw [conj_tmul, ← TensorProduct.add_tmul, ← h, algebraMap_tmul]⟩
  | add x y hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    refine ⟨p + q, ?_⟩
    rw [map_add, TensorProduct.tmul_add, ← hp, ← hq]; ring

/- English proof (translation)
Take `⟨p, hp⟩` from `exists_add_conj hc z`. Rewrite `hp` using `[hz, ← two_smul F z]`. Use `⟨(2⁻¹ : F) • p, ?_⟩` and prove the remaining obligations. Rewrite using `[TensorProduct.tmul_smul, ← hp, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]`.
-/
theorem exists_of_conj_eq (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] {z : E ⊗[F] R}
    (hz : Formalism.UG.sigR hc.sig R z = z) : ∃ p : R, (1 : E) ⊗ₜ[F] p = z := by
  obtain ⟨p, hp⟩ := exists_add_conj hc z
  rw [hz, ← two_smul F z] at hp
  refine ⟨(2⁻¹ : F) • p, ?_⟩
  rw [TensorProduct.tmul_smul, ← hp, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/- English proof (translation)
Set `f : K →+* K` to `((RingHom.fst K K).comp φ.toRingHom).comp (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := K)).toRingHom`. Establish `hf : ∀ y, φ ((1 : E) ⊗ₜ[F] y) = (f y, f y)` using `fun y => by`. Establish `h` using `hφ ((1 : E) ⊗ₜ[F] y)`. Rewrite `h` using `[conj_tmul, star_one]`. Establish `h2` using `congrArg Prod.snd h`.

Conclude with `Prod.ext rfl h2`. Use `⟨RingEquiv.ofBijective f ⟨f.injective, fun b => ?_⟩, hf⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `exists_of_conj_eq hc (z := φ.symm (b, b)) (φ.injective (by`. Rewrite using `[hφ, φ.apply_symm_apply]`. Use the proof step `rfl))`.

Use `⟨p, ?_⟩` and prove the remaining obligations. Use `hf p` as an intermediate fact. Rewrite `this` using `[hp, φ.apply_symm_apply]`. Conclude with `(congrArg Prod.fst this).symm`.
-/
theorem exists_diag (hc : CMData F E) {K : Type} [Field K] [Algebra F K]
    (φ : E ⊗[F] K ≃+* K × K) (hφ : ∀ x, φ (Formalism.UG.sigR hc.sig K x) = swapR _ (φ x)) :
    ∃ θ : K ≃+* K, ∀ y, φ ((1 : E) ⊗ₜ[F] y) = (θ y, θ y) := by
  let f : K →+* K := ((RingHom.fst K K).comp φ.toRingHom).comp
    (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := K)).toRingHom
  have hf : ∀ y, φ ((1 : E) ⊗ₜ[F] y) = (f y, f y) := fun y => by
    have h := hφ ((1 : E) ⊗ₜ[F] y)
    rw [conj_tmul, star_one] at h
    have h2 := congrArg Prod.snd h
    exact Prod.ext rfl h2
  refine ⟨RingEquiv.ofBijective f ⟨f.injective, fun b => ?_⟩, hf⟩
  obtain ⟨p, hp⟩ := exists_of_conj_eq hc (z := φ.symm (b, b)) (φ.injective (by
    rw [hφ, φ.apply_symm_apply]; rfl))
  refine ⟨p, ?_⟩
  have := hf p
  rw [hp, φ.apply_symm_apply] at this
  exact (congrArg Prod.fst this).symm

/- English proof (translation)
Establish `hi : IsIntegral (v.adicCompletionIntegers F) x` using `hx.tower_top`. Take `⟨b, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hi`. Conclude with `b.2`.
-/
theorem mem_of_isIntegral (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F}
    (hx : IsIntegral ℤ x) : x ∈ v.adicCompletionIntegers F := by
  have hi : IsIntegral (v.adicCompletionIntegers F) x := hx.tower_top
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact b.2

omit [NumberField E] [StarRing E] [Algebra F E] in
/- English proof (translation)
The claim follows from `mem_of_isIntegral v (a.isIntegral_coe.map_of_comp_eq (RingHom.id ℤ) (g : E →+* v.adicCompletion F) (RingHom.ext_int _ _))`.
-/
theorem map_mem {S : Type} (v : HeightOneSpectrum (𝓞 F)) [FunLike S E (v.adicCompletion F)]
    [RingHomClass S E (v.adicCompletion F)] (g : S) (a : 𝓞 E) :
    g (algebraMap (𝓞 E) E a) ∈ v.adicCompletionIntegers F :=
  mem_of_isIntegral v (a.isIntegral_coe.map_of_comp_eq (RingHom.id ℤ)
    (g : E →+* v.adicCompletion F) (RingHom.ext_int _ _))

end GlobalTheory.SplitIntegers

namespace GlobalTheory

open SplitIntegers

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc v hθ φ hφ`. Take `⟨θ, hd⟩` from `exists_diag hc φ hφ`. Establish `hθ' : ∀ y ∈ v.adicCompletionIntegers F, θ.symm y ∈ v.adicCompletionIntegers F` using `fun y hy => (hθ θ.symm y).2 hy`. Set `ι : E →+* v.adicCompletion F × v.adicCompletion F` to `φ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E) (B := v.adicCompletion F))`. Establish `hι : ∀ a : 𝓞 E, (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).1 ∈ v.adicCompletionIntegers F ∧ (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).2 ∈ v.adicCompletionIntegers F` using `fun a => ⟨map_mem v ((RingHom.fst _ _).comp ι) a, map_mem v ((RingHom.snd _ _).comp ι) a⟩`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`.

Break down `hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩` into its components or cases. Conclude with `hι a`. Use `beta_reduce`. Rewrite using `[hd]`. Conclude with `⟨(hθ θ y).2 y.2, (hθ θ y).2 y.2⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `⟨zero_mem _, zero_mem _⟩`. Consider the case `one => rw [map_one]`. Conclude with `⟨one_mem _, one_mem _⟩`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `⟨neg_mem hx.1, neg_mem hx.2⟩`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩`.

Introduce and unpack `⟨ha, hb⟩`. Take `⟨P, hP, hPv⟩` from `GlobalTheory.Mass.Genus.exists_over (E := E) v`. Take `⟨w, t, ht, hwt⟩` from `hc.cmUnram.2.2 P hP`. Take `⟨s, hs⟩` from `(hc.fixed (algebraMap (𝓞 E) E ((w - t) * (w - t)))).1 (by`. Rewrite using `[map_mul, map_sub, ht, star_mul, star_sub, star_star]`.

Use the proof step `ring)`. Establish `hsi : IsIntegral ℤ s`. Use `((w - t) * (w - t)).isIntegral_coe` as an intermediate fact. Rewrite `this` using `[← hs]`. Conclude with `(isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 this`.

Set `s' : 𝓞 F` to `⟨s, hsi⟩`. Establish `hs' : algebraMap (𝓞 F) (𝓞 E) s' = (w - t) * (w - t)` using `RingOfIntegers.ext hs`. Establish `hsv : s' ∉ v.asIdeal` using `fun h => by`. Rewrite `h` using `[← hPv, Ideal.mem_comap, hs']`. Conclude with `hwt ((hP.isPrime.mem_or_mem h).elim id id)`.

Take `⟨u, hu⟩` from `((SelfDualGenus.isUnit_algebraMap_iff v s').2 hsv).exists_left_inv`. Establish `hu' : (u : v.adicCompletion F) * algebraMap F (v.adicCompletion F) s = 1` using `congrArg Subtype.val hu`. Take `⟨hα, hβ⟩` from `hι w`. Establish `e1` using `hφ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1)`. Rewrite `e1` using `[conj_tmul, ← ht]`.

Establish `e2` using `hd (algebraMap F (v.adicCompletion F) s * 1)`. Rewrite `e2` using `[← algebraMap_tmul, hs, mul_one, ← mul_one (1 : v.adicCompletion F), map_mul, ← Algebra.TensorProduct.tmul_mul_tmul, map_sub, TensorProduct.sub_tmul, map_mul, map_sub, e1]`. Generalize the expression as in `hW : φ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1) = W at hα hβ e2`. Take `⟨α, β⟩` from `W`. Establish `e3 : (α - β) * (α - β) = θ (algebraMap F (v.adicCompletion F) s)` using `congrArg Prod.fst e2`.

Establish `e4 : θ u * ((α - β) * (α - β)) = 1` using `by rw [e3, ← map_mul, hu', map_one]`. Establish `hθu : θ u ∈ v.adicCompletionIntegers F` using `(hθ θ u).2 u.2`. Use `set c := ((φ x).1 - (φ x).2) * (θ u * (α - β)) with hcdef`. Establish `hcm : c ∈ v.adicCompletionIntegers F` using `mul_mem (sub_mem ha hb) (mul_mem hθu (sub_mem hα hβ))`. Establish `hx : x = (1 : E) ⊗ₜ[F] θ.symm ((φ x).1 - c * α) + ((1 : E) ⊗ₜ[F] θ.symm c) * (algebraMap (𝓞 E) E w ⊗ₜ[F] 1)`.

Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_add, map_mul, hd, hd, hW, θ.apply_symm_apply, θ.apply_symm_apply]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(φ x).1 = (φ x).1 - c * α + c * α`. Expand and normalize the polynomial expressions, which then agree.

Express the relevant statement in the definitionally equal form `(φ x).2 = (φ x).1 - c * α + c * β`. Rewrite using `[hcdef]`. Take the linear combination `((φ x).1 - (φ x).2) * e4`. Rewrite using `[hx]`. Use `add_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ (sub_mem ha (mul_mem hcm hα))⟩, rfl⟩)) (mul_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ hcm⟩, rfl⟩)) (Subring.subset_closure (Or.inl ⟨⟨_, w, rfl⟩, rfl⟩)))` and prove the remaining obligations.
-/
theorem mem_intV_iff_of_splitting : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (v : HeightOneSpectrum (𝓞 F)), (∀ (θ : v.adicCompletion F ≃+* v.adicCompletion F) (x : v.adicCompletion F), θ x ∈ v.adicCompletionIntegers F ↔ x ∈ v.adicCompletionIntegers F) → ∀ (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, φ (Formalism.UG.sigR hc.sig (v.adicCompletion F) x) = swapR _ (φ x)) → ∀ x, x ∈ intV E v ↔ (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ hc v hθ φ hφ
  obtain ⟨θ, hd⟩ := exists_diag hc φ hφ
  have hθ' : ∀ y ∈ v.adicCompletionIntegers F, θ.symm y ∈ v.adicCompletionIntegers F :=
    fun y hy => (hθ θ.symm y).2 hy
  let ι : E →+* v.adicCompletion F × v.adicCompletion F := φ.toRingHom.comp
    (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E) (B := v.adicCompletion F))
  have hι : ∀ a : 𝓞 E,
      (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).1 ∈ v.adicCompletionIntegers F ∧
      (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).2 ∈ v.adicCompletionIntegers F := fun a =>
    ⟨map_mem v ((RingHom.fst _ _).comp ι) a, map_mem v ((RingHom.snd _ _).comp ι) a⟩
  intro x
  constructor
  · intro hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩
      · exact hι a
      · beta_reduce
        rw [hd]
        exact ⟨(hθ θ y).2 y.2, (hθ θ y).2 y.2⟩
    | zero => rw [map_zero]; exact ⟨zero_mem _, zero_mem _⟩
    | one => rw [map_one]; exact ⟨one_mem _, one_mem _⟩
    | add x y _ _ hx hy => rw [map_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | neg x _ hx => rw [map_neg]; exact ⟨neg_mem hx.1, neg_mem hx.2⟩
    | mul x y _ _ hx hy => rw [map_mul]; exact ⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨P, hP, hPv⟩ := GlobalTheory.Mass.Genus.exists_over (E := E) v
    obtain ⟨w, t, ht, hwt⟩ := hc.cmUnram.2.2 P hP
    obtain ⟨s, hs⟩ := (hc.fixed (algebraMap (𝓞 E) E ((w - t) * (w - t)))).1 (by
      rw [map_mul, map_sub, ht, star_mul, star_sub, star_star]; ring)
    have hsi : IsIntegral ℤ s := by
      have := ((w - t) * (w - t)).isIntegral_coe
      rw [← hs] at this
      exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 this
    let s' : 𝓞 F := ⟨s, hsi⟩
    have hs' : algebraMap (𝓞 F) (𝓞 E) s' = (w - t) * (w - t) := RingOfIntegers.ext hs
    have hsv : s' ∉ v.asIdeal := fun h => by
      rw [← hPv, Ideal.mem_comap, hs'] at h
      exact hwt ((hP.isPrime.mem_or_mem h).elim id id)
    obtain ⟨u, hu⟩ := ((SelfDualGenus.isUnit_algebraMap_iff v s').2 hsv).exists_left_inv
    have hu' : (u : v.adicCompletion F) * algebraMap F (v.adicCompletion F) s = 1 :=
      congrArg Subtype.val hu
    obtain ⟨hα, hβ⟩ := hι w
    have e1 := hφ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1)
    rw [conj_tmul, ← ht] at e1
    have e2 := hd (algebraMap F (v.adicCompletion F) s * 1)
    rw [← algebraMap_tmul, hs, mul_one, ← mul_one (1 : v.adicCompletion F), map_mul,
      ← Algebra.TensorProduct.tmul_mul_tmul, map_sub, TensorProduct.sub_tmul, map_mul, map_sub,
      e1] at e2
    generalize hW : φ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1) = W at hα hβ e2
    obtain ⟨α, β⟩ := W
    have e3 : (α - β) * (α - β) = θ (algebraMap F (v.adicCompletion F) s) := congrArg Prod.fst e2
    have e4 : θ u * ((α - β) * (α - β)) = 1 := by rw [e3, ← map_mul, hu', map_one]
    have hθu : θ u ∈ v.adicCompletionIntegers F := (hθ θ u).2 u.2
    set c := ((φ x).1 - (φ x).2) * (θ u * (α - β)) with hcdef
    have hcm : c ∈ v.adicCompletionIntegers F :=
      mul_mem (sub_mem ha hb) (mul_mem hθu (sub_mem hα hβ))
    have hx : x = (1 : E) ⊗ₜ[F] θ.symm ((φ x).1 - c * α) +
        ((1 : E) ⊗ₜ[F] θ.symm c) * (algebraMap (𝓞 E) E w ⊗ₜ[F] 1) := by
      apply φ.injective
      rw [map_add, map_mul, hd, hd, hW, θ.apply_symm_apply, θ.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · change (φ x).1 = (φ x).1 - c * α + c * α
        ring
      · change (φ x).2 = (φ x).1 - c * α + c * β
        rw [hcdef]
        linear_combination ((φ x).1 - (φ x).2) * e4
    rw [hx]
    refine add_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ (sub_mem ha (mul_mem hcm hα))⟩, rfl⟩))
      (mul_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ hcm⟩, rfl⟩))
        (Subring.subset_closure (Or.inl ⟨⟨_, w, rfl⟩, rfl⟩)))

end GlobalTheory
