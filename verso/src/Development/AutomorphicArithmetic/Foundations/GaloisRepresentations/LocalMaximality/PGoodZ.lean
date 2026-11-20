import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverRingLocalizationChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemOmAOfMemRA

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section Tensor
variable {S S' E E' : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
  [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']

/- English proof (translation)
Introduce and unpack `_ ⟨z, rfl⟩`. Use `⟨Algebra.TensorProduct.map (Subalgebra.inclusion hA) (Subalgebra.inclusion hB) z, ?_⟩` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`.

Consider the case `add p q hp hq => simp only [map_add] at *`. Rewrite using `[hp, hq]`.
-/
private theorem range_mono {A A' : Subalgebra ℂ S} {B B' : Subalgebra ℂ S'} (hA : A ≤ A') (hB : B ≤ B') :
    (Algebra.TensorProduct.map A.val B.val).range ≤ (Algebra.TensorProduct.map A'.val B'.val).range := by
  rintro _ ⟨z, rfl⟩
  refine ⟨Algebra.TensorProduct.map (Subalgebra.inclusion hA) (Subalgebra.inclusion hB) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add p q hp hq => simp only [map_add] at *; rw [hp, hq]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(⟨a, ha⟩ : A) ⊗ₜ[ℂ] (⟨b, hb⟩ : B), by simp⟩`.
-/
private theorem tmul_mem_range {A : Subalgebra ℂ S} {B : Subalgebra ℂ S'} {a : S} {b : S'} (ha : a ∈ A) (hb : b ∈ B) :
    a ⊗ₜ[ℂ] b ∈ (Algebra.TensorProduct.map A.val B.val).range :=
  ⟨(⟨a, ha⟩ : A) ⊗ₜ[ℂ] (⟨b, hb⟩ : B), by simp⟩

/- English proof (translation)
Introduce and unpack `_ ⟨z, rfl⟩ m hm`. Proceed by induction on `z using TensorProduct.induction_on generalizing m with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Establish `hle : Submodule.map₂ (TensorProduct.mk ℂ E E') P Q ≤ (Submodule.map₂ (TensorProduct.mk ℂ E E') P Q).comap (TensorProduct.map (f a) (g b))`.

Rewrite using `[Submodule.map₂_le]`. Introduce `p hp q hq`. Simplify using `only [Submodule.mem_comap, TensorProduct.mk_apply, TensorProduct.map_tmul]`. Conclude with `Submodule.apply_mem_map₂ _ (hP _ a.2 _ hp) (hQ _ b.2 _ hq)`. Establish `h2` using `hle hm`.

Simplify using `only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Subalgebra.coe_val]`. Conclude with `h2`. Consider the case `add p q hp hq`. Rewrite using `[map_add, map_add, LinearMap.add_apply]`. Conclude with `add_mem (hp m hm) (hq m hm)`.
-/
private theorem stab_tensor (f : S →ₐ[ℂ] Module.End ℂ E) (g : S' →ₐ[ℂ] Module.End ℂ E')
    {A : Subalgebra ℂ S} {B : Subalgebra ℂ S'} {P : Submodule ℂ E} {Q : Submodule ℂ E'}
    (hP : ∀ a ∈ A, ∀ m ∈ P, f a m ∈ P) (hQ : ∀ b ∈ B, ∀ m ∈ Q, g b m ∈ Q) :
    Stab ((Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map f g))
      (Algebra.TensorProduct.map A.val B.val).range (Submodule.map₂ (TensorProduct.mk ℂ _ _) P Q) := by
  rintro _ ⟨z, rfl⟩ m hm
  induction z using TensorProduct.induction_on generalizing m with
  | zero => simp
  | tmul a b =>
    have hle : Submodule.map₂ (TensorProduct.mk ℂ E E') P Q ≤
        (Submodule.map₂ (TensorProduct.mk ℂ E E') P Q).comap (TensorProduct.map (f a) (g b)) := by
      rw [Submodule.map₂_le]
      intro p hp q hq
      simp only [Submodule.mem_comap, TensorProduct.mk_apply, TensorProduct.map_tmul]
      exact Submodule.apply_mem_map₂ _ (hP _ a.2 _ hp) (hQ _ b.2 _ hq)
    have h2 := hle hm
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Subalgebra.coe_val]
    exact h2
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply]
    exact add_mem (hp m hm) (hq m hm)

/- English proof (translation)
Simplify using `[div_eq_mul_inv]`.
-/
private theorem units_ratio {F : Type} [Field F] (f : F →+* S) (u v : Fˣ) :
    ((Units.map (f : F →* S) u * (Units.map (f : F →* S) v)⁻¹ : Sˣ) : S) = f ((u : F) / v) := by
  simp [div_eq_mul_inv]

end Tensor

section Forms
variable {K : Type} [Field K] [Algebra ℂ K]

/- English proof (translation)
Unfold `omB`. Conclude with `Submodule.span_mono (fun y ⟨b, hb, v, hv, e⟩ => ⟨b, h hb, v, fun j => h (hv j), e⟩)`.
-/
private theorem omB_mono' {B B' : Subalgebra ℂ K} (h : B ≤ B') (q : ℕ) : omB ℂ K B q ≤ omB ℂ K B' q := by
  unfold omB
  exact Submodule.span_mono (fun y ⟨b, hb, v, hv, e⟩ => ⟨b, h hb, v, fun j => h (hv j), e⟩)

/- English proof (translation)
Use `show c • m ∈ omB ℂ K B q`. Unfold `omB at hm ⊢`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, v, hv, rfl⟩` from `hy`.

Conclude with `Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [mul_smul]⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [smul_add]`. Conclude with `add_mem hy hz`. Consider the case `smul r y _ hy => rw [smul_comm]`.

Conclude with `Submodule.smul_mem _ r hy`.
-/
private theorem omB_smul (B : Subalgebra ℂ K) (q : ℕ) {c : K} (hc : c ∈ B) {m : DR ℂ K} (hm : m ∈ omB ℂ K B q) :
    Algebra.lsmul ℂ ℂ (DR ℂ K) c m ∈ omB ℂ K B q := by
  show c • m ∈ omB ℂ K B q
  unfold omB at hm ⊢
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [mul_smul]⟩
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ r hy

end Forms

section Chart
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

/- English proof (translation)
Unfold `rA`. Conclude with `Algebra.subset_adjoin ⟨i, hi, a, rfl⟩`.
-/
private theorem ratio_mem_rA {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    (x a : F) / x i ∈ rA ℂ (xv x) I := by
  unfold rA
  exact Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

/- English proof (translation)
Unfold `rB`. Conclude with `(integralClosure (rA ℂ (xv x) I) K).algebraMap_mem (⟨_, ratio_mem_rA x hi a⟩ : rA ℂ (xv x) I)`.
-/
private theorem ratio_mem_rB {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    algebraMap F K ((x a : F) / x i) ∈ rB ℂ K (xv x) I := by
  unfold rB
  exact (integralClosure (rA ℂ (xv x) I) K).algebraMap_mem (⟨_, ratio_mem_rA x hi a⟩ : rA ℂ (xv x) I)

/- English proof (translation)
Unfold `sysZ`. Conclude with `(units_ratio _ (x b) (x i)).trans rfl`.
-/
private theorem sysZ_X (a : ℕ) (b i : Fin (d + 1)) :
    (((sysZ K x a).X b * ((sysZ K x a).X i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      algebraMap F K ((x b : F) / x i) ⊗ₜ[ℂ] 1 := by
  unfold sysZ
  exact (units_ratio _ (x b) (x i)).trans rfl

/- English proof (translation)
Unfold `sysZ`. Conclude with `(units_ratio _ (x b) (x i)).trans rfl`.
-/
private theorem sysZ_Y (a : ℕ) (b i : Fin (d + 1)) :
    (((sysZ K x a).Y b * ((sysZ K x a).Y i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      1 ⊗ₜ[ℂ] algebraMap F K ((x b : F) / x i) := by
  unfold sysZ
  exact (units_ratio _ (x b) (x i)).trans rfl

/- English proof (translation)
Unfold `sysP`. Conclude with `(units_ratio _ (x b) (x i)).trans rfl`.
-/
private theorem sysP_X (a : ℕ) (b i : Fin (d + 1)) :
    (((sysP K x a).X b * ((sysP K x a).X i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
      ((x b : F) / x i) ⊗ₜ[ℂ] 1 := by
  unfold sysP
  exact (units_ratio _ (x b) (x i)).trans rfl

/- English proof (translation)
Unfold `sysP`. Conclude with `(units_ratio _ (x b) (x i)).trans rfl`.
-/
private theorem sysP_Y (a : ℕ) (b i : Fin (d + 1)) :
    (((sysP K x a).Y b * ((sysP K x a).Y i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
      1 ⊗ₜ[ℂ] algebraMap F K ((x b : F) / x i) := by
  unfold sysP
  exact (units_ratio _ (x b) (x i)).trans rfl

end Chart

/- English proof (translation)
Introduce `F K _ _ _ _ _ _ d x hx a`. Establish `hrB : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → I ⊆ J → rB ℂ K (xv x) I ≤ rB ℂ K (xv x) J`. Introduce `I J hI hIJ`. Take `⟨i, hi⟩` from `hI`. Conclude with `(GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) hx I i hi).1 J hIJ`.

Establish `hx0 : ∀ i, xv x i ≠ 0` using `fun i => (x i).ne_zero`. Use `⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `I I' J J' hI hJ hII hJJ`. Conclude with `range_mono (hrB I I' hI hII) (hrB J J' hJ hJJ)`. Introduce `I I' J J' hI hJ hII hJJ show MZ F K (xv x) a I J ≤ MZ F K (xv x) a I' J'`.

Unfold `MZ`. Conclude with `Submodule.map₂_le_map₂ (omB_mono' (hrB I I' hI hII) _) (omB_mono' (hrB J J' hJ hJJ) _)`. Introduce `I J hI hJ`. Conclude with `stab_tensor (Algebra.lsmul ℂ ℂ (DR ℂ K)) (Algebra.lsmul ℂ ℂ (DR ℂ K)) (fun c hc m hm => omB_smul _ _ hc hm) (fun c hc m hm => omB_smul _ _ hc hm)`. Introduce `I J hJ i hi b`.

Rewrite using `[sysZ_X]`. Conclude with `tmul_mem_range (ratio_mem_rB K x hi b) (Subalgebra.one_mem _)`. Introduce `I J hI j hj b`. Rewrite using `[sysZ_Y]`. Conclude with `tmul_mem_range (Subalgebra.one_mem _) (ratio_mem_rB K x hj b)`.

Introduce `I I' J J' hI hJ hII hJJ`. Conclude with `range_mono (rA_le_of_subset hII) (hrB J J' hJ hJJ)`. Introduce `I I' J J' hI hJ hII hJJ`. Conclude with `Submodule.map₂_le_map₂ (omA_le_of_subset hx0 hI hII) (omB_mono' (hrB J J' hJ hJJ) _)`. Introduce `I J hI hJ`.

Conclude with `stab_tensor (Algebra.lsmul ℂ ℂ F) (Algebra.lsmul ℂ ℂ (DR ℂ K)) (fun c hc m hm => mul_mem_omA_of_mem_rA hc hm) (fun c hc m hm => omB_smul _ _ hc hm)`. Introduce `I J hJ i hi b`. Rewrite using `[sysP_X]`. Conclude with `tmul_mem_range (ratio_mem_rA x hi b) (Subalgebra.one_mem _)`. Introduce `I J hI j hj b`.

Rewrite using `[sysP_Y]`. Conclude with `tmul_mem_range (Subalgebra.one_mem _) (ratio_mem_rB K x hj b)`. Introduce `s t hs hst`. Conclude with `omB_mono' (hrB s t hs hst) a`.
-/
theorem UpperTheory.Gal.productCup_of_system.goodZ_of :
    GoodZ := by
  intro F K _ _ _ _ _ _ d x hx a
  have hrB : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → I ⊆ J → rB ℂ K (xv x) I ≤ rB ℂ K (xv x) J := by
    intro I J hI hIJ
    obtain ⟨i, hi⟩ := hI
    exact (GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) hx I i hi).1 J hIJ
  have hx0 : ∀ i, xv x i ≠ 0 := fun i => (x i).ne_zero
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro I I' J J' hI hJ hII hJJ
    exact range_mono (hrB I I' hI hII) (hrB J J' hJ hJJ)
  · intro I I' J J' hI hJ hII hJJ
    show MZ F K (xv x) a I J ≤ MZ F K (xv x) a I' J'
    unfold MZ
    exact Submodule.map₂_le_map₂ (omB_mono' (hrB I I' hI hII) _) (omB_mono' (hrB J J' hJ hJJ) _)
  · intro I J hI hJ
    exact stab_tensor (Algebra.lsmul ℂ ℂ (DR ℂ K)) (Algebra.lsmul ℂ ℂ (DR ℂ K))
      (fun c hc m hm => omB_smul _ _ hc hm) (fun c hc m hm => omB_smul _ _ hc hm)
  · intro I J hJ i hi b
    rw [sysZ_X]
    exact tmul_mem_range (ratio_mem_rB K x hi b) (Subalgebra.one_mem _)
  · intro I J hI j hj b
    rw [sysZ_Y]
    exact tmul_mem_range (Subalgebra.one_mem _) (ratio_mem_rB K x hj b)
  · intro I I' J J' hI hJ hII hJJ
    exact range_mono (rA_le_of_subset hII) (hrB J J' hJ hJJ)
  · intro I I' J J' hI hJ hII hJJ
    exact Submodule.map₂_le_map₂ (omA_le_of_subset hx0 hI hII) (omB_mono' (hrB J J' hJ hJJ) _)
  · intro I J hI hJ
    exact stab_tensor (Algebra.lsmul ℂ ℂ F) (Algebra.lsmul ℂ ℂ (DR ℂ K))
      (fun c hc m hm => mul_mem_omA_of_mem_rA hc hm) (fun c hc m hm => omB_smul _ _ hc hm)
  · intro I J hJ i hi b
    rw [sysP_X]
    exact tmul_mem_range (ratio_mem_rA x hi b) (Subalgebra.one_mem _)
  · intro I J hI j hj b
    rw [sysP_Y]
    exact tmul_mem_range (Subalgebra.one_mem _) (ratio_mem_rB K x hj b)
  · intro s t hs hst
    exact omB_mono' (hrB s t hs hst) a
