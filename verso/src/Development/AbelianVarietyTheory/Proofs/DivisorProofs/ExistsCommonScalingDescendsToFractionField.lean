import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecTw
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.Mum.GalDesc

open GlobalTheory.FieldBaseChange

/- English proof (translation)
Use `haveI := IsAlgClosure.isGalois K F`. Establish `hx : x ∈ IntermediateField.fixedField (⊥ : IntermediateField K F).fixingSubgroup`. Rewrite using `[IntermediateField.mem_fixedField_iff]`. Introduce `σ _`. Conclude with `h σ.toAlgHom`.

Rewrite `hx` using `[InfiniteGalois.fixedField_fixingSubgroup]`. Conclude with `IntermediateField.mem_bot.1 hx`.
-/
theorem exists_algebraMap_eq_of_fixed {K F : Type} [Field K] [CharZero K] [Field F] [Algebra K F] [IsAlgClosure K F]
    (x : F) (h : ∀ σ : F →ₐ[K] F, σ x = x) : ∃ k : K, algebraMap K F k = x := by
  haveI := IsAlgClosure.isGalois K F
  have hx : x ∈ IntermediateField.fixedField (⊥ : IntermediateField K F).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ _
    exact h σ.toAlgHom
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hx
  exact IntermediateField.mem_bot.1 hx

variable {K F : Type} [Field K] [Field F] [Algebra K F] {V W : Type} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module F W]

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hg i hi`. Establish `key : ∀ ℓ : F →ₗ[K] K, ℓ (g i) = 0`. Introduce `ℓ`. Take `⟨Λ, hΛ⟩` from `ha.coord ℓ`.

Establish `h0 : ∑ j ∈ s, ℓ (g j) • Module.Basis.ofVectorSpace K V j = 0`. Use `congrArg Λ hg` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero, Finset.sum_congr rfl fun j _ => hΛ (g j) _]`. Conclude with `this`. Conclude with `linearIndependent_iff'.1 (Module.Basis.ofVectorSpace K V).linearIndependent s _ h0 i hi`.

Set `e` to `Module.Basis.ofVectorSpace K F`. Apply `e.repr.injective` to reduce the goal to its premises. Use extensionality with `j`. Simplify using `using key (e.coord j)`.
-/
theorem linearIndependent_image {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) :
    LinearIndependent F (fun i => a (Module.Basis.ofVectorSpace K V i)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have key : ∀ ℓ : F →ₗ[K] K, ℓ (g i) = 0 := by
    intro ℓ
    obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
    have h0 : ∑ j ∈ s, ℓ (g j) • Module.Basis.ofVectorSpace K V j = 0 := by
      have := congrArg Λ hg
      rw [map_sum, map_zero, Finset.sum_congr rfl fun j _ => hΛ (g j) _] at this
      exact this
    exact linearIndependent_iff'.1 (Module.Basis.ofVectorSpace K V).linearIndependent s _ h0 i hi
  let e := Module.Basis.ofVectorSpace K F
  apply e.repr.injective
  ext j
  simpa using key (e.coord j)

/- English proof (translation)
Rewrite using `[← ha.span, Submodule.span_le]`. Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[← (Module.Basis.ofVectorSpace K V).linearCombination_repr v, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem span_image {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) :
    ⊤ ≤ Submodule.span F (Set.range fun i => a (Module.Basis.ofVectorSpace K V i)) := by
  rw [← ha.span, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  rw [← (Module.Basis.ofVectorSpace K V).linearCombination_repr v, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def extBasis {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) :
    Module.Basis (Module.Basis.ofVectorSpaceIndex K V) F W :=
  Module.Basis.mk (linearIndependent_image ha) (span_image ha)

/- English proof (translation)
The claim follows from `Module.Basis.mk_apply _ _ _`.
-/
theorem extBasis_apply {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) (i) :
    extBasis ha i = a (Module.Basis.ofVectorSpace K V i) := Module.Basis.mk_apply _ _ _

/- English proof (translation)
Establish `hw : w ∈ Submodule.span F (Set.range B)` using `B.span_eq ▸ Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Rewrite using `[hg, B.repr_self, Finsupp.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`. Consider the case `smul c x _ hx`. Rewrite using `[map_smulₛₗ, map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, hx, map_mul]`.
-/
theorem repr_semilinear {Idx : Type} (B : Module.Basis Idx F W) (τ : F →+* F) (g : W →ₛₗ[τ] W)
    (hg : ∀ i, g (B i) = B i) (w : W) (i : Idx) : B.repr (g w) i = τ (B.repr w i) := by
  classical
  have hw : w ∈ Submodule.span F (Set.range B) := B.span_eq ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [hg, B.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | smul c x _ hx =>
    rw [map_smulₛₗ, map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, hx,
      map_mul]

/- English proof (translation)
Use `set B := extBasis ha`. Establish `hgB : ∀ σ j, g σ (B j) = B j` using `fun σ j => by rw [extBasis_apply, hg]`. Establish `fix : ∀ w : W, (∀ σ, g σ w = w) → ∃ v, a v = w`. Introduce `w hw`. Establish `: ∀ j, ∃ k : K, algebraMap K F k = B.repr w j` using `fun j => exists_algebraMap_eq_of_fixed _ fun σ => by`.

Establish `e` using `repr_semilinear B (σ : F →+* F) (g σ) (hgB σ) w j`. Rewrite `e` using `[hw σ]`. Conclude with `e.symm`. Use `choose k hk using this`. Use `⟨∑ j ∈ (B.repr w).support, k j • Module.Basis.ofVectorSpace K V j, ?_⟩` and prove the remaining obligations.

Use `conv_rhs => rw [← B.linearCombination_repr w, Finsupp.linearCombination_apply, Finsupp.sum]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, hk, extBasis_apply]`. Distinguish the cases in `h0 : ∀ i, T i = 0`.

Conclude with `⟨1, fun i => ⟨0, by rw [map_zero, h0 i, smul_zero]⟩⟩`. Use `push_neg at h0`. Take `⟨i₀, hi₀⟩` from `h0`. Establish `: B.repr (T i₀) ≠ 0` using `fun h => hi₀ (B.repr.injective (h.trans (map_zero _).symm))`. Take `⟨j, hj⟩` from `Finsupp.ne_iff.1 this`.

Use `set m0 := B.repr (T i₀) j with hm0`. Establish `hm00 : m0 ≠ 0` using `by simpa using hj`. Establish `hσm : ∀ σ : F →ₐ[K] F, σ m0 = (c σ : F) * m0` using `fun σ => by`. Use `repr_semilinear B (σ : F →+* F) (g σ) (hgB σ) (T i₀) j` as an intermediate fact. Rewrite `this` using `[hT, map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Conclude with `this.symm`. Use `⟨(Units.mk0 m0 hm00)⁻¹, fun i => fix _ fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, hT, smul_smul]`. Use `congr 1`. Simplify using `only [Units.val_inv_eq_inv_val, Units.val_mk0, RingHom.coe_coe, map_inv₀, hσm]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem exists_scale [CharZero K] [IsAlgClosure K F] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a)
    (g : ∀ σ : F →ₐ[K] F, W →ₛₗ[(σ : F →+* F)] W) (hg : ∀ σ v, g σ (a v) = a v)
    {Ix : Type} (T : Ix → W) (c : (F →ₐ[K] F) → Fˣ) (hT : ∀ σ i, g σ (T i) = (c σ : F) • T i) :
    ∃ u : Fˣ, ∀ i, ∃ v, a v = (u : F) • T i := by
  classical
  set B := extBasis ha
  have hgB : ∀ σ j, g σ (B j) = B j := fun σ j => by rw [extBasis_apply, hg]
  have fix : ∀ w : W, (∀ σ, g σ w = w) → ∃ v, a v = w := by
    intro w hw
    have : ∀ j, ∃ k : K, algebraMap K F k = B.repr w j := fun j =>
      exists_algebraMap_eq_of_fixed _ fun σ => by
        have e := repr_semilinear B (σ : F →+* F) (g σ) (hgB σ) w j
        rw [hw σ] at e
        exact e.symm
    choose k hk using this
    refine ⟨∑ j ∈ (B.repr w).support, k j • Module.Basis.ofVectorSpace K V j, ?_⟩
    conv_rhs => rw [← B.linearCombination_repr w, Finsupp.linearCombination_apply, Finsupp.sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulₛₗ, hk, extBasis_apply]
  by_cases h0 : ∀ i, T i = 0
  · exact ⟨1, fun i => ⟨0, by rw [map_zero, h0 i, smul_zero]⟩⟩
  push_neg at h0
  obtain ⟨i₀, hi₀⟩ := h0
  have : B.repr (T i₀) ≠ 0 := fun h => hi₀ (B.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 this
  set m0 := B.repr (T i₀) j with hm0
  have hm00 : m0 ≠ 0 := by simpa using hj
  have hσm : ∀ σ : F →ₐ[K] F, σ m0 = (c σ : F) * m0 := fun σ => by
    have := repr_semilinear B (σ : F →+* F) (g σ) (hgB σ) (T i₀) j
    rw [hT, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
    exact this.symm
  refine ⟨(Units.mk0 m0 hm00)⁻¹, fun i => fix _ fun σ => ?_⟩
  rw [map_smulₛₗ, hT, smul_smul]
  congr 1
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, RingHom.coe_coe, map_inv₀, hσm]
  field_simp
end GlobalTheory.Mum.GalDesc

namespace GlobalTheory.Mum

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.GalDesc

/- English proof (translation)
Introduce `R _ _ _ hB A N Ix T a hT`. Use `haveI : CharZero R := hB.2`. Use `haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))`. Set `π : A.A.left ⟶ Spec (CommRingCat.of (FractionRing R))` to `A.A.hom`. Set `π'` to `(fst (TFK (R := R) (Kb R)) A.A).left`.

Set `p` to `(snd (TFK (R := R) (Kb R)) A.A).left`. Establish `H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R))))` using `(IsPullback.of_hasPullback _ _).flip`. Use `haveI : TopologicalSpace.NoetherianSpace A.A.left := by`. Use `A.isAb.proper` as an intermediate fact. Establish `: IsLocallyNoetherian A.A.left` using `LocallyOfFiniteType.isLocallyNoetherian A.A.hom`.

Establish `: CompactSpace A.A.left` using `QuasiCompact.compactSpace_of_compactSpace A.A.hom`. Establish `: IsNoetherian A.A.left` using `{}`. Use `infer_instance`. Set `ε : Fin 1 → ℤ` to `fun _ => (N : ℤ)`. Set `aM` to `pullOver A.L ε (π := π) (π' := π') (φ := fun _ => 𝟙 A.A.left) (φ' := fun _ => p) H.w (fun _ => (Category.comp_id _).symm)`.

Establish `hext : IsExtension aM` using `isExtension_pullOver H A.isLB ε _`. Establish `hσ : ∀ σ : Kb R →ₐ[FractionRing R] Kb R, spMap (σ : Kb R →+* Kb R) ≫ (TFK (R` using `R) (Kb R)).hom = (TFK (R := R) (Kb R)).hom := fun σ => by show Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]`. Set `m : (Kb R →ₐ[FractionRing R] Kb R) → ((TFK (R` to `R) (Kb R) ⊗ A.A).left ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left) := fun σ => ((Over.homMk (spMap (σ : Kb R →+* Kb R)) (hσ σ) : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R)) ▷ A.A).left`. Establish `hm₁ : ∀ σ, m σ ≫ π' = π' ≫ Spec.map (CommRingCat.ofHom (σ : Kb R →+* Kb R))` using `fun σ => by`.

Simplify using `only [m, π', ← Over.comp_left, whiskerRight_fst]`. Both sides reduce to the same expression. Establish `hm₂ : ∀ σ, m σ ≫ p = p` using `fun σ => by`. Simplify using `only [m, p, ← Over.comp_left, whiskerRight_snd]`. Set `g : ∀ σ : Kb R →ₐ[FractionRing R] Kb R, SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε) →ₛₗ[(σ : Kb R →+* Kb R)] SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε)` to `fun σ => pullOver A.L ε (π := π') (π' := π') (p := m σ) (φ := fun _ => p) (φ' := fun _ => p) (hm₁ σ) (fun _ => (hm₂ σ).symm)`.

Establish `hg : ∀ σ v, g σ (aM v) = aM v` using `fun σ v => sec_ext' A.isLB fun y J hJ => by`. Rewrite using `[sval_pullOver (hm₁ σ) (fun _ => (hm₂ σ).symm) _ _ hJ, sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ, sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ, Category.assoc, hm₂]`. Set `T' : Ix → SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε)` to `T`. Establish `hsmul : ∀ (c : Kb R) (s t : SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε)), (∀ j, t.f j = liftFun A.A _ (fnF (Kb R) c) * s.f j) → t = c • s` using `fun c s t ht => SecOver.ext _ _ fun j => (ht j).trans rfl`. Establish `hT' : ∀ σ i, g σ (T' i) = ((a σ : (Kb R)ˣ) : Kb R) • T' i` using `fun σ i => by`.

Take `⟨t', htw, ht'⟩` from `hT σ i`. Rewrite using `[← hsmul _ _ t' ht']`. Use `sec_ext' A.isLB fun y J hJ => ?_` and prove the remaining obligations. Rewrite using `[sval_pullOver (hm₁ σ) (fun _ => (hm₂ σ).symm) _ _ hJ]`. Use `(htw _ (𝟙 _) (𝟙 _ ≫ m σ) (by rw [Category.assoc, hm₂]) ?_ y J hJ).symm` and prove the remaining obligations.

Rewrite using `[Category.assoc, hm₁, Category.id_comp, Category.id_comp]`. Both sides reduce to the same expression. Take `⟨u, hu⟩` from `exists_scale hext g hg T' a hT'`. Use `⟨u, fun i => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `hu i`.

Use `⟨v, fun t'' ht'' => ?_⟩` and prove the remaining obligations. Establish `e : t'' = aM v` using `(hsmul _ (T' i) t'' ht'').trans hv.symm`. Introduce `Z q q' hq z J hJ`. Rewrite using `[show t'' = aM v from e, sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ, hq, Category.comp_id]`.
-/
theorem exists_common_scale_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))) (N : ℕ) (Ix : Type) (T : Ix → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) (a : (Kb R →ₐ[FractionRing R] Kb R) → (Kb R)ˣ), (∀ σ i, ∃ t', SecTw σ (T i) t' ∧ ∀ j, t'.f j = liftFun A.A _ (fnF (Kb R) (a σ).val) * (T i).f j) → ∃ c : (Kb R)ˣ, ∀ i, ∃ Φ : H0 A.L N, ∀ t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N, (∀ j, t''.f j = liftFun A.A _ (fnF (Kb R) c.val) * (T i).f j) → Agree A.L t'' Φ := by
  intro R _ _ _ hB A N Ix T a hT
  haveI : CharZero R := hB.2
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  let π : A.A.left ⟶ Spec (CommRingCat.of (FractionRing R)) := A.A.hom
  let π' := (fst (TFK (R := R) (Kb R)) A.A).left
  let p := (snd (TFK (R := R) (Kb R)) A.A).left
  have H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R)))) :=
    (IsPullback.of_hasPullback _ _).flip
  haveI : TopologicalSpace.NoetherianSpace A.A.left := by
    have := A.isAb.proper
    have : IsLocallyNoetherian A.A.left := LocallyOfFiniteType.isLocallyNoetherian A.A.hom
    have : CompactSpace A.A.left := QuasiCompact.compactSpace_of_compactSpace A.A.hom
    have : IsNoetherian A.A.left := {}
    infer_instance
  let ε : Fin 1 → ℤ := fun _ => (N : ℤ)
  let aM := pullOver A.L ε (π := π) (π' := π') (φ := fun _ => 𝟙 A.A.left) (φ' := fun _ => p) H.w
    (fun _ => (Category.comp_id _).symm)
  have hext : IsExtension aM := isExtension_pullOver H A.isLB ε _

  have hσ : ∀ σ : Kb R →ₐ[FractionRing R] Kb R, spMap (σ : Kb R →+* Kb R) ≫ (TFK (R := R) (Kb R)).hom =
      (TFK (R := R) (Kb R)).hom := fun σ => by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
  let m : (Kb R →ₐ[FractionRing R] Kb R) → ((TFK (R := R) (Kb R) ⊗ A.A).left ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left) :=
    fun σ => ((Over.homMk (spMap (σ : Kb R →+* Kb R)) (hσ σ) : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R)) ▷ A.A).left
  have hm₁ : ∀ σ, m σ ≫ π' = π' ≫ Spec.map (CommRingCat.ofHom (σ : Kb R →+* Kb R)) := fun σ => by
    simp only [m, π', ← Over.comp_left, whiskerRight_fst]; rfl
  have hm₂ : ∀ σ, m σ ≫ p = p := fun σ => by
    simp only [m, p, ← Over.comp_left, whiskerRight_snd]
  let g : ∀ σ : Kb R →ₐ[FractionRing R] Kb R, SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε) →ₛₗ[(σ : Kb R →+* Kb R)]
      SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε) :=
    fun σ => pullOver A.L ε (π := π') (π' := π') (p := m σ) (φ := fun _ => p) (φ' := fun _ => p) (hm₁ σ)
      (fun _ => (hm₂ σ).symm)

  have hg : ∀ σ v, g σ (aM v) = aM v := fun σ v => sec_ext' A.isLB fun y J hJ => by
    rw [sval_pullOver (hm₁ σ) (fun _ => (hm₂ σ).symm) _ _ hJ, sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ,
      sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ, Category.assoc, hm₂]
  let T' : Ix → SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε) := T

  have hsmul : ∀ (c : Kb R) (s t : SecOver π' (LB.LinComb A.L (fun _ : Fin 1 => p) ε)),
      (∀ j, t.f j = liftFun A.A _ (fnF (Kb R) c) * s.f j) → t = c • s := fun c s t ht =>
    SecOver.ext _ _ fun j => (ht j).trans rfl
  have hT' : ∀ σ i, g σ (T' i) = ((a σ : (Kb R)ˣ) : Kb R) • T' i :=
    fun σ i => by
    obtain ⟨t', htw, ht'⟩ := hT σ i
    rw [← hsmul _ _ t' ht']
    refine sec_ext' A.isLB fun y J hJ => ?_
    rw [sval_pullOver (hm₁ σ) (fun _ => (hm₂ σ).symm) _ _ hJ]
    refine (htw _ (𝟙 _) (𝟙 _ ≫ m σ) (by rw [Category.assoc, hm₂]) ?_ y J hJ).symm
    rw [Category.assoc, hm₁, Category.id_comp, Category.id_comp]; rfl
  obtain ⟨u, hu⟩ := exists_scale hext g hg T' a hT'
  refine ⟨u, fun i => ?_⟩
  obtain ⟨v, hv⟩ := hu i
  refine ⟨v, fun t'' ht'' => ?_⟩
  have e : t'' = aM v := (hsmul _ (T' i) t'' ht'').trans hv.symm
  intro Z q q' hq z J hJ
  rw [show t'' = aM v from e, sval_pullOver H.w (fun _ => (Category.comp_id _).symm) _ _ hJ, hq, Category.comp_id]

end GlobalTheory.Mum
