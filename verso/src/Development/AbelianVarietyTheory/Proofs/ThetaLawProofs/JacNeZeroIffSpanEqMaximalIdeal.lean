import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet

noncomputable section

namespace GlobalTheory.JacGen

section Algebra

open IsLocalRing

/- English proof (translation)
Establish `hker : RingHom.ker u = maximalIdeal S` using `eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective u fun a => ⟨algebraMap K S a, u.commutes a⟩)`. Establish `hmem : ∀ a, a ∈ maximalIdeal S ↔ u a = 0` using `fun a => by rw [← hker, RingHom.mem_ker]`. Establish `hsub : ∀ a, a - algebraMap K S (u a) ∈ maximalIdeal S` using `fun a => by`. Simplify using `[hmem]`. Establish `hle : Ideal.span (Set.range f) ≤ maximalIdeal S` using `Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (hmem _).2 (hf i))`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `le_antisymm hle (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun a ha => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Take `⟨l, hl, hl0⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem (p := (Ideal.span (Set.range f) ⊔ maximalIdeal S • maximalIdeal S).restrictScalars K) hn inferInstance`.

Establish `hz : ∀ b ∈ Ideal.span (Set.range f) ⊔ maximalIdeal S • maximalIdeal S, l b = 0` using `fun b hb => (Submodule.mem_bot K).1 (hl0 ▸ Submodule.mem_map_of_mem hb)`. Set `δ : S →ₗ[K] K` to `l ∘ₗ (LinearMap.id - (Algebra.linearMap K S ∘ₗ u.toLinearMap))`. Establish `hδ : ∀ b, δ b = l (b - algebraMap K S (u b))` using `fun b => rfl`. Take `⟨c, hc⟩` from `hsurj δ fun a b => by`. Establish `h0` using `hz _ (Submodule.mem_sup_right (Submodule.smul_mem_smul (hsub a) (hsub b)))`.

Rewrite using `[hδ, hδ, hδ, ← smul_eq_mul (u a), ← smul_eq_mul (u b), ← map_smul, ← map_smul, ← map_add, ← sub_eq_zero, ← map_sub, ← h0]`. Use `congr 1`. Rewrite using `[smul_eq_mul]`. Simplify using `only [Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hc0 : c = 0` using `Matrix.eq_zero_of_mulVec_eq_zero h (funext fun i => by`. Use `hc (f i)` as an intermediate fact. Rewrite `this` using `[hδ, hf, map_zero, sub_zero, hz _ (Submodule.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))]`. Conclude with `this.symm)`. Use `hc a` as an intermediate fact.

Rewrite `this` using `[hδ, (hmem a).1 ha, map_zero, sub_zero, hc0]`. Conclude with `hl (by simpa using this)`. Introduce `h h0`. Take `⟨c, hc, hc0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Use `hc (hinj c fun a => ?_)` and prove the remaining obligations.

Establish `h1 : ∀ k, D k 1 = 0` using `fun k => by simpa using hD k 1 1`. Establish `key : ∀ b ∈ Ideal.span (Set.range f), ∑ k, D k b * c k = 0` using `fun b hb => by`. Take `⟨r, rfl⟩` from `Ideal.mem_span_range_iff_exists_fun.1 hb`. Simplify using `only [map_sum, hD, hf, zero_mul, add_zero, Finset.sum_mul, mul_assoc]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`. Conclude with `mul_eq_zero_of_right _ (congrFun hc0 i)`. Use `key _ (h ▸ hsub a)` as an intermediate fact. Simplify `this` using `[Algebra.algebraMap_eq_smul_one, h1]`.
-/
theorem det_ne_zero_iff_span_eq {K S : Type} [Field K] [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra K S] {n : ℕ} (u : S →ₐ[K] K) (D : Fin n → S →ₗ[K] K)
    (hD : ∀ k a b, D k (a * b) = u a * D k b + u b * D k a)
    (hinj : ∀ c : Fin n → K, (∀ a, ∑ k, D k a * c k = 0) → c = 0)
    (hsurj : ∀ δ : S →ₗ[K] K, (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
      ∃ c : Fin n → K, ∀ a, δ a = ∑ k, D k a * c k)
    (f : Fin n → S) (hf : ∀ i, u (f i) = 0) :
    (Matrix.of fun i k => D k (f i)).det ≠ 0 ↔ Ideal.span (Set.range f) = maximalIdeal S := by
  have hker : RingHom.ker u = maximalIdeal S := eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective u fun a => ⟨algebraMap K S a, u.commutes a⟩)
  have hmem : ∀ a, a ∈ maximalIdeal S ↔ u a = 0 := fun a => by rw [← hker, RingHom.mem_ker]
  have hsub : ∀ a, a - algebraMap K S (u a) ∈ maximalIdeal S := fun a => by
    simp [hmem]
  have hle : Ideal.span (Set.range f) ≤ maximalIdeal S :=
    Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (hmem _).2 (hf i))
  constructor
  · intro h
    refine le_antisymm hle (Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun a ha => ?_)
    by_contra hn
    obtain ⟨l, hl, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
      (p := (Ideal.span (Set.range f) ⊔ maximalIdeal S • maximalIdeal S).restrictScalars K) hn inferInstance
    have hz : ∀ b ∈ Ideal.span (Set.range f) ⊔ maximalIdeal S • maximalIdeal S, l b = 0 := fun b hb =>
      (Submodule.mem_bot K).1 (hl0 ▸ Submodule.mem_map_of_mem hb)
    let δ : S →ₗ[K] K := l ∘ₗ (LinearMap.id - (Algebra.linearMap K S ∘ₗ u.toLinearMap))
    have hδ : ∀ b, δ b = l (b - algebraMap K S (u b)) := fun b => rfl
    obtain ⟨c, hc⟩ := hsurj δ fun a b => by
      have h0 := hz _ (Submodule.mem_sup_right (Submodule.smul_mem_smul (hsub a) (hsub b)))
      rw [hδ, hδ, hδ, ← smul_eq_mul (u a), ← smul_eq_mul (u b), ← map_smul, ← map_smul, ← map_add,
        ← sub_eq_zero, ← map_sub, ← h0]
      congr 1
      rw [smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      ring
    have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero h (funext fun i => by
      have := hc (f i)
      rw [hδ, hf, map_zero, sub_zero,
        hz _ (Submodule.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))] at this
      exact this.symm)
    have := hc a
    rw [hδ, (hmem a).1 ha, map_zero, sub_zero, hc0] at this
    exact hl (by simpa using this)
  · intro h h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine hc (hinj c fun a => ?_)
    have h1 : ∀ k, D k 1 = 0 := fun k => by simpa using hD k 1 1
    have key : ∀ b ∈ Ideal.span (Set.range f), ∑ k, D k b * c k = 0 := fun b hb => by
      obtain ⟨r, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
      simp only [map_sum, hD, hf, zero_mul, add_zero, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.mul_sum]
      exact mul_eq_zero_of_right _ (congrFun hc0 i)
    have := key _ (h ▸ hsub a)
    simpa [Algebra.algebraMap_eq_smul_one, h1] using this

end Algebra

section Group

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))}

/- English proof (translation)
The claim follows from `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] exact isUnit_or_isUnit_one_sub_self _`.
-/
theorem isLocalRing_trivSqZeroExt (n : ℕ) : IsLocalRing (TrivSqZeroExt K (Fin n → K)) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : G.left.presheaf.stalk y ⟶ .of T, Spec.map φ ≫ G.left.fromSpecStalk y = w.left := by`. Substitute `hw` using the available equality. Conclude with `⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of T) w.left⟩`. Establish `h : CommRingCat.ofHom (algebraMap K (G.left.presheaf.stalk y)) ≫ φ = CommRingCat.ofHom (algebraMap K T)`. Apply `Spec.map_injective` to reduce the goal to its premises.

Establish `h1` using `Over.w j`. Establish `h2` using `Over.w w`. Rewrite `h1` using `[hj]`. Rewrite `h2` using `[← hφ]`. Rewrite using `[Spec.map_comp]`.

Conclude with `(congrArg (Spec.map φ ≫ ·) h1.symm).trans ((Category.assoc _ _ _).symm.trans h2)`. Use `⟨{ φ.hom with commutes' := fun a => congrArg (fun q => q.hom a) h }, ?_⟩` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, hj]`. Conclude with `hφ`.
-/
theorem exists_factor {y : G.left} [Algebra K (G.left.presheaf.stalk y)]
    (j : sp (R₀ := K) (G.left.presheaf.stalk y) ⟶ G) (hj : j.left = G.left.fromSpecStalk y)
    {T : Type} [CommRing T] [IsLocalRing T] [Algebra K T] (w : sp (R₀ := K) T ⟶ G)
    (hw : w.left (closedPoint T) = y) : ∃ φ : G.left.presheaf.stalk y →ₐ[K] T, spMap φ ≫ j = w := by
  obtain ⟨φ, hφ⟩ : ∃ φ : G.left.presheaf.stalk y ⟶ .of T, Spec.map φ ≫ G.left.fromSpecStalk y = w.left := by
    subst hw
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of T) w.left⟩
  have h : CommRingCat.ofHom (algebraMap K (G.left.presheaf.stalk y)) ≫ φ =
      CommRingCat.ofHom (algebraMap K T) := by
    apply Spec.map_injective
    have h1 := Over.w j
    have h2 := Over.w w
    rw [hj] at h1
    rw [← hφ] at h2
    rw [Spec.map_comp]
    exact (congrArg (Spec.map φ ≫ ·) h1.symm).trans ((Category.assoc _ _ _).symm.trans h2)
  refine ⟨{ φ.hom with commutes' := fun a => congrArg (fun q => q.hom a) h }, ?_⟩
  apply Over.OverMorphism.ext
  rw [Over.comp_left, hj]
  exact hφ

variable [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR K ⟶ G)}

/- English proof (translation)
Establish `inj : ∀ {T : Type} [CommRing T] [Algebra K T] (φ ψ : S →ₐ[K] T), spMap φ ≫ j = spMap ψ ≫ j → φ = ψ`. Introduce `T _ _ φ ψ h`. Establish `h1` using `Spec.map_injective (congrArg (·.left) ((cancel_mono j).1 h))`. Conclude with `AlgHom.ext fun a => congrArg (fun q => q.hom a) h1`. Establish `hz : ∀ {T T' : Type} [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T'] (φ : T →ₐ[K] T'), spMap φ ≫ toUnit _ ≫ z = toUnit _ ≫ z` using `fun φ => by`.

Rewrite using `[← Category.assoc, comp_toUnit]`. Establish `hfst : ∀ a, (χ a).fst = u a`. Use `AlgHom.congr_fun (inj ((TrivSqZeroExt.fstHom K K _).comp χ) u ?_)` and prove the remaining obligations. Rewrite using `[← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp, lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, hu]`. Set `φ : (Fin n → K) → (S →ₐ[K] DualNumber K)` to `fun c => (vecTo (inlS K K) (fun i => inr (c i)) (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ`.

Establish `hφ : ∀ c, spMap (φ c) ≫ j = (toUnit _ ≫ z) * tanExp v c` using `fun c => by`. Rewrite using `[← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp]`. Conclude with `congrArg _ (lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _)`. Establish `hφ1 : ∀ c a, (φ c a).fst = u a` using `fun c a => by`. Simplify using `[φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]`.

Establish `hφ2 : ∀ c a, (φ c a).snd = ∑ k, (χ a).snd k * c k` using `fun c a => by`. Simplify using `[φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]`. Take `⟨hinj, hsurj⟩` from `isLieBasisOver_self hv`. Use `⟨fun k => LinearMap.proj k ∘ₗ TrivSqZeroExt.sndHom K _ ∘ₗ χ.toLinearMap, fun k a b => ?_, fun c hc => hinj _ _ ?_, fun δ hδ => ?_, fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩` and prove the remaining obligations. Simplify using `[hfst]`.

Establish `: φ c = φ 0` using `AlgHom.ext fun a => TrivSqZeroExt.ext (by rw [hφ1, hφ1]) (by`. Rewrite using `[hφ2, hφ2]`. Simplify using `using hc a)`. Conclude with `mul_left_cancel ((hφ c).symm.trans (this ▸ hφ 0))`. Apply the tactic sequence `let ψ : S →ₐ[K] DualNumber K := addDer ((inlS K K).comp u) (TrivSqZeroExt.inrHom K K ∘ₗ δ) (fun a b => by ext <;> simp [hδ, mul_comm]) (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)`.

Establish `h1 : (fstS K K).comp ψ = u` using `AlgHom.ext fun a => add_zero (u a)`. Take `⟨c, hc⟩` from `hsurj ((toUnit _ ≫ z)⁻¹ * (spMap ψ ≫ j)) (by`. Rewrite using `[IsTanOver, MonObj.comp_mul, GrpObj.comp_inv, hz, ← Category.assoc, spMap_comp, h1, hu, inv_mul_cancel])`. Establish `h2 : ψ = φ c` using `inj _ _ (by rw [hφ, ← hc, mul_inv_cancel_left])`. Use `⟨c, fun a => ?_⟩` and prove the remaining obligations.

Use `hφ2 c a` as an intermediate fact. Rewrite `this` using `[← h2]`. Conclude with `(zero_add (δ a)).symm.trans this`. Rewrite using `[hφ, tanExp_single hv.1]`. Rewrite using `[hφ2]`.

Simplify using `[Pi.single_apply]`.
-/
theorem exists_derivations (hv : IsLieBasis v) {S : Type} [CommRing S] [Algebra K S] (j : sp (R₀ := K) S ⟶ G)
    [Mono j] (z : 𝟙_ _ ⟶ G) (u : S →ₐ[K] K) (hu : spMap u ≫ j = toUnit _ ≫ z)
    (χ : S →ₐ[K] TrivSqZeroExt K (Fin n → K))
    (hχ : spMap χ ≫ j = (toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    ∃ D : Fin n → S →ₗ[K] K, (∀ k a b, D k (a * b) = u a * D k b + u b * D k a) ∧
      (∀ c : Fin n → K, (∀ a, ∑ k, D k a * c k = 0) → c = 0) ∧
      (∀ δ : S →ₗ[K] K, (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
        ∃ c : Fin n → K, ∀ a, δ a = ∑ k, D k a * c k) ∧
      ∀ k, ∃ φ : S →ₐ[K] DualNumber K, spMap φ ≫ j = (toUnit _ ≫ z) * v k ∧ ∀ a, (φ a).snd = D k a := by
  have inj : ∀ {T : Type} [CommRing T] [Algebra K T] (φ ψ : S →ₐ[K] T), spMap φ ≫ j = spMap ψ ≫ j → φ = ψ := by
    intro T _ _ φ ψ h
    have h1 := Spec.map_injective (congrArg (·.left) ((cancel_mono j).1 h))
    exact AlgHom.ext fun a => congrArg (fun q => q.hom a) h1
  have hz : ∀ {T T' : Type} [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T'] (φ : T →ₐ[K] T'),
      spMap φ ≫ toUnit _ ≫ z = toUnit _ ≫ z := fun φ => by
    rw [← Category.assoc, comp_toUnit]
  have hfst : ∀ a, (χ a).fst = u a := by
    refine AlgHom.congr_fun (inj ((TrivSqZeroExt.fstHom K K _).comp χ) u ?_)
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp,
      lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, hu]
  let φ : (Fin n → K) → (S →ₐ[K] DualNumber K) := fun c => (vecTo (inlS K K) (fun i => inr (c i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = (toUnit _ ≫ z) * tanExp v c := fun c => by
    rw [← spMap_comp, Category.assoc, hχ, MonObj.comp_mul, hz, comp_lieExp]
    exact congrArg _ (lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _)
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, (χ a).snd k * c k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  obtain ⟨hinj, hsurj⟩ := isLieBasisOver_self hv
  refine ⟨fun k => LinearMap.proj k ∘ₗ TrivSqZeroExt.sndHom K _ ∘ₗ χ.toLinearMap, fun k a b => ?_,
    fun c hc => hinj _ _ ?_, fun δ hδ => ?_, fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · simp [hfst]
  · have : φ c = φ 0 := AlgHom.ext fun a => TrivSqZeroExt.ext (by rw [hφ1, hφ1]) (by
      rw [hφ2, hφ2]
      simpa using hc a)
    exact mul_left_cancel ((hφ c).symm.trans (this ▸ hφ 0))
  · let ψ : S →ₐ[K] DualNumber K := addDer ((inlS K K).comp u) (TrivSqZeroExt.inrHom K K ∘ₗ δ)
      (fun a b => by ext <;> simp [hδ, mul_comm]) (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
    have h1 : (fstS K K).comp ψ = u := AlgHom.ext fun a => add_zero (u a)
    obtain ⟨c, hc⟩ := hsurj ((toUnit _ ≫ z)⁻¹ * (spMap ψ ≫ j)) (by
      rw [IsTanOver, MonObj.comp_mul, GrpObj.comp_inv, hz, ← Category.assoc, spMap_comp, h1, hu,
        inv_mul_cancel])
    have h2 : ψ = φ c := inj _ _ (by rw [hφ, ← hc, mul_inv_cancel_left])
    refine ⟨c, fun a => ?_⟩
    have := hφ2 c a
    rw [← h2] at this
    exact (zero_add (δ a)).symm.trans this
  · rw [hφ, tanExp_single hv.1]
  · rw [hφ2]
    simp [Pi.single_apply]

/- English proof (translation)
Establish `ht : ⊤ ≤ X.fromSpecStalk y ⁻¹ᵁ U` using `(Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecStalk y) (by rwa [Scheme.fromSpecStalk_closedPoint])).ge`. Establish `ht' : ⊤ ≤ (Spec.map φ ≫ X.fromSpecStalk y) ⁻¹ᵁ U` using `fun q _ => ht (x := Spec.map φ q) trivial`. Use `(dif_pos ht').trans ?_` and prove the remaining obligations. Establish `h1 : (X.fromSpecStalk y).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (X.presheaf.stalk y)).hom = X.presheaf.germ U y hy`. Rewrite using `[Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]`.

Simplify using `only [Category.assoc]`. Establish `e : (Spec (X.presheaf.stalk y)).presheaf.map (homOfLE (le_top : X.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op ≫ (Spec (X.presheaf.stalk y)).presheaf.map (homOfLE ht).op = 𝟙 _`. Rewrite using `[← Functor.map_comp]`. Conclude with `CategoryTheory.Functor.map_id _ _`. Rewrite using `[reassoc_of% e, Iso.inv_hom_id, Category.comp_id]`.

Establish `h2 : (Spec.map φ ≫ X.fromSpecStalk y).appLE U ⊤ ht' ≫ (Scheme.ΓSpecIso (.of T)).hom = X.presheaf.germ U y hy ≫ φ`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE (Spec.map φ) _ U ⊤ ⊤ ht le_top, ← h1, Category.assoc, Category.assoc, ← Scheme.ΓSpecIso_naturality]`. Use `congr 2`. Conclude with `congrArg (fun q => q.hom f) h2`.
-/
theorem valT_specMap_fromSpecStalk {X : Scheme.{0}} {y : X} {U : X.Opens} (hy : y ∈ U) {T : Type} [CommRing T]
    (φ : X.presheaf.stalk y ⟶ .of T) (f : Γ(X, U)) :
    KeyKa.valT (T := T) (Spec.map φ ≫ X.fromSpecStalk y) U f = φ.hom ((X.presheaf.germ U y hy).hom f) := by
  have ht : ⊤ ≤ X.fromSpecStalk y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecStalk y)
    (by rwa [Scheme.fromSpecStalk_closedPoint])).ge
  have ht' : ⊤ ≤ (Spec.map φ ≫ X.fromSpecStalk y) ⁻¹ᵁ U := fun q _ => ht (x := Spec.map φ q) trivial
  refine (dif_pos ht').trans ?_
  have h1 : (X.fromSpecStalk y).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (X.presheaf.stalk y)).hom =
      X.presheaf.germ U y hy := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
    simp only [Category.assoc]
    have e : (Spec (X.presheaf.stalk y)).presheaf.map (homOfLE (le_top : X.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (X.presheaf.stalk y)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  have h2 : (Spec.map φ ≫ X.fromSpecStalk y).appLE U ⊤ ht' ≫ (Scheme.ΓSpecIso (.of T)).hom =
      X.presheaf.germ U y hy ≫ φ := by
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) _ U ⊤ ⊤ ht le_top, ← h1, Category.assoc, Category.assoc,
      ← Scheme.ΓSpecIso_naturality]
    congr 2
  exact congrArg (fun q => q.hom f) h2

/- English proof (translation)
Establish `: IsLocallyNoetherian G.left` using `LocallyOfFiniteType.isLocallyNoetherian G.hom`. Use `letI : Algebra K (G.left.presheaf.stalk (z.left p)) := (Spec.preimage (G.left.fromSpecStalk (z.left p) ≫ G.hom)).hom.toAlgebra`. Set `j : sp (R₀` to `K) (G.left.presheaf.stalk (z.left p)) ⟶ G := Over.homMk (G.left.fromSpecStalk (z.left p)) (Spec.map_preimage _).symm`. Establish `: Mono j.left` using `inferInstanceAs (Mono (G.left.fromSpecStalk (z.left p)))`. Establish `: Mono j` using `Over.mono_of_mono_left j`.

Establish `hpt : ∀ {T : Over (Sp K)} (t : T.left), (toUnit T ≫ z).left t = z.left p` using `fun {T} t => congrArg z.left (Subsingleton.elim (α := PrimeSpectrum K) _ _)`. Take `⟨u, hu⟩` from `exists_factor j rfl (T := K) (toUnit _ ≫ z) (hpt _)`. Use `isLocalRing_trivSqZeroExt (K := K) n` as an intermediate fact. Take `⟨χ, hχ⟩` from `exists_factor j rfl (T := TrivSqZeroExt K (Fin n → K)) ((toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) (by`. Establish `h1 : IsLocalHom (TrivSqZeroExt.fstHom K K (Fin n → K)).toRingHom` using `⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩`.

Establish `h2 : spMap (TrivSqZeroExt.fstHom K K (Fin n → K)) ≫ ((toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) = toUnit _ ≫ z`. Rewrite using `[MonObj.comp_mul, comp_lieExp, lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, ← Category.assoc, comp_toUnit]`. Rewrite using `[← comap_closedPoint (TrivSqZeroExt.fstHom K K (Fin n → K)).toRingHom, ← hpt (T := sp (R₀ := K) K) (closedPoint K), ← h2]`. Use the proof step `rfl)`. Take `⟨D, h1, h2, h3, h4⟩` from `exists_derivations hv j z u hu χ hχ`.

Establish `hz : z.left = Spec.map (CommRingCat.ofHom u.toRingHom) ≫ G.left.fromSpecStalk (z.left p)`. Establish `h` using `congrArg (·.left) hu`. Establish `e : (toUnit (sp (R₀` using `K) K)).left = 𝟙 (Sp K) := by`. Rewrite using `[Over.toUnit_left]`. Conclude with `Spec.map_id _`.

Use `Eq.trans ?_ h.symm` and prove the remaining obligations. Rewrite using `[Over.comp_left, e]`. Conclude with `(Category.id_comp _).symm`. Rewrite using `[← det_ne_zero_iff_span_eq u D h1 h2 h3 _ fun i => (valT_specMap_fromSpecStalk hU _ (f i)).symm.trans ((congrArg (KeyKa.valT (T := K) · U (f i)) hz.symm).trans (hf i))]`. Use `iff_of_eq (congrArg (fun M : Matrix (Fin n) (Fin n) K => M.det ≠ 0) (Matrix.ext fun i k => ?_))` and prove the remaining obligations.

Take `⟨φ, hφ, hD⟩` from `h4 k`. Rewrite using `[Matrix.of_apply, Matrix.of_apply, ← hD]`. Use `congrArg TrivSqZeroExt.snd ?_` and prove the remaining obligations. Conclude with `(congrArg (fun w : epsR K ⟶ G => KeyKa.valT (T := DualNumber K) w.left U (f i)) hφ.symm).trans (valT_specMap_fromSpecStalk hU (CommRingCat.ofHom φ.toRingHom) (f i))`.
-/
theorem det_ne_zero_iff_span_germ_eq [LocallyOfFiniteType G.hom] (hv : IsLieBasis v) (z : 𝟙_ _ ⟶ G) (p : Sp K)
    {U : G.left.Opens} (hU : z.left p ∈ U) (f : Fin n → Γ(G.left, U))
    (hf : ∀ i, KeyKa.valT (T := K) z.left U (f i) = 0) :
    (Matrix.of fun i k => (KeyKa.valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * v k).left U (f i)).snd).det ≠ 0 ↔
      Ideal.span (Set.range fun i => (G.left.presheaf.germ U _ hU).hom (f i)) =
        maximalIdeal (G.left.presheaf.stalk (z.left p)) := by
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  letI : Algebra K (G.left.presheaf.stalk (z.left p)) :=
    (Spec.preimage (G.left.fromSpecStalk (z.left p) ≫ G.hom)).hom.toAlgebra
  let j : sp (R₀ := K) (G.left.presheaf.stalk (z.left p)) ⟶ G :=
    Over.homMk (G.left.fromSpecStalk (z.left p)) (Spec.map_preimage _).symm
  have : Mono j.left := inferInstanceAs (Mono (G.left.fromSpecStalk (z.left p)))
  have : Mono j := Over.mono_of_mono_left j
  have hpt : ∀ {T : Over (Sp K)} (t : T.left), (toUnit T ≫ z).left t = z.left p := fun {T} t =>
    congrArg z.left (Subsingleton.elim (α := PrimeSpectrum K) _ _)
  obtain ⟨u, hu⟩ := exists_factor j rfl (T := K) (toUnit _ ≫ z) (hpt _)
  have := isLocalRing_trivSqZeroExt (K := K) n
  obtain ⟨χ, hχ⟩ := exists_factor j rfl (T := TrivSqZeroExt K (Fin n → K))
    ((toUnit _ ≫ z) * lieExp v (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) (by
      have h1 : IsLocalHom (TrivSqZeroExt.fstHom K K (Fin n → K)).toRingHom :=
        ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
      have h2 : spMap (TrivSqZeroExt.fstHom K K (Fin n → K)) ≫ ((toUnit _ ≫ z) * lieExp v
          (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) = toUnit _ ≫ z := by
        rw [MonObj.comp_mul, comp_lieExp, lieExp_eq_one hv.1 _ (fun i => by rfl), mul_one, ← Category.assoc,
          comp_toUnit]
      rw [← comap_closedPoint (TrivSqZeroExt.fstHom K K (Fin n → K)).toRingHom, ← hpt (T := sp (R₀ := K) K) (closedPoint K), ← h2]
      rfl)
  obtain ⟨D, h1, h2, h3, h4⟩ := exists_derivations hv j z u hu χ hχ
  have hz : z.left = Spec.map (CommRingCat.ofHom u.toRingHom) ≫ G.left.fromSpecStalk (z.left p) := by
    have h := congrArg (·.left) hu
    have e : (toUnit (sp (R₀ := K) K)).left = 𝟙 (Sp K) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    refine Eq.trans ?_ h.symm
    rw [Over.comp_left, e]
    exact (Category.id_comp _).symm
  rw [← det_ne_zero_iff_span_eq u D h1 h2 h3 _ fun i =>
    (valT_specMap_fromSpecStalk hU _ (f i)).symm.trans ((congrArg (KeyKa.valT (T := K) · U (f i)) hz.symm).trans (hf i))]
  refine iff_of_eq (congrArg (fun M : Matrix (Fin n) (Fin n) K => M.det ≠ 0) (Matrix.ext fun i k => ?_))
  obtain ⟨φ, hφ, hD⟩ := h4 k
  rw [Matrix.of_apply, Matrix.of_apply, ← hD]
  refine congrArg TrivSqZeroExt.snd ?_
  exact (congrArg (fun w : epsR K ⟶ G => KeyKa.valT (T := DualNumber K) w.left U (f i)) hφ.symm).trans
    (valT_specMap_fromSpecStalk hU (CommRingCat.ofHom φ.toRingHom) (f i))

end Group

end GlobalTheory.JacGen

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

/- English proof (translation)
Introduce `K _ x n s z c p hc hs`. Use `x.P.smoothDim` as an intermediate fact. Establish `: Smooth x.P.A.hom` using `SmoothOfRelativeDimension.smooth x.P.g _`. Establish `hU : z.left p ∈ x.P.L.U c` using `hc (x := p) trivial`. Use `(GlobalTheory.JacGen.det_ne_zero_iff_span_germ_eq x.basis z p hU (fun i => (s i).f c) hs).trans ?_` and prove the remaining obligations.

Use `iff_of_eq (congrArg (fun F => Ideal.span (Set.range F) = _) (funext fun i => ?_))` and prove the remaining obligations. Conclude with `(gs_eq (𝟙 _) _ _ hU _).symm`.
-/
theorem GlobalTheory.KeyKa.jac_ne_zero_iff_span_eq_maximalIdeal : ∀ (K : Type) [Field K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n) (z : Pt x) (c : x.P.L.ι) (p : Sp K), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0) → (jac x s z c ≠ 0 ↔ Ideal.span (Set.range fun i => gs (𝟙 _) (z.left p) (x.P.L.U c) ((s i).f c)) = IsLocalRing.maximalIdeal (x.P.A.left.presheaf.stalk (z.left p))) := by
  intro K _ x n s z c p hc hs
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  have hU : z.left p ∈ x.P.L.U c := hc (x := p) trivial
  refine (GlobalTheory.JacGen.det_ne_zero_iff_span_germ_eq x.basis z p hU (fun i => (s i).f c) hs).trans ?_
  refine iff_of_eq (congrArg (fun F => Ideal.span (Set.range F) = _) (funext fun i => ?_))
  exact (gs_eq (𝟙 _) _ _ hU _).symm

end
