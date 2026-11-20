import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteOfIsClosedSplitTorusOfPowEqOne

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionLift

/- English proof (translation)
Take `⟨y, hy⟩` from `hf y₀`. Establish `hker : y ^ N ∈ f.ker`. Rewrite using `[MonoidHom.mem_ker, map_pow, hy, hy₀]`. Take `⟨z, hz⟩` from `hN.2 ⟨y ^ N, hker⟩`. Establish `hz' : (z : M) ^ N = y ^ N` using `congrArg Subtype.val hz`.

Establish `hfz : f z = 1` using `(MonoidHom.mem_ker).1 z.2`. Use `⟨y * (z : M)⁻¹, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, inv_pow, hz', mul_inv_cancel]`. Rewrite using `[map_mul, map_inv, hy, hfz, inv_one, _root_.mul_one]`. Introduce and unpack `w ⟨hw, hfw⟩`.

Establish `hmem : w * (y * (z : M)⁻¹)⁻¹ ∈ f.ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_inv, hfw, hy, hfz, inv_one, _root_.mul_one, mul_inv_cancel]`. Establish `h1 : (⟨_, hmem⟩ : f.ker) = 1`. Apply `hN.1` to reduce the goal to its premises. Use `show (⟨_, hmem⟩ : f.ker) ^ N = 1 ^ N`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [SubgroupClass.coe_pow, one_pow, OneMemClass.coe_one]`. Rewrite using `[mul_pow, inv_pow, hw, mul_pow, inv_pow, hz', mul_inv_cancel, inv_one, _root_.one_mul]`. Conclude with `mul_inv_eq_one.1 (congrArg Subtype.val h1)`.
-/
theorem existsUnique_of_ker {M M' : Type*} [CommGroup M] [CommGroup M'] (f : M →* M')
    (hf : Function.Surjective f) {N : ℕ} (hN : Function.Bijective fun z : f.ker => z ^ N)
    (y₀ : M') (hy₀ : y₀ ^ N = 1) : ∃! y, y ^ N = 1 ∧ f y = y₀ := by
  obtain ⟨y, hy⟩ := hf y₀
  have hker : y ^ N ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, hy, hy₀]
  obtain ⟨z, hz⟩ := hN.2 ⟨y ^ N, hker⟩
  have hz' : (z : M) ^ N = y ^ N := congrArg Subtype.val hz
  have hfz : f z = 1 := (MonoidHom.mem_ker).1 z.2
  refine ⟨y * (z : M)⁻¹, ⟨?_, ?_⟩, ?_⟩
  · rw [mul_pow, inv_pow, hz', mul_inv_cancel]
  · rw [map_mul, map_inv, hy, hfz, inv_one, _root_.mul_one]
  · rintro w ⟨hw, hfw⟩
    have hmem : w * (y * (z : M)⁻¹)⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_inv, hfw, hy, hfz, inv_one, _root_.mul_one,
        mul_inv_cancel]
    have h1 : (⟨_, hmem⟩ : f.ker) = 1 := by
      apply hN.1
      show (⟨_, hmem⟩ : f.ker) ^ N = 1 ^ N
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, one_pow, OneMemClass.coe_one]
      rw [mul_pow, inv_pow, hw, mul_pow, inv_pow, hz', mul_inv_cancel, inv_one, _root_.one_mul]
    exact mul_inv_eq_one.1 (congrArg Subtype.val h1)

variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  [IsCommMonObj G] [Smooth G.hom]

/- English proof (translation)
Take `⟨n, hn⟩` from `sqZero_reduction_of_isLocalRing (R := R) G`. Take `⟨⟨e⟩, hsurj, -⟩` from `hn A J hJ`. Establish `hbij : Function.Bijective fun c : Fin n → J => N • c`. Establish `h` using `MulAction.bijective (β := Fin n → J) hN.unit`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `c`. Rewrite using `[Units.smul_def, IsUnit.unit_spec, Nat.cast_smul_eq_nsmul]`. Establish `key : ∀ z : SqZero.redKer (R` using `R) G J, e (Additive.ofMul (z ^ N)) = N • e (Additive.ofMul z) := fun z => by`. Rewrite using `[ofMul_pow, map_nsmul]`. Establish `h` using `existsUnique_of_ker (SqZero.pointsMap G (Ideal.Quotient.mkₐ R J)) (fun z => by`.

Take `⟨y, hy⟩` from `hsurj z`. Conclude with `⟨y, by rw [SqZero.ptsMap_apply]; exact hy⟩)`. Use the proof step `(N := N) ?_ y₀ hy₀`. Simplify `h` using `only [SqZero.ptsMap_apply]`. Use `show Function.Bijective fun z : SqZero.redKer (R := R) G J => z ^ N`.

Use `⟨fun z w hzw => ?_, fun w => ?_⟩` and prove the remaining obligations. Establish `h1 : N • e (Additive.ofMul z) = N • e (Additive.ofMul w)`. Rewrite using `[← key, ← key]`. Conclude with `congrArg (fun u => e (Additive.ofMul u)) hzw`. Conclude with `Additive.ofMul.injective (e.injective (hbij.1 h1))`.

Take `⟨c, hc⟩` from `hbij.2 (e (Additive.ofMul w))`. Use `⟨Additive.toMul (e.symm c), ?_⟩` and prove the remaining obligations. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Apply `e.injective` to reduce the goal to its premises. Use `show e (Additive.ofMul (Additive.toMul (e.symm c) ^ N)) = _`.

Rewrite using `[key]`. Simplify using `using hc`.
-/
theorem existsUnique_quotient {A : Type} [CommRing A] [Algebra R A] (J : Ideal A) (hJ : J ^ 2 = ⊥)
    {N : ℕ} (hN : IsUnit (N : A)) (y₀ : sp (R₀ := R) (A ⧸ J) ⟶ G) (hy₀ : y₀ ^ N = 1) :
    ∃! y : sp A ⟶ G, y ^ N = 1 ∧ spMap (Ideal.Quotient.mkₐ R J) ≫ y = y₀ := by
  obtain ⟨n, hn⟩ := sqZero_reduction_of_isLocalRing (R := R) G
  obtain ⟨⟨e⟩, hsurj, -⟩ := hn A J hJ
  have hbij : Function.Bijective fun c : Fin n → J => N • c := by
    have h := MulAction.bijective (β := Fin n → J) hN.unit
    convert h using 1
    funext c
    rw [Units.smul_def, IsUnit.unit_spec, Nat.cast_smul_eq_nsmul]
  have key : ∀ z : SqZero.redKer (R := R) G J,
      e (Additive.ofMul (z ^ N)) = N • e (Additive.ofMul z) := fun z => by
    rw [ofMul_pow, map_nsmul]
  have h := existsUnique_of_ker (SqZero.pointsMap G (Ideal.Quotient.mkₐ R J))
    (fun z => by
      obtain ⟨y, hy⟩ := hsurj z
      exact ⟨y, by rw [SqZero.ptsMap_apply]; exact hy⟩)
    (N := N) ?_ y₀ hy₀
  · simpa only [SqZero.ptsMap_apply] using h
  · show Function.Bijective fun z : SqZero.redKer (R := R) G J => z ^ N
    refine ⟨fun z w hzw => ?_, fun w => ?_⟩
    · have h1 : N • e (Additive.ofMul z) = N • e (Additive.ofMul w) := by
        rw [← key, ← key]
        exact congrArg (fun u => e (Additive.ofMul u)) hzw
      exact Additive.ofMul.injective (e.injective (hbij.1 h1))
    · obtain ⟨c, hc⟩ := hbij.2 (e (Additive.ofMul w))
      refine ⟨Additive.toMul (e.symm c), ?_⟩
      apply Additive.ofMul.injective
      apply e.injective
      show e (Additive.ofMul (Additive.toMul (e.symm c) ^ N)) = _
      rw [key]
      simpa using hc

/- English proof (translation)
Establish `h1 : spMap (e.symm : B' →ₐ[R] B) ≫ spMap (e : B →ₐ[R] B') = 𝟙 _`. Rewrite using `[spMap_comp, AlgEquiv.symm_comp, spMap_id]`. Establish `h2 : spMap (e : B →ₐ[R] B') ≫ spMap (e.symm : B' →ₐ[R] B) = 𝟙 _`. Rewrite using `[spMap_comp, AlgEquiv.comp_symm, spMap_id]`. Rewrite using `[← spMap_comp, Category.assoc]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Rewrite using `[reassoc_of% h1]`. Introduce `h`. Rewrite using `[h, reassoc_of% h2]`.
-/
private theorem sp_comp_algEquiv_iff {A B B' : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing B'] [Algebra R B'] (e : B ≃ₐ[R] B') (φ : A →ₐ[R] B) (y : sp A ⟶ G)
    (z : sp (R₀ := R) B' ⟶ G) :
    spMap ((e : B →ₐ[R] B').comp φ) ≫ y = z ↔
      spMap φ ≫ y = spMap (e.symm : B' →ₐ[R] B) ≫ z := by
  have h1 : spMap (e.symm : B' →ₐ[R] B) ≫ spMap (e : B →ₐ[R] B') = 𝟙 _ := by
    rw [spMap_comp, AlgEquiv.symm_comp, spMap_id]
  have h2 : spMap (e : B →ₐ[R] B') ≫ spMap (e.symm : B' →ₐ[R] B) = 𝟙 _ := by
    rw [spMap_comp, AlgEquiv.comp_symm, spMap_id]
  rw [← spMap_comp, Category.assoc]
  constructor
  · rintro rfl
    rw [reassoc_of% h1]
  · intro h
    rw [h, reassoc_of% h2]

/- English proof (translation)
Rewrite using `[← SqZero.ptsMap_apply, ← map_pow, hz, map_one]`.
-/
private theorem sp_pow_comp_algHom {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (z : sp (R₀ := R) A ⟶ G) {N : ℕ} (hz : z ^ N = 1) : (spMap φ ≫ z) ^ N = 1 := by
  rw [← SqZero.ptsMap_apply, ← map_pow, hz, map_one]

/- English proof (translation)
Set `e : (A ⧸ RingHom.ker q) ≃ₐ[R] A'` to `Ideal.quotientKerAlgEquivOfSurjective hq`. Establish `he : (e : (A ⧸ RingHom.ker q) →ₐ[R] A').comp (Ideal.Quotient.mkₐ R (RingHom.ker q)) = q`. Use extensionality with `a`. Both sides reduce to the same expression. Take `⟨y, ⟨hy1, hy2⟩, huniq⟩` from `existsUnique_quotient G (RingHom.ker q) hJ hN _ (sp_pow_comp_algHom G (e.symm : A' →ₐ[R] A ⧸ RingHom.ker q) y₀ hy₀)`.

Use `⟨y, ⟨hy1, ?_⟩, fun y' ⟨h1, h2⟩ => huniq y' ⟨h1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← he]`. Conclude with `(sp_comp_algEquiv_iff G e _ y y₀).2 hy2`. Rewrite `h2` using `[← he]`. Conclude with `(sp_comp_algEquiv_iff G e _ y' y₀).1 h2`.
-/
theorem existsUnique_of_surjective {A A' : Type} [CommRing A] [Algebra R A] [CommRing A']
    [Algebra R A'] (q : A →ₐ[R] A') (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
    {N : ℕ} (hN : IsUnit (N : A)) (y₀ : sp (R₀ := R) A' ⟶ G) (hy₀ : y₀ ^ N = 1) :
    ∃! y : sp A ⟶ G, y ^ N = 1 ∧ spMap q ≫ y = y₀ := by
  let e : (A ⧸ RingHom.ker q) ≃ₐ[R] A' := Ideal.quotientKerAlgEquivOfSurjective hq
  have he : (e : (A ⧸ RingHom.ker q) →ₐ[R] A').comp (Ideal.Quotient.mkₐ R (RingHom.ker q)) = q := by
    ext a
    rfl
  obtain ⟨y, ⟨hy1, hy2⟩, huniq⟩ := existsUnique_quotient G (RingHom.ker q) hJ hN _
    (sp_pow_comp_algHom G (e.symm : A' →ₐ[R] A ⧸ RingHom.ker q) y₀ hy₀)
  refine ⟨y, ⟨hy1, ?_⟩, fun y' ⟨h1, h2⟩ => huniq y' ⟨h1, ?_⟩⟩
  · rw [← he]
    exact (sp_comp_algEquiv_iff G e _ y y₀).2 hy2
  · rw [← he] at h2
    exact (sp_comp_algEquiv_iff G e _ y' y₀).1 h2

noncomputable def step (I : Ideal R) (n : ℕ) : (R ⧸ I ^ (n + 1 + 1)) →ₐ[R] R ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ _))

omit [IsLocalRing R] in
/- English proof (translation)
Introduce `x`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `⟨Ideal.Quotient.mk _ a, rfl⟩`.
-/
theorem step_surjective (I : Ideal R) (n : ℕ) : Function.Surjective (step I n) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

omit [IsLocalRing R] in
/- English proof (translation)
Rewrite using `[eq_bot_iff, sq, Ideal.mul_le]`. Introduce `x hx y hy`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite `hx`, `hy` using `[RingHom.mem_ker]`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (I ^ (n + 1)) a = 0 at hx`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (I ^ (n + 1)) b = 0 at hy`. Rewrite `hx`, `hy` using `[Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hab : a * b ∈ I ^ (n + 1 + (n + 1))`.

Rewrite using `[pow_add]`. Conclude with `Ideal.mul_mem_mul hx hy`. Conclude with `Ideal.pow_le_pow_right (by omega) hab`.
-/
theorem ker_step_sq (I : Ideal R) (n : ℕ) : RingHom.ker (step I n) ^ 2 = ⊥ := by
  rw [eq_bot_iff, sq, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker] at hx hy
  change Ideal.Quotient.mk (I ^ (n + 1)) a = 0 at hx
  change Ideal.Quotient.mk (I ^ (n + 1)) b = 0 at hy
  rw [Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hab : a * b ∈ I ^ (n + 1 + (n + 1)) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hx hy
  exact Ideal.pow_le_pow_right (by omega) hab

/- English proof (translation)
Establish `hNk : ∀ k, IsUnit (N : R ⧸ I ^ (k + 1))` using `fun k => by`. Simplify using `using hN.map (Ideal.Quotient.mk (I ^ (k + 1)))`. Establish `hstep : ∀ k (z : sp (R₀` using `R) (R ⧸ I ^ (k + 1)) ⟶ G), z ^ N = 1 → ∃! y : sp (R₀ := R) (R ⧸ I ^ (k + 1 + 1)) ⟶ G, y ^ N = 1 ∧ spMap (step I k) ≫ y = z := fun k z hz => existsUnique_of_surjective G (step I k) (step_surjective I k) (ker_step_sq I k) (hNk (k + 1)) z hz`. Use `choose lift hlift using fun k (z : sp (R₀ := R) (R ⧸ I ^ (k + 1)) ⟶ G) (hz : z ^ N = 1) => (hstep k z hz).exists`. Set `F : ∀ k : ℕ, {y : sp (R₀` to `R) (R ⧸ I ^ (k + 1)) ⟶ G // y ^ N = 1} := fun k => Nat.rec (motive := fun k => {y : sp (R₀ := R) (R ⧸ I ^ (k + 1)) ⟶ G // y ^ N = 1}) ⟨y₀, hy₀⟩ (fun k yk => ⟨lift k yk.1 yk.2, (hlift k yk.1 yk.2).1⟩) k`.

Establish `hFs : ∀ k, spMap (step I k) ≫ (F (k + 1)).1 = (F k).1` using `fun k => (hlift k (F k).1 (F k).2).2`. Establish `hmk : ∀ k, (step I k).comp (Ideal.Quotient.mkₐ R (I ^ (k + 1 + 1))) = Ideal.Quotient.mkₐ R (I ^ (k + 1))` using `fun k => Subsingleton.elim _ _`. Establish `hres : ∀ y : sp (R₀` using `R) R ⟶ G, y ^ N = 1 → spMap (Ideal.Quotient.mkₐ R (I ^ (0 + 1))) ≫ y = y₀ → ∀ k, spMap (Ideal.Quotient.mkₐ R (I ^ (k + 1))) ≫ y = (F k).1 := by`. Introduce `y hy hy0 k`. Proceed by induction on `k with`.

Consider the case `zero => exact hy0`. Consider the case `succ k ih`. Use `(hstep k (F k).1 (F k).2).unique ⟨sp_pow_comp_algHom G _ y hy, ?_⟩ (hlift k (F k).1 (F k).2)` and prove the remaining obligations. Rewrite using `[← Category.assoc, spMap_comp, hmk, ih]`. Establish `hι : ∀ n, adicLevelι I (n + 1) = (spMap (Ideal.Quotient.mkₐ R (I ^ (n + 1)))).left` using `fun n => by`.

Rewrite using `[spMap_left]`. Both sides reduce to the same expression. Establish `hext : ∀ a b : sp (R₀` using `R) R ⟶ G, (∀ k, spMap (Ideal.Quotient.mkₐ R (I ^ (k + 1))) ≫ a = spMap (Ideal.Quotient.mkₐ R (I ^ (k + 1))) ≫ b) → a = b := by`. Introduce `a b h`. Use `ext1`.

Conclude with `hom_ext_of_isHausdorff I fun n => by rw [hι n, ← Over.comp_left, ← Over.comp_left, h n]`. Establish `hfam : IsAdicFamily I fun n => (F n).1.left`. Introduce `n`. Establish `e1 : Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)) = (step I n).toRingHom`. Use extensionality with `x`.

Both sides reduce to the same expression. Establish `e2 : adicLevelMap I (Nat.le_succ (n + 1)) = (spMap (step I n)).left`. Rewrite using `[spMap_left, ← e1]`. Rewrite using `[e2, ← Over.comp_left, hFs]`. Establish `hs : ∀ n, (F n).1.left ≫ G.hom = adicLevelι I (n + 1) ≫ (sp (R₀` using `R) R).hom := fun n => by`.

Rewrite using `[Over.w (F n).1, hι n, Over.w]`. Take `⟨g, ⟨hg, hgn⟩, -⟩` from `existsUnique_over_of_isAdicFamily (sp (R₀ := R) R).hom G.hom hfam hs`. Establish `hy : ∀ k, spMap (Ideal.Quotient.mkₐ R (I ^ (k + 1))) ≫ (Over.homMk g hg : sp (R₀` using `R) R ⟶ G) = (F k).1 := fun k => by ext1`. Rewrite using `[Over.comp_left, ← hι k]`. Conclude with `hgn k`.

Establish `hpow : (Over.homMk g hg : sp (R₀` using `R) R ⟶ G) ^ N = 1 := hext _ _ fun k => by`. Rewrite using `[← SqZero.ptsMap_apply, ← SqZero.ptsMap_apply, map_pow, map_one, SqZero.ptsMap_apply, hy k, (F k).2]`. Conclude with `⟨Over.homMk g hg, ⟨hpow, hy 0⟩, fun y' ⟨h1, h2⟩ => hext _ _ fun k => by`. Rewrite using `[hres y' h1 h2 k, hy k]⟩`.
-/
theorem existsUnique_of_isAdicComplete (I : Ideal R) [IsAdicComplete I R] {N : ℕ}
    (hN : IsUnit (N : R)) (y₀ : sp (R₀ := R) (R ⧸ I ^ (0 + 1)) ⟶ G) (hy₀ : y₀ ^ N = 1) :
    ∃! y : sp R ⟶ G, y ^ N = 1 ∧ spMap (Ideal.Quotient.mkₐ R (I ^ (0 + 1))) ≫ y = y₀ := by
  have hNk : ∀ k, IsUnit (N : R ⧸ I ^ (k + 1)) := fun k => by
    simpa using hN.map (Ideal.Quotient.mk (I ^ (k + 1)))
  have hstep : ∀ k (z : sp (R₀ := R) (R ⧸ I ^ (k + 1)) ⟶ G), z ^ N = 1 →
      ∃! y : sp (R₀ := R) (R ⧸ I ^ (k + 1 + 1)) ⟶ G, y ^ N = 1 ∧ spMap (step I k) ≫ y = z :=
    fun k z hz => existsUnique_of_surjective G (step I k) (step_surjective I k) (ker_step_sq I k)
      (hNk (k + 1)) z hz
  choose lift hlift using fun k (z : sp (R₀ := R) (R ⧸ I ^ (k + 1)) ⟶ G) (hz : z ^ N = 1) =>
    (hstep k z hz).exists
  let F : ∀ k : ℕ, {y : sp (R₀ := R) (R ⧸ I ^ (k + 1)) ⟶ G // y ^ N = 1} := fun k =>
    Nat.rec (motive := fun k => {y : sp (R₀ := R) (R ⧸ I ^ (k + 1)) ⟶ G // y ^ N = 1})
      ⟨y₀, hy₀⟩ (fun k yk => ⟨lift k yk.1 yk.2, (hlift k yk.1 yk.2).1⟩) k
  have hFs : ∀ k, spMap (step I k) ≫ (F (k + 1)).1 = (F k).1 := fun k =>
    (hlift k (F k).1 (F k).2).2
  have hmk : ∀ k, (step I k).comp (Ideal.Quotient.mkₐ R (I ^ (k + 1 + 1))) =
      Ideal.Quotient.mkₐ R (I ^ (k + 1)) := fun k => Subsingleton.elim _ _

  have hres : ∀ y : sp (R₀ := R) R ⟶ G, y ^ N = 1 →
      spMap (Ideal.Quotient.mkₐ R (I ^ (0 + 1))) ≫ y = y₀ →
      ∀ k, spMap (Ideal.Quotient.mkₐ R (I ^ (k + 1))) ≫ y = (F k).1 := by
    intro y hy hy0 k
    induction k with
    | zero => exact hy0
    | succ k ih =>
      refine (hstep k (F k).1 (F k).2).unique ⟨sp_pow_comp_algHom G _ y hy, ?_⟩ (hlift k (F k).1 (F k).2)
      rw [← Category.assoc, spMap_comp, hmk, ih]
  have hι : ∀ n, adicLevelι I (n + 1) = (spMap (Ideal.Quotient.mkₐ R (I ^ (n + 1)))).left :=
    fun n => by
      rw [spMap_left]
      rfl

  have hext : ∀ a b : sp (R₀ := R) R ⟶ G,
      (∀ k, spMap (Ideal.Quotient.mkₐ R (I ^ (k + 1))) ≫ a =
        spMap (Ideal.Quotient.mkₐ R (I ^ (k + 1))) ≫ b) → a = b := by
    intro a b h
    ext1
    exact hom_ext_of_isHausdorff I fun n => by rw [hι n, ← Over.comp_left, ← Over.comp_left, h n]
  have hfam : IsAdicFamily I fun n => (F n).1.left := by
    intro n
    have e1 : Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)) = (step I n).toRingHom := by
      ext x
      rfl
    have e2 : adicLevelMap I (Nat.le_succ (n + 1)) = (spMap (step I n)).left := by
      rw [spMap_left, ← e1]
    rw [e2, ← Over.comp_left, hFs]
  have hs : ∀ n, (F n).1.left ≫ G.hom = adicLevelι I (n + 1) ≫ (sp (R₀ := R) R).hom := fun n => by
    rw [Over.w (F n).1, hι n, Over.w]
  obtain ⟨g, ⟨hg, hgn⟩, -⟩ := existsUnique_over_of_isAdicFamily (sp (R₀ := R) R).hom G.hom hfam hs
  have hy : ∀ k, spMap (Ideal.Quotient.mkₐ R (I ^ (k + 1))) ≫ (Over.homMk g hg : sp (R₀ := R) R ⟶ G) =
      (F k).1 := fun k => by
    ext1
    rw [Over.comp_left, ← hι k]
    exact hgn k
  have hpow : (Over.homMk g hg : sp (R₀ := R) R ⟶ G) ^ N = 1 := hext _ _ fun k => by
    rw [← SqZero.ptsMap_apply, ← SqZero.ptsMap_apply, map_pow, map_one, SqZero.ptsMap_apply, hy k,
      (F k).2]
  exact ⟨Over.homMk g hg, ⟨hpow, hy 0⟩, fun y' ⟨h1, h2⟩ => hext _ _ fun k => by
    rw [hres y' h1 h2 k, hy k]⟩

/- English proof (translation)
Establish `hm : maximalIdeal R ^ (0 + 1) = maximalIdeal R` using `pow_one _`. Set `e : (R ⧸ maximalIdeal R ^ (0 + 1)) ≃ₐ[R] ResidueField R` to `Ideal.quotientEquivAlgOfEq R hm`. Establish `he : (e : (R ⧸ maximalIdeal R ^ (0 + 1)) →ₐ[R] ResidueField R).comp (Ideal.Quotient.mkₐ R (maximalIdeal R ^ (0 + 1))) = Algebra.ofId R (ResidueField R)` using `Subsingleton.elim _ _`. Take `⟨y, ⟨hy1, hy2⟩, huniq⟩` from `existsUnique_of_isAdicComplete G (maximalIdeal R) hN _ (sp_pow_comp_algHom G (e.symm : ResidueField R →ₐ[R] R ⧸ maximalIdeal R ^ (0 + 1)) y₀ hy₀)`. Use `⟨y, ⟨hy1, ?_⟩, fun y' ⟨h1, h2⟩ => huniq y' ⟨h1, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← he]`. Conclude with `(sp_comp_algEquiv_iff G e _ y y₀).2 hy2`. Rewrite `h2` using `[← he]`. Conclude with `(sp_comp_algEquiv_iff G e _ y' y₀).1 h2`.
-/
theorem existsUnique_residue [IsAdicComplete (maximalIdeal R) R] {N : ℕ}
    (hN : IsUnit (N : R)) (y₀ : sp (R₀ := R) (ResidueField R) ⟶ G) (hy₀ : y₀ ^ N = 1) :
    ∃! y : sp R ⟶ G, y ^ N = 1 ∧ spMap (Algebra.ofId R (ResidueField R)) ≫ y = y₀ := by
  have hm : maximalIdeal R ^ (0 + 1) = maximalIdeal R := pow_one _
  let e : (R ⧸ maximalIdeal R ^ (0 + 1)) ≃ₐ[R] ResidueField R := Ideal.quotientEquivAlgOfEq R hm
  have he : (e : (R ⧸ maximalIdeal R ^ (0 + 1)) →ₐ[R] ResidueField R).comp
      (Ideal.Quotient.mkₐ R (maximalIdeal R ^ (0 + 1))) = Algebra.ofId R (ResidueField R) :=
    Subsingleton.elim _ _
  obtain ⟨y, ⟨hy1, hy2⟩, huniq⟩ := existsUnique_of_isAdicComplete G (maximalIdeal R) hN _
    (sp_pow_comp_algHom G (e.symm : ResidueField R →ₐ[R] R ⧸ maximalIdeal R ^ (0 + 1)) y₀ hy₀)
  refine ⟨y, ⟨hy1, ?_⟩, fun y' ⟨h1, h2⟩ => huniq y' ⟨h1, ?_⟩⟩
  · rw [← he]
    exact (sp_comp_algEquiv_iff G e _ y y₀).2 hy2
  · rw [← he] at h2
    exact (sp_comp_algEquiv_iff G e _ y' y₀).1 h2

noncomputable def ptsEquiv {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] (T : Over S')
    (t : T.left ⟶ S) (ht : T.hom ≫ p = t) :
    (T ⟶ (Over.pullback p).obj G) ≃* (Over.mk t ⟶ G) := by
  subst ht
  exact { ((Over.mapPullbackAdj p).homEquiv T G).symm with
    map_mul' := adjunction_homEquiv_symm_mul (Over.mapPullbackAdj p) }

/- English proof (translation)
Substitute `ht` using the available equality. Both sides reduce to the same expression.
-/
theorem ptsEquiv_left {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] (T : Over S')
    (t : T.left ⟶ S) (ht : T.hom ≫ p = t) (x : T ⟶ (Over.pullback p).obj G) :
    (ptsEquiv p G T t ht x).left = x.left ≫ pullback.fst G.hom p := by
  subst ht
  rfl

end GlobalTheory.TorsionLift

namespace GlobalTheory

open TorsionLift

/- English proof (translation)
Establish `: Smooth ((Over.pullback p).obj G).hom` using `by show Smooth (pullback.snd G.hom p) infer_instance`. Establish `hres : (sp (R₀` using `W) (ResidueField W)).hom ≫ p = Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ p := rfl`. Establish `hW : (sp (R₀` using `W) W).hom ≫ p = p := by show Spec.map (CommRingCat.ofHom (algebraMap W W)) ≫ p = p`. Simplify using the standard rewrite rules. Establish `hleft : ∀ y' : sp (R₀` using `W) W ⟶ (Over.pullback p).obj G, Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ (ptsEquiv p G (sp (R₀ := W) W) p hW y').left = (ptsEquiv p G (sp (R₀ := W) (ResidueField W)) _ hres (spMap (Algebra.ofId W (ResidueField W)) ≫ y')).left := fun y' => by`.

Rewrite using `[ptsEquiv_left, ptsEquiv_left, Over.comp_left, spMap_left, Category.assoc]`. Both sides reduce to the same expression. Take `⟨y, ⟨hy1, hy2⟩, huniq⟩` from `existsUnique_residue ((Over.pullback p).obj G) hN ((ptsEquiv p G (sp (R₀ := W) (ResidueField W)) _ hres).symm x₀) (by rw [← map_pow, hx₀, map_one])`. Use `⟨ptsEquiv p G (sp (R₀ := W) W) p hW y, ⟨by rw [← map_pow, hy1, map_one], ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hleft y, hy2, MulEquiv.apply_symm_apply]`.

Introduce and unpack `x ⟨hx1, hx2⟩`. Apply `(ptsEquiv p G (sp (R₀ := W) W) p hW).symm.injective` to reduce the goal to its premises. Rewrite using `[MulEquiv.symm_apply_apply]`. Apply `huniq` to reduce the goal to its premises. Use `⟨by rw [← map_pow, hx1, map_one], ?_⟩` and prove the remaining obligations.

Apply `(ptsEquiv p G (sp (R₀ := W) (ResidueField W)) _ hres).injective` to reduce the goal to its premises. Rewrite using `[MulEquiv.apply_symm_apply]`. Use `ext1`. Rewrite using `[← hleft, MulEquiv.apply_symm_apply]`. Conclude with `hx2`.
-/
theorem existsUnique_torsion_lift (W : Type) [CommRing W] [IsLocalRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (S : Scheme.{0}) (G : Over S) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (p : Spec (CommRingCat.of W) ⟶ S) (N : ℕ)
    (hN : IsUnit (N : W))
    (x₀ : Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ p) ⟶ G)
    (hx₀ : x₀ ^ N = 1) : ∃! x : Over.mk p ⟶ G, x ^ N = 1 ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ x.left = x₀.left := by
  have : Smooth ((Over.pullback p).obj G).hom := by
    show Smooth (pullback.snd G.hom p)
    infer_instance
  have hres : (sp (R₀ := W) (ResidueField W)).hom ≫ p =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫ p := rfl
  have hW : (sp (R₀ := W) W).hom ≫ p = p := by
    show Spec.map (CommRingCat.ofHom (algebraMap W W)) ≫ p = p
    simp
  have hleft : ∀ y' : sp (R₀ := W) W ⟶ (Over.pullback p).obj G,
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)) ≫
          (ptsEquiv p G (sp (R₀ := W) W) p hW y').left =
        (ptsEquiv p G (sp (R₀ := W) (ResidueField W)) _ hres
          (spMap (Algebra.ofId W (ResidueField W)) ≫ y')).left := fun y' => by
    rw [ptsEquiv_left, ptsEquiv_left, Over.comp_left, spMap_left, Category.assoc]
    rfl
  obtain ⟨y, ⟨hy1, hy2⟩, huniq⟩ := existsUnique_residue ((Over.pullback p).obj G) hN
    ((ptsEquiv p G (sp (R₀ := W) (ResidueField W)) _ hres).symm x₀)
    (by rw [← map_pow, hx₀, map_one])
  refine ⟨ptsEquiv p G (sp (R₀ := W) W) p hW y, ⟨by rw [← map_pow, hy1, map_one], ?_⟩, ?_⟩
  · rw [hleft y, hy2, MulEquiv.apply_symm_apply]
  · rintro x ⟨hx1, hx2⟩
    apply (ptsEquiv p G (sp (R₀ := W) W) p hW).symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply huniq
    refine ⟨by rw [← map_pow, hx1, map_one], ?_⟩
    apply (ptsEquiv p G (sp (R₀ := W) (ResidueField W)) _ hres).injective
    rw [MulEquiv.apply_symm_apply]
    ext1
    rw [← hleft, MulEquiv.apply_symm_apply]
    exact hx2

end GlobalTheory
