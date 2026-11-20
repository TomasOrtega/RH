import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubsingletonSpDualNumber
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ConstTheta

open GlobalTheory.CechPic

variable {K : Type} [Field K]

/- English proof (translation)
Rewrite using `[TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst, hx]`. Conclude with `IsNilpotent.zero`.
-/
theorem isNilpotent_of_fst_eq_zero {x : DualNumber K} (hx : x.fst = 0) : IsNilpotent x := by
  rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst, hx]; exact IsNilpotent.zero

/- English proof (translation)
Establish `: ¬ IsUnit x.fst` using `fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)`. Simplify using `using this`.
-/
theorem fst_eq_zero_of_mem {x : DualNumber K} (hx : x ∈ IsLocalRing.maximalIdeal (DualNumber K)) : x.fst = 0 := by
  have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
  simpa using this

/- English proof (translation)
Establish `h : ∀ p : PrimeSpectrum (DualNumber K), p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K)`. Introduce `p`. Use `le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `isNilpotent_of_fst_eq_zero (fst_eq_zero_of_mem hx)`. Conclude with `p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)`.

Conclude with `⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩`.
-/
theorem subsingleton_sp : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    obtain ⟨n, hn⟩ := isNilpotent_of_fst_eq_zero (fst_eq_zero_of_mem hx)
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]`. Use `congr 1`.
-/
theorem fst_comp_const : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

/- English proof (translation)
Use `haveI := subsingleton_sp (K := K)`. Set `c : A' ⟶ G'` to `a * b⁻¹`. Set `j' : Over.mk (j ≫ A'.hom) ⟶ A'` to `Over.homMk j rfl`. Establish `h1 : j' ≫ a = j' ≫ b` using `Over.OverMorphism.ext hab`. Establish `h2 : j' ≫ c = 1`.

Simplify using `only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]`. Establish `h3 : η[A'] ≫ c = 1`. Simplify using `only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]`. Take `⟨t₀⟩ : Nonempty (Sp K)` from `inferInstance`. Set `t : Sp (DualNumber K)` to `spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀`.

Establish `hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t`. Introduce `x`. Take `⟨z, rfl, -⟩` from `Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)`. Establish `e : j ≫ c.left = (j' ≫ c).left` using `rfl`. Rewrite using `[← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]`.

Use `(Scheme.Hom.comp_apply _ _ _).trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `Subsingleton.elim (α := Sp (DualNumber K)) _ _`. Establish `hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _` using `Over.w η[A']`. Establish `key` using `DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (hG _ A' hA).2 _ hc`.

Establish `key' : c = toUnit A' ≫ η[A'] ≫ c` using `Over.OverMorphism.ext key`. Rewrite `key'` using `[h3, MonObj.comp_one]`. Conclude with `mul_inv_eq_one.1 key'`.
-/
theorem rigidity (hG : Out.GlobalFnsSt) {A₀ : Over (Sp K)} {A' G' : Over (Sp (DualNumber K))} [GrpObj A'] [GrpObj G']
    {j : A₀.left ⟶ A'.left} {a b : A' ⟶ G'} (hA : IsAbelianScheme A')
    (hj : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  haveI := subsingleton_sp (K := K)
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (hG _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

variable {A : Over (Sp (DualNumber K))} {A₀ : Over (Sp K)} [GrpObj A] [GrpObj A₀] {io : A₀.left ⟶ A.left}
  {ψ : A.left ⟶ A₀.left}

/- English proof (translation)
Establish `w : (ψ ≫ f₀.left) ≫ A₀.hom = A.hom ≫ spMap (algebraMap K (DualNumber K))`. Rewrite using `[Category.assoc, Over.w, hψ.1.w]`. Set `b : A ⟶ A` to `Over.homMk (hψ.1.lift (ψ ≫ f₀.left) A.hom w) (hψ.1.lift_snd _ _ _)`. Establish `hb : b.left ≫ ψ = ψ ≫ f₀.left` using `hψ.1.lift_fst _ _ _`. It suffices to establish `H : f = b by rw [H, hb]`.

Use `rigidity hG hA hi.1 (hψ.1.hom_ext ?_ ?_) (Over.OverMorphism.ext (hψ.1.hom_ext ?_ ?_))` and prove the remaining obligations. Rewrite using `[← h, Category.assoc, Category.assoc, hb, e, reassoc_of% e, Category.comp_id]`. Rewrite using `[Category.assoc, Category.assoc, Over.w, Over.w]`. Establish `h₁ : eSec A ≫ ψ = _ ≫ eSec A₀` using `PolBaseChange.eSec_comm hψ`. Establish `h₂ : eSec A₀ ≫ f₀.left = eSec A₀` using `congrArg (fun z => z.left) (IsMonHom.one_hom f₀)`.

Rewrite using `[IsMonHom.one_hom f]`. Express the relevant statement in the definitionally equal form `eSec A ≫ ψ = (eSec A ≫ b.left) ≫ ψ`. Rewrite using `[Category.assoc, hb, reassoc_of% h₁, h₂, h₁]`. Rewrite using `[Over.w, Over.w]`.
-/
theorem endo_const (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    (hi : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) io)
    (hψ : IsGrpPullback A A₀ (spMap (algebraMap K (DualNumber K))) ψ) (e : io ≫ ψ = 𝟙 _)
    (f : A ⟶ A) (f₀ : A₀ ⟶ A₀) [IsMonHom f] [IsMonHom f₀] (h : f₀.left ≫ io = io ≫ f.left) :
    f.left ≫ ψ = ψ ≫ f₀.left := by
  have w : (ψ ≫ f₀.left) ≫ A₀.hom = A.hom ≫ spMap (algebraMap K (DualNumber K)) := by
    rw [Category.assoc, Over.w, hψ.1.w]
  let b : A ⟶ A := Over.homMk (hψ.1.lift (ψ ≫ f₀.left) A.hom w) (hψ.1.lift_snd _ _ _)
  have hb : b.left ≫ ψ = ψ ≫ f₀.left := hψ.1.lift_fst _ _ _
  suffices H : f = b by rw [H, hb]
  refine rigidity hG hA hi.1 (hψ.1.hom_ext ?_ ?_) (Over.OverMorphism.ext (hψ.1.hom_ext ?_ ?_))
  · rw [← h, Category.assoc, Category.assoc, hb, e, reassoc_of% e, Category.comp_id]
  · rw [Category.assoc, Category.assoc, Over.w, Over.w]
  · have h₁ : eSec A ≫ ψ = _ ≫ eSec A₀ := PolBaseChange.eSec_comm hψ
    have h₂ : eSec A₀ ≫ f₀.left = eSec A₀ := congrArg (fun z => z.left) (IsMonHom.one_hom f₀)
    rw [IsMonHom.one_hom f]
    change eSec A ≫ ψ = (eSec A ≫ b.left) ≫ ψ
    rw [Category.assoc, hb, reassoc_of% h₁, h₂, h₁]
  · rw [Over.w, Over.w]

/- English proof (translation)
Use `formallyUnramified_mulA _ A₀ n hn` as an intermediate fact. Establish `hs : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)` using `TrivSqZeroExt.fst_surjective`. Use `IsClosedImmersion.spec_of_surjective _ hs` as an intermediate fact. Establish `hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom)`. Use `⟨2, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]`. Introduce `r hr s hs`. Establish `hr' : r.fst = 0` using `hr`. Establish `hs' : s.fst = 0` using `hs`. Rewrite using `[Ideal.mem_bot]`.

Apply the tactic sequence `ext <;> simp [hr', hs']`. Set `r : Over.mk ((Out.baseOver _).hom ≫ spMap (algebraMap K (DualNumber K))) ⟶ Out.baseOver (Sp K)` to `Over.homMk (spMap (algebraMap K (DualNumber K))) (by simp)`. Establish `m : ∀ {T : Over (Sp K)} (p : T ⟶ A₀), p ^ n = 1 → p ≫ Out.mulA A₀ n = 1` using `fun p hp => by`. Rewrite using `[Out.mulA, MonObj.comp_pow, Category.comp_id, hp]`. Establish `e₁` using `m (pushHom hψ _ y) (by rw [← map_pow, hy, map_one])`.

Establish `e₂` using `m (r ≫ y₀) (by rw [← MonObj.comp_pow, hy₀, MonObj.comp_one])`. Use `FormallyUnramified.hom_ext (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (isNilpotent_ker_specMap _ hnil) (Out.mulA A₀ n).left ?_ (congrArg (fun z => z.left) (e₁.trans e₂.symm))` and prove the remaining obligations. Use `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) h.symm).trans ?_)` and prove the remaining obligations. Use `Eq.trans ?_ (Category.assoc _ _ _)` and prove the remaining obligations. Rewrite using `[fst_comp_const]`.

Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e).trans ((Category.comp_id _).trans (Category.id_comp _).symm))`.
-/
theorem torsion_const [IsCommMonObj A₀]
    (hψ : IsGrpPullback A A₀ (spMap (algebraMap K (DualNumber K))) ψ) (e : io ≫ ψ = 𝟙 _) {n : ℕ}
    (hn : IsUnit (n : Γ(Sp K, ⊤))) (y : Out.baseOver _ ⟶ A) (y₀ : Out.baseOver _ ⟶ A₀) (hy : y ^ n = 1)
    (hy₀ : y₀ ^ n = 1) (h : y₀.left ≫ io = spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ y.left) :
    y.left ≫ ψ = spMap (algebraMap K (DualNumber K)) ≫ y₀.left := by
  have := formallyUnramified_mulA _ A₀ n hn
  have hs : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    TrivSqZeroExt.fst_surjective
  have := IsClosedImmersion.spec_of_surjective _ hs
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro r hr s hs
    have hr' : r.fst = 0 := hr
    have hs' : s.fst = 0 := hs
    rw [Ideal.mem_bot]
    ext <;> simp [hr', hs']
  let r : Over.mk ((Out.baseOver _).hom ≫ spMap (algebraMap K (DualNumber K))) ⟶ Out.baseOver (Sp K) :=
    Over.homMk (spMap (algebraMap K (DualNumber K))) (by simp)
  have m : ∀ {T : Over (Sp K)} (p : T ⟶ A₀), p ^ n = 1 → p ≫ Out.mulA A₀ n = 1 := fun p hp => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id, hp]
  have e₁ := m (pushHom hψ _ y) (by rw [← map_pow, hy, map_one])
  have e₂ := m (r ≫ y₀) (by rw [← MonObj.comp_pow, hy₀, MonObj.comp_one])
  refine FormallyUnramified.hom_ext (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
    (isNilpotent_ker_specMap _ hnil) (Out.mulA A₀ n).left ?_ (congrArg (fun z => z.left) (e₁.trans e₂.symm))
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) h.symm).trans ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  rw [fst_comp_const]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e).trans ((Category.comp_id _).trans (Category.id_comp _).symm))

/- English proof (translation)
Set `r : Over.mk (G'.hom ≫ f) ⟶ G` to `Over.homMk φ h.1.w`. Establish `e₁ : r ≫ 𝟙 G = pushHom h G' (𝟙 G')` using `Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)`. Establish `e₂ : r ≫ x = pushHom h G' x'` using `Over.OverMorphism.ext hx.symm`. Use `Eq.trans ?_ (pull_lam r c (𝟙 G) x).symm` and prove the remaining obligations. Rewrite using `[e₁, e₂]`.

Unfold `lam`. Rewrite using `[← map_mul, ← map_one (pushHom h G'), ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp]`. Both sides reduce to the same expression.
-/
theorem lam_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (c : Pic G.left) (x' : G' ⟶ G') (x : G ⟶ G)
    (hx : x'.left ≫ φ = φ ≫ x.left) : lam (pull φ c) (𝟙 G') x' = pull φ (lam c (𝟙 G) x) := by
  let r : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have e₁ : r ≫ 𝟙 G = pushHom h G' (𝟙 G') := Over.OverMorphism.ext
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have e₂ : r ≫ x = pushHom h G' x' := Over.OverMorphism.ext hx.symm
  refine Eq.trans ?_ (pull_lam r c (𝟙 G) x).symm
  rw [e₁, e₂]
  unfold lam
  rw [← map_mul, ← map_one (pushHom h G'), ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp]
  rfl

/- English proof (translation)
Use `letI := hA.comm`. Take `⟨Q, hQ, rfl⟩` from `cls_surj q`. Establish `hN : (cubeLB A ![fst A A, snd A A] Q).IsLB` using `LB.isLB_linComb hQ _ _`. Establish `eN` using `cls_cube_two hQ _ _ hN`. Establish `ax : ∀ {T : Over (Sp (DualNumber K))} (u v : T ⟶ A), lam (cls Q hQ) u v = 0 → ∃ t : LB.Gen ((cubeLB A ![fst A A, snd A A] Q).pull (lift u v).left), t.IsGen` using `fun u v h => by`.

Rewrite using `[← cls_eq_zero_iff (pull_isLB hN _), cls_pull hN, eN, pull_lam, lift_fst, lift_snd, h]`. Set `mk` to `Ideal.Quotient.mk (Ideal.span {(DualNumber.eps : DualNumber K)})`. Set `π : Over.mk (pullback.snd (A ⊗ A).hom (spMap mk) ≫ spMap mk) ⟶ A ⊗ A` to `Over.homMk (pullback.fst _ _) pullback.condition`. Establish `fac : spMap mk = spMap (mk.comp (algebraMap K (DualNumber K))) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 2`. Use `RingHom.ext fun a => Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨algebraMap K _ a.snd, ?_⟩)` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]`. Establish `van : ∀ z : Over.mk (pullback.snd (A ⊗ A).hom (spMap mk) ≫ spMap mk) ⟶ A, pull z.left (cls Q hQ) = 0`. Introduce `z`.

Establish `w : z.left ≫ A.hom = (pullback.snd (A ⊗ A).hom (spMap mk) ≫ spMap (mk.comp (algebraMap K (DualNumber K)))) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom`. Rewrite using `[Over.w, Category.assoc, ← fac]`. Both sides reduce to the same expression. Rewrite using `[← hi.lift_fst z.left _ w, pull_comp, hq, map_zero]`. Establish `hε : (DualNumber.eps : DualNumber K) ∈ IsLocalRing.maximalIdeal (DualNumber K)` using `fun hu => by`.

Simplify using `using TrivSqZeroExt.isUnit_iff_isUnit_fst.1 hu`. Establish `H` using `SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective (DualNumber K) DualNumber.eps (fun a ha => by`. Use `fst_eq_zero_of_mem ha` as an intermediate fact. Apply the tactic sequence `ext <;> simp [this]) A hA _ hN (ax _ _ (lam_one_right _ _)) (ax _ _ (lam_one_left _ _)) _`. Use the proof step `(pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _) hε (by`.

Use `ax (π ≫ fst A A) (π ≫ snd A A) (by simp only [lam, van]; simp)` as an intermediate fact. Rewrite `this` using `[← comp_lift, lift_fst_snd, Category.comp_id]`. Conclude with `this)`. Establish `H'` using `congrArg (pull (lift x y).left) (eN.symm.trans ((cls_eq_zero_iff hN).2 H))`. Rewrite `H'` using `[pull_lam, lift_fst, lift_snd, map_zero]`. Then use the resulting hypothesis.
-/
theorem lam_eq_zero (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    (hi : IsPullback io A₀.hom A.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (q : Pic A.left) (hq : pull io q = 0) {T : Over (Sp (DualNumber K))} (x y : T ⟶ A) : lam q x y = 0 := by
  letI := hA.comm
  obtain ⟨Q, hQ, rfl⟩ := cls_surj q
  have hN : (cubeLB A ![fst A A, snd A A] Q).IsLB := LB.isLB_linComb hQ _ _
  have eN := cls_cube_two hQ _ _ hN
  have ax : ∀ {T : Over (Sp (DualNumber K))} (u v : T ⟶ A), lam (cls Q hQ) u v = 0 →
      ∃ t : LB.Gen ((cubeLB A ![fst A A, snd A A] Q).pull (lift u v).left), t.IsGen := fun u v h => by
    rw [← cls_eq_zero_iff (pull_isLB hN _), cls_pull hN, eN, pull_lam, lift_fst, lift_snd, h]
  let mk := Ideal.Quotient.mk (Ideal.span {(DualNumber.eps : DualNumber K)})
  let π : Over.mk (pullback.snd (A ⊗ A).hom (spMap mk) ≫ spMap mk) ⟶ A ⊗ A :=
    Over.homMk (pullback.fst _ _) pullback.condition
  have fac : spMap mk = spMap (mk.comp (algebraMap K (DualNumber K))) ≫
      spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨algebraMap K _ a.snd, ?_⟩)
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have van : ∀ z : Over.mk (pullback.snd (A ⊗ A).hom (spMap mk) ≫ spMap mk) ⟶ A, pull z.left (cls Q hQ) = 0 := by
    intro z
    have w : z.left ≫ A.hom = (pullback.snd (A ⊗ A).hom (spMap mk) ≫
        spMap (mk.comp (algebraMap K (DualNumber K)))) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
      rw [Over.w, Category.assoc, ← fac]; rfl
    rw [← hi.lift_fst z.left _ w, pull_comp, hq, map_zero]
  have hε : (DualNumber.eps : DualNumber K) ∈ IsLocalRing.maximalIdeal (DualNumber K) := fun hu => by
    simpa using TrivSqZeroExt.isUnit_iff_isUnit_fst.1 hu
  have H := SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective (DualNumber K)
    DualNumber.eps (fun a ha => by
      have := fst_eq_zero_of_mem ha
      ext <;> simp [this]) A hA _ hN (ax _ _ (lam_one_right _ _)) (ax _ _ (lam_one_left _ _)) _
    (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _) hε (by
      have := ax (π ≫ fst A A) (π ≫ snd A A) (by simp only [lam, van]; simp)
      rw [← comp_lift, lift_fst_snd, Category.comp_id] at this
      exact this)
  have H' := congrArg (pull (lift x y).left) (eN.symm.trans ((cls_eq_zero_iff hN).2 H))
  rwa [pull_lam, lift_fst, lift_snd, map_zero] at H'

/- English proof (translation)
Establish `e₀ : cls L₀ hL₀ = pull io (cls L hL)` using `(cls_eq_iff _ (pull_isLB hL io)).2 h₀`. Establish `p : cls L hL = lam (cls L hL) (𝟙 A) w` using `((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 hp).trans (cls_cube_two hL _ _ _)`. Establish `p₀ : cls L₀ hL₀ = lam (cls L₀ hL₀) (𝟙 A₀) w₀`. Rewrite using `[e₀, lam_push hi _ w₀ w h₁, ← p]`. Establish `z` using `lam_eq_zero hG hA hi.1 (cls L hL - pull ψ (cls L₀ hL₀)) (by rw [map_sub, ← pull_comp, e, pull_id, e₀, sub_self]) (𝟙 A) w`.

Establish `z' : lam (cls L hL) (𝟙 A) w - lam (pull ψ (cls L₀ hL₀)) (𝟙 A) w = 0`. Use `Eq.trans ?_ z` and prove the remaining obligations. Simplify using `only [lam, map_sub]`. Normalize the expressions using the abelian group laws. Rewrite `z'` using `[lam_push hψ _ w w₀ h₂, ← p, ← p₀, sub_eq_zero]`.

Conclude with `(cls_eq_iff hL (pull_isLB hL₀ ψ)).1 z'`.
-/
theorem lb_const [IsCommMonObj A] (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    (hi : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) io)
    (hψ : IsGrpPullback A A₀ (spMap (algebraMap K (DualNumber K))) ψ) (e : io ≫ ψ = 𝟙 _)
    (w : A ⟶ A) (w₀ : A₀ ⟶ A₀) (h₁ : w₀.left ≫ io = io ≫ w.left) (h₂ : w.left ≫ ψ = ψ ≫ w₀.left)
    {L : LB A.left} {L₀ : LB A₀.left} (hL : L.IsLB) (hL₀ : L₀.IsLB) (h₀ : LBIso L₀ (L.pull io))
    (hp : LBIso L (cubeLB A ![𝟙 A, w] L)) : LBIso L (L₀.pull ψ) := by
  have e₀ : cls L₀ hL₀ = pull io (cls L hL) := (cls_eq_iff _ (pull_isLB hL io)).2 h₀
  have p : cls L hL = lam (cls L hL) (𝟙 A) w :=
    ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 hp).trans (cls_cube_two hL _ _ _)
  have p₀ : cls L₀ hL₀ = lam (cls L₀ hL₀) (𝟙 A₀) w₀ := by
    rw [e₀, lam_push hi _ w₀ w h₁, ← p]
  have z := lam_eq_zero hG hA hi.1 (cls L hL - pull ψ (cls L₀ hL₀))
    (by rw [map_sub, ← pull_comp, e, pull_id, e₀, sub_self]) (𝟙 A) w
  have z' : lam (cls L hL) (𝟙 A) w - lam (pull ψ (cls L₀ hL₀)) (𝟙 A) w = 0 := by
    refine Eq.trans ?_ z
    simp only [lam, map_sub]
    abel
  rw [lam_push hψ _ w w₀ h₂, ← p, ← p₀, sub_eq_zero] at z'
  exact (cls_eq_iff hL (pull_isLB hL₀ ψ)).1 z'

/- English proof (translation)
Introduce `hL _ _ o _ g k J b w w' K _ s s₀ t t₀ io ψ₀ hp hi h₀ hpt hact hψ e`. Establish `hw : ∀ j, (t.act j).left ≫ ψ₀ = ψ₀ ≫ (t₀.act j).left` using `fun j => haveI := t.hom j haveI := t₀.hom j endo_const hL.globalFns t.ab hi hψ e _ _ (hact j)`. Use `letI := t.ab.comm`. Use `letI := t₀.ab.comm`. Establish `hk : IsUnit (k : Γ(Sp K, ⊤))`.

Simplify using `using b.unit.map (s₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)`. Conclude with `⟨ψ₀, hψ, lb_const hL.globalFns t.ab hi hψ e _ _ (hact w) (hw w) t.isLB t₀.isLB h₀ hp.2.2, fun i => torsion_const hψ e hk _ _ (t.torsion i) (t₀.torsion i) (hpt i), hw⟩`.
-/
theorem tMap_of_const : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (w w' : J) (K : Type) [Field K] (s : Sp (DualNumber K) ⟶ Sp o) (s₀ : Sp K ⟶ Sp o) (t : TObj g k J b s) (t₀ : TObj g k J b s₀) (io : t₀.A.left ⟶ t.A.left) (ψ₀ : t.A.left ⟶ t₀.A.left), t.Prim w w' → IsGrpPullback t₀.A t.A (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) io → LBIso t₀.L (t.L.pull io) → (∀ i, (t₀.pt i).left ≫ io = spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (t.pt i).left) → (∀ j, (t₀.act j).left ≫ io = io ≫ (t.act j).left) → IsGrpPullback t.A t₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ → io ≫ ψ₀ = 𝟙 _ → TMap t t₀ (spMap (algebraMap K (DualNumber K))) := by
  intro hL _ _ o _ g k J b w w' K _ s s₀ t t₀ io ψ₀ hp hi h₀ hpt hact hψ e
  have hw : ∀ j, (t.act j).left ≫ ψ₀ = ψ₀ ≫ (t₀.act j).left := fun j =>
    haveI := t.hom j
    haveI := t₀.hom j
    endo_const hL.globalFns t.ab hi hψ e _ _ (hact j)
  letI := t.ab.comm
  letI := t₀.ab.comm
  have hk : IsUnit (k : Γ(Sp K, ⊤)) := by
    simpa using b.unit.map (s₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
  exact ⟨ψ₀, hψ, lb_const hL.globalFns t.ab hi hψ e _ _ (hact w) (hw w) t.isLB t₀.isLB h₀ hp.2.2,
    fun i => torsion_const hψ e hk _ _ (t.torsion i) (t₀.torsion i) (hpt i), hw⟩

end GlobalTheory.ConstTheta
