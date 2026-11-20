import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

open GlobalTheory

noncomputable section

namespace GlobalTheory.HomExtNormal

open GlobalTheory.HomExt

/- English proof (translation)
Take `⟨z, rfl, rfl⟩` from `Scheme.Pullback.exists_preimage_pullback (f := c₁) (g := c₂) x₁ x₂ h`. Set `Ω` to `AlgebraicClosure ((pullback c₁ c₂).residueField z)`. Set `r : Sp Ω ⟶ Sp ((pullback c₁ c₂).residueField z)` to `spMap (algebraMap ((pullback c₁ c₂).residueField z) Ω)`. Set `y : Sp Ω ⟶ pullback c₁ c₂` to `r ≫ (pullback c₁ c₂).fromSpecResidueField z`. Establish `hy : y default = z` using `(Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply z _)`.

Use `⟨Ω, inferInstance, inferInstance, y ≫ pullback.fst _ _, y ≫ pullback.snd _ _, by simp [pullback.condition], ⟨default, ?_⟩, ⟨default, ?_⟩⟩` and prove the remaining obligations. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans (congrArg _ hy)`. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans (congrArg _ hy)`.
-/
theorem exists_common_point {A₁ A₂ Y : Scheme.{0}} (c₁ : A₁ ⟶ Y) (c₂ : A₂ ⟶ Y) (x₁ : A₁) (x₂ : A₂)
    (h : c₁ x₁ = c₂ x₂) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (e₁ : Sp Ω ⟶ A₁) (e₂ : Sp Ω ⟶ A₂),
      e₁ ≫ c₁ = e₂ ≫ c₂ ∧ x₁ ∈ Set.range e₁ ∧ x₂ ∈ Set.range e₂ := by
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := c₁) (g := c₂) x₁ x₂ h
  let Ω := AlgebraicClosure ((pullback c₁ c₂).residueField z)
  let r : Sp Ω ⟶ Sp ((pullback c₁ c₂).residueField z) :=
    spMap (algebraMap ((pullback c₁ c₂).residueField z) Ω)
  let y : Sp Ω ⟶ pullback c₁ c₂ := r ≫ (pullback c₁ c₂).fromSpecResidueField z
  have hy : y default = z :=
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply z _)
  refine ⟨Ω, inferInstance, inferInstance, y ≫ pullback.fst _ _, y ≫ pullback.snd _ _,
    by simp [pullback.condition], ⟨default, ?_⟩, ⟨default, ?_⟩⟩
  · exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ hy)
  · exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ hy)

section Pull

variable {X T T' : Scheme.{0}}

abbrev pullMap (r : T' ⟶ T) (τ : T ⟶ X) (τ' : T' ⟶ X) (h : r ≫ τ = τ') (G : Over X) :
    pullback G.hom τ' ⟶ pullback G.hom τ :=
  pullback.lift (pullback.fst G.hom τ') (pullback.snd G.hom τ' ≫ r)
    (by rw [pullback.condition, Category.assoc, h])

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem pullMap_fst (r : T' ⟶ T) (τ : T ⟶ X) (τ' : T' ⟶ X) (h : r ≫ τ = τ') (G : Over X) :
    pullMap r τ τ' h G ≫ pullback.fst G.hom τ = pullback.fst G.hom τ' := pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem pullMap_snd (r : T' ⟶ T) (τ : T ⟶ X) (τ' : T' ⟶ X) (h : r ≫ τ = τ') (G : Over X) :
    pullMap r τ τ' h G ≫ pullback.snd G.hom τ = pullback.snd G.hom τ' ≫ r :=
  pullback.lift_snd _ _ _

/- English proof (translation)
Establish `w : e.hom.left ≫ pullback.snd (pullback.snd G.hom τ) r = pullback.snd G.hom τ'` using `Over.w e.hom`. Establish `k : e.hom.left ≫ pullback.fst (pullback.snd G.hom τ) r = pullMap r τ τ' h G`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, he, pullback.lift_fst]`. Rewrite using `[Category.assoc, pullback.condition, reassoc_of% w, pullback.lift_snd]`.

Establish `n : e'.inv.left ≫ pullback.fst G'.hom τ' = pullback.fst (pullback.snd G'.hom τ) r ≫ pullback.fst G'.hom τ`. Rewrite using `[← he', ← Over.comp_left_assoc, e'.inv_hom_id]`. Simplify using the standard rewrite rules. Establish `l : ((Over.pullback r).map F).left ≫ pullback.fst (pullback.snd G'.hom τ) r = pullback.fst (pullback.snd G.hom τ) r ≫ F.left` using `pullback.lift_fst _ _ _`. Simplify using `only [Over.comp_left, Category.assoc]`.

Rewrite using `[n, reassoc_of% l, reassoc_of% k]`.
-/
theorem pull_left_fst (r : T' ⟶ T) (τ : T ⟶ X) (τ' : T' ⟶ X) (h : r ≫ τ = τ') {G G' : Over X}
    (e : (Over.pullback τ').obj G ≅ (Over.pullback r).obj ((Over.pullback τ).obj G))
    (e' : (Over.pullback τ').obj G' ≅ (Over.pullback r).obj ((Over.pullback τ).obj G'))
    (he : e.hom.left ≫ pullback.fst (pullback.snd G.hom τ) r ≫ pullback.fst G.hom τ =
      pullback.fst G.hom τ')
    (he' : e'.hom.left ≫ pullback.fst (pullback.snd G'.hom τ) r ≫ pullback.fst G'.hom τ =
      pullback.fst G'.hom τ')
    (F : (Over.pullback τ).obj G ⟶ (Over.pullback τ).obj G') :
    (e.hom ≫ (Over.pullback r).map F ≫ e'.inv).left ≫ pullback.fst G'.hom τ' =
      pullMap r τ τ' h G ≫ F.left ≫ pullback.fst G'.hom τ := by
  have w : e.hom.left ≫ pullback.snd (pullback.snd G.hom τ) r = pullback.snd G.hom τ' :=
    Over.w e.hom
  have k : e.hom.left ≫ pullback.fst (pullback.snd G.hom τ) r = pullMap r τ τ' h G := by
    apply pullback.hom_ext
    · rw [Category.assoc, he, pullback.lift_fst]
    · rw [Category.assoc, pullback.condition, reassoc_of% w, pullback.lift_snd]
  have n : e'.inv.left ≫ pullback.fst G'.hom τ' =
      pullback.fst (pullback.snd G'.hom τ) r ≫ pullback.fst G'.hom τ := by
    rw [← he', ← Over.comp_left_assoc, e'.inv_hom_id]; simp
  have l : ((Over.pullback r).map F).left ≫ pullback.fst (pullback.snd G'.hom τ) r =
      pullback.fst (pullback.snd G.hom τ) r ≫ F.left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc]
  rw [n, reassoc_of% l, reassoc_of% k]

/- English proof (translation)
Take `⟨e, m, he⟩` from `exists_iso_pullback_pullback r τ τ' h G`. Take `⟨e', m', he'⟩` from `exists_iso_pullback_pullback r τ τ' h G'`. Conclude with `⟨e.hom ≫ (Over.pullback r).map F ≫ e'.inv, inferInstance, pull_left_fst r τ τ' h e e' he he' F⟩`.
-/
theorem exists_pull_hom (r : T' ⟶ T) (τ : T ⟶ X) (τ' : T' ⟶ X) (h : r ≫ τ = τ') {G G' : Over X}
    [GrpObj G] [GrpObj G'] (F : (Over.pullback τ).obj G ⟶ (Over.pullback τ).obj G') [IsMonHom F] :
    ∃ F' : (Over.pullback τ').obj G ⟶ (Over.pullback τ').obj G', IsMonHom F' ∧
      F'.left ≫ pullback.fst G'.hom τ' = pullMap r τ τ' h G ≫ F.left ≫ pullback.fst G'.hom τ := by
  obtain ⟨e, m, he⟩ := exists_iso_pullback_pullback r τ τ' h G
  obtain ⟨e', m', he'⟩ := exists_iso_pullback_pullback r τ τ' h G'
  exact ⟨e.hom ≫ (Over.pullback r).map F ≫ e'.inv, inferInstance,
    pull_left_fst r τ τ' h e e' he he' F⟩

/- English proof (translation)
Use `set i := spMap (algebraMap T K) with hi`. Take `⟨e₁, m₁, h₁⟩` from `exists_iso_pullback_pullback i t _ rfl G`. Take `⟨e₃, m₃, h₃⟩` from `exists_iso_pullback_pullback i t _ rfl G'`. Take `⟨f', hf', hff⟩` from `exists_pull_hom y j (i ≫ t) hy f`. Take `⟨F, ⟨hF, hFf⟩, -⟩` from `H T K _ _ (IsSemiAbelian.pullback t G hG) (IsSemiAbelian.pullback t G' hG') (e₁.inv ≫ f' ≫ e₃.hom) inferInstance`.

Use `⟨F, hF, ?_⟩` and prove the remaining obligations. Rewrite using `[← hff, ← pull_left_fst i t _ rfl e₁ e₃ h₁ h₃ F, hFf]`. Simplify using the standard rewrite rules.
-/
theorem exists_hom_along_trait
    (H : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    {X U : Scheme.{0}} (j : U ⟶ X) {G G' : Over X} [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom f]
    (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
    [Algebra T K] [IsFractionRing T K] (t : Sp T ⟶ X) (y : Sp K ⟶ U)
    (hy : y ≫ j = spMap (algebraMap T K) ≫ t) :
    ∃ F : (Over.pullback t).obj G ⟶ (Over.pullback t).obj G', IsMonHom F ∧
      pullMap (spMap (algebraMap T K)) t _ rfl G ≫ F.left ≫ pullback.fst G'.hom t =
        pullMap y j _ hy G ≫ f.left ≫ pullback.fst G'.hom j := by
  set i := spMap (algebraMap T K) with hi
  obtain ⟨e₁, m₁, h₁⟩ := exists_iso_pullback_pullback i t _ rfl G
  obtain ⟨e₃, m₃, h₃⟩ := exists_iso_pullback_pullback i t _ rfl G'
  obtain ⟨f', hf', hff⟩ := exists_pull_hom y j (i ≫ t) hy f
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := H T K _ _ (IsSemiAbelian.pullback t G hG)
    (IsSemiAbelian.pullback t G' hG') (e₁.inv ≫ f' ≫ e₃.hom) inferInstance
  refine ⟨F, hF, ?_⟩
  rw [← hff, ← pull_left_fst i t _ rfl e₁ e₃ h₁ h₃ F, hFf]
  simp

end Pull

/- English proof (translation)
Use `hB.comm` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨l, hl, hlk⟩ : ∃ l : ℕ, l.Prime ∧ (l : Ω) ≠ 0 := by`. Take `⟨p, hp⟩` from `CharP.exists Ω`. Distinguish the cases in `h2 : p = 2`. Substitute `h2` using the available equality.

Use `⟨3, Nat.prime_three, fun h3 ↦ ?_⟩` and prove the remaining obligations. Use `(CharP.cast_eq_zero_iff Ω 2 3).mp (by exact_mod_cast h3)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨2, Nat.prime_two, fun h3 ↦ ?_⟩` and prove the remaining obligations. Establish `h4` using `(CharP.cast_eq_zero_iff Ω p 2).mp (by exact_mod_cast h3)`.

Break down `(Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5` into its components or cases. Conclude with `CharP.char_ne_one Ω p h5`. Conclude with `h2 h5`. Establish `hm : IsMonHom (F₁ * F₂⁻¹)` using `{ one_hom := by`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, IsMonHom.one_hom, IsMonHom.one_hom, mul_inv_cancel, one_eq_one]`.

Use `mul_hom := by`. Establish `e (z : A ⊗ A ⟶ A) : z ≫ (F₁ * F₂⁻¹) = z ≫ F₁ * (z ≫ F₂)⁻¹`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv]`. Rewrite using `[mul_eq_mul, e, MonObj.mul_comp, MonObj.mul_comp, mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, e, e, mul_inv, _root_.mul_mul_mul_comm] }`. Establish `h1` using `GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one Ω A B hA hB l hl hlk (F₁ * F₂⁻¹) hm (fun _ _ y a hy ↦ by`.

Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv]`. Conclude with `mul_inv_eq_one.mpr (h y (l ^ a) (pow_pos hl.pos a) hy))`. Conclude with `mul_inv_eq_one.mp h1`.
-/
theorem hom_eq_of_torsion {Ω : Type} [Field Ω] [IsAlgClosed Ω] {A B : Over (Sp Ω)} [GrpObj A]
    [GrpObj B] (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) (F₁ F₂ : A ⟶ B) [IsMonHom F₁]
    [IsMonHom F₂]
    (h : ∀ (y : 𝟙_ (Over (Sp Ω)) ⟶ A) (n : ℕ), 0 < n → y ^ n = 1 → y ≫ F₁ = y ≫ F₂) :
    F₁ = F₂ := by
  have := hB.comm
  obtain ⟨l, hl, hlk⟩ : ∃ l : ℕ, l.Prime ∧ (l : Ω) ≠ 0 := by
    obtain ⟨p, hp⟩ := CharP.exists Ω
    by_cases h2 : p = 2
    · subst h2
      refine ⟨3, Nat.prime_three, fun h3 ↦ ?_⟩
      have := (CharP.cast_eq_zero_iff Ω 2 3).mp (by exact_mod_cast h3)
      omega
    · refine ⟨2, Nat.prime_two, fun h3 ↦ ?_⟩
      have h4 := (CharP.cast_eq_zero_iff Ω p 2).mp (by exact_mod_cast h3)
      rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5
      · exact CharP.char_ne_one Ω p h5
      · exact h2 h5
  have hm : IsMonHom (F₁ * F₂⁻¹) :=
    { one_hom := by
        rw [MonObj.comp_mul, GrpObj.comp_inv, IsMonHom.one_hom, IsMonHom.one_hom, mul_inv_cancel,
          one_eq_one]
      mul_hom := by
        have e (z : A ⊗ A ⟶ A) : z ≫ (F₁ * F₂⁻¹) = z ≫ F₁ * (z ≫ F₂)⁻¹ := by
          rw [MonObj.comp_mul, GrpObj.comp_inv]
        rw [mul_eq_mul, e, MonObj.mul_comp, MonObj.mul_comp, mul_eq_mul, MonObj.comp_mul,
          tensorHom_fst, tensorHom_snd, e, e, mul_inv, _root_.mul_mul_mul_comm] }
  have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one Ω A B hA hB l hl hlk (F₁ * F₂⁻¹) hm
    (fun _ _ y a hy ↦ by
      rw [MonObj.comp_mul, GrpObj.comp_inv]
      exact mul_inv_eq_one.mpr (h y (l ^ a) (pow_pos hl.pos a) hy))
  exact mul_inv_eq_one.mp h1

/- English proof (translation)
Use `finite_torsion_points hG' t hn` as an intermediate fact. Set `l : {c : Sp Ω ⟶ Γ.left // c ≫ p.left = x.left} → (Over.mk t ⟶ Γ)` to `fun c ↦ Over.homMk c.1 (by`. Express the relevant statement in the definitionally equal form `c.1 ≫ Γ.hom = t`. Use `Over.w x` as an intermediate fact. Rewrite using `[← Over.w p, ← Category.assoc, c.2]`.

Conclude with `this)`. Establish `hl (c) : (l c ≫ q) ^ n = 1`. Establish `e : l c ≫ p = x` using `Over.OverMorphism.ext c.2`. Establish `h₁ : l c ≫ p ^ n = l c ≫ (1 : Γ ⟶ G)`. Rewrite using `[SemiAbTorsion.comp_pow_points, e, hx, MonObj.comp_one]`.

Establish `h₂ : l c ≫ q ^ n = l c ≫ (1 : Γ ⟶ G')` using `Over.OverMorphism.ext (key Ω c.1 n (congrArg CommaMorphism.left h₁))`. Rewrite `h₂` using `[SemiAbTorsion.comp_pow_points, MonObj.comp_one]`. Then use the resulting hypothesis. Establish `hfin : Finite {c : Sp Ω ⟶ Γ.left // c ≫ p.left = x.left}`. Use `Finite.of_injective (β := {z : Over.mk t ⟶ G' // z ^ n = 1}) (fun c ↦ ⟨l c ≫ q, hl c⟩) fun a b h ↦ Subtype.ext (hext _ _ (a.2.trans b.2.symm) ?_)` and prove the remaining obligations. Conclude with `congrArg (fun u ↦ u.1.left) h`.

Establish `hf : (p.left ⁻¹' {p.left w}).Finite` using `(finite_preimage_of_finite_lifts p.left x.left hfin).subset (Set.preimage_mono (Set.singleton_subset_iff.mpr hw))`. Establish `: Finite (p.left.fiber (p.left w))` using `(p.left.fiberHomeo (p.left w)).finite_iff.mpr hf`. Conclude with `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)`.
-/
theorem quasiFiniteAt_of_torsion {X : Scheme.{0}} {G G' Γ : Over X} [GrpObj G] [GrpObj G']
    (hG' : IsSemiAbelian G') (p : Γ ⟶ G) (q : Γ ⟶ G') [LocallyOfFiniteType p.left]
    (hext : ∀ {T : Scheme.{0}} (a b : T ⟶ Γ.left), a ≫ p.left = b ≫ p.left →
      a ≫ q.left = b ≫ q.left → a = b)
    (key : ∀ (k : Type) [Field k] (c : Sp k ⟶ Γ.left) (n : ℕ),
      c ≫ (p ^ n).left = c ≫ (1 : Γ ⟶ G).left → c ≫ (q ^ n).left = c ≫ (1 : Γ ⟶ G').left)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ X) (x : Over.mk t ⟶ G) {n : ℕ} (hn : 0 < n)
    (hx : x ^ n = 1) (w : Γ.left) (hw : p.left w ∈ Set.range x.left) :
    p.left.QuasiFiniteAt w := by
  have := finite_torsion_points hG' t hn
  let l : {c : Sp Ω ⟶ Γ.left // c ≫ p.left = x.left} → (Over.mk t ⟶ Γ) := fun c ↦
    Over.homMk c.1 (by
      change c.1 ≫ Γ.hom = t
      have := Over.w x
      rw [← Over.w p, ← Category.assoc, c.2]
      exact this)
  have hl (c) : (l c ≫ q) ^ n = 1 := by
    have e : l c ≫ p = x := Over.OverMorphism.ext c.2
    have h₁ : l c ≫ p ^ n = l c ≫ (1 : Γ ⟶ G) := by
      rw [SemiAbTorsion.comp_pow_points, e, hx, MonObj.comp_one]
    have h₂ : l c ≫ q ^ n = l c ≫ (1 : Γ ⟶ G') :=
      Over.OverMorphism.ext (key Ω c.1 n (congrArg CommaMorphism.left h₁))
    rwa [SemiAbTorsion.comp_pow_points, MonObj.comp_one] at h₂
  have hfin : Finite {c : Sp Ω ⟶ Γ.left // c ≫ p.left = x.left} := by
    refine Finite.of_injective (β := {z : Over.mk t ⟶ G' // z ^ n = 1})
      (fun c ↦ ⟨l c ≫ q, hl c⟩) fun a b h ↦ Subtype.ext (hext _ _ (a.2.trans b.2.symm) ?_)
    exact congrArg (fun u ↦ u.1.left) h
  have hf : (p.left ⁻¹' {p.left w}).Finite :=
    (finite_preimage_of_finite_lifts p.left x.left hfin).subset
      (Set.preimage_mono (Set.singleton_subset_iff.mpr hw))
  have : Finite (p.left.fiber (p.left w)) := (p.left.fiberHomeo (p.left w)).finite_iff.mpr hf
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

/- English proof (translation)
Take `⟨w₀, hw₀⟩` from `genericPoints_subset_range_of_isDominant (i ≫ p) (show genericPoint Y ∈ genericPoints Y by simp [genericPoints_eq_singleton])`. Establish `hgen : IsGenericPoint (i w₀) (Set.univ : Set Γ)`. Use `Set.eq_univ_of_univ_subset ?_` and prove the remaining obligations. Rewrite using `[← i.denseRange.closure_range]`. Use `closure_minimal ?_ isClosed_closure` and prove the remaining obligations.

Introduce and unpack `_ ⟨w, rfl⟩`. Establish `h : w₀ ⤳ w`. Rewrite using `[← (i ≫ p).isEmbedding.isInducing.specializes_iff, hw₀]`. Conclude with `genericPoint_specializes _`. Conclude with `specializes_iff_mem_closure.mp (h.map i.continuous)`.

Establish `: IrreducibleSpace Γ` using `(irreducibleSpace_def Γ).mpr hgen.isIrreducible`. Establish `: IsIntegral Γ` using `isIntegral_of_irreducibleSpace_of_isReduced Γ`. Establish `he : i w₀ = genericPoint Γ` using `hgen.eq (genericPoint_spec Γ)`. Establish `: IsIso (p.stalkMap (genericPoint Γ))`. Rewrite using `[← he]`.

Establish `h₁` using `isIso_stalkMap_of_flat_of_surjectiveOnStalks (i ≫ p) w₀`. Establish `h₂` using `isIso_stalkMap_of_flat_of_surjectiveOnStalks i w₀`. Rewrite `h₁` using `[Scheme.Hom.stalkMap_comp]`. Conclude with `@IsIso.of_isIso_comp_right _ _ _ _ _ _ (i.stalkMap w₀) h₂ h₁`. Use `isIso_fromNormalization_of_birational p (fun y ↦ inferInstance)` as an intermediate fact.

Establish `e : p.quasiFiniteLocus.ι ≫ p = (p.quasiFiniteLocus.ι ≫ p.toNormalization) ≫ p.fromNormalization`. Rewrite using `[Category.assoc, p.toNormalization_fromNormalization]`. Rewrite using `[e]`. Use `infer_instance`.
-/
theorem isOpenImmersion_quasiFiniteLocus_of_isIntegral {W Γ Y : Scheme.{0}} (i : W ⟶ Γ) (p : Γ ⟶ Y)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [Surjective p]
    [IsIntegral Y] [IsNormalScheme Y] [IsReduced Γ]
    [IsPreimmersion i] [Flat i] [IsDominant i]
    [IsPreimmersion (i ≫ p)] [Flat (i ≫ p)] [IsDominant (i ≫ p)] [QuasiCompact (i ≫ p)] :
    IsOpenImmersion (p.quasiFiniteLocus.ι ≫ p) := by
  obtain ⟨w₀, hw₀⟩ := genericPoints_subset_range_of_isDominant (i ≫ p)
    (show genericPoint Y ∈ genericPoints Y by simp [genericPoints_eq_singleton])
  have hgen : IsGenericPoint (i w₀) (Set.univ : Set Γ) := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← i.denseRange.closure_range]
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨w, rfl⟩
    have h : w₀ ⤳ w := by
      rw [← (i ≫ p).isEmbedding.isInducing.specializes_iff, hw₀]
      exact genericPoint_specializes _
    exact specializes_iff_mem_closure.mp (h.map i.continuous)
  have : IrreducibleSpace Γ := (irreducibleSpace_def Γ).mpr hgen.isIrreducible
  have : IsIntegral Γ := isIntegral_of_irreducibleSpace_of_isReduced Γ
  have he : i w₀ = genericPoint Γ := hgen.eq (genericPoint_spec Γ)
  have : IsIso (p.stalkMap (genericPoint Γ)) := by
    rw [← he]
    have h₁ := isIso_stalkMap_of_flat_of_surjectiveOnStalks (i ≫ p) w₀
    have h₂ := isIso_stalkMap_of_flat_of_surjectiveOnStalks i w₀
    rw [Scheme.Hom.stalkMap_comp] at h₁
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (i.stalkMap w₀) h₂ h₁
  have := isIso_fromNormalization_of_birational p (fun y ↦ inferInstance)
  have e : p.quasiFiniteLocus.ι ≫ p =
      (p.quasiFiniteLocus.ι ≫ p.toNormalization) ≫ p.fromNormalization := by
    rw [Category.assoc, p.toNormalization_fromNormalization]
  rw [e]
  infer_instance

/- English proof (translation)
Set `V : Y → Y.Opens` to `fun y ↦ ⟨irreducibleComponent y, IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents y)⟩`. Establish `hV : iSup V = ⊤`. Rewrite using `[eq_top_iff]`. Conclude with `fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, mem_irreducibleComponent⟩`. Use `(IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsOpenImmersion) V hV).mpr fun y ↦ ?_` and prove the remaining obligations.

Establish `: IrreducibleSpace (V y).toScheme` using `Subtype.irreducibleSpace (isIrreducible_irreducibleComponent (x := y))`. Establish `: IsIntegral (V y).toScheme` using `IsNormalScheme.isIntegral_of_irreducibleSpace _`. Establish `e : (i ≫ p) ∣_ V y = i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y` using `morphismRestrict_comp _ _ _`. Establish `: IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y))` using `IsZariskiLocalAtTarget.restrict ‹_› _`. Establish `: IsDominant (i ∣_ (p ⁻¹ᵁ V y))` using `IsZariskiLocalAtTarget.restrict ‹_› _`.

Establish `: IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y)` using `e ▸ IsZariskiLocalAtTarget.restrict ‹_› _`. Establish `: IsDominant (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y)` using `e ▸ IsZariskiLocalAtTarget.restrict ‹_› _`. Establish `: Flat (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y)` using `e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›`. Establish `: QuasiCompact (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y)` using `e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›`. Establish `: Surjective (p ∣_ V y)` using `IsZariskiLocalAtTarget.restrict ‹_› _`.

Establish `hint` using `isOpenImmersion_quasiFiniteLocus_of_isIntegral (i ∣_ (p ⁻¹ᵁ V y)) (p ∣_ V y)`. Rewrite using `[morphismRestrict_comp]`. Use `set Q' := (p ∣_ V y).quasiFiniteLocus with hQ'`. Use `set a := p.quasiFiniteLocus.ι ∣_ (p ⁻¹ᵁ V y) with ha`. Establish `hr : Set.range a ⊆ Set.range Q'.ι`.

Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Express the relevant statement in the definitionally equal form `(p ∣_ V y).QuasiFiniteAt (a x)`. Rewrite using `[← Scheme.Hom.quasiFiniteAt_comp_iff (g := (V y).ι), morphismRestrict_ι, Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion]`. Establish `hx : (p ⁻¹ᵁ V y).ι (a x) = p.quasiFiniteLocus.ι ((p.quasiFiniteLocus.ι ⁻¹ᵁ (p ⁻¹ᵁ V y)).ι x)`.

Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ha, morphismRestrict_ι]`. Rewrite using `[hx]`. Conclude with `(((p.quasiFiniteLocus.ι ⁻¹ᵁ (p ⁻¹ᵁ V y)).ι x)).2`. Set `b` to `IsOpenImmersion.lift Q'.ι a hr`. Establish `hb : b ≫ Q'.ι = a` using `IsOpenImmersion.lift_fac _ _ _`.

Establish `: IsOpenImmersion (b ≫ Q'.ι)` using `by rw [hb]; infer_instance`. Establish `: IsOpenImmersion b` using `IsOpenImmersion.of_comp b Q'.ι`. Rewrite using `[← hb, Category.assoc]`. Conclude with `@IsOpenImmersion.comp _ _ _ b (Q'.ι ≫ p ∣_ V y) _ hint`.
-/
theorem isOpenImmersion_quasiFiniteLocus {W Γ Y : Scheme.{0}} (i : W ⟶ Γ) (p : Γ ⟶ Y)
    [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [Surjective p]
    [IsLocallyNoetherian Y] [IsNormalScheme Y] [IsReduced Γ]
    [IsPreimmersion i] [Flat i] [IsDominant i]
    [IsPreimmersion (i ≫ p)] [Flat (i ≫ p)] [IsDominant (i ≫ p)] [QuasiCompact (i ≫ p)] :
    IsOpenImmersion (p.quasiFiniteLocus.ι ≫ p) := by
  let V : Y → Y.Opens := fun y ↦ ⟨irreducibleComponent y,
    IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (irreducibleComponent_mem_irreducibleComponents y)⟩
  have hV : iSup V = ⊤ := by
    rw [eq_top_iff]
    exact fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, mem_irreducibleComponent⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsOpenImmersion) V hV).mpr fun y ↦ ?_
  have : IrreducibleSpace (V y).toScheme :=
    Subtype.irreducibleSpace (isIrreducible_irreducibleComponent (x := y))
  have : IsIntegral (V y).toScheme := IsNormalScheme.isIntegral_of_irreducibleSpace _
  have e : (i ≫ p) ∣_ V y = i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y := morphismRestrict_comp _ _ _
  have : IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsDominant (i ∣_ (p ⁻¹ᵁ V y)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsPreimmersion (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) := e ▸ IsZariskiLocalAtTarget.restrict ‹_› _
  have : IsDominant (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) := e ▸ IsZariskiLocalAtTarget.restrict ‹_› _
  have : Flat (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) :=
    e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›
  have : QuasiCompact (i ∣_ (p ⁻¹ᵁ V y) ≫ p ∣_ V y) :=
    e ▸ MorphismProperty.of_isPullback (isPullback_morphismRestrict (i ≫ p) (V y)).flip ‹_›
  have : Surjective (p ∣_ V y) := IsZariskiLocalAtTarget.restrict ‹_› _
  have hint := isOpenImmersion_quasiFiniteLocus_of_isIntegral (i ∣_ (p ⁻¹ᵁ V y)) (p ∣_ V y)
  rw [morphismRestrict_comp]
  set Q' := (p ∣_ V y).quasiFiniteLocus with hQ'
  set a := p.quasiFiniteLocus.ι ∣_ (p ⁻¹ᵁ V y) with ha
  have hr : Set.range a ⊆ Set.range Q'.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (p ∣_ V y).QuasiFiniteAt (a x)
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff (g := (V y).ι), morphismRestrict_ι,
      Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion]
    have hx : (p ⁻¹ᵁ V y).ι (a x) = p.quasiFiniteLocus.ι ((p.quasiFiniteLocus.ι ⁻¹ᵁ (p ⁻¹ᵁ V y)).ι x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ha, morphismRestrict_ι]
    rw [hx]
    exact (((p.quasiFiniteLocus.ι ⁻¹ᵁ (p ⁻¹ᵁ V y)).ι x)).2
  let b := IsOpenImmersion.lift Q'.ι a hr
  have hb : b ≫ Q'.ι = a := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (b ≫ Q'.ι) := by rw [hb]; infer_instance
  have : IsOpenImmersion b := IsOpenImmersion.of_comp b Q'.ι
  rw [← hb, Category.assoc]
  exact @IsOpenImmersion.comp _ _ _ b (Q'.ι ≫ p ∣_ V y) _ hint

/- English proof (translation)
Use `hG.smooth` as an intermediate fact. Use `hG'.smooth` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact. Use `hG'.quasiCompact` as an intermediate fact. Use `hG'.separated` as an intermediate fact.

Establish `: GlobalTheory.IsNormalScheme X` using `(GlobalTheory.isNormalScheme_iff X).mpr hX`. Establish `: GlobalTheory.IsNormalScheme G.left` using `(GlobalTheory.isNormalScheme_iff _).mpr (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G.hom hX)`. Establish `: IsSchemeTheoreticallyDominant j` using `IsSchemeTheoreticallyDominant.of_isDominant j`. Set `u : pullback G.hom j ⟶ G.left` to `pullback.fst G.hom j`. Set `φ : pullback G.hom j ⟶ G'.left` to `f.left ≫ pullback.fst G'.hom j`.

Establish `hw : f.left ≫ pullback.snd G'.hom j = pullback.snd G.hom j` using `Over.w f`. Establish `huφ : u ≫ G.hom = φ ≫ G'.hom`. Rewrite using `[Category.assoc, pullback.condition, pullback.condition, reassoc_of% hw]`. Establish `: IsDominant u` using `isDominant_pullback_fst_of_isOpenMap j G.hom G.hom.isOpenMap`. Establish `: IsPreimmersion u` using `inferInstanceAs (IsPreimmersion (pullback.fst G.hom j))`.

Establish `: Flat u` using `inferInstanceAs (Flat (pullback.fst G.hom j))`. Establish `: QuasiCompact u` using `inferInstanceAs (QuasiCompact (pullback.fst G.hom j))`. Establish `hus` using `isIso_stalkMap_of_flat_of_surjectiveOnStalks u`. Establish `: GlobalTheory.IsNormalScheme (pullback G.hom j)` using `GlobalTheory.IsNormalScheme.of_isIso_stalkMap u`. Set `Γ` to `graphClosure G.hom G'.hom u φ huφ`.

Set `p : Γ ⟶ G.left` to `graphClosure.fst G.hom G'.hom u φ huφ`. Set `q : Γ ⟶ G'.left` to `graphClosure.snd G.hom G'.hom u φ huφ`. Set `i : pullback G.hom j ⟶ Γ` to `graphClosure.incl G.hom G'.hom u φ huφ`. Establish `hip : i ≫ p = u` using `graphClosure.incl_fst ..`. Establish `hiq : i ≫ q = φ` using `graphClosure.incl_snd ..`.

Establish `hpq : p ≫ G.hom = q ≫ G'.hom` using `graphClosure.condition ..`. Establish `hpb` using `graphClosure.isPullback_incl G.hom G'.hom u φ huφ`. Establish `: IsPreimmersion i` using `MorphismProperty.of_isPullback hpb ‹IsPreimmersion u›`. Establish `: Flat i` using `MorphismProperty.of_isPullback hpb ‹Flat u›`. Establish `: QuasiCompact i` using `graphClosure.quasiCompact_incl ..`.

Establish `: IsSchemeTheoreticallyDominant i` using `graphClosure.schemeDominant_incl ..`. Establish `: IsDominant i` using `inferInstance`. Establish `: IsReduced Γ` using `graphClosure.isReduced ..`. Establish `: LocallyOfFiniteType p` using `graphClosure.locallyOfFiniteType_fst ..`. Establish `: QuasiCompact p` using `graphClosure.quasiCompact_fst ..`.

Establish `: IsSeparated p` using `graphClosure.isSeparated_fst ..`. Establish `: IsLocallyNoetherian G.left` using `LocallyOfFiniteType.isLocallyNoetherian G.hom`. Establish `: IsLocallyNoetherian Γ` using `LocallyOfFiniteType.isLocallyNoetherian p`. Establish `: Surjective p`. Use `⟨fun σ ↦ ?_⟩` and prove the remaining obligations.

Break down `mem_range_or_exists_dvr u σ with ⟨w, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩` into its components or cases. Conclude with `⟨i w, by rw [← Scheme.Hom.comp_apply, hip]⟩`. Take `⟨F, s, -, -, hs₂, hs⟩` from `exists_hom_along_dvr H j hG hG' f T _ a c hc`. Use `schemeTheoreticallyDominant_fractionField T (FractionRing T)` as an intermediate fact. Establish `hF : F.left ≫ pullback.snd G'.hom (a ≫ G.hom) = pullback.snd G.hom (a ≫ G.hom)` using `Over.w F`.

Take `⟨l, ⟨hl, -⟩, -⟩` from `graphClosure.existsUnique_lift G.hom G'.hom u φ huφ a (s ≫ F.left ≫ pullback.fst G'.hom (a ≫ G.hom)) (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hF, reassoc_of% hs₂]) (spMap (algebraMap T (FractionRing T))) c hc.symm hs`. Conclude with `⟨l (IsLocalRing.closedPoint T), by rw [← hl]; rfl⟩`. Set `Γ' : Over X` to `Over.mk (p ≫ G.hom)`. Set `p' : Γ' ⟶ G` to `Over.homMk p rfl`. Set `q' : Γ' ⟶ G'` to `Over.homMk q hpq.symm`.

Establish `: LocallyOfFiniteType p'.left` using `‹LocallyOfFiniteType p›`. Establish `key : ∀ (k : Type) [Field k] (x : Sp k ⟶ Γ'.left) (n : ℕ), x ≫ (p' ^ n).left = x ≫ (1 : Γ' ⟶ G).left → x ≫ (q' ^ n).left = x ≫ (1 : Γ' ⟶ G').left`. Introduce `k _ x n hx`. Break down `mem_range_or_exists_dvr i (x default) with hw | ⟨T, _, _, _, a, c, hc, ha⟩` into its components or cases. Take `⟨c, rfl⟩` from `exists_lift_of_range_subset i x (by`.

Introduce and unpack `_ ⟨t, rfl⟩`. Rewrite using `[Subsingleton.elim t default])` and apply the resulting hypothesis. Conclude with `comp_pow_eq_one_of_pullback_hom j f p' q' _ c (by rw [Category.assoc]; exact congrArg (c ≫ ·) hip.symm) (by rw [Category.assoc]; exact congrArg (c ≫ ·) hiq.symm) n hx`. Take `⟨F, s, _, hs₁, hs₂, hs⟩` from `exists_hom_along_dvr H j hG hG' f T _ (a ≫ p) c (by rw [← reassoc_of% hc, hip])`. Use `schemeTheoreticallyDominant_fractionField T (FractionRing T)` as an intermediate fact.

Establish `hF : F.left ≫ pullback.snd G'.hom ((a ≫ p) ≫ G.hom) = pullback.snd G.hom ((a ≫ p) ≫ G.hom)` using `Over.w F`. Establish `hb : s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom) = a ≫ q`. Use `over_ext_of_schemeTheoreticallyDominant (Y := Over.mk ((a ≫ p) ≫ G.hom)) (X := G') (spMap (algebraMap T (FractionRing T))) (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) (by` as an intermediate fact. Express the relevant statement in the definitionally equal form `(s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) ≫ G'.hom = (a ≫ p) ≫ G.hom`. Rewrite using `[Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hF, reassoc_of% hs₂]))`.

Use the proof step `(b := Over.homMk (a ≫ q) (by`. Express the relevant statement in the definitionally equal form `(a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom`. Rewrite using `[Category.assoc, Category.assoc, hpq]))`. Use the proof step `(hs.trans (by`. Express the relevant statement in the definitionally equal form `_ = spMap (algebraMap T (FractionRing T)) ≫ a ≫ q`.

Rewrite using `[← reassoc_of% hc, hiq]))`. Conclude with `congrArg CommaMorphism.left this`. Set `r : Sp (IsLocalRing.ResidueField T) ⟶ Sp T` to `spMap (IsLocalRing.residue T)`. Establish `hr : x default ∈ Set.range (r ≫ a)`. Use `⟨IsLocalRing.closedPoint _, ?_⟩` and prove the remaining obligations.

Conclude with `(Scheme.Hom.comp_apply r a _).trans ((congrArg a (IsLocalRing.comap_closedPoint (IsLocalRing.residue T))).trans ha)`. Rewrite `hx`, the goal using `[field_point_comp_eq_iff _ _ x _ ⟨default, rfl⟩, ← field_point_comp_eq_iff (Z := Γ'.left) _ _ (r ≫ a) _ hr]`. Conclude with `comp_pow_eq_one_of_pullback_hom _ F p' q' (r ≫ a) (r ≫ s) (by rw [Category.assoc, hs₁, Category.assoc]; rfl) (by rw [Category.assoc, hb, Category.assoc]; rfl) n hx`. Establish `: IsPreimmersion (i ≫ p)` using `by rwa [hip]`. Establish `: Flat (i ≫ p)` using `by rwa [hip]`.

Establish `: IsDominant (i ≫ p)` using `by rwa [hip]`. Establish `: QuasiCompact (i ≫ p)` using `by rwa [hip]`. Establish `hQ : IsOpenImmersion (p.quasiFiniteLocus.ι ≫ p)` using `isOpenImmersion_quasiFiniteLocus i p`. Establish `hgraph : ∀ w : Γ, ∃ (T : Scheme.{0}) (τ : T ⟶ X) (F : (Over.pullback τ).obj G ⟶ (Over.pullback τ).obj G') (l : pullback G.hom τ ⟶ Γ) (x : ↥(pullback G.hom τ)), IsMonHom F ∧ l ≫ p = pullback.fst G.hom τ ∧ l ≫ q = F.left ≫ pullback.fst G'.hom τ ∧ l x = w`. Introduce `w`.

Break down `mem_range_or_exists_dvr i w with ⟨c, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩` into its components or cases. Conclude with `⟨U, j, f, i, c, hf, hip, hiq, rfl⟩`. Use `schemeTheoreticallyDominant_fractionField T (FractionRing T)` as an intermediate fact. Use `set iK := spMap (algebraMap T (FractionRing T)) with hiK`. Set `t : Sp T ⟶ X` to `(a ≫ p) ≫ G.hom`.

Set `y : Sp (FractionRing T) ⟶ U` to `c ≫ pullback.snd G.hom j`. Establish `h0 : c ≫ u = iK ≫ a ≫ p` using `by rw [← hip, reassoc_of% hc]`. Establish `hy : y ≫ j = iK ≫ t`. Express the relevant statement in the definitionally equal form `(c ≫ pullback.snd G.hom j) ≫ j = iK ≫ (a ≫ p) ≫ G.hom`. Rewrite using `[Category.assoc, ← pullback.condition]`.

Simplify `congrArg (· ≫ G.hom) h0` using `[u]`. Take `⟨F, hF, hFf⟩` from `exists_hom_along_trait H j hG hG' f T (FractionRing T) t y hy`. Establish `hFw : F.left ≫ pullback.snd G'.hom t = pullback.snd G.hom t` using `Over.w F`. Set `d : pullback (pullback.snd G.hom t) iK ⟶ pullback G.hom t` to `pullback.fst _ _`. Establish `: IsDominant d` using `isDominant_pullback_fst_of_isOpenMap iK (pullback.snd G.hom t) (pullback.snd G.hom t).isOpenMap`.

Establish `: GlobalTheory.IsNormalScheme (pullback G.hom t)` using `(GlobalTheory.isNormalScheme_iff _).mpr (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (pullback.snd G.hom t) ((GlobalTheory.isNormalScheme_iff _).mp inferInstance))`. Establish `: IsSchemeTheoreticallyDominant d` using `IsSchemeTheoreticallyDominant.of_isDominant d`. Set `v : pullback (pullback.snd G.hom t) iK ⟶ pullback G.hom (iK ≫ t)` to `pullback.lift (d ≫ pullback.fst G.hom t) (pullback.snd _ iK) (by`. Express the relevant statement in the definitionally equal form `(pullback.fst _ _ ≫ pullback.fst G.hom t) ≫ G.hom = _`. Rewrite using `[Category.assoc, pullback.condition, reassoc_of% (pullback.condition (f := pullback.snd G.hom t) (g := iK))])`.

Establish `hv₁ : v ≫ pullback.fst G.hom (iK ≫ t) = d ≫ pullback.fst G.hom t` using `pullback.lift_fst _ _ _`. Establish `hv₂ : v ≫ pullback.snd G.hom (iK ≫ t) = pullback.snd _ iK` using `pullback.lift_snd _ _ _`. Establish `hv : v ≫ pullMap iK t _ rfl G = d`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullMap_fst, hv₁]`.

Rewrite using `[Category.assoc, pullMap_snd, reassoc_of% hv₂]`. Conclude with `pullback.condition.symm`. Set `ρ` to `pullMap y j _ hy G`. Establish `hρ₁ : ρ ≫ pullback.fst G.hom j = pullback.fst G.hom (iK ≫ t)` using `pullMap_fst ..`. Establish `hρ₂ : ρ ≫ pullback.snd G.hom j = pullback.snd G.hom (iK ≫ t) ≫ y` using `pullMap_snd ..`.

Establish `hw₁ : d ≫ pullback.fst G.hom t = (v ≫ ρ) ≫ u`. Express the relevant statement in the definitionally equal form `_ = (v ≫ ρ) ≫ pullback.fst G.hom j`. Rewrite using `[Category.assoc, hρ₁, hv₁]`. Establish `hw₂ : d ≫ F.left ≫ pullback.fst G'.hom t = (v ≫ ρ) ≫ φ`. Rewrite using `[← hv, Category.assoc, Category.assoc, hFf]`.

Establish `hcond : pullback.fst G.hom t ≫ G.hom = (F.left ≫ pullback.fst G'.hom t) ≫ G'.hom`. Rewrite using `[Category.assoc, pullback.condition, pullback.condition, reassoc_of% hFw]`. Take `⟨l, ⟨hl₁, hl₂⟩, -⟩` from `graphClosure.existsUnique_lift G.hom G'.hom u φ huφ (pullback.fst G.hom t) (F.left ≫ pullback.fst G'.hom t) hcond d (v ≫ ρ) hw₁ hw₂`. Set `s : Sp T ⟶ pullback G.hom t` to `pullback.lift (a ≫ p) (𝟙 _) (by simp [t])`. Establish `hs₁ : s ≫ pullback.fst G.hom t = a ≫ p` using `pullback.lift_fst _ _ _`.

Establish `hs₂ : s ≫ pullback.snd G.hom t = 𝟙 _` using `pullback.lift_snd _ _ _`. Establish `hq : s ≫ F.left ≫ pullback.fst G'.hom t = a ≫ q`. Set `v' : Sp (FractionRing T) ⟶ pullback G.hom (iK ≫ t)` to `pullback.lift (iK ≫ a ≫ p) (𝟙 _) (by simp [t])`. Establish `hv'₁ : v' ≫ pullback.fst G.hom (iK ≫ t) = iK ≫ a ≫ p` using `pullback.lift_fst _ _ _`. Establish `hv'₂ : v' ≫ pullback.snd G.hom (iK ≫ t) = 𝟙 _` using `pullback.lift_snd _ _ _`.

Establish `h₁ : v' ≫ pullMap iK t _ rfl G = iK ≫ s`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullMap_fst, hv'₁, Category.assoc, hs₁]`. Rewrite using `[Category.assoc, pullMap_snd, reassoc_of% hv'₂, Category.assoc, hs₂, Category.comp_id]`. Establish `h₂ : v' ≫ ρ = c`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hρ₁, hv'₁]`. Conclude with `h0.symm`. Rewrite using `[Category.assoc, hρ₂, reassoc_of% hv'₂]`. Establish `h₃ : iK ≫ s ≫ F.left ≫ pullback.fst G'.hom t = iK ≫ a ≫ q`.

Rewrite using `[← reassoc_of% h₁, hFf, reassoc_of% h₂, ← reassoc_of% hc, hiq]`. Use `over_ext_of_schemeTheoreticallyDominant (Y := Over.mk t) (X := G') iK (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom t) (by` as an intermediate fact. Express the relevant statement in the definitionally equal form `(s ≫ F.left ≫ pullback.fst G'.hom t) ≫ G'.hom = t`. Rewrite using `[Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hFw, reassoc_of% hs₂]))`. Use the proof step `(b := Over.homMk (a ≫ q) (by`.

Express the relevant statement in the definitionally equal form `(a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom`. Rewrite using `[Category.assoc, Category.assoc, hpq]))`. Use `h₃`. Conclude with `congrArg CommaMorphism.left this`. Establish `hsl : s ≫ l = a`.

Use `graphClosure.hom_ext G.hom G'.hom u φ huφ ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(s ≫ l) ≫ p = a ≫ p`. Rewrite using `[Category.assoc, hl₁, hs₁]`. Express the relevant statement in the definitionally equal form `(s ≫ l) ≫ q = a ≫ q`. Rewrite using `[Category.assoc, hl₂, hq]`.

Conclude with `⟨Sp T, t, F, l, s (IsLocalRing.closedPoint T), hF, hl₁, hl₂, (Scheme.Hom.comp_apply s l _).symm.trans (by rw [hsl])⟩`. Establish `hinj : ∀ w₁ w₂ : Γ, p w₁ = p w₂ → w₁ = w₂`. Introduce `w₁ w₂ hw₁₂`. Take `⟨T₁, τ₁, F₁, l₁, x₁, m₁, a₁, b₁, rfl⟩` from `hgraph w₁`. Take `⟨T₂, τ₂, F₂, l₂, x₂, m₂, a₂, b₂, rfl⟩` from `hgraph w₂`.

Establish `hx : pullback.fst G.hom τ₁ x₁ = pullback.fst G.hom τ₂ x₂`. Rewrite using `[← a₁, ← a₂, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Conclude with `hw₁₂`. Take `⟨Ω, _, _, e₁, e₂, he, ⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩` from `exists_common_point _ _ x₁ x₂ hx`. Set `τ : Sp Ω ⟶ X` to `e₁ ≫ pullback.fst G.hom τ₁ ≫ G.hom`.

Establish `h₁ : (e₁ ≫ pullback.snd G.hom τ₁) ≫ τ₁ = τ`. Rewrite using `[Category.assoc, ← pullback.condition]`. Establish `h₂ : (e₂ ≫ pullback.snd G.hom τ₂) ≫ τ₂ = τ`. Rewrite using `[Category.assoc, ← pullback.condition, ← reassoc_of% he]`. Take `⟨F₁', m₁', c₁⟩` from `exists_pull_hom _ τ₁ τ h₁ F₁`.

Take `⟨F₂', m₂', c₂⟩` from `exists_pull_hom _ τ₂ τ h₂ F₂`. Set `g₁` to `pullMap _ τ₁ τ h₁ G ≫ l₁`. Set `g₂` to `pullMap _ τ₂ τ h₂ G ≫ l₂`. Establish `hg₁p : g₁ ≫ p = pullback.fst G.hom τ`. Express the relevant statement in the definitionally equal form `(pullMap _ τ₁ τ h₁ G ≫ l₁) ≫ p = _`.

Rewrite using `[Category.assoc, a₁, pullMap_fst]`. Establish `hg₂p : g₂ ≫ p = pullback.fst G.hom τ`. Express the relevant statement in the definitionally equal form `(pullMap _ τ₂ τ h₂ G ≫ l₂) ≫ p = _`. Rewrite using `[Category.assoc, a₂, pullMap_fst]`. Establish `hg₁q : g₁ ≫ q = F₁'.left ≫ pullback.fst G'.hom τ`.

Rewrite using `[c₁, Category.assoc, b₁]`. Establish `hg₂q : g₂ ≫ q = F₂'.left ≫ pullback.fst G'.hom τ`. Rewrite using `[c₂, Category.assoc, b₂]`. Establish `hF : F₁' = F₂'`. Use `hom_eq_of_torsion (IsSemiAbelian.pullback τ G hG) (IsSemiAbelian.pullback τ G' hG') F₁' F₂' fun y n hn hy ↦ ?_` and prove the remaining obligations.

Set `e` to `TorsionLift.ptsEquiv τ G (𝟙_ (Over (Sp Ω))) τ (Category.id_comp _)`. Establish `hx : (e y) ^ n = 1` using `by rw [← map_pow, hy, map_one]`. Establish `hxl : (e y).left = y.left ≫ pullback.fst G.hom τ` using `TorsionLift.ptsEquiv_left ..`. Establish `hqf : ∀ z : Sp Ω ⟶ Γ, z ≫ p = (e y).left → Set.range z ⊆ Set.range p.quasiFiniteLocus.ι`. Introduce and unpack `z hz _ ⟨s, rfl⟩`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `quasiFiniteAt_of_torsion hG' p' q' (fun a b ↦ graphClosure.hom_ext G.hom G'.hom u φ huφ) key τ (e y) hn hx (z s) ⟨s, by rw [← hz]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩`. Set `z₁ : Sp Ω ⟶ Γ` to `y.left ≫ g₁`. Set `z₂ : Sp Ω ⟶ Γ` to `y.left ≫ g₂`. Establish `hz₁ : z₁ ≫ p = (e y).left`.

Express the relevant statement in the definitionally equal form `(y.left ≫ g₁) ≫ p = _`. Rewrite using `[Category.assoc, hg₁p, hxl]`. Establish `hz₂ : z₂ ≫ p = (e y).left`. Express the relevant statement in the definitionally equal form `(y.left ≫ g₂) ≫ p = _`. Rewrite using `[Category.assoc, hg₂p, hxl]`.

Set `z₁'` to `IsOpenImmersion.lift p.quasiFiniteLocus.ι z₁ (hqf z₁ hz₁)`. Set `z₂'` to `IsOpenImmersion.lift p.quasiFiniteLocus.ι z₂ (hqf z₂ hz₂)`. Establish `hz₁' : z₁' ≫ p.quasiFiniteLocus.ι = z₁` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hz₂' : z₂' ≫ p.quasiFiniteLocus.ι = z₂` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hz' : z₁' = z₂'`.

Rewrite using `[← cancel_mono (p.quasiFiniteLocus.ι ≫ p), reassoc_of% hz₁', reassoc_of% hz₂', hz₁, hz₂]`. Establish `hz : z₁ = z₂` using `by rw [← hz₁', ← hz₂', hz']`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `y.left ≫ F₁'.left = y.left ≫ F₂'.left`. Establish `hw₁ : F₁'.left ≫ pullback.snd G'.hom τ = pullback.snd G.hom τ` using `Over.w F₁'`.

Establish `hw₂ : F₂'.left ≫ pullback.snd G'.hom τ = pullback.snd G.hom τ` using `Over.w F₂'`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, ← hg₁q, ← hg₂q]`. Conclude with `congrArg (· ≫ q) (by simpa [z₁, z₂] using hz)`. Rewrite using `[Category.assoc, Category.assoc, hw₁, hw₂]`.

Establish `hg : g₁ = g₂`. Use `graphClosure.hom_ext G.hom G'.hom u φ huφ ?_ ?_` and prove the remaining obligations. Conclude with `hg₁p.trans hg₂p.symm`. Use `hg₁q.trans (hF ▸ hg₂q.symm)` and prove the remaining obligations. Set `b : Sp Ω ⟶ pullback G.hom τ` to `pullback.lift (e₁ ≫ pullback.fst G.hom τ₁) (𝟙 _) (by simp [τ])`.

Establish `hbf : b ≫ pullback.fst G.hom τ = e₁ ≫ pullback.fst G.hom τ₁` using `pullback.lift_fst _ _ _`. Establish `hbs : b ≫ pullback.snd G.hom τ = 𝟙 _` using `pullback.lift_snd _ _ _`. Establish `hb₁ : b ≫ pullMap _ τ₁ τ h₁ G = e₁`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullMap_fst, hbf]`.

Rewrite using `[Category.assoc, pullMap_snd, reassoc_of% hbs]`. Establish `hb₂ : b ≫ pullMap _ τ₂ τ h₂ G = e₂`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullMap_fst, hbf, he]`. Rewrite using `[Category.assoc, pullMap_snd, reassoc_of% hbs]`.

Establish `hl : e₁ ≫ l₁ = e₂ ≫ l₂`. Rewrite using `[← hb₁, ← hb₂, Category.assoc, Category.assoc]`. Conclude with `congrArg (b ≫ ·) hg`. Rewrite using `[Subsingleton.elim s₂ s₁]`. Simplify using `only [← Scheme.Hom.comp_apply]`.

Rewrite using `[hl]`. Establish `: LocallyQuasiFinite p` using `locallyQuasiFinite_iff_finite_preimage_singleton.mpr fun σ ↦ Set.Subsingleton.finite fun a ha b hb ↦ hinj a b (ha.trans hb.symm)`. Establish `: IsIso p` using `isIso_of_densePart i p`. Take `⟨ψ, hψ, huψ⟩` from `graphClosure.exists_extension_of_isIso_fst G.hom G'.hom u φ huφ`. Set `F : G ⟶ G'` to `Over.homMk ψ hψ.symm`.

Establish `hF : (Over.pullback j).map F = f` using `by ext1`. Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `(pullback.lift_fst _ _ _).trans huψ`. Conclude with `(Over.w _).trans hw.symm`. Use `⟨F, ⟨?_, hF⟩, fun F' hF' ↦ pullback_map_injective_of_flat j (hF'.2.trans hF.symm)⟩` and prove the remaining obligations.

Establish `: IsMonHom ((Over.pullback j).map F)` using `hF ▸ hf`. Conclude with `isMonHom_of_pullback_of_flat j F`.
-/
theorem existsUnique_hom_extension_of_dvr
    (H : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f))
    (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) (hX : Geo.Tor.IsNormalScheme X)
    [IsOpenImmersion j] [IsDominant j] (G G' : Over X) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') (hf : IsMonHom f) :
    ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f := by
  have := hG.smooth
  have := hG'.smooth
  have := hG.quasiCompact
  have := hG'.quasiCompact
  have := hG'.separated
  have : GlobalTheory.IsNormalScheme X := (GlobalTheory.isNormalScheme_iff X).mpr hX
  have : GlobalTheory.IsNormalScheme G.left := (GlobalTheory.isNormalScheme_iff _).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G.hom hX)
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  let u : pullback G.hom j ⟶ G.left := pullback.fst G.hom j
  let φ : pullback G.hom j ⟶ G'.left := f.left ≫ pullback.fst G'.hom j
  have hw : f.left ≫ pullback.snd G'.hom j = pullback.snd G.hom j := Over.w f
  have huφ : u ≫ G.hom = φ ≫ G'.hom := by
    rw [Category.assoc, pullback.condition, pullback.condition, reassoc_of% hw]
  have : IsDominant u := isDominant_pullback_fst_of_isOpenMap j G.hom G.hom.isOpenMap
  have : IsPreimmersion u := inferInstanceAs (IsPreimmersion (pullback.fst G.hom j))
  have : Flat u := inferInstanceAs (Flat (pullback.fst G.hom j))
  have : QuasiCompact u := inferInstanceAs (QuasiCompact (pullback.fst G.hom j))
  have hus := isIso_stalkMap_of_flat_of_surjectiveOnStalks u
  have : GlobalTheory.IsNormalScheme (pullback G.hom j) := GlobalTheory.IsNormalScheme.of_isIso_stalkMap u
  let Γ := graphClosure G.hom G'.hom u φ huφ
  let p : Γ ⟶ G.left := graphClosure.fst G.hom G'.hom u φ huφ
  let q : Γ ⟶ G'.left := graphClosure.snd G.hom G'.hom u φ huφ
  let i : pullback G.hom j ⟶ Γ := graphClosure.incl G.hom G'.hom u φ huφ
  have hip : i ≫ p = u := graphClosure.incl_fst ..
  have hiq : i ≫ q = φ := graphClosure.incl_snd ..
  have hpq : p ≫ G.hom = q ≫ G'.hom := graphClosure.condition ..
  have hpb := graphClosure.isPullback_incl G.hom G'.hom u φ huφ
  have : IsPreimmersion i := MorphismProperty.of_isPullback hpb ‹IsPreimmersion u›
  have : Flat i := MorphismProperty.of_isPullback hpb ‹Flat u›
  have : QuasiCompact i := graphClosure.quasiCompact_incl ..
  have : IsSchemeTheoreticallyDominant i := graphClosure.schemeDominant_incl ..
  have : IsDominant i := inferInstance
  have : IsReduced Γ := graphClosure.isReduced ..
  have : LocallyOfFiniteType p := graphClosure.locallyOfFiniteType_fst ..
  have : QuasiCompact p := graphClosure.quasiCompact_fst ..
  have : IsSeparated p := graphClosure.isSeparated_fst ..
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsLocallyNoetherian Γ := LocallyOfFiniteType.isLocallyNoetherian p
  have : Surjective p := by
    refine ⟨fun σ ↦ ?_⟩
    rcases mem_range_or_exists_dvr u σ with ⟨w, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩
    · exact ⟨i w, by rw [← Scheme.Hom.comp_apply, hip]⟩
    obtain ⟨F, s, -, -, hs₂, hs⟩ := exists_hom_along_dvr H j hG hG' f T _ a c hc
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom (a ≫ G.hom) = pullback.snd G.hom (a ≫ G.hom) := Over.w F
    obtain ⟨l, ⟨hl, -⟩, -⟩ := graphClosure.existsUnique_lift G.hom G'.hom u φ huφ a
      (s ≫ F.left ≫ pullback.fst G'.hom (a ≫ G.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hF, reassoc_of% hs₂])
      (spMap (algebraMap T (FractionRing T))) c hc.symm hs
    exact ⟨l (IsLocalRing.closedPoint T), by rw [← hl]; rfl⟩
  let Γ' : Over X := Over.mk (p ≫ G.hom)
  let p' : Γ' ⟶ G := Over.homMk p rfl
  let q' : Γ' ⟶ G' := Over.homMk q hpq.symm
  have : LocallyOfFiniteType p'.left := ‹LocallyOfFiniteType p›
  have key : ∀ (k : Type) [Field k] (x : Sp k ⟶ Γ'.left) (n : ℕ),
      x ≫ (p' ^ n).left = x ≫ (1 : Γ' ⟶ G).left → x ≫ (q' ^ n).left = x ≫ (1 : Γ' ⟶ G').left := by
    intro k _ x n hx
    rcases mem_range_or_exists_dvr i (x default) with hw | ⟨T, _, _, _, a, c, hc, ha⟩
    · obtain ⟨c, rfl⟩ := exists_lift_of_range_subset i x (by
        rintro _ ⟨t, rfl⟩
        rwa [Subsingleton.elim t default])
      exact comp_pow_eq_one_of_pullback_hom j f p' q' _ c
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hip.symm)
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hiq.symm) n hx
    obtain ⟨F, s, _, hs₁, hs₂, hs⟩ := exists_hom_along_dvr H j hG hG' f T _ (a ≫ p) c
      (by rw [← reassoc_of% hc, hip])
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom ((a ≫ p) ≫ G.hom) =
      pullback.snd G.hom ((a ≫ p) ≫ G.hom) := Over.w F
    have hb : s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom) = a ≫ q := by
      have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk ((a ≫ p) ≫ G.hom)) (X := G')
        (spMap (algebraMap T (FractionRing T)))
        (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) (by
          change (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hF,
            reassoc_of% hs₂]))
        (b := Over.homMk (a ≫ q) (by
          change (a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc, Category.assoc, hpq]))
        (hs.trans (by
          change _ = spMap (algebraMap T (FractionRing T)) ≫ a ≫ q
          rw [← reassoc_of% hc, hiq]))
      exact congrArg CommaMorphism.left this
    let r : Sp (IsLocalRing.ResidueField T) ⟶ Sp T := spMap (IsLocalRing.residue T)
    have hr : x default ∈ Set.range (r ≫ a) := by
      refine ⟨IsLocalRing.closedPoint _, ?_⟩
      exact (Scheme.Hom.comp_apply r a _).trans
        ((congrArg a (IsLocalRing.comap_closedPoint (IsLocalRing.residue T))).trans ha)
    rw [field_point_comp_eq_iff _ _ x _ ⟨default, rfl⟩,
      ← field_point_comp_eq_iff (Z := Γ'.left) _ _ (r ≫ a) _ hr] at hx ⊢
    exact comp_pow_eq_one_of_pullback_hom _ F p' q' (r ≫ a) (r ≫ s)
      (by rw [Category.assoc, hs₁, Category.assoc]; rfl)
      (by rw [Category.assoc, hb, Category.assoc]; rfl) n hx
  have : IsPreimmersion (i ≫ p) := by rwa [hip]
  have : Flat (i ≫ p) := by rwa [hip]
  have : IsDominant (i ≫ p) := by rwa [hip]
  have : QuasiCompact (i ≫ p) := by rwa [hip]
  have hQ : IsOpenImmersion (p.quasiFiniteLocus.ι ≫ p) := isOpenImmersion_quasiFiniteLocus i p
  have hgraph : ∀ w : Γ, ∃ (T : Scheme.{0}) (τ : T ⟶ X)
      (F : (Over.pullback τ).obj G ⟶ (Over.pullback τ).obj G') (l : pullback G.hom τ ⟶ Γ)
      (x : ↥(pullback G.hom τ)), IsMonHom F ∧ l ≫ p = pullback.fst G.hom τ ∧
        l ≫ q = F.left ≫ pullback.fst G'.hom τ ∧ l x = w := by
    intro w
    rcases mem_range_or_exists_dvr i w with ⟨c, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩
    · exact ⟨U, j, f, i, c, hf, hip, hiq, rfl⟩
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    set iK := spMap (algebraMap T (FractionRing T)) with hiK
    let t : Sp T ⟶ X := (a ≫ p) ≫ G.hom
    let y : Sp (FractionRing T) ⟶ U := c ≫ pullback.snd G.hom j
    have h0 : c ≫ u = iK ≫ a ≫ p := by rw [← hip, reassoc_of% hc]
    have hy : y ≫ j = iK ≫ t := by
      change (c ≫ pullback.snd G.hom j) ≫ j = iK ≫ (a ≫ p) ≫ G.hom
      rw [Category.assoc, ← pullback.condition]
      simpa [u] using congrArg (· ≫ G.hom) h0
    obtain ⟨F, hF, hFf⟩ := exists_hom_along_trait H j hG hG' f T (FractionRing T) t y hy
    have hFw : F.left ≫ pullback.snd G'.hom t = pullback.snd G.hom t := Over.w F
    let d : pullback (pullback.snd G.hom t) iK ⟶ pullback G.hom t := pullback.fst _ _
    have : IsDominant d := isDominant_pullback_fst_of_isOpenMap iK (pullback.snd G.hom t)
      (pullback.snd G.hom t).isOpenMap
    have : GlobalTheory.IsNormalScheme (pullback G.hom t) := (GlobalTheory.isNormalScheme_iff _).mpr
      (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (pullback.snd G.hom t)
        ((GlobalTheory.isNormalScheme_iff _).mp inferInstance))
    have : IsSchemeTheoreticallyDominant d := IsSchemeTheoreticallyDominant.of_isDominant d
    let v : pullback (pullback.snd G.hom t) iK ⟶ pullback G.hom (iK ≫ t) :=
      pullback.lift (d ≫ pullback.fst G.hom t) (pullback.snd _ iK) (by
        change (pullback.fst _ _ ≫ pullback.fst G.hom t) ≫ G.hom = _
        rw [Category.assoc, pullback.condition, reassoc_of% (pullback.condition (f := pullback.snd G.hom t) (g := iK))])
    have hv₁ : v ≫ pullback.fst G.hom (iK ≫ t) = d ≫ pullback.fst G.hom t :=
      pullback.lift_fst _ _ _
    have hv₂ : v ≫ pullback.snd G.hom (iK ≫ t) = pullback.snd _ iK := pullback.lift_snd _ _ _
    have hv : v ≫ pullMap iK t _ rfl G = d := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, hv₁]
      · rw [Category.assoc, pullMap_snd, reassoc_of% hv₂]
        exact pullback.condition.symm
    let ρ := pullMap y j _ hy G
    have hρ₁ : ρ ≫ pullback.fst G.hom j = pullback.fst G.hom (iK ≫ t) := pullMap_fst ..
    have hρ₂ : ρ ≫ pullback.snd G.hom j = pullback.snd G.hom (iK ≫ t) ≫ y := pullMap_snd ..
    have hw₁ : d ≫ pullback.fst G.hom t = (v ≫ ρ) ≫ u := by
      change _ = (v ≫ ρ) ≫ pullback.fst G.hom j
      rw [Category.assoc, hρ₁, hv₁]
    have hw₂ : d ≫ F.left ≫ pullback.fst G'.hom t = (v ≫ ρ) ≫ φ := by
      rw [← hv, Category.assoc, Category.assoc, hFf]
    have hcond : pullback.fst G.hom t ≫ G.hom = (F.left ≫ pullback.fst G'.hom t) ≫ G'.hom := by
      rw [Category.assoc, pullback.condition, pullback.condition, reassoc_of% hFw]
    obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := graphClosure.existsUnique_lift G.hom G'.hom u φ huφ
      (pullback.fst G.hom t) (F.left ≫ pullback.fst G'.hom t) hcond d (v ≫ ρ) hw₁ hw₂
    let s : Sp T ⟶ pullback G.hom t := pullback.lift (a ≫ p) (𝟙 _) (by simp [t])
    have hs₁ : s ≫ pullback.fst G.hom t = a ≫ p := pullback.lift_fst _ _ _
    have hs₂ : s ≫ pullback.snd G.hom t = 𝟙 _ := pullback.lift_snd _ _ _
    have hq : s ≫ F.left ≫ pullback.fst G'.hom t = a ≫ q := by
      let v' : Sp (FractionRing T) ⟶ pullback G.hom (iK ≫ t) :=
        pullback.lift (iK ≫ a ≫ p) (𝟙 _) (by simp [t])
      have hv'₁ : v' ≫ pullback.fst G.hom (iK ≫ t) = iK ≫ a ≫ p := pullback.lift_fst _ _ _
      have hv'₂ : v' ≫ pullback.snd G.hom (iK ≫ t) = 𝟙 _ := pullback.lift_snd _ _ _
      have h₁ : v' ≫ pullMap iK t _ rfl G = iK ≫ s := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullMap_fst, hv'₁, Category.assoc, hs₁]
        · rw [Category.assoc, pullMap_snd, reassoc_of% hv'₂, Category.assoc, hs₂, Category.comp_id]
      have h₂ : v' ≫ ρ = c := by
        apply pullback.hom_ext
        · rw [Category.assoc, hρ₁, hv'₁]
          exact h0.symm
        · rw [Category.assoc, hρ₂, reassoc_of% hv'₂]
      have h₃ : iK ≫ s ≫ F.left ≫ pullback.fst G'.hom t = iK ≫ a ≫ q := by
        rw [← reassoc_of% h₁, hFf, reassoc_of% h₂, ← reassoc_of% hc, hiq]
      have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk t) (X := G') iK
        (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom t) (by
          change (s ≫ F.left ≫ pullback.fst G'.hom t) ≫ G'.hom = t
          rw [Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hFw,
            reassoc_of% hs₂]))
        (b := Over.homMk (a ≫ q) (by
          change (a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc, Category.assoc, hpq]))
        h₃
      exact congrArg CommaMorphism.left this
    have hsl : s ≫ l = a := by
      refine graphClosure.hom_ext G.hom G'.hom u φ huφ ?_ ?_
      · change (s ≫ l) ≫ p = a ≫ p
        rw [Category.assoc, hl₁, hs₁]
      · change (s ≫ l) ≫ q = a ≫ q
        rw [Category.assoc, hl₂, hq]
    exact ⟨Sp T, t, F, l, s (IsLocalRing.closedPoint T), hF, hl₁, hl₂,
      (Scheme.Hom.comp_apply s l _).symm.trans (by rw [hsl])⟩
  have hinj : ∀ w₁ w₂ : Γ, p w₁ = p w₂ → w₁ = w₂ := by
    intro w₁ w₂ hw₁₂
    obtain ⟨T₁, τ₁, F₁, l₁, x₁, m₁, a₁, b₁, rfl⟩ := hgraph w₁
    obtain ⟨T₂, τ₂, F₂, l₂, x₂, m₂, a₂, b₂, rfl⟩ := hgraph w₂
    have hx : pullback.fst G.hom τ₁ x₁ = pullback.fst G.hom τ₂ x₂ := by
      rw [← a₁, ← a₂, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact hw₁₂
    obtain ⟨Ω, _, _, e₁, e₂, he, ⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := exists_common_point _ _ x₁ x₂ hx
    let τ : Sp Ω ⟶ X := e₁ ≫ pullback.fst G.hom τ₁ ≫ G.hom
    have h₁ : (e₁ ≫ pullback.snd G.hom τ₁) ≫ τ₁ = τ := by
      rw [Category.assoc, ← pullback.condition]
    have h₂ : (e₂ ≫ pullback.snd G.hom τ₂) ≫ τ₂ = τ := by
      rw [Category.assoc, ← pullback.condition, ← reassoc_of% he]
    obtain ⟨F₁', m₁', c₁⟩ := exists_pull_hom _ τ₁ τ h₁ F₁
    obtain ⟨F₂', m₂', c₂⟩ := exists_pull_hom _ τ₂ τ h₂ F₂
    let g₁ := pullMap _ τ₁ τ h₁ G ≫ l₁
    let g₂ := pullMap _ τ₂ τ h₂ G ≫ l₂
    have hg₁p : g₁ ≫ p = pullback.fst G.hom τ := by
      change (pullMap _ τ₁ τ h₁ G ≫ l₁) ≫ p = _
      rw [Category.assoc, a₁, pullMap_fst]
    have hg₂p : g₂ ≫ p = pullback.fst G.hom τ := by
      change (pullMap _ τ₂ τ h₂ G ≫ l₂) ≫ p = _
      rw [Category.assoc, a₂, pullMap_fst]
    have hg₁q : g₁ ≫ q = F₁'.left ≫ pullback.fst G'.hom τ := by
      rw [c₁, Category.assoc, b₁]
    have hg₂q : g₂ ≫ q = F₂'.left ≫ pullback.fst G'.hom τ := by
      rw [c₂, Category.assoc, b₂]
    have hF : F₁' = F₂' := by
      refine hom_eq_of_torsion (IsSemiAbelian.pullback τ G hG) (IsSemiAbelian.pullback τ G' hG')
        F₁' F₂' fun y n hn hy ↦ ?_
      let e := TorsionLift.ptsEquiv τ G (𝟙_ (Over (Sp Ω))) τ (Category.id_comp _)
      have hx : (e y) ^ n = 1 := by rw [← map_pow, hy, map_one]
      have hxl : (e y).left = y.left ≫ pullback.fst G.hom τ := TorsionLift.ptsEquiv_left ..
      have hqf : ∀ z : Sp Ω ⟶ Γ, z ≫ p = (e y).left →
          Set.range z ⊆ Set.range p.quasiFiniteLocus.ι := by
        rintro z hz _ ⟨s, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact quasiFiniteAt_of_torsion hG' p' q'
          (fun a b ↦ graphClosure.hom_ext G.hom G'.hom u φ huφ) key τ (e y) hn hx (z s)
          ⟨s, by rw [← hz]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩
      let z₁ : Sp Ω ⟶ Γ := y.left ≫ g₁
      let z₂ : Sp Ω ⟶ Γ := y.left ≫ g₂
      have hz₁ : z₁ ≫ p = (e y).left := by
        change (y.left ≫ g₁) ≫ p = _
        rw [Category.assoc, hg₁p, hxl]
      have hz₂ : z₂ ≫ p = (e y).left := by
        change (y.left ≫ g₂) ≫ p = _
        rw [Category.assoc, hg₂p, hxl]
      let z₁' := IsOpenImmersion.lift p.quasiFiniteLocus.ι z₁ (hqf z₁ hz₁)
      let z₂' := IsOpenImmersion.lift p.quasiFiniteLocus.ι z₂ (hqf z₂ hz₂)
      have hz₁' : z₁' ≫ p.quasiFiniteLocus.ι = z₁ := IsOpenImmersion.lift_fac _ _ _
      have hz₂' : z₂' ≫ p.quasiFiniteLocus.ι = z₂ := IsOpenImmersion.lift_fac _ _ _
      have hz' : z₁' = z₂' := by
        rw [← cancel_mono (p.quasiFiniteLocus.ι ≫ p), reassoc_of% hz₁', reassoc_of% hz₂', hz₁, hz₂]
      have hz : z₁ = z₂ := by rw [← hz₁', ← hz₂', hz']
      apply Over.OverMorphism.ext
      change y.left ≫ F₁'.left = y.left ≫ F₂'.left
      have hw₁ : F₁'.left ≫ pullback.snd G'.hom τ = pullback.snd G.hom τ := Over.w F₁'
      have hw₂ : F₂'.left ≫ pullback.snd G'.hom τ = pullback.snd G.hom τ := Over.w F₂'
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, ← hg₁q, ← hg₂q]
        exact congrArg (· ≫ q) (by simpa [z₁, z₂] using hz)
      · rw [Category.assoc, Category.assoc, hw₁, hw₂]
    have hg : g₁ = g₂ := by
      refine graphClosure.hom_ext G.hom G'.hom u φ huφ ?_ ?_
      · exact hg₁p.trans hg₂p.symm
      · refine hg₁q.trans (hF ▸ hg₂q.symm)
    let b : Sp Ω ⟶ pullback G.hom τ := pullback.lift (e₁ ≫ pullback.fst G.hom τ₁) (𝟙 _) (by simp [τ])
    have hbf : b ≫ pullback.fst G.hom τ = e₁ ≫ pullback.fst G.hom τ₁ := pullback.lift_fst _ _ _
    have hbs : b ≫ pullback.snd G.hom τ = 𝟙 _ := pullback.lift_snd _ _ _
    have hb₁ : b ≫ pullMap _ τ₁ τ h₁ G = e₁ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, hbf]
      · rw [Category.assoc, pullMap_snd, reassoc_of% hbs]
    have hb₂ : b ≫ pullMap _ τ₂ τ h₂ G = e₂ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, hbf, he]
      · rw [Category.assoc, pullMap_snd, reassoc_of% hbs]
    have hl : e₁ ≫ l₁ = e₂ ≫ l₂ := by
      rw [← hb₁, ← hb₂, Category.assoc, Category.assoc]
      exact congrArg (b ≫ ·) hg
    rw [Subsingleton.elim s₂ s₁]
    simp only [← Scheme.Hom.comp_apply]
    rw [hl]
  have : LocallyQuasiFinite p := locallyQuasiFinite_iff_finite_preimage_singleton.mpr fun σ ↦
    Set.Subsingleton.finite fun a ha b hb ↦ hinj a b (ha.trans hb.symm)
  have : IsIso p := isIso_of_densePart i p
  obtain ⟨ψ, hψ, huψ⟩ := graphClosure.exists_extension_of_isIso_fst G.hom G'.hom u φ huφ
  let F : G ⟶ G' := Over.homMk ψ hψ.symm
  have hF : (Over.pullback j).map F = f := by
    ext1
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans huψ
    · exact (Over.w _).trans hw.symm
  refine ⟨F, ⟨?_, hF⟩, fun F' hF' ↦ pullback_map_injective_of_flat j (hF'.2.trans hF.symm)⟩
  have : IsMonHom ((Over.pullback j).map F) := hF ▸ hf
  exact isMonHom_of_pullback_of_flat j F

end GlobalTheory.HomExtNormal

open GlobalTheory.TorRef in

/- English proof (translation)
The claim follows from `fun X U _ j hX _ _ G G' _ _ hG hG' f hf ↦ GlobalTheory.HomExtNormal.existsUnique_hom_extension_of_dvr GlobalTheory.homExtension_semiAbelian_dvr X U j hX G G' hG hG' f hf`.
-/
theorem GlobalTheory.homExtNormal : HomExtNormalSt :=
  fun X U _ j hX _ _ G G' _ _ hG hG' f hf ↦
    GlobalTheory.HomExtNormal.existsUnique_hom_extension_of_dvr GlobalTheory.homExtension_semiAbelian_dvr X U j hX
      G G' hG hG' f hf
