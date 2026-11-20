import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubsingletonSpDualNumber
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.ConstEndo

/- English proof (translation)
Take `⟨hpb, hmul⟩` from `h`. Establish `hw : ((η[X]).left ≫ φ) ≫ X₀.hom = (𝟙_ (Over S)).hom ≫ f`. Rewrite using `[Category.assoc, hpb.w, ← Category.assoc, Over.w]`. Set `x₀ : Over.mk ((𝟙_ (Over S)).hom ≫ f) ⟶ X₀` to `Over.homMk ((η[X]).left ≫ φ) hw`. Establish `hηη : (η[X] : 𝟙_ (Over S) ⟶ X) * η[X] = η[X]`.

Rewrite using `[MonObj.one_eq_one, _root_.one_mul]`. Establish `hx : x₀ * x₀ = x₀` using `by ext1`. Rewrite using `[hmul (𝟙_ (Over S)) η[X] η[X] x₀ x₀ rfl rfl, hηη]`. Both sides reduce to the same expression. Establish `h1 : x₀ = 1`.

Simplify using `using hx`. Establish `h2` using `congrArg CommaMorphism.left h1`. Simplify using `only [x₀, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom, Over.tensorUnit_hom] at h2`. Conclude with `h2`.
-/
theorem unit_comp {S S₀ : Scheme.{0}} {f : S ⟶ S₀} {X : Over S} {X₀ : Over S₀} [GrpObj X] [GrpObj X₀]
    {φ : X.left ⟶ X₀.left} (h : IsGrpPullback X X₀ f φ) :
    (η[X]).left ≫ φ = f ≫ (η[X₀]).left := by
  obtain ⟨hpb, hmul⟩ := h

  have hw : ((η[X]).left ≫ φ) ≫ X₀.hom = (𝟙_ (Over S)).hom ≫ f := by
    rw [Category.assoc, hpb.w, ← Category.assoc, Over.w]
  let x₀ : Over.mk ((𝟙_ (Over S)).hom ≫ f) ⟶ X₀ := Over.homMk ((η[X]).left ≫ φ) hw

  have hηη : (η[X] : 𝟙_ (Over S) ⟶ X) * η[X] = η[X] := by
    rw [MonObj.one_eq_one, _root_.one_mul]
  have hx : x₀ * x₀ = x₀ := by
    ext1
    rw [hmul (𝟙_ (Over S)) η[X] η[X] x₀ x₀ rfl rfl, hηη]
    rfl
  have h1 : x₀ = 1 := by
    simpa using hx
  have h2 := congrArg CommaMorphism.left h1
  simp only [x₀, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom,
    Over.tensorUnit_hom] at h2
  exact h2

/- English proof (translation)
Establish `hc : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)`. Introduce `p`. Establish `hp : p ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)`. Rewrite using `[range_comap_of_surjective _ _ (fun x => ⟨TrivSqZeroExt.inl x, rfl⟩)]`. Introduce `x hx`.

Establish `hx0 : x.fst = 0` using `hx`. Apply `p.isPrime.mem_of_pow_mem 2` to reduce the goal to its premises. Establish `hx' : x = TrivSqZeroExt.inr x.snd` using `TrivSqZeroExt.ext hx0 rfl`. Rewrite using `[hx', pow_two, TrivSqZeroExt.inr_mul_inr]`. Conclude with `p.asIdeal.zero_mem`.

Conclude with `hp`. Establish `hs : Surjective (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)` using `⟨hc⟩`. Conclude with `(MorphismProperty.of_isPullback h.flip hs).surj`.
-/
private theorem surjective_of_isPullback_dualNumber_fst {A₀ : Over (Sp ℂ)} {A' : Over (Sp (DualNumber ℂ))} (j : A₀.left ⟶ A'.left)
    (h : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) :
    Function.Surjective j := by

  have hc : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    intro p
    have hp : p ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
      rw [range_comap_of_surjective _ _ (fun x => ⟨TrivSqZeroExt.inl x, rfl⟩)]
      intro x hx
      have hx0 : x.fst = 0 := hx
      apply p.isPrime.mem_of_pow_mem 2
      have hx' : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext hx0 rfl
      rw [hx', pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    exact hp
  have hs : Surjective (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := ⟨hc⟩
  exact (MorphismProperty.of_isPullback h.flip hs).surj

/- English proof (translation)
Establish `: IsIso π.appTop` using `(ConcreteCategory.isIso_iff_bijective _).mpr hπ`. Use `⟨S.toSpecΓ ≫ Spec.map (inv π.appTop) ≫ Spec.map g.appTop ≫ inv Y.toSpecΓ, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono Y.toSpecΓ]`. Simplify using `only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]`. Rewrite using `[Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, IsIso.inv_hom_id, Spec.map_id, Category.id_comp]`.
-/
private theorem exists_unit_mul_eq_mul_uniformizer_pow {X S Y : Scheme.{0}} [IsAffine Y] (π : X ⟶ S)
    (hπ : Function.Bijective (π.appTop).hom) (g : X ⟶ Y) : ∃ c : S ⟶ Y, g = π ≫ c := by

  have : IsIso π.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hπ
  refine ⟨S.toSpecΓ ≫ Spec.map (inv π.appTop) ≫ Spec.map g.appTop ≫ inv Y.toSpecΓ, ?_⟩
  rw [← cancel_mono Y.toSpecΓ]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc,
    IsIso.inv_hom_id, Spec.map_id, Category.id_comp]

/- English proof (translation)
Introduce `hL _ P₀ A' _ ρ j hc f' f₀ hab hf' hf₀ hj`. Take `⟨hρ, hjp, hjρ⟩` from `hc`. Use `set ic : Sp (DualNumber ℂ) ⟶ Sp ℂ := spMap (algebraMap ℂ (DualNumber ℂ)) with hic`. Establish `hwρ : ρ ≫ P₀.A.hom = A'.hom ≫ ic` using `hρ.1.w`. Set `T : Over (Sp ℂ)` to `Over.mk (A'.hom ≫ ic)`.

Set `D : T ⟶ P₀.A` to `Over.homMk (f'.left ≫ ρ) (by`. Simplify using `only [T, Over.mk_hom, Category.assoc, hwρ]`. Rewrite using `[← Category.assoc, Over.w])`. Set `E : T ⟶ P₀.A` to `Over.homMk (ρ ≫ f₀.left) (by`. Simplify using `only [T, Over.mk_hom, Category.assoc, Over.w, hwρ])`.

It suffices to establish `hDE : D = E from congrArg CommaMorphism.left hDE`. Rewrite using `[← _root_.mul_inv_eq_one]`. Use `set δ := D * E⁻¹ with hδ`. Establish `hjT : j ≫ T.hom = P₀.A.hom`. Simplify using `only [T, Over.mk_hom]`.

Rewrite using `[← hwρ, ← Category.assoc, hjρ, Category.id_comp]`. Set `jT : P₀.A ⟶ T` to `Over.homMk j hjT`. Establish `h1 : jT ≫ δ = 1`. Establish `hh : jT ≫ D = jT ≫ E` using `by ext1`. Simplify using `only [jT, D, E, Over.comp_left, Over.homMk_left]`.

Rewrite using `[← Category.assoc, hj, Category.assoc, hjρ, Category.comp_id, ← Category.assoc, hjρ, Category.id_comp]`. Rewrite using `[hδ, MonObj.comp_mul, GrpObj.comp_inv, hh, _root_.mul_inv_cancel]`. Establish `hη : (η[A']).left ≫ ρ = ic ≫ (η[P₀.A]).left` using `unit_comp hρ`. Establish `hηA : (η[A']).left ≫ A'.hom = 𝟙 _`. Rewrite using `[Over.w]`.

Both sides reduce to the same expression. Set `eT : Over.mk ic ⟶ T` to `Over.homMk (η[A']).left (by`. Simplify using `only [T, Over.mk_hom]`. Rewrite using `[← Category.assoc, hηA]`. Conclude with `Category.id_comp _)`.

Establish `h2 : (eT ≫ δ).left = ic ≫ (η[P₀.A]).left`. Establish `hh : eT ≫ D = eT ≫ E` using `by ext1`. Simplify using `only [eT, D, E, Over.comp_left, Over.homMk_left]`. Establish `e1 : (η[A']).left ≫ f'.left = (η[A']).left`. Rewrite using `[← Over.comp_left, IsMonHom.one_hom]`.

Establish `e2 : (η[P₀.A]).left ≫ f₀.left = (η[P₀.A]).left`. Rewrite using `[← Over.comp_left, IsMonHom.one_hom]`. Rewrite using `[← Category.assoc, e1, hη, ← Category.assoc, hη, Category.assoc, e2]`. Rewrite using `[hδ, MonObj.comp_mul, GrpObj.comp_inv, hh, _root_.mul_inv_cancel]`. Simplify using `[Hom.one_def]`.

Establish `hsurj` using `surjective_of_isPullback_dualNumber_fst j hjp.1`. Take `⟨p₀⟩ : Nonempty (Sp ℂ)` from `inferInstance`. Take `⟨_, ⟨V₀, hV, rfl⟩, hxV, -⟩` from `P₀.A.left.isBasis_affineOpens.exists_subset_of_mem_open (show (η[P₀.A]).left p₀ ∈ (⊤ : P₀.A.left.Opens) from trivial) (⊤ : P₀.A.left.Opens).2`. Set `V : P₀.A.left.Opens` to `V₀`. Establish `hrange : Set.range δ.left ⊆ Set.range V.ι`.

Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨y, rfl⟩` from `hsurj x`. Establish `e1 : (jT ≫ δ).left = (1 : P₀.A ⟶ P₀.A).left` using `by rw [h1]`. Establish `e2 : δ.left (j y) = (η[P₀.A]).left (P₀.A.hom y)`.

Use `congrArg (fun m => m y) e1` as an intermediate fact. Simplify `this` using `[jT, Hom.one_def]`. Rewrite using `[e2, Subsingleton.elim (P₀.A.hom y) p₀]`. Conclude with `hxV`. Establish `: IsAffine V` using `hV`.

Establish `hG : Function.Bijective (A'.hom.appTop).hom`. Establish `hgl` using `hL.globalFns`. Unfold `Out.GlobalFnsSt at hgl`. Conclude with `hgl _ A' hab`. Take `⟨c, hc⟩` from `exists_unit_mul_eq_mul_uniformizer_pow A'.hom hG (IsOpenImmersion.lift V.ι δ.left hrange)`.

Establish `hδc : δ.left = A'.hom ≫ c ≫ V.ι`. Rewrite using `[← Category.assoc, ← hc, IsOpenImmersion.lift_fac]`. Establish `h3 : c ≫ V.ι = ic ≫ (η[P₀.A]).left`. Rewrite using `[← h2]`. Simplify using `only [eT, Over.comp_left, Over.homMk_left, hδc]`.

Rewrite using `[← Category.assoc, hηA]`. Conclude with `(Category.id_comp (c ≫ V.ι)).symm`. Use `ext1`. Rewrite using `[hδc, h3]`. Simplify using `[T, Hom.one_def]`.
-/
theorem endo_comp_proj : Out.Laws → Out.Laws2 → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (f' : A' ⟶ A') (f₀ : P₀.A ⟶ P₀.A), IsAbelianScheme A' → IsMonHom f' → IsMonHom f₀ → j ≫ f'.left = f₀.left ≫ j → f'.left ≫ ρ = ρ ≫ f₀.left := by
  intro hL _ P₀ A' _ ρ j hc f' f₀ hab hf' hf₀ hj
  obtain ⟨hρ, hjp, hjρ⟩ := hc
  set ic : Sp (DualNumber ℂ) ⟶ Sp ℂ := spMap (algebraMap ℂ (DualNumber ℂ)) with hic
  have hwρ : ρ ≫ P₀.A.hom = A'.hom ≫ ic := hρ.1.w

  let T : Over (Sp ℂ) := Over.mk (A'.hom ≫ ic)
  let D : T ⟶ P₀.A := Over.homMk (f'.left ≫ ρ) (by
    simp only [T, Over.mk_hom, Category.assoc, hwρ]
    rw [← Category.assoc, Over.w])
  let E : T ⟶ P₀.A := Over.homMk (ρ ≫ f₀.left) (by
    simp only [T, Over.mk_hom, Category.assoc, Over.w, hwρ])
  suffices hDE : D = E from congrArg CommaMorphism.left hDE
  rw [← _root_.mul_inv_eq_one]
  set δ := D * E⁻¹ with hδ

  have hjT : j ≫ T.hom = P₀.A.hom := by
    simp only [T, Over.mk_hom]
    rw [← hwρ, ← Category.assoc, hjρ, Category.id_comp]
  let jT : P₀.A ⟶ T := Over.homMk j hjT
  have h1 : jT ≫ δ = 1 := by
    have hh : jT ≫ D = jT ≫ E := by
      ext1
      simp only [jT, D, E, Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, hj, Category.assoc, hjρ, Category.comp_id, ← Category.assoc, hjρ,
        Category.id_comp]
    rw [hδ, MonObj.comp_mul, GrpObj.comp_inv, hh, _root_.mul_inv_cancel]

  have hη : (η[A']).left ≫ ρ = ic ≫ (η[P₀.A]).left := unit_comp hρ
  have hηA : (η[A']).left ≫ A'.hom = 𝟙 _ := by
    rw [Over.w]; rfl
  let eT : Over.mk ic ⟶ T := Over.homMk (η[A']).left (by
    simp only [T, Over.mk_hom]
    rw [← Category.assoc, hηA]
    exact Category.id_comp _)
  have h2 : (eT ≫ δ).left = ic ≫ (η[P₀.A]).left := by
    have hh : eT ≫ D = eT ≫ E := by
      ext1
      simp only [eT, D, E, Over.comp_left, Over.homMk_left]
      have e1 : (η[A']).left ≫ f'.left = (η[A']).left := by
        rw [← Over.comp_left, IsMonHom.one_hom]
      have e2 : (η[P₀.A]).left ≫ f₀.left = (η[P₀.A]).left := by
        rw [← Over.comp_left, IsMonHom.one_hom]
      rw [← Category.assoc, e1, hη, ← Category.assoc, hη, Category.assoc, e2]
    rw [hδ, MonObj.comp_mul, GrpObj.comp_inv, hh, _root_.mul_inv_cancel]
    simp [Hom.one_def]

  have hsurj := surjective_of_isPullback_dualNumber_fst j hjp.1
  obtain ⟨p₀⟩ : Nonempty (Sp ℂ) := inferInstance
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hxV, -⟩ :=
    P₀.A.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show (η[P₀.A]).left p₀ ∈ (⊤ : P₀.A.left.Opens) from trivial) (⊤ : P₀.A.left.Opens).2
  let V : P₀.A.left.Opens := V₀
  have hrange : Set.range δ.left ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hsurj x
    have e1 : (jT ≫ δ).left = (1 : P₀.A ⟶ P₀.A).left := by rw [h1]
    have e2 : δ.left (j y) = (η[P₀.A]).left (P₀.A.hom y) := by
      have := congrArg (fun m => m y) e1
      simpa [jT, Hom.one_def] using this
    rw [e2, Subsingleton.elim (P₀.A.hom y) p₀]
    exact hxV
  have : IsAffine V := hV
  have hG : Function.Bijective (A'.hom.appTop).hom := by
    have hgl := hL.globalFns
    unfold Out.GlobalFnsSt at hgl
    exact hgl _ A' hab
  obtain ⟨c, hc⟩ := exists_unit_mul_eq_mul_uniformizer_pow A'.hom hG (IsOpenImmersion.lift V.ι δ.left hrange)
  have hδc : δ.left = A'.hom ≫ c ≫ V.ι := by
    rw [← Category.assoc, ← hc, IsOpenImmersion.lift_fac]

  have h3 : c ≫ V.ι = ic ≫ (η[P₀.A]).left := by
    rw [← h2]
    simp only [eT, Over.comp_left, Over.homMk_left, hδc]
    rw [← Category.assoc, hηA]
    exact (Category.id_comp (c ≫ V.ι)).symm
  ext1
  rw [hδc, h3]
  simp [T, Hom.one_def]

end GlobalTheory.ConstEndo
