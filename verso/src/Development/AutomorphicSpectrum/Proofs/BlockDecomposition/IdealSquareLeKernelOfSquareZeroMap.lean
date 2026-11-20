import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CotKer

/- English proof (translation)
Establish `key : ∀ x : Γ(Sp Q, ⊤), (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((spMap q).appTop.hom x) = q ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom.hom x)` using `fun x => congrArg (fun f => CommRingCat.Hom.hom f x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom q))`. Establish `hφ : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of Q)).hom.hom`. Introduce `x y hxy`. Establish `h` using `congrArg (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom hxy`. Simplify using `using h`.

Apply `hφ` to reduce the goal to its premises. Rewrite using `[map_mul, map_zero]`. Apply `hq` to reduce the goal to its premises. Rewrite using `[← key, ha, map_zero]`. Rewrite using `[← key, hb, map_zero]`.
-/
theorem mul_eq_zero_top {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (a b : Γ(Sp Q, ⊤))
    (ha : (spMap q).appTop.hom a = 0) (hb : (spMap q).appTop.hom b = 0) : a * b = 0 := by
  have key : ∀ x : Γ(Sp Q, ⊤), (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((spMap q).appTop.hom x) =
      q ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom.hom x) := fun x =>
    congrArg (fun f => CommRingCat.Hom.hom f x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom q))
  have hφ : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of Q)).hom.hom := by
    intro x y hxy
    have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom hxy
    simpa using h
  apply hφ
  rw [map_mul, map_zero]
  apply hq
  · rw [← key, ha, map_zero]
  · rw [← key, hb, map_zero]

/- English proof (translation)
Apply `Scheme.IdealSheafData.ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Scheme.Hom.ker_apply, pow_two, eq_bot_iff, Ideal.mul_le]`. Introduce `a ha b hb`. Conclude with `(Submodule.mem_bot _).mpr (mul_eq_zero_top q hq a b ha hb)`.
-/
theorem ker_sq_eq_bot {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) : (spMap q).ker ^ 2 = ⊥ := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    Scheme.Hom.ker_apply, pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  exact (Submodule.mem_bot _).mpr (mul_eq_zero_top q hq a b ha hb)

/- English proof (translation)
Establish `h` using `congrArg (fun I => Scheme.IdealSheafData.ideal I W) (ker_sq_eq_bot q hq)`. Simplify using `only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Scheme.Hom.ker_apply] at h`. Establish `hab : a * b ∈ (RingHom.ker ((spMap q).app W.1).hom) ^ 2`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul ha hb`.

Rewrite `hab` using `[h]`. Conclude with `(Submodule.mem_bot _).mp hab`.
-/
theorem mul_eq_zero_affine {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (W : (Sp Q).affineOpens) (a b : Γ(Sp Q, W.1))
    (ha : ((spMap q).app W.1).hom a = 0) (hb : ((spMap q).app W.1).hom b = 0) : a * b = 0 := by
  have h := congrArg (fun I => Scheme.IdealSheafData.ideal I W) (ker_sq_eq_bot q hq)
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot,
    Pi.bot_apply, Scheme.Hom.ker_apply] at h
  have hab : a * b ∈ (RingHom.ker ((spMap q).app W.1).hom) ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  rw [h] at hab
  exact (Submodule.mem_bot _).mp hab

/- English proof (translation)
Use `TopCat.Sheaf.eq_of_locally_eq' (Sp Q).sheaf (fun W : {W : (Sp Q).affineOpens // W.1 ≤ O} => W.1.1) O (fun W => homOfLE W.2) ?_ (a * b) 0 ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨U', hU', hxU', hle⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens (Sp Q))) hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U', hU'⟩, hle⟩, hxU'⟩`. Introduce `W`.

Establish `hres : ∀ s : Γ(Sp Q, O), ((spMap q).app O).hom s = 0 → ((spMap q).app W.1.1).hom (((Sp Q).presheaf.map (homOfLE W.2).op).hom s) = 0`. Introduce `s hs`. Establish `h` using `congrArg (fun f => CommRingCat.Hom.hom f s) ((spMap q).naturality (homOfLE W.2).op)`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, hs, map_zero] at h`. Conclude with `h`.

Use `show ((Sp Q).presheaf.map (homOfLE W.2).op).hom (a * b) = ((Sp Q).presheaf.map (homOfLE W.2).op).hom 0`. Rewrite using `[map_zero, map_mul]`. Conclude with `mul_eq_zero_affine q hq W.1 _ _ (hres a ha) (hres b hb)`.
-/
theorem mul_eq_zero_open {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (O : (Sp Q).Opens) (a b : Γ(Sp Q, O))
    (ha : ((spMap q).app O).hom a = 0) (hb : ((spMap q).app O).hom b = 0) : a * b = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' (Sp Q).sheaf
    (fun W : {W : (Sp Q).affineOpens // W.1 ≤ O} => W.1.1) O (fun W => homOfLE W.2) ?_ (a * b) 0 ?_
  · intro x hx
    obtain ⟨U', hU', hxU', hle⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens (Sp Q))) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U', hU'⟩, hle⟩, hxU'⟩
  · intro W
    have hres : ∀ s : Γ(Sp Q, O), ((spMap q).app O).hom s = 0 →
        ((spMap q).app W.1.1).hom (((Sp Q).presheaf.map (homOfLE W.2).op).hom s) = 0 := by
      intro s hs
      have h := congrArg (fun f => CommRingCat.Hom.hom f s) ((spMap q).naturality (homOfLE W.2).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, hs, map_zero] at h
      exact h
    show ((Sp Q).presheaf.map (homOfLE W.2).op).hom (a * b) =
      ((Sp Q).presheaf.map (homOfLE W.2).op).hom 0
    rw [map_zero, map_mul]
    exact mul_eq_zero_affine q hq W.1 _ _ (hres a ha) (hres b hb)

/- English proof (translation)
Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]`.
-/
theorem comp_comp_apply_eq_zero {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (a : A)
    (ha : f.hom a = 0) : ((f ≫ g) ≫ h).hom a = 0 := by
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]

/- English proof (translation)
Introduce `R Q B _ _ _ U e _ q ρ y _ hq hcomm`. Use `show _ ≤ Scheme.IdealSheafData.ofIdeals (fun V => RingHom.ker (y.app V).hom)`. Rewrite using `[Scheme.IdealSheafData.le_ofIdeals_iff]`. Introduce `V`. Rewrite using `[Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply e V, pow_two, Ideal.mul_le]`.

Introduce `a ha b hb`. Rewrite `ha`, `hb`, the goal using `[RingHom.mem_ker]`. Establish `key : ∀ s, (e.app V).hom s = 0 → ((spMap q).app (y ⁻¹ᵁ V)).hom ((y.app V).hom s) = 0`. Introduce `s hs`. Establish `h1 : ((spMap q).app (y ⁻¹ᵁ V)).hom ((y.app V).hom s) = ((spMap q ≫ y).app V).hom s`.

Rewrite using `[Scheme.Hom.comp_app]`. Both sides reduce to the same expression. Rewrite using `[h1, Scheme.Hom.congr_app hcomm V, Scheme.Hom.comp_app]`. Conclude with `comp_comp_apply_eq_zero _ _ _ s hs`. Rewrite using `[map_mul]`.

Conclude with `mul_eq_zero_open q hq (y ⁻¹ᵁ V) _ _ (key a ha) (key b hb)`.
-/
theorem ker_sq_le_ker : ∀ (R Q B : Type) [CommRing R] [CommRing Q] [CommRing B] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ U), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → e.ker ^ 2 ≤ y.ker := by
  intro R Q B _ _ _ U e _ q ρ y _ hq hcomm
  show _ ≤ Scheme.IdealSheafData.ofIdeals (fun V => RingHom.ker (y.app V).hom)
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro V
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply e V, pow_two, Ideal.mul_le]
  intro a ha b hb
  rw [RingHom.mem_ker] at ha hb ⊢
  have key : ∀ s, (e.app V).hom s = 0 → ((spMap q).app (y ⁻¹ᵁ V)).hom ((y.app V).hom s) = 0 := by
    intro s hs
    have h1 : ((spMap q).app (y ⁻¹ᵁ V)).hom ((y.app V).hom s) = ((spMap q ≫ y).app V).hom s := by
      rw [Scheme.Hom.comp_app]
      rfl
    rw [h1, Scheme.Hom.congr_app hcomm V, Scheme.Hom.comp_app]
    exact comp_comp_apply_eq_zero _ _ _ s hs
  rw [map_mul]
  exact mul_eq_zero_open q hq (y ⁻¹ᵁ V) _ _ (key a ha) (key b hb)

end GlobalTheory.CompanionTheory.CotKer
