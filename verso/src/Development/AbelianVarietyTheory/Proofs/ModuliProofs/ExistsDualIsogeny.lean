import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsHeckeIsog
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndEtaleOfCompOfFiniteEtaleCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReducedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivOfAxesTrivPullbackEtaleIsogenyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open GlobalTheory.CechPic

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `hf 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[pow_zero, zero_nsmul, left_eq_mul.1 h]`.

Consider the case `succ n ih => rw [pow_succ, ih, succ_nsmul, hf]`.
-/
theorem pow_eq_of_map_add {A Q : Type} [AddCommGroup A] [Group Q] (f : A → Q)
    (hf : ∀ a c, f (a + c) = f a * f c) (n : ℕ) (a : A) : f a ^ n = f (n • a) := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_nsmul, left_eq_mul.1 h]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, hf]

/- English proof (translation)
Introduce `E _ _ _ H D l p S _ s o o' ψ hp _ ⟨⟨hψ, hf, he, hs, hact, hiso⟩, hlev⟩ hker`. Establish `hA : IsAbelianScheme o.t.G` using `⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩`. Establish `hB : IsAbelianScheme o'.t.G` using `⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩`. Establish `hn : 0 < p ^ 2` using `pow_pos hp.pos 2`. Establish `hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤))`.

Establish `h0 : IsUnit ((p ^ 2 : ℕ) : Γ(Sp (KA l), ⊤))`. Use `((baseKA l).unit _ hn).map (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Use `h0.map s.appTop.hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Take `⟨m1, m2, m3, m4⟩` from `abelianScheme_id_pow_finite_etale_surjective S o.t.G (p ^ 2) hA hu`. Use `hA.proper` as an intermediate fact. Use `hB.proper` as an intermediate fact. Use `hA.smooth` as an intermediate fact. Use `hB.smooth` as an intermediate fact.

Take `⟨π, hπ, hψπ, -⟩` from `GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S o.t.G o'.t.G o.t.G ψ (𝟙 o.t.G ^ p ^ 2) hA hB inferInstance hψ hf he hs m1 fun k _ _ x z hz => by rw [MonObj.comp_pow, Category.comp_id, hker k x z hz]`. Establish `hepi : Epi ψ.left` using `Flat.epi_of_flat_of_surjective _`. Establish `canc : ∀ (Y : Over S) (f f' : o'.t.G ⟶ Y), ψ ≫ f = ψ ≫ f' → f = f'` using `fun Y f f' h => Over.OverMorphism.ext ((cancel_epi ψ.left).1 (congrArg (·.left) h))`. Establish `hπψ : π ≫ ψ = 𝟙 o'.t.G ^ p ^ 2` using `canc _ _ _ (by`. Rewrite using `[← Category.assoc, hψπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id])`.

Establish `hl : ψ.left ≫ π.left = (𝟙 o.t.G ^ p ^ 2).left` using `congrArg (·.left) hψπ`. Establish `hw : π.left ≫ o.t.G.hom = o'.t.G.hom` using `Over.w π`. Establish `hsep : IsSeparated π.left`. Establish `: IsSeparated (π.left ≫ o.t.G.hom)` using `by rw [hw]; infer_instance`. Conclude with `IsSeparated.of_comp _ o.t.G.hom`.

Establish `hlfp : LocallyOfFinitePresentation π.left`. Establish `: LocallyOfFinitePresentation (π.left ≫ o.t.G.hom)` using `by rw [hw]; infer_instance`. Conclude with `TangentCrit.locallyOfFinitePresentation_of_comp _ o.t.G.hom`. Take `⟨hf', he'⟩` from `isFinite_and_etale_of_comp_of_finite_etale_cover _ _ _ ψ.left π.left hf he hs (hl ▸ m2) (hl ▸ m3) hsep hlfp`. Establish `hs' : Surjective π.left`.

Establish `: Surjective (ψ.left ≫ π.left)` using `hl ▸ m4`. Conclude with `Surjective.of_comp ψ.left π.left`. Establish `hact' : ∀ a, o'.t.act.act a ≫ π = π ≫ o.t.act.act a` using `fun a => canc _ _ _ (by`. Use `o.t.act.hom a` as an intermediate fact. Rewrite using `[← Category.assoc, ← hact, Category.assoc, hψπ, ← Category.assoc, hψπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id])`.

Use `⟨π, hψπ, hπψ, ⟨hπ, hf', he', hs', hact', ?_⟩, fun p' hp' a => ?_⟩` and prove the remaining obligations. Establish `hL` using `o.t.PP.isLB`. Establish `hM` using `o'.t.PP.isLB`. Establish `hΘ : ∃ t : LB.Gen (Theta o.t.G o.t.PP.L), t.IsGen` using `⟨o.t.cub.t, o.t.cub.isGen⟩`. Establish `hn' : (lbPow o'.t.PP.L (p ^ 2)).IsLB` using `LB.isLB_linComb hM _ _`.

Establish `hψm : pull ψ.left (cls _ hM) = (p ^ 2) • cls _ hL`. Rewrite using `[← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]`. Conclude with `((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm`. Establish `h₁ : (cubeLB o.t.G ![fst o'.t.G o'.t.G ≫ π, snd o'.t.G o'.t.G ≫ π] o.t.PP.L).IsLB` using `LB.isLB_linComb hL _ _`. Establish `h₂ : (cubeLB o'.t.G ![fst o'.t.G o'.t.G, snd o'.t.G o'.t.G] (lbPow o'.t.PP.L (p ^ 2))).IsLB` using `LB.isLB_linComb hn' _ _`.

Establish `hN` using `LB.isLB_div h₁ h₂`. Establish `val : ∀ {T : Over S} (x y : T ⟶ o'.t.G), pull (lift x y).left (cls _ hN) = lam (cls _ hL) (x ≫ π) (y ≫ π) - (p ^ 2) • lam (cls _ hM) x y`. Introduce `T x y`. Rewrite using `[cls_div h₁ h₂, cls_cube_two hL, cls_cube_two hn', map_sub, pull_lam, pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, cls_lbPow hM, lam_nsmul]`. Establish `hN0 : cls _ hN = 0`.

Use `(cls_eq_zero_iff hN).2 (GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny S o.t.G o'.t.G ψ o'.t.PP.L _ (p ^ 2) hA hB hM o'.ample hN hψ hf he hs hn hu hker ?_ ?_ ?_)` and prove the remaining obligations. Use `(cls_eq_zero_iff (pull_isLB hN _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_pull hN, val, MonObj.one_comp, lam_one_left, lam_one_left, nsmul_zero, sub_self]`. Use `(cls_eq_zero_iff (pull_isLB hN _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_pull hN, val, MonObj.one_comp, lam_one_right, lam_one_right, nsmul_zero, sub_self]`.

Use `(cls_eq_zero_iff (pull_isLB hN _)).1 ?_` and prove the remaining obligations. Apply the tactic sequence `have e : ψ ⊗ₘ ψ = lift (fst _ _ ≫ ψ) (snd _ _ ≫ ψ) := by ext1 <;> simp`. Rewrite using `[cls_pull hN, e, val, Category.assoc, Category.assoc, hψπ, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, lam_pow_left hL hΘ, lam_pow_right hL hΘ, ← lam_pull, hψm, lam_nsmul, sub_self]`. Establish `e : cls _ hL = lam (cls _ hL) (𝟙 _) (o.t.act.act H.w0)` using `((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 o.t.prim).trans (cls_cube_two hL _ _ _)`. Establish `e' : cls _ hM = lam (cls _ hM) (𝟙 _) (o'.t.act.act H.w0)` using `((cls_eq_iff hM (LB.isLB_linComb hM _ _)).2 o'.t.prim).trans (cls_cube_two hM _ _ _)`.

Establish `key` using `val (𝟙 _) (o'.t.act.act H.w0)`. Rewrite `key` using `[hN0, map_zero, ← e', hact', Category.id_comp, eq_comm, sub_eq_zero]`. Rewrite using `[← cls_eq_iff hn' (pull_isLB hL _), cls_lbPow hM, cls_pull hL, ← key]`. Use `conv_rhs => rw [e, pull_lam, Category.comp_id]`. Establish `hM : ∀ a, o.eta (l.M • a) = 1` using `fun a => o.eta_ker _ (by`.

Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `Submodule.smul_mem_smul (HeckePoint.natCast_M_mem l) Submodule.mem_top)`. Establish `h2 : p ^ 2 * (p' * p') ≡ 1 [MOD l.M']`. Use `hp'.mul hp'` as an intermediate fact. Rewrite `this` using `[show p * p' * (p * p') = p ^ 2 * (p' * p') by ring]`. Then use the resulting hypothesis.

Rewrite using `[← (hlev p' hp' (p' • a)).1, ← (hlev p' hp' (p' • a)).2, Category.assoc, Category.assoc, hψπ, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, pow_eq_of_map_add _ o.eta_add, pow_eq_of_map_add _ o.etaA_add, smul_smul, smul_smul, _root_.mul_assoc, HeckePoint.eq …`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem exists_dual_isogeny : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o' : Ob D l s) (ψ : o.t.G ⟶ o'.t.G), p.Prime → ¬ p ∣ l.M' → IsIsog o o' p ψ → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G), z ≫ ψ = 1 → z ^ p ^ 2 = 1) → ∃ ψ' : o'.t.G ⟶ o.t.G, ψ ≫ ψ' = 𝟙 o.t.G ^ p ^ 2 ∧ ψ' ≫ ψ = 𝟙 o'.t.G ^ p ^ 2 ∧ IsIsog o' o p ψ' := by
  intro E _ _ _ H D l p S _ s o o' ψ hp _ ⟨⟨hψ, hf, he, hs, hact, hiso⟩, hlev⟩ hker
  have hA : IsAbelianScheme o.t.G := ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩
  have hB : IsAbelianScheme o'.t.G := ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  have hn : 0 < p ^ 2 := pow_pos hp.pos 2
  have hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    have h0 : IsUnit ((p ^ 2 : ℕ) : Γ(Sp (KA l), ⊤)) := by
      have := ((baseKA l).unit _ hn).map (Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom
      rwa [map_natCast] at this
    have := h0.map s.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨m1, m2, m3, m4⟩ := abelianScheme_id_pow_finite_etale_surjective S o.t.G (p ^ 2) hA hu
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  obtain ⟨π, hπ, hψπ, -⟩ := GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S o.t.G o'.t.G o.t.G ψ (𝟙 o.t.G ^ p ^ 2) hA hB inferInstance hψ hf he hs m1
    fun k _ _ x z hz => by rw [MonObj.comp_pow, Category.comp_id, hker k x z hz]
  have hepi : Epi ψ.left := Flat.epi_of_flat_of_surjective _
  have canc : ∀ (Y : Over S) (f f' : o'.t.G ⟶ Y), ψ ≫ f = ψ ≫ f' → f = f' := fun Y f f' h =>
    Over.OverMorphism.ext ((cancel_epi ψ.left).1 (congrArg (·.left) h))
  have hπψ : π ≫ ψ = 𝟙 o'.t.G ^ p ^ 2 := canc _ _ _ (by
    rw [← Category.assoc, hψπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id])
  have hl : ψ.left ≫ π.left = (𝟙 o.t.G ^ p ^ 2).left := congrArg (·.left) hψπ
  have hw : π.left ≫ o.t.G.hom = o'.t.G.hom := Over.w π
  have hsep : IsSeparated π.left := by
    have : IsSeparated (π.left ≫ o.t.G.hom) := by rw [hw]; infer_instance
    exact IsSeparated.of_comp _ o.t.G.hom
  have hlfp : LocallyOfFinitePresentation π.left := by
    have : LocallyOfFinitePresentation (π.left ≫ o.t.G.hom) := by rw [hw]; infer_instance
    exact TangentCrit.locallyOfFinitePresentation_of_comp _ o.t.G.hom
  obtain ⟨hf', he'⟩ := isFinite_and_etale_of_comp_of_finite_etale_cover _ _ _ ψ.left π.left hf he hs
    (hl ▸ m2) (hl ▸ m3) hsep hlfp
  have hs' : Surjective π.left := by
    have : Surjective (ψ.left ≫ π.left) := hl ▸ m4
    exact Surjective.of_comp ψ.left π.left
  have hact' : ∀ a, o'.t.act.act a ≫ π = π ≫ o.t.act.act a := fun a => canc _ _ _ (by
    have := o.t.act.hom a
    rw [← Category.assoc, ← hact, Category.assoc, hψπ, ← Category.assoc, hψπ, MonObj.pow_comp, MonObj.comp_pow,
      Category.id_comp, Category.comp_id])
  refine ⟨π, hψπ, hπψ, ⟨hπ, hf', he', hs', hact', ?_⟩, fun p' hp' a => ?_⟩
  · have hL := o.t.PP.isLB
    have hM := o'.t.PP.isLB
    have hΘ : ∃ t : LB.Gen (Theta o.t.G o.t.PP.L), t.IsGen := ⟨o.t.cub.t, o.t.cub.isGen⟩
    have hn' : (lbPow o'.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hM _ _
    have hψm : pull ψ.left (cls _ hM) = (p ^ 2) • cls _ hL := by
      rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
      exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
    have h₁ : (cubeLB o.t.G ![fst o'.t.G o'.t.G ≫ π, snd o'.t.G o'.t.G ≫ π] o.t.PP.L).IsLB :=
      LB.isLB_linComb hL _ _
    have h₂ : (cubeLB o'.t.G ![fst o'.t.G o'.t.G, snd o'.t.G o'.t.G] (lbPow o'.t.PP.L (p ^ 2))).IsLB :=
      LB.isLB_linComb hn' _ _
    have hN := LB.isLB_div h₁ h₂
    have val : ∀ {T : Over S} (x y : T ⟶ o'.t.G), pull (lift x y).left (cls _ hN) =
        lam (cls _ hL) (x ≫ π) (y ≫ π) - (p ^ 2) • lam (cls _ hM) x y := by
      intro T x y
      rw [cls_div h₁ h₂, cls_cube_two hL, cls_cube_two hn', map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, cls_lbPow hM, lam_nsmul]
    have hN0 : cls _ hN = 0 := by
      refine (cls_eq_zero_iff hN).2 (GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny S o.t.G o'.t.G ψ o'.t.PP.L _ (p ^ 2) hA hB hM o'.ample hN hψ hf he hs
        hn hu hker ?_ ?_ ?_)
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        rw [cls_pull hN, val, MonObj.one_comp, lam_one_left, lam_one_left, nsmul_zero, sub_self]
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        rw [cls_pull hN, val, MonObj.one_comp, lam_one_right, lam_one_right, nsmul_zero, sub_self]
      · refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
        have e : ψ ⊗ₘ ψ = lift (fst _ _ ≫ ψ) (snd _ _ ≫ ψ) := by ext1 <;> simp
        rw [cls_pull hN, e, val, Category.assoc, Category.assoc, hψπ, MonObj.comp_pow, MonObj.comp_pow,
          Category.comp_id, Category.comp_id, lam_pow_left hL hΘ, lam_pow_right hL hΘ, ← lam_pull, hψm,
          lam_nsmul, sub_self]
    have e : cls _ hL = lam (cls _ hL) (𝟙 _) (o.t.act.act H.w0) :=
      ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 o.t.prim).trans (cls_cube_two hL _ _ _)
    have e' : cls _ hM = lam (cls _ hM) (𝟙 _) (o'.t.act.act H.w0) :=
      ((cls_eq_iff hM (LB.isLB_linComb hM _ _)).2 o'.t.prim).trans (cls_cube_two hM _ _ _)
    have key := val (𝟙 _) (o'.t.act.act H.w0)
    rw [hN0, map_zero, ← e', hact', Category.id_comp, eq_comm, sub_eq_zero] at key
    rw [← cls_eq_iff hn' (pull_isLB hL _), cls_lbPow hM, cls_pull hL, ← key]
    conv_rhs => rw [e, pull_lam, Category.comp_id]
  · have hM : ∀ a, o.eta (l.M • a) = 1 := fun a => o.eta_ker _ (by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul (HeckePoint.natCast_M_mem l) Submodule.mem_top)
    have h2 : p ^ 2 * (p' * p') ≡ 1 [MOD l.M'] := by
      have := hp'.mul hp'
      rwa [show p * p' * (p * p') = p ^ 2 * (p' * p') by ring] at this
    rw [← (hlev p' hp' (p' • a)).1, ← (hlev p' hp' (p' • a)).2, Category.assoc, Category.assoc, hψπ,
      MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, pow_eq_of_map_add _ o.eta_add,
      pow_eq_of_map_add _ o.etaA_add, smul_smul, smul_smul, _root_.mul_assoc,
      HeckePoint.eq_of_modEq _ o.eta_add hM (h2.of_dvd (Nat.dvd_lcm_left _ _)),
      HeckePoint.eq_of_modEq _ o.etaA_add o.etaA_ker (h2.of_dvd (Nat.dvd_lcm_right _ _)), one_nsmul]
    exact ⟨rfl, rfl⟩

end GlobalTheory.HkFam
