import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

/- English proof (translation)
Use `Fintype.ofFinite G` as an intermediate fact. Use `set P : Polynomial B := ∏ g : G, (Polynomial.X - Polynomial.C (g • b)) with hP`. Establish `hinvP : ∀ k : G, k • P = P`. Introduce `k`. Rewrite using `[hP, Finset.smul_prod']`.

Conclude with `Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by`. Rewrite using `[smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])`. Establish `hmap : P.map x = P.map y`. Use extensionality with `n`. Rewrite using `[Polynomial.coeff_map, Polynomial.coeff_map]`.

Apply `h` to reduce the goal to its premises. Introduce `g`. Rewrite using `[← Polynomial.coeff_smul, hinvP]`. Establish `hb : P.eval b = 0`. Rewrite using `[hP, Polynomial.eval_prod]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)`. Establish `h0 : (P.map y).eval (y b) = 0`. Rewrite using `[Polynomial.eval_map, Polynomial.eval₂_at_apply, hb, map_zero]`. Rewrite `h0` using `[← hmap, Polynomial.eval_map, hP, Polynomial.eval₂_finsetProd]`. Simplify using `only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h0`.

Take `⟨g, -, hg⟩` from `Finset.prod_eq_zero_iff.mp h0`. Conclude with `⟨g, sub_eq_zero.mp hg⟩`.
-/
theorem exists_smul_apply_eq_of_eq_on_invariants {G B D : Type*} [Group G] [Finite G] [CommRing B]
    [CommRing D] [IsDomain D] [MulSemiringAction G B] (x y : B →+* D)
    (h : ∀ b, (∀ g : G, g • b = b) → x b = y b) (b : B) : ∃ g : G, y b = x (g • b) := by
  classical
  have := Fintype.ofFinite G
  set P : Polynomial B := ∏ g : G, (Polynomial.X - Polynomial.C (g • b)) with hP
  have hinvP : ∀ k : G, k • P = P := by
    intro k
    rw [hP, Finset.smul_prod']
    exact Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by
      rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])
  have hmap : P.map x = P.map y := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    apply h
    intro g
    rw [← Polynomial.coeff_smul, hinvP]
  have hb : P.eval b = 0 := by
    rw [hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  have h0 : (P.map y).eval (y b) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hb, map_zero]
  rw [← hmap, Polynomial.eval_map, hP, Polynomial.eval₂_finsetProd] at h0
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h0
  obtain ⟨g, -, hg⟩ := Finset.prod_eq_zero_iff.mp h0
  exact ⟨g, sub_eq_zero.mp hg⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Use `choose c hc using hne`. Use `Fintype.ofFinite G` as an intermediate fact. Set `e` to `Fintype.equivFin G`.

Set `p : Polynomial B` to `∑ g : G, Polynomial.C (c g) * Polynomial.X ^ (e g : ℕ)`. Establish `hcoef : ∀ g, p.coeff (e g) = c g`. Introduce `g`. Simplify using `only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_eq_single g (fun g' _ hg' => if_neg (fun hh => hg' (e.injective (Fin.ext hh)).symm)) (by simp), if_pos rfl]`.

Establish `hyp : ∀ q : Polynomial B, (∀ g : G, g • q = q) → Polynomial.mapRingHom x q = Polynomial.mapRingHom y q`. Introduce `q hq`. Use extensionality with `n`. Simplify using `only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]`. Apply `h` to reduce the goal to its premises.

Introduce `g`. Rewrite using `[← Polynomial.coeff_smul, hq]`. Take `⟨g, hg⟩` from `exists_smul_apply_eq_of_eq_on_invariants (G := G) (Polynomial.mapRingHom x) (Polynomial.mapRingHom y) hyp p`. Establish `hgc` using `congrArg (fun q => q.coeff (e g)) hg`. Simplify using `only [Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_smul, hcoef] at hgc`.

Conclude with `hc g hgc`.
-/
theorem exists_smul_eq_of_eq_on_invariants {G B D : Type*} [Group G] [Finite G] [CommRing B]
    [CommRing D] [IsDomain D] [MulSemiringAction G B] (x y : B →+* D)
    (h : ∀ b, (∀ g : G, g • b = b) → x b = y b) : ∃ g : G, ∀ b, y b = x (g • b) := by
  classical
  by_contra hne
  push Not at hne
  choose c hc using hne
  have := Fintype.ofFinite G
  let e := Fintype.equivFin G
  let p : Polynomial B := ∑ g : G, Polynomial.C (c g) * Polynomial.X ^ (e g : ℕ)
  have hcoef : ∀ g, p.coeff (e g) = c g := by
    intro g
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single g (fun g' _ hg' => if_neg (fun hh => hg' (e.injective (Fin.ext hh)).symm))
      (by simp), if_pos rfl]
  have hyp : ∀ q : Polynomial B, (∀ g : G, g • q = q) →
      Polynomial.mapRingHom x q = Polynomial.mapRingHom y q := by
    intro q hq
    ext n
    simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    apply h
    intro g
    rw [← Polynomial.coeff_smul, hq]
  obtain ⟨g, hg⟩ := exists_smul_apply_eq_of_eq_on_invariants (G := G)
    (Polynomial.mapRingHom x) (Polynomial.mapRingHom y) hyp p
  have hgc := congrArg (fun q => q.coeff (e g)) hg
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_smul, hcoef] at hgc
  exact hc g hgc

/- English proof (translation)
Establish `hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).hom ⁻¹ᵁ π ⁻¹ᵁ W` using `fun g => by show _ ≤ ((ρ g).hom ≫ π) ⁻¹ᵁ W`. Rewrite using `[hπ g]`. Set `_` to `sectionsAction ρ _ hU`. Establish `hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)), g • s = (ρ g⁻¹).hom.appLE _ _ (hU g⁻¹) s` using `fun g s => rfl`. Establish `hy : ⊤ ≤ y ⁻¹ᵁ π ⁻¹ᵁ W` using `by show ⊤ ≤ (y ≫ π) ⁻¹ᵁ W`.

Rewrite using `[← hxy]`. Conclude with `hx`. Establish `key : ∀ (f f' : T ⟶ X') (_ : f = f') (h1 : ⊤ ≤ f ⁻¹ᵁ W) (h2 : ⊤ ≤ f' ⁻¹ᵁ W), f.appLE W ⊤ h1 = f'.appLE W ⊤ h2`. Introduce and unpack `f f' rfl h1 h2`. Both sides reduce to the same expression.

Establish `hagree : ∀ s : Γ(X, π ⁻¹ᵁ W), (∀ g : G, g • s = s) → (x.appLE (π ⁻¹ᵁ W) ⊤ hx).hom s = (y.appLE (π ⁻¹ᵁ W) ⊤ hy).hom s`. Introduce `s hs`. Establish `hinv' : IsInvariantSection ρ _ s`. Introduce `g`. Use `⟨hU g, ?_⟩` and prove the remaining obligations.

Use `hs g⁻¹` as an intermediate fact. Rewrite `this` using `[hact]`. Simplify `this` using `only [inv_inv]`. Take `⟨t, rfl⟩` from `hinv s hinv'`. Establish `e1` using `Scheme.Hom.comp_appLE x π W ⊤ hx`.

Establish `e2` using `Scheme.Hom.comp_appLE y π W ⊤ hy`. Use `congrArg (fun φ => φ.hom t) (key _ _ hxy hx hy)` as an intermediate fact. Rewrite `this` using `[e1, e2]`. Conclude with `this`. Take `⟨g, hg⟩` from `exists_smul_eq_of_eq_on_invariants (G := G) _ _ hagree`.

Use `⟨g⁻¹, ?_⟩` and prove the remaining obligations. Establish `h' : ⊤ ≤ (x ≫ (ρ g⁻¹).hom) ⁻¹ᵁ π ⁻¹ᵁ W` using `by show ⊤ ≤ x ⁻¹ᵁ ((ρ g⁻¹).hom ⁻¹ᵁ π ⁻¹ᵁ W)`. Conclude with `hx.trans (x.preimage_mono (hU g⁻¹))`. Establish `heq : y.appLE (π ⁻¹ᵁ W) ⊤ hy = (x ≫ (ρ g⁻¹).hom).appLE (π ⁻¹ᵁ W) ⊤ h'`. Use extensionality with `s`.

Rewrite using `[← Scheme.Hom.appLE_comp_appLE x (ρ g⁻¹).hom _ _ _ (hU g⁻¹) hx]`. Rewrite using `[hg s, hact]`. Both sides reduce to the same expression. Establish `hA : IsAffineOpen (π ⁻¹ᵁ W)` using `hW.preimage π`. Establish `h1` using `IsAffineOpen.SpecMap_appLE_fromSpec y hA (isAffineOpen_top T) hy`.

Establish `h2` using `IsAffineOpen.SpecMap_appLE_fromSpec (x ≫ (ρ g⁻¹).hom) hA (isAffineOpen_top T) h'`. Rewrite `h1` using `[heq]`. Rewrite `h1`, `h2` using `[IsAffineOpen.fromSpec_top]`. Conclude with `(cancel_epi _).1 (h1.symm.trans h2)`.
-/
theorem exists_aut_of_comp_eq_of_invariant {G : Type*} [Group G] [Finite G] {X X' T : Scheme.{0}}
    (ρ : G →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    {W : X'.Opens} (hW : IsAffineOpen W)
    (hinv : ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    [IsAffine T] [IsIntegral T] (x y : T ⟶ X) (hxy : x ≫ π = y ≫ π)
    (hx : ⊤ ≤ x ⁻¹ᵁ π ⁻¹ᵁ W) : ∃ g, y = x ≫ (ρ g).hom := by
  have hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).hom ⁻¹ᵁ π ⁻¹ᵁ W := fun g => by
    show _ ≤ ((ρ g).hom ≫ π) ⁻¹ᵁ W
    rw [hπ g]
  let _ := sectionsAction ρ _ hU
  have hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)),
      g • s = (ρ g⁻¹).hom.appLE _ _ (hU g⁻¹) s := fun g s => rfl
  have hy : ⊤ ≤ y ⁻¹ᵁ π ⁻¹ᵁ W := by
    show ⊤ ≤ (y ≫ π) ⁻¹ᵁ W
    rw [← hxy]
    exact hx
  have key : ∀ (f f' : T ⟶ X') (_ : f = f') (h1 : ⊤ ≤ f ⁻¹ᵁ W) (h2 : ⊤ ≤ f' ⁻¹ᵁ W),
      f.appLE W ⊤ h1 = f'.appLE W ⊤ h2 := by
    rintro f f' rfl h1 h2
    rfl
  have hagree : ∀ s : Γ(X, π ⁻¹ᵁ W), (∀ g : G, g • s = s) →
      (x.appLE (π ⁻¹ᵁ W) ⊤ hx).hom s = (y.appLE (π ⁻¹ᵁ W) ⊤ hy).hom s := by
    intro s hs
    have hinv' : IsInvariantSection ρ _ s := by
      intro g
      refine ⟨hU g, ?_⟩
      have := hs g⁻¹
      rw [hact] at this
      simpa only [inv_inv] using this
    obtain ⟨t, rfl⟩ := hinv s hinv'
    have e1 := Scheme.Hom.comp_appLE x π W ⊤ hx
    have e2 := Scheme.Hom.comp_appLE y π W ⊤ hy
    have := congrArg (fun φ => φ.hom t) (key _ _ hxy hx hy)
    rw [e1, e2] at this
    exact this
  obtain ⟨g, hg⟩ := exists_smul_eq_of_eq_on_invariants (G := G) _ _ hagree
  refine ⟨g⁻¹, ?_⟩
  have h' : ⊤ ≤ (x ≫ (ρ g⁻¹).hom) ⁻¹ᵁ π ⁻¹ᵁ W := by
    show ⊤ ≤ x ⁻¹ᵁ ((ρ g⁻¹).hom ⁻¹ᵁ π ⁻¹ᵁ W)
    exact hx.trans (x.preimage_mono (hU g⁻¹))
  have heq : y.appLE (π ⁻¹ᵁ W) ⊤ hy = (x ≫ (ρ g⁻¹).hom).appLE (π ⁻¹ᵁ W) ⊤ h' := by
    ext s
    rw [← Scheme.Hom.appLE_comp_appLE x (ρ g⁻¹).hom _ _ _ (hU g⁻¹) hx]
    rw [hg s, hact]
    rfl
  have hA : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec y hA (isAffineOpen_top T) hy
  have h2 := IsAffineOpen.SpecMap_appLE_fromSpec (x ≫ (ρ g⁻¹).hom) hA (isAffineOpen_top T) h'
  rw [heq] at h1
  rw [IsAffineOpen.fromSpec_top] at h1 h2
  exact (cancel_epi _).1 (h1.symm.trans h2)

/- English proof (translation)
Rewrite using `[isIntegralHom_iff]`. Use `⟨inferInstance, fun W hW => ?_⟩` and prove the remaining obligations. Establish `hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).hom ⁻¹ᵁ π ⁻¹ᵁ W` using `fun g => by show _ ≤ ((ρ g).hom ≫ π) ⁻¹ᵁ W`. Rewrite using `[hπ g]`. Set `_` to `sectionsAction ρ _ hU`.

Establish `hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)), g • s = (ρ g⁻¹).hom.appLE _ _ (hU g⁻¹) s` using `fun g s => rfl`. Use `Fintype.ofFinite G` as an intermediate fact. Introduce `s`. Break down `subsingleton_or_nontrivial Γ(X, π ⁻¹ᵁ W) with hsub | hnt` into its components or cases. Rewrite using `[Subsingleton.elim s 0]`.

Conclude with `RingHom.isIntegralElem_zero _`. Use `set P : Polynomial Γ(X, π ⁻¹ᵁ W) := ∏ g : G, (Polynomial.X - Polynomial.C (g • s)) with hP`. Establish `hinvP : ∀ k : G, k • P = P`. Introduce `k`. Rewrite using `[hP, Finset.smul_prod']`.

Conclude with `Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by`. Rewrite using `[smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])`. Establish `hlift : P ∈ Polynomial.lifts (π.app W).hom`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`.

Apply `hinv W hW` to reduce the goal to its premises. Introduce `g`. Use `⟨hU g, ?_⟩` and prove the remaining obligations. Use `congrArg (fun q => q.coeff n) (hinvP g⁻¹)` as an intermediate fact. Simplify using `only [Polynomial.coeff_smul] at this`.

Rewrite `this` using `[hact]`. Simplify `this` using `only [inv_inv]`. Establish `hmonic : P.Monic` using `Polynomial.monic_prod_of_monic _ _ (fun g _ => Polynomial.monic_X_sub_C _)`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hlift hmonic`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Polynomial.eval_map, hq, hP, Polynomial.eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)`.
-/
theorem isIntegralHom_of_invariant {G : Type*} [Group G] [Finite G] {X X' : Scheme.{0}}
    (ρ : G →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W)) : IsIntegralHom π := by
  rw [isIntegralHom_iff]
  refine ⟨inferInstance, fun W hW => ?_⟩
  have hU : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).hom ⁻¹ᵁ π ⁻¹ᵁ W := fun g => by
    show _ ≤ ((ρ g).hom ≫ π) ⁻¹ᵁ W
    rw [hπ g]
  let _ := sectionsAction ρ _ hU
  have hact : ∀ (g : G) (s : Γ(X, π ⁻¹ᵁ W)),
      g • s = (ρ g⁻¹).hom.appLE _ _ (hU g⁻¹) s := fun g s => rfl
  classical
  have := Fintype.ofFinite G
  intro s
  rcases subsingleton_or_nontrivial Γ(X, π ⁻¹ᵁ W) with hsub | hnt
  · rw [Subsingleton.elim s 0]
    exact RingHom.isIntegralElem_zero _
  set P : Polynomial Γ(X, π ⁻¹ᵁ W) := ∏ g : G, (Polynomial.X - Polynomial.C (g • s)) with hP
  have hinvP : ∀ k : G, k • P = P := by
    intro k
    rw [hP, Finset.smul_prod']
    exact Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by
      rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])
  have hlift : P ∈ Polynomial.lifts (π.app W).hom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    apply hinv W hW
    intro g
    refine ⟨hU g, ?_⟩
    have := congrArg (fun q => q.coeff n) (hinvP g⁻¹)
    simp only [Polynomial.coeff_smul] at this
    rw [hact] at this
    simpa only [inv_inv] using this
  have hmonic : P.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun g _ => Polynomial.monic_X_sub_C _)
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, hP, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)

/- English proof (translation)
Introduce `Γ _ _ X X' ρ π ⟨hAff, hπ, hV⟩`. Establish `hinvAll : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W)`. Introduce `W _ s hs`. Apply `(hV W).2 s` to reduce the goal to its premises. Introduce `g h`.

Take `⟨h', e⟩` from `hs g`. Conclude with `e`. Establish `hInt : IsIntegralHom π` using `isIntegralHom_of_invariant ρ π hπ hinvAll`. Establish `hfield : ∀ (k : Type) [Field k] (x y : Sp k ⟶ X), x ≫ π = y ≫ π → ∃ g, y = x ≫ (ρ g).hom`. Introduce `k _ x y hxy`.

Set `p₀ : Sp k` to `⟨⊥, Ideal.isPrime_bot⟩`. Take `⟨W, hW, hmem, -⟩` from `exists_isAffineOpen_mem_and_subset (x := (x ≫ π) p₀) (U := ⊤) trivial`. Use `exists_aut_of_comp_eq_of_invariant ρ π hπ hW (hinvAll W hW) x y hxy ?_` and prove the remaining obligations. Introduce `p _`. Establish `hp : p = p₀` using `Subsingleton.elim _ _`.

Substitute `hp` using the available equality. Conclude with `hmem`. Establish `hpts : ∀ x y : X, π x = π y → ∃ g, y = (ρ g).hom x`. Introduce `x y hxy`. Take `⟨z, hz1, hz2⟩` from `Scheme.Pullback.exists_preimage_pullback x y hxy`.

Establish `hab : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) ≫ π = (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) ≫ π`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition]`. Take `⟨g, hg⟩` from `hfield ((pullback π π).residueField z) _ _ hab`. Use `⟨g, ?_⟩` and prove the remaining obligations. Set `s : Spec ((pullback π π).residueField z)` to `⟨⊥, Ideal.isPrime_bot⟩`.

Establish `ha : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) s = x` using `by show pullback.fst π π (Scheme.fromSpecResidueField _ z s) = x`. Rewrite using `[Scheme.fromSpecResidueField_apply]`. Conclude with `hz1`. Establish `hb : (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) s = y` using `by show pullback.snd π π (Scheme.fromSpecResidueField _ z s) = y`. Rewrite using `[Scheme.fromSpecResidueField_apply]`.

Conclude with `hz2`. Rewrite using `[← hb, hg, ← ha]`. Both sides reduce to the same expression. Establish `hsurj : Surjective π`. Rewrite using `[surjective_iff]`.

Introduce `y`. Take `⟨W, hW, hmem, -⟩` from `exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial`. Establish `hA : IsAffineOpen (π ⁻¹ᵁ W)` using `hW.preimage π`. Establish `heq` using `IsAffineOpen.SpecMap_appLE_fromSpec π hW hA le_rfl`. Establish `hmem' : y ∈ Set.range hW.fromSpec`.

Rewrite using `[hW.range_fromSpec]`. Conclude with `hmem`. Take `⟨p, rfl⟩` from `hmem'`. Establish `hint : (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom.IsIntegral`. Rewrite using `[← Scheme.Hom.app_eq_appLE]`.

Conclude with `hInt.isIntegral_app W hW`. Establish `hinj : Function.Injective (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom`. Rewrite using `[← Scheme.Hom.app_eq_appLE]`. Conclude with `(hV W).1`. Take `⟨q, hq⟩` from `hint.comap_surjective hinj p`.

Use `⟨hA.fromSpec q, ?_⟩` and prove the remaining obligations. Use `congrArg (fun f => f q) heq` as an intermediate fact. Rewrite using `[← hq]`. Conclude with `this.symm`. Establish `hopen : ∀ U : X.Opens, (∀ g, (ρ g).hom ⁻¹ᵁ U = U) → ∃ V : X'.Opens, π ⁻¹ᵁ V = U`.

Introduce `U hU`. Establish `hcl : IsClosed (π '' (U : Set X)ᶜ)` using `π.isClosedMap _ U.isOpen.isClosed_compl`. Use `⟨⟨(π '' (U : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Use `show π x ∈ (π '' (U : Set X)ᶜ)ᶜ ↔ x ∈ U`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hx`. Conclude with `h ⟨x, hx, rfl⟩`. Introduce and unpack `hx ⟨y, hy, hxy⟩`.

Take `⟨g, rfl⟩` from `hpts x y hxy.symm`. Apply `hy` to reduce the goal to its premises. Establish `hx' : x ∈ (ρ g).hom ⁻¹ᵁ U`. Rewrite using `[hU g]`. Conclude with `hx`.

Conclude with `hx'`. Conclude with `⟨hInt, hsurj, hpts, hfield, hopen⟩`.
-/
theorem quotient_isIntegral_surjective_orbits :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsIntegralHom π ∧ Surjective π ∧ (∀ x y : X, π x = π y → ∃ g, y = (ρ g).hom x) ∧ (∀ (k : Type) [Field k] (x y : Sp k ⟶ X), x ≫ π = y ≫ π → ∃ g, y = x ≫ (ρ g).hom) ∧ ∀ U : X.Opens, (∀ g, (ρ g).hom ⁻¹ᵁ U = U) → ∃ V : X'.Opens, π ⁻¹ᵁ V = U := by
  intro Γ _ _ X X' ρ π ⟨hAff, hπ, hV⟩
  have hinvAll : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W) := by
    intro W _ s hs
    apply (hV W).2 s
    intro g h
    obtain ⟨h', e⟩ := hs g
    exact e
  have hInt : IsIntegralHom π := isIntegralHom_of_invariant ρ π hπ hinvAll
  have hfield : ∀ (k : Type) [Field k] (x y : Sp k ⟶ X), x ≫ π = y ≫ π →
      ∃ g, y = x ≫ (ρ g).hom := by
    intro k _ x y hxy
    let p₀ : Sp k := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨W, hW, hmem, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := (x ≫ π) p₀) (U := ⊤) trivial
    refine exists_aut_of_comp_eq_of_invariant ρ π hπ hW (hinvAll W hW) x y hxy ?_
    intro p _
    have hp : p = p₀ := Subsingleton.elim _ _
    subst hp
    exact hmem
  have hpts : ∀ x y : X, π x = π y → ∃ g, y = (ρ g).hom x := by
    intro x y hxy
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
    have hab : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) ≫ π =
        (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) ≫ π := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨g, hg⟩ := hfield ((pullback π π).residueField z) _ _ hab
    refine ⟨g, ?_⟩
    let s : Spec ((pullback π π).residueField z) := ⟨⊥, Ideal.isPrime_bot⟩
    have ha : (Scheme.fromSpecResidueField _ z ≫ pullback.fst π π) s = x := by
      show pullback.fst π π (Scheme.fromSpecResidueField _ z s) = x
      rw [Scheme.fromSpecResidueField_apply]
      exact hz1
    have hb : (Scheme.fromSpecResidueField _ z ≫ pullback.snd π π) s = y := by
      show pullback.snd π π (Scheme.fromSpecResidueField _ z s) = y
      rw [Scheme.fromSpecResidueField_apply]
      exact hz2
    rw [← hb, hg, ← ha]
    rfl
  have hsurj : Surjective π := by
    rw [surjective_iff]
    intro y
    obtain ⟨W, hW, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    have hA : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
    have heq := IsAffineOpen.SpecMap_appLE_fromSpec π hW hA le_rfl
    have hmem' : y ∈ Set.range hW.fromSpec := by
      rw [hW.range_fromSpec]
      exact hmem
    obtain ⟨p, rfl⟩ := hmem'
    have hint : (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom.IsIntegral := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact hInt.isIntegral_app W hW
    have hinj : Function.Injective (π.appLE W (π ⁻¹ᵁ W) le_rfl).hom := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact (hV W).1
    obtain ⟨q, hq⟩ := hint.comap_surjective hinj p
    refine ⟨hA.fromSpec q, ?_⟩
    have := congrArg (fun f => f q) heq
    rw [← hq]
    exact this.symm
  have hopen : ∀ U : X.Opens, (∀ g, (ρ g).hom ⁻¹ᵁ U = U) → ∃ V : X'.Opens, π ⁻¹ᵁ V = U := by
    intro U hU
    have hcl : IsClosed (π '' (U : Set X)ᶜ) := π.isClosedMap _ U.isOpen.isClosed_compl
    refine ⟨⟨(π '' (U : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩, ?_⟩
    ext x
    show π x ∈ (π '' (U : Set X)ᶜ)ᶜ ↔ x ∈ U
    constructor
    · intro h
      by_contra hx
      exact h ⟨x, hx, rfl⟩
    · rintro hx ⟨y, hy, hxy⟩
      obtain ⟨g, rfl⟩ := hpts x y hxy.symm
      apply hy
      have hx' : x ∈ (ρ g).hom ⁻¹ᵁ U := by
        rw [hU g]
        exact hx
      exact hx'
  exact ⟨hInt, hsurj, hpts, hfield, hopen⟩

end GlobalTheory
