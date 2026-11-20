import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsChartOfMaximal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DividesOfNormBoundedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundMatrixEntriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericallyCompleteEmbeddingStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.TriFrame.Near

/- English proof (translation)
Rewrite using `[valF, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem valF_eq {F : Type} [Field F] {X : Scheme.{0}} (w : Sp F ⟶ X) {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U)
    (a : Γ(X, U)) : valF w U a = ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (w.appLE U ⊤ h).hom) a := by
  rw [valF, dif_pos h]; rfl

/- English proof (translation)
Take `⟨W, hW, hxW, hle⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (U := U) hx`. Establish `e : spMap f ≫ X.fromSpecStalk x = spMap (f.comp (X.presheaf.germ W x hxW).hom) ≫ hW.fromSpec`. Rewrite using `[spMap_comp, Category.assoc]`. Conclude with `congrArg (spMap f ≫ ·) (hW.fromSpecStalk_eq_fromSpecStalk hxW).symm`. Establish `hW' : ⊤ ≤ (spMap f ≫ X.fromSpecStalk x) ⁻¹ᵁ W` using `GlobalTheory.ShFam.Pad.Pull.le_of_fromSpec hW e.symm`.

Rewrite using `[← FieldPtGlue.valF_restrict (U := U) hle hW' t, e, GlobalTheory.ShFam.Pad.Pull.valF_fromSpec]`. Conclude with `congrArg f (X.presheaf.germ_res_apply (homOfLE hle) x hxW t)`.
-/
theorem valF_fromSpecStalk {X : Scheme.{0}} {x : X} {F : Type} [Field F] (f : X.presheaf.stalk x →+* F)
    {U : X.Opens} (hx : x ∈ U) (t : Γ(X, U)) :
    valF (spMap f ≫ X.fromSpecStalk x) U t = f ((X.presheaf.germ U x hx).hom t) := by
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U) hx
  have e : spMap f ≫ X.fromSpecStalk x = spMap (f.comp (X.presheaf.germ W x hxW).hom) ≫ hW.fromSpec := by
    rw [spMap_comp, Category.assoc]
    exact congrArg (spMap f ≫ ·) (hW.fromSpecStalk_eq_fromSpecStalk hxW).symm
  have hW' : ⊤ ≤ (spMap f ≫ X.fromSpecStalk x) ⁻¹ᵁ W := GlobalTheory.ShFam.Pad.Pull.le_of_fromSpec hW e.symm
  rw [← FieldPtGlue.valF_restrict (U := U) hle hW' t, e, GlobalTheory.ShFam.Pad.Pull.valF_fromSpec]
  exact congrArg f (X.presheaf.germ_res_apply (homOfLE hle) x hxW t)

/- English proof (translation)
Take `⟨V, hV, hxV, -⟩` from `exists_isAffineOpen_mem_and_subset (X := B.X) (U := ⊤) (x := x) trivial`. Use `letI := B.X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)`. Use `hV.isLocalization_stalk ⟨x, hxV⟩` as an intermediate fact. Use `(IsLocalization.cardinalMk_le (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl).trans ?_` and prove the remaining obligations. Establish `hft` using `HasRingHomProperty.appLE @LocallyOfFiniteType B.str inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top`.

Use `HTLine.Dvd.mk_le_of_finiteType _ hft ?_` and prove the remaining obligations. Conclude with `(Cardinal.mk_le_of_surjective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2).trans hc`.
-/
theorem mk_stalk_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : Vert.Model O)
    (hc : Cardinal.mk O ≤ Cardinal.continuum) (x : B.X) :
    Cardinal.mk (B.X.presheaf.stalk x) ≤ Cardinal.continuum := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := B.X) (U := ⊤) (x := x) trivial
  letI := B.X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  refine (IsLocalization.cardinalMk_le (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl).trans ?_
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType B.str inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  refine HTLine.Dvd.mk_le_of_finiteType _ hft ?_
  exact (Cardinal.mk_le_of_surjective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2).trans hc

end GlobalTheory.TriFrame.Near

namespace GlobalTheory.TriFrame.Near

/- English proof (translation)
Introduce `p hp O _ _ _ _ hpO hcO B hN A V x hA hxV hxg r M ρ hM`. Set `R : Type` to `B.X.presheaf.stalk x`. Take `⟨_, _⟩ : IsDomain R ∧ IsIntegrallyClosed R` from `(GlobalTheory.isNormalScheme_iff _).1 hN x`. Set `K` to `FractionRing R`. Set `ι₀ : Sp R ⟶ B.X` to `B.X.fromSpecStalk x`.

Establish `hι (q : Sp R) : ι₀ q ⤳ x` using `(B.X.range_fromSpecStalk (x := x)).le ⟨q, rfl⟩`. Set `w₀ : Sp K ⟶ B.X` to `spMap (algebraMap R K) ≫ ι₀`. Establish `hη : w₀ (closedPoint K) = genericPoint B.X` using `(GlobalTheory.ShFam.Pad.GenId.maximal_of_stalk (IsFractionRing.injective R K) _ (genericPoint_specializes _)).symm`. Establish `hgen : ∀ U : B.X.Opens, genericPoint B.X ∈ U → ⊤ ≤ w₀ ⁻¹ᵁ U` using `fun U h => (FieldPtGlue.le_preimage_iff U).2 (hη ▸ h)`. Establish `hgx : ∀ U : B.X.Opens, x ∈ U → genericPoint B.X ∈ U` using `fun U h => (genericPoint_specializes x).mem_open U.isOpen h`.

Establish `hconst : ∀ n : ℕ, n ≠ 0 → (B.X.presheaf.germ ⊤ x trivial).hom (n : Γ(B.X, ⊤)) ≠ 0`. Introduce `n hn e`. Establish `h0 : (n : Γ(B.X, ⊤)) = 0` using `germ_injective_of_isIntegral B.X (U := ⊤) x trivial (e.trans (map_zero _).symm)`. Establish `hn' : (n : O) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Establish `hb` using `B.gen_le_basicOpen hn' B.genericPoint_mem_gen`.

Rewrite `hb` using `[Vert.Model.const, map_natCast, h0, Scheme.basicOpen_zero]`. Simplify using `at hb`. Establish `: CharZero K` using `charZero_of_inj_zero fun n hn => by`. Assume the negation of the conclusion as `h`. Use `hconst n h (IsFractionRing.injective R K ?_)` and prove the remaining obligations.

Rewrite using `[map_natCast, map_natCast, map_zero]`. Conclude with `hn`. Establish `hpR : (p : R) ∈ maximalIdeal R`. Establish `hp0 : (p : O) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hx' : x ∉ B.X.basicOpen (B.const (p : O))` using `by rwa [← B.gen_eq_basicOpen hp0 hpO]`.

Rewrite `hx'` using `[Scheme.mem_basicOpen B.X (B.const (p : O)) x trivial, Vert.Model.const, map_natCast, map_natCast]`. Conclude with `(mem_maximalIdeal _).2 hx'`. Establish `hcR : Cardinal.mk R ≤ Cardinal.continuum` using `mk_stalk_le B hcO x`. Take `⟨C₀, θ₀, h₁, h₂⟩` from `GlobalTheory.T.exists_spherically_complete_embedding p hp R K hpR hcR`. Set `ιT` to `Σ C : SCF p, {θ : K →+* C.S // ∀ a, ‖θ (algebraMap R K a)‖ ≤ 1}`.

Set `valA` to `valF w₀ (V ⊓ A)`. Establish `hVA : ⊤ ≤ w₀ ⁻¹ᵁ (V ⊓ A)` using `hgen _ ⟨hgx V hxV, hA⟩`. Establish `hnorm : ∀ (t : ιT) (i : Fin r), ‖t.2.1 (valA (ρ i))‖ * matNorm ((M.map valA).map t.2.1) i = 1`. Introduce and unpack `⟨C, θ, hθ⟩ i`. Set `ψ : R →+* intO C.S` to `(θ.comp (algebraMap R K)).codRestrict (intO C.S) hθ`.

Set `w : Sp (intO C.S) ⟶ B.X` to `spMap ψ ≫ ι₀`. Establish `e : spMap (intO C.S).subtype ≫ w = spMap θ ≫ w₀`. Simplify using `only [w, w₀, ← Category.assoc, ← spMap_comp]`. Both sides reduce to the same expression. Establish `hwV : ⊤ ≤ w ⁻¹ᵁ V` using `fun q _ => (hι _).mem_open V.isOpen hxV`.

Establish `hwA : ⊤ ≤ (spMap (intO C.S).subtype ≫ w) ⁻¹ᵁ A`. Rewrite using `[e, FieldPtGlue.le_preimage_iff]`. Express the relevant statement in the definitionally equal form `w₀ (spMap θ (closedPoint C.S)) ∈ A`. Rewrite using `[Subsingleton.elim (α := PrimeSpectrum K) (spMap θ (closedPoint C.S)) (closedPoint K), hη]`. Conclude with `hA`.

Establish `hf : valF (spMap θ ≫ w₀) (V ⊓ A) = θ ∘ valA`. Use function extensionality and compare the values at `fun a => GlobalTheory.ShFam.Pad.GenId.valF_map θ hVA a`. Use `hM C w hwV hwA i` as an intermediate fact. Rewrite `this` using `[e, hf]`. Rewrite using `[Matrix.map_map]`.

Conclude with `this`. Take `⟨P, htri, hdiag⟩` from `GlobalTheory.T.valuation_bound_matrix_entries R K ιT (fun t => ↥t.1.S) (fun t => t.2.1) (fun t a => t.2.2 a) (fun κ hκ => GlobalTheory.ShFam.Pad.GenId.mem_range_of_norm_le hp hpR hcR fun C ψ θ e => hκ ⟨C, θ, fun a => by`. Establish `h` using `congrArg (fun g => g a) e`. Simplify using `only [RingHom.comp_apply] at h`. Rewrite using `[h]`.

Conclude with `(ψ a).2⟩)`. Use the proof step `⟨⟨C₀, θ₀, h₁⟩, h₂⟩ r (M.map valA) (fun i => valA (ρ i)) hnorm`. Establish `hP1 : ∀ l j, ∃ (U : B.X.Opens) (hU : x ∈ U) (t : Γ(B.X, U)), (B.X.presheaf.germ U x hU).hom t = (P : Matrix (Fin r) (Fin r) R) l j` using `fun l j => B.X.presheaf.germ_exist _`. Establish `hP2 : ∀ l j, ∃ (U : B.X.Opens) (hU : x ∈ U) (t : Γ(B.X, U)), (B.X.presheaf.germ U x hU).hom t = ((P⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) l j` using `fun l j => B.X.presheaf.germ_exist _`. Use `choose U₁ hU₁ t₁ ht₁ using hP1`.

Use `choose U₂ hU₂ t₂ ht₂ using hP2`. Set `V' : B.X.Opens` to `V ⊓ Finset.univ.inf fun lj : Fin r × Fin r => U₁ lj.1 lj.2 ⊓ U₂ lj.1 lj.2`. Establish `hV'V : V' ≤ V` using `inf_le_left`. Establish `hxV' : x ∈ V'` using `⟨hxV, Finset.inf_induction (p := fun U : B.X.Opens => x ∈ U) trivial (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) fun lj _ => ⟨hU₁ _ _, hU₂ _ _⟩⟩`. Establish `l₁ : ∀ l j, V' ≤ U₁ l j` using `fun l j => inf_le_right.trans ((Finset.inf_le (f := fun lj : Fin r × Fin r => U₁ lj.1 lj.2 ⊓ U₂ lj.1 lj.2) (Finset.mem_univ (l, j))).trans inf_le_left)`.

Establish `l₂ : ∀ l j, V' ≤ U₂ l j` using `fun l j => inf_le_right.trans ((Finset.inf_le (f := fun lj : Fin r × Fin r => U₁ lj.1 lj.2 ⊓ U₂ lj.1 lj.2) (Finset.mem_univ (l, j))).trans inf_le_right)`. Set `P₁ : Matrix (Fin r) (Fin r) Γ(B.X, V')` to `fun l j => resG B.X (l₁ l j) (t₁ l j)`. Set `P₂ : Matrix (Fin r) (Fin r) Γ(B.X, V')` to `fun l j => resG B.X (l₂ l j) (t₂ l j)`. Set `g` to `(B.X.presheaf.germ V' x hxV').hom`. Establish `hg1 : P₁.map g = (P : Matrix (Fin r) (Fin r) R)` using `Matrix.ext fun l j => (B.X.presheaf.germ_res_apply (homOfLE (l₁ l j)) x hxV' (t₁ l j)).trans (ht₁ l j)`.

Establish `hg2 : P₂.map g = ((P⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)` using `Matrix.ext fun l j => (B.X.presheaf.germ_res_apply (homOfLE (l₂ l j)) x hxV' (t₂ l j)).trans (ht₂ l j)`. Establish `hinj : Function.Injective g` using `germ_injective_of_isIntegral B.X x hxV'`. Establish `hmap1 : (1 : Matrix (Fin r) (Fin r) Γ(B.X, V')).map g = 1` using `Matrix.map_one _ (map_zero g) (map_one g)`. Establish `hmul12 : P₁ * P₂ = 1`. Establish `h : (P₁ * P₂).map g = (1 : Matrix (Fin r) (Fin r) Γ(B.X, V')).map g`.

Rewrite using `[Matrix.map_mul, hg1, hg2, hmap1]`. Conclude with `P.mul_inv`. Use extensionality with `l j`. Conclude with `hinj (congrFun (congrFun h l) j)`. Establish `hmul21 : P₂ * P₁ = 1`.

Establish `h : (P₂ * P₁).map g = (1 : Matrix (Fin r) (Fin r) Γ(B.X, V')).map g`. Rewrite using `[Matrix.map_mul, hg1, hg2, hmap1]`. Conclude with `P.inv_mul`. Use extensionality with `l j`. Conclude with `hinj (congrFun (congrFun h l) j)`.

Set `P' : GL (Fin r) Γ(B.X, V')` to `⟨P₁, P₂, hmul12, hmul21⟩`. Establish `hV'A : ⊤ ≤ w₀ ⁻¹ᵁ (V' ⊓ A)` using `hgen _ ⟨hgx V' hxV', hA⟩`. Set `φ : Γ(B.X, V' ⊓ A) →+* K` to `(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (w₀.appLE (V' ⊓ A) ⊤ hV'A).hom`. Establish `hφ : ∀ a, φ a = valF w₀ _ a` using `fun a => (valF_eq w₀ hV'A a).symm`. Establish `hφinj : Function.Injective φ`.

Use `(injective_iff_map_eq_zero φ).2 fun a ha => by_contra fun hne => ?_` and prove the remaining obligations. Rewrite `ha` using `[hφ]`. Establish `hb : genericPoint B.X ∈ B.X.basicOpen a`. Establish `hne' : B.X.basicOpen a ≠ ⊥` using `mt (basicOpen_eq_bot_iff a).1 hne`. Take `⟨y, hy⟩` from `(TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne'`.

Conclude with `(genericPoint_specializes y).mem_open (B.X.basicOpen a).isOpen hy`. Conclude with `(FieldPtGlue.valF_ne_zero_iff hV'A a).2 (hgen _ hb) ha`. Establish `vP : ∀ l k, φ (resG B.X (inf_le_left : V' ⊓ A ≤ V') (P₁ l k)) = algebraMap R K ((P : Matrix (Fin r) (Fin r) R) l k)`. Introduce `l k`. Rewrite using `[hφ, FieldPtGlue.valF_restrict inf_le_left hV'A, valF_fromSpecStalk (algebraMap R K) hxV']`.

Conclude with `congrArg _ (congrFun (congrFun hg1 l) k)`. Establish `vM : ∀ a, φ (resG B.X (inf_le_inf_right A hV'V) a) = valA a` using `fun a => by`. Rewrite using `[hφ]`. Conclude with `FieldPtGlue.valF_restrict _ hV'A _`. Establish `key : ((P' : Matrix (Fin r) (Fin r) Γ(B.X, V')).map (resG B.X (inf_le_left : V' ⊓ A ≤ V')) * M.map (resG B.X (inf_le_inf_right A hV'V))).map φ = (P : Matrix (Fin r) (Fin r) R).map (algebraMap R K) * M.map valA`.

Rewrite using `[Matrix.map_mul, Matrix.map_map, Matrix.map_map]`. Use `congr 1`. Use extensionality with `l k`. Conclude with `vP l k`. Use extensionality with `k j`.

Conclude with `vM (M k j)`. Use `⟨V', hV'V, P', hxV', fun l j hjl => hφinj ?_, fun j => hφinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `(congrFun (congrFun key l) j).trans (htri l j hjl)`. Rewrite using `[map_mul, map_one, vM]`.

Conclude with `(congrArg (· * valA (ρ j)) (congrFun (congrFun key j) j)).trans (hdiag j)`.
-/
theorem exists_tri_near_special : ∀ (p : ℕ), p.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (p : O) ∈ maximalIdeal O → Cardinal.mk O ≤ Cardinal.continuum → ∀ (B : Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (A V : B.X.Opens) (x : B.X), genericPoint B.X ∈ A → x ∈ V → x ∉ B.gen → ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) Γ(B.X, V ⊓ A)) (ρ : Fin r → Γ(B.X, V ⊓ A)), (∀ (C : SCF p) (w : Sp ↥(intO ↥C.S) ⟶ B.X), ⊤ ≤ w ⁻¹ᵁ V → ⊤ ≤ (spMap (intO ↥C.S).subtype ≫ w) ⁻¹ᵁ A → ∀ i, ‖valF (spMap (intO ↥C.S).subtype ≫ w) (V ⊓ A) (ρ i)‖ * matNorm (M.map (valF (spMap (intO ↥C.S).subtype ≫ w) (V ⊓ A))) i = 1) → ∃ (V' : B.X.Opens) (h : V' ≤ V) (P : GL (Fin r) Γ(B.X, V')), x ∈ V' ∧ (∀ l j, j < l → ((P : Matrix (Fin r) (Fin r) Γ(B.X, V')).map (resG B.X (inf_le_left : V' ⊓ A ≤ V')) * M.map (resG B.X (inf_le_inf_right A h))) l j = 0) ∧ ∀ j, ((P : Matrix (Fin r) (Fin r) Γ(B.X, V')).map (resG B.X (inf_le_left : V' ⊓ A ≤ V')) * M.map (resG B.X (inf_le_inf_right A h))) j j * resG B.X (inf_le_inf_right A h) (ρ j) = 1 := by
  intro p hp O _ _ _ _ hpO hcO B hN A V x hA hxV hxg r M ρ hM
  let R : Type := B.X.presheaf.stalk x
  obtain ⟨_, _⟩ : IsDomain R ∧ IsIntegrallyClosed R := (GlobalTheory.isNormalScheme_iff _).1 hN x
  let K := FractionRing R
  let ι₀ : Sp R ⟶ B.X := B.X.fromSpecStalk x
  have hι (q : Sp R) : ι₀ q ⤳ x := (B.X.range_fromSpecStalk (x := x)).le ⟨q, rfl⟩
  let w₀ : Sp K ⟶ B.X := spMap (algebraMap R K) ≫ ι₀
  have hη : w₀ (closedPoint K) = genericPoint B.X :=
    (GlobalTheory.ShFam.Pad.GenId.maximal_of_stalk (IsFractionRing.injective R K) _ (genericPoint_specializes _)).symm
  have hgen : ∀ U : B.X.Opens, genericPoint B.X ∈ U → ⊤ ≤ w₀ ⁻¹ᵁ U := fun U h =>
    (FieldPtGlue.le_preimage_iff U).2 (hη ▸ h)
  have hgx : ∀ U : B.X.Opens, x ∈ U → genericPoint B.X ∈ U := fun U h =>
    (genericPoint_specializes x).mem_open U.isOpen h
  have hconst : ∀ n : ℕ, n ≠ 0 → (B.X.presheaf.germ ⊤ x trivial).hom (n : Γ(B.X, ⊤)) ≠ 0 := by
    intro n hn e
    have h0 : (n : Γ(B.X, ⊤)) = 0 := germ_injective_of_isIntegral B.X (U := ⊤) x trivial (e.trans (map_zero _).symm)
    have hn' : (n : O) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hb := B.gen_le_basicOpen hn' B.genericPoint_mem_gen
    rw [Vert.Model.const, map_natCast, h0, Scheme.basicOpen_zero] at hb
    simp at hb
  have : CharZero K := charZero_of_inj_zero fun n hn => by
    by_contra h
    refine hconst n h (IsFractionRing.injective R K ?_)
    rw [map_natCast, map_natCast, map_zero]
    exact hn
  have hpR : (p : R) ∈ maximalIdeal R := by
    have hp0 : (p : O) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hx' : x ∉ B.X.basicOpen (B.const (p : O)) := by rwa [← B.gen_eq_basicOpen hp0 hpO]
    rw [Scheme.mem_basicOpen B.X (B.const (p : O)) x trivial, Vert.Model.const, map_natCast, map_natCast] at hx'
    exact (mem_maximalIdeal _).2 hx'
  have hcR : Cardinal.mk R ≤ Cardinal.continuum := mk_stalk_le B hcO x
  obtain ⟨C₀, θ₀, h₁, h₂⟩ := GlobalTheory.T.exists_spherically_complete_embedding p hp R K hpR hcR
  let ιT := Σ C : SCF p, {θ : K →+* C.S // ∀ a, ‖θ (algebraMap R K a)‖ ≤ 1}
  let valA := valF w₀ (V ⊓ A)
  have hVA : ⊤ ≤ w₀ ⁻¹ᵁ (V ⊓ A) := hgen _ ⟨hgx V hxV, hA⟩
  have hnorm : ∀ (t : ιT) (i : Fin r),
      ‖t.2.1 (valA (ρ i))‖ * matNorm ((M.map valA).map t.2.1) i = 1 := by
    rintro ⟨C, θ, hθ⟩ i
    let ψ : R →+* intO C.S := (θ.comp (algebraMap R K)).codRestrict (intO C.S) hθ
    let w : Sp (intO C.S) ⟶ B.X := spMap ψ ≫ ι₀
    have e : spMap (intO C.S).subtype ≫ w = spMap θ ≫ w₀ := by
      simp only [w, w₀, ← Category.assoc, ← spMap_comp]; rfl
    have hwV : ⊤ ≤ w ⁻¹ᵁ V := fun q _ => (hι _).mem_open V.isOpen hxV
    have hwA : ⊤ ≤ (spMap (intO C.S).subtype ≫ w) ⁻¹ᵁ A := by
      rw [e, FieldPtGlue.le_preimage_iff]
      change w₀ (spMap θ (closedPoint C.S)) ∈ A
      rw [Subsingleton.elim (α := PrimeSpectrum K) (spMap θ (closedPoint C.S)) (closedPoint K), hη]
      exact hA
    have hf : valF (spMap θ ≫ w₀) (V ⊓ A) = θ ∘ valA :=
      funext fun a => GlobalTheory.ShFam.Pad.GenId.valF_map θ hVA a
    have := hM C w hwV hwA i
    rw [e, hf] at this
    rw [Matrix.map_map]
    exact this
  obtain ⟨P, htri, hdiag⟩ := GlobalTheory.T.valuation_bound_matrix_entries R K ιT (fun t => ↥t.1.S) (fun t => t.2.1) (fun t a => t.2.2 a)
    (fun κ hκ => GlobalTheory.ShFam.Pad.GenId.mem_range_of_norm_le hp hpR hcR fun C ψ θ e => hκ ⟨C, θ, fun a => by
      have h := congrArg (fun g => g a) e
      simp only [RingHom.comp_apply] at h
      rw [h]
      exact (ψ a).2⟩)
    ⟨⟨C₀, θ₀, h₁⟩, h₂⟩ r (M.map valA) (fun i => valA (ρ i)) hnorm
  have hP1 : ∀ l j, ∃ (U : B.X.Opens) (hU : x ∈ U) (t : Γ(B.X, U)),
      (B.X.presheaf.germ U x hU).hom t = (P : Matrix (Fin r) (Fin r) R) l j :=
    fun l j => B.X.presheaf.germ_exist _
  have hP2 : ∀ l j, ∃ (U : B.X.Opens) (hU : x ∈ U) (t : Γ(B.X, U)),
      (B.X.presheaf.germ U x hU).hom t = ((P⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) l j :=
    fun l j => B.X.presheaf.germ_exist _
  choose U₁ hU₁ t₁ ht₁ using hP1
  choose U₂ hU₂ t₂ ht₂ using hP2
  let V' : B.X.Opens := V ⊓ Finset.univ.inf fun lj : Fin r × Fin r => U₁ lj.1 lj.2 ⊓ U₂ lj.1 lj.2
  have hV'V : V' ≤ V := inf_le_left
  have hxV' : x ∈ V' := ⟨hxV, Finset.inf_induction (p := fun U : B.X.Opens => x ∈ U) trivial
    (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) fun lj _ => ⟨hU₁ _ _, hU₂ _ _⟩⟩
  have l₁ : ∀ l j, V' ≤ U₁ l j := fun l j =>
    inf_le_right.trans ((Finset.inf_le (f := fun lj : Fin r × Fin r => U₁ lj.1 lj.2 ⊓ U₂ lj.1 lj.2)
      (Finset.mem_univ (l, j))).trans inf_le_left)
  have l₂ : ∀ l j, V' ≤ U₂ l j := fun l j =>
    inf_le_right.trans ((Finset.inf_le (f := fun lj : Fin r × Fin r => U₁ lj.1 lj.2 ⊓ U₂ lj.1 lj.2)
      (Finset.mem_univ (l, j))).trans inf_le_right)
  let P₁ : Matrix (Fin r) (Fin r) Γ(B.X, V') := fun l j => resG B.X (l₁ l j) (t₁ l j)
  let P₂ : Matrix (Fin r) (Fin r) Γ(B.X, V') := fun l j => resG B.X (l₂ l j) (t₂ l j)
  let g := (B.X.presheaf.germ V' x hxV').hom
  have hg1 : P₁.map g = (P : Matrix (Fin r) (Fin r) R) := Matrix.ext fun l j =>
    (B.X.presheaf.germ_res_apply (homOfLE (l₁ l j)) x hxV' (t₁ l j)).trans (ht₁ l j)
  have hg2 : P₂.map g = ((P⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) := Matrix.ext fun l j =>
    (B.X.presheaf.germ_res_apply (homOfLE (l₂ l j)) x hxV' (t₂ l j)).trans (ht₂ l j)
  have hinj : Function.Injective g := germ_injective_of_isIntegral B.X x hxV'
  have hmap1 : (1 : Matrix (Fin r) (Fin r) Γ(B.X, V')).map g = 1 := Matrix.map_one _ (map_zero g) (map_one g)
  have hmul12 : P₁ * P₂ = 1 := by
    have h : (P₁ * P₂).map g = (1 : Matrix (Fin r) (Fin r) Γ(B.X, V')).map g := by
      rw [Matrix.map_mul, hg1, hg2, hmap1]; exact P.mul_inv
    ext l j; exact hinj (congrFun (congrFun h l) j)
  have hmul21 : P₂ * P₁ = 1 := by
    have h : (P₂ * P₁).map g = (1 : Matrix (Fin r) (Fin r) Γ(B.X, V')).map g := by
      rw [Matrix.map_mul, hg1, hg2, hmap1]; exact P.inv_mul
    ext l j; exact hinj (congrFun (congrFun h l) j)
  let P' : GL (Fin r) Γ(B.X, V') := ⟨P₁, P₂, hmul12, hmul21⟩
  have hV'A : ⊤ ≤ w₀ ⁻¹ᵁ (V' ⊓ A) := hgen _ ⟨hgx V' hxV', hA⟩
  let φ : Γ(B.X, V' ⊓ A) →+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (w₀.appLE (V' ⊓ A) ⊤ hV'A).hom
  have hφ : ∀ a, φ a = valF w₀ _ a := fun a => (valF_eq w₀ hV'A a).symm
  have hφinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a ha => by_contra fun hne => ?_
    rw [hφ] at ha
    have hb : genericPoint B.X ∈ B.X.basicOpen a := by
      have hne' : B.X.basicOpen a ≠ ⊥ := mt (basicOpen_eq_bot_iff a).1 hne
      obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne'
      exact (genericPoint_specializes y).mem_open (B.X.basicOpen a).isOpen hy
    exact (FieldPtGlue.valF_ne_zero_iff hV'A a).2 (hgen _ hb) ha
  have vP : ∀ l k, φ (resG B.X (inf_le_left : V' ⊓ A ≤ V') (P₁ l k)) =
      algebraMap R K ((P : Matrix (Fin r) (Fin r) R) l k) := by
    intro l k
    rw [hφ, FieldPtGlue.valF_restrict inf_le_left hV'A, valF_fromSpecStalk (algebraMap R K) hxV']
    exact congrArg _ (congrFun (congrFun hg1 l) k)
  have vM : ∀ a, φ (resG B.X (inf_le_inf_right A hV'V) a) = valA a := fun a => by
    rw [hφ]; exact FieldPtGlue.valF_restrict _ hV'A _
  have key : ((P' : Matrix (Fin r) (Fin r) Γ(B.X, V')).map (resG B.X (inf_le_left : V' ⊓ A ≤ V')) *
      M.map (resG B.X (inf_le_inf_right A hV'V))).map φ =
      (P : Matrix (Fin r) (Fin r) R).map (algebraMap R K) * M.map valA := by
    rw [Matrix.map_mul, Matrix.map_map, Matrix.map_map]
    congr 1
    · ext l k; exact vP l k
    · ext k j; exact vM (M k j)
  refine ⟨V', hV'V, P', hxV', fun l j hjl => hφinj ?_, fun j => hφinj ?_⟩
  · rw [map_zero]
    exact (congrFun (congrFun key l) j).trans (htri l j hjl)
  · rw [map_mul, map_one, vM]
    exact (congrArg (· * valA (ρ j)) (congrFun (congrFun key j) j)).trans (hdiag j)

end GlobalTheory.TriFrame.Near
