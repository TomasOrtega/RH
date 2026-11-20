import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveSubbundleCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelNonvanishingWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMapExtendsAfterScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleMapDeterminedGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSubspaceMapExtendsStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

namespace GlobalTheory.CorankPair

open TopologicalSpace ReciprocityTheory.ChartRestriction.G GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier
open GlobalTheory.TrueGeo.SmallSec (fnMap fnMap_fnOf)

/- English proof (translation)
Establish `hs : smulHom ((Scheme.Modules.pullback f.f).obj E') (Z₁.const g) = (Scheme.Modules.pullback f.f).map (smulHom E' (Z.const g))`. Rewrite using `[VB.pullback_map_smulHom, GlobalTheory.Vert.Model.appTop_const f.comp_str]`. Establish `e₁` using `NatIso.naturality_2 (GlobalTheory.Vert.Model.GenIso.genPullIso f.comp_str) u`. Establish `e₂` using `NatIso.naturality_2 (GlobalTheory.Vert.Model.GenIso.genPullIso f.comp_str) (smulHom E' (Z.const g))`. Simplify using `only [Functor.comp_map] at e₁ e₂`.

Rewrite using `[hs, ← e₁, ← e₂, h]`. Simplify using `[GlobalTheory.Vert.Model.GenIso.pull]`.
-/
theorem genRes_pullback_map {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Z Z₁ : GlobalTheory.Vert.Model O} (f : GlobalTheory.Vert.Model.Hom Z₁ Z) {E E' : Z.X.Modules} (φ : Z.GenIso E E')
    (u : E ⟶ E') (g : O) (h : Z.genRes.map u = φ.hom ≫ Z.genRes.map (smulHom E' (Z.const g))) :
    Z₁.genRes.map ((Scheme.Modules.pullback f.f).map u) =
      (φ.pull f.comp_str).hom ≫ Z₁.genRes.map (smulHom _ (Z₁.const g)) := by
  have hs : smulHom ((Scheme.Modules.pullback f.f).obj E') (Z₁.const g) =
      (Scheme.Modules.pullback f.f).map (smulHom E' (Z.const g)) := by
    rw [VB.pullback_map_smulHom, GlobalTheory.Vert.Model.appTop_const f.comp_str]
  have e₁ := NatIso.naturality_2 (GlobalTheory.Vert.Model.GenIso.genPullIso f.comp_str) u
  have e₂ := NatIso.naturality_2 (GlobalTheory.Vert.Model.GenIso.genPullIso f.comp_str) (smulHom E' (Z.const g))
  simp only [Functor.comp_map] at e₁ e₂
  rw [hs, ← e₁, ← e₂, h]
  simp [GlobalTheory.Vert.Model.GenIso.pull]

/- English proof (translation)
Rewrite using `[← cancel_mono i, Category.assoc, hv₂, reassoc_of% hv, h, Category.assoc, smulHom_comp i b, ← Category.assoc (smulHom K a), smulHom_comp i a, Category.assoc]`.
-/
theorem comp_eq_smul {X : Scheme.{0}} {K K' F F' : X.Modules} (i : K ⟶ F) [Mono i] (i' : K' ⟶ F')
    (v : K ⟶ K') (v₂ : K' ⟶ K) (uf : F ⟶ F') (u₂f : F' ⟶ F) (a b : Γ(X, ⊤)) (hv : v ≫ i' = i ≫ uf)
    (hv₂ : v₂ ≫ i = i' ≫ u₂f) (h : uf ≫ u₂f = smulHom F a ≫ smulHom F b) :
    v ≫ v₂ = smulHom K a ≫ smulHom K b := by
  rw [← cancel_mono i, Category.assoc, hv₂, reassoc_of% hv, h, Category.assoc, smulHom_comp i b,
    ← Category.assoc (smulHom K a), smulHom_comp i a, Category.assoc]

/- English proof (translation)
Use `GlobalTheory.Vert.Model.isIso_genRes_map_smulHom K' hg` as an intermediate fact. Use `GlobalTheory.Vert.Model.isIso_genRes_map_smulHom F' hg` as an intermediate fact. Establish `e₁ : inv (Z.genRes.map (smulHom K' (Z.const g))) ≫ Z.genRes.map i' = Z.genRes.map i' ≫ inv (Z.genRes.map (smulHom F' (Z.const g)))`. Rewrite using `[IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, ← Functor.map_comp, ← Functor.map_comp, smulHom_comp]`. Simplify using `only [Iso.trans_hom, asIso_hom, GlobalTheory.Vert.Model.GenIso.smul, GlobalTheory.Vert.Model.GenIso.ofHom, Iso.symm_hom, asIso_inv, Category.assoc]`.

Rewrite using `[e₁, ← Category.assoc, ← Functor.map_comp, hv, Functor.map_comp, Category.assoc, e₂, Category.assoc, IsIso.hom_inv_id, Category.comp_id]`.
-/
theorem final_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : GlobalTheory.Vert.Model O}
    {F F' K K' : Z.X.Modules} (i : K ⟶ F) (i' : K' ⟶ F') (v : K ⟶ K') (uf : F ⟶ F') (φ' : Z.GenIso F F')
    (g : O) (hg : g ≠ 0) [IsIso (Z.genRes.map v)] (hv : v ≫ i' = i ≫ uf)
    (e₂ : Z.genRes.map uf = φ'.hom ≫ Z.genRes.map (smulHom F' (Z.const g))) :
    (asIso (Z.genRes.map v) ≪≫ GlobalTheory.Vert.Model.GenIso.smul K' g hg).hom ≫ Z.genRes.map i' =
      Z.genRes.map i ≫ φ'.hom := by
  have := GlobalTheory.Vert.Model.isIso_genRes_map_smulHom K' hg
  have := GlobalTheory.Vert.Model.isIso_genRes_map_smulHom F' hg
  have e₁ : inv (Z.genRes.map (smulHom K' (Z.const g))) ≫ Z.genRes.map i' =
      Z.genRes.map i' ≫ inv (Z.genRes.map (smulHom F' (Z.const g))) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, ← Functor.map_comp, ← Functor.map_comp,
      smulHom_comp]
  simp only [Iso.trans_hom, asIso_hom, GlobalTheory.Vert.Model.GenIso.smul, GlobalTheory.Vert.Model.GenIso.ofHom, Iso.symm_hom,
    asIso_inv, Category.assoc]
  rw [e₁, ← Category.assoc, ← Functor.map_comp, hv, Functor.map_comp, Category.assoc, e₂, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/- English proof (translation)
Take `⟨V, hV, s, rfl⟩` from `F.presheaf.exists_germ_eq t`. Rewrite using `[stalkLinear_germ, smulHom_app_apply, germ_smul]`. Conclude with `congrArg (· • _) (X.presheaf.germ_res_apply _ x hV a)`.
-/
theorem stalk_smul {X : Scheme.{0}} {F : X.Modules} (a : Γ(X, ⊤)) (x : X) (t : (F.presheaf.stalk x :)) :
    stalkLinear (smulHom F a) x t = X.presheaf.germ ⊤ x trivial a • t := by
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [stalkLinear_germ, smulHom_app_apply, germ_smul]
  exact congrArg (· • _) (X.presheaf.germ_res_apply _ x hV a)

/- English proof (translation)
Introduce `O _ _ _ p _ _ _ B hB r E E' φ hE hE'`. Use `hE.isQuasicoherent` as an intermediate fact. Use `hE'.isQuasicoherent` as an intermediate fact. Take `⟨g, u, hg, hu⟩` from `GlobalTheory.T.generic_map_extends_after_scaling O B E E' _ _ hE hE' φ.hom`. Take `⟨g₂, u₂, hg₂, hu₂⟩` from `GlobalTheory.T.generic_map_extends_after_scaling O B E' E _ _ hE' hE φ.inv`.

Establish `huu : u₂ ≫ u = smulHom E' (B.const g₂) ≫ smulHom E' (B.const g)`. Use `GlobalTheory.T.vector_bundle_map_determined_generic O B _ _ _ _ _ hE' ?_` and prove the remaining obligations. Rewrite using `[Functor.map_comp, Functor.map_comp, hu₂, hu, Category.assoc, ← Category.assoc (B.genRes.map _), VB.pullback_map_smulHom, smulHom_comp, Category.assoc, Iso.inv_hom_id_assoc]`. Simplify using `only [VB.pullback_map_smulHom]`. Establish `huu₂ : u ≫ u₂ = smulHom E (B.const g) ≫ smulHom E (B.const g₂)`.

Use `GlobalTheory.T.vector_bundle_map_determined_generic O B _ _ _ _ _ hE ?_` and prove the remaining obligations. Rewrite using `[Functor.map_comp, Functor.map_comp, hu₂, hu, Category.assoc, ← Category.assoc (B.genRes.map _), VB.pullback_map_smulHom, smulHom_comp, Category.assoc, Iso.hom_inv_id_assoc]`. Simplify using `only [VB.pullback_map_smulHom]`. Use `choose U e hx he using id hE`. Use `choose U' e' hx' he' using id hE'`.

Take `⟨T, hT⟩` from `exists_finset_iSup_eq_top U hx`. Take `⟨T', hT'⟩` from `exists_finset_iSup_eq_top U' hx'`. Set `l'` to `((he' (genericPoint B.X)).stalkBasis _ (hx' (genericPoint B.X))).coord 0`. Set `l₀ : genStalk E →ₗ[B.X.functionField] B.X.functionField` to `l'.comp (stalkLinear u (genericPoint B.X))`. Establish `hl' : l' ≠ 0` using `fun h0 => by`.

Use `LinearMap.congr_fun h0 ((he' _).stalkBasis _ (hx' (genericPoint B.X)) 0)` as an intermediate fact. Rewrite `this` using `[Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]`. Conclude with `one_ne_zero this`. Establish `hgerm (c : O) (hc : c ≠ 0) : B.X.presheaf.germ ⊤ (genericPoint B.X) trivial (B.const c) ≠ 0` using `fun h0 => (B.isRegularFn_const hc).ne_zero (germ_injective_of_isIntegral B.X (genericPoint B.X) (show genericPoint B.X ∈ (⊤ : B.X.Opens) from trivial) (h0.trans (map_zero _).symm))`. Establish `hl₀ : l₀ ≠ 0` using `fun h0 => by`.

Use `LinearMap.congr_fun h0 (stalkLinear u₂ _ ((he' _).stalkBasis _ (hx' (genericPoint B.X)) 0))` as an intermediate fact. Establish `e₁ : l₀ (stalkLinear u₂ _ ((he' _).stalkBasis _ (hx' (genericPoint B.X)) 0)) = B.X.presheaf.germ ⊤ (genericPoint B.X) trivial (B.const g) * B.X.presheaf.germ ⊤ (genericPoint B.X) trivial (B.const g₂)`. Express the relevant statement in the definitionally equal form `l' ((stalkLinear u _ ∘ₗ stalkLinear u₂ _) _) = _`. Rewrite using `[← stalkLinear_comp, huu, stalkLinear_comp, LinearMap.comp_apply, stalk_smul, stalk_smul, map_smul, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, smul_eq_mul, mul_one]`. Rewrite `this` using `[e₁, LinearMap.zero_apply]`.

Conclude with `mul_ne_zero (hgerm g hg) (hgerm g₂ hg₂) this`. Set `w : (T ⊕ T') → Fin (r + 1) → B.X.functionField` to `fun a => Sum.elim (fun (α : T) (j : Fin (r + 1)) => l₀ (E.presheaf.germ _ _ (gen_mem (hx α)) (e α j))) (fun (β : T') (j : Fin (r + 1)) => l' (E'.presheaf.germ _ _ (gen_mem (hx' β)) (e' β j))) a`. Establish `hw : ∀ a, ∃ j, w a j ≠ 0`. Introduce and unpack `(α | β)`. Use `by_contra! H`.

Conclude with `hl₀ (((he α).stalkBasis _ (gen_mem (hx α))).ext fun j => by`. Rewrite using `[IsFrame.stalkBasis_apply]`. Conclude with `H j)`. Use `by_contra! H`. Conclude with `hl' (((he' β).stalkBasis _ (gen_mem (hx' β))).ext fun j => by`.

Rewrite using `[IsFrame.stalkBasis_apply]`. Conclude with `H j)`. Take `⟨B', f, hη, hB', hrel, hdiv⟩` from `GlobalTheory.T.normal_model_nonvanishing_weights O B hB (T ⊕ T') (Fin (r + 1)) w hw`. Establish `hF` using `hE.pullback f.f`. Establish `hF'` using `hE'.pullback f.f`.

Use `hF.isQuasicoherent` as an intermediate fact. Use `hF'.isQuasicoherent` as an intermediate fact. Establish `hU₁ : genericPoint B'.X ∈ f.f ⁻¹ᵁ U (genericPoint B.X)` using `show f.f _ ∈ U _ from hη ▸ hx _`. Establish `hU₂ : genericPoint B'.X ∈ f.f ⁻¹ᵁ U' (genericPoint B.X)` using `show f.f _ ∈ U' _ from hη ▸ hx' _`. Set `uf` to `(Scheme.Modules.pullback f.f).map u`.

Set `u₂f` to `(Scheme.Modules.pullback f.f).map u₂`. Set `m'` to `(((he' _).pullback f.f).stalkBasis _ hU₂).coord 0`. Set `m : genStalk ((Scheme.Modules.pullback f.f).obj E) →ₗ[B'.X.functionField] B'.X.functionField` to `m'.comp (stalkLinear uf (genericPoint B'.X))`. Establish `cE (α : T) (j : Fin (r + 1)) (hα : genericPoint B'.X ∈ f.f ⁻¹ᵁ U α) : m (((Scheme.Modules.pullback f.f).obj E).presheaf.germ _ _ hα (pullbackSections f.f E (le_refl (f.f ⁻¹ᵁ U α)) (e α j))) = fnMap f.f (specializes_of_eq hη) (w (.inl α) j)`. Express the relevant statement in the definitionally equal form `m' (stalkLinear uf _ _) = _`.

Rewrite using `[stalkLinear_germ, pullback_map_app_pullbackSections, GlobalTheory.CorankOne.coord_pullback f.f hη (hx' _) hU₂ (he' _) 0 (gen_mem (hx α)) hα]`. Express the relevant statement in the definitionally equal form `_ = fnMap f.f _ (l' (stalkLinear u _ _))`. Rewrite using `[stalkLinear_germ]`. Establish `cE' (β : T') (j : Fin (r + 1)) (hβ : genericPoint B'.X ∈ f.f ⁻¹ᵁ U' β) : m' (((Scheme.Modules.pullback f.f).obj E').presheaf.germ _ _ hβ (pullbackSections f.f E' (le_refl (f.f ⁻¹ᵁ U' β)) (e' β j))) = fnMap f.f (specializes_of_eq hη) (w (.inr β) j)` using `GlobalTheory.CorankOne.coord_pullback f.f hη (hx' _) hU₂ (he' _) 0 (gen_mem (hx' β)) hβ _`. Establish `hQ` using `GlobalTheory.CorankOne.isVB_cokernel_ofGeneric (F := (Scheme.Modules.pullback f.f).obj E) m fun y => by`.

Take `⟨α, hα⟩` from `Opens.mem_iSup.1 (hT.ge (Set.mem_univ (f.f y)))`. Take `⟨i, hi, hj⟩` from `hdiv y (.inl α)`. Establish `hy : y ∈ f.f ⁻¹ᵁ U α` using `hα`. Establish `c (j)` using `cE α j (gen_mem hy)`. Use `⟨_, hy, _, i, (he α).pullback f.f, fun h0 => hi ?_, fun j => ?_⟩` and prove the remaining obligations.

Conclude with `(map_eq_zero _).1 ((c i).symm.trans h0)`. Take `⟨g', hg', e''⟩` from `hj j`. Conclude with `⟨g', hg', ((congrArg (g' * ·) (c i)).trans e'').trans (c j).symm⟩`. Establish `hQ'` using `GlobalTheory.CorankOne.isVB_cokernel_ofGeneric (F := (Scheme.Modules.pullback f.f).obj E') m' fun y => by`. Take `⟨β, hβ⟩` from `Opens.mem_iSup.1 (hT'.ge (Set.mem_univ (f.f y)))`.

Take `⟨i, hi, hj⟩` from `hdiv y (.inr β)`. Establish `hy : y ∈ f.f ⁻¹ᵁ U' β` using `hβ`. Establish `c (j)` using `cE' β j (gen_mem hy)`. Use `⟨_, hy, _, i, (he' β).pullback f.f, fun h0 => hi ?_, fun j => ?_⟩` and prove the remaining obligations. Conclude with `(map_eq_zero _).1 ((c i).symm.trans h0)`.

Take `⟨g', hg', e''⟩` from `hj j`. Conclude with `⟨g', hg', ((congrArg (g' * ·) (c i)).trans e'').trans (c j).symm⟩`. Set `N` to `Sub.ofGeneric (LinearMap.ker m)`. Set `N'` to `Sub.ofGeneric (LinearMap.ker m')`. Establish `hS : (ShortComplex.mk _ (cokernel.π N.incl) (cokernel.condition _)).ShortExact` using `{ exact := ShortComplex.exact_cokernel _ }`.

Establish `hS' : (ShortComplex.mk _ (cokernel.π N'.incl) (cokernel.condition _)).ShortExact` using `{ exact := ShortComplex.exact_cokernel _ }`. Establish `hK` using `isVB_X₁_of_shortExact B'.X _ r 1 hS hF hQ`. Establish `hK'` using `isVB_X₁_of_shortExact B'.X _ r 1 hS' hF' hQ'`. Take `⟨v, hv⟩` from `GlobalTheory.T.generic_subspace_map_extends B'.X _ _ uf (LinearMap.ker m) (LinearMap.ker m') fun t ht => LinearMap.mem_ker.2 (LinearMap.mem_ker.1 ht)`. Establish `hc (c : O) : f.f.appTop (B.const c) = B'.const c` using `GlobalTheory.Vert.Model.appTop_const f.comp_str c`.

Establish `hu₂u : u₂f ≫ uf = smulHom _ (B'.const g₂) ≫ smulHom _ (B'.const g)`. Rewrite using `[← Functor.map_comp, huu, Functor.map_comp, VB.pullback_map_smulHom, VB.pullback_map_smulHom, hc, hc]`. Establish `huu₂f : uf ≫ u₂f = smulHom _ (B'.const g) ≫ smulHom _ (B'.const g₂)`. Rewrite using `[← Functor.map_comp, huu₂, Functor.map_comp, VB.pullback_map_smulHom, VB.pullback_map_smulHom, hc, hc]`. Take `⟨v₂, hv₂⟩` from `GlobalTheory.T.generic_subspace_map_extends B'.X _ _ u₂f (LinearMap.ker m') (LinearMap.ker m) fun t ht => by`.

Use `LinearMap.mem_ker.2 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `m' ((stalkLinear uf _ ∘ₗ stalkLinear u₂f _) t) = 0`. Rewrite using `[← stalkLinear_comp, hu₂u, stalkLinear_comp, LinearMap.comp_apply, stalk_smul, stalk_smul, map_smul, map_smul, LinearMap.mem_ker.1 ht, smul_zero, smul_zero]`. Establish `hvv₂ : v ≫ v₂ = smulHom _ (B'.const g) ≫ smulHom _ (B'.const g₂)`. Conclude with `comp_eq_smul N.incl N'.incl v v₂ uf u₂f _ _ hv hv₂ huu₂f`.

Establish `hv₂v : v₂ ≫ v = smulHom _ (B'.const g₂) ≫ smulHom _ (B'.const g)`. Conclude with `comp_eq_smul N'.incl N.incl v₂ v u₂f uf _ _ hv₂ hv hu₂u`. Establish `: IsIso (B'.genRes.map v)`. Use `GlobalTheory.Vert.Model.isIso_genRes_map_smulHom N.toMod hg` as an intermediate fact. Use `GlobalTheory.Vert.Model.isIso_genRes_map_smulHom N.toMod hg₂` as an intermediate fact.

Use `GlobalTheory.Vert.Model.isIso_genRes_map_smulHom N'.toMod hg` as an intermediate fact. Use `GlobalTheory.Vert.Model.isIso_genRes_map_smulHom N'.toMod hg₂` as an intermediate fact. Establish `h₁ : IsIso (B'.genRes.map v ≫ B'.genRes.map v₂)`. Rewrite using `[← Functor.map_comp, hvv₂, Functor.map_comp]`. Use `infer_instance`.

Establish `h₂ : IsIso (B'.genRes.map v₂ ≫ B'.genRes.map v)`. Rewrite using `[← Functor.map_comp, hv₂v, Functor.map_comp]`. Use `infer_instance`. Establish `: Mono (B'.genRes.map v)` using `mono_of_mono _ (B'.genRes.map v₂)`. Establish `: Epi (B'.genRes.map v)` using `epi_of_epi (B'.genRes.map v₂) _`.

Conclude with `isIso_of_mono_of_epi _`. Use `⟨B', f, N.toMod, N'.toMod, N.incl, N'.incl, asIso (B'.genRes.map v) ≪≫ GlobalTheory.Vert.Model.GenIso.smul N'.toMod g hg, hB', hrel, ⟨inferInstance, 1, hQ⟩, ⟨inferInstance, 1, hQ'⟩, hK, hK', ?_⟩` and prove the remaining obligations. Conclude with `final_eq N.incl N'.incl v uf _ g hg hv (genRes_pullback_map f φ u g hu)`.
-/
theorem exists_corankOne_pair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (r : ℕ) (E E' : B.X.Modules) (φ : B.GenIso E E'), GlobalTheory.VB.IsVB E (r + 1) → GlobalTheory.VB.IsVB E' (r + 1) → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (K K' : B'.X.Modules) (i : K ⟶ (Scheme.Modules.pullback f.f).obj E) (i' : K' ⟶ (Scheme.Modules.pullback f.f).obj E') (ψ : B'.GenIso K K'), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ GlobalTheory.VB.IsSubbundle i ∧ GlobalTheory.VB.IsSubbundle i' ∧ GlobalTheory.VB.IsVB K r ∧ GlobalTheory.VB.IsVB K' r ∧ ψ.hom ≫ B'.genRes.map i' = B'.genRes.map i ≫ (φ.pull f.comp_str).hom := by
  intro O _ _ _ p _ _ _ B hB r E E' φ hE hE'
  have := hE.isQuasicoherent
  have := hE'.isQuasicoherent
  obtain ⟨g, u, hg, hu⟩ := GlobalTheory.T.generic_map_extends_after_scaling O B E E' _ _ hE hE' φ.hom
  obtain ⟨g₂, u₂, hg₂, hu₂⟩ := GlobalTheory.T.generic_map_extends_after_scaling O B E' E _ _ hE' hE φ.inv
  have huu : u₂ ≫ u = smulHom E' (B.const g₂) ≫ smulHom E' (B.const g) := by
    refine GlobalTheory.T.vector_bundle_map_determined_generic O B _ _ _ _ _ hE' ?_
    rw [Functor.map_comp, Functor.map_comp, hu₂, hu, Category.assoc, ← Category.assoc (B.genRes.map _),
      VB.pullback_map_smulHom, smulHom_comp, Category.assoc, Iso.inv_hom_id_assoc]
    simp only [VB.pullback_map_smulHom]
  have huu₂ : u ≫ u₂ = smulHom E (B.const g) ≫ smulHom E (B.const g₂) := by
    refine GlobalTheory.T.vector_bundle_map_determined_generic O B _ _ _ _ _ hE ?_
    rw [Functor.map_comp, Functor.map_comp, hu₂, hu, Category.assoc, ← Category.assoc (B.genRes.map _),
      VB.pullback_map_smulHom, smulHom_comp, Category.assoc, Iso.hom_inv_id_assoc]
    simp only [VB.pullback_map_smulHom]
  choose U e hx he using id hE
  choose U' e' hx' he' using id hE'
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top U hx
  obtain ⟨T', hT'⟩ := exists_finset_iSup_eq_top U' hx'
  let l' := ((he' (genericPoint B.X)).stalkBasis _ (hx' (genericPoint B.X))).coord 0
  let l₀ : genStalk E →ₗ[B.X.functionField] B.X.functionField := l'.comp (stalkLinear u (genericPoint B.X))
  have hl' : l' ≠ 0 := fun h0 => by
    have := LinearMap.congr_fun h0 ((he' _).stalkBasis _ (hx' (genericPoint B.X)) 0)
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at this
    exact one_ne_zero this
  have hgerm (c : O) (hc : c ≠ 0) : B.X.presheaf.germ ⊤ (genericPoint B.X) trivial (B.const c) ≠ 0 := fun h0 =>
    (B.isRegularFn_const hc).ne_zero (germ_injective_of_isIntegral B.X (genericPoint B.X) (show genericPoint B.X ∈ (⊤ : B.X.Opens) from trivial) (h0.trans (map_zero _).symm))
  have hl₀ : l₀ ≠ 0 := fun h0 => by
    have := LinearMap.congr_fun h0 (stalkLinear u₂ _ ((he' _).stalkBasis _ (hx' (genericPoint B.X)) 0))
    have e₁ : l₀ (stalkLinear u₂ _ ((he' _).stalkBasis _ (hx' (genericPoint B.X)) 0)) =
        B.X.presheaf.germ ⊤ (genericPoint B.X) trivial (B.const g) *
          B.X.presheaf.germ ⊤ (genericPoint B.X) trivial (B.const g₂) := by
      change l' ((stalkLinear u _ ∘ₗ stalkLinear u₂ _) _) = _
      rw [← stalkLinear_comp, huu, stalkLinear_comp, LinearMap.comp_apply, stalk_smul, stalk_smul,
        map_smul, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, smul_eq_mul, mul_one]
    rw [e₁, LinearMap.zero_apply] at this
    exact mul_ne_zero (hgerm g hg) (hgerm g₂ hg₂) this
  let w : (T ⊕ T') → Fin (r + 1) → B.X.functionField := fun a => Sum.elim
    (fun (α : T) (j : Fin (r + 1)) => l₀ (E.presheaf.germ _ _ (gen_mem (hx α)) (e α j)))
    (fun (β : T') (j : Fin (r + 1)) => l' (E'.presheaf.germ _ _ (gen_mem (hx' β)) (e' β j))) a
  have hw : ∀ a, ∃ j, w a j ≠ 0 := by
    rintro (α | β)
    · by_contra! H
      exact hl₀ (((he α).stalkBasis _ (gen_mem (hx α))).ext fun j => by
        rw [IsFrame.stalkBasis_apply]; exact H j)
    · by_contra! H
      exact hl' (((he' β).stalkBasis _ (gen_mem (hx' β))).ext fun j => by
        rw [IsFrame.stalkBasis_apply]; exact H j)
  obtain ⟨B', f, hη, hB', hrel, hdiv⟩ := GlobalTheory.T.normal_model_nonvanishing_weights O B hB (T ⊕ T') (Fin (r + 1)) w hw
  have hF := hE.pullback f.f
  have hF' := hE'.pullback f.f
  have := hF.isQuasicoherent
  have := hF'.isQuasicoherent
  have hU₁ : genericPoint B'.X ∈ f.f ⁻¹ᵁ U (genericPoint B.X) := show f.f _ ∈ U _ from hη ▸ hx _
  have hU₂ : genericPoint B'.X ∈ f.f ⁻¹ᵁ U' (genericPoint B.X) := show f.f _ ∈ U' _ from hη ▸ hx' _
  let uf := (Scheme.Modules.pullback f.f).map u
  let u₂f := (Scheme.Modules.pullback f.f).map u₂
  let m' := (((he' _).pullback f.f).stalkBasis _ hU₂).coord 0
  let m : genStalk ((Scheme.Modules.pullback f.f).obj E) →ₗ[B'.X.functionField] B'.X.functionField :=
    m'.comp (stalkLinear uf (genericPoint B'.X))
  have cE (α : T) (j : Fin (r + 1)) (hα : genericPoint B'.X ∈ f.f ⁻¹ᵁ U α) :
      m (((Scheme.Modules.pullback f.f).obj E).presheaf.germ _ _ hα
        (pullbackSections f.f E (le_refl (f.f ⁻¹ᵁ U α)) (e α j))) =
        fnMap f.f (specializes_of_eq hη) (w (.inl α) j) := by
    change m' (stalkLinear uf _ _) = _
    rw [stalkLinear_germ, pullback_map_app_pullbackSections,
      GlobalTheory.CorankOne.coord_pullback f.f hη (hx' _) hU₂ (he' _) 0 (gen_mem (hx α)) hα]
    change _ = fnMap f.f _ (l' (stalkLinear u _ _))
    rw [stalkLinear_germ]
  have cE' (β : T') (j : Fin (r + 1)) (hβ : genericPoint B'.X ∈ f.f ⁻¹ᵁ U' β) :
      m' (((Scheme.Modules.pullback f.f).obj E').presheaf.germ _ _ hβ
        (pullbackSections f.f E' (le_refl (f.f ⁻¹ᵁ U' β)) (e' β j))) =
        fnMap f.f (specializes_of_eq hη) (w (.inr β) j) :=
    GlobalTheory.CorankOne.coord_pullback f.f hη (hx' _) hU₂ (he' _) 0 (gen_mem (hx' β)) hβ _
  have hQ := GlobalTheory.CorankOne.isVB_cokernel_ofGeneric (F := (Scheme.Modules.pullback f.f).obj E) m fun y => by
    obtain ⟨α, hα⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ (f.f y)))
    obtain ⟨i, hi, hj⟩ := hdiv y (.inl α)
    have hy : y ∈ f.f ⁻¹ᵁ U α := hα
    have c (j) := cE α j (gen_mem hy)
    refine ⟨_, hy, _, i, (he α).pullback f.f, fun h0 => hi ?_, fun j => ?_⟩
    · exact (map_eq_zero _).1 ((c i).symm.trans h0)
    · obtain ⟨g', hg', e''⟩ := hj j
      exact ⟨g', hg', ((congrArg (g' * ·) (c i)).trans e'').trans (c j).symm⟩
  have hQ' := GlobalTheory.CorankOne.isVB_cokernel_ofGeneric (F := (Scheme.Modules.pullback f.f).obj E') m' fun y => by
    obtain ⟨β, hβ⟩ := Opens.mem_iSup.1 (hT'.ge (Set.mem_univ (f.f y)))
    obtain ⟨i, hi, hj⟩ := hdiv y (.inr β)
    have hy : y ∈ f.f ⁻¹ᵁ U' β := hβ
    have c (j) := cE' β j (gen_mem hy)
    refine ⟨_, hy, _, i, (he' β).pullback f.f, fun h0 => hi ?_, fun j => ?_⟩
    · exact (map_eq_zero _).1 ((c i).symm.trans h0)
    · obtain ⟨g', hg', e''⟩ := hj j
      exact ⟨g', hg', ((congrArg (g' * ·) (c i)).trans e'').trans (c j).symm⟩
  let N := Sub.ofGeneric (LinearMap.ker m)
  let N' := Sub.ofGeneric (LinearMap.ker m')
  have hS : (ShortComplex.mk _ (cokernel.π N.incl) (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hS' : (ShortComplex.mk _ (cokernel.π N'.incl) (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hK := isVB_X₁_of_shortExact B'.X _ r 1 hS hF hQ
  have hK' := isVB_X₁_of_shortExact B'.X _ r 1 hS' hF' hQ'
  obtain ⟨v, hv⟩ := GlobalTheory.T.generic_subspace_map_extends B'.X _ _ uf (LinearMap.ker m) (LinearMap.ker m') fun t ht =>
    LinearMap.mem_ker.2 (LinearMap.mem_ker.1 ht)
  have hc (c : O) : f.f.appTop (B.const c) = B'.const c := GlobalTheory.Vert.Model.appTop_const f.comp_str c
  have hu₂u : u₂f ≫ uf = smulHom _ (B'.const g₂) ≫ smulHom _ (B'.const g) := by
    rw [← Functor.map_comp, huu, Functor.map_comp, VB.pullback_map_smulHom, VB.pullback_map_smulHom, hc, hc]
  have huu₂f : uf ≫ u₂f = smulHom _ (B'.const g) ≫ smulHom _ (B'.const g₂) := by
    rw [← Functor.map_comp, huu₂, Functor.map_comp, VB.pullback_map_smulHom, VB.pullback_map_smulHom, hc, hc]
  obtain ⟨v₂, hv₂⟩ := GlobalTheory.T.generic_subspace_map_extends B'.X _ _ u₂f (LinearMap.ker m') (LinearMap.ker m) fun t ht => by
    refine LinearMap.mem_ker.2 ?_
    change m' ((stalkLinear uf _ ∘ₗ stalkLinear u₂f _) t) = 0
    rw [← stalkLinear_comp, hu₂u, stalkLinear_comp, LinearMap.comp_apply, stalk_smul, stalk_smul,
      map_smul, map_smul, LinearMap.mem_ker.1 ht, smul_zero, smul_zero]
  have hvv₂ : v ≫ v₂ = smulHom _ (B'.const g) ≫ smulHom _ (B'.const g₂) := by
    exact comp_eq_smul N.incl N'.incl v v₂ uf u₂f _ _ hv hv₂ huu₂f
  have hv₂v : v₂ ≫ v = smulHom _ (B'.const g₂) ≫ smulHom _ (B'.const g) := by
    exact comp_eq_smul N'.incl N.incl v₂ v u₂f uf _ _ hv₂ hv hu₂u
  have : IsIso (B'.genRes.map v) := by
    have := GlobalTheory.Vert.Model.isIso_genRes_map_smulHom N.toMod hg
    have := GlobalTheory.Vert.Model.isIso_genRes_map_smulHom N.toMod hg₂
    have := GlobalTheory.Vert.Model.isIso_genRes_map_smulHom N'.toMod hg
    have := GlobalTheory.Vert.Model.isIso_genRes_map_smulHom N'.toMod hg₂
    have h₁ : IsIso (B'.genRes.map v ≫ B'.genRes.map v₂) := by
      rw [← Functor.map_comp, hvv₂, Functor.map_comp]; infer_instance
    have h₂ : IsIso (B'.genRes.map v₂ ≫ B'.genRes.map v) := by
      rw [← Functor.map_comp, hv₂v, Functor.map_comp]; infer_instance
    have : Mono (B'.genRes.map v) := mono_of_mono _ (B'.genRes.map v₂)
    have : Epi (B'.genRes.map v) := epi_of_epi (B'.genRes.map v₂) _
    exact isIso_of_mono_of_epi _
  refine ⟨B', f, N.toMod, N'.toMod, N.incl, N'.incl,
    asIso (B'.genRes.map v) ≪≫ GlobalTheory.Vert.Model.GenIso.smul N'.toMod g hg, hB', hrel,
    ⟨inferInstance, 1, hQ⟩, ⟨inferInstance, 1, hQ'⟩, hK, hK', ?_⟩
  exact final_eq N.incl N'.incl v uf _ g hg hv (genRes_pullback_map f φ u g hu)

end GlobalTheory.CorankPair
