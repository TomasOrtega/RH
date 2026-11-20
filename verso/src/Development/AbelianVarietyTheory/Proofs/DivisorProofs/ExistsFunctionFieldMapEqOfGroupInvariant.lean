import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

/- English proof (translation)
Establish `hx : genericPoint X ∈ U` using `((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)`. Establish `hfx : f (genericPoint X) ∈ V` using `e hx`. Rewrite using `[← Scheme.algebraMap_germ_eq_germToFunctionField (X := X') hfx, functionFieldMap_algebraMap, ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx]`. Use `congr 1`. Conclude with `(Scheme.Hom.germ_stalkMap_apply f V _ hfx s).trans (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE e) _ hx (f.app V s)).symm`.
-/
theorem functionFieldMap_germToFunctionField {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    (f : X ⟶ X') [IsDominant f] (V : X'.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) [Nonempty U]
    [Nonempty V] (s : Γ(X', V)) :
    functionFieldMap f (X'.germToFunctionField V s) = X.germToFunctionField U (f.appLE V U e s) := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hfx : f (genericPoint X) ∈ V := e hx
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X') hfx, functionFieldMap_algebraMap,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx]
  congr 1
  exact (Scheme.Hom.germ_stalkMap_apply f V _ hfx s).trans
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE e) _ hx (f.app V s)).symm

/- English proof (translation)
Use `Fintype.ofFinite Γ` as an intermediate fact. Use `h.isAffineHom` as an intermediate fact. Take `⟨_, ⟨V, hV, rfl⟩, hyV, -⟩` from `W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint W)) isOpen_univ`. Use `haveI : Nonempty V := ⟨⟨_, hyV⟩⟩`. Establish `hU : IsAffineOpen (q ⁻¹ᵁ V)` using `(show IsAffineOpen V from hV).preimage q`.

Take `⟨x, hx⟩` from `q.denseRange.exists_mem_open V.isOpen ⟨_, hyV⟩`. Use `haveI : Nonempty (q ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩`. Establish `hst` using `h.preimage_le V`. Use `haveI (γ : Γ) : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)`. Use `haveI := functionField_isFractionRing_of_isAffineOpen X _ hU`.

Set `σ : Γ → Γ(X, q ⁻¹ᵁ V) →+* Γ(X, q ⁻¹ᵁ V)` to `fun γ ↦ ((ρ γ).hom.appLE _ _ (hst γ)).hom`. Establish `hσ (γ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) : functionFieldMap (ρ γ).hom (algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField s) = algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField (σ γ s)` using `functionFieldMap_germToFunctionField _ _ _ (hst γ) s`. Establish `hσ1 (s : Γ(X, q ⁻¹ᵁ V)) : σ 1 s = s`. Establish `e1 : (ρ 1).hom = 𝟙 X` using `by rw [map_one]; rfl`. Express the relevant statement in the definitionally equal form `(ρ 1).hom.appLE _ _ (hst 1) s = s`.

Simplify using `only [e1]`. Conclude with `congr($(X.presheaf.map_id (Opposite.op (q ⁻¹ᵁ V))) s)`. Establish `hσmul (γ δ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) : σ δ (σ γ s) = σ (γ * δ) s`. Establish `e2 : (ρ (γ * δ)).hom = (ρ δ).hom ≫ (ρ γ).hom` using `by rw [map_mul]; rfl`. Express the relevant statement in the definitionally equal form `(ρ δ).hom.appLE _ _ (hst δ) ((ρ γ).hom.appLE _ _ (hst γ) s) = (ρ (γ * δ)).hom.appLE _ _ (hst (γ * δ)) s`.

Simplify using `only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, e2]`. Use `set e := algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField with he_def`. Establish `einj : Function.Injective e` using `IsFractionRing.injective _ _`. Establish `hfu (δ : Γ) : functionFieldMap (ρ δ).hom (u : X.functionField) = u` using `congrArg Units.val (hu δ)`. Take `⟨a, t, ht, hat⟩` from `IsFractionRing.div_surjective (A := Γ(X, q ⁻¹ᵁ V)) (u : X.functionField)`.

Establish `ht0 : e t ≠ 0`. Rewrite using `[Ne, ← map_zero e]`. Conclude with `fun h0 ↦ nonZeroDivisors.ne_zero ht (einj h0)`. Set `N` to `∏ γ, σ γ t`. Establish `hN (δ : Γ) : σ δ N = N`.

Simplify using `only [N, map_prod, hσmul]`. Conclude with `Fintype.prod_equiv (Equiv.mulRight δ) _ _ (fun _ ↦ rfl)`. Establish `hNe : e N ≠ 0`. Simplify using `only [N, map_prod]`. Use `Finset.prod_ne_zero_iff.mpr fun γ _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[← hσ]`. Conclude with `(map_ne_zero _).mpr ht0`. Set `c` to `a * ∏ γ ∈ Finset.univ.erase 1, σ γ t`. Establish `hc : e c = u * e N`. Establish `hsplit : N = t * ∏ γ ∈ Finset.univ.erase 1, σ γ t`.

Simplify using `only [N]`. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun γ ↦ σ γ t) (Finset.mem_univ 1), hσ1]`. Rewrite `hat` using `[← he_def]`. Rewrite using `[hsplit]`. Simplify using `only [c, map_mul]`.

Rewrite using `[← hat]`. Clear the denominators using the available nonvanishing facts. Establish `hcinv (δ : Γ) : σ δ c = c`. Apply `einj` to reduce the goal to its premises. Rewrite using `[← hσ, hc, map_mul, hfu, hσ, hN]`.

Take `⟨bc, hbc⟩` from `h.mem_range_app V c fun δ ↦ ⟨hst δ, hcinv δ⟩`. Take `⟨bN, hbN⟩` from `h.mem_range_app V N fun δ ↦ ⟨hst δ, hN δ⟩`. Establish `hq (b : Γ(W, V)) : functionFieldMap q (W.germToFunctionField V b) = e (q.app V b)`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `functionFieldMap_germToFunctionField q V (q ⁻¹ᵁ V) le_rfl b`.

Establish `hbN0 : W.germToFunctionField V bN ≠ 0`. Introduce `h0`. Apply `hNe` to reduce the goal to its premises. Rewrite using `[← hbN, ← hq, h0, map_zero]`. Establish `hbc0 : W.germToFunctionField V bc ≠ 0`.

Introduce `h0`. Apply `mul_ne_zero u.ne_zero hNe` to reduce the goal to its premises. Rewrite using `[← hc, ← hbc, ← hq, h0, map_zero]`. Use `⟨Units.mk0 (W.germToFunctionField V bc / W.germToFunctionField V bN) (div_ne_zero hbc0 hbN0), Units.ext ?_⟩` and prove the remaining obligations. Simplify using `only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_div₀, hq, hbc, hbN, hc]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem exists_functionFieldMap_eq_of_invariant (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W]
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q]
    (h : IsAffineQuotient ρ q) (u : X.functionFieldˣ) (hu : ∀ γ, fnAct ρ γ u = u) :
    ∃ b : W.functionFieldˣ, Units.map (functionFieldMap q).toMonoidHom b = u := by
  classical
  have := Fintype.ofFinite Γ
  have := h.isAffineHom
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  haveI : Nonempty V := ⟨⟨_, hyV⟩⟩
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := (show IsAffineOpen V from hV).preimage q
  obtain ⟨x, hx⟩ := q.denseRange.exists_mem_open V.isOpen ⟨_, hyV⟩
  haveI : Nonempty (q ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩
  have hst := h.preimage_le V
  haveI (γ : Γ) : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  haveI := functionField_isFractionRing_of_isAffineOpen X _ hU
  let σ : Γ → Γ(X, q ⁻¹ᵁ V) →+* Γ(X, q ⁻¹ᵁ V) := fun γ ↦ ((ρ γ).hom.appLE _ _ (hst γ)).hom
  have hσ (γ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) :
      functionFieldMap (ρ γ).hom (algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField s) =
        algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField (σ γ s) :=
    functionFieldMap_germToFunctionField _ _ _ (hst γ) s
  have hσ1 (s : Γ(X, q ⁻¹ᵁ V)) : σ 1 s = s := by
    have e1 : (ρ 1).hom = 𝟙 X := by rw [map_one]; rfl
    change (ρ 1).hom.appLE _ _ (hst 1) s = s
    simp only [e1]
    exact congr($(X.presheaf.map_id (Opposite.op (q ⁻¹ᵁ V))) s)
  have hσmul (γ δ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) : σ δ (σ γ s) = σ (γ * δ) s := by
    have e2 : (ρ (γ * δ)).hom = (ρ δ).hom ≫ (ρ γ).hom := by rw [map_mul]; rfl
    change (ρ δ).hom.appLE _ _ (hst δ) ((ρ γ).hom.appLE _ _ (hst γ) s) =
      (ρ (γ * δ)).hom.appLE _ _ (hst (γ * δ)) s
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, e2]
  set e := algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField with he_def
  have einj : Function.Injective e := IsFractionRing.injective _ _
  have hfu (δ : Γ) : functionFieldMap (ρ δ).hom (u : X.functionField) = u :=
    congrArg Units.val (hu δ)
  obtain ⟨a, t, ht, hat⟩ := IsFractionRing.div_surjective (A := Γ(X, q ⁻¹ᵁ V)) (u : X.functionField)
  have ht0 : e t ≠ 0 := by
    rw [Ne, ← map_zero e]
    exact fun h0 ↦ nonZeroDivisors.ne_zero ht (einj h0)
  let N := ∏ γ, σ γ t
  have hN (δ : Γ) : σ δ N = N := by
    simp only [N, map_prod, hσmul]
    exact Fintype.prod_equiv (Equiv.mulRight δ) _ _ (fun _ ↦ rfl)
  have hNe : e N ≠ 0 := by
    simp only [N, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun γ _ ↦ ?_
    rw [← hσ]
    exact (map_ne_zero _).mpr ht0
  let c := a * ∏ γ ∈ Finset.univ.erase 1, σ γ t
  have hc : e c = u * e N := by
    have hsplit : N = t * ∏ γ ∈ Finset.univ.erase 1, σ γ t := by
      simp only [N]
      rw [← Finset.mul_prod_erase Finset.univ (fun γ ↦ σ γ t) (Finset.mem_univ 1), hσ1]
    rw [← he_def] at hat
    rw [hsplit]
    simp only [c, map_mul]
    rw [← hat]
    field_simp
  have hcinv (δ : Γ) : σ δ c = c := by
    apply einj
    rw [← hσ, hc, map_mul, hfu, hσ, hN]
  obtain ⟨bc, hbc⟩ := h.mem_range_app V c fun δ ↦ ⟨hst δ, hcinv δ⟩
  obtain ⟨bN, hbN⟩ := h.mem_range_app V N fun δ ↦ ⟨hst δ, hN δ⟩
  have hq (b : Γ(W, V)) : functionFieldMap q (W.germToFunctionField V b) = e (q.app V b) := by
    rw [Scheme.Hom.app_eq_appLE]
    exact functionFieldMap_germToFunctionField q V (q ⁻¹ᵁ V) le_rfl b
  have hbN0 : W.germToFunctionField V bN ≠ 0 := by
    intro h0
    apply hNe
    rw [← hbN, ← hq, h0, map_zero]
  have hbc0 : W.germToFunctionField V bc ≠ 0 := by
    intro h0
    apply mul_ne_zero u.ne_zero hNe
    rw [← hc, ← hbc, ← hq, h0, map_zero]
  refine ⟨Units.mk0 (W.germToFunctionField V bc / W.germToFunctionField V bN)
    (div_ne_zero hbc0 hbN0), Units.ext ?_⟩
  simp only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    map_div₀, hq, hbc, hbN, hc]
  field_simp

end GlobalTheory.OrbitSep
