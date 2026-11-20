import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePartAtOwnWeightNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryIntegralBelowPlaceCompactOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.MemIsotypicOfInjective

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

private noncomputable def fixW {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) : Submodule ℂ (UA E n → ℂ) where
  carrier := {ψ | ∀ y ∈ locU n w, cLoc w y ∈ GlobalTheory.LFun.KGL w n → RU E n y ψ = ψ}
  add_mem' ha hb y hy hk := by rw [map_add, ha y hy hk, hb y hy hk]
  zero_mem' _ _ _ := map_zero _
  smul_mem' c _ ha y hy hk := by rw [map_smul, ha y hy hk]

/- English proof (translation)
Establish `h1 : ∀ y, j y ∈ ⨆ f : {f : S →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1`. Introduce `y`. Establish `hle : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) ≤ ⨆ f : {f : S →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1` using `iSup_le fun f => le_iSup_of_le ⟨f.toLinearMap, fun g v => Representation.IntertwiningMap.isIntertwining σ ρ f g v⟩ le_rfl`. Conclude with `hle (h ▸ Submodule.mem_top)`. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Establish `h2` using `UpperTheory.V.PiLin.iso_sub σ π ρ hσ j hj he h1 y`. Establish `hle : (⨆ f : {f : S →ₗ[ℂ] Y // ∀ g v, f (σ g v) = π g (f v)}, LinearMap.range f.1) ≤ ⨆ f : σ.IntertwiningMap π, LinearMap.range f.toLinearMap` using `iSup_le fun f => le_iSup_of_le ⟨f.1, fun g => LinearMap.ext fun v => f.2 g v⟩ le_rfl`. Conclude with `hle h2`.
-/
private theorem span_sub {H S Y V : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H S) (π : Representation ℂ H Y)
    (ρ : Representation ℂ H V) (hσ : σ.IsIrreducible) (j : Y →ₗ[ℂ] V) (hj : Function.Injective j)
    (he : ∀ g y, j (π g y) = ρ g (j y))
    (h : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤) :
    (⨆ f : σ.IntertwiningMap π, LinearMap.range f.toLinearMap) = ⊤ := by
  have h1 : ∀ y, j y ∈ ⨆ f : {f : S →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
    intro y
    have hle : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) ≤
        ⨆ f : {f : S →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 :=
      iSup_le fun f => le_iSup_of_le ⟨f.toLinearMap, fun g v => Representation.IntertwiningMap.isIntertwining σ ρ f g v⟩ le_rfl
    exact hle (h ▸ Submodule.mem_top)
  rw [eq_top_iff]
  intro y _
  have h2 := UpperTheory.V.PiLin.iso_sub σ π ρ hσ j hj he h1 y
  have hle : (⨆ f : {f : S →ₗ[ℂ] Y // ∀ g v, f (σ g v) = π g (f v)}, LinearMap.range f.1) ≤
      ⨆ f : σ.IntertwiningMap π, LinearMap.range f.toLinearMap :=
    iSup_le fun f => le_iSup_of_le ⟨f.1, fun g => LinearMap.ext fun v => f.2 g v⟩ le_rfl
  exact hle h2

/- English proof (translation)
Introduce `E _ _ _ n hn V hV φ hφ lam hW w hw`. Take `⟨φ₀, hφ₀, hne, hfix⟩` from `hw`. Set `π : GlobalTheory.DefU.AutSub E n` to `⟨V, hV⟩`. Set `N : Submodule ℂ (UA E n → ℂ)` to `V ⊓ fixW n w`. Establish `hNV : N ≤ V` using `inf_le_left`.

Establish `hmemN : ∀ ψ, ψ ∈ N ↔ ψ ∈ V ∧ ∀ y ∈ locU n w, cLoc w y ∈ GlobalTheory.LFun.KGL w n → RU E n y ψ = ψ` using `fun _ => Iff.rfl`. Establish `hst : ∀ (x : infU E n), ∀ ψ ∈ N, ((RU E n).comp (infU E n).subtype) x ψ ∈ N`. Introduce `x ψ hψ`. Take `⟨h1, h2⟩` from `(hmemN ψ).1 hψ`. Use `(hmemN _).2 ⟨hV.stable _ _ h1, fun y hy hk => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `RU E n y (RU E n x.1 ψ) = RU E n x.1 ψ`. Rewrite using `[GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.fin_mul_inf hy.1 x.2, ← GlobalTheory.DefU.RU_RU, h2 y hy hk]`. Set `ρ : Representation ℂ (infU E n) N` to `GlobalTheory.PRep.sub ((RU E n).comp (infU E n).subtype) N hst`. Set `s : ∀ v : InfinitePlace E, embU n (φ v) →* infU E n` to `fun v => Subgroup.inclusion inf_le_left`. Set `σ : ∀ v, Representation ℂ (embU n (φ v)) (nablaSq ℂ n (lam v))` to `fun v => (GlobalTheory.Branching.sqRep ℂ n (lam v)).comp ((cEmb (φ v)).comp (embU n (φ v)).subtype)`.

Establish `hirr : ∀ v, (σ v).IsIrreducible` using `fun v => by`. Take `⟨e, he⟩` from `GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n (φ v)`. Take `⟨h1, h2⟩` from `(GlobalTheory.CuspRep.isIrreducible_iff _).1 (GlobalTheory.Branching.isIrreducible_smallRep_unitary n (lam v))`. Use `(GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h1, fun S hS => h2 S fun g u hu => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `e.surjective g`.

Establish `h3` using `hS x u hu`. Express the relevant statement in the definitionally equal form `GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb (φ v) (x : UA E n)) u ∈ S at h3`. Express the relevant statement in the definitionally equal form `GlobalTheory.Branching.sqRep ℂ n (lam v) (GlobalTheory.Branching.unitaryIncl n (e x)) u ∈ S`. Rewrite using `[he]` and apply the resulting hypothesis. Establish `hcomm : ∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b)` using `fun u v huv a b => Subtype.ext (GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places E n (φ u) (φ v) (by rwa [hφ, hφ]) _ a.2 _ b.2)`.

Establish `hspan : ∀ v, (⨆ f : (σ v).IntertwiningMap (ρ.comp (s v)), LinearMap.range f.toLinearMap) = ⊤` using `fun v => span_sub (σ v) (ρ.comp (s v)) (π.rep.comp (embU n (φ v)).subtype) (hirr v) (Submodule.inclusion hNV) (Submodule.inclusion_injective hNV) (fun g y => Subtype.ext rfl) (GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary E n π (φ v) (lam v) (hW v))`. Use `haveI : Nontrivial N := ⟨⟨⟨φ₀, (hmemN _).2 ⟨hφ₀, hfix⟩⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩`. Take `⟨F, hF0, hF⟩` from `GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups (InfinitePlace E) (infU E n) N (fun v => embU n (φ v)) (fun v => nablaSq ℂ n (lam v)) ρ s σ inferInstance hirr hcomm hspan`. Set `f : MultilinearMap ℂ (fun v => nablaSq ℂ n (lam v)) (UA E n → ℂ)` to `N.subtype.compMultilinearMap F`. Establish `hfN : ∀ x, f x ∈ N` using `fun x => (F x).2`.

Establish `hfne : f ≠ 0` using `fun h => hF0 (MultilinearMap.ext fun x => Subtype.ext (congrArg (fun m => m x) h))`. Establish `hfF : ∀ v (h : embU n (φ v)) (x : ∀ u, nablaSq ℂ n (lam u)), RU E n h.1 (f x) = f (Function.update x v (σ v h (x v)))` using `fun v h x => congrArg Subtype.val (hF v h x)`. Establish `hE : ∀ v, embU n (φ v) = embU n v.embedding` using `fun v => by`. Unfold `embU`. Rewrite using `[hφ v, InfinitePlace.mk_embedding]`.

Establish `hact : ∀ g ∈ infU E n, ∀ x : (∀ v, nablaSq ℂ n (lam v)), f (fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb (φ v) g) (x v)) = RU E n g (f x)`. Introduce `g hg x`. Take `⟨y, hy, -, hprod⟩` from `GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n g hg`. Establish `hy' : ∀ v, y v ∈ embU n (φ v)` using `fun v => (hE v).symm ▸ hy v`. Establish `hone : ∀ u v, u ≠ v → cEmb (φ v) (y u) = 1`.

Introduce `u v huv`. Establish `h2 : y u ∈ ⨅ (τ' : E →+* ℂ) (_ : InfinitePlace.mk τ' ≠ InfinitePlace.mk (φ u)), (cEmb (E` using `E) (n := n) τ').ker := (hy' u).2`. Rewrite `h2` using `[Subgroup.mem_iInf]`. Establish `h3` using `h2 (φ v)`. Rewrite `h3` using `[Subgroup.mem_iInf]`.

Conclude with `h3 (by rw [hφ, hφ]; exact huv.symm)`. Establish `hlist : ∀ v, ∀ L : List (InfinitePlace E), L.Nodup → cEmb (φ v) (L.map y).prod = if v ∈ L then cEmb (φ v) (y v) else 1`. Introduce `v L`. Proceed by induction on `L with`. Consider the case `nil => intro _`.

Simplify using the standard rewrite rules. Consider the case `cons a L ih`. Introduce `hL`. Rewrite `hL` using `[List.nodup_cons]`. Rewrite using `[List.map_cons, List.prod_cons, map_mul, ih hL.2]`.

Distinguish the cases in `ha : a = v`. Substitute `ha` using the available equality. Simplify using `[hL.1]`. Rewrite using `[hone a v ha, one_mul]`. Simplify using `[List.mem_cons, Ne.symm ha]`.

Establish `hcg : ∀ v, cEmb (φ v) g = cEmb (φ v) (y v)`. Introduce `v`. Rewrite using `[← hprod, hlist v _ (Finset.nodup_toList _)]`. Simplify using the standard rewrite rules. Establish `h1` using `GlobalTheory.DefU.prod_list_apply_multilinear (H := fun v => embU n (φ v)) (Wv := fun v => nablaSq ℂ n (lam v)) (RU E n) (fun v => (embU n (φ v)).subtype) σ f hfF (fun v => (⟨y v, hy' v⟩ : embU n (φ v))) x Finset.univ.toList (Finset.nodup_toList _)`.

Establish `h2 : (Finset.univ.toList.map fun v => (embU n (φ v)).subtype ⟨y v, hy' v⟩).prod = g` using `hprod`. Rewrite `h1` using `[h2]`. Rewrite using `[h1]`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Simplify using `only [Finset.mem_toList, Finset.mem_univ, if_true]`. Rewrite using `[hcg v]`. Both sides reduce to the same expression. Set `Kint : Subgroup (finU E n)` to `(GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n).comap (GlobalTheory.BCT.GlobLev.finPart E n)`. Set `Kst : Subgroup (finU E n)` to `{ carrier := {k | ∀ x, RU E n k.1 (f x) = f x} one_mem' := fun x => by simp mul_mem' := fun {a b} ha hb x => by`.

Rewrite using `[Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb x, ha x]`. Use the proof step `inv_mem' := fun {a} ha x => by`. Combine the equalities or inequalities in the displayed calculation. Establish `hO1 : IsOpen (Kint : Set (finU E n))` using `(GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n).preimage GlobalTheory.BCT.GlobLev.continuous_finPart`. Establish `hO2 : IsOpen (Kst : Set (finU E n))`.

Set `B` to `fun v => Module.finBasis ℂ (nablaSq ℂ n (lam v))`. Establish `e : (Kst : Set (finU E n)) = ⋂ t : (∀ v, Fin (Module.finrank ℂ (nablaSq ℂ n (lam v)))), {k : finU E n | RU E n k.1 (f fun v => B v (t v)) = f fun v => B v (t v)}`. Use extensionality with `k`. Simplify using `only [Set.mem_iInter]`. Use `⟨fun h t => h _, fun h x => ?_⟩` and prove the remaining obligations.

Establish `h4 : (RU E n k.1).compMultilinearMap f = f` using `Module.Basis.ext_multilinear B fun t => h t`. Conclude with `congrArg (fun m => m x) h4`. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun t => (hV.aut _ ((hmemN _).1 (hfN _)).1).level`. Use `⟨f, Kint ⊓ Kst, hfne, fun x => ((hmemN _).1 (hfN x)).1, hact, ?_, fun k hk => (GlobalTheory.Cong.AdaptLev.finPart_mem_integral_iff k).1 hk.1, fun k hk => hk.2, fun y hy hk x => ((hmemN _).1 (hfN x)).2 y hy hk⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.coe_inf]`. Conclude with `hO1.inter hO2`.
-/
theorem UpperTheory.V.Z.Int.vecForm :
    UpperTheory.V.Z.Int.VecForm := by
  intro E _ _ _ n hn V hV φ hφ lam hW w hw
  obtain ⟨φ₀, hφ₀, hne, hfix⟩ := hw
  let π : GlobalTheory.DefU.AutSub E n := ⟨V, hV⟩
  let N : Submodule ℂ (UA E n → ℂ) := V ⊓ fixW n w
  have hNV : N ≤ V := inf_le_left
  have hmemN : ∀ ψ, ψ ∈ N ↔ ψ ∈ V ∧ ∀ y ∈ locU n w, cLoc w y ∈ GlobalTheory.LFun.KGL w n → RU E n y ψ = ψ :=
    fun _ => Iff.rfl
  have hst : ∀ (x : infU E n), ∀ ψ ∈ N, ((RU E n).comp (infU E n).subtype) x ψ ∈ N := by
    intro x ψ hψ
    obtain ⟨h1, h2⟩ := (hmemN ψ).1 hψ
    refine (hmemN _).2 ⟨hV.stable _ _ h1, fun y hy hk => ?_⟩
    change RU E n y (RU E n x.1 ψ) = RU E n x.1 ψ
    rw [GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.fin_mul_inf hy.1 x.2, ← GlobalTheory.DefU.RU_RU, h2 y hy hk]
  let ρ : Representation ℂ (infU E n) N := GlobalTheory.PRep.sub ((RU E n).comp (infU E n).subtype) N hst
  let s : ∀ v : InfinitePlace E, embU n (φ v) →* infU E n := fun v => Subgroup.inclusion inf_le_left
  let σ : ∀ v, Representation ℂ (embU n (φ v)) (nablaSq ℂ n (lam v)) := fun v =>
    (GlobalTheory.Branching.sqRep ℂ n (lam v)).comp ((cEmb (φ v)).comp (embU n (φ v)).subtype)
  have hirr : ∀ v, (σ v).IsIrreducible := fun v => by
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n (φ v)
    obtain ⟨h1, h2⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1
      (GlobalTheory.Branching.isIrreducible_smallRep_unitary n (lam v))
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h1, fun S hS => h2 S fun g u hu => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective g
    have h3 := hS x u hu
    change GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb (φ v) (x : UA E n)) u ∈ S at h3
    change GlobalTheory.Branching.sqRep ℂ n (lam v) (GlobalTheory.Branching.unitaryIncl n (e x)) u ∈ S
    rwa [he]
  have hcomm : ∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b) := fun u v huv a b =>
    Subtype.ext (GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places E n (φ u) (φ v) (by rwa [hφ, hφ]) _ a.2 _ b.2)
  have hspan : ∀ v, (⨆ f : (σ v).IntertwiningMap (ρ.comp (s v)), LinearMap.range f.toLinearMap) = ⊤ :=
    fun v => span_sub (σ v) (ρ.comp (s v)) (π.rep.comp (embU n (φ v)).subtype) (hirr v)
      (Submodule.inclusion hNV) (Submodule.inclusion_injective hNV) (fun g y => Subtype.ext rfl)
      (GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary E n π (φ v) (lam v) (hW v))
  haveI : Nontrivial N := ⟨⟨⟨φ₀, (hmemN _).2 ⟨hφ₀, hfix⟩⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  obtain ⟨F, hF0, hF⟩ := GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups (InfinitePlace E) (infU E n) N (fun v => embU n (φ v))
    (fun v => nablaSq ℂ n (lam v)) ρ s σ inferInstance hirr hcomm hspan
  let f : MultilinearMap ℂ (fun v => nablaSq ℂ n (lam v)) (UA E n → ℂ) := N.subtype.compMultilinearMap F
  have hfN : ∀ x, f x ∈ N := fun x => (F x).2
  have hfne : f ≠ 0 := fun h => hF0 (MultilinearMap.ext fun x => Subtype.ext (congrArg (fun m => m x) h))
  have hfF : ∀ v (h : embU n (φ v)) (x : ∀ u, nablaSq ℂ n (lam u)),
      RU E n h.1 (f x) = f (Function.update x v (σ v h (x v))) := fun v h x =>
    congrArg Subtype.val (hF v h x)
  have hE : ∀ v, embU n (φ v) = embU n v.embedding := fun v => by
    unfold embU
    rw [hφ v, InfinitePlace.mk_embedding]
  have hact : ∀ g ∈ infU E n, ∀ x : (∀ v, nablaSq ℂ n (lam v)),
      f (fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb (φ v) g) (x v)) = RU E n g (f x) := by
    intro g hg x
    obtain ⟨y, hy, -, hprod⟩ := GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n g hg
    have hy' : ∀ v, y v ∈ embU n (φ v) := fun v => (hE v).symm ▸ hy v
    have hone : ∀ u v, u ≠ v → cEmb (φ v) (y u) = 1 := by
      intro u v huv
      have h2 : y u ∈ ⨅ (τ' : E →+* ℂ) (_ : InfinitePlace.mk τ' ≠ InfinitePlace.mk (φ u)),
          (cEmb (E := E) (n := n) τ').ker := (hy' u).2
      rw [Subgroup.mem_iInf] at h2
      have h3 := h2 (φ v)
      rw [Subgroup.mem_iInf] at h3
      exact h3 (by rw [hφ, hφ]; exact huv.symm)
    have hlist : ∀ v, ∀ L : List (InfinitePlace E), L.Nodup →
        cEmb (φ v) (L.map y).prod = if v ∈ L then cEmb (φ v) (y v) else 1 := by
      intro v L
      induction L with
      | nil => intro _; simp
      | cons a L ih =>
        intro hL
        rw [List.nodup_cons] at hL
        rw [List.map_cons, List.prod_cons, map_mul, ih hL.2]
        by_cases ha : a = v
        · subst ha
          simp [hL.1]
        · rw [hone a v ha, one_mul]
          simp [List.mem_cons, Ne.symm ha]
    have hcg : ∀ v, cEmb (φ v) g = cEmb (φ v) (y v) := by
      intro v
      rw [← hprod, hlist v _ (Finset.nodup_toList _)]
      simp
    have h1 := GlobalTheory.DefU.prod_list_apply_multilinear (H := fun v => embU n (φ v))
      (Wv := fun v => nablaSq ℂ n (lam v)) (RU E n) (fun v => (embU n (φ v)).subtype) σ f hfF
      (fun v => (⟨y v, hy' v⟩ : embU n (φ v))) x Finset.univ.toList (Finset.nodup_toList _)
    have h2 : (Finset.univ.toList.map fun v => (embU n (φ v)).subtype ⟨y v, hy' v⟩).prod = g := hprod
    rw [h2] at h1
    rw [h1]
    congr 1
    funext v
    simp only [Finset.mem_toList, Finset.mem_univ, if_true]
    rw [hcg v]
    rfl
  let Kint : Subgroup (finU E n) :=
    (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n).comap (GlobalTheory.BCT.GlobLev.finPart E n)
  let Kst : Subgroup (finU E n) :=
    { carrier := {k | ∀ x, RU E n k.1 (f x) = f x}
      one_mem' := fun x => by simp
      mul_mem' := fun {a b} ha hb x => by
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb x, ha x]
      inv_mem' := fun {a} ha x => by
        calc RU E n (a⁻¹).1 (f x) = RU E n (a⁻¹).1 (RU E n a.1 (f x)) := by rw [ha x]
          _ = RU E n ((a⁻¹).1 * a.1) (f x) := by rw [GlobalTheory.DefU.RU_RU]
          _ = f x := by simp }
  have hO1 : IsOpen (Kint : Set (finU E n)) :=
    (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n).preimage GlobalTheory.BCT.GlobLev.continuous_finPart
  have hO2 : IsOpen (Kst : Set (finU E n)) := by
    let B := fun v => Module.finBasis ℂ (nablaSq ℂ n (lam v))
    have e : (Kst : Set (finU E n)) = ⋂ t : (∀ v, Fin (Module.finrank ℂ (nablaSq ℂ n (lam v)))),
        {k : finU E n | RU E n k.1 (f fun v => B v (t v)) = f fun v => B v (t v)} := by
      ext k
      simp only [Set.mem_iInter]
      refine ⟨fun h t => h _, fun h x => ?_⟩
      have h4 : (RU E n k.1).compMultilinearMap f = f := Module.Basis.ext_multilinear B fun t => h t
      exact congrArg (fun m => m x) h4
    rw [e]
    exact isOpen_iInter_of_finite fun t => (hV.aut _ ((hmemN _).1 (hfN _)).1).level
  refine ⟨f, Kint ⊓ Kst, hfne, fun x => ((hmemN _).1 (hfN x)).1, hact, ?_,
    fun k hk => (GlobalTheory.Cong.AdaptLev.finPart_mem_integral_iff k).1 hk.1, fun k hk => hk.2,
    fun y hy hk x => ((hmemN _).1 (hfN x)).2 y hy hk⟩
  rw [Subgroup.coe_inf]
  exact hO1.inter hO2
