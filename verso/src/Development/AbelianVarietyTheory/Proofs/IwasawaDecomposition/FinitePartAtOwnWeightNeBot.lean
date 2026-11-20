import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultilinearMapOfIsotypicCommutingSubgroupsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupRangeWeightMapsEqTopDefiniteUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlacePartsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteUnitaryArchimedeanPointsDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAtStatement

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro _`. Simplify using the standard rewrite rules. Consider the case `cons a L ih`.

Introduce `hL`. Rewrite `hL` using `[List.nodup_cons]`. Rewrite using `[List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih hL.2, hF]`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Distinguish the cases in `hv : v = a`. Rewrite using `[hv, Function.update_self]`. Simplify using `[hL.1]`. Rewrite using `[Function.update_of_ne hv]`. Simplify using `[hv]`.
-/
theorem prod_list_apply_multilinear {ι G V : Type} [DecidableEq ι] [Group G] [AddCommGroup V] [Module ℂ V]
    {H : ι → Type} [∀ v, Group (H v)] {Wv : ι → Type} [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)]
    (ρ : Representation ℂ G V) (s : ∀ v, H v →* G) (σ : ∀ v, Representation ℂ (H v) (Wv v))
    (F : MultilinearMap ℂ Wv V)
    (hF : ∀ v (h : H v) (x : ∀ u, Wv u), ρ (s v h) (F x) = F (Function.update x v (σ v h (x v))))
    (y : ∀ v, H v) (u : ∀ v, Wv v) :
    ∀ L : List ι, L.Nodup →
      ρ (L.map fun v => s v (y v)).prod (F u) = F fun v => if v ∈ L then σ v (y v) (u v) else u v := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons a L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ih hL.2, hF]
    congr 1
    funext v
    by_cases hv : v = a
    · rw [hv, Function.update_self]
      simp [hL.1]
    · rw [Function.update_of_ne hv]
      simp [hv]

/- English proof (translation)
Introduce `E _ _ _ n π`. Establish `hW' : ∀ v : InfinitePlace E, HasWeightAt π.V v.embedding ((AU.mk π).wt v)` using `fun v => by`. Take `⟨lam, hlam, -⟩` from `GlobalTheory.T.existsUnique_weight_definiteUnitary_at E n (AU.mk π) v.embedding`. Establish `h` using `hlam.wt`. Rewrite `h` using `[Wt.at_embedding]`.

Conclude with `(AU.hasWt_mk π _ _).1 h`. Generalize the expression as in `(AU.mk π).wt = W at hW' ⊢`. Establish `hW` using `hW'`. Use `clear hW'`. Set `s : ∀ v : InfinitePlace E, embU n v.embedding →* UA E n` to `fun v => (embU n v.embedding).subtype`.

Set `σ : ∀ v : InfinitePlace E, Representation ℂ (embU n v.embedding) (nablaSq ℂ n (W v))` to `fun v => (GlobalTheory.Branching.sqRep ℂ n (W v)).comp ((cEmb v.embedding).comp (embU n v.embedding).subtype)`. Establish `hirr : ∀ v, (σ v).IsIrreducible` using `fun v => by`. Take `⟨e, he⟩` from `GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding`. Take `⟨h1, h2⟩` from `(CuspRep.isIrreducible_iff _).1 (GlobalTheory.Branching.isIrreducible_smallRep_unitary n (W v))`. Use `(CuspRep.isIrreducible_iff _).2 ⟨h1, fun S hS => h2 S fun g w hw => ?_⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `e.surjective g`. Use `hS x w hw` as an intermediate fact. Express the relevant statement in the definitionally equal form `GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding (x : UA E n)) w ∈ S at this`. Express the relevant statement in the definitionally equal form `GlobalTheory.Branching.sqRep ℂ n (W v) (GlobalTheory.Branching.unitaryIncl n (e x)) w ∈ S`. Rewrite using `[he]` and apply the resulting hypothesis.

Establish `hcomm : ∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b)` using `fun u v huv a b => GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places E n u.embedding v.embedding (by rwa [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding]) _ a.2 _ b.2`. Establish `hspan : ∀ v, (⨆ f : (σ v).IntertwiningMap (π.rep.comp (s v)), LinearMap.range f.toLinearMap) = ⊤` using `fun v => GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary E n π v.embedding (W v) (hW v)`. Use `haveI : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.isAut.ne_bot`. Take `⟨F, hF0, hF⟩` from `GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups (InfinitePlace E) (UA E n) π.V (fun v => embU n v.embedding) (fun v => nablaSq ℂ n (W v)) π.rep s σ inferInstance hirr hcomm hspan`. Take `⟨f0, hf0, -⟩` from `GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n W π.V F`.

Set `f : W.Sp →ₗ[ℂ] (UA E n → ℂ)` to `π.V.subtype ∘ₗ f0`. Establish `hten : ∀ (g : InfinitePlace E → GL (Fin n) ℂ) (u : ∀ v, nablaSq ℂ n (W v)), Formalism.L2.DIV.rhoK W g (GlobalTheory.CoefIrred.tenMul (K` using `ℂ) W u) = GlobalTheory.CoefIrred.tenMul (K := ℂ) W fun v => GlobalTheory.Branching.sqRep ℂ n (W v) (g v) (u v) := fun g u => by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Formalism.L2.DIV.rhoK_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.actTen, GlobalTheory.CoefIrred.tenMul_coe]`. Both sides reduce to the same expression.

Establish `hint : ∀ (x : infU E n) (w : W.Sp), f (W.rep x w) = RU E n x (f w)`. Introduce `x w`. Take `⟨y, hy, hyc, hprod⟩` from `GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x.1 x.2`. Set `y' : ∀ v : InfinitePlace E, embU n v.embedding` to `fun v => ⟨y v, hy v⟩`. Establish `key : ∀ u, f (W.rep x (GlobalTheory.CoefIrred.tenMul W u)) = RU E n x (f (GlobalTheory.CoefIrred.tenMul W u))`.

Introduce `u`. Establish `h1` using `prod_list_apply_multilinear π.rep s σ F hF y' u Finset.univ.toList (Finset.nodup_toList _)`. Establish `h2 : (Finset.univ.toList.map fun v => s v (y' v)).prod = x.1` using `hprod`. Rewrite `h1` using `[h2]`. Establish `h3 : W.rep x (GlobalTheory.CoefIrred.tenMul W u) = GlobalTheory.CoefIrred.tenMul W fun v => σ v (y' v) (u v)`.

Express the relevant statement in the definitionally equal form `Formalism.L2.DIV.rhoK W (cAll x.1) _ = _`. Rewrite using `[hten]`. Use `congrArg (GlobalTheory.CoefIrred.tenMul W) (funext fun v => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding (y v)) (u v)`. Rewrite using `[hyc v]`.

Both sides reduce to the same expression. Use `show (f0 (W.rep x (GlobalTheory.CoefIrred.tenMul W u))).1 = RU E n x (f0 (GlobalTheory.CoefIrred.tenMul W u)).1`. Rewrite using `[h3, hf0, hf0, ← AutSub.rep_val, h1]`. Simplify using `only [Finset.mem_toList, Finset.mem_univ, if_true]`. Use `(GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n W (UA E n → ℂ) ((f ∘ₗ W.rep x).compMultilinearMap (GlobalTheory.CoefIrred.tenMul W))).unique (y₁ := f ∘ₗ W.rep x) (y₂ := RU E n x ∘ₗ f) (fun u => (LinearMap.compMultilinearMap_apply _ _ _).symm) (fun …` as an intermediate fact.

Conclude with `LinearMap.congr_fun this w`. Establish `hmem : f ∈ algForms W` using `⟨fun w => π.le_autU (f0 w).2, hint⟩`. Establish `hfin : (⟨f, hmem⟩ : algForms W) ∈ π.finPart W` using `AutSub.mem_finPart.2 fun w => (f0 w).2`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u, F u ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hF0 (MultilinearMap.ext h)`. Use `(Submodule.ne_bot_iff _).2 ⟨⟨f, hmem⟩, hfin, fun h => hu ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun (congrArg Subtype.val h) (GlobalTheory.CoefIrred.tenMul W u)` as an intermediate fact. Rewrite using `[← hf0]`.

Conclude with `Subtype.ext this`.
-/
theorem AutSub.finPart_wt_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n),
    π.finPart (AU.mk π).wt ≠ ⊥ := by
  intro E _ _ _ n π
  classical
  have hW' : ∀ v : InfinitePlace E, HasWeightAt π.V v.embedding ((AU.mk π).wt v) := fun v => by
    obtain ⟨lam, hlam, -⟩ := GlobalTheory.T.existsUnique_weight_definiteUnitary_at E n (AU.mk π) v.embedding
    have h := hlam.wt
    rw [Wt.at_embedding] at h
    exact (AU.hasWt_mk π _ _).1 h
  generalize (AU.mk π).wt = W at hW' ⊢
  have hW := hW'
  clear hW'
  let s : ∀ v : InfinitePlace E, embU n v.embedding →* UA E n := fun v => (embU n v.embedding).subtype
  let σ : ∀ v : InfinitePlace E, Representation ℂ (embU n v.embedding) (nablaSq ℂ n (W v)) := fun v =>
    (GlobalTheory.Branching.sqRep ℂ n (W v)).comp ((cEmb v.embedding).comp (embU n v.embedding).subtype)
  have hirr : ∀ v, (σ v).IsIrreducible := fun v => by
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    obtain ⟨h1, h2⟩ := (CuspRep.isIrreducible_iff _).1 (GlobalTheory.Branching.isIrreducible_smallRep_unitary n (W v))
    refine (CuspRep.isIrreducible_iff _).2 ⟨h1, fun S hS => h2 S fun g w hw => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective g
    have := hS x w hw
    change GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding (x : UA E n)) w ∈ S at this
    change GlobalTheory.Branching.sqRep ℂ n (W v) (GlobalTheory.Branching.unitaryIncl n (e x)) w ∈ S
    rwa [he]
  have hcomm : ∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b) := fun u v huv a b =>
    GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places E n u.embedding v.embedding (by rwa [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding])
      _ a.2 _ b.2
  have hspan : ∀ v, (⨆ f : (σ v).IntertwiningMap (π.rep.comp (s v)), LinearMap.range f.toLinearMap) = ⊤ :=
    fun v => GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary E n π v.embedding (W v) (hW v)
  haveI : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.isAut.ne_bot
  obtain ⟨F, hF0, hF⟩ := GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups (InfinitePlace E) (UA E n) π.V (fun v => embU n v.embedding)
    (fun v => nablaSq ℂ n (W v)) π.rep s σ inferInstance hirr hcomm hspan
  obtain ⟨f0, hf0, -⟩ := GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n W π.V F
  let f : W.Sp →ₗ[ℂ] (UA E n → ℂ) := π.V.subtype ∘ₗ f0
  have hten : ∀ (g : InfinitePlace E → GL (Fin n) ℂ) (u : ∀ v, nablaSq ℂ n (W v)),
      Formalism.L2.DIV.rhoK W g (GlobalTheory.CoefIrred.tenMul (K := ℂ) W u) =
        GlobalTheory.CoefIrred.tenMul (K := ℂ) W fun v => GlobalTheory.Branching.sqRep ℂ n (W v) (g v) (u v) := fun g u => by
    apply Subtype.ext
    rw [Formalism.L2.DIV.rhoK_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.actTen, GlobalTheory.CoefIrred.tenMul_coe]
    rfl
  have hint : ∀ (x : infU E n) (w : W.Sp), f (W.rep x w) = RU E n x (f w) := by
    intro x w
    obtain ⟨y, hy, hyc, hprod⟩ := GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x.1 x.2
    let y' : ∀ v : InfinitePlace E, embU n v.embedding := fun v => ⟨y v, hy v⟩
    have key : ∀ u, f (W.rep x (GlobalTheory.CoefIrred.tenMul W u)) = RU E n x (f (GlobalTheory.CoefIrred.tenMul W u)) := by
      intro u
      have h1 := prod_list_apply_multilinear π.rep s σ F hF y' u Finset.univ.toList (Finset.nodup_toList _)
      have h2 : (Finset.univ.toList.map fun v => s v (y' v)).prod = x.1 := hprod
      rw [h2] at h1
      have h3 : W.rep x (GlobalTheory.CoefIrred.tenMul W u) = GlobalTheory.CoefIrred.tenMul W fun v => σ v (y' v) (u v) := by
        change Formalism.L2.DIV.rhoK W (cAll x.1) _ = _
        rw [hten]
        refine congrArg (GlobalTheory.CoefIrred.tenMul W) (funext fun v => ?_)
        change _ = GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding (y v)) (u v)
        rw [hyc v]
        rfl
      show (f0 (W.rep x (GlobalTheory.CoefIrred.tenMul W u))).1 = RU E n x (f0 (GlobalTheory.CoefIrred.tenMul W u)).1
      rw [h3, hf0, hf0, ← AutSub.rep_val, h1]
      simp only [Finset.mem_toList, Finset.mem_univ, if_true]
    have := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n W (UA E n → ℂ)
      ((f ∘ₗ W.rep x).compMultilinearMap (GlobalTheory.CoefIrred.tenMul W))).unique
      (y₁ := f ∘ₗ W.rep x) (y₂ := RU E n x ∘ₗ f) (fun u => (LinearMap.compMultilinearMap_apply _ _ _).symm)
      (fun u => by rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.comp_apply]; exact (key u).symm)
    exact LinearMap.congr_fun this w
  have hmem : f ∈ algForms W := ⟨fun w => π.le_autU (f0 w).2, hint⟩
  have hfin : (⟨f, hmem⟩ : algForms W) ∈ π.finPart W := AutSub.mem_finPart.2 fun w => (f0 w).2
  obtain ⟨u, hu⟩ : ∃ u, F u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hF0 (MultilinearMap.ext h)
  refine (Submodule.ne_bot_iff _).2 ⟨⟨f, hmem⟩, hfin, fun h => hu ?_⟩
  have := LinearMap.congr_fun (congrArg Subtype.val h) (GlobalTheory.CoefIrred.tenMul W u)
  rw [← hf0]
  exact Subtype.ext this

end GlobalTheory.DefU

end
