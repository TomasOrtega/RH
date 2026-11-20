import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.VB

section Generic

variable {X : Scheme.{0}} [IsIntegral X]

/- English proof (translation)
The claim follows from `have ⟨e⟩ := Twist.nonempty_stalkEquiv (F := F) hM (genericPoint X) e.finrank_eq`.
-/
theorem genRank_twist {F : X.Modules} {M : LB X} (hM : M.IsLB) :
    genRank (twist F M) = genRank F :=
  have ⟨e⟩ := Twist.nonempty_stalkEquiv (F := F) hM (genericPoint X)
  e.finrank_eq

/- English proof (translation)
Take `⟨n, s, hs⟩` from `QCoh.isGloballyGenerated_iff_spanStalks.1 h`. Use `by_contra! H`. Establish `: Subsingleton (genStalk F)` using `subsingleton_of_forall_eq 0 fun t => by`. Establish `ht` using `(hs (genericPoint X)).ge (Submodule.mem_top (x := t))`. Establish `e : (Set.range fun i => ((F.presheaf.germ ⊤ (genericPoint X) trivial (s i) : (F.presheaf.stalk (genericPoint X) :)))) ⊆ {0}`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `H _`. Simplify using `using Submodule.span_mono e ht`. Conclude with `hr Module.finrank_zero_of_subsingleton`.
-/
theorem exists_germ_ne_zero {F : X.Modules} (h : QCoh.IsGloballyGenerated F)
    (hr : genRank F ≠ 0) :
    ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0 := by
  obtain ⟨n, s, hs⟩ := QCoh.isGloballyGenerated_iff_spanStalks.1 h
  by_contra! H
  have : Subsingleton (genStalk F) := subsingleton_of_forall_eq 0 fun t => by
    have ht := (hs (genericPoint X)).ge (Submodule.mem_top (x := t))
    have e : (Set.range fun i => ((F.presheaf.germ ⊤ (genericPoint X) trivial (s i) :
        (F.presheaf.stalk (genericPoint X) :)))) ⊆ {0} := by
      rintro _ ⟨i, rfl⟩
      exact H _
    simpa using Submodule.span_mono e ht
  exact hr Module.finrank_zero_of_subsingleton

/- English proof (translation)
Use `QCoh.mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩` and prove the remaining obligations. Establish `hη` using `genericPoint_mem hx`. Apply `(QCoh.structureModuleSectionsEquiv W).injective` to reduce the goal to its premises. Establish `e' : (QCoh.structureModuleSectionsEquiv W a - QCoh.structureModuleSectionsEquiv W b) • Twist.resM F (le_top : W ≤ ⊤) s = 0`. Rewrite using `[sub_smul, sub_eq_zero]`.

Conclude with `e`. Establish `e''` using `congrArg (F.presheaf.germ W _ hη) e'`. Rewrite `e''` using `[QCoh.germ_smul, Twist.germ_resM, map_zero]`. Use `(smul_eq_zero.1 e'').resolve_right hs` as an intermediate fact. Conclude with `sub_eq_zero.1 (germ_injective_of_isIntegral X _ hη (this.trans (map_zero _).symm))`.
-/
theorem mono_sectionHom {F : X.Modules} (s : Γ(F, ⊤))
    (hs : F.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0) : Mono (QCoh.sectionHom s) := by
  refine QCoh.mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩
  have hη := genericPoint_mem hx
  apply (QCoh.structureModuleSectionsEquiv W).injective
  have e' : (QCoh.structureModuleSectionsEquiv W a - QCoh.structureModuleSectionsEquiv W b) •
      Twist.resM F (le_top : W ≤ ⊤) s = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact e
  have e'' := congrArg (F.presheaf.germ W _ hη) e'
  rw [QCoh.germ_smul, Twist.germ_resM, map_zero] at e''
  have := (smul_eq_zero.1 e'').resolve_right hs
  exact sub_eq_zero.1 (germ_injective_of_isIntegral X _ hη (this.trans (map_zero _).symm))

end Generic

variable {κ : Type} [Field κ] {Z : Scheme.{0}} [IsIntegral Z] [Algebra κ Γ(Z, ⊤)]

/- English proof (translation)
Establish `hf` using `algebraMap_eq_strHom κ Z`. Establish `hL` using `isLB_vecOne hN`. Establish `h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F` using `fun {F} _ => finiteCohTwists_of_isProjOver hf F hp`. Take `⟨_, A, hA⟩` from `isProper_and_exists_isAmpleLB_of_isProjOver hp`. Proceed by induction on `r with`.

Consider the case `zero`. Introduce `G _ h`. Establish `h0 : QCoh.suppDim G ≤ 0` using `suppDim_le_zero hd h`. Establish `: QCoh.suppDim G < Fintype.card (Fin 1)` using `h0.trans_lt (by simp)`. Rewrite using `[interNum_eq_zero_of_isProjOver hf G hp this hL]`.

Simplify using the standard rewrite rules. Consider the case `succ r ih`. Introduce `G _ h`. Take `⟨n, hn⟩` from `(hA.eventually_isGloballyGenerated_twist G).exists`. Establish `hM` using `isLB_lbPow hA.isLB n`.

Use `Twist.isFiniteQC_twist (F := G) hM` as an intermediate fact. Establish `hr : genRank (twist G (lbPow A n)) = r + 1` using `(genRank_twist hM).trans h`. Take `⟨s, hs⟩` from `exists_germ_ne_zero hn (by omega)`. Use `mono_sectionHom s hs` as an intermediate fact. Establish `e₁ : interNum κ (twist G (lbPow A n)) ![N] = interNum κ G ![N]` using `(diffVanish_chiPic_of_isProjOver (d := 1) hf G hp ((QCoh.suppDim_le G).trans_eq (by rw [hd]; rfl))).interNum_twist (by simp) hL hM`.

Establish `e₂` using `interNum_cokernel (k := κ) (QCoh.sectionHom s) hL h1 h1`. Establish `e₃` using `genRank_cokernel (QCoh.sectionHom s)`. Rewrite `e₃` using `[(isVB_structureModule Z).genRank_eq, hr]`. Rewrite `e₂` using `[ih _ (by omega)]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem interNum_one_of_genRank_eq (hp : IsProjOver (strHom κ Z)) (hd : topologicalKrullDim Z = 1)
    {N : LB Z} (hN : N.IsLB) (r : ℕ) :
    ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G ![N] = r * interNum κ (structureModule Z) ![N] := by
  have hf := algebraMap_eq_strHom κ Z
  have hL := isLB_vecOne hN
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    have h0 : QCoh.suppDim G ≤ 0 := suppDim_le_zero hd h
    have : QCoh.suppDim G < Fintype.card (Fin 1) := h0.trans_lt (by simp)
    rw [interNum_eq_zero_of_isProjOver hf G hp this hL]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) ![N] = interNum κ G ![N] :=
      (diffVanish_chiPic_of_isProjOver (d := 1) hf G hp
        ((QCoh.suppDim_le G).trans_eq (by rw [hd]; rfl))).interNum_twist (by simp) hL hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hL h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

/- English proof (translation)
Introduce `_ _ _ _ _ hp hd G _ _ hN` and use `interNum_one_of_genRank_eq hp hd hN _ G rfl`.
-/
theorem interNum_one_eq_genRank_mul : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z]
    [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → topologicalKrullDim Z = 1 →
    ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (N : LB Z), N.IsLB →
      interNum κ G ![N] = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) ![N] :=
  fun _ _ _ _ _ hp hd G _ _ hN => interNum_one_of_genRank_eq hp hd hN _ G rfl

end GlobalTheory.VB
