import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEigAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ShuffleChoices.FixedEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProductsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsolateRepresentationAtCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotientsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitDictionaryHolds

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Unfold `PositivityTheory.Rg.BcN.F2.hk`. Rewrite using `[smul_finsum]`. Conclude with `finsum_congr fun q => mul_smul _ _ _`.
-/
private theorem hk_const_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (c : ℂ) (e : GL ι F → ℂ) (v : V) :
    PositivityTheory.Rg.BcN.F2.hk ρ K (fun g => c * e g) v = c • PositivityTheory.Rg.BcN.F2.hk ρ K e v := by
  unfold PositivityTheory.Rg.BcN.F2.hk
  rw [smul_finsum]
  exact finsum_congr fun q => mul_smul _ _ _

/- English proof (translation)
Introduce `E _ _ _ n w hw K' hKo hKle hlev σ hσ k D`. Establish `hUL : UL n w = ⊤` using `by unfold UL; rw [if_pos hw]`. Establish `hmap : (K'.subgroupOf (UL n w)).map (UL n w).subtype = K'`. Rewrite using `[Subgroup.subgroupOf_map_subtype, hUL, inf_top_eq]`. Establish `hKc : IsCompact (K' : Set (GLw n w))` using `(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset (Subgroup.isClosed_of_isOpen K' hKo) hKle`.

Take `⟨P, T, hT, hcomp, hdict⟩` from `GlobalTheory.CompanionTheory.SplitPlace.splitDict E n w hw σ`. Establish `hd` using `hdict (K'.subgroupOf (UL n w)) hlev`. Rewrite `hd` using `[hmap]`. Take `⟨y₀, hy₀, hy₀0⟩` from `(Submodule.ne_bot_iff _).1 hσ`. Establish `hz : PositivityTheory.Rg.BcN.F2.IsHk K' (0 : GLw n w → ℂ)` using `⟨hKo, hKc, HasCompactSupport.zero, fun _ _ _ _ _ => rfl⟩`.

Establish `hP0 : ∃ v ∈ fixed P.ρ K', v ≠ 0` using `⟨T y₀, ((hd 0 hz).2 y₀ hy₀).1, fun h => hy₀0 (T.map_eq_zero_iff.1 h)⟩`. Take `⟨e₀, hIk, ⟨v₀, hv₀, l, hl1, hl⟩, hkill⟩` from `PositivityTheory.Rg.BcB.F.Choice.choiceS_of (fun E _ _ _ n w => GlobalTheory.T.isolate_representation_at_character _ _) (fun E _ _ _ n w => GlobalTheory.T.finite_subquotients _ _) (fun E _ _ _ n w => GlobalTheory.T.finite_length_of_products _ _) E n w K' hKo hKc P hP0 k D`. Use `set r : ℂ := (((K'.subgroupOf (UL n w)).relIndex (KL n w) : ℕ) : ℂ) with hr`. Establish `hIk' : PositivityTheory.Rg.BcN.F2.IsHk K' (fun g => r * e₀ g)` using `⟨hIk.1, hIk.2.1, hIk.2.2.1.mul_left, fun k₁ h₁ k₂ h₂ g => by`. Simplify using `only [hIk.2.2.2 k₁ h₁ k₂ h₂ g]⟩`.

Establish `hH` using `(hd _ hIk').1`. Use `⟨fun g => r * e₀ g, P, hIk', hH, hcomp, ?_, ?_⟩` and prove the remaining obligations. Establish `hy : T.symm v₀ ∈ fixed σ.ρ (K'.subgroupOf (UL n w))`. Introduce and unpack `⟨x, hx⟩`. Apply `T.injective` to reduce the goal to its premises.

Establish `h1` using `hv₀ ⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩`. Rewrite using `[map_smul, hT, T.apply_symm_apply]`. Simplify using `using h1`. Use `⟨⟨T.symm v₀, hy⟩, fun h => ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : T.symm v₀ = 0` using `congrArg Subtype.val h`.

Establish `h1 : v₀ = 0` using `T.symm.map_eq_zero_iff.1 h0`. Rewrite `hl1` using `[h1, map_zero]`. Conclude with `zero_ne_one hl1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[(GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ _ hlev _ _ hH hH).2.1]`.

Apply `T.injective` to reduce the goal to its premises. Establish `h2` using `((hd e₀ hIk).2 _ hy).2`. Rewrite `h2` using `[T.apply_symm_apply, hl v₀ hv₀, hl1, one_smul]`. Rewrite using `[h2, T.apply_symm_apply]`. Introduce `j τ hs hne v hv`.

Rewrite using `[hk_const_mul, hkill j τ hs hne v hv, smul_zero]`.
-/
theorem UpperTheory.HeckeLevelFrameExistence.locE :
    UpperTheory.HeckeLevelFrameExistence.LocE := by
  intro E _ _ _ n w hw K' hKo hKle hlev σ hσ k D
  have hUL : UL n w = ⊤ := by unfold UL; rw [if_pos hw]
  have hmap : (K'.subgroupOf (UL n w)).map (UL n w).subtype = K' := by
    rw [Subgroup.subgroupOf_map_subtype, hUL, inf_top_eq]
  have hKc : IsCompact (K' : Set (GLw n w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen K' hKo) hKle
  obtain ⟨P, T, hT, hcomp, hdict⟩ := GlobalTheory.CompanionTheory.SplitPlace.splitDict E n w hw σ
  have hd := hdict (K'.subgroupOf (UL n w)) hlev
  rw [hmap] at hd
  obtain ⟨y₀, hy₀, hy₀0⟩ := (Submodule.ne_bot_iff _).1 hσ
  have hz : PositivityTheory.Rg.BcN.F2.IsHk K' (0 : GLw n w → ℂ) :=
    ⟨hKo, hKc, HasCompactSupport.zero, fun _ _ _ _ _ => rfl⟩
  have hP0 : ∃ v ∈ fixed P.ρ K', v ≠ 0 :=
    ⟨T y₀, ((hd 0 hz).2 y₀ hy₀).1, fun h => hy₀0 (T.map_eq_zero_iff.1 h)⟩
  obtain ⟨e₀, hIk, ⟨v₀, hv₀, l, hl1, hl⟩, hkill⟩ :=
    PositivityTheory.Rg.BcB.F.Choice.choiceS_of (fun E _ _ _ n w => GlobalTheory.T.isolate_representation_at_character _ _)
      (fun E _ _ _ n w => GlobalTheory.T.finite_subquotients _ _) (fun E _ _ _ n w => GlobalTheory.T.finite_length_of_products _ _)
      E n w K' hKo hKc P hP0 k D
  set r : ℂ := (((K'.subgroupOf (UL n w)).relIndex (KL n w) : ℕ) : ℂ) with hr
  have hIk' : PositivityTheory.Rg.BcN.F2.IsHk K' (fun g => r * e₀ g) :=
    ⟨hIk.1, hIk.2.1, hIk.2.2.1.mul_left, fun k₁ h₁ k₂ h₂ g => by
      simp only [hIk.2.2.2 k₁ h₁ k₂ h₂ g]⟩
  have hH := (hd _ hIk').1
  refine ⟨fun g => r * e₀ g, P, hIk', hH, hcomp, ?_, ?_⟩
  · have hy : T.symm v₀ ∈ fixed σ.ρ (K'.subgroupOf (UL n w)) := by
      rintro ⟨x, hx⟩
      apply T.injective
      have h1 := hv₀ ⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩
      rw [map_smul, hT, T.apply_symm_apply]
      simpa using h1
    refine ⟨⟨T.symm v₀, hy⟩, fun h => ?_, ?_⟩
    · have h0 : T.symm v₀ = 0 := congrArg Subtype.val h
      have h1 : v₀ = 0 := T.symm.map_eq_zero_iff.1 h0
      rw [h1, map_zero] at hl1
      exact zero_ne_one hl1
    · apply Subtype.ext
      rw [(GlobalTheory.CompanionTheory.LocHecke.locAlg E n w σ _ hlev _ _ hH hH).2.1]
      apply T.injective
      have h2 := ((hd e₀ hIk).2 _ hy).2
      rw [T.apply_symm_apply, hl v₀ hv₀, hl1, one_smul] at h2
      rw [h2, T.apply_symm_apply]
  · intro j τ hs hne v hv
    rw [hk_const_mul, hkill j τ hs hne v hv, smul_zero]
