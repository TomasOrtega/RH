import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterSplitPlaceLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionCompletionBlockTriLowerBlockDetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitTwistPlaceOverProductCharacterRamifieStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeAndTwistPlacesOverOtherThanSplitStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtPara

/- English proof (translation)
Introduce `D T L μ0 hL hPg i t hr ψ v hv`. Take `⟨s, hsv, hsQ⟩` from `GlobalTheory.T.exists_splitTwistPlace_over_productCharacter_ramified D T L μ0 hL i t v hv`. Establish `hvg : s.v ∉ gPl D` using `hsv ▸ hv.1`. Take `⟨hPgo, hQo⟩` from `GlobalTheory.T.typeAndTwistPlaces_over_other_than_split D T L μ0 hL hPg t s hvg hsQ`. Establish `hunr : (L.C.mu0 i).UnrAt s.w`.

Use `(L.C.isMu0 i).unr s.w fun k hk => hvg ⟨s.w, s.w_under, k, hk⟩` and prove the remaining obligations. Establish `htame : (L.C.mu0 i * L.xiH t).TameAt s.w`. Introduce `x hx hx1`. Rewrite using `[HChar.loc_mul, (L.C.isMu0 i).tame s.w x hx hx1, hL.xi_tame t s.w x hx hx1, one_mul]`. Take `⟨ξ, hξc, hξr⟩` from `GlobalTheory.T.tame_heckeCharacter_split_place_local_component D.host.E s _ htame`.

Take `⟨hUA, hSt, hred, hloc⟩` from `GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV`. Take `⟨φ, -, hφ0, hφa, hφe⟩` from `hloc s`. Establish `hoff : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ PP, (PP ∈ L.Pg ∨ (PP ∈ L.Q t ∧ PP ≠ s.w)) → redFn 1 PP (km D D.R.nV κ) = 1`. Introduce `κ hκ htr PP hPP`. Take `⟨v', hov, hne⟩ : ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v` from `hPP.elim (hPgo PP) (fun h => hQo PP h.1 h.2)`.

Conclude with `hred κ hκ {s.v} v' PP htr hov (by simpa using hne)`. Use `⟨s, ξ, hsv, hξc, ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `κ htr`. Establish `hkey : ∀ hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, (redFn 1 s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) ↔ ∀ a b : Fin D.R.nV, D.R.r ≤ a.val → b.val < D.R.r → Valued.v (((s.loc D.R.nV κ : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) : Matrix (Fin …` using `fun hκ => (GlobalTheory.T.reduction_completion_blockTri_lowerBlockDet D.host.E s φ D.R.nV D.R.r (s.loc D.R.nV κ) (redFn 1 s.w (km D D.R.nV κ)) hφ0 (hφe κ hκ)).1`. Prove the components needed by the constructor for the conclusion.

Introduce `hJ`. Establish `hJ' : km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1 _` using `hJ`. Rewrite `hJ'` using `[mem_lev, mem_parLev]`. Take `⟨⟨-, hSt', -, hQ'⟩, -⟩` from `hJ'`. Establish `hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV` using `(hSt κ).1 hSt'`.

Use `⟨GlobalTheory.HeckeStdFacts.mem_GLint_iff.2 ⟨fun a b => GlobalTheory.HeckeStdFacts.proj_mem s (hκU a b), fun a b => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `GlobalTheory.HeckeStdFacts.proj_mem s ((inv_mem hκU) a b)`. Conclude with `(hkey hκU).1 (hQ' s.w hsQ)`. Introduce and unpack `⟨hG, hlow⟩`.

Take `⟨hG1, hG2⟩` from `GlobalTheory.HeckeStdFacts.mem_GLint_iff.1 hG`. Establish `hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV` using `GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ htr (fun a b => hG1 a b) (fun a b => by rw [map_inv]; exact hG2 a b)`. Establish `hrt : rTup 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = 1`. Use function extensionality and compare the values at `PP`. Use `show upperLeftBlock hr (redFn 1 PP.1 (km D D.R.nV κ)) = 1`.

Rewrite using `[hoff κ hκU htr PP.1 (Or.inl PP.2)]`. Conclude with `blockDiagonalExtendByOnePrimeField_one _ _`. Use `show km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1 _`. Rewrite using `[mem_lev, mem_parLev, hrt]`. Use `⟨⟨hUA κ, (hSt κ).2 hκU, fun PP hPP => ?_, fun PP hPP => ?_⟩, Subgroup.one_mem _⟩` and prove the remaining obligations.

Rewrite using `[hoff κ hκU htr PP (Or.inl hPP)]`. Conclude with `Subgroup.one_mem _`. Distinguish the cases in `hPs : PP = s.w`. Substitute `hPs` using the available equality. Conclude with `(hkey hκU).2 hlow`.

Rewrite using `[hoff κ hκU htr PP (Or.inr ⟨hPP, hPs⟩)]`. Conclude with `Subgroup.one_mem _`. Introduce `κ hJ htr u hu`. Establish `hJ' : km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))` using `hJ`. Establish `hpar` using `(mem_lev.1 hJ').1`.

Establish `hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV` using `(hSt κ).1 (parLev_St hpar)`. Establish `hrt : rTup 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = 1`. Use function extensionality and compare the values at `PP`. Use `show upperLeftBlock hr (redFn 1 PP.1 (km D D.R.nV κ)) = 1`. Rewrite using `[hoff κ hκU htr PP.1 (Or.inl PP.2)]`.

Conclude with `blockDiagonalExtendByOnePrimeField_one _ _`. Establish `hQ' : redFn 1 s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r)` using `parLev_q hpar hsQ`. Take `⟨hd, hdv⟩` from `(GlobalTheory.T.reduction_completion_blockTri_lowerBlockDet D.host.E s φ D.R.nV D.R.r (s.loc D.R.nV κ) (redFn 1 s.w (km D D.R.nV κ)) hφ0 (hφe κ hκU)).2 hQ'`. Take `⟨w0, hw0⟩ : ∃ w0, w0 = dBlk (blk2 D.R.r) 1 (redFn 1 s.w (km D D.R.nV κ))` from `⟨_, rfl⟩`. Rewrite `hdv` using `[← hw0]`.

Establish `hQ1 : ∏ PP ∈ L.Q t, L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP (km D D.R.nV κ))) = L.xiR t s.w w0`. Rewrite using `[hw0]`. Use `Finset.prod_eq_single_of_mem s.w hsQ fun PP hPP hne => ?_` and prove the remaining obligations. Rewrite using `[hoff κ hκU htr PP (Or.inr ⟨hPP, hne⟩)]`. Use `show L.xiR t PP (ext1 _ _ 1) = 1`.

Rewrite using `[blockDiagonalExtendByOnePrimeField_one, map_one]`. Establish `hval : stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) ⟨κ, hJ⟩ = L.xiR t s.w w0` using `by show levFn 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = _`. Unfold `levFn`. Rewrite using `[hrt, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, one_mul]`. Conclude with `hQ1`.

Introduce `PP hPP`. Use `Finset.prod_eq_one fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hoff κ hκU htr PP (Or.inl hPP)]`. Conclude with `(congrArg _ (blockDiagonalExtendByOnePrimeField_one _ _)).trans (map_one _)`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (w0 : kP s.w)`.

Establish `hw0ne : (w0 : kP s.w) ≠ 0` using `w0.ne_zero`. Establish `haP : a ∉ s.w.asIdeal` using `fun h => hw0ne (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)`. Establish `ha0 : (a : D.host.E) ≠ 0` using `fun h => haP (by`. Rewrite using `[show a = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]`. Conclude with `zero_mem _)`.

Take `⟨k, hk⟩ : ∃ k : D.host.Eˣ, (k : D.host.E) = a` from `⟨Units.mk0 _ ha0, rfl⟩`. Establish `hres : L.xiR t s.w w0 = (L.xiH t).locK s.w k` using `hL.xiR t s.w hsQ a k w0 hk ha.symm`. Take `⟨hia, hφia⟩` from `hφa a`. Establish `hu1 : Valued.v (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1`. Rewrite using `[hu]`.

Use `le_antisymm hd (not_lt.1 fun hlt => hw0ne ?_)` and prove the remaining obligations. Rewrite using `[hdv]`. Conclude with `(hφ0 _).2 hlt`. Establish `hu2 : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - s.i (a : D.host.E)) < 1`. Establish `h0 : φ (⟨_, hd⟩ - ⟨_, hia⟩) = 0` using `by rw [map_sub, ← hdv, hφia, ha, sub_self]`.

Establish `h1` using `(hφ0 _).1 h0`. Rewrite `h1` using `[AddSubgroupClass.coe_sub]`. Rewrite using `[hu]`. Conclude with `h1`. Establish `hk1 : (L.C.mu0 i).locK s.w k = 1`.

Establish `hv1 : Valued.v (((k : D.host.E) : s.w.adicCompletion D.host.E)) = 1`. Rewrite using `[hk]`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', RingOfIntegers.coe_eq_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]`. Conclude with `haP`. Conclude with `hunr _ hv1`.

Establish `hmul : (L.C.mu0 i * L.xiH t).locK s.w k = (L.C.mu0 i).locK s.w k * (L.xiH t).locK s.w k` using `HChar.loc_mul _ _ s.w (atFin s.w k)`. Use `hval.trans (hres.trans ?_)` and prove the remaining obligations. Rewrite using `[hξr u a k hk hu1 hu2, hmul, hk1, one_mul]`.
-/
theorem levelPara : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), ∀ v ∈ qPl D (L.C.mu0 i * L.xiH t), ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelPara (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ξ := by
  intro D T L μ0 hL hPg i t hr ψ v hv
  obtain ⟨s, hsv, hsQ⟩ := GlobalTheory.T.exists_splitTwistPlace_over_productCharacter_ramified D T L μ0 hL i t v hv
  have hvg : s.v ∉ gPl D := hsv ▸ hv.1
  obtain ⟨hPgo, hQo⟩ := GlobalTheory.T.typeAndTwistPlaces_over_other_than_split D T L μ0 hL hPg t s hvg hsQ

  have hunr : (L.C.mu0 i).UnrAt s.w := by
    refine (L.C.isMu0 i).unr s.w fun k hk => hvg ⟨s.w, s.w_under, k, hk⟩
  have htame : (L.C.mu0 i * L.xiH t).TameAt s.w := by
    intro x hx hx1
    rw [HChar.loc_mul, (L.C.isMu0 i).tame s.w x hx hx1, hL.xi_tame t s.w x hx hx1, one_mul]
  obtain ⟨ξ, hξc, hξr⟩ := GlobalTheory.T.tame_heckeCharacter_split_place_local_component D.host.E s _ htame
  obtain ⟨hUA, hSt, hred, hloc⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV
  obtain ⟨φ, -, hφ0, hφa, hφe⟩ := hloc s
  have hoff : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ PP,
      (PP ∈ L.Pg ∨ (PP ∈ L.Q t ∧ PP ≠ s.w)) → redFn 1 PP (km D D.R.nV κ) = 1 := by
    intro κ hκ htr PP hPP
    obtain ⟨v', hov, hne⟩ : ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v :=
      hPP.elim (hPgo PP) (fun h => hQo PP h.1 h.2)
    exact hred κ hκ {s.v} v' PP htr hov (by simpa using hne)
  refine ⟨s, ξ, hsv, hξc, ⟨?_, ?_⟩⟩
  · intro κ htr
    have hkey : ∀ hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV,
        (redFn 1 s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) ↔ ∀ a b : Fin D.R.nV, D.R.r ≤ a.val → b.val < D.R.r →
          Valued.v (((s.loc D.R.nV κ : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) := fun hκ =>
      (GlobalTheory.T.reduction_completion_blockTri_lowerBlockDet D.host.E s φ D.R.nV D.R.r (s.loc D.R.nV κ) (redFn 1 s.w (km D D.R.nV κ)) hφ0 (hφe κ hκ)).1
    constructor
    · intro hJ
      have hJ' : km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1 _ := hJ
      rw [mem_lev, mem_parLev] at hJ'
      obtain ⟨⟨-, hSt', -, hQ'⟩, -⟩ := hJ'
      have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := (hSt κ).1 hSt'
      refine ⟨GlobalTheory.HeckeStdFacts.mem_GLint_iff.2 ⟨fun a b => GlobalTheory.HeckeStdFacts.proj_mem s (hκU a b), fun a b => ?_⟩, ?_⟩
      · rw [← map_inv]
        exact GlobalTheory.HeckeStdFacts.proj_mem s ((inv_mem hκU) a b)
      · exact (hkey hκU).1 (hQ' s.w hsQ)
    · rintro ⟨hG, hlow⟩
      obtain ⟨hG1, hG2⟩ := GlobalTheory.HeckeStdFacts.mem_GLint_iff.1 hG
      have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV :=
        GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ htr (fun a b => hG1 a b) (fun a b => by rw [map_inv]; exact hG2 a b)
      have hrt : rTup 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = 1 := by
        funext PP
        show upperLeftBlock hr (redFn 1 PP.1 (km D D.R.nV κ)) = 1
        rw [hoff κ hκU htr PP.1 (Or.inl PP.2)]
        exact blockDiagonalExtendByOnePrimeField_one _ _
      show km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1 _
      rw [mem_lev, mem_parLev, hrt]
      refine ⟨⟨hUA κ, (hSt κ).2 hκU, fun PP hPP => ?_, fun PP hPP => ?_⟩, Subgroup.one_mem _⟩
      · rw [hoff κ hκU htr PP (Or.inl hPP)]; exact Subgroup.one_mem _
      · by_cases hPs : PP = s.w
        · subst hPs; exact (hkey hκU).2 hlow
        · rw [hoff κ hκU htr PP (Or.inr ⟨hPP, hPs⟩)]; exact Subgroup.one_mem _
  · intro κ hJ htr u hu
    have hJ' : km D D.R.nV κ ∈ lev D.sp.cm (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) D.host.E) 1
        (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) := hJ
    have hpar := (mem_lev.1 hJ').1
    have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := (hSt κ).1 (parLev_St hpar)
    have hrt : rTup 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = 1 := by
      funext PP
      show upperLeftBlock hr (redFn 1 PP.1 (km D D.R.nV κ)) = 1
      rw [hoff κ hκU htr PP.1 (Or.inl PP.2)]
      exact blockDiagonalExtendByOnePrimeField_one _ _
    have hQ' : redFn 1 s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) := parLev_q hpar hsQ
    obtain ⟨hd, hdv⟩ := (GlobalTheory.T.reduction_completion_blockTri_lowerBlockDet D.host.E s φ D.R.nV D.R.r (s.loc D.R.nV κ) (redFn 1 s.w (km D D.R.nV κ)) hφ0 (hφe κ hκU)).2 hQ'
    obtain ⟨w0, hw0⟩ : ∃ w0, w0 = dBlk (blk2 D.R.r) 1 (redFn 1 s.w (km D D.R.nV κ)) := ⟨_, rfl⟩
    rw [← hw0] at hdv
    have hQ1 : ∏ PP ∈ L.Q t, L.xiR t PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP (km D D.R.nV κ))) = L.xiR t s.w w0 := by
      rw [hw0]
      refine Finset.prod_eq_single_of_mem s.w hsQ fun PP hPP hne => ?_
      rw [hoff κ hκU htr PP (Or.inr ⟨hPP, hne⟩)]
      show L.xiR t PP (ext1 _ _ 1) = 1
      rw [blockDiagonalExtendByOnePrimeField_one, map_one]
    have hval : stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) ⟨κ, hJ⟩ =
        L.xiR t s.w w0 := by
      show levFn 1 (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t)) (km D D.R.nV κ) = _
      unfold levFn
      rw [hrt, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, one_mul]
      · exact hQ1
      · intro PP hPP
        refine Finset.prod_eq_one fun c _ => ?_
        rw [hoff κ hκU htr PP (Or.inl hPP)]
        exact (congrArg _ (blockDiagonalExtendByOnePrimeField_one _ _)).trans (map_one _)
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (w0 : kP s.w)
    have hw0ne : (w0 : kP s.w) ≠ 0 := w0.ne_zero
    have haP : a ∉ s.w.asIdeal := fun h => hw0ne (by rw [← ha]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
    have ha0 : (a : D.host.E) ≠ 0 := fun h => haP (by
      rw [show a = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
    obtain ⟨k, hk⟩ : ∃ k : D.host.Eˣ, (k : D.host.E) = a := ⟨Units.mk0 _ ha0, rfl⟩
    have hres : L.xiR t s.w w0 = (L.xiH t).locK s.w k := hL.xiR t s.w hsQ a k w0 hk ha.symm
    obtain ⟨hia, hφia⟩ := hφa a
    have hu1 : Valued.v (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by
      rw [hu]
      refine le_antisymm hd (not_lt.1 fun hlt => hw0ne ?_)
      rw [hdv]; exact (hφ0 _).2 hlt
    have hu2 : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield D.host.E)) - s.i (a : D.host.E)) < 1 := by
      have h0 : φ (⟨_, hd⟩ - ⟨_, hia⟩) = 0 := by rw [map_sub, ← hdv, hφia, ha, sub_self]
      have h1 := (hφ0 _).1 h0
      rw [AddSubgroupClass.coe_sub] at h1
      rw [hu]; exact h1
    have hk1 : (L.C.mu0 i).locK s.w k = 1 := by
      have hv1 : Valued.v (((k : D.host.E) : s.w.adicCompletion D.host.E)) = 1 := by
        rw [hk]
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', RingOfIntegers.coe_eq_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
          HeightOneSpectrum.intValuation_eq_one_iff]
        exact haP
      exact hunr _ hv1
    have hmul : (L.C.mu0 i * L.xiH t).locK s.w k = (L.C.mu0 i).locK s.w k * (L.xiH t).locK s.w k :=
      HChar.loc_mul _ _ s.w (atFin s.w k)
    refine hval.trans (hres.trans ?_)
    rw [hξr u a k hk hu1 hu2, hmul, hk1, one_mul]

end GlobalTheory.MtPara
