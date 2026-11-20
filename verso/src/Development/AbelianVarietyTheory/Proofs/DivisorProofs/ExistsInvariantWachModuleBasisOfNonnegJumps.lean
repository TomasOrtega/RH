import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachRingFactsUnramifiedLevelOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAddPiSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsOverLettersOfCrysWith
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeightsFromJumpsIff
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors
import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachFrame

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD LL O v f) {T : LocLat G Qp LL O} {n : ℕ}

/- English proof (translation)
Use `W.γD_smul T g (algebraMap (LetA O f) W.EE a) x` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, W.γE_ext, algebraMap_smul]`. Then use the resulting hypothesis.
-/
theorem γD_smulA (g : W.Gam) (a : LetA O f) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O f) W.EE a) x
  rwa [algebraMap_smul, W.γE_ext, algebraMap_smul] at this

/- English proof (translation)
Establish `h1` using `congrArg Subtype.val (b.sum_repr y)`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h1`. Conclude with `h1.symm`.
-/
theorem coe_eq_sum (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (y : ↥(W.N T)) :
    (y : W.DD T) = ∑ m, b.repr y m • (b m : W.DD T) := by
  have h1 := congrArg Subtype.val (b.sum_repr y)
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h1
  exact h1.symm

/- English proof (translation)
Establish `e : ∑ m, W.γA δ (b.repr y m) • b m = y`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : W.γD T δ (y : W.DD T) = ∑ m, W.γA δ (b.repr y m) • (b m : W.DD T)` using `by conv_lhs => rw [coe_eq_sum W b y, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[γD_smulA, (hb m).2 δ hδ]`.

Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]`. Conclude with `h1.symm.trans hy`. Establish `h2` using `congrFun (b.repr_sum_self fun m => W.γA δ (b.repr y m)) m`. Rewrite `h2` using `[e]`. Conclude with `h2.symm`.
-/
theorem coord_fixed (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (y : ↥(W.N T)) (δ : W.Gam) (hδ : δ ∈ W.DelF) (hy : W.γD T δ (y : W.DD T) = y) (m : Fin n) :
    W.γA δ (b.repr y m) = b.repr y m := by
  have e : ∑ m, W.γA δ (b.repr y m) • b m = y := by
    apply Subtype.ext
    have h1 : W.γD T δ (y : W.DD T) = ∑ m, W.γA δ (b.repr y m) • (b m : W.DD T) := by
      conv_lhs => rw [coe_eq_sum W b y, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [γD_smulA, (hb m).2 δ hδ]
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    exact h1.symm.trans hy
  have h2 := congrFun (b.repr_sum_self fun m => W.γA δ (b.repr y m)) m
  rw [e] at h2
  exact h2.symm

variable (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]

/- English proof (translation)
The claim follows from `hI _ fun δ hδ => congrFun (coord_fixed W b hb y δ hδ (hy δ hδ) m) i`.
-/
theorem exists_inc (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (y : ↥(W.N T)) (hy : ∀ δ ∈ W.DelF, W.γD T δ (y : W.DD T) = y) (m : Fin n) (i : ZMod f) :
    ∃ z, inc l O z = b.repr y m i :=
  hI _ fun δ hδ => congrFun (coord_fixed W b hb y δ hδ (hy δ hδ) m) i

/- English proof (translation)
Establish `h : ∀ i m k, ∃ z, inc l O z = b.repr ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩ m i` using `fun i m k => exists_inc W l hI b hb _ (fun δ hδ => by`. Express the relevant statement in the definitionally equal form `W.γD T δ (W.φD T (b k : W.DD T)) = W.φD T (b k : W.DD T)`. Rewrite using `[← W.φγ_comm, (hb k).2 δ hδ]) m i`. Use `choose Pm hPm using h`. Use `⟨fun i => Matrix.of (Pm i), fun k => ?_⟩` and prove the remaining obligations.

Use `(coe_eq_sum W b ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩).trans (Finset.sum_congr rfl fun m _ => ?_)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(hPm i m k).symm`.
-/
theorem exists_phi_matrix (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (hφ : ∀ x ∈ W.N T, W.φD T x ∈ W.N T) :
    ∃ Pm : ZMod f → Matrix (Fin n) (Fin n) O⟦X⟧, ∀ k, W.φD T (b k : W.DD T) =
      ∑ m, (fun i => inc l O (Pm i m k) : LetA O f) • (b m : W.DD T) := by
  have h : ∀ i m k, ∃ z, inc l O z = b.repr ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩ m i := fun i m k =>
    exists_inc W l hI b hb _ (fun δ hδ => by
      change W.γD T δ (W.φD T (b k : W.DD T)) = W.φD T (b k : W.DD T)
      rw [← W.φγ_comm, (hb k).2 δ hδ]) m i
  choose Pm hPm using h
  refine ⟨fun i => Matrix.of (Pm i), fun k => ?_⟩
  refine (coe_eq_sum W b ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩).trans (Finset.sum_congr rfl fun m _ => ?_)
  congr 1
  funext i
  exact (hPm i m k).symm

/- English proof (translation)
Establish `hγ : ∀ k, W.γD T γ (b k : W.DD T) ∈ W.N T` using `fun k => W.N_Γ T γ _ (b k).2`. Establish `h : ∀ i m k, ∃ d : O⟦X⟧, inc l O ((1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k + X * d) = b.repr ⟨W.γD T γ (b k : W.DD T), hγ k⟩ m i`. Introduce `i m k`. Take `⟨z, hz⟩` from `exists_inc W l hI b hb ⟨W.γD T γ (b k : W.DD T), hγ k⟩ (fun δ hδ => by`. Express the relevant statement in the definitionally equal form `W.γD T δ (W.γD T γ (b k : W.DD T)) = W.γD T γ (b k : W.DD T)`.

Rewrite using `[← W.γD_mul, mul_comm, W.γD_mul, (hb k).2 δ hδ]) m i`. Take `⟨y, hy, e⟩` from `W.N_π T γ _ (b k).2`. Establish `e1 : (⟨W.γD T γ (b k : W.DD T), hγ k⟩ : ↥(W.N T)) = b k + (letπ : LetA O f) • (⟨y, hy⟩ : ↥(W.N T))` using `Subtype.ext (eq_add_of_sub_eq' e)`. Establish `e2 : constantCoeff (z - (1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k) = 0`. Rewrite using `[map_sub, ← (pi0Subst_laws_hold l O).2.2.2.2.2.1 z, hz, e1, map_add, map_smul, b.repr_self]`.

Distinguish the cases in `hmk : m = k`. Substitute `hmk` using the available equality. Simplify using `[letπ]`. Simplify using `[letπ, hmk, Finsupp.single_eq_of_ne hmk]`. Take `⟨d, hd⟩` from `X_dvd_iff.2 e2`.

Conclude with `⟨d, by rw [← hd, add_sub_cancel, hz]⟩`. Use `choose Dm hDm using h`. Use `⟨fun i => Matrix.of (Dm i), fun k => ?_⟩` and prove the remaining obligations. Use `(coe_eq_sum W b ⟨W.γD T γ (b k : W.DD T), hγ k⟩).trans (Finset.sum_congr rfl fun m _ => ?_)` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `(hDm i m k).symm`.
-/
theorem exists_gam_matrix (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (γ : W.Gam) :
    ∃ Dm : ZMod f → Matrix (Fin n) (Fin n) O⟦X⟧, ∀ k, W.γD T γ (b k : W.DD T) =
      ∑ m, (fun i => inc l O ((1 + (X : O⟦X⟧) • Dm i) m k) : LetA O f) • (b m : W.DD T) := by
  have hγ : ∀ k, W.γD T γ (b k : W.DD T) ∈ W.N T := fun k => W.N_Γ T γ _ (b k).2
  have h : ∀ i m k, ∃ d : O⟦X⟧, inc l O ((1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k + X * d) =
      b.repr ⟨W.γD T γ (b k : W.DD T), hγ k⟩ m i := by
    intro i m k
    obtain ⟨z, hz⟩ := exists_inc W l hI b hb ⟨W.γD T γ (b k : W.DD T), hγ k⟩ (fun δ hδ => by
      change W.γD T δ (W.γD T γ (b k : W.DD T)) = W.γD T γ (b k : W.DD T)
      rw [← W.γD_mul, mul_comm, W.γD_mul, (hb k).2 δ hδ]) m i
    obtain ⟨y, hy, e⟩ := W.N_π T γ _ (b k).2
    have e1 : (⟨W.γD T γ (b k : W.DD T), hγ k⟩ : ↥(W.N T)) = b k + (letπ : LetA O f) • (⟨y, hy⟩ : ↥(W.N T)) :=
      Subtype.ext (eq_add_of_sub_eq' e)
    have e2 : constantCoeff (z - (1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k) = 0 := by
      rw [map_sub, ← (pi0Subst_laws_hold l O).2.2.2.2.2.1 z, hz, e1, map_add, map_smul, b.repr_self]
      by_cases hmk : m = k
      · subst hmk
        simp [letπ]
      · simp [letπ, hmk, Finsupp.single_eq_of_ne hmk]
    obtain ⟨d, hd⟩ := X_dvd_iff.2 e2
    exact ⟨d, by rw [← hd, add_sub_cancel, hz]⟩
  choose Dm hDm using h
  refine ⟨fun i => Matrix.of (Dm i), fun k => ?_⟩
  refine (coe_eq_sum W b ⟨W.γD T γ (b k : W.DD T), hγ k⟩).trans (Finset.sum_congr rfl fun m _ => ?_)
  congr 1
  funext i
  exact (hDm i m k).symm

/- English proof (translation)
Use `haveI := GlobalTheory.WachLettersCompare.neZero_letters W`. Establish `e : (∑ i, letE i : LetA O f) = 1` using `Finset.univ_sum_single (1 : LetA O f)`. Rewrite using `[← one_smul (LetA O f) x, ← e, Finset.sum_smul]`. Conclude with `Submodule.sum_mem _ fun i _ => h i`.
-/
theorem mem_of_letters (x : W.DD T) (h : ∀ i, (letE i : LetA O f) • x ∈ W.N T) : x ∈ W.N T := by
  haveI := GlobalTheory.WachLettersCompare.neZero_letters W
  have e : (∑ i, letE i : LetA O f) = 1 := Finset.univ_sum_single (1 : LetA O f)
  rw [← one_smul (LetA O f) x, ← e, Finset.sum_smul]
  exact Submodule.sum_mem _ fun i _ => h i

/- English proof (translation)
Introduce `x hx`. Use `mem_of_letters W _ fun i => ?_` and prove the remaining obligations. Use `(hH T U (fun _ => 0) (fun i => ((U i).map Int.toNat).sum) hU (fun i u hu => ?_) i).1 x hx` as an intermediate fact. Simplify using `using this`. Use `⟨by simpa using hpos i u hu, ?_⟩` and prove the remaining obligations.

Establish `h1 : u.toNat ≤ ((U i).map Int.toNat).sum` using `Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hu)`. Conclude with `(Int.self_le_toNat u).trans (by exact_mod_cast h1)`.
-/
theorem phi_mem (hH : GlobalTheory.WachUse.Heights W) (U : ZMod f → Multiset ℤ)
    (hU : GlobalTheory.AdmLoc.CrysWith PD W.emb T.ρ U) (hpos : ∀ i, ∀ u ∈ U i, 0 ≤ u) :
    ∀ x ∈ W.N T, W.φD T x ∈ W.N T := by
  intro x hx
  refine mem_of_letters W _ fun i => ?_
  have := (hH T U (fun _ => 0) (fun i => ((U i).map Int.toNat).sum) hU (fun i u hu => ?_) i).1 x hx
  · simpa using this
  · refine ⟨by simpa using hpos i u hu, ?_⟩
    have h1 : u.toNat ≤ ((U i).map Int.toNat).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hu)
    exact (Int.self_le_toNat u).trans (by exact_mod_cast h1)

end Generic

/- English proof (translation)
Take `⟨_, hc, hl⟩` from `GlobalTheory.FinExtIntegers.dvr_complete LL`. Take `⟨g₁, a, e⟩` from `(linear_division_holds ↥(OL LL) (maximalIdeal ↥(OL LL)) (l : ↥(OL LL)) ((mem_maximalIdeal _).2 hl)).1 g`. Conclude with `⟨a, g₁, by rw [e, add_sub_cancel_right]⟩`.
-/
theorem exists_rem {l : ℕ} [Fact l.Prime] (LL : FinExt l) (g : (↥(OL LL))⟦X⟧) :
    ∃ a : ↥(OL LL), (X - C (l : ↥(OL LL))) ∣ g - C a := by
  obtain ⟨_, hc, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨g₁, a, e⟩ := (linear_division_holds ↥(OL LL) (maximalIdeal ↥(OL LL)) (l : ↥(OL LL))
    ((mem_maximalIdeal _).2 hl)).1 g
  exact ⟨a, g₁, by rw [e, add_sub_cancel_right]⟩

/- English proof (translation)
Introduce `D HW F Cm l _ K LL hA T U n hU hpos hn γ`. Establish `hR` using `GlobalTheory.T.wachRingFacts_unramified_levelOne (HW l) K LL hA`. Establish `hJ` using `(GlobalTheory.HeightsClauseCompare.heights_iff D HW F Cm).2 ⟨GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm, GlobalTheory.NL.SandJumps.main D HW F Cm⟩`. Establish `hH` using `GlobalTheory.WachUse.HeightsProof.heights_of_caseA (D.locA l) (HW l) (F l) (Cm l) ⟨D.locT l⟩ ((GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff l _ _ _ _ _).2 (hJ l)) K LL hA`. Take `⟨b₀⟩` from `GlobalTheory.WachFree.wach_free (D.loc l) (HW l) K 1 LL hA.2.2 T hU.1`.

Take `⟨b, hb⟩` from `GlobalTheory.WachTie.exists_invariant_basis _ T hR.2.2.2.2.2 ⟨b₀.reindex (finCongr hn)⟩`. Take `⟨Pm, hP⟩` from `exists_phi_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb (phi_mem _ hH U hU hpos)`. Take `⟨Dm, hD⟩` from `exists_gam_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb γ`. Use `choose Th hTh using fun i a c => exists_rem LL (Dm i a c)`. Conclude with `⟨b, ⟨Pm, Dm, fun i => Matrix.of (Th i)⟩, hb, hP, hD, hTh⟩`.
-/
theorem exists_frame : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n : ℕ), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u) → Module.finrank ↥(OL LL) ↥T.L.T = n → ∀ γ : ((HW l).W K 1 LL hA.2.2).Gam, ∃ (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N := by
  intro D HW F Cm l _ K LL hA T U n hU hpos hn γ
  have hR := GlobalTheory.T.wachRingFacts_unramified_levelOne (HW l) K LL hA
  have hJ := (GlobalTheory.HeightsClauseCompare.heights_iff D HW F Cm).2
    ⟨GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm, GlobalTheory.NL.SandJumps.main D HW F Cm⟩
  have hH := GlobalTheory.WachUse.HeightsProof.heights_of_caseA (D.locA l) (HW l) (F l) (Cm l) ⟨D.locT l⟩
    ((GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff l _ _ _ _ _).2 (hJ l)) K LL hA
  obtain ⟨b₀⟩ := GlobalTheory.WachFree.wach_free (D.loc l) (HW l) K 1 LL hA.2.2 T hU.1
  obtain ⟨b, hb⟩ := GlobalTheory.WachTie.exists_invariant_basis _ T hR.2.2.2.2.2 ⟨b₀.reindex (finCongr hn)⟩
  obtain ⟨Pm, hP⟩ := exists_phi_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb (phi_mem _ hH U hU hpos)
  obtain ⟨Dm, hD⟩ := exists_gam_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb γ
  choose Th hTh using fun i a c => exists_rem LL (Dm i a c)
  exact ⟨b, ⟨Pm, Dm, fun i => Matrix.of (Th i)⟩, hb, hP, hD, hTh⟩

end GlobalTheory.WachFrame

end
