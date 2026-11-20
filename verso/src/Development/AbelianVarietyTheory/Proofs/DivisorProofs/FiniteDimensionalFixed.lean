import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicities
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenSubgroupFiniteSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AdmissibleSmoothRepresentations

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.CuspMult GlobalTheory.PRep
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDec

section Abstract

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [TopologicalSpace H] [IsTopologicalGroup H] in
/- English proof (translation)
Simplify using `[fixed, eig]`.
-/
theorem mem_fixed {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ H X} {K : Subgroup H} {x : X} :
    x ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k x = x := by
  simp [fixed, eig]

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ρ : Representation ℂ H V}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.isSemisimple ha hu ho hc`.
-/
theorem isSemisimple (ha : IsAdmissible ρ) (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) {K₀ : Subgroup H}
    (ho : IsOpen (K₀ : Set H)) (hc : IsCompact (K₀ : Set H)) : ρ.IsSemisimpleRepresentation :=
  _root_.UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.isSemisimple ha hu ho hc

/- English proof (translation)
Use `haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 h1`. Establish `hs : σ.asModuleEquiv.symm s ∈ sSup {m : Submodule (MonoidAlgebra ℂ H) σ.asModule | IsSimpleModule (MonoidAlgebra ℂ H) m}`. Rewrite using `[IsSemisimpleModule.sSup_simples_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `hs` using `[sSup_eq_iSup']`.

Use `Submodule.iSup_induction _ (motive := fun x => f (σ.asModuleEquiv x) ∈ irrSum ρ C) hs ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨m, hm⟩ y hy`. Take `⟨U, rfl⟩` from `Subrepresentation.subrepresentationSubmoduleOrderIso.surjective m`. Establish `hU : U.toRepresentation.IsIrreducible`. Rewrite using `[Representation.irreducible_iff_isSimpleModule_asModule]`.

Use `haveI : IsSimpleModule (MonoidAlgebra ℂ H) U.asSubmodule := hm`. Conclude with `IsSimpleModule.congr (GlobalTheory.RepCount.subEquiv U)`. Conclude with `GlobalTheory.RepCount.apply_mem_irrSum hU (GlobalTheory.RepCount.isAdmissible_of_injective U.toSubmodule.subtype (fun _ _ => rfl) Subtype.val_injective h2) (f := f.comp U.toSubmodule.subtype) ⟨fun s => hf.1 _, fun g s => hf.2 g s⟩ ⟨σ.asModuleEquiv y, hy⟩`. Simplify using the standard rewrite rules. Introduce `a b ha hb`.

Rewrite using `[map_add, map_add]`. Conclude with `Submodule.add_mem _ ha hb`.
-/
theorem mem_irrSum {W X : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ H W}
    {ρ : Representation ℂ H X} {C : Submodule ℂ X} (h1 : σ.IsSemisimpleRepresentation) (h2 : IsAdmissible σ)
    {f : W →ₗ[ℂ] X} (hf : f ∈ homInto σ ρ C) (s : W) : f s ∈ irrSum ρ C := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 h1
  have hs : σ.asModuleEquiv.symm s ∈ sSup {m : Submodule (MonoidAlgebra ℂ H) σ.asModule |
      IsSimpleModule (MonoidAlgebra ℂ H) m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]
    trivial
  rw [sSup_eq_iSup'] at hs
  refine Submodule.iSup_induction _ (motive := fun x => f (σ.asModuleEquiv x) ∈ irrSum ρ C) hs ?_ ?_ ?_
  · rintro ⟨m, hm⟩ y hy
    obtain ⟨U, rfl⟩ := Subrepresentation.subrepresentationSubmoduleOrderIso.surjective m
    have hU : U.toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      haveI : IsSimpleModule (MonoidAlgebra ℂ H) U.asSubmodule := hm
      exact IsSimpleModule.congr (GlobalTheory.RepCount.subEquiv U)
    exact GlobalTheory.RepCount.apply_mem_irrSum hU
      (GlobalTheory.RepCount.isAdmissible_of_injective U.toSubmodule.subtype (fun _ _ => rfl) Subtype.val_injective h2)
      (f := f.comp U.toSubmodule.subtype) ⟨fun s => hf.1 _, fun g s => hf.2 g s⟩ ⟨σ.asModuleEquiv y, hy⟩
  · simp
  · intro a b ha hb
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb

/- English proof (translation)
Introduce `x hx hx'`. Set `A : Subrepresentation ρ` to `⟨C ⊓ smoothPart ρ, fun g v hv => ⟨hC g v hv.1, smoothPart_stable ρ g v hv.2⟩⟩`. Establish `hsym : ∀ x ∈ C, ∀ y ∈ C, B y x = star (B x y)` using `fun x hx y hy => (hl x hx y hy y hy 0).2`. Establish `h0 : ∀ x ∈ C, B x 0 = 0` using `fun x hx => by simpa using (hl x hx 0 C.zero_mem 0 C.zero_mem 1).1`. Set `cd : InnerProductSpace.Core ℂ A.toSubmodule` to `{ inner := fun a b => B a b conj_inner_symm := fun a b => (hsym _ b.2.1 _ a.2.1).symm re_inner_nonneg := fun a => by`.

Distinguish the cases in `h : (a : X) = 0`. Simplify using `[h, h0 0 C.zero_mem]`. Conclude with `(hp _ a.2.1 h).le`. Use `add_left := fun a b c => by`. Use `(hl _ c.2.1 _ a.2.1 _ b.2.1 1).1` as an intermediate fact.

Rewrite `this` using `[one_smul, one_mul]`. Use `show B (a + b) c = B a c + B b c`. Rewrite using `[hsym _ c.2.1 _ (C.add_mem a.2.1 b.2.1), this, star_add, hsym _ c.2.1 _ a.2.1, hsym _ c.2.1 _ b.2.1]`. Use `smul_left := fun a b r => by`. Use `(hl _ b.2.1 _ C.zero_mem _ a.2.1 r).1` as an intermediate fact.

Rewrite `this` using `[zero_add, h0 _ b.2.1, zero_add]`. Use `show B (r • a) b = star r * B a b`. Rewrite using `[hsym _ b.2.1 _ (C.smul_mem r a.2.1), this, star_mul', hsym _ b.2.1 _ a.2.1]`. Use `definite := fun a h => by`. Assume the negation of the conclusion as `hn`.

Use `hp _ a.2.1 fun e => hn (Subtype.ext e)` as an intermediate fact. Rewrite `this` using `[show B a a = 0 from h]`. Simplify using `at this }`. Establish `ha : IsAdmissible A.toRepresentation`. Use `⟨fun v => ?_, fun K hK _ => ?_⟩` and prove the remaining obligations.

Establish `: {g : H | A.toRepresentation g v = v} = {g : H | ρ g v = v}`. Use extensionality with `g`. Conclude with `Subtype.ext_iff`. Rewrite using `[this]`. Conclude with `v.2.2`.

Use `haveI := hf K hK`. Use `FiniteDimensional.of_injective (A.toSubmodule.subtype.restrict (p := fixed A.toRepresentation K) (q := C ⊓ fixed ρ K) fun v hv => ⟨v.2.1, fun k => congrArg Subtype.val (hv k)⟩) fun a b h => ?_` and prove the remaining obligations. Establish `h' : (a.1 : X) = b.1` using `congrArg (fun z : ↥(C ⊓ fixed ρ K) => (z : X)) h`. Conclude with `Subtype.ext (Subtype.ext h')`. Establish `hs : A.toRepresentation.IsSemisimpleRepresentation`.

Use `letI := cd.toNormedAddCommGroup`. Use `letI := InnerProductSpace.ofCore cd.toCore`. Conclude with `isSemisimple ha (fun g a b => hi g _ a.2.1 _ b.2.1) ho hc`. Conclude with `mem_irrSum hs ha (f := A.toSubmodule.subtype) ⟨fun s => s.2.1, fun _ _ => rfl⟩ ⟨x, hx, hx'⟩`.
-/
theorem isDecomp_of_form {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (hC : ∀ g, ∀ x ∈ C, ρ g x ∈ C) (B : X → X → ℂ)
    (hl : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z ∧ B y x = star (B x y))
    (hp : ∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) (hi : ∀ g, ∀ x ∈ C, ∀ y ∈ C, B (ρ g x) (ρ g y) = B x y)
    (hf : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ ↥(C ⊓ fixed ρ K))
    {K₀ : Subgroup H} (ho : IsOpen (K₀ : Set H)) (hc : IsCompact (K₀ : Set H)) : IsDecomp ρ C := by
  intro x hx hx'
  let A : Subrepresentation ρ := ⟨C ⊓ smoothPart ρ, fun g v hv => ⟨hC g v hv.1, smoothPart_stable ρ g v hv.2⟩⟩
  have hsym : ∀ x ∈ C, ∀ y ∈ C, B y x = star (B x y) := fun x hx y hy => (hl x hx y hy y hy 0).2
  have h0 : ∀ x ∈ C, B x 0 = 0 := fun x hx => by simpa using (hl x hx 0 C.zero_mem 0 C.zero_mem 1).1
  let cd : InnerProductSpace.Core ℂ A.toSubmodule :=
    { inner := fun a b => B a b
      conj_inner_symm := fun a b => (hsym _ b.2.1 _ a.2.1).symm
      re_inner_nonneg := fun a => by
        by_cases h : (a : X) = 0
        · simp [h, h0 0 C.zero_mem]
        · exact (hp _ a.2.1 h).le
      add_left := fun a b c => by
        have := (hl _ c.2.1 _ a.2.1 _ b.2.1 1).1
        rw [one_smul, one_mul] at this
        show B (a + b) c = B a c + B b c
        rw [hsym _ c.2.1 _ (C.add_mem a.2.1 b.2.1), this, star_add, hsym _ c.2.1 _ a.2.1, hsym _ c.2.1 _ b.2.1]
      smul_left := fun a b r => by
        have := (hl _ b.2.1 _ C.zero_mem _ a.2.1 r).1
        rw [zero_add, h0 _ b.2.1, zero_add] at this
        show B (r • a) b = star r * B a b
        rw [hsym _ b.2.1 _ (C.smul_mem r a.2.1), this, star_mul', hsym _ b.2.1 _ a.2.1]
      definite := fun a h => by
        by_contra hn
        have := hp _ a.2.1 fun e => hn (Subtype.ext e)
        rw [show B a a = 0 from h] at this
        simp at this }
  have ha : IsAdmissible A.toRepresentation := by
    refine ⟨fun v => ?_, fun K hK _ => ?_⟩
    · have : {g : H | A.toRepresentation g v = v} = {g : H | ρ g v = v} := by
        ext g
        exact Subtype.ext_iff
      rw [this]
      exact v.2.2
    · haveI := hf K hK
      refine FiniteDimensional.of_injective (A.toSubmodule.subtype.restrict (p := fixed A.toRepresentation K)
        (q := C ⊓ fixed ρ K) fun v hv => ⟨v.2.1, fun k => congrArg Subtype.val (hv k)⟩) fun a b h => ?_
      have h' : (a.1 : X) = b.1 := congrArg (fun z : ↥(C ⊓ fixed ρ K) => (z : X)) h
      exact Subtype.ext (Subtype.ext h')
  have hs : A.toRepresentation.IsSemisimpleRepresentation := by
    letI := cd.toNormedAddCommGroup
    letI := InnerProductSpace.ofCore cd.toCore
    exact isSemisimple ha (fun g a b => hi g _ a.2.1 _ b.2.1) ho hc
  exact mem_irrSum hs ha (f := A.toSubmodule.subtype) ⟨fun s => s.2.1, fun _ _ => rfl⟩ ⟨x, hx, hx'⟩

end Abstract

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : DSModel V S}

/- English proof (translation)
Establish `e : finRep M g T = heckeOn M {(g : GA D V)} T`. Use extensionality with `v x`. Simplify using `[heckeOn, postOn_apply, heckeLin_apply, finRep_apply]`. Rewrite using `[e]`. Conclude with `Submodule.subset_span (GlobalTheory.SphericalOps.isMultMap_single ((GlobalTheory.MultMem.mem_mult_iff ..).1 hT) g.2)`.
-/
theorem finRep_mem (g : GfC V) (T : MMap M) (hT : T ∈ allMaps θ M) : finRep M g T ∈ allMaps θ M := by
  have e : finRep M g T = heckeOn M {(g : GA D V)} T := by
    ext v x
    simp [heckeOn, postOn_apply, heckeLin_apply, finRep_apply]
  rw [e]
  exact Submodule.subset_span (GlobalTheory.SphericalOps.isMultMap_single ((GlobalTheory.MultMem.mem_mult_iff ..).1 hT) g.2)

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram` as an intermediate fact. Establish `: Countable (GQ V)` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram`. Use `GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ` as an intermediate fact. Introduce `v v'`. Use `GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (T v x) * T' v' x) g hF fun γ hγ x => by` as an intermediate fact.

Rewrite using `[(GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T hT v).2 γ hγ, (GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T' hT' v').2 γ hγ]`. Conclude with `⟨this.1.1 (h v v').1, this.2.trans (h v v').2⟩`.
-/
theorem isMultiplicityInner_finRep {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (g : GfC V) {T T' : MMap M} (hT : T ∈ allMaps θ M) (hT' : T' ∈ allMaps θ M)
    {c : ℂ} (h : IsMultIP M μ 𝓕 T T' c) : IsMultIP M μ 𝓕 (finRep M g T) (finRep M g T') c := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  intro v v'
  have := GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (T v x) * T' v' x) g hF fun γ hγ x => by
    rw [(GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T hT v).2 γ hγ, (GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T' hT' v').2 γ hγ]
  exact ⟨this.1.1 (h v v').1, this.2.trans (h v v').2⟩

/- English proof (translation)
Take `⟨N, hN, e⟩` from `isOpen_induced_iff.1 hK`. Establish `hmem : ∀ k : GfC V, (k : GA D V) ∈ N ↔ k ∈ K` using `fun k => Set.ext_iff.1 e k`. Take `⟨U, hU, hUN⟩` from `GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N (hN.mem_nhds ((hmem 1).2 K.one_mem))`. Use `haveI := GlobalTheory.MultFinite.hcFinite (M := M) (J := N ∩ GfC V) (χ := fun _ => 1) hP hθ ⟨U, hU, fun k hk hf => ⟨⟨hUN k hk hf, hf⟩, rfl⟩⟩`. Use `Submodule.finiteDimensional_of_le (S₂ := Mult θ M (N ∩ GfC V) fun _ => 1) fun T hT => Submodule.subset_span ?_` and prove the remaining obligations.

Establish `h` using `(GlobalTheory.MultMem.mem_mult_iff ..).1 hT.1`. Use `⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩` and prove the remaining obligations. Use `congrArg (fun T : MMap M => T v g) (mem_fixed.1 hT.2 ⟨k, hk.2⟩ ((hmem ⟨k, hk.2⟩).1 hk.1))` as an intermediate fact. Rewrite using `[one_mul]`. Conclude with `this`.
-/
theorem finiteDimensional_fixed (hP : GlobalTheory.Published.HarishChandraFinite) (hθ : IsInfFam θ) (K : Subgroup (GfC V))
    (hK : IsOpen (K : Set (GfC V))) : FiniteDimensional ℂ ↥(allMaps θ M ⊓ fixed (finRep M) K) := by
  obtain ⟨N, hN, e⟩ := isOpen_induced_iff.1 hK
  have hmem : ∀ k : GfC V, (k : GA D V) ∈ N ↔ k ∈ K := fun k => Set.ext_iff.1 e k
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N (hN.mem_nhds ((hmem 1).2 K.one_mem))
  haveI := GlobalTheory.MultFinite.hcFinite (M := M) (J := N ∩ GfC V) (χ := fun _ => 1) hP hθ
    ⟨U, hU, fun k hk hf => ⟨⟨hUN k hk hf, hf⟩, rfl⟩⟩
  refine Submodule.finiteDimensional_of_le (S₂ := Mult θ M (N ∩ GfC V) fun _ => 1) fun T hT => Submodule.subset_span ?_
  have h := (GlobalTheory.MultMem.mem_mult_iff ..).1 hT.1
  refine ⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩
  have := congrArg (fun T : MMap M => T v g) (mem_fixed.1 hT.2 ⟨k, hk.2⟩ ((hmem ⟨k, hk.2⟩).1 hk.1))
  rw [one_mul]
  exact this

/- English proof (translation)
Take `⟨_, _, -⟩` from `GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V`. Take `⟨N, hN, h1⟩` from `exists_compact_mem_nhds (1 : GA D V)`. Take `⟨U, hU, hUN⟩` from `GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N h1`. Use `⟨U.subgroupOf (GfC V), hU.preimage continuous_subtype_val, ?_⟩` and prove the remaining obligations. Use `((GlobalTheory.Ker.CongTop.isClosed_GfC V).isClosedEmbedding_subtypeVal.isCompact_preimage hN).of_isClosed_subset ((U.isClosed_of_isOpen hU).preimage continuous_subtype_val) fun k hk => hUN k hk k.2` and prove the remaining obligations.
-/
theorem exists_compact_open (V : HSp D) : ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) := by
  obtain ⟨_, _, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  obtain ⟨N, hN, h1⟩ := exists_compact_mem_nhds (1 : GA D V)
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N h1
  refine ⟨U.subgroupOf (GfC V), hU.preimage continuous_subtype_val, ?_⟩
  refine ((GlobalTheory.Ker.CongTop.isClosed_GfC V).isClosedEmbedding_subtypeVal.isCompact_preimage hN).of_isClosed_subset
    ((U.isClosed_of_isOpen hU).preimage continuous_subtype_val) fun k hk => hUN k hk k.2

/- English proof (translation)
Introduce `hP hQ D θ hθ V S M`. Take `⟨_, _, _, _, _, -⟩` from `GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V`. Establish `hμ : (Measure.haar : Measure (GA D V)).IsHaarMeasure` using `inferInstance`. Take `⟨𝓕, hF⟩` from `(GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V _ hμ).2`. Establish `hS : SchurMult θ M ∅ (fun _ => 1) _ 𝓕` using `GlobalTheory.MultFinite.schurMult hQ Measure.haar 𝓕`.

Take `⟨h1, h2⟩` from `GlobalTheory.SchurConst.ipM_posDef D θ V S M _ _ _ 𝓕 hθ hμ hF hS (GlobalTheory.GardingVec.sm_ne_bot D V S M)`. Take `⟨v, hv⟩` from `GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D V S M)`. Take `⟨K, ho, hc⟩` from `exists_compact_open V`. Use `isDecomp_of_form (finRep M) _ finRep_mem (ipM M Measure.haar 𝓕) h1 h2 (fun g T hT T' hT' => ?_) (finiteDimensional_fixed hP hθ) ho hc` and prove the remaining obligations. Establish `h` using `isMultiplicityInner_finRep hμ hF g hT hT' (ipM_spec M _ 𝓕 T T' (hS hθ hμ hF T hT T' hT'))`.

Conclude with `hasPeterssonInner_unique M _ 𝓕 _ _ v hv (ipM_spec M _ 𝓕 _ _ ⟨_, h⟩) h`.
-/
theorem cuspDecomp : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, CuspDecomp D := by
  intro hP hQ D θ hθ V S M
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  have hμ : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
  obtain ⟨𝓕, hF⟩ := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V _ hμ).2
  have hS : SchurMult θ M ∅ (fun _ => 1) _ 𝓕 := GlobalTheory.MultFinite.schurMult hQ Measure.haar 𝓕
  obtain ⟨h1, h2⟩ := GlobalTheory.SchurConst.ipM_posDef D θ V S M _ _ _ 𝓕 hθ hμ hF hS (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  obtain ⟨K, ho, hc⟩ := exists_compact_open V
  refine isDecomp_of_form (finRep M) _ finRep_mem (ipM M Measure.haar 𝓕) h1 h2 (fun g T hT T' hT' => ?_)
    (finiteDimensional_fixed hP hθ) ho hc
  have h := isMultiplicityInner_finRep hμ hF g hT hT' (ipM_spec M _ 𝓕 T T' (hS hθ hμ hF T hT T' hT'))
  exact hasPeterssonInner_unique M _ 𝓕 _ _ v hv (ipM_spec M _ 𝓕 _ _ ⟨_, h⟩) h

end GlobalTheory.CuspDec

end
