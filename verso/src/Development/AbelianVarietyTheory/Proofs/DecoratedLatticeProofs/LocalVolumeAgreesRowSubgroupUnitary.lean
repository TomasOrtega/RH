import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemN1IffLocalHomStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemR1IffLocalHomStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLocalizedStdLatticeIffIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsN1LocalHomMemOpenStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsColSpaceAutToLocalGLMemOpenDenseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarVolumeRatioCompactEqRelIndexRatioStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarOpenSubgroupVolumeInvEqRelIndexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicConjInfIntegralGLUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicProjectionToGLStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMirabolicProjectionIffColSpaceAutToLocalGLStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexComapEqOfCosetsHit

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.VolBridge

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit`. Consider the case `exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit`. Consider the case `(apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)`.
-/
theorem index_comap_of_dense_image {A B : Type} [Group A] [Group B] (f : A →* B) (H : Subgroup B)
    (hf : ∀ b, ∃ a, (f a)⁻¹ * b ∈ H) : (H.comap f).index = H.index := by
  first
  | exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | (apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)

/- English proof (translation)
Set `f : U.comap φ →* U` to `φ.subgroupComap U`. Establish `hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f`. Use extensionality with `x`. Conclude with `Iff.rfl`. Establish `key` using `index_comap_of_dense_image f (K.subgroupOf U) (by`.

Introduce and unpack `⟨b, hb⟩`. Take `⟨γ, hγK, hγU⟩` from `h b hb`. Establish `hγ : φ γ ∈ U`. Use `U.mul_mem hb (U.inv_mem hγU)` as an intermediate fact. Simplify using `using this`.

Use `⟨⟨γ, hγ⟩, ?_⟩` and prove the remaining obligations. Conclude with `hγK)`. Simplify using `only [Subgroup.relIndex]`. Rewrite using `[hc, key]`.
-/
theorem relIndex_comap_of_dense_image {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G)
    (K U : Subgroup G) (h : ∀ g ∈ U, ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) :
    (K.comap φ).relIndex (U.comap φ) = K.relIndex U := by
  let f : U.comap φ →* U := φ.subgroupComap U
  have hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f := by
    ext x
    exact Iff.rfl
  have key := index_comap_of_dense_image f (K.subgroupOf U) (by
    rintro ⟨b, hb⟩
    obtain ⟨γ, hγK, hγU⟩ := h b hb
    have hγ : φ γ ∈ U := by
      have := U.mul_mem hb (U.inv_mem hγU)
      simpa using this
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact hγK)
  simp only [Subgroup.relIndex]
  rw [hc, key]

/- English proof (translation)
Introduce `X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hok hat`. Establish `hLev` using `GlobalTheory.T.parahoricLevels_characters_doubleCosets_agree_rational X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat`. Use `haveI : ν.IsAddHaarMeasure := hν.1`. Introduce `j c h γ g hg`. Take `⟨e, he, hge⟩` from `hg`.

Establish `hcc : cOf R j = c + 1` using `by unfold cOf; have := hat.steps; omega`. Establish `heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val` using `fun i => he (Sum.inr i)`. Establish `hgφ : g = GlobalTheory.VolBridge.locHom ι e γ` using `Units.ext hge`. Establish `hreg : (W.T s R).Regular` using `Chain.ofTwist_regular _ _ _ _ _`. Take `⟨hJo, hJc, -⟩` from `hreg.2.2 j (c + 1) h`.

Use `set J := ((W.T s R).lev j (c + 1) h).J with hJdef`. Use `set φ := GlobalTheory.VolBridge.locHom ι e with hφ`. Establish `hcompl` using `hat.compl`. Establish `hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g)`. Introduce `x`.

Use `⟨e, he, ?_⟩` and prove the remaining obligations. Rewrite using `[hgφ, ← map_inv, ← map_mul, ← map_mul]`. Both sides reduce to the same expression. Establish `hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr` using `Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by`. Introduce `x`.

Rewrite using `[mem_Cgrp, ← GlobalTheory.T.mem_R1_iff_local_hom ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]`. Simplify using `[Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]`. Establish `hN1` using `GlobalTheory.T.mem_N1_iff_locHom_mem_N_one ι e hcc heR`. Establish `hlam : lamYat (Pr` using `Pr) (R := R) j P.1 = stdAt X.E _ P.1 := by`. Use extensionality with `v`.

Simplify using `only [lamYat, if_neg hat.nmem, LocE.lamY, LocE.sclLat, Submodule.mem_comap]`. Use `congr! 1`. Use function extensionality and compare the values at `l`. Simplify using `[LocE.scE]`. Establish `hKO : ∀ x : AutY X R j, x ∈ stabL X.E _ (lamYat (Pr` using `Pr) (R := R) j P.1) ↔ φ x ∈ KO k _ := by`.

Introduce `x`. Rewrite using `[hlam]`. Conclude with `GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e x`. Establish `hdN` using `GlobalTheory.T.exists_N1_locHom_mem_open ι hcompl.dense e hcc heR`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hH` using `GlobalTheory.RootEx.VolN.volN_haar_and_modulus k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 le_rfl (by omega) ν`. Use `haveI := hH.2.2.1`. Take `⟨ho, hAc, hBc⟩` from `GlobalTheory.T.isOpen_mirabolicConj_inf_integralGL_unipotent J g hJo hJc`. Establish `hst : stabLat (1 : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k) = KO k _`. Use extensionality with `z`.

Simplify using `[stabLat, Subgroup.mem_comap]`. Establish `hvol : volNat ν 1 (Cgrp J g) = (volN ν _ (c + 1) 1 ((Cgrp J g).subgroupOf (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) : Set (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1))).toReal / (volN ν _ (c + 1) 1 ((KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1))).subgroupOf (N k (XIx (Fin R.k) …`. Rewrite using `[volNat, hst]`. Rewrite using `[hvol, GlobalTheory.T.haar_volume_ratio_compact_eq_relIndex_ratio _ _ _ ho hAc hBc]`. Use `set K := Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hKdef`.

Use `set U := KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hUdef`. Establish `hA : (Cgrp J g).subgroupOf (N k _ (c + 1) 1) = K.subgroupOf (N k _ (c + 1) 1)` using `(Subgroup.inf_subgroupOf_right _ _).symm`. Establish `hB : (KO k _).subgroupOf (N k _ (c + 1) 1) = U.subgroupOf (N k _ (c + 1) 1)` using `(Subgroup.inf_subgroupOf_right _ _).symm`. Rewrite using `[hA, hB, Subgroup.relIndex_subgroupOf inf_le_right, Subgroup.relIndex_subgroupOf inf_le_right]`. Establish `hKc : K.comap φ = Loc.Cbe (Jat (Pr` using `Pr) cst.sharp j P.1) γ ⊓ Loc.N1 X.E (R.N j) (cOf R j) := by`.

Use extensionality with `x`. Use `show φ x ∈ Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _`. Rewrite using `[Subgroup.mem_inf, Subgroup.mem_inf, hC, hN1]`. Establish `hUc : U.comap φ = Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr` using `Pr) (R := R) j P.1) := by`. Use extensionality with `x`.

Use `show φ x ∈ KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _`. Rewrite using `[Subgroup.mem_inf, Subgroup.mem_inf, hKO, hN1]`. Conclude with `And.comm`. Establish `hden : ∀ z, z ∈ K ∨ z ∈ U → ∃ x, (φ x)⁻¹ * z ∈ K ⊓ U`. Introduce `z hz`.

Establish `hzN : z ∈ N k _ (c + 1) 1` using `by rcases hz with hz | hz; exacts [hz.2, hz.2]`. Establish `hO1 : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J}` using `hJo.preimage (by fun_prop)`. Establish `hO'` using `hO1.inter (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)))`. Establish `hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | v⁻¹ * z ∈ ({w | g⁻¹ * w * g ∈ J} ∩ (KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) : Set (GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)))}` using `hO'.preimage (by fun_prop)`. Take `⟨x, hx, hxV⟩` from `hdN z hzN _ hV (by simp [J.one_mem, one_mem])`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `hxN` using `(hN1 x).1 hx`. Establish `hm : (φ x)⁻¹ * z ∈ N k _ (c + 1) 1` using `mul_mem (inv_mem hxN) hzN`. Establish `hmR : (φ x)⁻¹ * z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1` using `by unfold GlobalTheory.RootEx.R; exact Subgroup.mem_sup_right hm`. Conclude with `⟨⟨mem_Cgrp.2 ⟨hmR, hxV.1⟩, hm⟩, hxV.2, hm⟩`.

Establish `h1` using `GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ K U (fun z hz => hden z (Or.inr hz))`. Establish `h2` using `GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ U K (fun z hz => by`. Take `⟨x, hx⟩` from `hden z (Or.inl hz); exact ⟨x, by rwa [inf_comm]⟩)`. Rewrite `h1`, `h2` using `[hKc, hUc]`. Rewrite using `[← h1, ← h2]`.

Simplify using `[Loc.volN, map_div₀, map_natCast]`. Introduce `hle m hm hm1 haveI := hm set e' := GlobalTheory.VolBridge.eX e hcc heR with he' set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'`. Establish `hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J}` using `hJo.preimage (by fun_prop)`. Establish `hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1, z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J}` using `fun z hz => by`. Simplify using `[mem_Cgrp, hz]`.

Establish `hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1` using `fun z hz => (mem_Cgrp.1 hz).1`. Establish `hP : ∀ y, y ∈ prCat (Pr` using `Pr) cst.sharp j P.1 γ ↔ φ' y ∈ prX (Cgrp J g) := GlobalTheory.T.mem_mirabolicProjection_iff_colSpaceAutToLocalGL ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC`. Establish `hG : ∀ y, y ∈ GLint X.E (R.N j) P.1 ↔ φ' y ∈ KO k _` using `fun y => GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e' y`. Establish `hpo : IsOpen (prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k))` using `GlobalTheory.T.isOpen_mirabolicProjectionToGL _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)`. Establish `hden : ∀ z, z ∈ prX (Cgrp J g) ∨ z ∈ KO k _ → ∃ y, (φ' y)⁻¹ * z ∈ prX (Cgrp J g) ⊓ KO k _`.

Introduce `z _`. Establish `hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k | v⁻¹ * z ∈ ((prX (Cgrp J g) ⊓ KO k _ : Subgroup _) : Set _)}` using `(hpo.inter GlobalTheory.SplitFlip.isOpen_KO).preimage (by fun_prop)`. Take `⟨y, hy⟩` from `GlobalTheory.T.exists_colSpaceAutToLocalGL_mem_open_dense ι hcompl.dense e' z _ hV (by simp [one_mem])`. Conclude with `⟨y, hy⟩`. Establish `hle' : prX (Cgrp J g) ≤ KO k _`.

Introduce `z hz`. Take `⟨y, hy1, hy2⟩` from `hden z (Or.inl hz)`. Establish `hyC : φ' y ∈ prX (Cgrp J g)`. Use `mul_mem hz (inv_mem hy1)` as an intermediate fact. Simplify using `using this`.

Establish `hyK : φ' y ∈ KO k _` using `(hG y).1 (hle ((hP y).2 hyC))`. Use `mul_mem hyK hy2` as an intermediate fact. Simplify using `using this`. Establish `hidx` using `GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ' (prX (Cgrp J g)) (KO k _) (fun z hz => hden z (Or.inr hz))`. Establish `hc1 : (prX (Cgrp J g)).comap φ' = prCat (Pr` using `Pr) cst.sharp j P.1 γ := by ext y; exact (hP y).symm`.

Establish `hc2 : (KO k _).comap φ' = GLint X.E (R.N j) P.1` using `by ext y; exact (hG y).symm`. Rewrite `hidx` using `[hc1, hc2]`. Rewrite using `[hidx]`. Conclude with `GlobalTheory.T.haar_open_subgroup_volume_inv_eq_relIndex m _ _ hle' hpo GlobalTheory.SplitFlip.isCompact_KO hm1`.
-/
theorem vol_agree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → VolAgree (R := R) sel mu cst σ₀ P ι s W ν := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hok hat
  have hLev := GlobalTheory.T.parahoricLevels_characters_doubleCosets_agree_rational X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hat
  haveI : ν.IsAddHaarMeasure := hν.1
  intro j c h γ g hg
  obtain ⟨e, he, hge⟩ := hg
  have hcc : cOf R j = c + 1 := by unfold cOf; have := hat.steps; omega
  have heR : ∀ i : Fin (c + 1), (e (Sum.inr i)).val = R.N j + i.val := fun i => he (Sum.inr i)
  have hgφ : g = GlobalTheory.VolBridge.locHom ι e γ := Units.ext hge
  have hreg : (W.T s R).Regular := Chain.ofTwist_regular _ _ _ _ _
  obtain ⟨hJo, hJc, -⟩ := hreg.2.2 j (c + 1) h
  set J := ((W.T s R).lev j (c + 1) h).J with hJdef
  set φ := GlobalTheory.VolBridge.locHom ι e with hφ
  have hcompl := hat.compl

  have hIsGL : ∀ x : AutY X R j, IsGL ι (γ⁻¹ * x * γ) (g⁻¹ * φ x * g) := by
    intro x
    refine ⟨e, he, ?_⟩
    rw [hgφ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hC : ∀ x : AutY X R j, x ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ↔ φ x ∈ Cgrp J g := by
    intro x
    rw [mem_Cgrp, ← GlobalTheory.T.mem_R1_iff_local_hom ι e hcc heR x, (hLev j (c + 1) h _ _ (hIsGL x)).1]
    simp [Loc.Cbe, Subgroup.mem_comap, MulAut.conj_apply]
  have hN1 := GlobalTheory.T.mem_N1_iff_locHom_mem_N_one ι e hcc heR
  have hlam : lamYat (Pr := Pr) (R := R) j P.1 = stdAt X.E _ P.1 := by
    ext v
    simp only [lamYat, if_neg hat.nmem, LocE.lamY, LocE.sclLat, Submodule.mem_comap]
    congr! 1
    funext l
    simp [LocE.scE]
  have hKO : ∀ x : AutY X R j, x ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) ↔ φ x ∈ KO k _ := by
    intro x
    rw [hlam]
    exact GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e x
  have hdN := GlobalTheory.T.exists_N1_locHom_mem_open ι hcompl.dense e hcc heR
  refine ⟨?_, ?_⟩
  ·
    have hH := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 le_rfl (by omega) ν
    haveI := hH.2.2.1
    obtain ⟨ho, hAc, hBc⟩ := GlobalTheory.T.isOpen_mirabolicConj_inf_integralGL_unipotent J g hJo hJc
    have hst : stabLat (1 : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k) = KO k _ := by
      ext z; simp [stabLat, Subgroup.mem_comap]
    have hvol : volNat ν 1 (Cgrp J g) =
        (volN ν _ (c + 1) 1 ((Cgrp J g).subgroupOf (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) :
          Set (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1))).toReal /
        (volN ν _ (c + 1) 1 ((KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1))).subgroupOf (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1) :
          Set (N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1))).toReal := by
      rw [volNat, hst]
    rw [hvol, GlobalTheory.T.haar_volume_ratio_compact_eq_relIndex_ratio _ _ _ ho hAc hBc]
    set K := Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hKdef
    set U := KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 with hUdef
    have hA : (Cgrp J g).subgroupOf (N k _ (c + 1) 1) = K.subgroupOf (N k _ (c + 1) 1) :=
      (Subgroup.inf_subgroupOf_right _ _).symm
    have hB : (KO k _).subgroupOf (N k _ (c + 1) 1) = U.subgroupOf (N k _ (c + 1) 1) :=
      (Subgroup.inf_subgroupOf_right _ _).symm
    rw [hA, hB, Subgroup.relIndex_subgroupOf inf_le_right, Subgroup.relIndex_subgroupOf inf_le_right]
    have hKc : K.comap φ = Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) γ ⊓ Loc.N1 X.E (R.N j) (cOf R j) := by
      ext x
      show φ x ∈ Cgrp J g ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hC, hN1]
    have hUc : U.comap φ = Loc.N1 X.E (R.N j) (cOf R j) ⊓ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) := by
      ext x
      show φ x ∈ KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) ⊓ N k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hKO, hN1]; exact And.comm
    have hden : ∀ z, z ∈ K ∨ z ∈ U → ∃ x, (φ x)⁻¹ * z ∈ K ⊓ U := by
      intro z hz
      have hzN : z ∈ N k _ (c + 1) 1 := by rcases hz with hz | hz; exacts [hz.2, hz.2]
      have hO1 : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
        hJo.preimage (by fun_prop)
      have hO' := hO1.inter (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)))
      have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | v⁻¹ * z ∈ ({w | g⁻¹ * w * g ∈ J} ∩
          (KO k (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) : Set (GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k)))} :=
        hO'.preimage (by fun_prop)
      obtain ⟨x, hx, hxV⟩ := hdN z hzN _ hV (by simp [J.one_mem, one_mem])
      refine ⟨x, ?_⟩
      have hxN := (hN1 x).1 hx
      have hm : (φ x)⁻¹ * z ∈ N k _ (c + 1) 1 := mul_mem (inv_mem hxN) hzN
      have hmR : (φ x)⁻¹ * z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := by unfold GlobalTheory.RootEx.R; exact Subgroup.mem_sup_right hm
      exact ⟨⟨mem_Cgrp.2 ⟨hmR, hxV.1⟩, hm⟩, hxV.2, hm⟩
    have h1 := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ K U (fun z hz => hden z (Or.inr hz))
    have h2 := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ U K (fun z hz => by
      obtain ⟨x, hx⟩ := hden z (Or.inl hz); exact ⟨x, by rwa [inf_comm]⟩)
    rw [hKc, hUc] at h1 h2
    rw [← h1, ← h2]
    simp [Loc.volN, map_div₀, map_natCast]
  · intro hle m hm hm1
    haveI := hm
    set e' := GlobalTheory.VolBridge.eX e hcc heR with he'
    set φ' := GlobalTheory.VolBridge.locHom ι e' with hφ'
    have hOo : IsOpen {w : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin (c + 1)) k | g⁻¹ * w * g ∈ J} :=
      hJo.preimage (by fun_prop)
    have hOR : ∀ z ∈ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1, z ∈ Cgrp J g ↔ z ∈ {w | g⁻¹ * w * g ∈ J} := fun z hz => by
      simp [mem_Cgrp, hz]
    have hCR : Cgrp J g ≤ GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) j) (c + 1) 1 := fun z hz => (mem_Cgrp.1 hz).1
    have hP : ∀ y, y ∈ prCat (Pr := Pr) cst.sharp j P.1 γ ↔ φ' y ∈ prX (Cgrp J g) :=
      GlobalTheory.T.mem_mirabolicProjection_iff_colSpaceAutToLocalGL ι e hcc heR hN1 hdN _ _ _ hOo hOR hCR hC
    have hG : ∀ y, y ∈ GLint X.E (R.N j) P.1 ↔ φ' y ∈ KO k _ := fun y =>
      GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL P.1 ι hcompl.int e' y
    have hpo : IsOpen (prX (Cgrp J g) : Set (GL (XIx (Fin R.k) (Fin R.t) j) k)) :=
      GlobalTheory.T.isOpen_mirabolicProjectionToGL _ _ hOo (by simp [J.one_mem]) (fun z hz hzO => (hOR z hz).2 hzO)
    have hden : ∀ z, z ∈ prX (Cgrp J g) ∨ z ∈ KO k _ → ∃ y, (φ' y)⁻¹ * z ∈ prX (Cgrp J g) ⊓ KO k _ := by
      intro z _
      have hV : IsOpen {v : GL (XIx (Fin R.k) (Fin R.t) j) k | v⁻¹ * z ∈ ((prX (Cgrp J g) ⊓ KO k _ : Subgroup _) : Set _)} :=
        (hpo.inter GlobalTheory.SplitFlip.isOpen_KO).preimage (by fun_prop)
      obtain ⟨y, hy⟩ := GlobalTheory.T.exists_colSpaceAutToLocalGL_mem_open_dense ι hcompl.dense e' z _ hV (by simp [one_mem])
      exact ⟨y, hy⟩
    have hle' : prX (Cgrp J g) ≤ KO k _ := by
      intro z hz
      obtain ⟨y, hy1, hy2⟩ := hden z (Or.inl hz)
      have hyC : φ' y ∈ prX (Cgrp J g) := by
        have := mul_mem hz (inv_mem hy1); simpa using this
      have hyK : φ' y ∈ KO k _ := (hG y).1 (hle ((hP y).2 hyC))
      have := mul_mem hyK hy2; simpa using this
    have hidx := GlobalTheory.VolBridge.relIndex_comap_of_dense_image φ' (prX (Cgrp J g)) (KO k _)
      (fun z hz => hden z (Or.inr hz))
    have hc1 : (prX (Cgrp J g)).comap φ' = prCat (Pr := Pr) cst.sharp j P.1 γ := by ext y; exact (hP y).symm
    have hc2 : (KO k _).comap φ' = GLint X.E (R.N j) P.1 := by ext y; exact (hG y).symm
    rw [hc1, hc2] at hidx
    rw [hidx]
    exact GlobalTheory.T.haar_open_subgroup_volume_inv_eq_relIndex m _ _ hle' hpo GlobalTheory.SplitFlip.isCompact_KO hm1

end GlobalTheory.VolBridge
