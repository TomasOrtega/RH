import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfE

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)

/- English proof (translation)
Establish `F` using `hfr.1 T hcry hjmp`. Establish `C1 : ∀ x hx, x ∈ NL W T Pt π' Eπ h' c → ∃ y hy, y ∈ NcS W T c ∧ α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy`. Introduce `x hx hxNL`. Proceed by induction on `hxNL using Submodule.span_induction with`. Consider the case `mem x hxS`.

Take `⟨⟨y0, hy0⟩, hq⟩` from `Submodule.Quotient.mk_surjective _ (α T ⟨x, hx⟩)`. Establish `hα : α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y0 hy0` using `hq.symm`. Establish `hN` using `alpha_core W T Pt π' Eπ h' M σ c α β hfr hcry hjmp hs hww hQ h5a hp4 hpt hexp x hx hxS y0 hy0 hα`. Take `⟨-, h2, h3⟩` from `(mem_LamPS W T Eπ h' c y0).1 hy0`. Conclude with `⟨y0, hy0, (mem_NcS W T c y0).2 ⟨hN, h2, h3⟩, hα⟩`.

Consider the case `zero`. Use `⟨0, Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Establish `e : (⟨0, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = 0` using `rfl`. Rewrite using `[e, map_zero]`. Conclude with `(Submodule.Quotient.mk_zero _).symm`.

Consider the case `add x₁ x₂ h₁ h₂ ih₁ ih₂`. Establish `hx₁` using `NL_le_LamLA W T π' Eπ h' c Pt h₁`. Establish `hx₂` using `NL_le_LamLA W T π' Eπ h' c Pt h₂`. Take `⟨y₁, hy₁, hN₁, e₁⟩` from `ih₁ hx₁`. Take `⟨y₂, hy₂, hN₂, e₂⟩` from `ih₂ hx₂`.

Use `⟨y₁ + y₂, Submodule.add_mem _ hy₁ hy₂, Submodule.add_mem _ hN₁ hN₂, ?_⟩` and prove the remaining obligations. Establish `e : (⟨x₁ + x₂, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = ⟨x₁, hx₁⟩ + ⟨x₂, hx₂⟩` using `rfl`. Rewrite using `[e, map_add, e₁, e₂]`. Conclude with `(Submodule.Quotient.mk_add _).symm`. Consider the case `smul r x₁ h₁ ih₁`.

Establish `hx₁` using `NL_le_LamLA W T π' Eπ h' c Pt h₁`. Take `⟨y₁, hy₁, hN₁, e₁⟩` from `ih₁ hx₁`. Use `⟨r • y₁, Submodule.smul_mem _ _ hy₁, Submodule.smul_mem _ _ hN₁, ?_⟩` and prove the remaining obligations. Establish `e : (⟨r • x₁, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = r • ⟨x₁, hx₁⟩` using `rfl`. Rewrite using `[e, map_smul, e₁]`.

Conclude with `(Submodule.Quotient.mk_smul _ _ _).symm`. Establish `C2 : ∀ y hy, y ∈ NcS W T c → ∃ x hx, x ∈ NL W T Pt π' Eπ h' c ∧ β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx`. Introduce `y hy hyN`. Take `⟨⟨x, hx⟩, hq⟩` from `Submodule.Quotient.mk_surjective _ (β T ⟨y, hy⟩)`. Conclude with `⟨x, hx, Submodule.subset_span (beta_core W T Pt π' Eπ h' M σ c α β hfr hcry hjmp hs hww hQ hp4 hpt y hy ((mem_NcS W T c y).1 hyN).1 x hx hq.symm), hq.symm⟩`.

Establish `HighestWeightSpaceFinite : ∀ j : ℕ, j ≤ M → ∀ x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy → x ∈ piNL W T Pt π' Eπ h' c j → y ∈ PiNS W T π' j`. Introduce `j hjM x hx y hy hα hpi`. Take `⟨x', hx'NL, rfl⟩` from `Submodule.mem_map.1 hpi`. Establish `hx'L` using `NL_le_LamLA W T π' Eπ h' c Pt hx'NL`. Take `⟨y', hy', hy'N, hα'⟩` from `C1 x' hx'L hx'NL`.

Establish `hay` using `LamPS_smul W T Eπ h' c (W.AΔ.pow_mem hπΔ j) hy'`. Establish `h2` using `F.2.2.2.2.1 (π' ^ j) (W.AΔ.pow_mem hπΔ j) x' hx'L y' hy' hα' hx hay`. Rewrite `h2` using `[hα]`. Establish `hd : y - π' ^ j • y' ∈ JP W T π' Eπ h' M c`. Establish `h2' : (Submodule.Quotient.mk (⟨y, hy⟩ : ↥(LamPS W T Eπ h' c)) : QLamP W T π' Eπ h' M c) = Submodule.Quotient.mk ⟨π' ^ j • y', hay⟩` using `h2`.

Use `(Submodule.Quotient.eq ((JP W T π' Eπ h' M c).comap (LamPS W T Eπ h' c).subtype)).1 h2'` as an intermediate fact. Conclude with `this`. Take `⟨z, hzN, hz⟩` from `JP_mem W T π' Eπ h' c hww hQ h5a M j hjM hd`. Rewrite using `[mem_PiNS]`. Use `⟨⟨y' + z, Submodule.add_mem _ ((mem_NcS W T c y').1 hy'N).1 hzN, ?_⟩, ((mem_LamPS W T Eπ h' c y).1 hy).2.1⟩` and prove the remaining obligations.

Rewrite using `[smul_add, ← hz]`. Normalize the expressions using the abelian group laws. Establish `HighestWeightIntegral : ∀ j : ℕ, j ≤ M → ∀ y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx → y ∈ PiNS W T π' j → x ∈ piNL W T Pt π' Eπ h' c j`. Introduce `j hjM y hy x hx hβ hpi`. Take `⟨⟨y1, hy1N, rfl⟩, -⟩` from `(mem_PiNS W T π' j _).1 hpi`.

Establish `hunit : IsUnit (algebraMap (LetA O n) W.EE (π' ^ j))`. Rewrite using `[map_pow]`. Conclude with `hπu.pow j`. Take `⟨-, hyΔ, hyc⟩` from `(mem_LamPS W T Eπ h' c _).1 hy`. Establish `hy1Δ : ∀ δ ∈ W.DelF, W.γD T δ y1 = y1`.

Introduce `δ hδ`. Establish `e : W.γD T δ (π' ^ j • y1) = π' ^ j • W.γD T δ y1`. Rewrite using `[Formalism.MainNotions.LiftingTheory.wmap_γD_smul, W.AΔ.pow_mem hπΔ j δ hδ]`. Use `sub_eq_zero.1 (tf_smul W T hunit ?_)` and prove the remaining obligations. Rewrite using `[smul_sub, ← e, hyΔ δ hδ, sub_self]`.

Establish `hy1c : (letE c : LetA O n) • y1 = y1`. Use `sub_eq_zero.1 (tf_smul W T hunit ?_)` and prove the remaining obligations. Rewrite using `[smul_sub, smul_comm, hyc, sub_self]`. Establish `hy1Nc : y1 ∈ NcS W T c` using `(mem_NcS W T c y1).2 ⟨hy1N, hy1Δ, hy1c⟩`. Establish `hy1L` using `hNP y1 hy1Nc`.

Take `⟨x1, hx1, hx1NL, hβ1⟩` from `C2 y1 hy1L hy1Nc`. Establish `hax` using `LamLA_smul W T π' Eπ h' c (W.AΔ.pow_mem hπΔ j) hx1`. Establish `h6` using `F.2.2.2.2.2.1 (π' ^ j) (W.AΔ.pow_mem hπΔ j) y1 hy1L x1 hx1 hβ1 hy hax`. Rewrite `h6` using `[hβ]`. Establish `hd : x - smulLA W T π' c (π' ^ j) x1 ∈ JLA W T π' Eπ h' M c`.

Establish `h6' : (Submodule.Quotient.mk (⟨x, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) : QLamLA W T π' Eπ h' M c) = Submodule.Quotient.mk ⟨smulLA W T π' c (π' ^ j) x1, hax⟩` using `h6`. Use `(Submodule.Quotient.eq ((JLA W T π' Eπ h' M c).comap (LamLA W T π' Eπ h' c ⊤).subtype)).1 h6'` as an intermediate fact. Conclude with `this`. Establish `h1` using `JLA_le W T Pt π' Eπ h' M c hs hww hQ hp4 hpt hjmp hπΔ hEΔ j hjM hd`. Establish `h2 : smulLA W T π' c (π' ^ j) x1 ∈ piNL W T Pt π' Eπ h' c j` using `Submodule.mem_map_of_mem hx1NL`.

Use `Submodule.add_mem _ h1 h2` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Use `⟨C1, C2, fun j _ hjM => ⟨HighestWeightSpaceFinite j hjM, HighestWeightIntegral j hjM⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy hα hinv`. Establish `hγx : ((γLA W T π' c - LinearMap.id : LA W T π' c →ₗ[O] LA W T π' c) x) ∈ piNL W T Pt π' Eπ h' c 1` using `(Submodule.mem_inf.1 hinv).2`.

Rewrite `hγx` using `[LinearMap.sub_apply, LinearMap.id_apply]`. Use `(mem_InvS W T π' Eπ h' 1 c y).2 ⟨hy, ?_⟩` and prove the remaining obligations. Establish `hgx` using `LamLA_γ W T π' Eπ h' c hu' huu hγE hx`. Establish `hgy` using `LamPS_γ W T Eπ h' c huu hγE hy`. Establish `h7` using `F.2.2.2.2.2.2.1 x hx y hy hα hgx hgy`.

Establish `hsx` using `Submodule.sub_mem _ hgx hx`. Establish `hsy` using `Submodule.sub_mem _ hgy hy`. Establish `hα' : α T ⟨_, hsx⟩ = mkP W T π' Eπ h' M c _ hsy`. Establish `e : (⟨_, hsx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = ⟨_, hgx⟩ - ⟨x, hx⟩` using `rfl`. Rewrite using `[e, map_sub, h7, hα]`.

Conclude with `(Submodule.Quotient.mk_sub _).symm`. Conclude with `HighestWeightSpaceFinite 1 hM _ hsx _ hsy hα' hγx`. Introduce `y hy x hx hβ hinv`. Establish `hγy` using `((mem_InvS W T π' Eπ h' 1 c y).1 hinv).2`. Establish `hgx` using `LamLA_γ W T π' Eπ h' c hu' huu hγE hx`.

Establish `hgy` using `LamPS_γ W T Eπ h' c huu hγE hy`. Establish `h8` using `F.2.2.2.2.2.2.2.1 y hy x hx hβ hgy hgx`. Establish `hsx` using `Submodule.sub_mem _ hgx hx`. Establish `hsy` using `Submodule.sub_mem _ hgy hy`. Establish `hβ' : β T ⟨_, hsy⟩ = mkLA W T π' Eπ h' M c _ hsx`.

Establish `e : (⟨_, hsy⟩ : ↥(LamPS W T Eπ h' c)) = ⟨_, hgy⟩ - ⟨y, hy⟩` using `rfl`. Rewrite using `[e, map_sub, h8, hβ]`. Conclude with `(Submodule.Quotient.mk_sub _).symm`. Establish `h` using `HighestWeightIntegral 1 hM _ hsy _ hsx hβ' hγy`. Use `Submodule.mem_inf.2 ⟨hx, ?_⟩` and prove the remaining obligations.

Use `show ((γLA W T π' c - LinearMap.id : LA W T π' c →ₗ[O] LA W T π' c) x) ∈ piNL W T Pt π' Eπ h' c 1`. Rewrite using `[LinearMap.sub_apply, LinearMap.id_apply]`. Conclude with `h`.
-/
theorem modelF_local (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hcry : IsCrys PD T.ρ)
    (hjmp : ∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (hs : W.s = 1) (hM : 1 ≤ M)
    (hπΔ : π' ∈ W.AΔ) (hEΔ : Eπ ∈ W.AΔ) (hπu : IsUnit (algebraMap (LetA O n) W.EE π'))
    {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    {u u' : LetA O n} (hu' : u' ∈ W.AΔ) (huu : u' * u = 1) (hγE : W.γA W.gamK Eπ = u * Eπ)
    (h5a : ∀ x ∈ W.Nl T (c - 1), W.Q ^ h' • W.φD T x ∈ W.N T)
    (hNP : ∀ y ∈ NcS W T c, y ∈ LamPS W T Eπ h' c) (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hpt : ∀ ζ τ, Pt c ζ τ → ζ ^ PD.p = 1 ∧ ζ ≠ 1) (hexp : ExpansionFormLetter W T Pt) :
    ModelF W T Pt π' Eπ h' M c α β := by
  have F := hfr.1 T hcry hjmp

  have C1 : ∀ x hx, x ∈ NL W T Pt π' Eπ h' c →
      ∃ y hy, y ∈ NcS W T c ∧ α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy := by
    intro x hx hxNL
    induction hxNL using Submodule.span_induction with
    | mem x hxS =>
      obtain ⟨⟨y0, hy0⟩, hq⟩ := Submodule.Quotient.mk_surjective _ (α T ⟨x, hx⟩)
      have hα : α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y0 hy0 := hq.symm
      have hN := alpha_core W T Pt π' Eπ h' M σ c α β hfr hcry hjmp hs hww hQ h5a hp4 hpt hexp
        x hx hxS y0 hy0 hα
      obtain ⟨-, h2, h3⟩ := (mem_LamPS W T Eπ h' c y0).1 hy0
      exact ⟨y0, hy0, (mem_NcS W T c y0).2 ⟨hN, h2, h3⟩, hα⟩
    | zero =>
      refine ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩
      have e : (⟨0, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = 0 := rfl
      rw [e, map_zero]
      exact (Submodule.Quotient.mk_zero _).symm
    | add x₁ x₂ h₁ h₂ ih₁ ih₂ =>
      have hx₁ := NL_le_LamLA W T π' Eπ h' c Pt h₁
      have hx₂ := NL_le_LamLA W T π' Eπ h' c Pt h₂
      obtain ⟨y₁, hy₁, hN₁, e₁⟩ := ih₁ hx₁
      obtain ⟨y₂, hy₂, hN₂, e₂⟩ := ih₂ hx₂
      refine ⟨y₁ + y₂, Submodule.add_mem _ hy₁ hy₂, Submodule.add_mem _ hN₁ hN₂, ?_⟩
      have e : (⟨x₁ + x₂, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = ⟨x₁, hx₁⟩ + ⟨x₂, hx₂⟩ := rfl
      rw [e, map_add, e₁, e₂]
      exact (Submodule.Quotient.mk_add _).symm
    | smul r x₁ h₁ ih₁ =>
      have hx₁ := NL_le_LamLA W T π' Eπ h' c Pt h₁
      obtain ⟨y₁, hy₁, hN₁, e₁⟩ := ih₁ hx₁
      refine ⟨r • y₁, Submodule.smul_mem _ _ hy₁, Submodule.smul_mem _ _ hN₁, ?_⟩
      have e : (⟨r • x₁, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = r • ⟨x₁, hx₁⟩ := rfl
      rw [e, map_smul, e₁]
      exact (Submodule.Quotient.mk_smul _ _ _).symm

  have C2 : ∀ y hy, y ∈ NcS W T c →
      ∃ x hx, x ∈ NL W T Pt π' Eπ h' c ∧ β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx := by
    intro y hy hyN
    obtain ⟨⟨x, hx⟩, hq⟩ := Submodule.Quotient.mk_surjective _ (β T ⟨y, hy⟩)
    exact ⟨x, hx, Submodule.subset_span (beta_core W T Pt π' Eπ h' M σ c α β hfr hcry hjmp hs hww
      hQ hp4 hpt y hy ((mem_NcS W T c y).1 hyN).1 x hx hq.symm), hq.symm⟩

  have HighestWeightSpaceFinite : ∀ j : ℕ, j ≤ M → ∀ x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy →
      x ∈ piNL W T Pt π' Eπ h' c j → y ∈ PiNS W T π' j := by
    intro j hjM x hx y hy hα hpi
    obtain ⟨x', hx'NL, rfl⟩ := Submodule.mem_map.1 hpi
    have hx'L := NL_le_LamLA W T π' Eπ h' c Pt hx'NL
    obtain ⟨y', hy', hy'N, hα'⟩ := C1 x' hx'L hx'NL
    have hay := LamPS_smul W T Eπ h' c (W.AΔ.pow_mem hπΔ j) hy'
    have h2 := F.2.2.2.2.1 (π' ^ j) (W.AΔ.pow_mem hπΔ j) x' hx'L y' hy' hα' hx hay
    rw [hα] at h2
    have hd : y - π' ^ j • y' ∈ JP W T π' Eπ h' M c := by
      have h2' : (Submodule.Quotient.mk (⟨y, hy⟩ : ↥(LamPS W T Eπ h' c)) : QLamP W T π' Eπ h' M c) =
          Submodule.Quotient.mk ⟨π' ^ j • y', hay⟩ := h2
      have := (Submodule.Quotient.eq
        ((JP W T π' Eπ h' M c).comap (LamPS W T Eπ h' c).subtype)).1 h2'
      exact this
    obtain ⟨z, hzN, hz⟩ := JP_mem W T π' Eπ h' c hww hQ h5a M j hjM hd
    rw [mem_PiNS]
    refine ⟨⟨y' + z, Submodule.add_mem _ ((mem_NcS W T c y').1 hy'N).1 hzN, ?_⟩,
      ((mem_LamPS W T Eπ h' c y).1 hy).2.1⟩
    rw [smul_add, ← hz]
    abel

  have HighestWeightIntegral : ∀ j : ℕ, j ≤ M → ∀ y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx →
      y ∈ PiNS W T π' j → x ∈ piNL W T Pt π' Eπ h' c j := by
    intro j hjM y hy x hx hβ hpi
    obtain ⟨⟨y1, hy1N, rfl⟩, -⟩ := (mem_PiNS W T π' j _).1 hpi
    have hunit : IsUnit (algebraMap (LetA O n) W.EE (π' ^ j)) := by
      rw [map_pow]
      exact hπu.pow j
    obtain ⟨-, hyΔ, hyc⟩ := (mem_LamPS W T Eπ h' c _).1 hy
    have hy1Δ : ∀ δ ∈ W.DelF, W.γD T δ y1 = y1 := by
      intro δ hδ
      have e : W.γD T δ (π' ^ j • y1) = π' ^ j • W.γD T δ y1 := by
        rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, W.AΔ.pow_mem hπΔ j δ hδ]
      refine sub_eq_zero.1 (tf_smul W T hunit ?_)
      rw [smul_sub, ← e, hyΔ δ hδ, sub_self]
    have hy1c : (letE c : LetA O n) • y1 = y1 := by
      refine sub_eq_zero.1 (tf_smul W T hunit ?_)
      rw [smul_sub, smul_comm, hyc, sub_self]
    have hy1Nc : y1 ∈ NcS W T c := (mem_NcS W T c y1).2 ⟨hy1N, hy1Δ, hy1c⟩
    have hy1L := hNP y1 hy1Nc
    obtain ⟨x1, hx1, hx1NL, hβ1⟩ := C2 y1 hy1L hy1Nc
    have hax := LamLA_smul W T π' Eπ h' c (W.AΔ.pow_mem hπΔ j) hx1
    have h6 := F.2.2.2.2.2.1 (π' ^ j) (W.AΔ.pow_mem hπΔ j) y1 hy1L x1 hx1 hβ1 hy hax
    rw [hβ] at h6
    have hd : x - smulLA W T π' c (π' ^ j) x1 ∈ JLA W T π' Eπ h' M c := by
      have h6' : (Submodule.Quotient.mk (⟨x, hx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) :
          QLamLA W T π' Eπ h' M c) = Submodule.Quotient.mk ⟨smulLA W T π' c (π' ^ j) x1, hax⟩ := h6
      have := (Submodule.Quotient.eq
        ((JLA W T π' Eπ h' M c).comap (LamLA W T π' Eπ h' c ⊤).subtype)).1 h6'
      exact this
    have h1 := JLA_le W T Pt π' Eπ h' M c hs hww hQ hp4 hpt hjmp hπΔ hEΔ j hjM hd
    have h2 : smulLA W T π' c (π' ^ j) x1 ∈ piNL W T Pt π' Eπ h' c j :=
      Submodule.mem_map_of_mem hx1NL
    have := Submodule.add_mem _ h1 h2
    rwa [sub_add_cancel] at this
  refine ⟨C1, C2, fun j _ hjM => ⟨HighestWeightSpaceFinite j hjM, HighestWeightIntegral j hjM⟩, ?_, ?_⟩
  · intro x hx y hy hα hinv
    have hγx : ((γLA W T π' c - LinearMap.id : LA W T π' c →ₗ[O] LA W T π' c) x) ∈ piNL W T Pt π' Eπ h' c 1 :=
      (Submodule.mem_inf.1 hinv).2
    rw [LinearMap.sub_apply, LinearMap.id_apply] at hγx
    refine (mem_InvS W T π' Eπ h' 1 c y).2 ⟨hy, ?_⟩
    have hgx := LamLA_γ W T π' Eπ h' c hu' huu hγE hx
    have hgy := LamPS_γ W T Eπ h' c huu hγE hy
    have h7 := F.2.2.2.2.2.2.1 x hx y hy hα hgx hgy
    have hsx := Submodule.sub_mem _ hgx hx
    have hsy := Submodule.sub_mem _ hgy hy
    have hα' : α T ⟨_, hsx⟩ = mkP W T π' Eπ h' M c _ hsy := by
      have e : (⟨_, hsx⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = ⟨_, hgx⟩ - ⟨x, hx⟩ := rfl
      rw [e, map_sub, h7, hα]
      exact (Submodule.Quotient.mk_sub _).symm
    exact HighestWeightSpaceFinite 1 hM _ hsx _ hsy hα' hγx
  · intro y hy x hx hβ hinv
    have hγy := ((mem_InvS W T π' Eπ h' 1 c y).1 hinv).2
    have hgx := LamLA_γ W T π' Eπ h' c hu' huu hγE hx
    have hgy := LamPS_γ W T Eπ h' c huu hγE hy
    have h8 := F.2.2.2.2.2.2.2.1 y hy x hx hβ hgy hgx
    have hsx := Submodule.sub_mem _ hgx hx
    have hsy := Submodule.sub_mem _ hgy hy
    have hβ' : β T ⟨_, hsy⟩ = mkLA W T π' Eπ h' M c _ hsx := by
      have e : (⟨_, hsy⟩ : ↥(LamPS W T Eπ h' c)) = ⟨_, hgy⟩ - ⟨y, hy⟩ := rfl
      rw [e, map_sub, h8, hβ]
      exact (Submodule.Quotient.mk_sub _).symm
    have h := HighestWeightIntegral 1 hM _ hsy _ hsx hβ' hγy
    refine Submodule.mem_inf.2 ⟨hx, ?_⟩
    show ((γLA W T π' c - LinearMap.id : LA W T π' c →ₗ[O] LA W T π' c) x) ∈ piNL W T Pt π' Eπ h' c 1
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    exact h

end Local

end Formalism.MainNotions.N.Ln34.ModelFPf

end
