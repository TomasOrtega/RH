import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctions
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartSplitIdem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CoreOnto.Reps

/- English proof (translation)
Establish `hV : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.core k)) (G.Λ (.core k))` using `fun k hk => (G.isV (X := .core k) hk (fun j h => Node.noConfusion h)).sd`. Conclude with `⟨isSelfDualC_neg (hV (i + 1) hi), hV i hi.le⟩`.
-/
private theorem selfDual_core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ) (hi : i < D.R.m) :
    IsSelfDualC (G.pS (.core i)) (G.latS (.core i)) ∧ IsSelfDualC (G.pT (.core i)) (G.latT (.core i)) := by
  have hV : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V (.core k)) (G.Λ (.core k)) := fun k hk =>
    (G.isV (X := .core k) hk (fun j h => Node.noConfusion h)).sd
  exact ⟨isSelfDualC_neg (hV (i + 1) hi), hV i hi.le⟩

/- English proof (translation)
Establish `inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1`. Rewrite using `[← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]`. Establish `h'` using `congrArg (fun z : Mx D m n => incA D (K : D.host.E)⁻¹ • z) h`. Rewrite `h'` using `[← Nat.cast_smul_eq_nsmul (AE D), ← Nat.cast_smul_eq_nsmul (AE D), smul_smul, smul_smul, mul_comm, inv, one_smul, one_smul]`. Then use the resulting hypothesis.
-/
private theorem nsmul_inj {D : D7} {m n : ℕ} {K : ℕ} (hK : 0 < K) {x y : Mx D m n} (h : K • x = K • y) : x = y := by
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have h' := congrArg (fun z : Mx D m n => incA D (K : D.host.E)⁻¹ • z) h
  rwa [← Nat.cast_smul_eq_nsmul (AE D), ← Nat.cast_smul_eq_nsmul (AE D), smul_smul, smul_smul, mul_comm, inv,
    one_smul, one_smul] at h'

/- English proof (translation)
Introduce `a b` and use `by simp only [Matrix.add_apply, mul_add, hx a b, hy a b]`.
-/
private theorem isHalf_add {D : D7} {m n : ℕ} {c : AE D} {x y : Mx D m n} (hx : IsHalf c x) (hy : IsHalf c y) :
    IsHalf c (x + y) := fun a b => by simp only [Matrix.add_apply, mul_add, hx a b, hy a b]

/- English proof (translation)
Introduce `a b` and use `by simp only [Matrix.neg_apply, mul_neg, hx a b]`.
-/
private theorem isHalf_neg {D : D7} {m n : ℕ} {c : AE D} {x : Mx D m n} (hx : IsHalf c x) : IsHalf c (-x) := fun a b => by
  simp only [Matrix.neg_apply, mul_neg, hx a b]

/- English proof (translation)
Introduce `a b` and use `by simp`.
-/
private theorem isHalf_zero {D : D7} {m n : ℕ} (c : AE D) : IsHalf c (0 : Mx D m n) := fun a b => by simp

/- English proof (translation)
Use `GlobalTheory.ConjHalfDual.symplO_add_right' S T x 0 0` as an intermediate fact. Simplify using `only [add_zero] at this`. Conclude with `(add_eq_left.1 this.symm)`.
-/
private theorem symplO_zero_right {D : D7} (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  have := GlobalTheory.ConjHalfDual.symplO_add_right' S T x 0 0
  simp only [add_zero] at this
  exact (add_eq_left.1 this.symm)

/- English proof (translation)
Use `GlobalTheory.ConjHalfDual.symplO_add_right' S T x y (-y)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, symplO_zero_right]`. Conclude with `(neg_eq_of_add_eq_zero_right this.symm).symm`.
-/
private theorem symplO_neg_right {D : D7} (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have := GlobalTheory.ConjHalfDual.symplO_add_right' S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

/- English proof (translation)
Introduce `h`. Use `AddChar.map_add_eq_mul ψ a (-a)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul]`. Conclude with `one_ne_zero this`.
-/
private theorem psi_ne_zero {F : Type*} [AddGroup F] (ψ : AddChar F ℂ) (a : F) : ψ a ≠ 0 := by
  intro h
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

/- English proof (translation)
Take `⟨U, h1, h2, h3⟩` from `h.opn`. Establish `inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1`. Rewrite using `[← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]`. Establish `hc : Continuous fun a : Mx D m n => incA D (K : D.host.E)⁻¹ • a` using `continuous_id.const_smul (incA D (K : D.host.E)⁻¹)`. Use `GlobalTheory.AscFinWit.finLat_of (fun a ha => h.fin a (hle ha)) ⟨_, h1.preimage hc, by rwa [Set.mem_preimage, smul_zero], fun a ha hb => ?_⟩ h.cpt fun a ha => hle ha` and prove the remaining obligations.

Use `hA _ (h3 _ ha fun i j => Ideal.mul_mem_left _ _ (hb i j))` as an intermediate fact. Rewrite `this` using `[← Nat.cast_smul_eq_nsmul (AE D), smul_smul, inv, one_smul]`. Then use the resulting hypothesis.
-/
private theorem finLat_of_nsmul {D : D7} {m n : ℕ} {Λ A : AddSubgroup (Mx D m n)} (h : GlobalTheory.AscFin.FinLat Λ)
    (hle : A ≤ Λ) {K : ℕ} (hK : 0 < K) (hA : ∀ u ∈ Λ, K • u ∈ A) : GlobalTheory.AscFin.FinLat A := by
  obtain ⟨U, h1, h2, h3⟩ := h.opn
  have inv : (K : AE D) * incA D (K : D.host.E)⁻¹ = 1 := by
    rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK.ne'), map_one]
  have hc : Continuous fun a : Mx D m n => incA D (K : D.host.E)⁻¹ • a :=
    continuous_id.const_smul (incA D (K : D.host.E)⁻¹)
  refine GlobalTheory.AscFinWit.finLat_of (fun a ha => h.fin a (hle ha))
    ⟨_, h1.preimage hc, by rwa [Set.mem_preimage, smul_zero], fun a ha hb => ?_⟩ h.cpt fun a ha => hle ha
  have := hA _ (h3 _ ha fun i j => Ideal.mul_mem_left _ _ (hb i j))
  rwa [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, inv, one_smul] at this

end GlobalTheory.CoreOnto.Reps

open GlobalTheory.CoreOnto.Reps in
/- English proof (translation)
Introduce `D hQ T L μ₀ hL sc G W M hM i hi e he`. Take `⟨hS, hT⟩` from `selfDual_core G i hi`. Use `set Λ : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) := latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True) with hΛ`. Establish `hee : e * e = e` using `GlobalTheory.PlaceVec.idemSum_mul_self he`. Establish `hec : e * cA D e = 0` using `he.2`.

Establish `hinf : infPart D e = 0` using `Formalism.IndefR.Fin.infPart_idemSum he`. Establish `hfin : finPart D e ∈ intAE D` using `GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])`. Establish `hdual : ∀ u, IsHalf (cA D e) u → (u ∈ Λ ↔ ∀ l ∈ Λ, IsHalf e l → W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) l u) = 1)` using `GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf D W.ψ _ _ _ _ W.ψ_std hS hT e hee hec hinf hfin`. Choose the witnesses or unpack the hypotheses as in `⟨K, hK, hKΛ⟩ : ∃ K : ℕ, 0 < K ∧ ∀ u ∈ Λ, K • u ∈ depLat G (.core i) := by`. Take `⟨K, hK, h⟩` from `GlobalTheory.GridWeil.exists_nsmul_latO (T := G.pT (.core i)) (ΛT := G.latT (.core i)) hS (G.pl.modul_ne_bot sc)`.

Use `⟨K, hK, fun u hu => ⟨nsmul_mem hu K, fun e' he' => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `h _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e' (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he'])) _ hu)`. Establish `hKy : ∀ y, IsHalf (cA D e) y → (∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) → K • y ∈ Λ`. Introduce `y hy hyt`.

Use `(hdual _ (GlobalTheory.StdHalfLat.half_nsmul hy K)).2 fun l hl _ => ?_` and prove the remaining obligations. Rewrite using `[← GlobalTheory.DownLift.SplitSep.symplO_nsmul_swap]`. Conclude with `hyt _ (hKΛ l hl)`. Set `A : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i)))` to `{ carrier := {y | IsHalf (cA D e) y ∧ ∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1} add_mem' := fun {a b} ha hb => ⟨isHalf_add ha.1 hb.1, fun u hu => by`. Rewrite using `[GlobalTheory.ConjHalfDual.symplO_add_right', AddChar.map_add_eq_mul, ha.2 u hu, hb.2 u hu, one_mul]⟩`.

Use the proof step `zero_mem' := ⟨isHalf_zero _, fun u _ => by rw [symplO_zero_right, AddChar.map_zero_eq_one]⟩`. Use the proof step `neg_mem' := fun {a} ha => ⟨isHalf_neg ha.1, fun u hu => by`. Rewrite using `[symplO_neg_right, AddChar.map_neg_eq_inv, ha.2 u hu, inv_one]⟩ }`. Set `KΛ : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i)))` to `Λ.map (nsmulAddMonoidHom K)`. Establish `hKΛle : KΛ ≤ Λ`.

Introduce and unpack `_ ⟨w, hw, rfl⟩`. Conclude with `nsmul_mem hw K`. Establish `finΛ : GlobalTheory.AscFin.FinLat Λ` using `GlobalTheory.AscFinWit.finLat_latO hS.1 hT.1`. Establish `finKΛ : GlobalTheory.AscFin.FinLat KΛ` using `finLat_of_nsmul finΛ hKΛle hK (fun u hu => ⟨u, hu, rfl⟩)`. Set `N : AddSubgroup ↥Λ` to `KΛ.addSubgroupOf Λ`.

Use `haveI : CompactSpace ↥Λ := isCompact_iff_compactSpace.mp finΛ.cpt`. Establish `hNopen : IsOpen (N : Set ↥Λ)`. Take `⟨U, hU, h0, hUK⟩` from `finKΛ.opn`. Use `AddSubgroup.isOpen_of_mem_nhds N (g := 0) ?_` and prove the remaining obligations. Use `Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds (by simpa using h0)) ?_` and prove the remaining obligations.

Introduce `a ha`. Conclude with `AddSubgroup.mem_addSubgroupOf.2 (hUK _ ha (finΛ.fin _ a.2))`. Use `haveI : Finite (↥Λ ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N hNopen`. Set `f : ↥A →+ ↥Λ` to `{ toFun := fun y => ⟨K • (y : WO (G.pS (.core i)) (G.pT (.core i))), hKy _ y.2.1 y.2.2⟩ map_zero' := by ext1; simp map_add' := fun a b => by ext1; simp [nsmul_add] }`. Set `g : ↥A →+ ↥Λ ⧸ N` to `(QuotientAddGroup.mk' N).comp f`.

Establish `hker : ∀ y : ↥A, y ∈ g.ker ↔ (y : WO (G.pS (.core i)) (G.pT (.core i))) ∈ Λ`. Introduce `y`. Rewrite using `[AddMonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `(QuotientAddGroup.mk (f y) : ↥Λ ⧸ N) = 0 ↔ _`. Rewrite using `[QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`.

Express the relevant statement in the definitionally equal form `K • (y : WO (G.pS (.core i)) (G.pT (.core i))) ∈ KΛ ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, hwe⟩`. Establish `: w = (y : WO (G.pS (.core i)) (G.pT (.core i)))` using `nsmul_inj hK (by simpa using hwe)`. Conclude with `this ▸ hw`.

Introduce `hy`. Conclude with `⟨_, hy, by simp⟩`. Use `haveI : Finite (↥A ⧸ g.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective g)`. Use `haveI : Fintype (↥A ⧸ g.ker) := Fintype.ofFinite _`. Set `sec : ↥A ⧸ g.ker → ↥A` to `Function.surjInv QuotientAddGroup.mk_surjective`.

Establish `hsec : ∀ q, (QuotientAddGroup.mk (sec q) : ↥A ⧸ g.ker) = q` using `Function.surjInv_eq _`. Establish `hsame : ∀ a b : ↥A, ((a : WO (G.pS (.core i)) (G.pT (.core i))) - b ∈ Λ) ↔ (QuotientAddGroup.mk a : ↥A ⧸ g.ker) = QuotientAddGroup.mk b`. Introduce `a b`. Rewrite using `[QuotientAddGroup.eq, hker]`. Use `push_cast`.

Rewrite using `[show -(a : WO (G.pS (.core i)) (G.pT (.core i))) + (b : WO (G.pS (.core i)) (G.pT (.core i))) = -((a : WO (G.pS (.core i)) (G.pT (.core i))) - (b : WO (G.pS (.core i)) (G.pT (.core i)))) by abel, neg_mem_iff]`. Set `R : Finset (WO (G.pS (.core i)) (G.pT (.core i)))` to `Finset.univ.image (fun q => (sec q : WO (G.pS (.core i)) (G.pT (.core i))))`. Establish `hR : ∀ y ∈ R, y ∈ A`. Introduce `y hy`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hy`.

Conclude with `(sec q).2`. Establish `hsep : ∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ Λ → y = y'`. Introduce `y hy y' hy' hyy`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hy`. Take `⟨q', -, rfl⟩` from `Finset.mem_image.1 hy'`.

Use `(hsame _ _).1 hyy` as an intermediate fact. Rewrite `this` using `[hsec, hsec]`. Rewrite using `[this]`. Use `⟨R, fun y hy => hR y hy, ?_, hsep, ?_⟩` and prove the remaining obligations. Introduce `y hy hyt`.

Set `a : ↥A` to `⟨y, hy, hyt⟩`. Use `⟨sec (QuotientAddGroup.mk a), Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩` and prove the remaining obligations. Conclude with `(hsame a _).2 (hsec _).symm`. Introduce `y hy y' hy' hne`. Establish `hnot : y - y' ∉ Λ` using `fun h => hne (hsep y hy y' hy' h)`.

Establish `hhalf : IsHalf (cA D e) (y - y')`. Rewrite using `[sub_eq_add_neg]`. Conclude with `isHalf_add (hR y hy).1 (isHalf_neg (hR y' hy').1)`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl, hle, hne1⟩ : ∃ l ∈ Λ, IsHalf e l ∧ W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) l (y - y')) ≠ 1 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hnot ((hdual _ hhalf).2 hc)`. Use `⟨l, hl, hle, fun h => hne1 ?_⟩` and prove the remaining obligations. Establish `hsplit : symplO (G.pS (.core i)) (G.pT (.core i)) l y = symplO (G.pS (.core i)) (G.pT (.core i)) l (y - y') + symplO (G.pS (.core i)) (G.pT (.core i)) l y'`. Rewrite using `[← GlobalTheory.ConjHalfDual.symplO_add_right', sub_add_cancel]`.

Rewrite `h` using `[hsplit, AddChar.map_add_eq_mul]`. Conclude with `(mul_eq_right₀ (psi_ne_zero _ _)).1 h`.
-/
theorem _root_.GlobalTheory.T.exists_representatives_half_quotient_pairing_trivial_depthLattice : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∃ R : Finset (WO (G.pS (.core i)) (G.pT (.core i))), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) ∧ (∀ y, IsHalf (cA D e) y → (∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) fun _ => True) ∧ (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True) → y = y') ∧ (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ u ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True), IsHalf e u ∧ W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) ≠ W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y')) := by
  intro D hQ T L μ₀ hL sc G W M hM i hi e he
  classical
  obtain ⟨hS, hT⟩ := selfDual_core G i hi
  set Λ : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) := latO (G.pS (.core i)) (G.pT (.core i))
    (G.latS (.core i) : Set _) (G.latT (.core i) : Set _) (fun _ => True) with hΛ
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hinf : infPart D e = 0 := Formalism.IndefR.Fin.infPart_idemSum he
  have hfin : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hdual : ∀ u, IsHalf (cA D e) u → (u ∈ Λ ↔ ∀ l ∈ Λ, IsHalf e l →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) l u) = 1) :=
    GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf D W.ψ _ _ _ _ W.ψ_std hS hT e hee hec hinf hfin
  obtain ⟨K, hK, hKΛ⟩ : ∃ K : ℕ, 0 < K ∧ ∀ u ∈ Λ, K • u ∈ depLat G (.core i) := by
    obtain ⟨K, hK, h⟩ := GlobalTheory.GridWeil.exists_nsmul_latO (T := G.pT (.core i)) (ΛT := G.latT (.core i)) hS
      (G.pl.modul_ne_bot sc)
    refine ⟨K, hK, fun u hu => ⟨nsmul_mem hu K, fun e' he' => ?_⟩⟩
    rw [smul_comm]
    exact h _ (GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ e'
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he'])) _ hu)

  have hKy : ∀ y, IsHalf (cA D e) y → (∀ u ∈ depLat G (.core i),
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1) → K • y ∈ Λ := by
    intro y hy hyt
    refine (hdual _ (GlobalTheory.StdHalfLat.half_nsmul hy K)).2 fun l hl _ => ?_
    rw [← GlobalTheory.DownLift.SplitSep.symplO_nsmul_swap]
    exact hyt _ (hKΛ l hl)
  let A : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) :=
    { carrier := {y | IsHalf (cA D e) y ∧ ∀ u ∈ depLat G (.core i),
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1}
      add_mem' := fun {a b} ha hb => ⟨isHalf_add ha.1 hb.1, fun u hu => by
        rw [GlobalTheory.ConjHalfDual.symplO_add_right', AddChar.map_add_eq_mul, ha.2 u hu, hb.2 u hu, one_mul]⟩
      zero_mem' := ⟨isHalf_zero _, fun u _ => by rw [symplO_zero_right, AddChar.map_zero_eq_one]⟩
      neg_mem' := fun {a} ha => ⟨isHalf_neg ha.1, fun u hu => by
        rw [symplO_neg_right, AddChar.map_neg_eq_inv, ha.2 u hu, inv_one]⟩ }
  let KΛ : AddSubgroup (WO (G.pS (.core i)) (G.pT (.core i))) := Λ.map (nsmulAddMonoidHom K)
  have hKΛle : KΛ ≤ Λ := by
    rintro _ ⟨w, hw, rfl⟩
    exact nsmul_mem hw K
  have finΛ : GlobalTheory.AscFin.FinLat Λ := GlobalTheory.AscFinWit.finLat_latO hS.1 hT.1
  have finKΛ : GlobalTheory.AscFin.FinLat KΛ :=
    finLat_of_nsmul finΛ hKΛle hK (fun u hu => ⟨u, hu, rfl⟩)
  let N : AddSubgroup ↥Λ := KΛ.addSubgroupOf Λ
  haveI : CompactSpace ↥Λ := isCompact_iff_compactSpace.mp finΛ.cpt
  have hNopen : IsOpen (N : Set ↥Λ) := by
    obtain ⟨U, hU, h0, hUK⟩ := finKΛ.opn
    refine AddSubgroup.isOpen_of_mem_nhds N (g := 0) ?_
    refine Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds (by simpa using h0)) ?_
    intro a ha
    exact AddSubgroup.mem_addSubgroupOf.2 (hUK _ ha (finΛ.fin _ a.2))
  haveI : Finite (↥Λ ⧸ N) := AddSubgroup.quotient_finite_of_isOpen N hNopen
  let f : ↥A →+ ↥Λ :=
    { toFun := fun y => ⟨K • (y : WO (G.pS (.core i)) (G.pT (.core i))), hKy _ y.2.1 y.2.2⟩
      map_zero' := by ext1; simp
      map_add' := fun a b => by ext1; simp [nsmul_add] }
  let g : ↥A →+ ↥Λ ⧸ N := (QuotientAddGroup.mk' N).comp f
  have hker : ∀ y : ↥A, y ∈ g.ker ↔ (y : WO (G.pS (.core i)) (G.pT (.core i))) ∈ Λ := by
    intro y
    rw [AddMonoidHom.mem_ker]
    change (QuotientAddGroup.mk (f y) : ↥Λ ⧸ N) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    change K • (y : WO (G.pS (.core i)) (G.pT (.core i))) ∈ KΛ ↔ _
    constructor
    · rintro ⟨w, hw, hwe⟩
      have : w = (y : WO (G.pS (.core i)) (G.pT (.core i))) := nsmul_inj hK (by simpa using hwe)
      exact this ▸ hw
    · intro hy
      exact ⟨_, hy, by simp⟩
  haveI : Finite (↥A ⧸ g.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective g)
  haveI : Fintype (↥A ⧸ g.ker) := Fintype.ofFinite _
  let sec : ↥A ⧸ g.ker → ↥A := Function.surjInv QuotientAddGroup.mk_surjective
  have hsec : ∀ q, (QuotientAddGroup.mk (sec q) : ↥A ⧸ g.ker) = q := Function.surjInv_eq _
  have hsame : ∀ a b : ↥A, ((a : WO (G.pS (.core i)) (G.pT (.core i))) - b ∈ Λ) ↔
      (QuotientAddGroup.mk a : ↥A ⧸ g.ker) = QuotientAddGroup.mk b := by
    intro a b
    rw [QuotientAddGroup.eq, hker]
    push_cast
    rw [show -(a : WO (G.pS (.core i)) (G.pT (.core i))) + (b : WO (G.pS (.core i)) (G.pT (.core i))) =
      -((a : WO (G.pS (.core i)) (G.pT (.core i))) - (b : WO (G.pS (.core i)) (G.pT (.core i)))) by abel, neg_mem_iff]
  let R : Finset (WO (G.pS (.core i)) (G.pT (.core i))) :=
    Finset.univ.image (fun q => (sec q : WO (G.pS (.core i)) (G.pT (.core i))))
  have hR : ∀ y ∈ R, y ∈ A := by
    intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (sec q).2
  have hsep : ∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ Λ → y = y' := by
    intro y hy y' hy' hyy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy'
    have := (hsame _ _).1 hyy
    rw [hsec, hsec] at this
    rw [this]
  refine ⟨R, fun y hy => hR y hy, ?_, hsep, ?_⟩
  · intro y hy hyt
    let a : ↥A := ⟨y, hy, hyt⟩
    refine ⟨sec (QuotientAddGroup.mk a), Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (hsame a _).2 (hsec _).symm
  · intro y hy y' hy' hne
    have hnot : y - y' ∉ Λ := fun h => hne (hsep y hy y' hy' h)
    have hhalf : IsHalf (cA D e) (y - y') := by
      rw [sub_eq_add_neg]
      exact isHalf_add (hR y hy).1 (isHalf_neg (hR y' hy').1)
    obtain ⟨l, hl, hle, hne1⟩ : ∃ l ∈ Λ, IsHalf e l ∧
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) l (y - y')) ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hnot ((hdual _ hhalf).2 hc)
    refine ⟨l, hl, hle, fun h => hne1 ?_⟩
    have hsplit : symplO (G.pS (.core i)) (G.pT (.core i)) l y =
        symplO (G.pS (.core i)) (G.pT (.core i)) l (y - y') + symplO (G.pS (.core i)) (G.pT (.core i)) l y' := by
      rw [← GlobalTheory.ConjHalfDual.symplO_add_right', sub_add_cancel]
    rw [hsplit, AddChar.map_add_eq_mul] at h
    exact (mul_eq_right₀ (psi_ne_zero _ _)).1 h

end
