import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinWeilO

open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts

/- English proof (translation)
Use `haveI := hR.to_subtype`. Use `choose f hf hf' using h1`. Use `haveI : Finite (K ⧸ H.addSubgroupOf K) := by`. Use `Finite.of_injective (fun q => (⟨f _ (Quotient.out q : K).2, hf _ _⟩ : R)) fun q q' h => ?_` and prove the remaining obligations. Establish `h3 : f _ (Quotient.out q : K).2 = f _ (Quotient.out q' : K).2` using `congrArg Subtype.val h`.

Establish `h4` using `h2 _ _ _ (hf' _ (Quotient.out q : K).2) (h3 ▸ hf' _ (Quotient.out q' : K).2)`. Rewrite using `[← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq_iff_sub_mem]`. Conclude with `h4`. Conclude with `AddSubgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_finite {G Y : Type} [AddCommGroup G] (H K : AddSubgroup G) {R : Set Y} (hR : R.Finite)
    (rel : G → Y → Prop) (h1 : ∀ k ∈ K, ∃ r ∈ R, rel k r) (h2 : ∀ k k' r, rel k r → rel k' r → k - k' ∈ H) :
    H.relIndex K ≠ 0 := by
  haveI := hR.to_subtype
  choose f hf hf' using h1
  haveI : Finite (K ⧸ H.addSubgroupOf K) := by
    refine Finite.of_injective (fun q => (⟨f _ (Quotient.out q : K).2, hf _ _⟩ : R)) fun q q' h => ?_
    have h3 : f _ (Quotient.out q : K).2 = f _ (Quotient.out q' : K).2 := congrArg Subtype.val h
    have h4 := h2 _ _ _ (hf' _ (Quotient.out q : K).2) (h3 ▸ hf' _ (Quotient.out q' : K).2)
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq_iff_sub_mem]
    exact h4
  exact AddSubgroup.index_ne_zero_of_finite

/- English proof (translation)
Take `⟨C, hC⟩` from `M.exists_isCompl`. Set `e` to `M.prodEquivOfIsCompl C hC`. Use `⟨{ toFun := fun p => e.conj ((Om p).prodMap LinearMap.id), map_one' := ?_, map_mul' := fun p q => ?_ }, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one]`. Conclude with `(congrArg e.conj LinearMap.prodMap_id).trans e.conj_id`.

Rewrite using `[map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← e.conj_comp, LinearMap.prodMap_comp, LinearMap.id_comp]`. Introduce `p m show e (((Om p).prodMap LinearMap.id) (e.symm m)) = _`. Rewrite using `[Submodule.prodEquivOfIsCompl_symm_apply_left]`. Simplify using `[e]`.
-/
theorem exists_extend {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (Om : Γ →* Module.End ℂ M) : ∃ om : Γ →* Module.End ℂ V, ∀ p (m : M), om p m = Om p m := by
  obtain ⟨C, hC⟩ := M.exists_isCompl
  let e := M.prodEquivOfIsCompl C hC
  refine ⟨{ toFun := fun p => e.conj ((Om p).prodMap LinearMap.id), map_one' := ?_, map_mul' := fun p q => ?_ }, ?_⟩
  · rw [map_one]
    exact (congrArg e.conj LinearMap.prodMap_id).trans e.conj_id
  · rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← e.conj_comp, LinearMap.prodMap_comp,
      LinearMap.id_comp]
  · intro p m
    show e (((Om p).prodMap LinearMap.id) (e.symm m)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp [e]

section Abstract

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
  {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

/- English proof (translation)
Take `⟨h1, h2⟩` from `(sumOp_transversal h A B hB).2.2 hle`. Rewrite using `[normOp, h1, h2 e he, map_one, inv_one, one_smul]`.
-/
theorem normOp_of_le (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B) (hle : B ≤ A)
    {e : M} (he : Fixes W A e) : normOp lam W A B e = e := by
  obtain ⟨h1, h2⟩ := (sumOp_transversal h A B hB).2.2 hle
  rw [normOp, h1, h2 e he, map_one, inv_one, one_smul]

/- English proof (translation)
Take `⟨n, f, hf, hu⟩` from `((sumOp_transversal h A B hB).2.1 hi).1`. Establish `he' : Fixes W A (L e)` using `fun a ha => by rw [← hL, he a ha]`. Rewrite using `[normOp, normOp, ((sumOp_transversal h A B hB).1 _ he' _ f hf hu).1, ((sumOp_transversal h A B hB).1 _ he _ f hf hu).1, map_smul, map_sum]`. Simplify using `only [hL]`.
-/
theorem normOp_comm (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B) (hi : idx A B ≠ 0)
    (L : M →ₗ[ℂ] M) (hL : ∀ x v, L (W x v) = W x (L v)) {e : M} (he : Fixes W A e) :
    normOp lam W A B (L e) = L (normOp lam W A B e) := by
  obtain ⟨n, f, hf, hu⟩ := ((sumOp_transversal h A B hB).2.1 hi).1
  have he' : Fixes W A (L e) := fun a ha => by rw [← hL, he a ha]
  rw [normOp, normOp, ((sumOp_transversal h A B hB).1 _ he' _ f hf hu).1,
    ((sumOp_transversal h A B hB).1 _ he _ f hf hu).1, map_smul, map_sum]
  simp only [hL]

end Abstract

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

/- English proof (translation)
Take `⟨R, hR, h⟩` from `GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True) N hN`. Use `relIndex_ne_zero_of_finite _ _ hR (fun b r => ∃ u ∈ latO S T ΛS ΛT fun _ => True, N • (b : WO S T) = r + N • u) (fun b hb => h _ (hB b hb)) ?_` and prove the remaining obligations. Introduce and unpack `b b' r ⟨u, hu, h1⟩ ⟨u', hu', h2⟩`. Establish `h3 : N • ((b : WO S T) - b') = N • (u - u')`. Rewrite using `[nsmul_sub, nsmul_sub, h1, h2, add_sub_add_left_eq_sub]`.

Establish `h4 : (b : WO S T) - b' = u - u'`. Rewrite using `[← GlobalTheory.PlaceModel.inv_smul_nsmul S T hN ((b : WO S T) - b'), h3, GlobalTheory.PlaceModel.inv_smul_nsmul S T hN]`. Use `show (b : WO S T) - b' ∈ latO S T ΛS ΛT fun _ => True`. Rewrite using `[h4]`. Conclude with `sub_mem hu hu'`.
-/
theorem idx_latF_ne_zero {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (B : Submodule (𝓞 D.host.E) (XF S T)) {N : ℕ} (hN : 0 < N) (hB : ∀ b ∈ B, N • b ∈ latF S T ΛS ΛT) :
    idx (latF S T ΛS ΛT) B ≠ 0 := by
  obtain ⟨R, hR, h⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True) N hN
  refine relIndex_ne_zero_of_finite _ _ hR
    (fun b r => ∃ u ∈ latO S T ΛS ΛT fun _ => True, N • (b : WO S T) = r + N • u) (fun b hb => h _ (hB b hb)) ?_
  rintro b b' r ⟨u, hu, h1⟩ ⟨u', hu', h2⟩
  have h3 : N • ((b : WO S T) - b') = N • (u - u') := by
    rw [nsmul_sub, nsmul_sub, h1, h2, add_sub_add_left_eq_sub]
  have h4 : (b : WO S T) - b' = u - u' := by
    rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hN ((b : WO S T) - b'), h3, GlobalTheory.PlaceModel.inv_smul_nsmul S T hN]
  show (b : WO S T) - b' ∈ latO S T ΛS ΛT fun _ => True
  rw [h4]
  exact sub_mem hu hu'

/- English proof (translation)
The claim follows from `AddSubgroup.relIndex_comap (latO S T LS LT fun _ => True) (XF.incl S T) B.toAddSubgroup`.
-/
theorem idx_latF_eq (B : Submodule (𝓞 D.host.E) (XF S T)) :
    idx (latF S T LS LT) B = (latO S T LS LT fun _ => True).relIndex (B.toAddSubgroup.map (XF.incl S T)) :=
  AddSubgroup.relIndex_comap (latO S T LS LT fun _ => True) (XF.incl S T) B.toAddSubgroup

/- English proof (translation)
Establish `h : ψ (symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u) = 1` using `(hA _).1 ((latF S T LS LT).smul_mem w (nsmul_mem hu 2)) u hu`. Establish `h2` using `AddChar.map_add_eq_mul ψ (-symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u) (symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u)`. Rewrite `h2` using `[neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one]`. Rewrite using `[phase, h2]`. Use `congr 2`.

Rewrite using `[← symplOH_add_self, ← symplOH_add_right, XF.coe_nsmul, two_nsmul]`.
-/
theorem phase_two (hA : SelfDual (gamF ψ S T) (latF S T LS LT)) (w : 𝓞 D.host.E) {u : XF S T}
    (hu : u ∈ latF S T LS LT) : phase ψ w (2 • u) = 1 := by
  have h : ψ (symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u) = 1 :=
    (hA _).1 ((latF S T LS LT).smul_mem w (nsmul_mem hu 2)) u hu
  have h2 := AddChar.map_add_eq_mul ψ (-symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u)
    (symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u)
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at h2
  rw [phase, h2]
  congr 2
  rw [← symplOH_add_self, ← symplOH_add_right, XF.coe_nsmul, two_nsmul]

/- English proof (translation)
Establish `h : IsHalf e (intA D w • (u : WO S T))`. Rewrite `hu`, the goal using `[isHalf_iff]`. Rewrite using `[smul_comm, hu]`. Rewrite using `[phase, symplOH, half_orth he h hu, mul_zero, neg_zero, AddChar.map_zero_eq_one]`.
-/
theorem phase_half {e : AE D} (he : IsSplitIdem D e) (w : 𝓞 D.host.E) {u : XF S T} (hu : IsHalf e (u : WO S T)) :
    phase ψ w u = 1 := by
  have h : IsHalf e (intA D w • (u : WO S T)) := by
    rw [isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  rw [phase, symplOH, half_orth he h hu, mul_zero, neg_zero, AddChar.map_zero_eq_one]

/- English proof (translation)
Establish `h : (mt V g).map (infPart D) = 1` using `congrArg Units.val (MonoidHom.mem_ker.1 hg)`. Rewrite using `[← sub_eq_zero, ← smul_sub]`. Use `Matrix.ext fun i j => realIdem_mul_of_fin ?_` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]`. Use `(congrFun (congrFun h i) j).trans ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.map_one (infPart D) (infPart D).map_zero (infPart D).map_one]`. Both sides reduce to the same expression.
-/
theorem real_smul_mt {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) :
    realIdem D • mt V g = realIdem D • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : (mt V g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  rw [← sub_eq_zero, ← smul_sub]
  refine Matrix.ext fun i j => realIdem_mul_of_fin ?_
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (infPart D) (infPart D).map_zero (infPart D).map_one]
  rfl

/- English proof (translation)
Establish `h : (mt V g).map (finPart D) = 1` using `congrArg Units.val (MonoidHom.mem_ker.1 hg)`. Rewrite using `[← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero]`. Use `Matrix.ext fun i j => (realIdem_mul_of_real ?_).symm` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]`. Use `(congrFun (congrFun h i) j).trans ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.map_one (finPart D) (finPart D).map_zero (finPart D).map_one]`. Both sides reduce to the same expression.
-/
theorem fin_smul_mt {V : HSp D} {g : GA D V} (hg : g ∈ GinfC V) :
    (1 - realIdem D) • mt V g = (1 - realIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : (mt V g).map (finPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero]
  refine Matrix.ext fun i j => (realIdem_mul_of_real ?_).symm
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (finPart D) (finPart D).map_zero (finPart D).map_one]
  rfl

/- English proof (translation)
Establish `h1 : ∀ y : XF S T, (1 - realIdem D) • (y : WO S T) = y` using `fun y => by`. Rewrite using `[sub_smul, one_smul, mem_finSub_iff.1 y.fin, sub_zero]`. Apply `XF.ext` to reduce the goal to its premises. Rewrite using `[← h1 (rhoF S T (g, h) x), coe_rhoF, smul_actO (fin_smul_mt hg) (fin_smul_mt hh), h1]`.
-/
theorem rhoF_real {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) (x : XF S T) :
    rhoF S T (g, h) x = x := by
  have h1 : ∀ y : XF S T, (1 - realIdem D) • (y : WO S T) = y := fun y => by
    rw [sub_smul, one_smul, mem_finSub_iff.1 y.fin, sub_zero]
  apply XF.ext
  rw [← h1 (rhoF S T (g, h) x), coe_rhoF, smul_actO (fin_smul_mt hg) (fin_smul_mt hh), h1]

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Use `show finPart D (realIdem D * u i j) = 0`. Rewrite using `[RingHom.map_mul, finPart_realIdem, zero_mul]`.
-/
theorem real_smul_real (u : WO S T) : (realIdem D • u).map (finPart D) = 0 := by
  funext i j
  show finPart D (realIdem D * u i j) = 0
  rw [RingHom.map_mul, finPart_realIdem, zero_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Use `show infPart D ((1 - realIdem D) * u i j) = 0`. Rewrite using `[RingHom.map_mul, RingHom.map_sub, infPart_realIdem, RingHom.map_one, sub_self, zero_mul]`.
-/
theorem fin_smul_fin (u : WO S T) : ((1 - realIdem D) • u).map (infPart D) = 0 := by
  funext i j
  show infPart D ((1 - realIdem D) * u i j) = 0
  rw [RingHom.map_mul, RingHom.map_sub, infPart_realIdem, RingHom.map_one, sub_self, zero_mul]

/- English proof (translation)
Establish `h : algebraMap (AF D.host.F) (AE D) η • (mt V g - 1) = mt V g - 1` using `Matrix.ext fun i j => hg i j`. Rewrite using `[← sub_eq_zero, ← smul_sub, sub_smul, one_smul, h, sub_self]`.
-/
theorem off_smul_mt_place {V : HSp D} {η : AF D.host.F} {g : GA D V} (hg : SuppPl η V g) :
    (1 - algebraMap (AF D.host.F) (AE D) η) • mt V g =
      (1 - algebraMap (AF D.host.F) (AE D) η) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : algebraMap (AF D.host.F) (AE D) η • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, h, sub_self]

/- English proof (translation)
Use `show η ⊗ₜ[D.host.F] D.sp.cm.sig (1 : D.host.E) = _`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
theorem cA_algebraMap (η : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) η) = algebraMap (AF D.host.F) (AE D) η := by
  show η ⊗ₜ[D.host.F] D.sp.cm.sig (1 : D.host.E) = _
  rw [map_one]; rfl

/- English proof (translation)
Take `⟨⟨α, rfl, h1, h0⟩, hn⟩` from `h`. Establish `hα : α = singleV D.host.F v 1` using `GlobalTheory.SplitIdem.af_ext _ fun w => by`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[h1, GlobalTheory.SplitIdem.evalV_singleV_same]`.

Rewrite using `[h0 w hw, GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw]`. Establish `h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal` using `fun h2 => by`. Take `⟨e, e1, e2, e3, -⟩` from `GlobalTheory.SplitIdem.exists_split_idempotent D v h2`. Rewrite `e3` using `[← hα]`. Conclude with `hn ⟨e, ⟨e1, e2, v, _, ⟨α, rfl, h1, h0⟩, e3⟩, e3⟩`.

Take `⟨y, hy⟩` from `((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v 2).2 h2).exists_right_inv`. Rewrite `hy` using `[map_ofNat]`. Establish `hy' : (2 : Fv D.host.F v) * y = 1` using `congrArg Subtype.val hy`. Use `⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v y), ?_, ?_⟩` and prove the remaining obligations. Conclude with `AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v y, 1, rfl⟩`.

Rewrite using `[two_mul, ← map_add, ← map_add, ← two_mul, hy', hα]`. Both sides reduce to the same expression.
-/
theorem exists_half_of_nonSplit {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : NonSplitAt D v η) :
    ∃ a : AE D, finPart D a ∈ intAE D ∧ 2 * a = algebraMap (AF D.host.F) (AE D) η := by
  obtain ⟨⟨α, rfl, h1, h0⟩, hn⟩ := h
  have hα : α = singleV D.host.F v 1 := GlobalTheory.SplitIdem.af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h1, GlobalTheory.SplitIdem.evalV_singleV_same]
    · rw [h0 w hw, GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw]
  have h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal := fun h2 => by
    obtain ⟨e, e1, e2, e3, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
    rw [← hα] at e3
    exact hn ⟨e, ⟨e1, e2, v, _, ⟨α, rfl, h1, h0⟩, e3⟩, e3⟩
  obtain ⟨y, hy⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v 2).2 h2).exists_right_inv
  rw [map_ofNat] at hy
  have hy' : (2 : Fv D.host.F v) * y = 1 := congrArg Subtype.val hy
  refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v y), ?_, ?_⟩
  · exact AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v y, 1, rfl⟩
  · rw [two_mul, ← map_add, ← map_add, ← two_mul, hy', hα]
    rfl

/- English proof (translation)
Take `⟨β, rfl, h1, h0⟩` from `h`. Use `AddSubgroup.subset_closure ⟨β, fun w => ?_, 1, rfl⟩` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[h1]`.

Conclude with `one_mem _`. Rewrite using `[h0 w hw]`. Conclude with `zero_mem _`.
-/
theorem finPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : IsPlaceIdem D v η) :
    finPart D (algebraMap (AF D.host.F) (AE D) η) ∈ intAE D := by
  obtain ⟨β, rfl, h1, h0⟩ := h
  refine AddSubgroup.subset_closure ⟨β, fun w => ?_, 1, rfl⟩
  by_cases hw : w = v
  · subst hw; rw [h1]; exact one_mem _
  · rw [h0 w hw]; exact zero_mem _

/- English proof (translation)
Establish `H` using `isHeis_opF hψ S T hw`. Take `⟨U, hU, hf⟩` from `f.2.level`. Take `⟨N, hN, hNU⟩` from `hlev U hU`. Establish `hN2 : 0 < 2 * N` using `by omega`. Establish `hdiv : ∀ x : XF S T, (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • x) = x` using `fun x => by`.

Apply `XF.ext` to reduce the goal to its premises. Use `show (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • (x : WO S T)) = x`. Rewrite using `[smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hN2]`. Use `⟨(latF S T ΛS ΛT).comap ((2 * N) • LinearMap.id), idx_latF_ne_zero hS hT _ hN2 fun b hb => hb, fun a _ ha => ?_⟩` and prove the remaining obligations. Take `⟨a', rfl⟩ : ∃ a', a = (2 * N) • a'` from `⟨_, (hdiv a).symm⟩`.

Establish `ha' : a' ∈ latF S T ΛS ΛT` using `(hA a').2 fun t ht => by`. Rewrite using `[← hdiv t, H.nsmul_right, ← H.nsmul_left]`. Use `ha _ ?_` and prove the remaining obligations. Use `show (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • t) ∈ latF S T ΛS ΛT`. Rewrite using `[hdiv]`.

Conclude with `ht`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_opF, hf _ (by rw [XF.coe_nsmul, mul_comm, mul_smul]; exact hNU _ (nsmul_mem ha' 2)) (XF.fin _), mul_smul, phase_two hA w (nsmul_mem ha' N), one_smul]`.
-/
theorem smooth_theta (hψ : IsCharAF D.host.F ψ) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {w : 𝓞 D.host.E} (hw : w + sgO D w = 1) (hA : SelfDual (gamF ψ S T) (latF S T ΛS ΛT))
    (hlev : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧
      ∀ u ∈ latO S T ΛS ΛT fun _ => True, N • u ∈ U) (f : thetaSub ψ S T) :
    ∃ B : Submodule (𝓞 D.host.E) (XF S T), idx (latF S T ΛS ΛT) B ≠ 0 ∧
      ∀ a ∈ latF S T ΛS ΛT, (∀ t ∈ B, gamF ψ S T a t = 1) → opF hψ S T w a f = f := by
  have H := isHeis_opF hψ S T hw
  obtain ⟨U, hU, hf⟩ := f.2.level
  obtain ⟨N, hN, hNU⟩ := hlev U hU
  have hN2 : 0 < 2 * N := by omega
  have hdiv : ∀ x : XF S T, (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • x) = x := fun x => by
    apply XF.ext
    show (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • (x : WO S T)) = x
    rw [smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hN2]
  refine ⟨(latF S T ΛS ΛT).comap ((2 * N) • LinearMap.id), idx_latF_ne_zero hS hT _ hN2 fun b hb => hb,
    fun a _ ha => ?_⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = (2 * N) • a' := ⟨_, (hdiv a).symm⟩
  have ha' : a' ∈ latF S T ΛS ΛT := (hA a').2 fun t ht => by
    rw [← hdiv t, H.nsmul_right, ← H.nsmul_left]
    refine ha _ ?_
    show (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • t) ∈ latF S T ΛS ΛT
    rw [hdiv]
    exact ht
  apply Subtype.ext
  rw [coe_opF, hf _ (by rw [XF.coe_nsmul, mul_comm, mul_smul]; exact hNU _ (nsmul_mem ha' 2)) (XF.fin _),
    mul_smul, phase_two hA w (nsmul_mem ha' N), one_smul]

end GlobalTheory.FinWeilO

end
