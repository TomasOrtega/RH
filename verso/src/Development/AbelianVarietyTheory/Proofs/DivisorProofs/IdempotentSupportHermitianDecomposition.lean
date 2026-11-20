import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatSmulLe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.StdReps

section General

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le`. Consider the case `exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le`. Consider the case `(apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le ..)`.
-/
theorem exists_nat_smul_mem (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hsp : Submodule.span E (L' : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ x ∈ L, (c : E) • x ∈ L' := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le
  | exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le
  | (apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le ..)

/- English proof (translation)
The claim follows from `Submodule.fg_span (Set.finite_range _)`.
-/
theorem fg_colLat (B : GL (Fin n) E) : (colLat B).FG :=
  Submodule.fg_span (Set.finite_range _)

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : x = ∑ j, ((B⁻¹).1 *ᵥ x) j • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) E) a j)`. Establish `e : x = B.1 *ᵥ ((B⁻¹).1 *ᵥ x)`. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`.

Use `conv_lhs => rw [e]`. Use function extensionality and compare the values at `a`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Rewrite using `[hx]`.

Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨j, rfl⟩`.
-/
theorem span_colLat (B : GL (Fin n) E) : Submodule.span E (colLat B : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, ((B⁻¹).1 *ᵥ x) j • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) E) a j) := by
    have e : x = B.1 *ᵥ ((B⁻¹).1 *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    conv_lhs => rw [e]
    funext a
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hx]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Submodule.subset_span ⟨j, rfl⟩

end General

variable {D : D7}

def stabGL {R : Type} [CommRing R] {m : ℕ} (H : Set (Fin m → R)) : Subgroup (GL (Fin m) R) where
  carrier := {g | ∀ v, v ∈ H ↔ g.1 *ᵥ v ∈ H}
  one_mem' := fun v => by rw [Units.val_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb v => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb v).trans (ha _)
  inv_mem' := fun {a} ha v => by
    have := ha ((a⁻¹).1 *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm

def stabG (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Subgroup (GA D V) :=
  (stabGL (Formalism.L2.Herm.hatL (F := D.host.F) M : Set (Fin V.rank → Formalism.IndefR.Lev.EAf D))).comap (Formalism.IndefR.Lev.finE V)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hl` using `(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1`. Establish `hcong : ∀ z ∈ Formalism.L2.Herm.hatL (F` using `D.host.F) (GlobalTheory.Member.latC V), ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.Member.latC V), (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c * c) • y := by`. Unfold `GlobalTheory.Member.FinCong at ha`. Rewrite `ha` using `[hl]`. Conclude with `GlobalTheory.PrincInLevel.cong_swap _ _ _ ha`.

Introduce `z hz`. Take `⟨y, hy, e⟩` from `hcong _ (GlobalTheory.LevSplit.hatL_smul _ _ c h1 z hz)`. Establish `hcE : IsUnit (c : D.host.E)` using `(Nat.cast_ne_zero.2 hc.ne').isUnit`. Establish `hu : IsUnit (c : Formalism.IndefR.Lev.EAf D)`. Use `hcE.map (eToEAf D)` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `e2 : (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c : Formalism.IndefR.Lev.EAf D) • y`. Use `(hu.smul_left_cancel).1 ?_` and prove the remaining obligations. Rewrite using `[smul_sub, ← Matrix.mulVec_smul, e, ← Nat.cast_smul_eq_nsmul (Formalism.IndefR.Lev.EAf D), Nat.cast_mul, mul_smul]`. Rewrite `e2` using `[sub_eq_iff_eq_add']`.

Rewrite using `[e2]`. Conclude with `Submodule.add_mem _ hz (GlobalTheory.LevSplit.hatL_smul _ _ c h2 y hy)`.
-/
theorem mulVec_mem_of_finCong (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ) (hc : 0 < c)
    (h1 : ∀ x ∈ M, (c : D.host.E) • x ∈ GlobalTheory.Member.latC V)
    (h2 : ∀ x ∈ GlobalTheory.Member.latC V, (c : D.host.E) • x ∈ M) (a : GA D V) (ha : GlobalTheory.Member.FinCong V (c * c) a) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M,
      (Formalism.IndefR.Lev.finE V a).1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  have hl := (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hcong : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.Member.latC V),
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.Member.latC V),
        (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c * c) • y := by
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap _ _ _ ha
  intro z hz
  obtain ⟨y, hy, e⟩ := hcong _ (GlobalTheory.LevSplit.hatL_smul _ _ c h1 z hz)
  have hcE : IsUnit (c : D.host.E) := (Nat.cast_ne_zero.2 hc.ne').isUnit
  have hu : IsUnit (c : Formalism.IndefR.Lev.EAf D) := by
    have := hcE.map (eToEAf D)
    rwa [map_natCast] at this
  have e2 : (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c : Formalism.IndefR.Lev.EAf D) • y := by
    refine (hu.smul_left_cancel).1 ?_
    rw [smul_sub, ← Matrix.mulVec_smul, e, ← Nat.cast_smul_eq_nsmul (Formalism.IndefR.Lev.EAf D), Nat.cast_mul, mul_smul]
  rw [sub_eq_iff_eq_add'] at e2
  rw [e2]
  exact Submodule.add_mem _ hz (GlobalTheory.LevSplit.hatL_smul _ _ c h2 y hy)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `v`. Use `⟨mulVec_mem_of_finCong V M c hc h1 h2 a ha v, fun hv => ?_⟩` and prove the remaining obligations. Use `mulVec_mem_of_finCong V M c hc h1 h2 a⁻¹ (GlobalTheory.Member.PrincLevel.finCong_inv ha) _ hv` as an intermediate fact. Rewrite `this` using `[map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem mem_stabG_of_finCong (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ) (hc : 0 < c)
    (h1 : ∀ x ∈ M, (c : D.host.E) • x ∈ GlobalTheory.Member.latC V)
    (h2 : ∀ x ∈ GlobalTheory.Member.latC V, (c : D.host.E) • x ∈ M) (a : GA D V) (ha : GlobalTheory.Member.FinCong V (c * c) a) :
    a ∈ stabG V M := by
  intro v
  refine ⟨mulVec_mem_of_finCong V M c hc h1 h2 a ha v, fun hv => ?_⟩
  have := mulVec_mem_of_finCong V M c hc h1 h2 a⁻¹ (GlobalTheory.Member.PrincLevel.finCong_inv ha) _ hv
  rwa [map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `D V fr S hS x hx`. Take `⟨-, -, hfg, hsp, -⟩` from `GlobalTheory.Member.latHat_eq_hat_and_gram D V`. Take `⟨c1, hc1, h1⟩` from `exists_nat_smul_mem (colLat fr) (GlobalTheory.Member.latC V) (fg_colLat fr) hsp`. Take `⟨c2, hc2, h2⟩` from `exists_nat_smul_mem (GlobalTheory.Member.latC V) (colLat fr) hfg (span_colLat fr)`. Establish `h1' : ∀ y ∈ colLat fr, ((c1 * c2 : ℕ) : D.host.E) • y ∈ GlobalTheory.Member.latC V` using `fun y hy => by`.

Rewrite using `[Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c2]`. Conclude with `(GlobalTheory.Member.latC V).toAddSubmonoid.nsmul_mem (h1 y hy) c2`. Establish `h2' : ∀ y ∈ GlobalTheory.Member.latC V, ((c1 * c2 : ℕ) : D.host.E) • y ∈ colLat fr` using `fun y hy => by`. Rewrite using `[Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c1]`. Conclude with `(colLat fr).toAddSubmonoid.nsmul_mem (h2 y hy) c1`.

Establish `hc : 0 < c1 * c2` using `Nat.mul_pos hc1 hc2`. Set `J' : Subgroup (Formalism.IndefR.Bridge.Gf V)` to `(GfC V ⊓ stabG V (colLat fr)).map (finHom V).rangeRestrict`. Establish `hK : ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V ((c1 * c2) * (c1 * c2)) k → Formalism.IndefR.FWT.fin V k ∈ J'` using `fun k hk hck => ⟨k, ⟨hk, mem_stabG_of_finCong V (colLat fr) _ hc h1' h2' k hck⟩, rfl⟩`. Establish `hbad : 0 < ∏ q ∈ S, q` using `Finset.prod_pos fun q hq => (hS q hq).pos`. Take `⟨h, ⟨hh, hs⟩, γ, k, e⟩` from `GlobalTheory.SplitReps.exists_split_rep V (Nat.mul_pos hc hc) hK hbad (Formalism.IndefR.FWT.fin V x)`.

Take `⟨k0, ⟨hk0, hk0s⟩, hk0e⟩` from `Subgroup.mem_map.1 k.2`. Take `⟨-, e0, P, he0, hP, hsupp⟩` from `GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs`. Take `⟨γE, hU, hγ⟩` from `γ.2`. Establish `hm : matHom V γ.1 = Formalism.UG.bc (inclR (F` using `D.host.F) (AF D.host.F)) γE := hγ.symm`. Establish `hfγ : finHom V γ.1 = Formalism.UG.bc (inclR (F` using `D.host.F) (Af D.host.F)) γE := by`.

Rewrite using `[finHom, MonoidHom.comp_apply, hm]`. Conclude with `GlobalTheory.HLatMove.bc_map_bc_inclR _ _`. Establish `ef : finHom V x = finHom V γ.1 * finHom V h * finHom V k0`. Use `congrArg Subtype.val e` as an intermediate fact. Rewrite `this` using `[← hk0e]`.

Conclude with `this`. Use `⟨γE, h, k0, hU, hh, ⟨P, e0, he0, hsupp, fun w hw q hq hqw => hP w hw ?_⟩, hk0, hk0s, ?_⟩` and prove the remaining obligations. Take `⟨m, hm'⟩` from `Finset.dvd_prod_of_mem (fun q : ℕ => q) hq`. Rewrite using `[hm', Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hqw`.

Establish `eE : Formalism.IndefR.Lev.finE V x = Formalism.IndefR.Lev.finE V γ.1 * Formalism.IndefR.Lev.finE V h * Formalism.IndefR.Lev.finE V k0`. Simplify using `only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, ef, map_mul]`. Establish `eγ : (Formalism.IndefR.Lev.finE V γ.1).1 = γE.1.map (eToEAf D)`. Simplify using `only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, hfγ]`. Use extensionality with `i j`.

Both sides reduce to the same expression. Rewrite using `[eE, Units.val_mul, Units.val_mul, eγ]`.
-/
theorem exists_rep_std : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (S : Finset ℕ), (∀ q ∈ S, q.Prime) →
    ∀ x : GA D V, x ∈ GfC V →
    ∃ (γ : GL (Fin V.rank) D.host.E) (h k : GA D V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram ∧ h ∈ GfC V ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) ∧
      k ∈ GfC V ∧ (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) ∧
      (Formalism.IndefR.Lev.finE V x).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (Formalism.IndefR.Lev.finE V k).1 := by
  intro D V fr S hS x hx
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨c1, hc1, h1⟩ := exists_nat_smul_mem (colLat fr) (GlobalTheory.Member.latC V) (fg_colLat fr) hsp
  obtain ⟨c2, hc2, h2⟩ := exists_nat_smul_mem (GlobalTheory.Member.latC V) (colLat fr) hfg (span_colLat fr)
  have h1' : ∀ y ∈ colLat fr, ((c1 * c2 : ℕ) : D.host.E) • y ∈ GlobalTheory.Member.latC V := fun y hy => by
    rw [Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c2]
    exact (GlobalTheory.Member.latC V).toAddSubmonoid.nsmul_mem (h1 y hy) c2
  have h2' : ∀ y ∈ GlobalTheory.Member.latC V, ((c1 * c2 : ℕ) : D.host.E) • y ∈ colLat fr := fun y hy => by
    rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c1]
    exact (colLat fr).toAddSubmonoid.nsmul_mem (h2 y hy) c1
  have hc : 0 < c1 * c2 := Nat.mul_pos hc1 hc2
  let J' : Subgroup (Formalism.IndefR.Bridge.Gf V) := (GfC V ⊓ stabG V (colLat fr)).map (finHom V).rangeRestrict
  have hK : ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V ((c1 * c2) * (c1 * c2)) k → Formalism.IndefR.FWT.fin V k ∈ J' :=
    fun k hk hck => ⟨k, ⟨hk, mem_stabG_of_finCong V (colLat fr) _ hc h1' h2' k hck⟩, rfl⟩
  have hbad : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (hS q hq).pos
  obtain ⟨h, ⟨hh, hs⟩, γ, k, e⟩ :=
    GlobalTheory.SplitReps.exists_split_rep V (Nat.mul_pos hc hc) hK hbad (Formalism.IndefR.FWT.fin V x)
  obtain ⟨k0, ⟨hk0, hk0s⟩, hk0e⟩ := Subgroup.mem_map.1 k.2
  obtain ⟨-, e0, P, he0, hP, hsupp⟩ := GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs
  obtain ⟨γE, hU, hγ⟩ := γ.2
  have hm : matHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γE := hγ.symm
  have hfγ : finHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE := by
    rw [finHom, MonoidHom.comp_apply, hm]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  have ef : finHom V x = finHom V γ.1 * finHom V h * finHom V k0 := by
    have := congrArg Subtype.val e
    rw [← hk0e] at this
    exact this
  refine ⟨γE, h, k0, hU, hh, ⟨P, e0, he0, hsupp, fun w hw q hq hqw => hP w hw ?_⟩, hk0, hk0s, ?_⟩
  · obtain ⟨m, hm'⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
    rw [hm', Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hqw
  · have eE : Formalism.IndefR.Lev.finE V x = Formalism.IndefR.Lev.finE V γ.1 * Formalism.IndefR.Lev.finE V h * Formalism.IndefR.Lev.finE V k0 := by
      simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, ef, map_mul]
    have eγ : (Formalism.IndefR.Lev.finE V γ.1).1 = γE.1.map (eToEAf D) := by
      simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, hfγ]
      ext i j
      rfl
    rw [eE, Units.val_mul, Units.val_mul, eγ]

end GlobalTheory.FunObj.StdReps
