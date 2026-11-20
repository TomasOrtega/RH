import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntPolyEsymmEqPowerSumMultiset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OpOfAevalExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EsymmInvMulProd
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.Cong.SphOpsProof

open GlobalTheory.LFun Formalism.UG GlobalTheory.Cong.OpPoly

def zq (q : ℕ) (hq : q ≠ 0) : Subring ℂ where
  carrier := {x | ∃ (m : ℤ) (e : ℕ), x = (m : ℂ) / (q : ℂ) ^ e}
  mul_mem' := by
    rintro _ _ ⟨m, e, rfl⟩ ⟨m', e', rfl⟩
    refine ⟨m * m', e + e', ?_⟩
    push_cast
    rw [pow_add, div_mul_div_comm]
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, e, rfl⟩ ⟨m', e', rfl⟩
    have h0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    refine ⟨m * (q : ℤ) ^ e' + m' * (q : ℤ) ^ e, e + e', ?_⟩
    push_cast
    rw [pow_add]
    field_simp
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨m, e, rfl⟩
    exact ⟨-m, e, by push_cast; ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(q : ℤ) ^ k, 0, by push_cast; simp⟩`.
-/
theorem natPow_mem_zq {q : ℕ} (hq : q ≠ 0) (k : ℕ) : (q : ℂ) ^ k ∈ zq q hq :=
  ⟨(q : ℤ) ^ k, 0, by push_cast; simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, k, by simp⟩`.
-/
theorem inv_natPow_mem_zq {q : ℕ} (hq : q ≠ 0) (k : ℕ) : ((q : ℂ) ^ k)⁻¹ ∈ zq q hq :=
  ⟨1, k, by simp⟩

/- English proof (translation)
Rewrite using `[Finsupp.single_apply]`. Use `split_ifs`. Conclude with `hc`. Conclude with `S.zero_mem`.
-/
theorem single_mem {G : Type} (S : Subring ℂ) (x : G) {c : ℂ} (hc : c ∈ S) (g : G) : Finsupp.single x c g ∈ S := by
  classical
  rw [Finsupp.single_apply]
  split_ifs
  · exact hc
  · exact S.zero_mem

/- English proof (translation)
Simplify using `only [OpPoly.conv, Finsupp.sum, Finsupp.finset_sum_apply]`. Use `Subring.sum_mem _ fun g _ => Subring.sum_mem _ fun h _ => ?_` and prove the remaining obligations. Conclude with `single_mem S _ (S.mul_mem (hF g) (hf h)) x`.
-/
theorem conv_mem {G : Type} [Group G] (S : Subring ℂ) (F f : G →₀ ℂ) (hF : ∀ g, F g ∈ S) (hf : ∀ g, f g ∈ S) (x : G) :
    OpPoly.conv F f x ∈ S := by
  classical
  simp only [OpPoly.conv, Finsupp.sum, Finsupp.finset_sum_apply]
  refine Subring.sum_mem _ fun g _ => Subring.sum_mem _ fun h _ => ?_
  exact single_mem S _ (S.mul_mem (hF g) (hf h)) x

/- English proof (translation)
Simplify using `[opOf]`.
-/
theorem opOf_zero_vec {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (F : G →₀ ℂ) :
    opOf ρ F 0 = 0 := by
  simp [opOf]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Use `⟨Finsupp.single 1 (a : ℂ), single_mem S 1 (intCast_mem S a), fun V _ _ ρ z v _ => ?_⟩` and prove the remaining obligations. Simplify using `[opOf]`. Consider the case `add p q hp hq`.

Take `⟨F₁, h₁, e₁⟩` from `hp`. Take `⟨F₂, h₂, e₂⟩` from `hq`. Use `⟨F₁ + F₂, fun g => ?_, fun V _ _ ρ z v hz => ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply]`. Conclude with `S.add_mem (h₁ g) (h₂ g)`.

Rewrite using `[opOf_add, e₁ V ρ z v hz, e₂ V ρ z v hz, map_add, add_smul]`. Consider the case `mul_X p i hp`. Take `⟨F, hF, e⟩` from `hp`. Use `⟨OpPoly.conv F (f i), conv_mem S F (f i) hF (hf i), fun V _ _ ρ z v hz => ?_⟩` and prove the remaining obligations. Rewrite using `[opOf_conv, hz i, opOf_smul, e V ρ z v hz, map_mul, MvPolynomial.aeval_X, smul_smul, mul_comm]`.
-/
theorem exists_poly_op (S : Subring ℂ) {G I : Type} [Group G] (f : I → G →₀ ℂ) (hf : ∀ i g, f i g ∈ S)
    (P : MvPolynomial I ℤ) : ∃ F : G →₀ ℂ, (∀ g, F g ∈ S) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (z : I → ℂ) (v : V),
        (∀ i, opOf ρ (f i) v = z i • v) → opOf ρ F v = MvPolynomial.aeval z P • v := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Finsupp.single 1 (a : ℂ), single_mem S 1 (intCast_mem S a), fun V _ _ ρ z v _ => ?_⟩
    simp [opOf]
  | add p q hp hq =>
    obtain ⟨F₁, h₁, e₁⟩ := hp
    obtain ⟨F₂, h₂, e₂⟩ := hq
    refine ⟨F₁ + F₂, fun g => ?_, fun V _ _ ρ z v hz => ?_⟩
    · rw [Finsupp.add_apply]
      exact S.add_mem (h₁ g) (h₂ g)
    · rw [opOf_add, e₁ V ρ z v hz, e₂ V ρ z v hz, map_add, add_smul]
  | mul_X p i hp =>
    obtain ⟨F, hF, e⟩ := hp
    refine ⟨OpPoly.conv F (f i), conv_mem S F (f i) hF (hf i), fun V _ _ ρ z v hz => ?_⟩
    rw [opOf_conv, hz i, opOf_smul, e V ρ z v hz, map_mul, MvPolynomial.aeval_X, smul_smul, mul_comm]

/- English proof (translation)
Set `s` to `(Formalism.UG.P.finite_support_cosets hK hh.2).toFinset`. Use `⟨∑ c ∈ s, Finsupp.single c.out (h c.out), fun g => ?_, fun V _ _ ρ x => ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.finset_sum_apply]`. Conclude with `Subring.sum_mem _ fun c _ => single_mem S _ (hS _) g`. Rewrite using `[← opHom_apply ρ x, map_sum, heckeVec, finsum_eq_sum_of_support_subset (s := s)]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[opHom_apply, opOf_single]`. Introduce `c hc`. Simplify using `only [s, Set.Finite.coe_toFinset, Set.mem_setOf_eq]`. Conclude with `fun h0 => hc (by simp [h0])`.
-/
theorem exists_finsupp_heckeVec (S : Subring ℂ) {G : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K)
    {h : G → ℂ} (hh : h ∈ Hecke ℂ K) (hS : ∀ g, h g ∈ S) :
    ∃ F : G →₀ ℂ, (∀ g, F g ∈ S) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V),
      opOf ρ F x = heckeVec ρ K h x := by
  classical
  let s := (Formalism.UG.P.finite_support_cosets hK hh.2).toFinset
  refine ⟨∑ c ∈ s, Finsupp.single c.out (h c.out), fun g => ?_, fun V _ _ ρ x => ?_⟩
  · rw [Finsupp.finset_sum_apply]
    exact Subring.sum_mem _ fun c _ => single_mem S _ (hS _) g
  · rw [← opHom_apply ρ x, map_sum, heckeVec, finsum_eq_sum_of_support_subset (s := s)]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [opHom_apply, opOf_single]
    · intro c hc
      simp only [s, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      exact fun h0 => hc (by simp [h0])

end GlobalTheory.Cong.SphOpsProof

namespace GlobalTheory.Cong.SphOpsProof

open GlobalTheory.LFun Formalism.UG GlobalTheory.Cong.OpPoly

/- English proof (translation)
Rewrite using `[normV, qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem normV_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : normV w = qV E w := by
  rw [normV, qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Establish `h1` using `ConjPlace.apply_heckeVec_shift (Tj_mem_hecke (n := a) hp a).1 hv.2.1 (ConjPlace.dGL a ϖ a)`. Rewrite `h1` using `[funext (ConjPlace.Tj_shift_self _ ϖ), ExSatGL.heckeVec_Tj_zero ρ _ hv.2.1, hv.2.2.2 _ hp a le_rfl]`. Establish `h2 : v = satEig (qV E w) a B a • ρ (ConjPlace.dGL a ϖ a)⁻¹ v`. Rewrite using `[← map_smul, ← h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Establish `h0 : satEig (qV E w) a B a ≠ 0` using `fun e => hv.1 (by rw [h2, e, zero_smul])`.

Use `⟨h0, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [h2]`. Rewrite using `[smul_smul, inv_mul_cancel₀ h0, one_smul]`.
-/
theorem inv_center_act {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V)
    (ϖ : (w.adicCompletion E)ˣ) (hp : IsUnifV E w (ϖ : w.adicCompletion E)) {B : Multiset ℂˣ} {v : V}
    (hv : IsSatVecGL w ρ v B) :
    satEig (qV E w) a B a ≠ 0 ∧ ρ (ConjPlace.dGL a ϖ a)⁻¹ v = (satEig (qV E w) a B a)⁻¹ • v := by
  have h1 := ConjPlace.apply_heckeVec_shift (Tj_mem_hecke (n := a) hp a).1 hv.2.1 (ConjPlace.dGL a ϖ a)
  rw [funext (ConjPlace.Tj_shift_self _ ϖ), ExSatGL.heckeVec_Tj_zero ρ _ hv.2.1, hv.2.2.2 _ hp a le_rfl] at h1
  have h2 : v = satEig (qV E w) a B a • ρ (ConjPlace.dGL a ϖ a)⁻¹ v := by
    rw [← map_smul, ← h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h0 : satEig (qV E w) a B a ≠ 0 := fun e => hv.1 (by rw [h2, e, zero_smul])
  refine ⟨h0, ?_⟩
  conv_rhs => rw [h2]
  rw [smul_smul, inv_mul_cancel₀ h0, one_smul]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat`. Consider the case `exact _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat`. Consider the case `(apply _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat ..)`.
-/
theorem esymm_inv_algSat {q : ℕ} (hq : q ≠ 0) {a : ℕ} {B : Multiset ℂˣ} (hB : B.card = a) {j : ℕ} (hj : j ≤ a)
    (hne : satEig q a B a ≠ 0) :
    ((UpperTheory.V.Af.algSat a q B).map (·⁻¹)).esymm j =
      (UpperTheory.V.Af.algSat a q B).esymm (a - j) * (((q : ℂ) ^ a.choose 2)⁻¹ * (satEig q a B a)⁻¹) := by
  first
  | exact @_root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat
  | exact _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat
  | (apply _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat <;> assumption)
  | (intros; apply _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ElementarySymmetricInverse.esymm_inv_algSat ..)

/- English proof (translation)
Introduce `E _ _ w a`. Use `⟨fun σ h => GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred h, fun n => ?_⟩` and prove the remaining obligations. Establish `hq : qV E w ≠ 0` using `qV_ne_zero w`. Set `S` to `zq (qV E w) hq`. Take `⟨p, hp⟩` from `exists_isUnifV w`.

Take `⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p` from `⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩`. Establish `hTS : ∀ j g, Tj ℂ a (Ov E w) (ϖ : w.adicCompletion E) j g ∈ S` using `fun j g => by classical`. Rewrite using `[ConjPlace.Tj_apply]`. Use `split_ifs`. Conclude with `S.one_mem`.

Conclude with `S.zero_mem`. Use `choose T hT hTop using fun j => exists_finsupp_heckeVec S (Final.GLintComm E w a) (Tj_mem_hecke (n := a) hp j) (hTS j)`. Set `fP : ℕ → GL (Fin a) (w.adicCompletion E) →₀ ℂ` to `fun j => OpPoly.conv (Finsupp.single 1 ((qV E w : ℂ) ^ j.choose 2)) (T j)`. Establish `hfP : ∀ j g, fP j g ∈ S` using `fun j => conv_mem S _ _ (single_mem S 1 (natPow_mem_zq hq _)) (hT j)`. Establish `actP : ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), HasSatGL w σ.ρ B → ∀ v ∈ fixed σ.ρ (KGL w a), ∀ j ≤ a, opOf σ.ρ (fP j) v = (UpperTheory.V.Af.algSat a (qV E w) B).esymm j • v`.

Introduce `σ B hB v hv j hj`. Distinguish the cases in `h0 : v = 0`. Substitute `h0` using the available equality. Rewrite using `[opOf_zero_vec, smul_zero]`. Rewrite using `[opOf_conv, hTop j σ.V σ.ρ v, (hB.2 v hv h0).2.2.2 _ hp j hj, opOf_single, map_one, Module.End.one_apply, smul_smul, UpperTheory.V.Af.satEig_eq_algSat hq, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hq)), one_mul]`.

Set `fN : Fin (a + 1) → GL (Fin a) (w.adicCompletion E) →₀ ℂ` to `fun j => OpPoly.conv (Finsupp.single (ConjPlace.dGL a ϖ a)⁻¹ ((qV E w : ℂ) ^ a.choose 2)⁻¹) (fP (a - j))`. Establish `hfN : ∀ j g, fN j g ∈ S` using `fun j => conv_mem S _ _ (single_mem S _ (inv_natPow_mem_zq hq _)) (hfP _)`. Establish `actN : ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), HasSatGL w σ.ρ B → ∀ v ∈ fixed σ.ρ (KGL w a), ∀ j : Fin (a + 1), opOf σ.ρ (fN j) v = ((UpperTheory.V.Af.algSat a (qV E w) B).map (·⁻¹)).esymm j • v`. Introduce `σ B hB v hv j`. Distinguish the cases in `h0 : v = 0`.

Substitute `h0` using the available equality. Rewrite using `[opOf_zero_vec, smul_zero]`. Take `⟨hne, hinv⟩` from `inv_center_act σ.ρ ϖ hp (hB.2 v hv h0)`. Rewrite using `[opOf_conv, actP σ B hB v hv _ (Nat.sub_le _ _), opOf_smul, opOf_single, hinv, smul_smul, smul_smul, esymm_inv_algSat hq hB.card (Nat.lt_succ_iff.1 j.2) hne, mul_assoc]`. Establish `hcard : ∀ B : Multiset ℂˣ, B.card = a → (UpperTheory.V.Af.algSat a (qV E w) B).card = a` using `fun B h => by`.

Simplify using `[UpperTheory.V.Af.algSat, h]`. Establish `hfin : ∀ F : GL (Fin a) (w.adicCompletion E) →₀ ℂ, (∀ g, F g ∈ S) → ∀ g, ∃ (m : ℤ) (e : ℕ), F g = (m : ℂ) / ((normV w : ℕ) : ℂ) ^ e`. Introduce `F hF g`. Take `⟨m, e, he⟩` from `hF g`. Conclude with `⟨m, e, by rw [normV_eq]; exact he⟩`.

Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Use `⟨Finsupp.single 1 (a : ℂ), hfin _ (single_mem S 1 (natCast_mem S a)), fun σ B hB v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[opOf_single, map_one, Module.End.one_apply, normV_eq]`. Simplify using `[hcard B hB.card]`.

Take `⟨m, rfl | rfl⟩` from `Int.eq_nat_or_neg n`. Establish `hm : 1 ≤ m` using `by omega`. Take `⟨P, hP⟩` from `GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq a m hm`. Take `⟨F, hF, hFa⟩` from `exists_poly_op S (fun j : Fin (a + 1) => fP j) (fun j => hfP j) P`. Use `⟨F, hfin F hF, fun σ B hB v hv => ?_⟩` and prove the remaining obligations.

Rewrite using `[hFa σ.V σ.ρ (fun j => (UpperTheory.V.Af.algSat a (qV E w) B).esymm j) v (fun j => actP σ B hB v hv j (Nat.lt_succ_iff.1 j.2)), hP _ (hcard B hB.card), normV_eq]`. Simplify using `only [zpow_natCast]`. Establish `hm : 1 ≤ m` using `by omega`. Take `⟨P, hP⟩` from `GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq a m hm`. Take `⟨F, hF, hFa⟩` from `exists_poly_op S fN hfN P`.

Use `⟨F, hfin F hF, fun σ B hB v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[hFa σ.V σ.ρ (fun j => ((UpperTheory.V.Af.algSat a (qV E w) B).map (·⁻¹)).esymm j) v (actN σ B hB v hv), hP _ (by rw [Multiset.card_map]; exact hcard B hB.card), normV_eq, Multiset.map_map]`. Use `congr 2`. Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `[zpow_neg, zpow_natCast, inv_pow]`.
-/
theorem sphOps : SphOps := by
  intro E _ _ w a
  refine ⟨fun σ h => GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred h, fun n => ?_⟩
  have hq : qV E w ≠ 0 := qV_ne_zero w
  let S := zq (qV E w) hq
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  have hTS : ∀ j g, Tj ℂ a (Ov E w) (ϖ : w.adicCompletion E) j g ∈ S := fun j g => by
    classical
    rw [ConjPlace.Tj_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  choose T hT hTop using fun j =>
    exists_finsupp_heckeVec S (Final.GLintComm E w a) (Tj_mem_hecke (n := a) hp j) (hTS j)
  let fP : ℕ → GL (Fin a) (w.adicCompletion E) →₀ ℂ := fun j =>
    OpPoly.conv (Finsupp.single 1 ((qV E w : ℂ) ^ j.choose 2)) (T j)
  have hfP : ∀ j g, fP j g ∈ S := fun j => conv_mem S _ _ (single_mem S 1 (natPow_mem_zq hq _)) (hT j)
  have actP : ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), HasSatGL w σ.ρ B →
      ∀ v ∈ fixed σ.ρ (KGL w a), ∀ j ≤ a, opOf σ.ρ (fP j) v = (UpperTheory.V.Af.algSat a (qV E w) B).esymm j • v := by
    intro σ B hB v hv j hj
    by_cases h0 : v = 0
    · subst h0; rw [opOf_zero_vec, smul_zero]
    rw [opOf_conv, hTop j σ.V σ.ρ v, (hB.2 v hv h0).2.2.2 _ hp j hj, opOf_single, map_one, Module.End.one_apply,
      smul_smul, UpperTheory.V.Af.satEig_eq_algSat hq, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hq)), one_mul]
  let fN : Fin (a + 1) → GL (Fin a) (w.adicCompletion E) →₀ ℂ := fun j =>
    OpPoly.conv (Finsupp.single (ConjPlace.dGL a ϖ a)⁻¹ ((qV E w : ℂ) ^ a.choose 2)⁻¹) (fP (a - j))
  have hfN : ∀ j g, fN j g ∈ S := fun j => conv_mem S _ _ (single_mem S _ (inv_natPow_mem_zq hq _)) (hfP _)
  have actN : ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), HasSatGL w σ.ρ B →
      ∀ v ∈ fixed σ.ρ (KGL w a), ∀ j : Fin (a + 1),
        opOf σ.ρ (fN j) v = ((UpperTheory.V.Af.algSat a (qV E w) B).map (·⁻¹)).esymm j • v := by
    intro σ B hB v hv j
    by_cases h0 : v = 0
    · subst h0; rw [opOf_zero_vec, smul_zero]
    obtain ⟨hne, hinv⟩ := inv_center_act σ.ρ ϖ hp (hB.2 v hv h0)
    rw [opOf_conv, actP σ B hB v hv _ (Nat.sub_le _ _), opOf_smul, opOf_single, hinv, smul_smul, smul_smul,
      esymm_inv_algSat hq hB.card (Nat.lt_succ_iff.1 j.2) hne, mul_assoc]
  have hcard : ∀ B : Multiset ℂˣ, B.card = a → (UpperTheory.V.Af.algSat a (qV E w) B).card = a := fun B h => by
    simp [UpperTheory.V.Af.algSat, h]
  have hfin : ∀ F : GL (Fin a) (w.adicCompletion E) →₀ ℂ, (∀ g, F g ∈ S) →
      ∀ g, ∃ (m : ℤ) (e : ℕ), F g = (m : ℂ) / ((normV w : ℕ) : ℂ) ^ e := by
    intro F hF g
    obtain ⟨m, e, he⟩ := hF g
    exact ⟨m, e, by rw [normV_eq]; exact he⟩
  by_cases hn : n = 0
  · subst hn
    refine ⟨Finsupp.single 1 (a : ℂ), hfin _ (single_mem S 1 (natCast_mem S a)), fun σ B hB v hv => ?_⟩
    rw [opOf_single, map_one, Module.End.one_apply, normV_eq]
    simp [hcard B hB.card]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have hm : 1 ≤ m := by omega
    obtain ⟨P, hP⟩ := GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq a m hm
    obtain ⟨F, hF, hFa⟩ := exists_poly_op S (fun j : Fin (a + 1) => fP j) (fun j => hfP j) P
    refine ⟨F, hfin F hF, fun σ B hB v hv => ?_⟩
    rw [hFa σ.V σ.ρ (fun j => (UpperTheory.V.Af.algSat a (qV E w) B).esymm j) v
      (fun j => actP σ B hB v hv j (Nat.lt_succ_iff.1 j.2)), hP _ (hcard B hB.card), normV_eq]
    simp only [zpow_natCast]
  · have hm : 1 ≤ m := by omega
    obtain ⟨P, hP⟩ := GlobalTheory.PowerSumPoly.exists_intPoly_psum_eq a m hm
    obtain ⟨F, hF, hFa⟩ := exists_poly_op S fN hfN P
    refine ⟨F, hfin F hF, fun σ B hB v hv => ?_⟩
    rw [hFa σ.V σ.ρ (fun j => ((UpperTheory.V.Af.algSat a (qV E w) B).map (·⁻¹)).esymm j) v (actN σ B hB v hv),
      hP _ (by rw [Multiset.card_map]; exact hcard B hB.card), normV_eq, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.Cong.SphOpsProof

end
