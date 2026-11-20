import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterTrivialBaseFiniteIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.EtaTilde

section General

open GlobalTheory.BaseIdeleTriv GlobalTheory.PlaceIdem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Rewrite using `[← map_mul, ← adele_mul_apply, ← map_mul, Units.mul_inv, map_one, adele_one_apply, map_one]`.
-/
theorem val_mul_inv (g : Af E →+* Af E) (P : HeightOneSpectrum (𝓞 E)) (w : (Af E)ˣ) :
    Valued.v (g w P) * Valued.v (g (w⁻¹ : (Af E)ˣ) P) = 1 := by
  rw [← map_mul, ← adele_mul_apply, ← map_mul, Units.mul_inv, map_one, adele_one_apply, map_one]

/- English proof (translation)
Use `set v := P.under (𝓞 F) with hv`. Establish `e1 : f (singleV F v 1) P = 1`. Use `sub_eq_zero.1 (eq_zero_of_val P _ fun n => ?_)` and prove the remaining obligations. Use `h0 P (singleV F v 1 - 1) n (by` as an intermediate fact. Rewrite using `[adele_sub_apply, adele_one_apply, ← hv, single_same, sub_self, map_zero]`.

Conclude with `zero_le)`. Rewrite `this` using `[map_sub, map_one, adele_sub_apply, adele_one_apply]`. Then use the resulting hypothesis. Establish `e0 : ∀ Q, Q ≠ P → f (singleV F v 1) Q = 0` using `fun Q hQ => eq_zero_of_val Q _ fun n => h0 Q _ n (by`. Rewrite using `[single_ne fun h => hQ (hP Q h), map_zero]`. Conclude with `zero_le)`.

Establish `key : ∀ a : Af E, Valued.v (a P) ≤ 1 → Valued.v (c a P) ≤ 1`. Introduce `a ha`. Use `hint (f (singleV F v 1) * a) (fun Q => by` as an intermediate fact. Distinguish the cases in `hQ : Q = P`. Rewrite using `[hQ, mul_ap, e1, one_mul]` and apply the resulting hypothesis.

Rewrite using `[mul_ap, e0 Q hQ, zero_mul, map_zero]`. Conclude with `zero_le) P`. Rewrite `this` using `[map_mul, hcf, mul_ap, e1, one_mul]`. Then use the resulting hypothesis. Establish `hu0 : Valued.v ((u : Af E) P) ≠ 0` using `left_ne_zero_of_mul_eq_one (val_mul_inv (RingHom.id _) P u)`. Establish `hπ : ordF v (unif v) = 1`.

Establish `h2 : v.valuation F (unif v : F) = WithZero.exp (-1 : ℤ)` using `(val_algebraMap v _).symm.trans (unif_spec v)`. Rewrite using `[ordF, h2, WithZero.log_exp, neg_neg]`. Set `t : Fˣ` to `unif v ^ (-WithZero.log (Valued.v ((u : Af E) P)))`. Establish `ht0 : P.valuation E (algebraMap F E t) ≠ 0` using `(Valuation.ne_zero_iff _).2 (by simp)`. Establish `ht : P.valuation E (algebraMap F E t) = Valued.v ((u : Af E) P)`.

Establish `h1 : -WithZero.log (P.valuation E (algebraMap F E (unif v : Fˣ))) = 1` using `(hunr P (unif v)).trans hπ`. Establish `h2 : P.valuation E (algebraMap F E (unif v : Fˣ)) ≠ 0` using `(Valuation.ne_zero_iff _).2 (by simp)`. Establish `h3 : P.valuation E (algebraMap F E (unif v : Fˣ)) = WithZero.exp (-1 : ℤ)`. Rewrite using `[← WithZero.exp_log h2, ← h1, neg_neg]`. Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀, h3, ← WithZero.exp_zsmul]`.

Simplify using `only [smul_eq_mul, mul_neg, mul_one, neg_neg]`. Conclude with `WithZero.exp_log hu0`. Set `T : (Af E)ˣ` to `Units.map (f.comp (algebraMap F (Af F))).toMonoidHom t⁻¹`. Establish `hT : (T : Af E) = f (algebraMap F _ ((t⁻¹ : Fˣ) : F))` using `rfl`. Establish `hTv : Valued.v ((T : Af E) P) = (Valued.v ((u : Af E) P))⁻¹`.

Rewrite using `[hT, hf, adele_algebraMap_apply, val_algebraMap, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, ht]`. Establish `w1 : Valued.v (((u * T : (Af E)ˣ) : Af E) P) = 1`. Rewrite using `[Units.val_mul, mul_ap, map_mul, hTv, mul_inv_cancel₀ hu0]`. Establish `w2 : Valued.v ((((u * T)⁻¹ : (Af E)ˣ) : Af E) P) = 1`. Use `val_mul_inv (RingHom.id _) P (u * T)` as an intermediate fact.

Rewrite `this` using `[RingHom.id_apply, RingHom.id_apply, w1, one_mul]`. Then use the resulting hypothesis. Establish `w3 : Valued.v (c ((u * T : (Af E)ˣ) : Af E) P) = 1`. Use `le_antisymm (key _ w1.le) ?_` and prove the remaining obligations. Rewrite using `[← val_mul_inv c P (u * T)]`. Conclude with `mul_le_of_le_one_right' (key _ w2.le)`.

Rewrite `w3` using `[Units.val_mul, map_mul, hT, hcf, ← hT, mul_ap, map_mul, hTv]`. Conclude with `(mul_inv_eq_one₀ hu0).1 w3`.
-/
theorem val_conj (f : Af F →+* Af E)
    (hf : ∀ k : F, f (algebraMap F _ k) = algebraMap E _ (algebraMap F E k))
    (h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (b : Af F) (n : ℕ),
      Valued.v (b (P.under (𝓞 F))) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (f b P) ≤ WithZero.exp (-(n : ℤ)))
    (c : Af E →+* Af E) (hcf : ∀ a, c (f a) = f a)
    (hint : ∀ a : Af E, (∀ Q, Valued.v (a Q) ≤ 1) → ∀ Q, Valued.v (c a Q) ≤ 1)
    (hunr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (P : HeightOneSpectrum (𝓞 E)) (hP : ∀ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = P.under (𝓞 F) → Q = P)
    (u : (Af E)ˣ) : Valued.v (c u P) = Valued.v ((u : Af E) P) := by
  set v := P.under (𝓞 F) with hv
  have e1 : f (singleV F v 1) P = 1 := by
    refine sub_eq_zero.1 (eq_zero_of_val P _ fun n => ?_)
    have := h0 P (singleV F v 1 - 1) n (by
      rw [adele_sub_apply, adele_one_apply, ← hv, single_same, sub_self, map_zero]; exact zero_le)
    rwa [map_sub, map_one, adele_sub_apply, adele_one_apply] at this
  have e0 : ∀ Q, Q ≠ P → f (singleV F v 1) Q = 0 := fun Q hQ =>
    eq_zero_of_val Q _ fun n => h0 Q _ n (by
      rw [single_ne fun h => hQ (hP Q h), map_zero]; exact zero_le)
  have key : ∀ a : Af E, Valued.v (a P) ≤ 1 → Valued.v (c a P) ≤ 1 := by
    intro a ha
    have := hint (f (singleV F v 1) * a) (fun Q => by
      by_cases hQ : Q = P
      · rwa [hQ, mul_ap, e1, one_mul]
      · rw [mul_ap, e0 Q hQ, zero_mul, map_zero]; exact zero_le) P
    rwa [map_mul, hcf, mul_ap, e1, one_mul] at this
  have hu0 : Valued.v ((u : Af E) P) ≠ 0 := left_ne_zero_of_mul_eq_one (val_mul_inv (RingHom.id _) P u)
  have hπ : ordF v (unif v) = 1 := by
    have h2 : v.valuation F (unif v : F) = WithZero.exp (-1 : ℤ) :=
      (val_algebraMap v _).symm.trans (unif_spec v)
    rw [ordF, h2, WithZero.log_exp, neg_neg]
  let t : Fˣ := unif v ^ (-WithZero.log (Valued.v ((u : Af E) P)))
  have ht0 : P.valuation E (algebraMap F E t) ≠ 0 := (Valuation.ne_zero_iff _).2 (by simp)
  have ht : P.valuation E (algebraMap F E t) = Valued.v ((u : Af E) P) := by
    have h1 : -WithZero.log (P.valuation E (algebraMap F E (unif v : Fˣ))) = 1 := (hunr P (unif v)).trans hπ
    have h2 : P.valuation E (algebraMap F E (unif v : Fˣ)) ≠ 0 := (Valuation.ne_zero_iff _).2 (by simp)
    have h3 : P.valuation E (algebraMap F E (unif v : Fˣ)) = WithZero.exp (-1 : ℤ) := by
      rw [← WithZero.exp_log h2, ← h1, neg_neg]
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀, h3, ← WithZero.exp_zsmul]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    exact WithZero.exp_log hu0
  let T : (Af E)ˣ := Units.map (f.comp (algebraMap F (Af F))).toMonoidHom t⁻¹
  have hT : (T : Af E) = f (algebraMap F _ ((t⁻¹ : Fˣ) : F)) := rfl
  have hTv : Valued.v ((T : Af E) P) = (Valued.v ((u : Af E) P))⁻¹ := by
    rw [hT, hf, adele_algebraMap_apply, val_algebraMap, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, ht]
  have w1 : Valued.v (((u * T : (Af E)ˣ) : Af E) P) = 1 := by
    rw [Units.val_mul, mul_ap, map_mul, hTv, mul_inv_cancel₀ hu0]
  have w2 : Valued.v ((((u * T)⁻¹ : (Af E)ˣ) : Af E) P) = 1 := by
    have := val_mul_inv (RingHom.id _) P (u * T)
    rwa [RingHom.id_apply, RingHom.id_apply, w1, one_mul] at this
  have w3 : Valued.v (c ((u * T : (Af E)ˣ) : Af E) P) = 1 := by
    refine le_antisymm (key _ w1.le) ?_
    rw [← val_mul_inv c P (u * T)]
    exact mul_le_of_le_one_right' (key _ w2.le)
  rw [Units.val_mul, map_mul, hT, hcf, ← hT, mul_ap, map_mul, hTv] at w3
  exact (mul_inv_eq_one₀ hu0).1 w3

/- English proof (translation)
Take `⟨S, k, hS, hS'⟩` from `GlobalTheory.finiteIdele_exists_local_approx F 1 one_pos α`. Establish `hval : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∈ S → -WithZero.log (Valued.v (f α P)) = ordF P (upF F (k (P.under (𝓞 F))))`. Introduce `P hv`. Take `⟨-, -, b2⟩` from `hS _ hv`. Use `set kk := k (P.under (𝓞 F)) with hkk`.

Establish `c2` using `close_scaled f hf P _ (h0 P) α kk kk kk.ne_zero 1 (by simpa using b2)`. Establish `: Valued.v (f α P) = P.valuation E (algebraMap F E kk)`. Rewrite using `[← val_algebraMap]`. Apply `Valuation.map_eq_of_sub_lt` to reduce the goal to its premises. Rewrite using `[val_algebraMap]`.

Use `c2.trans_lt ?_` and prove the remaining obligations. Establish `hm2 : P.valuation E (algebraMap F E kk) ≠ 0` using `(Valuation.ne_zero_iff _).2 (by simp)`. Use `mul_lt_of_lt_one_left (zero_lt_iff.2 hm2) ?_` and prove the remaining obligations. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions.

Rewrite using `[this]`. Both sides reduce to the same expression. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := S.biUnion (aboveF (L := E) F))]`. Rewrite using `[Finset.prod_biUnion]`. Use `Finset.prod_eq_one fun v hv => ?_` and prove the remaining obligations.

Establish `h1` using `hχ.1 v (k v)`. Rewrite `h1` using `[HChar.resFin, MonoidHom.finsetProd_apply]`. Establish `h2 : etaFin (L` using `E) F v (k v) = 1 := by`. Rewrite using `[etaFin]`. Use `split_ifs with hc`.

Take `⟨P, hP⟩` from `Finset.card_eq_one.1 hc`. Establish `hPv : P.under (𝓞 F) = v` using `(mem_aboveF v P).1 (hP ▸ Finset.mem_singleton_self P)`. Substitute `hPv` using the available equality. Establish `hu0 : Valued.v ((u : Af E) P) ≠ 0` using `left_ne_zero_of_mul_eq_one (val_mul_inv (RingHom.id _) P u)`. Rewrite using `[← hunr, ← hval P hv, hα, mul_ap, map_mul, val_conj f hf h0 c hcf hint hunr P (fun Q hQ => Finset.mem_singleton.1 (hP ▸ (mem_aboveF _ Q).2 hQ)) u, WithZero.log_mul hu0 hu0]`.

Conclude with `Even.neg_one_zpow (Even.add_self _).neg`. Both sides reduce to the same expression. Rewrite using `[← h2, ← h1]`. Use `Finset.prod_congr rfl fun P hP => ?_` and prove the remaining obligations. Take `rfl` from `(mem_aboveF v P).1 hP`.

Rewrite using `[hval P hv]`. Conclude with `(GlobalTheory.HeckeProduct.locK_unr χ (hu P) _).symm`. Introduce `v _ w _ hvw`. Use `Finset.disjoint_left.2 fun P hv hw => hvw ?_` and prove the remaining obligations. Rewrite using `[← (mem_aboveF v P).1 hv, ← (mem_aboveF w P).1 hw]`.

Introduce `P hP`. Assume the negation of the conclusion as `h`. Establish `hv : P.under (𝓞 F) ∉ S` using `fun h' => h (Finset.mem_biUnion.2 ⟨_, h', (mem_aboveF _ P).2 rfl⟩)`. Apply `hP` to reduce the goal to its premises. Use `beta_reduce`.

Rewrite using `[val_eq_one f P _ (h0 P) α (hS' _ hv).1, WithZero.log_one, neg_zero, zpow_zero]`.
-/
theorem finprod_norm (f : Af F →+* Af E)
    (hf : ∀ k : F, f (algebraMap F _ k) = algebraMap E _ (algebraMap F E k))
    (h0 : ∀ (P : HeightOneSpectrum (𝓞 E)) (b : Af F) (n : ℕ),
      Valued.v (b (P.under (𝓞 F))) ≤ WithZero.exp (-(n : ℤ)) → Valued.v (f b P) ≤ WithZero.exp (-(n : ℤ)))
    (c : Af E →+* Af E) (hcf : ∀ a, c (f a) = f a)
    (hint : ∀ a : Af E, (∀ Q, Valued.v (a Q) ≤ 1) → ∀ Q, Valued.v (c a Q) ≤ 1)
    (hunr : ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (χ : HChar E) (hu : ∀ P, χ.UnrAt P) (hχ : χ.ResEta F) (u : (Af E)ˣ) (α : (Af F)ˣ) (hα : f α = u * c u) :
    ∏ᶠ P : HeightOneSpectrum (𝓞 E), χ.val P ^ (-WithZero.log (Valued.v (f α P))) = 1 := by
  classical
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx F 1 one_pos α
  have hval : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∈ S →
      -WithZero.log (Valued.v (f α P)) = ordF P (upF F (k (P.under (𝓞 F)))) := by
    intro P hv
    obtain ⟨-, -, b2⟩ := hS _ hv
    set kk := k (P.under (𝓞 F)) with hkk
    have c2 := close_scaled f hf P _ (h0 P) α kk kk kk.ne_zero 1 (by simpa using b2)
    have : Valued.v (f α P) = P.valuation E (algebraMap F E kk) := by
      rw [← val_algebraMap]
      apply Valuation.map_eq_of_sub_lt
      rw [val_algebraMap]
      refine c2.trans_lt ?_
      have hm2 : P.valuation E (algebraMap F E kk) ≠ 0 := (Valuation.ne_zero_iff _).2 (by simp)
      refine mul_lt_of_lt_one_left (zero_lt_iff.2 hm2) ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    rw [this]; rfl
  rw [finprod_eq_prod_of_mulSupport_subset (s := S.biUnion (aboveF (L := E) F))]
  · rw [Finset.prod_biUnion]
    · refine Finset.prod_eq_one fun v hv => ?_
      have h1 := hχ.1 v (k v)
      rw [HChar.resFin, MonoidHom.finsetProd_apply] at h1
      have h2 : etaFin (L := E) F v (k v) = 1 := by
        rw [etaFin]
        split_ifs with hc
        · obtain ⟨P, hP⟩ := Finset.card_eq_one.1 hc
          have hPv : P.under (𝓞 F) = v := (mem_aboveF v P).1 (hP ▸ Finset.mem_singleton_self P)
          subst hPv
          have hu0 : Valued.v ((u : Af E) P) ≠ 0 := left_ne_zero_of_mul_eq_one (val_mul_inv (RingHom.id _) P u)
          rw [← hunr, ← hval P hv, hα, mul_ap, map_mul, val_conj f hf h0 c hcf hint hunr P
            (fun Q hQ => Finset.mem_singleton.1 (hP ▸ (mem_aboveF _ Q).2 hQ)) u, WithZero.log_mul hu0 hu0]
          exact Even.neg_one_zpow (Even.add_self _).neg
        · rfl
      rw [← h2, ← h1]
      refine Finset.prod_congr rfl fun P hP => ?_
      obtain rfl := (mem_aboveF v P).1 hP
      rw [hval P hv]
      exact (GlobalTheory.HeckeProduct.locK_unr χ (hu P) _).symm
    · intro v _ w _ hvw
      refine Finset.disjoint_left.2 fun P hv hw => hvw ?_
      rw [← (mem_aboveF v P).1 hv, ← (mem_aboveF w P).1 hw]
  · intro P hP
    by_contra h
    have hv : P.under (𝓞 F) ∉ S := fun h' => h (Finset.mem_biUnion.2 ⟨_, h', (mem_aboveF _ P).2 rfl⟩)
    apply hP
    beta_reduce
    rw [val_eq_one f P _ (h0 P) α (hS' _ hv).1, WithZero.log_one, neg_zero, zpow_zero]

end General

/- English proof (translation)
Take `⟨N, hN, hprod⟩` from `GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h3 c χ hc`. Take `⟨S, k, hS, hS'⟩` from `GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)`. Rewrite using `[hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS', finprod_eq_prod_of_mulSupport_subset (s := S), Units.coe_prod]`. Use `Finset.prod_congr rfl fun P hP => ?_` and prove the remaining obligations. Establish `a : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E)` using `(hS P hP).1`.

Rewrite using `[GlobalTheory.HeckeProduct.locK_unr χ (hu P), a]`. Both sides reduce to the same expression. Introduce `P hP`. Assume the negation of the conclusion as `h`. Establish `a : Valued.v (ι (finPart D (x : AE D)) P) = 1` using `(hS' P h).1`.

Apply `hP` to reduce the goal to its premises. Use `beta_reduce`. Rewrite using `[a, WithZero.log_one, neg_zero, zpow_zero]`.
-/
theorem val_finite (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* Af D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    (h3 : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧
      ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0)
    (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ) (hu : ∀ P, χ.UnrAt P) (x : (AE D)ˣ)
    (hx : infPart D (x : AE D) = 1) :
    ((c x : Circle) : ℂ) = ((∏ᶠ P : HeightOneSpectrum (𝓞 D.host.E),
      χ.val P ^ (-WithZero.log (Valued.v (ι (finPart D (x : AE D)) P))) : ℂˣ) : ℂ) := by
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h3 c χ hc
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  rw [hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS', finprod_eq_prod_of_mulSupport_subset (s := S),
    Units.coe_prod]
  · refine Finset.prod_congr rfl fun P hP => ?_
    have a : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := (hS P hP).1
    rw [GlobalTheory.HeckeProduct.locK_unr χ (hu P), a]
    rfl
  · intro P hP
    by_contra h
    have a : Valued.v (ι (finPart D (x : AE D)) P) = 1 := (hS' P h).1
    apply hP
    beta_reduce
    rw [a, WithZero.log_one, neg_zero, zpow_zero]

set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare in

/- English proof (translation)
Take `⟨ι, h1, h2, h3⟩` from `GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D`. Establish `hfin` using `val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc hu`. Take `⟨ρ, hρ, r1, r0⟩` from `exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)`. Take `⟨s, hs⟩` from `RealChart.exists_chart D θ hθ ρ hρ r1 r0`. Take `⟨-, a, b, -, -, hab, ha, hb⟩` from `GlobalTheory.IdeleParts.congr_open_and_parts D`.

Use `haveI : Nonempty D.what₂.Tau := ⟨((GlobalTheory.CMTypePlaces.places_bijective D).2 (Classical.arbitrary _)).choose⟩`. Establish `ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b`. Introduce `a b h1 h2`. Rewrite using `[← sub_eq_zero]`. Conclude with `hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by`.

Rewrite using `[RingHom.map_sub, RingHom.map_sub, h2, sub_self]`. Set `t : (D.what₂.Tau → ℂˣ) → AE D` to `fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)`. Establish `tf : ∀ z, finPart D (t z) = 1` using `fun z => by`. Simplify using `only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]`. Establish `ti : ∀ z τ, θ τ (infPart D (t z)) = z τ` using `fun z τ => by`.

Simplify using `only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]`. Establish `tc : Continuous t` using `(hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const`. Set `T : (D.what₂.Tau → ℂˣ) →* AE D` to `{ toFun := t map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by`. Rewrite using `[ti, RingHom.map_one, RingHom.map_one]`. Both sides reduce to the same expression.

Use the proof step `map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by`. Rewrite using `[RingHom.map_mul, RingHom.map_mul, ti, ti, ti]`. Use `rfl }`. Establish `Tc : Continuous T.toHomUnits` using `Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩`. Establish `hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x` using `fun x hx => Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ => (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)`.

Establish `hd : DenseRange fun (k : D.host.E) τ => tauE D τ k`. Introduce `z`. Use `GlobalTheory.HeckeFinTrivial.mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))` as an intermediate fact. Rewrite `this` using `[show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ]`. Then use the resulting hypothesis. Establish `main : ∀ z : D.what₂.Tau → ℂˣ, ((c (T.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / (‖(z τ : ℂ)‖ : ℂ)) ^ n (D.eTau τ)`.

Introduce `z`. Use `(GlobalTheory.HeckeFinTrivial.denseRange_units (tauE D) hd).induction_on z (isClosed_eq (continuous_subtype_val.comp (hc.1.1.comp Tc)) ?_) fun k => ?_` and prove the remaining obligations. Use `continuous_finset_prod _ fun τ _ => ?_` and prove the remaining obligations. Establish `c1 : Continuous fun z : D.what₂.Tau → ℂˣ => (z τ : ℂ)` using `Units.continuous_val.comp (continuous_apply τ)`. Establish `n0 : ∀ z : D.what₂.Tau → ℂˣ, (‖(z τ : ℂ)‖ : ℂ) ≠ 0` using `fun z => by simp`.

Conclude with `(c1.div (Complex.continuous_ofReal.comp c1.norm) n0).zpow₀ _ fun z => Or.inl (div_ne_zero (z τ).ne_zero (n0 z))`. Use `set y : (AE D)ˣ := Units.map (incA D).toMonoidHom k with hy`. Establish `e1 : a y = T.toHomUnits fun τ => Units.map (tauE D τ).toMonoidHom k`. Rewrite using `[hT _ (ha y).2]`. Use `congr 1`.

Use function extensionality and compare the values at `τ`. Conclude with `Units.ext ((congrArg (θ τ) (ha y).1).trans ((hθ τ).1 k))`. Establish `e2 : c (a y) * c (b y) = 1` using `by rw [← map_mul, ← hab y]; exact hc.1.2 k`. Establish `e3` using `hfin (b y) (hb y).1`. Establish `e4 : ∀ P : HeightOneSpectrum (𝓞 D.host.E), -WithZero.log (Valued.v (ι (finPart D (b y : AE D)) P)) = ordF P k` using `fun P => by`.

Rewrite using `[(hb y).2, show finPart D (y : AE D) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (k : D.host.E) from rfl, h1, GlobalTheory.BaseIdeleTriv.adele_algebraMap_apply, GlobalTheory.BaseIdeleTriv.val_algebraMap]`. Both sides reduce to the same expression. Simplify using `only [e4] at e3`. Establish `e5` using `GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hu v) k`. Simplify using `only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at e5`.

Establish `e6 : ((c (a y) : Circle) : ℂ) = ((χ.inf k : ℂˣ) : ℂ)`. Use `mul_right_cancel₀ (Circle.coe_ne_zero (c (b y))) ?_` and prove the remaining obligations. Rewrite using `[← Circle.coe_mul, e2, e3, ← Units.val_mul, e5, Circle.coe_one, Units.val_one]`. Rewrite using `[← e1, e6, hn k, ← D.eTau.prod_comp]`. Both sides reduce to the same expression.

Use `main fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x` as an intermediate fact. Rewrite `this` using `[← hT x hx]`. Conclude with `this`.
-/
theorem val_infinite (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ) (hu : ∀ P, χ.UnrAt P)
    (n : D.R.Psi → ℤ) (hn : χ.HasInf (embPsi D.host) n)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (x : (AE D)ˣ)
    (hx : finPart D (x : AE D) = 1) :
    ((c x : Circle) : ℂ) =
      ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ n (D.eTau τ) := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have hfin := val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc hu
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau :=
    ⟨((GlobalTheory.CMTypePlaces.places_bijective D).2 (Classical.arbitrary _)).choose⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Tc : Continuous T.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x := fun x hx =>
    Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := GlobalTheory.HeckeFinTrivial.mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  have main : ∀ z : D.what₂.Tau → ℂˣ, ((c (T.toHomUnits z) : Circle) : ℂ) =
      ∏ τ, ((z τ : ℂ) / (‖(z τ : ℂ)‖ : ℂ)) ^ n (D.eTau τ) := by
    intro z
    refine (GlobalTheory.HeckeFinTrivial.denseRange_units (tauE D) hd).induction_on z
      (isClosed_eq (continuous_subtype_val.comp (hc.1.1.comp Tc)) ?_) fun k => ?_
    · refine continuous_finset_prod _ fun τ _ => ?_
      have c1 : Continuous fun z : D.what₂.Tau → ℂˣ => (z τ : ℂ) := Units.continuous_val.comp (continuous_apply τ)
      have n0 : ∀ z : D.what₂.Tau → ℂˣ, (‖(z τ : ℂ)‖ : ℂ) ≠ 0 := fun z => by simp
      exact (c1.div (Complex.continuous_ofReal.comp c1.norm) n0).zpow₀ _
        fun z => Or.inl (div_ne_zero (z τ).ne_zero (n0 z))
    · set y : (AE D)ˣ := Units.map (incA D).toMonoidHom k with hy
      have e1 : a y = T.toHomUnits fun τ => Units.map (tauE D τ).toMonoidHom k := by
        rw [hT _ (ha y).2]
        congr 1
        funext τ
        exact Units.ext ((congrArg (θ τ) (ha y).1).trans ((hθ τ).1 k))
      have e2 : c (a y) * c (b y) = 1 := by rw [← map_mul, ← hab y]; exact hc.1.2 k
      have e3 := hfin (b y) (hb y).1
      have e4 : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
          -WithZero.log (Valued.v (ι (finPart D (b y : AE D)) P)) = ordF P k := fun P => by
        rw [(hb y).2, show finPart D (y : AE D) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (k : D.host.E) from rfl, h1,
          GlobalTheory.BaseIdeleTriv.adele_algebraMap_apply, GlobalTheory.BaseIdeleTriv.val_algebraMap]
        rfl
      simp only [e4] at e3
      have e5 := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hu v) k
      simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at e5
      have e6 : ((c (a y) : Circle) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
        refine mul_right_cancel₀ (Circle.coe_ne_zero (c (b y))) ?_
        rw [← Circle.coe_mul, e2, e3, ← Units.val_mul, e5, Circle.coe_one, Units.val_one]
      rw [← e1, e6, hn k, ← D.eTau.prod_comp]
      rfl
  have := main fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x
  rw [← hT x hx] at this
  exact this

/- English proof (translation)
Use `D.host.isCMField_hostE` as an intermediate fact. Conclude with `GlobalTheory.Published.algebraMap_norm_tensor (E := D.host.E) (AF D.host.F) (x : AE D)`.
-/
theorem idF_norm (D : D7) (x : (AE D)ˣ) :
    (idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) x) : AE D) = x * cA D x := by
  have := D.host.isCMField_hostE
  exact GlobalTheory.Published.algebraMap_norm_tensor (E := D.host.E) (AF D.host.F) (x : AE D)

set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare in

/- English proof (translation)
Take `⟨⟨θ', hθ'⟩, -⟩` from `GlobalTheory.Member.infiniteAdele_bijective D`. Set `θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)` to `fun τ => θ' (tauE D τ)`. Establish `hθ : IsInfFam θ` using `fun τ => hθ' _`. Establish `hinf` using `val_infinite D c χ hc h.unr _ h.inf θ hθ`. Use `⟨?_, fun a => ?_, fun x => ?_, fun h1 => ?_⟩` and prove the remaining obligations.

Use `hc.1.1.comp (Continuous.units_map _ ?_)` and prove the remaining obligations. Conclude with `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))`. Rewrite using `[← hc.1.2 (upF D.host.F a), MonoidHom.comp_apply]`. Use `congr 1`. Conclude with `Units.ext (GlobalTheory.BaseIdeleTriv.algebraMap_tmul_one (a : D.host.F))`.

Take `⟨-, a, b, -, -, hab, ha, hb⟩` from `GlobalTheory.IdeleParts.congr_open_and_parts D`. Rewrite using `[hab x, map_mul, map_mul, MonoidHom.comp_apply, MonoidHom.comp_apply]`. Establish `e1 : c (idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (a x))) = 1`. Apply `Circle.ext` to reduce the goal to its premises. Rewrite using `[hinf _ (by rw [idF_norm, RingHom.map_mul, GlobalTheory.PlaceIdem.finPart_cA, (ha x).2, RingHom.map_one, mul_one]), Circle.coe_one]`.

Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations. Establish `h0 : θ τ (infPart D (a x : AE D)) ≠ 0` using `((a x).isUnit.map ((θ τ).comp (infPart D))).ne_zero`. Rewrite using `[idF_norm, RingHom.map_mul, RingHom.map_mul, comp_cA hθ, Complex.mul_conj, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _), div_self (by simpa using h0), one_zpow]`. Establish `e2 : c (idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (b x))) = 1`. Take `⟨ι, h1, h2, h3⟩` from `GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D`.

Take `⟨-, -, -, hunr, -⟩` from `GlobalTheory.Mem.HostCM.host_cm D.R D.host`. Use `set N := Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (b x) with hN`. Establish `hNv : (idF D N : AE D) = b x * cA D (b x)` using `idF_norm D _`. Apply `Circle.ext` to reduce the goal to its premises. Rewrite using `[val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc h.unr _ (by rw [hNv, RingHom.map_mul, GlobalTheory.PlaceIdem.infPart_cA, (hb x).1, RingHom.map_one, mul_one]), Circle.coe_one, Units.val_eq_one]`.

Set `α : (Af D.host.F)ˣ` to `Units.map (sndA D.host.F).toRingHom.toMonoidHom N`. Set `f : Af D.host.F →+* Af D.host.E` to `ι.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (B := D.host.E))`. Establish `hfa : ∀ b, f b = ι (b ⊗ₜ[D.host.F] (1 : D.host.E))` using `fun _ => rfl`. Set `s` to `sigR (Af D.host.F) D.sp.cm.sig`. Set `g : Af D.host.E →+* Af D.host.E` to `(ι.toRingHom.comp s).comp ι.symm.toRingHom`.

Establish `hg : ∀ z, g (ι z) = ι (s z)` using `fun z => by`. Express the relevant statement in the definitionally equal form `ι (s (ι.symm (ι z))) = _`. Rewrite using `[ι.symm_apply_apply]`. Establish `hfin : ι (finPart D (idF D N : AE D)) = f α` using `rfl`. Rewrite using `[hfin]`.

Use `finprod_norm f (fun k => ?_) (fun P b n h => ?_) g (fun a => ?_) (fun a ha => ?_) hunr χ h.unr h.res (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom (b x)) α ?_` and prove the remaining obligations. Rewrite using `[hfa, ← h1, GlobalTheory.BaseIdeleTriv.algebraMap_tmul_one]`. Use `h3 b 0 P n (by rwa [map_zero, sub_zero])` as an intermediate fact. Rewrite `this` using `[map_zero, map_zero, sub_zero]`. Then use the resulting hypothesis. Rewrite using `[hfa, hg]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _`. Rewrite using `[map_one]`. Take `⟨z, rfl⟩` from `ι.surjective a`. Rewrite using `[hg]`.

Conclude with `(h2 _).1 (GlobalTheory.PlaceIdem.sig_mem D ((h2 z).2 ha))`. Rewrite using `[← hfin, hNv, RingHom.map_mul, map_mul, GlobalTheory.PlaceIdem.finPart_cA, ← hg]`. Both sides reduce to the same expression. Rewrite using `[e1, e2, mul_one]`. Take `⟨ρ, -, r1, r0⟩` from `exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)`.

Set `τ₀ : D.what₂.Tau` to `((GlobalTheory.CMTypePlaces.places_bijective D).2 (Classical.arbitrary _)).choose`. Set `w : Ainf D.host.F` to `1 + ρ (Pi.single τ₀ (-2))`. Establish `hw : ∀ τ, θ τ (w ⊗ₜ[D.host.F] (1 : D.host.E)) = if τ = τ₀ then -1 else 1` using `fun τ => by`. Rewrite using `[TensorProduct.add_tmul, map_add, r1, ← Algebra.TensorProduct.one_def, map_one, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> norm_num`.

Establish `hww : w * w = 1`. Use `sub_eq_zero.1 (r0 _ fun τ => ?_)` and prove the remaining obligations. Rewrite using `[TensorProduct.sub_tmul, map_sub, ← Algebra.TensorProduct.one_def, map_one, ← mul_one (1 : D.host.E), ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, hw]`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hp : ((w, 1) : AF D.host.F) * (w, 1) = 1` using `Prod.ext hww (mul_one _)`.

Set `u : (AF D.host.F)ˣ` to `⟨(w, 1), (w, 1), hp, hp⟩`. Establish `e` using `hinf (idF D u) rfl`. Establish `e1 : c (idF D u) = 1` using `DFunLike.congr_fun h1 u`. Establish `e2 : infPart D (idF D u : AE D) = w ⊗ₜ[D.host.F] (1 : D.host.E)` using `rfl`. Rewrite `e` using `[e1, e2, Finset.prod_eq_single τ₀ (fun τ _ hτ => by rw [hw, if_neg hτ]; simp) (by simp), hw, if_pos rfl]`.

Evaluate the numerical expressions using `at e`.
-/
theorem isEta_res (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ) (h : IsEtaT D.host χ) :
    IsEta D (c.comp (idF D)) := by
  classical
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun τ => θ' (tauE D τ)
  have hθ : IsInfFam θ := fun τ => hθ' _
  have hinf := val_infinite D c χ hc h.unr _ h.inf θ hθ
  refine ⟨?_, fun a => ?_, fun x => ?_, fun h1 => ?_⟩
  · refine hc.1.1.comp (Continuous.units_map _ ?_)
    exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))
  · rw [← hc.1.2 (upF D.host.F a), MonoidHom.comp_apply]
    congr 1
    exact Units.ext (GlobalTheory.BaseIdeleTriv.algebraMap_tmul_one (a : D.host.F))
  · obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
    rw [hab x, map_mul, map_mul, MonoidHom.comp_apply, MonoidHom.comp_apply]
    have e1 : c (idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (a x))) = 1 := by
      apply Circle.ext
      rw [hinf _ (by rw [idF_norm, RingHom.map_mul, GlobalTheory.PlaceIdem.finPart_cA, (ha x).2, RingHom.map_one, mul_one]),
        Circle.coe_one]
      refine Finset.prod_eq_one fun τ _ => ?_
      have h0 : θ τ (infPart D (a x : AE D)) ≠ 0 := ((a x).isUnit.map ((θ τ).comp (infPart D))).ne_zero
      rw [idF_norm, RingHom.map_mul, RingHom.map_mul, comp_cA hθ, Complex.mul_conj, Complex.norm_real,
        Real.norm_of_nonneg (Complex.normSq_nonneg _), div_self (by simpa using h0), one_zpow]
    have e2 : c (idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (b x))) = 1 := by
      obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
      obtain ⟨-, -, -, hunr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
      set N := Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (b x) with hN
      have hNv : (idF D N : AE D) = b x * cA D (b x) := idF_norm D _
      apply Circle.ext
      rw [val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc h.unr _
        (by rw [hNv, RingHom.map_mul, GlobalTheory.PlaceIdem.infPart_cA, (hb x).1, RingHom.map_one, mul_one]),
        Circle.coe_one, Units.val_eq_one]
      let α : (Af D.host.F)ˣ := Units.map (sndA D.host.F).toRingHom.toMonoidHom N
      let f : Af D.host.F →+* Af D.host.E :=
        ι.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (B := D.host.E))
      have hfa : ∀ b, f b = ι (b ⊗ₜ[D.host.F] (1 : D.host.E)) := fun _ => rfl
      let s := sigR (Af D.host.F) D.sp.cm.sig
      let g : Af D.host.E →+* Af D.host.E := (ι.toRingHom.comp s).comp ι.symm.toRingHom
      have hg : ∀ z, g (ι z) = ι (s z) := fun z => by
        change ι (s (ι.symm (ι z))) = _
        rw [ι.symm_apply_apply]
      have hfin : ι (finPart D (idF D N : AE D)) = f α := rfl
      rw [hfin]
      refine finprod_norm f (fun k => ?_) (fun P b n h => ?_) g (fun a => ?_) (fun a ha => ?_) hunr χ h.unr h.res
        (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom (b x)) α ?_
      · rw [hfa, ← h1, GlobalTheory.BaseIdeleTriv.algebraMap_tmul_one]
      · have := h3 b 0 P n (by rwa [map_zero, sub_zero])
        rwa [map_zero, map_zero, sub_zero] at this
      · rw [hfa, hg]
        congr 1
        change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
        rw [map_one]
      · obtain ⟨z, rfl⟩ := ι.surjective a
        rw [hg]
        exact (h2 _).1 (GlobalTheory.PlaceIdem.sig_mem D ((h2 z).2 ha))
      · rw [← hfin, hNv, RingHom.map_mul, map_mul, GlobalTheory.PlaceIdem.finPart_cA, ← hg]
        rfl
    rw [e1, e2, mul_one]
  · obtain ⟨ρ, -, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
    let τ₀ : D.what₂.Tau := ((GlobalTheory.CMTypePlaces.places_bijective D).2 (Classical.arbitrary _)).choose
    let w : Ainf D.host.F := 1 + ρ (Pi.single τ₀ (-2))
    have hw : ∀ τ, θ τ (w ⊗ₜ[D.host.F] (1 : D.host.E)) = if τ = τ₀ then -1 else 1 := fun τ => by
      rw [TensorProduct.add_tmul, map_add, r1, ← Algebra.TensorProduct.one_def, map_one, Pi.single_apply]
      split_ifs <;> norm_num
    have hww : w * w = 1 := by
      refine sub_eq_zero.1 (r0 _ fun τ => ?_)
      rw [TensorProduct.sub_tmul, map_sub, ← Algebra.TensorProduct.one_def, map_one, ← mul_one (1 : D.host.E),
        ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, hw]
      split_ifs <;> norm_num
    have hp : ((w, 1) : AF D.host.F) * (w, 1) = 1 := Prod.ext hww (mul_one _)
    let u : (AF D.host.F)ˣ := ⟨(w, 1), (w, 1), hp, hp⟩
    have e := hinf (idF D u) rfl
    have e1 : c (idF D u) = 1 := DFunLike.congr_fun h1 u
    have e2 : infPart D (idF D u : AE D) = w ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [e1, e2, Finset.prod_eq_single τ₀ (fun τ _ hτ => by rw [hw, if_neg hτ]; simp) (by simp), hw, if_pos rfl] at e
    norm_num at e

/- English proof (translation)
Introduce `D`. Take `⟨χ, h⟩` from `GlobalTheory.Mem.EtaT.etaT_exists D.R D.host`. Take `⟨c, hc⟩` from `GlobalTheory.CharTransport.exists_chrEq D χ h.unitary`. Establish `hη` using `isEta_res D c χ hc h`. Use `⟨c, hc.1, fun τ => ⟨1, by norm_num, ?_, fun θ hθ x hx hx' => ?_⟩, ⟨⟨_, hη⟩, fun η hη' a => ?_⟩, fun x hx h4 h5 => ?_⟩` and prove the remaining obligations.

Take `⟨⟨θ', hθ'⟩, -⟩` from `GlobalTheory.Member.infiniteAdele_bijective D`. Conclude with `⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩`. Rewrite using `[val_infinite D c χ hc h.unr _ h.inf θ hθ x hx, Finset.prod_eq_single τ (fun τ' _ hτ => by rw [hx' τ' hτ]; simp) (by simp)]`. Rewrite using `[(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique hη' hη, pow_one, MonoidHom.comp_apply]`. Take `⟨ι, h1, h2, h3⟩` from `GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D`.

Apply `Circle.ext` to reduce the goal to its premises. Rewrite using `[val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc h.unr x hx, Circle.coe_one, Units.val_eq_one]`. Use `finprod_eq_one_of_forall_eq_one fun P => ?_` and prove the remaining obligations. Establish `e` using `val_mul_inv (RingHom.id _) P (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)`. Establish `e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1` using `e`.

Establish `e1 : Valued.v (ι (finPart D (x : AE D)) P) = 1`. Use `le_antisymm ((h2 _).1 h4 P) ?_` and prove the remaining obligations. Rewrite using `[← e']`. Conclude with `mul_le_of_le_one_right' ((h2 _).1 h5 P)`. Rewrite using `[e1, WithZero.log_one, neg_zero, zpow_zero]`.
-/
theorem exists_etaTilde : ∀ D : D7, ∃ χ : GlobalTheory.Mem.Th.IdC D, IsHeckeChar D χ ∧ (∀ τ, HasInfExp D χ τ (1 / 2)) ∧
    ResEta D χ 1 ∧ UnramEverywhere D χ := by
  intro D
  obtain ⟨χ, h⟩ := GlobalTheory.Mem.EtaT.etaT_exists D.R D.host
  obtain ⟨c, hc⟩ := GlobalTheory.CharTransport.exists_chrEq D χ h.unitary
  have hη := isEta_res D c χ hc h
  refine ⟨c, hc.1, fun τ => ⟨1, by norm_num, ?_, fun θ hθ x hx hx' => ?_⟩, ⟨⟨_, hη⟩, fun η hη' a => ?_⟩,
    fun x hx h4 h5 => ?_⟩
  · obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
    exact ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩
  · rw [val_infinite D c χ hc h.unr _ h.inf θ hθ x hx,
      Finset.prod_eq_single τ (fun τ' _ hτ => by rw [hx' τ' hτ]; simp) (by simp)]
  · rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique hη' hη, pow_one, MonoidHom.comp_apply]
  · obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    apply Circle.ext
    rw [val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc h.unr x hx, Circle.coe_one,
      Units.val_eq_one]
    refine finprod_eq_one_of_forall_eq_one fun P => ?_
    have e := val_mul_inv (RingHom.id _) P (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := e
    have e1 : Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
      refine le_antisymm ((h2 _).1 h4 P) ?_
      rw [← e']
      exact mul_le_of_le_one_right' ((h2 _).1 h5 P)
    rw [e1, WithZero.log_one, neg_zero, zpow_zero]

end GlobalTheory.Mem.EtaTilde
