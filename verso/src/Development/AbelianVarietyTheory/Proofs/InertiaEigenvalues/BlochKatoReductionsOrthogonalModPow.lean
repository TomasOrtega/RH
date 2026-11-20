import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoLMk
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKOrthRed

section Gen

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

/- English proof (translation)
Rewrite using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, -, rfl⟩`. Conclude with `⟨y, rfl⟩`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨y, Submodule.mem_top, rfl⟩`.
-/
theorem mem_span_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

/- English proof (translation)
Establish `hs` using `(Submodule.Quotient.mk_surjective (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T) (Submodule.Quotient.mk ⟨v, hv⟩)).choose_spec`. Take `⟨t, ht⟩` from `(mem_span_smul_top L _ _).1 ((Submodule.Quotient.eq _).1 hs)`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun x : ↥L.T => (x : V)) ht`. Simplify using `only [Submodule.coe_sub, Submodule.coe_smul] at h2`.

Unfold `Formalism.MainNotions.LocalSituation.liftQ`. Rewrite using `[← map_pow, algebraMap_smul, ← h2]`. Normalize the expressions using the abelian group laws.
-/
theorem liftQ_eq (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (v : V) (hv : v ∈ L.T) :
    ∃ t : ↥L.T, Formalism.MainNotions.LocalSituation.liftQ L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)
      (Submodule.Quotient.mk ⟨v, hv⟩) = v + (algebraMap O LL ϖ) ^ r • (t : V) := by
  have hs := (Submodule.Quotient.mk_surjective (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)
    (Submodule.Quotient.mk ⟨v, hv⟩)).choose_spec
  obtain ⟨t, ht⟩ := (mem_span_smul_top L _ _).1 ((Submodule.Quotient.eq _).1 hs)
  refine ⟨t, ?_⟩
  have h2 := congrArg (fun x : ↥L.T => (x : V)) ht
  simp only [Submodule.coe_sub, Submodule.coe_smul] at h2
  unfold Formalism.MainNotions.LocalSituation.liftQ
  rw [← map_pow, algebraMap_smul, ← h2]
  abel

end Gen

section Gal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

/- English proof (translation)
Rewrite `hc` using `[HfQ, Submodule.mem_sup]`. Take `⟨y, hy, z, hz, rfl⟩` from `hc`. Take `⟨a0, ha0, rfl⟩` from `hy`. Take `⟨x, rfl⟩` from `hz`. Take `⟨xh, rfl⟩` from `Submodule.Quotient.mk_surjective I x`.

Use `⟨(a0 : G → A.V) + cob A.ρ (xh : A.V), (finiteCocycles PD A.ρ).add_mem ha0.2 (Formalism.MainNotions.BlochKatoDuality.Br.coboundary_mem_finite_cocycles PD A _), fun g => ⟨LA.T.add_mem (a0.2.2 g trivial) (LA.T.sub_mem (LA.stable g _ xh.2) xh.2), ?_⟩⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk (evT LA g a0) + (actQ LA I hI g (Submodule.Quotient.mk xh) - Submodule.Quotient.mk xh) = _`. Rewrite using `[actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]`. Use `congr 1`.
-/
theorem hfQ_lift {A : GRep G Qp LL O} (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T)
    (hI : StableSub LA I) (c : G → ↥LA.T ⧸ I) (hc : c ∈ HfQ PD LA I hI) :
    ∃ a : G → A.V, a ∈ finiteCocycles PD A.ρ ∧ ∀ g, ∃ h : a g ∈ LA.T, c g = Submodule.Quotient.mk ⟨a g, h⟩ := by
  rw [HfQ, Submodule.mem_sup] at hc
  obtain ⟨y, hy, z, hz, rfl⟩ := hc
  obtain ⟨a0, ha0, rfl⟩ := hy
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨xh, rfl⟩ := Submodule.Quotient.mk_surjective I x
  refine ⟨(a0 : G → A.V) + cob A.ρ (xh : A.V), (finiteCocycles PD A.ρ).add_mem ha0.2 (Formalism.MainNotions.BlochKatoDuality.Br.coboundary_mem_finite_cocycles PD A _),
    fun g => ⟨LA.T.add_mem (a0.2.2 g trivial) (LA.T.sub_mem (LA.stable g _ xh.2) xh.2), ?_⟩⟩
  show Submodule.Quotient.mk (evT LA g a0) + (actQ LA I hI g (Submodule.Quotient.mk xh) - Submodule.Quotient.mk xh) = _
  rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
  congr 1

end Gal

/- English proof (translation)
Introduce `l _ P K hA LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hDR hd ϖ r hI hI' c hc c' hc'`. Establish `hA'` using `hA LL O hO`. Take `⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩` from `hO`. Use `haveI := hDom`. Use `haveI := hDVR`.

Use `haveI := hFr`. Use `haveI := htr`. Take `⟨a, ha, hag⟩` from `hfQ_lift (P.PD K) LA _ hI c hc`. Take `⟨b, hb, hbg⟩` from `hfQ_lift (P.PD K) LA' _ hI' c' hc'`. Take `⟨f, hf, hfd1⟩` from `((hA' A A' m hDR hd.1).1 a ha.1).1 ha b hb`.

Use `set s : LL := (algebraMap O LL ϖ)⁻¹ ^ r with hs`. Establish `hcob : CobL (P.PD K) (fun x => s * cupL A'.ρ m a b x)`. Use `⟨s • f, continuous_const.mul hf, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hfd1]`. Both sides reduce to the same expression.

Establish `hred` using `Formalism.MainNotions.BlochKatoDuality.Br.red_cob (P.PD K) hopen L1 hL1 _ hcob`. Use `(Formalism.MainNotions.BlochKatoDuality.Br.cobO_congr (P.PD K) L1 _ _ ?_).2 hred` and prove the remaining obligations. Introduce and unpack `⟨g, h⟩`. Take `⟨hag1, hcg⟩` from `hag g`. Take `⟨hbh1, hch⟩` from `hbg h`.

Take `⟨t, ht⟩` from `liftQ_eq LA ϖ r (a g) hag1`. Take `⟨t', ht'⟩` from `liftQ_eq LA' ϖ r (b h) hbh1`. Take `⟨u1, hu1⟩` from `(hd.2 _).1 (LA'.stable g _ hbh1) t t.2`. Take `⟨u2, hu2⟩` from `(hd.2 _).1 (LA'.stable g _ t'.2) (a g) hag1`. Take `⟨u3, hu3⟩` from `(hd.2 _).1 (LA'.stable g _ t'.2) t t.2`.

Establish `ho : ∃ o : O, algebraMap O LL o = s * (algebraMap O LL ϖ) ^ r`. Rewrite using `[hs, ← mul_pow]`. Break down `eq_or_ne (algebraMap O LL ϖ) 0 with h0 | h0` into its components or cases. Conclude with `⟨0 ^ r, by rw [h0, inv_zero, zero_mul, map_pow, map_zero]⟩`. Conclude with `⟨1, by rw [inv_mul_cancel₀ h0, one_pow, map_one]⟩`.

Take `⟨o, ho⟩` from `ho`. Rewrite using `[Submodule.Quotient.eq, hL1]`. Use `⟨o * (u1 + u2 + ϖ ^ r * u3), ?_⟩` and prove the remaining obligations. Use `show _ = s * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c g)) (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h))) - s * m (a g) (A'.ρ g (b h))`. Rewrite using `[hcg, hch, ht, ht']`.

Simplify using `only [Algebra.linearMap_apply, map_mul, map_add, map_pow, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[← hu1, ← hu2, ← hu3, ho]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cupQ_cobO_of_bkA : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), Formalism.MainNotions.N.bkACore (P.PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), ∀ c ∈ HfQ (P.PD K) LA _ hI, ∀ c' ∈ HfQ (P.PD K) LA' _ hI', CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c') := by
  intro l _ P K hA LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hDR hd ϖ r hI hI' c hc c' hc'
  have hA' := hA LL O hO
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  obtain ⟨a, ha, hag⟩ := hfQ_lift (P.PD K) LA _ hI c hc
  obtain ⟨b, hb, hbg⟩ := hfQ_lift (P.PD K) LA' _ hI' c' hc'
  obtain ⟨f, hf, hfd1⟩ := ((hA' A A' m hDR hd.1).1 a ha.1).1 ha b hb
  set s : LL := (algebraMap O LL ϖ)⁻¹ ^ r with hs
  have hcob : CobL (P.PD K) (fun x => s * cupL A'.ρ m a b x) := by
    refine ⟨s • f, continuous_const.mul hf, ?_⟩
    rw [map_smul, hfd1]
    rfl
  have hred := Formalism.MainNotions.BlochKatoDuality.Br.red_cob (P.PD K) hopen L1 hL1 _ hcob
  refine (Formalism.MainNotions.BlochKatoDuality.Br.cobO_congr (P.PD K) L1 _ _ ?_).2 hred
  rintro ⟨g, h⟩
  obtain ⟨hag1, hcg⟩ := hag g
  obtain ⟨hbh1, hch⟩ := hbg h
  obtain ⟨t, ht⟩ := liftQ_eq LA ϖ r (a g) hag1
  obtain ⟨t', ht'⟩ := liftQ_eq LA' ϖ r (b h) hbh1
  obtain ⟨u1, hu1⟩ := (hd.2 _).1 (LA'.stable g _ hbh1) t t.2
  obtain ⟨u2, hu2⟩ := (hd.2 _).1 (LA'.stable g _ t'.2) (a g) hag1
  obtain ⟨u3, hu3⟩ := (hd.2 _).1 (LA'.stable g _ t'.2) t t.2
  have ho : ∃ o : O, algebraMap O LL o = s * (algebraMap O LL ϖ) ^ r := by
    rw [hs, ← mul_pow]
    rcases eq_or_ne (algebraMap O LL ϖ) 0 with h0 | h0
    · exact ⟨0 ^ r, by rw [h0, inv_zero, zero_mul, map_pow, map_zero]⟩
    · exact ⟨1, by rw [inv_mul_cancel₀ h0, one_pow, map_one]⟩
  obtain ⟨o, ho⟩ := ho
  rw [Submodule.Quotient.eq, hL1]
  refine ⟨o * (u1 + u2 + ϖ ^ r * u3), ?_⟩
  show _ = s * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c g)) (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h))) - s * m (a g) (A'.ρ g (b h))
  rw [hcg, hch, ht, ht']
  simp only [Algebra.linearMap_apply, map_mul, map_add, map_pow, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [← hu1, ← hu2, ← hu3, ho]
  ring

end GlobalTheory.BKOrthRed
