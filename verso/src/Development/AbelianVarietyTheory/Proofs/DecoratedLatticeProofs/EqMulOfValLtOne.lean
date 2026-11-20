import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeConjOfIdemSum
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SplitUnif

section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hT0 : T ≠ 0` using `by rintro rfl; exact h2 (zero_mem _)`. Establish `hle : v.intValuation b ≤ v.intValuation T`. Establish `h3` using `(v.intValuation_le_pow_iff_mem b 1).2 (by simpa using hb)`. Use `h3.trans ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[not_le]`. Apply `h2` to reduce the goal to its premises. Rewrite using `[← v.intValuation_le_pow_iff_mem]`. Establish `h0 : v.intValuation T ≠ 0` using `v.intValuation_ne_zero _ hT0`. Rewrite `h`, the goal using `[← WithZero.exp_log h0]`.

Rewrite `h` using `[WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hTF : (T : F) ≠ 0` using `RingOfIntegers.coe_ne_zero_iff.2 hT0`. Use `⟨algebraMap F (v.adicCompletion F) ((b : F) / (T : F)), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `h` using `v.valuedAdicCompletion_eq_valuation' ((b : F) / (T : F))`. Express the relevant statement in the definitionally equal form `Valued.v (((b : F) / (T : F) : F) : v.adicCompletion F) ≤ 1`. Rewrite using `[h, map_div₀]`. Establish `e1 : v.valuation F (b : F) = v.intValuation b` using `v.valuation_of_algebraMap b`.

Establish `e2 : v.valuation F (T : F) = v.intValuation T` using `v.valuation_of_algebraMap T`. Rewrite using `[e1, e2]`. Conclude with `div_le_one_of_le₀ hle zero_le`. Rewrite using `[← map_mul, mul_div_cancel₀ _ hTF]`.
-/
theorem exists_eq_mul (v : HeightOneSpectrum (𝓞 F)) (T b : 𝓞 F) (h1 : T ∈ v.asIdeal) (h2 : T ∉ v.asIdeal ^ 2)
    (hb : b ∈ v.asIdeal) : ∃ c ∈ v.adicCompletionIntegers F,
      algebraMap F (v.adicCompletion F) (b : F) = algebraMap F (v.adicCompletion F) (T : F) * c := by
  have hT0 : T ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hle : v.intValuation b ≤ v.intValuation T := by
    have h3 := (v.intValuation_le_pow_iff_mem b 1).2 (by simpa using hb)
    refine h3.trans ?_
    by_contra h
    rw [not_le] at h
    apply h2
    rw [← v.intValuation_le_pow_iff_mem]
    have h0 : v.intValuation T ≠ 0 := v.intValuation_ne_zero _ hT0
    rw [← WithZero.exp_log h0] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega
  have hTF : (T : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hT0
  refine ⟨algebraMap F (v.adicCompletion F) ((b : F) / (T : F)), ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h := v.valuedAdicCompletion_eq_valuation' ((b : F) / (T : F))
    change Valued.v (((b : F) / (T : F) : F) : v.adicCompletion F) ≤ 1
    rw [h, map_div₀]
    have e1 : v.valuation F (b : F) = v.intValuation b := v.valuation_of_algebraMap b
    have e2 : v.valuation F (T : F) = v.intValuation T := v.valuation_of_algebraMap T
    rw [e1, e2]
    exact div_le_one_of_le₀ hle zero_le
  · rw [← map_mul, mul_div_cancel₀ _ hTF]

/- English proof (translation)
Establish `hO : ∀ r : 𝓞 E, Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (r : E) ∈ intV E v := fun r => Subring.subset_closure (Or.inl ⟨⟨(r : E), r, rfl⟩, rfl⟩)`. Establish `hF : ∀ x : F, Formalism.UG.inclE (F` using `F) (v.adicCompletion F) (algebraMap F E x) = (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) x := fun x => by`. Express the relevant statement in the definitionally equal form `(algebraMap F E x) ⊗ₜ[F] (1 : v.adicCompletion F) = _`. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]`. Set `a' : 𝓞 E` to `⟨star (a : E), (RingOfIntegers.isIntegral_coe a).map_of_comp_eq (RingHom.id ℤ) (starRingEnd E) (RingHom.ext_int _ _)⟩`.

Establish `ha' : (a' : E) = star (a : E)` using `rfl`. Take `⟨b₀, hb₀⟩` from `(hc.fixed ((t' * a + t * a' : 𝓞 E) : E)).1 (by`. Express the relevant statement in the definitionally equal form `star ((t' : E) * (a : E) + (t : E) * star (a : E)) = (t' : E) * (a : E) + (t : E) * star (a : E)`. Rewrite using `[ht', star_add, star_mul', star_mul', star_star, star_star, add_comm])`. Establish `hint : IsIntegral ℤ b₀`.

Rewrite using `[← isIntegral_algebraMap_iff (algebraMap F E).injective, hb₀]`. Conclude with `RingOfIntegers.isIntegral_coe _`. Set `b : 𝓞 F` to `⟨b₀, hint⟩`. Establish `hb : algebraMap (𝓞 F) (𝓞 E) b = t' * a + t * a'` using `RingOfIntegers.ext hb₀`. Take `⟨c, hc1, hc2⟩` from `exists_eq_mul v T b h1 h2 (hv b (by rw [hb]; exact add_mem (P.mul_mem_left _ ha) (P.mul_mem_right _ ht)))`.

Establish `hcV : (1 : E) ⊗ₜ[F] c ∈ intV E v` using `Subring.subset_closure (Or.inr ⟨⟨c, hc1⟩, rfl⟩)`. Take `⟨α, β, hαβ⟩` from `hco`. Use `set ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F) with hι`. Establish `e1 : ι t' * ι a + ι t * ι a' = ι t * ι t' * ((1 : E) ⊗ₜ[F] c)`. Establish `l : ι t' * ι a + ι t * ι a' = ι (algebraMap F E (b : F))`.

Rewrite using `[← map_mul ι, ← map_mul ι, ← map_add ι]`. Conclude with `congrArg ι hb₀.symm`. Establish `r : ι t * ι t' = ι (algebraMap F E (T : F))`. Rewrite using `[← map_mul ι]`. Conclude with `congrArg (fun z : 𝓞 E => ι (z : E)) htt`.

Rewrite using `[l, r, hF, hF, hc2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Establish `e2 : ι α * ι t + ι β * ι t' = 1`. Rewrite using `[← map_mul ι, ← map_mul ι, ← map_add ι, ← map_one ι]`. Conclude with `congrArg (fun z : 𝓞 E => ι (z : E)) hαβ`. Use `⟨ι α * ι a + ι β * (ι t' * ((1 : E) ⊗ₜ[F] c) - ι a'), add_mem (mul_mem (hO _) (hO _)) (mul_mem (hO _) (sub_mem (mul_mem (hO _) hcV) (hO _))), ?_⟩` and prove the remaining obligations.

Take the linear combination `(-(ι a)) * e2 + ι β * e1`.
-/
theorem incl_eq_mul [StarRing E] (hc : CMData F E) (v : HeightOneSpectrum (𝓞 F)) (P : Ideal (𝓞 E))
    (hv : ∀ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b ∈ P → b ∈ v.asIdeal) (T : 𝓞 F) (t t' : 𝓞 E)
    (ht' : (t' : E) = star (t : E)) (htt : t * t' = algebraMap (𝓞 F) (𝓞 E) T) (hco : IsCoprime t t') (ht : t ∈ P)
    (h1 : T ∈ v.asIdeal) (h2 : T ∉ v.asIdeal ^ 2) (a : 𝓞 E) (ha : a ∈ P) :
    ∃ c ∈ intV E v, Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E) * c := by
  have hO : ∀ r : 𝓞 E, Formalism.UG.inclE (F := F) (v.adicCompletion F) (r : E) ∈ intV E v := fun r =>
    Subring.subset_closure (Or.inl ⟨⟨(r : E), r, rfl⟩, rfl⟩)
  have hF : ∀ x : F, Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap F E x) =
      (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) x := fun x => by
    change (algebraMap F E x) ⊗ₜ[F] (1 : v.adicCompletion F) = _
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  let a' : 𝓞 E := ⟨star (a : E), (RingOfIntegers.isIntegral_coe a).map_of_comp_eq (RingHom.id ℤ) (starRingEnd E)
    (RingHom.ext_int _ _)⟩
  have ha' : (a' : E) = star (a : E) := rfl
  obtain ⟨b₀, hb₀⟩ := (hc.fixed ((t' * a + t * a' : 𝓞 E) : E)).1 (by
    change star ((t' : E) * (a : E) + (t : E) * star (a : E)) = (t' : E) * (a : E) + (t : E) * star (a : E)
    rw [ht', star_add, star_mul', star_mul', star_star, star_star, add_comm])
  have hint : IsIntegral ℤ b₀ := by
    rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, hb₀]
    exact RingOfIntegers.isIntegral_coe _
  let b : 𝓞 F := ⟨b₀, hint⟩
  have hb : algebraMap (𝓞 F) (𝓞 E) b = t' * a + t * a' := RingOfIntegers.ext hb₀
  obtain ⟨c, hc1, hc2⟩ := exists_eq_mul v T b h1 h2
    (hv b (by rw [hb]; exact add_mem (P.mul_mem_left _ ha) (P.mul_mem_right _ ht)))
  have hcV : (1 : E) ⊗ₜ[F] c ∈ intV E v := Subring.subset_closure (Or.inr ⟨⟨c, hc1⟩, rfl⟩)
  obtain ⟨α, β, hαβ⟩ := hco
  set ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F) with hι
  have e1 : ι t' * ι a + ι t * ι a' = ι t * ι t' * ((1 : E) ⊗ₜ[F] c) := by
    have l : ι t' * ι a + ι t * ι a' = ι (algebraMap F E (b : F)) := by
      rw [← map_mul ι, ← map_mul ι, ← map_add ι]
      exact congrArg ι hb₀.symm
    have r : ι t * ι t' = ι (algebraMap F E (T : F)) := by
      rw [← map_mul ι]
      exact congrArg (fun z : 𝓞 E => ι (z : E)) htt
    rw [l, r, hF, hF, hc2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have e2 : ι α * ι t + ι β * ι t' = 1 := by
    rw [← map_mul ι, ← map_mul ι, ← map_add ι, ← map_one ι]
    exact congrArg (fun z : 𝓞 E => ι (z : E)) hαβ
  refine ⟨ι α * ι a + ι β * (ι t' * ((1 : E) ⊗ₜ[F] c) - ι a'),
    add_mem (mul_mem (hO _) (hO _)) (mul_mem (hO _) (sub_mem (mul_mem (hO _) hcV) (hO _))), ?_⟩
  linear_combination (-(ι a)) * e2 + ι β * e1

end General

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D k _ _ _ _ p P hP T t t' ht' htt hco ht h1 h2 y hy hval`. Take `⟨π₀, hπ₀, -, -, hres⟩` from `GlobalTheory.LocMod.LevBack.exists_chart p hP`. Establish `he : toEAf D p.e = Formalism.UG.P.afsplitEps D.host.E p.v * toEAf D p.e`. Take `⟨ε, hε, hsum⟩` from `p.above`. Establish `hee : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e`.

Rewrite using `[← hsum, add_mul, p.split.1, mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]`. Rewrite using `[← sub_eq_zero]`. Use `Formalism.UG.P.afsplit_inj _ fun w => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul]`. Distinguish the cases in `hw : w = p.v`.

Substitute `hw` using the available equality. Rewrite using `[Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]`. Rewrite using `[← hee, GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw, mul_zero, sub_zero]`. Establish `hpe : π₀ (toEAf D p.e) = 1` using `by rw [hπ₀]; exact GlobalTheory.LocMod.LevBack.pr_e p`. Establish `heps : π₀ (Formalism.UG.P.afsplitEps D.host.E p.v) = 1`.

Establish `h3` using `congrArg π₀ he`. Rewrite `h3` using `[map_mul, hpe, mul_one]`. Conclude with `h3.symm`. Set `s : Formalism.L2.Herm.intAf D.host.F D.host.E` to `⟨_, Formalism.UG.P.afsplit_IE_int p.v _ hy⟩`. Establish `hs : s ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal`.

Rewrite using `[← Formalism.L2.DIV.resS_eq_zero_iff, hres]`. Express the relevant statement in the definitionally equal form `valuation k (π₀ (Formalism.UG.P.afsplitIE p.v _)) < 1`. Rewrite using `[Formalism.UG.P.afsplit_decomp, map_mul, heps, one_mul, hπ₀]`. Conclude with `hval`. Establish `hv : ∀ b : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b ∈ P.asIdeal → b ∈ p.v.asIdeal` using `fun b hb => by`.

Rewrite using `[GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under p hP]`. Conclude with `hb`. Establish `key : ∀ z ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal, ∃ c ∈ intV D.host.E p.v, Formalism.UG.prV (E` using `D.host.E) p.v (z : Formalism.L2.Herm.intAf D.host.F D.host.E) = Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `incl_eq_mul D.sp.cm p.v P.asIdeal hv (T : 𝓞 D.host.F) t t' ht' (by rw [htt, map_natCast]) hco ht h1 h2 a ha`. Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add a b _ _ ha hb`.

Take `⟨c, hc, ea⟩` from `ha`. Take `⟨d, hd, eb⟩` from `hb`. Conclude with `⟨c + d, add_mem hc hd, by rw [Subring.coe_add, map_add, ea, eb, mul_add]⟩`. Consider the case `smul r a _ ha`. Take `⟨c, hc, ea⟩` from `ha`.

Conclude with `⟨Formalism.UG.prV (E := D.host.E) p.v r * c, mul_mem (Formalism.UG.P.afsplit_prV_int p.v _ r.2) hc, by`. Rewrite using `[smul_eq_mul, Subring.coe_mul, map_mul, ea, mul_left_comm]⟩`. Take `⟨c, hc, e⟩` from `key s hs`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[← e]`.

Conclude with `(Formalism.UG.P.afsplit_prV_IE p.v _).symm`.
-/
theorem eq_mul_of_val_lt_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ (T : ℕ) (t t' : 𝓞 D.host.E), (t' : D.host.E) = star (t : D.host.E) → t * t' = (T : 𝓞 D.host.E) → IsCoprime t t' → t ∈ P.asIdeal → (T : 𝓞 D.host.F) ∈ p.v.asIdeal → (T : 𝓞 D.host.F) ∉ p.v.asIdeal ^ 2 → ∀ y : AE D, Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) ∈ Formalism.BasicNotions.intV D.host.E p.v → valuation k (p.pr y) < 1 → ∃ c ∈ Formalism.BasicNotions.intV D.host.E p.v, Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) = Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
  intro D k _ _ _ _ p P hP T t t' ht' htt hco ht h1 h2 y hy hval
  obtain ⟨π₀, hπ₀, -, -, hres⟩ := GlobalTheory.LocMod.LevBack.exists_chart p hP
  have he : toEAf D p.e = Formalism.UG.P.afsplitEps D.host.E p.v * toEAf D p.e := by
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hee : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_sub, map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
    · rw [← hee, GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw, mul_zero, sub_zero]
  have hpe : π₀ (toEAf D p.e) = 1 := by rw [hπ₀]; exact GlobalTheory.LocMod.LevBack.pr_e p
  have heps : π₀ (Formalism.UG.P.afsplitEps D.host.E p.v) = 1 := by
    have h3 := congrArg π₀ he
    rw [map_mul, hpe, mul_one] at h3
    exact h3.symm
  let s : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨_, Formalism.UG.P.afsplit_IE_int p.v _ hy⟩
  have hs : s ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal := by
    rw [← Formalism.L2.DIV.resS_eq_zero_iff, hres]
    change valuation k (π₀ (Formalism.UG.P.afsplitIE p.v _)) < 1
    rw [Formalism.UG.P.afsplit_decomp, map_mul, heps, one_mul, hπ₀]
    exact hval
  have hv : ∀ b : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b ∈ P.asIdeal → b ∈ p.v.asIdeal := fun b hb => by
    rw [GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under p hP]
    exact hb
  have key : ∀ z ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal, ∃ c ∈ intV D.host.E p.v,
      Formalism.UG.prV (E := D.host.E) p.v (z : Formalism.L2.Herm.intAf D.host.F D.host.E) =
        Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact incl_eq_mul D.sp.cm p.v P.asIdeal hv (T : 𝓞 D.host.F) t t' ht' (by rw [htt, map_natCast]) hco ht h1 h2 a ha
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc, ea⟩ := ha
      obtain ⟨d, hd, eb⟩ := hb
      exact ⟨c + d, add_mem hc hd, by rw [Subring.coe_add, map_add, ea, eb, mul_add]⟩
    | smul r a _ ha =>
      obtain ⟨c, hc, ea⟩ := ha
      exact ⟨Formalism.UG.prV (E := D.host.E) p.v r * c, mul_mem (Formalism.UG.P.afsplit_prV_int p.v _ r.2) hc, by
        rw [smul_eq_mul, Subring.coe_mul, map_mul, ea, mul_left_comm]⟩
  obtain ⟨c, hc, e⟩ := key s hs
  refine ⟨c, hc, ?_⟩
  rw [← e]
  exact (Formalism.UG.P.afsplit_prV_IE p.v _).symm

end GlobalTheory.LocMod.SplitUnif
