import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNormEqDrViaPower
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

namespace GlobalTheory.LieSmooth

/- English proof (translation)
Establish `h : x ∈ (NormedField.valuation (K` using `C)).integer := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top`. Rewrite `h` using `[Valuation.mem_integer_iff]`. Conclude with `h` after adjusting the coercions.
-/
theorem norm_le_one_of_isIntegral_ultra {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff] at h
  exact_mod_cast h

/- English proof (translation)
Introduce `F _ _ K _ _ v hp ε θ 𝔞 hfg hne`. Use `set p := resP v with hpdef`. Establish `hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal` using `residueCharacteristic_mem v`. Establish `hq` using `hp.out`. Use `set c := -Real.log (ε.w (p : AlgebraicClosure F)) / Real.log p with hcdef`.

Establish `hw1 : ε.w (p : AlgebraicClosure F) < 1`. Establish `h : (p : AlgebraicClosure F) = algebraMap F _ (algebraMap (𝓞 F) F (p : 𝓞 F))` using `by simp`. Rewrite using `[h, ε.w_alg]`. Conclude with `(v.adicAbv_coe_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 hv`. Establish `hw0 : 0 < ε.w (p : AlgebraicClosure F)` using `ε.w.pos (Nat.cast_ne_zero.2 hq.ne_zero)`.

Establish `hlp : 0 < Real.log p` using `Real.log_pos (by exact_mod_cast hq.one_lt)`. Establish `hc : 0 < c` using `div_pos (neg_pos.2 (Real.log_neg hw0 hw1)) hlp`. Use `set ι := (ioOf p ε).comp θ with hι`. Establish `hw : ∀ a : K, ε.w (θ a) = ‖ι a‖ ^ c` using `fun a => by`. Rewrite using `[hι, RingHom.comp_apply]`.

Conclude with `GlobalTheory.CovHt.Link.w_eq_norm_ioOf_rpow p v hv ε (θ a)`. Take `⟨S, hS⟩` from `hfg`. Establish `hSne : S.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce and unpack `rfl`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hS]`. Simplify using the standard rewrite rules. Take `⟨g, hgS, hg⟩` from `S.exists_max_image (fun a => ‖ι a‖) hSne`. Establish `hg𝔞 : g ∈ 𝔞` using `hS ▸ Submodule.subset_span hgS`.

Establish `hint : ∀ r : 𝓞 K, ‖ι (r : K)‖ ≤ 1` using `fun r => norm_le_one_of_isIntegral_ultra (map_isIntegral_int ι (RingOfIntegers.isIntegral_coe r))`. Establish `hbd : ∀ a ∈ 𝔞, ‖ι a‖ ≤ ‖ι g‖`. Introduce `a ha`. Rewrite `ha` using `[← hS]`. Proceed by induction on `ha using Submodule.span_induction with`.

Consider the case `mem x hx => exact hg x hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)`.

Consider the case `smul r x _ hx`. Rewrite using `[Algebra.smul_def, map_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hs1 : (⨆ a : 𝔞, ‖ι a‖) = ‖ι g‖` using `le_antisymm (ciSup_le fun a => hbd a a.2) (le_ciSup (f := fun a : 𝔞 => ‖ι a‖) ⟨‖ι g‖, by rintro _ ⟨a, rfl⟩; exact hbd a a.2⟩ ⟨g, hg𝔞⟩)`. Establish `hs2 : (⨆ a : 𝔞, ε.w (θ a)) = ‖ι g‖ ^ c`.

Repeatedly rewrite using `[hw]`. Conclude with `le_antisymm (ciSup_le fun a => Real.rpow_le_rpow (norm_nonneg _) (hbd a a.2) hc.le) (le_ciSup (f := fun a : 𝔞 => ‖ι a‖ ^ c) ⟨‖ι g‖ ^ c, by rintro _ ⟨a, rfl⟩; exact Real.rpow_le_rpow (norm_nonneg _) (hbd a a.2) hc.le⟩ ⟨g, hg𝔞⟩)`. Rewrite using `[hs1, hs2]`. Break down `(norm_nonneg (ι g)).eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0, Real.zero_rpow hc.ne', Real.log_zero, mul_zero]`.

Rewrite using `[Real.log_rpow h0]`.
-/
theorem log_iSup_w_eq_mul_log_iSup_norm : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 F)) [Fact (resP v).Prime] (ε : GlobalTheory.TrueGeo.Ext v) (θ : K →+* AlgebraicClosure F) (𝔞 : Submodule (𝓞 K) K), 𝔞.FG → 𝔞 ≠ ⊥ → (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (⨆ a : 𝔞, ‖((ioOf (resP v) ε).comp θ) a‖) = Real.log (⨆ a : 𝔞, ε.w (θ a)) := by
  intro F _ _ K _ _ v hp ε θ 𝔞 hfg hne
  set p := resP v with hpdef
  have hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := residueCharacteristic_mem v
  have hq := hp.out
  set c := -Real.log (ε.w (p : AlgebraicClosure F)) / Real.log p with hcdef
  have hw1 : ε.w (p : AlgebraicClosure F) < 1 := by
    have h : (p : AlgebraicClosure F) = algebraMap F _ (algebraMap (𝓞 F) F (p : 𝓞 F)) := by simp
    rw [h, ε.w_alg]
    exact (v.adicAbv_coe_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 hv
  have hw0 : 0 < ε.w (p : AlgebraicClosure F) := ε.w.pos (Nat.cast_ne_zero.2 hq.ne_zero)
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hc : 0 < c := div_pos (neg_pos.2 (Real.log_neg hw0 hw1)) hlp
  set ι := (ioOf p ε).comp θ with hι
  have hw : ∀ a : K, ε.w (θ a) = ‖ι a‖ ^ c := fun a => by
    rw [hι, RingHom.comp_apply]; exact GlobalTheory.CovHt.Link.w_eq_norm_ioOf_rpow p v hv ε (θ a)
  obtain ⟨S, hS⟩ := hfg
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hne
    rw [← hS]; simp
  obtain ⟨g, hgS, hg⟩ := S.exists_max_image (fun a => ‖ι a‖) hSne
  have hg𝔞 : g ∈ 𝔞 := hS ▸ Submodule.subset_span hgS
  have hint : ∀ r : 𝓞 K, ‖ι (r : K)‖ ≤ 1 := fun r =>
    norm_le_one_of_isIntegral_ultra (map_isIntegral_int ι (RingOfIntegers.isIntegral_coe r))
  have hbd : ∀ a ∈ 𝔞, ‖ι a‖ ≤ ‖ι g‖ := by
    intro a ha
    rw [← hS] at ha
    induction ha using Submodule.span_induction with
    | mem x hx => exact hg x hx
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul, norm_mul]
      calc ‖ι (algebraMap (𝓞 K) K r)‖ * ‖ι x‖ ≤ 1 * ‖ι g‖ :=
            mul_le_mul (hint r) hx (norm_nonneg _) zero_le_one
        _ = ‖ι g‖ := one_mul _
  have hs1 : (⨆ a : 𝔞, ‖ι a‖) = ‖ι g‖ :=
    le_antisymm (ciSup_le fun a => hbd a a.2)
      (le_ciSup (f := fun a : 𝔞 => ‖ι a‖) ⟨‖ι g‖, by rintro _ ⟨a, rfl⟩; exact hbd a a.2⟩ ⟨g, hg𝔞⟩)
  have hs2 : (⨆ a : 𝔞, ε.w (θ a)) = ‖ι g‖ ^ c := by
    simp_rw [hw]
    exact le_antisymm (ciSup_le fun a => Real.rpow_le_rpow (norm_nonneg _) (hbd a a.2) hc.le)
      (le_ciSup (f := fun a : 𝔞 => ‖ι a‖ ^ c)
        ⟨‖ι g‖ ^ c, by rintro _ ⟨a, rfl⟩; exact Real.rpow_le_rpow (norm_nonneg _) (hbd a a.2) hc.le⟩ ⟨g, hg𝔞⟩)
  rw [hs1, hs2]
  rcases (norm_nonneg (ι g)).eq_or_lt with h0 | h0
  · rw [← h0, Real.zero_rpow hc.ne', Real.log_zero, mul_zero]
  · rw [Real.log_rpow h0]

end GlobalTheory.LieSmooth
