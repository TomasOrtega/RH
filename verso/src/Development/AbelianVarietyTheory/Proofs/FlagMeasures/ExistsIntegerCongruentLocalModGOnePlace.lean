import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WithZeroLeOneEqExp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLocGlob

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CongrLoc

/- English proof (translation)
Establish `hle : (D.s.atP q).ιF x ≤ᵥ (D.s.atP q).ιF y` using `((D.s.atP q).val x y).2 h`. Establish `hv` using `(Valuation.vle_iff_le (ValuativeRel.valuation (D.s.atP q).Fp)).1 hle`. Establish `hy' : (D.s.atP q).ιF y ≠ 0` using `(map_ne_zero _).2 hy`. Establish `hpos : 0 < ValuativeRel.valuation (D.s.atP q).Fp ((D.s.atP q).ιF y)` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hy')`. Use `⟨(D.s.atP q).ιF x / (D.s.atP q).ιF y, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Valuation.mem_integer_iff, map_div₀]`. Conclude with `(div_le_one₀ hpos).2 hv`. Clear the denominators using the available nonvanishing facts.
-/
private lemma exists_integer_mul_eq_of_valuation_le (D : D7) (q : PlF D) (x y : D.host.F) (hy : y ≠ 0)
    (h : q.valuation D.host.F x ≤ q.valuation D.host.F y) :
    ∃ β ∈ Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp),
      (D.s.atP q).ιF x = (D.s.atP q).ιF y * β := by
  have hle : (D.s.atP q).ιF x ≤ᵥ (D.s.atP q).ιF y := ((D.s.atP q).val x y).2 h
  have hv := (Valuation.vle_iff_le (ValuativeRel.valuation (D.s.atP q).Fp)).1 hle
  have hy' : (D.s.atP q).ιF y ≠ 0 := (map_ne_zero _).2 hy
  have hpos : 0 < ValuativeRel.valuation (D.s.atP q).Fp ((D.s.atP q).ιF y) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hy')
  refine ⟨(D.s.atP q).ιF x / (D.s.atP q).ιF y, ?_, ?_⟩
  · rw [Valuation.mem_integer_iff, map_div₀]
    exact (div_le_one₀ hpos).2 hv
  · field_simp

/- English proof (translation)
Rewrite using `[(D.s.atP q).O_def]`. Conclude with `isIntegral_algebraMap (R := Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp)) (x := (⟨w, hw⟩ : Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp)))`.
-/
private lemma algebraMap_mem_O_of_mem_integer' (D : D7) (q : PlF D) (w : (D.s.atP q).Fp)
    (hw : w ∈ Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp)) :
    algebraMap (D.s.atP q).Fp (D.s.atP q).Ep w ∈ (D.s.atP q).O := by
  rw [(D.s.atP q).O_def]
  exact isIntegral_algebraMap (R := Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp))
    (x := (⟨w, hw⟩ : Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp)))

/- English proof (translation)
Use `(D.s.atP p).char0` as an intermediate fact. Use `(D.s.atP p).lf` as an intermediate fact. Establish `hg0 : ((gS D : ℕ) : D.host.E) ≠ 0` using `Formalism.L2.SG.Pf.StabIntSh.gS_ne`. Establish `hgN : (gS D : ℕ) ≠ 0`. Introduce `h`.

Apply `hg0` to reduce the goal to its premises. Simplify using `[h]`. Establish `halg : Algebra.IsAlgebraic ℤ D.host.E` using `(IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).mpr inferInstance`. Take `⟨d, hd0, hdint⟩` from `(halg.isAlgebraic e).exists_integral_multiple`. Use `set u : (D.s.atP p).Fp := ((gS D : ℕ) : (D.s.atP p).Fp) * ((d : ℤ) : (D.s.atP p).Fp) with hu`.

Establish `hu0 : u ≠ 0`. Rewrite using `[hu]`. Conclude with `mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)`. Establish `hvu : ValuativeRel.valuation (D.s.atP p).Fp u ≠ 0` using `(Valuation.ne_zero_iff _).2 hu0`. Establish `hnhds : {z : (D.s.atP p).Fp | ValuativeRel.valuation (D.s.atP p).Fp (z - f) < ((Units.mk0 _ hvu : (ValuativeRel.ValueGroupWithZero (D.s.atP p).Fp)ˣ) : ValuativeRel.ValueGroupWithZero (D.s.atP p).Fp)} ∈ nhds f` using `(IsValuativeTopology.mem_nhds_iff').2 ⟨Units.mk0 _ hvu, subset_rfl⟩`.

Take `⟨a, ha⟩` from `(D.s.atP p).dense.mem_nhds hnhds`. Simplify using `only [Set.mem_ofPred_eq, Units.val_mk0] at ha`. Establish `hβ : ValuativeRel.valuation (D.s.atP p).Fp ((f - (D.s.atP p).ιF a) / u) ≤ 1`. Rewrite using `[map_div₀, ← Valuation.map_neg, neg_sub]`. Conclude with `(div_le_one₀ (zero_lt_iff.2 hvu)).2 ha.le`.

Use `⟨algebraMap D.host.F D.host.E a * e, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((f - (D.s.atP p).ιF a) / u) * (D.s.atP p).ιE ((d : ℤ) • e), mul_mem (algebraMap_mem_O_of_mem_integer' D p _ ((Valuation.mem_integer_iff _ _).2 hβ)) (Formalism.L2.SG.Pf.StabIntSh.lg_iota_int p ⟨(d : ℤ) …` and prove the remaining obligations. Rewrite using `[map_mul, (D.s.atP p).compat, zsmul_eq_mul, map_mul, map_intCast, map_natCast, Algebra.smul_def]`. Establish `hsplit : f = (f - (D.s.atP p).ιF a) / u * u + (D.s.atP p).ιF a`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `conv_lhs => rw [hsplit]`. Rewrite using `[hu]`. Simplify using `only [map_add, map_mul, map_natCast, map_intCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exists_smul_sub_eq_gS_mul_mem_O (D : D7) (p : PlF D) (f : (D.s.atP p).Fp) (e : D.host.E) :
    ∃ b : D.host.E, ∃ o ∈ (D.s.atP p).O,
      f • (D.s.atP p).ιE e - (D.s.atP p).ιE b = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  classical
  have := (D.s.atP p).char0
  have := (D.s.atP p).lf
  have hg0 : ((gS D : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Pf.StabIntSh.gS_ne
  have hgN : (gS D : ℕ) ≠ 0 := by
    intro h
    apply hg0
    simp [h]
  have halg : Algebra.IsAlgebraic ℤ D.host.E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).mpr inferInstance
  obtain ⟨d, hd0, hdint⟩ := (halg.isAlgebraic e).exists_integral_multiple

  set u : (D.s.atP p).Fp := ((gS D : ℕ) : (D.s.atP p).Fp) * ((d : ℤ) : (D.s.atP p).Fp) with hu
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)
  have hvu : ValuativeRel.valuation (D.s.atP p).Fp u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have hnhds : {z : (D.s.atP p).Fp | ValuativeRel.valuation (D.s.atP p).Fp (z - f) <
      ((Units.mk0 _ hvu : (ValuativeRel.ValueGroupWithZero (D.s.atP p).Fp)ˣ) : ValuativeRel.ValueGroupWithZero (D.s.atP p).Fp)} ∈ nhds f :=
    (IsValuativeTopology.mem_nhds_iff').2 ⟨Units.mk0 _ hvu, subset_rfl⟩
  obtain ⟨a, ha⟩ := (D.s.atP p).dense.mem_nhds hnhds
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at ha

  have hβ : ValuativeRel.valuation (D.s.atP p).Fp ((f - (D.s.atP p).ιF a) / u) ≤ 1 := by
    rw [map_div₀, ← Valuation.map_neg, neg_sub]
    exact (div_le_one₀ (zero_lt_iff.2 hvu)).2 ha.le
  refine ⟨algebraMap D.host.F D.host.E a * e,
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((f - (D.s.atP p).ιF a) / u) * (D.s.atP p).ιE ((d : ℤ) • e),
    mul_mem (algebraMap_mem_O_of_mem_integer' D p _ ((Valuation.mem_integer_iff _ _).2 hβ))
      (Formalism.L2.SG.Pf.StabIntSh.lg_iota_int p ⟨(d : ℤ) • e, hdint⟩), ?_⟩
  rw [map_mul, (D.s.atP p).compat, zsmul_eq_mul, map_mul, map_intCast, map_natCast, Algebra.smul_def]
  have hsplit : f = (f - (D.s.atP p).ιF a) / u * u + (D.s.atP p).ιF a := by
    field_simp
    ring
  conv_lhs => rw [hsplit]
  rw [hu]
  simp only [map_add, map_mul, map_natCast, map_intCast]
  ring

/- English proof (translation)
Establish `hx : x ∈ Submodule.span (D.s.atP p).Fp (Set.range (D.s.atP p).ιE)`. Rewrite using `[(D.s.atP p).span]`. Conclude with `Submodule.mem_top`. Take `⟨w, rfl⟩` from `(Finsupp.mem_span_range_iff_exists_finsupp).1 hx`. Rewrite using `[Finsupp.sum]`.

Proceed by induction on `w.support using Finset.induction_on with`. Consider the case `empty => exact ⟨0, 0, zero_mem _, by simp⟩`. Consider the case `insert i s hi ih`. Take `⟨b₁, o₁, ho₁, h₁⟩` from `ih`. Take `⟨b₂, o₂, ho₂, h₂⟩` from `exists_smul_sub_eq_gS_mul_mem_O D p (w i) i`.

Use `⟨b₂ + b₁, o₂ + o₁, add_mem ho₂ ho₁, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_insert hi, map_add, mul_add, ← h₁, ← h₂]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exists_pow_mul_finset_sum_mem_subring (D : D7) (p : PlF D) (x : (D.s.atP p).Ep) :
    ∃ b : D.host.E, ∃ o ∈ (D.s.atP p).O,
      x - (D.s.atP p).ιE b = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  classical
  have hx : x ∈ Submodule.span (D.s.atP p).Fp (Set.range (D.s.atP p).ιE) := by
    rw [(D.s.atP p).span]
    exact Submodule.mem_top
  obtain ⟨w, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hx
  rw [Finsupp.sum]
  induction w.support using Finset.induction_on with
  | empty => exact ⟨0, 0, zero_mem _, by simp⟩
  | insert i s hi ih =>
    obtain ⟨b₁, o₁, ho₁, h₁⟩ := ih
    obtain ⟨b₂, o₂, ho₂, h₂⟩ := exists_smul_sub_eq_gS_mul_mem_O D p (w i) i
    refine ⟨b₂ + b₁, o₂ + o₁, add_mem ho₂ ho₁, ?_⟩
    rw [Finset.sum_insert hi, map_add, mul_add, ← h₁, ← h₂]
    ring

/- English proof (translation)
Establish `hfin : {q : PlF D | r ∈ q.asIdeal}.Finite`. Establish `hI : Ideal.span {r} ≠ 0`. Simplify `hr` using `[Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Use `(Ideal.finite_factors hI).subset ?_` and prove the remaining obligations. Introduce `q hq`.

Simplify using `only [Set.mem_ofPred_eq] at hq ⊢`. Conclude with `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)`. Take `⟨y, hy⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert p hfin.toFinset) (fun q : PlF D => q.asIdeal) (fun q => multiplicity q.asIdeal (Ideal.span {r})) (fun q _ => q.prime) (fun q _ q' _ hne h => hne (IsDedekindDomain.HeightOneSpectrum.ext h)) (fun q => if (q : PlF D) = p then …`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hy p (Finset.mem_insert_self _ _)`.

Simplify using `only [if_true] at h`. Rewrite using `[p.intValuation_eq_exp_neg_multiplicity hr]`. Conclude with `(p.intValuation_le_pow_iff_mem _ _).2 h`. Introduce `q hq`. Distinguish the cases in `hqs : r ∈ q.asIdeal`.

Establish `h` using `hy q (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 hqs))`. Simplify using `only [hq, if_false, sub_zero] at h`. Rewrite using `[q.intValuation_eq_exp_neg_multiplicity hr]`. Conclude with `(q.intValuation_le_pow_iff_mem _ _).2 h`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hqs]`.

Conclude with `q.intValuation_le_one _`.
-/
private lemma exists_intValuation_sub_one_le_and_le_elsewhere (D : D7) (p : PlF D) (r : 𝓞 D.host.F) (hr : r ≠ 0) :
    ∃ t : 𝓞 D.host.F, p.intValuation (t - 1) ≤ p.intValuation r ∧
      ∀ q : PlF D, q ≠ p → q.intValuation t ≤ q.intValuation r := by
  classical
  have hfin : {q : PlF D | r ∈ q.asIdeal}.Finite := by
    have hI : Ideal.span {r} ≠ 0 := by
      simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
    refine (Ideal.finite_factors hI).subset ?_
    intro q hq
    simp only [Set.mem_ofPred_eq] at hq ⊢
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert p hfin.toFinset)
    (fun q : PlF D => q.asIdeal) (fun q => multiplicity q.asIdeal (Ideal.span {r}))
    (fun q _ => q.prime) (fun q _ q' _ hne h => hne (IsDedekindDomain.HeightOneSpectrum.ext h))
    (fun q => if (q : PlF D) = p then 1 else 0)
  refine ⟨y, ?_, ?_⟩
  · have h := hy p (Finset.mem_insert_self _ _)
    simp only [if_true] at h
    rw [p.intValuation_eq_exp_neg_multiplicity hr]
    exact (p.intValuation_le_pow_iff_mem _ _).2 h
  · intro q hq
    by_cases hqs : r ∈ q.asIdeal
    · have h := hy q (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 hqs))
      simp only [hq, if_false, sub_zero] at h
      rw [q.intValuation_eq_exp_neg_multiplicity hr]
      exact (q.intValuation_le_pow_iff_mem _ _).2 h
    · rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hqs]
      exact q.intValuation_le_one _

/- English proof (translation)
Introduce `D p c hc`. Establish `hg0 : ((gS D : ℕ) : D.host.E) ≠ 0` using `Formalism.L2.SG.Pf.StabIntSh.gS_ne`. Establish `hgN : (gS D : ℕ) ≠ 0`. Introduce `h`. Apply `hg0` to reduce the goal to its premises.

Simplify using `[h]`. Take `⟨b₀, o₀, ho₀, h₀⟩` from `exists_pow_mul_finset_sum_mem_subring D p c`. Establish `halg : Algebra.IsAlgebraic ℤ D.host.E` using `(IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).mpr inferInstance`. Take `⟨d, hd0, hdint⟩` from `(halg.isAlgebraic b₀).exists_integral_multiple`. Use `set r : 𝓞 D.host.F := ((gS D : ℕ) : 𝓞 D.host.F) * ((d : ℤ) : 𝓞 D.host.F) with hr`.

Establish `hr0 : r ≠ 0` using `mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)`. Take `⟨t, ht₁, ht₂⟩` from `exists_intValuation_sub_one_le_and_le_elsewhere D p r hr0`. Use `set a : D.host.E := algebraMap D.host.F D.host.E (t : D.host.F) * b₀ with ha`. Establish `hιa : ∀ q : PlF D, (D.s.atP q).ιE a = algebraMap (D.s.atP q).Fp (D.s.atP q).Ep ((D.s.atP q).ιF (t : D.host.F)) * (D.s.atP q).ιE b₀`. Introduce `q`.

Rewrite using `[ha, map_mul, (D.s.atP q).compat]`. Establish `hG : ∀ q : PlF D, (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) ∈ (D.s.atP q).O`. Introduce `q`. Rewrite using `[map_natCast]`. Conclude with `natCast_mem _ _`.

Establish `hb₀ : (D.s.atP p).ιE b₀ ∈ (D.s.atP p).O`. Establish `: (D.s.atP p).ιE b₀ = c - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o₀`. Rewrite using `[← h₀]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `sub_mem hc (mul_mem (hG p) ho₀)`. Establish `hdb : ∀ q : PlF D, (D.s.atP q).ιE ((d : ℤ) • b₀) ∈ (D.s.atP q).O` using `fun q => Formalism.L2.SG.Pf.StabIntSh.lg_iota_int q ⟨(d : ℤ) • b₀, hdint⟩`. Establish `hp : ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE a - c = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o`. Establish `hle : p.valuation D.host.F ((t : D.host.F) - 1) ≤ p.valuation D.host.F ((gS D : ℕ) : D.host.F)`. Establish `e1 : ((t : D.host.F) - 1) = algebraMap (𝓞 D.host.F) D.host.F (t - 1)` using `by simp`.

Establish `e2 : ((gS D : ℕ) : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F ((gS D : ℕ) : 𝓞 D.host.F)` using `by simp`. Rewrite using `[e1, e2, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Use `ht₁.trans ?_` and prove the remaining obligations. Rewrite using `[hr, map_mul]`. Conclude with `mul_le_of_le_one_right' (p.intValuation_le_one _)`.

Take `⟨β, hβ, hβe⟩` from `exists_integer_mul_eq_of_valuation_le D p _ _ (by exact_mod_cast hgN) hle`. Use `⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep β * (D.s.atP p).ιE b₀ - o₀, sub_mem (mul_mem (algebraMap_mem_O_of_mem_integer' D p β hβ) hb₀) ho₀, ?_⟩` and prove the remaining obligations. Establish `ht : (D.s.atP p).ιF (t : D.host.F) = (D.s.atP p).ιF ((gS D : ℕ) : D.host.F) * β + 1`. Rewrite using `[← hβe, map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hιa p, ht, map_add, map_mul, map_one, map_natCast, map_natCast, map_natCast]`. Establish `: c = (D.s.atP p).ιE b₀ + ((gS D : ℕ) : (D.s.atP p).Ep) * o₀`. Rewrite using `[← map_natCast (D.s.atP p).ιE, ← h₀]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hq : ∀ q : PlF D, q ≠ p → ∃ o ∈ (D.s.atP q).O, (D.s.atP q).ιE a = (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) * o`. Introduce `q hqp`. Establish `hle : q.valuation D.host.F (t : D.host.F) ≤ q.valuation D.host.F (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F))`. Establish `e1 : (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F r`.

Simplify using `[hr]`. Rewrite using `[e1, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `ht₂ q hqp`. Establish `hne : (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F)) ≠ 0` using `mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)`. Take `⟨β, hβ, hβe⟩` from `exists_integer_mul_eq_of_valuation_le D q _ _ hne hle`.

Use `⟨algebraMap (D.s.atP q).Fp (D.s.atP q).Ep β * (D.s.atP q).ιE ((d : ℤ) • b₀), mul_mem (algebraMap_mem_O_of_mem_integer' D q β hβ) (hdb q), ?_⟩` and prove the remaining obligations. Rewrite using `[hιa q, hβe, zsmul_eq_mul]`. Simplify using `only [map_mul, map_intCast, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hloc : ∀ q : PlF D, (D.s.atP q).ιE a ∈ (D.s.atP q).O`.

Introduce `q`. Distinguish the cases in `hqp : q = p`. Substitute `hqp` using the available equality. Take `⟨o, ho, he⟩` from `hp`. Establish `: (D.s.atP q).ιE a = c + (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) * o`.

Rewrite using `[← he]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem hc (mul_mem (hG q) ho)`. Take `⟨o, ho, he⟩` from `hq q hqp`.

Rewrite using `[he]`. Conclude with `mul_mem (hG q) ho`. Establish `hint : IsIntegral ℤ a` using `Formalism.L2.SG.Pf.StabIntSh.lg_int_of_loc a hloc`. Conclude with `⟨⟨a, hint⟩, hp, hq⟩`.
-/
theorem exists_int_congr_gS : ∀ (D : D7) (p : PlF D) (c : (D.s.atP p).Ep), c ∈ (D.s.atP p).O → ∃ a : 𝓞 D.host.E, (∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (a : D.host.E) - c = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) ∧ ∀ p' : PlF D, p' ≠ p → ∃ o ∈ (D.s.atP p').O, (D.s.atP p').ιE (a : D.host.E) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) * o := by
  intro D p c hc
  classical
  have hg0 : ((gS D : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Pf.StabIntSh.gS_ne
  have hgN : (gS D : ℕ) ≠ 0 := by
    intro h
    apply hg0
    simp [h]

  obtain ⟨b₀, o₀, ho₀, h₀⟩ := exists_pow_mul_finset_sum_mem_subring D p c
  have halg : Algebra.IsAlgebraic ℤ D.host.E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).mpr inferInstance
  obtain ⟨d, hd0, hdint⟩ := (halg.isAlgebraic b₀).exists_integral_multiple
  set r : 𝓞 D.host.F := ((gS D : ℕ) : 𝓞 D.host.F) * ((d : ℤ) : 𝓞 D.host.F) with hr
  have hr0 : r ≠ 0 := mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)

  obtain ⟨t, ht₁, ht₂⟩ := exists_intValuation_sub_one_le_and_le_elsewhere D p r hr0
  set a : D.host.E := algebraMap D.host.F D.host.E (t : D.host.F) * b₀ with ha
  have hιa : ∀ q : PlF D, (D.s.atP q).ιE a =
      algebraMap (D.s.atP q).Fp (D.s.atP q).Ep ((D.s.atP q).ιF (t : D.host.F)) * (D.s.atP q).ιE b₀ := by
    intro q
    rw [ha, map_mul, (D.s.atP q).compat]
  have hG : ∀ q : PlF D, (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) ∈ (D.s.atP q).O := by
    intro q
    rw [map_natCast]
    exact natCast_mem _ _
  have hb₀ : (D.s.atP p).ιE b₀ ∈ (D.s.atP p).O := by
    have : (D.s.atP p).ιE b₀ = c - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o₀ := by
      rw [← h₀]; ring
    rw [this]
    exact sub_mem hc (mul_mem (hG p) ho₀)
  have hdb : ∀ q : PlF D, (D.s.atP q).ιE ((d : ℤ) • b₀) ∈ (D.s.atP q).O :=
    fun q => Formalism.L2.SG.Pf.StabIntSh.lg_iota_int q ⟨(d : ℤ) • b₀, hdint⟩

  have hp : ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE a - c = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
    have hle : p.valuation D.host.F ((t : D.host.F) - 1) ≤ p.valuation D.host.F ((gS D : ℕ) : D.host.F) := by
      have e1 : ((t : D.host.F) - 1) = algebraMap (𝓞 D.host.F) D.host.F (t - 1) := by simp
      have e2 : ((gS D : ℕ) : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F ((gS D : ℕ) : 𝓞 D.host.F) := by simp
      rw [e1, e2, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      refine ht₁.trans ?_
      rw [hr, map_mul]
      exact mul_le_of_le_one_right' (p.intValuation_le_one _)
    obtain ⟨β, hβ, hβe⟩ := exists_integer_mul_eq_of_valuation_le D p _ _ (by exact_mod_cast hgN) hle
    refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep β * (D.s.atP p).ιE b₀ - o₀,
      sub_mem (mul_mem (algebraMap_mem_O_of_mem_integer' D p β hβ) hb₀) ho₀, ?_⟩
    have ht : (D.s.atP p).ιF (t : D.host.F) = (D.s.atP p).ιF ((gS D : ℕ) : D.host.F) * β + 1 := by
      rw [← hβe, map_sub, map_one]; ring
    rw [hιa p, ht, map_add, map_mul, map_one, map_natCast, map_natCast, map_natCast]
    have : c = (D.s.atP p).ιE b₀ + ((gS D : ℕ) : (D.s.atP p).Ep) * o₀ := by
      rw [← map_natCast (D.s.atP p).ιE, ← h₀]; ring
    rw [this]
    ring

  have hq : ∀ q : PlF D, q ≠ p →
      ∃ o ∈ (D.s.atP q).O, (D.s.atP q).ιE a = (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) * o := by
    intro q hqp
    have hle : q.valuation D.host.F (t : D.host.F) ≤
        q.valuation D.host.F (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F)) := by
      have e1 : (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F r := by
        simp [hr]
      rw [e1, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact ht₂ q hqp
    have hne : (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F)) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)
    obtain ⟨β, hβ, hβe⟩ := exists_integer_mul_eq_of_valuation_le D q _ _ hne hle
    refine ⟨algebraMap (D.s.atP q).Fp (D.s.atP q).Ep β * (D.s.atP q).ιE ((d : ℤ) • b₀),
      mul_mem (algebraMap_mem_O_of_mem_integer' D q β hβ) (hdb q), ?_⟩
    rw [hιa q, hβe, zsmul_eq_mul]
    simp only [map_mul, map_intCast, map_natCast]
    ring

  have hloc : ∀ q : PlF D, (D.s.atP q).ιE a ∈ (D.s.atP q).O := by
    intro q
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨o, ho, he⟩ := hp
      have : (D.s.atP q).ιE a = c + (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) * o := by
        rw [← he]; ring
      rw [this]
      exact add_mem hc (mul_mem (hG q) ho)
    · obtain ⟨o, ho, he⟩ := hq q hqp
      rw [he]
      exact mul_mem (hG q) ho
  have hint : IsIntegral ℤ a := Formalism.L2.SG.Pf.StabIntSh.lg_int_of_loc a hloc
  exact ⟨⟨a, hint⟩, hp, hq⟩

end GlobalTheory.CongrLoc
