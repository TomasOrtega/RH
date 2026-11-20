import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LaArtin

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Hi.AxU
open GlobalTheory.SplitPts
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}
/- English proof (translation)
The claim follows from `((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L) (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w w').1 h).imp_right eq_conjSrc`.
-/
private theorem sameOver {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    w' = w ∨ w = conjSrc (conjE L) w' :=
  ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w w').1 h).imp_right eq_conjSrc
/- English proof (translation)
Establish `h` using `comp_eq x u`. Rewrite using `[← inv_inj]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_eq_left_inv h]`. Both sides reduce to the same expression.
-/
private theorem cLoc_conj (x : UA L n) (u : Plc L) :
    cLoc u x = invT n _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE L) u) (cLoc (conjSrc (conjE L) u) x)) := by
  have h := comp_eq x u
  rw [← inv_inj]
  apply Units.ext
  rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv h]
  rfl
/- English proof (translation)
Establish `h : valuation (w.adicCompletion L) x ≤ valuation (w.adicCompletion L) 1 ↔ Valued.v x ≤ Valued.v (1 : w.adicCompletion L)`. Rewrite using `[← Valuation.Compatible.vle_iff_le]`. Conclude with `Iff.rfl`. Express the relevant statement in the definitionally equal form `valuation _ x ≤ 1 ↔ _`. Simplify using `using h`.
-/
private theorem mem_O {w : Plc L} (x : w.adicCompletion L) : x ∈ 𝒪[w.adicCompletion L] ↔ Valued.v x ≤ 1 := by
  have h : valuation (w.adicCompletion L) x ≤ valuation (w.adicCompletion L) 1 ↔
      Valued.v x ≤ Valued.v (1 : w.adicCompletion L) := by
    rw [← Valuation.Compatible.vle_iff_le]
    exact Iff.rfl
  change valuation _ x ≤ 1 ↔ _
  simpa using h
/- English proof (translation)
Break down `sameOver h with rfl | rfl` into its components or cases. Conclude with `hx`. Rewrite using `[cLoc_conj, hx, map_one, map_one]`.
-/
private theorem cLoc_one {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : UA L n)
    (hx : cLoc w x = 1) : cLoc w' x = 1 := by
  rcases sameOver h with rfl | rfl
  · exact hx
  · rw [cLoc_conj, hx, map_one, map_one]
/- English proof (translation)
Break down `sameOver h with rfl | rfl` into its components or cases. Conclude with `hx`. Rewrite using `[cLoc_conj]`. Rewrite `hx`, the goal using `[GlobalTheory.SplitFlip.mem_KO_iff]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Conclude with `(mem_O _).2 (((conjLoc_spec (conjE L) w').2.2 _).trans_le ((mem_O _).1 (hx.2 j i)))`. Conclude with `(mem_O _).2 (((conjLoc_spec (conjE L) w').2.2 _).trans_le ((mem_O _).1 (hx.1 j i)))`.
-/
private theorem cLoc_KO {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : UA L n)
    (hx : cLoc w x ∈ KO (w.adicCompletion L) (Fin n)) : cLoc w' x ∈ KO (w'.adicCompletion L) (Fin n) := by
  rcases sameOver h with rfl | rfl
  · exact hx
  · rw [cLoc_conj]
    rw [GlobalTheory.SplitFlip.mem_KO_iff] at hx ⊢
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact (mem_O _).2 (((conjLoc_spec (conjE L) w').2.2 _).trans_le ((mem_O _).1 (hx.2 j i)))
    · exact (mem_O _).2 (((conjLoc_spec (conjE L) w').2.2 _).trans_le ((mem_O _).1 (hx.1 j i)))
/- English proof (translation)
Establish `key : ∀ u : Plc L, ((l : ℕ) : 𝓞 L) ∈ u.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.under (𝓞 (Lp L))).asIdeal` using `fun u => by`. Express the relevant statement in the definitionally equal form `_ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ u.asIdeal`. Rewrite using `[map_natCast]`. Rewrite using `[key, key, h]`.
-/
private theorem l_iff {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    ((l : ℕ) : 𝓞 L) ∈ w'.asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  have key : ∀ u : Plc L, ((l : ℕ) : 𝓞 L) ∈ u.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.under (𝓞 (Lp L))).asIdeal := fun u => by
    change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ u.asIdeal
    rw [map_natCast]
  rw [key, key, h]
/- English proof (translation)
Unfold `CaseU.cmp`. Rewrite using `[dif_pos h]`. Both sides reduce to the same expression.
-/
private theorem cmp_eq {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl
/- English proof (translation)
Unfold `CaseU.cmp`. Rewrite using `[dif_neg (not_not.2 h)]`. Both sides reduce to the same expression.
-/
private theorem cmp_l {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (x : Ga l L n) : cmp n w x = 1 := by
  unfold CaseU.cmp
  rw [dif_neg (not_not.2 h)]
  rfl
/- English proof (translation)
Take `⟨x, rfl⟩` from `(away l L n).rangeRestrict_surjective x`. Take `⟨y, rfl⟩` from `(away l L n).rangeRestrict_surjective y`. Use `Subtype.ext (funext fun w => ?_)` and prove the remaining obligations. Use `h w.1` as an intermediate fact. Rewrite `this` using `[cmp_eq w.2, cmp_eq w.2]`. Then use the resulting hypothesis.
-/
private theorem ga_ext {x y : Ga l L n} (h : ∀ w, cmp n w x = cmp n w y) : x = y := by
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  obtain ⟨y, rfl⟩ := (away l L n).rangeRestrict_surjective y
  refine Subtype.ext (funext fun w => ?_)
  have := h w.1
  rwa [cmp_eq w.2, cmp_eq w.2] at this
/- English proof (translation)
Distinguish the cases in `hl : ((l : ℕ) : 𝓞 L) ∈ w'.asIdeal`. Conclude with `cmp_l hl x`. Take `⟨x, rfl⟩` from `(away l L n).rangeRestrict_surjective x`. Rewrite `hx` using `[cmp_eq (mt (l_iff h).2 hl)]`. Rewrite using `[cmp_eq hl]`.

Conclude with `cLoc_one h x hx`.
-/
private theorem cmp_one {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : Ga l L n)
    (hx : cmp n w x = 1) : cmp n w' x = 1 := by
  by_cases hl : ((l : ℕ) : 𝓞 L) ∈ w'.asIdeal
  · exact cmp_l hl x
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  rw [cmp_eq (mt (l_iff h).2 hl)] at hx
  rw [cmp_eq hl]
  exact cLoc_one h x hx
/- English proof (translation)
Distinguish the cases in `hl : ((l : ℕ) : 𝓞 L) ∈ w'.asIdeal`. Rewrite using `[cmp_l hl x]`. Conclude with `one_mem _`. Take `⟨x, rfl⟩` from `(away l L n).rangeRestrict_surjective x`. Rewrite `hx` using `[cmp_eq (mt (l_iff h).2 hl)]`.

Rewrite using `[cmp_eq hl]`. Conclude with `cLoc_KO h x hx`.
-/
private theorem cmp_KO {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : Ga l L n)
    (hx : cmp n w x ∈ KO (w.adicCompletion L) (Fin n)) : cmp n w' x ∈ KO (w'.adicCompletion L) (Fin n) := by
  by_cases hl : ((l : ℕ) : 𝓞 L) ∈ w'.asIdeal
  · rw [cmp_l hl x]
    exact one_mem _
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  rw [cmp_eq (mt (l_iff h).2 hl)] at hx
  rw [cmp_eq hl]
  exact cLoc_KO h x hx
variable (s : HidaSetting l L Ω)
/- English proof (translation)
Use extensionality with `x`. Conclude with `(s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)`.
-/
private theorem under_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)
/- English proof (translation)
Simplify using `only [locA, Subgroup.mem_iInf, MonoidHom.mem_ker]`. Both sides reduce to the same expression.
-/
private theorem mem_locA {w : Plc L} {x : Ub n s} :
    x ∈ locA n s w ↔ ∀ w' : Plc L, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) → cmp n w' (x : Ga l L n) = 1 := by
  simp only [locA, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rfl
/- English proof (translation)
Unfold `sec`. Use `split_ifs`. Conclude with `Subtype.property _`. Conclude with `one_mem _`.
-/
private theorem sec_mem (w : Plc L) (g : GLw n w) : sec n s w g ∈ locA n s w := by
  unfold sec
  split_ifs
  · exact Subtype.property _
  · exact one_mem _
/- English proof (translation)
Use `Subtype.ext (ga_ext fun w' => ?_)` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]`. Distinguish the cases in `h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))`. Rewrite using `[cmp_one h _ hu, one_mul, mul_one]`. Rewrite using `[(mem_locA s).1 hx w' h, one_mul, mul_one]`.
-/
private theorem comm {w : Plc L} {u x : Ub n s} (hu : cmp n w (u : Ga l L n) = 1) (hx : x ∈ locA n s w) :
    Commute u x := by
  refine Subtype.ext (ga_ext fun w' => ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  by_cases h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
  · rw [cmp_one h _ hu, one_mul, mul_one]
  · rw [(mem_locA s).1 hx w' h, one_mul, mul_one]
/- English proof (translation)
The claim follows from `comm s ((mem_locA s).1 (sec_mem s w g) w' h) (sec_mem s w' g')`.
-/
private theorem comm' {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) (g : GLw n w) (g' : GLw n w') :
    Commute (sec n s w g) (sec n s w' g') :=
  comm s ((mem_locA s).1 (sec_mem s w g) w' h) (sec_mem s w' g')
/- English proof (translation)
Use `Subtype.ext (funext fun u => ?_)` and prove the remaining obligations. Use `(mem_locA s).1 (sec_mem s w g) (s.w u) fun e => h ?_` and prove the remaining obligations. Rewrite using `[← e, under_w]`. Conclude with `Or.inr (Or.inl u.2)`.
-/
private theorem toKT_sec {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) (g : GLw n w) : toKT n s (sec n s w g) = 1 := by
  refine Subtype.ext (funext fun u => ?_)
  refine (mem_locA s).1 (sec_mem s w g) (s.w u) fun e => h ?_
  rw [← e, under_w]
  exact Or.inr (Or.inl u.2)
/- English proof (translation)
Introduce `e` and use `h (Or.inl (by change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal rwa [map_natCast]))`.
-/
private theorem away_l {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun e =>
  h (Or.inl (by
    change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal
    rwa [map_natCast]))
variable {s} {V : s.Lev} (Q : QData V)
/- English proof (translation)
Simplify using `only [UQ, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap]`. Both sides reduce to the same expression.
-/
private theorem mem_UQ {x : Ub n s} : x ∈ UQ n Q ↔
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cmp n w (x : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) ∧
      ∀ q, cmp n (Q.wq q) (x : Ga l L n) = 1 := by
  simp only [UQ, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap]
  rfl
/- English proof (translation)
Rewrite using `[Q.range]`. Conclude with `Or.inr ⟨q, rfl⟩`.
-/
private theorem wq_mem (q : Q.Q) : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
  rw [Q.range]
  exact Or.inr ⟨q, rfl⟩
/- English proof (translation)
Establish `hc` using `((secU l L Ω s n hn w hs).2 fun h => hw (V.sub h)).2.1 k`. Use `(mem_UQ Q).2 ⟨fun w' _ => ?_, fun q => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))`. Conclude with `cmp_KO h _ (by rwa [hc])`. Rewrite using `[(mem_locA s).1 (sec_mem s w k) w' h]`.

Conclude with `one_mem _`. Conclude with `(mem_locA s).1 (sec_mem s w k) _ fun e => hw (e ▸ wq_mem Q q)`.
-/
private theorem sec_KO (hn : 1 ≤ n) {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ V.S') (hs : IsSplitAt w) {k : GLw n w}
    (hk : k ∈ KO (w.adicCompletion L) (Fin n)) : sec n s w k ∈ UQ n Q := by
  have hc := ((secU l L Ω s n hn w hs).2 fun h => hw (V.sub h)).2.1 k
  refine (mem_UQ Q).2 ⟨fun w' _ => ?_, fun q => ?_⟩
  · by_cases h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · exact cmp_KO h _ (by rwa [hc])
    · rw [(mem_locA s).1 (sec_mem s w k) w' h]
      exact one_mem _
  · exact (mem_locA s).1 (sec_mem s w k) _ fun e => hw (e ▸ wq_mem Q q)
/- English proof (translation)
Establish `hc` using `((secU l L Ω s n hn w hs).2 fun h => hw (V.sub h)).2.1`. Establish `hk` using `((mem_UQ Q).1 hu).1 w hw`. Use `⟨_, hk, (sec n s w (cmp n w (u : Ga l L n)))⁻¹ * u, mul_mem (inv_mem (sec_KO Q hn hw hs hk)) hu, (mul_inv_cancel_left _ _).symm, fun g => comm s ?_ (sec_mem s w g)⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hc, inv_mul_cancel]`.
-/
private theorem dec (hn : 1 ≤ n) {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ V.S') (hs : IsSplitAt w) {u : Ub n s}
    (hu : u ∈ UQ n Q) : ∃ k ∈ KO (w.adicCompletion L) (Fin n), ∃ u' ∈ UQ n Q,
      u = sec n s w k * u' ∧ ∀ g, Commute u' (sec n s w g) := by
  have hc := ((secU l L Ω s n hn w hs).2 fun h => hw (V.sub h)).2.1
  have hk := ((mem_UQ Q).1 hu).1 w hw
  refine ⟨_, hk, (sec n s w (cmp n w (u : Ga l L n)))⁻¹ * u, mul_mem (inv_mem (sec_KO Q hn hw hs hk)) hu,
    (mul_inv_cancel_left _ _).symm, fun g => comm s ?_ (sec_mem s w g)⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hc, inv_mul_cancel]
variable (s) in
/- English proof (translation)
Take `⟨hb, hc, hm⟩` from `(secU l L Ω s n hn w hs).2 hw`. Conclude with `congrArg Subtype.val (hb.1 (a₁ := ⟨_, hm _⟩) (a₂ := ⟨x, hx⟩) (hc _))`.
-/
private theorem sec_cmp (hn : 1 ≤ n) {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ s.S) (hs : IsSplitAt w) {x : Ub n s}
    (hx : x ∈ locA n s w) : sec n s w (cmp n w (x : Ga l L n)) = x := by
  obtain ⟨hb, hc, hm⟩ := (secU l L Ω s n hn w hs).2 hw
  exact congrArg Subtype.val (hb.1 (a₁ := ⟨_, hm _⟩) (a₂ := ⟨x, hx⟩) (hc _))
variable (s) in
/- English proof (translation)
Establish `hw' : w'.under (𝓞 (Lp L)) ∉ s.S` using `by rwa [h]`. Establish `hc` using `((secU l L Ω s n hn w hs).2 hw).2.1`. Establish `hc'` using `((secU l L Ω s n hn w' hs').2 hw').2.1`. Establish `h1 : ∀ g, sec n s w (cmp n w (sec n s w' g : Ga l L n)) = sec n s w' g` using `fun g => sec_cmp s hn hw hs ((mem_locA s).2 fun u hu => (mem_locA s).1 (sec_mem s w' g) u (by rwa [h]))`. Establish `h2 : ∀ g, sec n s w' (cmp n w' (sec n s w g : Ga l L n)) = sec n s w g` using `fun g => sec_cmp s hn hw' hs' ((mem_locA s).2 fun u hu => (mem_locA s).1 (sec_mem s w g) u (by rwa [← h]))`.

Use `⟨{ toFun := fun g => cmp n w (sec n s w' g : Ga l L n) invFun := fun g => cmp n w' (sec n s w g : Ga l L n) left_inv := fun g => by simp only [h1, hc'] right_inv := fun g => by simp only [h2, hc] map_mul' := fun g g' => by rw [map_mul, Subgroup.coe_mul, map_mul] }, fun g => ⟨fun …` and prove the remaining obligations. Use `cmp_KO h _ hg` as an intermediate fact. Rewrite `this` using `[hc']`. Then use the resulting hypothesis. Conclude with `cmp_KO h.symm _ (by rwa [hc'])`.
-/
private theorem same (hn : 1 ≤ n) {w w' : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ s.S) (hs : IsSplitAt w) (hs' : IsSplitAt w')
    (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    ∃ e : GLw n w' ≃* GLw n w, (∀ g, e g ∈ KO (w.adicCompletion L) (Fin n) ↔ g ∈ KO (w'.adicCompletion L) (Fin n)) ∧
      ∀ g, sec n s w' g = sec n s w (e g) := by
  have hw' : w'.under (𝓞 (Lp L)) ∉ s.S := by rwa [h]
  have hc := ((secU l L Ω s n hn w hs).2 hw).2.1
  have hc' := ((secU l L Ω s n hn w' hs').2 hw').2.1
  have h1 : ∀ g, sec n s w (cmp n w (sec n s w' g : Ga l L n)) = sec n s w' g := fun g =>
    sec_cmp s hn hw hs ((mem_locA s).2 fun u hu => (mem_locA s).1 (sec_mem s w' g) u (by rwa [h]))
  have h2 : ∀ g, sec n s w' (cmp n w' (sec n s w g : Ga l L n)) = sec n s w g := fun g =>
    sec_cmp s hn hw' hs' ((mem_locA s).2 fun u hu => (mem_locA s).1 (sec_mem s w g) u (by rwa [← h]))
  refine ⟨{ toFun := fun g => cmp n w (sec n s w' g : Ga l L n)
            invFun := fun g => cmp n w' (sec n s w g : Ga l L n)
            left_inv := fun g => by simp only [h1, hc']
            right_inv := fun g => by simp only [h2, hc]
            map_mul' := fun g g' => by rw [map_mul, Subgroup.coe_mul, map_mul] }, fun g => ⟨fun hg => ?_, fun hg => ?_⟩,
    fun g => (h1 g).symm⟩
  · have := cmp_KO h _ hg
    rwa [hc'] at this
  · exact cmp_KO h.symm _ (by rwa [hc'])
variable (V) in
/- English proof (translation)
Introduce and unpack `⟨x, hx⟩`. Take `⟨g, rfl⟩` from `QuotientGroup.mk'_surjective (NS Ω V.S') x`. Take `⟨σ, rfl⟩` from `(V.hη g).1 hx`. Conclude with `⟨σ, rfl⟩`.
-/
private theorem pr_surj : Function.Surjective V.pr := by
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω V.S') x
  obtain ⟨σ, rfl⟩ := (V.hη g).1 hx
  exact ⟨σ, rfl⟩
variable (V) in
/- English proof (translation)
Establish `hfin1 : {w : Plc L | w.asIdeal ∣ differentIdeal (𝓞 (Lp L)) (𝓞 L)}.Finite` using `Ideal.finite_factors differentIdeal_ne_bot`. Establish `hfin2 : ((fun w : Plc L => w.under (𝓞 (Lp L))) ⁻¹' V.S').Finite`. Use `V.fin.preimage' fun v _ => ?_` and prove the remaining obligations. Use `v.isMaximal` as an intermediate fact. Use `((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage (f := fun w : Plc L => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_` and prove the remaining obligations.

Introduce and unpack `w rfl`. Conclude with `⟨w.isPrime, ⟨rfl⟩⟩`. Establish `hD` using `GlobalTheory.Published.ChebotarevDegreeOne.dense (F := L) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' (hfin1.union hfin2)`. Establish `hs : Function.Surjective fun σ : G L Ω => V.pr σ⁻¹` using `(pr_surj V).comp inv_surjective`. Use `(hs.denseRange.dense_image ((V.pr_cont W.continuous_resP).comp continuous_inv) hD).mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨σ, ⟨w, hw, hd, B, hB, hF⟩, rfl⟩`. Use `w.isPrime` as an intermediate fact. Conclude with `⟨w, ⟨fun h => hw (Or.inr h), UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one L w (not_dvd_differentIdeal_iff.1 fun h => hw (Or.inl h)) hd⟩, B, σ, hB, hF, rfl⟩`.
-/
private theorem dense : Dense {g : V.η.ker | ∃ w ∈ {w : Plc L | w.under (𝓞 (Lp L)) ∉ V.S' ∧ IsSplitAt w},
    ∃ (A : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver A w ∧ IsFrob A (normV w) σ ∧ g = V.pr σ⁻¹} := by
  have hfin1 : {w : Plc L | w.asIdeal ∣ differentIdeal (𝓞 (Lp L)) (𝓞 L)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  have hfin2 : ((fun w : Plc L => w.under (𝓞 (Lp L))) ⁻¹' V.S').Finite := by
    refine V.fin.preimage' fun v _ => ?_
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
      (f := fun w : Plc L => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, ⟨rfl⟩⟩
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := L) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (hfin1.union hfin2)
  have hs : Function.Surjective fun σ : G L Ω => V.pr σ⁻¹ := (pr_surj V).comp inv_surjective
  refine (hs.denseRange.dense_image ((V.pr_cont W.continuous_resP).comp continuous_inv) hD).mono ?_
  rintro _ ⟨σ, ⟨w, hw, hd, B, hB, hF⟩, rfl⟩
  have := w.isPrime
  exact ⟨w, ⟨fun h => hw (Or.inr h),
    UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one L w (not_dvd_differentIdeal_iff.1 fun h => hw (Or.inl h)) hd⟩, B, σ, hB, hF, rfl⟩
end UpperTheory.V.Hi.AxU
open UpperTheory.V.Hi.AxU in
/- English proof (translation)
Introduce `H l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀`. Conclude with `{ odd := s.odd pos := hn Sl_over := fun v => by`. Establish `h : ((l : ℕ) : 𝓞 (Lp L)) ∈ ((s.w v.1).under (𝓞 (Lp L))).asIdeal`. Rewrite using `[under_w]`. Conclude with `v.2`.

Express the relevant statement in the definitionally equal form `algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ (s.w v.1).asIdeal at h`. Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis. Use `Sl_inj := fun v v' h => Subtype.ext (by`. Rewrite using `[← under_w s v.1, ← under_w s v'.1]`. Conclude with `congrArg _ h)`.

Use `art_spec := fun v => Classical.epsilon_spec (_root_.UpperTheory.V.Z.Win.T2.laArtinLit' H (s.hw v.1))`. Use `Q_away := fun q => away_l s (Q.notS q)`. Use `Wp_away := fun w hw => away_l s fun h => hw.1 (V.sub h)`. Use `fin := UpperTheory.V.Hi.finU l L Ω s n hn V Q c m τ₀`. Use `τ_Q := fun q g => (congrArg τ₀ (toKT_sec s (Q.notS q) g)).trans (map_one τ₀)`.

Use `coefficientRep_trivial_on_unramified := fun w hw g => (congrArg τ₀ (toKT_sec s (fun h => hw.1 (V.sub h)) g)).trans (map_one τ₀)`. Use `Q_UQ := fun q u hu g => comm s (((mem_UQ Q).1 hu).2 q) (sec_mem s _ g)`. Use `Q_Q := fun q q' h => comm' s fun e => h (Q.inj e).symm`. Use `sectionsCommuteAtSplit := fun q w hw => comm' s fun e => hw.1 (e ▸ wq_mem Q q)`. Use `W_le := fun w hw => by`.

Introduce and unpack `_ ⟨k, hk, rfl⟩`. Conclude with `sec_KO Q hn hw.1 hw.2 hk`. Use `W_dec := fun w hw u hu => dec Q hn hw.1 hw.2 hu`. Use `Wm_mul_Wm_comm := fun w hw w' hw' => by`. Distinguish the cases in `h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))`.

Conclude with `Or.inr (same s hn (fun h => hw.1 (V.sub h)) hw.2 hw'.2 h)`. Conclude with `Or.inl (comm' s h)`. Use `prj_cont := V.pr_cont W.continuous_resP`. Use `dense := dense V }`.
-/
theorem UpperTheory.V.Hi.axU_s :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), (hset Q τ₀).Ax := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀
  exact
    { odd := s.odd
      pos := hn
      Sl_over := fun v => by
        have h : ((l : ℕ) : 𝓞 (Lp L)) ∈ ((s.w v.1).under (𝓞 (Lp L))).asIdeal := by
          rw [under_w]
          exact v.2
        change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ (s.w v.1).asIdeal at h
        rwa [map_natCast] at h
      Sl_inj := fun v v' h => Subtype.ext (by
        rw [← under_w s v.1, ← under_w s v'.1]
        exact congrArg _ h)
      art_spec := fun v => Classical.epsilon_spec (_root_.UpperTheory.V.Z.Win.T2.laArtinLit' H (s.hw v.1))
      Q_away := fun q => away_l s (Q.notS q)
      Wp_away := fun w hw => away_l s fun h => hw.1 (V.sub h)
      fin := UpperTheory.V.Hi.finU l L Ω s n hn V Q c m τ₀
      τ_Q := fun q g => (congrArg τ₀ (toKT_sec s (Q.notS q) g)).trans (map_one τ₀)
      coefficientRep_trivial_on_unramified := fun w hw g => (congrArg τ₀ (toKT_sec s (fun h => hw.1 (V.sub h)) g)).trans (map_one τ₀)
      Q_UQ := fun q u hu g => comm s (((mem_UQ Q).1 hu).2 q) (sec_mem s _ g)
      Q_Q := fun q q' h => comm' s fun e => h (Q.inj e).symm
      sectionsCommuteAtSplit := fun q w hw => comm' s fun e => hw.1 (e ▸ wq_mem Q q)
      W_le := fun w hw => by
        rintro _ ⟨k, hk, rfl⟩
        exact sec_KO Q hn hw.1 hw.2 hk
      W_dec := fun w hw u hu => dec Q hn hw.1 hw.2 hu
      Wm_mul_Wm_comm := fun w hw w' hw' => by
        by_cases h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
        · exact Or.inr (same s hn (fun h => hw.1 (V.sub h)) hw.2 hw'.2 h)
        · exact Or.inl (comm' s h)
      prj_cont := V.pr_cont W.continuous_resP
      dense := dense V }
end
