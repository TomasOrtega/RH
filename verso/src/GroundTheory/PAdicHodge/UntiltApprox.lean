import Mathlib
import GroundTheory.PAdicHodge.UntiltField
import GroundTheory.PAdicHodge.UntiltApproxLemmas
import GroundTheory.PAdicHodge.UntiltPerfectoid
import GroundTheory.PAdicHodge.TiltAlgClosed
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial

/- English proof (translation)
Break down `CharP.exists' K with h | ⟨q, hq, hqK⟩` into its components or cases. Use `infer_instance`. Establish `hqp : q = p`. Assume the negation of the conclusion as `hne`. Establish `: NeZero q` using `⟨hq.out.ne_zero⟩`.

Establish `hdvd : ¬ q ∣ p` using `fun h => hne ((Nat.prime_dvd_prime_iff_eq hq.out (Fact.out : p.Prime)).1 h)`. Establish `hp0 : (p : ZMod q) ≠ 0`. Rewrite using `[Ne, ZMod.natCast_eq_zero_iff]`. Conclude with `hdvd`. Use `set u := (p : ZMod q)⁻¹`.

Establish `h1 : (p : ZMod q) * u = 1` using `mul_inv_cancel₀ hp0`. Establish `h2` using `congrArg (ZMod.castHom (dvd_refl q) K) h1`. Rewrite `h2` using `[map_mul, map_one, map_natCast, ZMod.castHom_apply, ZMod.cast_eq_val]`. Establish `h3 : ‖(p : K)‖ * ‖((u.val : ℕ) : K)‖ = 1`. Rewrite using `[← norm_mul, h2, norm_one]`.

Establish `h4 : ‖((u.val : ℕ) : K)‖ ≤ 1` using `(isUltrametricDist_iff_forall_norm_natCast_le_one.1 inferInstance) _`. Establish `h5` using `IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)`. Use polynomial arithmetic with `[norm_nonneg ((u.val : ℕ) : K), norm_nonneg (p : K)]`. Substitute `hqp` using the available equality. Use `IsPerfectoidField.perfectRing (K := K) q` as an intermediate fact.

Conclude with `PerfectRing.toPerfectField K q`.
-/
theorem perfectField_of_isPerfectoidField (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] : PerfectField K := by
  rcases CharP.exists' K with h | ⟨q, hq, hqK⟩
  · infer_instance
  · have hqp : q = p := by
      by_contra hne
      have : NeZero q := ⟨hq.out.ne_zero⟩
      have hdvd : ¬ q ∣ p := fun h =>
        hne ((Nat.prime_dvd_prime_iff_eq hq.out (Fact.out : p.Prime)).1 h)
      have hp0 : (p : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact hdvd
      set u := (p : ZMod q)⁻¹
      have h1 : (p : ZMod q) * u = 1 := mul_inv_cancel₀ hp0
      have h2 := congrArg (ZMod.castHom (dvd_refl q) K) h1
      rw [map_mul, map_one, map_natCast, ZMod.castHom_apply, ZMod.cast_eq_val] at h2
      have h3 : ‖(p : K)‖ * ‖((u.val : ℕ) : K)‖ = 1 := by
        rw [← norm_mul, h2, norm_one]
      have h4 : ‖((u.val : ℕ) : K)‖ ≤ 1 :=
        (isUltrametricDist_iff_forall_norm_natCast_le_one.1 inferInstance) _
      have h5 := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
      nlinarith [norm_nonneg ((u.val : ℕ) : K), norm_nonneg (p : K)]
    subst hqp
    have := IsPerfectoidField.perfectRing (K := K) q
    exact PerfectRing.toPerfectField K q

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p

omit [IsUltrametricDist K] [IsUltrametricDist C] [Fact p.Prime] [IsPerfectoidField K p]
  [IsPerfectoidField C p] in
/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap K C), norm_algebraMap']`.
-/
theorem norm_natCast_eq_of_normedAlgebra : ‖(p : C)‖ = ‖(p : K)‖ := by
  rw [← map_natCast (algebraMap K C), norm_algebraMap']

set_option synthInstance.maxHeartbeats 200000 in

/- English proof (translation)
Distinguish the cases in `hαβ : α = β`. Conclude with `⟨N, le_rfl, inferInstance, β, hβ, by rw [hαβ, sub_self, norm_zero, mul_zero]⟩`. Use `set F := untiltField K C p N with hFdef`. Establish `hδ : 0 < ‖α - β‖` using `norm_pos_iff.2 (sub_ne_zero.2 hαβ)`. Establish `: CompleteSpace K` using `IsPerfectoidField.completeSpace p`.

Establish `: CompleteSpace F` using `FiniteDimensional.complete K F`. Take `⟨c, hc1, hc2⟩` from `exists_norm_mem_Ioc (K := K) p hδ (b := ‖α - β‖ / ε) (by rw [lt_div_iff₀ hε0]; nlinarith)`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc1` using `[norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set c' : C := algebraMap K C c`. Establish `hc'0 : c' ≠ 0` using `(map_ne_zero_iff _ (algebraMap K C).injective).2 hc0`. Establish `hnc' : ‖c'‖ = ‖c‖` using `norm_algebraMap' C c`. Establish `hαF : IsIntegral F α` using `hα.tower_top`.

Use `set Q := minpoly F α`. Establish `hQm : Q.Monic` using `minpoly.monic hαF`. Use `set e := Q.natDegree with hedef`. Establish `he0 : 0 < e` using `minpoly.natDegree_pos hαF`. Establish `hed : e ≤ (minpoly K α).natDegree`.

Establish `hdvd : Q ∣ (minpoly K α).map (algebraMap K F)` using `minpoly.dvd_map_of_isScalarTower K F α`. Use `Polynomial.natDegree_le_of_dvd hdvd (Polynomial.map_ne_zero (minpoly.ne_zero hα))` as an intermediate fact. Rewrite `this` using `[natDegree_map]`. Then use the resulting hypothesis. Use `set βF : F := ⟨β, hβ⟩`. Use `set cF : F := algebraMap K F c`.

Establish `hcF : cF ≠ 0` using `(map_ne_zero_iff _ (algebraMap K F).injective).2 hc0`. Use `set Qt : F[X] := Polynomial.C (cF⁻¹ ^ e) * Q.comp (Polynomial.C βF + Polynomial.C cF * X)`. Use `set R := (Q.map (algebraMap F C)).roots`. Establish `hQt : Qt.map (algebraMap F C) = (R.map fun γ => X - Polynomial.C ((γ - β) / c')).prod` using `map_scale_eq_prod (E := C) hQm βF cF hcF`. Establish `hQne : Q.map (algebraMap F C) ≠ 0` using `Polynomial.map_ne_zero (minpoly.ne_zero hαF)`.

Establish `hαR : α ∈ R`. Rewrite using `[mem_roots hQne, IsRoot, eval_map_algebraMap]`. Conclude with `minpoly.aeval F α`. Establish `hdist : ∀ γ ∈ R, ‖γ - β‖ = ‖α - β‖`. Introduce `γ hγ`.

Establish `hγ' : aeval γ Q = 0`. Use `(mem_roots hQne).1 hγ` as an intermediate fact. Rewrite `this` using `[IsRoot, eval_map_algebraMap]`. Then use the resulting hypothesis. Establish `hconj : IsConjRoot F α γ` using `(isConjRoot_iff_mem_minpoly_rootSet hαF).2 (mem_rootSet.2 ⟨minpoly.ne_zero hαF, hγ'⟩)`. Use `norm_eq_of_isConjRoot (F := F) (E := C) (hαF.sub isIntegral_algebraMap) (hconj.sub_algebraMap βF)` as an intermediate fact.

Conclude with `this.symm`. Establish `hrootle : ∀ r ∈ R.map (fun γ => (γ - β) / c'), ‖r‖ ≤ 1`. Introduce `r hr`. Take `⟨γ, hγ, rfl⟩` from `Multiset.mem_map.1 hr`. Rewrite using `[norm_div, hdist γ hγ, hnc']`.

Conclude with `div_le_one_of_le₀ hc1.le (norm_nonneg _)`. Use `set Qt' := Qt.map (algebraMap F C) with hQt'def`. Establish `hQt' : Qt' = ((R.map (fun γ => (γ - β) / c')).map fun r => X - Polynomial.C r).prod`. Rewrite using `[hQt, Multiset.map_map]`. Both sides reduce to the same expression.

Establish `hcoef : ∀ n, ‖Qt'.coeff n‖ ≤ 1` using `fun n => by`. Rewrite using `[hQt']`. Conclude with `norm_coeff_prod_X_sub_C_le_one hrootle n`. Establish `hcard : Multiset.card R = e`. Rewrite using `[← (IsAlgClosed.splits (Q.map (algebraMap F C))).natDegree_eq_card_roots, natDegree_map]`.

Establish `hQt'deg : Qt'.natDegree = e`. Rewrite using `[hQt', natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, hcard]`. Establish `hQt'mon : Qt'.Monic`. Rewrite using `[hQt']`. Conclude with `monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r`.

Establish `hsub : (↑Qt'.coeffs : Set C) ⊆ normInteger C`. Introduce `x hx`. Take `⟨n, -, rfl⟩` from `Polynomial.mem_coeffs_iff.1 hx`. Conclude with `mem_normInteger.2 (hcoef n)`. Use `set Qi := Qt'.toSubring (normInteger C) hsub`.

Establish `hQi : Qi.map (normInteger C).subtype = Qt'` using `Polynomial.map_toSubring _ _ hsub`. Establish `hQimon : Qi.Monic`. Use `Polynomial.monic_of_injective (normInteger C).subtype_injective ?_` and prove the remaining obligations. Rewrite using `[hQi]`. Conclude with `hQt'mon`.

Establish `hQideg : Qi.natDegree = e`. Rewrite using `[← hQt'deg, ← hQi, natDegree_map_eq_of_injective (normInteger C).subtype_injective]`. Establish `hz1 : ‖(α - β) / c'‖ ≤ 1` using `hrootle _ (Multiset.mem_map.2 ⟨α, hαR, rfl⟩)`. Use `set z : normInteger C := ⟨(α - β) / c', mem_normInteger.2 hz1⟩`. Establish `hz : Qi.eval z = 0`.

Apply `(normInteger C).subtype_injective` to reduce the goal to its premises. Rewrite using `[map_zero, ← eval₂_at_apply, ← eval_map, hQi, hQt, eval_multiset_prod]`. Use `Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map.2 ⟨α, hαR, rfl⟩, ?_⟩)` and prove the remaining obligations. Simplify using `[z]`. Establish `happ : ∀ m, ∃ a : 𝒪C♭, m < e → a ∈ integerTilt K C p N ∧ Ideal.Quotient.mk (Ideal.span {(p : normInteger C)}) (Qi.coeff m) = PreTilt.coeff 0 a`.

Introduce `m`. Distinguish the cases in `hm : m < e`. Establish `hy : ((Qt.coeff m : F) : C) ∈ F` using `(Qt.coeff m).2`. Establish `hy1 : ‖((Qt.coeff m : F) : C)‖ ≤ 1`. Use `hcoef m` as an intermediate fact.

Rewrite `this` using `[hQt'def, coeff_map]`. Then use the resulting hypothesis. Take `⟨a, ha, hab⟩` from `happrox _ hy hy1`. Use `⟨a, fun _ => ⟨ha, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← PreTilt.mk_untilt_eq_coeff_zero, mk_eq_mk_iff_norm_sub_le, norm_natCast_eq_of_normedAlgebra (K := K)]`. Establish `: ((Qi.coeff m : normInteger C) : C) = ((Qt.coeff m : F) : C)`.

Rewrite using `[← (normInteger C).subtype_apply, ← coeff_map, hQi, hQt'def, coeff_map]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hab`. Conclude with `⟨0, fun h => absurd h hm⟩`.

Use `choose a ha using happ`. Establish `hdeg : 0 < Qi.natDegree` using `hQideg ▸ he0`. Take `⟨b, hbroot, hbnorm⟩` from `exists_root_norm_sub_untilt_pow_le (C := C) (p := p) hQimon hdeg a (fun m hm => (ha m (hQideg ▸ hm)).2) hz`. Rewrite `hbnorm`, `hbroot` using `[hQideg]`. Establish `hbμ : ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ≤ μ`.

Establish `h1 : ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ^ e ≤ μ ^ e`. Use `hbnorm.trans ?_` and prove the remaining obligations. Rewrite using `[norm_natCast_eq_of_normedAlgebra (K := K)]`. Conclude with `hμ.trans (pow_le_pow_of_le_one hμ0 hμ1 hed)`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) hμ0 he0.ne').1 h1`.

Use `set b' : C♭ := algebraMap 𝒪C♭ C♭ b`. Use `set g : C♭[X] := (monicOfCoeffs e a).map (algebraMap 𝒪C♭ C♭)`. Establish `hgmon : g.Monic` using `(monic_monicOfCoeffs e a).map _`. Establish `hgmem : ∀ n, g.coeff n ∈ N`. Introduce `n`.

Rewrite using `[coeff_map, coeff_monicOfCoeffs]`. Use `split_ifs with h1 h2`. Rewrite using `[map_one]`. Conclude with `one_mem N`. Conclude with `(ha n h2).1`.

Rewrite using `[map_zero]`. Conclude with `zero_mem N`. Establish `hlift : g ∈ Polynomial.lifts (algebraMap N C♭)` using `(lifts_iff_coeff_lifts g).2 fun n => ⟨⟨g.coeff n, hgmem n⟩, rfl⟩`. Take `⟨gN, hgN, -, hgNmon⟩` from `lifts_and_natDegree_eq_and_monic hlift hgmon`. Establish `hbN : IsIntegral N b'`.

Use `⟨gN, hgNmon, ?_⟩` and prove the remaining obligations. Rewrite using `[← eval_map, hgN, eval_map, eval₂_at_apply, hbroot, map_zero]`. Establish `hbK : IsIntegral K♭ b'` using `isIntegral_trans b' hbN`. Establish `: FiniteDimensional K♭ (IntermediateField.adjoin K♭ {b'})` using `IntermediateField.adjoin.finiteDimensional hbK`. Use `set N' := N ⊔ IntermediateField.adjoin K♭ {b'}`.

Establish `hb'N' : b' ∈ N'` using `(le_sup_right : IntermediateField.adjoin K♭ {b'} ≤ N') (IntermediateField.mem_adjoin_simple_self K♭ b')`. Use `⟨N', le_sup_left, inferInstance, β + c' * ((PreTilt.untilt b : normInteger C) : C), ?_, ?_⟩` and prove the remaining obligations. Use `add_mem (untiltField_mono le_sup_left hβ) (mul_mem ?_ ?_)` and prove the remaining obligations. Conclude with `IntermediateField.algebraMap_mem _ c`. Use `tiltSharp_mem_untiltField (K := K) (N := N') hb'N'` as an intermediate fact.

Rewrite `this` using `[tiltSharp_algebraMap]`. Then use the resulting hypothesis. Establish `hsplit : α - (β + c' * ((PreTilt.untilt b : normInteger C) : C)) = c' * ((z : C) - ((PreTilt.untilt b : normInteger C) : C))`. Simplify using `only [z]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsplit, norm_mul, hnc']`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_untiltField_norm_sub_le [IsAlgClosed C] [IsAlgClosed C♭]
    (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [FiniteDimensional K (untiltField K C p N)]
    (happrox : ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
      ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖)
    {α : C} (hα : IsIntegral K α) {μ ε : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hμ : ‖(p : K)‖ ≤ μ ^ (minpoly K α).natDegree) (hε0 : 0 < ε) (hε1 : ε < 1)
    {β : C} (hβ : β ∈ untiltField K C p N) :
    ∃ N' : IntermediateField K♭ C♭, N ≤ N' ∧ FiniteDimensional K♭ N' ∧
      ∃ β' ∈ untiltField K C p N', ‖α - β'‖ ≤ μ / ε * ‖α - β‖ := by
  classical
  by_cases hαβ : α = β
  · exact ⟨N, le_rfl, inferInstance, β, hβ, by rw [hαβ, sub_self, norm_zero, mul_zero]⟩
  set F := untiltField K C p N with hFdef
  have hδ : 0 < ‖α - β‖ := norm_pos_iff.2 (sub_ne_zero.2 hαβ)
  have : CompleteSpace K := IsPerfectoidField.completeSpace p
  have : CompleteSpace F := FiniteDimensional.complete K F
  obtain ⟨c, hc1, hc2⟩ := exists_norm_mem_Ioc (K := K) p hδ
    (b := ‖α - β‖ / ε) (by rw [lt_div_iff₀ hε0]; nlinarith)
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [norm_zero] at hc1; linarith
  set c' : C := algebraMap K C c
  have hc'0 : c' ≠ 0 := (map_ne_zero_iff _ (algebraMap K C).injective).2 hc0
  have hnc' : ‖c'‖ = ‖c‖ := norm_algebraMap' C c
  have hαF : IsIntegral F α := hα.tower_top
  set Q := minpoly F α
  have hQm : Q.Monic := minpoly.monic hαF
  set e := Q.natDegree with hedef
  have he0 : 0 < e := minpoly.natDegree_pos hαF
  have hed : e ≤ (minpoly K α).natDegree := by
    have hdvd : Q ∣ (minpoly K α).map (algebraMap K F) :=
      minpoly.dvd_map_of_isScalarTower K F α
    have := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.map_ne_zero (minpoly.ne_zero hα))
    rwa [natDegree_map] at this
  set βF : F := ⟨β, hβ⟩
  set cF : F := algebraMap K F c
  have hcF : cF ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).2 hc0
  set Qt : F[X] := Polynomial.C (cF⁻¹ ^ e) * Q.comp (Polynomial.C βF + Polynomial.C cF * X)
  set R := (Q.map (algebraMap F C)).roots
  have hQt : Qt.map (algebraMap F C) = (R.map fun γ => X - Polynomial.C ((γ - β) / c')).prod :=
    map_scale_eq_prod (E := C) hQm βF cF hcF

  have hQne : Q.map (algebraMap F C) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hαF)
  have hαR : α ∈ R := by
    rw [mem_roots hQne, IsRoot, eval_map_algebraMap]
    exact minpoly.aeval F α
  have hdist : ∀ γ ∈ R, ‖γ - β‖ = ‖α - β‖ := by
    intro γ hγ
    have hγ' : aeval γ Q = 0 := by
      have := (mem_roots hQne).1 hγ
      rwa [IsRoot, eval_map_algebraMap] at this
    have hconj : IsConjRoot F α γ :=
      (isConjRoot_iff_mem_minpoly_rootSet hαF).2 (mem_rootSet.2 ⟨minpoly.ne_zero hαF, hγ'⟩)
    have := norm_eq_of_isConjRoot (F := F) (E := C) (hαF.sub isIntegral_algebraMap)
      (hconj.sub_algebraMap βF)
    exact this.symm
  have hrootle : ∀ r ∈ R.map (fun γ => (γ - β) / c'), ‖r‖ ≤ 1 := by
    intro r hr
    obtain ⟨γ, hγ, rfl⟩ := Multiset.mem_map.1 hr
    rw [norm_div, hdist γ hγ, hnc']
    exact div_le_one_of_le₀ hc1.le (norm_nonneg _)
  set Qt' := Qt.map (algebraMap F C) with hQt'def
  have hQt' : Qt' = ((R.map (fun γ => (γ - β) / c')).map fun r => X - Polynomial.C r).prod := by
    rw [hQt, Multiset.map_map]; rfl
  have hcoef : ∀ n, ‖Qt'.coeff n‖ ≤ 1 := fun n => by
    rw [hQt']; exact norm_coeff_prod_X_sub_C_le_one hrootle n
  have hcard : Multiset.card R = e := by
    rw [← (IsAlgClosed.splits (Q.map (algebraMap F C))).natDegree_eq_card_roots, natDegree_map]
  have hQt'deg : Qt'.natDegree = e := by
    rw [hQt', natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, hcard]
  have hQt'mon : Qt'.Monic := by
    rw [hQt']; exact monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r

  have hsub : (↑Qt'.coeffs : Set C) ⊆ normInteger C := by
    intro x hx
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
    exact mem_normInteger.2 (hcoef n)
  set Qi := Qt'.toSubring (normInteger C) hsub
  have hQi : Qi.map (normInteger C).subtype = Qt' := Polynomial.map_toSubring _ _ hsub
  have hQimon : Qi.Monic := by
    refine Polynomial.monic_of_injective (normInteger C).subtype_injective ?_
    rw [hQi]; exact hQt'mon
  have hQideg : Qi.natDegree = e := by
    rw [← hQt'deg, ← hQi, natDegree_map_eq_of_injective (normInteger C).subtype_injective]
  have hz1 : ‖(α - β) / c'‖ ≤ 1 :=
    hrootle _ (Multiset.mem_map.2 ⟨α, hαR, rfl⟩)
  set z : normInteger C := ⟨(α - β) / c', mem_normInteger.2 hz1⟩
  have hz : Qi.eval z = 0 := by
    apply (normInteger C).subtype_injective
    rw [map_zero, ← eval₂_at_apply, ← eval_map, hQi, hQt, eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map.2 ⟨α, hαR, rfl⟩, ?_⟩)
    simp [z]

  have happ : ∀ m, ∃ a : 𝒪C♭, m < e → a ∈ integerTilt K C p N ∧
      Ideal.Quotient.mk (Ideal.span {(p : normInteger C)}) (Qi.coeff m) = PreTilt.coeff 0 a := by
    intro m
    by_cases hm : m < e
    · have hy : ((Qt.coeff m : F) : C) ∈ F := (Qt.coeff m).2
      have hy1 : ‖((Qt.coeff m : F) : C)‖ ≤ 1 := by
        have := hcoef m
        rwa [hQt'def, coeff_map] at this
      obtain ⟨a, ha, hab⟩ := happrox _ hy hy1
      refine ⟨a, fun _ => ⟨ha, ?_⟩⟩
      rw [← PreTilt.mk_untilt_eq_coeff_zero, mk_eq_mk_iff_norm_sub_le,
        norm_natCast_eq_of_normedAlgebra (K := K)]
      have : ((Qi.coeff m : normInteger C) : C) = ((Qt.coeff m : F) : C) := by
        rw [← (normInteger C).subtype_apply, ← coeff_map, hQi, hQt'def, coeff_map]; rfl
      rw [this]; exact hab
    · exact ⟨0, fun h => absurd h hm⟩
  choose a ha using happ
  have hdeg : 0 < Qi.natDegree := hQideg ▸ he0
  obtain ⟨b, hbroot, hbnorm⟩ := exists_root_norm_sub_untilt_pow_le (C := C) (p := p) hQimon hdeg a
    (fun m hm => (ha m (hQideg ▸ hm)).2) hz
  rw [hQideg] at hbnorm hbroot

  have hbμ : ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ≤ μ := by
    have h1 : ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ^ e ≤ μ ^ e := by
      refine hbnorm.trans ?_
      rw [norm_natCast_eq_of_normedAlgebra (K := K)]
      exact hμ.trans (pow_le_pow_of_le_one hμ0 hμ1 hed)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hμ0 he0.ne').1 h1

  set b' : C♭ := algebraMap 𝒪C♭ C♭ b
  set g : C♭[X] := (monicOfCoeffs e a).map (algebraMap 𝒪C♭ C♭)
  have hgmon : g.Monic := (monic_monicOfCoeffs e a).map _
  have hgmem : ∀ n, g.coeff n ∈ N := by
    intro n
    rw [coeff_map, coeff_monicOfCoeffs]
    split_ifs with h1 h2
    · rw [map_one]; exact one_mem N
    · exact (ha n h2).1
    · rw [map_zero]; exact zero_mem N
  have hlift : g ∈ Polynomial.lifts (algebraMap N C♭) :=
    (lifts_iff_coeff_lifts g).2 fun n => ⟨⟨g.coeff n, hgmem n⟩, rfl⟩
  obtain ⟨gN, hgN, -, hgNmon⟩ := lifts_and_natDegree_eq_and_monic hlift hgmon
  have hbN : IsIntegral N b' := by
    refine ⟨gN, hgNmon, ?_⟩
    rw [← eval_map, hgN, eval_map, eval₂_at_apply, hbroot, map_zero]
  have hbK : IsIntegral K♭ b' := isIntegral_trans b' hbN
  have : FiniteDimensional K♭ (IntermediateField.adjoin K♭ {b'}) :=
    IntermediateField.adjoin.finiteDimensional hbK
  set N' := N ⊔ IntermediateField.adjoin K♭ {b'}
  have hb'N' : b' ∈ N' :=
    (le_sup_right : IntermediateField.adjoin K♭ {b'} ≤ N')
      (IntermediateField.mem_adjoin_simple_self K♭ b')
  refine ⟨N', le_sup_left, inferInstance, β + c' * ((PreTilt.untilt b : normInteger C) : C), ?_, ?_⟩
  · refine add_mem (untiltField_mono le_sup_left hβ) (mul_mem ?_ ?_)
    · exact IntermediateField.algebraMap_mem _ c
    · have := tiltSharp_mem_untiltField (K := K) (N := N') hb'N'
      rwa [tiltSharp_algebraMap] at this
  · have hsplit : α - (β + c' * ((PreTilt.untilt b : normInteger C) : C)) =
        c' * ((z : C) - ((PreTilt.untilt b : normInteger C) : C)) := by
      simp only [z]; field_simp; ring
    rw [hsplit, norm_mul, hnc']
    calc ‖c‖ * ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ≤ ‖α - β‖ / ε * μ := by
          gcongr
      _ = μ / ε * ‖α - β‖ := by ring

/- English proof (translation)
Use `set d := (minpoly K α).natDegree`. Take `⟨μ, hμ0, hμ1, hμ⟩` from `exists_lt_one_le_pow (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)) d`. Use `set ε := (1 + μ) / 2`. Establish `hε0 : 0 < ε` using `by simp only [ε]; linarith`. Establish `hε1 : ε < 1` using `by simp only [ε]; linarith`.

Use `set lam := μ / ε`. Establish `hlam0 : 0 ≤ lam` using `div_nonneg hμ0.le hε0.le`. Establish `hlam1 : lam < 1`. Rewrite using `[div_lt_one hε0]`. Simplify using `only [ε]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `iter : ∀ k : ℕ, ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ ∃ β ∈ untiltField K C p N, ‖α - β‖ ≤ lam ^ k * ‖α‖`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨⊥, inferInstance, 0, zero_mem _, by simp⟩`.

Consider the case `succ k ih`. Take `⟨N, hN, β, hβ, hβα⟩` from `ih`. Use `hN` as an intermediate fact. Use `hfin N hN` as an intermediate fact. Take `⟨N', -, hN', β', hβ', hle⟩` from `exists_untiltField_norm_sub_le N (happrox N hN) hα hμ0.le hμ1.le hμ hε0 hε1 hβ`.

Use `⟨N', hN', β', hβ', hle.trans ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, mul_comm (lam ^ k) lam, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left hβα hlam0`. Use `set T : Finset C := ((minpoly K α).aroots C).toFinset.erase α`. Choose the witnesses or unpack the hypotheses as in `⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ α' ∈ T, ρ ≤ ‖α - α'‖ := by`.

Distinguish the cases in `hT : T.Nonempty`. Use `⟨T.inf' hT fun α' => ‖α - α'‖, ?_, fun α' h => Finset.inf'_le _ h⟩` and prove the remaining obligations. Rewrite using `[Finset.lt_inf'_iff]`. Introduce `α' h`. Conclude with `norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase h)))`.

Conclude with `⟨1, one_pos, fun α' h => absurd ⟨α', h⟩ hT⟩`. Distinguish the cases in `hα0 : α = 0`. Conclude with `⟨⊥, inferInstance, by rw [hα0]; exact zero_mem _⟩`. Establish `hαn : 0 < ‖α‖` using `norm_pos_iff.2 hα0`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one (div_pos hρ0 hαn) hlam1`.

Take `⟨N, hN, β, hβ, hβα⟩` from `iter k`. Establish `hclose : ‖α - β‖ < ρ`. Use `hβα.trans_lt ?_` and prove the remaining obligations. Rewrite `hk` using `[lt_div_iff₀ hαn]`. Then use the resulting hypothesis. Use `hN` as an intermediate fact.

Use `hfin N hN` as an intermediate fact. Use `set F := untiltField K C p N`. Establish `: CompleteSpace K` using `IsPerfectoidField.completeSpace p`. Establish `: CompleteSpace F` using `FiniteDimensional.complete K F`. Establish `: PerfectField K` using `perfectField_of_isPerfectoidField K p`.

Establish `hsepK : IsSeparable K α` using `Algebra.IsSeparable.isSeparable K (⟨α, hα⟩ : algebraicClosure K C) |> fun h => by`. Rewrite `h` using `[IsSeparable, IntermediateField.minpoly_eq]`. Then use the resulting hypothesis. Establish `hsep : IsSeparable F α` using `hsepK.tower_top F`. Use `⟨N, hN, ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `mem_range_of_norm_sub_lt (F := F) (E := C) ⟨β, hβ⟩ hsep fun α' hα' hne => by`.

Use `hclose.trans_le (hρ α' ?_)` and prove the remaining obligations. Rewrite using `[Finset.mem_erase, Multiset.mem_toFinset]`. Use `⟨Ne.symm hne, ?_⟩` and prove the remaining obligations. Establish `hαF : IsIntegral F α` using `hα.tower_top`. Establish `h1 : aeval α' (minpoly F α) = 0`.

Rewrite using `[hα']`. Conclude with `minpoly.aeval F α'`. Establish `h2 : aeval α' ((minpoly K α).map (algebraMap K F)) = 0`. Take `⟨r, hr⟩` from `minpoly.dvd_map_of_isScalarTower K F α`. Rewrite using `[hr, map_mul, h1, zero_mul]`.

Rewrite `h2` using `[aeval_map_algebraMap]`. Rewrite using `[mem_aroots]`. Conclude with `⟨minpoly.ne_zero hα, h2⟩`. Rewrite using `[← hc]`. Conclude with `(c : F).2`.
-/
theorem exists_mem_untiltField_of_approx [IsAlgClosed C] [IsAlgClosed C♭]
    (hfin : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      FiniteDimensional K (untiltField K C p N))
    (happrox : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
        ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖)
    {α : C} (hα : IsIntegral K α) :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ α ∈ untiltField K C p N := by
  classical
  set d := (minpoly K α).natDegree
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := exists_lt_one_le_pow
    (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)) d
  set ε := (1 + μ) / 2
  have hε0 : 0 < ε := by simp only [ε]; linarith
  have hε1 : ε < 1 := by simp only [ε]; linarith
  set lam := μ / ε
  have hlam0 : 0 ≤ lam := div_nonneg hμ0.le hε0.le
  have hlam1 : lam < 1 := by
    rw [div_lt_one hε0]; simp only [ε]; linarith

  have iter : ∀ k : ℕ, ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧
      ∃ β ∈ untiltField K C p N, ‖α - β‖ ≤ lam ^ k * ‖α‖ := by
    intro k
    induction k with
    | zero => exact ⟨⊥, inferInstance, 0, zero_mem _, by simp⟩
    | succ k ih =>
      obtain ⟨N, hN, β, hβ, hβα⟩ := ih
      have := hN
      have := hfin N hN
      obtain ⟨N', -, hN', β', hβ', hle⟩ := exists_untiltField_norm_sub_le N (happrox N hN) hα
        hμ0.le hμ1.le hμ hε0 hε1 hβ
      refine ⟨N', hN', β', hβ', hle.trans ?_⟩
      rw [pow_succ, mul_comm (lam ^ k) lam, mul_assoc]
      exact mul_le_mul_of_nonneg_left hβα hlam0

  set T : Finset C := ((minpoly K α).aroots C).toFinset.erase α
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ α' ∈ T, ρ ≤ ‖α - α'‖ := by
    by_cases hT : T.Nonempty
    · refine ⟨T.inf' hT fun α' => ‖α - α'‖, ?_, fun α' h => Finset.inf'_le _ h⟩
      rw [Finset.lt_inf'_iff]
      intro α' h
      exact norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase h)))
    · exact ⟨1, one_pos, fun α' h => absurd ⟨α', h⟩ hT⟩
  by_cases hα0 : α = 0
  · exact ⟨⊥, inferInstance, by rw [hα0]; exact zero_mem _⟩
  have hαn : 0 < ‖α‖ := norm_pos_iff.2 hα0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hρ0 hαn) hlam1
  obtain ⟨N, hN, β, hβ, hβα⟩ := iter k
  have hclose : ‖α - β‖ < ρ := by
    refine hβα.trans_lt ?_
    rwa [lt_div_iff₀ hαn] at hk
  have := hN
  have := hfin N hN
  set F := untiltField K C p N
  have : CompleteSpace K := IsPerfectoidField.completeSpace p
  have : CompleteSpace F := FiniteDimensional.complete K F
  have : PerfectField K := perfectField_of_isPerfectoidField K p
  have hsepK : IsSeparable K α := Algebra.IsSeparable.isSeparable K (⟨α, hα⟩ :
    algebraicClosure K C) |> fun h => by
      rwa [IsSeparable, IntermediateField.minpoly_eq] at h
  have hsep : IsSeparable F α := hsepK.tower_top F
  refine ⟨N, hN, ?_⟩
  obtain ⟨c, hc⟩ := mem_range_of_norm_sub_lt (F := F) (E := C) ⟨β, hβ⟩ hsep fun α' hα' hne => by
    refine hclose.trans_le (hρ α' ?_)
    rw [Finset.mem_erase, Multiset.mem_toFinset]
    refine ⟨Ne.symm hne, ?_⟩
    have hαF : IsIntegral F α := hα.tower_top
    have h1 : aeval α' (minpoly F α) = 0 := by
      rw [hα']; exact minpoly.aeval F α'
    have h2 : aeval α' ((minpoly K α).map (algebraMap K F)) = 0 := by
      obtain ⟨r, hr⟩ := minpoly.dvd_map_of_isScalarTower K F α
      rw [hr, map_mul, h1, zero_mul]
    rw [aeval_map_algebraMap] at h2
    rw [mem_aroots]
    exact ⟨minpoly.ne_zero hα, h2⟩
  rw [← hc]
  exact (c : F).2

/- English proof (translation)
Establish `: PerfectField K` using `perfectField_of_isPerfectoidField K p`. Take `⟨γ, hγ⟩` from `Field.exists_primitive_element K L`. Establish `hγi : IsIntegral K (γ : C)` using `(IsIntegral.of_finite K γ).map (IsScalarTower.toAlgHom K L C)`. Take `⟨N, hN, hmem⟩` from `exists_mem_untiltField_of_approx hfin happrox hγi`. Use `⟨N, hN, ?_⟩` and prove the remaining obligations.

Establish `hL : L = IntermediateField.adjoin K {(γ : C)}`. Rewrite using `[← IntermediateField.lift_adjoin_simple, hγ, IntermediateField.lift_top]`. Rewrite using `[hL, IntermediateField.adjoin_simple_le_iff]`. Conclude with `hmem`.
-/
theorem exists_le_untiltField_of_approx [IsAlgClosed C] [IsAlgClosed C♭]
    (hfin : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      FiniteDimensional K (untiltField K C p N))
    (happrox : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
        ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖)
    (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ L ≤ untiltField K C p N := by
  have : PerfectField K := perfectField_of_isPerfectoidField K p
  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element K L
  have hγi : IsIntegral K (γ : C) := (IsIntegral.of_finite K γ).map (IsScalarTower.toAlgHom K L C)
  obtain ⟨N, hN, hmem⟩ := exists_mem_untiltField_of_approx hfin happrox hγi
  refine ⟨N, hN, ?_⟩
  have hL : L = IntermediateField.adjoin K {(γ : C)} := by
    rw [← IntermediateField.lift_adjoin_simple, hγ, IntermediateField.lift_top]
  rw [hL, IntermediateField.adjoin_simple_le_iff]
  exact hmem

/- English proof (translation)
The claim follows from `exists_mem_untiltField_of_approx (fun N hN => by have := hN; infer_instance) (fun N hN _ hy hy1 => by have := hN; exact exists_norm_sub_untilt_le N hy hy1) hα`.
-/
theorem exists_mem_untiltField [IsAlgClosed C] {α : C} (hα : IsIntegral K α) :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ α ∈ untiltField K C p N :=
  exists_mem_untiltField_of_approx (fun N hN => by have := hN; infer_instance)
    (fun N hN _ hy hy1 => by have := hN; exact exists_norm_sub_untilt_le N hy hy1) hα

/- English proof (translation)
The claim follows from `exists_le_untiltField_of_approx (fun N hN => by have := hN; infer_instance) (fun N hN _ hy hy1 => by have := hN; exact exists_norm_sub_untilt_le N hy hy1) L`.
-/
theorem exists_le_untiltField [IsAlgClosed C] (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ L ≤ untiltField K C p N :=
  exists_le_untiltField_of_approx (fun N hN => by have := hN; infer_instance)
    (fun N hN _ hy hy1 => by have := hN; exact exists_norm_sub_untilt_le N hy hy1) L

end GroundTheory.PAdicHodge
