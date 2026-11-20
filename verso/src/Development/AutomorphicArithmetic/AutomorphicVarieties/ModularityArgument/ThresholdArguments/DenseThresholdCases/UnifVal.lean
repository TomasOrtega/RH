import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.HeckeCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Hi.Up
section Loc
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {w : Plc F} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}
/- English proof (translation)
Establish `h1 : (ψ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) = _` using `ho.val s _ rfl (Set.mem_univ _)`. Establish `h2 : algPow w (-htW lam i) (a s : w.adicCompletion F) * algPow w (fun _ => 1) (a s : w.adicCompletion F) ^ (i : ℕ) = (algPow w (lowW lam i) (a s : w.adicCompletion F))⁻¹` using `by haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}`. Unfold `algPow`. Simplify using `only [finprod_eq_prod_of_fintype]`. Rewrite using `[← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_one, ← zpow_natCast, ← zpow_add₀ ((map_ne_zero j.1).2 (a s).ne_zero), ← zpow_neg]`. Simplify using `[htW]`. Rewrite using `[h1, UpperTheory.V.Loc.epsArt hN.aut.art h hw a ha s, ← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ord_val (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (ha : IsLocalArtin h a) {lam : Wt F l n} {i : Fin n}
    {ω : (w.adicCompletion F)ˣ →* ℂˣ} {ψ : Dec (F := F) A →* (Qbar l)ˣ} (ho : OrdChar ι a ω (htW lam i) ψ) (s : Weil h) :
    (ψ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * (cycBar F Ω l s : Qbar l) ^ (i : ℕ) =
      (algPow w (lowW lam i) (a s : w.adicCompletion F))⁻¹ * (ι.symm (ω (a s)) * (((normV w : ℕ) : Qbar l) ^ deg s) ^ (i : ℕ)) := by
  have h1 : (ψ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) = _ := ho.val s _ rfl (Set.mem_univ _)
  have h2 : algPow w (-htW lam i) (a s : w.adicCompletion F) * algPow w (fun _ => 1) (a s : w.adicCompletion F) ^ (i : ℕ) =
      (algPow w (lowW lam i) (a s : w.adicCompletion F))⁻¹ := by
    haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
    haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
    unfold algPow
    simp only [finprod_eq_prod_of_fintype]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [zpow_one, ← zpow_natCast, ← zpow_add₀ ((map_ne_zero j.1).2 (a s).ne_zero), ← zpow_neg]
    simp [htW]
  rw [h1, UpperTheory.V.Loc.epsArt hN.aut.art h hw a ha s, ← h2]
  ring
end Loc
section Set
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} {Q : QData V} {c : Coef l} {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r}
  {Λ : LamObj r} (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (x : B.Pt) {lam : Wt L l n}
/- English proof (translation)
Establish `ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1))` using `hA.art_spec v`. Take `⟨t, ht⟩` from `ha.surj u`. Establish `hd : deg t = 0`. Use `ha.ord_eq t` as an intermediate fact. Rewrite `this` using `[ht, ord_eq_zero u.2]`.

Use linear arithmetic over natural numbers and integers. Establish `h1` using `congrArg (fun z : Λ.Λˣ => x (Λ.toPair B.u z)) (R.theta v i t (Subgroup.inclusion (Weil_le_Dec _) t) (deg_eq_zero_iff.1 hd) u rfl ht)`. Establish `h2` using `ord_val (w := s.w v.1) hN (hA.Sl_over v) ha ho t`. Establish `h3` using `congrArg (fun z : B.Bˣ => x z) (DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i) ⟨Subgroup.inclusion (Weil_le_Dec _) t, deg_eq_zero_iff.1 hd⟩)`. Establish `h4 : x (Λ.toPair B.u ((hset Q R.τ₀).epsV Λ.Λ v (Subgroup.inclusion (Weil_le_Dec _) t) : Λ.Λˣ)) = cycBar L Ω l t` using `(x.comp (Λ.toPair B.u)).commutes _`.

Simplify using `only [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h1`. Use `erw [h4] at h1`. Rewrite `h2` using `[hd, ht, zpow_zero, one_pow, mul_one]`. Establish `h5` using `(congrArg (· * _) (h2.symm.trans (congrArg (· * _) h3.symm))).trans h1`. Rewrite using `[← ι.apply_symm_apply (ω u : ℂ), ← map_mul, ← map_one ι, ← h5]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `_ * (x (Λ.toPair B.u _) / algPow (s.w v.1) _ _) = _`. Rewrite using `[div_eq_inv_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ordChar_unit_mul_finite_component_eq_one (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hA : (hset Q R.τ₀).Ax) (v : V.frame.Vl) (i : Fin n)
    {ω : ((s.w v.1).adicCompletion L)ˣ →* ℂˣ} (ho : OrdChar ι (artOf (s.hw v.1)) ω (htW lam i) (x.psi v i))
    (u : Uo ((s.w v.1).adicCompletion L)) :
    (ω u : ℂ) * ι ((hset Q R.τ₀).finPart R.θ (x.comp (Λ.toPair B.u)).toRingHom lam v i u) = 1 := by
  have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := hA.art_spec v
  obtain ⟨t, ht⟩ := ha.surj u
  have hd : deg t = 0 := by
    have := ha.ord_eq t
    rw [ht, ord_eq_zero u.2] at this
    omega
  have h1 := congrArg (fun z : Λ.Λˣ => x (Λ.toPair B.u z))
    (R.theta v i t (Subgroup.inclusion (Weil_le_Dec _) t) (deg_eq_zero_iff.1 hd) u rfl ht)
  have h2 := ord_val (w := s.w v.1) hN (hA.Sl_over v) ha ho t
  have h3 := congrArg (fun z : B.Bˣ => x z) (DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i)
    ⟨Subgroup.inclusion (Weil_le_Dec _) t, deg_eq_zero_iff.1 hd⟩)
  have h4 : x (Λ.toPair B.u ((hset Q R.τ₀).epsV Λ.Λ v (Subgroup.inclusion (Weil_le_Dec _) t) : Λ.Λˣ)) = cycBar L Ω l t :=
    (x.comp (Λ.toPair B.u)).commutes _
  simp only [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h1
  erw [h4] at h1
  rw [hd, ht, zpow_zero, one_pow, mul_one] at h2
  have h5 := (congrArg (· * _) (h2.symm.trans (congrArg (· * _) h3.symm))).trans h1
  rw [← ι.apply_symm_apply (ω u : ℂ), ← map_mul, ← map_one ι, ← h5]
  congr 1
  change _ * (x (Λ.toPair B.u _) / algPow (s.w v.1) _ _) = _
  rw [div_eq_inv_mul]
  ring
/- English proof (translation)
Establish `ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1))` using `hA.art_spec v`. Take `⟨t, ht⟩` from `ha.surj (unif _)`. Establish `hd : deg t = -1`. Use `ha.ord_eq t` as an intermediate fact. Rewrite `this` using `[ht, ord_eq_one GlAx.unif_spec]`.

Use linear arithmetic over natural numbers and integers. Set `g : Dec (F` to `L) (s.A v.1) := Subgroup.inclusion (Weil_le_Dec _) t`. Set `b : B.Bˣ` to `∏ i with i ≤ j, B.u.ψ v i g * (hset Q R.τ₀).epsV B.B v g ^ (i : ℕ)`. Establish `h1 : ι.symm (((hset Q R.τ₀).lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)) = x b`. Establish `h4 : x ((hset Q R.τ₀).epsV B.B v g : B.Bˣ) = cycBar L Ω l t` using `x.commutes _`.

Establish `e : (Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1) = Finset.univ.filter fun i : Fin n => i ≤ j` using `Finset.filter_congr fun i _ => Nat.lt_succ_iff`. Simplify using `only [b, HSet.lowVal, psEig, e, Units.coe_prod, map_prod, map_mul, map_inv₀, Units.val_mul, Units.val_pow_eq_pow_val, map_pow, h4, RingEquiv.symm_apply_apply, map_natCast]`. Rewrite using `[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h2` using `ord_val (w := s.w v.1) hN (hA.Sl_over v) ha (ho i) t`.

Rewrite `h2` using `[hd, ht, ← resCard_eq_normV, zpow_neg_one, inv_pow]`. Conclude with `h2.symm`. Rewrite using `[h1]`. Use `⟨pt_unit x b, pt_res x _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[← R.res.unif v j t g rfl ht]`.

Establish `h4 : Alg.res c.O B.B ((hset Q R.τ₀).epsV B.B v g : B.Bˣ) = ((hset Q R.τ₀).epsV (ResidueField c.O) v g : (ResidueField c.O)ˣ)` using `(Alg.res c.O B.B).commutes _`. Simplify using `only [b, Units.coe_prod, map_prod, map_mul, Units.val_mul, Units.val_pow_eq_pow_val, map_pow, h4]`. Conclude with `Finset.prod_congr rfl fun i _ => congrArg (· * _) ((B.u.psi v i).red g)`.
-/
theorem norm_lowVal_inv_mul_psEig_eq_one_and_norm_sub_lt_one (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hA : (hset Q R.τ₀).Ax) (v : V.frame.Vl)
    {ω : Fin n → ((s.w v.1).adicCompletion L)ˣ →* ℂˣ} (ho : ∀ i, OrdChar ι (artOf (s.hw v.1)) (ω i) (htW lam i) (x.psi v i))
    (j : Fin n) : ‖ι.symm (((hset Q R.τ₀).lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1))‖ = 1 ∧
      ‖ι.symm (((hset Q R.τ₀).lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)) - algebraMap c.O (Qbar l) (R.a (.inr (v, j)))‖ < 1 := by
  have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := hA.art_spec v
  obtain ⟨t, ht⟩ := ha.surj (unif _)
  have hd : deg t = -1 := by
    have := ha.ord_eq t
    rw [ht, ord_eq_one GlAx.unif_spec] at this
    omega
  let g : Dec (F := L) (s.A v.1) := Subgroup.inclusion (Weil_le_Dec _) t
  let b : B.Bˣ := ∏ i with i ≤ j, B.u.ψ v i g * (hset Q R.τ₀).epsV B.B v g ^ (i : ℕ)
  have h1 : ι.symm (((hset Q R.τ₀).lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)) = x b := by
    have h4 : x ((hset Q R.τ₀).epsV B.B v g : B.Bˣ) = cycBar L Ω l t := x.commutes _
    have e : (Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1) = Finset.univ.filter fun i : Fin n => i ≤ j :=
      Finset.filter_congr fun i _ => Nat.lt_succ_iff
    simp only [b, HSet.lowVal, psEig, e, Units.coe_prod, map_prod, map_mul, map_inv₀, Units.val_mul, Units.val_pow_eq_pow_val,
      map_pow, h4, RingEquiv.symm_apply_apply, map_natCast]
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h2 := ord_val (w := s.w v.1) hN (hA.Sl_over v) ha (ho i) t
    rw [hd, ht, ← resCard_eq_normV, zpow_neg_one, inv_pow] at h2
    exact h2.symm
  rw [h1]
  refine ⟨pt_unit x b, pt_res x _ _ ?_⟩
  rw [← R.res.unif v j t g rfl ht]
  have h4 : Alg.res c.O B.B ((hset Q R.τ₀).epsV B.B v g : B.Bˣ) = ((hset Q R.τ₀).epsV (ResidueField c.O) v g : (ResidueField c.O)ˣ) :=
    (Alg.res c.O B.B).commutes _
  simp only [b, Units.coe_prod, map_prod, map_mul, Units.val_mul, Units.val_pow_eq_pow_val, map_pow, h4]
  exact Finset.prod_congr rfl fun i _ => congrArg (· * _) ((B.u.psi v i).red g)
end Set
end UpperTheory.V.Hi.Up
end
