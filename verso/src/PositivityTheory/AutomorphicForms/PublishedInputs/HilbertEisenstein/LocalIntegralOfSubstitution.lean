import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HcToIdele
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.QuasiCharConductorLoc

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalGaussSum

open L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

abbrev tv (v : HeightOneSpectrum (𝓞 F)) (ξ : Fˣ) : (v.adicCompletion F)ˣ :=
  Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ξ

abbrev yv (v : HeightOneSpectrum (𝓞 F)) (yf : (Af F)ˣ) : (v.adicCompletion F)ˣ :=
  Units.map (pLoc F v).toMonoidHom yf

/- English proof (translation)
Rewrite using `[← ord_units_mul]`. Both sides reduce to the same expression.
-/
theorem ordAt_eq (v : HeightOneSpectrum (𝓞 F)) (ξ : Fˣ) (yf : (Af F)ˣ) :
    ordAt (xiF ξ * yf) v = ord ((tv v ξ : (v.adicCompletion F)ˣ) : v.adicCompletion F) +
      ord ((yv v yf : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
  rw [← ord_units_mul]
  rfl

/- English proof (translation)
Rewrite using `[valued_eq_exp_neg_ord u.ne_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem valued_le_iff {v : HeightOneSpectrum (𝓞 F)} (u : (v.adicCompletion F)ˣ) (n : ℤ) :
    Valued.v (u : v.adicCompletion F) ≤ WithZero.exp n ↔ -n ≤ ord (u : v.adicCompletion F) := by
  rw [valued_eq_exp_neg_ord u.ne_zero, WithZero.exp_le_exp]
  omega

def gI (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : HeightOneSpectrum (𝓞 F)) (A B : ℤ)
    (x : (v.adicCompletion F)ˣ) : ℂ :=
  if A ≤ ord (x : v.adicCompletion F) ∧ ord (x : v.adicCompletion F) ≤ B then
    ((ω.loc v x : ℂˣ) : ℂ) * (localAdelicChar F v (x : v.adicCompletion F) : ℂ) else 0

/- English proof (translation)
Establish `h1 : (((tv v ξ * x⁻¹)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ξ : F) = (x : v.adicCompletion F)`. Establish `: (algebraMap F (v.adicCompletion F) (ξ : F)) = ((tv v ξ : (v.adicCompletion F)ˣ) : v.adicCompletion F)` using `rfl`. Rewrite using `[this, mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]`. Establish `h2 : ((tv v ξ * x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * pLoc F v (yf : Af F) = ((tv v ξ * x⁻¹ * yv v yf : (v.adicCompletion F)ˣ) : v.adicCompletion F)` using `rfl`. Establish `hc1 : Valued.v (((tv v ξ * x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * pLoc F v (yf : Af F)) ≤ WithZero.exp (-(c v : ℤ)) ↔ ord (x : v.adicCompletion F) ≤ ordAt (xiF ξ * yf) v - c v`.

Rewrite using `[h2, valued_le_iff, ord_units_mul, ord_units_mul, ord_units_inv, ordAt_eq]`. Use linear arithmetic over natural numbers and integers. Establish `hc2 : Valued.v ((((tv v ξ * x⁻¹)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ξ : F)) ≤ WithZero.exp ((c v : ℤ) + dd v) ↔ -((c v : ℤ) + dd v) ≤ ord (x : v.adicCompletion F)`. Rewrite using `[h1, valued_le_iff]`. Establish `h3 : ((ω.loc v (tv v ξ * x⁻¹) : ℂˣ) : ℂ)⁻¹ = ((ω.loc v (tv v ξ) : ℂˣ) : ℂ)⁻¹ * ((ω.loc v x : ℂˣ) : ℂ)`.

Rewrite using `[map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv, inv_inv]`. Unfold `locF gI`. Rewrite using `[h3, h1]`. Establish `hc2'` using `valued_le_iff x ((c v : ℤ) + dd v)`. Distinguish the cases in `hA : Valued.v (((tv v ξ * x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * pLoc F v (yf : Af F)) ≤ WithZero.exp (-(c v : ℤ)) ∧ Valued.v (x : v.adicCompletion F) ≤ WithZero.exp ((c v : ℤ) + dd v)`.

Rewrite using `[if_pos hA, if_pos ⟨hc2'.1 hA.2, hc1.1 hA.1⟩]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hA, if_neg fun h => hA ⟨hc1.2 h.2, hc2'.2 h.1⟩]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locF_subst (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (yf : (Af F)ˣ) (ξ : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    locF ω c yf (ξ : F) v (tv v ξ * x⁻¹) = ((ω.loc v (tv v ξ) : ℂˣ) : ℂ)⁻¹ *
      gI ω c v (-((c v : ℤ) + dd v)) (ordAt (xiF ξ * yf) v - c v) x := by
  have h1 : (((tv v ξ * x⁻¹)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      algebraMap F (v.adicCompletion F) (ξ : F) = (x : v.adicCompletion F) := by
    have : (algebraMap F (v.adicCompletion F) (ξ : F)) = ((tv v ξ : (v.adicCompletion F)ˣ) : v.adicCompletion F) := rfl
    rw [this, mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have h2 : ((tv v ξ * x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * pLoc F v (yf : Af F) =
      ((tv v ξ * x⁻¹ * yv v yf : (v.adicCompletion F)ˣ) : v.adicCompletion F) := rfl
  have hc1 : Valued.v (((tv v ξ * x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * pLoc F v (yf : Af F)) ≤
      WithZero.exp (-(c v : ℤ)) ↔ ord (x : v.adicCompletion F) ≤ ordAt (xiF ξ * yf) v - c v := by
    rw [h2, valued_le_iff, ord_units_mul, ord_units_mul, ord_units_inv, ordAt_eq]
    omega
  have hc2 : Valued.v ((((tv v ξ * x⁻¹)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      algebraMap F (v.adicCompletion F) (ξ : F)) ≤ WithZero.exp ((c v : ℤ) + dd v) ↔
      -((c v : ℤ) + dd v) ≤ ord (x : v.adicCompletion F) := by
    rw [h1, valued_le_iff]
  have h3 : ((ω.loc v (tv v ξ * x⁻¹) : ℂˣ) : ℂ)⁻¹ =
      ((ω.loc v (tv v ξ) : ℂˣ) : ℂ)⁻¹ * ((ω.loc v x : ℂˣ) : ℂ) := by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv, inv_inv]
  unfold locF gI
  rw [h3, h1]
  have hc2' := valued_le_iff x ((c v : ℤ) + dd v)
  by_cases hA : Valued.v (((tv v ξ * x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * pLoc F v (yf : Af F)) ≤
      WithZero.exp (-(c v : ℤ)) ∧ Valued.v (x : v.adicCompletion F) ≤ WithZero.exp ((c v : ℤ) + dd v)
  · rw [if_pos hA, if_pos ⟨hc2'.1 hA.2, hc1.1 hA.1⟩]
    ring
  · rw [if_neg hA, if_neg fun h => hA ⟨hc1.2 h.2, hc2'.2 h.1⟩]
    ring

/- English proof (translation)
The claim follows from `L2.norm_omega_eq_one hfin _`.
-/
theorem norm_loc {ω : HChar F} (hfin : IsOfFinOrder ω) (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    ‖((ω.loc v x : ℂˣ) : ℂ)‖ = 1 :=
  L2.norm_omega_eq_one hfin _

/- English proof (translation)
The claim follows from `(Units.continuous_val.comp (LocalShellIntegral.continuous_loc ω v)).mul (continuous_subtype_val.comp ((continuous_localAdelicChar v).comp Units.continuous_val))`.
-/
theorem continuous_chiPsi (ω : HChar F) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun x : (v.adicCompletion F)ˣ =>
      ((ω.loc v x : ℂˣ) : ℂ) * (localAdelicChar F v (x : v.adicCompletion F) : ℂ) :=
  (Units.continuous_val.comp (LocalShellIntegral.continuous_loc ω v)).mul
    (continuous_subtype_val.comp ((continuous_localAdelicChar v).comp Units.continuous_val))

/- English proof (translation)
Use `IntegrableOn.of_bound (by rw [multHaar_ordShell]; exact ENNReal.one_lt_top) (continuous_chiPsi ω v).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_loc hfin, Circle.norm_coe, one_mul]`.
-/
theorem integrableOn_shell {ω : HChar F} (hfin : IsOfFinOrder ω) (v : HeightOneSpectrum (𝓞 F)) (k : ℤ) :
    IntegrableOn (fun x : (v.adicCompletion F)ˣ =>
      ((ω.loc v x : ℂˣ) : ℂ) * (localAdelicChar F v (x : v.adicCompletion F) : ℂ))
      (ordShell (v.adicCompletion F) k) (multHaar (v.adicCompletion F)) := by
  refine IntegrableOn.of_bound (by rw [multHaar_ordShell]; exact ENNReal.one_lt_top)
    (continuous_chiPsi ω v).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_loc hfin, Circle.norm_coe, one_mul]

/- English proof (translation)
Unfold `gI`. Distinguish the cases in `h : A ≤ ord (x : v.adicCompletion F) ∧ ord (x : v.adicCompletion F) ≤ A + m`. Rewrite using `[if_pos h, Finset.sum_eq_single_of_mem (ord (x : v.adicCompletion F) - A).toNat (Finset.mem_range.2 (by omega))]`. Rewrite using `[Set.indicator_of_mem]`. Rewrite using `[mem_ordShell]`.

Use linear arithmetic over natural numbers and integers. Introduce `j _ hj`. Rewrite using `[Set.indicator_of_notMem]`. Rewrite using `[mem_ordShell]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg h]`. Use `symm`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Rewrite using `[Set.indicator_of_notMem]`. Rewrite using `[mem_ordShell]`.

Rewrite `hj` using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem gI_eq_sum (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : HeightOneSpectrum (𝓞 F)) (A m : ℤ)
    (hm : 0 ≤ m) (x : (v.adicCompletion F)ˣ) :
    gI ω c v A (A + m) x = ∑ j ∈ Finset.range (m.toNat + 1), (ordShell (v.adicCompletion F) (A + j)).indicator
      (fun x : (v.adicCompletion F)ˣ => ((ω.loc v x : ℂˣ) : ℂ) * (localAdelicChar F v (x : v.adicCompletion F) : ℂ)) x := by
  unfold gI
  by_cases h : A ≤ ord (x : v.adicCompletion F) ∧ ord (x : v.adicCompletion F) ≤ A + m
  · rw [if_pos h, Finset.sum_eq_single_of_mem (ord (x : v.adicCompletion F) - A).toNat
      (Finset.mem_range.2 (by omega))]
    · rw [Set.indicator_of_mem]
      rw [mem_ordShell]
      omega
    · intro j _ hj
      rw [Set.indicator_of_notMem]
      rw [mem_ordShell]
      omega
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Set.indicator_of_notMem]
    rw [mem_ordShell]
    rw [Finset.mem_range] at hj
    omega

/- English proof (translation)
Establish `hfun : gI ω c v A (A + m) = fun x => ∑ j ∈ Finset.range (m.toNat + 1), (ordShell (v.adicCompletion F) (A + j)).indicator (fun x : (v.adicCompletion F)ˣ => ((ω.loc v x : ℂˣ) : ℂ) * (localAdelicChar F v (x : v.adicCompletion F) : ℂ)) x`. Use function extensionality and compare the values at `(gI_eq_sum ω c v A m hm)`. Establish `hint : ∀ j ∈ Finset.range (m.toNat + 1), Integrable ((ordShell (v.adicCompletion F) (A + j)).indicator (fun x : (v.adicCompletion F)ˣ => ((ω.loc v x : ℂˣ) : ℂ) * (localAdelicChar F v (x : v.adicCompletion F) : ℂ))) (multHaar (v.adicCompletion F))` using `fun j _ => (integrableOn_shell hfin v (A + j)).integrable_indicator (measurableSet_ordShell _)`. Rewrite using `[hfun]`. Use `⟨integrable_finset_sum _ hint, ?_⟩` and prove the remaining obligations.

Rewrite using `[integral_finset_sum _ hint]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[integral_indicator (measurableSet_ordShell _)]`.
-/
theorem integral_gI {ω : HChar F} (hfin : IsOfFinOrder ω) (c : HeightOneSpectrum (𝓞 F) → ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (A m : ℤ) (hm : 0 ≤ m) :
    Integrable (gI ω c v A (A + m)) (multHaar (v.adicCompletion F)) ∧
    ∫ x, gI ω c v A (A + m) x ∂multHaar (v.adicCompletion F) =
      ∑ j ∈ Finset.range (m.toNat + 1), ∫ x in ordShell (v.adicCompletion F) (A + j),
        ((ω.loc v x : ℂˣ) : ℂ) * (localAdelicChar F v (x : v.adicCompletion F) : ℂ) ∂multHaar (v.adicCompletion F) := by
  have hfun : gI ω c v A (A + m) = fun x => ∑ j ∈ Finset.range (m.toNat + 1),
      (ordShell (v.adicCompletion F) (A + j)).indicator
      (fun x : (v.adicCompletion F)ˣ => ((ω.loc v x : ℂˣ) : ℂ) * (localAdelicChar F v (x : v.adicCompletion F) : ℂ)) x :=
    funext (gI_eq_sum ω c v A m hm)
  have hint : ∀ j ∈ Finset.range (m.toNat + 1), Integrable ((ordShell (v.adicCompletion F) (A + j)).indicator
      (fun x : (v.adicCompletion F)ˣ => ((ω.loc v x : ℂˣ) : ℂ) * (localAdelicChar F v (x : v.adicCompletion F) : ℂ)))
      (multHaar (v.adicCompletion F)) := fun j _ =>
    (integrableOn_shell hfin v (A + j)).integrable_indicator (measurableSet_ordShell _)
  rw [hfun]
  refine ⟨integrable_finset_sum _ hint, ?_⟩
  rw [integral_finset_sum _ hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_indicator (measurableSet_ordShell _)]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Unfold `gI`. Rewrite using `[if_neg]`. Both sides reduce to the same expression. Introduce `h'`.

Use linear arithmetic over natural numbers and integers.
-/
theorem gI_empty (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : HeightOneSpectrum (𝓞 F)) (A B : ℤ)
    (h : B < A) : gI ω c v A B = 0 := by
  funext x
  unfold gI
  rw [if_neg]
  · rfl
  · intro h'
    omega

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalGaussSum

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4 LocalGaussSum

/- English proof (translation)
Introduce `hInv F _ _ _ ω c H yf ξ v`. Establish `hfin` using `H.fin`. Use `set A : ℤ := -((c v : ℤ) + dd v) with hAdef`. Use `set M : ℤ := ordAt (xiF ξ * yf) v with hMdef`. Use `set m : ℤ := M + dd v with hmdef`.

Establish `hB : M - (c v : ℤ) = A + m` using `by simp only [hAdef, hmdef]; ring`. Take `⟨hiff, heq⟩` from `hInv F v (locF ω c yf (ξ : F) v) (tv v ξ)`. Establish `hsub : (fun x => locF ω c yf (ξ : F) v (tv v ξ * x⁻¹)) = fun x => ((ω.loc v (tv v ξ) : ℂˣ) : ℂ)⁻¹ * gI ω c v A (A + m) x`. Use function extensionality and compare the values at `x`. Rewrite using `[locF_subst, hB]`.

Establish `key : Integrable (gI ω c v A (A + m)) (multHaar (v.adicCompletion F)) ∧ ∫ x, gI ω c v A (A + m) x ∂multHaar (v.adicCompletion F) = if M + dd v < 0 then 0 else cst ω c v * ∑ j ∈ Finset.range ((M + dd v).toNat + 1), chiW ω c v ^ j`. Distinguish the cases in `hm0 : M + dd v < 0`. Rewrite using `[if_pos hm0, gI_empty ω c v A (A + m) (by omega)]`. Conclude with `⟨integrable_zero _ _ _, by simp⟩`. Rewrite using `[if_neg hm0]`.

Establish `hm : 0 ≤ m` using `by omega`. Take `⟨hI, hE⟩` from `integral_gI hfin c v A m hm`. Use `⟨hI, ?_⟩` and prove the remaining obligations. Rewrite using `[hE]`. Distinguish the cases in `hc : c v = 0`.

Establish `hcond` using `LocalShellIntegral.quasiCharConductor_loc (H.cond v)`. Establish `hunr : IsUnramifiedChar (ω.loc v)` using `(quasiCharConductor_eq_zero_iff (LocalShellIntegral.continuous_loc ω v)).1 (hcond.trans hc)`. Establish `hψ1 : ∀ x : (v.adicCompletion F)ˣ, -dd v ≤ ord (x : v.adicCompletion F) → localAdelicChar F v (x : v.adicCompletion F) = 1`. Introduce `x hx`. Establish `ht` using `(isTrivialOn_localAdelicChar_iff v (-dd v)).2 (by rw [LocalShellIntegral.dd_eq])`.

Conclude with `ht _ ((mem_valBall_iff_le_ord x.ne_zero).2 hx)`. Establish `hπ : ord ((atFin v (unif v) : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1`. Establish `h1` using `unif_spec v`. Unfold `IsUnifAt at h1`. Rewrite `h1` using `[valued_eq_exp_neg_ord (atFin v (unif v)).ne_zero, WithZero.exp_inj]`.

Use linear arithmetic over natural numbers and integers. Establish `hval : ((ω.val v : ℂˣ) : ℂ) = ((ω.loc v (unifUnit (v.adicCompletion F)) : ℂˣ) : ℂ)`. Use `quasiChar_apply_eq_of_isUnramified hunr hπ` as an intermediate fact. Conclude with `congrArg (fun u : ℂˣ => (u : ℂ)) this`. Establish `hα : ((ω.val v : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`.

Establish `hterm : ∀ j : ℕ, ∫ x in ordShell (v.adicCompletion F) (A + j), ((ω.loc v x : ℂˣ) : ℂ) * (localAdelicChar F v (x : v.adicCompletion F) : ℂ) ∂multHaar (v.adicCompletion F) = ((ω.val v : ℂˣ) : ℂ) ^ (-dd v) * ((ω.val v : ℂˣ) : ℂ) ^ j`. Introduce `j`. Rewrite using `[setIntegral_congr_fun (measurableSet_ordShell _) (g := fun x => ((ω.loc v x : ℂˣ) : ℂ)) (fun x hx => by`. Rewrite `hx` using `[mem_ordShell]`. Simplify using `only`.

Rewrite using `[hψ1 x (by rw [hx, hAdef, hc]; push_cast; omega), Circle.coe_one, mul_one])]`. Rewrite using `[setIntegral_ordShell_quasiChar (LocalShellIntegral.continuous_loc ω v), if_pos hunr, ← hval, hAdef, hc, Nat.cast_zero, zero_add, zpow_add₀ hα, zpow_natCast]`. Simplify using `only [hterm]`. Rewrite using `[← Finset.mul_sum, cst, if_pos hc]`. Unfold `chiW`.

Rewrite using `[if_pos hc]`. Take `⟨hvan, -⟩` from `local_ramified_holds F ω c H v hc`. Rewrite using `[Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (Nat.succ_pos _)) (fun j _ hj => hvan _ (by`. Establish `: (0 : ℤ) < j` using `by exact_mod_cast Nat.pos_of_ne_zero hj`. Use the proof step `omega))]`.

Establish `hsum : ∑ j ∈ Finset.range (m.toNat + 1), chiW ω c v ^ j = 1`. Unfold `chiW`. Rewrite using `[if_neg hc, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (Nat.succ_pos _)) (fun j _ hj => zero_pow hj), pow_zero]`. Rewrite using `[hsum, mul_one, cst, if_neg hc, Nat.cast_zero, add_zero]`. Use `⟨hiff.2 ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hsub]`. Conclude with `key.1.const_mul _`. Rewrite using `[heq, hsub, integral_const_mul, key.2]`.
-/
theorem local_integral_of_substitution : InvSubst → LocInt := by
  intro hInv F _ _ _ ω c H yf ξ v
  have hfin := H.fin
  set A : ℤ := -((c v : ℤ) + dd v) with hAdef
  set M : ℤ := ordAt (xiF ξ * yf) v with hMdef
  set m : ℤ := M + dd v with hmdef
  have hB : M - (c v : ℤ) = A + m := by simp only [hAdef, hmdef]; ring
  obtain ⟨hiff, heq⟩ := hInv F v (locF ω c yf (ξ : F) v) (tv v ξ)
  have hsub : (fun x => locF ω c yf (ξ : F) v (tv v ξ * x⁻¹)) =
      fun x => ((ω.loc v (tv v ξ) : ℂˣ) : ℂ)⁻¹ * gI ω c v A (A + m) x := by
    funext x
    rw [locF_subst, hB]
  have key : Integrable (gI ω c v A (A + m)) (multHaar (v.adicCompletion F)) ∧
      ∫ x, gI ω c v A (A + m) x ∂multHaar (v.adicCompletion F) =
        if M + dd v < 0 then 0 else
          cst ω c v * ∑ j ∈ Finset.range ((M + dd v).toNat + 1), chiW ω c v ^ j := by
    by_cases hm0 : M + dd v < 0
    · rw [if_pos hm0, gI_empty ω c v A (A + m) (by omega)]
      exact ⟨integrable_zero _ _ _, by simp⟩
    · rw [if_neg hm0]
      have hm : 0 ≤ m := by omega
      obtain ⟨hI, hE⟩ := integral_gI hfin c v A m hm
      refine ⟨hI, ?_⟩
      rw [hE]
      by_cases hc : c v = 0
      · have hcond := LocalShellIntegral.quasiCharConductor_loc (H.cond v)
        have hunr : IsUnramifiedChar (ω.loc v) :=
          (quasiCharConductor_eq_zero_iff (LocalShellIntegral.continuous_loc ω v)).1 (hcond.trans hc)
        have hψ1 : ∀ x : (v.adicCompletion F)ˣ, -dd v ≤ ord (x : v.adicCompletion F) →
            localAdelicChar F v (x : v.adicCompletion F) = 1 := by
          intro x hx
          have ht := (isTrivialOn_localAdelicChar_iff v (-dd v)).2 (by rw [LocalShellIntegral.dd_eq])
          exact ht _ ((mem_valBall_iff_le_ord x.ne_zero).2 hx)
        have hπ : ord ((atFin v (unif v) : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
          have h1 := unif_spec v
          unfold IsUnifAt at h1
          rw [valued_eq_exp_neg_ord (atFin v (unif v)).ne_zero, WithZero.exp_inj] at h1
          omega
        have hval : ((ω.val v : ℂˣ) : ℂ) = ((ω.loc v (unifUnit (v.adicCompletion F)) : ℂˣ) : ℂ) := by
          have := quasiChar_apply_eq_of_isUnramified hunr hπ
          exact congrArg (fun u : ℂˣ => (u : ℂ)) this
        have hα : ((ω.val v : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        have hterm : ∀ j : ℕ, ∫ x in ordShell (v.adicCompletion F) (A + j),
            ((ω.loc v x : ℂˣ) : ℂ) * (localAdelicChar F v (x : v.adicCompletion F) : ℂ) ∂multHaar (v.adicCompletion F) =
            ((ω.val v : ℂˣ) : ℂ) ^ (-dd v) * ((ω.val v : ℂˣ) : ℂ) ^ j := by
          intro j
          rw [setIntegral_congr_fun (measurableSet_ordShell _) (g := fun x => ((ω.loc v x : ℂˣ) : ℂ)) (fun x hx => by
            rw [mem_ordShell] at hx
            simp only
            rw [hψ1 x (by rw [hx, hAdef, hc]; push_cast; omega), Circle.coe_one, mul_one])]
          rw [setIntegral_ordShell_quasiChar (LocalShellIntegral.continuous_loc ω v), if_pos hunr, ← hval, hAdef, hc,
            Nat.cast_zero, zero_add, zpow_add₀ hα, zpow_natCast]
        simp only [hterm]
        rw [← Finset.mul_sum, cst, if_pos hc]
        unfold chiW
        rw [if_pos hc]
      · obtain ⟨hvan, -⟩ := local_ramified_holds F ω c H v hc
        rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (Nat.succ_pos _)) (fun j _ hj => hvan _ (by
          have : (0 : ℤ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
          omega))]
        have hsum : ∑ j ∈ Finset.range (m.toNat + 1), chiW ω c v ^ j = 1 := by
          unfold chiW
          rw [if_neg hc, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (Nat.succ_pos _))
            (fun j _ hj => zero_pow hj), pow_zero]
        rw [hsum, mul_one, cst, if_neg hc, Nat.cast_zero, add_zero]
  refine ⟨hiff.2 ?_, ?_⟩
  · rw [hsub]
    exact key.1.const_mul _
  · rw [heq, hsub, integral_const_mul, key.2]

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
