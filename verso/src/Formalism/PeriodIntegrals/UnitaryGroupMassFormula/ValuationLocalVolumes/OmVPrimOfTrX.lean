import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IotaAlgInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVPrimOfDdX

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Establish `hmem : X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) ∈ D.host.F` using `(X.ιE_F _).2 ⟨x0, rfl⟩`. Use `set y : D.host.F := ⟨_, hmem⟩`. Establish `hi : IsIntegral ℤ (X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)))` using `((RingOfIntegers.isIntegral_coe x0).map (algebraMap X.B.I.F X.B.I.E).toIntAlgHom).map (X.ιE : X.B.I.E →+* D.host.E).toIntAlgHom`. Establish `hy : IsIntegral ℤ y` using `(isIntegral_algHom_iff ((D.host.F).subtype : D.host.F →+* D.host.E).toIntAlgHom Subtype.val_injective).1 hi`. Conclude with `⟨⟨y, (mem_integralClosure_iff ℤ _).2 hy⟩, rfl⟩`.
-/
theorem host_el (x0 : 𝓞 X.B.I.F) : ∃ d0 : 𝓞 D.host.F, ((d0 : D.host.F) : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) := by
  have hmem : X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) ∈ D.host.F := (X.ιE_F _).2 ⟨x0, rfl⟩
  set y : D.host.F := ⟨_, hmem⟩
  have hi : IsIntegral ℤ (X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F))) :=
    ((RingOfIntegers.isIntegral_coe x0).map (algebraMap X.B.I.F X.B.I.E).toIntAlgHom).map (X.ιE : X.B.I.E →+* D.host.E).toIntAlgHom
  have hy : IsIntegral ℤ y :=
    (isIntegral_algHom_iff ((D.host.F).subtype : D.host.F →+* D.host.E).toIntAlgHom Subtype.val_injective).1 hi
  exact ⟨⟨y, (mem_integralClosure_iff ℤ _).2 hy⟩, rfl⟩

/- English proof (translation)
Take `⟨x0, hx0, hv0⟩` from `(dV_isDiffVal v).2.2`. Take `⟨d0, hd0e⟩` from `host_el X x0`. Establish `hd0 : d0 ∈ differentIdeal ℤ (𝓞 D.host.F)` using `(hT d0).2 ⟨x0, hx0, hd0e.symm⟩`. Use `set g : 𝓞 D.host.E := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d0 with hg_def`. Establish `hgE : (g : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F))` using `hd0e`.

Use `set c : Fv X.B.I.F v := algebraMap X.B.I.F (Fv X.B.I.F v) (x0 : X.B.I.F) with hc_def`. Establish `hvd0 : Valued.v (dV v) ≠ 0` using `(Valuation.ne_zero_iff _).2 (dV_ne_zero v)`. Establish `hc0 : c ≠ 0`. Introduce `h`. Rewrite `hv0` using `[h, map_zero]`.

Conclude with `hvd0 hv0.symm`. Establish `hg0 : (g : D.host.E) ≠ 0`. Rewrite using `[hgE]`. Introduce `h`. Apply `hc0` to reduce the goal to its premises.

Establish `: algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F) = 0`. Rewrite `h` using `[← map_zero X.ιE]`. Conclude with `X.ιE.injective h`. Rewrite using `[hc_def, (algebraMap X.B.I.F X.B.I.E).injective (this.trans (map_zero _).symm), map_zero]`. Establish `hgk : (g : D.host.E) ^ k ∈ ddS D ^ k`.

Rewrite using `[ddS_pow, FractionalIdeal.mem_coeIdeal]`. Conclude with `⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (d0 ^ k), Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hd0 k), by rw [map_pow, map_pow]⟩`. Establish `hne : ddS D ^ k ≠ 0`. Introduce `h`. Rewrite `hgk` using `[h, FractionalIdeal.mem_zero_iff]`.

Conclude with `hg0 (by by_contra hne0; exact (pow_ne_zero k hne0) hgk)`. Establish `hprod : x * (g : D.host.E) ^ k ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)`. Use `FractionalIdeal.mul_mem_mul hx hgk` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel₀ hne]`. Then use the resulting hypothesis. Take `⟨o, ho⟩` from `(FractionalIdeal.mem_one_iff _).1 hprod`.

Establish `key : X.ιE.symm x * (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) ^ k = X.ιE.symm (o : D.host.E)`. Establish `h1 : ((o : D.host.E)) = x * (g : D.host.E) ^ k` using `ho`. Rewrite using `[h1, map_mul, map_pow, hgE, RingEquiv.symm_apply_apply]`. Establish `key2 : inclR (F` using `X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) * algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (c ^ k) = inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (o : D.host.E)) := by`. Rewrite using `[← key, map_mul, map_pow, map_pow, hc_def, alg_alg]`.

Establish `hu : Valued.v (dV v * c⁻¹) = 1` using `by rw [map_mul, map_inv₀, ← hv0, mul_inv_cancel₀ (hv0 ▸ hvd0)]`. Establish `hid : (dV v * c⁻¹) ^ k * c ^ k = dV v ^ k`. Rewrite using `[mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hc0), mul_one]`. Establish `e : sc (E` using `X.B.I.E) v (dV v ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) = algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((dV v * c⁻¹) ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (o : D.host.E)) := by`. Rewrite using `[← key2]`.

Express the relevant statement in the definitionally equal form `algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (dV v ^ k) * _ = _`. Rewrite using `[← hid, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `oev_mul v (alg_int_mem X v _ ?_) (incl_mem v (⟨X.ιE.symm (o : D.host.E), (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E))` and prove the remaining obligations.

Rewrite using `[map_pow, hu, one_pow]`.
-/
theorem dd2 (hT : OmVDdTr X) (v : PlX X) (k : ℕ) (x : D.host.E) (hx : x ∈ (ddS D ^ k)⁻¹) :
    sc (E := X.B.I.E) v ((dV v) ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v := by
  obtain ⟨x0, hx0, hv0⟩ := (dV_isDiffVal v).2.2
  obtain ⟨d0, hd0e⟩ := host_el X x0
  have hd0 : d0 ∈ differentIdeal ℤ (𝓞 D.host.F) := (hT d0).2 ⟨x0, hx0, hd0e.symm⟩
  set g : 𝓞 D.host.E := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d0 with hg_def
  have hgE : (g : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) := hd0e
  set c : Fv X.B.I.F v := algebraMap X.B.I.F (Fv X.B.I.F v) (x0 : X.B.I.F) with hc_def
  have hvd0 : Valued.v (dV v) ≠ 0 := (Valuation.ne_zero_iff _).2 (dV_ne_zero v)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hv0; exact hvd0 hv0.symm
  have hg0 : (g : D.host.E) ≠ 0 := by
    rw [hgE]; intro h
    apply hc0
    have : algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F) = 0 := by
      rw [← map_zero X.ιE] at h; exact X.ιE.injective h
    rw [hc_def, (algebraMap X.B.I.F X.B.I.E).injective (this.trans (map_zero _).symm), map_zero]
  have hgk : (g : D.host.E) ^ k ∈ ddS D ^ k := by
    rw [ddS_pow, FractionalIdeal.mem_coeIdeal]
    exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (d0 ^ k),
      Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hd0 k), by rw [map_pow, map_pow]⟩
  have hne : ddS D ^ k ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hgk
    exact hg0 (by by_contra hne0; exact (pow_ne_zero k hne0) hgk)
  have hprod : x * (g : D.host.E) ^ k ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    have := FractionalIdeal.mul_mem_mul hx hgk
    rwa [inv_mul_cancel₀ hne] at this
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
  have key : X.ιE.symm x * (algebraMap X.B.I.F X.B.I.E (x0 : X.B.I.F)) ^ k = X.ιE.symm (o : D.host.E) := by
    have h1 : ((o : D.host.E)) = x * (g : D.host.E) ^ k := ho
    rw [h1, map_mul, map_pow, hgE, RingEquiv.symm_apply_apply]
  have key2 : inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) *
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (c ^ k) =
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (o : D.host.E)) := by
    rw [← key, map_mul, map_pow, map_pow, hc_def, alg_alg]
  have hu : Valued.v (dV v * c⁻¹) = 1 := by rw [map_mul, map_inv₀, ← hv0, mul_inv_cancel₀ (hv0 ▸ hvd0)]
  have hid : (dV v * c⁻¹) ^ k * c ^ k = dV v ^ k := by
    rw [mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hc0), mul_one]
  have e : sc (E := X.B.I.E) v (dV v ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) =
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ((dV v * c⁻¹) ^ k) *
        inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (o : D.host.E)) := by
    rw [← key2]
    change algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (dV v ^ k) * _ = _
    rw [← hid, map_mul]; ring
  rw [e]
  refine oev_mul v (alg_int_mem X v _ ?_) (incl_mem v (⟨X.ιE.symm (o : D.host.E),
    (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E))
  rw [map_pow, hu, one_pow]

/- English proof (translation)
Introduce `v a`. Establish `hlt : ((a.castSucc : Fin (D.R.rS + 1)) : ℕ) < D.R.rS` using `by simp`. Establish `halp : alp v D.R.rS a.castSucc = (dV v)⁻¹ ^ (D.R.rS - (a : ℕ))`. Unfold `alp`. Rewrite using `[if_pos hlt]`.

Simplify using the standard rewrite rules. Establish `hk : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ)`. Rewrite using `[Nat.cast_sub a.isLt.le]`. Establish `haa : aaD D a = (ddS D ^ (D.R.rS - (a : ℕ)))⁻¹`. Unfold `aaD`.

Rewrite using `[hk, zpow_neg, zpow_natCast]`. Use `⟨fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[haa, inv_inv]`. Rewrite using `[halp]`. Conclude with `dd1 X hT v _ x hx`.

Rewrite `hx` using `[haa]`. Rewrite using `[halp, inv_pow, inv_inv]`. Conclude with `dd2 X hT v _ x hx`.
-/
theorem omVDdLoc_of (hT : OmVDdTr X) : OmVDdLoc X := by
  intro v a
  have hlt : ((a.castSucc : Fin (D.R.rS + 1)) : ℕ) < D.R.rS := by simp
  have halp : alp v D.R.rS a.castSucc = (dV v)⁻¹ ^ (D.R.rS - (a : ℕ)) := by
    unfold alp; rw [if_pos hlt]; simp
  have hk : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
    rw [Nat.cast_sub a.isLt.le]
  have haa : aaD D a = (ddS D ^ (D.R.rS - (a : ℕ)))⁻¹ := by
    unfold aaD; rw [hk, zpow_neg, zpow_natCast]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [haa, inv_inv] at hx; rw [halp]; exact dd1 X hT v _ x hx
  · rw [haa] at hx; rw [halp, inv_pow, inv_inv]; exact dd2 X hT v _ x hx

variable (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

/- English proof (translation)
The claim follows from `omV_of_dd X u' ψ (omVDdLoc_of X hT) hScale hBad hLocU`.
-/
theorem omV_of_tr (hT : OmVDdTr X) (hScale : OmVScale X u' ψ) (hBad : OmVBadT X u' ψ) (hLocU : OmVLocU X ψ) :
    Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  omV_of_dd X u' ψ (omVDdLoc_of X hT) hScale hBad hLocU

/- English proof (translation)
The claim follows from `omVPrim_of_dd X u' (omVDdLoc_of X hT)`.
-/
theorem omVPrim_of_tr (hT : OmVDdTr X) : OmVPrim X u' := omVPrim_of_dd X u' (omVDdLoc_of X hT)

/- English proof (translation)
The claim follows from `omVPrim_of_dd X u' (omVDdLoc_of X hT)`.
-/
theorem omVPrim_of_trX (hT : OmVDdTr X) : Formalism.L2.SG.Pf.NcX.OmVSt.OmVPrim X u' := omVPrim_of_dd X u' (omVDdLoc_of X hT)

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
