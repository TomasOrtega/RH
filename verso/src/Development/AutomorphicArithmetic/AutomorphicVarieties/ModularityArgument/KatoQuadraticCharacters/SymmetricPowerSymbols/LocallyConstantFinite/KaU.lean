import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

namespace UpperTheory.V.Z.Kato.Sym.PE

/- English proof (translation)
Introduce `Ω _ _ _ ε X m hm θ hθ g h hgz hhz hgm hhm`. Use `haveI : NeZero m := NeZero.of_pos hm`. Take `⟨hprim, hrep, hlg, -⟩` from `lgB Ω ε X m hm`. Establish `hpow : zt X m ^ m = 1` using `hprim.pow_eq_one`. Establish `hgθ : g θ = zt X m ^ (ka X m θ g).val * θ` using `hrep (g θ) θ hθ (by rw [← map_pow, hgm])`.

Establish `hhθ : h θ = zt X m ^ (ka X m θ h).val * θ` using `hrep (h θ) θ hθ (by rw [← map_pow, hhm])`. Establish `hadd : ∀ i j : ZMod m, zt X m ^ i.val * zt X m ^ j.val = zt X m ^ (i + j).val`. Introduce `i j`. Rewrite using `[← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hpow]`. Establish `hhg : h (g θ) = zt X m ^ (ka X m θ h).val * g θ`.

Rewrite using `[hgθ, map_mul, map_pow, hhz, hhθ]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `hlg _ _ _ hθ ?_ show g (h θ) = _` and prove the remaining obligations. Rewrite using `[hhθ, map_mul, map_pow, hgz, hgθ, ← mul_assoc, hadd, add_comm]`.

Conclude with `hlg _ _ _ ((map_ne_zero g).2 hθ) hhg`. Use `hlg _ _ _ hθ ?_ show g.symm (h (g θ)) = _` and prove the remaining obligations. Establish `e2 : g.symm (zt X m) = zt X m`. Rewrite using `[RingEquiv.symm_apply_eq, hgz]`. Rewrite using `[hhg, map_mul, map_pow, e2, RingEquiv.symm_apply_apply]`.
-/
theorem kaU : KaU := by
  intro Ω _ _ _ ε X m hm θ hθ g h hgz hhz hgm hhm
  haveI : NeZero m := NeZero.of_pos hm
  obtain ⟨hprim, hrep, hlg, -⟩ := lgB Ω ε X m hm
  have hpow : zt X m ^ m = 1 := hprim.pow_eq_one
  have hgθ : g θ = zt X m ^ (ka X m θ g).val * θ := hrep (g θ) θ hθ (by rw [← map_pow, hgm])
  have hhθ : h θ = zt X m ^ (ka X m θ h).val * θ := hrep (h θ) θ hθ (by rw [← map_pow, hhm])
  have hadd : ∀ i j : ZMod m, zt X m ^ i.val * zt X m ^ j.val = zt X m ^ (i + j).val := by
    intro i j
    rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hpow]
  have hhg : h (g θ) = zt X m ^ (ka X m θ h).val * g θ := by
    rw [hgθ, map_mul, map_pow, hhz, hhθ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · refine hlg _ _ _ hθ ?_
    show g (h θ) = _
    rw [hhθ, map_mul, map_pow, hgz, hgθ, ← mul_assoc, hadd, add_comm]
  · exact hlg _ _ _ ((map_ne_zero g).2 hθ) hhg
  · refine hlg _ _ _ hθ ?_
    show g.symm (h (g θ)) = _
    have e2 : g.symm (zt X m) = zt X m := by
      rw [RingEquiv.symm_apply_eq, hgz]
    rw [hhg, map_mul, map_pow, e2, RingEquiv.symm_apply_apply]

end UpperTheory.V.Z.Kato.Sym.PE
