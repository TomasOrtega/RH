import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Formalism.LocalToGlobal.NormalizedHeckeFactors.ValLeOneOfIsIntegral
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

/- English proof (translation)
Introduce `Ω _ E _ _ _ _ l _ ι n r _hr w hl A h B hF`. Take `⟨hI, hFr⟩` from `hF A h`. Establish `ht` using `isTameChar_tameL h hl`. Establish `hN : IsMonodromy (tameL h hl) r 0` using `(isMonodromy_zero_iff (h := h)).mpr (.of_trivial fun σ => hI σ σ.2)`. Establish `hu1 : (wdOf h hl ι r).unr` using `(hN.unr_wdOf_iff hl ht ι).mpr hI`.

Establish `hm : (0 : ℂ) ∉ B.map fun b => ((b⁻¹ : ℂˣ) : ℂ)`. Simplify using the standard rewrite rules. Establish `hs` using `WD.lpUnr_spec (h := h) _ hm`. Establish `hu2 : (satWD h n B).unr` using `(WD.unr_tw _ _).mpr hs.1`. Rewrite using `[WD.unr_eq_lpUnr _ hu1, WD.unr_eq_lpUnr _ hu2]`.

Use `congr 1`. Rewrite using `[satWD, WD.frobEig_tw _ _ hs.1, hs.2.1, WD.frobEig, WD.eig, hN.charPol_wdOf hl ht ι (frob h)]`. Establish `hσ : IsFrob A (normV w) ((frob h : Weil h) : G E Ω)` using `deg_eq_one_iff.mp deg_frob`. Establish `hc` using `Formalism.L2.NR.charpoly_map_of_inv ι.toRingHom (r (frob h : G E Ω)) _ (by rw [← map_inv]; exact hFr _ hσ)`. Establish `e : ∀ s : Multiset ℂ, s.map (fun μ => X - C μ⁻¹) = (s.map (·⁻¹)).map (fun a => X - C a)` using `fun s => by`.

Rewrite using `[Multiset.map_map]`. Both sides reduce to the same expression. Rewrite using `[hc, e, roots_multiset_prod_X_sub_C, UpperTheory.V.Af.algSat, Multiset.map_map, Multiset.map_map]`. Establish `hB : (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map (Units.val : ℂˣ → ℂ)`. Simplify using `[Multiset.bind_singleton]`.

Rewrite using `[hB, Multiset.map_map]`. Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Units.val_inv_eq_inv_val]`. Establish `hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_cpow hq, show (1 - (n : ℝ)) / 2 = -(((n : ℝ) - 1) / 2) by ring, Real.rpow_neg hq, Complex.ofReal_inv, mul_inv, mul_comm]`.
-/
theorem wdOf_eq_satWD_of_frobEig : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G E Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ B : Multiset ℂˣ, UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat n (normV w) B) → wdOf h hl ι r = satWD h n B := by
  intro Ω _ E _ _ _ _ l _ ι n r _hr w hl A h B hF
  obtain ⟨hI, hFr⟩ := hF A h
  have ht := isTameChar_tameL h hl
  have hN : IsMonodromy (tameL h hl) r 0 :=
    (isMonodromy_zero_iff (h := h)).mpr (.of_trivial fun σ => hI σ σ.2)
  have hu1 : (wdOf h hl ι r).unr := (hN.unr_wdOf_iff hl ht ι).mpr hI
  have hm : (0 : ℂ) ∉ B.map fun b => ((b⁻¹ : ℂˣ) : ℂ) := by
    simp
  have hs := WD.lpUnr_spec (h := h) _ hm
  have hu2 : (satWD h n B).unr := (WD.unr_tw _ _).mpr hs.1
  rw [WD.unr_eq_lpUnr _ hu1, WD.unr_eq_lpUnr _ hu2]
  congr 1
  rw [satWD, WD.frobEig_tw _ _ hs.1, hs.2.1, WD.frobEig, WD.eig, hN.charPol_wdOf hl ht ι (frob h)]
  have hσ : IsFrob A (normV w) ((frob h : Weil h) : G E Ω) := deg_eq_one_iff.mp deg_frob
  have hc := Formalism.L2.NR.charpoly_map_of_inv ι.toRingHom (r (frob h : G E Ω)) _
    (by rw [← map_inv]; exact hFr _ hσ)
  have e : ∀ s : Multiset ℂ, s.map (fun μ => X - C μ⁻¹) = (s.map (·⁻¹)).map (fun a => X - C a) := fun s => by
    rw [Multiset.map_map]; rfl
  rw [hc, e, roots_multiset_prod_X_sub_C, UpperTheory.V.Af.algSat, Multiset.map_map, Multiset.map_map]
  have hB : (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map (Units.val : ℂˣ → ℂ) := by
    simp [Multiset.bind_singleton]
  rw [hB, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_inv_eq_inv_val]
  have hq : (0 : ℝ) ≤ ((normV w : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hq, show (1 - (n : ℝ)) / 2 = -(((n : ℝ) - 1) / 2) by ring,
    Real.rpow_neg hq, Complex.ofReal_inv, mul_inv, mul_comm]

end GlobalTheory.RoadU
