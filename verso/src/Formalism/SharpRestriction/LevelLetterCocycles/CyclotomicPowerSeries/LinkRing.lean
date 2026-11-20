import Mathlib
import Formalism.DistinguishedUnitIdeals.GammaCongruentArcFromStart
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCycloStatement
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EmultiplicityEqValuation
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PowValMemPrimitiveRoots

noncomputable section

namespace LevelStatements.Link

open PowerSeries IsLocalRing Formalism.ExponentWindows

abbrev Ks (LL : Type) [Field LL] (l s : ℕ) : Type :=
  ↥(primitiveRoots (l ^ (s + 1)) LL) → LL

/- English proof (translation)
Establish `hp : B.ℓ.Prime` using `hℓ.out`. Establish `hl1 : 0 < B.ℓ - 1` using `by have := hp.two_le; omega`. Establish `hpos : ∀ s, 0 < B.ℓ ^ (s + 1)` using `fun s => pow_pos hp.pos _`. Establish `hprim : ∀ s (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)), IsPrimitiveRoot (ζ : LL) (B.ℓ ^ (s + 1))` using `fun s ζ => (mem_primitiveRoots (hpos s)).1 ζ.2`. Establish `hit : ∀ s a, ι ((⇑B.φ)^[s] a) = (⇑φπ)^[s] (ι a)`.

Introduce `s`. Proceed by induction on `s with`. Consider the case `zero => intro a`. Both sides reduce to the same expression. Consider the case `succ s ih`.

Introduce `a`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', G3, ih]`. Establish `hG : ∀ s, ∃ w' : (PowerSeries O)ˣ, ι (B.p s) = (w' : PowerSeries O) * (((Polynomial.cyclotomic (B.ℓ ^ (s + 1)) O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O)`. Introduce `s`. Take `⟨v, hv⟩` from `G2`.

Unfold `Formalism.ExponentWindows.E.Base.p`. Rewrite using `[hit]`. Conclude with `hPs O B.ℓ hp φπ hφπ (ι B.q) v hv s`. Establish `hcyc : ∀ s < ell, ∀ (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)) (m : ℕ), ρζ ζ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) = Polynomial.aeval (C (ζ : LL) * exp LL) (Polynomial.cyclotomic m LL)` using `fun s hs ζ m => map_cyclotomic_comp (ρζ ζ) ζ (hρζ s hs (ζ : LL) ζ.2) m`. Establish `hK1b : R.K1b`.

Introduce `s hs`. Take `⟨w', hw'⟩` from `hG s`. Establish `hcomp : ∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL), ∃ U : (PowerSeries LL)ˣ, PowerSeries.map (Pi.evalRingHom (fun _ => LL) ζ) (R.ρ s (B.p s)) = (U : PowerSeries LL) * X`. Introduce `ζ`. Take `⟨U, hU⟩` from `hSimple LL LL (B.ℓ ^ (s + 1)) (hpos s) (ζ : LL) (exp LL) ((hprim s ζ).isRoot_cyclotomic (hpos s)) (constantCoeff_exp (A := LL)) (derivative_exp LL)`.

Use `⟨Units.map (ρζ ζ).toMonoidHom w' * U, ?_⟩` and prove the remaining obligations. Rewrite using `[hρ s hs, hw', map_mul, hcyc s hs, hU, Units.val_mul, Units.coe_map, mul_assoc]`. Both sides reduce to the same expression. Use `choose U hU using hcomp`. Establish `hdvd : (X : PowerSeries (Ks LL B.ℓ s)) ^ 1 ∣ R.ρ s (B.p s)` using `(((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s (B.p s))).1 1).2 fun ζ => by`.

Rewrite using `[hU ζ, pow_one]`. Conclude with `dvd_mul_left _ _`. Take `⟨G, hG'⟩` from `hdvd`. Establish `hGu : IsUnit G`. Use `(((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 G).2).2 fun ζ => ?_` and prove the remaining obligations.

Establish `h` using `hU ζ`. Rewrite `h` using `[hG', map_mul, map_pow, map_X, pow_one, mul_comm]`. Rewrite using `[mul_right_cancel₀ X_ne_zero h]`. Conclude with `(U ζ).isUnit`. Use `⟨hGu.unit, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsUnit.unit_spec, hG', pow_one, mul_comm]`. Establish `hUnits : R.UnitsAt`. Introduce `s hs`. Establish `hcomp : ∀ F : PowerSeries O, (∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL), IsUnit (ρζ ζ (ι F))) → IsUnit (R.ρ s F)`. Introduce `F hF`.

Conclude with `(((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s F)).2).2 fun ζ => by`. Rewrite using `[hρ s hs]`. Conclude with `hF ζ`. Use `⟨hcomp X fun ζ => ?_, fun s' hs' hne => hcomp _ fun ζ => ?_⟩` and prove the remaining obligations. Rewrite using `[G1, map_mul, map_pow]`.

Use `(w.isUnit.map (ρζ ζ)).mul (IsUnit.pow _ ?_)` and prove the remaining obligations. Rewrite using `[isUnit_iff_constantCoeff]`. Establish `h` using `congrArg constantCoeff (hρζ s hs (ζ : LL) ζ.2)`. Simplify using `only [map_add, map_one, map_mul, constantCoeff_C, constantCoeff_exp, mul_one] at h`. Rewrite using `[eq_sub_of_add_eq' h]`.

Conclude with `(sub_ne_zero.2 ((hprim s ζ).ne_one (Nat.one_lt_pow (Nat.succ_ne_zero s) hp.one_lt))).isUnit`. Take `⟨w', hw'⟩` from `hG s'`. Rewrite using `[hw', map_mul, hcyc s hs]`. Use `(w'.isUnit.map (ρζ ζ)).mul ?_` and prove the remaining obligations. Rewrite using `[isUnit_iff_constantCoeff, LevelStatements.Lv.constantCoeff_aeval]`.

Simplify using `only [map_mul, constantCoeff_C, constantCoeff_exp, mul_one]`. Use `Ne.isUnit fun h0 => hne ?_` and prove the remaining obligations. Establish `hroot : (Polynomial.cyclotomic (B.ℓ ^ (s' + 1)) LL).IsRoot (ζ : LL)`. Rewrite using `[Polynomial.IsRoot.def, ← Polynomial.coe_aeval_eq_eval]`. Conclude with `h0`.

Establish `h` using `((Polynomial.isRoot_cyclotomic_iff_charZero (hpos s')).1 hroot).unique (hprim s ζ)`. Conclude with `Nat.succ_injective (Nat.pow_right_injective hp.two_le h)`. Establish `hComplR : R.Compl ϖ`. Introduce `s hs k a hk`. Take `⟨ζ, hζ⟩` from `hroot`.

Establish `hζ0 : IsPrimitiveRoot (ζ ^ (B.ℓ ^ (n0 - (s + 1)))) (B.ℓ ^ (s + 1))` using `hζ.pow (pow_pos hp.pos _) (by rw [← pow_add]; congr 1; omega)`. Establish `hcd` using `hCompl O LL B.ℓ s hp hℓm ⟨_, hζ0⟩ ρζ (fun ζ' hζ' => hρζ s hs ζ' ((mem_primitiveRoots (hpos s)).2 hζ')) k (ι a) (fun ζ' hζ' => by`. Establish `h` using `(((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s a)).1 k).1 hk ⟨ζ', (mem_primitiveRoots (hpos s)).2 hζ'⟩`. Rewrite using `[hρ s hs] at h)` and apply the resulting hypothesis. Take `⟨w', hw'⟩` from `hG s`.

Establish `hdv : ι (B.p s ^ k) ∣ ι a`. Rewrite using `[map_pow, hw', mul_pow, ← Units.val_pow_eq_pow_val, Units.mul_left_dvd]`. Conclude with `hcd`. Take `⟨z, hz⟩` from `(hDesc O ι (B.ℓ - 1) hl1 ⟨w, G1⟩).2 _ _ hdv`. Conclude with `⟨0, z, by rw [pow_zero, map_one, one_mul]; exact hz⟩`.

Establish `hunitu : ∀ s, IsUnit (PadicInt.toZModPow (s + 1) uZ)` using `fun s => IsUnit.of_pow_eq_one (pow_orderOf_eq_one _) (by rw [LevelStatements.Ln03.orderOf_u hℓ2 uZ huZ s]; exact (pow_pos hp.pos _).ne')`. Establish `hunitom : ∀ s j, IsUnit (PadicInt.toZModPow (s + 1) (om j))` using `fun s j => IsUnit.of_pow_eq_one (by rw [← map_pow, hom j, map_one]) hl1.ne'`. Establish `hmem : ∀ s (a : ZMod (B.ℓ ^ (s + 1))), IsUnit a → ∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL), (ζ : LL) ^ a.val ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL` using `fun s a ha ζ => pow_val_mem_primitiveRoots _ (hpos s) a ha ζ.2`. Establish `hsig : ∀ s < ell, ∀ (x : Ks LL B.ℓ s) (k : ℕ) (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)), ∃ ζ' : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL), (ζ' : LL) = (ζ : LL) ^ ((PadicInt.toZModPow (s + 1) uZ).val ^ k) ∧ (⇑(R.lev s).σ)^[k] x ζ = x ζ'`. Introduce `s hs x k`.

Proceed by induction on `k with`. Consider the case `zero => intro ζ; exact ⟨ζ, by simp, rfl⟩`. Consider the case `succ k ih`. Introduce `ζ`. Take `⟨ζ2, h2, h2'⟩` from `ih ⟨_, hmem s _ (hunitu s) ζ⟩`.

Use `⟨ζ2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`. Express the relevant statement in the definitionally equal form `((ζ : LL) ^ _) ^ _ = _`. Rewrite using `[← pow_mul, ← pow_succ']`. Rewrite using `[Function.iterate_succ_apply', hσ s hs _ ζ ⟨_, hmem s _ (hunitu s) ζ⟩ rfl, h2']`.

Establish `hK1c : ∀ s < ell, (R.lev s).FiniteOrderFixed B.ℓ s`. Introduce `s hs`. Use `⟨fun x => ?_, fun x hxσ hxτ => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `ζ`. Take `⟨ζ', h1, h2⟩` from `hsig s hs x (B.ℓ ^ s) ζ`.

Rewrite using `[h2]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[h1]`. Conclude with `(LevelStatements.Ln03.sigma_u_order hℓ2 s uZ huZ ζ.2 _).2 dvd_rfl`.

Set `f : LL → LL` to `fun y => if h : y ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL then x ⟨y, h⟩ else 0`. Establish `hfu : ∀ ξ ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL, f (ξ ^ (PadicInt.toZModPow (s + 1) uZ).val) = f ξ`. Introduce `ξ hξ`. Establish `hm` using `hmem s _ (hunitu s) ⟨ξ, hξ⟩`. Simplify using `only [f]`.

Rewrite using `[dif_pos hm, dif_pos hξ]`. Establish `h` using `hσ s hs x ⟨ξ, hξ⟩ ⟨_, hm⟩ rfl`. Rewrite `h` using `[hxσ]`. Conclude with `h.symm`. Establish `hfΔ : ∀ a : ZMod (B.ℓ ^ (s + 1)), a ^ (B.ℓ - 1) = 1 → ∀ ξ ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL, f (ξ ^ a.val) = f ξ`.

Introduce `a ha ξ hξ`. Take `⟨j, hj⟩` from `exists_toZModPow_eq_of_pow_pred_eq_one om hom hom' s a ha`. Establish `hm` using `hmem s a (IsUnit.of_pow_eq_one ha hl1.ne') ⟨ξ, hξ⟩`. Simplify using `only [f]`. Rewrite using `[dif_pos hm, dif_pos hξ]`.

Establish `h` using `hτ s hs j x ⟨ξ, hξ⟩ ⟨_, hm⟩ (by rw [hj])`. Rewrite `h` using `[hxτ j]`. Conclude with `h.symm`. Establish `hconst` using `LevelStatements.Ln03.invariants_const hℓ2 s uZ huZ f hfu hfΔ`. Distinguish the cases in `hne : Nonempty ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)`.

Take `⟨ξ0⟩` from `hne`. Use `⟨x ξ0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `ζ`. Establish `h` using `hconst ξ0 ξ0.2 ζ ζ.2`. Simplify using `only [f, dif_pos ξ0.2, dif_pos ζ.2] at h`.

Simplify using `only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Conclude with `h`. Use `⟨0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `ζ`. Conclude with `absurd ⟨ζ⟩ hne`.

Establish `hK1d : ∀ s < ell, (R.lev s).PhiGammaCommute`. Introduce `s hs j x`. Use function extensionality and compare the values at `ζ`. Establish `e1` using `hσ s hs ((R.lev s).τ j x) ζ ⟨_, hmem s _ (hunitu s) ζ⟩ rfl`. Establish `e2` using `hτ s hs j x ⟨_, hmem s _ (hunitu s) ζ⟩ ⟨_, hmem s _ (hunitom s j) ⟨_, hmem s _ (hunitu s) ζ⟩⟩ rfl`.

Establish `e3` using `hτ s hs j ((R.lev s).σ x) ζ ⟨_, hmem s _ (hunitom s j) ζ⟩ rfl`. Establish `e4` using `hσ s hs x ⟨_, hmem s _ (hunitom s j) ζ⟩ ⟨_, hmem s _ (hunitom s j) ⟨_, hmem s _ (hunitu s) ζ⟩⟩ (by`. Express the relevant statement in the definitionally equal form `((ζ : LL) ^ _) ^ _ = ((ζ : LL) ^ _) ^ _`. Rewrite using `[← pow_mul, ← pow_mul, mul_comm])`. Rewrite using `[e1, e2, e3, e4]`.

Conclude with `⟨hK1b, fun s hs => hu s hs, fun s hs => ⟨hK1c s hs, hK1d s hs⟩, hUnits, hComplR⟩`.
-/
theorem linkRing

    (hUnique : LevelStatements.Lv.RhoUniqueStatement) (hCompl : LevelStatements.Lv.SplitComplStatement)
    (hSimple : LevelStatements.Lv.CycloSimpleStatement) (hCop : LevelStatements.Lv.PsCoprimeStatement)
    (hUnit : LevelStatements.Lv.RhoUnitStatement) (hDesc : LevelStatements.Lv.DescendDvdStatement)
    (hPi : LevelStatements.Lv.PiSeriesStatement)

    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O]
    {LL : Type} [Field LL] [CharZero LL] [Algebra O LL] [IsFractionRing O LL]
    (ϖ : O) (hϖ : Irreducible ϖ)

    {B : E.Base O} {n : ℕ} {V : Type} [AddCommGroup V] [Module (PowerSeries O) V]
    {L : E.Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}
    (S : E.LevelData L c ell Λ r) {Δ D : Type} [AddCommGroup D] [Module LL D]
    [hℓ : Fact B.ℓ.Prime] (hℓ2 : B.ℓ ≠ 2) (hℓm : (B.ℓ : O) ∈ maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (B.ℓ ^ n0))

    (ι : PowerSeries O →ₐ[O] PowerSeries O) (w : (PowerSeries O)ˣ)
    (G1 : ι X = (w : PowerSeries O) * X ^ (B.ℓ - 1))

    (φπ : PowerSeries O →ₐ[O] PowerSeries O) (hφπ : φπ X = (1 + X) ^ B.ℓ - 1)
    (G3 : ∀ a, ι (B.φ a) = φπ (ι a))

    (hPs : LevelStatements.Lv.PsCycloStatement)
    (G2 : ∃ v : (PowerSeries O)ˣ, ι B.q = (v : PowerSeries O) *
      (((Polynomial.cyclotomic B.ℓ O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))

    (ρζ : LL → (PowerSeries O →ₐ[O] PowerSeries LL))
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL, 1 + ρζ ζ X = C ζ * exp LL)

    (R : G.LevelModel S LL (fun s => Ks LL B.ℓ s) Δ D)
    (hρ : ∀ s < ell, ∀ (a : PowerSeries O) (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      PowerSeries.map (Pi.evalRingHom (fun _ => LL) ζ) (R.ρ s a) = ρζ ζ (ι a))
    (u : Oˣ) (uZ : ℤ_[B.ℓ]) (huZ : (uZ - 1).valuation = 1)
    (ιZ : ℤ_[B.ℓ] →+* O) (hutie : ιZ uZ = (u : O))
    (hu : ∀ s < ell, ((R.lev s).u : LL) = algebraMap O LL (u : O))
    (hσ : ∀ s < ell, ∀ (f : Ks LL B.ℓ s) (ζ ζ' : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      (ζ' : LL) = (ζ : LL) ^ (PadicInt.toZModPow (s + 1) uZ).val → (R.lev s).σ f ζ = f ζ')
    (om : Δ → ℤ_[B.ℓ]) (hom : ∀ j, om j ^ (B.ℓ - 1) = 1)
    (hom' : ∀ a : ZMod B.ℓ, a ≠ 0 → ∃ j, PadicInt.toZMod (om j) = a)
    (hτ : ∀ s < ell, ∀ j (f : Ks LL B.ℓ s) (ζ ζ' : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      (ζ' : LL) = (ζ : LL) ^ (PadicInt.toZModPow (s + 1) (om j)).val → (R.lev s).τ j f ζ = f ζ') :
    R.K1b ∧ R.HasU u ∧ (∀ s < ell, (R.lev s).FiniteOrderFixed B.ℓ s ∧ (R.lev s).PhiGammaCommute) ∧ R.UnitsAt ∧ R.Compl ϖ := by
  have hp : B.ℓ.Prime := hℓ.out
  have hl1 : 0 < B.ℓ - 1 := by have := hp.two_le; omega
  have hpos : ∀ s, 0 < B.ℓ ^ (s + 1) := fun s => pow_pos hp.pos _
  have hprim : ∀ s (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      IsPrimitiveRoot (ζ : LL) (B.ℓ ^ (s + 1)) :=
    fun s ζ => (mem_primitiveRoots (hpos s)).1 ζ.2

  have hit : ∀ s a, ι ((⇑B.φ)^[s] a) = (⇑φπ)^[s] (ι a) := by
    intro s
    induction s with
    | zero => intro a; rfl
    | succ s ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', G3, ih]

  have hG : ∀ s, ∃ w' : (PowerSeries O)ˣ, ι (B.p s) = (w' : PowerSeries O) *
      (((Polynomial.cyclotomic (B.ℓ ^ (s + 1)) O).comp (Polynomial.X + 1) : Polynomial O) :
        PowerSeries O) := by
    intro s
    obtain ⟨v, hv⟩ := G2
    unfold Formalism.ExponentWindows.E.Base.p
    rw [hit]
    exact hPs O B.ℓ hp φπ hφπ (ι B.q) v hv s

  have hcyc : ∀ s < ell, ∀ (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)) (m : ℕ),
      ρζ ζ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
        Polynomial.aeval (C (ζ : LL) * exp LL) (Polynomial.cyclotomic m LL) :=
    fun s hs ζ m => map_cyclotomic_comp (ρζ ζ) ζ (hρζ s hs (ζ : LL) ζ.2) m

  have hK1b : R.K1b := by
    intro s hs
    obtain ⟨w', hw'⟩ := hG s
    have hcomp : ∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL), ∃ U : (PowerSeries LL)ˣ,
        PowerSeries.map (Pi.evalRingHom (fun _ => LL) ζ) (R.ρ s (B.p s)) =
          (U : PowerSeries LL) * X := by
      intro ζ
      obtain ⟨U, hU⟩ := hSimple LL LL (B.ℓ ^ (s + 1)) (hpos s) (ζ : LL) (exp LL)
        ((hprim s ζ).isRoot_cyclotomic (hpos s)) (constantCoeff_exp (A := LL)) (derivative_exp LL)
      refine ⟨Units.map (ρζ ζ).toMonoidHom w' * U, ?_⟩
      rw [hρ s hs, hw', map_mul, hcyc s hs, hU, Units.val_mul, Units.coe_map, mul_assoc]
      rfl
    choose U hU using hcomp
    have hdvd : (X : PowerSeries (Ks LL B.ℓ s)) ^ 1 ∣ R.ρ s (B.p s) :=
      (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s (B.p s))).1 1).2 fun ζ => by
        rw [hU ζ, pow_one]
        exact dvd_mul_left _ _
    obtain ⟨G, hG'⟩ := hdvd
    have hGu : IsUnit G := by
      refine (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 G).2).2 fun ζ => ?_
      have h := hU ζ
      rw [hG', map_mul, map_pow, map_X, pow_one, mul_comm] at h
      rw [mul_right_cancel₀ X_ne_zero h]
      exact (U ζ).isUnit
    refine ⟨hGu.unit, ?_⟩
    rw [IsUnit.unit_spec, hG', pow_one, mul_comm]

  have hUnits : R.UnitsAt := by
    intro s hs
    have hcomp : ∀ F : PowerSeries O, (∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL),
        IsUnit (ρζ ζ (ι F))) → IsUnit (R.ρ s F) := by
      intro F hF
      exact (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s F)).2).2 fun ζ => by
        rw [hρ s hs]
        exact hF ζ
    refine ⟨hcomp X fun ζ => ?_, fun s' hs' hne => hcomp _ fun ζ => ?_⟩
    · rw [G1, map_mul, map_pow]
      refine (w.isUnit.map (ρζ ζ)).mul (IsUnit.pow _ ?_)
      rw [isUnit_iff_constantCoeff]
      have h := congrArg constantCoeff (hρζ s hs (ζ : LL) ζ.2)
      simp only [map_add, map_one, map_mul, constantCoeff_C, constantCoeff_exp, mul_one] at h
      rw [eq_sub_of_add_eq' h]
      exact (sub_ne_zero.2 ((hprim s ζ).ne_one (Nat.one_lt_pow (Nat.succ_ne_zero s) hp.one_lt))).isUnit
    · obtain ⟨w', hw'⟩ := hG s'
      rw [hw', map_mul, hcyc s hs]
      refine (w'.isUnit.map (ρζ ζ)).mul ?_
      rw [isUnit_iff_constantCoeff, LevelStatements.Lv.constantCoeff_aeval]
      simp only [map_mul, constantCoeff_C, constantCoeff_exp, mul_one]
      refine Ne.isUnit fun h0 => hne ?_
      have hroot : (Polynomial.cyclotomic (B.ℓ ^ (s' + 1)) LL).IsRoot (ζ : LL) := by
        rw [Polynomial.IsRoot.def, ← Polynomial.coe_aeval_eq_eval]
        exact h0
      have h := ((Polynomial.isRoot_cyclotomic_iff_charZero (hpos s')).1 hroot).unique (hprim s ζ)
      exact Nat.succ_injective (Nat.pow_right_injective hp.two_le h)

  have hComplR : R.Compl ϖ := by
    intro s hs k a hk
    obtain ⟨ζ, hζ⟩ := hroot
    have hζ0 : IsPrimitiveRoot (ζ ^ (B.ℓ ^ (n0 - (s + 1)))) (B.ℓ ^ (s + 1)) :=
      hζ.pow (pow_pos hp.pos _) (by rw [← pow_add]; congr 1; omega)
    have hcd := hCompl O LL B.ℓ s hp hℓm ⟨_, hζ0⟩ ρζ
      (fun ζ' hζ' => hρζ s hs ζ' ((mem_primitiveRoots (hpos s)).2 hζ')) k (ι a)
      (fun ζ' hζ' => by
        have h := (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s a)).1 k).1 hk
          ⟨ζ', (mem_primitiveRoots (hpos s)).2 hζ'⟩
        rwa [hρ s hs] at h)
    obtain ⟨w', hw'⟩ := hG s
    have hdv : ι (B.p s ^ k) ∣ ι a := by
      rw [map_pow, hw', mul_pow, ← Units.val_pow_eq_pow_val, Units.mul_left_dvd]
      exact hcd
    obtain ⟨z, hz⟩ := (hDesc O ι (B.ℓ - 1) hl1 ⟨w, G1⟩).2 _ _ hdv
    exact ⟨0, z, by rw [pow_zero, map_one, one_mul]; exact hz⟩

  have hunitu : ∀ s, IsUnit (PadicInt.toZModPow (s + 1) uZ) := fun s =>
    IsUnit.of_pow_eq_one (pow_orderOf_eq_one _)
      (by rw [LevelStatements.Ln03.orderOf_u hℓ2 uZ huZ s]; exact (pow_pos hp.pos _).ne')
  have hunitom : ∀ s j, IsUnit (PadicInt.toZModPow (s + 1) (om j)) := fun s j =>
    IsUnit.of_pow_eq_one (by rw [← map_pow, hom j, map_one]) hl1.ne'
  have hmem : ∀ s (a : ZMod (B.ℓ ^ (s + 1))), IsUnit a →
      ∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL),
        (ζ : LL) ^ a.val ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL := fun s a ha ζ =>
    pow_val_mem_primitiveRoots _ (hpos s) a ha ζ.2
  have hsig : ∀ s < ell, ∀ (x : Ks LL B.ℓ s) (k : ℕ) (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      ∃ ζ' : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL),
        (ζ' : LL) = (ζ : LL) ^ ((PadicInt.toZModPow (s + 1) uZ).val ^ k) ∧
          (⇑(R.lev s).σ)^[k] x ζ = x ζ' := by
    intro s hs x k
    induction k with
    | zero => intro ζ; exact ⟨ζ, by simp, rfl⟩
    | succ k ih =>
      intro ζ
      obtain ⟨ζ2, h2, h2'⟩ := ih ⟨_, hmem s _ (hunitu s) ζ⟩
      refine ⟨ζ2, ?_, ?_⟩
      · rw [h2]
        change ((ζ : LL) ^ _) ^ _ = _
        rw [← pow_mul, ← pow_succ']
      · rw [Function.iterate_succ_apply', hσ s hs _ ζ ⟨_, hmem s _ (hunitu s) ζ⟩ rfl, h2']

  have hK1c : ∀ s < ell, (R.lev s).FiniteOrderFixed B.ℓ s := by
    intro s hs
    refine ⟨fun x => ?_, fun x hxσ hxτ => ?_⟩
    · funext ζ
      obtain ⟨ζ', h1, h2⟩ := hsig s hs x (B.ℓ ^ s) ζ
      rw [h2]
      congr 1
      apply Subtype.ext
      rw [h1]
      exact (LevelStatements.Ln03.sigma_u_order hℓ2 s uZ huZ ζ.2 _).2 dvd_rfl
    · classical
      let f : LL → LL := fun y =>
        if h : y ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL then x ⟨y, h⟩ else 0
      have hfu : ∀ ξ ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL,
          f (ξ ^ (PadicInt.toZModPow (s + 1) uZ).val) = f ξ := by
        intro ξ hξ
        have hm := hmem s _ (hunitu s) ⟨ξ, hξ⟩
        simp only [f]
        rw [dif_pos hm, dif_pos hξ]
        have h := hσ s hs x ⟨ξ, hξ⟩ ⟨_, hm⟩ rfl
        rw [hxσ] at h
        exact h.symm
      have hfΔ : ∀ a : ZMod (B.ℓ ^ (s + 1)), a ^ (B.ℓ - 1) = 1 →
          ∀ ξ ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL, f (ξ ^ a.val) = f ξ := by
        intro a ha ξ hξ
        obtain ⟨j, hj⟩ := exists_toZModPow_eq_of_pow_pred_eq_one om hom hom' s a ha
        have hm := hmem s a (IsUnit.of_pow_eq_one ha hl1.ne') ⟨ξ, hξ⟩
        simp only [f]
        rw [dif_pos hm, dif_pos hξ]
        have h := hτ s hs j x ⟨ξ, hξ⟩ ⟨_, hm⟩ (by rw [hj])
        rw [hxτ j] at h
        exact h.symm
      have hconst := LevelStatements.Ln03.invariants_const hℓ2 s uZ huZ f hfu hfΔ
      by_cases hne : Nonempty ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)
      · obtain ⟨ξ0⟩ := hne
        refine ⟨x ξ0, ?_⟩
        funext ζ
        have h := hconst ξ0 ξ0.2 ζ ζ.2
        simp only [f, dif_pos ξ0.2, dif_pos ζ.2] at h
        simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        exact h
      · refine ⟨0, ?_⟩
        funext ζ
        exact absurd ⟨ζ⟩ hne

  have hK1d : ∀ s < ell, (R.lev s).PhiGammaCommute := by
    intro s hs j x
    funext ζ
    have e1 := hσ s hs ((R.lev s).τ j x) ζ ⟨_, hmem s _ (hunitu s) ζ⟩ rfl
    have e2 := hτ s hs j x ⟨_, hmem s _ (hunitu s) ζ⟩
      ⟨_, hmem s _ (hunitom s j) ⟨_, hmem s _ (hunitu s) ζ⟩⟩ rfl
    have e3 := hτ s hs j ((R.lev s).σ x) ζ ⟨_, hmem s _ (hunitom s j) ζ⟩ rfl
    have e4 := hσ s hs x ⟨_, hmem s _ (hunitom s j) ζ⟩
      ⟨_, hmem s _ (hunitom s j) ⟨_, hmem s _ (hunitu s) ζ⟩⟩
      (by
        change ((ζ : LL) ^ _) ^ _ = ((ζ : LL) ^ _) ^ _
        rw [← pow_mul, ← pow_mul, mul_comm])
    rw [e1, e2, e3, e4]
  exact ⟨hK1b, fun s hs => hu s hs, fun s hs => ⟨hK1c s hs, hK1d s hs⟩, hUnits, hComplR⟩

end LevelStatements.Link
