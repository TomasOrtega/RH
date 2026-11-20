import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.KerTransfer

/- English proof (translation)
Establish `hmC' : (m' : ℂ) = 2 * (aS : ℂ)` using `by exact_mod_cast hm'`. Establish `hmem : ∀ v, U'.symm (R₂.ι v) ∈ kFin M' τ` using `fun v => (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩`. Set `j : R₂.HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ` to `{ toFun := fun v => ⟨U'.symm (R₂.ι v), hmem v⟩ map_add' := fun v w => Subtype.ext (by simp) map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }`. Establish `hj : ∀ v, U' (j v : M'.H τ) = R₂.ι v` using `fun v => U'.apply_symm_apply _`. Establish `hsurj : Function.Surjective j` using `fun y => by`.

Take `⟨v, hv⟩` from `(h₂.kfin y).1 y.2`. Conclude with `⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩`. Establish `key : ∀ (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z), IsLocPair M M' τ aS aT a' B → ∃ B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z, IsCoverPair R₂.HK B' ∧ ∀ P v, B' (κ P) v = B P (j v)`. Introduce `Z _ _ B hB`. Set `B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z` to `{ toFun := fun P => (B (κ.symm P)).comp j map_add' := fun P Q => by ext v; simp map_smul' := fun c P => by ext v; simp }`.

Establish `hB' : ∀ P v, B' (κ P) v = B P (j v)` using `fun P v => by simp [B']`. Use `⟨B', ⟨fun X hX P P' y y' => ?_, fun Y hY P y => ?_⟩, hB'⟩` and prove the remaining obligations. Take `⟨P, rfl⟩` from `κ.surjective P`. Take `⟨P', rfl⟩` from `κ.surjective P'`. Establish `hX' : toFrame M τ (barMat e X) ∈ lieAt V τ` using `h₁.lie ▸ ⟨X, hX, rfl⟩`.

Establish `h3 : (barMat e X).map (starRingEnd ℂ) = Matrix.reindex e e X` using `by ext a b; simp [barMat]`. Establish `h4 : (barMat e X).trace = -X.trace`. Rewrite using `[barMat, trace_reindex', ← trace_conj hX]`. Simplify using `[Matrix.trace]`. Establish `h` using `hB.skew _ hX' P P' (j y) (j y')`.

Simplify using `only [sOp, fr_toFrame, trace_toFrame, h3, h4, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, map_neg, map_mul, map_ratCast, trace_conj hX] at h`. Rewrite using `[← hκ.1, ← hκ.1, hB', hB', hB', hB']`. Take the linear combination `h`. Take `⟨P, rfl⟩` from `κ.surjective P`. Establish `hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ` using `h₂.lie ▸ ⟨Y, hY, rfl⟩`.

Establish `h4 : (plainMat e' Y).trace = Y.trace` using `trace_reindex' e' Y`. Establish `h5 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j (R₂.HK.act Y y) - ((aS : ℂ) * Y.trace) • j y`. Establish `h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j (R₂.HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y)`. Use `Subtype.ext (U'.injective ?_)` and prove the remaining obligations. Rewrite using `[hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]`.

Rewrite using `[h6, map_add, LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC', sub_eq_add_neg, ← neg_smul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `hB.inv _ hY' P (j y)`. Rewrite `h` using `[h5, tOp, fr_toFrame, trace_toFrame, h4]`.

Rewrite using `[← hκ.2, hB', hB', ← h]`. Simplify using `[plainMat]`. Introduce `Z₁ Z₂ _ _ _ _ B₁ B₂ hB₁ hB₂ hne n a b hs`. Take `⟨C₁, hC₁, e₁⟩` from `key Z₁ B₁ hB₁`. Take `⟨C₂, hC₂, e₂⟩` from `key Z₂ B₂ hB₂`.

Use `choose g hg using hsurj`. Establish `hne' : C₁ ≠ 0` using `fun h0 => hne (LinearMap.ext fun P => LinearMap.ext fun y => by`. Rewrite using `[← hg y, ← e₁, h0]`. Use the proof step `rfl)`. Establish `h` using `hC Z₁ Z₂ C₁ C₂ hC₁ hC₂ hne' n (fun i => κ (a i)) (fun i => g (b i)) (by simpa [e₁, hg] using hs)`.

Simplify `h` using `[e₂, hg]`.
-/
theorem locKer_of_coverKer (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ → R₁.U.H)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s)
    (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) (hm' : (m' : ℚ) = 2 * aS)
    (h₁ : Matches R₁ M τ (barMat e) m U) (h₂ : Matches R₂ M' τ (plainMat e') m' U')
    (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) (ha : IsKAct M' τ a') (hC : CoverKer p q R₂.HK) :
    LocKer M M' τ aS aT a' := by
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm (R₂.ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : R₂.HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm (R₂.ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = R₂.ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  have key : ∀ (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
      (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z), IsLocPair M M' τ aS aT a' B →
      ∃ B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z, IsCoverPair R₂.HK B' ∧
        ∀ P v, B' (κ P) v = B P (j v) := by
    intro Z _ _ B hB
    let B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z :=
      { toFun := fun P => (B (κ.symm P)).comp j
        map_add' := fun P Q => by ext v; simp
        map_smul' := fun c P => by ext v; simp }
    have hB' : ∀ P v, B' (κ P) v = B P (j v) := fun P v => by simp [B']
    refine ⟨B', ⟨fun X hX P P' y y' => ?_, fun Y hY P y => ?_⟩, hB'⟩
    · obtain ⟨P, rfl⟩ := κ.surjective P
      obtain ⟨P', rfl⟩ := κ.surjective P'
      have hX' : toFrame M τ (barMat e X) ∈ lieAt V τ := h₁.lie ▸ ⟨X, hX, rfl⟩
      have h3 : (barMat e X).map (starRingEnd ℂ) = Matrix.reindex e e X := by ext a b; simp [barMat]
      have h4 : (barMat e X).trace = -X.trace := by
        rw [barMat, trace_reindex', ← trace_conj hX]
        simp [Matrix.trace]
      have h := hB.skew _ hX' P P' (j y) (j y')
      simp only [sOp, fr_toFrame, trace_toFrame, h3, h4, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, map_neg, map_mul, map_ratCast, trace_conj hX] at h
      rw [← hκ.1, ← hκ.1, hB', hB', hB', hB']
      linear_combination h
    · obtain ⟨P, rfl⟩ := κ.surjective P
      have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
      have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
      have h5 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j (R₂.HK.act Y y) - ((aS : ℂ) * Y.trace) • j y := by
        have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
            j (R₂.HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
          refine Subtype.ext (U'.injective ?_)
          rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
        rw [h6, map_add, LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
          sub_eq_add_neg, ← neg_smul]
        congr 2
        ring
      have h := hB.inv _ hY' P (j y)
      rw [h5, tOp, fr_toFrame, trace_toFrame, h4] at h
      rw [← hκ.2, hB', hB', ← h]
      simp [plainMat]
  intro Z₁ Z₂ _ _ _ _ B₁ B₂ hB₁ hB₂ hne n a b hs
  obtain ⟨C₁, hC₁, e₁⟩ := key Z₁ B₁ hB₁
  obtain ⟨C₂, hC₂, e₂⟩ := key Z₂ B₂ hB₂
  choose g hg using hsurj
  have hne' : C₁ ≠ 0 := fun h0 => hne (LinearMap.ext fun P => LinearMap.ext fun y => by
    rw [← hg y, ← e₁, h0]; rfl)
  have h := hC Z₁ Z₂ C₁ C₂ hC₁ hC₂ hne' n (fun i => κ (a i)) (fun i => g (b i)) (by simpa [e₁, hg] using hs)
  simpa [e₂, hg] using h

end GlobalTheory.Chain.IoLift.KerTransfer

end
