import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelTwistTrivialLocalMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNear
import Formalism.LocalToGlobal.Columns.RecLevelLocP
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.IntSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ}

/- English proof (translation)
Establish `he : (Pi.single j 1 : Sp E n) ∈ Formalism.L2.Col.stdAt E n P`. Use `Formalism.L2.Col.le_locP P _ ((mem_stdLat _).2 fun l => ?_)` and prove the remaining obligations. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Use `exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩]`.

Establish `hGe : G (Pi.single j 1) ∈ Formalism.L2.Col.stdAt E n P` using `(hG (Pi.single j 1)).2 he`. Establish `hint : Formalism.L2.Col.IntAt P (G (Pi.single j 1) i)`. Take `⟨s, hs, hsx⟩` from `(Formalism.L2.Col.mem_locP P _ _).1 hGe`. Take `⟨r, hr⟩` from `(mem_stdLat _).1 hsx i`. Use `⟨r, s, hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[hr]`. Simplify using `[Algebra.smul_def]`. Establish `e : LinearMap.toMatrix' G.toLinearMap i j = G (Pi.single j 1) i`. Rewrite using `[LinearMap.toMatrix'_apply]`. Use `congr 2`.

Rewrite using `[e]`. Conclude with `LevRead.hasRes_le (ReadBad.hasRes_redP hint)`.
-/
theorem val_entry_le {P : HeightOneSpectrum (𝓞 E)} {G : Sp E n ≃ₗ[E] Sp E n} (hG : G ∈ Formalism.L2.Col.GLint E n P) (i j : Fin n) :
    Valued.v (algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' G.toLinearMap i j)) ≤ 1 := by
  have he : (Pi.single j 1 : Sp E n) ∈ Formalism.L2.Col.stdAt E n P := by
    refine Formalism.L2.Col.le_locP P _ ((mem_stdLat _).2 fun l => ?_)
    rw [Pi.single_apply]
    split_ifs
    exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩]
  have hGe : G (Pi.single j 1) ∈ Formalism.L2.Col.stdAt E n P := (hG (Pi.single j 1)).2 he
  have hint : Formalism.L2.Col.IntAt P (G (Pi.single j 1) i) := by
    obtain ⟨s, hs, hsx⟩ := (Formalism.L2.Col.mem_locP P _ _).1 hGe
    obtain ⟨r, hr⟩ := (mem_stdLat _).1 hsx i
    refine ⟨r, s, hs, ?_⟩
    rw [hr]
    simp [Algebra.smul_def]
  have e : LinearMap.toMatrix' G.toLinearMap i j = G (Pi.single j 1) i := by
    rw [LinearMap.toMatrix'_apply]
    congr 2
  rw [e]
  exact LevRead.hasRes_le (ReadBad.hasRes_redP hint)

/- English proof (translation)
Establish `hne : Q.under (𝓞 F) ≠ v` using `fun e => hQ (e ▸ (rfl : Formalism.L2.Col.IsOver (Q.under (𝓞 F)) Q))`. Establish `h1 : bc (prV (E` using `E) (Q.under (𝓞 F))) u = bc (prV (E := E) (Q.under (𝓞 F))) (1 : GL (Fin n) (AfE F E)) := by`. Rewrite using `[map_one]`. Conclude with `hu _ hne`. Establish `h2 : adAt F Q ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j) = adAt F Q (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)`.

Apply `ChTwRead.adAt_congr_prV` to reduce the goal to its premises. Conclude with `congrArg (fun g => g.1 i j) h1`. Rewrite using `[h2, Units.val_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem val_away {u : GL (Fin n) (AfE F E)} {v : HeightOneSpectrum (𝓞 F)}
    (hu : ∀ v', v' ≠ v → bc (prV (E := E) v') u = 1) {Q : HeightOneSpectrum (𝓞 E)} (hQ : ¬ Formalism.L2.Col.IsOver v Q) (i j : Fin n) :
    Valued.v (adAt F Q ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 := by
  have hne : Q.under (𝓞 F) ≠ v := fun e => hQ (e ▸ (rfl : Formalism.L2.Col.IsOver (Q.under (𝓞 F)) Q))
  have h1 : bc (prV (E := E) (Q.under (𝓞 F))) u = bc (prV (E := E) (Q.under (𝓞 F))) (1 : GL (Fin n) (AfE F E)) := by
    rw [map_one]; exact hu _ hne
  have h2 : adAt F Q ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      adAt F Q (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
    apply ChTwRead.adAt_congr_prV
    exact congrArg (fun g => g.1 i j) h1
  rw [h2, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `h` using `Opn.inv_eq_cT hc.sig (u := u) hu`. Establish `h'` using `congrFun (congrFun h j) i`. Use `h'.trans ?_` and prove the remaining obligations. Unfold `cT`. Rewrite using `[Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_sub, Matrix.transpose_one, add_sub_cancel]`.

Both sides reduce to the same expression.
-/
theorem inv_entry (hc : CMData F E) {u : GL (Fin n) (AfE F E)} (hu : u ∈ Formalism.L2.Herm.UstdAf hc n) (i j : Fin n) :
    ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) j i =
      sigR hc.sig (FiniteAdeleRing (𝓞 F) F) ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  have h := Opn.inv_eq_cT hc.sig (u := u) hu
  have h' := congrFun (congrFun h j) i
  refine h'.trans ?_
  unfold cT
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_sub, Matrix.transpose_one,
    add_sub_cancel]
  rfl

/- English proof (translation)
Establish `e1 : (adAt F P).mapMatrix (u : Matrix (Fin n) (Fin n) (AfE F E)) = (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' g.toLinearMap)`. Conclude with `Matrix.ext fun r s => h r s`. Establish `e2 : (adAt F P).mapMatrix ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) * (adAt F P).mapMatrix (u : Matrix (Fin n) (Fin n) (AfE F E)) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Establish `e3 : (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' g.toLinearMap) * (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' (g⁻¹).toLinearMap) = 1`.

Rewrite using `[← map_mul, ← LinearMap.toMatrix'_comp]`. Establish `: g.toLinearMap ∘ₗ (g⁻¹).toLinearMap = LinearMap.id`. Conclude with `LinearMap.ext fun y => g.apply_symm_apply y`. Rewrite using `[this, LinearMap.toMatrix'_id, map_one]`. Rewrite `e2` using `[e1]`.

Establish `e4` using `left_inv_eq_right_inv e2 e3`. Conclude with `congrFun (congrFun e4 r) s`.
-/
theorem adAt_inv {u : GL (Fin n) (AfE F E)} {P : HeightOneSpectrum (𝓞 E)} {g : Sp E n ≃ₗ[E] Sp E n}
    (h : ∀ r s, adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) (r s : Fin n) :
    adAt F P (((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' (g⁻¹).toLinearMap r s) := by
  have e1 : (adAt F P).mapMatrix (u : Matrix (Fin n) (Fin n) (AfE F E)) =
      (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' g.toLinearMap) := by
    exact Matrix.ext fun r s => h r s
  have e2 : (adAt F P).mapMatrix ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *
      (adAt F P).mapMatrix (u : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e3 : (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' g.toLinearMap) *
      (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' (g⁻¹).toLinearMap) = 1 := by
    rw [← map_mul, ← LinearMap.toMatrix'_comp]
    have : g.toLinearMap ∘ₗ (g⁻¹).toLinearMap = LinearMap.id := by
      exact LinearMap.ext fun y => g.apply_symm_apply y
    rw [this, LinearMap.toMatrix'_id, map_one]
  rw [e1] at e2
  have e4 := left_inv_eq_right_inv e2 e3
  exact congrFun (congrFun e4 r) s

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n u hu v P hv hsup g hg hcomp i j`. Establish `hsup' : ∀ v', v' ≠ v → bc (prV (E` using `E) v') u⁻¹ = 1 := fun v' h => by rw [map_inv, hsup v' h, inv_one]`. Establish `a1 : ∀ r s, Valued.v (adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s)) ≤ 1` using `fun r s => by`. Rewrite using `[hcomp]`. Conclude with `val_entry_le hg r s`.

Establish `a2 : ∀ r s, Valued.v (adAt F P (((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)) ≤ 1` using `fun r s => by`. Rewrite using `[adAt_inv hcomp]`. Conclude with `val_entry_le (inv_mem hg) r s`. Use `⟨(mem_rInt_iff F E _).2 fun Q => ?_, (mem_rInt_iff F E _).2 fun Q => ?_⟩` and prove the remaining obligations. Use `show Valued.v (adAt F Q _) ≤ 1`.

Distinguish the cases in `hQ : Formalism.L2.Col.IsOver v Q`. Break down `rll_over_cases hc hv hQ with rfl | rfl` into its components or cases. Conclude with `a1 i j`. Apply the tactic sequence `rw [← valued_sigR hc, ← inv_entry hc hu]`. Conclude with `a2 j i`.

Conclude with `val_away hsup hQ i j`. Use `show Valued.v (adAt F Q _) ≤ 1`. Distinguish the cases in `hQ : Formalism.L2.Col.IsOver v Q`. Break down `rll_over_cases hc hv hQ with rfl | rfl` into its components or cases. Conclude with `a2 i j`.

Apply the tactic sequence `rw [← valued_sigR hc, ← inv_entry hc (inv_mem hu), inv_inv]`. Conclude with `a1 j i`. Conclude with `val_away hsup' hQ i j`.
-/
theorem int_of_supported : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) {n : ℕ} (u : GL (Fin n) (AfE F E)), u ∈ Formalism.L2.Herm.UstdAf hc n → ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v P → (∀ v', v' ≠ v → bc (prV (E := E) v') u = 1) → ∀ g ∈ Formalism.L2.Col.GLint E n P, (∀ r s, adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) → ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E ∧ ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E := by
  intro F E _ _ _ _ _ _ hc n u hu v P hv hsup g hg hcomp i j
  have hsup' : ∀ v', v' ≠ v → bc (prV (E := E) v') u⁻¹ = 1 := fun v' h => by rw [map_inv, hsup v' h, inv_one]
  have a1 : ∀ r s, Valued.v (adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s)) ≤ 1 := fun r s => by
    rw [hcomp]; exact val_entry_le hg r s
  have a2 : ∀ r s, Valued.v (adAt F P (((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)) ≤ 1 := fun r s => by
    rw [adAt_inv hcomp]; exact val_entry_le (inv_mem hg) r s
  refine ⟨(mem_rInt_iff F E _).2 fun Q => ?_, (mem_rInt_iff F E _).2 fun Q => ?_⟩
  · show Valued.v (adAt F Q _) ≤ 1
    by_cases hQ : Formalism.L2.Col.IsOver v Q
    · rcases rll_over_cases hc hv hQ with rfl | rfl
      · exact a1 i j
      · rw [← valued_sigR hc, ← inv_entry hc hu]
        exact a2 j i
    · exact val_away hsup hQ i j
  · show Valued.v (adAt F Q _) ≤ 1
    by_cases hQ : Formalism.L2.Col.IsOver v Q
    · rcases rll_over_cases hc hv hQ with rfl | rfl
      · exact a2 i j
      · rw [← valued_sigR hc, ← inv_entry hc (inv_mem hu), inv_inv]
        exact a1 j i
    · exact val_away hsup' hQ i j

end GlobalTheory.Mem.Col2.AdT.IntSplit

end
