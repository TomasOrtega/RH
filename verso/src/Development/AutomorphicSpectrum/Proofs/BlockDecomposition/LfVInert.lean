import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrInertOfUnramified

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.InertFactor

/- English proof (translation)
Rewrite using `[← mul_inv]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inv_factor (a b Q : ℂ) :
    (1 - a ^ 2 * b ^ 2 * Q ^ 2)⁻¹ = (1 - a * b * Q)⁻¹ * (1 - a * (-b) * Q)⁻¹ := by
  rw [← mul_inv]
  congr 1
  ring

/- English proof (translation)
Rewrite using `[pow_two, pow_two, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]`.
-/
theorem cpow_sq (q : ℕ) (s : ℂ) : (((q ^ 2 : ℕ) : ℂ)) ^ (-s) = ((q : ℂ) ^ (-s)) ^ 2 := by
  rw [pow_two, pow_two, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

section Loc

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

/- English proof (translation)
The claim follows from `isUnramifiedChar_iff.mpr fun u hu => by rw [MonoidHom.mul_apply, isUnramifiedChar_iff.mp h u hu, isUnramifiedChar_iff.mp h' u hu, one_mul]`.
-/
theorem unr_mul {μ μ' : Eˣ →* ℂˣ} (h : IsUnramifiedChar μ) (h' : IsUnramifiedChar μ') :
    IsUnramifiedChar (μ * μ') :=
  isUnramifiedChar_iff.mpr fun u hu => by
    rw [MonoidHom.mul_apply, isUnramifiedChar_iff.mp h u hu, isUnramifiedChar_iff.mp h' u hu, one_mul]

/- English proof (translation)
The claim follows from `isUnramifiedChar_iff.mpr fun u hu => by rw [MonoidHom.inv_apply, isUnramifiedChar_iff.mp h u hu, inv_one]`.
-/
theorem unr_inv {μ : Eˣ →* ℂˣ} (h : IsUnramifiedChar μ) : IsUnramifiedChar μ⁻¹ :=
  isUnramifiedChar_iff.mpr fun u hu => by
    rw [MonoidHom.inv_apply, isUnramifiedChar_iff.mp h u hu, inv_one]

/- English proof (translation)
Unfold `lf3`. Rewrite using `[localLFactor_of_isUnramified (unr_mul hν hχ), localLFactor_of_isUnramified hχ, localLFactor_of_isUnramified (unr_mul (unr_inv hν) hχ), hq, cpow_sq]`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, Fin.prod_univ_three, Fin.prod_univ_two]`. Establish `e1` using `inv_factor (A : ℂ) (B : ℂ) ((q : ℂ) ^ (-s))`. Establish `e2` using `inv_factor (1 : ℂ) (B : ℂ) ((q : ℂ) ^ (-s))`.

Establish `e3` using `inv_factor ((A : ℂ)⁻¹) (B : ℂ) ((q : ℂ) ^ (-s))`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_neg, Units.val_one, inv_pow, one_pow, one_mul] at e1 e2 e3 ⊢`. Rewrite using `[e1, e2, e3]`.
-/
theorem local_l_factor_rank_three_unramified (ν χ : Eˣ →* ℂˣ) (hν : IsUnramifiedChar ν) (hχ : IsUnramifiedChar χ) (A B : ℂˣ)
    (h1 : ν (unifUnit E) = A ^ 2) (h2 : χ (unifUnit E) = B ^ 2) (q : ℕ)
    (hq : residueCard E = q ^ 2) (s : ℂ) :
    lf3 ν χ s = ∏ i : Fin 3, ∏ j : Fin 2,
      (1 - ((![A, 1, A⁻¹] : Fin 3 → ℂˣ) i : ℂ) * (((![B, -B] : Fin 2 → ℂˣ) j : ℂˣ) : ℂ) *
        (q : ℂ) ^ (-s))⁻¹ := by
  unfold lf3
  rw [localLFactor_of_isUnramified (unr_mul hν hχ), localLFactor_of_isUnramified hχ,
    localLFactor_of_isUnramified (unr_mul (unr_inv hν) hχ), hq, cpow_sq]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, Fin.prod_univ_three,
    Fin.prod_univ_two]
  have e1 := inv_factor (A : ℂ) (B : ℂ) ((q : ℂ) ^ (-s))
  have e2 := inv_factor (1 : ℂ) (B : ℂ) ((q : ℂ) ^ (-s))
  have e3 := inv_factor ((A : ℂ)⁻¹) (B : ℂ) ((q : ℂ) ^ (-s))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val, Units.val_neg, Units.val_one, inv_pow, one_pow, one_mul] at e1 e2 e3 ⊢
  rw [e1, e2, e3]

end Loc

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Use `GroundTheory.Automorphic.GodementSection.localChar_mul_inv c c w` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, mul_inv_cancel]`. Then use the resulting hypothesis.
-/
theorem localChar_one (c : HeckeCharacter K) (w : PlK K) : localChar (1 : HeckeCharacter K) w = 1 := by
  have := GroundTheory.Automorphic.GodementSection.localChar_mul_inv c c w
  rwa [mul_inv_cancel, mul_inv_cancel] at this

/- English proof (translation)
Use `GroundTheory.Automorphic.GodementSection.localChar_mul_inv 1 c w` as an intermediate fact. Rewrite `this` using `[one_mul, localChar_one c, one_mul]`. Then use the resulting hypothesis.
-/
theorem localChar_inv (c : HeckeCharacter K) (w : PlK K) : localChar c⁻¹ w = (localChar c w)⁻¹ := by
  have := GroundTheory.Automorphic.GodementSection.localChar_mul_inv 1 c w
  rwa [one_mul, localChar_one c, one_mul] at this

/- English proof (translation)
Rewrite using `[Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal]`.
-/
theorem absNorm_over (v : Pl) (w : PlK K) [hw : w.asIdeal.LiesOver v.asIdeal] :
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ w.asIdeal.inertiaDeg (𝓞 ℚ) := by
  rw [Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal]

/- English proof (translation)
Introduce `K _ _ h2 D DK hBC c v hv hun w _ huniq`. Break down `GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K h2 v (fun w' _ => (hun w').2) with ⟨w₁, w₂, h₁, h₂, hne⟩ | ⟨w', hw', -, hfin, hord⟩` into its components or cases. Conclude with `absurd ((huniq w₁ h₁).trans (huniq w₂ h₂).symm) hne`. Take `rfl` from `huniq w' hw'`. Establish `hf : w'.asIdeal.inertiaDeg (𝓞 ℚ) = 2`.

Establish `h` using `finrank_adicCompletion v w'`. Rewrite `h` using `[hfin, (hun w').2, one_mul]`. Conclude with `h.symm`. Establish `hq : residueCard (Kv K w') = residueCard (Qv v) ^ 2`. Rewrite using `[residueCard_adicCompletion, residueCard_adicCompletion, absNorm_over v w', hf]`.

Use `⟨hfin, hq, fun b hb s => ?_⟩` and prove the remaining obligations. Use `set π : (Kv K w')ˣ := Units.map (algebraMap (Qv v) (Kv K w')).toMonoidHom (unifUnit (Qv v)) with hπdef`. Establish `hπ : ord ((π : (Kv K w')ˣ) : Kv K w') = 1` using `hord`. Establish `hχu` using `(hun w').1`. Establish `hνu : IsUnramifiedChar (DK.ν w')` using `DK.unr w' fun hbad => by`.

Break down `(hBC.bad v w').mp hbad with h | h` into its components or cases. Conclude with `hv h`. Conclude with `h (hun w').2`. Establish `hχ : localChar c w' (unifUnit (Kv K w')) = b ^ 2`. Rewrite using `[← quasiChar_apply_eq_of_isUnramified hχu hπ, hb]`.

Establish `hnorm : nrm v w' π = unifUnit (Qv v) ^ 2`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[nrm, π, Algebra.norm_algebraMap, hfin]`. Establish `hν : DK.ν w' (unifUnit (Kv K w')) = D.ν v (unifUnit (Qv v)) ^ 2`. Rewrite using `[← quasiChar_apply_eq_of_isUnramified hνu hπ, hBC.nu v w', MonoidHom.comp_apply, hnorm, map_pow]`.

Establish `hfib : GlobalTheory.CompanionTheory.PlaceBlocks.fib K v = {w'}`. Use extensionality with `x`. Rewrite using `[GlobalTheory.CompanionTheory.PlaceBlocks.mem_fib, Finset.mem_singleton, ← GlobalTheory.CompanionTheory.PlaceBlocks.liesOver_iff]`. Conclude with `⟨huniq x, fun h => h ▸ hw'⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.CompanionTheory.PlaceBlocks.lfV_eq, hfib, Finset.prod_singleton]`. Conclude with `local_l_factor_rank_three_unramified _ _ hνu hχu _ _ hν hχ _ hq s`. Rewrite using `[GlobalTheory.CompanionTheory.PlaceBlocks.lfV_eq, hfib, Finset.prod_singleton, localChar_inv]`. Rewrite using `[local_l_factor_rank_three_unramified (DK.ν w') (localChar c w')⁻¹ hνu (unr_inv hχu) (D.ν v (unifUnit (Qv v))) b⁻¹ hν (by rw [MonoidHom.inv_apply, hχ, inv_pow]) _ hq s]`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `fin_cases j <;> simp`.
-/
theorem lfV_inert : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (D : Dat) (DK : DatK K), IsBC D DK → ∀ (c : HeckeCharacter K) (v : Pl), v ∉ D.bad → (∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], IsUnramifiedChar (localChar c w) ∧ w.asIdeal.ramificationIdx (𝓞 ℚ) = 1) → ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], (∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) → Module.finrank (Qv v) (Kv K w) = 2 ∧ residueCard (Kv K w) = residueCard (Qv v) ^ 2 ∧ ∀ b : ℂˣ, b ^ 2 = localChar c w (Units.map (algebraMap (Qv v) (Kv K w)).toMonoidHom (unifUnit (Qv v))) → ∀ s : ℂ, lfV DK c v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * (((![b, -b] : Fin 2 → ℂˣ) j : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ ∧ lfV DK c⁻¹ v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * ((((![b, -b] : Fin 2 → ℂˣ) j)⁻¹ : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ := by
  intro K _ _ h2 D DK hBC c v hv hun w _ huniq
  rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K h2 v (fun w' _ => (hun w').2) with
    ⟨w₁, w₂, h₁, h₂, hne⟩ | ⟨w', hw', -, hfin, hord⟩
  · exact absurd ((huniq w₁ h₁).trans (huniq w₂ h₂).symm) hne
  obtain rfl := huniq w' hw'
  have hf : w'.asIdeal.inertiaDeg (𝓞 ℚ) = 2 := by
    have h := finrank_adicCompletion v w'
    rw [hfin, (hun w').2, one_mul] at h
    exact h.symm
  have hq : residueCard (Kv K w') = residueCard (Qv v) ^ 2 := by
    rw [residueCard_adicCompletion, residueCard_adicCompletion, absNorm_over v w', hf]
  refine ⟨hfin, hq, fun b hb s => ?_⟩
  set π : (Kv K w')ˣ := Units.map (algebraMap (Qv v) (Kv K w')).toMonoidHom (unifUnit (Qv v)) with hπdef
  have hπ : ord ((π : (Kv K w')ˣ) : Kv K w') = 1 := hord
  have hχu := (hun w').1
  have hνu : IsUnramifiedChar (DK.ν w') := DK.unr w' fun hbad => by
    rcases (hBC.bad v w').mp hbad with h | h
    · exact hv h
    · exact h (hun w').2
  have hχ : localChar c w' (unifUnit (Kv K w')) = b ^ 2 := by
    rw [← quasiChar_apply_eq_of_isUnramified hχu hπ, hb]
  have hnorm : nrm v w' π = unifUnit (Qv v) ^ 2 := by
    apply Units.ext
    simp [nrm, π, Algebra.norm_algebraMap, hfin]
  have hν : DK.ν w' (unifUnit (Kv K w')) = D.ν v (unifUnit (Qv v)) ^ 2 := by
    rw [← quasiChar_apply_eq_of_isUnramified hνu hπ, hBC.nu v w', MonoidHom.comp_apply, hnorm, map_pow]
  have hfib : GlobalTheory.CompanionTheory.PlaceBlocks.fib K v = {w'} := by
    ext x
    rw [GlobalTheory.CompanionTheory.PlaceBlocks.mem_fib, Finset.mem_singleton, ← GlobalTheory.CompanionTheory.PlaceBlocks.liesOver_iff]
    exact ⟨huniq x, fun h => h ▸ hw'⟩
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.PlaceBlocks.lfV_eq, hfib, Finset.prod_singleton]
    exact local_l_factor_rank_three_unramified _ _ hνu hχu _ _ hν hχ _ hq s
  · rw [GlobalTheory.CompanionTheory.PlaceBlocks.lfV_eq, hfib, Finset.prod_singleton, localChar_inv]
    rw [local_l_factor_rank_three_unramified (DK.ν w') (localChar c w')⁻¹ hνu (unr_inv hχu) (D.ν v (unifUnit (Qv v))) b⁻¹ hν
      (by rw [MonoidHom.inv_apply, hχ, inv_pow]) _ hq s]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    fin_cases j <;> simp

end GlobalTheory.CompanionTheory.InertFactor
