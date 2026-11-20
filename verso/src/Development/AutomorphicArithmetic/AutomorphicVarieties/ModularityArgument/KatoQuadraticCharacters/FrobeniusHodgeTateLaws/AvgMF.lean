import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SerVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMuModelMeasureOfEigenfunctional

open UpperTheory.V.Z.Kato.Joint GlobalTheory.EisM

/- English proof (translation)
Introduce `k l N m θ χ f t α B c hp hk hodd hN hlN hm hχ hf hα hE`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Establish `hsq : ∀ ν : DirichletCharacter ℂ N, ν (-1) * ν (-1) = 1` using `fun ν => by rw [← map_mul]; simp`. Establish `hform : ∀ ν : DirichletCharacter ℂ N, ν (-1) = -θ (-1) → MF k (N * l) (ch (θ⁻¹ * ν)) (frm l N m k θ ν f)` using `fun ν hν => (GlobalTheory.iterU_level_val_stable k N l m (θ⁻¹ * ν) (fun _ => 0) α B c _ (by omega) hp hα (GlobalTheory.T.isModularFormCoeffSeq_eisensteinProduct_parity k N l m (θ⁻¹ * ν) θ ν f hk hodd hN hp hm hlN rfl hν hf)).1`. Establish `hsign : (θ * χ) (-1) = -θ (-1)`.

Rewrite using `[MulChar.coeToFun_mul, Pi.mul_apply, hχ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmain` using `hform (θ * χ) hsign`. Rewrite `hmain` using `[inv_mul_cancel_left]`. Use `⟨hmain, ?_⟩` and prove the remaining obligations.

Establish `hφ : (N.totient : ℂ) ≠ 0` using `by exact_mod_cast (Nat.totient_pos.2 hN).ne'`. Establish `htw : tw2 N (θ (-1)) = fun y => ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) * ch ν y`. Use function extensionality and compare the values at `y`. Rewrite using `[GlobalTheory.T.tw2_eq_inv_totient_mul_sum_characters N (θ (-1)) hN y, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun ν _ => by ring`.

Establish `hmes : mesMu k l (hat θ) (tw2 N (θ (-1))) α B c m f = ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) * ((α ^ m)⁻¹ * lam B c (frm l N m k θ ν f))`. Unfold `mesMu`. Rewrite using `[htw, funext (measMu_zm_sum k l (hat θ) Finset.univ _ _ _), measMu_val_sum]`. Both sides reduce to the same expression. Rewrite using `[hmes, Finset.sum_eq_single_of_mem (θ * χ) (Finset.mem_univ _)]`.

Establish `h2 : (1 : ℂ) - θ (-1) * (θ * χ) (-1) = 2`. Rewrite using `[hsign]`. Take the linear combination `hsq θ`. Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts.

Introduce `ν _ hne`. Establish `h0 : (ν (-1) - θ (-1)) * (ν (-1) + θ (-1)) = 0` using `by linear_combination hsq ν - hsq θ`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Rewrite using `[sub_eq_zero.1 h, hsq θ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hne' : θ⁻¹ * ν ≠ χ` using `fun h' => hne (by rw [← h', mul_inv_cancel_left])`. Rewrite using `[hE.kill _ _ hne' (hform ν (eq_neg_of_add_eq_zero_left h))]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Kato.Joint.avgMF :
    UpperTheory.V.Z.Kato.Joint.AvgMF := by
  intro k l N m θ χ f t α B c hp hk hodd hN hlN hm hχ hf hα hE
  haveI : NeZero N := ⟨hN.ne'⟩
  have hsq : ∀ ν : DirichletCharacter ℂ N, ν (-1) * ν (-1) = 1 := fun ν => by rw [← map_mul]; simp
  have hform : ∀ ν : DirichletCharacter ℂ N, ν (-1) = -θ (-1) → MF k (N * l) (ch (θ⁻¹ * ν)) (frm l N m k θ ν f) :=
    fun ν hν => (GlobalTheory.iterU_level_val_stable k N l m (θ⁻¹ * ν) (fun _ => 0) α B c _ (by omega) hp hα
      (GlobalTheory.T.isModularFormCoeffSeq_eisensteinProduct_parity k N l m (θ⁻¹ * ν) θ ν f hk hodd hN hp hm hlN rfl hν hf)).1
  have hsign : (θ * χ) (-1) = -θ (-1) := by
    rw [MulChar.coeToFun_mul, Pi.mul_apply, hχ]; ring
  have hmain := hform (θ * χ) hsign
  rw [inv_mul_cancel_left] at hmain
  refine ⟨hmain, ?_⟩
  have hφ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hN).ne'
  have htw : tw2 N (θ (-1)) =
      fun y => ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) * ch ν y := by
    funext y
    rw [GlobalTheory.T.tw2_eq_inv_totient_mul_sum_characters N (θ (-1)) hN y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have hmes : mesMu k l (hat θ) (tw2 N (θ (-1))) α B c m f =
      ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) *
        ((α ^ m)⁻¹ * lam B c (frm l N m k θ ν f)) := by
    unfold mesMu
    rw [htw, funext (measMu_zm_sum k l (hat θ) Finset.univ _ _ _), measMu_val_sum]
    rfl
  rw [hmes, Finset.sum_eq_single_of_mem (θ * χ) (Finset.mem_univ _)]
  · have h2 : (1 : ℂ) - θ (-1) * (θ * χ) (-1) = 2 := by
      rw [hsign]; linear_combination hsq θ
    rw [h2]
    field_simp
  · intro ν _ hne
    have h0 : (ν (-1) - θ (-1)) * (ν (-1) + θ (-1)) = 0 := by linear_combination hsq ν - hsq θ
    rcases mul_eq_zero.1 h0 with h | h
    · rw [sub_eq_zero.1 h, hsq θ]; ring
    · have hne' : θ⁻¹ * ν ≠ χ := fun h' => hne (by rw [← h', mul_inv_cancel_left])
      rw [hE.kill _ _ hne' (hform ν (eq_neg_of_add_eq_zero_left h))]
      ring
