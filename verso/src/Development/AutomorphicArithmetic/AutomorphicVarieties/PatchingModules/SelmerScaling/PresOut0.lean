import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `O B _ _ _ _ _ _ _ D0 X hX hspan Z Q hZ hQ hdim`. Use `haveI hOO : IsCO O O := { complete := inferInstance isLocalHom := ⟨fun a h => by simpa using h⟩ res_surj := fun x => ⟨x, by simp⟩ }`. Use `haveI hA : IsCO O (MvPowerSeries (Fin D0) O) := co_mvps O O (Fin D0)`. Take `⟨F, ⟨hFC, hFX⟩, -⟩` from `co_ev O O B (Fin D0) (Algebra.ofId O B) X hX`. Establish `hsurj : Function.Surjective F`.

Apply `co_surj` to reduce the goal to its premises. Use `le_trans hspan (sup_le ?_ (sup_le ?_ le_sup_right))` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `Ideal.mem_sup_left ?_` and prove the remaining obligations.

Rewrite using `[← hFX i]`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]`. Simplify using the standard rewrite rules. Use `le_sup_of_le_left ?_` and prove the remaining obligations.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap]`. Establish `h1 : algebraMap O B a = F (MvPowerSeries.C a)`. Rewrite using `[hFC]`.

Both sides reduce to the same expression. Rewrite using `[h1]`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]`. Simplify using `using ha`.

Establish `hdimA : ringKrullDim (MvPowerSeries (Fin D0) O) = 1 + (D0 : WithBot ℕ∞)`. Rewrite using `[GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]`. Simplify using the standard rewrite rules. Establish `hinj : ∀ r, F r ∈ Z → r = 0`. Introduce `r hr`.

Assume the negation of the conclusion as `hne`. Establish `hnz : r ∈ nonZeroDivisors (MvPowerSeries (Fin D0) O)` using `mem_nonZeroDivisors_of_ne_zero hne`. Establish `hle` using `ringKrullDim_succ_le_of_surjective ((Ideal.Quotient.mk Z).comp F.toRingHom) ((Ideal.Quotient.mk_surjective).comp hsurj) hnz (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hr)`. Rewrite `hle` using `[hdimA]`. Generalize the expression as in `ringKrullDim (B ⧸ Z) = d at hle hdim`.

Establish `hb : d ≠ ⊥` using `ne_bot_of_le_ne_bot (WithBot.coe_ne_bot) hdim`. Take `⟨e, rfl⟩` from `WithBot.ne_bot_iff_exists.mp hb`. Establish `h2 : (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (e : WithBot ℕ∞)` using `hdim`. Rewrite `h2` using `[WithBot.coe_le_coe]`. Establish `h1 : ((e + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞)`.

Move the coercions through the operations in `at hle ⊢`. Conclude with `hle`. Rewrite `h1` using `[WithBot.coe_le_coe]`. Establish `het : e ≠ ⊤`. Introduce `h`.

Rewrite `h1` using `[h]`. Simplify using `at h1`. Use `lift e to ℕ using het`. Normalize the coercions in `at h1 h2`. Use linear arithmetic over natural numbers and integers.

Establish `hZbot : Z = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `z hz`. Take `⟨r, rfl⟩` from `hsurj z`. Rewrite using `[hinj r hz, map_zero]`.

Conclude with `Ideal.zero_mem _`. Rewrite using `[hZbot]`. Conclude with `bot_le`.
-/
theorem UpperTheory.V.Pa.presOut0 :
    ∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing B] [Algebra O B] [IsCO O B] (D0 : ℕ) (X : Fin D0 → B), (∀ a, X a ∈ maximalIdeal B) → maximalIdeal B ≤ Ideal.span (Set.range X) ⊔ ((maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2) → ∀ Z Q : Ideal B, Z.IsPrime → Q.IsPrime → ((1 + D0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Z) → Z ≤ Q := by
  intro O B _ _ _ _ _ _ _ D0 X hX hspan Z Q hZ hQ hdim
  haveI hOO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun a h => by simpa using h⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hA : IsCO O (MvPowerSeries (Fin D0) O) := co_mvps O O (Fin D0)
  obtain ⟨F, ⟨hFC, hFX⟩, -⟩ := co_ev O O B (Fin D0) (Algebra.ofId O B) X hX
  have hsurj : Function.Surjective F := by
    apply co_surj
    refine le_trans hspan (sup_le ?_ (sup_le ?_ le_sup_right))
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Ideal.mem_sup_left ?_
      rw [← hFX i]
      refine Ideal.mem_map_of_mem _ ?_
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
      simp
    · refine le_sup_of_le_left ?_
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have h1 : algebraMap O B a = F (MvPowerSeries.C a) := by
        rw [hFC]; rfl
      rw [h1]
      refine Ideal.mem_map_of_mem _ ?_
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
      simpa using ha
  have hdimA : ringKrullDim (MvPowerSeries (Fin D0) O) = 1 + (D0 : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp
  have hinj : ∀ r, F r ∈ Z → r = 0 := by
    intro r hr
    by_contra hne
    have hnz : r ∈ nonZeroDivisors (MvPowerSeries (Fin D0) O) := mem_nonZeroDivisors_of_ne_zero hne
    have hle := ringKrullDim_succ_le_of_surjective ((Ideal.Quotient.mk Z).comp F.toRingHom)
      ((Ideal.Quotient.mk_surjective).comp hsurj) hnz (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hr)
    rw [hdimA] at hle
    generalize ringKrullDim (B ⧸ Z) = d at hle hdim
    have hb : d ≠ ⊥ := ne_bot_of_le_ne_bot (WithBot.coe_ne_bot) hdim
    obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hb
    have h2 : (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) := hdim
    rw [WithBot.coe_le_coe] at h2
    have h1 : ((e + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      push_cast at hle ⊢; exact hle
    rw [WithBot.coe_le_coe] at h1
    have het : e ≠ ⊤ := by
      intro h; rw [h] at h1; simp at h1
    lift e to ℕ using het
    norm_cast at h1 h2
    omega
  have hZbot : Z = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨r, rfl⟩ := hsurj z
    rw [hinj r hz, map_zero]
    exact Ideal.zero_mem _
  rw [hZbot]
  exact bot_le
