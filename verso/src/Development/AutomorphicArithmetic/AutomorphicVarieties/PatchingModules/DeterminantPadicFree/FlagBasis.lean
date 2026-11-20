import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FlagFDiagonalise
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExistsIntegralBlockIwasawaDecomposition

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hA h, zero_mul]`. Rewrite using `[hB h, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
private theorem flagBasis_diag_mul {F : Type} [Field F] {n : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Establish `hbm : (b : Matrix (Fin n) (Fin n) F).BlockTriangular id` using `fun i j h => hb i j h`. Establish `htm : (t : Matrix (Fin n) (Fin n) F).BlockTriangular id` using `fun i j h => ht i j h`. Establish `hbi : ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id`. Use `letI := b.invertible`. Rewrite using `[Matrix.coe_units_inv]`.

Conclude with `blockTriangular_inv_of_blockTriangular hbm`. Establish `hdiag : ∀ i, ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i * (b : Matrix (Fin n) (Fin n) F) i i = 1`. Introduce `i`. Rewrite using `[← flagBasis_diag_mul hbi hbm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, Units.val_mul]`. Conclude with `((hbi.mul htm).mul hbm) hij`. Rewrite using `[Units.val_mul, Units.val_mul, flagBasis_diag_mul (hbi.mul htm) hbm, flagBasis_diag_mul hbi htm, mul_right_comm, hdiag, one_mul]`.
-/
private theorem flagBasis_conj {F : Type} [Field F] {n : ℕ} (b t : GL (Fin n) F)
    (hb : ∀ i j, j < i → b i j = 0) (ht : ∀ i j, j < i → t i j = 0) :
    (∀ i j, j < i → (b⁻¹ * t * b : GL (Fin n) F) i j = 0) ∧
      ∀ i, (b⁻¹ * t * b : GL (Fin n) F) i i = t i i := by
  have hbm : (b : Matrix (Fin n) (Fin n) F).BlockTriangular id := fun i j h => hb i j h
  have htm : (t : Matrix (Fin n) (Fin n) F).BlockTriangular id := fun i j h => ht i j h
  have hbi : ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id := by
    letI := b.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hbm
  have hdiag : ∀ i, ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i *
      (b : Matrix (Fin n) (Fin n) F) i i = 1 := by
    intro i
    rw [← flagBasis_diag_mul hbi hbm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact ((hbi.mul htm).mul hbm) hij
  · rw [Units.val_mul, Units.val_mul, flagBasis_diag_mul (hbi.mul htm) hbm,
      flagBasis_diag_mul hbi htm, mul_right_comm, hdiag, one_mul]

/- English proof (translation)
Introduce `K H _ _ n a r ψ hev hinj hflag`. Use `set ι := algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) with hι`. Establish `hιi : Function.Injective ι` using `IsFractionRing.injective _ _`. Use `haveI : Infinite (FractionRing (PowerSeries K)) := by`. Use `Infinite.of_injective (fun m : ℕ => ι (PowerSeries.X ^ m)) ?_` and prove the remaining obligations.

Introduce `m k hmk`. Establish `h` using `congrArg (fun p => PowerSeries.coeff (R := K) m p) (hιi hmk)`. Simplify using `only [PowerSeries.coeff_X_pow, if_true] at h`. Assume the negation of the conclusion as `hne`. Rewrite `h` using `[if_neg hne]`.

Conclude with `one_ne_zero h`. Establish `hev' : ∀ g, mat (pushRep ι r) g ∈ Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a`. Introduce `g`. Establish `hg` using `hev g`. Introduce `i j`.

Use `⟨fun _ => Submodule.mem_top, fun h => ?_⟩` and prove the remaining obligations. Establish `h0` using `(Submodule.mem_bot _).1 ((hg i j).2 h)`. Establish `e : mat (pushRep ι r) g i j = ι (mat r g i j)` using `rfl`. Rewrite using `[e, h0, map_zero]`. Conclude with `Submodule.zero_mem _`.

Establish `hψ : Function.Injective (fun i => pushCh ι (ψ i))`. Introduce `i j hij`. Apply `hinj` to reduce the goal to its premises. Use extensionality with `g`. Use `congrArg (fun f : H →* (FractionRing (PowerSeries K))ˣ => ((f g : (FractionRing (PowerSeries K))ˣ) : FractionRing (PowerSeries K))) hij` as an intermediate fact.

Rewrite using `[hιi this]`. Take `⟨w0, ty, hw0, htri⟩` from `Det.flagF (pushRep ι r) (fun i => pushCh ι (ψ i)) hev' hψ hflag`. Take `⟨w, b, hb, hwb, hw⟩` from `Det.exists_integral_block_iwasawa_decomposition (A := PowerSeries K) (fun i : Fin n => decide ((i : ℕ) < a)) ty w0 hw0`. Use `⟨w, ty, hw, fun g => ?_⟩` and prove the remaining obligations. Establish `hmap : GeneralLinearGroup.map ι (w⁻¹ * r g * w) = b⁻¹ * (w0⁻¹ * pushRep ι r g * w0) * b`.

Rewrite using `[map_mul, map_mul, map_inv, hwb, _root_.mul_inv_rev]`. Simplify using `only [pushRep, MonoidHom.comp_apply, mul_assoc]`. Establish `hent : ∀ i j, ι ((w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i j) = (b⁻¹ * (w0⁻¹ * pushRep ι r g * w0) * b : GL (Fin n) (FractionRing (PowerSeries K))) i j`. Introduce `i j`. Rewrite using `[← hmap]`.

Both sides reduce to the same expression. Take `⟨hc1, hc2⟩` from `flagBasis_conj b (w0⁻¹ * pushRep ι r g * w0) hb (htri g).1`. Use `⟨fun i j hij => hιi ?_, fun i => hιi ?_⟩` and prove the remaining obligations. Rewrite using `[hent, hc1 i j hij, map_zero]`. Rewrite using `[hent, hc2 i, (htri g).2 i]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Pa.Det.flagBasis :
    ∀ {K H : Type} [Field K] [Group H] {n a : ℕ} (r : H →* GL (Fin n) (PowerSeries K)) (ψ : Fin n → H →* (PowerSeries K)ˣ), (∀ g, mat r g ∈ Ev (PowerSeries K) (PowerSeries K) n a) → Function.Injective ψ → HasFlag (pushRep (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) r) (fun i => pushCh (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) (ψ i)) → ∃ (w : GL (Fin n) (PowerSeries K)) (ty : Fin n → Bool), (∀ i j : Fin n, decide ((i : ℕ) < a) ≠ ty j → w i j = 0) ∧ ∀ g, (∀ i j, j < i → (w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i j = 0) ∧ ∀ i, (w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i i = (ψ i g : PowerSeries K) := by
  intro K H _ _ n a r ψ hev hinj hflag
  set ι := algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) with hι
  have hιi : Function.Injective ι := IsFractionRing.injective _ _
  haveI : Infinite (FractionRing (PowerSeries K)) := by
    refine Infinite.of_injective (fun m : ℕ => ι (PowerSeries.X ^ m)) ?_
    intro m k hmk
    have h := congrArg (fun p => PowerSeries.coeff (R := K) m p) (hιi hmk)
    simp only [PowerSeries.coeff_X_pow, if_true] at h
    by_contra hne
    rw [if_neg hne] at h
    exact one_ne_zero h
  have hev' : ∀ g, mat (pushRep ι r) g ∈ Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a := by
    intro g
    have hg := hev g
    intro i j
    refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
    have h0 := (Submodule.mem_bot _).1 ((hg i j).2 h)
    have e : mat (pushRep ι r) g i j = ι (mat r g i j) := rfl
    rw [e, h0, map_zero]
    exact Submodule.zero_mem _
  have hψ : Function.Injective (fun i => pushCh ι (ψ i)) := by
    intro i j hij
    apply hinj
    ext g
    have := congrArg (fun f : H →* (FractionRing (PowerSeries K))ˣ => ((f g : (FractionRing (PowerSeries K))ˣ) : FractionRing (PowerSeries K))) hij
    rw [hιi this]
  obtain ⟨w0, ty, hw0, htri⟩ := Det.flagF (pushRep ι r) (fun i => pushCh ι (ψ i)) hev' hψ hflag
  obtain ⟨w, b, hb, hwb, hw⟩ :=
    Det.exists_integral_block_iwasawa_decomposition (A := PowerSeries K) (fun i : Fin n => decide ((i : ℕ) < a)) ty w0 hw0
  refine ⟨w, ty, hw, fun g => ?_⟩
  have hmap : GeneralLinearGroup.map ι (w⁻¹ * r g * w) = b⁻¹ * (w0⁻¹ * pushRep ι r g * w0) * b := by
    rw [map_mul, map_mul, map_inv, hwb, _root_.mul_inv_rev]
    simp only [pushRep, MonoidHom.comp_apply, mul_assoc]
  have hent : ∀ i j, ι ((w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i j) =
      (b⁻¹ * (w0⁻¹ * pushRep ι r g * w0) * b : GL (Fin n) (FractionRing (PowerSeries K))) i j := by
    intro i j
    rw [← hmap]
    rfl
  obtain ⟨hc1, hc2⟩ := flagBasis_conj b (w0⁻¹ * pushRep ι r g * w0) hb (htri g).1
  refine ⟨fun i j hij => hιi ?_, fun i => hιi ?_⟩
  · rw [hent, hc1 i j hij, map_zero]
  · rw [hent, hc2 i, (htri g).2 i]
    rfl
