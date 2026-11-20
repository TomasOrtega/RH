import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `A F _ _ _ _ _ _ n bl ty g hg`. Take `⟨k, b0, hb0, hgkb⟩` from `GlobalTheory.ValIwasawa.iwasawa A F n g`. Use `haveI : Invertible (b0 : Matrix (Fin n) (Fin n) F) := Units.invertible b0`. Establish `hctri : ((b0 : Matrix (Fin n) (Fin n) F)⁻¹).BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hb0`. Use `set c : Matrix (Fin n) (Fin n) F := (b0 : Matrix (Fin n) (Fin n) F)⁻¹ with hcdef`.

Establish `hgc : (g : Matrix (Fin n) (Fin n) F) * c = (GeneralLinearGroup.map (algebraMap A F) k : Matrix (Fin n) (Fin n) F)`. Establish `h1 : g * b0⁻¹ = GeneralLinearGroup.map (algebraMap A F) k` using `mul_inv_eq_iff_eq_mul.mpr hgkb`. Establish `h2` using `congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) h1`. Simplify `h2` using `[Units.val_mul, Matrix.coe_units_inv, hcdef]`. Set `c' : Matrix (Fin n) (Fin n) F` to `Matrix.of fun i j => if ty i = ty j then c i j else 0`.

Establish `hc'tri : c'.BlockTriangular id`. Introduce `i j hij`. Simplify using `only [c', Matrix.of_apply]`. Use `split_ifs`. Conclude with `hctri hij`.

Both sides reduce to the same expression. Establish `hgc' : ∀ i j, ((g : Matrix (Fin n) (Fin n) F) * c') i j = if bl i = ty j then algebraMap A F ((k : Matrix (Fin n) (Fin n) A) i j) else 0`. Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Use `split_ifs with hij`.

Rewrite using `[← GeneralLinearGroup.map_apply, ← hgc, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [c', Matrix.of_apply]`. Use `split_ifs with hl`. Both sides reduce to the same expression.

Rewrite using `[hg i l (fun h => hl (h.symm.trans hij)), zero_mul, zero_mul]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Simplify using `only [c', Matrix.of_apply]`. Use `split_ifs with hl`. Rewrite using `[hg i l (fun h => hij (h.trans hl)), zero_mul]`.

Rewrite using `[mul_zero]`. Set `kw : Matrix (Fin n) (Fin n) A` to `Matrix.of fun i j => if bl i = ty j then (k : Matrix (Fin n) (Fin n) A) i j else 0`. Establish `hmap : (algebraMap A F).mapMatrix kw = (g : Matrix (Fin n) (Fin n) F) * c'`. Use extensionality with `i j`. Rewrite using `[hgc' i j]`.

Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, kw, Matrix.of_apply]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `map_zero _`. Establish `hdetc : c'.det = c.det`.

Rewrite using `[Matrix.det_of_upperTriangular hc'tri, Matrix.det_of_upperTriangular hctri]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[c']`. Establish `hcunit : IsUnit c.det`. Use `Matrix.isUnits_det_units b0⁻¹` as an intermediate fact.

Rewrite `this` using `[Matrix.coe_units_inv]`. Then use the resulting hypothesis. Establish `hc'unit : IsUnit c'.det` using `hdetc ▸ hcunit`. Establish `hdetk : kw.det = (k : Matrix (Fin n) (Fin n) A).det`. Apply `IsFractionRing.injective A F` to reduce the goal to its premises. Rewrite using `[RingHom.map_det, RingHom.map_det, hmap, Matrix.det_mul, hdetc, ← Matrix.det_mul, hgc]`.

Both sides reduce to the same expression. Establish `hkunit : IsUnit kw.det` using `hdetk ▸ Matrix.isUnits_det_units k`. Use `⟨GeneralLinearGroup.mk'' kw hkunit, GeneralLinearGroup.mk'' c' hc'unit, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Conclude with `hc'tri hij`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul]`. Conclude with `hmap`. Introduce `i j hij show kw i j = 0`. Simplify using `[kw, hij]`.
-/
theorem UpperTheory.V.Pa.Det.exists_integral_block_iwasawa_decomposition :
    ∀ {A F : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F] [Algebra A F] [IsFractionRing A F] {n : ℕ} (bl ty : Fin n → Bool) (g : GL (Fin n) F), (∀ i j, bl i ≠ ty j → g i j = 0) → ∃ (w : GL (Fin n) A) (b : GL (Fin n) F), (∀ i j, j < i → b i j = 0) ∧ GeneralLinearGroup.map (algebraMap A F) w = g * b ∧ ∀ i j, bl i ≠ ty j → w i j = 0 := by
  intro A F _ _ _ _ _ _ n bl ty g hg
  obtain ⟨k, b0, hb0, hgkb⟩ := GlobalTheory.ValIwasawa.iwasawa A F n g
  haveI : Invertible (b0 : Matrix (Fin n) (Fin n) F) := Units.invertible b0
  have hctri : ((b0 : Matrix (Fin n) (Fin n) F)⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular hb0
  set c : Matrix (Fin n) (Fin n) F := (b0 : Matrix (Fin n) (Fin n) F)⁻¹ with hcdef
  have hgc : (g : Matrix (Fin n) (Fin n) F) * c = (GeneralLinearGroup.map (algebraMap A F) k : Matrix (Fin n) (Fin n) F) := by
    have h1 : g * b0⁻¹ = GeneralLinearGroup.map (algebraMap A F) k := mul_inv_eq_iff_eq_mul.mpr hgkb
    have h2 := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) h1
    simpa [Units.val_mul, Matrix.coe_units_inv, hcdef] using h2
  let c' : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => if ty i = ty j then c i j else 0
  have hc'tri : c'.BlockTriangular id := by
    intro i j hij
    simp only [c', Matrix.of_apply]
    split_ifs
    · exact hctri hij
    · rfl
  have hgc' : ∀ i j, ((g : Matrix (Fin n) (Fin n) F) * c') i j = if bl i = ty j then algebraMap A F ((k : Matrix (Fin n) (Fin n) A) i j) else 0 := by
    intro i j
    rw [Matrix.mul_apply]
    split_ifs with hij
    · rw [← GeneralLinearGroup.map_apply, ← hgc, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [c', Matrix.of_apply]
      split_ifs with hl
      · rfl
      · rw [hg i l (fun h => hl (h.symm.trans hij)), zero_mul, zero_mul]
    · refine Finset.sum_eq_zero fun l _ => ?_
      simp only [c', Matrix.of_apply]
      split_ifs with hl
      · rw [hg i l (fun h => hij (h.trans hl)), zero_mul]
      · rw [mul_zero]
  let kw : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => if bl i = ty j then (k : Matrix (Fin n) (Fin n) A) i j else 0
  have hmap : (algebraMap A F).mapMatrix kw = (g : Matrix (Fin n) (Fin n) F) * c' := by
    ext i j
    rw [hgc' i j]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, kw, Matrix.of_apply]
    split_ifs
    · rfl
    · exact map_zero _
  have hdetc : c'.det = c.det := by
    rw [Matrix.det_of_upperTriangular hc'tri, Matrix.det_of_upperTriangular hctri]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [c']
  have hcunit : IsUnit c.det := by
    have := Matrix.isUnits_det_units b0⁻¹
    rwa [Matrix.coe_units_inv] at this
  have hc'unit : IsUnit c'.det := hdetc ▸ hcunit
  have hdetk : kw.det = (k : Matrix (Fin n) (Fin n) A).det := by
    apply IsFractionRing.injective A F
    rw [RingHom.map_det, RingHom.map_det, hmap, Matrix.det_mul, hdetc, ← Matrix.det_mul, hgc]
    rfl
  have hkunit : IsUnit kw.det := hdetk ▸ Matrix.isUnits_det_units k
  refine ⟨GeneralLinearGroup.mk'' kw hkunit, GeneralLinearGroup.mk'' c' hc'unit, ?_, ?_, ?_⟩
  · intro i j hij
    exact hc'tri hij
  · apply Units.ext
    rw [Units.val_mul]
    exact hmap
  · intro i j hij
    show kw i j = 0
    simp [kw, hij]
