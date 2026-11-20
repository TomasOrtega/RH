import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.FrameDeco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in

/- English proof (translation)
Take `⟨a, p, hp, h⟩` from `P.isMaximal.exists_inv hs`. Conclude with `⟨a, p, hp, h⟩`.
-/
theorem exists_inv_mod (P : HeightOneSpectrum (𝓞 E)) {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    ∃ a p : 𝓞 E, p ∈ P.asIdeal ∧ a * s + p = 1 := by
  obtain ⟨a, p, hp, h⟩ := P.isMaximal.exists_inv hs
  exact ⟨a, p, hp, h⟩

/- English proof (translation)
Rewrite using `[Submodule.smul_le]`. Introduce `r hr x hx`. Take `⟨t, ht, htx⟩` from `(mem_locP P N x).1 hx`. Use `(mem_locP P _ _).2 ⟨t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`.

Conclude with `Submodule.smul_mem_smul hr htx`.
-/
theorem smul_localizationAt_le (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) :
    P.asIdeal • localization₂ P.asIdeal N ≤ localization₂ P.asIdeal (P.asIdeal • N) := by
  rw [Submodule.smul_le]
  intro r hr x hx
  obtain ⟨t, ht, htx⟩ := (mem_locP P N x).1 hx
  refine (mem_locP P _ _).2 ⟨t, ht, ?_⟩
  rw [smul_comm]
  exact Submodule.smul_mem_smul hr htx

/- English proof (translation)
Take `⟨t, ht, hty⟩` from `(mem_locP P _ _).1 h`. Take `⟨a, p, hp, e⟩` from `exists_inv_mod P ht`. Establish `: y = a • (t • y) + p • y`. Rewrite using `[smul_smul, ← add_smul, e, one_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ hty) (Submodule.smul_mem_smul hp hy)`.
-/
theorem mem_smul_of_mem_locP (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    {y : Sp E n} (hy : y ∈ N) (h : y ∈ localization₂ P.asIdeal (P.asIdeal • N)) : y ∈ P.asIdeal • N := by
  obtain ⟨t, ht, hty⟩ := (mem_locP P _ _).1 h
  obtain ⟨a, p, hp, e⟩ := exists_inv_mod P ht
  have : y = a • (t • y) + p • y := by
    rw [smul_smul, ← add_smul, e, one_smul]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hty) (Submodule.smul_mem_smul hp hy)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `reduction_add ((mem_localization_standardLattice _ _).1 hx _) ((mem_localization_standardLattice _ _).1 hy _)`.
-/
theorem redV_add (P : HeightOneSpectrum (𝓞 E)) {x y : Sp E n}
    (hx : x ∈ stdAt E n P) (hy : y ∈ stdAt E n P) : redV P (x + y) = redV P x + redV P y := by
  funext i
  exact reduction_add ((mem_localization_standardLattice _ _).1 hx _) ((mem_localization_standardLattice _ _).1 hy _)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `redP_osmul a ((mem_localization_standardLattice _ _).1 hx _)`.
-/
theorem redV_osmul (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) {x : Sp E n}
    (hx : x ∈ stdAt E n P) :
    redV P (a • x) = Ideal.Quotient.mk P.asIdeal a • redV P x := by
  funext i
  exact redP_osmul a ((mem_localization_standardLattice _ _).1 hx _)

/- English proof (translation)
Introduce `E _ _ _ n ST SG d f hf`. Establish `hf' : ∀ (w : SG) (y : Sp E n), y ∈ d.1.at w.1 → (f w).symm y ∈ stdAt E n w.1`. Introduce `w y hy`. Conclude with `(hf w _).1 (by simpa using hy)`. Set `D : Deco E n ST SG` to `{ N := d.1.N f := d.1.f be := fun w y => if y ∈ d.1.at w.1 then redV w.1 ((f w).symm y) else 0 }`.

Establish `hbe : ∀ (w : SG) (y : Sp E n), y ∈ d.1.at w.1 → D.be w y = redV w.1 ((f w).symm y)` using `fun w y hy => if_pos hy`. Establish `hsm : ∀ (w : SG) (a : 𝓞 E), ∀ x ∈ d.1.at w.1, D.be w (a • x) = Ideal.Quotient.mk w.1.asIdeal a • D.be w x`. Introduce `w a x hx`. Rewrite using `[hbe w _ (Submodule.smul_mem _ a hx), hbe w _ hx, equiv_osmul, redV_osmul _ _ (hf' w x hx)]`. Establish `hD : D.Ok` using `{ lat := d.2.lat uni := d.2.uni f_add := d.2.f_add f_smul := d.2.f_smul f_off := d.2.f_off f_ne := d.2.f_ne be_add := by`.

Introduce `w x hx y hy`. Use `replace hx : x ∈ d.1.at w.1 := hx`. Use `replace hy : y ∈ d.1.at w.1 := hy`. Rewrite using `[hbe w _ (Submodule.add_mem _ hx hy), hbe w _ hx, hbe w _ hy, map_add, redV_add _ (hf' w x hx) (hf' w y hy)]`. Use `be_smul := hsm`.

Use `be_off := fun w x hx => if_neg hx`. Use `be_surj := by`. Introduce `w c`. Use `choose r hr using fun i => Ideal.Quotient.mk_surjective (c i)`. Establish `h1 : (fun i => algebraMap (𝓞 E) E (r i) : Sp E n) ∈ stdLat E n` using `(mem_stdLat _).2 fun i => ⟨r i, rfl⟩`.

Establish `h2` using `(hf w _).2 (le_locP _ _ h1)`. Take `⟨s, hs, hsy⟩` from `(mem_locP _ _ _).1 h2`. Take `⟨a, p, hp, e⟩` from `exists_inv_mod w.1 hs`. Use `⟨a • s • _, Submodule.smul_mem _ a hsy, ?_⟩` and prove the remaining obligations. Establish `e' : Ideal.Quotient.mk w.1.asIdeal (a * s) = 1`.

Use `congrArg (Ideal.Quotient.mk w.1.asIdeal) e` as an intermediate fact. Rewrite `this` using `[map_add, Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero, map_one]`. Then use the resulting hypothesis. Rewrite using `[smul_smul, hsm w _ _ h2, e', one_smul, hbe w _ h2, LinearEquiv.symm_apply_apply]`. Use function extensionality and compare the values at `i`. Conclude with `(reduction_coe _ _).trans (hr i)`.

Use `be_ker := by`. Introduce `w y hy h0`. Use `replace hy : y ∈ d.1.N := hy`. Establish `hy' : y ∈ d.1.at w.1` using `le_locP _ _ hy`. Rewrite `h0` using `[hbe w _ hy']`.

Establish `hx` using `hf' w y hy'`. Take `⟨s, hs, hsx⟩` from `(mem_locP _ _ _).1 hx`. Establish `h0' : redV w.1 (s • (f w).symm y) = 0`. Rewrite using `[redV_osmul _ _ hx, h0, smul_zero]`. Use `choose r hr using (mem_stdLat _).1 hsx`.

Establish `hmem : ∀ i, r i ∈ w.1.asIdeal`. Introduce `i`. Establish `h3 : redP w.1 ((s • (f w).symm y) i) = 0` using `congrFun h0' i`. Rewrite `h3` using `[← hr i, reduction_coe]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h3`.

Establish `h4 : s • (f w).symm y = ∑ i, r i • (Pi.single i (algebraMap (𝓞 E) E 1) : Sp E n)`. Generalize the expression as in `s • (f w).symm y = x at hr`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]`. Establish `h5 : s • y ∈ w.1.asIdeal • d.1.at w.1`.

Establish `: s • y = f w (s • (f w).symm y)`. Rewrite using `[equiv_osmul, LinearEquiv.apply_symm_apply]`. Rewrite using `[this, h4, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[equiv_osmul]`.

Conclude with `Submodule.smul_mem_smul (hmem i) ((hf w _).2 (le_locP _ _ (single_mem_stdLat i 1)))`. Take `⟨t, ht, hts⟩` from `(mem_locP _ _ _).1 (smul_localizationAt_le w.1 d.1.N h5)`. Use `mem_smul_of_mem_locP w.1 d.1.N hy ((mem_locP _ _ _).2 ⟨t * s, ?_, ?_⟩)` and prove the remaining obligations. Conclude with `fun hm => (w.1.isPrime.mem_or_mem hm).elim ht hs`. Rewrite using `[mul_smul] }` and apply the resulting hypothesis.

Use `⟨⟨D, hD⟩, rfl, rfl, fun w x hx => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D.be w (f w x) = _`. Rewrite using `[hbe w _ ((hf w x).2 hx), LinearEquiv.symm_apply_apply]`.
-/
theorem exists_deco_of_frames : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (d : DecoSet E n ST ∅) (f : SG → (Sp E n ≃ₗ[E] Sp E n)), (∀ (w : SG) (x : Sp E n), f w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) → ∃ d' : DecoSet E n ST SG, d'.1.N = d.1.N ∧ d'.1.f = d.1.f ∧ ∀ w : SG, ∀ x ∈ stdAt E n w.1, d'.1.be w (f w x) = redV w.1 x := by
  classical
  intro E _ _ _ n ST SG d f hf
  have hf' : ∀ (w : SG) (y : Sp E n), y ∈ d.1.at w.1 → (f w).symm y ∈ stdAt E n w.1 := by
    intro w y hy
    exact (hf w _).1 (by simpa using hy)
  let D : Deco E n ST SG :=
    { N := d.1.N
      f := d.1.f
      be := fun w y => if y ∈ d.1.at w.1 then redV w.1 ((f w).symm y) else 0 }
  have hbe : ∀ (w : SG) (y : Sp E n), y ∈ d.1.at w.1 → D.be w y = redV w.1 ((f w).symm y) :=
    fun w y hy => if_pos hy
  have hsm : ∀ (w : SG) (a : 𝓞 E), ∀ x ∈ d.1.at w.1,
      D.be w (a • x) = Ideal.Quotient.mk w.1.asIdeal a • D.be w x := by
    intro w a x hx
    rw [hbe w _ (Submodule.smul_mem _ a hx), hbe w _ hx, equiv_osmul, redV_osmul _ _ (hf' w x hx)]
  have hD : D.Ok :=
    { lat := d.2.lat
      uni := d.2.uni
      f_add := d.2.f_add
      f_smul := d.2.f_smul
      f_off := d.2.f_off
      f_ne := d.2.f_ne
      be_add := by
        intro w x hx y hy
        replace hx : x ∈ d.1.at w.1 := hx
        replace hy : y ∈ d.1.at w.1 := hy
        rw [hbe w _ (Submodule.add_mem _ hx hy), hbe w _ hx, hbe w _ hy, map_add,
          redV_add _ (hf' w x hx) (hf' w y hy)]
      be_smul := hsm
      be_off := fun w x hx => if_neg hx
      be_surj := by
        intro w c
        choose r hr using fun i => Ideal.Quotient.mk_surjective (c i)
        have h1 : (fun i => algebraMap (𝓞 E) E (r i) : Sp E n) ∈ stdLat E n :=
          (mem_stdLat _).2 fun i => ⟨r i, rfl⟩
        have h2 := (hf w _).2 (le_locP _ _ h1)
        obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 h2
        obtain ⟨a, p, hp, e⟩ := exists_inv_mod w.1 hs
        refine ⟨a • s • _, Submodule.smul_mem _ a hsy, ?_⟩
        have e' : Ideal.Quotient.mk w.1.asIdeal (a * s) = 1 := by
          have := congrArg (Ideal.Quotient.mk w.1.asIdeal) e
          rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero, map_one] at this
        rw [smul_smul, hsm w _ _ h2, e', one_smul, hbe w _ h2, LinearEquiv.symm_apply_apply]
        funext i
        exact (reduction_coe _ _).trans (hr i)
      be_ker := by
        intro w y hy h0
        replace hy : y ∈ d.1.N := hy
        have hy' : y ∈ d.1.at w.1 := le_locP _ _ hy
        rw [hbe w _ hy'] at h0
        have hx := hf' w y hy'
        obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hx
        have h0' : redV w.1 (s • (f w).symm y) = 0 := by
          rw [redV_osmul _ _ hx, h0, smul_zero]
        choose r hr using (mem_stdLat _).1 hsx
        have hmem : ∀ i, r i ∈ w.1.asIdeal := by
          intro i
          have h3 : redP w.1 ((s • (f w).symm y) i) = 0 := congrFun h0' i
          rw [← hr i, reduction_coe] at h3
          exact Ideal.Quotient.eq_zero_iff_mem.1 h3
        have h4 : s • (f w).symm y
            = ∑ i, r i • (Pi.single i (algebraMap (𝓞 E) E 1) : Sp E n) := by
          generalize s • (f w).symm y = x at hr
          funext j
          simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
        have h5 : s • y ∈ w.1.asIdeal • d.1.at w.1 := by
          have : s • y = f w (s • (f w).symm y) := by
            rw [equiv_osmul, LinearEquiv.apply_symm_apply]
          rw [this, h4, map_sum]
          refine Submodule.sum_mem _ fun i _ => ?_
          rw [equiv_osmul]
          exact Submodule.smul_mem_smul (hmem i)
            ((hf w _).2 (le_locP _ _ (single_mem_stdLat i 1)))
        obtain ⟨t, ht, hts⟩ := (mem_locP _ _ _).1 (smul_localizationAt_le w.1 d.1.N h5)
        refine mem_smul_of_mem_locP w.1 d.1.N hy ((mem_locP _ _ _).2 ⟨t * s, ?_, ?_⟩)
        · exact fun hm => (w.1.isPrime.mem_or_mem hm).elim ht hs
        · rwa [mul_smul] }
  refine ⟨⟨D, hD⟩, rfl, rfl, fun w x hx => ?_⟩
  change D.be w (f w x) = _
  rw [hbe w _ ((hf w x).2 hx), LinearEquiv.symm_apply_apply]

end GlobalTheory.FrameDeco
