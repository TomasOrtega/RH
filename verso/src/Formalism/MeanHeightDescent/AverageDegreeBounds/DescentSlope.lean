import Mathlib
import Formalism.MeanHeightDescent.MuMaxMinkowski
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeIneq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar

open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

open Formalism.HN

/- English proof (translation)
Establish `: FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hrkeq` using `sizeIneq_rk φ A`. Take `⟨hsat, hht⟩` from `height_image_formula K V ι W κ b X b' X' hX hX' φ A hAfg`. Establish `hker : A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot.2 hinj, Submodule.restrictScalars_bot, inf_bot_eq]`.

Rewrite `hrkeq`, `hsat`, `hht` using `[hker]`. Establish `hrkbot : rkK (K` using `K) (⊥ : Submodule (𝓞 K) V) = 0 := by`. Unfold `rkK`. Simplify using the standard rewrite rules. Rewrite `hrkeq` using `[hrkbot, add_zero]`.

Use `⟨hrkeq, ?_⟩` and prove the remaining obligations. Use `set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef`. Use `set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ`. Use `set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'`. Establish `hIfg : I.FG` using `hAfg.map _`.

Establish `hI0 : I ≠ ⊥`. Introduce `h`. Apply `hA0` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `x hx`.

Establish `hm : φ x ∈ I` using `⟨x, hx, rfl⟩`. Rewrite `hm` using `[h]`. Establish `h0 : φ x = 0` using `(Submodule.mem_bot _).1 hm`. Conclude with `(Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))`. Take `⟨hAlat, -, -⟩` from `place_lattice_structure K V ι b X hX A hAfg`.

Take `⟨-, -, hhtI⟩` from `place_lattice_structure K W κ b' X' hX' I hIfg`. Take `⟨-, -, hsQ, -, -, -⟩` from `size_maximal_slope K V ι b X hX A hAfg hA0`. Establish `hSI` using `(size_maximal_slope K W κ b' X' hX' I hIfg hI0).1`. Establish `hSBA` using `saturation_basic_properties (𝓞 K) V _ ρ A hAlat`. Establish `hq` using `hSBA.2.2.2.2.2.2.2 ⊥ hsat`.

Establish `hrb : rk ρ (⊥ : Submodule (𝓞 K) V) = 0` using `(hSBA.2.2.2.1 ⊥ bot_le).2 rfl`. Establish `hdb : deg ρ (⊥ : Submodule (𝓞 K) V) = 0` using `hSBA.2.2.2.2.1`. Establish `hslQ : Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ (⊥ : Submodule (𝓞 K) V))) = slope ρ A`. Unfold `Formalism.F.slope`. Rewrite using `[hq.1, hq.2.2, hrb, hdb, Nat.sub_zero, sub_zero]`.

Both sides reduce to the same expression. Establish `hsQ'` using `hsQ ⊥ hsat (Ne.symm hA0)`. Rewrite `hsQ'` using `[hslQ]`. Use `set P := ∏ v, opNormAt b X b' X' v φ with hPdef`. Establish `hP : 0 ≤ P` using `Finset.prod_nonneg (fun v _ => norm_nonneg _)`.

Establish `hf : (0 : ℝ) < nPl K`. Establish `: 0 < nPl K` using `Fintype.card_pos`. Conclude with `this` after adjusting the coercions. Establish `hs : (0 : ℝ) < rkK I`. Rewrite using `[hrkeq]`.

Establish `h : Submodule.span K (A : Set V) ≠ ⊥`. Introduce `h`. Apply `hA0` to reduce the goal to its premises. Rewrite `h` using `[Submodule.span_eq_bot]`. Conclude with `(Submodule.eq_bot_iff _).2 (fun x hx => h x hx)`.

Establish `: 0 < rkK (K` using `K) A := Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)`. Conclude with `this` after adjusting the coercions. Establish `hrkR : ((rkK A : ℝ) - rkK (K` using `K) (⊥ : Submodule (𝓞 K) V)) = rkK I := by`. Rewrite using `[hrkbot, hrkeq]`. Simplify using the standard rewrite rules.

Rewrite `hht` using `[Finset.prod_pow, ← hPdef]`. Establish `hX0 : 0 ≤ P ^ (2 * rkK I)` using `pow_nonneg hP _`. Establish `hQpos : 0 < htQ b X A ⊥` using `pos_of_mul_pos_right (lt_of_lt_of_le hhtI hht) hX0`. Establish `hPpos : 0 < P`. Break down `hP.lt_or_eq with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Establish `hne : 2 * rkK I ≠ 0`. Establish `: 0 < rkK I` using `by exact_mod_cast hs`. Use linear arithmetic over natural numbers and integers.

Rewrite `hht` using `[← h, zero_pow hne, zero_mul]`. Conclude with `absurd hhtI (not_lt.2 hht)`. Establish `he : (0 : ℝ) ≤ 1 / (2 * (nPl K : ℝ) * (rkK I : ℝ))` using `by positivity`. Establish `hcore : size b' X' I ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A ⊥`. Unfold `size sizeQ`.

Rewrite using `[hrkR]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hP]`. Use `congr 1`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite `hcore` using `[hSI, hsQ', Real.rpow_def_of_pos hPpos, ← Real.exp_add, Real.exp_le_exp]`. Establish `hht2 : htMap b X b' X' φ = 2 * (Real.log P * (1 / (nPl K : ℝ)))`. Unfold `htMap`.

Establish `hne : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)), opNormAt b X b' X' v φ ≠ 0`. Introduce `v hv h0`. Conclude with `hPpos.ne' (Finset.prod_eq_zero hv h0)`. Rewrite using `[hPdef, Real.log_prod hne]`. Simplify using `only [Real.log_pow]`.

Rewrite using `[← Finset.mul_sum]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hht2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem slope_image_injective
    {K V ι W κ : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det)
    (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (hAfg : A.FG) (hA0 : A ≠ ⊥)
    (hinj : Function.Injective φ) :
    rkK (A.map (φ.restrictScalars (𝓞 K))) = rkK A ∧
      2 * slope (Formalism.HermitianLatticesTheory.realize b X) A - htMap b X b' X' φ ≤
        2 * slope (Formalism.HermitianLatticesTheory.realize b' X') (A.map (φ.restrictScalars (𝓞 K))) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hrkeq := sizeIneq_rk φ A
  obtain ⟨hsat, hht⟩ := height_image_formula K V ι W κ b X b' X' hX hX' φ A hAfg
  have hker : A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥ := by
    rw [LinearMap.ker_eq_bot.2 hinj, Submodule.restrictScalars_bot, inf_bot_eq]
  rw [hker] at hrkeq hsat hht
  have hrkbot : rkK (K := K) (⊥ : Submodule (𝓞 K) V) = 0 := by
    unfold rkK
    simp
  rw [hrkbot, add_zero] at hrkeq
  refine ⟨hrkeq, ?_⟩
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hm : φ x ∈ I := ⟨x, hx, rfl⟩
    rw [h] at hm
    have h0 : φ x = 0 := (Submodule.mem_bot _).1 hm
    exact (Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))
  obtain ⟨hAlat, -, -⟩ := place_lattice_structure K V ι b X hX A hAfg
  obtain ⟨-, -, hhtI⟩ := place_lattice_structure K W κ b' X' hX' I hIfg
  obtain ⟨-, -, hsQ, -, -, -⟩ := size_maximal_slope K V ι b X hX A hAfg hA0
  have hSI := (size_maximal_slope K W κ b' X' hX' I hIfg hI0).1
  have hSBA := saturation_basic_properties (𝓞 K) V _ ρ A hAlat
  have hq := hSBA.2.2.2.2.2.2.2 ⊥ hsat
  have hrb : rk ρ (⊥ : Submodule (𝓞 K) V) = 0 := (hSBA.2.2.2.1 ⊥ bot_le).2 rfl
  have hdb : deg ρ (⊥ : Submodule (𝓞 K) V) = 0 := hSBA.2.2.2.2.1
  have hslQ : Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ (⊥ : Submodule (𝓞 K) V))) = slope ρ A := by
    unfold Formalism.F.slope
    rw [hq.1, hq.2.2, hrb, hdb, Nat.sub_zero, sub_zero]
    rfl
  have hsQ' := hsQ ⊥ hsat (Ne.symm hA0)
  rw [hslQ] at hsQ'
  set P := ∏ v, opNormAt b X b' X' v φ with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg (fun v _ => norm_nonneg _)
  have hf : (0 : ℝ) < nPl K := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hs : (0 : ℝ) < rkK I := by
    rw [hrkeq]
    have h : Submodule.span K (A : Set V) ≠ ⊥ := by
      intro h
      apply hA0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    have : 0 < rkK (K := K) A :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
    exact_mod_cast this
  have hrkR : ((rkK A : ℝ) - rkK (K := K) (⊥ : Submodule (𝓞 K) V)) = rkK I := by
    rw [hrkbot, hrkeq]; simp
  rw [Finset.prod_pow, ← hPdef] at hht
  have hX0 : 0 ≤ P ^ (2 * rkK I) := pow_nonneg hP _
  have hQpos : 0 < htQ b X A ⊥ := pos_of_mul_pos_right (lt_of_lt_of_le hhtI hht) hX0
  have hPpos : 0 < P := by
    rcases hP.lt_or_eq with h | h
    · exact h
    · exfalso
      have hne : 2 * rkK I ≠ 0 := by
        have : 0 < rkK I := by exact_mod_cast hs
        omega
      rw [← h, zero_pow hne, zero_mul] at hht
      exact absurd hhtI (not_lt.2 hht)
  have he : (0 : ℝ) ≤ 1 / (2 * (nPl K : ℝ) * (rkK I : ℝ)) := by positivity
  have hcore : size b' X' I ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A ⊥ := by
    unfold size sizeQ
    rw [hrkR]
    calc ht b' X' I ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ)))
        ≤ (P ^ (2 * rkK I) * htQ b X A ⊥) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.rpow_le_rpow hhtI.le hht he
      _ = (P ^ (2 * rkK I)) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) *
            htQ b X A ⊥ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.mul_rpow hX0 hQpos.le
      _ = P ^ ((1 : ℝ) / (nPl K : ℝ)) *
            htQ b X A ⊥ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP]
          congr 1
          push_cast
          field_simp
  rw [hSI, hsQ', Real.rpow_def_of_pos hPpos, ← Real.exp_add, Real.exp_le_exp] at hcore
  have hht2 : htMap b X b' X' φ = 2 * (Real.log P * (1 / (nPl K : ℝ))) := by
    unfold htMap
    have hne : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)), opNormAt b X b' X' v φ ≠ 0 := by
      intro v hv h0
      exact hPpos.ne' (Finset.prod_eq_zero hv h0)
    rw [hPdef, Real.log_prod hne]
    simp only [Real.log_pow]
    rw [← Finset.mul_sum]
    push_cast
    ring
  rw [hht2]
  linarith

/- English proof (translation)
Introduce `K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hAfg hBfg hA0 hinj hIB`. Take `⟨hrkeq, hsl⟩` from `slope_image_injective b X b' X' hX hX' φ A hAfg hA0 hinj`. Use `set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef`. Use `set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ`. Use `set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'`.

Establish `hIfg : I.FG` using `hAfg.map _`. Establish `hI0 : I ≠ ⊥`. Introduce `h`. Apply `hA0` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`.

Introduce `x hx`. Establish `hm : φ x ∈ I` using `⟨x, hx, rfl⟩`. Rewrite `hm` using `[h]`. Establish `h0 : φ x = 0` using `(Submodule.mem_bot _).1 hm`. Conclude with `(Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))`.

Establish `hB0 : B ≠ ⊥` using `fun h => hI0 (le_bot_iff.mp (h ▸ hIB))`. Take `⟨hBlat, hrkB, -⟩` from `place_lattice_structure K W κ b' X' hX' B hBfg`. Take `⟨-, hrkI, -⟩` from `place_lattice_structure K W κ b' X' hX' I hIfg`. Establish `hSBB` using `saturation_basic_properties (𝓞 K) W _ ρ' B hBlat`. Establish `hMB` using `slope_characterization (𝓞 K) W _ ρ' B hBlat hB0`.

Establish `hmin` using `(hMB.2.1 (muMin ρ' B)).1 le_rfl I hIB`. Establish `hrkIpos : 0 < rk ρ' I`. Break down `Nat.eq_zero_or_pos (rk ρ' I) with h | h` into its components or cases. Conclude with `absurd ((hSBB.2.2.2.1 I hIB).1 h) hI0`. Conclude with `h`.

Establish `hrkBpos : 0 < rk ρ' B`. Break down `Nat.eq_zero_or_pos (rk ρ' B) with h | h` into its components or cases. Conclude with `absurd ((hSBB.2.2.2.1 B le_rfl).1 h) hB0`. Conclude with `h`. Establish `hdI : deg ρ' I = slope ρ' I * (rk ρ' I : ℝ)`.

Establish `: (rk ρ' I : ℝ) ≠ 0` using `by exact_mod_cast hrkIpos.ne'`. Use `show deg ρ' I = deg ρ' I / (rk ρ' I : ℝ) * (rk ρ' I : ℝ)`. Clear the denominators using the available nonvanishing facts. Establish `hdB : deg ρ' B = slope ρ' B * (rk ρ' B : ℝ)`. Establish `: (rk ρ' B : ℝ) ≠ 0` using `by exact_mod_cast hrkBpos.ne'`.

Use `show deg ρ' B = deg ρ' B / (rk ρ' B : ℝ) * (rk ρ' B : ℝ)`. Clear the denominators using the available nonvanishing facts. Establish `hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ)`. Conclude with `(Module.finrank_pos : 0 < Module.finrank ℚ K)` after adjusting the coercions. Rewrite `hmin` using `[hdI, hdB, hrkB, hrkI, hrkeq]`.

Move the coercions through the operations in `at hmin`. Establish `hmin' : muMin ρ' B * ((rkK B : ℝ) - rkK A) ≤ slope ρ' B * (rkK B : ℝ) - slope ρ' I * (rkK A : ℝ)`. Use `le_of_mul_le_mul_left ?_ hn` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hra : (0 : ℝ) ≤ (rkK A : ℝ)` using `Nat.cast_nonneg _`.

Establish `h2` using `mul_le_mul_of_nonneg_left hsl hra`. Unfold `muDef muMinDef`. Simplify using `only [← hρ, ← hρ']`. Use polynomial arithmetic with `[h2, hmin']`.
-/
theorem descent_slope : DescentSlope := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hAfg hBfg hA0 hinj hIB
  obtain ⟨hrkeq, hsl⟩ := slope_image_injective b X b' X' hX hX' φ A hAfg hA0 hinj
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hm : φ x ∈ I := ⟨x, hx, rfl⟩
    rw [h] at hm
    have h0 : φ x = 0 := (Submodule.mem_bot _).1 hm
    exact (Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))
  have hB0 : B ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hIB))
  obtain ⟨hBlat, hrkB, -⟩ := place_lattice_structure K W κ b' X' hX' B hBfg
  obtain ⟨-, hrkI, -⟩ := place_lattice_structure K W κ b' X' hX' I hIfg
  have hSBB := saturation_basic_properties (𝓞 K) W _ ρ' B hBlat
  have hMB := slope_characterization (𝓞 K) W _ ρ' B hBlat hB0
  have hmin := (hMB.2.1 (muMin ρ' B)).1 le_rfl I hIB
  have hrkIpos : 0 < rk ρ' I := by
    rcases Nat.eq_zero_or_pos (rk ρ' I) with h | h
    · exact absurd ((hSBB.2.2.2.1 I hIB).1 h) hI0
    · exact h
  have hrkBpos : 0 < rk ρ' B := by
    rcases Nat.eq_zero_or_pos (rk ρ' B) with h | h
    · exact absurd ((hSBB.2.2.2.1 B le_rfl).1 h) hB0
    · exact h
  have hdI : deg ρ' I = slope ρ' I * (rk ρ' I : ℝ) := by
    have : (rk ρ' I : ℝ) ≠ 0 := by exact_mod_cast hrkIpos.ne'
    show deg ρ' I = deg ρ' I / (rk ρ' I : ℝ) * (rk ρ' I : ℝ)
    field_simp
  have hdB : deg ρ' B = slope ρ' B * (rk ρ' B : ℝ) := by
    have : (rk ρ' B : ℝ) ≠ 0 := by exact_mod_cast hrkBpos.ne'
    show deg ρ' B = deg ρ' B / (rk ρ' B : ℝ) * (rk ρ' B : ℝ)
    field_simp
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  rw [hdI, hdB, hrkB, hrkI, hrkeq] at hmin
  push_cast at hmin
  have hmin' : muMin ρ' B * ((rkK B : ℝ) - rkK A) ≤
      slope ρ' B * (rkK B : ℝ) - slope ρ' I * (rkK A : ℝ) := by
    refine le_of_mul_le_mul_left ?_ hn
    linarith
  have hra : (0 : ℝ) ≤ (rkK A : ℝ) := Nat.cast_nonneg _
  have h2 := mul_le_mul_of_nonneg_left hsl hra
  unfold muDef muMinDef
  simp only [← hρ, ← hρ']
  nlinarith [h2, hmin']

end Formalism.ExtensionFiltration
