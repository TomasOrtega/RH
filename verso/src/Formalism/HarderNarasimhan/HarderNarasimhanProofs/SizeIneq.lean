import Formalism.HarderNarasimhan.StatementPl
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Lemmata.GeneralBFactSecondTail.Imports

open Module NumberField

noncomputable section

namespace Formalism.HN

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] [NumberField K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {W : Type*} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_second''''''.goal1 .. | (apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_ …`.
-/
theorem sizeIneq_exists_mul_mem (A : Submodule (𝓞 K) V) (x : V)
    (hx : x ∈ Submodule.span K (A : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  first | exact Bl.general_b_fact_second''''''.goal1 .. | (apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''.goal1 <;> first | assumption | infer_instance)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨hxA, hxk⟩`. Conclude with `⟨Submodule.subset_span hxA, hxk⟩`. Introduce and unpack `x ⟨hxS, hxk⟩`.

Take `⟨d, hd, hdx⟩` from `sizeIneq_exists_mul_mem A x hxS`. Establish `hd' : algebraMap (𝓞 K) K d ≠ 0`. Introduce `h0`. Conclude with `hd (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))`. Establish `hmem : d • x ∈ (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V)`.

Use `⟨hdx, ?_⟩` and prove the remaining obligations. Use `show φ (d • x) = 0`. Rewrite using `[← algebraMap_smul K d x, map_smul, LinearMap.mem_ker.mp hxk, smul_zero]`. Establish `hx : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x)`. Rewrite using `[← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]`.

Rewrite using `[hx]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem sizeIneq_span_inf_ker (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    Submodule.span K ((A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (A : Set V) ⊓ LinearMap.ker φ := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨hxA, hxk⟩
    exact ⟨Submodule.subset_span hxA, hxk⟩
  · rintro x ⟨hxS, hxk⟩
    obtain ⟨d, hd, hdx⟩ := sizeIneq_exists_mul_mem A x hxS
    have hd' : algebraMap (𝓞 K) K d ≠ 0 := by
      intro h0
      exact hd (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))
    have hmem : d • x ∈ (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := by
      refine ⟨hdx, ?_⟩
      show φ (d • x) = 0
      rw [← algebraMap_smul K d x, map_smul, LinearMap.mem_ker.mp hxk, smul_zero]
    have hx : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/- English proof (translation)
Unfold `rkK`. Use `set S := Submodule.span K (A : Set V) with hS`. Establish `h1 : Submodule.span K ((A.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) W) : Set W) = S.map φ`. Rewrite using `[Submodule.map_coe, hS, Submodule.map_span]`. Both sides reduce to the same expression.

Rewrite using `[h1, sizeIneq_span_inf_ker]`. Use `(φ.domRestrict S).finrank_range_add_finrank_ker` as an intermediate fact. Rewrite `this` using `[LinearMap.range_domRestrict, LinearMap.ker_domRestrict]`. Rewrite using `[← this, ← Submodule.map_comap_subtype S (LinearMap.ker φ)]`. Use `congr 1`.

Conclude with `(Submodule.equivMapOfInjective _ S.injective_subtype _).finrank_eq.symm`.
-/
theorem sizeIneq_rk [FiniteDimensional K V] (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    rkK (A.map (φ.restrictScalars (𝓞 K))) + rkK (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) =
      rkK A := by
  unfold rkK
  set S := Submodule.span K (A : Set V) with hS
  have h1 : Submodule.span K ((A.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) W) : Set W) =
      S.map φ := by
    rw [Submodule.map_coe, hS, Submodule.map_span]
    rfl
  rw [h1, sizeIneq_span_inf_ker]
  have := (φ.domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at this
  rw [← this, ← Submodule.map_comap_subtype S (LinearMap.ker φ)]
  congr 1
  exact (Submodule.equivMapOfInjective _ S.injective_subtype _).finrank_eq.symm

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hAfg hBfg hIB hI0`. Establish `: FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hrkeq` using `sizeIneq_rk φ A`. Use `set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef`. Use `set A₀ := A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) with hA₀def`.

Use `set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ`. Use `set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'`. Establish `hIfg : I.FG` using `hAfg.map _`. Establish `hA0 : A ≠ ⊥`. Introduce `h`.

Apply `hI0` to reduce the goal to its premises. Rewrite using `[hIdef, h, Submodule.map_bot]`. Establish `hB0 : B ≠ ⊥` using `fun h => hI0 (le_bot_iff.mp (h ▸ hIB))`. Take `⟨hAlat, -, -⟩` from `h3 K V ι b X hX A hAfg`. Take `⟨hBlat, -, -⟩` from `h3 K W κ b' X' hX' B hBfg`.

Take `⟨-, hrkI, hhtI⟩` from `h3 K W κ b' X' hX' I hIfg`. Take `⟨hsat, hht⟩` from `h2 K V ι W κ b X b' X' hX hX' φ A hAfg`. Establish `hSA` using `h1 K V ι b X hX A hAfg hA0`. Establish `hSB` using `h1 K W κ b' X' hX' B hBfg hB0`. Take `⟨-, -, hsQ, -, hlarge, -⟩` from `hSA`.

Take `⟨-, -, -, hleast, -, -⟩` from `hSB`. Establish `hSI` using `(h1 K W κ b' X' hX' I hIfg hI0).1`. Establish `hA₀ne : A₀ ≠ A`. Introduce `h`. Apply `hI0` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff]`. Introduce and unpack `y ⟨x, hx, rfl⟩`. Establish `hx0 : x ∈ A₀` using `h ▸ hx`. Conclude with `(Submodule.mem_bot _).2 (LinearMap.mem_ker.1 hx0.2)`. Establish `hSBB` using `saturation_basic_properties (𝓞 K) W _ ρ' B hBlat`.

Establish `hrkIpos : 0 < rk ρ' I`. Break down `Nat.eq_zero_or_pos (rk ρ' I) with h | h` into its components or cases. Conclude with `absurd ((hSBB.2.2.2.1 I hIB).1 h) hI0`. Conclude with `h`. Establish `hMB` using `slope_characterization (𝓞 K) W _ ρ' B hBlat hB0`.

Establish `hdegI` using `(hMB.1 (muMax ρ' B)).1 le_rfl I hIB`. Establish `hslI : slope ρ' I ≤ muMax ρ' B` using `by show Formalism.F.deg (zl ρ' I) / (Formalism.F.rk (zl ρ' I) : ℝ) ≤ _`. Rewrite using `[div_le_iff₀ (by exact_mod_cast hrkIpos)]`. Conclude with `hdegI`. Establish `hleI : leastSize b' X' B ≤ size b' X' I`.

Rewrite using `[hleast, hSI]`. Conclude with `Real.exp_le_exp.2 (by linarith)`. Establish `hSBA` using `saturation_basic_properties (𝓞 K) V _ ρ A hAlat`. Establish `hq` using `hSBA.2.2.2.2.2.2.2 A₀ hsat`. Establish `hlt : rk ρ A₀ < rk ρ A`.

Use `lt_of_le_of_ne hq.2.1 (fun h => hA₀ne ?_)` and prove the remaining obligations. Conclude with `(hSBA.2.2.1 A₀ A hsat hsat.1 le_rfl h.symm).symm`. Establish `hMA` using `slope_characterization (𝓞 K) V _ ρ A hAlat hA0`. Establish `hmin` using `(hMA.2.1 (muMin ρ A)).1 le_rfl A₀ hsat.1`. Establish `hslQ : muMin ρ A ≤ Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ A₀))`.

Establish `hr : (Formalism.F.rk (Formalism.F.quot (zl ρ A) (zl ρ A₀)) : ℝ) = (rk ρ A : ℝ) - rk ρ A₀`. Rewrite using `[hq.1, Nat.cast_sub hq.2.1]`. Establish `hrpos : (0 : ℝ) < (rk ρ A : ℝ) - rk ρ A₀`. Establish `: (rk ρ A₀ : ℝ) < rk ρ A` using `by exact_mod_cast hlt`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `Formalism.F.slope`. Rewrite using `[hr, le_div_iff₀ hrpos, hq.2.2]`. Conclude with `hmin`. Establish `hQle : sizeQ b X A A₀ ≤ largestSize b X A`. Rewrite using `[hlarge, hsQ A₀ hsat hA₀ne]`.

Conclude with `Real.exp_le_exp.2 (by linarith)`. Establish `hlargepos : 0 < largestSize b X A` using `by rw [hlarge]; exact Real.exp_pos _`. Use `set P := ∏ v, opNormAt b X b' X' v φ with hPdef`. Establish `hP : 0 ≤ P` using `Finset.prod_nonneg (fun v _ => norm_nonneg _)`. Establish `hf : (0 : ℝ) < nPl K`.

Establish `: 0 < nPl K` using `Fintype.card_pos`. Conclude with `this` after adjusting the coercions. Establish `hs : (0 : ℝ) < rkK I`. Establish `: rkK I ≠ 0`. Introduce `h`.

Rewrite `hrkIpos` using `[hrkI, h, mul_zero]`. Conclude with `lt_irrefl _ hrkIpos`. Conclude with `Nat.pos_of_ne_zero this` after adjusting the coercions. Establish `hrkR : ((rkK A : ℝ) - rkK A₀) = rkK I`. Rewrite using `[← hrkeq]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hht` using `[Finset.prod_pow]`. Establish `hX0 : 0 ≤ P ^ (2 * rkK I)` using `pow_nonneg hP _`. Establish `hQpos : 0 < htQ b X A A₀` using `pos_of_mul_pos_right (lt_of_lt_of_le hhtI hht) hX0`.

Establish `he : (0 : ℝ) ≤ 1 / (2 * (nPl K : ℝ) * (rkK I : ℝ))` using `by positivity`. Establish `hcore : size b' X' I ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A A₀`. Unfold `size sizeQ`. Rewrite using `[hrkR]`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hP]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[div_le_iff₀ hlargepos]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sizeIneq_of (h1 : SizeMu) (h2 : HtImage) (h3 : PlLat) : SizeIneq := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hAfg hBfg hIB hI0
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hrkeq := sizeIneq_rk φ A
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set A₀ := A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) with hA₀def
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hA0 : A ≠ ⊥ := by
    intro h
    apply hI0
    rw [hIdef, h, Submodule.map_bot]
  have hB0 : B ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hIB))
  obtain ⟨hAlat, -, -⟩ := h3 K V ι b X hX A hAfg
  obtain ⟨hBlat, -, -⟩ := h3 K W κ b' X' hX' B hBfg
  obtain ⟨-, hrkI, hhtI⟩ := h3 K W κ b' X' hX' I hIfg
  obtain ⟨hsat, hht⟩ := h2 K V ι W κ b X b' X' hX hX' φ A hAfg
  have hSA := h1 K V ι b X hX A hAfg hA0
  have hSB := h1 K W κ b' X' hX' B hBfg hB0
  obtain ⟨-, -, hsQ, -, hlarge, -⟩ := hSA
  obtain ⟨-, -, -, hleast, -, -⟩ := hSB
  have hSI := (h1 K W κ b' X' hX' I hIfg hI0).1

  have hA₀ne : A₀ ≠ A := by
    intro h
    apply hI0
    rw [eq_bot_iff]
    rintro y ⟨x, hx, rfl⟩
    have hx0 : x ∈ A₀ := h ▸ hx
    exact (Submodule.mem_bot _).2 (LinearMap.mem_ker.1 hx0.2)

  have hSBB := saturation_basic_properties (𝓞 K) W _ ρ' B hBlat
  have hrkIpos : 0 < rk ρ' I := by
    rcases Nat.eq_zero_or_pos (rk ρ' I) with h | h
    · exact absurd ((hSBB.2.2.2.1 I hIB).1 h) hI0
    · exact h
  have hMB := slope_characterization (𝓞 K) W _ ρ' B hBlat hB0
  have hdegI := (hMB.1 (muMax ρ' B)).1 le_rfl I hIB
  have hslI : slope ρ' I ≤ muMax ρ' B := by
    show Formalism.F.deg (zl ρ' I) / (Formalism.F.rk (zl ρ' I) : ℝ) ≤ _
    rw [div_le_iff₀ (by exact_mod_cast hrkIpos)]
    exact hdegI
  have hleI : leastSize b' X' B ≤ size b' X' I := by
    rw [hleast, hSI]
    exact Real.exp_le_exp.2 (by linarith)

  have hSBA := saturation_basic_properties (𝓞 K) V _ ρ A hAlat
  have hq := hSBA.2.2.2.2.2.2.2 A₀ hsat
  have hlt : rk ρ A₀ < rk ρ A := by
    refine lt_of_le_of_ne hq.2.1 (fun h => hA₀ne ?_)
    exact (hSBA.2.2.1 A₀ A hsat hsat.1 le_rfl h.symm).symm
  have hMA := slope_characterization (𝓞 K) V _ ρ A hAlat hA0
  have hmin := (hMA.2.1 (muMin ρ A)).1 le_rfl A₀ hsat.1
  have hslQ : muMin ρ A ≤ Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ A₀)) := by
    have hr : (Formalism.F.rk (Formalism.F.quot (zl ρ A) (zl ρ A₀)) : ℝ) = (rk ρ A : ℝ) - rk ρ A₀ := by
      rw [hq.1, Nat.cast_sub hq.2.1]
    have hrpos : (0 : ℝ) < (rk ρ A : ℝ) - rk ρ A₀ := by
      have : (rk ρ A₀ : ℝ) < rk ρ A := by exact_mod_cast hlt
      linarith
    unfold Formalism.F.slope
    rw [hr, le_div_iff₀ hrpos, hq.2.2]
    exact hmin
  have hQle : sizeQ b X A A₀ ≤ largestSize b X A := by
    rw [hlarge, hsQ A₀ hsat hA₀ne]
    exact Real.exp_le_exp.2 (by linarith)
  have hlargepos : 0 < largestSize b X A := by rw [hlarge]; exact Real.exp_pos _

  set P := ∏ v, opNormAt b X b' X' v φ with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg (fun v _ => norm_nonneg _)
  have hf : (0 : ℝ) < nPl K := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hs : (0 : ℝ) < rkK I := by
    have : rkK I ≠ 0 := by
      intro h
      rw [hrkI, h, mul_zero] at hrkIpos
      exact lt_irrefl _ hrkIpos
    exact_mod_cast Nat.pos_of_ne_zero this
  have hrkR : ((rkK A : ℝ) - rkK A₀) = rkK I := by
    rw [← hrkeq]; push_cast; ring
  rw [Finset.prod_pow] at hht
  have hX0 : 0 ≤ P ^ (2 * rkK I) := pow_nonneg hP _
  have hQpos : 0 < htQ b X A A₀ := pos_of_mul_pos_right (lt_of_lt_of_le hhtI hht) hX0
  have he : (0 : ℝ) ≤ 1 / (2 * (nPl K : ℝ) * (rkK I : ℝ)) := by positivity
  have hcore : size b' X' I ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A A₀ := by
    unfold size sizeQ
    rw [hrkR]
    calc ht b' X' I ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ)))
        ≤ (P ^ (2 * rkK I) * htQ b X A A₀) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.rpow_le_rpow hhtI.le hht he
      _ = (P ^ (2 * rkK I)) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) *
            htQ b X A A₀ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.mul_rpow hX0 hQpos.le
      _ = P ^ ((1 : ℝ) / (nPl K : ℝ)) *
            htQ b X A A₀ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP]
          congr 1
          push_cast
          field_simp
  rw [div_le_iff₀ hlargepos]
  calc leastSize b' X' B ≤ size b' X' I := hleI
    _ ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A A₀ := hcore
    _ ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * largestSize b X A :=
        mul_le_mul_of_nonneg_left hQle (Real.rpow_nonneg hP _)

end Formalism.HN
