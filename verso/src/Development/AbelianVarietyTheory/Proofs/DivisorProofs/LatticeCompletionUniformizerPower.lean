import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.SUCong

noncomputable section
namespace GlobalTheory.TamCnt

section CompK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Conclude with `hπ2 (zero_mem _)`. Establish `hv0 : v.intValuation π ≠ 0` using `v.intValuation_ne_zero π hπ0`. Establish `hπF : algebraMap F (Fv F v) (π : F) ≠ 0`.

Introduce `h`. Apply `hπ0` to reduce the goal to its premises. Use `(map_eq_zero_iff (algebraMap F (Fv F v)) (algebraMap F (Fv F v)).injective).1 h` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hlow : WithZero.exp (-1 : ℤ) ≤ v.intValuation π`.

Establish `h2 : ¬ v.intValuation π ≤ WithZero.exp (-((2 : ℕ) : ℤ))` using `fun h => hπ2 ((v.intValuation_le_pow_iff_mem π 2).1 h)`. Rewrite `h2`, the goal using `[← WithZero.exp_log hv0]`. Rewrite using `[WithZero.exp_le_exp]`. Rewrite `h2` using `[WithZero.exp_le_exp]`. Move the coercions through the operations in `at h2`.

Use linear arithmetic over natural numbers and integers. Establish `htv : v.intValuation t ≤ WithZero.exp (-(k : ℤ))` using `(v.intValuation_le_pow_iff_mem t k).2 ht`. Use `⟨algebraMap F (Fv F v) (t : F) / algebraMap F (Fv F v) (π : F) ^ k, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, map_pow]`. Express the relevant statement in the definitionally equal form `Valued.v ((t : F) : v.adicCompletion F) / Valued.v ((π : F) : v.adicCompletion F) ^ k ≤ 1`.

Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]`. Rewrite using `[div_le_one₀ (pow_pos (zero_lt_iff.2 hv0) k)]`. Use `htv.trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← WithZero.exp_nsmul]`.

Use `congr 1`. Simplify using the standard rewrite rules. Use `_ ≤ v.intValuation π ^ k := pow_le_pow_left₀ zero_le' hlow k`. Rewrite using `[div_mul_cancel₀ _ (pow_ne_zero k hπF)]`.
-/
theorem exists_int_mul_unif_pow (v : HeightOneSpectrum (𝓞 F)) {π : 𝓞 F} (hπ : π ∈ v.asIdeal)
    (hπ2 : π ∉ v.asIdeal ^ 2) {k : ℕ} {t : 𝓞 F} (ht : t ∈ v.asIdeal ^ k) :
    ∃ b ∈ v.adicCompletionIntegers F, algebraMap F (Fv F v) (t : F) = b * algebraMap F (Fv F v) (π : F) ^ k := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (zero_mem _)
  have hv0 : v.intValuation π ≠ 0 := v.intValuation_ne_zero π hπ0
  have hπF : algebraMap F (Fv F v) (π : F) ≠ 0 := by
    intro h
    apply hπ0
    have := (map_eq_zero_iff (algebraMap F (Fv F v)) (algebraMap F (Fv F v)).injective).1 h
    exact_mod_cast this
  have hlow : WithZero.exp (-1 : ℤ) ≤ v.intValuation π := by
    have h2 : ¬ v.intValuation π ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
      hπ2 ((v.intValuation_le_pow_iff_mem π 2).1 h)
    rw [← WithZero.exp_log hv0] at h2 ⊢
    rw [WithZero.exp_le_exp]
    rw [WithZero.exp_le_exp] at h2
    push_cast at h2
    omega
  have htv : v.intValuation t ≤ WithZero.exp (-(k : ℤ)) := (v.intValuation_le_pow_iff_mem t k).2 ht
  refine ⟨algebraMap F (Fv F v) (t : F) / algebraMap F (Fv F v) (π : F) ^ k, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, map_pow]
    change Valued.v ((t : F) : v.adicCompletion F) / Valued.v ((π : F) : v.adicCompletion F) ^ k ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    rw [div_le_one₀ (pow_pos (zero_lt_iff.2 hv0) k)]
    refine htv.trans ?_
    calc WithZero.exp (-(k : ℤ)) = WithZero.exp (-1 : ℤ) ^ k := by
          rw [← WithZero.exp_nsmul]; congr 1; simp
      _ ≤ v.intValuation π ^ k := pow_le_pow_left₀ zero_le' hlow k
  · rw [div_mul_cancel₀ _ (pow_ne_zero k hπF)]

end CompK

section CompKMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.tmul_pow, one_pow]`.
-/
theorem unif_tmul_pow (v : HeightOneSpectrum (𝓞 F)) (π : 𝓞 F) (k : ℕ) :
    ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k = (1 : Fv F v) ⊗ₜ[F] (algebraMap F E (π : F) ^ k) := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow]

/- English proof (translation)
Rewrite using `[unif_tmul_pow, ← map_pow (algebraMap F E), ← map_pow (algebraMap F (Fv F v))]`. Use function extensionality and compare the values at `j`. Rewrite using `[Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]`.
-/
theorem unif_pow_smul_gen (v : HeightOneSpectrum (𝓞 F)) (π : 𝓞 F) (k : ℕ) (b : Fv F v) (x : Fin n → E) :
    ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k • (fun j => b ⊗ₜ[F] x j) =
      fun j => (b * algebraMap F (Fv F v) (π : F) ^ k) ⊗ₜ[F] x j := by
  rw [unif_tmul_pow, ← map_pow (algebraMap F E), ← map_pow (algebraMap F (Fv F v))]
  funext j
  rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def,
    mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[TensorProduct.tmul_add]`.
-/
theorem gen_add (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (x x' : Fin n → E) :
    (fun j => a ⊗ₜ[F] (x + x') j) = (fun j => a ⊗ₜ[F] x j) + fun j => a ⊗ₜ[F] x' j := by
  funext j
  simp [TensorProduct.tmul_add]

/- English proof (translation)
Use `set I : Ideal (𝓞 E) := (v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E)) with hI`. Use `set T : AddSubgroup (Fin n → Fv F v ⊗[F] E) := (compLat v (Λ : Set (Fin n → E))).map (DistribMulAction.toAddMonoidHom _ (((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k)) with hT`. Establish `memT : ∀ z ∈ compLat v (Λ : Set (Fin n → E)), ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k • z ∈ T` using `fun z hz => ⟨z, hz, rfl⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

It suffices to establish `h : compK Λ v k ≤ T by`. Take `⟨z, hz, rfl⟩` from `h hy`. Conclude with `⟨z, hz, rfl⟩`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, hx, rfl⟩`.

Establish `key : ∀ i ∈ I, ∀ l ∈ Λ, ∀ a ∈ (v.adicCompletionIntegers F : Set (Fv F v)), (fun j => a ⊗ₜ[F] (i • l) j) ∈ T`. Introduce `i hi`. Proceed by induction on `hi using Submodule.span_induction with`. Consider the case `mem i hi`. Take `⟨t, ht, rfl⟩` from `hi`.

Introduce `l hl a ha`. Take `⟨b, hb, htb⟩` from `exists_int_mul_unif_pow v hπ hπ2 ht`. Establish `e : (fun j => a ⊗ₜ[F] (algebraMap (𝓞 F) (𝓞 E) t • l) j) = ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k • (fun j => (a * b) ⊗ₜ[F] l j)`. Rewrite using `[unif_pow_smul_gen]`. Use function extensionality and compare the values at `j`.

Establish `: (algebraMap (𝓞 F) (𝓞 E) t • l) j = (t : F) • l j`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[this, ← TensorProduct.smul_tmul, Algebra.smul_def, htb, mul_comm, mul_assoc]`. Rewrite using `[e]`.

Conclude with `memT _ (AddSubgroup.subset_closure ⟨a * b, mul_mem ha hb, l, hl, rfl⟩)`. Consider the case `zero`. Introduce `l _ a _`. Establish `: (fun j => a ⊗ₜ[F] ((0 : 𝓞 E) • l) j) = 0`. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add i i' _ _ h1 h2`. Introduce `l hl a ha`.

Rewrite using `[add_smul, gen_add]`. Conclude with `add_mem (h1 l hl a ha) (h2 l hl a ha)`. Consider the case `smul c i _ h`. Introduce `l hl a ha`. Rewrite using `[smul_eq_mul, mul_comm, mul_smul]`.

Conclude with `h (c • l) (Λ.smul_mem c hl) a ha`. Proceed by induction on `hx using Submodule.smul_induction_on' with`. Consider the case `smul i hi l hl => exact key i hi l hl a ha`. Consider the case `add x hx x' hx' h1 h2`. Rewrite using `[gen_add]`.

Conclude with `add_mem h1 h2`. Introduce and unpack `⟨z, hz, rfl⟩`. Establish `hi : algebraMap (𝓞 F) (𝓞 E) (π ^ k) ∈ I` using `Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hπ k)`. Establish `e : ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k = (1 : Fv F v) ⊗ₜ[F] ((algebraMap (𝓞 F) (𝓞 E) (π ^ k) : 𝓞 E) : E)`. Rewrite using `[unif_tmul_pow]`.

Use `congr 1`. Use `show _ = algebraMap F E ((π ^ k : 𝓞 F) : F)`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `tmul_smul_mem_genLat (Fv F v) _ Λ I hi hz`.
-/
theorem mem_compK_iff (Λ : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (π : 𝓞 F)
    (hπ : π ∈ v.asIdeal) (hπ2 : π ∉ v.asIdeal ^ 2) (k : ℕ) (y : Fin n → Fv F v ⊗[F] E) :
    y ∈ compK Λ v k ↔ ∃ z ∈ compLat v (Λ : Set (Fin n → E)),
      y = ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k • z := by
  set I : Ideal (𝓞 E) := (v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E)) with hI
  set T : AddSubgroup (Fin n → Fv F v ⊗[F] E) := (compLat v (Λ : Set (Fin n → E))).map
    (DistribMulAction.toAddMonoidHom _ (((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k)) with hT
  have memT : ∀ z ∈ compLat v (Λ : Set (Fin n → E)),
      ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k • z ∈ T := fun z hz => ⟨z, hz, rfl⟩
  constructor
  · intro hy
    suffices h : compK Λ v k ≤ T by
      obtain ⟨z, hz, rfl⟩ := h hy
      exact ⟨z, hz, rfl⟩
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    have key : ∀ i ∈ I, ∀ l ∈ Λ, ∀ a ∈ (v.adicCompletionIntegers F : Set (Fv F v)),
        (fun j => a ⊗ₜ[F] (i • l) j) ∈ T := by
      intro i hi
      induction hi using Submodule.span_induction with
      | mem i hi =>
        obtain ⟨t, ht, rfl⟩ := hi
        intro l hl a ha
        obtain ⟨b, hb, htb⟩ := exists_int_mul_unif_pow v hπ hπ2 ht
        have e : (fun j => a ⊗ₜ[F] (algebraMap (𝓞 F) (𝓞 E) t • l) j) =
            ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k • (fun j => (a * b) ⊗ₜ[F] l j) := by
          rw [unif_pow_smul_gen]
          funext j
          have : (algebraMap (𝓞 F) (𝓞 E) t • l) j = (t : F) • l j := by
            rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
            rfl
          rw [this, ← TensorProduct.smul_tmul, Algebra.smul_def, htb, mul_comm, mul_assoc]
        rw [e]
        exact memT _ (AddSubgroup.subset_closure ⟨a * b, mul_mem ha hb, l, hl, rfl⟩)
      | zero =>
        intro l _ a _
        have : (fun j => a ⊗ₜ[F] ((0 : 𝓞 E) • l) j) = 0 := by
          funext j
          simp
        rw [this]
        exact zero_mem _
      | add i i' _ _ h1 h2 =>
        intro l hl a ha
        rw [add_smul, gen_add]
        exact add_mem (h1 l hl a ha) (h2 l hl a ha)
      | smul c i _ h =>
        intro l hl a ha
        rw [smul_eq_mul, mul_comm, mul_smul]
        exact h (c • l) (Λ.smul_mem c hl) a ha
    induction hx using Submodule.smul_induction_on' with
    | smul i hi l hl => exact key i hi l hl a ha
    | add x hx x' hx' h1 h2 =>
      rw [gen_add]
      exact add_mem h1 h2
  · rintro ⟨z, hz, rfl⟩
    have hi : algebraMap (𝓞 F) (𝓞 E) (π ^ k) ∈ I := Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hπ k)
    have e : ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k =
        (1 : Fv F v) ⊗ₜ[F] ((algebraMap (𝓞 F) (𝓞 E) (π ^ k) : 𝓞 E) : E) := by
      rw [unif_tmul_pow]
      congr 1
      show _ = algebraMap F E ((π ^ k : 𝓞 F) : F)
      push_cast
      rfl
    rw [e]
    exact tmul_smul_mem_genLat (Fv F v) _ Λ I hi hz

end CompKMain

end GlobalTheory.TamCnt
