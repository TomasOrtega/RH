import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES

open GlobalTheory.KroneckerCongruence in

/- English proof (translation)
Introduce `Ω _ _ _ ε X M q hM hq V s hFr f hf hfV`. Take `⟨hqV, hs⟩` from `hFr`. Establish `hε : Function.Injective ε` using `ε.injective`. Use `haveI : Fact q.Prime := ⟨hq⟩`. Establish `hq0 : (q : ℚ) ≠ 0` using `by exact_mod_cast hq.ne_zero`.

Use `set ρ := IsLocalRing.residue V with hρ_def`. Establish `hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1` using `fun x => by`. Rewrite using `[hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]`. Use `haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by`. Establish `: ρ (q : V) = 0` using `(hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hqV)`.

Simplify using `using this)`. Establish `hfrob : ∀ x : V, ρ ⟨s x, (hs x x.2).1⟩ = ρ x ^ q`. Introduce `x`. Rewrite using `[← sub_eq_zero, ← map_pow, ← map_sub, hρ0]`. Simplify using `using (hs x x.2).2.2`.

Use `set c := X.exp f with hc`. Establish `hdet : ∀ j : ℕ, 0 < (!![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det`. Introduce `j`. Simplify using `[Matrix.det_fin_two]`. Conclude with `hq.pos` after adjusting the coercions.

Establish `hFj : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t = eOm ε (t * j * M) * c.coeff (t * q)`. Introduce `j t`. Establish `h` using `X.exp_upper (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) (by rw [ent_toGQ _ (hdet j)]; simp) f (t * q)`. Rewrite `h` using `[ent_toGQ _ (hdet j), ent_toGQ _ (hdet j), ent_toGQ _ (hdet j)]`. Simplify using `at h`.

Apply the tactic sequence `convert h using 2 <;> first | field_simp | (congr 1; field_simp)`. Establish `hw : ∀ (j : ℕ) (t : ℚ), c.coeff (t * q) ≠ 0 → ∃ h : eOm ε (t * j * M) ∈ V, ρ ⟨_, h⟩ = 1`. Introduce `j t ht`. Establish `h1 : eOm ε (t * j * M) ^ q = 1`. Rewrite using `[← eOm_mul_nat hε, show (q : ℚ) * (t * j * M) = j * (t * q * M) by ring, eOm_mul_nat hε, eOm_level X M f hf _ ht, one_pow]`.

Establish `hmem : eOm ε (t * j * M) ∈ V` using `mem_of_pow_eq_one V hq.ne_zero h1`. Use `⟨hmem, ?_⟩` and prove the remaining obligations. Establish `h2 : (⟨_, hmem⟩ : V) ^ q = 1` using `Subtype.ext (by simpa using h1)`. Establish `h3 : (ρ ⟨_, hmem⟩ - 1) ^ q = 0` using `by rw [sub_pow_char, ← map_pow, h2, map_one, one_pow, sub_self]`. Conclude with `sub_eq_zero.1 (pow_eq_zero_iff hq.ne_zero |>.1 h3)`.

Establish `memF : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t ∈ V`. Introduce `j t`. Rewrite using `[hFj]`. Distinguish the cases in `h0 : c.coeff (t * q) = 0`. Rewrite using `[h0, mul_zero]`.

Conclude with `zero_mem V`. Conclude with `mul_mem (hw j t h0).1 (hfV _)`. Establish `redF : ∀ (j : ℕ) (t : ℚ), ρ ⟨_, memF j t⟩ = ρ ⟨_, hfV (t * q)⟩`. Introduce `j t`. Distinguish the cases in `h0 : c.coeff (t * q) = 0`.

Conclude with `congrArg ρ (Subtype.ext (by simp only; rw [hFj, h0, mul_zero]))`. Take `⟨hm, h1⟩` from `hw j t h0`. Establish `e : (⟨_, memF j t⟩ : V) = ⟨_, hm⟩ * ⟨_, hfV (t * q)⟩` using `Subtype.ext (by simp only [MulMemClass.mk_mul_mk]; rw [hFj])`. Rewrite using `[e, map_mul, h1, one_mul]`. Establish `memC : ∀ t : ℚ, (X.exp (X.gal s f)).coeff t ∈ V`.

Introduce `t`. Rewrite using `[X.gal_exp]`. Conclude with `(hs _ (hfV t)).1`. Use `set LF : ℕ → HahnSeries ℚ V := fun j => liftV V _ (memF j) with hLF`. Use `set LC := liftV V _ memC with hLC`.

Establish `h1 : ∀ j, hahnSeriesCoeffRingHomMap ρ (LF j) = hahnSeriesCoeffRingHomMap ρ (LF 0)`. Introduce `j`. Use extensionality with `t`. Rewrite using `[hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]`. Conclude with `(redF j t).trans (redF 0 t).symm`.

Establish `h2 : hahnSeriesCoeffRingHomMap ρ (LF 0) ^ q = hahnSeriesCoeffRingHomMap ρ LC`. Use extensionality with `t`. Rewrite using `[coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]`. Use `show ρ ⟨_, memF 0 (t / q)⟩ ^ q = ρ ⟨_, memC t⟩`. Rewrite using `[redF 0 (t / q), ← hfrob]`.

Conclude with `congrArg ρ (Subtype.ext (by simp only; rw [X.gal_exp, div_mul_cancel₀ t hq0]))`. Establish `hexp : X.exp ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f) - X.gal s f) = hahnSeriesCoeffRingHomMap V.subtype ((∏ j ∈ Finset.range q, LF j) - LC)`. Simplify using `only [map_sub, map_prod, hLF, hLC, map_liftV]`. Establish `hW : hahnSeriesCoeffRingHomMap ρ ((∏ j ∈ Finset.range q, LF j) - LC) = 0`. Rewrite using `[map_sub, map_prod, Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const, Finset.card_range, h2, sub_self]`.

Introduce `r`. Unfold `Nq`. Rewrite using `[hexp, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]`. Use `(hρ0 (((∏ j ∈ Finset.range q, LF j) - LC).coeff r)).1 ?_` and prove the remaining obligations. Rewrite using `[← hahnSeriesCoeffRingHomMap_coeff, hW]`.

Both sides reduce to the same expression.
-/
theorem nq_sub_gal_small : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M q : ℕ), 0 < M → q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s →
    ∀ a : X.K, Lev X M a → IntC X V a → SmallC X V (Nq X M q a - X.gal s a) := by
  intro Ω _ _ _ ε X M q hM hq V s hFr f hf hfV
  obtain ⟨hqV, hs⟩ := hFr
  have hε : Function.Injective ε := ε.injective
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hqV)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs x x.2).2.2
  set c := X.exp f with hc
  have hdet : ∀ j : ℕ, 0 < (!![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    intro j; simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hFj : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t =
      eOm ε (t * j * M) * c.coeff (t * q) := by
    intro j t
    have h := X.exp_upper (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) (by rw [ent_toGQ _ (hdet j)]; simp) f (t * q)
    rw [ent_toGQ _ (hdet j), ent_toGQ _ (hdet j), ent_toGQ _ (hdet j)] at h
    simp at h
    convert h using 2 <;> first | field_simp | (congr 1; field_simp)
  have hw : ∀ (j : ℕ) (t : ℚ), c.coeff (t * q) ≠ 0 → ∃ h : eOm ε (t * j * M) ∈ V, ρ ⟨_, h⟩ = 1 := by
    intro j t ht
    have h1 : eOm ε (t * j * M) ^ q = 1 := by
      rw [← eOm_mul_nat hε, show (q : ℚ) * (t * j * M) = j * (t * q * M) by ring, eOm_mul_nat hε,
        eOm_level X M f hf _ ht, one_pow]
    have hmem : eOm ε (t * j * M) ∈ V := mem_of_pow_eq_one V hq.ne_zero h1
    refine ⟨hmem, ?_⟩
    have h2 : (⟨_, hmem⟩ : V) ^ q = 1 := Subtype.ext (by simpa using h1)
    have h3 : (ρ ⟨_, hmem⟩ - 1) ^ q = 0 := by rw [sub_pow_char, ← map_pow, h2, map_one, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff hq.ne_zero |>.1 h3)
  have memF : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t ∈ V := by
    intro j t
    rw [hFj]
    by_cases h0 : c.coeff (t * q) = 0
    · rw [h0, mul_zero]; exact zero_mem V
    · exact mul_mem (hw j t h0).1 (hfV _)
  have redF : ∀ (j : ℕ) (t : ℚ), ρ ⟨_, memF j t⟩ = ρ ⟨_, hfV (t * q)⟩ := by
    intro j t
    by_cases h0 : c.coeff (t * q) = 0
    · exact congrArg ρ (Subtype.ext (by simp only; rw [hFj, h0, mul_zero]))
    · obtain ⟨hm, h1⟩ := hw j t h0
      have e : (⟨_, memF j t⟩ : V) = ⟨_, hm⟩ * ⟨_, hfV (t * q)⟩ :=
        Subtype.ext (by simp only [MulMemClass.mk_mul_mk]; rw [hFj])
      rw [e, map_mul, h1, one_mul]
  have memC : ∀ t : ℚ, (X.exp (X.gal s f)).coeff t ∈ V := by
    intro t; rw [X.gal_exp]; exact (hs _ (hfV t)).1
  set LF : ℕ → HahnSeries ℚ V := fun j => liftV V _ (memF j) with hLF
  set LC := liftV V _ memC with hLC
  have h1 : ∀ j, hahnSeriesCoeffRingHomMap ρ (LF j) = hahnSeriesCoeffRingHomMap ρ (LF 0) := by
    intro j; ext t; rw [hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]; exact (redF j t).trans (redF 0 t).symm
  have h2 : hahnSeriesCoeffRingHomMap ρ (LF 0) ^ q = hahnSeriesCoeffRingHomMap ρ LC := by
    ext t
    rw [coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]
    show ρ ⟨_, memF 0 (t / q)⟩ ^ q = ρ ⟨_, memC t⟩
    rw [redF 0 (t / q), ← hfrob]
    exact congrArg ρ (Subtype.ext (by simp only; rw [X.gal_exp, div_mul_cancel₀ t hq0]))
  have hexp : X.exp ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f) - X.gal s f) =
      hahnSeriesCoeffRingHomMap V.subtype ((∏ j ∈ Finset.range q, LF j) - LC) := by
    simp only [map_sub, map_prod, hLF, hLC, map_liftV]
  have hW : hahnSeriesCoeffRingHomMap ρ ((∏ j ∈ Finset.range q, LF j) - LC) = 0 := by
    rw [map_sub, map_prod, Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const, Finset.card_range, h2, sub_self]
  intro r
  unfold Nq
  rw [hexp, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 (((∏ j ∈ Finset.range q, LF j) - LC).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, hW]
  rfl

end GlobalTheory.KZ.ES
