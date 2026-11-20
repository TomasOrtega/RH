import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `: ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap', Padic.norm_p]`.
-/
theorem norm_natCast_l : ‖((l : ℕ) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  have : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]

/- English proof (translation)
Take `⟨-, -, -, -, -, he0, -, hev, -⟩` from `UpperTheory.V.Base.dvrFacts l c.O`. Establish `hl0 : ((l : ℕ) : c.O) ≠ 0`. Introduce `h`. Establish `h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0` using `by rw [h]; rfl`. Establish `: ((l : ℕ) : PadicAlgCl l) = 0` using `by simpa using h'`.

Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this`. Establish `htop : UpperTheory.V.Base.eO l c.O ≠ ⊤`. Rewrite using `[hev, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]`. Conclude with `hl0`. Establish `: (UpperTheory.V.Base.eO l c.O).toNat ≠ 0`.

Introduce `h`. Conclude with `he0 ((ENat.toNat_eq_zero).1 h |>.resolve_right htop)`. Use linear arithmetic over natural numbers and integers.
-/
theorem eO_toNat_pos (c : Coef l) : 1 ≤ (UpperTheory.V.Base.eO l c.O).toNat := by
  obtain ⟨-, -, -, -, -, he0, -, hev, -⟩ := UpperTheory.V.Base.dvrFacts l c.O
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have htop : UpperTheory.V.Base.eO l c.O ≠ ⊤ := by
    rw [hev, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hl0
  have : (UpperTheory.V.Base.eO l c.O).toNat ≠ 0 := by
    intro h; exact he0 ((ENat.toNat_eq_zero).1 h |>.resolve_right htop)
  omega

/- English proof (translation)
Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`. Establish `h` using `UpperTheory.V.Base.normO l c.O y hy`. Establish `he` using `eO_toNat_pos c`. Establish `hl : (0 : ℝ) ≤ (l : ℝ)⁻¹` using `by positivity`.

Establish `hl1 : (l : ℝ)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)`. Establish `: ‖(y : PadicAlgCl l)‖ ^ (UpperTheory.V.Base.eO l c.O).toNat ≤ 1`. Rewrite using `[h]`. Conclude with `pow_le_one₀ hl hl1`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 this`.
-/
theorem norm_le_one (c : Coef l) (y : c.O) : ‖(y : PadicAlgCl l)‖ ≤ 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have h := UpperTheory.V.Base.normO l c.O y hy
  have he := eO_toNat_pos c
  have hl : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  have hl1 : (l : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
  have : ‖(y : PadicAlgCl l)‖ ^ (UpperTheory.V.Base.eO l c.O).toNat ≤ 1 := by
    rw [h]; exact pow_le_one₀ hl hl1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 this

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`. Conclude with `dvd_zero _`.

Take `⟨-, -, -, -, -, -, -, hev, -⟩` from `UpperTheory.V.Base.dvrFacts l c.O`. Establish `h` using `UpperTheory.V.Base.normO l c.O x hx0`. Establish `he` using `eO_toNat_pos c`. Use `set e := (UpperTheory.V.Base.eO l c.O).toNat with he_def`. Use `set v := (IsDiscreteValuationRing.addVal c.O x).toNat with hv_def`.

Establish `hq0 : (0 : ℝ) < (l : ℝ)⁻¹`. Use `(Fact.out : l.Prime).pos` as an intermediate fact. Check the signs of the components of the expression. Establish `hq1 : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`. Rewrite `hx` using `[norm_pow, norm_natCast_l]`.

Establish `h2 : ‖(x : PadicAlgCl l)‖ ^ e ≤ ((l : ℝ)⁻¹ ^ k) ^ e` using `pow_le_pow_left₀ (norm_nonneg _) hx e`. Rewrite `h2` using `[h, ← pow_mul]`. Establish `h3 : k * e ≤ v` using `(pow_le_pow_iff_right_of_lt_one₀ hq0 hq1).1 h2`. Establish `hl0 : ((l : ℕ) : c.O) ≠ 0`. Introduce `h0`.

Establish `h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0` using `by rw [h0]; rfl`. Establish `: ((l : ℕ) : PadicAlgCl l) = 0` using `by simpa using h'`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this`. Establish `htl : IsDiscreteValuationRing.addVal c.O ((l : ℕ) : c.O) ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]`.

Conclude with `hl0`. Establish `htx : IsDiscreteValuationRing.addVal c.O x ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]`. Conclude with `hx0`. Rewrite using `[← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow, ← ENat.coe_toNat htl, ← ENat.coe_toNat htx, ← hev, ← he_def, ← hv_def]`.

Rewrite using `[nsmul_eq_mul]`. Conclude with `h3` after adjusting the coercions. Introduce and unpack `⟨y, rfl⟩`. Establish `: (((l : ℕ) : c.O) ^ k * y : c.O) = ((l : ℕ) : PadicAlgCl l) ^ k * (y : PadicAlgCl l)` using `by simp`. Rewrite using `[this, norm_mul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_le_iff_dvd (c : Coef l) (x : c.O) (k : ℕ) :
    ‖(x : PadicAlgCl l)‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ k‖ ↔ ((l : ℕ) : c.O) ^ k ∣ x := by
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact dvd_zero _
    obtain ⟨-, -, -, -, -, -, -, hev, -⟩ := UpperTheory.V.Base.dvrFacts l c.O
    have h := UpperTheory.V.Base.normO l c.O x hx0
    have he := eO_toNat_pos c
    set e := (UpperTheory.V.Base.eO l c.O).toNat with he_def
    set v := (IsDiscreteValuationRing.addVal c.O x).toNat with hv_def
    have hq0 : (0 : ℝ) < (l : ℝ)⁻¹ := by
      have := (Fact.out : l.Prime).pos; positivity
    have hq1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
    rw [norm_pow, norm_natCast_l] at hx
    have h2 : ‖(x : PadicAlgCl l)‖ ^ e ≤ ((l : ℝ)⁻¹ ^ k) ^ e := pow_le_pow_left₀ (norm_nonneg _) hx e
    rw [h, ← pow_mul] at h2
    have h3 : k * e ≤ v := (pow_le_pow_iff_right_of_lt_one₀ hq0 hq1).1 h2
    have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
      intro h0
      have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h0]; rfl
      have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
      exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
    have htl : IsDiscreteValuationRing.addVal c.O ((l : ℕ) : c.O) ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hl0
    have htx : IsDiscreteValuationRing.addVal c.O x ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hx0
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      ← ENat.coe_toNat htl, ← ENat.coe_toNat htx, ← hev, ← he_def, ← hv_def]
    rw [nsmul_eq_mul]
    exact_mod_cast h3
  · rintro ⟨y, rfl⟩
    have : (((l : ℕ) : c.O) ^ k * y : c.O) = ((l : ℕ) : PadicAlgCl l) ^ k * (y : PadicAlgCl l) := by simp
    rw [this, norm_mul]
    calc _ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ k‖ * 1 := mul_le_mul_of_nonneg_left (norm_le_one c y) (norm_nonneg _)
      _ = _ := mul_one _

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, m = k + 2` from `⟨m - 2, by omega⟩`. Proceed by induction on `N with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ N ih`. Take `⟨C, hC⟩` from `ih`.

Use `⟨((N : R) * t ^ k) • (B * B) + C + t ^ (k + 2) • (C * B), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, hC]`. Simplify using `only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one, one_mul, smul_add]`. Use `push_cast`. Use `module`.
-/
theorem pow_expand {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (t : R) (m : ℕ) (hm : 2 ≤ m) (B : Matrix n n R) (N : ℕ) :
    ∃ C : Matrix n n R, (1 + t ^ m • B) ^ N = 1 + ((N : R) * t ^ m) • B + t ^ (m + 2) • C := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨((N : R) * t ^ k) • (B * B) + C + t ^ (k + 2) • (C * B), ?_⟩
    rw [pow_succ, hC]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one, one_mul, smul_add]
    push_cast
    module

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

def intRep (c : Coef l) {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) (PadicAlgCl l))
    (hint : ∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) i j ∈ c.O) :
    Γ →* Matrix (Fin 2) (Fin 2) c.O where
  toFun g := Matrix.of fun i j => ⟨_, hint g i j⟩
  map_one' := by
    ext i j
    simp only [map_one, Units.val_one, Matrix.of_apply]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  map_mul' g h := by
    apply Matrix.map_injective (f := (c.O.val : c.O →+* PadicAlgCl l)) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul]
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, Units.val_mul]
    rfl

/- English proof (translation)
Simplify using `only [Matrix.sub_apply]`. Rewrite using `[Subalgebra.coe_sub]`. Use `congr 1`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem intRep_map (c : Coef l) {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) (PadicAlgCl l))
    (hint : ∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) i j ∈ c.O) (g : Γ) (i j : Fin 2) :
    ((((r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) - 1) i j) : PadicAlgCl l) =
      ((((intRep c r hint g) - 1) i j : c.O) : PadicAlgCl l) := by
  simp only [Matrix.sub_apply]
  rw [Subalgebra.coe_sub]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [intRep_map c r hint, norm_le_iff_dvd]`. Prove the components needed by the constructor for the conclusion. Introduce `h choose B hB using h`. Use `⟨Matrix.of B, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Use `hB i j` as an intermediate fact. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← this, Matrix.sub_apply]`. Put the polynomial expressions in normal form. Introduce and unpack `⟨B, hB⟩ i j`. Conclude with `⟨B i j, by rw [hB]; simp⟩`.
-/
theorem level_iff (c : Coef l) {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) (PadicAlgCl l))
    (hint : ∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) i j ∈ c.O) (g : Γ) (k : ℕ) :
    (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) - 1) i j‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ k‖) ↔
      ∃ B : Matrix (Fin 2) (Fin 2) c.O, intRep c r hint g = 1 + (((l : ℕ) : c.O) ^ k) • B := by
  simp only [intRep_map c r hint, norm_le_iff_dvd]
  constructor
  · intro h
    choose B hB using h
    refine ⟨Matrix.of B, ?_⟩
    ext i j
    have := hB i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← this, Matrix.sub_apply]
    ring_nf
  · rintro ⟨B, hB⟩ i j
    exact ⟨B i j, by rw [hB]; simp⟩

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Take `⟨C, hC⟩` from `pow_expand ((l : ℕ) : c.O) m hm B l`. Use `⟨B + ((l : ℕ) : c.O) • C, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hA, hC, smul_add, smul_smul, show ((l : ℕ) : c.O) * ((l : ℕ) : c.O) ^ m = ((l : ℕ) : c.O) ^ (m + 1) by ring, show ((l : ℕ) : c.O) ^ (m + 2) = ((l : ℕ) : c.O) ^ (m + 1) * ((l : ℕ) : c.O) by ring]`. Normalize the expressions using the abelian group laws. Use extensionality with `i j`.

Establish `h0 : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)}) ((l : ℕ) : c.O) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`. Simplify using `[Matrix.map_apply, h0]`.
-/
theorem pow_step (c : Coef l) (A B : Matrix (Fin 2) (Fin 2) c.O) (m : ℕ) (hm : 2 ≤ m)
    (hA : A = 1 + (((l : ℕ) : c.O) ^ m) • B) :
    ∃ B' : Matrix (Fin 2) (Fin 2) c.O, A ^ l = 1 + (((l : ℕ) : c.O) ^ (m + 1)) • B' ∧
      B'.map (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)})) =
        B.map (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)})) := by
  obtain ⟨C, hC⟩ := pow_expand ((l : ℕ) : c.O) m hm B l
  refine ⟨B + ((l : ℕ) : c.O) • C, ?_, ?_⟩
  · rw [hA, hC, smul_add, smul_smul, show ((l : ℕ) : c.O) * ((l : ℕ) : c.O) ^ m = ((l : ℕ) : c.O) ^ (m + 1) by ring,
      show ((l : ℕ) : c.O) ^ (m + 2) = ((l : ℕ) : c.O) ^ (m + 1) * ((l : ℕ) : c.O) by ring]
    abel
  · ext i j
    have h0 : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)}) ((l : ℕ) : c.O) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    simp [Matrix.map_apply, h0]

def img (c : Coef l) {Γ : Type} [Group Γ] (ρ : Γ →* Matrix (Fin 2) (Fin 2) c.O) (m : ℕ) :
    Set (Matrix (Fin 2) (Fin 2) (c.O ⧸ Ideal.span {((l : ℕ) : c.O)})) :=
  {X | ∃ g B, ρ g = 1 + (((l : ℕ) : c.O) ^ m) • B ∧ B.map (Ideal.Quotient.mk _) = X}

/- English proof (translation)
Introduce and unpack `X ⟨g, B, hg, rfl⟩`. Take `⟨B', h1, h2⟩` from `pow_step c (ρ g) B m hm hg`. Conclude with `⟨g ^ l, B', by rw [map_pow, h1], h2⟩`.
-/
theorem img_mono (c : Coef l) {Γ : Type} [Group Γ] (ρ : Γ →* Matrix (Fin 2) (Fin 2) c.O) (m : ℕ) (hm : 2 ≤ m) :
    img c ρ m ⊆ img c ρ (m + 1) := by
  rintro X ⟨g, B, hg, rfl⟩
  obtain ⟨B', h1, h2⟩ := pow_step c (ρ g) B m hm hg
  exact ⟨g ^ l, B', by rw [map_pow, h1], h2⟩

/- English proof (translation)
Introduce `l _ c Γ _ r hint`. Use `set ρ := intRep c r hint with hρ`. Establish `hl0 : ((l : ℕ) : c.O) ≠ 0`. Introduce `h0`. Establish `h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0` using `by rw [h0]; rfl`.

Establish `: ((l : ℕ) : PadicAlgCl l) = 0` using `by simpa using h'`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this`. Use `haveI : Finite (c.O ⧸ Ideal.span {((l : ℕ) : c.O)}) := (UpperTheory.V.X.So.levFacts l c.O ((l : ℕ) : c.O) hl0 _ ⟨LinearEquiv.refl _ _⟩).1`. Use `haveI : Finite (Matrix (Fin 2) (Fin 2) (c.O ⧸ Ideal.span {((l : ℕ) : c.O)})) := inferInstanceAs (Finite (Fin 2 → Fin 2 → _))`. Set `F : ℕ →o Set (Matrix (Fin 2) (Fin 2) (c.O ⧸ Ideal.span {((l : ℕ) : c.O)}))` to `⟨fun n => img c ρ (n + 2), monotone_nat_of_le_succ fun n => img_mono c ρ (n + 2) (by omega)⟩`.

Take `⟨n, hn⟩` from `WellFoundedGT.monotone_chain_condition F`. Use `⟨n + 2, fun m hm g hg => ?_⟩` and prove the remaining obligations. Establish `hS : img c ρ (m + 1) ⊆ img c ρ m`. Establish `e1` using `hn (m - 2) (by omega)`. Establish `e2` using `hn (m - 1) (by omega)`.

Establish `h1 : F (m - 2) = img c ρ m` using `by show img c ρ (m - 2 + 2) = _; congr 1; omega`. Establish `h2 : F (m - 1) = img c ρ (m + 1)` using `by show img c ρ (m - 1 + 2) = _; congr 1; omega`. Rewrite using `[← h1, ← h2, ← e1, ← e2]`. Take `⟨B, hB⟩` from `(level_iff c r hint g (m + 1)).1 hg`. Take `⟨h, B₁, hh, hB₁⟩` from `hS ⟨g, B, hB, rfl⟩`.

Take `⟨B₂, hh2, hB₂⟩` from `pow_step c (ρ h) B₁ m (by omega) hh`. Establish `hD : ∀ i j, ∃ d : c.O, B i j - B₂ i j = ((l : ℕ) : c.O) * d`. Introduce `i j`. Use `congrFun (congrFun (hB₁.symm.trans hB₂.symm) i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`.

Take `⟨d, hd⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 this)`. Conclude with `⟨d, by rw [← hd]; ring⟩`. Use `choose D hDD using hD`. Use `⟨h, (h ^ l)⁻¹ * g, (level_iff c r hint h m).2 ⟨B₁, hh⟩, (level_iff c r hint _ (m + 2)).2 ⟨ρ (h ^ l)⁻¹ * Matrix.of D, ?_⟩, (mul_inv_cancel_left _ _).symm⟩` and prove the remaining obligations. Establish `hBB : B = B₂ + ((l : ℕ) : c.O) • Matrix.of D`.

Use extensionality with `i j`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hDD]`. Put the polynomial expressions in normal form. Establish `hinv : ρ (h ^ l)⁻¹ * ρ (h ^ l) = 1` using `by rw [← map_mul, inv_mul_cancel, map_one]`. Establish `hpow : ρ (h ^ l) = 1 + (((l : ℕ) : c.O) ^ (m + 1)) • B₂` using `by rw [map_pow, hh2]`.

Establish `hg' : ρ g = ρ (h ^ l) + (((l : ℕ) : c.O) ^ (m + 2)) • Matrix.of D`. Rewrite using `[hB, hpow, hBB, smul_add, smul_smul, ← pow_succ]`. Normalize the expressions using the abelian group laws. Rewrite using `[map_mul, hg', mul_add, hinv, Matrix.mul_smul]`.
-/
theorem exists_pow_mul_of_deep_level : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ (m + 1)‖) → ∃ h g' : Γ, (∀ i j, ‖((r h : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) ∧ (∀ i j, ‖((r g' : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ (m + 2)‖) ∧ g = h ^ l * g' := by
  intro l _ c Γ _ r hint
  set ρ := intRep c r hint with hρ
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h0
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h0]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  haveI : Finite (c.O ⧸ Ideal.span {((l : ℕ) : c.O)}) :=
    (UpperTheory.V.X.So.levFacts l c.O ((l : ℕ) : c.O) hl0 _ ⟨LinearEquiv.refl _ _⟩).1
  haveI : Finite (Matrix (Fin 2) (Fin 2) (c.O ⧸ Ideal.span {((l : ℕ) : c.O)})) :=
    inferInstanceAs (Finite (Fin 2 → Fin 2 → _))
  let F : ℕ →o Set (Matrix (Fin 2) (Fin 2) (c.O ⧸ Ideal.span {((l : ℕ) : c.O)})) :=
    ⟨fun n => img c ρ (n + 2), monotone_nat_of_le_succ fun n => img_mono c ρ (n + 2) (by omega)⟩
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition F
  refine ⟨n + 2, fun m hm g hg => ?_⟩
  have hS : img c ρ (m + 1) ⊆ img c ρ m := by
    have e1 := hn (m - 2) (by omega)
    have e2 := hn (m - 1) (by omega)
    have h1 : F (m - 2) = img c ρ m := by
      show img c ρ (m - 2 + 2) = _; congr 1; omega
    have h2 : F (m - 1) = img c ρ (m + 1) := by
      show img c ρ (m - 1 + 2) = _; congr 1; omega
    rw [← h1, ← h2, ← e1, ← e2]
  obtain ⟨B, hB⟩ := (level_iff c r hint g (m + 1)).1 hg
  obtain ⟨h, B₁, hh, hB₁⟩ := hS ⟨g, B, hB, rfl⟩
  obtain ⟨B₂, hh2, hB₂⟩ := pow_step c (ρ h) B₁ m (by omega) hh
  have hD : ∀ i j, ∃ d : c.O, B i j - B₂ i j = ((l : ℕ) : c.O) * d := by
    intro i j
    have := congrFun (congrFun (hB₁.symm.trans hB₂.symm) i) j
    simp only [Matrix.map_apply] at this
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 this)
    exact ⟨d, by rw [← hd]; ring⟩
  choose D hDD using hD
  refine ⟨h, (h ^ l)⁻¹ * g, (level_iff c r hint h m).2 ⟨B₁, hh⟩, (level_iff c r hint _ (m + 2)).2
    ⟨ρ (h ^ l)⁻¹ * Matrix.of D, ?_⟩, (mul_inv_cancel_left _ _).symm⟩
  have hBB : B = B₂ + ((l : ℕ) : c.O) • Matrix.of D := by
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hDD]
    ring_nf
  have hinv : ρ (h ^ l)⁻¹ * ρ (h ^ l) = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hpow : ρ (h ^ l) = 1 + (((l : ℕ) : c.O) ^ (m + 1)) • B₂ := by rw [map_pow, hh2]
  have hg' : ρ g = ρ (h ^ l) + (((l : ℕ) : c.O) ^ (m + 2)) • Matrix.of D := by
    rw [hB, hpow, hBB, smul_add, smul_smul, ← pow_succ]
    abel
  rw [map_mul, hg', mul_add, hinv, Matrix.mul_smul]

end GlobalTheory.DeepLevel
