import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DecompU
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartU
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Mathlib.RingTheory.Teichmuller

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

/- English proof (translation)
Establish `h1 : 1 ≤ Fintype.card (ResidueField O)` using `Fintype.card_pos`. Rewrite using `[Nat.cast_sub h1, FiniteField.cast_card_eq_zero]`. Simplify using the standard rewrite rules.
-/
private theorem card_residueField_sub_one_eq_neg_one {O : Type} [CommRing O] [IsLocalRing O] [Fintype (ResidueField O)] :
    ((Fintype.card (ResidueField O) - 1 : ℕ) : ResidueField O) = -1 := by
  have h1 : 1 ≤ Fintype.card (ResidueField O) := Fintype.card_pos
  rw [Nat.cast_sub h1, FiniteField.cast_card_eq_zero]
  simp

/- English proof (translation)
Take `⟨N, hN⟩ : ∃ N, N = Fintype.card (ResidueField O) - 1` from `⟨_, rfl⟩`. Rewrite `ha`, `hb` using `[← hN]`. Establish `hN0 : N ≠ 0`. Use `Fintype.one_lt_card (α := ResidueField O)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hra : residue O a ≠ 0`. Introduce `h0`. Establish `h` using `congrArg (residue O) ha`. Rewrite `h` using `[map_pow, h0, map_one, zero_pow hN0]`. Conclude with `zero_ne_one h`.

Establish `key` using `geom_sum₂_mul a b N`. Rewrite `key` using `[ha, hb, sub_self]`. Establish `hu : IsUnit (∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i))`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]`. Simplify using `only [map_mul, map_pow, ← hab]`.

Establish `hterm : ∀ i ∈ Finset.range N, residue O a ^ i * residue O a ^ (N - 1 - i) = residue O a ^ (N - 1)`. Introduce `i hi`. Rewrite using `[← pow_add]`. Use `congr 1`. Use `Finset.mem_range.mp hi` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hN, card_residueField_sub_one_eq_neg_one]`. Conclude with `mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero _ hra)`. Conclude with `sub_eq_zero.mp ((hu.mul_right_eq_zero).mp key)`.
-/
private theorem teichmuller_eq_of_residue_eq {O : Type} [CommRing O] [IsLocalRing O] [Fintype (ResidueField O)] (a b : O)
    (ha : a ^ (Fintype.card (ResidueField O) - 1) = 1) (hb : b ^ (Fintype.card (ResidueField O) - 1) = 1)
    (hab : residue O a = residue O b) : a = b := by
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card (ResidueField O) - 1 := ⟨_, rfl⟩
  rw [← hN] at ha hb
  have hN0 : N ≠ 0 := by
    have := Fintype.one_lt_card (α := ResidueField O)
    omega
  have hra : residue O a ≠ 0 := by
    intro h0
    have h := congrArg (residue O) ha
    rw [map_pow, h0, map_one, zero_pow hN0] at h
    exact zero_ne_one h
  have key := geom_sum₂_mul a b N
  rw [ha, hb, sub_self] at key
  have hu : IsUnit (∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_mul, map_pow, ← hab]
    have hterm : ∀ i ∈ Finset.range N,
        residue O a ^ i * residue O a ^ (N - 1 - i) = residue O a ^ (N - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hN, card_residueField_sub_one_eq_neg_one]
    exact mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero _ hra)
  exact sub_eq_zero.mp ((hu.mul_right_eq_zero).mp key)

/- English proof (translation)
Take `⟨N, hN⟩ : ∃ N, N = Fintype.card (ResidueField O) - 1` from `⟨_, rfl⟩`. Rewrite using `[← hN]`. Establish `hN0 : N ≠ 0`. Use `Fintype.one_lt_card (α := ResidueField O)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨a₀, rfl⟩` from `IsLocalRing.residue_surjective u`. Use `haveI := IsAdicComplete.henselianRing O (maximalIdeal O)`. Establish `h1 : eval a₀ (X ^ N - C 1) ∈ maximalIdeal O`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff]`. Simplify using `only [eval_sub, eval_pow, eval_X, eval_C, eval_one, map_sub, map_pow, map_one]`.

Rewrite using `[hN, FiniteField.pow_card_sub_one_eq_one _ hu, sub_self]`. Establish `h2 : IsUnit (Ideal.Quotient.mk (maximalIdeal O) (eval a₀ (derivative (X ^ N - C 1))))`. Express the relevant statement in the definitionally equal form `IsUnit (residue O _)`. Rewrite using `[isUnit_iff_ne_zero]`. Simplify using `only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X, eval_natCast, map_mul, map_pow, map_natCast]`.

Rewrite using `[hN, card_residueField_sub_one_eq_neg_one]`. Conclude with `mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero _ hu)`. Take `⟨a, hroot, hmem⟩` from `HenselianRing.is_henselian (I := maximalIdeal O) (X ^ N - C 1) (monic_X_pow_sub_C 1 hN0) a₀ h1 h2`. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations. Establish `h : eval a (X ^ N - C 1) = 0` using `hroot`.

Simplify using `only [eval_sub, eval_pow, eval_X, eval_C, eval_one] at h`. Conclude with `sub_eq_zero.mp h`. Conclude with `Ideal.Quotient.eq.mpr hmem`.
-/
private theorem exists_teichmuller_lift' {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] (u : ResidueField O) (hu : u ≠ 0) :
    ∃ a : O, a ^ (Fintype.card (ResidueField O) - 1) = 1 ∧ residue O a = u := by
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card (ResidueField O) - 1 := ⟨_, rfl⟩
  rw [← hN]
  have hN0 : N ≠ 0 := by
    have := Fintype.one_lt_card (α := ResidueField O)
    omega
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective u
  haveI := IsAdicComplete.henselianRing O (maximalIdeal O)
  have h1 : eval a₀ (X ^ N - C 1) ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_one, map_sub, map_pow, map_one]
    rw [hN, FiniteField.pow_card_sub_one_eq_one _ hu, sub_self]
  have h2 : IsUnit (Ideal.Quotient.mk (maximalIdeal O) (eval a₀ (derivative (X ^ N - C 1)))) := by
    change IsUnit (residue O _)
    rw [isUnit_iff_ne_zero]
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X,
      eval_natCast, map_mul, map_pow, map_natCast]
    rw [hN, card_residueField_sub_one_eq_neg_one]
    exact mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero _ hu)
  obtain ⟨a, hroot, hmem⟩ := HenselianRing.is_henselian (I := maximalIdeal O) (X ^ N - C 1)
    (monic_X_pow_sub_C 1 hN0) a₀ h1 h2
  refine ⟨a, ?_, ?_⟩
  · have h : eval a (X ^ N - C 1) = 0 := hroot
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_one] at h
    exact sub_eq_zero.mp h
  · exact Ideal.Quotient.eq.mpr hmem

/- English proof (translation)
Use `letI := Fintype.ofFinite (ResidueField O)`. Establish `ex` using `fun (x : ResidueField O) (hx : x ≠ 0) => exists_teichmuller_lift' (O := O) x hx`. Set `f : ResidueField O → O` to `fun x => if hx : x = 0 then 0 else Classical.choose (ex x hx)`. Establish `hf : ∀ x, x ≠ 0 → f x ^ (Fintype.card (ResidueField O) - 1) = 1 ∧ residue O (f x) = x`. Introduce `x hx`.

Simplify using `only [f, dif_neg hx]`. Conclude with `Classical.choose_spec (ex x hx)`. Establish `hf0 : f 0 = 0` using `by simp [f]`. Establish `hres : ∀ x, residue O (f x) = x`. Introduce `x`.

Distinguish the cases in `hx : x = 0`. Rewrite using `[hx, hf0, map_zero]`. Conclude with `(hf x hx).2`. Use `⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hres⟩` and prove the remaining obligations. Apply `teichmuller_eq_of_residue_eq` to reduce the goal to its premises.

Conclude with `(hf 1 one_ne_zero).1`. Conclude with `one_pow _`. Rewrite using `[(hf 1 one_ne_zero).2, map_one]`. Introduce `x y`. Distinguish the cases in `hx : x = 0`.

Simplify using `[hx, hf0]`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy, hf0]`. Apply `teichmuller_eq_of_residue_eq` to reduce the goal to its premises. Conclude with `(hf _ (mul_ne_zero hx hy)).1`.

Rewrite using `[mul_pow, (hf x hx).1, (hf y hy).1, one_mul]`. Rewrite using `[(hf _ (mul_ne_zero hx hy)).2, map_mul, (hf x hx).2, (hf y hy).2]`.
-/
private theorem au_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  letI := Fintype.ofFinite (ResidueField O)
  classical
  have ex := fun (x : ResidueField O) (hx : x ≠ 0) => exists_teichmuller_lift' (O := O) x hx
  let f : ResidueField O → O := fun x => if hx : x = 0 then 0 else Classical.choose (ex x hx)
  have hf : ∀ x, x ≠ 0 → f x ^ (Fintype.card (ResidueField O) - 1) = 1 ∧ residue O (f x) = x := by
    intro x hx
    simp only [f, dif_neg hx]
    exact Classical.choose_spec (ex x hx)
  have hf0 : f 0 = 0 := by simp [f]
  have hres : ∀ x, residue O (f x) = x := by
    intro x
    by_cases hx : x = 0
    · rw [hx, hf0, map_zero]
    · exact (hf x hx).2
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hres⟩
  · apply teichmuller_eq_of_residue_eq
    · exact (hf 1 one_ne_zero).1
    · exact one_pow _
    · rw [(hf 1 one_ne_zero).2, map_one]
  · intro x y
    by_cases hx : x = 0
    · simp [hx, hf0]
    by_cases hy : y = 0
    · simp [hy, hf0]
    apply teichmuller_eq_of_residue_eq
    · exact (hf _ (mul_ne_zero hx hy)).1
    · rw [mul_pow, (hf x hx).1, (hf y hy).1, one_mul]
    · rw [(hf _ (mul_ne_zero hx hy)).2, map_mul, (hf x hx).2, (hf y hy).2]

/- English proof (translation)
Use `haveI := c.dvr`. Use `haveI := c.fin`. Take `⟨hc, hfin, hlm, -⟩` from `abelian₂.dvr_finite l c.O`. Use `haveI := hc`. Use `haveI := hfin`.

Use `haveI : CharP (ResidueField c.O) l := by`. Rewrite using `[CharP.charP_iff_prime_eq_zero hl.out]`. Use `(IsLocalRing.residue_eq_zero_iff _).mpr hlm` as an intermediate fact. Simplify using `using this`. Take `⟨τ, hτ⟩` from `au_teich_ex l c.O`.

Use `⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `[hτ]`. Rewrite using `[MonoidHom.comp_apply, ← map_pow]`. Establish `hp : (r.chib i g) ^ (Nat.card (ResidueField c.O) - 1) = 1`. Use `letI := Fintype.ofFinite (ResidueField c.O)`.

Use `ext`. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]`. Conclude with `FiniteField.pow_card_sub_one_eq_one _ (r.chib i g).ne_zero`. Rewrite using `[hp, map_one]`.
-/
private theorem au_isTeich {l : ℕ} [hl : Fact l.Prime] {F : W.GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t := by
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨hc, hfin, hlm, -⟩ := abelian₂.dvr_finite l c.O
  haveI := hc
  haveI := hfin
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out]
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hlm
    simpa using this
  obtain ⟨τ, hτ⟩ := au_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨?_, ?_⟩⟩
  · simp [hτ]
  · rw [MonoidHom.comp_apply, ← map_pow]
    have hp : (r.chib i g) ^ (Nat.card (ResidueField c.O) - 1) = 1 := by
      letI := Fintype.ofFinite (ResidueField c.O)
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one _ (r.chib i g).ne_zero
    rw [hp, map_one]

/- English proof (translation)
Establish `hinj : Function.Injective (Matrix.GeneralLinearGroup.map f : GL (Fin m) O →* GL (Fin m) ℂ)`. Introduce `A B hAB`. Use extensionality with `i j`. Establish `h` using `congrArg (fun M : GL (Fin m) ℂ => (M : Matrix (Fin m) (Fin m) ℂ) i j) hAB`. Simplify using `at h`.

Conclude with `hf h`. Establish `hk : ((Matrix.GeneralLinearGroup.map f).comp τ).ker = τ.ker`. Use extensionality with `g`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `hinj (by rw [h, map_one])`. Introduce `h`. Rewrite using `[h, map_one]`. Rewrite `h` using `[hk]`. Then use the resulting hypothesis.
-/
private theorem au_open {G O : Type} [Group G] [TopologicalSpace G] [CommRing O] {m : ℕ} (f : O →+* ℂ) (hf : Function.Injective f)
    (τ : G →* GL (Fin m) O) (h : IsOpen (((Matrix.GeneralLinearGroup.map f).comp τ).ker : Set G)) : IsOpen (τ.ker : Set G) := by
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map f : GL (Fin m) O →* GL (Fin m) ℂ) := by
    intro A B hAB
    ext i j
    have h := congrArg (fun M : GL (Fin m) ℂ => (M : Matrix (Fin m) (Fin m) ℂ) i j) hAB
    simp at h
    exact hf h
  have hk : ((Matrix.GeneralLinearGroup.map f).comp τ).ker = τ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      exact hinj (by rw [h, map_one])
    · intro h
      rw [h, map_one]
  rwa [hk] at h

/- English proof (translation)
Introduce `hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam _ d ξ hξ F hF hK hI`. Take `⟨e, he⟩` from `hξ`. Take `⟨t, ht⟩` from `au_isTeich c r`. Establish `hop : IsOpen (τ₀.ker : Set (KT n (wt s)))` using `au_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1`. Establish `h1` using `decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI`.

Use `SetLike.le_def.1 (iSup_le fun σ => ?_) h1` and prove the remaining obligations. Distinguish the cases in `h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥`. Rewrite using `[h0]`. Conclude with `bot_le`. Take `⟨Y, hY, hPU, -⟩` from `partU hP l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0`.

Rewrite using `[← hY]`. Conclude with `le_iSup (fun Y : {Y : (hset Q τ₀).Part ι lam ξ // PU r ι lam Y.r} => Y.1.Y) ⟨Y, hPU⟩`.
-/
theorem UpperTheory.V.Hi.autU :
    Af.HypothesesH → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ →
    (hset Q τ₀).Aut ι (PU r ι) := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  obtain ⟨t, ht⟩ := au_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    au_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine SetLike.le_def.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  · obtain ⟨Y, hY, hPU, -⟩ := partU hP l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
    rw [← hY]
    exact le_iSup (fun Y : {Y : (hset Q τ₀).Part ι lam ξ // PU r ι lam Y.r} => Y.1.Y) ⟨Y, hPU⟩
