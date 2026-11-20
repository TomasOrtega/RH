import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
open NumberField Formalism.L2.Pj

namespace GlobalTheory.ComplexEmbedding

open Cardinal IsLocalRing

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x; exact ⟨Fin.elim0, by simp⟩`. Consider the case `succ n ih`. Introduce `x`.

Take `⟨f, hf⟩` from `ih x`. Establish `hm : maximalIdeal V = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`. Establish `hf'` using `hf`. Rewrite `hf'` using `[hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨y, hy⟩` from `hf'`.

Use `⟨Fin.snoc f (residue V y), ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]`. Establish `hxy : x - (∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ) + s (residue V y) * ϖ ^ n) = ϖ ^ n * (y - s (residue V y))`. Rewrite using `[← sub_sub, hy]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hxy, pow_succ]`. Establish `hϖm : ϖ ∈ maximalIdeal V` using `(mem_maximalIdeal _).2 hϖ.not_isUnit`. Establish `hym : y - s (residue V y) ∈ maximalIdeal V`. Rewrite using `[← residue_eq_zero_iff, map_sub, hs, sub_self]`.

Conclude with `Ideal.mul_mem_mul (Ideal.pow_mem_pow hϖm n) hym`.
-/
theorem exists_digits_of_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (ϖ : V) (hϖ : Irreducible ϖ) (s : ResidueField V → V) (hs : ∀ r, residue V (s r) = r) :
    ∀ (n : ℕ) (x : V), ∃ f : Fin n → ResidueField V,
      x - ∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ) ∈ maximalIdeal V ^ n := by
  intro n
  induction n with
  | zero => intro x; exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
    intro x
    obtain ⟨f, hf⟩ := ih x
    have hm : maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    have hf' := hf
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hf'
    obtain ⟨y, hy⟩ := hf'
    refine ⟨Fin.snoc f (residue V y), ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
    have hxy : x - (∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ) + s (residue V y) * ϖ ^ n) =
        ϖ ^ n * (y - s (residue V y)) := by
      rw [← sub_sub, hy]; ring
    rw [hxy, pow_succ]
    have hϖm : ϖ ∈ maximalIdeal V := (mem_maximalIdeal _).2 hϖ.not_isUnit
    have hym : y - s (residue V y) ∈ maximalIdeal V := by
      rw [← residue_eq_zero_iff, map_sub, hs, sub_self]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hϖm n) hym

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Set `s : ResidueField V → V` to `Function.surjInv (residue_surjective (R := V))`. Establish `hs : ∀ r, residue V (s r) = r` using `Function.surjInv_eq _`. Establish `hsurj : Function.Surjective (fun f : Fin n → ResidueField V => Ideal.Quotient.mk (maximalIdeal V ^ n) (∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ)))`. Introduce `q`.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Take `⟨f, hf⟩` from `exists_digits_of_dvr V ϖ hϖ s hs n x`. Conclude with `⟨f, (Ideal.Quotient.eq.2 hf).symm⟩`. Conclude with `hsurj.countable`.
-/
theorem countable_quotient_pow_of_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Countable (ResidueField V)] (n : ℕ) : Countable (V ⧸ maximalIdeal V ^ n) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let s : ResidueField V → V := Function.surjInv (residue_surjective (R := V))
  have hs : ∀ r, residue V (s r) = r := Function.surjInv_eq _
  have hsurj : Function.Surjective (fun f : Fin n → ResidueField V =>
      Ideal.Quotient.mk (maximalIdeal V ^ n) (∑ i : Fin n, s (f i) * ϖ ^ (i : ℕ))) := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨f, hf⟩ := exists_digits_of_dvr V ϖ hϖ s hs n x
    exact ⟨f, (Ideal.Quotient.eq.2 hf).symm⟩
  exact hsurj.countable

/- English proof (translation)
Set `f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n` to `fun x n => Ideal.Quotient.mk _ x`. Establish `hinj : Function.Injective f`. Introduce `x y hxy`. Establish `: x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n` using `Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)`. Rewrite `this` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top]`.

Conclude with `sub_eq_zero.1 this`. Use `(mk_le_of_injective hinj).trans ?_` and prove the remaining obligations. Rewrite using `[mk_pi]`. Use `(prod_le_prod _ (fun _ => ℵ₀) fun n => haveI := countable_quotient_pow_of_dvr V n; mk_le_aleph0).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem mk_le_continuum_of_countable_residueField (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Countable (ResidueField V)] : #V ≤ 𝔠 := by
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n =>
    haveI := countable_quotient_pow_of_dvr V n; mk_le_aleph0).trans ?_
  simp

/- English proof (translation)
Introduce `K _ _ σ T T' g _ hfin hc io`. Establish `hV : #T.V ≤ 𝔠` using `mk_le_continuum_of_countable_residueField T.V`. Use `letI : Algebra T.V T'.V := g.toAlgebra`. Use `haveI : Module.Finite T.V T'.V := hfin`. Take `⟨d, φ, hφ⟩` from `Module.Finite.exists_fin' T.V T'.V`.

Establish `hV' : #T'.V ≤ 𝔠`. Use `(mk_le_of_surjective hφ).trans ?_` and prove the remaining obligations. Rewrite using `[mk_arrow, mk_fin, lift_id, lift_natCast]`. Use `(power_le_power_right hV).trans ?_` and prove the remaining obligations. Conclude with `power_nat_le aleph0_le_continuum`.

Establish `hF : #T'.Fr ≤ 𝔠`. Rewrite using `[show #T'.Fr = #T'.V from IsFractionRing.cardinalMk T'.V T'.Fr]`. Conclude with `hV'`. Conclude with `@exists_embedding_of_mk_le_continuum K T'.Fr _ _ _ io.toAlgebra hF σ`.
-/
theorem exists_embedding_fractionField_of_finite :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T T' : CDVR) (g : T.V →+* T'.V),
      Function.Injective g → g.Finite → Countable (IsLocalRing.ResidueField T.V) →
      ∀ io : K →+* T'.Fr, ∃ ι : T'.Fr →+* ℂ, ι.comp io = σ := by
  intro K _ _ σ T T' g _ hfin hc io
  have hV : #T.V ≤ 𝔠 := mk_le_continuum_of_countable_residueField T.V
  letI : Algebra T.V T'.V := g.toAlgebra
  haveI : Module.Finite T.V T'.V := hfin
  obtain ⟨d, φ, hφ⟩ := Module.Finite.exists_fin' T.V T'.V
  have hV' : #T'.V ≤ 𝔠 := by
    refine (mk_le_of_surjective hφ).trans ?_
    rw [mk_arrow, mk_fin, lift_id, lift_natCast]
    refine (power_le_power_right hV).trans ?_
    exact power_nat_le aleph0_le_continuum
  have hF : #T'.Fr ≤ 𝔠 := by
    rw [show #T'.Fr = #T'.V from IsFractionRing.cardinalMk T'.V T'.Fr]
    exact hV'
  exact @exists_embedding_of_mk_le_continuum K T'.Fr _ _ _ io.toAlgebra hF σ

end GlobalTheory.ComplexEmbedding
