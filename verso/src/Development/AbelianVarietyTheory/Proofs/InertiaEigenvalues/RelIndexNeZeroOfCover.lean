import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.ClassPet

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

/- English proof (translation)
Use `⟨Subgroup.mul_mem _ ha.1 hb.1, fun i j => ?_⟩` and prove the remaining obligations. Use `choose y hy e using ha.2`. Use `choose z hz e' using hb.2`. Establish `hbU : ∀ k l, (b.1 : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L` using `hb.1`. Use `⟨∑ k, y i k * (b.1 : Matrix (Fin n) (Fin n) (AL L)) k j + z i j, Subring.add_mem _ (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy i k) (hbU k j)) (hz i j), ?_⟩` and prove the remaining obligations.

Establish `hA : (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of y`. Use extensionality with `k l`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hB : (b.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of z`. Use extensionality with `k l`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[← e']`. Expand and normalize the polynomial expressions, which then agree.

Establish `: ((a * b).1 : Matrix (Fin n) (Fin n) (AL L)) = (a.1 : Matrix _ _ _) * (b.1 : Matrix _ _ _)` using `rfl`. Rewrite using `[this]`. Use `conv_lhs => rw [hA, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]`. Rewrite using `[hB]`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cong_mul {N : ℕ} {a b : GAf L n} (ha : NG.Cong L n N a) (hb : NG.Cong L n N b) :
    NG.Cong L n N (a * b) := by
  refine ⟨Subgroup.mul_mem _ ha.1 hb.1, fun i j => ?_⟩
  choose y hy e using ha.2
  choose z hz e' using hb.2
  have hbU : ∀ k l, (b.1 : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L := hb.1
  refine ⟨∑ k, y i k * (b.1 : Matrix (Fin n) (Fin n) (AL L)) k j + z i j,
    Subring.add_mem _ (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy i k) (hbU k j)) (hz i j), ?_⟩
  have hA : (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of y := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e]; ring
  have hB : (b.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of z := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e']; ring
  have : ((a * b).1 : Matrix (Fin n) (Fin n) (AL L)) = (a.1 : Matrix _ _ _) * (b.1 : Matrix _ _ _) := rfl
  rw [this]
  conv_lhs => rw [hA, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [hB]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use `⟨Subgroup.one_mem _, fun i j => ⟨0, Subring.zero_mem _, ?_⟩⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem cong_one (N : ℕ) : NG.Cong L n N (1 : GAf L n) := by
  refine ⟨Subgroup.one_mem _, fun i j => ⟨0, Subring.zero_mem _, ?_⟩⟩
  simp

/- English proof (translation)
Use `⟨Subgroup.inv_mem _ ha.1, fun i j => ?_⟩` and prove the remaining obligations. Use `choose y hy e using ha.2`. Establish `hiU : ∀ k l, ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L` using `Subgroup.inv_mem _ ha.1`. Use `⟨-(∑ k, ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i k * y k j), Subring.neg_mem _ (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hiU i k) (hy k j)), ?_⟩` and prove the remaining obligations. Establish `hA : (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of y`.

Use extensionality with `k l`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree. Establish `hinv : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix _ _ _) = 1`.

Establish `: (a⁻¹ * a).1 = 1` using `by simp`. Conclude with `congrArg (fun u : GL (Fin n) (AL L) => (u : Matrix (Fin n) (Fin n) (AL L))) this`. Establish `key : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 = -((N : AL L) • (((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * Matrix.of y))`. Combine the equalities or inequalities in the displayed calculation. Use `congrFun (congrFun key i) j` as an intermediate fact.

Simplify using `only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul] at this`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cong_inv {N : ℕ} {a : GAf L n} (ha : NG.Cong L n N a) : NG.Cong L n N a⁻¹ := by
  refine ⟨Subgroup.inv_mem _ ha.1, fun i j => ?_⟩
  choose y hy e using ha.2
  have hiU : ∀ k l, ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L := Subgroup.inv_mem _ ha.1
  refine ⟨-(∑ k, ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i k * y k j),
    Subring.neg_mem _ (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hiU i k) (hy k j)), ?_⟩
  have hA : (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of y := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e]; ring
  have hinv : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix _ _ _) = 1 := by
    have : (a⁻¹ * a).1 = 1 := by simp
    exact congrArg (fun u : GL (Fin n) (AL L) => (u : Matrix (Fin n) (Fin n) (AL L))) this
  have key : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
      -((N : AL L) • (((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * Matrix.of y)) := by
    calc ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1
        = ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - ((a⁻¹).1 : Matrix _ _ _) * (a.1 : Matrix _ _ _) := by rw [hinv]
      _ = _ := by rw [hA, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]; abel
  have := congrFun (congrFun key i) j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul] at this
  rw [this]; ring

variable (L n) in

def congSub (N : ℕ) : Subgroup (GAf L n) where
  carrier := {κ | NG.Cong L n N κ}
  mul_mem' := cong_mul
  one_mem' := cong_one N
  inv_mem' := cong_inv

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_congSub {N : ℕ} {κ : GAf L n} : κ ∈ congSub L n N ↔ NG.Cong L n N κ := Iff.rfl

/- English proof (translation)
Introduce `_ h` and use `h.1`.
-/
theorem congSub_le_umax (N : ℕ) : congSub L n N ≤ Umax L n := fun _ h => h.1

/- English proof (translation)
Introduce `_ h` and use `NG.Cong.of_mul_left L n h`.
-/
theorem congSub_mul_le (N M : ℕ) : congSub L n (N * M) ≤ congSub L n N := fun _ h => NG.Cong.of_mul_left L n h

end GlobalTheory.ClassPet

namespace GlobalTheory.ClassPet

section Grp
variable {G : Type*} [Group G]

/- English proof (translation)
Use `haveI : Finite (K ⧸ H.subgroupOf K) := by`. Set `φ : F → K ⧸ H.subgroupOf K` to `fun f => if h : (f : G) ∈ K then ((⟨f, h⟩ : K) : K ⧸ H.subgroupOf K) else ((1 : K) : K ⧸ H.subgroupOf K)`. Use `Finite.of_surjective φ (fun q => ?_)` and prove the remaining obligations. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H κ`.

Take `⟨f, hf, hfκ⟩` from `hF κ κ.2`. Establish `hfK : f ∈ K`. Use `K.mul_mem κ.2 (K.inv_mem (hle hfκ))` as an intermediate fact. Simplify using `using this`. Use `⟨⟨f, hf⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [φ, dif_pos hfK]`. Conclude with `QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hfκ)`. Use `show (H.subgroupOf K).index ≠ 0`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_cover {H K : Subgroup G} (F : Finset G) (hF : ∀ κ ∈ K, ∃ f ∈ F, f⁻¹ * κ ∈ H)
    (hle : H ≤ K) : H.relIndex K ≠ 0 := by
  classical
  haveI : Finite (K ⧸ H.subgroupOf K) := by
    let φ : F → K ⧸ H.subgroupOf K := fun f =>
      if h : (f : G) ∈ K then ((⟨f, h⟩ : K) : K ⧸ H.subgroupOf K) else ((1 : K) : K ⧸ H.subgroupOf K)
    refine Finite.of_surjective φ (fun q => ?_)
    induction q using QuotientGroup.induction_on with
    | H κ =>
      obtain ⟨f, hf, hfκ⟩ := hF κ κ.2
      have hfK : f ∈ K := by
        have := K.mul_mem κ.2 (K.inv_mem (hle hfκ))
        simpa using this
      refine ⟨⟨f, hf⟩, ?_⟩
      simp only [φ, dif_pos hfK]
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hfκ)
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Use `haveI : (H.subgroupOf K).FiniteIndex := ⟨hne⟩`. Use `haveI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _`. Set `o : K ⧸ H.subgroupOf K → G` to `fun q => ((Quotient.out q : K) : G)`. Establish `ho : Function.Injective o`. Introduce `q q' h`.

Establish `: Quotient.out q = Quotient.out q'` using `Subtype.ext h`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', this]`. Use `⟨Finset.univ.image o, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hu`.

Conclude with `(Quotient.out q).2`. Introduce `κ hκ`. Use `⟨o ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K))`. Simplify `h` using `[Subgroup.mem_subgroupOf, o]`.

Introduce and unpack `u ⟨hu, hu'⟩`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hu`. Establish `: q = ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K)`. Rewrite using `[← QuotientGroup.out_eq' q]`. Conclude with `QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf, o] using hu')`.

Rewrite using `[this]`. Rewrite using `[Finset.card_image_of_injective _ ho, Finset.card_univ] show _ = (H.subgroupOf K).index`. Rewrite using `[Subgroup.index, Nat.card_eq_fintype_card]`.
-/
theorem exists_cosetReps {H K : Subgroup G} (hle : H ≤ K) (hne : H.relIndex K ≠ 0) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ K) ∧ (∀ κ ∈ K, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ H) ∧ F.card = H.relIndex K := by
  classical
  haveI : (H.subgroupOf K).FiniteIndex := ⟨hne⟩
  haveI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  let o : K ⧸ H.subgroupOf K → G := fun q => ((Quotient.out q : K) : G)
  have ho : Function.Injective o := by
    intro q q' h
    have : Quotient.out q = Quotient.out q' := Subtype.ext h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', this]
  refine ⟨Finset.univ.image o, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact (Quotient.out q).2
  · intro κ hκ
    refine ⟨o ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K))
      simpa [Subgroup.mem_subgroupOf, o] using h
    · rintro u ⟨hu, hu'⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      have : q = ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K) := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf, o] using hu')
      rw [this]
  · rw [Finset.card_image_of_injective _ ho, Finset.card_univ]
    show _ = (H.subgroupOf K).index
    rw [Subgroup.index, Nat.card_eq_fintype_card]

/- English proof (translation)
Use `haveI : (K.subgroupOf J).FiniteIndex := ⟨hne⟩`. Take `⟨i, j, hij, e⟩` from `Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => ((κ ^ i : J) : J ⧸ K.subgroupOf J))`. Establish `hmem : ((κ ^ i)⁻¹ * κ ^ j : J) ∈ K.subgroupOf J` using `QuotientGroup.eq.1 e`. Establish `h1 : χ ((κ ^ i)⁻¹ * κ ^ j) = 1`. Use `hχ _ (Subgroup.mem_subgroupOf.1 hmem)` as an intermediate fact.

Rewrite `this` using `[Subtype.coe_eta]`. Then use the resulting hypothesis. Establish `h2 : ((χ κ : ℂˣ) : ℂ) ^ i = ((χ κ : ℂˣ) : ℂ) ^ j`. Rewrite `h1` using `[map_mul, map_inv, map_pow, map_pow, inv_mul_eq_one]`. Use `congrArg (fun u : ℂˣ => (u : ℂ)) h1` as an intermediate fact. Simplify using `using this`.

Establish `h3 : ‖((χ κ : ℂˣ) : ℂ)‖ ^ i = ‖((χ κ : ℂˣ) : ℂ)‖ ^ j` using `by rw [← norm_pow, ← norm_pow, h2]`. Establish `hpos : 0 < ‖((χ κ : ℂˣ) : ℂ)‖` using `norm_pos_iff.2 (Units.ne_zero _)`. Assume the negation of the conclusion as `hne1`. Conclude with `hij (pow_right_injective₀ hpos hne1 h3)`.
-/
theorem norm_eq_one_of_relIndex {J K : Subgroup G} (hle : K ≤ J) (hne : K.relIndex J ≠ 0) (χ : J →* ℂˣ)
    (hχ : ∀ κ (h : κ ∈ K), χ ⟨κ, hle h⟩ = 1) (κ : J) : ‖((χ κ : ℂˣ) : ℂ)‖ = 1 := by
  haveI : (K.subgroupOf J).FiniteIndex := ⟨hne⟩
  obtain ⟨i, j, hij, e⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => ((κ ^ i : J) : J ⧸ K.subgroupOf J))
  have hmem : ((κ ^ i)⁻¹ * κ ^ j : J) ∈ K.subgroupOf J := QuotientGroup.eq.1 e
  have h1 : χ ((κ ^ i)⁻¹ * κ ^ j) = 1 := by
    have := hχ _ (Subgroup.mem_subgroupOf.1 hmem)
    rwa [Subtype.coe_eta] at this
  have h2 : ((χ κ : ℂˣ) : ℂ) ^ i = ((χ κ : ℂˣ) : ℂ) ^ j := by
    rw [map_mul, map_inv, map_pow, map_pow, inv_mul_eq_one] at h1
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h1
    simpa using this
  have h3 : ‖((χ κ : ℂˣ) : ℂ)‖ ^ i = ‖((χ κ : ℂˣ) : ℂ)‖ ^ j := by rw [← norm_pow, ← norm_pow, h2]
  have hpos : 0 < ‖((χ κ : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  by_contra hne1
  exact hij (pow_right_injective₀ hpos hne1 h3)

end Grp

section Sum
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
  (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (J : Subgroup (GAf L n)) (T : Finset (GAf L n))

/- English proof (translation)
Simplify using `only [classSum, Pi.add_apply, LinearMap.map_add₂, mul_add, Finset.sum_add_distrib]`.
-/
theorem classSum_add_left (f₁ f₂ f' : GAf L n → a.W) :
    classSum a β J T (f₁ + f₂) f' = classSum a β J T f₁ f' + classSum a β J T f₂ f' := by
  simp only [classSum, Pi.add_apply, LinearMap.map_add₂, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [classSum, Pi.smul_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => by ring` and prove the remaining obligations.
-/
theorem classSum_smul_left (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T (c • f) f' = starRingEnd ℂ c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

/- English proof (translation)
Simplify using `only [classSum, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem classSum_add_right (f f₁ f₂ : GAf L n → a.W) :
    classSum a β J T f (f₁ + f₂) = classSum a β J T f f₁ + classSum a β J T f f₂ := by
  simp only [classSum, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [classSum, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => by ring` and prove the remaining obligations.
-/
theorem classSum_smul_right (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T f (c • f') = c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

/- English proof (translation)
Simplify using `only [classSum, map_sum, map_mul, map_inv₀, map_natCast]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[hβ.1 (f' t) (f t)]`.
-/
theorem classSum_conj (hβ : IsInvForm a β) (f f' : GAf L n → a.W) :
    classSum a β J T f' f = starRingEnd ℂ (classSum a β J T f f') := by
  simp only [classSum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hβ.1 (f' t) (f t)]

end Sum

end GlobalTheory.ClassPet
