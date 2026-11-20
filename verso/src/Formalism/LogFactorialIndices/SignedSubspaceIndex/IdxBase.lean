import Formalism.LogFactorialIndices.StatementIdx
import Lemmata.GeneralBFactSecondFurther.Imports

noncomputable section

namespace Formalism.LatticeIndexTer

open Module
open scoped Pointwise

namespace LatticeIndexLength

section SlopeTestRemainingChoices

/- English proof (translation)
Set `I : Ideal O` to `Ideal.span {d}`. Establish `hle : I • (⊤ : Submodule O M) ≤ N`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr m _`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`.

Rewrite using `[mul_smul]`. Conclude with `N.smul_mem _ (hN m)`. Use `ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle))` and prove the remaining obligations. Establish `h1 : IsFiniteLength O (O ⧸ I)` using `isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hd)`. Rewrite `h1` using `[isFiniteLength_iff_isNoetherian_isArtinian]`.

Take `⟨_, h1a⟩` from `h1`. Establish `: IsArtinianRing (O ⧸ I)` using `isArtinian_of_tower O h1a`. Establish `: Module.Finite (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M))` using `Module.Finite.of_restrictScalars_finite O (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M))`. Establish `: IsArtinian (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M))` using `inferInstance`. Establish `: IsArtinian O (M ⧸ I • (⊤ : Submodule O M))` using `isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))`.

Conclude with `Module.length_ne_top`.
-/
theorem length_quot_ne_top {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M]
    (d : O) (hd : d ≠ 0) (N : Submodule O M) (hN : ∀ m : M, d • m ∈ N) :
    Module.length O (M ⧸ N) ≠ ⊤ := by
  let I : Ideal O := Ideal.span {d}
  have hle : I • (⊤ : Submodule O M) ≤ N := by
    rw [Submodule.smul_le]
    intro r hr m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact N.smul_mem _ (hN m)
  refine ne_top_of_le_ne_top ?_
    (Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle))
  have h1 : IsFiniteLength O (O ⧸ I) :=
    isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hd)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h1
  obtain ⟨_, h1a⟩ := h1
  have : IsArtinianRing (O ⧸ I) := isArtinian_of_tower O h1a
  have : Module.Finite (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M)) :=
    Module.Finite.of_restrictScalars_finite O (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M))
  have : IsArtinian (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M)) := inferInstance
  have : IsArtinian O (M ⧸ I • (⊤ : Submodule O M)) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top

/- English proof (translation)
Set `f : (E ⧸ D.comap E.subtype) →ₗ[O] (P ⧸ D.comap P.subtype)` to `Submodule.mapQ _ _ (Submodule.inclusion hEP) (by intro x hx; simpa using hx)`. Set `g : (P ⧸ D.comap P.subtype) →ₗ[O] (P ⧸ E.comap P.subtype)` to `Submodule.factor (Submodule.comap_mono hDE)`. Apply `Module.length_eq_add_of_exact f g` to reduce the goal to its premises. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `x hx`.

Proceed by induction on `x using Submodule.Quotient.induction_on with | H e => ?_`. Rewrite `hx` using `[LinearMap.mem_ker]`. Simplify using `only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx`. Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]`. Conclude with `hx`.

Conclude with `Submodule.factor_surjective _`. Introduce `y`. Proceed by induction on `y using Submodule.Quotient.induction_on with | H p => ?_`. Rewrite using `[show g (Submodule.Quotient.mk p) = Submodule.Quotient.mk p from Submodule.factor_mk _ p, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `hp`. Conclude with `⟨Submodule.Quotient.mk ⟨p, hp⟩, rfl⟩`. Introduce and unpack `⟨x, hx⟩`. Proceed by induction on `x using Submodule.Quotient.induction_on with | H e => ?_`. Simplify using `only [f, Submodule.mapQ_apply] at hx`.

Rewrite `hx` using `[Submodule.Quotient.eq, Submodule.mem_comap]`. Simplify using `only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion] at hx`. Establish `: (p : X) = (e : X) - ((e : X) - p)` using `by abel`. Rewrite using `[this]`. Conclude with `E.sub_mem e.2 (hDE hx)`.
-/
theorem length_quotient_tower_add {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
    (D E P : Submodule O X) (hDE : D ≤ E) (hEP : E ≤ P) :
    Module.length O (P ⧸ D.comap P.subtype) =
      Module.length O (E ⧸ D.comap E.subtype) + Module.length O (P ⧸ E.comap P.subtype) := by
  let f : (E ⧸ D.comap E.subtype) →ₗ[O] (P ⧸ D.comap P.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hEP) (by intro x hx; simpa using hx)
  let g : (P ⧸ D.comap P.subtype) →ₗ[O] (P ⧸ E.comap P.subtype) :=
    Submodule.factor (Submodule.comap_mono hDE)
  apply Module.length_eq_add_of_exact f g
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with | H e => ?_
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_inclusion] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    exact hx
  · exact Submodule.factor_surjective _
  · intro y
    induction y using Submodule.Quotient.induction_on with | H p => ?_
    rw [show g (Submodule.Quotient.mk p) = Submodule.Quotient.mk p from Submodule.factor_mk _ p,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hp
      exact ⟨Submodule.Quotient.mk ⟨p, hp⟩, rfl⟩
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | H e => ?_
      simp only [f, Submodule.mapQ_apply] at hx
      rw [Submodule.Quotient.eq, Submodule.mem_comap] at hx
      simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion] at hx
      have : (p : X) = (e : X) - ((e : X) - p) := by abel
      rw [this]
      exact E.sub_mem e.2 (hDE hx)

end SlopeTestRemainingChoices

section Sat

variable {O K X : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_second''.goal1 .. | (apply Bl.general_b_fact_second''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second''.go …`.
-/
theorem exists_smul_mem_of_span (B : Submodule O X) (hB : Submodule.span K (B : Set X) = ⊤)
    (x : X) : ∃ d : O, d ≠ 0 ∧ d • x ∈ B := by
  first | exact Bl.general_b_fact_second''.goal1 .. | (apply Bl.general_b_fact_second''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B hB x | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B hB | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X | exact @Bl.general_b_fact_second''.goal1 O K | exact @Bl.general_b_fact_second''.goal1 O

/- English proof (translation)
Take `⟨s, rfl⟩` from `hA`. Use `choose f hf0 hf using fun x => exists_smul_mem_of_span (K := K) B hB x`. Use `⟨∏ x ∈ s, f x, Finset.prod_ne_zero_iff.2 (fun x _ => hf0 x), ?_⟩` and prove the remaining obligations. Introduce `a ha`. Establish `h : Submodule.span O (s : Set X) ≤ B.comap ((∏ x ∈ s, f x) • LinearMap.id)`.

Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem f (Finset.mem_coe.1 hx)`. Use `show ((∏ x ∈ s, f x) • LinearMap.id : X →ₗ[O] X) x ∈ B`. Rewrite using `[LinearMap.smul_apply, LinearMap.id_apply, hc, mul_comm, mul_smul]`.

Conclude with `B.smul_mem _ (hf x)`. Conclude with `h ha`.
-/
theorem exists_smul_le (A B : Submodule O X) (hA : A.FG)
    (hB : Submodule.span K (B : Set X) = ⊤) : ∃ d : O, d ≠ 0 ∧ ∀ a ∈ A, d • a ∈ B := by
  classical
  obtain ⟨s, rfl⟩ := hA
  choose f hf0 hf using fun x => exists_smul_mem_of_span (K := K) B hB x
  refine ⟨∏ x ∈ s, f x, Finset.prod_ne_zero_iff.2 (fun x _ => hf0 x), ?_⟩
  intro a ha
  have h : Submodule.span O (s : Set X) ≤ B.comap ((∏ x ∈ s, f x) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.1 hx)
    show ((∏ x ∈ s, f x) • LinearMap.id : X →ₗ[O] X) x ∈ B
    rw [LinearMap.smul_apply, LinearMap.id_apply, hc, mul_comm, mul_smul]
    exact B.smul_mem _ (hf x)
  exact h ha

/- English proof (translation)
Take `⟨d₁, hd₁, e₁⟩` from `exists_smul_le P Q₁ hP h₁`. Take `⟨d₂, hd₂, e₂⟩` from `exists_smul_le P Q₂ hP h₂`. Take `⟨d₃, hd₃, e₃⟩` from `exists_smul_le P Q₃ hP h₃`. Use `⟨d₁ * d₂ * d₃, mul_ne_zero (mul_ne_zero hd₁ hd₂) hd₃, fun p hp => ?_⟩` and prove the remaining obligations. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[show d₁ * d₂ * d₃ = (d₂ * d₃) * d₁ by ring, mul_smul]; exact Q₁.smul_mem _ (e₁ p hp)`. Rewrite using `[show d₁ * d₂ * d₃ = (d₁ * d₃) * d₂ by ring, mul_smul]; exact Q₂.smul_mem _ (e₂ p hp)`. Rewrite using `[mul_smul]`. Conclude with `Q₃.smul_mem _ (e₃ p hp)`.
-/
theorem exists_smul_mem_inf_three (P Q₁ Q₂ Q₃ : Submodule O X) (hP : P.FG)
    (h₁ : Submodule.span K (Q₁ : Set X) = ⊤) (h₂ : Submodule.span K (Q₂ : Set X) = ⊤)
    (h₃ : Submodule.span K (Q₃ : Set X) = ⊤) :
    ∃ d : O, d ≠ 0 ∧ ∀ p ∈ P, d • p ∈ Q₁ ⊓ Q₂ ⊓ Q₃ := by
  obtain ⟨d₁, hd₁, e₁⟩ := exists_smul_le P Q₁ hP h₁
  obtain ⟨d₂, hd₂, e₂⟩ := exists_smul_le P Q₂ hP h₂
  obtain ⟨d₃, hd₃, e₃⟩ := exists_smul_le P Q₃ hP h₃
  refine ⟨d₁ * d₂ * d₃, mul_ne_zero (mul_ne_zero hd₁ hd₂) hd₃, fun p hp => ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [show d₁ * d₂ * d₃ = (d₂ * d₃) * d₁ by ring, mul_smul]; exact Q₁.smul_mem _ (e₁ p hp)
  · rw [show d₁ * d₂ * d₃ = (d₁ * d₃) * d₂ by ring, mul_smul]; exact Q₂.smul_mem _ (e₂ p hp)
  · rw [mul_smul]; exact Q₃.smul_mem _ (e₃ p hp)

end Sat

section Main

/- English proof (translation)
Establish `: Module.Finite O P` using `Module.Finite.iff_fg.2 hP`. Use `length_quot_ne_top d hd _ (fun m => ?_)` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]`. Conclude with `h m m.2`.
-/
theorem len_ne_top {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup X] [Module O X] (P D : Submodule O X) (hP : P.FG) (d : O) (hd : d ≠ 0)
    (h : ∀ p ∈ P, d • p ∈ D) : Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤ := by
  have : Module.Finite O P := Module.Finite.iff_fg.2 hP
  refine length_quot_ne_top d hd _ (fun m => ?_)
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]
  exact h m m.2

/- English proof (translation)
Establish `eP` using `length_quotient_tower_add D (P ⊓ Q) P hD inf_le_left`. Establish `eQ` using `length_quotient_tower_add D (P ⊓ Q) Q hD inf_le_right`. Establish `cP : Q.comap P.subtype = (P ⊓ Q).comap P.subtype`. Rewrite using `[Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]`. Establish `cQ : P.comap Q.subtype = (P ⊓ Q).comap Q.subtype`.

Rewrite using `[Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]`. Unfold `idx qlen`. Rewrite using `[cP, cQ]`. Rewrite `hP`, the goal using `[eP]`. Rewrite `hQ`, the goal using `[eQ]`.

Take `⟨h1, h2⟩` from `WithTop.add_ne_top.1 hP`. Take `⟨_, h3⟩` from `WithTop.add_ne_top.1 hQ`. Rewrite using `[ENat.toNat_add h1 h2, ENat.toNat_add h1 h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem idx_eq_sub {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
    (P Q D : Submodule O X) (hD : D ≤ P ⊓ Q)
    (hP : Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤)
    (hQ : Module.length O (Q ⧸ D.comap Q.subtype) ≠ ⊤) :
    idx O X P Q = ((Module.length O (P ⧸ D.comap P.subtype)).toNat : ℤ) -
      ((Module.length O (Q ⧸ D.comap Q.subtype)).toNat : ℤ) := by
  have eP := length_quotient_tower_add D (P ⊓ Q) P hD inf_le_left
  have eQ := length_quotient_tower_add D (P ⊓ Q) Q hD inf_le_right
  have cP : Q.comap P.subtype = (P ⊓ Q).comap P.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  have cQ : P.comap Q.subtype = (P ⊓ Q).comap Q.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  unfold idx qlen
  rw [cP, cQ]
  rw [eP] at hP ⊢
  rw [eQ] at hQ ⊢
  obtain ⟨h1, h2⟩ := WithTop.add_ne_top.1 hP
  obtain ⟨_, h3⟩ := WithTop.add_ne_top.1 hQ
  rw [ENat.toNat_add h1 h2, ENat.toNat_add h1 h3]
  push_cast
  ring

end Main

end LatticeIndexLength

open LatticeIndexLength

/- English proof (translation)
Introduce `O K X _ _ _ _ _ _ _ _ _ _ A B hA hB`. Take `⟨d, hd, h⟩` from `exists_smul_le (K := K) A B hA.1 hB.2`. Conclude with `len_ne_top A B hA.1 d hd h`.
-/
theorem lattice_quotient_finite : LatFinite := by
  intro O K X _ _ _ _ _ _ _ _ _ _ A B hA hB
  obtain ⟨d, hd, h⟩ := exists_smul_le (K := K) A B hA.1 hB.2
  exact len_ne_top A B hA.1 d hd h

/- English proof (translation)
Introduce `O K X _ _ _ _ _ _ _ _ _ _ A B C hA hB hC`. Set `D` to `A ⊓ B ⊓ C`. Establish `fin : ∀ P : Submodule O X, IsLat O K X P → Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤`. Introduce `P hP`. Take `⟨d, hd, h⟩` from `exists_smul_mem_inf_three (K := K) P A B C hP.1 hA.2 hB.2 hC.2`.

Conclude with `len_ne_top P D hP.1 d hd h`. Establish `hAB : D ≤ A ⊓ B` using `inf_le_left`. Establish `hBC : D ≤ B ⊓ C` using `le_inf (inf_le_left.trans inf_le_right) inf_le_right`. Establish `hAC : D ≤ A ⊓ C` using `le_inf (inf_le_left.trans inf_le_left) inf_le_right`. Rewrite using `[idx_eq_sub A C D hAC (fin A hA) (fin C hC), idx_eq_sub A B D hAB (fin A hA) (fin B hB), idx_eq_sub B C D hBC (fin B hB) (fin C hC)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lattice_index_add : IdxAdd := by
  intro O K X _ _ _ _ _ _ _ _ _ _ A B C hA hB hC
  let D := A ⊓ B ⊓ C
  have fin : ∀ P : Submodule O X, IsLat O K X P → Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤ := by
    intro P hP
    obtain ⟨d, hd, h⟩ := exists_smul_mem_inf_three (K := K) P A B C hP.1 hA.2 hB.2 hC.2
    exact len_ne_top P D hP.1 d hd h
  have hAB : D ≤ A ⊓ B := inf_le_left
  have hBC : D ≤ B ⊓ C := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hAC : D ≤ A ⊓ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [idx_eq_sub A C D hAC (fin A hA) (fin C hC), idx_eq_sub A B D hAB (fin A hA) (fin B hB),
    idx_eq_sub B C D hBC (fin B hB) (fin C hC)]
  ring

/- English proof (translation)
Introduce `O K X _ _ _ _ _ _ _ _ _ _ _ A hA`. Establish `: Submodule.IsLattice K A` using `⟨hA.1, hA.2⟩`. Set `b` to `Module.Free.chooseBasis O A`. Set `b'` to `b.extendOfIsLattice K`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex O A) = finrank K X` using `(Module.finrank_eq_card_basis b').symm`.

Use `⟨b'.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.range_reindex]`. Establish `hr : Set.range b' = A.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Use extensionality with `x`.

Simplify using `[b']`. Rewrite using `[hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem lattice_has_basis : LatBasis := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ A hA
  have : Submodule.IsLattice K A := ⟨hA.1, hA.2⟩
  let b := Module.Free.chooseBasis O A
  let b' := b.extendOfIsLattice K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O A) = finrank K X :=
    (Module.finrank_eq_card_basis b').symm
  refine ⟨b'.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Module.Basis.range_reindex]
  have hr : Set.range b' = A.subtype '' Set.range b := by
    rw [← Set.range_comp]
    ext x
    simp [b']
  rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end Formalism.LatticeIndexTer
