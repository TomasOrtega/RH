import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.BlockIdx

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨b, hb, s, hs, rfl⟩`.
-/
theorem gen_mem_hatId {b : 𝓞 D.host.E} (hb : b ∈ 𝔪) {s : AE D} (hs : s ∈ OhE D) :
    inc D (b : D.host.E) * s ∈ hatId D 𝔪 :=
  AddSubgroup.subset_closure ⟨b, hb, s, hs, rfl⟩

/- English proof (translation)
Establish `h : AddSubgroup.closure {y | ∃ b ∈ 𝔪, ∃ t ∈ OhE D, y = inc D (b : D.host.E) * t} ≤ (hatId D 𝔪).comap (AddMonoidHom.mulLeft s)`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `y ⟨b, hb, t, ht, rfl⟩`. Use `show s * (inc D (b : D.host.E) * t) ∈ hatId D 𝔪`. Rewrite using `[mul_left_comm]`.

Conclude with `gen_mem_hatId D 𝔪 hb (mul_mem hs ht)`. Conclude with `h hx`.
-/
theorem mul_mem_hatId {s : AE D} (hs : s ∈ OhE D) {x : AE D} (hx : x ∈ hatId D 𝔪) :
    s * x ∈ hatId D 𝔪 := by
  have h : AddSubgroup.closure {y | ∃ b ∈ 𝔪, ∃ t ∈ OhE D, y = inc D (b : D.host.E) * t} ≤
      (hatId D 𝔪).comap (AddMonoidHom.mulLeft s) := by
    rw [AddSubgroup.closure_le]
    rintro y ⟨b, hb, t, ht, rfl⟩
    show s * (inc D (b : D.host.E) * t) ∈ hatId D 𝔪
    rw [mul_left_comm]
    exact gen_mem_hatId D 𝔪 hb (mul_mem hs ht)
  exact h hx

/- English proof (translation)
Use `gen_mem_hatId D 𝔪 (Ideal.absNorm_mem 𝔪) hw` as an intermediate fact. Simplify using `using this`.
-/
theorem absNorm_mul_mem_hatId {w : AE D} (hw : w ∈ OhE D) :
    (Ideal.absNorm 𝔪 : AE D) * w ∈ hatId D 𝔪 := by
  have := gen_mem_hatId D 𝔪 (Ideal.absNorm_mem 𝔪) hw
  simpa using this

/- English proof (translation)
Establish `hn : 0 < Ideal.absNorm 𝔪` using `Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)`. Take `⟨r, hr, w, hw, e⟩` from `GlobalTheory.HeckeVal.exists_approx D _ hn x hx`. Use `⟨⟨r, (mem_integralClosure_iff ℤ _).2 hr⟩, ?_⟩` and prove the remaining obligations. Use `show x - inc D r ∈ hatId D 𝔪`. Rewrite using `[e, add_sub_cancel_left]`.

Conclude with `absNorm_mul_mem_hatId D 𝔪 hw`.
-/
theorem exists_red (h𝔪 : 𝔪 ≠ ⊥) (x : AE D) (hx : x ∈ OhE D) :
    ∃ r : 𝓞 D.host.E, x - inc D (r : D.host.E) ∈ hatId D 𝔪 := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  obtain ⟨r, hr, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D _ hn x hx
  refine ⟨⟨r, (mem_integralClosure_iff ℤ _).2 hr⟩, ?_⟩
  show x - inc D r ∈ hatId D 𝔪
  rw [e, add_sub_cancel_left]
  exact absNorm_mul_mem_hatId D 𝔪 hw

/- English proof (translation)
Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨(intG D N).mul_mem ((intG D N).inv_mem h₁) h₂, fun i j hj hi => ?_⟩` and prove the remaining obligations. Establish `hij : i ≠ j` using `fun e => by subst e; omega`. Establish `hinv` using `(mem_intG k₁).1 h₁`. Establish `e : (((k₁⁻¹ * k₂ : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = (((k₁ : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) * (((k₂ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - ((k₁ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) …`.

Rewrite using `[Matrix.mul_sub, Units.inv_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, Matrix.add_apply, Matrix.one_apply_ne hij, add_zero, Matrix.mul_apply]`. Conclude with `AddSubgroup.sum_mem _ fun l _ => mul_mem_hatId D 𝔪 ((hinv i l).2) (h l j)`.
-/
theorem mem_blockJ_of_congr {a N : ℕ} {k₁ k₂ : GA D N} (h₁ : k₁ ∈ intG D N) (h₂ : k₂ ∈ intG D N)
    (h : ∀ i j, ((k₂ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
      ((k₁ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪) :
    k₁⁻¹ * k₂ ∈ blockJ D 𝔪 a N := by
  apply Subgroup.subset_closure
  refine ⟨(intG D N).mul_mem ((intG D N).inv_mem h₁) h₂, fun i j hj hi => ?_⟩
  have hij : i ≠ j := fun e => by subst e; omega
  have hinv := (mem_intG k₁).1 h₁
  have e : (((k₁⁻¹ * k₂ : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      (((k₁ : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        (((k₂ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) -
          ((k₁ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) + 1 := by
    rw [Matrix.mul_sub, Units.inv_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    abel
  rw [e, Matrix.add_apply, Matrix.one_apply_ne hij, add_zero, Matrix.mul_apply]
  exact AddSubgroup.sum_mem _ fun l _ => mul_mem_hatId D 𝔪 ((hinv i l).2) (h l j)

end GlobalTheory.BotPairSmall.BlockIdx

namespace GlobalTheory.BotPairSmall

open BlockIdx in

/- English proof (translation)
Introduce `D 𝔪 h𝔪 a N`. Establish `hent : ∀ k : intG D N, ∀ i j, (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D` using `fun k i j => (((mem_intG _).1 k.2) i j).1`. Use `choose r hr using fun (k : intG D N) i j => exists_red D 𝔪 h𝔪 _ (hent k i j)`. Set `H` to `(blockJ D 𝔪 a N).subgroupOf (intG D N)`. Set `f : (intG D N ⧸ H) → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪)` to `fun q i j => Ideal.Quotient.mk 𝔪 (r q.out i j)`.

Establish `hf : Function.Injective f`. Introduce `q₁ q₂ e`. Rewrite using `[← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]`. Use `mem_blockJ_of_congr D 𝔪 q₁.out.2 q₂.out.2 fun i j => ?_` and prove the remaining obligations. Establish `e' : Ideal.Quotient.mk 𝔪 (r q₁.out i j) = Ideal.Quotient.mk 𝔪 (r q₂.out i j)` using `congrFun (congrFun e i) j`.

Rewrite `e'` using `[Ideal.Quotient.eq]`. Use `sub_mem (sub_mem (hr q₂.out i j) (gen_mem_hatId D 𝔪 e' (one_mem (OhE D)))) (hr q₁.out i j)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Rewrite using `[map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcard : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 D.host.E ⧸ 𝔪) := Nat.finite_of_card_ne_zero (by rw [hcard]; simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)`. Use `haveI : Finite (intG D N ⧸ H) := Finite.of_injective f hf`.

Use `⟨Subgroup.index_ne_zero_of_finite, ?_⟩` and prove the remaining obligations. Use `show H.index ≤ _`. Rewrite using `[Subgroup.index]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.card_fun, Nat.card_fun, Nat.card_fin, hcard, ← pow_mul, sq]`.
-/
theorem blockJ_relIndex : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (a N : ℕ),
    (GlobalTheory.BotPairSmall.blockJ D 𝔪 a N).relIndex (intG D N) ≠ 0 ∧
      (GlobalTheory.BotPairSmall.blockJ D 𝔪 a N).relIndex (intG D N) ≤ Ideal.absNorm 𝔪 ^ (N ^ 2) := by
  intro D 𝔪 h𝔪 a N
  have hent : ∀ k : intG D N, ∀ i j,
      (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D :=
    fun k i j => (((mem_intG _).1 k.2) i j).1
  choose r hr using fun (k : intG D N) i j => exists_red D 𝔪 h𝔪 _ (hent k i j)
  let H := (blockJ D 𝔪 a N).subgroupOf (intG D N)
  let f : (intG D N ⧸ H) → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) :=
    fun q i j => Ideal.Quotient.mk 𝔪 (r q.out i j)
  have hf : Function.Injective f := by
    intro q₁ q₂ e
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv]
    refine mem_blockJ_of_congr D 𝔪 q₁.out.2 q₂.out.2 fun i j => ?_
    have e' : Ideal.Quotient.mk 𝔪 (r q₁.out i j) = Ideal.Quotient.mk 𝔪 (r q₂.out i j) :=
      congrFun (congrFun e i) j
    rw [Ideal.Quotient.eq] at e'
    have := sub_mem (sub_mem (hr q₂.out i j) (gen_mem_hatId D 𝔪 e' (one_mem (OhE D)))) (hr q₁.out i j)
    convert this using 1
    push_cast
    rw [map_sub]
    ring
  have hcard : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  haveI : Finite (intG D N ⧸ H) := Finite.of_injective f hf
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  show H.index ≤ _
  rw [Subgroup.index]
  calc Nat.card (intG D N ⧸ H) ≤ Nat.card (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) := Nat.card_le_card_of_injective f hf
    _ = Ideal.absNorm 𝔪 ^ (N ^ 2) := by
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, hcard, ← pow_mul, sq]

end GlobalTheory.BotPairSmall
