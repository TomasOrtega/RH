import Mathlib

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.DimCodim

section

attribute [local instance low] specializationOrder

/- English proof (translation)
Establish `hmono : StrictMono j`. Introduce `x y hxy`. Use `lt_of_le_of_ne ?_ (fun hxy' => hxy.ne (hi hxy'))` and prove the remaining obligations. Conclude with `(show y ⤳ x from hxy.le).map hj`. Rewrite using `[topologicalKrullDim, topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := W)), Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S))]`.

Break down `isEmpty_or_nonempty W with hW | hW` into its components or cases. Rewrite using `[Order.krullDim_eq_bot]`. Simplify using the standard rewrite rules. Establish `: Nonempty S` using `⟨j hW.some⟩`. Rewrite using `[Order.krullDim_eq_iSup_height_of_nonempty, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add, WithBot.coe_le_coe, ENat.iSup_add]`.

Use `iSup_le fun w => le_trans ?_ (le_iSup (fun a : S => Order.height a + Order.coheight a) (j w))` and prove the remaining obligations. Conclude with `add_le_add (Order.height_le_height_apply_of_strictMono j hmono w) (h w)`.
-/
theorem dim_add_le_of_le_coheight {S W : Type*} [TopologicalSpace S] [TopologicalSpace W]
    [QuasiSober S] [T0Space S] [QuasiSober W] [T0Space W] {j : W → S} (hj : Continuous j)
    (hi : Function.Injective j) (c : ℕ∞) (h : ∀ w, c ≤ Order.coheight (j w)) :
    topologicalKrullDim W + c ≤ topologicalKrullDim S := by
  have hmono : StrictMono j := by
    intro x y hxy
    refine lt_of_le_of_ne ?_ (fun hxy' => hxy.ne (hi hxy'))
    exact (show y ⤳ x from hxy.le).map hj
  rw [topologicalKrullDim, topologicalKrullDim,
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := W)),
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S))]
  rcases isEmpty_or_nonempty W with hW | hW
  · rw [Order.krullDim_eq_bot]
    simp
  · have : Nonempty S := ⟨j hW.some⟩
    rw [Order.krullDim_eq_iSup_height_of_nonempty,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add,
      WithBot.coe_le_coe, ENat.iSup_add]
    refine iSup_le fun w => le_trans ?_
      (le_iSup (fun a : S => Order.height a + Order.coheight a) (j w))
    exact add_le_add (Order.height_le_height_apply_of_strictMono j hmono w) (h w)

end

/- English proof (translation)
Establish `hc : IsClosed ((U : Set X)ᶜ)` using `U.isOpen.isClosed_compl`. Establish `: QuasiSober ((U : Set X)ᶜ : Set X)` using `hc.isClosedEmbedding_subtypeVal.quasiSober`. Establish `key : topologicalKrullDim ((U : Set X)ᶜ : Set X) + ((2 : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X`. Apply `dim_add_le_of_le_coheight continuous_subtype_val Subtype.val_injective` to reduce the goal to its premises. Introduce `w`.

Establish `hlt : 1 < ringKrullDim (X.presheaf.stalk w.1)` using `lt_of_not_ge fun h => w.2 (hU _ h)`. Rewrite `hlt` using `[AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]`. Establish `h1 : (1 : ℕ∞) < Order.coheight w.1` using `by exact_mod_cast hlt`. Use `Order.add_one_le_of_lt h1` as an intermediate fact. Conclude with `le_trans (by norm_num) this`.

Rewrite `key` using `[hX]`. Generalize the expression as in `topologicalKrullDim ((U : Set X)ᶜ : Set X) = D at key ⊢`. Proceed by induction on `D using WithBot.recBotCoe with`. Consider the case `bot => simp`. Consider the case `coe m`.

Rewrite `key` using `[← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_le_coe]`. Rewrite using `[← WithBot.coe_natCast, ← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]`. Proceed by induction on `m using ENat.recTopCoe with`. Consider the case `top => exfalso`. Simplify using `at key`.

Consider the case `coe n`. Normalize the coercions in `at key ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem dim_compl_add_one_le (X : Scheme.{0}) (U : X.Opens) (d : ℕ)
    (hX : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hU : ∀ y : X, ringKrullDim (X.presheaf.stalk y) ≤ 1 → y ∈ U) :
    topologicalKrullDim ((U : Set X)ᶜ : Set X) + 1 ≤ (d : WithBot ℕ∞) := by
  have hc : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have : QuasiSober ((U : Set X)ᶜ : Set X) := hc.isClosedEmbedding_subtypeVal.quasiSober
  have key : topologicalKrullDim ((U : Set X)ᶜ : Set X) + ((2 : ℕ∞) : WithBot ℕ∞) ≤
      topologicalKrullDim X := by
    apply dim_add_le_of_le_coheight continuous_subtype_val Subtype.val_injective
    intro w
    have hlt : 1 < ringKrullDim (X.presheaf.stalk w.1) :=
      lt_of_not_ge fun h => w.2 (hU _ h)
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at hlt
    have h1 : (1 : ℕ∞) < Order.coheight w.1 := by exact_mod_cast hlt
    have := Order.add_one_le_of_lt h1
    exact le_trans (by norm_num) this
  rw [hX] at key
  generalize topologicalKrullDim ((U : Set X)ᶜ : Set X) = D at key ⊢
  induction D using WithBot.recBotCoe with
  | bot => simp
  | coe m =>
    rw [← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_le_coe] at key
    rw [← WithBot.coe_natCast, ← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
    induction m using ENat.recTopCoe with
    | top => exfalso; simp at key
    | coe n =>
      norm_cast at key ⊢
      omega

end GlobalTheory.DimCodim
