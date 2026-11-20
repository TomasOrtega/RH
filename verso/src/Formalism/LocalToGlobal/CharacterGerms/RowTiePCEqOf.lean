import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartTop

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval

variable {C : Type} [Field C]

def RawChart.expG {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} (X : RawChart C d I κ) (g : Fin 2)
    (i : κ) : MvPowerSeries (I g) C :=
  MvPowerSeries.subst (fun j : κ => ∑ c : I g, X.u g c j • (MvPowerSeries.X c : MvPowerSeries (I g) C)) (X.ex i)

def CEqSumSt : Prop :=
  AllFB fun C _ V _ I _ dd X => ∀ (g : Fin 2) (H : X.CartHyp V g) (S : Sys (RawChart.cart H))
    (t : I g → MvPowerSeries (I g) C), S.IsT t →
    ∃ Φ : Fin dd → MvPowerSeries (I g) C, (∀ i, MvPowerSeries.constantCoeff (Φ i) = 0) ∧ (∀ i, IntS V (Φ i)) ∧
      (∀ i, MvPowerSeries.subst t (Φ i) = X.expG g i) ∧
      ∀ q : JJ I g, ∃ Λ : MvPowerSeries (I g) C, IntS V Λ ∧
        MvPowerSeries.subst (X.expG g) (X.sg (X.u (1 - g) q)) =
          S.ze t q + MvPowerSeries.subst t Λ + ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
            X.sg1 (X.u g c) (X.u (1 - g) q) • (MvPowerSeries.X c : MvPowerSeries (I g) C) else 0

def CEqDerSt : Prop :=
  AllFB fun C _ V _ I _ dd X => ∀ (g : Fin 2) (k : I (1 - g)), ∃ J : MvPowerSeries (Fin 2 × Fin dd) C, IntS V J ∧
    dVar (⟨1 - g, k⟩ : WV I) X.hRow =
      (X.k : C) • (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => X.expPt q.1 q.2) J -
        MvPowerSeries.subst (X.expPt g) (X.sg (X.u (1 - g) k)))

namespace RowTiePCEq

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _`.
-/
theorem hasSubst_X (g : Fin 2) : MvPowerSeries.HasSubst
    (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

/- English proof (translation)
Rewrite using `[MvPowerSeries.substAlgHom_apply]`. Both sides reduce to the same expression.
-/
theorem upG_eq (g : Fin 2) (F : MvPowerSeries (I g) C) :
    upG g F = MvPowerSeries.substAlgHom (hasSubst_X (C := C) g) F := by
  rw [MvPowerSeries.substAlgHom_apply]
  rfl

/- English proof (translation)
The claim follows from `constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) hF`.
-/
theorem upG_const (g : Fin 2) {F : MvPowerSeries (I g) C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (upG g F) = 0 :=
  constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) hF

/- English proof (translation)
Unfold `upG`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) (hasSubst_X g)]`.
-/
theorem upG_subst {σ : Type} [Finite σ] (g : Fin 2) {a : σ → MvPowerSeries (I g) C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    upG g (MvPowerSeries.subst a f) = MvPowerSeries.subst (fun s => upG g (a s)) f := by
  unfold upG
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) (hasSubst_X g)]

/- English proof (translation)
Unfold `upG`. Rewrite using `[MvPowerSeries.subst_X (hasSubst_X g)]`.
-/
theorem upG_X (g : Fin 2) (c : I g) :
    upG g (MvPowerSeries.X c : MvPowerSeries (I g) C) = MvPowerSeries.X (⟨g, c⟩ : WV I) := by
  unfold upG
  rw [MvPowerSeries.subst_X (hasSubst_X g)]

/- English proof (translation)
The claim follows from `IntS.subst (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X _) hF`.
-/
theorem intS_upG {V : VF C} (g : Fin 2) {F : MvPowerSeries (I g) C} (hF : IntS V F) : IntS V (upG g F) :=
  IntS.subst (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X _) hF

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X, mul_zero]`.
-/
theorem lin_const {κ : Type} (X : RawChart C d I κ) (g : Fin 2) (j : κ) :
    MvPowerSeries.constantCoeff (∑ c : I g, X.u g c j • (MvPowerSeries.X c : MvPowerSeries (I g) C)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X, mul_zero]

/- English proof (translation)
Unfold `RawChart.expG`. Rewrite using `[upG_subst g (lin_const X g)]`. Unfold `RawChart.expPt`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Rewrite using `[upG_eq, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← upG_eq, upG_X]`.
-/
theorem expPt_eq {κ : Type} [Fintype κ] (X : RawChart C d I κ) (g : Fin 2) (i : κ) :
    X.expPt g i = upG g (X.expG g i) := by
  unfold RawChart.expG
  rw [upG_subst g (lin_const X g)]
  unfold RawChart.expPt
  congr 1
  funext j
  rw [upG_eq, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, ← upG_eq, upG_X]

def tW (t : ∀ g, I g → MvPowerSeries (I g) C) : WV I → MvPowerSeries (WV I) C := fun w => upG w.1 (t w.1 w.2)

/- English proof (translation)
Introduce `w` and use `upG_const _ (ht _ _)`.
-/
theorem tW_const {t : ∀ g, I g → MvPowerSeries (I g) C} (ht : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) :
    ∀ w, MvPowerSeries.constantCoeff (tW t w) = 0 := fun w => upG_const _ (ht _ _)

/- English proof (translation)
Rewrite using `[upG_subst g (ht g) f]`. Use `show MvPowerSeries.subst (tW t) (MvPowerSeries.subst _ f) = _`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (hasSubst_X g) (MvPowerSeries.hasSubst_of_constantCoeff_zero (tW_const ht))]`. Use `congr 1`. Use function extensionality and compare the values at `c`.

Rewrite using `[MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (tW_const ht))]`. Both sides reduce to the same expression.
-/
theorem subst_tW_upG {t : ∀ g, I g → MvPowerSeries (I g) C} (ht : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0)
    (g : Fin 2) (f : MvPowerSeries (I g) C) :
    MvPowerSeries.subst (tW t) (upG g f) = upG g (MvPowerSeries.subst (t g) f) := by
  rw [upG_subst g (ht g) f]
  show MvPowerSeries.subst (tW t) (MvPowerSeries.subst _ f) = _
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_X g)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (tW_const ht))]
  congr 1
  funext c
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (tW_const ht))]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_toLeaf {V : VF C} {J : Fin 2 → Type} [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) (F : MvPowerSeries (WV I) C) (μ : WV I →₀ ℕ) :
    MvPowerSeries.coeff μ (toLeaf G g a a' F) =
      if ∀ w ∈ μ.support, OnLeafV G g a a' w then MvPowerSeries.coeff μ F else 0 := rfl

def toLeafL {V : VF C} {J : Fin 2 → Type} [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) : MvPowerSeries (WV I) C →ₗ[C] MvPowerSeries (WV I) C where
  toFun := toLeaf G g a a'
  map_add' F F' := by
    ext μ
    rw [coeff_toLeaf, map_add, map_add, coeff_toLeaf, coeff_toLeaf]
    split_ifs <;> simp
  map_smul' r F := by
    ext μ
    rw [coeff_toLeaf, RingHom.id_apply, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_toLeaf]
    split_ifs <;> simp

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[coeff_toLeaf, MvPowerSeries.coeff_X, map_zero]`. Use `split_ifs with h1 h2`. It suffices to derive a contradiction. Apply `hw` to reduce the goal to its premises.

Apply `h1` to reduce the goal to its premises. Rewrite using `[h2]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem toLeaf_X_off {V : VF C} {J : Fin 2 → Type} [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) (w : WV I) (hw : ¬ OnLeafV G g a a' w) :
    toLeaf G g a a' (MvPowerSeries.X w : MvPowerSeries (WV I) C) = 0 := by
  ext μ
  rw [coeff_toLeaf, MvPowerSeries.coeff_X, map_zero]
  split_ifs with h1 h2
  · exfalso
    apply hw
    apply h1
    rw [h2]
    simp
  · rfl
  · rfl

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[coeff_toLeaf]`. Establish `key : (∀ x ∈ (μ + Finsupp.single w 1).support, X.OnLf g a a' x) ↔ ∀ x ∈ μ.support, X.OnLf g a a' x`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`.

Apply `h` to reduce the goal to its premises. Rewrite `hx`, the goal using `[Finsupp.mem_support_iff]`. Rewrite using `[Finsupp.add_apply]`. Use linear arithmetic over natural numbers and integers. Introduce `h x hx`.

Distinguish the cases in `hxw : x = w`. Conclude with `hxw ▸ hw`. Apply `h` to reduce the goal to its premises. Rewrite `hx`, the goal using `[Finsupp.mem_support_iff]`. Rewrite `hx` using `[Finsupp.add_apply, Finsupp.single_eq_of_ne hxw, add_zero]`. Then use the resulting hypothesis.

Use `show ((μ w + 1 : ℕ) : C) * (if ∀ x ∈ (μ + Finsupp.single w 1).support, X.OnLf g a a' x then MvPowerSeries.coeff (μ + Finsupp.single w 1) X.hRow else 0) = if ∀ x ∈ μ.support, X.OnLf g a a' x then ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) X.hRow else 0`. Distinguish the cases in `hc : ∀ x ∈ μ.support, X.OnLf g a a' x`. Rewrite using `[if_pos (key.2 hc), if_pos hc]`. Rewrite using `[if_neg (fun h => hc (key.1 h)), if_neg hc, mul_zero]`.
-/
theorem dVar_hLf {κ : Type} [Fintype κ] {V : VF C} (X : RawChart C d I κ) (H : ∀ g, X.CartHyp V g)
    (g : Fin 2) (a a' : ZMod d) (w : WV I) (hw : X.OnLf g a a' w) :
    dVar w (X.hLf g a a') = toLeaf (fun g => RawChart.cart (H g)) g a a' (dVar w X.hRow) := by
  ext μ
  rw [coeff_toLeaf]
  have key : (∀ x ∈ (μ + Finsupp.single w 1).support, X.OnLf g a a' x) ↔ ∀ x ∈ μ.support, X.OnLf g a a' x := by
    constructor
    · intro h x hx
      apply h
      rw [Finsupp.mem_support_iff] at hx ⊢
      rw [Finsupp.add_apply]
      omega
    · intro h x hx
      by_cases hxw : x = w
      · exact hxw ▸ hw
      · apply h
        rw [Finsupp.mem_support_iff] at hx ⊢
        rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hxw, add_zero] at hx
  show ((μ w + 1 : ℕ) : C) * (if ∀ x ∈ (μ + Finsupp.single w 1).support, X.OnLf g a a' x then
      MvPowerSeries.coeff (μ + Finsupp.single w 1) X.hRow else 0) =
    if ∀ x ∈ μ.support, X.OnLf g a a' x then ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) X.hRow
      else 0
  by_cases hc : ∀ x ∈ μ.support, X.OnLf g a a' x
  · rw [if_pos (key.2 hc), if_pos hc]
  · rw [if_neg (fun h => hc (key.1 h)), if_neg hc, mul_zero]

end RowTiePCEq

open RowTiePCEq

/- English proof (translation)
Introduce `C _ _ V O _ _ dd Y d _ I _ p _ H _ g a a' hodd S t ht k hk`. Use `set X := Y.raw p with hX`. Establish `ht0 : ∀ g' c, MvPowerSeries.constantCoeff (t g' c) = 0` using `fun g' => (ht g').1`. Establish `hT` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (tW_const ht0)`. Establish `hne : a ≠ a'`.

Introduce `h`. Substitute `h` using the available equality. Rewrite `hodd` using `[sub_self, ZMod.val_zero]`. Use `Nat.odd_iff.mp hodd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hSg` using `fun g' => hS C V O dd Y d I p g' (H g') (S g') (t g') (ht g')`. Use `choose Φ hΦ0 hΦI hΦt hΛ using hSg`. Take `⟨Λ, hΛI, hσ⟩` from `hΛ g k`. Take `⟨J, hJI, hder⟩` from `hD C V O dd Y d I p g k`. Use `set Φ' : Fin 2 × Fin dd → MvPowerSeries (WV I) C := fun q => upG q.1 (Φ q.1 q.2) with hΦ'`.

Establish `hΦ'0 : ∀ q, MvPowerSeries.constantCoeff (Φ' q) = 0` using `fun q => upG_const _ (hΦ0 q.1 q.2)`. Establish `hΦ'I : ∀ q, IntS V (Φ' q)` using `fun q => intS_upG _ (hΦI q.1 q.2)`. Establish `hΨ : (fun q : Fin 2 × Fin dd => X.expPt q.1 q.2) = fun q => MvPowerSeries.subst (tW t) (Φ' q)`. Use function extensionality and compare the values at `q`. Rewrite using `[expPt_eq, ← hΦt q.1 q.2, subst_tW_upG ht0]`.

Establish `hJ' : MvPowerSeries.subst (fun q : Fin 2 × Fin dd => X.expPt q.1 q.2) J = MvPowerSeries.subst (tW t) (MvPowerSeries.subst Φ' J)`. Rewrite using `[hΨ, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hΦ'0) hT]`. Establish `hexG0 : ∀ i, MvPowerSeries.constantCoeff (X.expG g i) = 0` using `fun i => by`. Rewrite using `[← hΦt g i]`. Conclude with `constantCoeff_subst_zero (ht0 g) (hΦ0 g i)`.

Establish `hsg : MvPowerSeries.subst (X.expPt g) (X.sg (X.u (1 - g) k)) = upG g (MvPowerSeries.subst (X.expG g) (X.sg (X.u (1 - g) k)))`. Rewrite using `[upG_subst g hexG0]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `expPt_eq X g i`.

Use `set sig0 : MvPowerSeries (I g) C := ∑ c : I g, if X.ty g c = X.ty (1 - g) k then X.sg1 (X.u g c) (X.u (1 - g) k) • (MvPowerSeries.X c : MvPowerSeries (I g) C) else 0 with hsig0`. Use `set L := toLeafL (fun g => RawChart.cart (H g)) g a a' with hL`. Establish `hsig : L (upG g sig0) = 0`. Rewrite using `[hsig0, upG_eq, map_sum, map_sum]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Use `split_ifs with hc`. Rewrite using `[map_smul, map_smul, ← upG_eq, upG_X]`. Establish `: L (MvPowerSeries.X (⟨g, c⟩ : WV I)) = 0`. Use `toLeaf_X_off _ g a a' _ ?_` and prove the remaining obligations. Introduce and unpack `(⟨-, h2⟩ | ⟨h1, -⟩)`.

Conclude with `hne (h2.symm.trans (hc.trans hk))`. Apply the tactic sequence `fin_cases g <;> simp at h1`. Rewrite using `[this, smul_zero]`. Rewrite using `[map_zero, map_zero]`. Use `⟨MvPowerSeries.subst (tW t) ((X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ)), ⟨(X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ), fun μ => ?_, rfl⟩, ?_⟩` and prove the remaining obligations.

Establish `hI : IntS V ((X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ))`. Introduce `ν`. Rewrite using `[MvPowerSeries.coeff_smul, map_sub]`. Conclude with `(ge_natCast _).mul_int ((IntS.subst hΦ'0 hΦ'I hJI ν).sub (intS_upG g hΛI ν))`. Conclude with `hI μ`.

Establish `hpair : (∑ q : JJ I g, X.pairK g q k • upG g ((S g).ze (t g) q)) = (-(X.k : C)) • upG g ((S g).ze (t g) k)`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using `[RawChart.pairK]`. Introduce `q _ hq`. Simplify using `[RawChart.pairK, hq]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`. Establish `hw : X.OnLf g a a' (⟨1 - g, k⟩ : WV I)` using `Or.inr ⟨rfl, hk⟩`. Rewrite using `[dVar_hLf X H g a a' _ hw, hpair, hder, hJ', hsg, hσ]`. Establish `e1 : upG g ((S g).ze (t g) k + MvPowerSeries.subst (t g) Λ + sig0) = upG g ((S g).ze (t g) k) + MvPowerSeries.subst (tW t) (upG g Λ) + upG g sig0`.

Rewrite using `[upG_eq, map_add, map_add, ← upG_eq, ← upG_eq, ← upG_eq, subst_tW_upG ht0]`. Establish `e2 : MvPowerSeries.subst (tW t) ((X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ)) = (X.k : C) • (MvPowerSeries.subst (tW t) (MvPowerSeries.subst Φ' J) - MvPowerSeries.subst (tW t) (upG g Λ))`. Rewrite using `[← MvPowerSeries.coe_substAlgHom hT, map_smul, map_sub]`. Rewrite using `[e1, e2]`. Use `show L _ - L _ = L _`.

Simplify using `only [map_smul, map_sub, map_add, hsig]`. Use `module`.
-/
theorem cEqFB_of (hS : CEqSumSt) (hD : CEqDerSt) : CEqFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p _ H _ g a a' hodd S t ht k hk
  set X := Y.raw p with hX
  have ht0 : ∀ g' c, MvPowerSeries.constantCoeff (t g' c) = 0 := fun g' => (ht g').1
  have hT := MvPowerSeries.hasSubst_of_constantCoeff_zero (tW_const ht0)
  have hne : a ≠ a' := by
    intro h
    subst h
    rw [sub_self, ZMod.val_zero] at hodd
    have := Nat.odd_iff.mp hodd
    omega
  have hSg := fun g' => hS C V O dd Y d I p g' (H g') (S g') (t g') (ht g')
  choose Φ hΦ0 hΦI hΦt hΛ using hSg
  obtain ⟨Λ, hΛI, hσ⟩ := hΛ g k
  obtain ⟨J, hJI, hder⟩ := hD C V O dd Y d I p g k
  set Φ' : Fin 2 × Fin dd → MvPowerSeries (WV I) C := fun q => upG q.1 (Φ q.1 q.2) with hΦ'
  have hΦ'0 : ∀ q, MvPowerSeries.constantCoeff (Φ' q) = 0 := fun q => upG_const _ (hΦ0 q.1 q.2)
  have hΦ'I : ∀ q, IntS V (Φ' q) := fun q => intS_upG _ (hΦI q.1 q.2)
  have hΨ : (fun q : Fin 2 × Fin dd => X.expPt q.1 q.2) = fun q => MvPowerSeries.subst (tW t) (Φ' q) := by
    funext q
    rw [expPt_eq, ← hΦt q.1 q.2, subst_tW_upG ht0]
  have hJ' : MvPowerSeries.subst (fun q : Fin 2 × Fin dd => X.expPt q.1 q.2) J =
      MvPowerSeries.subst (tW t) (MvPowerSeries.subst Φ' J) := by
    rw [hΨ, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hΦ'0) hT]
  have hexG0 : ∀ i, MvPowerSeries.constantCoeff (X.expG g i) = 0 := fun i => by
    rw [← hΦt g i]
    exact constantCoeff_subst_zero (ht0 g) (hΦ0 g i)
  have hsg : MvPowerSeries.subst (X.expPt g) (X.sg (X.u (1 - g) k)) =
      upG g (MvPowerSeries.subst (X.expG g) (X.sg (X.u (1 - g) k))) := by
    rw [upG_subst g hexG0]
    congr 1
    funext i
    exact expPt_eq X g i
  set sig0 : MvPowerSeries (I g) C := ∑ c : I g, if X.ty g c = X.ty (1 - g) k then
    X.sg1 (X.u g c) (X.u (1 - g) k) • (MvPowerSeries.X c : MvPowerSeries (I g) C) else 0 with hsig0
  set L := toLeafL (fun g => RawChart.cart (H g)) g a a' with hL
  have hsig : L (upG g sig0) = 0 := by
    rw [hsig0, upG_eq, map_sum, map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with hc
    · rw [map_smul, map_smul, ← upG_eq, upG_X]
      have : L (MvPowerSeries.X (⟨g, c⟩ : WV I)) = 0 := by
        refine toLeaf_X_off _ g a a' _ ?_
        rintro (⟨-, h2⟩ | ⟨h1, -⟩)
        · exact hne (h2.symm.trans (hc.trans hk))
        · fin_cases g <;> simp at h1
      rw [this, smul_zero]
    · rw [map_zero, map_zero]
  refine ⟨MvPowerSeries.subst (tW t) ((X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ)),
    ⟨(X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ), fun μ => ?_, rfl⟩, ?_⟩
  · have hI : IntS V ((X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ)) := by
      intro ν
      rw [MvPowerSeries.coeff_smul, map_sub]
      exact (ge_natCast _).mul_int ((IntS.subst hΦ'0 hΦ'I hJI ν).sub (intS_upG g hΛI ν))
    exact hI μ
  · have hpair : (∑ q : JJ I g, X.pairK g q k • upG g ((S g).ze (t g) q)) =
        (-(X.k : C)) • upG g ((S g).ze (t g) k) := by
      rw [Finset.sum_eq_single k]
      · simp [RawChart.pairK]
      · intro q _ hq
        simp [RawChart.pairK, hq]
      · intro h
        exact absurd (Finset.mem_univ k) h
    have hw : X.OnLf g a a' (⟨1 - g, k⟩ : WV I) := Or.inr ⟨rfl, hk⟩
    rw [dVar_hLf X H g a a' _ hw, hpair, hder, hJ', hsg, hσ]
    have e1 : upG g ((S g).ze (t g) k + MvPowerSeries.subst (t g) Λ + sig0) =
        upG g ((S g).ze (t g) k) + MvPowerSeries.subst (tW t) (upG g Λ) + upG g sig0 := by
      rw [upG_eq, map_add, map_add, ← upG_eq, ← upG_eq, ← upG_eq, subst_tW_upG ht0]
    have e2 : MvPowerSeries.subst (tW t) ((X.k : C) • (MvPowerSeries.subst Φ' J - upG g Λ)) =
        (X.k : C) • (MvPowerSeries.subst (tW t) (MvPowerSeries.subst Φ' J) -
          MvPowerSeries.subst (tW t) (upG g Λ)) := by
      rw [← MvPowerSeries.coe_substAlgHom hT, map_smul, map_sub]
    rw [e1, e2]
    show L _ - L _ = L _
    simp only [map_smul, map_sub, map_add, hsig]
    module

end Formalism.L2.FormalSeriesBounds
