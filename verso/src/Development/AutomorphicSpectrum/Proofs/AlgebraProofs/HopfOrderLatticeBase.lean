import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import ReciprocityTheory.DualLattices.ImportsBis
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CompanionTheory.Ar.Num.StepOnto

def stepSub (F : Type) [Field F] (n i : ℕ) : AddSubgroup (Fin n → F) where
  carrier := {x | ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0}
  add_mem' := by
    intro a b ha hb j hj
    simp [ha j hj, hb j hj]
  zero_mem' := by
    intro j _
    rfl
  neg_mem' := by
    intro a ha j hj
    simp [ha j hj]

/- English proof (translation)
Take `⟨-, -, -, H4⟩` from `ReciprocityTheory.PGsh.L2.h3 C R ‹IsAlgClosed C› ‹CharZero C› v hv N K AA`. Establish `hg' : g ∈ augIdeal AA.carrier`. Use `Submodule.mem_inf.2 ⟨hg, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker]`. Conclude with `h0`.

Establish `hres : ReciprocityTheory.PGsh.L2.resK (R` using `R) K g = 0 := by`. Use function extensionality and compare the values at `k`. Use `show g k = 0`. Conclude with `hK k k.2`. Establish `h2` using `H4 g hg' (by rw [hres]; exact zero_mem _)`.

Take `⟨h, hh, q, hq, hgq⟩` from `Submodule.mem_sup.1 h2`. Take `⟨b, hb, rfl⟩` from `hh`. Take `⟨hbA, hb0⟩` from `Submodule.mem_inf.1 hb`. Use `⟨_, hbA, q, ?_, ?_, ?_, hgq.symm⟩` and prove the remaining obligations. Establish `hsq : augIdeal AA.carrier * augIdeal AA.carrier ≤ sqIdeal (augIdeal AA.carrier)`.

Rewrite using `[Submodule.mul_le]`. Introduce `x hx y hy`. Use `show x * y ∈ Submodule.span R {h | ∃ f ∈ augIdeal AA.carrier, ∃ f' ∈ augIdeal AA.carrier, h = f * f'}`. Conclude with `Submodule.subset_span ⟨x, hx, y, hy, rfl⟩`. Conclude with `hsq hq`.

Use `show b (QuotientAddGroup.mk 0) = 0`. Rewrite using `[QuotientAddGroup.mk_zero]`. Conclude with `LinearMap.mem_ker.1 hb0`. Introduce `x k hk show b (QuotientAddGroup.mk (x + k)) = b (QuotientAddGroup.mk x)`. Establish `hk0 : (QuotientAddGroup.mk k : N ⧸ K) = 0` using `(QuotientAddGroup.eq_zero_iff k).2 hk`.

Rewrite using `[QuotientAddGroup.mk_add, hk0, add_zero]`.
-/
theorem exists_inv_add_sq {C R : Type} [Field C] [IsAlgClosed C] [CharZero C] [CommRing R]
    [Algebra R C] (v : Valuation C NNReal) (hv : v.Integers R) {N : Type} [AddCommGroup N]
    [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) (g : N → C)
    (hg : g ∈ AA.carrier) (h0 : g 0 = 0) (hK : ∀ k ∈ K, g k = 0) :
    ∃ h ∈ AA.carrier, ∃ q ∈ sqIdeal (augIdeal AA.carrier),
      h 0 = 0 ∧ (∀ x, ∀ k ∈ K, h (x + k) = h x) ∧ g = h + q := by
  classical
  obtain ⟨-, -, -, H4⟩ := ReciprocityTheory.PGsh.L2.h3 C R ‹IsAlgClosed C› ‹CharZero C› v hv N K AA
  have hg' : g ∈ augIdeal AA.carrier := by
    refine Submodule.mem_inf.2 ⟨hg, ?_⟩
    rw [LinearMap.mem_ker]
    exact h0
  have hres : ReciprocityTheory.PGsh.L2.resK (R := R) K g = 0 := by
    funext k
    show g k = 0
    exact hK k k.2
  have h2 := H4 g hg' (by rw [hres]; exact zero_mem _)
  obtain ⟨h, hh, q, hq, hgq⟩ := Submodule.mem_sup.1 h2
  obtain ⟨b, hb, rfl⟩ := hh
  obtain ⟨hbA, hb0⟩ := Submodule.mem_inf.1 hb
  refine ⟨_, hbA, q, ?_, ?_, ?_, hgq.symm⟩
  · have hsq : augIdeal AA.carrier * augIdeal AA.carrier ≤ sqIdeal (augIdeal AA.carrier) := by
      rw [Submodule.mul_le]
      intro x hx y hy
      show x * y ∈ Submodule.span R {h | ∃ f ∈ augIdeal AA.carrier, ∃ f' ∈ augIdeal AA.carrier, h = f * f'}
      exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
    exact hsq hq
  · show b (QuotientAddGroup.mk 0) = 0
    rw [QuotientAddGroup.mk_zero]
    exact LinearMap.mem_ker.1 hb0
  · intro x k hk
    show b (QuotientAddGroup.mk (x + k)) = b (QuotientAddGroup.mk x)
    have hk0 : (QuotientAddGroup.mk k : N ⧸ K) = 0 := (QuotientAddGroup.eq_zero_iff k).2 hk
    rw [QuotientAddGroup.mk_add, hk0, add_zero]

/- English proof (translation)
Establish `hmem : ∀ a : Fˣ, (u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m)) ∈ T` using `fun a => hs u hu _ (hs _ (hS _) _ (heq _ h m hm))`. It suffices to establish `e : ((fun x => u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)), m) = ∑ a : Fˣ, u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m) by`. Rewrite using `[e]`. Conclude with `T.sum_mem (fun a _ => hmem a)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[Prod.fst_sum]`. Use function extensionality and compare the values at `x`. Simplify using `only`. Rewrite using `[Finset.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations.

Simplify using `[Prod.smul_fst, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Rewrite using `[Prod.snd_sum]`. Establish `hterm : ∀ a : Fˣ, (u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m)).2 = u • m`. Introduce `a`. Simplify using `only [Prod.smul_snd, smul_smul]`.

Rewrite using `[mul_assoc, ← hmul, Units.inv_mul, h1, mul_one]`. Rewrite using `[Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul C, smul_smul, mul_comm, hu', one_smul]`.
-/
theorem avg_mem {C V X F : Type} [Field C] [AddCommGroup V] [Module C V] [Field F] [Fintype F]
    [DecidableEq F] [AddCommGroup X] [Module F X]
    (T : AddSubgroup ((X → C) × V)) (S : Set C) (hs : ∀ a ∈ S, ∀ t ∈ T, a • t ∈ T)
    (χ : F → C) (hS : ∀ a, χ a ∈ S) (hmul : ∀ a b, χ (a * b) = χ a * χ b) (h1 : χ 1 = 1)
    (u : C) (hu : u ∈ S) (hu' : u * (Fintype.card Fˣ : C) = 1)
    (heq : ∀ (a : F) g m, (g, m) ∈ T → ((fun x => g (a • x)), χ a • m) ∈ T)
    (h : X → C) (m : V) (hm : (h, m) ∈ T) :
    ((fun x => u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)), m) ∈ T := by
  have hmem : ∀ a : Fˣ, (u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m)) ∈ T :=
    fun a => hs u hu _ (hs _ (hS _) _ (heq _ h m hm))
  suffices e : ((fun x => u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)), m) =
      ∑ a : Fˣ, u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m) by
    rw [e]
    exact T.sum_mem (fun a _ => hmem a)
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    funext x
    dsimp only
    rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · rw [Prod.snd_sum]
    have hterm : ∀ a : Fˣ, (u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m)).2 = u • m := by
      intro a
      simp only [Prod.smul_snd, smul_smul]
      rw [mul_assoc, ← hmul, Units.inv_mul, h1, mul_one]
    rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul C, smul_smul, mul_comm, hu', one_smul]

/- English proof (translation)
Establish `key : ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (b : F) • x) = ∑ c : Fˣ, χ (b : F) * (χ ((c⁻¹ : Fˣ) : F) * h ((c : F) • x))`. Use `Fintype.sum_equiv (Equiv.mulRight b) _ _ (fun a => ?_)` and prove the remaining obligations. Use `show χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (b : F) • x) = χ (b : F) * (χ (((a * b)⁻¹ : Fˣ) : F) * h (((a * b : Fˣ) : F) • x))`. Rewrite using `[smul_smul, ← mul_assoc, ← hmul, Units.val_mul, mul_inv_rev, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]`. Rewrite using `[key, ← Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem avg_smul {C X F : Type} [Field C] [Field F] [Fintype F] [DecidableEq F] [AddCommGroup X]
    [Module F X] (χ : F → C) (hmul : ∀ a b, χ (a * b) = χ a * χ b) (h1 : χ 1 = 1) (u : C)
    (h : X → C) (b : Fˣ) (x : X) :
    u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (b : F) • x) =
      χ (b : F) * (u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)) := by
  have key : ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (b : F) • x) =
      ∑ c : Fˣ, χ (b : F) * (χ ((c⁻¹ : Fˣ) : F) * h ((c : F) • x)) := by
    refine Fintype.sum_equiv (Equiv.mulRight b) _ _ (fun a => ?_)
    show χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (b : F) • x) =
      χ (b : F) * (χ (((a * b)⁻¹ : Fˣ) : F) * h (((a * b : Fˣ) : F) • x))
    rw [smul_smul, ← mul_assoc, ← hmul, Units.val_mul, mul_inv_rev, Units.val_mul, ← mul_assoc,
      Units.mul_inv, one_mul]
  rw [key, ← Finset.mul_sum]
  ring

/- English proof (translation)
Rewrite using `[Submodule.mem_toAddSubgroup]`. Use `show g ∈ Submodule.pi {x : Fin n → F | ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0} (fun _ => (⊥ : Submodule C C)) ↔ _`. Simplify using `only [Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]`.
-/
theorem mem_vanSub {C F : Type} [Field C] [Field F] {n i : ℕ} (g : (Fin n → F) → C) :
    g ∈ (vanSub C F n i).toAddSubgroup ↔ ∀ x : Fin n → F, (∀ j : Fin n, i ≤ (j : ℕ) → x j = 0) → g x = 0 := by
  rw [Submodule.mem_toAddSubgroup]
  show g ∈ Submodule.pi {x : Fin n → F | ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0} (fun _ => (⊥ : Submodule C C)) ↔ _
  simp only [Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]

/- English proof (translation)
Establish `hk : x - x i • Pi.single i 1 ∈ stepSub F n i` using `by show ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → (x - x i • (Pi.single i 1 : Fin n → F) : Fin n → F) j = 0`. Introduce `j hj`. Break down `eq_or_lt_of_le hj with hij | hij` into its components or cases. Establish `hji : j = i` using `Fin.ext hij.symm`. Substitute `hji` using the available equality.

Simplify using the standard rewrite rules. Establish `hne : j ≠ i` using `fun e => by subst e; exact lt_irrefl _ hij`. Simplify using `[hx j hij, Pi.single_apply, hne]`. Establish `e : H x = H (x i • Pi.single i 1)`. Use `hinv (x i • Pi.single i 1) _ hk` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[e]`. Distinguish the cases in `hxi : x i = 0`. Rewrite using `[hxi, zero_smul, h0, hχ0, mul_zero]`. Use `hsm (Units.mk0 (x i) hxi) (Pi.single i 1)` as an intermediate fact.

Rewrite `this` using `[Units.val_mk0]`. Rewrite using `[this, mul_comm]`.
-/
theorem eq_on_step {C F : Type} [Field C] [Field F] {n : ℕ} (i : Fin n) (H : (Fin n → F) → C)
    (χ : F → C) (hχ0 : χ 0 = 0)
    (hinv : ∀ y, ∀ k ∈ stepSub F n i, H (y + k) = H y)
    (hsm : ∀ (b : Fˣ) y, H ((b : F) • y) = χ (b : F) * H y) (h0 : H 0 = 0)
    (x : Fin n → F) (hx : ∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → x j = 0) :
    H x = H (Pi.single i 1) * χ (x i) := by
  have hk : x - x i • Pi.single i 1 ∈ stepSub F n i := by
    show ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → (x - x i • (Pi.single i 1 : Fin n → F) : Fin n → F) j = 0
    intro j hj
    rcases eq_or_lt_of_le hj with hij | hij
    · have hji : j = i := Fin.ext hij.symm
      subst hji
      simp
    · have hne : j ≠ i := fun e => by subst e; exact lt_irrefl _ hij
      simp [hx j hij, Pi.single_apply, hne]
  have e : H x = H (x i • Pi.single i 1) := by
    have := hinv (x i • Pi.single i 1) _ hk
    rwa [add_sub_cancel] at this
  rw [e]
  by_cases hxi : x i = 0
  · rw [hxi, zero_smul, h0, hχ0, mul_zero]
  · have := hsm (Units.mk0 (x i) hxi) (Pi.single i 1)
    rw [Units.val_mk0] at this
    rw [this, mul_comm]

end GlobalTheory.CompanionTheory.Ar.Num.StepOnto

namespace GlobalTheory.CompanionTheory.Ar.Num

open StepOnto

/- English proof (translation)
Introduce `o C _ _ _ _ _ RC v hRC p _ hp F _ _ _ _ n Sg r s D w χ φ hB AA hAA hFS σ hσ hfl e hχ hφ hTh τ i`. Take `⟨hsq, heq, -⟩` from `hTh τ`. Establish `hth` using `(hB.th τ).1`. Establish `hstab : ∀ a ∈ RC, ∀ t ∈ D.Th τ, a • t ∈ D.Th τ` using `fun a ha t ht => ((hB.stable τ) a ha).2.2 t ht`. Establish `hχ0 : χ τ 0 = 0`.

Rewrite using `[hχ, MulChar.map_zero]`. Both sides reduce to the same expression. Use extensionality with `m`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, m'⟩, hmem, rfl⟩`.

Establish `hmem' : ((a • fun y : Fin n → F => χ τ (y i)), m') ∈ D.Th τ ⊔ (vanSub C F n (↑i + 1)).toAddSubgroup.prod ⊥` using `hmem`. Take `⟨⟨g, m1⟩, hgm, ⟨f, m2⟩, hf, hsum⟩` from `AddSubgroup.mem_sup.1 hmem'`. Take `⟨hfv, hm2⟩` from `AddSubgroup.mem_prod.1 hf`. Establish `hm2' : m2 = 0` using `AddSubgroup.mem_bot.1 hm2`. Establish `e0 : g + f = a • (fun y : Fin n → F => χ τ (y i))` using `congrArg Prod.fst hsum`.

Establish `e1 : m1 + m2 = m'` using `congrArg Prod.snd hsum`. Rewrite `e1` using `[hm2', add_zero]`. Substitute `e1` using the available equality. Establish `e2 : g = a • (fun y : Fin n → F => χ τ (y i)) - f` using `eq_sub_of_add_eq e0`. Use `show m1 ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.Th τ ⊓ (vanSub C F n ↑i).toAddSubgroup.prod ⊤)`.

Use `AddSubgroup.mem_map.2 ⟨(g, m1), AddSubgroup.mem_inf.2 ⟨hgm, AddSubgroup.mem_prod.2 ⟨?_, AddSubgroup.mem_top _⟩⟩, rfl⟩` and prove the remaining obligations. Use `(mem_vanSub g).2 (fun x hx => ?_)` and prove the remaining obligations. Establish `hxi : x i = 0` using `hx i le_rfl`. Establish `hfx : f x = 0` using `(mem_vanSub f).1 hfv x (fun j hj => hx j (by omega))`. Rewrite using `[e2]`.

Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hxi, hχ0, mul_zero, hfx, sub_zero]`. Introduce `hm`. Establish `hm' : m ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.Th τ ⊓ (vanSub C F n ↑i).toAddSubgroup.prod ⊤)` using `hm`. Take `⟨⟨g, m'⟩, hgm, rfl⟩` from `AddSubgroup.mem_map.1 hm'`. Take `⟨hgTh, hgp⟩` from `AddSubgroup.mem_inf.1 hgm`.

Establish `hgv : g ∈ (vanSub C F n ↑i).toAddSubgroup` using `(AddSubgroup.mem_prod.1 hgp).1`. Take `⟨hgM, hg0⟩` from `(hth g).1 ⟨m', hgTh⟩`. Establish `hgA : g ∈ AA.carrier`. Rewrite `hgM` using `[← hAA]`. Conclude with `(Submodule.mem_toAddSubgroup _).1 hgM`.

Establish `hgK : ∀ k ∈ stepSub F n ↑i, g k = 0` using `fun k hk => (mem_vanSub g).1 hgv k hk`. Establish `hv : v.Integers RC` using `⟨fun a b hab => Subtype.ext hab, fun x => (hRC x).1 x.2, fun r hr => ⟨⟨r, (hRC r).2 hr⟩, rfl⟩⟩`. Take `⟨h, hhA, q, hq, hh0, hhinv, hgq⟩` from `exists_inv_add_sq v hv AA (stepSub F n ↑i) g hgA hg0 hgK`. Establish `hhTh : (h, m') ∈ D.Th τ`. Establish `e3 : (h, m') = (g, m') - (q, 0)`.

Rewrite using `[hgq]`. Simplify using the standard rewrite rules. Rewrite using `[e3]`. Conclude with `sub_mem hgTh (hsq q hq)`. Establish `hcard : ((Fintype.card Fˣ : ℕ) : C) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`.

Establish `hu' : ((Fintype.card Fˣ : ℕ) : C)⁻¹ * (Fintype.card Fˣ : C) = 1` using `inv_mul_cancel₀ hcard`. Establish `hvF : v ((Fintype.card F : ℕ) : C) < 1`. Take `⟨k, -, hk⟩` from `FiniteField.card F p`. Rewrite using `[hk, Nat.cast_pow, map_pow]`. Conclude with `pow_lt_one₀ zero_le' hp (PNat.ne_zero k)`.

Establish `hvU : v ((Fintype.card Fˣ : ℕ) : C) = 1`. Establish `e3 : ((Fintype.card Fˣ : ℕ) : C) = -(1 - ((Fintype.card F : ℕ) : C))`. Rewrite using `[Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3, Valuation.map_neg, Valuation.map_one_sub_of_lt v hvF]`.

Establish `hu : ((Fintype.card Fˣ : ℕ) : C)⁻¹ ∈ RC` using `(hRC _).2 (by rw [map_inv₀, hvU, inv_one])`. Establish `hS : ∀ a, χ τ a ∈ (RC : Set C)` using `fun a => by`. Rewrite using `[hχ]`. Conclude with `Subtype.prop _`. Establish `hmul : ∀ a b, χ τ (a * b) = χ τ a * χ τ b` using `fun a b => by`.

Rewrite using `[hχ, hχ, hχ, map_mul]`. Both sides reduce to the same expression. Establish `h1 : χ τ 1 = 1`. Rewrite using `[hχ, map_one]`. Both sides reduce to the same expression.

Establish `hav` using `avg_mem (D.Th τ) (RC : Set C) hstab (χ τ) hS hmul h1 _ hu hu' heq h m' hhTh`. Set `H' : (Fin n → F) → C` to `fun x => ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)`. Establish `hinv' : ∀ y, ∀ k ∈ stepSub F n ↑i, H' (y + k) = H' y`. Introduce `y k hk`. Establish `hk' : ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → k j = 0` using `hk`.

Use `show ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (y + k)) = ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • y)`. Use `congr 1`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Establish `hak : (a : F) • k ∈ stepSub F n ↑i` using `by show ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → ((a : F) • k) j = 0`. Introduce `j hj`.

Rewrite using `[Pi.smul_apply, hk' j hj, smul_zero]`. Rewrite using `[smul_add, hhinv _ _ hak]`. Establish `hsm' : ∀ (b : Fˣ) y, H' ((b : F) • y) = χ τ (b : F) * H' y` using `fun b y => avg_smul (χ τ) hmul h1 _ h b y`. Establish `h0' : H' 0 = 0` using `by show ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (0 : Fin n → F)) = 0`. Simplify using `[hh0]`.

Establish `hstep` using `eq_on_step i H' (χ τ) hχ0 hinv' hsm' h0'`. Use `show m' ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.stepGraph τ (χ τ) i)`. Use `AddSubgroup.mem_map.2 ⟨(H' (Pi.single i 1), m'), ?_, rfl⟩` and prove the remaining obligations. Use `show ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)), m') ∈ D.Th τ ⊔ (vanSub C F n (↑i + 1)).toAddSubgroup.prod ⊥`. Use `AddSubgroup.mem_sup.2 ⟨(H', m'), hav, ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)) - H', 0), AddSubgroup.mem_prod.2 ⟨?_, zero_mem _⟩, ?_⟩` and prove the remaining obligations.

Use `(mem_vanSub _).2 (fun x hx => ?_)` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hstep x hx, sub_self]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show H' + ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)) - H') = H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)`.

Normalize the expressions using the abelian group laws. Use `show m' + 0 = m'`. Rewrite using `[add_zero]`.
-/
theorem stepGraph_snd_eq_kk : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] [IsAlgClosed C] [CharZero C] (RC : Subalgebra o C) (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → ∀ (p : ℕ) [Fact p.Prime], v (p : C) < 1 → ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (φ : Equiv.Perm Sg), D.Base RC p w → ∀ AA : HopfOrder (C := C) RC (Fin n → F), AA.carrier.toAddSubgroup = D.M → FStable F AA.carrier → ∀ (σ : MulChar F RC), IsFund p σ → FlagConcl v p AA.carrier (Pi.basisFun F (Fin n)) σ → ∀ e : Sg → ℕ, (∀ τ a, χ τ a = ((σ ^ p ^ e τ) a : RC)) → (∀ τ, σ ^ p ^ e (φ τ) = σ ^ p ^ (e τ + 1)) → (∀ τ, (∀ g ∈ sqIdeal (augIdeal AA.carrier), (g, 0) ∈ D.Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ D.Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ D.Th τ) ∧ ∀ g ∈ eig AA.carrier (σ ^ p ^ e τ), (g, 0) ∈ D.Th τ → g ∈ sqIdeal (augIdeal AA.carrier)) → ∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i := by
  intro o C _ _ _ _ _ RC v hRC p _ hp F _ _ _ _ n Sg r s D w χ φ hB AA hAA hFS σ hσ hfl e hχ hφ hTh τ i
  obtain ⟨hsq, heq, -⟩ := hTh τ
  have hth := (hB.th τ).1
  have hstab : ∀ a ∈ RC, ∀ t ∈ D.Th τ, a • t ∈ D.Th τ := fun a ha t ht => ((hB.stable τ) a ha).2.2 t ht
  have hχ0 : χ τ 0 = 0 := by
    rw [hχ, MulChar.map_zero]
    rfl
  ext m
  constructor
  · rintro ⟨⟨a, m'⟩, hmem, rfl⟩
    have hmem' : ((a • fun y : Fin n → F => χ τ (y i)), m') ∈
        D.Th τ ⊔ (vanSub C F n (↑i + 1)).toAddSubgroup.prod ⊥ := hmem
    obtain ⟨⟨g, m1⟩, hgm, ⟨f, m2⟩, hf, hsum⟩ := AddSubgroup.mem_sup.1 hmem'
    obtain ⟨hfv, hm2⟩ := AddSubgroup.mem_prod.1 hf
    have hm2' : m2 = 0 := AddSubgroup.mem_bot.1 hm2
    have e0 : g + f = a • (fun y : Fin n → F => χ τ (y i)) := congrArg Prod.fst hsum
    have e1 : m1 + m2 = m' := congrArg Prod.snd hsum
    rw [hm2', add_zero] at e1
    subst e1
    have e2 : g = a • (fun y : Fin n → F => χ τ (y i)) - f := eq_sub_of_add_eq e0
    show m1 ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.Th τ ⊓ (vanSub C F n ↑i).toAddSubgroup.prod ⊤)
    refine AddSubgroup.mem_map.2 ⟨(g, m1), AddSubgroup.mem_inf.2 ⟨hgm, AddSubgroup.mem_prod.2 ⟨?_, AddSubgroup.mem_top _⟩⟩, rfl⟩
    refine (mem_vanSub g).2 (fun x hx => ?_)
    have hxi : x i = 0 := hx i le_rfl
    have hfx : f x = 0 := (mem_vanSub f).1 hfv x (fun j hj => hx j (by omega))
    rw [e2]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hxi, hχ0, mul_zero, hfx, sub_zero]
  · intro hm
    have hm' : m ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.Th τ ⊓ (vanSub C F n ↑i).toAddSubgroup.prod ⊤) := hm
    obtain ⟨⟨g, m'⟩, hgm, rfl⟩ := AddSubgroup.mem_map.1 hm'
    obtain ⟨hgTh, hgp⟩ := AddSubgroup.mem_inf.1 hgm
    have hgv : g ∈ (vanSub C F n ↑i).toAddSubgroup := (AddSubgroup.mem_prod.1 hgp).1
    obtain ⟨hgM, hg0⟩ := (hth g).1 ⟨m', hgTh⟩
    have hgA : g ∈ AA.carrier := by
      rw [← hAA] at hgM
      exact (Submodule.mem_toAddSubgroup _).1 hgM
    have hgK : ∀ k ∈ stepSub F n ↑i, g k = 0 := fun k hk => (mem_vanSub g).1 hgv k hk
    have hv : v.Integers RC :=
      ⟨fun a b hab => Subtype.ext hab, fun x => (hRC x).1 x.2, fun r hr => ⟨⟨r, (hRC r).2 hr⟩, rfl⟩⟩
    obtain ⟨h, hhA, q, hq, hh0, hhinv, hgq⟩ := exists_inv_add_sq v hv AA (stepSub F n ↑i) g hgA hg0 hgK
    have hhTh : (h, m') ∈ D.Th τ := by
      have e3 : (h, m') = (g, m') - (q, 0) := by
        rw [hgq]
        simp
      rw [e3]
      exact sub_mem hgTh (hsq q hq)
    have hcard : ((Fintype.card Fˣ : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hu' : ((Fintype.card Fˣ : ℕ) : C)⁻¹ * (Fintype.card Fˣ : C) = 1 := inv_mul_cancel₀ hcard
    have hvF : v ((Fintype.card F : ℕ) : C) < 1 := by
      obtain ⟨k, -, hk⟩ := FiniteField.card F p
      rw [hk, Nat.cast_pow, map_pow]
      exact pow_lt_one₀ zero_le' hp (PNat.ne_zero k)
    have hvU : v ((Fintype.card Fˣ : ℕ) : C) = 1 := by
      have e3 : ((Fintype.card Fˣ : ℕ) : C) = -(1 - ((Fintype.card F : ℕ) : C)) := by
        rw [Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
        ring
      rw [e3, Valuation.map_neg, Valuation.map_one_sub_of_lt v hvF]
    have hu : ((Fintype.card Fˣ : ℕ) : C)⁻¹ ∈ RC := (hRC _).2 (by rw [map_inv₀, hvU, inv_one])
    have hS : ∀ a, χ τ a ∈ (RC : Set C) := fun a => by
      rw [hχ]
      exact Subtype.prop _
    have hmul : ∀ a b, χ τ (a * b) = χ τ a * χ τ b := fun a b => by
      rw [hχ, hχ, hχ, map_mul]
      rfl
    have h1 : χ τ 1 = 1 := by
      rw [hχ, map_one]
      rfl
    have hav := avg_mem (D.Th τ) (RC : Set C) hstab (χ τ) hS hmul h1 _ hu hu' heq h m' hhTh
    let H' : (Fin n → F) → C := fun x =>
      ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)
    have hinv' : ∀ y, ∀ k ∈ stepSub F n ↑i, H' (y + k) = H' y := by
      intro y k hk
      have hk' : ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → k j = 0 := hk
      show ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (y + k)) =
        ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • y)
      congr 1
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have hak : (a : F) • k ∈ stepSub F n ↑i := by
        show ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → ((a : F) • k) j = 0
        intro j hj
        rw [Pi.smul_apply, hk' j hj, smul_zero]
      rw [smul_add, hhinv _ _ hak]
    have hsm' : ∀ (b : Fˣ) y, H' ((b : F) • y) = χ τ (b : F) * H' y := fun b y =>
      avg_smul (χ τ) hmul h1 _ h b y
    have h0' : H' 0 = 0 := by
      show ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (0 : Fin n → F)) = 0
      simp [hh0]
    have hstep := eq_on_step i H' (χ τ) hχ0 hinv' hsm' h0'
    show m' ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.stepGraph τ (χ τ) i)
    refine AddSubgroup.mem_map.2 ⟨(H' (Pi.single i 1), m'), ?_, rfl⟩
    show ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)), m') ∈
      D.Th τ ⊔ (vanSub C F n (↑i + 1)).toAddSubgroup.prod ⊥
    refine AddSubgroup.mem_sup.2 ⟨(H', m'), hav, ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)) - H', 0),
      AddSubgroup.mem_prod.2 ⟨?_, zero_mem _⟩, ?_⟩
    · refine (mem_vanSub _).2 (fun x hx => ?_)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hstep x hx, sub_self]
    · refine Prod.ext ?_ ?_
      · show H' + ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)) - H') =
          H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)
        abel
      · show m' + 0 = m'
        rw [add_zero]

end GlobalTheory.CompanionTheory.Ar.Num
