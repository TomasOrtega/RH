import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.CechPic
open GlobalTheory.GroupBplus (AffOp Kbar)

namespace GlobalTheory.ChainPts.SysB

section Ring

variable {R : Type} [CommRing R] [IsDomain R] {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, p = n + 1` from `⟨p - 1, (Nat.sub_add_cancel hp.out.one_lt.le).symm⟩`. Establish `h` using `hz.prod_one_sub_pow_eq_order`. Rewrite using `[Nat.cast_succ, ← h, Nat.add_sub_cancel]`. Establish `: (ξ - 1) ^ n = ∏ _k ∈ Finset.range n, (ξ - 1)` using `by simp`. Rewrite using `[this]`.

Use `Associated.prod _ _ _ fun k hk => ?_` and prove the remaining obligations. Establish `hk' : k + 1 < n + 1` using `Nat.succ_lt_succ (Finset.mem_range.1 hk)`. Establish `hc : (k + 1).Coprime (n + 1)` using `((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt k.succ_pos hk')).symm`. Use `hz.associated_sub_one_pow_sub_one_of_coprime hc` as an intermediate fact. Rewrite using `[← neg_sub (ξ ^ (k + 1)) 1]`.

Conclude with `this.neg_right`.
-/
theorem root_assoc_base {ξ : R} (hz : IsPrimitiveRoot ξ p) : Associated ((ξ - 1) ^ (p - 1)) (p : R) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_lt.le).symm⟩
  have h := hz.prod_one_sub_pow_eq_order
  rw [Nat.cast_succ, ← h, Nat.add_sub_cancel]
  have : (ξ - 1) ^ n = ∏ _k ∈ Finset.range n, (ξ - 1) := by simp
  rw [this]
  refine Associated.prod _ _ _ fun k hk => ?_
  have hk' : k + 1 < n + 1 := Nat.succ_lt_succ (Finset.mem_range.1 hk)
  have hc : (k + 1).Coprime (n + 1) :=
    ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt k.succ_pos hk')).symm
  have := hz.associated_sub_one_pow_sub_one_of_coprime hc
  rw [← neg_sub (ξ ^ (k + 1)) 1]
  exact this.neg_right

/- English proof (translation)
Establish `hω : IsPrimitiveRoot (ξ ^ p ^ (j + 1)) p` using `hz.pow (pow_pos hp.out.pos _) (pow_succ p (j + 1))`. Establish `h` using `congrArg (Polynomial.eval (1 : R)) (X_pow_sub_C_eq_prod hω hp.out.pos (rfl : ξ ^ p = ξ ^ p))`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_prod, one_pow] at h`. Rewrite using `[← neg_sub 1 (ξ ^ p), h]`. Use `Associated.neg_right ?_` and prove the remaining obligations.

Establish `: (ξ - 1) ^ p = ∏ _k ∈ Finset.range p, (ξ - 1)` using `by simp`. Rewrite using `[this]`. Use `Associated.prod _ _ _ fun k _ => ?_` and prove the remaining obligations. Establish `hc : (p ^ (j + 1) * k + 1).Coprime (p ^ (j + 2))`. Use `Nat.Coprime.pow_right _ ?_` and prove the remaining obligations.

Rewrite using `[pow_succ', mul_assoc, add_comm, Nat.coprime_add_mul_left_left]`. Conclude with `Nat.coprime_one_left _`. Use `hz.associated_sub_one_pow_sub_one_of_coprime hc` as an intermediate fact. Rewrite using `[← pow_mul, ← pow_succ, ← neg_sub (ξ ^ _) 1]`. Conclude with `this.neg_right`.
-/
theorem root_assoc_step {j : ℕ} {ξ : R} (hz : IsPrimitiveRoot ξ (p ^ (j + 2))) :
    Associated ((ξ - 1) ^ p) (ξ ^ p - 1) := by
  have hω : IsPrimitiveRoot (ξ ^ p ^ (j + 1)) p := hz.pow (pow_pos hp.out.pos _) (pow_succ p (j + 1))
  have h := congrArg (Polynomial.eval (1 : R)) (X_pow_sub_C_eq_prod hω hp.out.pos (rfl : ξ ^ p = ξ ^ p))
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_prod,
    one_pow] at h
  rw [← neg_sub 1 (ξ ^ p), h]
  refine Associated.neg_right ?_
  have : (ξ - 1) ^ p = ∏ _k ∈ Finset.range p, (ξ - 1) := by simp
  rw [this]
  refine Associated.prod _ _ _ fun k _ => ?_
  have hc : (p ^ (j + 1) * k + 1).Coprime (p ^ (j + 2)) := by
    refine Nat.Coprime.pow_right _ ?_
    rw [pow_succ', mul_assoc, add_comm, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left _
  have := hz.associated_sub_one_pow_sub_one_of_coprime hc
  rw [← pow_mul, ← pow_succ, ← neg_sub (ξ ^ _) 1]
  exact this.neg_right

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => intro ξ hz; simpa using root_assoc_base (by simpa using hz)`. Consider the case `succ j ih`. Introduce `ξ hz`. Establish `h1 : IsPrimitiveRoot (ξ ^ p) (p ^ (j + 1))` using `hz.pow (pow_pos hp.out.pos _) (pow_succ' p (j + 1))`.

Rewrite using `[pow_succ', mul_assoc, pow_mul]`. Conclude with `(root_assoc_step hz).pow_pow.trans (ih h1)`.
-/
theorem root_assoc_pow (j : ℕ) : ∀ {ξ : R}, IsPrimitiveRoot ξ (p ^ (j + 1)) →
    Associated ((ξ - 1) ^ (p ^ j * (p - 1))) (p : R) := by
  induction j with
  | zero => intro ξ hz; simpa using root_assoc_base (by simpa using hz)
  | succ j ih =>
    intro ξ hz
    have h1 : IsPrimitiveRoot (ξ ^ p) (p ^ (j + 1)) := hz.pow (pow_pos hp.out.pos _) (pow_succ' p (j + 1))
    rw [pow_succ', mul_assoc, pow_mul]
    exact (root_assoc_step hz).pow_pow.trans (ih h1)

/- English proof (translation)
Establish `hne : ξ - 1 ≠ 0` using `sub_ne_zero.2 (hz.ne_one (Nat.one_lt_pow (by omega) hp.out.one_lt))`. Establish `h` using `root_assoc_step hz`. Rewrite `h` using `[← geom_sum_mul]`. Establish `e : (ξ - 1) ^ p = (ξ - 1) ^ (p - 1) * (ξ - 1)`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]`.

Rewrite `h` using `[e]`. Establish `h2` using `h.of_mul_right (Associated.refl _) hne`. Use `h2.symm.pow_pow.trans ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm]`. Conclude with `root_assoc_pow (k + 1) hz`.
-/
theorem root_assoc_sum {k : ℕ} {ξ : R} (hz : IsPrimitiveRoot ξ (p ^ (k + 2))) :
    Associated ((∑ i ∈ Finset.range p, ξ ^ i) ^ p ^ (k + 1)) (p : R) := by
  have hne : ξ - 1 ≠ 0 := sub_ne_zero.2 (hz.ne_one (Nat.one_lt_pow (by omega) hp.out.one_lt))
  have h := root_assoc_step hz
  rw [← geom_sum_mul] at h
  have e : (ξ - 1) ^ p = (ξ - 1) ^ (p - 1) * (ξ - 1) := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]
  rw [e] at h
  have h2 := h.of_mul_right (Associated.refl _) hne
  refine h2.symm.pow_pow.trans ?_
  rw [← pow_mul, mul_comm]
  exact root_assoc_pow (k + 1) hz

end Ring

/- English proof (translation)
Introduce `O _ _ _ B p hp o ζ z hζ hz hres`. Set `ι : Γ(B.X, ⊤) →+* Kbar B.X` to `(algebraMap B.X.functionField (Kbar B.X)).comp (B.X.germToFunctionField ⊤).hom`. Establish `hι : Function.Injective ι` using `(algebraMap B.X.functionField (Kbar B.X)).injective.comp (B.X.germToFunctionField_injective ⊤)`. Establish `hc : ∀ (U : AffOp B.X) (a : Γ(B.X, ⊤)), (cstBp U a : Kbar B.X) = ι a` using `fun U a => congrArg (algebraMap B.X.functionField (Kbar B.X)) (B.X.presheaf.germ_res_apply (homOfLE le_top) _ _ a)`. Establish `hsub : ∀ (V : B.X.Opens), Nonempty V → ∃ W : AffOp B.X, W.1 ≤ V`.

Introduce and unpack `V ⟨x, hx⟩`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩` from `B.X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) hx V.isOpen`. Conclude with `⟨⟨U, hU, ⟨⟨x, hxU⟩⟩⟩, hUV⟩`. Take `⟨U₀, -⟩` from `hsub ⊤ inferInstance`. Establish `hind : ∀ (U : AffOp B.X) (n : ℕ), (z U n : Kbar B.X) = z U₀ n` using `fun U n => by`.

Establish `hne : Nonempty (U.1 ⊓ U₀.1 : B.X.Opens)`. Take `⟨x, hx⟩` from `U.2.2`. Take `⟨y, hy⟩` from `U₀.2.2`. Take `⟨w, hw⟩` from `nonempty_preirreducible_inter U.1.isOpen U₀.1.isOpen ⟨x, hx⟩ ⟨y, hy⟩`. Conclude with `⟨⟨w, hw⟩⟩`.

Take `⟨W, hW⟩` from `hsub _ hne`. Conclude with `(congrArg Subtype.val (hres U W (hW.trans inf_le_left) n)).symm.trans (congrArg Subtype.val (hres U₀ W (hW.trans inf_le_right) n))`. Establish `hprim : ∀ n, IsPrimitiveRoot (z U₀ n : Kbar B.X) (p ^ n)` using `fun n => (hz U₀ n).map_of_injective (f := (integralClosure Γ(B.X, U₀.1) (Kbar B.X)).val) Subtype.val_injective`. Establish `: NeZero (p ^ (o + 2))` using `⟨pow_ne_zero _ hp.out.ne_zero⟩`. Establish `hex : ∀ n, ∃ y : Γ(B.X, ⊤), n ≤ o + 2 → ι y = z U₀ n` using `fun n => by`.

Distinguish the cases in `hn : n ≤ o + 2`. Establish `h1 : (z U₀ n : Kbar B.X) ^ p ^ (o + 2) = 1` using `((hprim n).pow_eq_one_iff_dvd _).2 (pow_dvd_pow p hn)`. Take `⟨i, -, hi⟩` from `(hζ.map_of_injective hι).eq_pow_of_pow_eq_one h1`. Conclude with `⟨ζ ^ i, fun _ => (map_pow ι ζ i).trans hi⟩`. Conclude with `⟨0, fun h => absurd h hn⟩`.

Use `choose y hy using hex`. Establish `hyp : ∀ n ≤ o + 2, IsPrimitiveRoot (y n) (p ^ n)` using `fun n hn => IsPrimitiveRoot.of_map_of_injective (f := ι) (by rw [hy n hn]; exact hprim n) hι`. Establish `hroot : ∀ (g : Γ(B.X, ⊤)) (a : ℕ), Associated (g ^ a) (p : Γ(B.X, ⊤)) → IsRootOfP p g a` using `fun g a h => by`. Take `⟨u, hu⟩` from `h.symm`. Conclude with `⟨u, hu.symm.trans (mul_comm _ _)⟩`.

Use `⟨y 1 - 1, fun k => ∑ i ∈ Finset.range p, y (k + 2) ^ i, hroot _ _ ?_, fun k hk => hroot _ _ ?_, fun U => ⟨Subtype.ext ?_, fun k hk => Subtype.ext ?_⟩⟩` and prove the remaining obligations. Conclude with `root_assoc_base (by simpa using hyp 1 (by omega))`. Conclude with `root_assoc_sum (hyp (k + 2) (by omega))`. Rewrite using `[hc, map_sub, map_one, hy 1 (by omega), ← hind U]`. Both sides reduce to the same expression.

Rewrite using `[hc, map_sum, AddSubmonoidClass.coe_finsetSum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, hy (k + 2) (by omega), ← hind U]`. Both sides reduce to the same expression.
-/
theorem exists_global_roots : RootSt := by
  intro O _ _ _ B p hp o ζ z hζ hz hres
  let ι : Γ(B.X, ⊤) →+* Kbar B.X :=
    (algebraMap B.X.functionField (Kbar B.X)).comp (B.X.germToFunctionField ⊤).hom
  have hι : Function.Injective ι :=
    (algebraMap B.X.functionField (Kbar B.X)).injective.comp (B.X.germToFunctionField_injective ⊤)
  have hc : ∀ (U : AffOp B.X) (a : Γ(B.X, ⊤)), (cstBp U a : Kbar B.X) = ι a := fun U a =>
    congrArg (algebraMap B.X.functionField (Kbar B.X)) (B.X.presheaf.germ_res_apply (homOfLE le_top) _ _ a)
  have hsub : ∀ (V : B.X.Opens), Nonempty V → ∃ W : AffOp B.X, W.1 ≤ V := by
    rintro V ⟨x, hx⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := B.X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) hx V.isOpen
    exact ⟨⟨U, hU, ⟨⟨x, hxU⟩⟩⟩, hUV⟩
  obtain ⟨U₀, -⟩ := hsub ⊤ inferInstance
  have hind : ∀ (U : AffOp B.X) (n : ℕ), (z U n : Kbar B.X) = z U₀ n := fun U n => by
    have hne : Nonempty (U.1 ⊓ U₀.1 : B.X.Opens) := by
      obtain ⟨x, hx⟩ := U.2.2
      obtain ⟨y, hy⟩ := U₀.2.2
      obtain ⟨w, hw⟩ := nonempty_preirreducible_inter U.1.isOpen U₀.1.isOpen ⟨x, hx⟩ ⟨y, hy⟩
      exact ⟨⟨w, hw⟩⟩
    obtain ⟨W, hW⟩ := hsub _ hne
    exact (congrArg Subtype.val (hres U W (hW.trans inf_le_left) n)).symm.trans
      (congrArg Subtype.val (hres U₀ W (hW.trans inf_le_right) n))
  have hprim : ∀ n, IsPrimitiveRoot (z U₀ n : Kbar B.X) (p ^ n) := fun n =>
    (hz U₀ n).map_of_injective (f := (integralClosure Γ(B.X, U₀.1) (Kbar B.X)).val) Subtype.val_injective
  have : NeZero (p ^ (o + 2)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hex : ∀ n, ∃ y : Γ(B.X, ⊤), n ≤ o + 2 → ι y = z U₀ n := fun n => by
    by_cases hn : n ≤ o + 2
    · have h1 : (z U₀ n : Kbar B.X) ^ p ^ (o + 2) = 1 := ((hprim n).pow_eq_one_iff_dvd _).2 (pow_dvd_pow p hn)
      obtain ⟨i, -, hi⟩ := (hζ.map_of_injective hι).eq_pow_of_pow_eq_one h1
      exact ⟨ζ ^ i, fun _ => (map_pow ι ζ i).trans hi⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose y hy using hex
  have hyp : ∀ n ≤ o + 2, IsPrimitiveRoot (y n) (p ^ n) := fun n hn =>
    IsPrimitiveRoot.of_map_of_injective (f := ι) (by rw [hy n hn]; exact hprim n) hι
  have hroot : ∀ (g : Γ(B.X, ⊤)) (a : ℕ), Associated (g ^ a) (p : Γ(B.X, ⊤)) → IsRootOfP p g a := fun g a h => by
    obtain ⟨u, hu⟩ := h.symm
    exact ⟨u, hu.symm.trans (mul_comm _ _)⟩
  refine ⟨y 1 - 1, fun k => ∑ i ∈ Finset.range p, y (k + 2) ^ i, hroot _ _ ?_, fun k hk => hroot _ _ ?_,
    fun U => ⟨Subtype.ext ?_, fun k hk => Subtype.ext ?_⟩⟩
  · exact root_assoc_base (by simpa using hyp 1 (by omega))
  · exact root_assoc_sum (hyp (k + 2) (by omega))
  · rw [hc, map_sub, map_one, hy 1 (by omega), ← hind U]
    rfl
  · rw [hc, map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, hy (k + 2) (by omega), ← hind U]
    rfl

end GlobalTheory.ChainPts.SysB

end
