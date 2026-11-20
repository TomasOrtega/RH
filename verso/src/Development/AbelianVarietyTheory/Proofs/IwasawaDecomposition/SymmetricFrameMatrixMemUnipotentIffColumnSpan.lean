import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymAllowed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameReducesToBasisModPlaceStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFrameW
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRhoX
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GroupLoc.Coords

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA PIW.AdelClassFin

variable {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p m : ℕ}

/- English proof (translation)
Establish `: NeZero p` using `⟨hp.ne_zero⟩`. Establish `h2 : ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j - ∑ j, ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_smul]`.

Use `Wq_smul ?_ (hu j)` and prove the remaining obligations. Establish `hk : c j - ((((c j : ZMod p)).val : ℕ) : ℤ) = (c j / p) * p`. Rewrite using `[ZMod.val_intCast, Int.emod_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `e : (c j : I.E ⊗[I.F] Af I.F) - ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) = ((c j / p : ℤ) : I.E ⊗[I.F] Af I.F) * (p : I.E ⊗[I.F] Af I.F)`.

Use `congrArg (Int.cast : ℤ → I.E ⊗[I.F] Af I.F) hk` as an intermediate fact. Simplify `this` using `only [Int.cast_sub, Int.cast_natCast, Int.cast_mul]`. Rewrite using `[e]`. Conclude with `Wq_mul (natCast_Wq hp hcard) (intCast_int _)`. Use `add_mem h h2` as an intermediate fact.

Use `show v - _ ∈ _`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem rep_of_int (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hu : ∀ j, u j ∈ I.Lf) {v : Fin I.n → I.E ⊗[I.F] Af I.F}
    {c : Fin m → ℤ} (h : v - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w) :
    RepV w p u v (fun j => (c j : ZMod p)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2 : ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j -
      ∑ j, ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    rw [← sub_smul]
    refine Wq_smul ?_ (hu j)
    have hk : c j - ((((c j : ZMod p)).val : ℕ) : ℤ) = (c j / p) * p := by
      rw [ZMod.val_intCast, Int.emod_def]; ring
    have e : (c j : I.E ⊗[I.F] Af I.F) - ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) =
        ((c j / p : ℤ) : I.E ⊗[I.F] Af I.F) * (p : I.E ⊗[I.F] Af I.F) := by
      have := congrArg (Int.cast : ℤ → I.E ⊗[I.F] Af I.F) hk
      simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_mul] using this
    rw [e]
    exact Wq_mul (natCast_Wq hp hcard) (intCast_int _)
  have := add_mem h h2
  show v - _ ∈ _
  convert this using 1
  abel

/- English proof (translation)
Take `⟨y1, hy1, y2, hy2, rfl⟩` from `Submodule.mem_sup.1 hy`. Establish `key : ∃ c : Fin m → ℤ, (∀ j, j ∉ S → c j = 0) ∧ y1 - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w` using `by clear hy`. Proceed by induction on `hy1 using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, hi, rfl⟩` from `hx`.

Use `⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun e : j = i => hj (by rw [e]; exact hi)) _, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.sum_eq_single i (fun j hj => by simp [hj])]`. Simplify using the standard rewrite rules. Consider the case `zero => exact ⟨0, fun _ _ => rfl, by simp⟩`. Consider the case `add x z _ _ hx hz`.

Take `⟨c, hc0, hc⟩` from `hx`. Take `⟨d, hd0, hd⟩` from `hz`. Use `⟨c + d, fun j hj => by simp [hc0 j hj, hd0 j hj], ?_⟩` and prove the remaining obligations. Use `add_mem hc hd` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws. Consider the case `smul s x _ hx`. Take `⟨c, hc0, hc⟩` from `hx`. Take `⟨_, t, -, ht⟩` from `congW_exists (w := w) hp hcard s.2`.

Use `⟨fun j => t * c j, fun j hj => by simp [hc0 j hj], ?_⟩` and prove the remaining obligations. Establish `h1` using `(Lq I w).smul_mem s hc`. Establish `h2 : ((s : I.E ⊗[I.F] Af I.F) - (t : I.E ⊗[I.F] Af I.F)) • ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w`. Use `Wq_smul ht (sum_mem fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`.

Conclude with `zsmul_mem (hu j) _`. Use `add_mem h1 h2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `show (s : I.E ⊗[I.F] Af I.F) • x - _ = (s : I.E ⊗[I.F] Af I.F) • (x - _) + _`. Simplify using `only [Int.cast_mul, mul_smul, ← Finset.smul_sum, smul_sub, sub_smul]`.

Normalize the expressions using the abelian group laws. Take `⟨c, hc0, hc⟩` from `key`. Use `⟨c, hc0, ?_⟩` and prove the remaining obligations. Use `add_mem hc hy2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws.
-/
theorem int_comb (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hu : ∀ j, u j ∈ I.Lf) (S : Set (Fin m))
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ Submodule.span (IntAf I.F I.E) (u '' S) ⊔ Lq I w) :
    ∃ c : Fin m → ℤ, (∀ j, j ∉ S → c j = 0) ∧ y - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
  classical
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
  have key : ∃ c : Fin m → ℤ, (∀ j, j ∉ S → c j = 0) ∧
      y1 - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
    clear hy
    induction hy1 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun e : j = i => hj (by rw [e]; exact hi)) _, ?_⟩
      rw [Fintype.sum_eq_single i (fun j hj => by simp [hj])]
      simp
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, hc0, hc⟩ := hx
      obtain ⟨d, hd0, hd⟩ := hz
      refine ⟨c + d, fun j hj => by simp [hc0 j hj, hd0 j hj], ?_⟩
      have := add_mem hc hd
      convert this using 1
      simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
      abel
    | smul s x _ hx =>
      obtain ⟨c, hc0, hc⟩ := hx
      obtain ⟨_, t, -, ht⟩ := congW_exists (w := w) hp hcard s.2
      refine ⟨fun j => t * c j, fun j hj => by simp [hc0 j hj], ?_⟩
      have h1 := (Lq I w).smul_mem s hc
      have h2 : ((s : I.E ⊗[I.F] Af I.F) - (t : I.E ⊗[I.F] Af I.F)) •
          ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
        refine Wq_smul ht (sum_mem fun j _ => ?_)
        rw [Int.cast_smul_eq_zsmul]
        exact zsmul_mem (hu j) _
      have := add_mem h1 h2
      convert this using 1
      show (s : I.E ⊗[I.F] Af I.F) • x - _ = (s : I.E ⊗[I.F] Af I.F) • (x - _) + _
      simp only [Int.cast_mul, mul_smul, ← Finset.smul_sum, smul_sub, sub_smul]
      abel
  obtain ⟨c, hc0, hc⟩ := key
  refine ⟨c, hc0, ?_⟩
  have := add_mem hc hy2
  convert this using 1
  abel

/- English proof (translation)
Establish `: NeZero p` using `⟨hp.ne_zero⟩`. Establish `: Fact (1 < p)` using `⟨hp.one_lt⟩`. Establish `hu : ∀ j, u j ∈ I.Lf` using `fun j => by`. Establish `h1 : u j - _ ∈ I.Lf` using `lamAf_mono I (wLat0_le I w) (hP j)`. Establish `h2 : ∑ k, ((((P : Matrix (Fin m) (Fin m) (ZMod p)) k j).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ I.Lf` using `sum_mem fun k _ => by`.

Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem (DictLat.iv_mem I (hb.1 k)) _`. Simplify using `using add_mem h1 h2`. Establish `e1 : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j = u i`. Rewrite using `[Fintype.sum_eq_single i (fun j hj => by simp [Matrix.one_apply_ne hj])]`.

Simplify using `only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : ∑ j, (((N j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j - u i ∈ Submodule.span (IntAf I.F I.E) (u '' S)`.

Rewrite using `[← e1, ← Finset.sum_sub_distrib]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j ∈ S`. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`. Establish `hm : u j ∈ Submodule.span (IntAf I.F I.E) (u '' S)` using `Submodule.subset_span ⟨j, hj, rfl⟩`.

Conclude with `sub_mem (nsmul_mem hm _) (nsmul_mem hm _)`. Rewrite using `[h j hj, sub_self]`. Conclude with `zero_mem _`. Use `Submodule.add_mem_sup h1 hN` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Introduce `h j hj`. Take `⟨c, hc0, hc⟩` from `int_comb hp hcard hu S h`. Establish `h2 : A *ᵥ u i - ∑ l, (((c + Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l ∈ Lq I w`. Use `hc using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]`. Rewrite using `[Fintype.sum_eq_single i (f := fun l => (((Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l) (fun l hl => by simp [hl])]`. Simplify using `only [Pi.single_eq_same, Int.cast_one, one_smul]`. Normalize the expressions using the abelian group laws. Establish `h3` using `rep_unique hp hcard hm hb (rep_comp hp hcard hb.1 hN hP) (rep_comp hp hcard hb.1 (rep_of_int hp hcard hu h2) hP)`.

Establish `h4` using `congrArg (fun v => ((P⁻¹ : GL (Fin m) (ZMod p)) : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ v) h3`. Simplify using `only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h4`. Establish `h5` using `congrFun h4 j`. Simplify using `only [Pi.add_apply, hc0 j hj, zero_add] at h5`. Rewrite using `[h5]`.

Distinguish the cases in `e : j = i`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[e]`.
-/
theorem cols_iff (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hm : m = I.n)
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) (P : GL (Fin m) (ZMod p))
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F}
    (hP : ∀ j, RepV w p (fun k => iv I (b k)) (u j) (fun k => (P : Matrix (Fin m) (Fin m) (ZMod p)) k j))
    (A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (N : Matrix (Fin m) (Fin m) (ZMod p))
    (i : Fin m) (hN : RepV w p u (A *ᵥ u i) (fun j => N j i)) (S : Set (Fin m)) :
    (∀ j, j ∉ S → N j i = (1 : Matrix (Fin m) (Fin m) (ZMod p)) j i) ↔
      (A - 1) *ᵥ u i ∈ Submodule.span (IntAf I.F I.E) (u '' S) ⊔ Lq I w := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hu : ∀ j, u j ∈ I.Lf := fun j => by
    have h1 : u j - _ ∈ I.Lf := lamAf_mono I (wLat0_le I w) (hP j)
    have h2 : ∑ k, ((((P : Matrix (Fin m) (Fin m) (ZMod p)) k j).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ I.Lf :=
      sum_mem fun k _ => by
        rw [Nat.cast_smul_eq_nsmul]
        exact nsmul_mem (DictLat.iv_mem I (hb.1 k)) _
    simpa using add_mem h1 h2
  have e1 : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j = u i := by
    rw [Fintype.sum_eq_single i (fun j hj => by simp [Matrix.one_apply_ne hj])]
    simp only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · intro h
    have h1 : ∑ j, (((N j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j - u i ∈
        Submodule.span (IntAf I.F I.E) (u '' S) := by
      rw [← e1, ← Finset.sum_sub_distrib]
      refine sum_mem fun j _ => ?_
      by_cases hj : j ∈ S
      · rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        have hm : u j ∈ Submodule.span (IntAf I.F I.E) (u '' S) := Submodule.subset_span ⟨j, hj, rfl⟩
        exact sub_mem (nsmul_mem hm _) (nsmul_mem hm _)
      · rw [h j hj, sub_self]; exact zero_mem _
    have := Submodule.add_mem_sup h1 hN
    convert this using 1
    abel
  · intro h j hj
    obtain ⟨c, hc0, hc⟩ := int_comb hp hcard hu S h
    have h2 : A *ᵥ u i - ∑ l, (((c + Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l ∈ Lq I w := by
      convert hc using 1
      simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
      rw [Fintype.sum_eq_single i (f := fun l => (((Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l)
        (fun l hl => by simp [hl])]
      simp only [Pi.single_eq_same, Int.cast_one, one_smul]
      abel
    have h3 := rep_unique hp hcard hm hb (rep_comp hp hcard hb.1 hN hP)
      (rep_comp hp hcard hb.1 (rep_of_int hp hcard hu h2) hP)
    have h4 := congrArg (fun v => ((P⁻¹ : GL (Fin m) (ZMod p)) : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ v) h3
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h4
    have h5 := congrFun h4 j
    simp only [Pi.add_apply, hc0 j hj, zero_add] at h5
    rw [h5]
    by_cases e : j = i
    · subst e; simp
    · simp [e]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ i j hj`. Break down `lt_trichotomy j i with h | h | h` into its components or cases. Choose the witnesses or unpack the hypotheses as in `⟨a, b, c⟩ : ρ ≤ j.1 ∧ j.1 < ρ + k ∧ i.1 = ρ + k := by`. Assume the negation of the conclusion as `hh`.

Conclude with `hj ⟨h, hh⟩`. Rewrite using `[h2 j i a b c, Matrix.one_apply_ne h.ne]`. Substitute `h` using the available equality. Rewrite using `[unip_diag h1, Matrix.one_apply_eq]`. Rewrite using `[unip_lower h1 h, Matrix.one_apply_ne h.ne']`.

Introduce `h`. Use `⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩` and prove the remaining obligations. Establish `hij' : j.val < i.val` using `hij`. Rewrite using `[h j i (fun hh => by have := hh.1; omega), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]`. Rewrite using `[h i i (fun hh => lt_irrefl _ hh.1), Matrix.one_apply_eq]`.

Rewrite using `[h j i (fun hh => hh.2 ⟨ha, hb, hc⟩), Matrix.one_apply_ne (fun e => by rw [e] at hb; omega)]`.
-/
theorem mem_unipSym_iff {κ : Type} [CommRing κ] {r ρ k : ℕ} (N : GL (Fin r) κ) :
    N ∈ unipSym κ r ρ k ↔ ∀ i j : Fin r, j ∉ {j | symAllowed ρ k i j} →
      (N : Matrix (Fin r) (Fin r) κ) j i = (1 : Matrix (Fin r) (Fin r) κ) j i := by
  constructor
  · rintro ⟨h1, h2⟩ i j hj
    rcases lt_trichotomy j i with h | h | h
    · obtain ⟨a, b, c⟩ : ρ ≤ j.1 ∧ j.1 < ρ + k ∧ i.1 = ρ + k := by
        by_contra hh
        exact hj ⟨h, hh⟩
      rw [h2 j i a b c, Matrix.one_apply_ne h.ne]
    · subst h
      rw [unip_diag h1, Matrix.one_apply_eq]
    · rw [unip_lower h1 h, Matrix.one_apply_ne h.ne']
  · intro h
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · have hij' : j.val < i.val := hij
      rw [h j i (fun hh => by have := hh.1; omega), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
    · rw [h i i (fun hh => lt_irrefl _ hh.1), Matrix.one_apply_eq]
    · rw [h j i (fun hh => hh.2 ⟨ha, hb, hc⟩), Matrix.one_apply_ne (fun e => by rw [e] at hb; omega)]

end GlobalTheory.Mem.GroupLoc.Coords

namespace GlobalTheory.Mem.GroupLoc

open Formalism.L2.SG.Pf.RowDictPf in

/- English proof (translation)
Introduce `D X h hι hg k _ kv N hN`. Use `choose b hb using fun kv => Formalism.L2.SG.Pf.AllRowsRhoX.exists_b X kv`. Take `⟨P, hP⟩` from `GlobalTheory.T.symmetricFrame_reduces_to_basis_mod_place D X h hι b (fun kv => by`. Unfold `IsRedBasis`. Rewrite using `[wLat_eq X]`.

Conclude with `hb kv) hg 1`. Rewrite using `[Coords.mem_unipSym_iff]`. Unfold `ColCond ModW`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Establish `hP'` using `hP kv`.

Establish `hN'` using `hN i`. Unfold `wLf at hP' hN' ⊢`. Rewrite `hP'`, `hN'`, the goal using `[wLat_eq X]`. Conclude with `Coords.cols_iff (w := wB X (D.naut.plGw kv.1 kv.2)) (D.host.g_prime kv.1) (by rw [card_wB, card_res_host]) X.n_eq.symm (hb kv) (P kv) hP' (X.B.I.fmat k) _ i hN' _`.
-/
theorem mem_unipSym_iff_colCond : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (N : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → (N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k ↔ GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k) := by
  intro D X h hι hg k _ kv N hN
  choose b hb using fun kv => Formalism.L2.SG.Pf.AllRowsRhoX.exists_b X kv
  obtain ⟨P, hP⟩ := GlobalTheory.T.symmetricFrame_reduces_to_basis_mod_place D X h hι b (fun kv => by
    unfold IsRedBasis
    rw [wLat_eq X]
    exact hb kv) hg 1
  rw [Coords.mem_unipSym_iff]
  unfold ColCond ModW
  refine forall_congr' fun i => ?_
  have hP' := hP kv
  have hN' := hN i
  unfold wLf at hP' hN' ⊢
  rw [wLat_eq X] at hP' hN' ⊢
  exact Coords.cols_iff (w := wB X (D.naut.plGw kv.1 kv.2)) (D.host.g_prime kv.1)
    (by rw [card_wB, card_res_host]) X.n_eq.symm (hb kv) (P kv) hP' (X.B.I.fmat k) _ i hN' _

end GlobalTheory.Mem.GroupLoc
