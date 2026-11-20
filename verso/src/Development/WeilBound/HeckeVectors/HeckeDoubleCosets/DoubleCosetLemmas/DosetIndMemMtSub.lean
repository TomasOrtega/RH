import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.MatchB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosetsStatement

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.WeylGL
open GlobalTheory.LFun.SatCompare GlobalTheory.CompanionTheory.Ipf.Val
open GlobalTheory.SplitHecke (IntM GInt Hk Reps tr yw nKer)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers K v

/- English proof (translation)
Rewrite using `[heckeVec_dosetInd hx (R := {z}) (by`. Introduce `γ hγ`. Rewrite using `[Finset.mem_singleton.1 hγ]`. Conclude with `mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩) (by`. Introduce `g hg`.

Take `⟨a, ha, b, hb, rfl⟩` from `mem_doset.1 hg`. Use `⟨z, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩` and prove the remaining obligations. Rewrite using `[← hz a, show z⁻¹ * (z * a * b) = a * b by group]`. Conclude with `mul_mem ha hb), Finset.sum_singleton]`.
-/
theorem heckeVec_central {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {J : Subgroup G}
    {ρ : Representation ℂ G V} {x : V} (hx : x ∈ fixed ρ J) {z : G} (hz : ∀ g, z * g = g * z) :
    heckeVec ρ J (dosetInd ℂ J z) x = ρ z x := by
  rw [heckeVec_dosetInd hx (R := {z}) (by
    intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩) (by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
    refine ⟨z, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← hz a, show z⁻¹ * (z * a * b) = a * b by group]
    exact mul_mem ha hb), Finset.sum_singleton]

/- English proof (translation)
Establish `hp` using `Multiset.powersetCard_self (B.map fun b : ℂˣ => (b : ℂ))`. Rewrite `hp` using `[Multiset.card_map, hB]`. Simplify using `only [satEig, Multiset.esymm, hp, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul, Multiset.map_singleton, Multiset.sum_singleton]`. Conclude with `(map_multiset_prod (Units.coeHom ℂ) B).symm`.
-/
theorem satEig_top (q n : ℕ) {B : Multiset ℂˣ} (hB : B.card = n) :
    satEig q n B n = ((B.prod : ℂˣ) : ℂ) := by
  have hp := Multiset.powersetCard_self (B.map fun b : ℂˣ => (b : ℂ))
  rw [Multiset.card_map, hB] at hp
  simp only [satEig, Multiset.esymm, hp, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul,
    Multiset.map_singleton, Multiset.sum_singleton]
  exact (map_multiset_prod (Units.coeHom ℂ) B).symm

/- English proof (translation)
The claim follows from `Units.ext (npow_add v y z)`.
-/
theorem npowU_add (y z : ℂ) : npowU v (y + z) = npowU v y * npowU v z :=
  Units.ext (npow_add v y z)

/- English proof (translation)
The claim follows from `Units.ext (Complex.cpow_zero _)`.
-/
theorem npowU_zero : npowU v 0 = 1 := Units.ext (Complex.cpow_zero _)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [npowU_zero]`. Consider the case `insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, npowU_add, ih]`.
-/
theorem prod_npowU (s : Finset ℕ) (f : ℕ → ℂ) :
    ∏ i ∈ s, npowU v (f i) = npowU v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [npowU_zero]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, npowU_add, ih]

/- English proof (translation)
Establish `h : ∑ i ∈ Finset.range t, (((t : ℂ) - 1) / 2 - i) = 0`. Establish `: ∀ n : ℕ, ∑ i ∈ Finset.range n, (i : ℂ) = n * (n - 1) / 2` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Finset.sum_range_succ, ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_sub_distrib, this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [seg, one_mul]`.

Rewrite using `[← Finset.prod_eq_multiset_prod, prod_npowU, h, npowU_zero]`.
-/
theorem seg_prod (t : ℕ) : (seg v 1 t).prod = 1 := by
  have h : ∑ i ∈ Finset.range t, (((t : ℂ) - 1) / 2 - i) = 0 := by
    have : ∀ n : ℕ, ∑ i ∈ Finset.range n, (i : ℂ) = n * (n - 1) / 2 := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
    rw [Finset.sum_sub_distrib, this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  simp only [seg, one_mul]
  rw [← Finset.prod_eq_multiset_prod, prod_npowU, h, npowU_zero]

/- English proof (translation)
Simplify using `only [seg, one_mul, Multiset.map_map, Function.comp_def]`. Use `Multiset.map_eq_map_of_bij_of_nodup _ _ (Finset.range t).nodup (Finset.range t).nodup (fun i _ => t - 1 - i) (fun i hi => ?_) (fun i hi j hj e => ?_) (fun j hj => ⟨t - 1 - j, ?_, ?_⟩) fun i hi => ?_` and prove the remaining obligations. Use `Finset.mem_range.1 hi; exact Finset.mem_range.2 (by omega)` as an intermediate fact. Use `Finset.mem_range.1 hi` as an intermediate fact. Use `Finset.mem_range.1 hj` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `Finset.mem_range.1 hj; exact Finset.mem_range.2 (by omega)` as an intermediate fact. Use `Finset.mem_range.1 hj` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h : i + 1 ≤ t` using `Finset.mem_range.1 hi`.

Rewrite using `[inv_eq_iff_mul_eq_one, ← npowU_add, ← npowU_zero (v := v)]`. Use `congr 1`. Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem seg_inv (t : ℕ) : (seg v 1 t).map (·⁻¹) = seg v 1 t := by
  simp only [seg, one_mul, Multiset.map_map, Function.comp_def]
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ (Finset.range t).nodup (Finset.range t).nodup
    (fun i _ => t - 1 - i) (fun i hi => ?_) (fun i hi j hj e => ?_)
    (fun j hj => ⟨t - 1 - j, ?_, ?_⟩) fun i hi => ?_
  · have := Finset.mem_range.1 hi; exact Finset.mem_range.2 (by omega)
  · have := Finset.mem_range.1 hi; have := Finset.mem_range.1 hj; omega
  · have := Finset.mem_range.1 hj; exact Finset.mem_range.2 (by omega)
  · have := Finset.mem_range.1 hj; omega
  · have h : i + 1 ≤ t := Finset.mem_range.1 hi
    rw [inv_eq_iff_mul_eq_one, ← npowU_add, ← npowU_zero (v := v)]
    congr 1
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring

/- English proof (translation)
Simplify using `[seg]`.
-/
theorem seg_card (t : ℕ) : (seg v 1 t).card = t := by simp [seg]

/- English proof (translation)
Introduce `V _ _ ρ x hx`. Establish `h1` using `hx.2.2.2 ϖ hu m le_rfl`. Rewrite `h1` using `[Tj_eq h0, satEig_top _ _ hx.2.2.1]`. Simplify using `only [Fin.is_lt, if_true] at h1`. Rewrite `h1` using `[heckeVec_central hx.2.1 (tor_const_comm h0 1)]`.

Rewrite using `[heckeVec_central hx.2.1 (tor_const_comm h0 (-1))]`. Establish `h2 : tor h0 (fun _ : Fin m => -1) * tor h0 (fun _ => 1) = 1`. Rewrite using `[← tor_add]`. Use `ext1`. Simplify using `[tor_val]`.

Establish `h3` using `congrArg (ρ (tor h0 fun _ : Fin m => -1)) h1`. Rewrite `h3` using `[← Module.End.mul_apply, ← map_mul, h2, map_one, Module.End.one_apply, map_smul]`. Use `conv_rhs => rw [h3, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`.
-/
theorem acts_neg {m : ℕ} {ϖ : Cv v} (hu : IsUnifV K v ϖ) (h0 : ϖ ≠ 0) (B : Multiset ℂˣ) :
    Acts (dosetInd ℂ (KGL v m) (tor h0 fun _ => -1)) B ((B.prod⁻¹ : ℂˣ) : ℂ) := by
  intro V _ _ ρ x hx
  have h1 := hx.2.2.2 ϖ hu m le_rfl
  rw [Tj_eq h0, satEig_top _ _ hx.2.2.1] at h1
  simp only [Fin.is_lt, if_true] at h1
  rw [heckeVec_central hx.2.1 (tor_const_comm h0 1)] at h1
  rw [heckeVec_central hx.2.1 (tor_const_comm h0 (-1))]
  have h2 : tor h0 (fun _ : Fin m => -1) * tor h0 (fun _ => 1) = 1 := by
    rw [← tor_add]; ext1; simp [tor_val]
  have h3 := congrArg (ρ (tor h0 fun _ : Fin m => -1)) h1
  rw [← Module.End.mul_apply, ← map_mul, h2, map_one, Module.End.one_apply, map_smul] at h3
  conv_rhs => rw [h3, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/- English proof (translation)
Rewrite using `[wt, tor_val, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, absV_pow, _root_.zpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul (absV_nonneg _), mul_div_assoc]`.
-/
theorem wt_const {m l : ℕ} {ϖ : Cv v} (h0 : ϖ ≠ 0) :
    wt ((l : ℝ) / 2) (tor h0 fun _ : Fin m => -1) = ((absV v ϖ⁻¹ ^ ((m * l : ℝ) / 2) : ℝ) : ℂ) := by
  rw [wt, tor_val, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, absV_pow,
    _root_.zpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul (absV_nonneg _), mul_div_assoc]

/- English proof (translation)
Use `⟨dosetInd ℂ (KGL v c) (tor h0 fun _ => -1), Final.DosetIndMem _ _ ℂ _, Final.DosetIndMem _ _ ℂ _, ?_, fun B _ => ⟨_, acts_neg hu h0 B, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[heckeVec_central (sphericalVector_fixed_left _ _) (tor_const_comm h0 (-1)), heckeVec_central (sphericalVector_fixed_right _ _) (tor_const_comm h0 (-1))]`. Use function extensionality and compare the values at `y`. Rewrite using `[rT_apply, rS_apply, wt_const, wt_const, mul_comm (c : ℝ)]`. Use `congr 2`.

Use extensionality with `i j`. Simplify using `[tor_val, diagonal_mul, mul_diagonal, mul_comm]`. Use `acts_neg (m := c + t) hu h0 (B + seg v 1 t)` as an intermediate fact. Rewrite `this` using `[Multiset.prod_add, seg_prod, mul_one]`. Then use the resulting hypothesis.
-/
theorem neg_mem_mtSub {c t : ℕ} {ϖ : Cv v} (hu : IsUnifV K v ϖ) (h0 : ϖ ≠ 0) :
    dosetInd ℂ (KGL v (c + t)) (tor h0 fun _ => -1) ∈ mtSub v c t := by
  refine ⟨dosetInd ℂ (KGL v c) (tor h0 fun _ => -1), Final.DosetIndMem _ _ ℂ _,
    Final.DosetIndMem _ _ ℂ _, ?_, fun B _ => ⟨_, acts_neg hu h0 B, ?_⟩⟩
  · rw [heckeVec_central (sphericalVector_fixed_left _ _) (tor_const_comm h0 (-1)),
      heckeVec_central (sphericalVector_fixed_right _ _) (tor_const_comm h0 (-1))]
    funext y
    rw [rT_apply, rS_apply, wt_const, wt_const, mul_comm (c : ℝ)]
    congr 2
    ext i j
    simp [tor_val, diagonal_mul, mul_diagonal, mul_comm]
  · have := acts_neg (m := c + t) hu h0 (B + seg v 1 t)
    rwa [Multiset.prod_add, seg_prod, mul_one] at this

/- English proof (translation)
Establish `hK : IsCommensurated (KGL v (c + t))` using `Final.GLintComm K v _`. Take `⟨ϖ, hu⟩` from `exists_isUnifV v`. Establish `h0` using `ne_zero_of_isUnifV hu`. Establish `shift : ∀ g, dosetInd ℂ (KGL v (c + t)) g ∈ mtSub v c t → dosetInd ℂ (KGL v (c + t)) (tor h0 (fun _ => -1) * g) ∈ mtSub v c t`. Introduce `g hg`.

Use `set z := tor h0 fun _ : Fin (c + t) => -1`. Establish `hc` using `conv_mem_mtSub _ (neg_mem_mtSub hu h0) _ hg`. Establish `hb` using `(Final.HeckeConvMem _ _ ℂ hK _ (Final.DosetIndMem _ (KGL v (c + t)) ℂ z) _ (Final.DosetIndMem _ (KGL v (c + t)) ℂ g)).1`. Establish `hne` using `conv_top hK z g`. Establish `e : dosetInd ℂ (KGL v (c + t)) (z * g) = (conv (KGL v (c + t)) (dosetInd ℂ (KGL v (c + t)) z) (dosetInd ℂ (KGL v (c + t)) g) (z * g))⁻¹ • conv (KGL v (c + t)) (dosetInd ℂ (KGL v (c + t)) z) (dosetInd ℂ (KGL v (c + t)) g)`.

Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : ∃ a ∈ KGL v (c + t), ∃ b ∈ KGL v (c + t), x = a * (z * g) * b`. Rewrite using `[dosetInd_of_mem hx]`. Take `⟨a, ha, b, hb', rfl⟩` from `hx`. Rewrite using `[Pi.smul_apply, hb ⟨a, ha⟩ ⟨b, hb'⟩, smul_eq_mul, inv_mul_cancel₀ hne]`.

Rewrite using `[dosetInd_of_not hx, Pi.smul_apply, smul_eq_mul, eq_comm, mul_eq_zero]`. Use `Or.inr (by_contra fun h => hx ?_)` and prove the remaining obligations. Take `⟨y, y', ⟨a, ha, b, hb, rfl⟩, ⟨a', ha', b', hb', rfl⟩, rfl⟩` from `conv_supp hK h`. Use `⟨a * b * a', mul_mem (mul_mem ha hb) ha', b', hb', ?_⟩` and prove the remaining obligations. Establish `: z * (b * a') = b * a' * z` using `tor_const_comm h0 (-1) (b * a')`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hc`. Establish `hall : ∀ (N : ℕ) (a : Fin (c + t) → ℤ), Antitone a → (∀ i, 0 ≤ a i + N) → dosetInd ℂ (KGL v (c + t)) (tor h0 a) ∈ mtSub v c t`. Introduce `N`.

Proceed by induction on `N with`. Consider the case `zero`. Introduce `a ha ha0`. Take `⟨d, rfl⟩ : ∃ d : Fin (c + t) → ℕ, a = fun i => (d i : ℤ)` from `⟨fun i => (a i).toNat, funext fun i => (Int.toNat_of_nonneg (by simpa using ha0 i)).symm⟩`. Conclude with `gen_nat h0 hu _ (Tj_mem_mtSub hu) conv_mem_mtSub _ _ d (fun a b hab => Int.ofNat_le.1 (ha hab)) rfl rfl`.

Consider the case `succ N ih`. Introduce `a ha ha0`. Use `shift _ (ih (fun i => a i + 1) (fun i j hij => by have := ha hij; simp only; omega) fun i => by have := ha0 i; push_cast at this; omega)` as an intermediate fact. Rewrite `this` using `[← tor_add]`. Use `this using 3` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Take `⟨a, ha, hg⟩` from `cartan h0 hu g`. Rewrite using `[dosetInd_congr hg]`. Use `hall (∑ i, (a i).natAbs) a ha fun i => ?_` and prove the remaining obligations.

Use `Finset.single_le_sum (f := fun i => (a i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem dosetInd_mem_mtSub {c t : ℕ} (g : GL (Fin (c + t)) (Cv v)) :
    dosetInd ℂ (KGL v (c + t)) g ∈ mtSub v c t := by
  have hK : IsCommensurated (KGL v (c + t)) := Final.GLintComm K v _
  obtain ⟨ϖ, hu⟩ := exists_isUnifV v
  have h0 := ne_zero_of_isUnifV hu
  have shift : ∀ g, dosetInd ℂ (KGL v (c + t)) g ∈ mtSub v c t →
      dosetInd ℂ (KGL v (c + t)) (tor h0 (fun _ => -1) * g) ∈ mtSub v c t := by
    intro g hg
    set z := tor h0 fun _ : Fin (c + t) => -1
    have hc := conv_mem_mtSub _ (neg_mem_mtSub hu h0) _ hg
    have hb := (Final.HeckeConvMem _ _ ℂ hK _ (Final.DosetIndMem _ (KGL v (c + t)) ℂ z) _
      (Final.DosetIndMem _ (KGL v (c + t)) ℂ g)).1
    have hne := conv_top hK z g
    have e : dosetInd ℂ (KGL v (c + t)) (z * g) = (conv (KGL v (c + t))
        (dosetInd ℂ (KGL v (c + t)) z)
        (dosetInd ℂ (KGL v (c + t)) g) (z * g))⁻¹ • conv (KGL v (c + t))
        (dosetInd ℂ (KGL v (c + t)) z) (dosetInd ℂ (KGL v (c + t)) g) := by
      funext x
      by_cases hx : ∃ a ∈ KGL v (c + t), ∃ b ∈ KGL v (c + t), x = a * (z * g) * b
      · rw [dosetInd_of_mem hx]
        obtain ⟨a, ha, b, hb', rfl⟩ := hx
        rw [Pi.smul_apply, hb ⟨a, ha⟩ ⟨b, hb'⟩, smul_eq_mul, inv_mul_cancel₀ hne]
      · rw [dosetInd_of_not hx, Pi.smul_apply, smul_eq_mul, eq_comm, mul_eq_zero]
        refine Or.inr (by_contra fun h => hx ?_)
        obtain ⟨y, y', ⟨a, ha, b, hb, rfl⟩, ⟨a', ha', b', hb', rfl⟩, rfl⟩ := conv_supp hK h
        refine ⟨a * b * a', mul_mem (mul_mem ha hb) ha', b', hb', ?_⟩
        have : z * (b * a') = b * a' * z := tor_const_comm h0 (-1) (b * a')
        calc a * z * b * (a' * g * b') = a * (z * (b * a')) * g * b' := by group
          _ = _ := by rw [this]; group
    rw [e]
    exact Submodule.smul_mem _ _ hc
  have hall : ∀ (N : ℕ) (a : Fin (c + t) → ℤ), Antitone a → (∀ i, 0 ≤ a i + N) →
      dosetInd ℂ (KGL v (c + t)) (tor h0 a) ∈ mtSub v c t := by
    intro N
    induction N with
    | zero =>
      intro a ha ha0
      obtain ⟨d, rfl⟩ : ∃ d : Fin (c + t) → ℕ, a = fun i => (d i : ℤ) :=
        ⟨fun i => (a i).toNat, funext fun i =>
          (Int.toNat_of_nonneg (by simpa using ha0 i)).symm⟩
      exact gen_nat h0 hu _ (Tj_mem_mtSub hu) conv_mem_mtSub _ _ d
        (fun a b hab => Int.ofNat_le.1 (ha hab)) rfl rfl
    | succ N ih =>
      intro a ha ha0
      have := shift _ (ih (fun i => a i + 1) (fun i j hij => by have := ha hij; simp only; omega)
        fun i => by have := ha0 i; push_cast at this; omega)
      rw [← tor_add] at this
      convert this using 3
      funext i
      simp
  obtain ⟨a, ha, hg⟩ := cartan h0 hu g
  rw [dosetInd_congr hg]
  refine hall (∑ i, (a i).natAbs) a ha fun i => ?_
  have := Finset.single_le_sum (f := fun i => (a i).natAbs) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  omega

def theta (m : ℕ) : GL (Fin m) (Cv v) ≃* GL (Fin m) (Cv v) where
  toFun g := tr g⁻¹
  invFun g := tr g⁻¹
  left_inv _ := Units.ext rfl
  right_inv _ := Units.ext rfl
  map_mul' g h := by rw [_root_.mul_inv_rev, GlobalTheory.SplitHecke.tr_mul]

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem theta_theta {m : ℕ} (g : GL (Fin m) (Cv v)) : theta m (theta m g) = g := Units.ext rfl

/- English proof (translation)
Rewrite using `[mem_KGL, mem_KGL]`. Conclude with `(GlobalTheory.SplitHecke.gInt_tr.trans GlobalTheory.SplitHecke.gInt_inv).symm`.
-/
theorem theta_mem {m : ℕ} (g : GL (Fin m) (Cv v)) : g ∈ KGL v m ↔ theta m g ∈ KGL v m := by
  rw [mem_KGL, mem_KGL]
  exact (GlobalTheory.SplitHecke.gInt_tr.trans GlobalTheory.SplitHecke.gInt_inv).symm

/- English proof (translation)
The claim follows from `Units.ext (diagonal_transpose _)`.
-/
theorem theta_tor {m : ℕ} {ϖ : Cv v} (h0 : ϖ ≠ 0) (a : Fin m → ℤ) :
    theta m (tor h0 a) = (tor h0 a)⁻¹ := Units.ext (diagonal_transpose _)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Distinguish the cases in `h : ∃ a ∈ KGL v m, ∃ b ∈ KGL v m, x = a * theta m g * b`. Rewrite using `[dosetInd_of_mem h]`. Take `⟨a, ha, b, hb, rfl⟩` from `h`. Conclude with `dosetInd_of_mem ⟨_, (theta_mem a).1 ha, _, (theta_mem b).1 hb, by`.

Rewrite using `[map_mul, map_mul, theta_theta]⟩`. Rewrite using `[dosetInd_of_not h]`. Use `dosetInd_of_not fun ⟨a, ha, b, hb, e⟩ => h ⟨_, (theta_mem a).1 ha, _, (theta_mem b).1 hb, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_mul, ← e, theta_theta]`.
-/
theorem dosetInd_theta {m : ℕ} (g : GL (Fin m) (Cv v)) :
    dosetInd ℂ (KGL v m) g ∘ theta m = dosetInd ℂ (KGL v m) (theta m g) := by
  funext x
  by_cases h : ∃ a ∈ KGL v m, ∃ b ∈ KGL v m, x = a * theta m g * b
  · rw [dosetInd_of_mem h]
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact dosetInd_of_mem ⟨_, (theta_mem a).1 ha, _, (theta_mem b).1 hb, by
      rw [map_mul, map_mul, theta_theta]⟩
  · rw [dosetInd_of_not h]
    refine dosetInd_of_not fun ⟨a, ha, b, hb, e⟩ => h ⟨_, (theta_mem a).1 ha, _,
      (theta_mem b).1 hb, ?_⟩
    rw [← map_mul, ← map_mul, ← e, theta_theta]

/- English proof (translation)
Rewrite using `[heckeVec_comp_symm (theta m) theta_mem (Final.DosetIndMem _ (KGL v m) ℂ g).1 hx, dosetInd_theta]`.
-/
theorem heckeVec_theta {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin m) (Cv v)) V} {x : V} (hx : x ∈ fixed ρ (KGL v m))
    (g : GL (Fin m) (Cv v)) :
    heckeVec (ρ.comp (theta m).symm.toMonoidHom) (KGL v m) (dosetInd ℂ (KGL v m) g) x =
      heckeVec ρ (KGL v m) (dosetInd ℂ (KGL v m) (theta m g)) x := by
  rw [heckeVec_comp_symm (theta m) theta_mem (Final.DosetIndMem _ (KGL v m) ℂ g).1 hx,
    dosetInd_theta]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Distinguish the cases in `h : ∃ a ∈ J, ∃ b ∈ J, x = a * g⁻¹ * b`. Rewrite using `[dosetInd_of_mem h]`. Take `⟨a, ha, b, hb, rfl⟩` from `h`. Conclude with `dosetInd_of_mem ⟨_, inv_mem hb, _, inv_mem ha, by group⟩`.

Rewrite using `[dosetInd_of_not h]`. Use `dosetInd_of_not fun ⟨a, ha, b, hb, e⟩ => h ⟨_, inv_mem hb, _, inv_mem ha, ?_⟩` and prove the remaining obligations. Rewrite using `[← inv_inv x, e]`. Use `group`.
-/
theorem dosetInd_inv {G : Type} [Group G] (J : Subgroup G) (g : G) :
    (fun x => dosetInd ℂ J g x⁻¹) = dosetInd ℂ J g⁻¹ := by
  funext x
  by_cases h : ∃ a ∈ J, ∃ b ∈ J, x = a * g⁻¹ * b
  · rw [dosetInd_of_mem h]
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact dosetInd_of_mem ⟨_, inv_mem hb, _, inv_mem ha, by group⟩
  · rw [dosetInd_of_not h]
    refine dosetInd_of_not fun ⟨a, ha, b, hb, e⟩ => h ⟨_, inv_mem hb, _, inv_mem ha, ?_⟩
    rw [← inv_inv x, e]; group

/- English proof (translation)
Use `⟨hx.1, (mem_fixed_comp_symm (theta m) theta_mem).2 hx.2.1, by simpa using hx.2.2.1, fun ϖ hu j hj => ?_⟩` and prove the remaining obligations. Establish `h0` using `ne_zero_of_isUnifV hu`. Use `(GlobalTheory.T.satake_vector_iff_inverse_doubleCosets K v m V ρ x B hx.1 hx.2.1 hx.2.2.1).1 hx ϖ hu j hj` as an intermediate fact. Rewrite `this` using `[Tj_eq h0, dosetInd_inv]`. Rewrite using `[Tj_eq h0, heckeVec_theta hx.2.1, theta_tor, this]`.
-/
theorem sat_theta {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin m) (Cv v)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL v ρ x B) :
    IsSatVecGL v (ρ.comp (theta m).symm.toMonoidHom) x (B.map (·⁻¹)) := by
  refine ⟨hx.1, (mem_fixed_comp_symm (theta m) theta_mem).2 hx.2.1, by simpa using hx.2.2.1,
    fun ϖ hu j hj => ?_⟩
  have h0 := ne_zero_of_isUnifV hu
  have := (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets K v m V ρ x B hx.1 hx.2.1 hx.2.2.1).1 hx ϖ hu j hj
  rw [Tj_eq h0, dosetInd_inv] at this
  rw [Tj_eq h0, heckeVec_theta hx.2.1, theta_tor, this]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨α, rfl⟩ : ∃ α : Fin m → ℂˣ, Finset.univ.val.map α = B := by`. Take `⟨l, rfl⟩` from `Quot.exists_rep B`. Take `rfl : l.length = m` from `hB`. Conclude with `⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩`. Take `⟨x, hx⟩` from `(hasSatGL_psFunGL (w := v) α).exists_vec`.

Conclude with `⟨_, _, _, _, x, hx⟩`.
-/
theorem exists_sat (m : ℕ) (B : Multiset ℂˣ) (hB : B.card = m) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (GL (Fin m) (Cv v)) V) (x : V), IsSatVecGL v ρ x B := by
  obtain ⟨α, rfl⟩ : ∃ α : Fin m → ℂˣ, Finset.univ.val.map α = B := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep B
    obtain rfl : l.length = m := hB
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨x, hx⟩ := (hasSatGL_psFunGL (w := v) α).exists_vec
  exact ⟨_, _, _, _, x, hx⟩

/- English proof (translation)
Establish `: f ∈ Submodule.span ℂ (Set.range fun e : Fin m → ℤ => dosetInd ℂ (KGL v m) (tor h0 e))` using `mem_of_supp _ hf fun g _ => by`. Take `⟨a, -, hg⟩` from `cartan h0 hu g`. Rewrite using `[dosetInd_congr hg]`. Conclude with `Submodule.subset_span ⟨a, rfl⟩`. Take `⟨a, ha⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 this`.

Conclude with `⟨a.support, a, ha.symm⟩`.
-/
theorem hecke_eq_sum {m : ℕ} {ϖ : Cv v} (hu : IsUnifV K v ϖ) (h0 : ϖ ≠ 0)
    {f : GL (Fin m) (Cv v) → ℂ} (hf : f ∈ Hecke ℂ (KGL v m)) :
    ∃ (I : Finset (Fin m → ℤ)) (a : (Fin m → ℤ) → ℂ),
      f = ∑ e ∈ I, a e • dosetInd ℂ (KGL v m) (tor h0 e) := by
  have : f ∈ Submodule.span ℂ (Set.range fun e : Fin m → ℤ => dosetInd ℂ (KGL v m) (tor h0 e)) :=
    mem_of_supp _ hf fun g _ => by
      obtain ⟨a, -, hg⟩ := cartan h0 hu g
      rw [dosetInd_congr hg]
      exact Submodule.subset_span ⟨a, rfl⟩
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 this
  exact ⟨a.support, a, ha.symm⟩

/- English proof (translation)
Simplify using `[linAct, rS_apply, wt, absV_one]`.
-/
theorem linAct_S {n c : ℕ} (g : GL (Fin c) (Cv v)) (Φ) (y) :
    linAct v 1 1 g (1 : GL (Fin n) (Cv v)) Φ y = rS v n c g Φ y := by
  simp [linAct, rS_apply, wt, absV_one]

/- English proof (translation)
Establish `h : ((theta n).symm z).1.det = z.1.det⁻¹`. Express the relevant statement in the definitionally equal form `((z⁻¹).1ᵀ).det = _`. Rewrite using `[det_transpose, Matrix.coe_units_inv, det_nonsing_inv, Ring.inverse_eq_inv']`. Establish `h2 : ((theta n).symm z).1ᵀ = (z⁻¹).1` using `rfl`. Rewrite using `[rT_apply, wt, h, h2, absV_inv, Real.inv_rpow (absV_nonneg _), ← Real.rpow_neg (absV_nonneg _), ← neg_div]`.

Simplify using `[linAct, absV_one]`.
-/
theorem linAct_alt {n c : ℕ} (z : GL (Fin n) (Cv v)) (Φ) (y) :
    linAct v 1 1 (1 : GL (Fin c) (Cv v)) z Φ y = rT v n c ((theta n).symm z) Φ y := by
  have h : ((theta n).symm z).1.det = z.1.det⁻¹ := by
    change ((z⁻¹).1ᵀ).det = _
    rw [det_transpose, Matrix.coe_units_inv, det_nonsing_inv, Ring.inverse_eq_inv']
  have h2 : ((theta n).symm z).1ᵀ = (z⁻¹).1 := rfl
  rw [rT_apply, wt, h, h2, absV_inv, Real.inv_rpow (absV_nonneg _), ← Real.rpow_neg (absV_nonneg _),
    ← neg_div]
  simp [linAct, absV_one]

/- English proof (translation)
Introduce `K _ _ v c t ϖ hu m'`. Establish `h0` using `ne_zero_of_isUnifV hu`. Establish `hK : IsCommensurated (KGL v c)` using `Final.GLintComm K v _`. Establish `hK' : IsCommensurated (KGL v (c + t))` using `Final.GLintComm K v _`. Establish `hd` using `fun {m} (g : GL (Fin m) (Cv v)) => Final.DosetIndMem _ (KGL v m) ℂ g`.

Take `⟨f, -, a2, a3, a4⟩` from `dosetInd_mem_mtSub (theta (c + t) m')`. Take `⟨I, a, rfl⟩` from `hecke_eq_sum hu h0 a2`. Use `⟨I, a, tor h0, fun e => rfl, fun y => ?_, fun B lam hlam => ?_⟩` and prove the remaining obligations. Rewrite `a3` using `[← heckeVec_theta (sphericalVector_fixed_left _ _), heckeVec_sum_left hK _ _ _ _ fun e => hd _]`. Use `congrFun a3 y` as an intermediate fact.

Rewrite `this` using `[heckeVec_apply hK' (hd _), Finset.sum_apply]`. Simplify using `only [linAct_S, linAct_alt]`. Use `this.trans (Finset.sum_congr rfl fun e _ => ?_)` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, heckeVec_apply hK (hd _)]`. Both sides reduce to the same expression.

Take `⟨V, _, _, ρ, x, hx, -⟩` from `hlam 0`. Establish `hB` using `hx.2.2.1`. Take `⟨l, l1, l2⟩` from `a4 (B.map (·⁻¹)) (by simpa using hB)`. Take `⟨V', _, _, ρ', x', hx'⟩` from `exists_sat (v := v) (c + t) (B + seg v 1 t) (by rw [Multiset.card_add, hB, seg_card])`. Establish `e1` using `l1 V _ x (sat_theta hx)`.

Establish `e2` using `l2 V' _ x' (by simpa only [Multiset.map_add, seg_inv] using sat_theta hx')`. Rewrite `e2` using `[heckeVec_theta hx'.2.1, theta_theta]`. Establish `e3 : ∀ e, heckeVec (ρ.comp (theta c).symm.toMonoidHom) (KGL v c) (dosetInd ℂ (KGL v c) (tor h0 e)) x = lam e • x` using `fun e => by`. Take `⟨V₀, _, _, ρ₀, x₀, hx₀, e₀⟩` from `hlam e`. Take `⟨z, hz⟩` from `GlobalTheory.ChainOnto.SatHeckeChar.heckeVec_eq_smul_of_isSatVecGL K v c B _ (hd (tor h0 e)⁻¹)`.

Rewrite using `[heckeVec_theta hx.2.1, theta_tor, hz V ρ x hx, smul_left_injective ℂ hx₀.1 ((hz V₀ ρ₀ x₀ hx₀).symm.trans e₀)]`. Rewrite `e1` using `[heckeVec_sum_left hK _ _ _ _ fun e => hd _]`. Simplify using `only [e3, smul_smul, ← Finset.sum_smul] at e1`. Use `⟨V', _, _, ρ', x', hx', ?_⟩` and prove the remaining obligations. Rewrite using `[e2, smul_left_injective ℂ hx.1 e1]`.
-/
theorem sphMatchAll : SphMatchAll := by
  intro K _ _ v c t ϖ hu m'
  have h0 := ne_zero_of_isUnifV hu
  have hK : IsCommensurated (KGL v c) := Final.GLintComm K v _
  have hK' : IsCommensurated (KGL v (c + t)) := Final.GLintComm K v _
  have hd := fun {m} (g : GL (Fin m) (Cv v)) => Final.DosetIndMem _ (KGL v m) ℂ g
  obtain ⟨f, -, a2, a3, a4⟩ := dosetInd_mem_mtSub (theta (c + t) m')
  obtain ⟨I, a, rfl⟩ := hecke_eq_sum hu h0 a2
  refine ⟨I, a, tor h0, fun e => rfl, fun y => ?_, fun B lam hlam => ?_⟩
  · rw [← heckeVec_theta (sphericalVector_fixed_left _ _), heckeVec_sum_left hK _ _ _ _ fun e => hd _] at a3
    have := congrFun a3 y
    rw [heckeVec_apply hK' (hd _), Finset.sum_apply] at this
    simp only [linAct_S, linAct_alt]
    refine this.trans (Finset.sum_congr rfl fun e _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, heckeVec_apply hK (hd _)]
    rfl
  · obtain ⟨V, _, _, ρ, x, hx, -⟩ := hlam 0
    have hB := hx.2.2.1
    obtain ⟨l, l1, l2⟩ := a4 (B.map (·⁻¹)) (by simpa using hB)
    obtain ⟨V', _, _, ρ', x', hx'⟩ := exists_sat (v := v) (c + t) (B + seg v 1 t)
      (by rw [Multiset.card_add, hB, seg_card])
    have e1 := l1 V _ x (sat_theta hx)
    have e2 := l2 V' _ x' (by simpa only [Multiset.map_add, seg_inv] using sat_theta hx')
    rw [heckeVec_theta hx'.2.1, theta_theta] at e2
    have e3 : ∀ e, heckeVec (ρ.comp (theta c).symm.toMonoidHom) (KGL v c)
        (dosetInd ℂ (KGL v c) (tor h0 e)) x = lam e • x := fun e => by
      obtain ⟨V₀, _, _, ρ₀, x₀, hx₀, e₀⟩ := hlam e
      obtain ⟨z, hz⟩ := GlobalTheory.ChainOnto.SatHeckeChar.heckeVec_eq_smul_of_isSatVecGL K v c B _
        (hd (tor h0 e)⁻¹)
      rw [heckeVec_theta hx.2.1, theta_tor, hz V ρ x hx,
        smul_left_injective ℂ hx₀.1 ((hz V₀ ρ₀ x₀ hx₀).symm.trans e₀)]
    rw [heckeVec_sum_left hK _ _ _ _ fun e => hd _] at e1
    simp only [e3, smul_smul, ← Finset.sum_smul] at e1
    refine ⟨V', _, _, ρ', x', hx', ?_⟩
    rw [e2, smul_left_injective ℂ hx.1 e1]

end CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

end
