import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgTwist

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Establish `h2 : (2 : ZMod 2) = 0` using `rfl`. Take `⟨k, rfl | rfl⟩` from `Int.even_or_odd' j`. Rewrite using `[Even.neg_one_zpow (even_two_mul k)]`. Use `push_cast`. Rewrite using `[h2, zero_mul]`.

Simplify using `[sg]`. Rewrite using `[Odd.neg_one_zpow (odd_two_mul_add_one k)]`. Use `push_cast`. Rewrite using `[h2, zero_mul, zero_add]`. Use `show _ = (-1 : K) ^ 1`.

Simplify using the standard rewrite rules.
-/
private theorem neg_one_zpow_sg (K : Type) [CommRing K] (j : ℤ) :
    (((-1 : Kˣ) ^ j : Kˣ) : K) = sg K (j : ZMod 2) := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
  · rw [Even.neg_one_zpow (even_two_mul k)]
    push_cast
    rw [h2, zero_mul]
    simp [sg]
  · rw [Odd.neg_one_zpow (odd_two_mul_add_one k)]
    push_cast
    rw [h2, zero_mul, zero_add]
    show _ = (-1 : K) ^ 1
    simp

/- English proof (translation)
Simplify using `[sg]`.
-/
private theorem map_sg {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (j : ZMod 2) :
    f (sg K j) = sg K' j := by simp [sg]

/- English proof (translation)
Rewrite using `[sg, ← mul_pow]`. Simplify using the standard rewrite rules.
-/
private theorem sg_sq (K : Type) [CommRing K] (j : ZMod 2) : sg K j * sg K j = 1 := by
  rw [sg, ← mul_pow]; simp

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
  (S : Space O F 3)

/- English proof (translation)
Take `⟨ρ', h1, h2⟩` from `alg_twist (-1 : S.Rˣ) S.ρ`. Take `⟨⟨c1, c2⟩, ⟨b1, b2⟩, d⟩` from `S.lift`. Establish `hl : IsLift O ρ'`. Use `⟨⟨fun i j N => ?_, by rw [h2]; exact c2⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩` and prove the remaining obligations. Simplify using `only [h1, map_mul]`.

Conclude with `(c1 i j N).comp (fun y => Ideal.Quotient.mk _ _ * y)`. Rewrite using `[NRep.map_r, h1, sub_self, zpow_zero, Units.val_one, one_mul]`. Conclude with `b1 g i`. Rewrite using `[NRep.map_ψ, h2]`. Conclude with `b2 v i g`.

Rewrite using `[NRep.map_r, h1, map_mul]`. Use `d g i j hij` as an intermediate fact. Rewrite `this` using `[NRep.map_r]`. Rewrite using `[this, mul_zero]`. Take `⟨τ, hτ, -⟩` from `S.univ S.R ρ' hl`.

Use `⟨τ, fun g i j => ?_, fun v i g => ?_⟩` and prove the remaining obligations. Rewrite using `[← h1, ← hτ]`. Both sides reduce to the same expression. Use `conv_rhs => rw [← h2, ← hτ]`. Both sides reduce to the same expression.
-/
private theorem ex_tau : ∃ τ : S.R →ₐ[O] S.R,
    (∀ g i j, τ (S.ρ.r g i j) = (((-1 : S.Rˣ) ^ (w 3 i - w 3 j) : S.Rˣ) : S.R) * S.ρ.r g i j) ∧
      ∀ v i g, τ (S.ρ.ψ v i g) = S.ρ.ψ v i g := by
  obtain ⟨ρ', h1, h2⟩ := alg_twist (-1 : S.Rˣ) S.ρ
  obtain ⟨⟨c1, c2⟩, ⟨b1, b2⟩, d⟩ := S.lift
  have hl : IsLift O ρ' := by
    refine ⟨⟨fun i j N => ?_, by rw [h2]; exact c2⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩
    · simp only [h1, map_mul]
      exact (c1 i j N).comp (fun y => Ideal.Quotient.mk _ _ * y)
    · rw [NRep.map_r, h1, sub_self, zpow_zero, Units.val_one, one_mul]
      exact b1 g i
    · rw [NRep.map_ψ, h2]
      exact b2 v i g
    · rw [NRep.map_r, h1, map_mul]
      have := d g i j hij
      rw [NRep.map_r] at this
      rw [this, mul_zero]
  obtain ⟨τ, hτ, -⟩ := S.univ S.R ρ' hl
  refine ⟨τ, fun g i j => ?_, fun v i g => ?_⟩
  · rw [← h1, ← hτ]; rfl
  · conv_rhs => rw [← h2, ← hτ]
    rfl

/- English proof (translation)
Establish `hm : ∀ M : List (F.G0 × Fin 3 × Fin 3), τ (M.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod = (((-1 : S.Rˣ) ^ (M.map fun s => w 3 s.2.1 - w 3 s.2.2).sum : S.Rˣ) : S.R) * (M.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod`. Introduce `M`. Proceed by induction on `M with`. Consider the case `nil => simp`. Consider the case `cons a M ih`.

Simplify using `only [List.map_cons, List.prod_cons, List.sum_cons, map_mul, h1, ih, _root_.zpow_add, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `ha : ∀ y ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}), τ y = y`. Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Break down `hy with ⟨M, e, rfl⟩ | ⟨v, i, g, rfl⟩` into its components or cases. Rewrite using `[hm, e]`. Simplify using the standard rewrite rules. Conclude with `h2 v i g`.

Consider the case `algebraMap r => exact τ.commutes r`. Consider the case `add a b _ _ ha hb => rw [map_add, ha, hb]`. Consider the case `mul a b _ _ ha hb => rw [map_mul, ha, hb]`. Establish `hloc : (maximalIdeal S.R).map τ ≤ maximalIdeal S.R`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `y hy`. Rewrite using `[Ideal.mem_comap, ← res_eq_zero_iff O, res_map, res_eq_zero_iff]`. Conclude with `hy`. Introduce `y hy`. Rewrite using `[← sub_eq_zero]`.

Use `IsHausdorff.haus (I := maximalIdeal S.R) inferInstance _ fun N => ?_` and prove the remaining obligations. Take `⟨z, hz, hyz⟩` from `hy N`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`. Establish `e : τ y - y = τ (y - z) - (y - z)` using `by rw [map_sub, ha z hz]; ring`. Rewrite using `[e]`.

Use `sub_mem ?_ hyz` and prove the remaining obligations. Use `Ideal.mem_map_of_mem τ hyz` as an intermediate fact. Rewrite `this` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hloc N this`.
-/
private theorem tau_B (τ : S.R →ₐ[O] S.R)
    (h1 : ∀ g i j, τ (S.ρ.r g i j) = (((-1 : S.Rˣ) ^ (w 3 i - w 3 j) : S.Rˣ) : S.R) * S.ρ.r g i j)
    (h2 : ∀ v i g, τ (S.ρ.ψ v i g) = S.ρ.ψ v i g) : ∀ y ∈ S.B, τ y = y := by
  have hm : ∀ M : List (F.G0 × Fin 3 × Fin 3), τ (M.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod =
      (((-1 : S.Rˣ) ^ (M.map fun s => w 3 s.2.1 - w 3 s.2.2).sum : S.Rˣ) : S.R) *
        (M.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod := by
    intro M
    induction M with
    | nil => simp
    | cons a M ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul, h1, ih, _root_.zpow_add, Units.val_mul]
      ring
  have ha : ∀ y ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}), τ y = y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨M, e, rfl⟩ | ⟨v, i, g, rfl⟩
      · rw [hm, e]; simp
      · exact h2 v i g
    | algebraMap r => exact τ.commutes r
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
  have hloc : (maximalIdeal S.R).map τ ≤ maximalIdeal S.R := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, ← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  intro y hy
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := maximalIdeal S.R) inferInstance _ fun N => ?_
  obtain ⟨z, hz, hyz⟩ := hy N
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have e : τ y - y = τ (y - z) - (y - z) := by rw [map_sub, ha z hz]; ring
  rw [e]
  refine sub_mem ?_ hyz
  have := Ideal.mem_map_of_mem τ hyz
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono hloc N this

/- English proof (translation)
Take `⟨τ, h1, h2⟩` from `ex_tau S`. Establish `hB` using `tau_B S τ h1 h2`. Establish `h1' : ∀ g i j, τ (S.ρ.r g i j) = sg S.R (pw i j) * S.ρ.r g i j` using `fun g i j => by`. Rewrite using `[h1, neg_one_zpow_sg]`. Both sides reduce to the same expression.

Establish `hA : ∀ y ∈ S.A, τ y ∈ S.A`. Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Break down `hy with hy | ⟨g, i, j, rfl⟩` into its components or cases.

Rewrite using `[hB y hy]`. Conclude with `S.B_le_A hy`. Rewrite using `[h1']`. Conclude with `mul_mem (pow_mem (neg_mem (one_mem _)) _) (S.r_mem g i j)`. Consider the case `algebraMap r => rw [τ.commutes r]`.

Conclude with `S.A.algebraMap_mem r`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`.

Set `τA : S.A →ₐ[O] S.A` to `(τ.comp S.A.val).codRestrict S.A fun a => hA a a.2`. Establish `e1 : ∀ g i j, τA (S.u.r g i j) = sg S.A (pw i j) * S.u.r g i j` using `fun g i j => Subtype.ext ((h1' g i j).trans (by`. Rewrite using `[← map_sg (S.A.val : S.A →+* S.R)]`. Use the proof step `rfl))`. Establish `e2 : ∀ y : S.B, τA (S.inc y) = S.inc y` using `fun y => Subtype.ext (hB y y.2)`.

Establish `ind : ∀ P : S.A → Prop, (∀ y : S.B, P (S.inc y)) → (∀ g i j, P (S.u.r g i j)) → (∀ a b, P a → P b → P (a + b)) → (∀ a b, P a → P b → P (a * b)) → ∀ a, P a`. Introduce `P p1 p2 p3 p4 ⟨y, hy⟩`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Break down `hy with hy | ⟨g, i, j, rfl⟩` into its components or cases.

Conclude with `p1 ⟨y, hy⟩`. Conclude with `p2 g i j`. Consider the case `algebraMap r => exact p1 (algebraMap O S.B r)`. Consider the case `add a b ha hb qa qb => exact p3 ⟨a, ha⟩ ⟨b, hb⟩ qa qb`. Consider the case `mul a b ha hb qa qb => exact p4 ⟨a, ha⟩ ⟨b, hb⟩ qa qb`.

Use `⟨τA, e1, e2, ind _ (fun y => by rw [e2, e2]) (fun g i j => ?_) (fun a b qa qb => ?_) fun a b qa qb => ?_, ind _ (fun y => by rw [e2, sub_self]; exact zero_mem _) (fun g i j => ?_) (fun a b qa qb => ?_) fun a b qa qb => ?_⟩` and prove the remaining obligations. Rewrite using `[e1, map_mul, e1, ← mul_assoc]`. Use `map_sg (τA : S.A →+* S.A) (pw i j)` as an intermediate fact. Rewrite `this` using `[RingHom.coe_coe]`. Rewrite using `[this, sg_sq, one_mul]`.

Rewrite using `[map_add, map_add, qa, qb]`. Rewrite using `[map_mul, map_mul, qa, qb]`. Rewrite using `[e1, pw, ← neg_one_zpow_sg]`. Break down `Int.even_or_odd (w 3 i - w 3 j) with h | h` into its components or cases. Rewrite using `[h.neg_one_zpow]`.

Simplify using the standard rewrite rules. Conclude with `sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, i, j, h, rfl⟩)) (Ideal.subset_span ⟨g, i, j, h, rfl⟩)`. Rewrite using `[map_add, add_sub_add_comm]`. Conclude with `add_mem qa qb`. Establish `: τA (a * b) - a * b = (τA a - a) * τA b + a * (τA b - b)` using `by rw [map_mul]; ring`.

Rewrite using `[this]`. Conclude with `add_mem (Ideal.mul_mem_right _ _ qa) (Ideal.mul_mem_left _ _ qb)`.
-/
private theorem ex_tauA : ∃ τ : S.A →ₐ[O] S.A,
    (∀ g i j, τ (S.u.r g i j) = sg S.A (pw i j) * S.u.r g i j) ∧ (∀ y : S.B, τ (S.inc y) = S.inc y) ∧
      (∀ a, τ (τ a) = a) ∧ ∀ a, τ a - a ∈ S.u.ee := by
  obtain ⟨τ, h1, h2⟩ := ex_tau S
  have hB := tau_B S τ h1 h2
  have h1' : ∀ g i j, τ (S.ρ.r g i j) = sg S.R (pw i j) * S.ρ.r g i j := fun g i j => by
    rw [h1, neg_one_zpow_sg]; rfl
  have hA : ∀ y ∈ S.A, τ y ∈ S.A := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · rw [hB y hy]; exact S.B_le_A hy
      · rw [h1']
        exact mul_mem (pow_mem (neg_mem (one_mem _)) _) (S.r_mem g i j)
    | algebraMap r => rw [τ.commutes r]; exact S.A.algebraMap_mem r
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let τA : S.A →ₐ[O] S.A := (τ.comp S.A.val).codRestrict S.A fun a => hA a a.2
  have e1 : ∀ g i j, τA (S.u.r g i j) = sg S.A (pw i j) * S.u.r g i j := fun g i j =>
    Subtype.ext ((h1' g i j).trans (by
      rw [← map_sg (S.A.val : S.A →+* S.R)]; rfl))
  have e2 : ∀ y : S.B, τA (S.inc y) = S.inc y := fun y => Subtype.ext (hB y y.2)
  have ind : ∀ P : S.A → Prop, (∀ y : S.B, P (S.inc y)) → (∀ g i j, P (S.u.r g i j)) →
      (∀ a b, P a → P b → P (a + b)) → (∀ a b, P a → P b → P (a * b)) → ∀ a, P a := by
    intro P p1 p2 p3 p4 ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · exact p1 ⟨y, hy⟩
      · exact p2 g i j
    | algebraMap r => exact p1 (algebraMap O S.B r)
    | add a b ha hb qa qb => exact p3 ⟨a, ha⟩ ⟨b, hb⟩ qa qb
    | mul a b ha hb qa qb => exact p4 ⟨a, ha⟩ ⟨b, hb⟩ qa qb
  refine ⟨τA, e1, e2, ind _ (fun y => by rw [e2, e2]) (fun g i j => ?_) (fun a b qa qb => ?_) fun a b qa qb => ?_,
    ind _ (fun y => by rw [e2, sub_self]; exact zero_mem _) (fun g i j => ?_) (fun a b qa qb => ?_)
      fun a b qa qb => ?_⟩
  · rw [e1, map_mul, e1, ← mul_assoc]
    have := map_sg (τA : S.A →+* S.A) (pw i j)
    rw [RingHom.coe_coe] at this
    rw [this, sg_sq, one_mul]
  · rw [map_add, map_add, qa, qb]
  · rw [map_mul, map_mul, qa, qb]
  · rw [e1, pw, ← neg_one_zpow_sg]
    rcases Int.even_or_odd (w 3 i - w 3 j) with h | h
    · rw [h.neg_one_zpow]; simp
    · exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, i, j, h, rfl⟩))
        (Ideal.subset_span ⟨g, i, j, h, rfl⟩)
  · rw [map_add, add_sub_add_comm]; exact add_mem qa qb
  · have : τA (a * b) - a * b = (τA a - a) * τA b + a * (τA b - b) := by rw [map_mul]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ qa) (Ideal.mul_mem_left _ _ qb)

end

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ _ S x L hx`. Take `⟨τ, h1, h2, h3, h4⟩` from `ex_tauA S`. Take `⟨σ, hσ, -⟩` from `L.univ L.R (L.ι.comp τ) fun a => by`. Rewrite using `[← sub_eq_zero, ← map_sub, res_eq_zero_iff, AlgHom.comp_apply, ← map_sub]`. Use `hx (h4 a)` as an intermediate fact.

Rewrite `this` using `[← L.lies]`. Conclude with `this`. Take `⟨g₀, -, hu⟩` from `L.univ L.R L.ι fun _ => rfl`. Establish `hsq : σ.comp σ = AlgHom.id _ _` using `(hu (σ.comp σ) fun a => by`. Rewrite using `[AlgHom.comp_apply, hσ, AlgHom.comp_apply, hσ, AlgHom.comp_apply, h3]).trans`.

Use the proof step `(hu (AlgHom.id _ _) fun _ => rfl).symm`. Use `⟨σ, fun y => DFunLike.congr_fun hsq y, fun g a b => ?_, fun y => ?_⟩` and prove the remaining obligations. Use `show σ (L.ι (S.u.r g a b)) = sg _ _ * L.ι (S.u.r g a b)`. Rewrite using `[hσ, AlgHom.comp_apply, h1, map_mul, ← map_sg (L.ι : S.A →+* L.R)]`. Both sides reduce to the same expression.

Use `show σ (L.ι (S.inc y)) = sg _ _ * L.ι (S.inc y)`. Rewrite using `[hσ, AlgHom.comp_apply, h2]`. Simplify using `[sg]`.
-/
theorem UpperTheory.V.Fr.ep_inv :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → ∃ σ, L.IsInv σ := by
  intro l _ O _ _ _ _ F C₀ _ S x L hx
  obtain ⟨τ, h1, h2, h3, h4⟩ := ex_tauA S
  obtain ⟨σ, hσ, -⟩ := L.univ L.R (L.ι.comp τ) fun a => by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff, AlgHom.comp_apply, ← map_sub]
    have := hx (h4 a)
    rw [← L.lies] at this
    exact this
  obtain ⟨g₀, -, hu⟩ := L.univ L.R L.ι fun _ => rfl
  have hsq : σ.comp σ = AlgHom.id _ _ :=
    (hu (σ.comp σ) fun a => by
      rw [AlgHom.comp_apply, hσ, AlgHom.comp_apply, hσ, AlgHom.comp_apply, h3]).trans
      (hu (AlgHom.id _ _) fun _ => rfl).symm
  refine ⟨σ, fun y => DFunLike.congr_fun hsq y, fun g a b => ?_, fun y => ?_⟩
  · show σ (L.ι (S.u.r g a b)) = sg _ _ * L.ι (S.u.r g a b)
    rw [hσ, AlgHom.comp_apply, h1, map_mul, ← map_sg (L.ι : S.A →+* L.R)]
    rfl
  · show σ (L.ι (S.inc y)) = sg _ _ * L.ι (S.inc y)
    rw [hσ, AlgHom.comp_apply, h2]
    simp [sg]
