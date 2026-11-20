import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSublevelOfIntQuadraticGeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeightOneValuationsControlSubgroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.QuadTend

/- English proof (translation)
Use `set s : Set (Fin n → ℕ) := Set.range f`. Establish `hpwo : s.IsPWO` using `Set.isPWO_of_wellQuasiOrderedLE s`. Use `set m : Set (Fin n → ℕ) := {x | Minimal (· ∈ s) x}`. Establish `hm : m.Finite` using `(setOf_minimal_antichain (· ∈ s)).finite_of_partiallyWellOrderedOn (hpwo.mono (fun x hx => hx.prop))`. Establish `hpre : ∀ x ∈ m, ∃ j, f j = x` using `fun x hx => hx.prop`.

Break down `isEmpty_or_nonempty J with hJ | hJ` into its components or cases. Conclude with `⟨∅, fun i => isEmptyElim i⟩`. Use `choose! g hg using hpre`. Use `⟨hm.toFinset.image g, fun i => ?_⟩` and prove the remaining obligations. Take `⟨x, hxi, hx⟩` from `hpwo.exists_le_minimal (Set.mem_range_self i)`.

Conclude with `⟨g x, Finset.mem_image_of_mem g (hm.mem_toFinset.mpr hx), by rw [hg x hx]; exact hxi⟩`.
-/
theorem dickson_fin {J : Type*} (n : ℕ) (f : J → Fin n → ℕ) :
    ∃ F : Finset J, ∀ i, ∃ j ∈ F, f j ≤ f i := by
  classical
  set s : Set (Fin n → ℕ) := Set.range f
  have hpwo : s.IsPWO := Set.isPWO_of_wellQuasiOrderedLE s
  set m : Set (Fin n → ℕ) := {x | Minimal (· ∈ s) x}
  have hm : m.Finite := (setOf_minimal_antichain (· ∈ s)).finite_of_partiallyWellOrderedOn
    (hpwo.mono (fun x hx => hx.prop))
  have hpre : ∀ x ∈ m, ∃ j, f j = x := fun x hx => hx.prop
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨∅, fun i => isEmptyElim i⟩
  choose! g hg using hpre
  refine ⟨hm.toFinset.image g, fun i => ?_⟩
  obtain ⟨x, hxi, hx⟩ := hpwo.exists_le_minimal (Set.mem_range_self i)
  exact ⟨g x, Finset.mem_image_of_mem g (hm.mem_toFinset.mpr hx), by rw [hg x hx]; exact hxi⟩

section Cl

variable {G X : Type*} [CommGroup G] [AddCommGroup X] (κ : X → G)

def defect (a b : X) : G := κ (a + b) / (κ a * κ b)

variable {κ}

/- English proof (translation)
Establish `h` using `hc 0 0 0`. Simplify using `only [add_zero] at h`. Establish `h2 : κ 0 * (κ 0 * κ 0 * κ 0) = 1 * (κ 0 * κ 0 * κ 0)`. Rewrite using `[_root_.one_mul]`. Simplify `h` using `only [_root_.mul_assoc]`.

Conclude with `mul_right_cancel h2`.
-/
theorem kappa_zero (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) :
    κ 0 = 1 := by
  have h := hc 0 0 0
  simp only [add_zero] at h
  have h2 : κ 0 * (κ 0 * κ 0 * κ 0) = 1 * (κ 0 * κ 0 * κ 0) := by
    rw [_root_.one_mul]; simpa only [_root_.mul_assoc] using h
  exact mul_right_cancel h2

/- English proof (translation)
Unfold `defect`. Rewrite using `[div_mul_div_comm, div_eq_div_iff_mul_eq_mul]`. Establish `h` using `hc a a' b`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_comm, _root_.mul_assoc, _root_.mul_left_comm]`.

Use `_ = (κ (a + a') * κ (a + b) * κ (a' + b)) * κ b := by rw [h]`. Use `_ = κ (a + b) * κ (a' + b) * (κ (a + a') * κ b) := by simp only [mul_comm, _root_.mul_assoc, _root_.mul_left_comm]`.
-/
theorem defect_add_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (a a' b : X) : defect κ (a + a') b = defect κ a b * defect κ a' b := by
  unfold defect
  rw [div_mul_div_comm, div_eq_div_iff_mul_eq_mul]
  have h := hc a a' b
  calc κ (a + a' + b) * (κ a * κ b * (κ a' * κ b)) = (κ (a + a' + b) * κ a * κ a' * κ b) * κ b := by
        simp only [mul_comm, _root_.mul_assoc, _root_.mul_left_comm]
    _ = (κ (a + a') * κ (a + b) * κ (a' + b)) * κ b := by rw [h]
    _ = κ (a + b) * κ (a' + b) * (κ (a + a') * κ b) := by simp only [mul_comm, _root_.mul_assoc, _root_.mul_left_comm]

/- English proof (translation)
Unfold `defect`. Rewrite using `[add_comm, _root_.mul_comm]`.
-/
theorem defect_comm (a b : X) : defect κ a b = defect κ b a := by
  unfold defect; rw [add_comm, _root_.mul_comm]

/- English proof (translation)
Establish `h` using `defect_add_left hc 0 0 b`. Rewrite `h` using `[add_zero]`. Conclude with `(mul_eq_left.mp h.symm)`.
-/
theorem defect_zero_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (b : X) : defect κ 0 b = 1 := by
  have h := defect_add_left hc 0 0 b
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

/- English proof (translation)
Establish `h` using `defect_add_left hc a (-a) b`. Rewrite `h` using `[add_neg_cancel, defect_zero_left hc]`. Conclude with `eq_inv_of_mul_eq_one_right h.symm`.
-/
theorem defect_neg_left (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    (a b : X) : defect κ (-a) b = (defect κ a b)⁻¹ := by
  have h := defect_add_left hc a (-a) b
  rw [add_neg_cancel, defect_zero_left hc] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/- English proof (translation)
Unfold `defect`. Rewrite using `[mul_div_cancel]`.
-/
theorem kappa_add (a b : X) : κ (a + b) = κ a * κ b * defect κ a b := by
  unfold defect; rw [mul_div_cancel]

/- English proof (translation)
Use `set H := Subgroup.closure (Set.range (Sum.elim (fun i => κ (e i)) (fun p : J × J => κ (e p.1 + e p.2))))`. Establish `hk : ∀ i, κ (e i) ∈ H` using `fun i => Subgroup.subset_closure ⟨Sum.inl i, rfl⟩`. Establish `hg : ∀ i j, defect κ (e i) (e j) ∈ H` using `fun i j => H.div_mem (Subgroup.subset_closure ⟨Sum.inr (i, j), rfl⟩) (H.mul_mem (hk i) (hk j))`. Establish `mem : ∀ x : X, x ∈ AddSubgroup.closure (Set.range e)` using `fun x => he ▸ AddSubgroup.mem_top x`. Establish `step1 : ∀ i b, defect κ (e i) b ∈ H`.

Introduce `i b`. Proceed by induction on `mem b using AddSubgroup.closure_induction with`. Consider the case `mem x hx => obtain ⟨j, rfl⟩ := hx`. Conclude with `hg i j`. Consider the case `zero => rw [defect_comm, defect_zero_left hc]`.

Conclude with `H.one_mem`. Consider the case `add x y _ _ hx hy`. Rewrite using `[defect_comm, defect_add_left hc, defect_comm x, defect_comm y]`. Conclude with `H.mul_mem hx hy`. Consider the case `neg x _ hx => rw [defect_comm, defect_neg_left hc, defect_comm]`.

Conclude with `H.inv_mem hx`. Establish `step2 : ∀ a b, defect κ a b ∈ H`. Introduce `a b`. Proceed by induction on `mem a using AddSubgroup.closure_induction with`. Consider the case `mem x hx => obtain ⟨j, rfl⟩ := hx`.

Conclude with `step1 j b`. Consider the case `zero => rw [defect_zero_left hc]`. Conclude with `H.one_mem`. Consider the case `add x y _ _ hx hy => rw [defect_add_left hc]`. Conclude with `H.mul_mem hx hy`.

Consider the case `neg x _ hx => rw [defect_neg_left hc]`. Conclude with `H.inv_mem hx`. Proceed by induction on `mem a using AddSubgroup.closure_induction with`. Consider the case `mem x hx => obtain ⟨j, rfl⟩ := hx`. Conclude with `hk j`.

Consider the case `zero => rw [kappa_zero hc]`. Conclude with `H.one_mem`. Consider the case `add x y _ _ hx hy => rw [kappa_add (κ := κ)]`. Conclude with `H.mul_mem (H.mul_mem hx hy) (step2 x y)`. Consider the case `neg x _ hx => rw [hn]`.

Conclude with `hx`.
-/
theorem mem_closure_of_gen (hn : ∀ a, κ (-a) = κ a)
    (hc : ∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b))
    {J : Type*} (e : J → X) (he : AddSubgroup.closure (Set.range e) = ⊤) (a : X) :
    κ a ∈ Subgroup.closure (Set.range (Sum.elim (fun i => κ (e i)) (fun p : J × J => κ (e p.1 + e p.2)))) := by
  set H := Subgroup.closure (Set.range (Sum.elim (fun i => κ (e i)) (fun p : J × J => κ (e p.1 + e p.2))))
  have hk : ∀ i, κ (e i) ∈ H := fun i => Subgroup.subset_closure ⟨Sum.inl i, rfl⟩
  have hg : ∀ i j, defect κ (e i) (e j) ∈ H := fun i j =>
    H.div_mem (Subgroup.subset_closure ⟨Sum.inr (i, j), rfl⟩) (H.mul_mem (hk i) (hk j))
  have mem : ∀ x : X, x ∈ AddSubgroup.closure (Set.range e) := fun x => he ▸ AddSubgroup.mem_top x
  have step1 : ∀ i b, defect κ (e i) b ∈ H := by
    intro i b
    induction mem b using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hg i j
    | zero => rw [defect_comm, defect_zero_left hc]; exact H.one_mem
    | add x y _ _ hx hy =>
      rw [defect_comm, defect_add_left hc, defect_comm x, defect_comm y]; exact H.mul_mem hx hy
    | neg x _ hx => rw [defect_comm, defect_neg_left hc, defect_comm]; exact H.inv_mem hx
  have step2 : ∀ a b, defect κ a b ∈ H := by
    intro a b
    induction mem a using AddSubgroup.closure_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact step1 j b
    | zero => rw [defect_zero_left hc]; exact H.one_mem
    | add x y _ _ hx hy => rw [defect_add_left hc]; exact H.mul_mem hx hy
    | neg x _ hx => rw [defect_neg_left hc]; exact H.inv_mem hx
  induction mem a using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hk j
  | zero => rw [kappa_zero hc]; exact H.one_mem
  | add x y _ _ hx hy => rw [kappa_add (κ := κ)]; exact H.mul_mem (H.mul_mem hx hy) (step2 x y)
  | neg x _ hx => rw [hn]; exact hx

end Cl

/- English proof (translation)
Introduce `R _ _ _ _ _ X _ _ κ hneg hcube hm n`. Take `⟨S, hS⟩` from `(Module.Finite.fg_top (R := ℤ) (M := X))`. Establish `hcl : AddSubgroup.closure (Set.range (fun x : S => (x : X))) = ⊤`. Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure, Subtype.range_coe_subtype, Finset.setOf_mem, hS]`. Both sides reduce to the same expression.

Establish `hΓ` using `mem_closure_of_gen hneg hcube (fun x : S => (x : X)) hcl`. Use `set gg := Sum.elim (fun i : S => κ (i : X)) (fun p : S × S => κ ((p.1 : X) + p.2))`. Use `set Γ := Subgroup.closure (Set.range gg)`. Take `⟨s, v, hv1, hv2⟩` from `GlobalTheory.T.exists_heightOne_valuations_control_subgroup R (S ⊕ (S × S)) gg`. Use `set K := FractionRing R`.

Set `w : Kˣ → Fin s → ℤ` to `fun x i => Multiplicative.toAdd (v i x)`. Establish `wmul : ∀ x y i, w (x * y) i = w x i + w y i` using `fun x y i => by simp [w]`. Establish `winv : ∀ x i, w x⁻¹ i = - w x i` using `fun x i => by simp [w]`. Establish `wone : ∀ i, w 1 i = 0` using `fun i => by simp [w]`. Establish `hk0` using `kappa_zero hcube`.

Establish `wκ : ∀ a i, 0 ≤ w (κ a) i`. Introduce `a i`. Distinguish the cases in `ha : a = 0`. Rewrite using `[ha, hk0, wone]`. Take `⟨t, -, ht⟩` from `hm a ha`.

Conclude with `hv1 i (κ a) t ht`. Establish `unitOf : ∀ x ∈ Γ, (∀ i, w x i = 0) → ∃ r : R, IsUnit r ∧ (x : K) = algebraMap R K r`. Introduce `x hx h0`. Take `⟨r, hr⟩` from `hv2 x hx (fun i => (h0 i).ge)`. Take `⟨r', hr'⟩` from `hv2 x⁻¹ (Γ.inv_mem hx) (fun i => show 0 ≤ w x⁻¹ i by rw [winv, h0 i, neg_zero])`.

Establish `hrr : r * r' = 1` using `IsFractionRing.injective R K (by`. Rewrite using `[map_mul, ← hr, ← hr', map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])`. Conclude with `⟨r, ⟨Units.mkOfMulEqOne r r' hrr, rfl⟩, hr⟩`. Set `q : X → ℤ` to `fun a => ∑ i, w (κ a) i`. Establish `hqneg : ∀ a, q (-a) = q a` using `fun a => by simp only [q, hneg]`.

Establish `hqcube : ∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b)`. Introduce `a a' b`. Establish `h` using `congrArg (fun x => ∑ i, w x i) (hcube a a' b)`. Simplify using `only [wmul, Finset.sum_add_distrib] at h`. Simplify `h` using `only [q]`.

Establish `hqpos : ∀ a, a ≠ 0 → 1 ≤ q a`. Introduce `a ha`. Take `⟨t, htm, ht⟩` from `hm a ha`. Assume the negation of the conclusion as `hlt`. Establish `hsum0 : q a = 0` using `le_antisymm (by omega) (Finset.sum_nonneg fun i _ => wκ a i)`.

Establish `hall : ∀ i, w (κ a) i = 0` using `fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => wκ a i)).mp hsum0 i (Finset.mem_univ i)`. Take `⟨r, hru, hr⟩` from `unitOf (κ a) (hΓ a) hall`. Establish `: t = r` using `IsFractionRing.injective R K (ht.symm.trans hr)`. Conclude with `(IsLocalRing.mem_maximalIdeal t).mp htm (this ▸ hru)`. Set `P` to `{x : Kˣ // x ∈ Γ ∧ (∀ i, 0 ≤ w x i) ∧ 0 < ∑ i, w x i}`.

Take `⟨F, hF⟩` from `dickson_fin s (fun x : P => fun i => (w x.1 i).toNat)`. Use `set C : ℤ := 1 + ∑ j ∈ F, ∑ i, w j.1 i`. Establish `hC : ∀ j ∈ F, ∑ i, w j.1 i + 1 ≤ C`. Introduce `j hj`. Use `Finset.single_le_sum (f := fun j : P => ∑ i, w j.1 i) (fun j _ => Finset.sum_nonneg fun i _ => j.2.2.1 i) hj` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hC1 : 1 ≤ C`. Use `Finset.sum_nonneg (s := F) (f := fun j : P => ∑ i, w j.1 i) (fun j _ => Finset.sum_nonneg fun i _ => j.2.2.1 i)` as an intermediate fact. Simplify using `only [C]`. Use linear arithmetic over natural numbers and integers.

Establish `hPm : ∀ j : P, ∃ t ∈ maximalIdeal R, (j.1 : K) = algebraMap R K t`. Introduce `j`. Take `⟨t, ht⟩` from `hv2 j.1 j.2.1 j.2.2.1`. Use `⟨t, ?_, ht⟩` and prove the remaining obligations. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Introduce `hu`. Take `⟨u, rfl⟩` from `hu`. Establish `hinv : ((j.1⁻¹ : Kˣ) : K) = algebraMap R K (u⁻¹ : Rˣ)`. Rewrite using `[Units.val_inv_eq_inv_val, ht]`. Use `symm`.

Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Establish `hle : ∀ i, w j.1 i ≤ 0` using `fun i => by`. Use `hv1 i j.1⁻¹ _ hinv` as an intermediate fact. Establish `h2` using `winv j.1 i`.

Simplify using `only [w] at h2 ⊢`. Use linear arithmetic over natural numbers and integers. Use `j.2.2.2` as an intermediate fact. Use `Finset.sum_nonpos (s := Finset.univ) (fun i _ => hle i)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `key : ∀ k : ℕ, ∀ x ∈ Γ, (∀ i, 0 ≤ w x i) → C * k ≤ ∑ i, w x i → ∃ t ∈ maximalIdeal R ^ k, (x : K) = algebraMap R K t`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `x hx h0 _`.

Take `⟨t, ht⟩` from `hv2 x hx h0`. Conclude with `⟨t, by simp, ht⟩`. Consider the case `succ k ih`. Introduce `x hx h0 hsum`. Establish `hpos : 0 < ∑ i, w x i` using `by push_cast at hsum; nlinarith`.

Take `⟨j, hjF, hjle⟩` from `hF ⟨x, hx, h0, hpos⟩`. Establish `hle : ∀ i, w j.1 i ≤ w x i`. Introduce `i`. Establish `h1` using `hjle i`. Establish `h2` using `j.2.2.1 i`.

Establish `h3` using `h0 i`. Simplify using `only at h1`. Use linear arithmetic over natural numbers and integers. Establish `hjC` using `hC j hjF`. Take `⟨t', ht'm, ht'⟩` from `ih (x * j.1⁻¹) (Γ.mul_mem hx (Γ.inv_mem j.2.1)) (fun i => by rw [wmul, winv]; linarith [hle i]) (by`.

Simplify using `only [wmul, winv, Finset.sum_add_distrib, Finset.sum_neg_distrib]`. Move the coercions through the operations in `at hsum ⊢`. Use the proof step `nlinarith)`. Take `⟨t, htm, ht⟩` from `hPm j`. Use `⟨t' * t, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul ht'm htm`. Rewrite using `[map_mul, ← ht', ← ht, ← Units.val_mul, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]`. Apply `(GlobalTheory.T.finite_sublevel_of_int_quadratic_ge_one X q hqneg hqcube hqpos (C * n)).subset` to reduce the goal to its premises. Introduce `a ha`.

Assume the negation of the conclusion as `hlt`. Conclude with `ha (key n (κ a) (hΓ a) (wκ a) (le_of_lt (not_le.mp hlt)))`.
-/
theorem finite_not_mem_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ n : ℕ, {a | ¬ ∃ s ∈ maximalIdeal R ^ n, (κ a : FractionRing R) = algebraMap R _ s}.Finite := by
  intro R _ _ _ _ _ X _ _ κ hneg hcube hm n
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top (R := ℤ) (M := X))
  have hcl : AddSubgroup.closure (Set.range (fun x : S => (x : X))) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Subtype.range_coe_subtype, Finset.setOf_mem, hS]; rfl
  have hΓ := mem_closure_of_gen hneg hcube (fun x : S => (x : X)) hcl
  set gg := Sum.elim (fun i : S => κ (i : X)) (fun p : S × S => κ ((p.1 : X) + p.2))
  set Γ := Subgroup.closure (Set.range gg)
  obtain ⟨s, v, hv1, hv2⟩ := GlobalTheory.T.exists_heightOne_valuations_control_subgroup R (S ⊕ (S × S)) gg
  set K := FractionRing R
  let w : Kˣ → Fin s → ℤ := fun x i => Multiplicative.toAdd (v i x)
  have wmul : ∀ x y i, w (x * y) i = w x i + w y i := fun x y i => by simp [w]
  have winv : ∀ x i, w x⁻¹ i = - w x i := fun x i => by simp [w]
  have wone : ∀ i, w 1 i = 0 := fun i => by simp [w]
  have hk0 := kappa_zero hcube
  have wκ : ∀ a i, 0 ≤ w (κ a) i := by
    intro a i
    by_cases ha : a = 0
    · rw [ha, hk0, wone]
    · obtain ⟨t, -, ht⟩ := hm a ha
      exact hv1 i (κ a) t ht

  have unitOf : ∀ x ∈ Γ, (∀ i, w x i = 0) → ∃ r : R, IsUnit r ∧ (x : K) = algebraMap R K r := by
    intro x hx h0
    obtain ⟨r, hr⟩ := hv2 x hx (fun i => (h0 i).ge)
    obtain ⟨r', hr'⟩ := hv2 x⁻¹ (Γ.inv_mem hx) (fun i => show 0 ≤ w x⁻¹ i by rw [winv, h0 i, neg_zero])
    have hrr : r * r' = 1 := IsFractionRing.injective R K (by
      rw [map_mul, ← hr, ← hr', map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    exact ⟨r, ⟨Units.mkOfMulEqOne r r' hrr, rfl⟩, hr⟩
  let q : X → ℤ := fun a => ∑ i, w (κ a) i
  have hqneg : ∀ a, q (-a) = q a := fun a => by simp only [q, hneg]
  have hqcube : ∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b) := by
    intro a a' b
    have h := congrArg (fun x => ∑ i, w x i) (hcube a a' b)
    simp only [wmul, Finset.sum_add_distrib] at h
    simpa only [q] using h
  have hqpos : ∀ a, a ≠ 0 → 1 ≤ q a := by
    intro a ha
    obtain ⟨t, htm, ht⟩ := hm a ha
    by_contra hlt
    have hsum0 : q a = 0 := le_antisymm (by omega) (Finset.sum_nonneg fun i _ => wκ a i)
    have hall : ∀ i, w (κ a) i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => wκ a i)).mp hsum0 i (Finset.mem_univ i)
    obtain ⟨r, hru, hr⟩ := unitOf (κ a) (hΓ a) hall
    have : t = r := IsFractionRing.injective R K (ht.symm.trans hr)
    exact (IsLocalRing.mem_maximalIdeal t).mp htm (this ▸ hru)

  let P := {x : Kˣ // x ∈ Γ ∧ (∀ i, 0 ≤ w x i) ∧ 0 < ∑ i, w x i}
  obtain ⟨F, hF⟩ := dickson_fin s (fun x : P => fun i => (w x.1 i).toNat)
  set C : ℤ := 1 + ∑ j ∈ F, ∑ i, w j.1 i
  have hC : ∀ j ∈ F, ∑ i, w j.1 i + 1 ≤ C := by
    intro j hj
    have := Finset.single_le_sum (f := fun j : P => ∑ i, w j.1 i)
      (fun j _ => Finset.sum_nonneg fun i _ => j.2.2.1 i) hj
    omega
  have hC1 : 1 ≤ C := by
    have := Finset.sum_nonneg (s := F) (f := fun j : P => ∑ i, w j.1 i) (fun j _ => Finset.sum_nonneg fun i _ => j.2.2.1 i)
    simp only [C]; omega
  have hPm : ∀ j : P, ∃ t ∈ maximalIdeal R, (j.1 : K) = algebraMap R K t := by
    intro j
    obtain ⟨t, ht⟩ := hv2 j.1 j.2.1 j.2.2.1
    refine ⟨t, ?_, ht⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, rfl⟩ := hu
    have hinv : ((j.1⁻¹ : Kˣ) : K) = algebraMap R K (u⁻¹ : Rˣ) := by
      rw [Units.val_inv_eq_inv_val, ht]; symm; apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    have hle : ∀ i, w j.1 i ≤ 0 := fun i => by
      have := hv1 i j.1⁻¹ _ hinv
      have h2 := winv j.1 i
      simp only [w] at h2 ⊢; omega
    have := j.2.2.2
    have := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hle i)
    omega
  have key : ∀ k : ℕ, ∀ x ∈ Γ, (∀ i, 0 ≤ w x i) → C * k ≤ ∑ i, w x i →
      ∃ t ∈ maximalIdeal R ^ k, (x : K) = algebraMap R K t := by
    intro k
    induction k with
    | zero =>
      intro x hx h0 _
      obtain ⟨t, ht⟩ := hv2 x hx h0
      exact ⟨t, by simp, ht⟩
    | succ k ih =>
      intro x hx h0 hsum
      have hpos : 0 < ∑ i, w x i := by push_cast at hsum; nlinarith
      obtain ⟨j, hjF, hjle⟩ := hF ⟨x, hx, h0, hpos⟩
      have hle : ∀ i, w j.1 i ≤ w x i := by
        intro i
        have h1 := hjle i
        have h2 := j.2.2.1 i
        have h3 := h0 i
        simp only at h1
        omega
      have hjC := hC j hjF
      obtain ⟨t', ht'm, ht'⟩ := ih (x * j.1⁻¹) (Γ.mul_mem hx (Γ.inv_mem j.2.1))
        (fun i => by rw [wmul, winv]; linarith [hle i])
        (by
          simp only [wmul, winv, Finset.sum_add_distrib, Finset.sum_neg_distrib]
          push_cast at hsum ⊢
          nlinarith)
      obtain ⟨t, htm, ht⟩ := hPm j
      refine ⟨t' * t, ?_, ?_⟩
      · rw [pow_succ]; exact Ideal.mul_mem_mul ht'm htm
      · rw [map_mul, ← ht', ← ht, ← Units.val_mul, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
  apply (GlobalTheory.T.finite_sublevel_of_int_quadratic_ge_one X q hqneg hqcube hqpos (C * n)).subset
  intro a ha
  by_contra hlt
  exact ha (key n (κ a) (hΓ a) (wκ a) (le_of_lt (not_le.mp hlt)))

end GlobalTheory.QuadTend
