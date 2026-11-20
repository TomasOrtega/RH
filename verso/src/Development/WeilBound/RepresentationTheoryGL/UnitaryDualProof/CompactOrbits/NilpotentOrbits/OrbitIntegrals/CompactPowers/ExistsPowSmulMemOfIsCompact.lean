import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
import GroundTheory.AutomorphicForms.GLnLocal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisExtra

noncomputable section

open Matrix ValuativeRel Topology Filter Set

namespace PositivityTheory.RgUd.T.Nil.Orb.Ozn

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb GroundTheory.Automorphic.GLnLocal

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def ball (n : ℕ) (γ : ValueGroupWithZero k) : Set (Matrix (Fin n) (Fin n) k) :=
  {M | ∀ i j, valuation k (M i j) ≤ γ}

/- English proof (translation)
Establish `h : ball (k` using `k) n γ = Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin n => {x : k | valuation k x ≤ γ})) := by`. Use extensionality with `M`. Conclude with `⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩`. Rewrite using `[h]`. Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ`.
-/
theorem isCompact_ball (γ : ValueGroupWithZero k) : IsCompact (ball (k := k) n γ) := by
  have h : ball (k := k) n γ =
      Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin n => {x : k | valuation k x ≤ γ})) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [h]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    IsNonarchimedeanLocalField.isCompact_closedBall k γ

/- English proof (translation)
The claim follows from `(continuous_apply j).comp (continuous_apply i)`.
-/
theorem continuous_entry' (i j : Fin n) : Continuous fun M : Matrix (Fin n) (Fin n) k => M i j :=
  (continuous_apply j).comp (continuous_apply i)

/- English proof (translation)
Establish `h : ball (k` using `k) n γ = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) k => M i j) ⁻¹' {x : k | valuation k x ≤ γ} := by`. Use extensionality with `M`. Simplify using `[ball]`. Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_valuation_le k hγ).preimage (continuous_entry' i j)`.
-/
theorem isOpen_ball {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) : IsOpen (ball (k := k) n γ) := by
  have h : ball (k := k) n γ =
      ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) k => M i j) ⁻¹' {x : k | valuation k x ≤ γ} := by
    ext M; simp [ball]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_valuation_le k hγ).preimage (continuous_entry' i j)

/- English proof (translation)
Introduce `i j` and use `(Valuation.map_add _ _ _).trans (max_le (h i j) (h' i j))`.
-/
theorem add_mem_ball {γ : ValueGroupWithZero k} {M M' : Matrix (Fin n) (Fin n) k} (h : M ∈ ball n γ)
    (h' : M' ∈ ball n γ) : M + M' ∈ ball n γ :=
  fun i j => (Valuation.map_add _ _ _).trans (max_le (h i j) (h' i j))

/- English proof (translation)
Introduce `i j` and use `by simpa [Valuation.map_neg] using h i j`.
-/
theorem neg_mem_ball {γ : ValueGroupWithZero k} {M : Matrix (Fin n) (Fin n) k} (h : M ∈ ball n γ) :
    -M ∈ ball n γ :=
  fun i j => by simpa [Valuation.map_neg] using h i j

/- English proof (translation)
Introduce `_ h i j` and use `(h i j).trans hγ`.
-/
theorem ball_mono {γ γ' : ValueGroupWithZero k} (hγ : γ ≤ γ') : ball (k := k) n γ ⊆ ball n γ' :=
  fun _ h i j => (h i j).trans hγ

/- English proof (translation)
Introduce `i j` and use `by simp only [Matrix.smul_apply, smul_eq_mul, map_mul] exact mul_le_mul_right (h i j) _`.
-/
theorem smul_mem_ball (a : k) {γ : ValueGroupWithZero k} {M : Matrix (Fin n) (Fin n) k} (h : M ∈ ball n γ) :
    a • M ∈ ball n (valuation k a * γ) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_mul_right (h i j) _

abbrev ϖ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : k :=
  (uniformizer k : k)

/- English proof (translation)
The claim follows from `valuation_uniformizer_lt_one k`.
-/
theorem q_lt_one : valuation k (ϖ k) < 1 := valuation_uniformizer_lt_one k

/- English proof (translation)
The claim follows from `valuation_uniformizer_ne_zero k`.
-/
theorem q_ne_zero : valuation k (ϖ k) ≠ 0 := valuation_uniformizer_ne_zero k

/- English proof (translation)
The claim follows from `(Valuation.ne_zero_iff _).1 q_ne_zero`.
-/
theorem ϖ_ne_zero : ϖ k ≠ 0 := (Valuation.ne_zero_iff _).1 q_ne_zero

/- English proof (translation)
The claim follows from `pow_le_pow_right_of_le_one' q_lt_one.le h`.
-/
theorem q_pow_anti {a b : ℕ} (h : a ≤ b) : valuation k (ϖ k) ^ b ≤ valuation k (ϖ k) ^ a :=
  pow_le_pow_right_of_le_one' q_lt_one.le h

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by simp [hx]⟩`. Establish `hx' : valuation k x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Take `⟨j, hj⟩` from `exists_pow_lt₀ (q_lt_one (k := k)) (Units.mk0 (valuation k x)⁻¹ (inv_ne_zero hx'))`. Use `⟨j, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_pow_le_one (x : k) : ∃ j : ℕ, valuation k (ϖ k) ^ j * valuation k x ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hx' : valuation k x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  obtain ⟨j, hj⟩ := exists_pow_lt₀ (q_lt_one (k := k)) (Units.mk0 (valuation k x)⁻¹ (inv_ne_zero hx'))
  refine ⟨j, ?_⟩
  calc valuation k (ϖ k) ^ j * valuation k x ≤ (valuation k x)⁻¹ * valuation k x :=
        mul_le_mul_left (by simpa using hj.le) _
    _ = 1 := inv_mul_cancel₀ hx'

/- English proof (translation)
Use `choose f hf using fun p : Fin n × Fin n => exists_pow_le_one (M p.1 p.2)`. Use `⟨Finset.univ.sup f, fun i j => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]`. Conclude with `(mul_le_mul_left (q_pow_anti (Finset.le_sup (f := f) (Finset.mem_univ (i, j)))) _).trans (hf (i, j))`.
-/
theorem exists_pow_smul_mem (M : Matrix (Fin n) (Fin n) k) : ∃ j : ℕ, (ϖ k ^ j) • M ∈ ball n 1 := by
  choose f hf using fun p : Fin n × Fin n => exists_pow_le_one (M p.1 p.2)
  refine ⟨Finset.univ.sup f, fun i j => ?_⟩
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
  exact (mul_le_mul_left (q_pow_anti (Finset.le_sup (f := f) (Finset.mem_univ (i, j)))) _).trans (hf (i, j))

/- English proof (translation)
Establish `e : (ϖ k ^ b) • M = (ϖ k ^ (b - a)) • ((ϖ k ^ a) • M)`. Rewrite using `[smul_smul, ← pow_add, Nat.sub_add_cancel hab]`. Rewrite using `[e]`. Use `ball_mono ?_ (smul_mem_ball _ h)` and prove the remaining obligations. Rewrite using `[map_pow, mul_one]`.

Conclude with `pow_le_one₀ zero_le q_lt_one.le`.
-/
theorem pow_smul_mem_mono {M : Matrix (Fin n) (Fin n) k} {a b : ℕ} (hab : a ≤ b) (h : (ϖ k ^ a) • M ∈ ball n 1) :
    (ϖ k ^ b) • M ∈ ball n 1 := by
  have e : (ϖ k ^ b) • M = (ϖ k ^ (b - a)) • ((ϖ k ^ a) • M) := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hab]
  rw [e]
  refine ball_mono ?_ (smul_mem_ball _ h)
  rw [map_pow, mul_one]
  exact pow_le_one₀ zero_le q_lt_one.le

/- English proof (translation)
Establish `hU : ∀ j : ℕ, IsOpen {M : Matrix (Fin n) (Fin n) k | (ϖ k ^ j) • M ∈ ball n 1}` using `fun j => (isOpen_ball one_ne_zero).preimage (continuous_const_smul _)`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun j : ℕ => {M : Matrix (Fin n) (Fin n) k | (ϖ k ^ j) • M ∈ ball n 1}) hU fun M _ => Set.mem_iUnion.2 (exists_pow_smul_mem M)`. Use `⟨t.sup id, fun M hM => ?_⟩` and prove the remaining obligations. Take `⟨j, hj, hMj⟩` from `Set.mem_iUnion₂.1 (ht hM)`. Conclude with `pow_smul_mem_mono (Finset.le_sup (f := id) hj) hMj`.
-/
theorem exists_pow_smul_mem_of_isCompact {K : Set (Matrix (Fin n) (Fin n) k)} (hK : IsCompact K) :
    ∃ j : ℕ, ∀ M ∈ K, (ϖ k ^ j) • M ∈ ball n 1 := by
  have hU : ∀ j : ℕ, IsOpen {M : Matrix (Fin n) (Fin n) k | (ϖ k ^ j) • M ∈ ball n 1} := fun j =>
    (isOpen_ball one_ne_zero).preimage (continuous_const_smul _)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun j : ℕ => {M : Matrix (Fin n) (Fin n) k | (ϖ k ^ j) • M ∈ ball n 1})
    hU fun M _ => Set.mem_iUnion.2 (exists_pow_smul_mem M)
  refine ⟨t.sup id, fun M hM => ?_⟩
  obtain ⟨j, hj, hMj⟩ := Set.mem_iUnion₂.1 (ht hM)
  exact pow_smul_mem_mono (Finset.le_sup (f := id) hj) hMj

/- English proof (translation)
Use `⟨fun h => ?_, fun h => ⟨n, h⟩⟩` and prove the remaining obligations. Establish `h1` using `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h`. Establish `h2 : M.charpoly = Polynomial.X ^ Fintype.card (Fin n)` using `sub_eq_zero.1 h1.eq_zero`. Establish `h3` using `Matrix.aeval_self_charpoly M`. Rewrite `h3` using `[h2]`.

Simplify using `using h3`.
-/
theorem isNilpotent_iff_pow (M : Matrix (Fin n) (Fin n) k) : IsNilpotent M ↔ M ^ n = 0 := by
  refine ⟨fun h => ?_, fun h => ⟨n, h⟩⟩
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have h2 : M.charpoly = Polynomial.X ^ Fintype.card (Fin n) := sub_eq_zero.1 h1.eq_zero
  have h3 := Matrix.aeval_self_charpoly M
  rw [h2] at h3
  simpa using h3

/- English proof (translation)
Establish `e : {M : Matrix (Fin n) (Fin n) k | IsNilpotent M} = (fun M => M ^ n) ⁻¹' {0}`. Use extensionality with `M`. Simplify using `[isNilpotent_iff_pow]`. Rewrite using `[e]`. Conclude with `isClosed_singleton.preimage (continuous_pow n)`.
-/
theorem isClosed_nilpotent : IsClosed {M : Matrix (Fin n) (Fin n) k | IsNilpotent M} := by
  have e : {M : Matrix (Fin n) (Fin n) k | IsNilpotent M} = (fun M => M ^ n) ⁻¹' {0} := by
    ext M; simp [isNilpotent_iff_pow]
  rw [e]
  exact isClosed_singleton.preimage (continuous_pow n)

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DYlb5.main f`.
-/
theorem continuous_dual (f : Module.Dual k (Matrix (Fin n) (Fin n) k)) : Continuous f :=
  _root_.UpperTheory.Reformulated.B.DYlb5.main f

/- English proof (translation)
Rewrite using `[← isOpen_compl_iff, isOpen_iff_forall_mem_open]`. Introduce `x hx`. Take `⟨f, hfx, hf⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem (p := Subalgebra.toSubmodule Z) hx inferInstance`. Use `⟨{y | f y ≠ 0}, fun y hy hyZ => hy ?_, isOpen_ne_fun (continuous_dual f) continuous_const, hfx⟩` and prove the remaining obligations. Establish `: f y ∈ (Subalgebra.toSubmodule Z).map f` using `⟨y, hyZ, rfl⟩`.

Rewrite `this` using `[hf]`. Simplify using `using this`.
-/
theorem isClosed_subalgebra (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) :
    IsClosed (Z : Set (Matrix (Fin n) (Fin n) k)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := Subalgebra.toSubmodule Z) hx inferInstance
  refine ⟨{y | f y ≠ 0}, fun y hy hyZ => hy ?_, isOpen_ne_fun (continuous_dual f) continuous_const, hfx⟩
  have : f y ∈ (Subalgebra.toSubmodule Z).map f := ⟨y, hyZ, rfl⟩
  rw [hf] at this
  simpa using this

/- English proof (translation)
Use `haveI := hZ.2`. Take `⟨m, hm⟩` from `h`. Establish `h' : IsNilpotent (⟨c, hc⟩ : Z)` using `⟨m, Subtype.ext (by simpa using hm)⟩`. Simplify using `using congrArg Subtype.val h'.eq_zero`.
-/
theorem eq_zero_of_mem_of_isNilpotent {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (h : IsNilpotent c) : c = 0 := by
  haveI := hZ.2
  obtain ⟨m, hm⟩ := h
  have h' : IsNilpotent (⟨c, hc⟩ : Z) := ⟨m, Subtype.ext (by simpa using hm)⟩
  simpa using congrArg Subtype.val h'.eq_zero

/- English proof (translation)
Use `set S : Set (Matrix (Fin n) (Fin n) k) := (Z : Set _) ∩ ball n 1 ∩ (ball n (valuation k (ϖ k)))ᶜ with hS`. Establish `hSc : IsCompact S` using `(isCompact_ball 1).inter_left (isClosed_subalgebra Z) |>.inter_right (isOpen_ball q_ne_zero).isClosed_compl`. Establish `hloc : ∀ s ∈ S, ∃ J : ℕ, ∀ w ∈ ball n (valuation k (ϖ k) ^ J), ¬ IsNilpotent (s + w)`. Introduce `s hs`. Establish `hsN : ¬ IsNilpotent s` using `fun h => hs.2 (by rw [eq_zero_of_mem_of_isNilpotent hZ hs.1.1 h]; exact fun i j => by simp)`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `C : ℕ → Set (Matrix (Fin n) (Fin n) k)` to `fun J => {M | M - s ∈ ball n (valuation k (ϖ k) ^ J)} ∩ {M | IsNilpotent M}`. Establish `hCc : ∀ J, IsClosed (C J)` using `fun J => ((isCompact_ball _).isClosed.preimage (continuous_id.sub continuous_const)).inter isClosed_nilpotent`. Establish `hC0 : IsCompact (C 0)`.

Establish `h1 : IsCompact ((fun w => w + s) '' ball n (valuation k (ϖ k) ^ 0))` using `(isCompact_ball _).image (continuous_id.add continuous_const)`. Use `h1.of_isClosed_subset (hCc 0) fun M hM => ⟨M - s, hM.1, by simp⟩` and prove the remaining obligations. Establish `hCd : ∀ J, C (J + 1) ⊆ C J` using `fun J M hM => ⟨ball_mono (q_pow_anti (Nat.le_succ J)) hM.1, hM.2⟩`. Establish `hCn : ∀ J, (C J).Nonempty` using `fun J => by`. Take `⟨w, hw, hnil⟩` from `hcon J`.

Conclude with `⟨s + w, by simpa using hw, hnil⟩`. Take `⟨M, hM⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCd hCn hC0 hCc`. Establish `hMs : M - s = 0`. Use extensionality with `i j`. Conclude with `eq_zero_of_forall_valuation_le k fun J => (Set.mem_iInter.1 hM J).1 i j`.

Establish `hMeq : M = s` using `sub_eq_zero.1 hMs`. Conclude with `hsN (hMeq ▸ (Set.mem_iInter.1 hM 0).2)`. Use `choose! Js hJs using hloc`. Establish `hopen : ∀ s ∈ S, IsOpen ((fun w => s + w) '' ball n (valuation k (ϖ k) ^ Js s))` using `fun s _ => (Homeomorph.addLeft s).isOpenMap _ (isOpen_ball (pow_ne_zero _ q_ne_zero))`. Take `⟨t, ht⟩` from `hSc.elim_nhds_subcover' (fun s hs => (fun w => s + w) '' ball n (valuation k (ϖ k) ^ Js s)) fun s hs => (hopen s hs).mem_nhds ⟨0, fun i j => by simp, by simp⟩`.

Use `⟨t.sup (fun s : S => Js s), fun s hsZ hs1 hsq w hw hnil => ?_⟩` and prove the remaining obligations. Establish `hsS : s ∈ S` using `⟨⟨hsZ, hs1⟩, hsq⟩`. Take `⟨⟨s', hs'⟩, hmem, hss'⟩` from `Set.mem_iUnion₂.1 (ht hsS)`. Take `⟨u, hu, rfl⟩` from `hss'`. Establish `hw' : w ∈ ball n (valuation k (ϖ k) ^ Js s')` using `ball_mono (q_pow_anti (Finset.le_sup (f := fun s : S => Js s) hmem)) hw`.

Conclude with `hJs s' hs' (u + w) (add_mem_ball hu hw') (by simpa [add_assoc] using hnil)`.
-/
theorem exists_sep {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) : ∃ J : ℕ,
    ∀ s ∈ (Z : Set (Matrix (Fin n) (Fin n) k)), s ∈ ball n 1 → s ∉ ball n (valuation k (ϖ k)) →
      ∀ w ∈ ball n (valuation k (ϖ k) ^ J), ¬ IsNilpotent (s + w) := by
  set S : Set (Matrix (Fin n) (Fin n) k) := (Z : Set _) ∩ ball n 1 ∩ (ball n (valuation k (ϖ k)))ᶜ with hS
  have hSc : IsCompact S :=
    (isCompact_ball 1).inter_left (isClosed_subalgebra Z) |>.inter_right (isOpen_ball q_ne_zero).isClosed_compl
  have hloc : ∀ s ∈ S, ∃ J : ℕ, ∀ w ∈ ball n (valuation k (ϖ k) ^ J), ¬ IsNilpotent (s + w) := by
    intro s hs
    have hsN : ¬ IsNilpotent s := fun h =>
      hs.2 (by rw [eq_zero_of_mem_of_isNilpotent hZ hs.1.1 h]; exact fun i j => by simp)
    by_contra hcon
    push_neg at hcon
    let C : ℕ → Set (Matrix (Fin n) (Fin n) k) := fun J =>
      {M | M - s ∈ ball n (valuation k (ϖ k) ^ J)} ∩ {M | IsNilpotent M}
    have hCc : ∀ J, IsClosed (C J) := fun J =>
      ((isCompact_ball _).isClosed.preimage (continuous_id.sub continuous_const)).inter isClosed_nilpotent
    have hC0 : IsCompact (C 0) := by
      have h1 : IsCompact ((fun w => w + s) '' ball n (valuation k (ϖ k) ^ 0)) :=
        (isCompact_ball _).image (continuous_id.add continuous_const)
      refine h1.of_isClosed_subset (hCc 0) fun M hM => ⟨M - s, hM.1, by simp⟩
    have hCd : ∀ J, C (J + 1) ⊆ C J := fun J M hM =>
      ⟨ball_mono (q_pow_anti (Nat.le_succ J)) hM.1, hM.2⟩
    have hCn : ∀ J, (C J).Nonempty := fun J => by
      obtain ⟨w, hw, hnil⟩ := hcon J
      exact ⟨s + w, by simpa using hw, hnil⟩
    obtain ⟨M, hM⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCd hCn hC0 hCc
    have hMs : M - s = 0 := by
      ext i j
      exact eq_zero_of_forall_valuation_le k fun J => (Set.mem_iInter.1 hM J).1 i j
    have hMeq : M = s := sub_eq_zero.1 hMs
    exact hsN (hMeq ▸ (Set.mem_iInter.1 hM 0).2)
  choose! Js hJs using hloc
  have hopen : ∀ s ∈ S, IsOpen ((fun w => s + w) '' ball n (valuation k (ϖ k) ^ Js s)) := fun s _ =>
    (Homeomorph.addLeft s).isOpenMap _ (isOpen_ball (pow_ne_zero _ q_ne_zero))
  obtain ⟨t, ht⟩ := hSc.elim_nhds_subcover' (fun s hs => (fun w => s + w) '' ball n (valuation k (ϖ k) ^ Js s))
    fun s hs => (hopen s hs).mem_nhds ⟨0, fun i j => by simp, by simp⟩
  refine ⟨t.sup (fun s : S => Js s), fun s hsZ hs1 hsq w hw hnil => ?_⟩
  have hsS : s ∈ S := ⟨⟨hsZ, hs1⟩, hsq⟩
  obtain ⟨⟨s', hs'⟩, hmem, hss'⟩ := Set.mem_iUnion₂.1 (ht hsS)
  obtain ⟨u, hu, rfl⟩ := hss'
  have hw' : w ∈ ball n (valuation k (ϖ k) ^ Js s') :=
    ball_mono (q_pow_anti (Finset.le_sup (f := fun s : S => Js s) hmem)) hw
  exact hJs s' hs' (u + w) (add_mem_ball hu hw') (by simpa [add_assoc] using hnil)

/- English proof (translation)
Take `⟨j₀, hj₀⟩` from `exists_pow_smul_mem_of_isCompact hK`. Take `⟨J, hJ⟩` from `exists_sep hZ`. Use `⟨j₀ + J, fun c hc m hm hcm => ?_⟩` and prove the remaining obligations. Set `e` to `Nat.find (exists_pow_smul_mem c)`. Establish `he : (ϖ k ^ e) • c ∈ ball n 1` using `Nat.find_spec (exists_pow_smul_mem c)`.

Distinguish the cases in `hle : e ≤ j₀ + J`. Conclude with `pow_smul_mem_mono hle he`. It suffices to derive a contradiction. Use `push_neg at hle`. Take `⟨e', he'⟩ : ∃ e', e = e' + 1` from `⟨e - 1, by omega⟩`.

Establish `hmin : ¬ (ϖ k ^ e') • c ∈ ball n 1` using `Nat.find_min (exists_pow_smul_mem c) (by omega)`. Establish `hs1 : (ϖ k ^ e) • c ∈ ball n 1` using `he`. Establish `hsq : (ϖ k ^ e) • c ∉ ball n (valuation k (ϖ k))`. Introduce `h`. Apply `hmin` to reduce the goal to its premises.

Introduce `i j`. Establish `h1` using `h i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at h1 ⊢`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel_left₀ q_ne_zero]`.

Use `_ = (valuation k (ϖ k))⁻¹ * valuation k (ϖ k ^ e * c i j) := by`. Rewrite using `[he', pow_succ', mul_assoc, map_mul (valuation k) (ϖ k)]`. Use `_ ≤ (valuation k (ϖ k))⁻¹ * valuation k (ϖ k) := mul_le_mul_right h1 _`. Use `_ = 1 := inv_mul_cancel₀ q_ne_zero`. Establish `hsZ : (ϖ k ^ e) • c ∈ (Z : Set (Matrix (Fin n) (Fin n) k))` using `Z.smul_mem hc _`.

Establish `hw : (ϖ k ^ e) • (c + m) ∈ ball n (valuation k (ϖ k) ^ J)`. Establish `e1 : (ϖ k ^ e) • (c + m) = (ϖ k ^ (e - j₀)) • ((ϖ k ^ j₀) • (c + m))`. Rewrite using `[smul_smul, ← pow_add, Nat.sub_add_cancel (by omega)]`. Rewrite using `[e1]`. Use `ball_mono ?_ (smul_mem_ball _ (hj₀ _ hcm))` and prove the remaining obligations.

Rewrite using `[map_pow, mul_one]`. Conclude with `q_pow_anti (by omega)`. Apply `hJ _ hsZ hs1 hsq _ (neg_mem_ball hw)` to reduce the goal to its premises. Establish `: (ϖ k ^ e) • c + -((ϖ k ^ e) • (c + m)) = -((ϖ k ^ e) • m)`. Rewrite using `[smul_add]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `(hm.smul _).neg`.
-/
theorem exists_bound {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {K : Set (Matrix (Fin n) (Fin n) k)}
    (hK : IsCompact K) : ∃ T : ℕ, ∀ c ∈ (Z : Set (Matrix (Fin n) (Fin n) k)), ∀ m : Matrix (Fin n) (Fin n) k,
      IsNilpotent m → c + m ∈ K → (ϖ k ^ T) • c ∈ ball n 1 := by
  classical
  obtain ⟨j₀, hj₀⟩ := exists_pow_smul_mem_of_isCompact hK
  obtain ⟨J, hJ⟩ := exists_sep hZ
  refine ⟨j₀ + J, fun c hc m hm hcm => ?_⟩
  let e := Nat.find (exists_pow_smul_mem c)
  have he : (ϖ k ^ e) • c ∈ ball n 1 := Nat.find_spec (exists_pow_smul_mem c)
  by_cases hle : e ≤ j₀ + J
  · exact pow_smul_mem_mono hle he
  exfalso
  push_neg at hle
  obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hmin : ¬ (ϖ k ^ e') • c ∈ ball n 1 := Nat.find_min (exists_pow_smul_mem c) (by omega)
  have hs1 : (ϖ k ^ e) • c ∈ ball n 1 := he
  have hsq : (ϖ k ^ e) • c ∉ ball n (valuation k (ϖ k)) := by
    intro h
    apply hmin
    intro i j
    have h1 := h i j
    simp only [Matrix.smul_apply, smul_eq_mul] at h1 ⊢
    calc valuation k (ϖ k ^ e' * c i j)
        = (valuation k (ϖ k))⁻¹ * (valuation k (ϖ k) * valuation k (ϖ k ^ e' * c i j)) := by
          rw [inv_mul_cancel_left₀ q_ne_zero]
      _ = (valuation k (ϖ k))⁻¹ * valuation k (ϖ k ^ e * c i j) := by
          rw [he', pow_succ', mul_assoc, map_mul (valuation k) (ϖ k)]
      _ ≤ (valuation k (ϖ k))⁻¹ * valuation k (ϖ k) := mul_le_mul_right h1 _
      _ = 1 := inv_mul_cancel₀ q_ne_zero
  have hsZ : (ϖ k ^ e) • c ∈ (Z : Set (Matrix (Fin n) (Fin n) k)) := Z.smul_mem hc _
  have hw : (ϖ k ^ e) • (c + m) ∈ ball n (valuation k (ϖ k) ^ J) := by
    have e1 : (ϖ k ^ e) • (c + m) = (ϖ k ^ (e - j₀)) • ((ϖ k ^ j₀) • (c + m)) := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel (by omega)]
    rw [e1]
    refine ball_mono ?_ (smul_mem_ball _ (hj₀ _ hcm))
    rw [map_pow, mul_one]
    exact q_pow_anti (by omega)
  apply hJ _ hsZ hs1 hsq _ (neg_mem_ball hw)
  have : (ϖ k ^ e) • c + -((ϖ k ^ e) • (c + m)) = -((ϖ k ^ e) • m) := by
    rw [smul_add]; abel
  rw [this]
  exact (hm.smul _).neg

/- English proof (translation)
Take `⟨T, hT⟩` from `exists_bound hZ hK`. Use `set CZ : Set (Matrix (Fin n) (Fin n) k) := (Z : Set (Matrix (Fin n) (Fin n) k)) ∩ (fun c => (ϖ k ^ T) • c) ⁻¹' ball n 1 with hCZdef`. Establish `hCZ : IsCompact CZ`. Establish `h1 : IsCompact ((fun c : Matrix (Fin n) (Fin n) k => (ϖ k ^ T) • c) ⁻¹' ball n 1)` using `(Homeomorph.smulOfNeZero (ϖ k ^ T) (pow_ne_zero _ ϖ_ne_zero)).isCompact_preimage.2 (isCompact_ball 1)`. Conclude with `h1.inter_left (isClosed_subalgebra Z)`.

Set `A : Set (Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k)` to `{p | p.1 ∈ (Z : Set (Matrix (Fin n) (Fin n) k)) ∧ IsNilpotent p.2 ∧ p.1 + p.2 ∈ K}`. Establish `hAsub : A ⊆ CZ ×ˢ ((fun p : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k => p.1 - p.2) '' (K ×ˢ CZ))`. Introduce and unpack `⟨c, m⟩ ⟨hc, hm, hcm⟩`. Establish `hcz : c ∈ CZ` using `⟨hc, hT c hc m hm hcm⟩`. Conclude with `⟨hcz, ⟨(c + m, c), ⟨hcm, hcz⟩, by simp⟩⟩`.

Establish `hAc : IsClosed A` using `((isClosed_subalgebra Z).preimage continuous_fst).inter ((isClosed_nilpotent.preimage continuous_snd).inter (hK.isClosed.preimage (continuous_fst.add continuous_snd)))`. Establish `hA : IsCompact A` using `(hCZ.prod ((hK.prod hCZ).image (continuous_fst.sub continuous_snd))).of_isClosed_subset hAc hAsub`. Establish `e : ZN Z ∩ K = (fun p : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k => p.1 + p.2) '' A`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨c, hc, hxc⟩, hxK⟩`. Conclude with `⟨(c, x - c), ⟨hc, hxc, by simpa using hxK⟩, by simp⟩`. Introduce and unpack `⟨⟨c, m⟩, ⟨hc, hm, hcm⟩, rfl⟩`. Conclude with `⟨⟨c, hc, by simpa using hm⟩, hcm⟩`. Rewrite using `[e]`.

Conclude with `hA.image (continuous_fst.add continuous_snd)`.
-/
theorem isCompact_inter {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    {K : Set (Matrix (Fin n) (Fin n) k)} (hK : IsCompact K) : IsCompact (ZN Z ∩ K) := by
  obtain ⟨T, hT⟩ := exists_bound hZ hK
  set CZ : Set (Matrix (Fin n) (Fin n) k) :=
    (Z : Set (Matrix (Fin n) (Fin n) k)) ∩ (fun c => (ϖ k ^ T) • c) ⁻¹' ball n 1 with hCZdef
  have hCZ : IsCompact CZ := by
    have h1 : IsCompact ((fun c : Matrix (Fin n) (Fin n) k => (ϖ k ^ T) • c) ⁻¹' ball n 1) :=
      (Homeomorph.smulOfNeZero (ϖ k ^ T) (pow_ne_zero _ ϖ_ne_zero)).isCompact_preimage.2 (isCompact_ball 1)
    exact h1.inter_left (isClosed_subalgebra Z)
  let A : Set (Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k) :=
    {p | p.1 ∈ (Z : Set (Matrix (Fin n) (Fin n) k)) ∧ IsNilpotent p.2 ∧ p.1 + p.2 ∈ K}
  have hAsub : A ⊆ CZ ×ˢ ((fun p : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k => p.1 - p.2) '' (K ×ˢ CZ)) := by
    rintro ⟨c, m⟩ ⟨hc, hm, hcm⟩
    have hcz : c ∈ CZ := ⟨hc, hT c hc m hm hcm⟩
    exact ⟨hcz, ⟨(c + m, c), ⟨hcm, hcz⟩, by simp⟩⟩
  have hAc : IsClosed A := ((isClosed_subalgebra Z).preimage continuous_fst).inter
    ((isClosed_nilpotent.preimage continuous_snd).inter (hK.isClosed.preimage (continuous_fst.add continuous_snd)))
  have hA : IsCompact A :=
    (hCZ.prod ((hK.prod hCZ).image (continuous_fst.sub continuous_snd))).of_isClosed_subset hAc hAsub
  have e : ZN Z ∩ K = (fun p : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k => p.1 + p.2) '' A := by
    ext x
    constructor
    · rintro ⟨⟨c, hc, hxc⟩, hxK⟩
      exact ⟨(c, x - c), ⟨hc, hxc, by simpa using hxK⟩, by simp⟩
    · rintro ⟨⟨c, m⟩, ⟨hc, hm, hcm⟩, rfl⟩
      exact ⟨⟨c, hc, by simpa using hm⟩, hcm⟩
  rw [e]
  exact hA.image (continuous_fst.add continuous_snd)

/- English proof (translation)
Introduce `n Z hZ`. Use `isClosed_of_closure_subset fun x hx => ?_` and prove the remaining obligations. Take `⟨K, hKc, hKx⟩` from `exists_compact_mem_nhds x`. Establish `h1 : x ∈ closure (ZN Z ∩ K)`. Rewrite `hx`, the goal using `[mem_closure_iff_nhds]`.

Introduce `U hU`. Take `⟨y, hyU, hyZ⟩` from `hx (U ∩ K) (inter_mem hU hKx)`. Conclude with `⟨y, hyU.1, hyZ, hyU.2⟩`. Rewrite `h1` using `[(isCompact_inter hZ hKc).isClosed.closure_eq]`. Conclude with `h1.1`.
-/
theorem zNClosed : ZNClosed (k := k) := by
  intro n Z hZ
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨K, hKc, hKx⟩ := exists_compact_mem_nhds x
  have h1 : x ∈ closure (ZN Z ∩ K) := by
    rw [mem_closure_iff_nhds] at hx ⊢
    intro U hU
    obtain ⟨y, hyU, hyZ⟩ := hx (U ∩ K) (inter_mem hU hKx)
    exact ⟨y, hyU.1, hyZ, hyU.2⟩
  rw [(isCompact_inter hZ hKc).isClosed.closure_eq] at h1
  exact h1.1

end PositivityTheory.RgUd.T.Nil.Orb.Ozn
