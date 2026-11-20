import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoSumBoundOfMapsSplitting
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.EdgeLatRS

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def LatticeFunctorComparison : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m → ∀ (TT : Finset (Fin n')) (a : ℕ) (A B : TT → ℕ),
    (∀ s, A s + B s + 1 ≤ 8 * a) →
    ∃ (io : ∀ j : TT → ℕ, Vsp R.Kf (flatW m (fun s => A s - j s) (fun s => B s - j s)) →ₗ[R.Kf]
        VHH (m := m) R.Kf TT (ex A) (ex B))
      (pr : ∀ j : TT → ℕ, VHH (m := m) R.Kf TT (ex A) (ex B) →ₗ[R.Kf]
        Vsp R.Kf (flatW m (fun s => A s - j s) (fun s => B s - j s))),
      (∀ x, ∑ j ∈ Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)), io j (pr j x) = x) ∧
      ∀ M : Fin n' → Submodule R.O (Fin (m + 1) → R.Kf), (∀ s, IsLattice R.O (M s)) →
        ∀ j ∈ Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)),
        (∀ x ∈ toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) M),
          ((p : R.Kf) ^ (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊)) • pr j x ∈
            toV (flatW m (fun s => A s - j s) (fun s => B s - j s))
              (Hten R.O (flatW m (fun s => A s - j s) (fun s => B s - j s)) M)) ∧
        (∀ y ∈ toV (flatW m (fun s => A s - j s) (fun s => B s - j s))
              (Hten R.O (flatW m (fun s => A s - j s) (fun s => B s - j s)) M),
          ((p : R.Kf) ^ (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊)) • io j y ∈
            toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) M))

/- English proof (translation)
Establish `h0 : (Finset.univ.filter fun i : Fin (m + 1) => i.val < 1) = {0}`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `Fin.ext (by rw [Fin.val_zero]; omega)`. Introduce `h`. Substitute `h` using the available equality. Rewrite using `[Fin.val_zero]`. Use linear arithmetic over natural numbers and integers.

Establish `hl : (Fin.last m : Fin (m + 1)) ≠ 0`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[Fin.val_last, Fin.val_zero]`. Use linear arithmetic over natural numbers and integers.

Establish `key : ∀ s : Fin n', (∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => i.val < 1), lamAt (flatW m (fun s => A s - j s) (fun s => B s - j s)) s i) ≤ if s ∈ TT then (hhDeg (ex A) (ex B) s true : ℤ) else 0`. Introduce `s`. Rewrite using `[h0, Finset.sum_singleton]`. Distinguish the cases in `hs : s ∈ TT`. Establish `hA : ex A s = A ⟨s, hs⟩` using `dif_pos hs`.

Establish `hB : ex B s = B ⟨s, hs⟩` using `dif_pos hs`. Establish `f0 : flatW m (fun s => A s - j s) (fun s => B s - j s) s 0 = ((A ⟨s, hs⟩ - j ⟨s, hs⟩ : ℕ) : ℤ)`. Simplify using `[flatW, hs]`. Establish `fl : flatW m (fun s => A s - j s) (fun s => B s - j s) s (Fin.last m) = -((B ⟨s, hs⟩ - j ⟨s, hs⟩ : ℕ) : ℤ)`. Simplify using `[flatW, hs, hl]`.

Rewrite using `[if_pos hs]`. Unfold `lamAt hhDeg`. Rewrite using `[if_pos rfl, hA, hB]`. Distinguish the cases in `he : Even s.val`. Rewrite using `[if_pos he, if_pos he, f0]`.

Conclude with `Nat.sub_le _ _` after adjusting the coercions. Rewrite using `[if_neg he, if_neg he] beta_reduce`. Rewrite using `[Fin.rev_zero, fl, neg_neg]`. Conclude with `Nat.sub_le _ _` after adjusting the coercions. Establish `hz : ∀ i, flatW m (fun s => A s - j s) (fun s => B s - j s) s i = 0` using `fun i => by`.

Simplify using `[flatW, hs]`. Rewrite using `[if_neg hs]`. Unfold `lamAt`. Distinguish the cases in `he : Even s.val`. Rewrite using `[if_pos he, hz]`.

Rewrite using `[if_neg he] beta_reduce`. Rewrite using `[hz, neg_zero]`. Unfold `Ar AHH`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Ar_le_AHH {n' : ℕ} (m : ℕ) (hm : 1 ≤ m) (TT : Finset (Fin n')) (A B j : TT → ℕ) :
    Ar 1 (flatW m (fun s => A s - j s) (fun s => B s - j s)) ≤ AHH TT (ex A) (ex B) := by
  have h0 : (Finset.univ.filter fun i : Fin (m + 1) => i.val < 1) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact Fin.ext (by rw [Fin.val_zero]; omega)
    · intro h
      subst h
      rw [Fin.val_zero]
      omega
  have hl : (Fin.last m : Fin (m + 1)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    rw [Fin.val_last, Fin.val_zero] at this
    omega
  have key : ∀ s : Fin n',
      (∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => i.val < 1),
        lamAt (flatW m (fun s => A s - j s) (fun s => B s - j s)) s i) ≤
        if s ∈ TT then (hhDeg (ex A) (ex B) s true : ℤ) else 0 := by
    intro s
    rw [h0, Finset.sum_singleton]
    by_cases hs : s ∈ TT
    · have hA : ex A s = A ⟨s, hs⟩ := dif_pos hs
      have hB : ex B s = B ⟨s, hs⟩ := dif_pos hs
      have f0 : flatW m (fun s => A s - j s) (fun s => B s - j s) s 0 = ((A ⟨s, hs⟩ - j ⟨s, hs⟩ : ℕ) : ℤ) := by
        simp [flatW, hs]
      have fl : flatW m (fun s => A s - j s) (fun s => B s - j s) s (Fin.last m) =
          -((B ⟨s, hs⟩ - j ⟨s, hs⟩ : ℕ) : ℤ) := by
        simp [flatW, hs, hl]
      rw [if_pos hs]
      unfold lamAt hhDeg
      rw [if_pos rfl, hA, hB]
      by_cases he : Even s.val
      · rw [if_pos he, if_pos he, f0]
        exact_mod_cast Nat.sub_le _ _
      · rw [if_neg he, if_neg he]
        beta_reduce
        rw [Fin.rev_zero, fl, neg_neg]
        exact_mod_cast Nat.sub_le _ _
    · have hz : ∀ i, flatW m (fun s => A s - j s) (fun s => B s - j s) s i = 0 := fun i => by
        simp [flatW, hs]
      rw [if_neg hs]
      unfold lamAt
      by_cases he : Even s.val
      · rw [if_pos he, hz]
      · rw [if_neg he]
        beta_reduce
        rw [hz, neg_zero]
  unfold Ar AHH
  calc _ ≤ ∑ s : Fin n', (if s ∈ TT then (hhDeg (ex A) (ex B) s true : ℤ) else 0) :=
        Finset.sum_le_sum fun s _ => key s
    _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]

section Formal

variable {O Kf V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V] [Module O V]
  [IsScalarTower O Kf V]

/- English proof (translation)
Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le hd`. Unfold `scale`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `⟨(w ^ k) • x, M.smul_mem _ hx, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]`.

Rewrite using `[zpow_add₀ hw, zpow_natCast, mul_smul, ← map_pow, algebraMap_smul]`.
-/
theorem scale_add_le (w : O) (hw : algebraMap O Kf w ≠ 0) (a d : ℤ) (hd : 0 ≤ d) (M : Submodule O V) :
    scale (algebraMap O Kf w ^ (a + d)) M ≤ scale (algebraMap O Kf w ^ a) M := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd
  unfold scale
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(w ^ k) • x, M.smul_mem _ hx, ?_⟩
  simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
  rw [zpow_add₀ hw, zpow_natCast, mul_smul, ← map_pow, algebraMap_smul]

end Formal

/- English proof (translation)
Introduce `p n' R m hm TT a A B hdeg`. Take `⟨io, pr, hsum, hL⟩` from `h p n' R m hm TT a A B hdeg`. Generalize the expression as in `hu : TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊ = u at hL`. Use `set ω : R.Kf := algebraMap R.O R.Kf R.w with hω`. Establish `hω0 : ω ≠ 0` using `R.w_ne`.

Establish `hpω : (p : R.Kf) = ω ^ 2` using `R.p_eq`. Set `lamj : (TT → ℕ) → Fin n' → Fin (m + 1) → ℤ` to `fun j => flatW m (fun s => A s - j s) (fun s => B s - j s)`. Set `d : (TT → ℕ) → ℤ` to `fun j => AHH TT (ex A) (ex B) - Ar 1 (lamj j)`. Establish `hd : ∀ j, 0 ≤ d j` using `fun j => sub_nonneg.2 (Ar_le_AHH m (by omega) TT A B j)`. Use `⟨fun j => (ω ^ (-d j)) • io j, fun j => (ω ^ (d j)) • pr j, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x`. Rewrite using `[← hsum x]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hsum x]`. Simplify using `only [LinearMap.smul_apply, map_smul, smul_smul]`.

Rewrite using `[← zpow_add₀ hω0]`. Simplify using the standard rewrite rules. Introduce `t c e he j hj`. Establish `src : ∀ (M : Fin n' → Submodule R.O (Fin (m + 1) → R.Kf)), (∀ s, IsLattice R.O (M s)) → ∀ (E : ℤ) x, x ∈ scale (ω ^ E) (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) M)) → ((p : R.Kf) ^ u) • ((ω ^ (d j)) • pr j) x ∈ scale (ω ^ (E + d j)) (toV (lamj j) (Hten R.O (lamj j) M))`. Introduce and unpack `M hM E x ⟨x0, hx0, rfl⟩`.

Use `⟨_, (hL M hM j hj).1 x0 hx0, ?_⟩` and prove the remaining obligations. Use `show ω ^ (E + d j) • ((p : R.Kf) ^ u • pr j x0) = (p : R.Kf) ^ u • ((ω ^ (d j)) • pr j) (ω ^ E • x0)`. Rewrite using `[LinearMap.smul_apply, map_smul, smul_smul, smul_smul, smul_smul, zpow_add₀ hω0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `tst : ∀ (M : Fin n' → Submodule R.O (Fin (m + 1) → R.Kf)), (∀ s, IsLattice R.O (M s)) → ∀ (E : ℤ) Φ, Φ ∈ scale (ω ^ E) (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) M))) → ((p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (e …`. Introduce and unpack `M hM E Φ ⟨Φ0, hΦ0, rfl⟩`. Use `⟨((p : R.Kf) ^ (2 * u)) • (Φ0 ∘ₗ io j), ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨b, hb⟩` from `hΦ0 _ ((hL M hM j hj).2 y hy)`.

Use `⟨(p : R.O) ^ u * b, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hb, map_pow, map_natCast, LinearMap.smul_apply, LinearMap.comp_apply, map_smul]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `show ω ^ (E + d j) • ((p : R.Kf) ^ (2 * u) • (Φ0 ∘ₗ io j)) = (p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j)) • ((ω ^ E • Φ0) ∘ₗ ((ω ^ (-d j)) • io j))`.

Use extensionality with `y`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, map_smul]`. Establish `e1 : (p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j)) = (p : R.Kf) ^ (2 * u) * ω ^ (d j) * ω ^ (d j)`. Establish `hp0 : (p : R.Kf) ≠ 0` using `by rw [hpω]; exact pow_ne_zero _ hω0`. Establish `: ((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j) = ((2 * u : ℕ) : ℤ) + d j`.

Simplify using `only [d]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, zpow_add₀ hp0, zpow_natCast, mul_assoc]`. Use `congr 1`. Rewrite using `[hpω, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hω0]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, zpow_add₀ hω0, zpow_neg]`. Establish `hne : ω ^ (d j) ≠ 0` using `zpow_ne_zero _ hω0`.

Clear the denominators using the available nonvanishing facts. Establish `latE : ∀ e' : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e' → (∀ s : Fin n', IsLattice R.O (extO R.O R.ι R.σ s.val e'.src)) ∧ (∀ s : Fin n', IsLattice R.O (LeAt p R.ι R.σ R.w s.val e')) ∧ (∀ s : Fin n', IsLattice R.O (extO R.O R.ι R.σ s.val e'.tgt))`. Introduce `e' he'`. Take `⟨gs, hg, h1, h2, h3⟩` from `edgeLat_RS R e' he'`. Establish `hD : IsUnit (Formalism.MainNotions.G.LatticeSystems.lb_D (m + 1) 1 ω).det` using `Formalism.MainNotions.G.LatticeSystems.lb_D_det _ _ _ hω0`.

Use `⟨fun s => ⟨gs s.val, hg _, h1 _⟩, fun s => ⟨_, ?_, h2 _⟩, fun s => ⟨_, ?_, h3 _⟩⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `(hg _).mul hD`. Rewrite using `[Matrix.det_mul, Matrix.det_mul]`. Conclude with `((hg _).mul hD).mul hD`.

Establish `hAr : ∀ E : ℤ, E + -AHH TT (ex A) (ex B) + d j = E + -Ar 1 (lamj j)` using `fun E => by simp only [d]; ring`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Take `⟨⟨hx1, hx2⟩, hx3⟩` from `hx`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `scale_add_le R.w hω0 _ _ (hd j) _ (src _ (latE e he).1 _ x hx1)`. Use `src _ (latE e he).2.1 _ x hx2` as an intermediate fact. Establish `e2 : -AHH TT (ex A) (ex B) + d j = -Ar 1 (lamj j)` using `by simp only [d]; ring`. Rewrite `this` using `[e2]`. Conclude with `this`.

Use `SetLike.mem_coe.2 ((Submodule.mem_iInf _).2 fun e' => (Submodule.mem_iInf _).2 fun hc => ?_)` and prove the remaining obligations. Establish `hx4` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (SetLike.mem_coe.1 hx3) e') hc`. Take `⟨x1, ⟨x0, hx0, rfl⟩, hx5⟩` from `hx4`. Establish `hx6 : x ∈ scale (ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B))) (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) fun s => LeAt p R.ι R.σ R.w s.val e'))`. Use `⟨x0, hx0, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hx5]`. Use `show ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B)) • x0 = ω ^ (c : ℤ) • (ω ^ (-AHH TT (ex A) (ex B)) • x0)`. Rewrite using `[smul_smul, zpow_add₀ hω0]`. Take `⟨y0, hy0, hy1⟩` from `src _ (latE e' hc.1).2.1 _ x hx6`. Rewrite `hy1` using `[hAr]`.

Use `⟨ω ^ (-Ar 1 (lamj j)) • y0, ⟨y0, hy0, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy1]`. Use `show ω ^ (c : ℤ) • (ω ^ (-Ar 1 (lamj j)) • y0) = ω ^ ((c : ℤ) + -Ar 1 (lamj j)) • y0`. Rewrite using `[smul_smul, zpow_add₀ hω0]`. Introduce `Φ hΦ`.

Take `⟨⟨h1, h2⟩, h3⟩` from `hΦ`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `scale_add_le R.w hω0 _ _ (hd j) _ (tst _ (latE e he).2.2 _ Φ h1)`. Use `tst _ (latE e he).2.1 _ Φ h2` as an intermediate fact. Establish `e2 : -AHH TT (ex A) (ex B) + d j = -Ar 1 (lamj j)` using `by simp only [d]; ring`.

Rewrite `this` using `[e2]`. Conclude with `this`. Use `SetLike.mem_coe.2 ((Submodule.mem_iInf _).2 fun e' => (Submodule.mem_iInf _).2 fun hc => ?_)` and prove the remaining obligations. Establish `h4` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (SetLike.mem_coe.1 h3) e') hc`. Take `⟨Φ1, ⟨Φ0, hΦ0, rfl⟩, h5⟩` from `h4`.

Establish `h6 : Φ ∈ scale (ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B))) (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) fun s => LeAt p R.ι R.σ R.w s.val e')))`. Use `⟨Φ0, hΦ0, ?_⟩` and prove the remaining obligations. Rewrite using `[← h5]`. Use `show ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B)) • Φ0 = ω ^ (c : ℤ) • (ω ^ (-AHH TT (ex A) (ex B)) • Φ0)`. Rewrite using `[smul_smul, zpow_add₀ hω0]`.

Take `⟨y0, hy0, hy1⟩` from `tst _ (latE e' hc.1).2.1 _ Φ h6`. Rewrite `hy1` using `[hAr]`. Use `⟨ω ^ (-Ar 1 (lamj j)) • y0, ⟨y0, hy0, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy1]`. Use `show ω ^ (c : ℤ) • (ω ^ (-Ar 1 (lamj j)) • y0) = ω ^ ((c : ℤ) + -Ar 1 (lamj j)) • y0`.

Rewrite using `[smul_smul, zpow_add₀ hω0]`.
-/
theorem lattice_maps_of_functor_comparison (h : LatticeFunctorComparison) : RhoSumLatticeMaps := by
  classical
  intro p n' R m hm TT a A B hdeg
  obtain ⟨io, pr, hsum, hL⟩ := h p n' R m hm TT a A B hdeg
  generalize hu : TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊ = u at hL
  set ω : R.Kf := algebraMap R.O R.Kf R.w with hω
  have hω0 : ω ≠ 0 := R.w_ne
  have hpω : (p : R.Kf) = ω ^ 2 := R.p_eq
  let lamj : (TT → ℕ) → Fin n' → Fin (m + 1) → ℤ := fun j => flatW m (fun s => A s - j s) (fun s => B s - j s)
  let d : (TT → ℕ) → ℤ := fun j => AHH TT (ex A) (ex B) - Ar 1 (lamj j)
  have hd : ∀ j, 0 ≤ d j := fun j => sub_nonneg.2 (Ar_le_AHH m (by omega) TT A B j)
  refine ⟨fun j => (ω ^ (-d j)) • io j, fun j => (ω ^ (d j)) • pr j, ?_, ?_⟩
  · intro x
    rw [← hsum x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsum x]
    simp only [LinearMap.smul_apply, map_smul, smul_smul]
    rw [← zpow_add₀ hω0]
    simp
  intro t c e he j hj

  have src : ∀ (M : Fin n' → Submodule R.O (Fin (m + 1) → R.Kf)), (∀ s, IsLattice R.O (M s)) → ∀ (E : ℤ) x,
      x ∈ scale (ω ^ E) (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) M)) →
      ((p : R.Kf) ^ u) • ((ω ^ (d j)) • pr j) x ∈ scale (ω ^ (E + d j)) (toV (lamj j) (Hten R.O (lamj j) M)) := by
    rintro M hM E x ⟨x0, hx0, rfl⟩
    refine ⟨_, (hL M hM j hj).1 x0 hx0, ?_⟩
    show ω ^ (E + d j) • ((p : R.Kf) ^ u • pr j x0) = (p : R.Kf) ^ u • ((ω ^ (d j)) • pr j) (ω ^ E • x0)
    rw [LinearMap.smul_apply, map_smul, smul_smul, smul_smul, smul_smul, zpow_add₀ hω0]
    congr 1
    ring
  have tst : ∀ (M : Fin n' → Submodule R.O (Fin (m + 1) → R.Kf)), (∀ s, IsLattice R.O (M s)) → ∀ (E : ℤ) Φ,
      Φ ∈ scale (ω ^ E) (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) M))) →
      ((p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j))) • (Φ ∘ₗ ((ω ^ (-d j)) • io j)) ∈
        scale (ω ^ (E + d j)) (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf (toV (lamj j) (Hten R.O (lamj j) M))) := by
    rintro M hM E Φ ⟨Φ0, hΦ0, rfl⟩
    refine ⟨((p : R.Kf) ^ (2 * u)) • (Φ0 ∘ₗ io j), ?_, ?_⟩
    · intro y hy
      obtain ⟨b, hb⟩ := hΦ0 _ ((hL M hM j hj).2 y hy)
      refine ⟨(p : R.O) ^ u * b, ?_⟩
      rw [map_mul, hb, map_pow, map_natCast, LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
      simp only [smul_eq_mul]
      ring
    · show ω ^ (E + d j) • ((p : R.Kf) ^ (2 * u) • (Φ0 ∘ₗ io j)) =
        (p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j)) •
          ((ω ^ E • Φ0) ∘ₗ ((ω ^ (-d j)) • io j))
      ext y
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, map_smul]
      have e1 : (p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j)) =
          (p : R.Kf) ^ (2 * u) * ω ^ (d j) * ω ^ (d j) := by
        have hp0 : (p : R.Kf) ≠ 0 := by rw [hpω]; exact pow_ne_zero _ hω0
        have : ((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j) = ((2 * u : ℕ) : ℤ) + d j := by
          simp only [d]; ring
        rw [this, zpow_add₀ hp0, zpow_natCast, mul_assoc]
        congr 1
        rw [hpω, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hω0]
        congr 1
        push_cast
        ring
      rw [e1, zpow_add₀ hω0, zpow_neg]
      have hne : ω ^ (d j) ≠ 0 := zpow_ne_zero _ hω0
      field_simp

  have latE : ∀ e' : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e' →
      (∀ s : Fin n', IsLattice R.O (extO R.O R.ι R.σ s.val e'.src)) ∧
      (∀ s : Fin n', IsLattice R.O (LeAt p R.ι R.σ R.w s.val e')) ∧
      (∀ s : Fin n', IsLattice R.O (extO R.O R.ι R.σ s.val e'.tgt)) := by
    intro e' he'
    obtain ⟨gs, hg, h1, h2, h3⟩ := edgeLat_RS R e' he'
    have hD : IsUnit (Formalism.MainNotions.G.LatticeSystems.lb_D (m + 1) 1 ω).det := Formalism.MainNotions.G.LatticeSystems.lb_D_det _ _ _ hω0
    refine ⟨fun s => ⟨gs s.val, hg _, h1 _⟩, fun s => ⟨_, ?_, h2 _⟩, fun s => ⟨_, ?_, h3 _⟩⟩
    · rw [Matrix.det_mul]; exact (hg _).mul hD
    · rw [Matrix.det_mul, Matrix.det_mul]; exact ((hg _).mul hD).mul hD
  have hAr : ∀ E : ℤ, E + -AHH TT (ex A) (ex B) + d j = E + -Ar 1 (lamj j) := fun E => by simp only [d]; ring
  constructor
  · intro x hx
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact scale_add_le R.w hω0 _ _ (hd j) _ (src _ (latE e he).1 _ x hx1)
    · have := src _ (latE e he).2.1 _ x hx2
      have e2 : -AHH TT (ex A) (ex B) + d j = -Ar 1 (lamj j) := by simp only [d]; ring
      rw [e2] at this
      exact this
    · refine SetLike.mem_coe.2 ((Submodule.mem_iInf _).2 fun e' => (Submodule.mem_iInf _).2 fun hc => ?_)
      have hx4 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (SetLike.mem_coe.1 hx3) e') hc
      obtain ⟨x1, ⟨x0, hx0, rfl⟩, hx5⟩ := hx4
      have hx6 : x ∈ scale (ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B)))
          (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) fun s => LeAt p R.ι R.σ R.w s.val e')) := by
        refine ⟨x0, hx0, ?_⟩
        rw [← hx5]
        show ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B)) • x0 = ω ^ (c : ℤ) • (ω ^ (-AHH TT (ex A) (ex B)) • x0)
        rw [smul_smul, zpow_add₀ hω0]
      obtain ⟨y0, hy0, hy1⟩ := src _ (latE e' hc.1).2.1 _ x hx6
      rw [hAr] at hy1
      refine ⟨ω ^ (-Ar 1 (lamj j)) • y0, ⟨y0, hy0, rfl⟩, ?_⟩
      rw [← hy1]
      show ω ^ (c : ℤ) • (ω ^ (-Ar 1 (lamj j)) • y0) = ω ^ ((c : ℤ) + -Ar 1 (lamj j)) • y0
      rw [smul_smul, zpow_add₀ hω0]
  · intro Φ hΦ
    obtain ⟨⟨h1, h2⟩, h3⟩ := hΦ
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact scale_add_le R.w hω0 _ _ (hd j) _ (tst _ (latE e he).2.2 _ Φ h1)
    · have := tst _ (latE e he).2.1 _ Φ h2
      have e2 : -AHH TT (ex A) (ex B) + d j = -Ar 1 (lamj j) := by simp only [d]; ring
      rw [e2] at this
      exact this
    · refine SetLike.mem_coe.2 ((Submodule.mem_iInf _).2 fun e' => (Submodule.mem_iInf _).2 fun hc => ?_)
      have h4 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (SetLike.mem_coe.1 h3) e') hc
      obtain ⟨Φ1, ⟨Φ0, hΦ0, rfl⟩, h5⟩ := h4
      have h6 : Φ ∈ scale (ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B))) (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf
          (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) fun s => LeAt p R.ι R.σ R.w s.val e'))) := by
        refine ⟨Φ0, hΦ0, ?_⟩
        rw [← h5]
        show ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B)) • Φ0 = ω ^ (c : ℤ) • (ω ^ (-AHH TT (ex A) (ex B)) • Φ0)
        rw [smul_smul, zpow_add₀ hω0]
      obtain ⟨y0, hy0, hy1⟩ := tst _ (latE e' hc.1).2.1 _ Φ h6
      rw [hAr] at hy1
      refine ⟨ω ^ (-Ar 1 (lamj j)) • y0, ⟨y0, hy0, rfl⟩, ?_⟩
      rw [← hy1]
      show ω ^ (c : ℤ) • (ω ^ (-Ar 1 (lamj j)) • y0) = ω ^ ((c : ℤ) + -Ar 1 (lamj j)) • y0
      rw [smul_smul, zpow_add₀ hω0]

end Formalism.MainNotions.flipOneThree.Pf

end
