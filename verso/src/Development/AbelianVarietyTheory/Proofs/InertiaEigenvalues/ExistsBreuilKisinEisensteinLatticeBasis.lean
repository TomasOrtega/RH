import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrincipalIdealRingWittPowerSeriesAwayPrimeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LocalizedLatticeBasis

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

/- English proof (translation)
Introduce `h`. Establish `h2` using `congrArg (fun x => bk.str.symm (Ideal.Quotient.mk _ x)) h`. Simplify using `only [map_natCast, map_zero] at h2`. Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2`.
-/
theorem l_ne_zero : (l : bk.S) ≠ 0 := by
  intro h
  have h2 := congrArg (fun x => bk.str.symm (Ideal.Quotient.mk _ x)) h
  simp only [map_natCast, map_zero] at h2
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2

/- English proof (translation)
The claim follows from `IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (l_ne_zero bk))`.
-/
theorem isDomain_loc : IsDomain (Localization.Away (l : bk.S)) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (l_ne_zero bk))

/- English proof (translation)
The claim follows from `IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (l_ne_zero bk))`.
-/
theorem inj_loc : Function.Injective (algebraMap bk.S (Localization.Away (l : bk.S))) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (l_ne_zero bk))

/- English proof (translation)
Take `⟨⟨b, hb⟩, h⟩` from `IsLocalization.exist_integer_multiples (Submonoid.powers (l : bk.S)) (Finset.univ : Finset (α × β)) (fun p => A p.1 p.2)`. Take `⟨k, rfl⟩` from `Submonoid.mem_powers_iff _ _ |>.1 hb`. Use `⟨k, fun j hj => ?_⟩` and prove the remaining obligations. Establish `h' : ∀ p : α × β, ∃ s : bk.S, algebraMap bk.S _ s = ((l : bk.S) ^ k) • A p.1 p.2`. Introduce `p`.

Take `⟨s, hs⟩` from `h p (Finset.mem_univ _)`. Conclude with `⟨s, hs⟩`. Use `choose s hs using h'`. Use `⟨Matrix.of fun i i' => (l : bk.S) ^ (j - k) * s (i, i'), ?_⟩` and prove the remaining obligations. Use extensionality with `i i'`.

Simplify using `only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, map_mul, map_pow, hs, smul_eq_mul, Algebra.smul_def]`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hj]`.
-/
theorem clear {α β : Type} [Fintype α] [Fintype β]
    (A : Matrix α β (Localization.Away (l : bk.S))) :
    ∃ k : ℕ, ∀ j, k ≤ j → ∃ A₀ : Matrix α β bk.S,
      A₀.map (algebraMap bk.S (Localization.Away (l : bk.S))) =
        (algebraMap bk.S (Localization.Away (l : bk.S)) (l : bk.S)) ^ j • A := by
  obtain ⟨⟨b, hb⟩, h⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers (l : bk.S))
    (Finset.univ : Finset (α × β)) (fun p => A p.1 p.2)
  obtain ⟨k, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hb
  refine ⟨k, fun j hj => ?_⟩
  have h' : ∀ p : α × β, ∃ s : bk.S, algebraMap bk.S _ s = ((l : bk.S) ^ k) • A p.1 p.2 := by
    intro p
    obtain ⟨s, hs⟩ := h p (Finset.mem_univ _)
    exact ⟨s, hs⟩
  choose s hs using h'
  refine ⟨Matrix.of fun i i' => (l : bk.S) ^ (j - k) * s (i, i'), ?_⟩
  ext i i'
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, map_mul, map_pow, hs, smul_eq_mul,
    Algebra.smul_def]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj]

end GlobalTheory.BSP.LocalizedLatticeBasis

namespace GlobalTheory.BSP.LocalizedLatticeBasis

/- English proof (translation)
Set `g : Fin m ⊕ Fin d → (Fin d → R)` to `fun s => Sum.elim (fun k i => Y i k) (fun j => e • Pi.single j 1) s`. Set `N : Submodule R (Fin d → R)` to `Submodule.span R (Set.range g)`. Take `⟨k, bN⟩` from `Submodule.basisOfPid (Pi.basisFun R (Fin d)) N`. Establish `gmem : ∀ s, g s ∈ N` using `fun s => Submodule.subset_span ⟨s, rfl⟩`. Establish `hk : k = d`.

Apply `le_antisymm` to reduce the goal to its premises. Establish `h1` using `Submodule.finrank_le N`. Rewrite `h1` using `[Module.finrank_eq_card_basis bN, Module.finrank_fin_fun]`. Simplify using `using h1`. Establish `hli : LinearIndependent R (fun j : Fin d => (⟨g (Sum.inr j), gmem _⟩ : N))`.

Apply `LinearIndependent.of_comp N.subtype` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `LinearIndependent R (fun j : Fin d => e • (Pi.single j (1 : R) : Fin d → R))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`. Use `congrFun hc i` as an intermediate fact.

Simplify using `[Finset.sum_apply, Pi.single_apply] at this`. Conclude with `(this.resolve_right he)`. Establish `h1` using `hli.fintype_card_le_finrank`. Rewrite `h1` using `[Module.finrank_eq_card_basis bN]`. Simplify using `using h1`.

Substitute `hk` using the available equality. Establish `hc : ∀ j, ∃ c : Fin m ⊕ Fin k → R, ∑ s, c s • g s = (bN j : Fin k → R)` using `fun j => (Submodule.mem_span_range_iff_exists_fun R).1 (bN j).2`. Use `choose c hc using hc`. Establish `hr : ∀ s (i : Fin k), g s i = ∑ j, bN.repr ⟨g s, gmem s⟩ j * (bN j : Fin k → R) i`. Introduce `s i`.

Establish `h` using `congrArg (fun x : N => (x : Fin k → R) i) (bN.sum_repr ⟨g s, gmem s⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h`. Conclude with `h.symm`. Use `⟨Matrix.of fun i j => (bN j : Fin k → R) i, Matrix.of fun j i => bN.repr ⟨g (Sum.inr i), gmem _⟩ j, Matrix.of fun i j => c j (Sum.inr i), Matrix.of fun i j => c j (Sum.inl i), Matrix.of fun j i => bN.repr ⟨g (Sum.inl i), gmem _⟩ j, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Establish `h` using `congrFun (hc j) i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, g, Sum.elim_inl, Sum.elim_inr, Pi.single_apply] at h`. Simplify using `only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, ← h]`. Simplify using `[mul_comm]`. Use extensionality with `i i'`.

Simplify using `only [Matrix.of_apply, Matrix.mul_apply]`. Rewrite using `[show Y i i' = g (Sum.inl i') i from rfl, hr]`. Simplify using `[mul_comm]`. Use extensionality with `i i'`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply]`.

Establish `h` using `hr (Sum.inr i') i`. Simplify using `only [g, Sum.elim_inr, Pi.smul_apply, Pi.single_apply, smul_eq_mul] at h`. Simplify using `only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Rewrite using `[h]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem pid_basis {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (d m : ℕ)
    (Y : Matrix (Fin d) (Fin m) R) (e : R) (he : e ≠ 0) :
    ∃ (X X' Rm : Matrix (Fin d) (Fin d) R) (Q : Matrix (Fin m) (Fin d) R) (Q' : Matrix (Fin d) (Fin m) R),
      X = Y * Q + e • Rm ∧ Y = X * Q' ∧ X * X' = e • (1 : Matrix (Fin d) (Fin d) R) := by
  classical
  let g : Fin m ⊕ Fin d → (Fin d → R) := fun s => Sum.elim (fun k i => Y i k) (fun j => e • Pi.single j 1) s
  let N : Submodule R (Fin d → R) := Submodule.span R (Set.range g)
  obtain ⟨k, bN⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin d)) N
  have gmem : ∀ s, g s ∈ N := fun s => Submodule.subset_span ⟨s, rfl⟩
  have hk : k = d := by
    apply le_antisymm
    · have h1 := Submodule.finrank_le N
      rw [Module.finrank_eq_card_basis bN, Module.finrank_fin_fun] at h1
      simpa using h1
    · have hli : LinearIndependent R (fun j : Fin d => (⟨g (Sum.inr j), gmem _⟩ : N)) := by
        apply LinearIndependent.of_comp N.subtype
        change LinearIndependent R (fun j : Fin d => e • (Pi.single j (1 : R) : Fin d → R))
        rw [Fintype.linearIndependent_iff]
        intro c hc i
        have := congrFun hc i
        simp [Finset.sum_apply, Pi.single_apply] at this
        exact (this.resolve_right he)
      have h1 := hli.fintype_card_le_finrank
      rw [Module.finrank_eq_card_basis bN] at h1
      simpa using h1
  subst hk
  have hc : ∀ j, ∃ c : Fin m ⊕ Fin k → R, ∑ s, c s • g s = (bN j : Fin k → R) :=
    fun j => (Submodule.mem_span_range_iff_exists_fun R).1 (bN j).2
  choose c hc using hc
  have hr : ∀ s (i : Fin k), g s i = ∑ j, bN.repr ⟨g s, gmem s⟩ j * (bN j : Fin k → R) i := by
    intro s i
    have h := congrArg (fun x : N => (x : Fin k → R) i) (bN.sum_repr ⟨g s, gmem s⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  refine ⟨Matrix.of fun i j => (bN j : Fin k → R) i, Matrix.of fun j i => bN.repr ⟨g (Sum.inr i), gmem _⟩ j,
    Matrix.of fun i j => c j (Sum.inr i), Matrix.of fun i j => c j (Sum.inl i),
    Matrix.of fun j i => bN.repr ⟨g (Sum.inl i), gmem _⟩ j, ?_, ?_, ?_⟩
  · ext i j
    have h := congrFun (hc j) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, g, Sum.elim_inl,
      Sum.elim_inr, Pi.single_apply] at h
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, ← h]
    simp [mul_comm]
  · ext i i'
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [show Y i i' = g (Sum.inl i') i from rfl, hr]
    simp [mul_comm]
  · ext i i'
    simp only [Matrix.of_apply, Matrix.mul_apply]
    have h := hr (Sum.inr i') i
    simp only [g, Sum.elim_inr, Pi.smul_apply, Pi.single_apply, smul_eq_mul] at h
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.BSP.LocalizedLatticeBasis

namespace GlobalTheory.BSP.LocalizedLatticeBasis

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem matMapSmul {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {α β : Type} (s : S) (M : Matrix α β S) :
    (s • M).map f = f s • M.map f := by
  ext i j; simp

open Matrix in

/- English proof (translation)
Introduce `l _ K bk d m n Y`. Use `haveI := isDomain_loc bk`. Use `haveI := GlobalTheory.T.isPrincipalIdealRing_wittPowerSeries_away_prime l K bk`. Use `set φ := algebraMap bk.S (Localization.Away (l : bk.S)) with hφ`. Establish `hE : φ (bk.E ^ n) ≠ 0`.

Rewrite using `[map_ne_zero_iff _ (inj_loc bk)]`. Conclude with `pow_ne_zero _ bk.E_ne_zero`. Take `⟨Xb, X'b, Rb, Qb, Q'b, h1, h2, h3⟩` from `pid_basis d m (Y.map φ) (φ (bk.E ^ n)) hE`. Take `⟨k1, c1⟩` from `clear bk Qb`. Take `⟨k2, c2⟩` from `clear bk Rb`.

Take `⟨k3, c3⟩` from `clear bk Q'b`. Take `⟨k4, c4⟩` from `clear bk X'b`. Take `⟨Q0, hQ0⟩` from `c1 (k1 + k2 + k3 + k4) (by omega)`. Take `⟨R0, hR0⟩` from `c2 (k1 + k2 + k3 + k4) (by omega)`. Take `⟨Q'0, hQ'0⟩` from `c3 (k1 + k2 + k3 + k4) (by omega)`.

Take `⟨X'0, hX'0⟩` from `c4 (k1 + k2 + k3 + k4) (by omega)`. Rewrite `hQ0`, `hR0`, `hQ'0`, `hX'0` using `[← hφ]`. Use `set c0 := k1 + k2 + k3 + k4`. Establish `hinj : Function.Injective fun M : Matrix (Fin d) (Fin d) bk.S => M.map φ` using `Matrix.map_injective (inj_loc bk)`. Establish `hinj' : Function.Injective fun M : Matrix (Fin d) (Fin m) bk.S => M.map φ` using `Matrix.map_injective (inj_loc bk)`.

Establish `hX : (Y * Q0 + bk.E ^ n • R0).map φ = φ (l : bk.S) ^ c0 • Xb`. Rewrite using `[Matrix.map_add φ (map_add φ), Matrix.map_mul, matMapSmul, hQ0, hR0, h1, smul_add, Matrix.mul_smul, smul_comm]`. Use `⟨2 * c0, Y * Q0 + bk.E ^ n • R0, X'0, R0, Q0, Q'0, ?_, rfl, ?_⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Simplify using `only`.

Rewrite using `[Matrix.map_mul, hX, hX'0, Matrix.smul_mul, Matrix.mul_smul, h3, matMapSmul, Matrix.map_one _ (map_zero φ) (map_one φ), smul_smul, smul_smul]`. Use `congr 1`. Simplify using `only [map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Apply `hinj'` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[Matrix.map_mul, hX, hQ'0, Matrix.smul_mul, Matrix.mul_smul, ← h2, matMapSmul, smul_smul, map_pow, two_mul, pow_add]`.
-/
theorem exists_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d m n : ℕ)
    (Y : Matrix (Fin d) (Fin m) (bk.S)), ∃ (c : ℕ) (X X' R : Matrix (Fin d) (Fin d) (bk.S))
    (Q : Matrix (Fin m) (Fin d) (bk.S)) (Q' : Matrix (Fin d) (Fin m) (bk.S)),
    X * X' = ((l : bk.S) ^ c * bk.E ^ n) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ X = Y * Q + bk.E ^ n • R ∧
      (l : bk.S) ^ c • Y = X * Q' := by
  intro l _ K bk d m n Y
  haveI := isDomain_loc bk
  haveI := GlobalTheory.T.isPrincipalIdealRing_wittPowerSeries_away_prime l K bk
  set φ := algebraMap bk.S (Localization.Away (l : bk.S)) with hφ
  have hE : φ (bk.E ^ n) ≠ 0 := by
    rw [map_ne_zero_iff _ (inj_loc bk)]; exact pow_ne_zero _ bk.E_ne_zero
  obtain ⟨Xb, X'b, Rb, Qb, Q'b, h1, h2, h3⟩ := pid_basis d m (Y.map φ) (φ (bk.E ^ n)) hE
  obtain ⟨k1, c1⟩ := clear bk Qb
  obtain ⟨k2, c2⟩ := clear bk Rb
  obtain ⟨k3, c3⟩ := clear bk Q'b
  obtain ⟨k4, c4⟩ := clear bk X'b
  obtain ⟨Q0, hQ0⟩ := c1 (k1 + k2 + k3 + k4) (by omega)
  obtain ⟨R0, hR0⟩ := c2 (k1 + k2 + k3 + k4) (by omega)
  obtain ⟨Q'0, hQ'0⟩ := c3 (k1 + k2 + k3 + k4) (by omega)
  obtain ⟨X'0, hX'0⟩ := c4 (k1 + k2 + k3 + k4) (by omega)
  rw [← hφ] at hQ0 hR0 hQ'0 hX'0
  set c0 := k1 + k2 + k3 + k4
  have hinj : Function.Injective fun M : Matrix (Fin d) (Fin d) bk.S => M.map φ := Matrix.map_injective (inj_loc bk)
  have hinj' : Function.Injective fun M : Matrix (Fin d) (Fin m) bk.S => M.map φ := Matrix.map_injective (inj_loc bk)
  have hX : (Y * Q0 + bk.E ^ n • R0).map φ = φ (l : bk.S) ^ c0 • Xb := by
    rw [Matrix.map_add φ (map_add φ), Matrix.map_mul, matMapSmul, hQ0, hR0, h1, smul_add, Matrix.mul_smul, smul_comm]
  refine ⟨2 * c0, Y * Q0 + bk.E ^ n • R0, X'0, R0, Q0, Q'0, ?_, rfl, ?_⟩
  · apply hinj
    simp only
    rw [Matrix.map_mul, hX, hX'0, Matrix.smul_mul, Matrix.mul_smul, h3, matMapSmul, Matrix.map_one _ (map_zero φ) (map_one φ),
      smul_smul, smul_smul]
    congr 1
    simp only [map_mul, map_pow]
    ring
  · apply hinj'
    simp only
    rw [Matrix.map_mul, hX, hQ'0, Matrix.smul_mul, Matrix.mul_smul, ← h2, matMapSmul, smul_smul, map_pow, two_mul, pow_add]

end GlobalTheory.BSP.LocalizedLatticeBasis
