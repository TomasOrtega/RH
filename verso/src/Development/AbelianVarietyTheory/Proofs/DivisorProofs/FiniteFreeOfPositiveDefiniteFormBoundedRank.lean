import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `H _ Q hQ hpos hdef r hr`. Establish `h0 : Q 0 = 0`. Use `hQ 0 0` as an intermediate fact. Simplify using `only [add_zero, sub_zero] at this`. Use linear arithmetic over natural numbers and integers.

Establish `htf : ∀ (k : ℤ) (f : H), k ≠ 0 → k • f = 0 → f = 0`. Introduce `k f hk hkf`. Apply `hdef` to reduce the goal to its premises. Establish `h1` using `parallelogram_zsmul Q hQ k f`. Rewrite `h1` using `[hkf, h0]`.

Conclude with `(mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero 2 hk)`. Set `P : ℕ → Prop` to `fun n => ∃ u : Fin n → H, LinearIndependent ℤ u`. Take `⟨n, hn⟩ : ∃ n, n = Nat.findGreatest P r` from `⟨_, rfl⟩`. Establish `hPn : P n` using `hn ▸ Nat.findGreatest_spec (P := P) (m := 0) (Nat.zero_le r) ⟨Fin.elim0, linearIndependent_empty_type⟩`. Take `⟨u, hu⟩` from `hPn`.

Establish `hmax : ¬ P (n + 1)`. Introduce and unpack `⟨v, hv⟩`. Establish `hlt : Nat.findGreatest P r < n + 1` using `by omega`. Conclude with `Nat.findGreatest_is_greatest (P := P) (n := r) hlt (hr _ v hv) ⟨v, hv⟩`. Establish `hspan : ∀ h : H, ∃ k : ℕ, 0 < k ∧ ∃ m : Fin n → ℤ, k • h = ∑ i, m i • u i`.

Introduce `h`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `hmax` to reduce the goal to its premises. Use `⟨Fin.cons h u, LinearIndependent.finCons' h u hu fun c y hy hcy => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Take `⟨m, hm⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hy`. Establish `hpos' : 0 < c.natAbs` using `Int.natAbs_pos.2 hc`. Break down `Int.natAbs_eq c with hc' | hc'` into its components or cases. Apply `hne c.natAbs hpos' (fun i => - m i)` to reduce the goal to its premises.

Rewrite using `[← natCast_zsmul, ← hc']`. Simplify using `only [neg_smul, Finset.sum_neg_distrib, hm]`. Conclude with `eq_neg_of_add_eq_zero_left hcy`. Apply `hne c.natAbs hpos' m` to reduce the goal to its premises. Rewrite using `[← natCast_zsmul, hm]`.

Establish `: c • h = - ((c.natAbs : ℤ) • h)` using `by conv_lhs => rw [hc']`. Rewrite using `[neg_smul]`. Rewrite `hcy` using `[this]`. Conclude with `(neg_add_eq_zero.mp hcy)`. Take `⟨e, he, hdiv⟩` from `exists_dvd_coords_of_definite_form H ⊤ Q hQ hpos (fun f _ => hdef f) n u (fun _ => trivial) hu`.

Establish `hmem : ∀ h : H, (e : ℤ) • h ∈ Submodule.span ℤ (Set.range u)`. Introduce `h`. Take `⟨k, hk, m, hkm⟩` from `hspan h`. Establish `hd` using `hdiv k m h trivial hkm`. Use `choose m' hm' using hd`.

Establish `hz : (k : ℤ) • ((e : ℤ) • h - ∑ i, m' i • u i) = 0`. Rewrite using `[smul_sub, smul_comm (k : ℤ) (e : ℤ) h, natCast_zsmul h k, hkm, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, ← hm' i, sub_self]`. Use `htf k _ (by exact_mod_cast hk.ne') hz` as an intermediate fact.

Rewrite using `[sub_eq_zero.mp this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `f : H →ₗ[ℤ] Submodule.span ℤ (Set.range u)` to `LinearMap.codRestrict _ ((e : ℤ) • LinearMap.id) hmem`. Establish `hinj : Function.Injective f`. Introduce `a b hab`.

Establish `h' : (e : ℤ) • a = (e : ℤ) • b` using `congrArg Subtype.val hab`. Establish `: (e : ℤ) • (a - b) = 0` using `by rw [smul_sub, h', sub_self]`. Conclude with `sub_eq_zero.mp (htf e _ (by exact_mod_cast he.ne') this)`. Establish `: Module.Finite ℤ (Submodule.span ℤ (Set.range u))` using `Module.Finite.span_of_finite ℤ (Set.finite_range u)`. Establish `hfin : Module.Finite ℤ H` using `Module.Finite.of_injective f hinj`.

Establish `: Module.IsTorsionFree ℤ H` using `Module.IsTorsionFree.of_smul_eq_zero fun k x hkx => by`. Distinguish the cases in `hk : k = 0`. Conclude with `Or.inl hk`. Conclude with `Or.inr (htf k x hk hkx)`. Establish `hfree : Module.Free ℤ H` using `Module.free_of_finite_type_torsion_free'`.

Use `⟨hfin, hfree, ?_⟩` and prove the remaining obligations. Conclude with `hr _ _ (Module.finBasis ℤ H).linearIndependent`.
-/
theorem finite_free_of_definite_form_of_rank_le :
    ∀ (H : Type) [AddCommGroup H] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ r : ℕ, (∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ r) → Module.Finite ℤ H ∧ Module.Free ℤ H ∧ Module.finrank ℤ H ≤ r := by
  intro H _ Q hQ hpos hdef r hr
  classical
  have h0 : Q 0 = 0 := by
    have := hQ 0 0
    simp only [add_zero, sub_zero] at this
    omega
  have htf : ∀ (k : ℤ) (f : H), k ≠ 0 → k • f = 0 → f = 0 := by
    intro k f hk hkf
    apply hdef
    have h1 := parallelogram_zsmul Q hQ k f
    rw [hkf, h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero 2 hk)
  let P : ℕ → Prop := fun n => ∃ u : Fin n → H, LinearIndependent ℤ u
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.findGreatest P r := ⟨_, rfl⟩
  have hPn : P n := hn ▸
    Nat.findGreatest_spec (P := P) (m := 0) (Nat.zero_le r) ⟨Fin.elim0, linearIndependent_empty_type⟩
  obtain ⟨u, hu⟩ := hPn
  have hmax : ¬ P (n + 1) := by
    rintro ⟨v, hv⟩
    have hlt : Nat.findGreatest P r < n + 1 := by omega
    exact Nat.findGreatest_is_greatest (P := P) (n := r) hlt (hr _ v hv) ⟨v, hv⟩
  have hspan : ∀ h : H, ∃ k : ℕ, 0 < k ∧ ∃ m : Fin n → ℤ, k • h = ∑ i, m i • u i := by
    intro h
    by_contra hne
    push_neg at hne
    apply hmax
    refine ⟨Fin.cons h u, LinearIndependent.finCons' h u hu fun c y hy hcy => ?_⟩
    by_contra hc
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
    have hpos' : 0 < c.natAbs := Int.natAbs_pos.2 hc
    rcases Int.natAbs_eq c with hc' | hc'
    · apply hne c.natAbs hpos' (fun i => - m i)
      rw [← natCast_zsmul, ← hc']
      simp only [neg_smul, Finset.sum_neg_distrib, hm]
      exact eq_neg_of_add_eq_zero_left hcy
    · apply hne c.natAbs hpos' m
      rw [← natCast_zsmul, hm]
      have : c • h = - ((c.natAbs : ℤ) • h) := by
        conv_lhs => rw [hc']
        rw [neg_smul]
      rw [this] at hcy
      exact (neg_add_eq_zero.mp hcy)
  obtain ⟨e, he, hdiv⟩ := exists_dvd_coords_of_definite_form H ⊤ Q hQ hpos
    (fun f _ => hdef f) n u (fun _ => trivial) hu
  have hmem : ∀ h : H, (e : ℤ) • h ∈ Submodule.span ℤ (Set.range u) := by
    intro h
    obtain ⟨k, hk, m, hkm⟩ := hspan h
    have hd := hdiv k m h trivial hkm
    choose m' hm' using hd
    have hz : (k : ℤ) • ((e : ℤ) • h - ∑ i, m' i • u i) = 0 := by
      rw [smul_sub, smul_comm (k : ℤ) (e : ℤ) h, natCast_zsmul h k, hkm, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_smul, smul_smul, ← hm' i, sub_self]
    have := htf k _ (by exact_mod_cast hk.ne') hz
    rw [sub_eq_zero.mp this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : H →ₗ[ℤ] Submodule.span ℤ (Set.range u) :=
    LinearMap.codRestrict _ ((e : ℤ) • LinearMap.id) hmem
  have hinj : Function.Injective f := by
    intro a b hab
    have h' : (e : ℤ) • a = (e : ℤ) • b := congrArg Subtype.val hab
    have : (e : ℤ) • (a - b) = 0 := by rw [smul_sub, h', sub_self]
    exact sub_eq_zero.mp (htf e _ (by exact_mod_cast he.ne') this)
  have : Module.Finite ℤ (Submodule.span ℤ (Set.range u)) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range u)
  have hfin : Module.Finite ℤ H := Module.Finite.of_injective f hinj
  have : Module.IsTorsionFree ℤ H := Module.IsTorsionFree.of_smul_eq_zero fun k x hkx => by
    by_cases hk : k = 0
    · exact Or.inl hk
    · exact Or.inr (htf k x hk hkx)
  have hfree : Module.Free ℤ H := Module.free_of_finite_type_torsion_free'
  refine ⟨hfin, hfree, ?_⟩
  exact hr _ _ (Module.finBasis ℤ H).linearIndependent

end GlobalTheory
