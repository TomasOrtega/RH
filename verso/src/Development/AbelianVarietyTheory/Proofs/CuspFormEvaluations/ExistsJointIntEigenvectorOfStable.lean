import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ s : Finset ℤ, ∀ x ∈ U, x ≠ 0 → x ∈ (⨆ n ∈ s, f.eigenspace (n : K)) → ∃ n : ℤ, ∃ u ∈ U, u ≠ 0 ∧ f u = (n : K) • u`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro x _ hx0 hx`. Simplify using `at hx`.

Conclude with `absurd hx hx0`. Consider the case `insert a s _ ih`. Introduce `x hxU hx0 hx`. Distinguish the cases in `hw : f x - (a : K) • x = 0`. Conclude with `⟨a, x, hxU, hx0, sub_eq_zero.mp hw⟩`.

Use `ih _ (U.sub_mem (hU x hxU) (U.smul_mem _ hxU)) hw ?_` and prove the remaining obligations. Rewrite `hx` using `[Finset.iSup_insert, Submodule.mem_sup]`. Take `⟨y, hy, z, hz, rfl⟩` from `hx`. Rewrite `hy` using `[Module.End.mem_eigenspace_iff]`. Establish `h1 : f (y + z) - (a : K) • (y + z) = f z - (a : K) • z`.

Rewrite using `[map_add, hy, smul_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1]`. Use `Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ hz)` and prove the remaining obligations. Establish `: (⨆ n ∈ s, f.eigenspace (n : K)) ≤ (⨆ n ∈ s, f.eigenspace (n : K)).comap f`.

Use `iSup₂_le fun n hn => ?_` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[Submodule.mem_comap, Module.End.mem_eigenspace_iff.mp hw]`. Conclude with `Submodule.smul_mem _ _ (le_iSup₂ (f := fun n (_ : n ∈ s) => f.eigenspace (n : K)) n hn hw)`. Conclude with `this hz`.

Take `⟨x, hxU, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU0`. Establish `hx : x ∈ ⨆ n : ℤ, f.eigenspace (n : K)` using `by rw [hf]; trivial`. Take `⟨s, hs⟩` from `Submodule.mem_iSup_iff_exists_finset.mp hx`. Conclude with `key s x hxU hx0 hs`.
-/
theorem exists_int_eigenvector_of_stable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (hf : ⨆ n : ℤ, f.eigenspace (n : K) = ⊤)
    (U : Submodule K V) (hU : ∀ x ∈ U, f x ∈ U) (hU0 : U ≠ ⊥) :
    ∃ n : ℤ, ∃ u ∈ U, u ≠ 0 ∧ f u = (n : K) • u := by
  classical
  have key : ∀ s : Finset ℤ, ∀ x ∈ U, x ≠ 0 → x ∈ (⨆ n ∈ s, f.eigenspace (n : K)) →
      ∃ n : ℤ, ∃ u ∈ U, u ≠ 0 ∧ f u = (n : K) • u := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ hx0 hx; simp at hx; exact absurd hx hx0
    | insert a s _ ih =>
      intro x hxU hx0 hx
      by_cases hw : f x - (a : K) • x = 0
      · exact ⟨a, x, hxU, hx0, sub_eq_zero.mp hw⟩
      · refine ih _ (U.sub_mem (hU x hxU) (U.smul_mem _ hxU)) hw ?_
        rw [Finset.iSup_insert, Submodule.mem_sup] at hx
        obtain ⟨y, hy, z, hz, rfl⟩ := hx
        rw [Module.End.mem_eigenspace_iff] at hy
        have h1 : f (y + z) - (a : K) • (y + z) = f z - (a : K) • z := by
          rw [map_add, hy, smul_add]; abel
        rw [h1]
        refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ hz)
        have : (⨆ n ∈ s, f.eigenspace (n : K)) ≤ (⨆ n ∈ s, f.eigenspace (n : K)).comap f := by
          refine iSup₂_le fun n hn => ?_
          intro w hw
          rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff.mp hw]
          exact Submodule.smul_mem _ _
            (le_iSup₂ (f := fun n (_ : n ∈ s) => f.eigenspace (n : K)) n hn hw)
        exact this hz
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hx : x ∈ ⨆ n : ℤ, f.eigenspace (n : K) := by rw [hf]; trivial
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx
  exact key s x hxU hx0 hs

/- English proof (translation)
Establish `key : ∀ s : Finset ι, ∃ U : Submodule K V, U ≤ W ∧ U ≠ ⊥ ∧ (∀ a, ∀ x ∈ U, f a x ∈ U) ∧ ∃ κ : ι → ℤ, ∀ a ∈ s, ∀ x ∈ U, f a x = (κ a : K) • x`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨W, le_rfl, hW0, hW, 0, by simp⟩`. Consider the case `insert a s ha ih`.

Take `⟨U, hUW, hU0, hU, κ, hκ⟩` from `ih`. Take `⟨n, u, huU, hu0, hu⟩` from `exists_int_eigenvector_of_stable (f a) (hf a) U (hU a) hU0`. Use `⟨U ⊓ (f a).eigenspace (n : K), inf_le_left.trans hUW, ?_, ?_, Function.update κ a n, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.ne_bot_iff]`. Conclude with `⟨u, ⟨huU, Module.End.mem_eigenspace_iff.mpr hu⟩, hu0⟩`.

Introduce `b x hx`. Use `⟨hU b x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩` and prove the remaining obligations. Establish `h1` using `Module.End.mem_eigenspace_iff.mp hx.2`. Establish `h2` using `LinearMap.congr_fun (hc a b) x`. Simplify using `only [Module.End.mul_apply] at h2`.

Rewrite using `[h2, h1, map_smul]`. Introduce `b hb x hx`. Break down `Finset.mem_insert.mp hb with rfl | hb` into its components or cases. Rewrite using `[Function.update_self]`. Conclude with `Module.End.mem_eigenspace_iff.mp hx.2`.

Establish `: b ≠ a` using `fun h => ha (h ▸ hb)`. Rewrite using `[Function.update_of_ne this]`. Conclude with `hκ b hb x hx.1`. Take `⟨U, hUW, hU0, -, κ, hκ⟩` from `key Finset.univ`. Take `⟨x, hxU, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU0`.

Conclude with `⟨κ, x, hUW hxU, hx0, fun a => hκ a (Finset.mem_univ a) x hxU⟩`.
-/
theorem exists_joint_int_eigenvector_of_stable {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (f : ι → Module.End K V) (hc : ∀ a b, f a * f b = f b * f a)
    (hf : ∀ a, ⨆ n : ℤ, (f a).eigenspace (n : K) = ⊤)
    (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, f a x ∈ W) (hW0 : W ≠ ⊥) :
    ∃ κ : ι → ℤ, ∃ u ∈ W, u ≠ 0 ∧ ∀ a, f a u = (κ a : K) • u := by
  classical
  have key : ∀ s : Finset ι, ∃ U : Submodule K V, U ≤ W ∧ U ≠ ⊥ ∧ (∀ a, ∀ x ∈ U, f a x ∈ U) ∧
      ∃ κ : ι → ℤ, ∀ a ∈ s, ∀ x ∈ U, f a x = (κ a : K) • x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨W, le_rfl, hW0, hW, 0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨U, hUW, hU0, hU, κ, hκ⟩ := ih
      obtain ⟨n, u, huU, hu0, hu⟩ := exists_int_eigenvector_of_stable (f a) (hf a) U (hU a) hU0
      refine ⟨U ⊓ (f a).eigenspace (n : K), inf_le_left.trans hUW, ?_, ?_,
        Function.update κ a n, ?_⟩
      · rw [Submodule.ne_bot_iff]
        exact ⟨u, ⟨huU, Module.End.mem_eigenspace_iff.mpr hu⟩, hu0⟩
      · intro b x hx
        refine ⟨hU b x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h1 := Module.End.mem_eigenspace_iff.mp hx.2
        have h2 := LinearMap.congr_fun (hc a b) x
        simp only [Module.End.mul_apply] at h2
        rw [h2, h1, map_smul]
      · intro b hb x hx
        rcases Finset.mem_insert.mp hb with rfl | hb
        · rw [Function.update_self]; exact Module.End.mem_eigenspace_iff.mp hx.2
        · have : b ≠ a := fun h => ha (h ▸ hb)
          rw [Function.update_of_ne this]; exact hκ b hb x hx.1
  obtain ⟨U, hUW, hU0, -, κ, hκ⟩ := key Finset.univ
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  exact ⟨κ, x, hUW hxU, hx0, fun a => hκ a (Finset.mem_univ a) x hxU⟩

/- English proof (translation)
Take `⟨κ₀, u₀, hu₀W, hu₀, hκ₀⟩` from `exists_joint_int_eigenvector_of_stable (fun a : T × Fin m => e a.1 a.2 a.2) (by`. Introduce `a b`. Use `he a.1 b.1 a.2 b.2 b.2` as an intermediate fact. Rewrite `this` using `[sub_self, ite_self, zero_smul]`. Conclude with `sub_eq_zero.mp this)`.

Use the proof step `(by`. Introduce `a`. Rewrite using `[eq_top_iff, ← hdiag]`. Use `iSup_le fun κ => ?_` and prove the remaining obligations. Conclude with `le_trans ((iInf_le _ a.1).trans (iInf_le _ a.2)) (le_iSup (fun n : ℤ => (e a.1 a.2 a.2).eigenspace (n : K)) (κ a.1 a.2)))`.

Use `W (fun a => hW a.1 a.2 a.2) hW0`. Set `ht : (T → Fin m → ℤ) → ℤ` to `fun κ => ∑ t, ∑ i : Fin m, (i : ℤ) * κ t i`. Set `h : Module.End K V` to `∑ t, ∑ i : Fin m, ((i : ℕ) : K) • e t i i`. Establish `hhW : ∀ w ∈ W, h w ∈ W`. Introduce `w hw`.

Simplify using `only [h, LinearMap.sum_apply, LinearMap.smul_apply]`. Conclude with `W.sum_mem fun t _ => W.sum_mem fun i _ => W.smul_mem _ (hW t i i w hw)`. Establish `hh : ∀ (κ : T → Fin m → ℤ) (v : V), (∀ t i, e t i i v = (κ t i : K) • v) → h v = (ht κ : K) • v`. Introduce `κ v hv`. Simplify using `only [h, ht, LinearMap.sum_apply, LinearMap.smul_apply, hv, smul_smul]`.

Use `push_cast`. Simplify using `only [Finset.sum_smul]`. Set `S : Set ℤ` to `{n | ∃ κ : T → Fin m → ℤ, ht κ = n ∧ ∃ v ∈ W, v ≠ 0 ∧ ∀ t i, e t i i v = (κ t i : K) • v}`. Establish `hS : S.Finite`. Establish `hfin` using `Module.End.finite_hasEigenvalue (h.restrict hhW)`.

Use `(hfin.preimage (f := fun n : ℤ => (n : K)) Int.cast_injective.injOn).subset ?_` and prove the remaining obligations. Introduce and unpack `n ⟨κ, rfl, v, hvW, hv0, hv⟩`. Use `Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvW⟩) ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff]`. Conclude with `Subtype.ext (hh κ v hv)`.

Conclude with `fun h0 => hv0 (congrArg Subtype.val h0)`. Establish `hSne : S.Nonempty` using `⟨_, fun t i => κ₀ (t, i), rfl, u₀, hu₀W, hu₀, fun t i => hκ₀ (t, i)⟩`. Take `⟨n, ⟨κ, rfl, v, hvW, hv0, hv⟩, hmin⟩` from `Set.exists_min_image S id hS hSne`. Use `⟨v, hvW, hv0, ?_, κ, hv⟩` and prove the remaining obligations. Introduce `t' k l hkl`.

Assume the negation of the conclusion as `hne`. Set `δ : T → Fin m → ℤ` to `fun t i => if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0)) else 0`. Establish `hmem : ht (κ + δ) ∈ S`. Use `⟨κ + δ, rfl, e t' k l v, hW _ _ _ v hvW, hne, fun t i => ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun (he t t' i k l) v`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hv, map_smul] at h1`. Rewrite `h1` using `[sub_eq_iff_eq_add]`. Rewrite using `[h1, ← add_smul, add_comm]`. Use `congr 1`. Simplify using `only [δ, Pi.add_apply]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hδ : ht δ = (k : ℤ) - (l : ℤ)`. Simplify using `only [ht, δ]`. Rewrite using `[Finset.sum_eq_single t']`.

Simplify using `[mul_sub, Finset.sum_sub_distrib]`. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Establish `hadd : ht (κ + δ) = ht κ + ht δ`.

Simplify using `only [ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Establish `h2` using `hmin _ hmem`. Establish `h3 : (k : ℕ) < l` using `hkl`. Simplify using `only [id] at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_highest_vector {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [Fintype T] [DecidableEq T] {m : ℕ}
    (e : T → Fin m → Fin m → Module.End K V)
    (he : ∀ t t' i k l, e t i i * e t' k l - e t' k l * e t i i = (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : K) else 0) • e t' k l)
    (hdiag : ⨆ κ : T → Fin m → ℤ, (⨅ t, ⨅ i, Module.End.eigenspace (e t i i) (κ t i : K)) = ⊤)
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ t i j, ∀ w ∈ W, e t i j w ∈ W) (hW0 : W ≠ ⊥) :
    ∃ v ∈ W, v ≠ 0 ∧ (∀ t i j, i < j → e t i j v = 0) ∧ ∃ κ : T → Fin m → ℤ, ∀ t i, e t i i v = (κ t i : K) • v := by
  classical

  obtain ⟨κ₀, u₀, hu₀W, hu₀, hκ₀⟩ := exists_joint_int_eigenvector_of_stable
    (fun a : T × Fin m => e a.1 a.2 a.2)
    (by
      intro a b
      have := he a.1 b.1 a.2 b.2 b.2
      rw [sub_self, ite_self, zero_smul] at this
      exact sub_eq_zero.mp this)
    (by
      intro a
      rw [eq_top_iff, ← hdiag]
      refine iSup_le fun κ => ?_
      exact le_trans ((iInf_le _ a.1).trans (iInf_le _ a.2))
        (le_iSup (fun n : ℤ => (e a.1 a.2 a.2).eigenspace (n : K)) (κ a.1 a.2)))
    W (fun a => hW a.1 a.2 a.2) hW0

  let ht : (T → Fin m → ℤ) → ℤ := fun κ => ∑ t, ∑ i : Fin m, (i : ℤ) * κ t i
  let h : Module.End K V := ∑ t, ∑ i : Fin m, ((i : ℕ) : K) • e t i i
  have hhW : ∀ w ∈ W, h w ∈ W := by
    intro w hw
    simp only [h, LinearMap.sum_apply, LinearMap.smul_apply]
    exact W.sum_mem fun t _ => W.sum_mem fun i _ => W.smul_mem _ (hW t i i w hw)
  have hh : ∀ (κ : T → Fin m → ℤ) (v : V), (∀ t i, e t i i v = (κ t i : K) • v) →
      h v = (ht κ : K) • v := by
    intro κ v hv
    simp only [h, ht, LinearMap.sum_apply, LinearMap.smul_apply, hv, smul_smul]
    push_cast
    simp only [Finset.sum_smul]
  let S : Set ℤ := {n | ∃ κ : T → Fin m → ℤ, ht κ = n ∧
    ∃ v ∈ W, v ≠ 0 ∧ ∀ t i, e t i i v = (κ t i : K) • v}
  have hS : S.Finite := by
    have hfin := Module.End.finite_hasEigenvalue (h.restrict hhW)
    refine (hfin.preimage (f := fun n : ℤ => (n : K)) Int.cast_injective.injOn).subset ?_
    rintro n ⟨κ, rfl, v, hvW, hv0, hv⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvW⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (hh κ v hv)
    · exact fun h0 => hv0 (congrArg Subtype.val h0)
  have hSne : S.Nonempty :=
    ⟨_, fun t i => κ₀ (t, i), rfl, u₀, hu₀W, hu₀, fun t i => hκ₀ (t, i)⟩
  obtain ⟨n, ⟨κ, rfl, v, hvW, hv0, hv⟩, hmin⟩ := Set.exists_min_image S id hS hSne
  refine ⟨v, hvW, hv0, ?_, κ, hv⟩
  intro t' k l hkl
  by_contra hne
  let δ : T → Fin m → ℤ := fun t i =>
    if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0)) else 0
  have hmem : ht (κ + δ) ∈ S := by
    refine ⟨κ + δ, rfl, e t' k l v, hW _ _ _ v hvW, hne, fun t i => ?_⟩
    have h1 := LinearMap.congr_fun (he t t' i k l) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hv,
      map_smul] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, ← add_smul, add_comm]
    congr 1
    simp only [δ, Pi.add_apply]
    push_cast
    rfl
  have hδ : ht δ = (k : ℤ) - (l : ℤ) := by
    simp only [ht, δ]
    rw [Finset.sum_eq_single t']
    · simp [mul_sub, Finset.sum_sub_distrib]
    · intro b _ hb; simp [hb]
    · simp
  have hadd : ht (κ + δ) = ht κ + ht δ := by
    simp only [ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have h2 := hmin _ hmem
  have h3 : (k : ℕ) < l := hkl
  simp only [id] at h2
  omega

end GlobalTheory
