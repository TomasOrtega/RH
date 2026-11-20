import Mathlib

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Submodule

/- English proof (translation)
Take `⟨c, hcdef⟩ : ∃ c : K, c = algebraMap O K π ^ N` from `⟨_, rfl⟩`. Rewrite `hd` using `[← hcdef]`. Rewrite using `[← hcdef]`. Establish `hinj : Function.Injective (algebraMap O K)` using `IsFractionRing.injective O K`. Establish `hπ0 : π ≠ 0` using `by rw [← hπ]; exact pow_ne_zero _ hw.ne_zero`.

Establish `hc0 : c ≠ 0` using `by rw [hcdef]; exact pow_ne_zero _ ((map_ne_zero_iff _ hinj).2 hπ0)`. Establish `hbmem : ∀ k, b k ∈ span O (Set.range b)` using `fun k => subset_span ⟨k, rfl⟩`. Establish `hMo : ∀ k l, ∃ m : O, algebraMap O K m = c * B0 (b k) (b l)`. Introduce `k l`. Take `⟨m, hm⟩` from `hd (b l) (hbmem l) (b k) (hbmem k)`.

Conclude with `⟨m, by rw [hm, LinearMap.map_smul, smul_eq_mul]⟩`. Use `choose Mo hMo using hMo`. Set `Mat : Matrix (Fin n) (Fin n) O` to `fun k l => Mo k l`. Set `vec : (Fin n → O) → V` to `fun d => ∑ k, algebraMap O K (d k) • b k`. Establish `hvec_mem : ∀ d, vec d ∈ span O (Set.range b)`.

Introduce `d`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (hbmem k)`. Establish `hvec_memK : ∀ d, vec d ∈ span K (Set.range b)` using `fun d => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (subset_span ⟨k, rfl⟩)`.

Establish `hvec_single : ∀ k, vec (Pi.single k 1) = b k`. Introduce `k`. Simplify using `only [vec]`. Rewrite using `[Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl, map_zero, zero_smul]) (by simp)]`. Rewrite using `[Pi.single_eq_same, map_one, one_smul]`.

Establish `hvec_zero : ∀ d : Fin n → O, vec d = 0 → d = 0`. Introduce `d h`. Use `Fintype.linearIndependent_iff.1 hli (fun k => algebraMap O K (d k)) h` as an intermediate fact. Use function extensionality and compare the values at `k`. Conclude with `hinj (by simp [this k])`.

Establish `hpair : ∀ d e : Fin n → O, c * B0 (vec d) (vec e) = algebraMap O K (Matrix.vecMul d Mat ⬝ᵥ e)`. Introduce `d e`. Establish `lhs : c * B0 (vec d) (vec e) = ∑ k, ∑ l, algebraMap O K (d k) * algebraMap O K (e l) * (c * B0 (b k) (b l))`. Establish `e1 : ∀ k l, B0 (algebraMap O K (d k) • b k) (algebraMap O K (e l) • b l) = algebraMap O K (d k) * algebraMap O K (e l) * B0 (b k) (b l)`. Introduce `k l`.

Rewrite using `[LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [vec]`. Rewrite using `[map_sum B0, LinearMap.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum (B0 (algebraMap O K (d k) • b k)), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[e1]`. Expand and normalize the polynomial expressions, which then agree. Establish `rhs : algebraMap O K (Matrix.vecMul d Mat ⬝ᵥ e) = ∑ k, ∑ l, algebraMap O K (d k) * algebraMap O K (e l) * (c * B0 (b k) (b l))`.

Simplify using `only [dotProduct, Matrix.vecMul, map_sum, map_mul, Finset.sum_mul, Mat]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← hMo k l]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[lhs, rhs]`. Establish `hzero : ∀ Q ∈ span K (Set.range b), (∀ k, B0 (b k) Q = 0) → Q = 0`. Introduce `Q hQ h`. Use `hb Q hQ fun P hP => ?_` and prove the remaining obligations. Proceed by induction on `hP using Submodule.span_induction with`.

Consider the case `mem x hx => obtain ⟨k, rfl⟩ := hx`. Conclude with `h k`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul a x _ hx => simp [hx]`.

Establish `hint : ∀ Q, (∀ k, B0 (b k) Q ∈ Set.range (algebraMap O K)) → ∀ P ∈ span O (Set.range b), B0 P Q ∈ Set.range (algebraMap O K)`. Introduce `Q h P hP`. Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨k, rfl⟩ := hx`. Conclude with `h k`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨s, hs⟩` from `hx`. Take `⟨t, ht⟩` from `hy`. Conclude with `⟨s + t, by simp [hs, ht]⟩`.

Consider the case `smul a x _ hx`. Take `⟨s, hs⟩` from `hx`. Use `⟨a * s, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K a x, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, hs]`. Set `Nsub : Submodule O (Fin n → O)` to `LinearMap.range (Matrix.vecMulLinear Mat)`.

Establish `hrowd : ∀ d, Matrix.vecMul d Mat ∈ Nsub` using `fun d => LinearMap.mem_range.2 ⟨d, Matrix.vecMulLinear_apply _ _⟩`. Take `⟨n', S⟩` from `Nsub.smithNormalForm (Pi.basisFun O (Fin n))`. Set `dc : Fin n → Fin n → O` to `fun j l => S.bM.coord j (fun j' => if l = j' then 1 else 0)`. Establish `hcoord : ∀ j (r : Fin n → O), S.bM.coord j r = r ⬝ᵥ dc j`. Introduce `j r`.

Rewrite using `[LinearMap.pi_apply_eq_sum_univ]`. Simplify using `only [dotProduct, smul_eq_mul, dc]`. Establish `hBy : ∀ d j, c * B0 (vec d) (vec (dc j)) = algebraMap O K (S.bM.coord j (Matrix.vecMul d Mat))`. Introduce `d j`. Rewrite using `[hpair, hcoord]`.

Establish `hNcoord : ∀ r ∈ Nsub, ∀ j, ∃ s : Fin n' → O, S.bM.coord j r = ∑ i', s i' * S.a i' * (if S.f i' = j then 1 else 0)`. Introduce `r hr j`. Use `⟨fun i' => S.bN.repr ⟨r, hr⟩ i', ?_⟩` and prove the remaining obligations. Establish `h2 : r = ∑ i', S.bN.repr ⟨r, hr⟩ i' • (S.bN i' : Fin n → O)`. Use `congrArg Subtype.val (S.bN.sum_repr ⟨r, hr⟩)` as an intermediate fact.

Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at this`. Conclude with `this.symm`. Use `conv_lhs => rw [h2]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, S.snf, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsurj : Function.Surjective S.f`. Introduce `j`.

Assume the negation of the conclusion as `hj`. Use `push_neg at hj`. Establish `hvan : ∀ r ∈ Nsub, S.bM.coord j r = 0`. Introduce `r hr`. Take `⟨s, hs⟩` from `hNcoord r hr j`.

Rewrite using `[hs]`. Conclude with `Finset.sum_eq_zero fun i' _ => by simp [hj i']`. Establish `hy0 : vec (dc j) = 0`. Use `hzero _ (hvec_memK _) fun k => ?_` and prove the remaining obligations. Establish `h1` using `hBy (Pi.single k 1) j`.

Rewrite `h1` using `[hvec_single, hvan _ (hrowd _), map_zero]`. Conclude with `(mul_eq_zero.1 h1).resolve_left hc0`. Establish `hd0 : dc j = 0` using `hvec_zero _ hy0`. Establish `h1 : S.bM.coord j (S.bM j) = 1`. Rewrite using `[Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]`.

Rewrite `h1` using `[hcoord, hd0, dotProduct_zero]`. Conclude with `zero_ne_one h1`. Set `g` to `Equiv.ofBijective S.f ⟨S.f.injective, hsurj⟩`. Establish `hfg : ∀ i, S.f (g.symm i) = i` using `fun i => Equiv.ofBijective_apply_symm_apply _ _ i`. Establish `hpre : ∀ i : Fin n, ∃ d : Fin n → O, Matrix.vecMul d Mat = (S.bN (g.symm i) : Fin n → O)`.

Introduce `i`. Take `⟨d, hd⟩` from `LinearMap.mem_range.1 (S.bN (g.symm i)).2`. Conclude with `⟨d, by rw [← hd, Matrix.vecMulLinear_apply]⟩`. Use `choose dd hdd using hpre`. Establish `hdiag : ∀ i j, c * B0 (vec (dd i)) (vec (dc j)) = algebraMap O K (if j = i then S.a (g.symm i) else 0)`.

Introduce `i j`. Rewrite using `[hBy, hdd, S.snf, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, hfg, Finsupp.single_apply, smul_eq_mul]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`. Establish `ha0 : ∀ i, S.a (g.symm i) ≠ 0`. Introduce `i h`. Apply `S.bN.ne_zero (g.symm i)` to reduce the goal to its premises. Use `S.snf (g.symm i)` as an intermediate fact.

Rewrite `this` using `[h, zero_smul]`. Conclude with `(Submodule.coe_eq_zero).1 this`. Establish `hdvd : ∀ i, S.a (g.symm i) ∣ π ^ N`. Introduce `i`. Establish `haK : algebraMap O K (S.a (g.symm i)) ≠ 0` using `(map_ne_zero_iff _ hinj).2 (ha0 i)`.

Establish `hk : ∀ k, ∃ t : O, c * B0 (b k) (vec (dc i)) = algebraMap O K (S.a (g.symm i) * t)`. Introduce `k`. Take `⟨s, hs⟩` from `hNcoord _ (hrowd (Pi.single k 1)) i`. Use `⟨s (g.symm i), ?_⟩` and prove the remaining obligations. Rewrite using `[← hvec_single k, hBy, hs]`.

Use `congr 1`. Rewrite using `[Finset.sum_eq_single (g.symm i)]`. Rewrite using `[hfg, if_pos rfl]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i' _ hi'`.

Establish `: S.f i' ≠ i` using `fun h => hi' (S.f.injective (h.trans (hfg i).symm))`. Simplify using `[this]`. Simplify using the standard rewrite rules. Take `⟨Q, hQdef⟩ : ∃ Q : V, Q = (c / algebraMap O K (S.a (g.symm i))) • vec (dc i)` from `⟨_, rfl⟩`. Establish `hQint : ∀ k, B0 (b k) Q ∈ Set.range (algebraMap O K)`.

Introduce `k`. Take `⟨t, ht⟩` from `hk k`. Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[hQdef, LinearMap.map_smul, smul_eq_mul, div_mul_eq_mul_div, ht, map_mul, mul_div_right_comm, div_self haK, one_mul]`. Establish `hQmem : Q ∈ span O (Set.range b)` using `hc Q (hQdef ▸ Submodule.smul_mem _ _ (hvec_memK _)) (hint Q hQint)`.

Establish `hQ' : Q = ∑ k, ((c / algebraMap O K (S.a (g.symm i))) * algebraMap O K (dc i k)) • b k`. Rewrite using `[hQdef]`. Simplify using `only [vec, Finset.smul_sum, smul_smul]`. Take `⟨q, hq⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 hQmem`. Establish `hq' : ∑ k, algebraMap O K (q k) • b k = Q`.

Rewrite using `[← hq]`. Conclude with `Finset.sum_congr rfl fun k _ => algebraMap_smul K (q k) (b k)`. Establish `hlin` using `Fintype.linearIndependent_iff.1 hli (fun k => algebraMap O K (q k) - (c / algebraMap O K (S.a (g.symm i))) * algebraMap O K (dc i k)) (by simp only [sub_smul, Finset.sum_sub_distrib]; rw [hq', ← hQ', sub_self])`. Establish `h1 : S.bM.coord i (S.bM i) = 1`. Rewrite using `[Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]`.

Rewrite `h1` using `[hcoord]`. Establish `key : c / algebraMap O K (S.a (g.symm i)) = algebraMap O K (∑ k, q k * S.bM i k)`. Establish `e1 : c / algebraMap O K (S.a (g.symm i)) = c / algebraMap O K (S.a (g.symm i)) * algebraMap O K (S.bM i ⬝ᵥ dc i)`. Rewrite using `[h1, map_one, mul_one]`. Rewrite using `[e1, dotProduct, map_sum, map_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, sub_eq_zero.1 (hlin k)]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨∑ k, q k * S.bM i k, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, map_mul, ← key, ← hcdef]`.

Clear the denominators using the available nonvanishing facts. Establish `hexp : ∀ i, ∃ (m : ℕ) (v : Oˣ), S.a (g.symm i) = ↑v * w ^ m ∧ m ≤ 2 * N`. Introduce `i`. Take `⟨m, v, hv⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (ha0 i) hw`. Use `⟨m, v, hv, ?_⟩` and prove the remaining obligations.

Establish `h` using `hdvd i`. Rewrite `h` using `[hv, Units.mul_left_dvd, ← hπ, ← pow_mul]`. Conclude with `(pow_dvd_pow_iff hw.ne_zero hw.not_isUnit).1 h`. Use `choose mm uu hmu using hexp`. Use `⟨fun i => vec (dd i), fun j => algebraMap O K (↑(uu j)⁻¹ * w ^ (2 * ((mm j + 1) / 2) - mm j)) • vec (dc j), fun i => (mm i + 1) / 2, fun i => ?_, fun i => hvec_mem _, fun j => ?_, fun a' i => ?_⟩` and prove the remaining obligations.

Use `(hmu i).2 show (mm i + 1) / 2 ≤ N` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `show _ • _ ∈ _`. Rewrite using `[algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (hvec_mem _)`.

Rewrite using `[LinearMap.map_smul, smul_eq_mul, mul_left_comm, hdiag i a']`. Distinguish the cases in `h : a' = i`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, ← map_mul, ← map_pow, (hmu a').1]`. Use `congr 1`.

Establish `hm` using `(hmu a').2`. Take `⟨r, hr⟩ : ∃ r, r = 2 * ((mm a' + 1) / 2) - mm a'` from `⟨_, rfl⟩`. Rewrite using `[← hr, ← hπ, ← pow_mul, show 2 * ((mm a' + 1) / 2) = mm a' + r by omega, pow_add]`. Rewrite using `[show (↑(uu a')⁻¹ : O) * w ^ r * (↑(uu a') * w ^ mm a') = (↑(uu a')⁻¹ * ↑(uu a')) * (w ^ mm a' * w ^ r) by ring, Units.inv_mul, one_mul]`. Rewrite using `[if_neg h, if_neg h, map_zero, mul_zero]`.
-/
theorem pb_abs {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (w π : O) (hw : Irreducible w) (hπ : w ^ 2 = π) (N n : ℕ) (b : Fin n → V) (hli : LinearIndependent K b)
    (B0 : V →ₗ[K] V →ₗ[K] K)
    (hb : ∀ Q ∈ span K (Set.range b), (∀ P ∈ span K (Set.range b), B0 P Q = 0) → Q = 0)
    (hc : ∀ Q ∈ span K (Set.range b), (∀ P ∈ span O (Set.range b), B0 P Q ∈ Set.range (algebraMap O K)) →
      Q ∈ span O (Set.range b))
    (hd : ∀ Q ∈ span O (Set.range b), ∀ P ∈ span O (Set.range b),
      B0 P ((algebraMap O K π ^ N) • Q) ∈ Set.range (algebraMap O K)) :
    ∃ (x x' : Fin n → V) (ka : Fin n → ℕ), (∀ i, ka i ≤ N) ∧ (∀ i, x i ∈ span O (Set.range b)) ∧
      (∀ i, x' i ∈ span O (Set.range b)) ∧
      ∀ a' i, algebraMap O K π ^ N * B0 (x i) (x' a') = if a' = i then algebraMap O K π ^ ka i else 0 := by
  classical
  obtain ⟨c, hcdef⟩ : ∃ c : K, c = algebraMap O K π ^ N := ⟨_, rfl⟩
  rw [← hcdef] at hd
  rw [← hcdef]
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hπ0 : π ≠ 0 := by rw [← hπ]; exact pow_ne_zero _ hw.ne_zero
  have hc0 : c ≠ 0 := by rw [hcdef]; exact pow_ne_zero _ ((map_ne_zero_iff _ hinj).2 hπ0)
  have hbmem : ∀ k, b k ∈ span O (Set.range b) := fun k => subset_span ⟨k, rfl⟩
  have hMo : ∀ k l, ∃ m : O, algebraMap O K m = c * B0 (b k) (b l) := by
    intro k l
    obtain ⟨m, hm⟩ := hd (b l) (hbmem l) (b k) (hbmem k)
    exact ⟨m, by rw [hm, LinearMap.map_smul, smul_eq_mul]⟩
  choose Mo hMo using hMo
  let Mat : Matrix (Fin n) (Fin n) O := fun k l => Mo k l
  let vec : (Fin n → O) → V := fun d => ∑ k, algebraMap O K (d k) • b k
  have hvec_mem : ∀ d, vec d ∈ span O (Set.range b) := by
    intro d
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (hbmem k)
  have hvec_memK : ∀ d, vec d ∈ span K (Set.range b) := fun d =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (subset_span ⟨k, rfl⟩)
  have hvec_single : ∀ k, vec (Pi.single k 1) = b k := by
    intro k
    simp only [vec]
    rw [Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl, map_zero, zero_smul])
      (by simp)]
    rw [Pi.single_eq_same, map_one, one_smul]
  have hvec_zero : ∀ d : Fin n → O, vec d = 0 → d = 0 := by
    intro d h
    have := Fintype.linearIndependent_iff.1 hli (fun k => algebraMap O K (d k)) h
    funext k
    exact hinj (by simp [this k])
  have hpair : ∀ d e : Fin n → O, c * B0 (vec d) (vec e) = algebraMap O K (Matrix.vecMul d Mat ⬝ᵥ e) := by
    intro d e
    have lhs : c * B0 (vec d) (vec e) =
        ∑ k, ∑ l, algebraMap O K (d k) * algebraMap O K (e l) * (c * B0 (b k) (b l)) := by
      have e1 : ∀ k l, B0 (algebraMap O K (d k) • b k) (algebraMap O K (e l) • b l) =
          algebraMap O K (d k) * algebraMap O K (e l) * B0 (b k) (b l) := by
        intro k l
        rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
        ring
      simp only [vec]
      rw [map_sum B0, LinearMap.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sum (B0 (algebraMap O K (d k) • b k)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [e1]
      ring
    have rhs : algebraMap O K (Matrix.vecMul d Mat ⬝ᵥ e) =
        ∑ k, ∑ l, algebraMap O K (d k) * algebraMap O K (e l) * (c * B0 (b k) (b l)) := by
      simp only [dotProduct, Matrix.vecMul, map_sum, map_mul, Finset.sum_mul, Mat]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [← hMo k l]; ring
    rw [lhs, rhs]
  have hzero : ∀ Q ∈ span K (Set.range b), (∀ k, B0 (b k) Q = 0) → Q = 0 := by
    intro Q hQ h
    refine hb Q hQ fun P hP => ?_
    induction hP using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h k
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have hint : ∀ Q, (∀ k, B0 (b k) Q ∈ Set.range (algebraMap O K)) →
      ∀ P ∈ span O (Set.range b), B0 P Q ∈ Set.range (algebraMap O K) := by
    intro Q h P hP
    induction hP using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h k
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      exact ⟨s + t, by simp [hs, ht]⟩
    | smul a x _ hx =>
      obtain ⟨s, hs⟩ := hx
      refine ⟨a * s, ?_⟩
      rw [← algebraMap_smul K a x, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, hs]
  let Nsub : Submodule O (Fin n → O) := LinearMap.range (Matrix.vecMulLinear Mat)
  have hrowd : ∀ d, Matrix.vecMul d Mat ∈ Nsub := fun d =>
    LinearMap.mem_range.2 ⟨d, Matrix.vecMulLinear_apply _ _⟩
  obtain ⟨n', S⟩ := Nsub.smithNormalForm (Pi.basisFun O (Fin n))
  let dc : Fin n → Fin n → O := fun j l => S.bM.coord j (fun j' => if l = j' then 1 else 0)
  have hcoord : ∀ j (r : Fin n → O), S.bM.coord j r = r ⬝ᵥ dc j := by
    intro j r
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp only [dotProduct, smul_eq_mul, dc]
  have hBy : ∀ d j, c * B0 (vec d) (vec (dc j)) = algebraMap O K (S.bM.coord j (Matrix.vecMul d Mat)) := by
    intro d j
    rw [hpair, hcoord]
  have hNcoord : ∀ r ∈ Nsub, ∀ j, ∃ s : Fin n' → O,
      S.bM.coord j r = ∑ i', s i' * S.a i' * (if S.f i' = j then 1 else 0) := by
    intro r hr j
    refine ⟨fun i' => S.bN.repr ⟨r, hr⟩ i', ?_⟩
    have h2 : r = ∑ i', S.bN.repr ⟨r, hr⟩ i' • (S.bN i' : Fin n → O) := by
      have := congrArg Subtype.val (S.bN.sum_repr ⟨r, hr⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    conv_lhs => rw [h2]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [map_smul, S.snf, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      smul_eq_mul, smul_eq_mul]
    ring
  have hsurj : Function.Surjective S.f := by
    intro j
    by_contra hj
    push_neg at hj
    have hvan : ∀ r ∈ Nsub, S.bM.coord j r = 0 := by
      intro r hr
      obtain ⟨s, hs⟩ := hNcoord r hr j
      rw [hs]
      exact Finset.sum_eq_zero fun i' _ => by simp [hj i']
    have hy0 : vec (dc j) = 0 := by
      refine hzero _ (hvec_memK _) fun k => ?_
      have h1 := hBy (Pi.single k 1) j
      rw [hvec_single, hvan _ (hrowd _), map_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_left hc0
    have hd0 : dc j = 0 := hvec_zero _ hy0
    have h1 : S.bM.coord j (S.bM j) = 1 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
    rw [hcoord, hd0, dotProduct_zero] at h1
    exact zero_ne_one h1
  let g := Equiv.ofBijective S.f ⟨S.f.injective, hsurj⟩
  have hfg : ∀ i, S.f (g.symm i) = i := fun i => Equiv.ofBijective_apply_symm_apply _ _ i
  have hpre : ∀ i : Fin n, ∃ d : Fin n → O, Matrix.vecMul d Mat = (S.bN (g.symm i) : Fin n → O) := by
    intro i
    obtain ⟨d, hd⟩ := LinearMap.mem_range.1 (S.bN (g.symm i)).2
    exact ⟨d, by rw [← hd, Matrix.vecMulLinear_apply]⟩
  choose dd hdd using hpre
  have hdiag : ∀ i j, c * B0 (vec (dd i)) (vec (dc j)) =
      algebraMap O K (if j = i then S.a (g.symm i) else 0) := by
    intro i j
    rw [hBy, hdd, S.snf, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, hfg,
      Finsupp.single_apply, smul_eq_mul]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have ha0 : ∀ i, S.a (g.symm i) ≠ 0 := by
    intro i h
    apply S.bN.ne_zero (g.symm i)
    have := S.snf (g.symm i)
    rw [h, zero_smul] at this
    exact (Submodule.coe_eq_zero).1 this
  have hdvd : ∀ i, S.a (g.symm i) ∣ π ^ N := by
    intro i
    have haK : algebraMap O K (S.a (g.symm i)) ≠ 0 := (map_ne_zero_iff _ hinj).2 (ha0 i)
    have hk : ∀ k, ∃ t : O, c * B0 (b k) (vec (dc i)) = algebraMap O K (S.a (g.symm i) * t) := by
      intro k
      obtain ⟨s, hs⟩ := hNcoord _ (hrowd (Pi.single k 1)) i
      refine ⟨s (g.symm i), ?_⟩
      rw [← hvec_single k, hBy, hs]
      congr 1
      rw [Finset.sum_eq_single (g.symm i)]
      · rw [hfg, if_pos rfl]; ring
      · intro i' _ hi'
        have : S.f i' ≠ i := fun h => hi' (S.f.injective (h.trans (hfg i).symm))
        simp [this]
      · simp
    obtain ⟨Q, hQdef⟩ : ∃ Q : V, Q = (c / algebraMap O K (S.a (g.symm i))) • vec (dc i) := ⟨_, rfl⟩
    have hQint : ∀ k, B0 (b k) Q ∈ Set.range (algebraMap O K) := by
      intro k
      obtain ⟨t, ht⟩ := hk k
      refine ⟨t, ?_⟩
      rw [hQdef, LinearMap.map_smul, smul_eq_mul, div_mul_eq_mul_div, ht, map_mul, mul_div_right_comm,
        div_self haK, one_mul]
    have hQmem : Q ∈ span O (Set.range b) :=
      hc Q (hQdef ▸ Submodule.smul_mem _ _ (hvec_memK _)) (hint Q hQint)
    have hQ' : Q = ∑ k, ((c / algebraMap O K (S.a (g.symm i))) * algebraMap O K (dc i k)) • b k := by
      rw [hQdef]
      simp only [vec, Finset.smul_sum, smul_smul]
    obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hQmem
    have hq' : ∑ k, algebraMap O K (q k) • b k = Q := by
      rw [← hq]
      exact Finset.sum_congr rfl fun k _ => algebraMap_smul K (q k) (b k)
    have hlin := Fintype.linearIndependent_iff.1 hli
      (fun k => algebraMap O K (q k) - (c / algebraMap O K (S.a (g.symm i))) * algebraMap O K (dc i k))
      (by simp only [sub_smul, Finset.sum_sub_distrib]; rw [hq', ← hQ', sub_self])
    have h1 : S.bM.coord i (S.bM i) = 1 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
    rw [hcoord] at h1
    have key : c / algebraMap O K (S.a (g.symm i)) = algebraMap O K (∑ k, q k * S.bM i k) := by
      have e1 : c / algebraMap O K (S.a (g.symm i)) =
          c / algebraMap O K (S.a (g.symm i)) * algebraMap O K (S.bM i ⬝ᵥ dc i) := by
        rw [h1, map_one, mul_one]
      rw [e1, dotProduct, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_mul, sub_eq_zero.1 (hlin k)]
      ring
    refine ⟨∑ k, q k * S.bM i k, hinj ?_⟩
    rw [map_pow, map_mul, ← key, ← hcdef]
    field_simp
  have hexp : ∀ i, ∃ (m : ℕ) (v : Oˣ), S.a (g.symm i) = ↑v * w ^ m ∧ m ≤ 2 * N := by
    intro i
    obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (ha0 i) hw
    refine ⟨m, v, hv, ?_⟩
    have h := hdvd i
    rw [hv, Units.mul_left_dvd, ← hπ, ← pow_mul] at h
    exact (pow_dvd_pow_iff hw.ne_zero hw.not_isUnit).1 h
  choose mm uu hmu using hexp
  refine ⟨fun i => vec (dd i),
    fun j => algebraMap O K (↑(uu j)⁻¹ * w ^ (2 * ((mm j + 1) / 2) - mm j)) • vec (dc j),
    fun i => (mm i + 1) / 2, fun i => ?_, fun i => hvec_mem _, fun j => ?_, fun a' i => ?_⟩
  · have := (hmu i).2
    show (mm i + 1) / 2 ≤ N
    omega
  · show _ • _ ∈ _
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (hvec_mem _)
  · rw [LinearMap.map_smul, smul_eq_mul, mul_left_comm, hdiag i a']
    by_cases h : a' = i
    · subst h
      rw [if_pos rfl, if_pos rfl, ← map_mul, ← map_pow, (hmu a').1]
      congr 1
      have hm := (hmu a').2
      obtain ⟨r, hr⟩ : ∃ r, r = 2 * ((mm a' + 1) / 2) - mm a' := ⟨_, rfl⟩
      rw [← hr, ← hπ, ← pow_mul, show 2 * ((mm a' + 1) / 2) = mm a' + r by omega, pow_add]
      rw [show (↑(uu a')⁻¹ : O) * w ^ r * (↑(uu a') * w ^ mm a') =
        (↑(uu a')⁻¹ * ↑(uu a')) * (w ^ mm a' * w ^ r) by ring, Units.inv_mul, one_mul]
    · rw [if_neg h, if_neg h, map_zero, mul_zero]

end Formalism.MainNotions.flipOneThree.Pf

end
