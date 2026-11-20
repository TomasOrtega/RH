import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

/- English proof (translation)
Take `⟨W', hW'W, hW'o, h0⟩` from `mem_nhds_iff.1 hW`. Establish `hn : IsOpen ((fun p : K × K => p.1 * p.2) ⁻¹' W')` using `hW'o.preimage continuous_mul`. Take `⟨u, v, hu, -, hsu, htv, huv⟩` from `generalized_tube_lemma (isCompact_singleton (x := (0 : K))) hC hn (by`. Introduce and unpack `⟨a, b⟩ ⟨ha, -⟩`. Establish `ha' : a = 0` using `ha`.

Simplify using `[ha', h0])`. Conclude with `⟨u, hu.mem_nhds (hsu rfl), fun a ha c hc => hW'W (huv (Set.mk_mem_prod ha (htv hc)))⟩`.
-/
theorem small_mul {C : Set K} (hC : IsCompact C) {W : Set K} (hW : W ∈ 𝓝 (0 : K)) :
    ∃ U ∈ 𝓝 (0 : K), ∀ u ∈ U, ∀ c ∈ C, u * c ∈ W := by
  obtain ⟨W', hW'W, hW'o, h0⟩ := mem_nhds_iff.1 hW
  have hn : IsOpen ((fun p : K × K => p.1 * p.2) ⁻¹' W') := hW'o.preimage continuous_mul
  obtain ⟨u, v, hu, -, hsu, htv, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : K))) hC hn (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      have ha' : a = 0 := ha
      simp [ha', h0])
  exact ⟨u, hu.mem_nhds (hsu rfl), fun a ha c hc => hW'W (huv (Set.mk_mem_prod ha (htv hc)))⟩

def I (R : Subring K) (a : K) : Set K := {x | ∃ r ∈ R, x = a * r}

/- English proof (translation)
Establish `: I R a = (fun r => a * r) '' (R : Set K)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, rfl⟩`. Conclude with `⟨r, hr, rfl⟩`.

Introduce and unpack `⟨r, hr, rfl⟩`. Conclude with `⟨r, hr, rfl⟩`. Rewrite using `[this]`. Conclude with `hc.image (continuous_const.mul continuous_id)`.
-/
theorem I_compact {R : Subring K} (hc : IsCompact (R : Set K)) (a : K) : IsCompact (I R a) := by
  have : I R a = (fun r => a * r) '' (R : Set K) := by
    ext x; constructor
    · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
  rw [this]
  exact hc.image (continuous_const.mul continuous_id)

/- English proof (translation)
Establish `: I R (a : K) = (fun x => ((a⁻¹ : Kˣ) : K) * x) ⁻¹' (R : Set K)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, rfl⟩ show ((a⁻¹ : Kˣ) : K) * ((a : K) * r) ∈ R`. Simplify using `using hr`.

Introduce `hx`. Conclude with `⟨_, hx, by simp⟩`. Rewrite using `[this]`. Use `(ho.preimage (continuous_const.mul continuous_id)).mem_nhds ?_` and prove the remaining obligations. Use `show ((a⁻¹ : Kˣ) : K) * 0 ∈ R`.

Simplify using the standard rewrite rules.
-/
theorem I_nhds {R : Subring K} (ho : IsOpen (R : Set K)) (a : Kˣ) : I R (a : K) ∈ 𝓝 (0 : K) := by
  have : I R (a : K) = (fun x => ((a⁻¹ : Kˣ) : K) * x) ⁻¹' (R : Set K) := by
    ext x; constructor
    · rintro ⟨r, hr, rfl⟩
      show ((a⁻¹ : Kˣ) : K) * ((a : K) * r) ∈ R
      simpa using hr
    · intro hx
      exact ⟨_, hx, by simp⟩
  rw [this]
  refine (ho.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
  show ((a⁻¹ : Kˣ) : K) * 0 ∈ R
  simp

/- English proof (translation)
Assume the negation of the conclusion as `hx0`. Establish `hx2 : x ^ 2 ≠ 0` using `fun h => hx0 (IsNilpotent.eq_zero ⟨2, h⟩)`. Establish `hI : ∀ y : K, y * x ∈ R`. Introduce `y`. Take `⟨m, hm⟩` from `hu y`.

Take `⟨r, hr, e⟩` from `hx m`. Establish `: y * x = ϖ ^ m * y * r` using `by rw [e]; ring`. Rewrite using `[this]`. Conclude with `R.mul_mem hm hr`. Establish `hW : ({x ^ 2}ᶜ : Set K) ∈ 𝓝 (0 : K)` using `isOpen_compl_singleton.mem_nhds (by`.

Simplify using `using hx2.symm)`. Take `⟨U, hU, hUR⟩` from `small_mul hc hW`. Take `⟨U', hU', hsub⟩` from `exists_nhds_half_neg hU`. Take `⟨a, -, ha⟩` from `hc.exists_mapClusterPt (f := (atTop : Filter ℕ)) (u := fun n : ℕ => (n : K) * x) (le_principal_iff.2 (mem_map.2 (Filter.univ_mem' fun n : ℕ => hI (n : K))))`. Establish `hN : {y | y - a ∈ U'} ∈ 𝓝 a`.

Establish `: ContinuousAt (fun y : K => y - a) a` using `(continuous_id.sub continuous_const).continuousAt`. Conclude with `this.preimage_mem_nhds (by simpa using hU')`. Establish `hf` using `frequently_atTop.1 (ha.frequently hN)`. Take `⟨n, -, h1⟩` from `hf 0`. Take `⟨m, hm, h2⟩` from `hf (n + 1)`.

Establish `h3` using `hsub _ h2 _ h1`. Take `⟨d, rfl⟩ : ∃ d, m = n + 1 + d` from `⟨m - (n + 1), by omega⟩`. Establish `e : ((n + 1 + d : ℕ) : K) * x - a - ((n : K) * x - a) = ((d + 1 : ℕ) : K) * x` using `by push_cast; ring`. Rewrite `h3` using `[e]`. Take `⟨v, hv⟩` from `hn (d + 1) (by omega)`.

Establish `h4` using `hUR _ h3 _ (hI ((v⁻¹ : Kˣ) : K))`. Apply `h4` to reduce the goal to its premises. Use `show ((d + 1 : ℕ) : K) * x * (((v⁻¹ : Kˣ) : K) * x) = x ^ 2`. Rewrite using `[← hv]`. Establish `: (v : K) * ((v⁻¹ : Kˣ) : K) = 1` using `by simp`.

Take the linear combination `x ^ 2 * this`.
-/
theorem inter_zero {R : Subring K} [T2Space K] [IsReduced K] (hc : IsCompact (R : Set K))
    (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (ϖ : K) (hu : ∀ x : K, ∃ m : ℕ, ϖ ^ m * x ∈ R)
    (x : K) (hx : ∀ n, x ∈ I R (ϖ ^ n)) : x = 0 := by
  by_contra hx0
  have hx2 : x ^ 2 ≠ 0 := fun h => hx0 (IsNilpotent.eq_zero ⟨2, h⟩)
  have hI : ∀ y : K, y * x ∈ R := by
    intro y
    obtain ⟨m, hm⟩ := hu y
    obtain ⟨r, hr, e⟩ := hx m
    have : y * x = ϖ ^ m * y * r := by rw [e]; ring
    rw [this]; exact R.mul_mem hm hr
  have hW : ({x ^ 2}ᶜ : Set K) ∈ 𝓝 (0 : K) := isOpen_compl_singleton.mem_nhds (by
    simpa using hx2.symm)
  obtain ⟨U, hU, hUR⟩ := small_mul hc hW
  obtain ⟨U', hU', hsub⟩ := exists_nhds_half_neg hU
  obtain ⟨a, -, ha⟩ := hc.exists_mapClusterPt (f := (atTop : Filter ℕ)) (u := fun n : ℕ => (n : K) * x)
    (le_principal_iff.2 (mem_map.2 (Filter.univ_mem' fun n : ℕ => hI (n : K))))
  have hN : {y | y - a ∈ U'} ∈ 𝓝 a := by
    have : ContinuousAt (fun y : K => y - a) a := (continuous_id.sub continuous_const).continuousAt
    exact this.preimage_mem_nhds (by simpa using hU')
  have hf := frequently_atTop.1 (ha.frequently hN)
  obtain ⟨n, -, h1⟩ := hf 0
  obtain ⟨m, hm, h2⟩ := hf (n + 1)
  have h3 := hsub _ h2 _ h1
  obtain ⟨d, rfl⟩ : ∃ d, m = n + 1 + d := ⟨m - (n + 1), by omega⟩
  have e : ((n + 1 + d : ℕ) : K) * x - a - ((n : K) * x - a) = ((d + 1 : ℕ) : K) * x := by
    push_cast; ring
  rw [e] at h3
  obtain ⟨v, hv⟩ := hn (d + 1) (by omega)
  have h4 := hUR _ h3 _ (hI ((v⁻¹ : Kˣ) : K))
  apply h4
  show ((d + 1 : ℕ) : K) * x * (((v⁻¹ : Kˣ) : K) * x) = x ^ 2
  rw [← hv]
  have : (v : K) * ((v⁻¹ : Kˣ) : K) = 1 := by simp
  linear_combination x ^ 2 * this

structure Adic (R : Subring K) (ϖ : Kˣ) : Prop where
  t2 : T2Space K
  isOpen : IsOpen (R : Set K)
  isCompact : IsCompact (R : Set K)
  mem : (ϖ : K) ∈ R
  absorb : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R
  basis : ∀ W ∈ 𝓝 (0 : K), ∃ n : ℕ, ∀ r ∈ R, (ϖ : K) ^ n * r ∈ W

/- English proof (translation)
Take `⟨ϖ, hϖ, hu⟩` from `hD.unif`. Use `hD.t2` as an intermediate fact. Use `hD.red` as an intermediate fact. Use `⟨ϖ, hD.t2, hD.isOpen, hD.isCompact, hϖ, hu, fun W hW => ?_⟩` and prove the remaining obligations. Take `⟨W', hW'W, hW'o, h0⟩` from `mem_nhds_iff.1 hW`.

Establish `hs : IsCompact ((R : Set K) ∩ W'ᶜ)` using `hD.isCompact.inter_right hW'o.isClosed_compl`. Establish `hanti : Antitone fun n : ℕ => I R ((ϖ : K) ^ n)`. Introduce `n m hnm x hx`. Take `⟨r, hr, rfl⟩` from `hx`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hnm`.

Conclude with `⟨(ϖ : K) ^ d * r, R.mul_mem (R.pow_mem hϖ d) hr, by ring⟩`. Take `⟨n, hn'⟩` from `hs.elim_directed_family_closed (fun n : ℕ => I R ((ϖ : K) ^ n)) (fun n => (I_compact hD.isCompact _).isClosed) (by`. Rewrite using `[Set.eq_empty_iff_forall_notMem]`. Introduce and unpack `x ⟨⟨-, hxW⟩, hx⟩`. Use `inter_zero hD.isCompact hn (ϖ : K) hu x (fun n => Set.mem_iInter.1 hx n)` as an intermediate fact.

Conclude with `hxW (this ▸ h0)) hanti.directed_ge`. Use `⟨n, fun r hr => hW'W ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Establish `: (ϖ : K) ^ n * r ∈ ((R : Set K) ∩ W'ᶜ) ∩ I R ((ϖ : K) ^ n)` using `⟨⟨R.mul_mem (R.pow_mem hϖ n) hr, hc⟩, r, hr, rfl⟩`. Rewrite `this` using `[hn']`.

Conclude with `this`.
-/
theorem adic_of_datum {R : Subring K} {ψ : AddChar K ℂ} (hD : LocalDatum K R ψ)
    (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) : ∃ ϖ : Kˣ, Adic R ϖ := by
  obtain ⟨ϖ, hϖ, hu⟩ := hD.unif
  have := hD.t2
  have := hD.red
  refine ⟨ϖ, hD.t2, hD.isOpen, hD.isCompact, hϖ, hu, fun W hW => ?_⟩
  obtain ⟨W', hW'W, hW'o, h0⟩ := mem_nhds_iff.1 hW
  have hs : IsCompact ((R : Set K) ∩ W'ᶜ) := hD.isCompact.inter_right hW'o.isClosed_compl
  have hanti : Antitone fun n : ℕ => I R ((ϖ : K) ^ n) := by
    intro n m hnm x hx
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact ⟨(ϖ : K) ^ d * r, R.mul_mem (R.pow_mem hϖ d) hr, by ring⟩
  obtain ⟨n, hn'⟩ := hs.elim_directed_family_closed (fun n : ℕ => I R ((ϖ : K) ^ n))
    (fun n => (I_compact hD.isCompact _).isClosed) (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨⟨-, hxW⟩, hx⟩
      have := inter_zero hD.isCompact hn (ϖ : K) hu x (fun n => Set.mem_iInter.1 hx n)
      exact hxW (this ▸ h0)) hanti.directed_ge
  refine ⟨n, fun r hr => hW'W ?_⟩
  by_contra hc
  have : (ϖ : K) ^ n * r ∈ ((R : Set K) ∩ W'ᶜ) ∩ I R ((ϖ : K) ^ n) :=
    ⟨⟨R.mul_mem (R.pow_mem hϖ n) hr, hc⟩, r, hr, rfl⟩
  rw [hn'] at this
  exact this

variable {R : Subring K} {ϖ : Kˣ}

/- English proof (translation)
Use `h.t2` as an intermediate fact. Establish `hcl : IsClosed (f '' (R : Set K))` using `(h.isCompact.image hf).isClosed`. Establish `hb : b ∈ closure (f '' (R : Set K))`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `N hN`.

Establish `hW : {y | b + y ∈ N} ∈ 𝓝 (0 : K)`. Establish `: ContinuousAt (fun y : K => b + y) 0` using `(continuous_const.add continuous_id).continuousAt`. Conclude with `this.preimage_mem_nhds (by simpa using hN)`. Take `⟨n, hn⟩` from `h.basis _ hW`. Take `⟨r, hr, e, he, hre⟩` from `ha n`.

Conclude with `⟨f r, by rw [hre]; exact hn e he, r, hr, rfl⟩`. Rewrite `hb` using `[hcl.closure_eq]`. Take `⟨r, hr, e⟩` from `hb`. Conclude with `⟨r, hr, e⟩`.
-/
theorem Adic.approx (h : Adic R ϖ) (f : K → K) (hf : Continuous f) (b : K)
    (ha : ∀ n : ℕ, ∃ r ∈ R, ∃ e ∈ R, f r = b + (ϖ : K) ^ n * e) : ∃ r ∈ R, f r = b := by
  have := h.t2
  have hcl : IsClosed (f '' (R : Set K)) := (h.isCompact.image hf).isClosed
  have hb : b ∈ closure (f '' (R : Set K)) := by
    rw [mem_closure_iff_nhds]
    intro N hN
    have hW : {y | b + y ∈ N} ∈ 𝓝 (0 : K) := by
      have : ContinuousAt (fun y : K => b + y) 0 := (continuous_const.add continuous_id).continuousAt
      exact this.preimage_mem_nhds (by simpa using hN)
    obtain ⟨n, hn⟩ := h.basis _ hW
    obtain ⟨r, hr, e, he, hre⟩ := ha n
    exact ⟨f r, by rw [hre]; exact hn e he, r, hr, rfl⟩
  rw [hcl.closure_eq] at hb
  obtain ⟨r, hr, e⟩ := hb
  exact ⟨r, hr, e⟩

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hj`. Use `h.approx (fun v => (1 + (ϖ : K) * r) * v) (continuous_const.mul continuous_id) 1 fun n => ?_` and prove the remaining obligations. Establish `hjR : -((ϖ : K) * r) ∈ R` using `R.neg_mem (R.mul_mem h.mem hr)`. Use `⟨∑ i ∈ Finset.range n, (-((ϖ : K) * r)) ^ i, R.sum_mem fun i _ => R.pow_mem hjR i, -(-r) ^ n, R.neg_mem (R.pow_mem (R.neg_mem hr) n), ?_⟩` and prove the remaining obligations. Use `mul_neg_geom_sum (-((ϖ : K) * r)) n` as an intermediate fact.

Establish `e : (-((ϖ : K) * r)) ^ n = (ϖ : K) ^ n * (-r) ^ n` using `by rw [← mul_pow]; ring`. Use `show (1 + (ϖ : K) * r) * _ = _`. Rewrite `this` using `[e]`. Take the linear combination `this`.
-/
theorem Adic.unit_one (h : Adic R ϖ) (j : K) (hj : j ∈ I R (ϖ : K)) : ∃ v ∈ R, (1 + j) * v = 1 := by
  obtain ⟨r, hr, rfl⟩ := hj
  refine h.approx (fun v => (1 + (ϖ : K) * r) * v) (continuous_const.mul continuous_id) 1 fun n => ?_
  have hjR : -((ϖ : K) * r) ∈ R := R.neg_mem (R.mul_mem h.mem hr)
  refine ⟨∑ i ∈ Finset.range n, (-((ϖ : K) * r)) ^ i, R.sum_mem fun i _ => R.pow_mem hjR i,
    -(-r) ^ n, R.neg_mem (R.pow_mem (R.neg_mem hr) n), ?_⟩
  have := mul_neg_geom_sum (-((ϖ : K) * r)) n
  have e : (-((ϖ : K) * r)) ^ n = (ϖ : K) ^ n * (-r) ^ n := by rw [← mul_pow]; ring
  show (1 + (ϖ : K) * r) * _ = _
  rw [e] at this
  linear_combination this

def Near (R : Subring K) (a x : K) : Prop := ∃ r ∈ R, x = 1 + a * r

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, R.zero_mem, by simp⟩`.
-/
theorem near_one (a : K) : Near R a 1 := ⟨0, R.zero_mem, by simp⟩

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Take `⟨q, hq, rfl⟩` from `hy`. Conclude with `⟨r + q + a * r * q, R.add_mem (R.add_mem hr hq) (R.mul_mem (R.mul_mem ha hr) hq), by ring⟩`.
-/
theorem Near.mul {a x y : K} (ha : a ∈ R) (hx : Near R a x) (hy : Near R a y) : Near R a (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨r + q + a * r * q, R.add_mem (R.add_mem hr hq) (R.mul_mem (R.mul_mem ha hr) hq), by ring⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using near_one a`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul ha hx`.
-/
theorem Near.pow {a x : K} (ha : a ∈ R) (hx : Near R a x) (n : ℕ) : Near R a (x ^ n) := by
  induction n with
  | zero => simpa using near_one a
  | succ n ih => rw [pow_succ]; exact ih.mul ha hx

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Take `⟨a', ha', rfl⟩` from `ha`. Take `⟨v, hv, e⟩` from `h.unit_one ((ϖ : K) * a' * r) ⟨a' * r, R.mul_mem ha' hr, by ring⟩`. Conclude with `⟨v, e, ⟨-(r * v), R.neg_mem (R.mul_mem hr hv), by linear_combination e⟩, hv⟩`.
-/
theorem Adic.near_inv (h : Adic R ϖ) {a x : K} (ha : a ∈ I R (ϖ : K)) (hx : Near R a x) :
    ∃ v, x * v = 1 ∧ Near R a v ∧ v ∈ R := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨v, hv, e⟩ := h.unit_one ((ϖ : K) * a' * r) ⟨a' * r, R.mul_mem ha' hr, by ring⟩
  exact ⟨v, e, ⟨-(r * v), R.neg_mem (R.mul_mem hr hv), by linear_combination e⟩, hv⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, R.zero_mem, by simp⟩`. Consider the case `succ n ih`. Take `⟨q, hq, e⟩` from `ih`. Take `⟨r, hr, e'⟩` from `hf n`.

Conclude with `⟨q + r, R.add_mem hq hr, by rw [Finset.sum_range_succ, e, e']; push_cast; ring⟩`.
-/
theorem near_sum {a : K} (n : ℕ) (f : ℕ → K) (hf : ∀ i, Near R a (f i)) :
    ∃ q ∈ R, ∑ i ∈ Finset.range n, f i = (n : K) + a * q := by
  induction n with
  | zero => exact ⟨0, R.zero_mem, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq, e⟩ := ih
    obtain ⟨r, hr, e'⟩ := hf n
    exact ⟨q + r, R.add_mem hq hr, by rw [Finset.sum_range_succ, e, e']; push_cast; ring⟩

/- English proof (translation)
Establish `ha : (s : K) * c ∈ R` using `R.mul_mem (natCast_mem R s) hc`. Take `⟨q, hq, e⟩` from `near_sum (R := R) s (fun i => x ^ i * y ^ (s - 1 - i)) (fun i => (hx.pow ha i).mul ha (hy.pow ha _))`. Use `⟨q, hq, ?_⟩` and prove the remaining obligations. Rewrite using `[← geom_sum₂_mul, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_diff {c : K} (hc : c ∈ R) (s : ℕ) {x y : K} (hx : Near R ((s : K) * c) x)
    (hy : Near R ((s : K) * c) y) : ∃ q ∈ R, x ^ s - y ^ s = (s : K) * (x - y) * (1 + c * q) := by
  have ha : (s : K) * c ∈ R := R.mul_mem (natCast_mem R s) hc
  obtain ⟨q, hq, e⟩ := near_sum (R := R) s (fun i => x ^ i * y ^ (s - 1 - i))
    (fun i => (hx.pow ha i).mul ha (hy.pow ha _))
  refine ⟨q, hq, ?_⟩
  rw [← geom_sum₂_mul, e]; ring

/- English proof (translation)
Take `⟨c', hc', hcc⟩` from `hc`. Establish `hcR : c ∈ R` using `by rw [hcc]; exact R.mul_mem h.mem hc'`. Establish `key : ∀ k : ℕ, ∃ r ∈ R, ∃ e ∈ R, (1 + (s : K) * c * r) ^ s = b + (s : K) ^ 2 * c ^ (k + 1) * e`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Take `⟨r0, hr0, e0⟩` from `hb`. Conclude with `⟨0, R.zero_mem, -r0, R.neg_mem hr0, by rw [e0]; simp⟩`. Consider the case `succ k ih`. Take `⟨r, hr, e, he, hre⟩` from `ih`.

Establish `hr' : r - c ^ k * e ∈ R` using `R.sub_mem hr (R.mul_mem (R.pow_mem hcR k) he)`. Take `⟨q, hq, hd⟩` from `pow_diff (R := R) hcR s (x := 1 + (s : K) * c * (r - c ^ k * e)) (y := 1 + (s : K) * c * r) ⟨_, hr', rfl⟩ ⟨_, hr, rfl⟩`. Use `⟨_, hr', -(e * q), R.neg_mem (R.mul_mem he hq), ?_⟩` and prove the remaining obligations. Take the linear combination `hd + hre`. Take `⟨r, hr, e⟩` from `h.approx (fun r => (1 + (s : K) * c * r) ^ s) ((continuous_const.add (continuous_const.mul continuous_id)).pow s) b (fun n => by`.

Take `⟨r, hr, e, he, hre⟩` from `key n`. Use `⟨r, hr, (s : K) ^ 2 * ((ϖ : K) * c' ^ (n + 1)) * e, R.mul_mem (R.mul_mem (R.pow_mem (natCast_mem R s) 2) (R.mul_mem h.mem (R.pow_mem hc' _))) he, ?_⟩` and prove the remaining obligations. Use `show (1 + (s : K) * c * r) ^ s = _`. Rewrite using `[hre, hcc]`. Use the proof step `ring)`.

Conclude with `⟨_, ⟨r, hr, rfl⟩, e⟩`.
-/
theorem Adic.root (h : Adic R ϖ) (s : ℕ) {c : K} (hc : c ∈ I R (ϖ : K)) {b : K}
    (hb : Near R ((s : K) ^ 2 * c) b) : ∃ κ, Near R ((s : K) * c) κ ∧ κ ^ s = b := by
  obtain ⟨c', hc', hcc⟩ := hc
  have hcR : c ∈ R := by rw [hcc]; exact R.mul_mem h.mem hc'
  have key : ∀ k : ℕ, ∃ r ∈ R, ∃ e ∈ R, (1 + (s : K) * c * r) ^ s = b + (s : K) ^ 2 * c ^ (k + 1) * e := by
    intro k
    induction k with
    | zero =>
      obtain ⟨r0, hr0, e0⟩ := hb
      exact ⟨0, R.zero_mem, -r0, R.neg_mem hr0, by rw [e0]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr, e, he, hre⟩ := ih
      have hr' : r - c ^ k * e ∈ R := R.sub_mem hr (R.mul_mem (R.pow_mem hcR k) he)
      obtain ⟨q, hq, hd⟩ := pow_diff (R := R) hcR s (x := 1 + (s : K) * c * (r - c ^ k * e))
        (y := 1 + (s : K) * c * r) ⟨_, hr', rfl⟩ ⟨_, hr, rfl⟩
      refine ⟨_, hr', -(e * q), R.neg_mem (R.mul_mem he hq), ?_⟩
      linear_combination hd + hre
  obtain ⟨r, hr, e⟩ := h.approx (fun r => (1 + (s : K) * c * r) ^ s)
    ((continuous_const.add (continuous_const.mul continuous_id)).pow s) b (fun n => by
      obtain ⟨r, hr, e, he, hre⟩ := key n
      refine ⟨r, hr, (s : K) ^ 2 * ((ϖ : K) * c' ^ (n + 1)) * e,
        R.mul_mem (R.mul_mem (R.pow_mem (natCast_mem R s) 2)
          (R.mul_mem h.mem (R.pow_mem hc' _))) he, ?_⟩
      show (1 + (s : K) * c * r) ^ s = _
      rw [hre, hcc]; ring)
  exact ⟨_, ⟨r, hr, rfl⟩, e⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `hC.elim_directed_cover (fun a : ℕ => {x : K | (ϖ : K) ^ a * x ∈ R}) (fun a => h.isOpen.preimage (continuous_const.mul continuous_id)) (fun x _ => by`. Take `⟨m, hm⟩` from `h.absorb x`. Conclude with `Set.mem_iUnion.2 ⟨m, hm⟩)`. Use the proof step `(Monotone.directed_le (by`. Introduce `a b hab x hx`.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hab`. Establish `: (ϖ : K) ^ (a + d) * x = (ϖ : K) ^ d * ((ϖ : K) ^ a * x)` using `by ring`. Use `show (ϖ : K) ^ (a + d) * x ∈ R`. Rewrite using `[this]`. Conclude with `R.mul_mem (R.pow_mem h.mem d) hx))`.

Conclude with `⟨a, fun x hx => ha hx⟩`.
-/
theorem Adic.bounded (h : Adic R ϖ) {C : Set K} (hC : IsCompact C) :
    ∃ a : ℕ, ∀ x ∈ C, (ϖ : K) ^ a * x ∈ R := by
  obtain ⟨a, ha⟩ := hC.elim_directed_cover (fun a : ℕ => {x : K | (ϖ : K) ^ a * x ∈ R})
    (fun a => h.isOpen.preimage (continuous_const.mul continuous_id))
    (fun x _ => by
      obtain ⟨m, hm⟩ := h.absorb x
      exact Set.mem_iUnion.2 ⟨m, hm⟩)
    (Monotone.directed_le (by
      intro a b hab x hx
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      have : (ϖ : K) ^ (a + d) * x = (ϖ : K) ^ d * ((ϖ : K) ^ a * x) := by ring
      show (ϖ : K) ^ (a + d) * x ∈ R
      rw [this]; exact R.mul_mem (R.pow_mem h.mem d) hx))
  exact ⟨a, fun x hx => ha hx⟩

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using near_one a`. Consider the case `insert i S hi ih`. Rewrite using `[Finset.prod_insert hi]`. Conclude with `(hf i (Finset.mem_insert_self _ _)).mul ha (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))`.
-/
theorem Near.prod {ι : Type} {a : K} (ha : a ∈ R) (S : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ S, Near R a (f i)) : Near R a (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using near_one a
  | insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul ha (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Take `⟨b, hb⟩` from `h.basis _ hB`. Take `⟨v, hv⟩` from `hn (m + 1) (by omega)`. Take `⟨e, he⟩` from `h.absorb (((v⁻¹ : Kˣ) : K) ^ 2)`. Use `⟨a + b + 1 + e, fun D x xi hx hxa hg => ?_⟩` and prove the remaining obligations. Take `⟨πi, hπ⟩ : ∃ p : K, p = ∏ i, xi i` from `⟨_, rfl⟩`.

Take `⟨π, hπx⟩ : ∃ p : K, p = ∏ i, x i` from `⟨_, rfl⟩`. Rewrite `hg` using `[← hπ]`. Establish `hvv : ((m + 1 : ℕ) : K) * ((v⁻¹ : Kˣ) : K) = 1` using `by rw [← hv]; simp`. Establish `hϖj : (ϖ : K) ^ (a + b + 1 + e) ∈ R` using `R.pow_mem h.mem _`. Establish `hck : ∀ k, Near R ((ϖ : K) ^ (a + b + 1 + e)) ((D : K) * (xi k * πi))`.

Introduce `k`. Take `⟨r, hr, e1⟩` from `hg k`. Conclude with `⟨-r, R.neg_mem hr, by linear_combination -e1⟩`. Take `⟨r0, hr0, e0⟩` from `Near.prod hϖj Finset.univ (fun k => (D : K) * (xi k * πi)) (fun k _ => hck k)`. Establish `hb1 : Near R (((m + 1 : ℕ) : K) ^ 2 * (ϖ : K) ^ (a + b + 1)) (∏ k, (D : K) * (xi k * πi))` using `⟨(ϖ : K) ^ e * ((v⁻¹ : Kˣ) : K) ^ 2 * r0, R.mul_mem he hr0, by`.

Rewrite using `[e0]`. Establish `: ((m + 1 : ℕ) : K) ^ 2 * ((v⁻¹ : Kˣ) : K) ^ 2 = 1` using `by rw [← mul_pow, hvv, one_pow]`. Rewrite using `[pow_add (ϖ : K) (a + b + 1) e]`. Take the linear combination `(-(ϖ : K) ^ (a + b + 1) * (ϖ : K) ^ e * r0) * this⟩`. Establish `hcI : (ϖ : K) ^ (a + b + 1) ∈ I R (ϖ : K)` using `⟨(ϖ : K) ^ (a + b), R.pow_mem h.mem _, by ring⟩`.

Take `⟨κ, hκ, hκs⟩` from `h.root (m + 1) hcI hb1`. Establish `hscI : ((m + 1 : ℕ) : K) * (ϖ : K) ^ (a + b + 1) ∈ I R (ϖ : K)` using `⟨((m + 1 : ℕ) : K) * (ϖ : K) ^ (a + b), R.mul_mem (natCast_mem R (m + 1)) (R.pow_mem h.mem _), by ring⟩`. Take `⟨w, hκw, -, hw⟩` from `h.near_inv hscI hκ`. Establish `hprod : ∏ k, (D : K) * (xi k * πi) = (D : K) ^ m * πi ^ (m + 1)`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← hπ]`.

Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree. Establish `hππ : π * πi = 1`. Rewrite using `[hπ, hπx, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => hx k`.

Establish `hDD : (D : K) * ((D⁻¹ : Kˣ) : K) = 1` using `by simp`. Establish `hz1 : (D : K) * πi * w * (((D⁻¹ : Kˣ) : K) * π * κ) = 1`. Take the linear combination `(π * πi * κ * w) * hDD + (κ * w) * hππ + hκw`. Use `⟨⟨(D : K) * πi * w, ((D⁻¹ : Kˣ) : K) * π * κ, hz1, by rw [mul_comm]; exact hz1⟩, ?_, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_pow_eq_pow_val]`. Use `show ((D : K) * πi * w) ^ (m + 1) = (D : K)`. Establish `h1 : κ ^ (m + 1) * w ^ (m + 1) = 1` using `by rw [← mul_pow, hκw, one_pow]`. Rewrite `h1` using `[hκs, hprod]`. Take the linear combination `(D : K) * h1`.

Introduce `k show x k - (D : K) * πi * w ∈ B`. Take `⟨r1, hr1, eκ⟩` from `hκ`. Take `⟨rk, hrk, ek⟩` from `hck k`. Establish `: x k - (D : K) * πi * w = (ϖ : K) ^ b * (((ϖ : K) ^ a * x k) * w * (((m + 1 : ℕ) : K) * (ϖ : K) * r1 - (ϖ : K) ^ (1 + e) * rk))`. Take the linear combination `(-x k) * hκw + ((D : K) * πi * w) * hx k + (x k * w) * eκ - (x k * w) * ek`.

Rewrite using `[this]`. Conclude with `hb _ (R.mul_mem (R.mul_mem (hxa k) hw) (R.sub_mem (R.mul_mem (R.mul_mem (natCast_mem R (m + 1)) h.mem) hr1) (R.mul_mem (R.pow_mem h.mem _) hrk)))`.
-/
theorem Adic.crit (h : Adic R ϖ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (m a : ℕ)
    (B : AddSubgroup K) (hB : (B : Set K) ∈ 𝓝 (0 : K)) :
    ∃ j : ℕ, ∀ (D : Kˣ) (x xi : Fin m → K), (∀ k, x k * xi k = 1) →
      (∀ k, (ϖ : K) ^ a * x k ∈ R) →
      (∀ k, 1 - (D : K) * (xi k * ∏ i, xi i) ∈ I R ((ϖ : K) ^ j)) →
      ∃ z : Kˣ, z ^ (m + 1) = D ∧ ∀ k, x k - (z : K) ∈ B := by
  obtain ⟨b, hb⟩ := h.basis _ hB
  obtain ⟨v, hv⟩ := hn (m + 1) (by omega)
  obtain ⟨e, he⟩ := h.absorb (((v⁻¹ : Kˣ) : K) ^ 2)
  refine ⟨a + b + 1 + e, fun D x xi hx hxa hg => ?_⟩
  obtain ⟨πi, hπ⟩ : ∃ p : K, p = ∏ i, xi i := ⟨_, rfl⟩
  obtain ⟨π, hπx⟩ : ∃ p : K, p = ∏ i, x i := ⟨_, rfl⟩
  rw [← hπ] at hg
  have hvv : ((m + 1 : ℕ) : K) * ((v⁻¹ : Kˣ) : K) = 1 := by rw [← hv]; simp
  have hϖj : (ϖ : K) ^ (a + b + 1 + e) ∈ R := R.pow_mem h.mem _
  have hck : ∀ k, Near R ((ϖ : K) ^ (a + b + 1 + e)) ((D : K) * (xi k * πi)) := by
    intro k
    obtain ⟨r, hr, e1⟩ := hg k
    exact ⟨-r, R.neg_mem hr, by linear_combination -e1⟩
  obtain ⟨r0, hr0, e0⟩ := Near.prod hϖj Finset.univ (fun k => (D : K) * (xi k * πi)) (fun k _ => hck k)
  have hb1 : Near R (((m + 1 : ℕ) : K) ^ 2 * (ϖ : K) ^ (a + b + 1)) (∏ k, (D : K) * (xi k * πi)) :=
    ⟨(ϖ : K) ^ e * ((v⁻¹ : Kˣ) : K) ^ 2 * r0, R.mul_mem he hr0, by
      rw [e0]
      have : ((m + 1 : ℕ) : K) ^ 2 * ((v⁻¹ : Kˣ) : K) ^ 2 = 1 := by rw [← mul_pow, hvv, one_pow]
      rw [pow_add (ϖ : K) (a + b + 1) e]
      linear_combination (-(ϖ : K) ^ (a + b + 1) * (ϖ : K) ^ e * r0) * this⟩
  have hcI : (ϖ : K) ^ (a + b + 1) ∈ I R (ϖ : K) := ⟨(ϖ : K) ^ (a + b), R.pow_mem h.mem _, by ring⟩
  obtain ⟨κ, hκ, hκs⟩ := h.root (m + 1) hcI hb1
  have hscI : ((m + 1 : ℕ) : K) * (ϖ : K) ^ (a + b + 1) ∈ I R (ϖ : K) :=
    ⟨((m + 1 : ℕ) : K) * (ϖ : K) ^ (a + b),
      R.mul_mem (natCast_mem R (m + 1)) (R.pow_mem h.mem _), by ring⟩
  obtain ⟨w, hκw, -, hw⟩ := h.near_inv hscI hκ
  have hprod : ∏ k, (D : K) * (xi k * πi) = (D : K) ^ m * πi ^ (m + 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← hπ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hππ : π * πi = 1 := by
    rw [hπ, hπx, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => hx k
  have hDD : (D : K) * ((D⁻¹ : Kˣ) : K) = 1 := by simp
  have hz1 : (D : K) * πi * w * (((D⁻¹ : Kˣ) : K) * π * κ) = 1 := by
    linear_combination (π * πi * κ * w) * hDD + (κ * w) * hππ + hκw
  refine ⟨⟨(D : K) * πi * w, ((D⁻¹ : Kˣ) : K) * π * κ, hz1, by rw [mul_comm]; exact hz1⟩, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    show ((D : K) * πi * w) ^ (m + 1) = (D : K)
    have h1 : κ ^ (m + 1) * w ^ (m + 1) = 1 := by rw [← mul_pow, hκw, one_pow]
    rw [hκs, hprod] at h1
    linear_combination (D : K) * h1
  · intro k
    show x k - (D : K) * πi * w ∈ B
    obtain ⟨r1, hr1, eκ⟩ := hκ
    obtain ⟨rk, hrk, ek⟩ := hck k
    have : x k - (D : K) * πi * w = (ϖ : K) ^ b * (((ϖ : K) ^ a * x k) * w *
        (((m + 1 : ℕ) : K) * (ϖ : K) * r1 - (ϖ : K) ^ (1 + e) * rk)) := by
      linear_combination (-x k) * hκw + ((D : K) * πi * w) * hx k + (x k * w) * eκ - (x k * w) * ek
    rw [this]
    exact hb _ (R.mul_mem (R.mul_mem (hxa k) hw) (R.sub_mem
      (R.mul_mem (R.mul_mem (natCast_mem R (m + 1)) h.mem) hr1)
      (R.mul_mem (R.pow_mem h.mem _) hrk)))

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨0, R.zero_mem, 0, R.zero_mem, by simp, by simp⟩`. Consider the case `insert i S hi ih`. Take `⟨ρ, hρ, σ, hσ, e1, e2⟩` from `ih (fun k hk => hu k (Finset.mem_insert_of_mem hk)) (fun k hk => hw k (Finset.mem_insert_of_mem hk))`. Take `⟨ρi, hρi, e3⟩` from `hu i (Finset.mem_insert_self _ _)`.

Take `⟨ei, hei, e4⟩` from `hw i (Finset.mem_insert_self _ _)`. Use `⟨ρi * σ + ρ - μ * ρi * ρ + ei * (1 - μ * σ + μ ^ 2 * ρ), ?_, ρi + σ, R.add_mem hρi hσ, ?_, ?_⟩` and prove the remaining obligations. Conclude with `R.add_mem (R.sub_mem (R.add_mem (R.mul_mem hρi hσ) hρ) (R.mul_mem (R.mul_mem hμ hρi) hρ)) (R.mul_mem hei (R.add_mem (R.sub_mem R.one_mem (R.mul_mem hμ hσ)) (R.mul_mem (R.pow_mem hμ 2) hρ)))`. Rewrite using `[Finset.sum_insert hi, e1, e3]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_insert hi, Finset.prod_insert hi, e2, e4, e1, e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_expand {ι : Type} {μ : K} (hμ : μ ∈ R) (S : Finset ι) (w u : ι → K)
    (hu : ∀ i ∈ S, ∃ ρ ∈ R, u i = μ * ρ) (hw : ∀ i ∈ S, ∃ e ∈ R, w i = 1 - u i + μ ^ 2 * e) :
    ∃ ρ ∈ R, ∃ σ ∈ R, ∑ i ∈ S, u i = μ * σ ∧ ∏ i ∈ S, w i = 1 - ∑ i ∈ S, u i + μ ^ 2 * ρ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, R.zero_mem, 0, R.zero_mem, by simp, by simp⟩
  | insert i S hi ih =>
    obtain ⟨ρ, hρ, σ, hσ, e1, e2⟩ := ih (fun k hk => hu k (Finset.mem_insert_of_mem hk))
      (fun k hk => hw k (Finset.mem_insert_of_mem hk))
    obtain ⟨ρi, hρi, e3⟩ := hu i (Finset.mem_insert_self _ _)
    obtain ⟨ei, hei, e4⟩ := hw i (Finset.mem_insert_self _ _)
    refine ⟨ρi * σ + ρ - μ * ρi * ρ + ei * (1 - μ * σ + μ ^ 2 * ρ), ?_, ρi + σ, R.add_mem hρi hσ, ?_, ?_⟩
    · exact R.add_mem (R.sub_mem (R.add_mem (R.mul_mem hρi hσ) hρ) (R.mul_mem (R.mul_mem hμ hρi) hρ))
        (R.mul_mem hei (R.add_mem (R.sub_mem R.one_mem (R.mul_mem hμ hσ))
          (R.mul_mem (R.pow_mem hμ 2) hρ)))
    · rw [Finset.sum_insert hi, e1, e3]; ring
    · rw [Finset.sum_insert hi, Finset.prod_insert hi, e2, e4, e1, e3]; ring

/- English proof (translation)
Use `Ring.inverse_unit (⟨a, b, h, by rw [mul_comm]; exact h⟩ : Kˣ)` as an intermediate fact. Simplify using `using this`.
-/
theorem inverse_eq {a b : K} (h : a * b = 1) : Ring.inverse a = b := by
  have := Ring.inverse_unit (⟨a, b, h, by rw [mul_comm]; exact h⟩ : Kˣ)
  simpa using this

/- English proof (translation)
Take `⟨μ', hμ', eμ⟩` from `hμ`. Establish `hμR : μ ∈ R` using `by rw [eμ]; exact R.mul_mem h.mem hμ'`. Establish `hu : ∀ k, ∃ ρ ∈ R, v k * xi k = μ * ρ`. Introduce `k`. Take `⟨r, hr, e⟩` from `hv k`.

Conclude with `⟨r * ((ϖ : K) ^ a * xi k), R.mul_mem hr (hxi k), by rw [e]; ring⟩`. Establish `hw : ∀ k, ∃ w ∈ R, (1 + v k * xi k) * w = 1`. Introduce `k`. Take `⟨ρ, hρ, e⟩` from `hu k`. Conclude with `h.unit_one _ ⟨μ' * ρ, R.mul_mem hμ' hρ, by rw [e, eμ]; ring⟩`.

Use `choose w hwR hw1 using hw`. Establish `hw2 : ∀ k, ∃ e ∈ R, w k = 1 - v k * xi k + μ ^ 2 * e`. Introduce `k`. Take `⟨ρ, hρ, e⟩` from `hu k`. Use `⟨ρ ^ 2 * w k, R.mul_mem (R.pow_mem hρ 2) (hwR k), ?_⟩` and prove the remaining obligations.

Establish `e2 : μ ^ 2 * (ρ ^ 2 * w k) = (v k * xi k) ^ 2 * w k` using `by rw [e]; ring`. Rewrite using `[e2]`. Take the linear combination `(1 - v k * xi k) * hw1 k`. Take `⟨ρ, hρ, -, -, -, e2⟩` from `prod_expand hμR Finset.univ w (fun k => v k * xi k) (fun k _ => hu k) (fun k _ => hw2 k)`. Use `⟨ρ, hρ, ?_⟩` and prove the remaining obligations.

Establish `i1 : Ring.inverse (∏ k, x k) = ∏ i, xi i` using `inverse_eq (by`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => hx k)`. Establish `i2 : Ring.inverse (∏ k, (x + v) k) = (∏ i, xi i) * ∏ i, w i` using `inverse_eq (by`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Use `show (x k + v k) * (xi k * w k) = 1`. Take the linear combination `hw1 k + w k * hx k)`. Establish `s1 : ∑ k, v k * (1 - D * (xi k * ∏ i, xi i)) = ∑ k, v k - D * (∏ i, xi i) * ∑ k, v k * xi k`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Establish `s2 : ∑ k, (x + v) k = ∑ k, x k + ∑ k, v k`. Rewrite using `[← Finset.sum_add_distrib]`. Both sides reduce to the same expression. Unfold `g0`.

Rewrite using `[i1, i2, s1, s2, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Adic.taylor (h : Adic R ϖ) (m a : ℕ) (D : K) (x xi v : Fin m → K) (μ : K)
    (hμ : μ ∈ I R (ϖ : K)) (hx : ∀ k, x k * xi k = 1) (hxi : ∀ k, (ϖ : K) ^ a * xi k ∈ R)
    (hv : ∀ k, ∃ r ∈ R, v k = (ϖ : K) ^ a * μ * r) :
    ∃ ρ ∈ R, g0 D (x + v) = g0 D x + ∑ k, v k * (1 - D * (xi k * ∏ i, xi i)) +
      D * (∏ i, xi i) * μ ^ 2 * ρ := by
  obtain ⟨μ', hμ', eμ⟩ := hμ
  have hμR : μ ∈ R := by rw [eμ]; exact R.mul_mem h.mem hμ'
  have hu : ∀ k, ∃ ρ ∈ R, v k * xi k = μ * ρ := by
    intro k
    obtain ⟨r, hr, e⟩ := hv k
    exact ⟨r * ((ϖ : K) ^ a * xi k), R.mul_mem hr (hxi k), by rw [e]; ring⟩
  have hw : ∀ k, ∃ w ∈ R, (1 + v k * xi k) * w = 1 := by
    intro k
    obtain ⟨ρ, hρ, e⟩ := hu k
    exact h.unit_one _ ⟨μ' * ρ, R.mul_mem hμ' hρ, by rw [e, eμ]; ring⟩
  choose w hwR hw1 using hw
  have hw2 : ∀ k, ∃ e ∈ R, w k = 1 - v k * xi k + μ ^ 2 * e := by
    intro k
    obtain ⟨ρ, hρ, e⟩ := hu k
    refine ⟨ρ ^ 2 * w k, R.mul_mem (R.pow_mem hρ 2) (hwR k), ?_⟩
    have e2 : μ ^ 2 * (ρ ^ 2 * w k) = (v k * xi k) ^ 2 * w k := by rw [e]; ring
    rw [e2]
    linear_combination (1 - v k * xi k) * hw1 k
  obtain ⟨ρ, hρ, -, -, -, e2⟩ := prod_expand hμR Finset.univ w (fun k => v k * xi k)
    (fun k _ => hu k) (fun k _ => hw2 k)
  refine ⟨ρ, hρ, ?_⟩
  have i1 : Ring.inverse (∏ k, x k) = ∏ i, xi i := inverse_eq (by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun k _ => hx k)
  have i2 : Ring.inverse (∏ k, (x + v) k) = (∏ i, xi i) * ∏ i, w i := inverse_eq (by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    show (x k + v k) * (xi k * w k) = 1
    linear_combination hw1 k + w k * hx k)
  have s1 : ∑ k, v k * (1 - D * (xi k * ∏ i, xi i)) =
      ∑ k, v k - D * (∏ i, xi i) * ∑ k, v k * xi k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have s2 : ∑ k, (x + v) k = ∑ k, x k + ∑ k, v k := by
    rw [← Finset.sum_add_distrib]; rfl
  unfold g0
  rw [i1, i2, s1, s2, e2]
  ring

end Top

section Avg

/- English proof (translation)
Use `⟨Quotient.out (y + (v : G ⧸ Λ)) - Quotient.out y - v, ?_, by abel⟩` and prove the remaining obligations. Rewrite using `[← QuotientAddGroup.eq_zero_iff]`. Simplify using `[QuotientAddGroup.mk_sub]`.
-/
theorem out_add {G : Type} [AddCommGroup G] (Λ : AddSubgroup G) (y : G ⧸ Λ) (v : G) :
    ∃ l ∈ Λ, (Quotient.out (y + (v : G ⧸ Λ)) : G) = Quotient.out y + v + l := by
  refine ⟨Quotient.out (y + (v : G ⧸ Λ)) - Quotient.out y - v, ?_, by abel⟩
  rw [← QuotientAddGroup.eq_zero_iff]
  simp [QuotientAddGroup.mk_sub]

variable {K : Type} [CommRing K]

def Osc (N : AddSubgroup K) {d : ℕ} (F : (Fin d → K) → ℂ) (x : Fin d → K) : Prop :=
  (∀ v : Fin d → K, (∀ i, v i ∈ N) → F (x + v) = 0) ∨
    ∃ k : Fin d, ∃ n₀ ∈ N, ∃ c : ℂ, c ≠ 1 ∧ ∀ v : Fin d → K, (∀ i, v i ∈ N) →
      F (x + v + Pi.single k n₀) = c * F (x + v)

/- English proof (translation)
Break down `hx with hx | ⟨k, n₀, hn₀, c, hc, hx⟩` into its components or cases. Conclude with `Finset.sum_eq_zero fun h _ => hx _ fun i => (Quotient.out (h i) : N).2`. Take `⟨Φ, hΦ⟩ : ∃ Φ : (Fin d → N ⧸ Λ.addSubgroupOf N) → ℂ, Φ = fun h => F (x + fun i => ((Quotient.out (h i) : N) : K))` from `⟨_, rfl⟩`. Take `⟨q, hq⟩ : ∃ q : Fin d → N ⧸ Λ.addSubgroupOf N, q = fun i => (((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i : N) : N ⧸ Λ.addSubgroupOf N)` from `⟨_, rfl⟩`. Establish `key : ∀ h, Φ (h + q) = c * Φ h`.

Introduce `h`. Rewrite using `[hΦ]`. Use `show F _ = c * F _`. Rewrite using `[← hx _ (fun i => (Quotient.out (h i) : N).2)]`. Establish `: ∀ i, ∃ l ∈ Λ, ((Quotient.out ((h + q) i) : N) : K) = ((Quotient.out (h i) : N) : K) + (Pi.single k n₀ : Fin d → K) i + l`.

Introduce `i`. Take `⟨l, hl, e⟩` from `out_add (Λ.addSubgroupOf N) (h i) ((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i)`. Use `⟨(l : K), AddSubgroup.mem_addSubgroupOf.1 hl, ?_⟩` and prove the remaining obligations. Establish `e' : (h + q) i = h i + (((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i : N) : N ⧸ Λ.addSubgroupOf N)` using `by rw [hq]; rfl`. Rewrite using `[e', e]`.

Establish `e'' : (((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i : N) : K) = (Pi.single k n₀ : Fin d → K) i`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hik]`.

Use `push_cast`. Rewrite using `[e'']`. Use `choose l hl el using this`. Establish `e : (x + fun i => ((Quotient.out ((h + q) i) : N) : K)) = (x + (fun i => ((Quotient.out (h i) : N) : K)) + Pi.single k n₀) + l`. Use extensionality with `i`.

Establish `e0` using `el i`. Simplify using `only [Pi.add_apply] at e0 ⊢`. Rewrite using `[e0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hF _ l hl]`.

Establish `e` using `Equiv.sum_comp (Equiv.addRight q) Φ`. Simplify using `only [Equiv.coe_addRight, key] at e`. Rewrite `e` using `[← Finset.mul_sum]`. Establish `e2 : (c - 1) * ∑ h, Φ h = 0` using `by linear_combination e`. Rewrite `e2` using `[hΦ]`.

Break down `mul_eq_zero.1 e2 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h) hc`. Conclude with `h`.
-/
theorem local_zero (Λ N : AddSubgroup K) [Fintype (N ⧸ Λ.addSubgroupOf N)] {d : ℕ}
    (F : (Fin d → K) → ℂ) (hF : LatInvN Λ F) (x : Fin d → K) (hx : Osc N F x) :
    ∑ h : Fin d → N ⧸ Λ.addSubgroupOf N, F (x + fun i => ((Quotient.out (h i) : N) : K)) = 0 := by
  classical
  rcases hx with hx | ⟨k, n₀, hn₀, c, hc, hx⟩
  · exact Finset.sum_eq_zero fun h _ => hx _ fun i => (Quotient.out (h i) : N).2
  · obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin d → N ⧸ Λ.addSubgroupOf N) → ℂ,
        Φ = fun h => F (x + fun i => ((Quotient.out (h i) : N) : K)) := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : Fin d → N ⧸ Λ.addSubgroupOf N,
        q = fun i => (((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i : N) : N ⧸ Λ.addSubgroupOf N) := ⟨_, rfl⟩
    have key : ∀ h, Φ (h + q) = c * Φ h := by
      intro h
      rw [hΦ]
      show F _ = c * F _
      rw [← hx _ (fun i => (Quotient.out (h i) : N).2)]
      have : ∀ i, ∃ l ∈ Λ, ((Quotient.out ((h + q) i) : N) : K) =
          ((Quotient.out (h i) : N) : K) + (Pi.single k n₀ : Fin d → K) i + l := by
        intro i
        obtain ⟨l, hl, e⟩ := out_add (Λ.addSubgroupOf N) (h i) ((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i)
        refine ⟨(l : K), AddSubgroup.mem_addSubgroupOf.1 hl, ?_⟩
        have e' : (h + q) i = h i + (((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i : N) :
            N ⧸ Λ.addSubgroupOf N) := by rw [hq]; rfl
        rw [e', e]
        have e'' : (((Pi.single k ⟨n₀, hn₀⟩ : Fin d → N) i : N) : K) =
            (Pi.single k n₀ : Fin d → K) i := by
          by_cases hik : i = k
          · subst hik; simp
          · simp [hik]
        push_cast
        rw [e'']
      choose l hl el using this
      have e : (x + fun i => ((Quotient.out ((h + q) i) : N) : K)) =
          (x + (fun i => ((Quotient.out (h i) : N) : K)) + Pi.single k n₀) + l := by
        ext i
        have e0 := el i
        simp only [Pi.add_apply] at e0 ⊢
        rw [e0]; ring
      rw [e, hF _ l hl]
    have e := Equiv.sum_comp (Equiv.addRight q) Φ
    simp only [Equiv.coe_addRight, key] at e
    rw [← Finset.mul_sum] at e
    have e2 : (c - 1) * ∑ h, Φ h = 0 := by linear_combination e
    rw [hΦ] at e2
    rcases mul_eq_zero.1 e2 with h | h
    · exact absurd (sub_eq_zero.1 h) hc
    · exact h

/- English proof (translation)
Use `Fintype.ofFinite (N ⧸ Λ.addSubgroupOf N)` as an intermediate fact. Take `⟨f, hf⟩ : ∃ f : (Fin d → K ⧸ Λ) → ℂ, f = fun y => F (fun i => Quotient.out (y i))` from `⟨_, rfl⟩`. Rewrite using `[← hf]`. Distinguish the cases in `hfin : (Function.support f).Finite`. Use `swap`.

Conclude with `finsum_of_infinite_support hfin`. Establish `shift : ∀ (v : Fin d → K) (y : Fin d → K ⧸ Λ), f (y + fun i => (v i : K ⧸ Λ)) = F ((fun i => Quotient.out (y i)) + v)`. Introduce `v y`. Establish `: ∀ i, ∃ l ∈ Λ, (Quotient.out (y i + (v i : K ⧸ Λ)) : K) = Quotient.out (y i) + v i + l` using `fun i => out_add Λ (y i) (v i)`. Use `choose l hl el using this`.

Establish `e : (fun i => (Quotient.out ((y + fun i => (v i : K ⧸ Λ)) i) : K)) = ((fun i => Quotient.out (y i)) + v) + l`. Use extensionality with `i`. Conclude with `el i`. Rewrite using `[hf]`. Use `show F _ = _`.

Rewrite using `[e, hF _ l hl]`. Take `⟨o, ho⟩ : ∃ o : (Fin d → N ⧸ Λ.addSubgroupOf N) → Fin d → K, o = fun h i => ((Quotient.out (h i) : N) : K)` from `⟨_, rfl⟩`. Establish `h1 : ∀ h, ∑ᶠ y, f (y + fun i => (o h i : K ⧸ Λ)) = ∑ᶠ y, f y` using `fun h => finsum_comp_equiv (Equiv.addRight (fun i => (o h i : K ⧸ Λ)))`. Establish `h2 : ∑ h : (Fin d → N ⧸ Λ.addSubgroupOf N), ∑ᶠ y, f (y + fun i => (o h i : K ⧸ Λ)) = 0`. Rewrite using `[← finsum_sum_comm]`.

Establish `: ∀ y : Fin d → K ⧸ Λ, ∑ h, f (y + fun i => (o h i : K ⧸ Λ)) = 0`. Introduce `y`. Simplify using `only [shift]`. Rewrite using `[ho]`. Conclude with `local_zero Λ N F hF _ (hx _)`.

Simplify using `only [this, finsum_zero]`. Introduce `h _`. Conclude with `hfin.preimage ((Equiv.addRight (fun i => (o h i : K ⧸ Λ))).injective.injOn)`. Simplify using `only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases.

Conclude with `absurd h (by exact_mod_cast Fintype.card_ne_zero)`. Conclude with `h`.
-/
theorem avg_zero (Λ N : AddSubgroup K) [Finite (N ⧸ Λ.addSubgroupOf N)] {d : ℕ}
    (F : (Fin d → K) → ℂ) (hF : LatInvN Λ F) (hx : ∀ x, Osc N F x) :
    ∑ᶠ y : Fin d → K ⧸ Λ, F (fun i => Quotient.out (y i)) = 0 := by
  classical
  have := Fintype.ofFinite (N ⧸ Λ.addSubgroupOf N)
  obtain ⟨f, hf⟩ : ∃ f : (Fin d → K ⧸ Λ) → ℂ, f = fun y => F (fun i => Quotient.out (y i)) :=
    ⟨_, rfl⟩
  rw [← hf]
  by_cases hfin : (Function.support f).Finite
  swap
  · exact finsum_of_infinite_support hfin
  have shift : ∀ (v : Fin d → K) (y : Fin d → K ⧸ Λ), f (y + fun i => (v i : K ⧸ Λ)) =
      F ((fun i => Quotient.out (y i)) + v) := by
    intro v y
    have : ∀ i, ∃ l ∈ Λ, (Quotient.out (y i + (v i : K ⧸ Λ)) : K) = Quotient.out (y i) + v i + l :=
      fun i => out_add Λ (y i) (v i)
    choose l hl el using this
    have e : (fun i => (Quotient.out ((y + fun i => (v i : K ⧸ Λ)) i) : K)) =
        ((fun i => Quotient.out (y i)) + v) + l := by
      ext i; exact el i
    rw [hf]
    show F _ = _
    rw [e, hF _ l hl]
  obtain ⟨o, ho⟩ : ∃ o : (Fin d → N ⧸ Λ.addSubgroupOf N) → Fin d → K,
      o = fun h i => ((Quotient.out (h i) : N) : K) := ⟨_, rfl⟩
  have h1 : ∀ h, ∑ᶠ y, f (y + fun i => (o h i : K ⧸ Λ)) = ∑ᶠ y, f y :=
    fun h => finsum_comp_equiv (Equiv.addRight (fun i => (o h i : K ⧸ Λ)))
  have h2 : ∑ h : (Fin d → N ⧸ Λ.addSubgroupOf N), ∑ᶠ y, f (y + fun i => (o h i : K ⧸ Λ)) = 0 := by
    rw [← finsum_sum_comm]
    · have : ∀ y : Fin d → K ⧸ Λ, ∑ h, f (y + fun i => (o h i : K ⧸ Λ)) = 0 := by
        intro y
        simp only [shift]
        rw [ho]
        exact local_zero Λ N F hF _ (hx _)
      simp only [this, finsum_zero]
    · intro h _
      exact hfin.preimage ((Equiv.addRight (fun i => (o h i : K ⧸ Λ))).injective.injOn)
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h (by exact_mod_cast Fintype.card_ne_zero)
  · exact h

/- English proof (translation)
Establish `: CompactSpace N` using `isCompact_iff_compactSpace.1 hN`. Conclude with `AddSubgroup.quotient_finite_of_isOpen _ (hΛ.preimage continuous_subtype_val)`.
-/
theorem finite_quot [TopologicalSpace K] [IsTopologicalRing K] (N Λ : AddSubgroup K)
    (hN : IsCompact (N : Set K)) (hΛ : IsOpen (Λ : Set K)) : Finite (N ⧸ Λ.addSubgroupOf N) := by
  have : CompactSpace N := isCompact_iff_compactSpace.1 hN
  exact AddSubgroup.quotient_finite_of_isOpen _ (hΛ.preimage continuous_subtype_val)

end Avg

section Main

variable {K : Type} [CommRing K]

/- English proof (translation)
Unfold `mulR`. Rewrite using `[AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, e⟩`. Conclude with `⟨r, hr, e.symm⟩`.

Introduce and unpack `⟨r, hr, e⟩`. Conclude with `⟨r, hr, e.symm⟩`.
-/
theorem mem_mulR {R : Subring K} {ν x : K} : x ∈ mulR R ν ↔ ∃ r ∈ R, x = ν * r := by
  unfold mulR
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨r, hr, e⟩; exact ⟨r, hr, e.symm⟩
  · rintro ⟨r, hr, e⟩; exact ⟨r, hr, e.symm⟩

/- English proof (translation)
Establish `: ((mulR R ν : AddSubgroup K) : Set K) = I R ν`. Use extensionality with `x`. Conclude with `mem_mulR`. Rewrite using `[this]`. Conclude with `I_compact hc ν`.
-/
theorem compact_mulR [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
    (hc : IsCompact (R : Set K)) (ν : K) : IsCompact ((mulR R ν : AddSubgroup K) : Set K) := by
  have : ((mulR R ν : AddSubgroup K) : Set K) = I R ν := by
    ext x; exact mem_mulR
  rw [this]; exact I_compact hc ν

open Classical in
/- English proof (translation)
Introduce `K _ _ _ R ψ hD hn m _ L₀ Λ₁ B Q hL₀ hΛ₁ hB hQ _`. Take `⟨ϖ, h⟩` from `adic_of_datum hD hn`. Take `⟨a, ha⟩` from `h.bounded hL₀.2`. Take `⟨d, hd⟩` from `h.bounded hQ`. Take `⟨j, hj⟩` from `h.crit hn m a B (hB.1.mem_nhds B.zero_mem)`.

Take `⟨b, hb⟩` from `h.basis ((B : Set K) ∩ (Λ₁ : Set K)) (Filter.inter_mem (hB.1.mem_nhds B.zero_mem) (hΛ₁.1.mem_nhds Λ₁.zero_mem))`. Establish `hψR : ∀ r ∈ R, ψ r = 1` using `fun r hr => by simpa using (hD.selfDual 1).2 R.one_mem r hr`. Use `⟨I R ((ϖ ^ (2 * (a + j) + (1 + b + d + a * m)) : Kˣ) : K), I_nhds h.isOpen _, ?_⟩` and prove the remaining obligations. Introduce `t D' A ht hD'Q hA Λ hΛ hInv`. Take `⟨τ, hτ, et⟩` from `ht`.

Rewrite `et` using `[Units.val_pow_eq_pow_val]`. Take `⟨κ, hκ⟩ : ∃ κ : K, κ = (ϖ : K) ^ (1 + b + d + a * m) * τ` from `⟨_, rfl⟩`. Take `⟨μ, hμ⟩ : ∃ μ : K, μ = (ϖ : K) ^ (a + j) * κ` from `⟨_, rfl⟩`. Take `⟨ν, hν⟩ : ∃ ν : K, ν = (ϖ : K) ^ a * μ` from `⟨_, rfl⟩`. Take `⟨ti, hti⟩ : ∃ ti : K, ti = ((t⁻¹ : Kˣ) : K)` from `⟨_, rfl⟩`.

Take `⟨ϖi, hϖi⟩ : ∃ p : K, p = ((ϖ⁻¹ : Kˣ) : K)` from `⟨_, rfl⟩`. Establish `htt : (t : K) * ti = 1` using `by rw [hti]; simp`. Establish `hϖϖ : (ϖ : K) ^ j * ϖi ^ j = 1` using `by rw [hϖi, ← mul_pow]; simp`. Establish `etν : (t : K) = (ϖ : K) ^ j * ν` using `by rw [et, hν, hμ, hκ]; ring`. Establish `hμ2 : μ ^ 2 = κ * (t : K)` using `by rw [etν, hν, hμ]; ring`.

Establish `hμI : μ ∈ I R (ϖ : K)` using `⟨(ϖ : K) ^ (a + j + b + d + a * m) * τ, R.mul_mem (R.pow_mem h.mem _) hτ, by`. Rewrite using `[hμ, hκ]`. Use the proof step `ring⟩`. Establish `hNB : ∀ v ∈ mulR R ν, v ∈ B ∧ v ∈ Λ₁`. Introduce `v hv`.

Take `⟨r, hr, rfl⟩` from `mem_mulR.1 hv`. Establish `e : ν * r = (ϖ : K) ^ b * ((ϖ : K) ^ (a + a + j + 1 + d + a * m) * τ * r)`. Rewrite using `[hν, hμ, hκ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `hb _ (R.mul_mem (R.mul_mem (R.pow_mem h.mem _) hτ) hr)`. Use `finite_quot (mulR R ν) Λ (compact_mulR h.isCompact ν) hΛ.1` as an intermediate fact. Unfold `intK`. Rewrite `hInv`, the goal using `[← hti]`. Rewrite using `[avg_zero Λ (mulR R ν) _ hInv ?_, mul_zero]`.

Introduce `x`. Establish `hE : ∀ v : Fin m → K, (∀ i, v i ∈ mulR R ν) → ((∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, (x + v) k - (z : K) ∈ B) ↔ ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B)`. Introduce `v hv`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hk⟩`.

Use `⟨z, hz, fun k => ?_⟩` and prove the remaining obligations. Establish `e : x k - (z : K) = ((x + v) k - (z : K)) - v k` using `by simp only [Pi.add_apply]; ring`. Rewrite using `[e]`. Conclude with `B.sub_mem (hk k) (hNB _ (hv k)).1`. Introduce and unpack `⟨z, hz, hk⟩`.

Use `⟨z, hz, fun k => ?_⟩` and prove the remaining obligations. Establish `e : (x + v) k - (z : K) = (x k - (z : K)) + v k` using `by simp only [Pi.add_apply]; ring`. Rewrite using `[e]`. Conclude with `B.add_mem (hk k) (hNB _ (hv k)).1`. Establish `hAv : ∀ v : Fin m → K, (∀ i, v i ∈ mulR R ν) → A (x + v) = A x` using `fun v hv => hA.2 x v fun i => (hNB _ (hv i)).2`.

Distinguish the cases in `hEx : ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B`. Use `left`. Introduce `v hv`. Conclude with `if_pos ((hE v hv).2 hEx)`. Distinguish the cases in `hAx : A x = 0`.

Use `left`. Introduce `v hv`. Use `show (if _ then _ else _) = _`. Rewrite using `[hAv v hv, hAx, zero_mul, ite_self]`. Use `right`.

Establish `hsup` using `hA.1 x hAx`. Take `⟨xi, hxi⟩ : ∃ xi : Fin m → K, xi = fun k => Ring.inverse (x k)` from `⟨_, rfl⟩`. Establish `hxxi : ∀ k, x k * xi k = 1` using `fun k => by`. Rewrite using `[hxi]`. Conclude with `Ring.mul_inverse_cancel _ (hsup k).2.1`.

Establish `hxiR : ∀ k, (ϖ : K) ^ a * xi k ∈ R` using `fun k => by`. Rewrite using `[hxi]`. Conclude with `ha _ (hsup k).2.2`. Take `⟨G, hG⟩ : ∃ G : Fin m → K, G = fun k => 1 - (D' : K) * (xi k * ∏ i, xi i)` from `⟨_, rfl⟩`. Establish `hnot : ¬ ∀ k, 1 - (D' : K) * (xi k * ∏ i, xi i) ∈ I R ((ϖ : K) ^ j)` using `fun hall => hEx (hj D' x xi hxxi (fun k => ha _ (hsup k).1) hall)`.

Use `push Not at hnot`. Take `⟨k, hk⟩` from `hnot`. Establish `hk2 : ¬ (G k * ϖi ^ j ∈ R)`. Introduce `hc`. Apply `hk` to reduce the goal to its premises.

Use `⟨_, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[hG]`. Take the linear combination `(-(1 - (D' : K) * (xi k * ∏ i, xi i))) * hϖϖ`. Rewrite `hk2` using `[← hD.selfDual]`. Use `push Not at hk2`.

Take `⟨r, hr, hrψ⟩` from `hk2`. Establish `formula : ∀ v : Fin m → K, (∀ i, v i ∈ mulR R ν) → (if ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, (x + v) k - (z : K) ∈ B then (0 : ℂ) else A (x + v) * ψ (g0 (D' : K) (x + v) * ti)) = A x * ψ (g0 (D' : K) x * ti) * ψ ((∑ i, v i * G i) * ti)`. Introduce `v hv`. Rewrite using `[if_neg (fun hc => hEx ((hE v hv).1 hc)), hAv v hv]`. Take `⟨ρ, hρ, e⟩` from `h.taylor m a (D' : K) x xi v μ hμI hxxi hxiR (fun i => by`.

Take `⟨r, hr, e⟩` from `mem_mulR.1 (hv i)`. Conclude with `⟨r, hr, by rw [e, hν]⟩)`. Establish `hP : ∏ i, ((ϖ : K) ^ a * xi i) ∈ R` using `R.prod_mem fun i _ => hxiR i`. Establish `eP : ∏ i, ((ϖ : K) ^ a * xi i) = (ϖ : K) ^ (a * m) * ∏ i, xi i`. Rewrite using `[Finset.prod_mul_distrib]`.

Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree. Establish `hZ : (D' : K) * (∏ i, xi i) * μ ^ 2 * ρ * ti ∈ R`. Establish `e3 : (D' : K) * (∏ i, xi i) * μ ^ 2 * ρ * ti = ((ϖ : K) ^ d * (D' : K)) * (∏ i, ((ϖ : K) ^ a * xi i)) * ((ϖ : K) ^ (1 + b) * τ) * ρ`. Rewrite using `[eP, hμ2, hκ]`.

Take the linear combination `((D' : K) * (∏ i, xi i) * ((ϖ : K) ^ (1 + b + d + a * m) * τ) * ρ) * htt`. Rewrite using `[e3]`. Conclude with `R.mul_mem (R.mul_mem (R.mul_mem (hd _ hD'Q) hP) (R.mul_mem (R.pow_mem h.mem _) hτ)) hρ`. Establish `e4 : g0 (D' : K) (x + v) * ti = g0 (D' : K) x * ti + (∑ i, v i * G i) * ti + (D' : K) * (∏ i, xi i) * μ ^ 2 * ρ * ti`. Rewrite using `[e, hG]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e4, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψR _ hZ, mul_one, mul_assoc]`. Use `⟨k, ν * r, mem_mulR.2 ⟨r, hr, rfl⟩, ψ (G k * ϖi ^ j * r), hrψ, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hv' : ∀ i, (v + Pi.single k (ν * r) : Fin m → K) i ∈ mulR R ν`. Introduce `i`.

Use `(mulR R ν).add_mem (hv i) ?_` and prove the remaining obligations. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality. Simplify using `using mem_mulR.2 ⟨r, hr, rfl⟩`. Simplify using `[hik]`.

Establish `f1` using `formula _ hv'`. Establish `f2` using `formula v hv`. Rewrite `f1` using `[← add_assoc]`. Use `f1.trans ?_` and prove the remaining obligations. Use `show _ = _ * (if _ then _ else _)`.

Rewrite using `[f2]`. Establish `e5 : (∑ i, (v + Pi.single k (ν * r) : Fin m → K) i * G i) * ti = (∑ i, v i * G i) * ti + G k * ϖi ^ j * r`. Establish `e6 : ∑ i, (v + Pi.single k (ν * r) : Fin m → K) i * G i = ∑ i, v i * G i + ν * r * G k`. Simplify using `[add_mul, Finset.sum_add_distrib, Pi.single_apply, ite_mul]`. Establish `e7 : ν * ti = ϖi ^ j`.

Rewrite `htt` using `[etν]`. Take the linear combination `(ϖi ^ j) * htt - (ν * ti) * hϖϖ`. Rewrite using `[e6]`. Take the linear combination `(r * G k) * e7`. Rewrite using `[e5, AddChar.map_add_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nonStationary_main : NonStationary := by
  intro K _ _ _ R ψ hD hn m _ L₀ Λ₁ B Q hL₀ hΛ₁ hB hQ _
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨a, ha⟩ := h.bounded hL₀.2
  obtain ⟨d, hd⟩ := h.bounded hQ
  obtain ⟨j, hj⟩ := h.crit hn m a B (hB.1.mem_nhds B.zero_mem)
  obtain ⟨b, hb⟩ := h.basis ((B : Set K) ∩ (Λ₁ : Set K))
    (Filter.inter_mem (hB.1.mem_nhds B.zero_mem) (hΛ₁.1.mem_nhds Λ₁.zero_mem))
  have hψR : ∀ r ∈ R, ψ r = 1 := fun r hr => by simpa using (hD.selfDual 1).2 R.one_mem r hr
  refine ⟨I R ((ϖ ^ (2 * (a + j) + (1 + b + d + a * m)) : Kˣ) : K), I_nhds h.isOpen _, ?_⟩
  intro t D' A ht hD'Q hA Λ hΛ hInv
  obtain ⟨τ, hτ, et⟩ := ht
  rw [Units.val_pow_eq_pow_val] at et
  obtain ⟨κ, hκ⟩ : ∃ κ : K, κ = (ϖ : K) ^ (1 + b + d + a * m) * τ := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ = (ϖ : K) ^ (a + j) * κ := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : K, ν = (ϖ : K) ^ a * μ := ⟨_, rfl⟩
  obtain ⟨ti, hti⟩ : ∃ ti : K, ti = ((t⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  obtain ⟨ϖi, hϖi⟩ : ∃ p : K, p = ((ϖ⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have htt : (t : K) * ti = 1 := by rw [hti]; simp
  have hϖϖ : (ϖ : K) ^ j * ϖi ^ j = 1 := by rw [hϖi, ← mul_pow]; simp
  have etν : (t : K) = (ϖ : K) ^ j * ν := by rw [et, hν, hμ, hκ]; ring
  have hμ2 : μ ^ 2 = κ * (t : K) := by rw [etν, hν, hμ]; ring
  have hμI : μ ∈ I R (ϖ : K) :=
    ⟨(ϖ : K) ^ (a + j + b + d + a * m) * τ, R.mul_mem (R.pow_mem h.mem _) hτ, by
      rw [hμ, hκ]; ring⟩
  have hNB : ∀ v ∈ mulR R ν, v ∈ B ∧ v ∈ Λ₁ := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hv
    have e : ν * r = (ϖ : K) ^ b * ((ϖ : K) ^ (a + a + j + 1 + d + a * m) * τ * r) := by
      rw [hν, hμ, hκ]; ring
    rw [e]
    exact hb _ (R.mul_mem (R.mul_mem (R.pow_mem h.mem _) hτ) hr)
  have := finite_quot (mulR R ν) Λ (compact_mulR h.isCompact ν) hΛ.1
  unfold intK
  rw [← hti] at hInv ⊢
  rw [avg_zero Λ (mulR R ν) _ hInv ?_, mul_zero]
  intro x
  have hE : ∀ v : Fin m → K, (∀ i, v i ∈ mulR R ν) →
      ((∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, (x + v) k - (z : K) ∈ B) ↔
        ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B) := by
    intro v hv
    constructor
    · rintro ⟨z, hz, hk⟩
      refine ⟨z, hz, fun k => ?_⟩
      have e : x k - (z : K) = ((x + v) k - (z : K)) - v k := by simp only [Pi.add_apply]; ring
      rw [e]; exact B.sub_mem (hk k) (hNB _ (hv k)).1
    · rintro ⟨z, hz, hk⟩
      refine ⟨z, hz, fun k => ?_⟩
      have e : (x + v) k - (z : K) = (x k - (z : K)) + v k := by simp only [Pi.add_apply]; ring
      rw [e]; exact B.add_mem (hk k) (hNB _ (hv k)).1
  have hAv : ∀ v : Fin m → K, (∀ i, v i ∈ mulR R ν) → A (x + v) = A x :=
    fun v hv => hA.2 x v fun i => (hNB _ (hv i)).2
  by_cases hEx : ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, x k - (z : K) ∈ B
  · left
    intro v hv
    exact if_pos ((hE v hv).2 hEx)
  by_cases hAx : A x = 0
  · left
    intro v hv
    show (if _ then _ else _) = _
    rw [hAv v hv, hAx, zero_mul, ite_self]
  right
  have hsup := hA.1 x hAx
  obtain ⟨xi, hxi⟩ : ∃ xi : Fin m → K, xi = fun k => Ring.inverse (x k) := ⟨_, rfl⟩
  have hxxi : ∀ k, x k * xi k = 1 := fun k => by
    rw [hxi]; exact Ring.mul_inverse_cancel _ (hsup k).2.1
  have hxiR : ∀ k, (ϖ : K) ^ a * xi k ∈ R := fun k => by
    rw [hxi]; exact ha _ (hsup k).2.2
  obtain ⟨G, hG⟩ : ∃ G : Fin m → K, G = fun k => 1 - (D' : K) * (xi k * ∏ i, xi i) := ⟨_, rfl⟩
  have hnot : ¬ ∀ k, 1 - (D' : K) * (xi k * ∏ i, xi i) ∈ I R ((ϖ : K) ^ j) :=
    fun hall => hEx (hj D' x xi hxxi (fun k => ha _ (hsup k).1) hall)
  push Not at hnot
  obtain ⟨k, hk⟩ := hnot
  have hk2 : ¬ (G k * ϖi ^ j ∈ R) := by
    intro hc
    apply hk
    refine ⟨_, hc, ?_⟩
    rw [hG]
    linear_combination (-(1 - (D' : K) * (xi k * ∏ i, xi i))) * hϖϖ
  rw [← hD.selfDual] at hk2
  push Not at hk2
  obtain ⟨r, hr, hrψ⟩ := hk2
  have formula : ∀ v : Fin m → K, (∀ i, v i ∈ mulR R ν) →
      (if ∃ z : Kˣ, z ^ (m + 1) = D' ∧ ∀ k, (x + v) k - (z : K) ∈ B then (0 : ℂ)
        else A (x + v) * ψ (g0 (D' : K) (x + v) * ti)) =
      A x * ψ (g0 (D' : K) x * ti) * ψ ((∑ i, v i * G i) * ti) := by
    intro v hv
    rw [if_neg (fun hc => hEx ((hE v hv).1 hc)), hAv v hv]
    obtain ⟨ρ, hρ, e⟩ := h.taylor m a (D' : K) x xi v μ hμI hxxi hxiR (fun i => by
      obtain ⟨r, hr, e⟩ := mem_mulR.1 (hv i)
      exact ⟨r, hr, by rw [e, hν]⟩)
    have hP : ∏ i, ((ϖ : K) ^ a * xi i) ∈ R := R.prod_mem fun i _ => hxiR i
    have eP : ∏ i, ((ϖ : K) ^ a * xi i) = (ϖ : K) ^ (a * m) * ∏ i, xi i := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    have hZ : (D' : K) * (∏ i, xi i) * μ ^ 2 * ρ * ti ∈ R := by
      have e3 : (D' : K) * (∏ i, xi i) * μ ^ 2 * ρ * ti =
          ((ϖ : K) ^ d * (D' : K)) * (∏ i, ((ϖ : K) ^ a * xi i)) * ((ϖ : K) ^ (1 + b) * τ) * ρ := by
        rw [eP, hμ2, hκ]
        linear_combination ((D' : K) * (∏ i, xi i) * ((ϖ : K) ^ (1 + b + d + a * m) * τ) * ρ) * htt
      rw [e3]
      exact R.mul_mem (R.mul_mem (R.mul_mem (hd _ hD'Q) hP) (R.mul_mem (R.pow_mem h.mem _) hτ)) hρ
    have e4 : g0 (D' : K) (x + v) * ti = g0 (D' : K) x * ti + (∑ i, v i * G i) * ti +
        (D' : K) * (∏ i, xi i) * μ ^ 2 * ρ * ti := by
      rw [e, hG]; ring
    rw [e4, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψR _ hZ, mul_one, mul_assoc]
  refine ⟨k, ν * r, mem_mulR.2 ⟨r, hr, rfl⟩, ψ (G k * ϖi ^ j * r), hrψ, fun v hv => ?_⟩
  have hv' : ∀ i, (v + Pi.single k (ν * r) : Fin m → K) i ∈ mulR R ν := by
    intro i
    refine (mulR R ν).add_mem (hv i) ?_
    by_cases hik : i = k
    · subst hik; simpa using mem_mulR.2 ⟨r, hr, rfl⟩
    · simp [hik]
  have f1 := formula _ hv'
  have f2 := formula v hv
  rw [← add_assoc] at f1
  refine f1.trans ?_
  show _ = _ * (if _ then _ else _)
  rw [f2]
  have e5 : (∑ i, (v + Pi.single k (ν * r) : Fin m → K) i * G i) * ti =
      (∑ i, v i * G i) * ti + G k * ϖi ^ j * r := by
    have e6 : ∑ i, (v + Pi.single k (ν * r) : Fin m → K) i * G i = ∑ i, v i * G i + ν * r * G k := by
      simp [add_mul, Finset.sum_add_distrib, Pi.single_apply, ite_mul]
    have e7 : ν * ti = ϖi ^ j := by
      rw [etν] at htt
      linear_combination (ϖi ^ j) * htt - (ν * ti) * hϖϖ
    rw [e6]
    linear_combination (r * G k) * e7
  rw [e5, AddChar.map_add_eq_mul]
  ring

end Main

end Formalism.FourierDecayAlt.P.AdicNeighbourhood

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `AdicNeighbourhood.nonStationary_main`.
-/
theorem nonStationary : Formalism.FourierDecayAlt.A6.NonStationary := AdicNeighbourhood.nonStationary_main

end Formalism.FourierDecayAlt.P
