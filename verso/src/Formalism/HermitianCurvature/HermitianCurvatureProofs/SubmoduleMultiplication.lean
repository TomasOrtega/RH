import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix

namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint

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

/- English proof (translation)
Use `hC.induction_on (p := fun S => ∃ M : ℕ, ∀ z ∈ S, ∀ z' : K, z * z' = 1 → (ϖ : K) ^ M * z' ∈ R) ⟨0, by simp⟩ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `S T hST ⟨M, hM⟩`. Conclude with `⟨M, fun z hz => hM z (hST hz)⟩`. Introduce and unpack `S T ⟨M, hM⟩ ⟨M', hM'⟩`. Use `⟨M + M', fun z hz z' e => ?_⟩` and prove the remaining obligations.

Break down `hz with hz | hz` into its components or cases. Use `R.mul_mem (R.pow_mem h.mem M') (hM z hz z' e)` as an intermediate fact. Establish `e' : (ϖ : K) ^ (M + M') * z' = (ϖ : K) ^ M' * ((ϖ : K) ^ M * z')` using `by ring`. Rewrite using `[e']` and apply the resulting hypothesis. Use `R.mul_mem (R.pow_mem h.mem M) (hM' z hz z' e)` as an intermediate fact.

Establish `e' : (ϖ : K) ^ (M + M') * z' = (ϖ : K) ^ M * ((ϖ : K) ^ M' * z')` using `by ring`. Rewrite using `[e']` and apply the resulting hypothesis. Introduce `x hx`. Take `⟨u, rfl⟩` from `hU x hx`. Take `⟨M, hM⟩` from `h.absorb ((u⁻¹ : Kˣ) : K)`.

Use `⟨{z | (z - (u : K)) * ((u⁻¹ : Kˣ) : K) ∈ I R (ϖ : K)}, mem_nhdsWithin_of_mem_nhds ?_, M, fun z hz z' e => ?_⟩` and prove the remaining obligations. Establish `: ContinuousAt (fun z : K => (z - (u : K)) * ((u⁻¹ : Kˣ) : K)) (u : K)` using `((continuous_id.sub continuous_const).mul continuous_const).continuousAt`. Conclude with `this.preimage_mem_nhds (by simpa using I_nhds h.isOpen ϖ)`. Take `⟨v, hv, ev⟩` from `h.unit_one _ hz`. Establish `i1 : (u : K) * ((u⁻¹ : Kˣ) : K) = 1` using `by simp`.

Establish `: z' = ((u⁻¹ : Kˣ) : K) * v`. Take the linear combination `((u⁻¹ : Kˣ) : K) * v * e - z' * v * i1 - z' * ev`. Rewrite using `[this, ← mul_assoc]`. Conclude with `R.mul_mem hM hv`.
-/
theorem Adic.inv_bounded (h : Adic R ϖ) {Om : Set K} (hC : IsCompact Om) (hU : ∀ z ∈ Om, IsUnit z) :
    ∃ M : ℕ, ∀ z ∈ Om, ∀ z' : K, z * z' = 1 → (ϖ : K) ^ M * z' ∈ R := by
  refine hC.induction_on
    (p := fun S => ∃ M : ℕ, ∀ z ∈ S, ∀ z' : K, z * z' = 1 → (ϖ : K) ^ M * z' ∈ R)
    ⟨0, by simp⟩ ?_ ?_ ?_
  · rintro S T hST ⟨M, hM⟩
    exact ⟨M, fun z hz => hM z (hST hz)⟩
  · rintro S T ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', fun z hz z' e => ?_⟩
    rcases hz with hz | hz
    · have := R.mul_mem (R.pow_mem h.mem M') (hM z hz z' e)
      have e' : (ϖ : K) ^ (M + M') * z' = (ϖ : K) ^ M' * ((ϖ : K) ^ M * z') := by ring
      rwa [e']
    · have := R.mul_mem (R.pow_mem h.mem M) (hM' z hz z' e)
      have e' : (ϖ : K) ^ (M + M') * z' = (ϖ : K) ^ M * ((ϖ : K) ^ M' * z') := by ring
      rwa [e']
  · intro x hx
    obtain ⟨u, rfl⟩ := hU x hx
    obtain ⟨M, hM⟩ := h.absorb ((u⁻¹ : Kˣ) : K)
    refine ⟨{z | (z - (u : K)) * ((u⁻¹ : Kˣ) : K) ∈ I R (ϖ : K)}, mem_nhdsWithin_of_mem_nhds ?_, M,
      fun z hz z' e => ?_⟩
    · have : ContinuousAt (fun z : K => (z - (u : K)) * ((u⁻¹ : Kˣ) : K)) (u : K) :=
        ((continuous_id.sub continuous_const).mul continuous_const).continuousAt
      exact this.preimage_mem_nhds (by simpa using I_nhds h.isOpen ϖ)
    · obtain ⟨v, hv, ev⟩ := h.unit_one _ hz
      have i1 : (u : K) * ((u⁻¹ : Kˣ) : K) = 1 := by simp
      have : z' = ((u⁻¹ : Kˣ) : K) * v := by
        linear_combination ((u⁻¹ : Kˣ) : K) * v * e - z' * v * i1 - z' * ev
      rw [this, ← mul_assoc]
      exact R.mul_mem hM hv

/- English proof (translation)
Establish `: I R (a : K) = (fun x => ((a⁻¹ : Kˣ) : K) * x) ⁻¹' (R : Set K)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, rfl⟩ show ((a⁻¹ : Kˣ) : K) * ((a : K) * r) ∈ R`. Simplify using `using hr`.

Introduce `hx`. Conclude with `⟨_, hx, by simp⟩`. Rewrite using `[this]`. Conclude with `ho.preimage (continuous_const.mul continuous_id)`.
-/
theorem I_isOpen {R : Subring K} (ho : IsOpen (R : Set K)) (a : Kˣ) : IsOpen (I R (a : K)) := by
  have : I R (a : K) = (fun x => ((a⁻¹ : Kˣ) : K) * x) ⁻¹' (R : Set K) := by
    ext x; constructor
    · rintro ⟨r, hr, rfl⟩
      show ((a⁻¹ : Kˣ) : K) * ((a : K) * r) ∈ R
      simpa using hr
    · intro hx
      exact ⟨_, hx, by simp⟩
  rw [this]
  exact ho.preimage (continuous_const.mul continuous_id)

/- English proof (translation)
Use `h.t2` as an intermediate fact. Assume the negation of the conclusion as `hx0`. Establish `hW : ({x}ᶜ : Set K) ∈ 𝓝 (0 : K)` using `isOpen_compl_singleton.mem_nhds (by`. Simplify using `using Ne.symm hx0)`. Take `⟨n, hn⟩` from `h.basis _ hW`.

Take `⟨r, hr, e⟩` from `hx n`. Conclude with `hn r hr e.symm`.
-/
theorem Adic.sep (h : Adic R ϖ) (x : K) (hx : ∀ n, x ∈ I R ((ϖ : K) ^ n)) : x = 0 := by
  have := h.t2
  by_contra hx0
  have hW : ({x}ᶜ : Set K) ∈ 𝓝 (0 : K) := isOpen_compl_singleton.mem_nhds (by
    simpa using Ne.symm hx0)
  obtain ⟨n, hn⟩ := h.basis _ hW
  obtain ⟨r, hr, e⟩ := hx n
  exact hn r hr e.symm

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hnm`. Conclude with `⟨(ϖ : K) ^ d * r, R.mul_mem (R.pow_mem hϖ d) hr, by ring⟩`.
-/
theorem I_anti (hϖ : (ϖ : K) ∈ R) {n m : ℕ} (hnm : n ≤ m) {x : K} (hx : x ∈ I R ((ϖ : K) ^ m)) :
    x ∈ I R ((ϖ : K) ^ n) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact ⟨(ϖ : K) ^ d * r, R.mul_mem (R.pow_mem hϖ d) hr, by ring⟩

/- English proof (translation)
Use `h.t2` as an intermediate fact. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Set `C : ℕ → Set K` to `fun n => (R : Set K) ∩ ((I R (ϖ : K))ᶜ ∩ (fun u => u ^ s) ⁻¹' I R ((ϖ : K) ^ n))`. Establish `hcl : ∀ n, IsClosed (C n)` using `fun n => h.isCompact.isClosed.inter ((I_isOpen h.isOpen ϖ).isClosed_compl.inter ((I_compact h.isCompact _).isClosed.preimage (continuous_pow s)))`.

Take `⟨u, hu⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C (fun n x hx => ⟨hx.1, hx.2.1, I_anti h.mem (Nat.le_succ n) hx.2.2⟩) (fun n => by`. Take `⟨u, hu, h1, h2⟩` from `hcon n`. Conclude with `⟨u, hu, h2, h1⟩)`. Use the proof step `(h.isCompact.of_isClosed_subset (hcl 0) Set.inter_subset_left) hcl`. Establish `hu'` using `Set.mem_iInter.1 hu`.

Establish `h0 : u ^ s = 0` using `h.sep _ fun n => (hu' n).2.2`. Establish `: u = 0` using `IsNilpotent.eq_zero ⟨s, h0⟩`. Conclude with `(hu' 0).2.1 ⟨0, R.zero_mem, by simp [this]⟩`.
-/
theorem Adic.pow_step (h : Adic R ϖ) [IsReduced K] (s : ℕ) :
    ∃ n0 : ℕ, ∀ u ∈ R, u ^ s ∈ I R ((ϖ : K) ^ n0) → u ∈ I R (ϖ : K) := by
  have := h.t2
  by_contra hcon
  push Not at hcon
  let C : ℕ → Set K := fun n => (R : Set K) ∩ ((I R (ϖ : K))ᶜ ∩ (fun u => u ^ s) ⁻¹' I R ((ϖ : K) ^ n))
  have hcl : ∀ n, IsClosed (C n) := fun n =>
    h.isCompact.isClosed.inter ((I_isOpen h.isOpen ϖ).isClosed_compl.inter
      ((I_compact h.isCompact _).isClosed.preimage (continuous_pow s)))
  obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    (fun n x hx => ⟨hx.1, hx.2.1, I_anti h.mem (Nat.le_succ n) hx.2.2⟩)
    (fun n => by
      obtain ⟨u, hu, h1, h2⟩ := hcon n
      exact ⟨u, hu, h2, h1⟩)
    (h.isCompact.of_isClosed_subset (hcl 0) Set.inter_subset_left) hcl
  have hu' := Set.mem_iInter.1 hu
  have h0 : u ^ s = 0 := h.sep _ fun n => (hu' n).2.2
  have : u = 0 := IsNilpotent.eq_zero ⟨s, h0⟩
  exact (hu' 0).2.1 ⟨0, R.zero_mem, by simp [this]⟩

/- English proof (translation)
Take `⟨n0, hn0⟩` from `h.pow_step s`. Use `⟨n0, fun v hv => ?_⟩` and prove the remaining obligations. Establish `key : ∀ k : ℕ, (ϖ : K) ^ k * v ∈ R → (ϖ : K) ^ n0 * v ∈ R`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `h0`. Use `R.mul_mem (R.pow_mem h.mem n0) h0` as an intermediate fact. Simplify using `using this`. Consider the case `succ k ih`.

Introduce `hk`. Distinguish the cases in `hkn : k + 1 ≤ n0`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le hkn`. Use `R.mul_mem (R.pow_mem h.mem d) hk` as an intermediate fact. Establish `e : (ϖ : K) ^ n0 * v = (ϖ : K) ^ d * ((ϖ : K) ^ (k + 1) * v)` using `by rw [hd]; ring`.

Rewrite using `[e]` and apply the resulting hypothesis. Apply `ih` to reduce the goal to its premises. Establish `h1 : ((ϖ : K) ^ (k + 1) * v) ^ s ∈ I R ((ϖ : K) ^ n0)`. Establish `hle : n0 ≤ (k + 1) * s` using `by nlinarith`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le hle`.

Conclude with `⟨(ϖ : K) ^ d * v ^ s, R.mul_mem (R.pow_mem h.mem d) hv, by`. Rewrite using `[mul_pow, ← pow_mul, hd]`. Use the proof step `ring⟩`. Take `⟨r, hr, e⟩` from `hn0 _ hk h1`. Establish `i1 : ((ϖ⁻¹ : Kˣ) : K) * (ϖ : K) = 1` using `by simp`.

Establish `: (ϖ : K) ^ k * v = r`. Take the linear combination `((ϖ⁻¹ : Kˣ) : K) * e + (r - (ϖ : K) ^ k * v) * i1`. Rewrite using `[this]` and apply the resulting hypothesis. Take `⟨k, hk⟩` from `h.absorb v`. Conclude with `key k hk`.
-/
theorem Adic.root_bounded (h : Adic R ϖ) [IsReduced K] (s : ℕ) (hs : 1 ≤ s) :
    ∃ n0 : ℕ, ∀ v : K, v ^ s ∈ R → (ϖ : K) ^ n0 * v ∈ R := by
  obtain ⟨n0, hn0⟩ := h.pow_step s
  refine ⟨n0, fun v hv => ?_⟩
  have key : ∀ k : ℕ, (ϖ : K) ^ k * v ∈ R → (ϖ : K) ^ n0 * v ∈ R := by
    intro k
    induction k with
    | zero =>
      intro h0
      have := R.mul_mem (R.pow_mem h.mem n0) h0
      simpa using this
    | succ k ih =>
      intro hk
      by_cases hkn : k + 1 ≤ n0
      · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hkn
        have := R.mul_mem (R.pow_mem h.mem d) hk
        have e : (ϖ : K) ^ n0 * v = (ϖ : K) ^ d * ((ϖ : K) ^ (k + 1) * v) := by rw [hd]; ring
        rwa [e]
      · apply ih
        have h1 : ((ϖ : K) ^ (k + 1) * v) ^ s ∈ I R ((ϖ : K) ^ n0) := by
          have hle : n0 ≤ (k + 1) * s := by nlinarith
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
          exact ⟨(ϖ : K) ^ d * v ^ s, R.mul_mem (R.pow_mem h.mem d) hv, by
            rw [mul_pow, ← pow_mul, hd]; ring⟩
        obtain ⟨r, hr, e⟩ := hn0 _ hk h1
        have i1 : ((ϖ⁻¹ : Kˣ) : K) * (ϖ : K) = 1 := by simp
        have : (ϖ : K) ^ k * v = r := by
          linear_combination ((ϖ⁻¹ : Kˣ) : K) * e + (r - (ϖ : K) ^ k * v) * i1
        rwa [this]
  obtain ⟨k, hk⟩ := h.absorb v
  exact key k hk

/- English proof (translation)
Take `⟨x0, hx0⟩` from `hne`. Establish `hx : ∀ n, T^[n] x0 ∈ X`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact hx0`.

Consider the case `succ n ih => rw [Function.iterate_succ_apply']`. Conclude with `hT _ ih`. Establish `hstep : ∀ n, rel n (T^[n + 1] x0) (T^[n] x0)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => exact h0 _ (hx 1) _ (hx 0)`. Consider the case `succ n ih`. Establish `h2` using `hc n _ (hx _) _ (hx _) ih`. Rewrite `h2` using `[← Function.iterate_succ_apply' T (n + 1), ← Function.iterate_succ_apply' T n]`. Then use the resulting hypothesis. Take `⟨x, hxx⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (fun n => X ∩ {x | rel n x (T^[n] x0)}) (fun n x hx => ⟨hx.1, htrans n _ _ _ (hmono n _ _ hx.2) (hstep n)⟩) (fun n => ⟨_, hx n, hrefl n _⟩) (hX.of_isClosed_subset (hXc.inter (hcl 0 _)) Set.inter_subset_left) (fun n …`.

Establish `hxx'` using `Set.mem_iInter.1 hxx`. Use `⟨x, (hxx' 0).1, hsep _ _ fun n => hmono n _ _ ?_⟩` and prove the remaining obligations. Establish `h1` using `hc n _ (hxx' n).1 _ (hx n) (hxx' n).2`. Rewrite `h1` using `[← Function.iterate_succ_apply' T n]`. Conclude with `htrans _ _ _ _ h1 (hsymm _ _ _ (hxx' (n + 1)).2)`.
-/
theorem fixed_point {E : Type} [TopologicalSpace E] (X : Set E) (hX : IsCompact X) (hXc : IsClosed X)
    (hne : X.Nonempty) (rel : ℕ → E → E → Prop) (hcl : ∀ n y, IsClosed {x | rel n x y})
    (h0 : ∀ x ∈ X, ∀ y ∈ X, rel 0 x y) (hrefl : ∀ n x, rel n x x)
    (hmono : ∀ n x y, rel (n + 1) x y → rel n x y)
    (htrans : ∀ n x y z, rel n x y → rel n y z → rel n x z)
    (hsymm : ∀ n x y, rel n x y → rel n y x) (hsep : ∀ x y, (∀ n, rel n x y) → x = y)
    (T : E → E) (hT : ∀ x ∈ X, T x ∈ X)
    (hc : ∀ n, ∀ x ∈ X, ∀ y ∈ X, rel n x y → rel (n + 1) (T x) (T y)) : ∃ x ∈ X, T x = x := by
  obtain ⟨x0, hx0⟩ := hne
  have hx : ∀ n, T^[n] x0 ∈ X := by
    intro n
    induction n with
    | zero => exact hx0
    | succ n ih => rw [Function.iterate_succ_apply']; exact hT _ ih
  have hstep : ∀ n, rel n (T^[n + 1] x0) (T^[n] x0) := by
    intro n
    induction n with
    | zero => exact h0 _ (hx 1) _ (hx 0)
    | succ n ih =>
      have h2 := hc n _ (hx _) _ (hx _) ih
      rwa [← Function.iterate_succ_apply' T (n + 1), ← Function.iterate_succ_apply' T n] at h2
  obtain ⟨x, hxx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => X ∩ {x | rel n x (T^[n] x0)})
    (fun n x hx => ⟨hx.1, htrans n _ _ _ (hmono n _ _ hx.2) (hstep n)⟩)
    (fun n => ⟨_, hx n, hrefl n _⟩)
    (hX.of_isClosed_subset (hXc.inter (hcl 0 _)) Set.inter_subset_left)
    (fun n => hXc.inter (hcl n _))
  have hxx' := Set.mem_iInter.1 hxx
  refine ⟨x, (hxx' 0).1, hsep _ _ fun n => hmono n _ _ ?_⟩
  have h1 := hc n _ (hxx' n).1 _ (hx n) (hxx' n).2
  rw [← Function.iterate_succ_apply' T n] at h1
  exact htrans _ _ _ _ h1 (hsymm _ _ _ (hxx' (n + 1)).2)

/- English proof (translation)
Use `h.t2` as an intermediate fact. Use `fixed_point X hX hXc hne (fun n x y => ∀ i, co i x - co i y ∈ I R ((ϖ : K) ^ n)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ T hT hc` and prove the remaining obligations. Introduce `n y`. Establish `: {x | ∀ i, co i x - co i y ∈ I R ((ϖ : K) ^ n)} = ⋂ i, (fun x => co i x - co i y) ⁻¹' I R ((ϖ : K) ^ n)`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `isClosed_iInter fun i => (I_compact h.isCompact _).isClosed.preimage ((hco i).sub continuous_const)`. Introduce `x hx y hy i`. Conclude with `⟨_, R.sub_mem (hXR x hx i) (hXR y hy i), by simp⟩`.

Introduce `n x i`. Conclude with `⟨0, R.zero_mem, by simp⟩`. Introduce `n x y hxy i`. Conclude with `I_anti h.mem (Nat.le_succ n) (hxy i)`. Introduce `n x y z h1 h2 i`.

Take `⟨r, hr, e⟩` from `h1 i`. Take `⟨r', hr', e'⟩` from `h2 i`. Conclude with `⟨r + r', R.add_mem hr hr', by linear_combination e + e'⟩`. Introduce `n x y h1 i`. Take `⟨r, hr, e⟩` from `h1 i`.

Conclude with `⟨-r, R.neg_mem hr, by linear_combination -e⟩`. Introduce `x y hxy`. Conclude with `hinj x y fun i => sub_eq_zero.1 (h.sep _ fun n => hxy n i)`.
-/
theorem Adic.fp (h : Adic R ϖ) {E ι : Type} [TopologicalSpace E] (co : ι → E → K)
    (hco : ∀ i, Continuous (co i)) (hinj : ∀ x y, (∀ i, co i x = co i y) → x = y)
    (X : Set E) (hX : IsCompact X) (hXc : IsClosed X) (hne : X.Nonempty)
    (hXR : ∀ x ∈ X, ∀ i, co i x ∈ R) (T : E → E) (hT : ∀ x ∈ X, T x ∈ X)
    (hc : ∀ n, ∀ x ∈ X, ∀ y ∈ X, (∀ i, co i x - co i y ∈ I R ((ϖ : K) ^ n)) →
      ∀ i, co i (T x) - co i (T y) ∈ I R ((ϖ : K) ^ (n + 1))) : ∃ x ∈ X, T x = x := by
  have := h.t2
  refine fixed_point X hX hXc hne (fun n x y => ∀ i, co i x - co i y ∈ I R ((ϖ : K) ^ n))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ T hT hc
  · intro n y
    have : {x | ∀ i, co i x - co i y ∈ I R ((ϖ : K) ^ n)} =
        ⋂ i, (fun x => co i x - co i y) ⁻¹' I R ((ϖ : K) ^ n) := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun i =>
      (I_compact h.isCompact _).isClosed.preimage ((hco i).sub continuous_const)
  · intro x hx y hy i
    exact ⟨_, R.sub_mem (hXR x hx i) (hXR y hy i), by simp⟩
  · intro n x i
    exact ⟨0, R.zero_mem, by simp⟩
  · intro n x y hxy i
    exact I_anti h.mem (Nat.le_succ n) (hxy i)
  · intro n x y z h1 h2 i
    obtain ⟨r, hr, e⟩ := h1 i
    obtain ⟨r', hr', e'⟩ := h2 i
    exact ⟨r + r', R.add_mem hr hr', by linear_combination e + e'⟩
  · intro n x y h1 i
    obtain ⟨r, hr, e⟩ := h1 i
    exact ⟨-r, R.neg_mem hr, by linear_combination -e⟩
  · intro x y hxy
    exact hinj x y fun i => sub_eq_zero.1 (h.sep _ fun n => hxy n i)

/- English proof (translation)
The claim follows from `Λ.smul_mem (⟨r, hr⟩ : R) hx`.
-/
theorem mul_mem_sub (Λ : Submodule R K) {r x : K} (hr : r ∈ R) (hx : x ∈ Λ) : r * x ∈ Λ :=
  Λ.smul_mem (⟨r, hr⟩ : R) hx

/- English proof (translation)
Establish `hfg : (Submodule.span R (Set.range d)).FG` using `Submodule.fg_span (Set.finite_range d)`. Establish `hJ : Ideal.span {(⟨(ϖ : K), h.mem⟩ : R)} ≤ Ideal.jacobson ⊥`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Use `Ideal.mem_jacobson_bot.2 fun y => ?_` and prove the remaining obligations. Take `⟨v, hv, e⟩` from `h.unit_one ((ϖ : K) * (y : K)) ⟨y, y.2, rfl⟩`.

Use `IsUnit.of_mul_eq_one (⟨v, hv⟩ : R) (Subtype.ext ?_)` and prove the remaining obligations. Use `show ((ϖ : K) * (y : K) + 1) * v = 1`. Take the linear combination `e`. Establish `hle` using `Submodule.le_of_le_smul_of_le_jacobson_bot (N := Λ) hfg hJ (by`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨l, hl, l', hl', e⟩` from `hd (Submodule.span R (Set.range d)) (fun i => Submodule.subset_span ⟨i, rfl⟩) i`. Use `show d i ∈ _`. Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup hl (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl'))`.

Conclude with `fun i => hle (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem Adic.nak (h : Adic R ϖ) {ι : Type} [Finite ι] (d : ι → K) (Λ : Submodule R K)
    (hd : ∀ Λ' : Submodule R K, (∀ i, d i ∈ Λ') → ∀ i, ∃ l ∈ Λ, ∃ l' ∈ Λ', d i = l + (ϖ : K) * l') :
    ∀ i, d i ∈ Λ := by
  have hfg : (Submodule.span R (Set.range d)).FG := Submodule.fg_span (Set.finite_range d)
  have hJ : Ideal.span {(⟨(ϖ : K), h.mem⟩ : R)} ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    refine Ideal.mem_jacobson_bot.2 fun y => ?_
    obtain ⟨v, hv, e⟩ := h.unit_one ((ϖ : K) * (y : K)) ⟨y, y.2, rfl⟩
    refine IsUnit.of_mul_eq_one (⟨v, hv⟩ : R) (Subtype.ext ?_)
    show ((ϖ : K) * (y : K) + 1) * v = 1
    linear_combination e
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot (N := Λ) hfg hJ (by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨l, hl, l', hl', e⟩ := hd (Submodule.span R (Set.range d)) (fun i => Submodule.subset_span ⟨i, rfl⟩) i
    show d i ∈ _
    rw [e]
    exact Submodule.add_mem_sup hl
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl'))
  exact fun i => hle (Submodule.subset_span ⟨i, rfl⟩)

end Top

section Mat

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ}

def Rs (R : Subring K) : Submodule R K where
  carrier := R
  add_mem' := R.add_mem
  zero_mem' := R.zero_mem
  smul_mem' := fun c _ hx => R.mul_mem c.2 hx

def sm (a : K) (Λ : Submodule R K) : Submodule R K where
  carrier := {x | ∃ l ∈ Λ, x = a * l}
  add_mem' := by
    rintro _ _ ⟨l, hl, rfl⟩ ⟨l', hl', rfl⟩
    exact ⟨l + l', Λ.add_mem hl hl', by ring⟩
  zero_mem' := ⟨0, Λ.zero_mem, by simp⟩
  smul_mem' := by
    rintro c _ ⟨l, hl, rfl⟩
    exact ⟨c • l, Λ.smul_mem c hl, by rw [Subring.smul_def, Subring.smul_def]; simp only [smul_eq_mul]; ring⟩

def MemM (Λ : Submodule R K) (X : Matrix (Fin m) (Fin m) K) : Prop := ∀ i j, X i j ∈ Λ

/- English proof (translation)
Introduce `i j` and use `Λ.add_mem (hX i j) (hY i j)`.
-/
theorem MemM.add {Λ : Submodule R K} {X Y : Matrix (Fin m) (Fin m) K} (hX : MemM Λ X)
    (hY : MemM Λ Y) : MemM Λ (X + Y) := fun i j => Λ.add_mem (hX i j) (hY i j)

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact Λ.sum_mem fun k _ => mul_mem_sub Λ (hA i k) (hX k j)`.
-/
theorem MemM.mul_left {Λ : Submodule R K} {A X : Matrix (Fin m) (Fin m) K} (hA : ∀ i j, A i j ∈ R)
    (hX : MemM Λ X) : MemM Λ (A * X) := fun i j => by
  rw [Matrix.mul_apply]
  exact Λ.sum_mem fun k _ => mul_mem_sub Λ (hA i k) (hX k j)

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact Λ.sum_mem fun k _ => by rw [mul_comm]; exact mul_mem_sub Λ (hA k j) (hX i k)`.
-/
theorem MemM.mul_right {Λ : Submodule R K} {A X : Matrix (Fin m) (Fin m) K} (hA : ∀ i j, A i j ∈ R)
    (hX : MemM Λ X) : MemM Λ (X * A) := fun i j => by
  rw [Matrix.mul_apply]
  exact Λ.sum_mem fun k _ => by rw [mul_comm]; exact mul_mem_sub Λ (hA k j) (hX i k)

/- English proof (translation)
The claim follows from `MemM.mul_left (Λ := Rs R) hA hB`.
-/
theorem int_mul {A B : Matrix (Fin m) (Fin m) K} (hA : ∀ i j, A i j ∈ R) (hB : ∀ i j, B i j ∈ R) :
    ∀ i j, (A * B) i j ∈ R := MemM.mul_left (Λ := Rs R) hA hB

/- English proof (translation)
Establish `e : Y * G * Y - Y' * G * Y' = (Y - Y') * (G * Y) + Y' * G * (Y - Y')` using `by noncomm_ring`. Rewrite using `[e]`. Conclude with `(hd.mul_right (int_mul hG hY)).add (hd.mul_left (int_mul hY' hG))`.
-/
theorem quad_diff {Λ : Submodule R K} {G Y Y' : Matrix (Fin m) (Fin m) K} (hG : ∀ i j, G i j ∈ R)
    (hY : ∀ i j, Y i j ∈ R) (hY' : ∀ i j, Y' i j ∈ R) (hd : MemM Λ (Y - Y')) :
    MemM Λ (Y * G * Y - Y' * G * Y') := by
  have e : Y * G * Y - Y' * G * Y' = (Y - Y') * (G * Y) + Y' * G * (Y - Y') := by
    noncomm_ring
  rw [e]
  exact (hd.mul_right (int_mul hG hY)).add (hd.mul_left (int_mul hY' hG))

/- English proof (translation)
Use `h.t2` as an intermediate fact. Establish `hXe : {Y : Matrix (Fin m) (Fin m) K | ∀ i j, Y i j ∈ R} = Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => (R : Set K)`. Use extensionality with `Y`. Conclude with `⟨fun hY i _ j _ => hY i j, fun hY i j => hY i trivial j trivial⟩`. Establish `hXc : IsCompact {Y : Matrix (Fin m) (Fin m) K | ∀ i j, Y i j ∈ R}`.

Rewrite using `[hXe]`. Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => h.isCompact`. Take `⟨Y, hY, e⟩` from `h.fp (E := Matrix (Fin m) (Fin m) K) (ι := Fin m × Fin m) (fun p Y => Y p.1 p.2) (fun p => continuous_id.matrix_elem p.1 p.2) (fun x y hxy => Matrix.ext fun i j => hxy (i, j)) {Y | ∀ i j, Y i j ∈ R} hXc hXc.isClosed ⟨0, fun i j => R.zero_mem⟩ (fun x hx p => hx p.1 p.2) (fun Y => …`. Establish `h1` using `quad_diff (Λ := sm ((ϖ : K) ^ n) (Rs R)) hG hY hY' (fun i j => hd (i, j))`. Take `⟨l, hl, e⟩` from `h1 p.1 p.2`.

Use `⟨-l, R.neg_mem hl, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e ⊢`. Take the linear combination `(-(ϖ : K)) * e)`. Conclude with `⟨Y, hY, e.symm⟩`.
-/
theorem Adic.sqrtM (h : Adic R ϖ) (G N : Matrix (Fin m) (Fin m) K) (hG : ∀ i j, G i j ∈ R)
    (hN : ∀ i j, N i j ∈ R) :
    ∃ Y : Matrix (Fin m) (Fin m) K, (∀ i j, Y i j ∈ R) ∧ Y = N - (ϖ : K) • (Y * G * Y) := by
  have := h.t2
  have hXe : {Y : Matrix (Fin m) (Fin m) K | ∀ i j, Y i j ∈ R} =
      Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => (R : Set K) := by
    ext Y
    exact ⟨fun hY i _ j _ => hY i j, fun hY i j => hY i trivial j trivial⟩
  have hXc : IsCompact {Y : Matrix (Fin m) (Fin m) K | ∀ i j, Y i j ∈ R} := by
    rw [hXe]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => h.isCompact
  obtain ⟨Y, hY, e⟩ := h.fp (E := Matrix (Fin m) (Fin m) K) (ι := Fin m × Fin m)
    (fun p Y => Y p.1 p.2) (fun p => continuous_id.matrix_elem p.1 p.2)
    (fun x y hxy => Matrix.ext fun i j => hxy (i, j))
    {Y | ∀ i j, Y i j ∈ R} hXc hXc.isClosed ⟨0, fun i j => R.zero_mem⟩ (fun x hx p => hx p.1 p.2)
    (fun Y => N - (ϖ : K) • (Y * G * Y))
    (fun Y hY i j => R.sub_mem (hN i j) (R.mul_mem h.mem (int_mul (int_mul hY hG) hY i j)))
    (fun n Y hY Y' hY' hd p => by
      have h1 := quad_diff (Λ := sm ((ϖ : K) ^ n) (Rs R)) hG hY hY' (fun i j => hd (i, j))
      obtain ⟨l, hl, e⟩ := h1 p.1 p.2
      refine ⟨-l, R.neg_mem hl, ?_⟩
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e ⊢
      linear_combination (-(ϖ : K)) * e)
  exact ⟨Y, hY, e.symm⟩

/- English proof (translation)
Use `h.nak (ι := Fin m × Fin m) (fun p => (Y - Y') p.1 p.2) Λ (fun Λ' hd p => by` as an intermediate fact. Establish `h1` using `quad_diff (Λ := Λ') hG hY hY' (fun i j => hd (i, j))`. Use `⟨_, hN p.1 p.2, _, Λ'.neg_mem (h1 p.1 p.2), ?_⟩` and prove the remaining obligations. Establish `e1` using `congrFun (congrFun e p.1) p.2`. Establish `e2` using `congrFun (congrFun e' p.1) p.2`.

Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2 ⊢`. Take the linear combination `e1 - e2)`. Conclude with `fun i j => this (i, j)`.
-/
theorem Adic.sqrt_lip (h : Adic R ϖ) {G N N' Y Y' : Matrix (Fin m) (Fin m) K}
    (hG : ∀ i j, G i j ∈ R) (hY : ∀ i j, Y i j ∈ R) (hY' : ∀ i j, Y' i j ∈ R)
    (e : Y = N - (ϖ : K) • (Y * G * Y)) (e' : Y' = N' - (ϖ : K) • (Y' * G * Y'))
    (Λ : Submodule R K) (hN : MemM Λ (N - N')) : MemM Λ (Y - Y') := by
  have := h.nak (ι := Fin m × Fin m) (fun p => (Y - Y') p.1 p.2) Λ (fun Λ' hd p => by
    have h1 := quad_diff (Λ := Λ') hG hY hY' (fun i j => hd (i, j))
    refine ⟨_, hN p.1 p.2, _, Λ'.neg_mem (h1 p.1 p.2), ?_⟩
    have e1 := congrFun (congrFun e p.1) p.2
    have e2 := congrFun (congrFun e' p.1) p.2
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2 ⊢
    linear_combination e1 - e2)
  exact fun i j => this (i, j)

/- English proof (translation)
Establish `e' : Yᵀ = N - (ϖ : K) • (Yᵀ * G * Yᵀ)` using `by conv_lhs => rw [e]`. Rewrite using `[Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, hGs, hNs, Matrix.mul_assoc]`. Use `h.sqrt_lip hG (fun i j => hY j i) hY e' e ⊥ (fun i j => by simp)` as an intermediate fact. Use extensionality with `i j`. Establish `h1 : Yᵀ i j - Y i j = 0` using `this i j`.

Conclude with `sub_eq_zero.1 h1`.
-/
theorem Adic.sqrt_symm (h : Adic R ϖ) {G N Y : Matrix (Fin m) (Fin m) K}
    (hG : ∀ i j, G i j ∈ R) (hY : ∀ i j, Y i j ∈ R) (e : Y = N - (ϖ : K) • (Y * G * Y))
    (hGs : Gᵀ = G) (hNs : Nᵀ = N) : Yᵀ = Y := by
  have e' : Yᵀ = N - (ϖ : K) • (Yᵀ * G * Yᵀ) := by
    conv_lhs => rw [e]
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      hGs, hNs, Matrix.mul_assoc]
  have := h.sqrt_lip hG (fun i j => hY j i) hY e' e ⊥ (fun i j => by simp)
  ext i j
  have h1 : Yᵀ i j - Y i j = 0 := this i j
  exact sub_eq_zero.1 h1

/- English proof (translation)
Use `h.t2` as an intermediate fact. Establish `hmv : ∀ v, (∀ k, v k ∈ 𝔅) → ∀ k, (Y v *ᵥ v) k ∈ 𝔅` using `fun v hv k => by`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `𝔅.sum_mem fun j _ => mul_mem_sub 𝔅 (hYR v hv k j) (hv j)`. Establish `key : ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ 𝔅) → (∀ k, v' k ∈ 𝔅) → (∀ k, v k - v' k ∈ Λ) → ∀ k, (Y v *ᵥ v) k - (Y v' *ᵥ v') k ∈ Λ`.

Introduce `Λ v v' hv hv' hd k`. Establish `e : (Y v *ᵥ v) k - (Y v' *ᵥ v') k = ∑ j, (Y v k j * (v j - v' j) + v' j * (Y v - Y v') k j)`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.sub_apply]`. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.

Rewrite using `[e]`. Conclude with `Λ.sum_mem fun j _ => Λ.add_mem (mul_mem_sub Λ (hYR v hv k j) (hd j)) (mul_mem_sub Λ (hBR _ (hv' j)) (hYL Λ v v' hv hv' hd k j))`. Use `⟨fun v hv k => 𝔅.add_mem (hv k) (mul_mem_sub 𝔅 h.mem (hmv v hv k)), ?_, ?_⟩` and prove the remaining obligations. Introduce `η hη`. Establish `hXe : {v : Fin m → K | ∀ k, v k ∈ 𝔅} = Set.pi Set.univ fun _ : Fin m => (𝔅 : Set K)`.

Use extensionality with `v`. Simplify using `[Set.mem_pi]`. Establish `hBcomp : IsCompact (𝔅 : Set K)` using `h.isCompact.of_isClosed_subset hBc hBR`. Establish `hXc : IsCompact {v : Fin m → K | ∀ k, v k ∈ 𝔅}`. Rewrite using `[hXe]`.

Conclude with `isCompact_univ_pi fun _ => hBcomp`. Take `⟨v, hv, e⟩` from `h.fp (E := Fin m → K) (ι := Fin m) (fun k v => v k) (fun k => continuous_apply k) (fun x y hxy => funext hxy) {v | ∀ k, v k ∈ 𝔅} hXc hXc.isClosed ⟨0, fun k => 𝔅.zero_mem⟩ (fun x hx k => hBR _ (hx k)) (fun v => η - (ϖ : K) • (Y v *ᵥ v)) (fun v hv k => 𝔅.sub_mem (hη k) (mul_mem_sub …`. Take `⟨l, hl, e⟩` from `key (sm ((ϖ : K) ^ n) (Rs R)) v v' hv hv' hd k`. Use `⟨-l, R.neg_mem hl, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`.

Take the linear combination `(-(ϖ : K)) * e)`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Establish `e2 : η - (ϖ : K) • (Y v *ᵥ v) = v` using `e`. Conclude with `(sub_eq_iff_eq_add.1 e2).symm`. Introduce `Λ v v' hv hv'`.

Prove the components needed by the constructor for the conclusion. Introduce `hd`. Use `h.nak (fun k => v k - v' k) Λ fun Λ' hd' k => ?_` and prove the remaining obligations. Use `⟨_, hd k, _, Λ'.neg_mem (key Λ' v v' hv hv' hd' k), ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `hd k`. Establish `e : (v + (ϖ : K) • (Y v *ᵥ v)) k - (v' + (ϖ : K) • (Y v' *ᵥ v')) k = (v k - v' k) + (ϖ : K) * ((Y v *ᵥ v) k - (Y v' *ᵥ v') k)`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Λ.add_mem (hd k) (mul_mem_sub Λ h.mem (key Λ v v' hv hv' hd k))`.
-/
theorem Adic.core (h : Adic R ϖ) (𝔅 : Submodule R K) (hBR : ∀ x ∈ 𝔅, x ∈ R)
    (hBc : IsClosed (𝔅 : Set K)) (Y : (Fin m → K) → Matrix (Fin m) (Fin m) K)
    (hYR : ∀ v, (∀ k, v k ∈ 𝔅) → ∀ i j, Y v i j ∈ R)
    (hYL : ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ 𝔅) → (∀ k, v' k ∈ 𝔅) →
      (∀ k, v k - v' k ∈ Λ) → MemM Λ (Y v - Y v')) :
    (∀ v, (∀ k, v k ∈ 𝔅) → ∀ k, (v + (ϖ : K) • (Y v *ᵥ v)) k ∈ 𝔅) ∧
    (∀ η : Fin m → K, (∀ k, η k ∈ 𝔅) → ∃ v, (∀ k, v k ∈ 𝔅) ∧ v + (ϖ : K) • (Y v *ᵥ v) = η) ∧
    ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ 𝔅) → (∀ k, v' k ∈ 𝔅) →
      ((∀ k, (v + (ϖ : K) • (Y v *ᵥ v)) k - (v' + (ϖ : K) • (Y v' *ᵥ v')) k ∈ Λ) ↔
        ∀ k, v k - v' k ∈ Λ) := by
  have := h.t2
  have hmv : ∀ v, (∀ k, v k ∈ 𝔅) → ∀ k, (Y v *ᵥ v) k ∈ 𝔅 := fun v hv k => by
    simp only [Matrix.mulVec, dotProduct]
    exact 𝔅.sum_mem fun j _ => mul_mem_sub 𝔅 (hYR v hv k j) (hv j)
  have key : ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ 𝔅) → (∀ k, v' k ∈ 𝔅) →
      (∀ k, v k - v' k ∈ Λ) → ∀ k, (Y v *ᵥ v) k - (Y v' *ᵥ v') k ∈ Λ := by
    intro Λ v v' hv hv' hd k
    have e : (Y v *ᵥ v) k - (Y v' *ᵥ v') k =
        ∑ j, (Y v k j * (v j - v' j) + v' j * (Y v - Y v') k j) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact Λ.sum_mem fun j _ => Λ.add_mem (mul_mem_sub Λ (hYR v hv k j) (hd j))
      (mul_mem_sub Λ (hBR _ (hv' j)) (hYL Λ v v' hv hv' hd k j))
  refine ⟨fun v hv k => 𝔅.add_mem (hv k) (mul_mem_sub 𝔅 h.mem (hmv v hv k)), ?_, ?_⟩
  · intro η hη
    have hXe : {v : Fin m → K | ∀ k, v k ∈ 𝔅} = Set.pi Set.univ fun _ : Fin m => (𝔅 : Set K) := by
      ext v; simp [Set.mem_pi]
    have hBcomp : IsCompact (𝔅 : Set K) := h.isCompact.of_isClosed_subset hBc hBR
    have hXc : IsCompact {v : Fin m → K | ∀ k, v k ∈ 𝔅} := by
      rw [hXe]; exact isCompact_univ_pi fun _ => hBcomp
    obtain ⟨v, hv, e⟩ := h.fp (E := Fin m → K) (ι := Fin m) (fun k v => v k)
      (fun k => continuous_apply k) (fun x y hxy => funext hxy) {v | ∀ k, v k ∈ 𝔅} hXc hXc.isClosed
      ⟨0, fun k => 𝔅.zero_mem⟩ (fun x hx k => hBR _ (hx k))
      (fun v => η - (ϖ : K) • (Y v *ᵥ v))
      (fun v hv k => 𝔅.sub_mem (hη k) (mul_mem_sub 𝔅 h.mem (hmv v hv k)))
      (fun n v hv v' hv' hd k => by
        obtain ⟨l, hl, e⟩ := key (sm ((ϖ : K) ^ n) (Rs R)) v v' hv hv' hd k
        refine ⟨-l, R.neg_mem hl, ?_⟩
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (-(ϖ : K)) * e)
    refine ⟨v, hv, ?_⟩
    have e2 : η - (ϖ : K) • (Y v *ᵥ v) = v := e
    exact (sub_eq_iff_eq_add.1 e2).symm
  · intro Λ v v' hv hv'
    constructor
    · intro hd
      refine h.nak (fun k => v k - v' k) Λ fun Λ' hd' k => ?_
      refine ⟨_, hd k, _, Λ'.neg_mem (key Λ' v v' hv hv' hd' k), ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · intro hd k
      have e : (v + (ϖ : K) • (Y v *ᵥ v)) k - (v' + (ϖ : K) • (Y v' *ᵥ v')) k =
          (v k - v' k) + (ϖ : K) * ((Y v *ᵥ v) k - (Y v' *ᵥ v') k) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      exact Λ.add_mem (hd k) (mul_mem_sub Λ h.mem (key Λ v v' hv hv' hd k))

end Mat

section Alg

variable {K : Type} [CommRing K] {m : ℕ}

def piW (w : Fin m → K) (j : Fin m) : K := ∏ k ∈ Finset.univ.filter (· < j), w k

def uW (w : Fin m → K) (i j : Fin m) : K := w i * w j * piW w j

def MW (w : Fin m → K) : Matrix (Fin m) (Fin m) K := Matrix.of fun i j =>
  (if i = j then 2 * w i else 0) + (if j < i then uW w i j else 0) + (if i < j then uW w j i else 0)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [MW, Matrix.transpose_apply, Matrix.of_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `only [hij, Ne.symm hij, if_false]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem MW_symm (w : Fin m → K) : (MW w)ᵀ = MW w := by
  ext i j
  simp only [MW, Matrix.transpose_apply, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp only [hij, Ne.symm hij, if_false]; ring

/- English proof (translation)
Establish `e : ∀ i j, y i * (MW w i j * y j) = (if i = j then 2 * (y i ^ 2 * w i) else 0) + (if j < i then y i * uW w i j * y j else 0) + (if i < j then y j * uW w j i * y i else 0)`. Introduce `i j`. Simplify using `only [MW, Matrix.of_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `simp only [hij, if_false] split_ifs <;> ring`. Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, e, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_comm (f := fun i j => if i < j then y j * uW w j i * y i else 0)]`.

Simplify using `only [Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_expand (y w : Fin m → K) :
    y ⬝ᵥ (MW w *ᵥ y) = 2 * (∑ i, y i ^ 2 * w i +
      ∑ i, ∑ j, if j < i then y i * uW w i j * y j else 0) := by
  have e : ∀ i j, y i * (MW w i j * y j) = (if i = j then 2 * (y i ^ 2 * w i) else 0) +
      (if j < i then y i * uW w i j * y j else 0) + (if i < j then y j * uW w j i * y i else 0) := by
    intro i j
    simp only [MW, Matrix.of_apply]
    by_cases hij : i = j
    · subst hij; simp; ring
    · simp only [hij, if_false]
      split_ifs <;> ring
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, e, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then y j * uW w j i * y i else 0)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.mul_sum]
  ring

/- English proof (translation)
Establish `ha : ∀ k, 1 - y k * w k = w k` using `fun k => by linear_combination -h k`. Use `Finset.prod_one_sub_ordered s (fun i => y i * w i)` as an intermediate fact. Simplify `this` using `only [ha]`.
-/
theorem prod_ordered (y w : Fin m → K) (h : ∀ k, (1 + y k) * w k = 1) (s : Finset (Fin m)) :
    ∏ i ∈ s, w i = 1 - ∑ i ∈ s, (y i * w i) * ∏ j ∈ s.filter (· < i), w j := by
  have ha : ∀ k, 1 - y k * w k = w k := fun k => by linear_combination -h k
  have := Finset.prod_one_sub_ordered s (fun i => y i * w i)
  simpa only [ha] using this

/- English proof (translation)
Establish `h1 : ∏ k, w k = 1 - ∑ i, (y i * w i) * piW w i` using `prod_ordered y w h Finset.univ`. Establish `h2 : ∀ i, piW w i = 1 - ∑ j, if j < i then (y j * w j) * piW w j else 0`. Introduce `i`. Rewrite using `[← Finset.sum_filter]`. Unfold `piW`.

Rewrite using `[prod_ordered y w h]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hji : j < i` using `(Finset.mem_filter.1 hj).2`. Rewrite using `[Finset.filter_filter]`.

Use `congr 2`. Use `Finset.filter_congr fun k _ => ⟨fun hk => hk.2, fun hk => ⟨hk.trans hji, hk⟩⟩` and prove the remaining obligations. Rewrite using `[h1, ← Finset.sum_add_distrib]`. Establish `e : ∑ k, y k + (1 - ∑ i, (y i * w i) * piW w i) - 1 = ∑ i, (y i - (y i * w i) * piW w i)`. Rewrite using `[Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [h2 i]`. Establish `e2 : ∑ j, (if j < i then y i * uW w i j * y j else 0) = (y i * w i) * ∑ j, if j < i then (y j * w j) * piW w j else 0`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Unfold `uW`. Apply the tactic sequence `split_ifs <;> ring`. Rewrite using `[e2]`.

Take the linear combination `(-(y i)) * h i`.
-/
theorem phase_identity (y w : Fin m → K) (h : ∀ k, (1 + y k) * w k = 1) :
    ∑ k, y k + ∏ k, w k - 1 = ∑ i, y i ^ 2 * w i +
      ∑ i, ∑ j, if j < i then y i * uW w i j * y j else 0 := by
  have h1 : ∏ k, w k = 1 - ∑ i, (y i * w i) * piW w i := prod_ordered y w h Finset.univ
  have h2 : ∀ i, piW w i = 1 - ∑ j, if j < i then (y j * w j) * piW w j else 0 := by
    intro i
    rw [← Finset.sum_filter]
    unfold piW
    rw [prod_ordered y w h]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j < i := (Finset.mem_filter.1 hj).2
    rw [Finset.filter_filter]
    congr 2
    refine Finset.filter_congr fun k _ => ⟨fun hk => hk.2, fun hk => ⟨hk.trans hji, hk⟩⟩
  rw [h1, ← Finset.sum_add_distrib]
  have e : ∑ k, y k + (1 - ∑ i, (y i * w i) * piW w i) - 1 = ∑ i, (y i - (y i * w i) * piW w i) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [h2 i]
  have e2 : ∑ j, (if j < i then y i * uW w i j * y j else 0) =
      (y i * w i) * ∑ j, if j < i then (y j * w j) * piW w j else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold uW
    split_ifs <;> ring
  rw [e2]
  linear_combination (-(y i)) * h i

/- English proof (translation)
Rewrite using `[quad_expand, phase_identity y w h]`.
-/
theorem quad_identity (y w : Fin m → K) (h : ∀ k, (1 + y k) * w k = 1) :
    y ⬝ᵥ (MW w *ᵥ y) = 2 * (∑ k, y k + ∏ k, w k - 1) := by
  rw [quad_expand, phase_identity y w h]

def HH (K : Type) [CommRing K] (m : ℕ) : Matrix (Fin m) (Fin m) K := 1 + Matrix.of fun _ _ => (1 : K)

def HA (K : Type) [CommRing K] (m : ℕ) : Matrix (Fin m) (Fin m) K :=
  ((m + 1 : ℕ) : K) • (1 : Matrix (Fin m) (Fin m) K) - Matrix.of fun _ _ => (1 : K)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [MW, HH, uW, piW, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Finset.prod_const_one, mul_one]`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Simplify using `[h, h.ne, h.le.not_gt]`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Evaluate the numerical expressions. Simplify using `[h, h.ne', h.le.not_gt]`.
-/
theorem MW_one : MW (fun _ : Fin m => (1 : K)) = HH K m := by
  ext i j
  simp only [MW, HH, uW, piW, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply,
    Finset.prod_const_one, mul_one]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne, h.le.not_gt]
  · subst h; simp; norm_num
  · simp [h, h.ne', h.le.not_gt]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`.
-/
theorem ones_sq : (Matrix.of fun _ _ => (1 : K) : Matrix (Fin m) (Fin m) K) * Matrix.of (fun _ _ => (1 : K)) =
    (m : K) • Matrix.of fun _ _ => (1 : K) := by
  ext i j
  simp [Matrix.mul_apply]

/- English proof (translation)
Unfold `HH HA`. Rewrite using `[add_mul, mul_sub, mul_sub, ones_sq]`. Simplify using `only [one_mul, mul_one, Matrix.mul_smul]`. Use `push_cast`. Use `module`.
-/
theorem HH_HA : HH K m * HA K m = ((m + 1 : ℕ) : K) • (1 : Matrix (Fin m) (Fin m) K) := by
  unfold HH HA
  rw [add_mul, mul_sub, mul_sub, ones_sq]
  simp only [one_mul, mul_one, Matrix.mul_smul]
  push_cast
  module

/- English proof (translation)
Unfold `HH HA`. Rewrite using `[mul_add, sub_mul, sub_mul, ones_sq]`. Simplify using `only [one_mul, mul_one, Matrix.smul_mul]`. Use `push_cast`. Use `module`.
-/
theorem HA_HH : HA K m * HH K m = ((m + 1 : ℕ) : K) • (1 : Matrix (Fin m) (Fin m) K) := by
  unfold HH HA
  rw [mul_add, sub_mul, sub_mul, ones_sq]
  simp only [one_mul, mul_one, Matrix.smul_mul]
  push_cast
  module

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[HH, Matrix.one_apply, eq_comm]`.
-/
theorem HH_symm : (HH K m)ᵀ = HH K m := by
  ext i j
  simp [HH, Matrix.one_apply, eq_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[HA, Matrix.one_apply, eq_comm]`.
-/
theorem HA_symm : (HA K m)ᵀ = HA K m := by
  ext i j
  simp [HA, Matrix.one_apply, eq_comm]

/- English proof (translation)
Establish `eN : N = Y + p • (Y * HA K m * Y)` using `by rw [eq_sub_iff_add_eq] at e; exact e.symm`. Establish `e1 : HH K m * (HA K m * Y) = ((m + 1 : ℕ) : K) • Y`. Rewrite using `[← Matrix.mul_assoc, HH_HA, Matrix.smul_mul, one_mul]`. Establish `e2 : Y * HA K m * HH K m = ((m + 1 : ℕ) : K) • Y`. Rewrite using `[Matrix.mul_assoc, HA_HH, Matrix.mul_smul, mul_one]`.

Rewrite using `[Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, Matrix.transpose_mul, hs, HA_symm]`. Simplify using `only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, e1, e2]`. Use `conv_rhs => rw [eN]`. Simplify using `only [Matrix.mul_assoc]`. Use `module`.
-/
theorem conj_identity (p : K) (Y N : Matrix (Fin m) (Fin m) K) (hs : Yᵀ = Y)
    (e : Y = N - p • (Y * HA K m * Y)) :
    (1 + (2 * p) • (HA K m * Y))ᵀ * HH K m * (1 + (2 * p) • (HA K m * Y)) =
      HH K m + (4 * ((m + 1 : ℕ) : K) * p) • N := by
  have eN : N = Y + p • (Y * HA K m * Y) := by rw [eq_sub_iff_add_eq] at e; exact e.symm
  have e1 : HH K m * (HA K m * Y) = ((m + 1 : ℕ) : K) • Y := by
    rw [← Matrix.mul_assoc, HH_HA, Matrix.smul_mul, one_mul]
  have e2 : Y * HA K m * HH K m = ((m + 1 : ℕ) : K) • Y := by
    rw [Matrix.mul_assoc, HA_HH, Matrix.mul_smul, mul_one]
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, Matrix.transpose_mul, hs,
    HA_symm]
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, e1, e2]
  conv_rhs => rw [eN]
  simp only [Matrix.mul_assoc]
  module

end Alg

section Lip

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ} {c : K}

def LW (R : Subring K) (c : K) (f : (Fin m → K) → K) : Prop :=
  (∀ v, (∀ k, v k ∈ R) → f v ∈ R) ∧
  ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ R) → (∀ k, v' k ∈ R) →
    (∀ k, v k - v' k ∈ Λ) → f v - f v' ∈ sm c Λ

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ => hr, fun Λ _ _ _ _ _ => by simp⟩`.
-/
theorem LW.const {r : K} (hr : r ∈ R) : LW R c (fun _ : Fin m → K => r) :=
  ⟨fun _ _ => hr, fun Λ _ _ _ _ _ => by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun v hv => R.add_mem (hf.1 v hv) (hg.1 v hv), fun Λ v v' hv hv' hd => by have := (sm c Λ).add_mem (hf.2 Λ v v' hv hv' hd) (hg.2 Λ v v' hv hv' hd) have e : f v + g v - (f v' + g v') = f v - f v' + (g v - g v') := by ring rw [e]; exact this⟩`.
-/
theorem LW.add {f g : (Fin m → K) → K} (hf : LW R c f) (hg : LW R c g) :
    LW R c (fun v => f v + g v) :=
  ⟨fun v hv => R.add_mem (hf.1 v hv) (hg.1 v hv), fun Λ v v' hv hv' hd => by
    have := (sm c Λ).add_mem (hf.2 Λ v v' hv hv' hd) (hg.2 Λ v v' hv hv' hd)
    have e : f v + g v - (f v' + g v') = f v - f v' + (g v - g v') := by ring
    rw [e]; exact this⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun v hv => R.mul_mem (hf.1 v hv) (hg.1 v hv), fun Λ v v' hv hv' hd => by have := (sm c Λ).add_mem (mul_mem_sub _ (hf.1 v hv) (hg.2 Λ v v' hv hv' hd)) (mul_mem_sub _ (hg.1 v' hv') (hf.2 Λ v v' hv hv' hd)) have e : f v * g v - f v' * g v' = f v * (g v - g v') + g v' * (f v - f v' …`.
-/
theorem LW.mul {f g : (Fin m → K) → K} (hf : LW R c f) (hg : LW R c g) :
    LW R c (fun v => f v * g v) :=
  ⟨fun v hv => R.mul_mem (hf.1 v hv) (hg.1 v hv), fun Λ v v' hv hv' hd => by
    have := (sm c Λ).add_mem (mul_mem_sub _ (hf.1 v hv) (hg.2 Λ v v' hv hv' hd))
      (mul_mem_sub _ (hg.1 v' hv') (hf.2 Λ v v' hv hv' hd))
    have e : f v * g v - f v' * g v' = f v * (g v - g v') + g v' * (f v - f v') := by ring
    rw [e]; exact this⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using LW.const (R := R) (c := c) (m := m) R.one_mem`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.prod_insert ha]`. Conclude with `(hf a).mul ih`.
-/
theorem LW.prod {ι : Type} (s : Finset ι) {f : ι → (Fin m → K) → K} (hf : ∀ i, LW R c (f i)) :
    LW R c (fun v => ∏ i ∈ s, f i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LW.const (R := R) (c := c) (m := m) R.one_mem
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a).mul ih

/- English proof (translation)
Distinguish the cases in `hp : p`. Simplify `hf` using `[hp]`. Simplify `LW.const (R := R) (c := c) (m := m) R.zero_mem` using `[hp]`.
-/
theorem LW.ite (p : Prop) [Decidable p] {f : (Fin m → K) → K} (hf : LW R c f) :
    LW R c (fun v => if p then f v else 0) := by
  by_cases hp : p
  · simpa [hp] using hf
  · simpa [hp] using LW.const (R := R) (c := c) (m := m) R.zero_mem

noncomputable def wv (c : K) (v : Fin m → K) (k : Fin m) : K := Ring.inverse (1 + c * v k)

/- English proof (translation)
Take `⟨u, hu, e⟩` from `hc _ hv`. Establish `h1 : (1 + c * v k) * wv c v k = 1` using `Ring.mul_inverse_cancel _ (IsUnit.of_mul_eq_one _ e)`. Establish `: wv c v k = u` using `by linear_combination u * h1 - wv c v k * e`. Conclude with `⟨h1, this ▸ hu⟩`.
-/
theorem wv_spec (hc : ∀ r ∈ R, ∃ u ∈ R, (1 + c * r) * u = 1) (v : Fin m → K) (k : Fin m)
    (hv : v k ∈ R) : (1 + c * v k) * wv c v k = 1 ∧ wv c v k ∈ R := by
  obtain ⟨u, hu, e⟩ := hc _ hv
  have h1 : (1 + c * v k) * wv c v k = 1 := Ring.mul_inverse_cancel _ (IsUnit.of_mul_eq_one _ e)
  have : wv c v k = u := by linear_combination u * h1 - wv c v k * e
  exact ⟨h1, this ▸ hu⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun v hv => (wv_spec hc v k (hv k)).2, fun Λ v v' hv hv' hd => by obtain ⟨e, h1⟩ := wv_spec hc v k (hv k) obtain ⟨e', h1'⟩ := wv_spec hc v' k (hv' k) refine ⟨-(InverseBoundedFixedPoint.wv c v k * InverseBoundedFixedPoint.wv c v' k) * (v k - v' k), mul_mem_sub Λ (R.neg_mem (R.mul …`.
-/
theorem LW.wv (hc : ∀ r ∈ R, ∃ u ∈ R, (1 + c * r) * u = 1) (k : Fin m) :
    LW R c (fun v : Fin m → K => wv c v k) :=
  ⟨fun v hv => (wv_spec hc v k (hv k)).2, fun Λ v v' hv hv' hd => by
    obtain ⟨e, h1⟩ := wv_spec hc v k (hv k)
    obtain ⟨e', h1'⟩ := wv_spec hc v' k (hv' k)
    refine ⟨-(InverseBoundedFixedPoint.wv c v k * InverseBoundedFixedPoint.wv c v' k) * (v k - v' k),
      mul_mem_sub Λ (R.neg_mem (R.mul_mem h1 h1')) (hd k), ?_⟩
    linear_combination (InverseBoundedFixedPoint.wv c v' k) * e - (InverseBoundedFixedPoint.wv c v k) * e'⟩

/- English proof (translation)
Establish `hu : ∀ i j : Fin m, LW R c (fun v : Fin m → K => uW (InverseBoundedFixedPoint.wv c v) i j)` using `fun i j => ((LW.wv hc i).mul (LW.wv hc j)).mul (LW.prod _ fun k => LW.wv hc k)`. Establish `h2 : (2 : K) ∈ R` using `ofNat_mem R 2`. Conclude with `((LW.ite _ ((LW.const h2).mul (LW.wv hc i))).add (LW.ite _ (hu i j))).add (LW.ite _ (hu j i))`.
-/
theorem LW.MW (hc : ∀ r ∈ R, ∃ u ∈ R, (1 + c * r) * u = 1) (i j : Fin m) :
    LW R c (fun v : Fin m → K => MW (InverseBoundedFixedPoint.wv c v) i j) := by
  have hu : ∀ i j : Fin m, LW R c (fun v : Fin m → K => uW (InverseBoundedFixedPoint.wv c v) i j) := fun i j =>
    ((LW.wv hc i).mul (LW.wv hc j)).mul (LW.prod _ fun k => LW.wv hc k)
  have h2 : (2 : K) ∈ R := ofNat_mem R 2
  exact ((LW.ite _ ((LW.const h2).mul (LW.wv hc i))).add (LW.ite _ (hu i j))).add (LW.ite _ (hu j i))

def cm (a : K) (Λ : Submodule R K) : Submodule R K where
  carrier := {v | a * v ∈ Λ}
  add_mem' := by
    intro x y hx hy
    show a * (x + y) ∈ Λ
    rw [mul_add]; exact Λ.add_mem hx hy
  zero_mem' := by
    show a * 0 ∈ Λ
    simp
  smul_mem' := by
    intro r x hx
    show a * (r • x) ∈ Λ
    have : a * (r • x) = r • (a * x) := by
      rw [Subring.smul_def, Subring.smul_def]; simp only [smul_eq_mul]; ring
    rw [this]; exact Λ.smul_mem r hx

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v Pᵀ, Matrix.vecMul_transpose]`.
-/
theorem quad_conj (P H : Matrix (Fin m) (Fin m) K) (v : Fin m → K) :
    (P *ᵥ v) ⬝ᵥ (H *ᵥ (P *ᵥ v)) = v ⬝ᵥ ((Pᵀ * H * P) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v Pᵀ,
    Matrix.vecMul_transpose]

/- English proof (translation)
Establish `h1 : a * Ring.inverse a = 1` using `Ring.mul_inverse_cancel _ (IsUnit.of_mul_eq_one _ h)`. Take the linear combination `b * h1 - Ring.inverse a * h`.
-/
theorem inverse_eq {a b : K} (h : a * b = 1) : Ring.inverse a = b := by
  have h1 : a * Ring.inverse a = 1 := Ring.mul_inverse_cancel _ (IsUnit.of_mul_eq_one _ h)
  linear_combination b * h1 - Ring.inverse a * h

end Lip

section Main

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}

/- English proof (translation)
Simplify using `only [HA, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]`. Use `R.sub_mem (R.mul_mem (natCast_mem R _) ?_) R.one_mem` and prove the remaining obligations. Use `split_ifs`. Conclude with `R.one_mem`. Conclude with `R.zero_mem`.
-/
theorem HA_int (R : Subring K) (m : ℕ) (i j : Fin m) : HA K m i j ∈ R := by
  simp only [HA, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  refine R.sub_mem (R.mul_mem (natCast_mem R _) ?_) R.one_mem
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

/- English proof (translation)
Use `h.t2` as an intermediate fact. Establish `i0 : (z : K) * ((z⁻¹ : Kˣ) : K) = 1` using `by simp`. Establish `ic : (c : K) * ((c⁻¹ : Kˣ) : K) = 1` using `by simp`. Take `⟨a, ha⟩ : ∃ a : K, a = (z : K) * (c : K)` from `⟨_, rfl⟩`. Take `⟨ai, hai⟩ : ∃ ai : K, ai = ((z⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K)` from `⟨_, rfl⟩`.

Establish `haai : a * ai = 1`. Rewrite using `[ha, hai]`. Take the linear combination `(c : K) * ((c⁻¹ : Kˣ) : K) * i0 + ic`. Establish `hcancel : ∀ x : K, a * (ai * x) = x` using `fun x => by linear_combination x * haai`. Establish `hcancel' : ∀ x : K, ai * (a * x) = x` using `fun x => by linear_combination x * haai`.

Establish `hc : ∀ r ∈ R, ∃ u ∈ R, (1 + (c : K) * r) * u = 1` using `fun r hr => h.unit_one _ ⟨4 * ((m + 1 : ℕ) : K) * r, R.mul_mem (R.mul_mem (ofNat_mem R 4) (natCast_mem R _)) hr, by rw [hcv]; ring⟩`. Establish `hBR : ∀ x ∈ cm a B, x ∈ R`. Introduce `x hx`. Take `⟨r, hr, e⟩` from `hBz _ hx`. Rewrite `e` using `[← ha]`.

Establish `: x = r` using `by linear_combination ai * e - (x - r) * haai`. Rewrite using `[this]` and apply the resulting hypothesis. Establish `hBcl : IsClosed ((cm a B : Submodule R K) : Set K)` using `by show IsClosed ((fun v => a * v) ⁻¹' (B : Set K))`. Conclude with `hBc.preimage (continuous_const.mul continuous_id)`. Take `⟨Nv, hNv⟩ : ∃ Nv : (Fin m → K) → Matrix (Fin m) (Fin m) K, ∀ v, Nv v = ((c⁻¹ : Kˣ) : K) • (MW (wv (c : K) v) - HH K m)` from `⟨_, fun _ => rfl⟩`.

Establish `hNL : ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ R) → (∀ k, v' k ∈ R) → (∀ k, v k - v' k ∈ Λ) → MemM Λ (Nv v - Nv v')`. Introduce `Λ v v' hv hv' hd i j`. Take `⟨l, hl, e⟩` from `(LW.MW hc i j).2 Λ v v' hv hv' hd`. Establish `: (Nv v - Nv v') i j = l`. Simplify using `only [hNv, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`.

Take the linear combination `((c⁻¹ : Kˣ) : K) * e + l * ic`. Rewrite using `[this]`. Conclude with `hl`. Establish `hN0 : Nv 0 = 0`. Establish `: wv (c : K) (0 : Fin m → K) = fun _ => 1`.

Use function extensionality and compare the values at `k`. Simplify using `[wv]`. Rewrite using `[hNv, this, MW_one, sub_self, smul_zero]`. Establish `hNR : ∀ v : Fin m → K, (∀ k, v k ∈ R) → ∀ i j, Nv v i j ∈ R`. Introduce `v hv i j`.

Use `hNL (Rs R) v 0 hv (fun _ => R.zero_mem) (fun k => by show v k - (0 : Fin m → K) k ∈ R` as an intermediate fact. Simplify using `using hv k) i j`. Rewrite `this` using `[hN0, sub_zero]`. Conclude with `this`. Establish `hNs : ∀ v, (Nv v)ᵀ = Nv v` using `fun v => by`.

Rewrite using `[hNv, Matrix.transpose_smul, Matrix.transpose_sub, MW_symm, HH_symm]`. Establish `hHA` using `HA_int R m`. Establish `hex : ∀ v : Fin m → K, ∃ Y : Matrix (Fin m) (Fin m) K, (∀ k, v k ∈ R) → (∀ i j, Y i j ∈ R) ∧ Y = Nv v - (ϖ : K) • (Y * HA K m * Y)`. Introduce `v`. Distinguish the cases in `hv : ∀ k, v k ∈ R`.

Take `⟨Y, h1, h2⟩` from `h.sqrtM (HA K m) (Nv v) hHA (hNR v hv)`. Conclude with `⟨Y, fun _ => ⟨h1, h2⟩⟩`. Conclude with `⟨0, fun h => absurd h hv⟩`. Use `choose Y0 hY0 using hex`. Establish `h2R : (2 : K) ∈ R` using `ofNat_mem R 2`.

Take `⟨hmap, hsurj, hiff⟩` from `h.core (cm a B) hBR hBcl (fun v => (2 : K) • (HA K m * Y0 v)) (fun v hv i j => R.mul_mem h2R (int_mul hHA (hY0 v fun k => hBR _ (hv k)).1 i j)) (fun Λ v v' hv hv' hd i j => by`. Establish `hvR` using `fun k => hBR _ (hv k)`. Establish `hvR'` using `fun k => hBR _ (hv' k)`. Establish `h1` using `h.sqrt_lip hHA (hY0 v hvR).1 (hY0 v' hvR').1 (hY0 v hvR).2 (hY0 v' hvR').2 Λ (hNL Λ v v' hvR hvR' hd)`. Establish `e : ((2 : K) • (HA K m * Y0 v) - (2 : K) • (HA K m * Y0 v')) i j = 2 * (HA K m * (Y0 v - Y0 v')) i j`.

Rewrite using `[Matrix.mul_sub]`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_mem_sub Λ h2R (h1.mul_left hHA i j))`.

Take `⟨θ, hθ⟩ : ∃ θ : (Fin m → K) → (Fin m → K), ∀ v, θ v = v + (ϖ : K) • (((2 : K) • (HA K m * Y0 v)) *ᵥ v)` from `⟨_, fun _ => rfl⟩`. Simplify using `only [← hθ] at hmap hsurj hiff`. Establish `hquad : ∀ v : Fin m → K, (∀ k, v k ∈ cm a B) → θ v ⬝ᵥ (HH K m *ᵥ θ v) = v ⬝ᵥ (MW (wv (c : K) v) *ᵥ v)`. Introduce `v hv`. Establish `hvR` using `fun k => hBR _ (hv k)`.

Establish `e1 : θ v = (1 + (2 * (ϖ : K)) • (HA K m * Y0 v)) *ᵥ v`. Rewrite using `[hθ, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, smul_smul, mul_comm]`. Rewrite using `[e1, quad_conj, conj_identity (ϖ : K) (Y0 v) (Nv v) (h.sqrt_symm hHA (hY0 v hvR).1 (hY0 v hvR).2 HA_symm (hNs v)) (hY0 v hvR).2, ← hcv, hNv, smul_smul, ic, one_smul, add_sub_cancel]`. Establish `hexg : ∀ η : Fin m → K, ∃ v : Fin m → K, (∀ k, η k ∈ cm a B) → (∀ k, v k ∈ cm a B) ∧ θ v = η`. Introduce `η`.

Distinguish the cases in `hη : ∀ k, η k ∈ cm a B`. Take `⟨v, h1, h2⟩` from `hsurj η hη`. Conclude with `⟨v, fun _ => ⟨h1, h2⟩⟩`. Conclude with `⟨0, fun h => absurd h hη⟩`. Use `choose g hg using hexg`.

Establish `hsc : ∀ ξ : Fin m → K, (∀ k, ξ k ∈ B) → ∀ k, ai * ξ k ∈ cm a B`. Introduce `ξ hξ k`. Use `show a * (ai * ξ k) ∈ B`. Rewrite using `[hcancel]`. Conclude with `hξ k`.

Establish `hIff : ∀ Λ : Submodule R K, ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) → ((∀ k, a * g (fun k => ai * ξ k) k - a * g (fun k => ai * η k) k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ)`. Introduce `Λ ξ η hξ hη`. Take `⟨hv, e⟩` from `hg _ (hsc ξ hξ)`. Take `⟨hv', e'⟩` from `hg _ (hsc η hη)`. Establish `h1` using `hiff (cm a Λ) _ _ hv hv'`.

Rewrite `h1` using `[e, e']`. Prove the components needed by the constructor for the conclusion. Introduce `hd k`. Use `h1.2 (fun k => by show a * (_ - _) ∈ Λ` as an intermediate fact. Rewrite using `[mul_sub]`.

Conclude with `hd k) k`. Establish `this' : a * (ai * ξ k - ai * η k) ∈ Λ` using `this`. Rewrite `this'` using `[mul_sub, hcancel, hcancel]`. Then use the resulting hypothesis. Introduce `hd k`. Use `h1.1 (fun k => by show a * (ai * ξ k - ai * η k) ∈ Λ` as an intermediate fact.

Rewrite using `[mul_sub, hcancel, hcancel]`. Conclude with `hd k) k`. Establish `this' : a * (g (fun k => ai * ξ k) k - g (fun k => ai * η k) k) ∈ Λ` using `this`. Rewrite `this'` using `[mul_sub]`. Then use the resulting hypothesis. Use `⟨fun ξ k => a * g (fun k => ai * ξ k) k, ⟨?_, ?_, ?_⟩, hIff, ?_⟩` and prove the remaining obligations.

Introduce `ξ hξ k`. Conclude with `(hg _ (hsc ξ hξ)).1 k`. Introduce `ξ hξ η hη e`. Use `(hIff ⊥ ξ η hξ hη).1 (fun k => by` as an intermediate fact. Use `congrFun e k` as an intermediate fact.

Simplify using `only at this`. Rewrite using `[this, sub_self]`. Conclude with `Submodule.zero_mem _)`. Use function extensionality and compare the values at `k`. Conclude with `sub_eq_zero.1 ((Submodule.mem_bot R).1 (this k))`.

Introduce `b hb`. Establish `hv` using `hsc b hb`. Establish `hη` using `hmap _ hv`. Use `⟨fun k => a * θ (fun k => ai * b k) k, fun k => hη k, ?_⟩` and prove the remaining obligations. Establish `e1 : (fun k => ai * (a * θ (fun k => ai * b k) k)) = θ (fun k => ai * b k)`.

Use function extensionality and compare the values at `k`. Rewrite using `[hcancel']`. Take `⟨hv', e'⟩` from `hg _ hη`. Establish `h1` using `(hiff ⊥ _ _ hv' hv).1 (fun k => by rw [e', sub_self]; exact Submodule.zero_mem _)`. Use function extensionality and compare the values at `k`.

Simplify using `only [e1]`. Establish `h3` using `sub_eq_zero.1 ((Submodule.mem_bot R).1 (h1 k))`. Rewrite using `[h3, hcancel]`. Introduce `ξ hξ`. Take `⟨hv, e⟩` from `hg _ (hsc ξ hξ)`.

Take `⟨v, hvdef⟩ : ∃ v, v = g (fun k => ai * ξ k)` from `⟨_, rfl⟩`. Rewrite `hv`, `e` using `[← hvdef]`. Simplify using `only [← hvdef]`. Establish `hw : ∀ k, (1 + (c : K) * v k) * wv (c : K) v k = 1` using `fun k => (wv_spec hc v k (hBR _ (hv k))).1`. Establish `hφ : ∀ k, (z : K) + a * v k = (z : K) * (1 + (c : K) * v k)` using `fun k => by rw [ha]; ring`.

Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ]`. Conclude with `z.isUnit.mul (IsUnit.of_mul_eq_one _ (hw k))`. Simplify using `only [g0, hφ]`. Take `⟨W, hW⟩ : ∃ W, W = ∏ k, wv (c : K) v k` from `⟨_, rfl⟩`.

Take `⟨S, hS⟩ : ∃ S, S = ∑ k, (c : K) * v k` from `⟨_, rfl⟩`. Establish `i1 : (z : K) ^ m * (((z⁻¹ : Kˣ) : K)) ^ m = 1` using `by rw [← mul_pow, i0, one_pow]`. Establish `e2 : Ring.inverse (∏ k, (z : K) * (1 + (c : K) * v k)) = (((z⁻¹ : Kˣ) : K)) ^ m * W` using `inverse_eq (by`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hW]`. Establish `hp : (∏ k, (1 + (c : K) * v k)) * ∏ k, wv (c : K) v k = 1`.

Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => hw k`. Take the linear combination `((∏ k, (1 + (c : K) * v k)) * ∏ k, wv (c : K) v k) * i1 + hp)`. Establish `e3 : ∑ k, (z : K) * (1 + (c : K) * v k) = (m : K) * (z : K) + (z : K) * S`. Rewrite using `[← Finset.mul_sum, Finset.sum_add_distrib, hS]`.

Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq1` using `quad_identity (fun k => (c : K) * v k) (wv (c : K) v) hw`. Rewrite `hq1` using `[← hW, ← hS]`. Establish `hq2 : (fun k => (c : K) * v k) ⬝ᵥ (MW (wv (c : K) v) *ᵥ fun k => (c : K) * v k) = (c : K) ^ 2 * (v ⬝ᵥ (MW (wv (c : K) v) *ᵥ v))`.

Establish `: (fun k => (c : K) * v k) = (c : K) • v` using `rfl`. Rewrite using `[this, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq3 : ξ ⬝ᵥ (hessM m z *ᵥ ξ) = ((z⁻¹ : Kˣ) : K) * a ^ 2 * (θ v ⬝ᵥ (HH K m *ᵥ θ v))`. Establish `e4 : ξ = a • θ v`.

Use function extensionality and compare the values at `k`. Rewrite using `[e]`. Use `show ξ k = a * (ai * ξ k)`. Rewrite using `[hcancel]`. Establish `e5 : hessM m z = ((z⁻¹ : Kˣ) : K) • HH K m` using `rfl`.

Use `conv_lhs => rw [e4, e5]`. Rewrite using `[Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `i2 : Ring.inverse (2 : K) * 2 = 1` using `Ring.inverse_mul_cancel _ h2`. Rewrite using `[e2, e3, hq3, hquad v hv, ha]`.

Rewrite `hq1` using `[hq2]`. Use `push_cast`. Take the linear combination `(z : K) * W * i1 - Ring.inverse (2 : K) * (z : K) * (c : K) ^ 2 * (v ⬝ᵥ (MW (wv (c : K) v) *ᵥ v)) * i0 - Ring.inverse (2 : K) * (z : K) * hq1 - (z : K) * (S + W - 1) * i2`.
-/
theorem Adic.morse_local (h : Adic R ϖ) (h2 : IsUnit (2 : K)) (m : ℕ) (c z : Kˣ)
    (hcv : (c : K) = 4 * ((m + 1 : ℕ) : K) * (ϖ : K)) (B : Submodule R K)
    (hBc : IsClosed (B : Set K)) (hBz : ∀ b ∈ B, ∃ r ∈ R, b = (z : K) * (c : K) * r) :
    ∃ φ : (Fin m → K) → (Fin m → K),
      Set.BijOn φ {ξ | ∀ k, ξ k ∈ B} {ξ | ∀ k, ξ k ∈ B} ∧
      (∀ Λ : Submodule R K, ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
        ((∀ k, φ ξ k - φ η k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ)) ∧
      ∀ ξ : Fin m → K, (∀ k, ξ k ∈ B) →
        (∀ k, IsUnit ((z : K) + φ ξ k)) ∧
        g0 ((z : K) ^ (m + 1)) (fun k => (z : K) + φ ξ k) =
          ((m + 1 : ℕ) : K) * (z : K) + Ring.inverse 2 * (ξ ⬝ᵥ (hessM m z *ᵥ ξ)) := by
  have := h.t2
  have i0 : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := by simp
  have ic : (c : K) * ((c⁻¹ : Kˣ) : K) = 1 := by simp
  obtain ⟨a, ha⟩ : ∃ a : K, a = (z : K) * (c : K) := ⟨_, rfl⟩
  obtain ⟨ai, hai⟩ : ∃ ai : K, ai = ((z⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have haai : a * ai = 1 := by
    rw [ha, hai]; linear_combination (c : K) * ((c⁻¹ : Kˣ) : K) * i0 + ic
  have hcancel : ∀ x : K, a * (ai * x) = x := fun x => by linear_combination x * haai
  have hcancel' : ∀ x : K, ai * (a * x) = x := fun x => by linear_combination x * haai
  have hc : ∀ r ∈ R, ∃ u ∈ R, (1 + (c : K) * r) * u = 1 := fun r hr =>
    h.unit_one _ ⟨4 * ((m + 1 : ℕ) : K) * r,
      R.mul_mem (R.mul_mem (ofNat_mem R 4) (natCast_mem R _)) hr, by rw [hcv]; ring⟩
  have hBR : ∀ x ∈ cm a B, x ∈ R := by
    intro x hx
    obtain ⟨r, hr, e⟩ := hBz _ hx
    rw [← ha] at e
    have : x = r := by linear_combination ai * e - (x - r) * haai
    rwa [this]
  have hBcl : IsClosed ((cm a B : Submodule R K) : Set K) := by
    show IsClosed ((fun v => a * v) ⁻¹' (B : Set K))
    exact hBc.preimage (continuous_const.mul continuous_id)
  obtain ⟨Nv, hNv⟩ : ∃ Nv : (Fin m → K) → Matrix (Fin m) (Fin m) K,
      ∀ v, Nv v = ((c⁻¹ : Kˣ) : K) • (MW (wv (c : K) v) - HH K m) := ⟨_, fun _ => rfl⟩
  have hNL : ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ R) → (∀ k, v' k ∈ R) →
      (∀ k, v k - v' k ∈ Λ) → MemM Λ (Nv v - Nv v') := by
    intro Λ v v' hv hv' hd i j
    obtain ⟨l, hl, e⟩ := (LW.MW hc i j).2 Λ v v' hv hv' hd
    have : (Nv v - Nv v') i j = l := by
      simp only [hNv, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination ((c⁻¹ : Kˣ) : K) * e + l * ic
    rw [this]; exact hl
  have hN0 : Nv 0 = 0 := by
    have : wv (c : K) (0 : Fin m → K) = fun _ => 1 := by
      funext k; simp [wv]
    rw [hNv, this, MW_one, sub_self, smul_zero]
  have hNR : ∀ v : Fin m → K, (∀ k, v k ∈ R) → ∀ i j, Nv v i j ∈ R := by
    intro v hv i j
    have := hNL (Rs R) v 0 hv (fun _ => R.zero_mem) (fun k => by
      show v k - (0 : Fin m → K) k ∈ R
      simpa using hv k) i j
    rw [hN0, sub_zero] at this
    exact this
  have hNs : ∀ v, (Nv v)ᵀ = Nv v := fun v => by
    rw [hNv, Matrix.transpose_smul, Matrix.transpose_sub, MW_symm, HH_symm]
  have hHA := HA_int R m
  have hex : ∀ v : Fin m → K, ∃ Y : Matrix (Fin m) (Fin m) K, (∀ k, v k ∈ R) →
      (∀ i j, Y i j ∈ R) ∧ Y = Nv v - (ϖ : K) • (Y * HA K m * Y) := by
    intro v
    by_cases hv : ∀ k, v k ∈ R
    · obtain ⟨Y, h1, h2⟩ := h.sqrtM (HA K m) (Nv v) hHA (hNR v hv)
      exact ⟨Y, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose Y0 hY0 using hex
  have h2R : (2 : K) ∈ R := ofNat_mem R 2
  obtain ⟨hmap, hsurj, hiff⟩ := h.core (cm a B) hBR hBcl (fun v => (2 : K) • (HA K m * Y0 v))
    (fun v hv i j => R.mul_mem h2R (int_mul hHA (hY0 v fun k => hBR _ (hv k)).1 i j))
    (fun Λ v v' hv hv' hd i j => by
      have hvR := fun k => hBR _ (hv k)
      have hvR' := fun k => hBR _ (hv' k)
      have h1 := h.sqrt_lip hHA (hY0 v hvR).1 (hY0 v' hvR').1 (hY0 v hvR).2 (hY0 v' hvR').2 Λ
        (hNL Λ v v' hvR hvR' hd)
      have e : ((2 : K) • (HA K m * Y0 v) - (2 : K) • (HA K m * Y0 v')) i j =
          2 * (HA K m * (Y0 v - Y0 v')) i j := by
        rw [Matrix.mul_sub]
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
      rw [e]
      exact mul_mem_sub Λ h2R (h1.mul_left hHA i j))
  obtain ⟨θ, hθ⟩ : ∃ θ : (Fin m → K) → (Fin m → K),
      ∀ v, θ v = v + (ϖ : K) • (((2 : K) • (HA K m * Y0 v)) *ᵥ v) := ⟨_, fun _ => rfl⟩
  simp only [← hθ] at hmap hsurj hiff
  have hquad : ∀ v : Fin m → K, (∀ k, v k ∈ cm a B) →
      θ v ⬝ᵥ (HH K m *ᵥ θ v) = v ⬝ᵥ (MW (wv (c : K) v) *ᵥ v) := by
    intro v hv
    have hvR := fun k => hBR _ (hv k)
    have e1 : θ v = (1 + (2 * (ϖ : K)) • (HA K m * Y0 v)) *ᵥ v := by
      rw [hθ, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, smul_smul,
        mul_comm]
    rw [e1, quad_conj, conj_identity (ϖ : K) (Y0 v) (Nv v)
      (h.sqrt_symm hHA (hY0 v hvR).1 (hY0 v hvR).2 HA_symm (hNs v)) (hY0 v hvR).2, ← hcv, hNv,
      smul_smul, ic, one_smul, add_sub_cancel]
  have hexg : ∀ η : Fin m → K, ∃ v : Fin m → K, (∀ k, η k ∈ cm a B) →
      (∀ k, v k ∈ cm a B) ∧ θ v = η := by
    intro η
    by_cases hη : ∀ k, η k ∈ cm a B
    · obtain ⟨v, h1, h2⟩ := hsurj η hη
      exact ⟨v, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hη⟩
  choose g hg using hexg
  have hsc : ∀ ξ : Fin m → K, (∀ k, ξ k ∈ B) → ∀ k, ai * ξ k ∈ cm a B := by
    intro ξ hξ k
    show a * (ai * ξ k) ∈ B
    rw [hcancel]; exact hξ k
  have hIff : ∀ Λ : Submodule R K, ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
      ((∀ k, a * g (fun k => ai * ξ k) k - a * g (fun k => ai * η k) k ∈ Λ) ↔
        ∀ k, ξ k - η k ∈ Λ) := by
    intro Λ ξ η hξ hη
    obtain ⟨hv, e⟩ := hg _ (hsc ξ hξ)
    obtain ⟨hv', e'⟩ := hg _ (hsc η hη)
    have h1 := hiff (cm a Λ) _ _ hv hv'
    rw [e, e'] at h1
    constructor
    · intro hd k
      have := h1.2 (fun k => by
        show a * (_ - _) ∈ Λ
        rw [mul_sub]; exact hd k) k
      have this' : a * (ai * ξ k - ai * η k) ∈ Λ := this
      rwa [mul_sub, hcancel, hcancel] at this'
    · intro hd k
      have := h1.1 (fun k => by
        show a * (ai * ξ k - ai * η k) ∈ Λ
        rw [mul_sub, hcancel, hcancel]; exact hd k) k
      have this' : a * (g (fun k => ai * ξ k) k - g (fun k => ai * η k) k) ∈ Λ := this
      rwa [mul_sub] at this'
  refine ⟨fun ξ k => a * g (fun k => ai * ξ k) k, ⟨?_, ?_, ?_⟩, hIff, ?_⟩
  · intro ξ hξ k
    exact (hg _ (hsc ξ hξ)).1 k
  · intro ξ hξ η hη e
    have := (hIff ⊥ ξ η hξ hη).1 (fun k => by
      have := congrFun e k
      simp only at this
      rw [this, sub_self]; exact Submodule.zero_mem _)
    funext k
    exact sub_eq_zero.1 ((Submodule.mem_bot R).1 (this k))
  · intro b hb
    have hv := hsc b hb
    have hη := hmap _ hv
    refine ⟨fun k => a * θ (fun k => ai * b k) k, fun k => hη k, ?_⟩
    have e1 : (fun k => ai * (a * θ (fun k => ai * b k) k)) = θ (fun k => ai * b k) := by
      funext k; rw [hcancel']
    obtain ⟨hv', e'⟩ := hg _ hη
    have h1 := (hiff ⊥ _ _ hv' hv).1 (fun k => by rw [e', sub_self]; exact Submodule.zero_mem _)
    funext k
    simp only [e1]
    have h3 := sub_eq_zero.1 ((Submodule.mem_bot R).1 (h1 k))
    rw [h3, hcancel]
  · intro ξ hξ
    obtain ⟨hv, e⟩ := hg _ (hsc ξ hξ)
    obtain ⟨v, hvdef⟩ : ∃ v, v = g (fun k => ai * ξ k) := ⟨_, rfl⟩
    rw [← hvdef] at hv e
    simp only [← hvdef]
    have hw : ∀ k, (1 + (c : K) * v k) * wv (c : K) v k = 1 := fun k =>
      (wv_spec hc v k (hBR _ (hv k))).1
    have hφ : ∀ k, (z : K) + a * v k = (z : K) * (1 + (c : K) * v k) := fun k => by rw [ha]; ring
    refine ⟨fun k => ?_, ?_⟩
    · rw [hφ]; exact z.isUnit.mul (IsUnit.of_mul_eq_one _ (hw k))
    · simp only [g0, hφ]
      obtain ⟨W, hW⟩ : ∃ W, W = ∏ k, wv (c : K) v k := ⟨_, rfl⟩
      obtain ⟨S, hS⟩ : ∃ S, S = ∑ k, (c : K) * v k := ⟨_, rfl⟩
      have i1 : (z : K) ^ m * (((z⁻¹ : Kˣ) : K)) ^ m = 1 := by rw [← mul_pow, i0, one_pow]
      have e2 : Ring.inverse (∏ k, (z : K) * (1 + (c : K) * v k)) = (((z⁻¹ : Kˣ) : K)) ^ m * W :=
        inverse_eq (by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hW]
          have hp : (∏ k, (1 + (c : K) * v k)) * ∏ k, wv (c : K) v k = 1 := by
            rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun k _ => hw k
          linear_combination ((∏ k, (1 + (c : K) * v k)) * ∏ k, wv (c : K) v k) * i1 + hp)
      have e3 : ∑ k, (z : K) * (1 + (c : K) * v k) = (m : K) * (z : K) + (z : K) * S := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hS]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring
      have hq1 := quad_identity (fun k => (c : K) * v k) (wv (c : K) v) hw
      rw [← hW, ← hS] at hq1
      have hq2 : (fun k => (c : K) * v k) ⬝ᵥ (MW (wv (c : K) v) *ᵥ fun k => (c : K) * v k) =
          (c : K) ^ 2 * (v ⬝ᵥ (MW (wv (c : K) v) *ᵥ v)) := by
        have : (fun k => (c : K) * v k) = (c : K) • v := rfl
        rw [this, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        ring
      have hq3 : ξ ⬝ᵥ (hessM m z *ᵥ ξ) =
          ((z⁻¹ : Kˣ) : K) * a ^ 2 * (θ v ⬝ᵥ (HH K m *ᵥ θ v)) := by
        have e4 : ξ = a • θ v := by
          funext k
          rw [e]
          show ξ k = a * (ai * ξ k)
          rw [hcancel]
        have e5 : hessM m z = ((z⁻¹ : Kˣ) : K) • HH K m := rfl
        conv_lhs => rw [e4, e5]
        rw [Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul,
          smul_eq_mul, smul_eq_mul, smul_eq_mul]
        ring
      have i2 : Ring.inverse (2 : K) * 2 = 1 := Ring.inverse_mul_cancel _ h2
      rw [e2, e3, hq3, hquad v hv, ha]
      rw [hq2] at hq1
      push_cast
      linear_combination (z : K) * W * i1 -
        Ring.inverse (2 : K) * (z : K) * (c : K) ^ 2 * (v ⬝ᵥ (MW (wv (c : K) v) *ᵥ v)) * i0 -
        Ring.inverse (2 : K) * (z : K) * hq1 - (z : K) * (S + W - 1) * i2

/- English proof (translation)
Introduce `K _ _ _ R ψ hD hn m _ Q hQ hQu`. Take `⟨ϖ, h⟩` from `adic_of_datum hD hn`. Use `hD.red` as an intermediate fact. Use `hD.t2` as an intermediate fact. Take `⟨M0, hM0⟩` from `h.inv_bounded hQ hQu`.

Take `⟨n0, hn0⟩` from `h.root_bounded (m + 1) (by omega)`. Take `⟨u4, hu4⟩` from `hn (4 * (m + 1)) (by omega)`. Establish `h2 : IsUnit (2 : K)`. Use `hn 2 (by omega)` as an intermediate fact. Simplify using `using this`.

Establish `hcv : ((u4 * ϖ : Kˣ) : K) = 4 * ((m + 1 : ℕ) : K) * (ϖ : K)`. Rewrite using `[Units.val_mul, hu4]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨I R ((ϖ ^ (n0 + M0) * (u4 * ϖ) : Kˣ) : K), I_nhds h.isOpen _, fun B hB hBV z hz => ?_⟩` and prove the remaining obligations.

Establish `hz' : (ϖ : K) ^ n0 * ((ϖ : K) ^ M0 * ((z⁻¹ : Kˣ) : K)) ∈ R`. Apply `hn0` to reduce the goal to its premises. Establish `h1` using `hM0 _ hz ((((z⁻¹ : Kˣ) : K)) ^ (m + 1)) (by rw [← mul_pow]; simp)`. Establish `e : ((ϖ : K) ^ M0 * ((z⁻¹ : Kˣ) : K)) ^ (m + 1) = ((ϖ : K) ^ M0) ^ m * ((ϖ : K) ^ M0 * (((z⁻¹ : Kˣ) : K)) ^ (m + 1))` using `by ring`. Rewrite using `[e]`.

Conclude with `R.mul_mem (R.pow_mem (R.pow_mem h.mem _) _) h1`. Take `⟨φ, h1, h2', h3⟩` from `h.morse_local h2 m (u4 * ϖ) z hcv B hB.2.isClosed (fun b hb => by`. Take `⟨r, hr, e⟩` from `hBV hb`. Use `⟨_, R.mul_mem hz' hr, ?_⟩` and prove the remaining obligations. Establish `i0 : (z : K) * ((z⁻¹ : Kˣ) : K) = 1` using `by simp`.

Rewrite using `[e]`. Use `push_cast`. Take the linear combination `(-((ϖ : K) ^ (n0 + M0) * ((u4 : K) * (ϖ : K)) * r)) * i0)`. Conclude with `⟨φ, h1, fun Λ _ => h2' Λ, h3⟩`.
-/
theorem morse : MorseLemma := by
  intro K _ _ _ R ψ hD hn m _ Q hQ hQu
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  have := hD.red
  have := hD.t2
  obtain ⟨M0, hM0⟩ := h.inv_bounded hQ hQu
  obtain ⟨n0, hn0⟩ := h.root_bounded (m + 1) (by omega)
  obtain ⟨u4, hu4⟩ := hn (4 * (m + 1)) (by omega)
  have h2 : IsUnit (2 : K) := by
    have := hn 2 (by omega)
    simpa using this
  have hcv : ((u4 * ϖ : Kˣ) : K) = 4 * ((m + 1 : ℕ) : K) * (ϖ : K) := by
    rw [Units.val_mul, hu4]; push_cast; ring
  refine ⟨I R ((ϖ ^ (n0 + M0) * (u4 * ϖ) : Kˣ) : K), I_nhds h.isOpen _, fun B hB hBV z hz => ?_⟩
  have hz' : (ϖ : K) ^ n0 * ((ϖ : K) ^ M0 * ((z⁻¹ : Kˣ) : K)) ∈ R := by
    apply hn0
    have h1 := hM0 _ hz ((((z⁻¹ : Kˣ) : K)) ^ (m + 1)) (by rw [← mul_pow]; simp)
    have e : ((ϖ : K) ^ M0 * ((z⁻¹ : Kˣ) : K)) ^ (m + 1) =
        ((ϖ : K) ^ M0) ^ m * ((ϖ : K) ^ M0 * (((z⁻¹ : Kˣ) : K)) ^ (m + 1)) := by ring
    rw [e]
    exact R.mul_mem (R.pow_mem (R.pow_mem h.mem _) _) h1
  obtain ⟨φ, h1, h2', h3⟩ := h.morse_local h2 m (u4 * ϖ) z hcv B hB.2.isClosed (fun b hb => by
    obtain ⟨r, hr, e⟩ := hBV hb
    refine ⟨_, R.mul_mem hz' hr, ?_⟩
    have i0 : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := by simp
    rw [e]
    push_cast
    linear_combination (-((ϖ : K) ^ (n0 + M0) * ((u4 : K) * (ϖ : K)) * r)) * i0)
  exact ⟨φ, h1, fun Λ _ => h2' Λ, h3⟩

end Main

end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.morse`.
-/
theorem Formalism.FourierDecayAlt.P.morseLemma : Formalism.FourierDecayAlt.A6.MorseLemma := Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.morse
