import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraExtra

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel Filter Topology PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc.KillNlo

section Generic

variable {G : Type} [Group G]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Ydb1.main hK hSK h1 hΨ hΨS hφS hid hl hc`.
-/
theorem exists_fixed_of_contract [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {K S : Set G} (hK : IsCompact K) (hSK : S ⊆ K) (h1 : (1 : G) ∈ S) {Ψ φ : G → G}
    (hΨ : Continuous Ψ) (hΨS : ∀ x ∈ S, Ψ x ∈ S) (hφS : ∀ x ∈ S, φ x ∈ S)
    (hid : ∀ x y, (Ψ x)⁻¹ * Ψ y = φ (x⁻¹ * y)) {l : ℕ} (hl : 0 < l)
    (hc : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ x ∈ S, φ^[l * m] x ∈ U) :
    ∃ v ∈ K, Ψ v = v :=
  _root_.UpperTheory.Reformulated.B.Ydb1.main hK hSK h1 hΨ hΨS hφS hid hl hc

/- English proof (translation)
Simplify using `[tnorm]`.
-/
theorem tnorm_zero (θ : MulAut G) (x : G) : tnorm θ 0 x = 1 := by
  simp [tnorm]

/- English proof (translation)
Unfold `tnorm`. Rewrite using `[List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]`. Both sides reduce to the same expression.
-/
theorem tnorm_succ (θ : MulAut G) (i : ℕ) (x : G) :
    tnorm θ (i + 1) x = tnorm θ i x * (θ ^ i) x := by
  unfold tnorm
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  rfl

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simpa using hx`. Consider the case `succ i ih`. Rewrite using `[pow_succ', MulAut.mul_apply, ← h]`. Conclude with `Subgroup.mem_map_of_mem _ ih`.
-/
theorem pow_apply_mem {H : Subgroup G} {θ : MulAut G} (h : H.map θ.toMonoidHom = H) (i : ℕ) {x : G}
    (hx : x ∈ H) : (θ ^ i) x ∈ H := by
  induction i with
  | zero => simpa using hx
  | succ i ih =>
    rw [pow_succ', MulAut.mul_apply, ← h]
    exact Subgroup.mem_map_of_mem _ ih

/- English proof (translation)
Rewrite `hx` using `[← h]`. Take `⟨y, hy, rfl⟩` from `hx`. Simplify using `using hy`.
-/
theorem inv_apply_mem {H : Subgroup G} {θ : MulAut G} (h : H.map θ.toMonoidHom = H) {x : G}
    (hx : x ∈ H) : θ⁻¹ x ∈ H := by
  rw [← h] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => rw [tnorm_zero]`. Conclude with `H.one_mem`. Consider the case `succ i ih => rw [tnorm_succ]`. Conclude with `H.mul_mem ih (pow_apply_mem h i hx)`.
-/
theorem tnorm_mem {H : Subgroup G} {θ : MulAut G} (h : H.map θ.toMonoidHom = H) (i : ℕ) {x : G}
    (hx : x ∈ H) : tnorm θ i x ∈ H := by
  induction i with
  | zero => rw [tnorm_zero]; exact H.one_mem
  | succ i ih => rw [tnorm_succ]; exact H.mul_mem ih (pow_apply_mem h i hx)

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp [tnorm_zero]`. Consider the case `succ i ih`. Rewrite using `[tnorm_succ, tnorm_succ, tnorm_succ, ih, map_mul]`. Use `hc _ (tnorm_mem h i hy) _ (pow_apply_mem h i hx)` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem tnorm_mul_of_comm {T : Subgroup G} {θ : MulAut G} (h : T.map θ.toMonoidHom = T)
    (hc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (i : ℕ) {x y : G} (hx : x ∈ T) (hy : y ∈ T) :
    tnorm θ i (x * y) = tnorm θ i x * tnorm θ i y := by
  induction i with
  | zero => simp [tnorm_zero]
  | succ i ih =>
    rw [tnorm_succ, tnorm_succ, tnorm_succ, ih, map_mul]
    have := hc _ (tnorm_mem h i hy) _ (pow_apply_mem h i hx)
    calc tnorm θ i x * tnorm θ i y * ((θ ^ i) x * (θ ^ i) y)
        = tnorm θ i x * (tnorm θ i y * (θ ^ i) x) * (θ ^ i) y := by simp only [mul_assoc]
      _ = tnorm θ i x * ((θ ^ i) x * tnorm θ i y) * (θ ^ i) y := by rw [this]
      _ = _ := by simp only [mul_assoc]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp [tnorm_zero]`. Consider the case `succ i ih`. Rewrite using `[Function.iterate_succ_apply', ih, tnorm_succ, pow_succ', MulAut.mul_apply]`. Use `congr 1`.

Establish `hu : (θ⁻¹ ^ i) ((θ ^ i) u) = u`. Rewrite using `[← MulAut.mul_apply, inv_pow, inv_mul_cancel, MulAut.one_apply]`. Establish `: (θ⁻¹ ^ i) (((tnorm θ i u) * (θ ^ i) u)⁻¹ * x * ((tnorm θ i u) * (θ ^ i) u)) = ((θ⁻¹ ^ i) ((θ ^ i) u))⁻¹ * (θ⁻¹ ^ i) ((tnorm θ i u)⁻¹ * x * tnorm θ i u) * (θ⁻¹ ^ i) ((θ ^ i) u)`. Rewrite using `[← map_inv, ← map_mul, ← map_mul]`. Use `congr 1`.

Simplify using `only [mul_inv_rev, mul_assoc]`. Rewrite using `[this, hu]`.
-/
theorem iterate_twist (θ : MulAut G) (u : G) (i : ℕ) (x : G) :
    (fun y => θ⁻¹ (u⁻¹ * y * u))^[i] x =
      (θ⁻¹ ^ i) ((tnorm θ i u)⁻¹ * x * tnorm θ i u) := by
  induction i with
  | zero => simp [tnorm_zero]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, tnorm_succ, pow_succ', MulAut.mul_apply]
    congr 1
    have hu : (θ⁻¹ ^ i) ((θ ^ i) u) = u := by
      rw [← MulAut.mul_apply, inv_pow, inv_mul_cancel, MulAut.one_apply]
    have : (θ⁻¹ ^ i) (((tnorm θ i u) * (θ ^ i) u)⁻¹ * x * ((tnorm θ i u) * (θ ^ i) u)) =
        ((θ⁻¹ ^ i) ((θ ^ i) u))⁻¹ * (θ⁻¹ ^ i) ((tnorm θ i u)⁻¹ * x * tnorm θ i u) *
          (θ⁻¹ ^ i) ((θ ^ i) u) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      simp only [mul_inv_rev, mul_assoc]
    rw [this, hu]

/- English proof (translation)
Establish `hl : ∀ y, (fun y => θ⁻¹ (u⁻¹ * y * u))^[l] y = (tnorm θ l u)⁻¹ * y * tnorm θ l u`. Introduce `y`. Rewrite using `[iterate_twist, inv_pow, hθ]`. Simplify using the standard rewrite rules. Rewrite using `[Function.iterate_mul]`.

Proceed by induction on `m generalizing x with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Function.iterate_succ_apply', ih, hl, pow_succ]`. Use `group`.
-/
theorem iterate_twist_mul (θ : MulAut G) {l : ℕ} (hθ : θ ^ l = 1) (u : G) (m : ℕ) (x : G) :
    (fun y => θ⁻¹ (u⁻¹ * y * u))^[l * m] x =
      (tnorm θ l u ^ m)⁻¹ * x * tnorm θ l u ^ m := by
  have hl : ∀ y, (fun y => θ⁻¹ (u⁻¹ * y * u))^[l] y = (tnorm θ l u)⁻¹ * y * tnorm θ l u := by
    intro y
    rw [iterate_twist, inv_pow, hθ]
    simp
  rw [Function.iterate_mul]
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, hl, pow_succ]
    group

/- English proof (translation)
Establish `hp : ∀ i : ℕ, Continuous (θ ^ i : MulAut G)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simpa using continuous_id`. Consider the case `succ i ih`.

Rewrite using `[pow_succ']`. Conclude with `hc.comp ih`. Establish `: θ⁻¹ = θ ^ (l - 1)`. Use `symm`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises.

Rewrite using `[← pow_succ, Nat.sub_add_cancel hl, hθ]`. Rewrite using `[this]`. Conclude with `hp _`.
-/
theorem continuous_inv_of_pow_eq_one [TopologicalSpace G] {θ : MulAut G} (hc : Continuous θ)
    {l : ℕ} (hl : 0 < l) (hθ : θ ^ l = 1) : Continuous (θ⁻¹ : MulAut G) := by
  have hp : ∀ i : ℕ, Continuous (θ ^ i : MulAut G) := by
    intro i
    induction i with
    | zero => simpa using continuous_id
    | succ i ih =>
      rw [pow_succ']
      exact hc.comp ih
  have : θ⁻¹ = θ ^ (l - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hl, hθ]
  rw [this]
  exact hp _

/- English proof (translation)
Establish `hconj : ∀ s ∈ J ⊓ T, ∀ n ∈ J ⊓ L, s⁻¹ * n * s ∈ J ⊓ L` using `fun s hs n hn => ⟨J.mul_mem (J.mul_mem (J.inv_mem hs.1) hn.1) hs.1, hTL s hs.2 n hn.2⟩`. Establish `hθS : ∀ x ∈ J ⊓ L, θ⁻¹ x ∈ J ⊓ L` using `fun x hx => ⟨inv_apply_mem hθJ hx.1, inv_apply_mem hθL hx.2⟩`. Establish `hcinv` using `continuous_inv_of_pow_eq_one hθc hl hθl`. Set `Ψ : G → G` to `fun x => θ⁻¹ (τ⁻¹ * (a⁻¹ * (t⁻¹ * x * t)) * τ)`. Set `φ : G → G` to `fun x => θ⁻¹ ((t * τ)⁻¹ * x * (t * τ))`.

Establish `hΨc : Continuous Ψ` using `hcinv.comp (by fun_prop)`. Establish `hΨS : ∀ x ∈ ((J ⊓ L : Subgroup G) : Set G), Ψ x ∈ ((J ⊓ L : Subgroup G) : Set G)` using `fun x hx => hθS _ (hconj τ hτ _ ((J ⊓ L).mul_mem ((J ⊓ L).inv_mem ha) (htd x hx)))`. Establish `hφS : ∀ x ∈ ((J ⊓ L : Subgroup G) : Set G), φ x ∈ ((J ⊓ L : Subgroup G) : Set G)`. Introduce `x hx`. Use `hθS _ ?_` and prove the remaining obligations.

Establish `: (t * τ)⁻¹ * x * (t * τ) = τ⁻¹ * (t⁻¹ * x * t) * τ` using `by group`. Rewrite using `[this]`. Conclude with `hconj τ hτ _ (htd x hx)`. Establish `hid : ∀ x y, (Ψ x)⁻¹ * Ψ y = φ (x⁻¹ * y)`. Introduce `x y`.

Use `show (θ⁻¹ _)⁻¹ * θ⁻¹ _ = θ⁻¹ _`. Rewrite using `[← map_inv, ← map_mul]`. Use `congr 1`. Use `group`. Establish `hc : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ x ∈ ((J ⊓ L : Subgroup G) : Set G), φ^[l * m] x ∈ U`.

Introduce `U hU h1`. Take `⟨j, hj⟩` from `hns U hU h1`. Use `⟨j, fun m hm x hx => ?_⟩` and prove the remaining obligations. Use `set n := tnorm θ l t with hn`. Use `set τ' := tnorm θ l τ with hτ'`.

Establish `hnT : n ∈ T` using `tnorm_mem hθT l htT`. Establish `hτ'S : τ' ∈ J ⊓ T` using `⟨tnorm_mem hθJ l hτ.1, tnorm_mem hθT l hτ.2⟩`. Establish `hw : tnorm θ l (t * τ) = τ' * n`. Rewrite using `[tnorm_mul_of_comm hθT hTc l htT hτ.2, hTc _ hnT _ hτ'S.2]`. Establish `hcomm : Commute τ' n` using `hTc _ hτ'S.2 _ hnT`.

Establish `hiter` using `iterate_twist_mul θ hθl (t * τ) m x`. Establish `hφ : φ^[l * m] x = (n ^ m)⁻¹ * ((τ' ^ m)⁻¹ * x * τ' ^ m) * n ^ m`. Use `hiter.trans ?_` and prove the remaining obligations. Rewrite using `[hw, hcomm.mul_pow]`. Use `group`.

Rewrite using `[hφ]`. Establish `hy : (τ' ^ m)⁻¹ * x * τ' ^ m ∈ J ⊓ L` using `hconj _ ⟨J.pow_mem hτ'S.1 m, T.pow_mem hτ'S.2 m⟩ x hx`. Establish `hdom : ∀ p : ℕ, ∀ y ∈ J ⊓ L, (n ^ p)⁻¹ * y * n ^ p ∈ J ⊓ L`. Introduce `p`. Proceed by induction on `p with`.

Consider the case `zero => intro y hy`. Simplify using `using hy`. Consider the case `succ p ih`. Introduce `y hy`. Use `hnd _ (ih y hy)` as an intermediate fact.

Establish `e : (n ^ (p + 1))⁻¹ * y * n ^ (p + 1) = n⁻¹ * ((n ^ p)⁻¹ * y * n ^ p) * n`. Rewrite using `[pow_succ]`. Use `group`. Rewrite using `[e]`. Conclude with `this`.

Take `⟨p, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Establish `e : (n ^ (j + p))⁻¹ * ((τ' ^ (j + p))⁻¹ * x * τ' ^ (j + p)) * n ^ (j + p) = (n ^ j)⁻¹ * ((n ^ p)⁻¹ * ((τ' ^ (j + p))⁻¹ * x * τ' ^ (j + p)) * n ^ p) * n ^ j`. Rewrite using `[pow_add n j p, (Commute.pow_pow_self n j p).eq]`. Use `group`. Rewrite using `[e]`.

Conclude with `hj _ (hdom p _ hy)`. Take `⟨v, hvJ, hv⟩` from `exists_fixed_of_contract (K := (J : Set G)) (S := ((J ⊓ L : Subgroup G) : Set G)) hJ (fun x hx => hx.1) (J ⊓ L).one_mem hΨc hΨS hφS hid hl hc`. Use `⟨v, hvJ, ?_⟩` and prove the remaining obligations. Establish `hθv : θ v = τ⁻¹ * (a⁻¹ * (t⁻¹ * v * t)) * τ` using `by conv_lhs => rw [← hv] show θ (θ⁻¹ _) = _`. Simplify using the standard rewrite rules.

Rewrite using `[hθv]`. Use `group`.
-/
theorem exists_twist_of_contract [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (J L T : Subgroup G) (hJ : IsCompact (J : Set G)) (θ : MulAut G) (hθc : Continuous θ) {l : ℕ}
    (hl : 0 < l) (hθl : θ ^ l = 1) (hθJ : J.map θ.toMonoidHom = J) (hθL : L.map θ.toMonoidHom = L)
    (hθT : T.map θ.toMonoidHom = T) (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hTL : ∀ s ∈ T, ∀ n ∈ L, s⁻¹ * n * s ∈ L) {t : G} (htT : t ∈ T)
    (htd : ∀ n ∈ J ⊓ L, t⁻¹ * n * t ∈ J ⊓ L)
    (hnd : ∀ n ∈ J ⊓ L, (tnorm θ l t)⁻¹ * n * tnorm θ l t ∈ J ⊓ L)
    (hns : ∀ U : Set G, IsOpen U → (1 : G) ∈ U →
      ∃ j : ℕ, ∀ n ∈ J ⊓ L, (tnorm θ l t ^ j)⁻¹ * n * tnorm θ l t ^ j ∈ U)
    {a τ : G} (ha : a ∈ J ⊓ L) (hτ : τ ∈ J ⊓ T) :
    ∃ v ∈ J, v⁻¹ * (t * a * τ) * θ v = t * τ := by
  have hconj : ∀ s ∈ J ⊓ T, ∀ n ∈ J ⊓ L, s⁻¹ * n * s ∈ J ⊓ L := fun s hs n hn =>
    ⟨J.mul_mem (J.mul_mem (J.inv_mem hs.1) hn.1) hs.1, hTL s hs.2 n hn.2⟩
  have hθS : ∀ x ∈ J ⊓ L, θ⁻¹ x ∈ J ⊓ L := fun x hx =>
    ⟨inv_apply_mem hθJ hx.1, inv_apply_mem hθL hx.2⟩
  have hcinv := continuous_inv_of_pow_eq_one hθc hl hθl

  let Ψ : G → G := fun x => θ⁻¹ (τ⁻¹ * (a⁻¹ * (t⁻¹ * x * t)) * τ)
  let φ : G → G := fun x => θ⁻¹ ((t * τ)⁻¹ * x * (t * τ))
  have hΨc : Continuous Ψ := hcinv.comp (by fun_prop)
  have hΨS : ∀ x ∈ ((J ⊓ L : Subgroup G) : Set G), Ψ x ∈ ((J ⊓ L : Subgroup G) : Set G) :=
    fun x hx => hθS _ (hconj τ hτ _ ((J ⊓ L).mul_mem ((J ⊓ L).inv_mem ha) (htd x hx)))
  have hφS : ∀ x ∈ ((J ⊓ L : Subgroup G) : Set G), φ x ∈ ((J ⊓ L : Subgroup G) : Set G) := by
    intro x hx
    refine hθS _ ?_
    have : (t * τ)⁻¹ * x * (t * τ) = τ⁻¹ * (t⁻¹ * x * t) * τ := by group
    rw [this]
    exact hconj τ hτ _ (htd x hx)
  have hid : ∀ x y, (Ψ x)⁻¹ * Ψ y = φ (x⁻¹ * y) := by
    intro x y
    show (θ⁻¹ _)⁻¹ * θ⁻¹ _ = θ⁻¹ _
    rw [← map_inv, ← map_mul]
    congr 1
    group
  have hc : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → ∃ m₀ : ℕ, ∀ m ≥ m₀,
      ∀ x ∈ ((J ⊓ L : Subgroup G) : Set G), φ^[l * m] x ∈ U := by
    intro U hU h1
    obtain ⟨j, hj⟩ := hns U hU h1
    refine ⟨j, fun m hm x hx => ?_⟩
    set n := tnorm θ l t with hn
    set τ' := tnorm θ l τ with hτ'
    have hnT : n ∈ T := tnorm_mem hθT l htT
    have hτ'S : τ' ∈ J ⊓ T := ⟨tnorm_mem hθJ l hτ.1, tnorm_mem hθT l hτ.2⟩
    have hw : tnorm θ l (t * τ) = τ' * n := by
      rw [tnorm_mul_of_comm hθT hTc l htT hτ.2, hTc _ hnT _ hτ'S.2]
    have hcomm : Commute τ' n := hTc _ hτ'S.2 _ hnT
    have hiter := iterate_twist_mul θ hθl (t * τ) m x
    have hφ : φ^[l * m] x = (n ^ m)⁻¹ * ((τ' ^ m)⁻¹ * x * τ' ^ m) * n ^ m := by
      refine hiter.trans ?_
      rw [hw, hcomm.mul_pow]
      group
    rw [hφ]
    have hy : (τ' ^ m)⁻¹ * x * τ' ^ m ∈ J ⊓ L :=
      hconj _ ⟨J.pow_mem hτ'S.1 m, T.pow_mem hτ'S.2 m⟩ x hx
    have hdom : ∀ p : ℕ, ∀ y ∈ J ⊓ L, (n ^ p)⁻¹ * y * n ^ p ∈ J ⊓ L := by
      intro p
      induction p with
      | zero => intro y hy; simpa using hy
      | succ p ih =>
        intro y hy
        have := hnd _ (ih y hy)
        have e : (n ^ (p + 1))⁻¹ * y * n ^ (p + 1) = n⁻¹ * ((n ^ p)⁻¹ * y * n ^ p) * n := by
          rw [pow_succ]
          group
        rw [e]
        exact this
    obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hm
    have e : (n ^ (j + p))⁻¹ * ((τ' ^ (j + p))⁻¹ * x * τ' ^ (j + p)) * n ^ (j + p) =
        (n ^ j)⁻¹ * ((n ^ p)⁻¹ * ((τ' ^ (j + p))⁻¹ * x * τ' ^ (j + p)) * n ^ p) * n ^ j := by
      rw [pow_add n j p, (Commute.pow_pow_self n j p).eq]
      group
    rw [e]
    exact hj _ (hdom p _ hy)
  obtain ⟨v, hvJ, hv⟩ := exists_fixed_of_contract (K := (J : Set G))
    (S := ((J ⊓ L : Subgroup G) : Set G)) hJ (fun x hx => hx.1) (J ⊓ L).one_mem hΨc hΨS hφS hid hl hc
  refine ⟨v, hvJ, ?_⟩
  have hθv : θ v = τ⁻¹ * (a⁻¹ * (t⁻¹ * v * t)) * τ := by
    conv_lhs => rw [← hv]
    show θ (θ⁻¹ _) = _
    simp
  rw [hθv]
  group

end Generic

section Torus

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce and unpack `_ ⟨s, rfl⟩ _ ⟨s', rfl⟩`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Establish `hs : Subsingleton (Fin (ones N a))` using `by unfold ones; infer_instance`. Take `rfl : i = j` from `Subsingleton.elim _ _`. Use `show ((s a).val * (s' a).val) i i = ((s' a).val * (s a).val) i i`. Simplify using `only [Matrix.mul_apply]`.

Rewrite using `[Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i, mul_comm]`.
-/
theorem tor_comm (N : ℕ) : ∀ x ∈ Tor k N, ∀ y ∈ Tor k N, x * y = y * x := by
  rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  funext a
  apply Units.ext
  ext i j
  have hs : Subsingleton (Fin (ones N a)) := by unfold ones; infer_instance
  obtain rfl : i = j := Subsingleton.elim _ _
  show ((s a).val * (s' a).val) i i = ((s' a).val * (s a).val) i i
  simp only [Matrix.mul_apply]
  rw [Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i, mul_comm]

/- English proof (translation)
Introduce and unpack `_ ⟨s, rfl⟩ n hn`. Establish `h` using `Subgroup.inv_mem _ (leviEmb_mem_normalizer_lower k (stdBlocks (ones N) (sum_ones N)) s)`. Use `(Subgroup.mem_normalizer_iff.1 h n).1 hn` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Conclude with `this`.
-/
theorem tor_conj_nlo (N : ℕ) : ∀ s ∈ Tor k N, ∀ n ∈ Nlo k N, s⁻¹ * n * s ∈ Nlo k N := by
  rintro _ ⟨s, rfl⟩ n hn
  have h := Subgroup.inv_mem _ (leviEmb_mem_normalizer_lower k (stdBlocks (ones N) (sum_ones N)) s)
  have := (Subgroup.mem_normalizer_iff.1 h n).1 hn
  rw [inv_inv] at this
  exact this

/- English proof (translation)
Take `⟨-, hJc, -, hθc, hl, hθl, hθJ, -, hθL, hθT⟩` from `hA`. Take `⟨htT, hdom, hstr⟩` from `hT`. Introduce `a ha τ hτ`. Take `⟨s, hs, hsd⟩` from `hdom 0 hl`. Take `⟨s', hs', hsd', hc⟩` from `hstr`.

Establish `ht0 : torEmb k N s = t` using `by simpa using hs`. Establish `htd : ∀ n ∈ J ⊓ Nlo k N, t⁻¹ * n * t ∈ J ⊓ Nlo k N`. Introduce `n hn`. Rewrite using `[← ht0]`. Conclude with `hsd.2.1 n hn`.

Establish `hnd : ∀ n ∈ J ⊓ Nlo k N, (tnorm θ l t)⁻¹ * n * tnorm θ l t ∈ J ⊓ Nlo k N`. Introduce `n hn`. Rewrite using `[← hs']`. Conclude with `hsd'.1.2.1 n hn`. Take `⟨v, hvJ, hv⟩` from `exists_twist_of_contract J (Nlo k N) (Tor k N) hJc θ hθc hl hθl hθJ hθL hθT (tor_comm N) (tor_conj_nlo N) htT htd hnd hc ha hτ`.

Conclude with `⟨v, hvJ, τ, hτ, hv⟩`.
-/
theorem killNlo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ) (t : GL (Fin N) k)
    (hA : admitted k N J θ l) (hT : GoodT k N J θ l t) :
    ∀ a ∈ J ⊓ Nlo k N, ∀ τ ∈ J ⊓ Tor k N, ∃ j ∈ J, ∃ κ ∈ J ⊓ Tor k N,
      j⁻¹ * (t * a * τ) * θ j = t * κ := by
  obtain ⟨-, hJc, -, hθc, hl, hθl, hθJ, -, hθL, hθT⟩ := hA
  obtain ⟨htT, hdom, hstr⟩ := hT
  intro a ha τ hτ
  obtain ⟨s, hs, hsd⟩ := hdom 0 hl
  obtain ⟨s', hs', hsd', hc⟩ := hstr
  have ht0 : torEmb k N s = t := by simpa using hs
  have htd : ∀ n ∈ J ⊓ Nlo k N, t⁻¹ * n * t ∈ J ⊓ Nlo k N := by
    intro n hn
    rw [← ht0]
    exact hsd.2.1 n hn
  have hnd : ∀ n ∈ J ⊓ Nlo k N, (tnorm θ l t)⁻¹ * n * tnorm θ l t ∈ J ⊓ Nlo k N := by
    intro n hn
    rw [← hs']
    exact hsd'.1.2.1 n hn
  obtain ⟨v, hvJ, hv⟩ := exists_twist_of_contract J (Nlo k N) (Tor k N) hJc θ hθc hl hθl hθJ hθL hθT
    (tor_comm N) (tor_conj_nlo N) htT htd hnd hc ha hτ
  exact ⟨v, hvJ, τ, hτ, hv⟩

end Torus

end GlobalTheory.CompanionTheory.Lbc.KillNlo

end
