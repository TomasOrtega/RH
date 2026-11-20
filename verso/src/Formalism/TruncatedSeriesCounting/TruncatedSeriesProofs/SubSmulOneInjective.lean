import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality

noncomputable section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Module

section Snake

variable {O : Type} [CommRing O]

/- English proof (translation)
Establish `hF : LinearMap.range a ≤ (LinearMap.range b).comap f`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨f x, h1 x⟩`. Establish `hG : LinearMap.range b ≤ (LinearMap.range c).comap g`. Introduce and unpack `_ ⟨y, rfl⟩`.

Conclude with `⟨g y, h2 y⟩`. Set `F` to `Submodule.mapQ (LinearMap.range a) (LinearMap.range b) f hF`. Set `G` to `Submodule.mapQ (LinearMap.range b) (LinearMap.range c) g hG`. Use `Module.length_eq_add_of_exact F G ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`.

Introduce `x hx`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hx` using `[LinearMap.mem_ker]`. Simplify using `only [F, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx`. Take `⟨y, hy⟩` from `hx`.

Establish `hgy : g y = 0`. Apply `hc` to reduce the goal to its premises. Rewrite using `[h2, hy, hfg.apply_apply_eq_zero, map_zero]`. Take `⟨z, rfl⟩` from `(hfg y).1 hgy`. Establish `: a z = x` using `hf (by rw [← h1, hy])`.

Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨z, this⟩`. Introduce `w`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Take `⟨y, rfl⟩` from `hg w`.

Conclude with `⟨Submodule.Quotient.mk y, by simp [G]⟩`. Introduce `w`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Simplify using `only [G, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu⟩`. Take `⟨v, rfl⟩` from `hg u`. Establish `: g (y - b v) = 0` using `by rw [map_sub, ← h2, hu, sub_self]`. Take `⟨z, hz⟩` from `(hfg _).1 this`. Use `⟨Submodule.Quotient.mk z, ?_⟩` and prove the remaining obligations.

Simplify using `only [F, Submodule.mapQ_apply, hz]`. Rewrite using `[Submodule.Quotient.eq]`. Conclude with `⟨-v, by simp⟩`. Introduce and unpack `⟨z, hz⟩`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`.

Simplify using `only [F, Submodule.mapQ_apply] at hz`. Rewrite `hz` using `[Submodule.Quotient.eq']`. Take `⟨t, ht⟩` from `hz`. Use `⟨g t, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, ht, map_add, map_neg, hfg.apply_apply_eq_zero, neg_zero, zero_add]`.
-/
theorem len_coker_add {A B C : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    [AddCommGroup C] [Module O C] (f : A →ₗ[O] B) (g : B →ₗ[O] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (a : Module.End O A) (b : Module.End O B) (c : Module.End O C)
    (h1 : ∀ x, b (f x) = f (a x)) (h2 : ∀ y, c (g y) = g (b y)) (hc : Function.Injective c) :
    Module.length O (B ⧸ LinearMap.range b) =
      Module.length O (A ⧸ LinearMap.range a) + Module.length O (C ⧸ LinearMap.range c) := by
  have hF : LinearMap.range a ≤ (LinearMap.range b).comap f := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, h1 x⟩
  have hG : LinearMap.range b ≤ (LinearMap.range c).comap g := by
    rintro _ ⟨y, rfl⟩
    exact ⟨g y, h2 y⟩
  let F := Submodule.mapQ (LinearMap.range a) (LinearMap.range b) f hF
  let G := Submodule.mapQ (LinearMap.range b) (LinearMap.range c) g hG
  refine Module.length_eq_add_of_exact F G ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [F, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, hy⟩ := hx
    have hgy : g y = 0 := by
      apply hc
      rw [h2, hy, hfg.apply_apply_eq_zero, map_zero]
    obtain ⟨z, rfl⟩ := (hfg y).1 hgy
    have : a z = x := hf (by rw [← h1, hy])
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, this⟩
  · intro w
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨y, rfl⟩ := hg w
    exact ⟨Submodule.Quotient.mk y, by simp [G]⟩
  · intro w
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    simp only [G, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨v, rfl⟩ := hg u
      have : g (y - b v) = 0 := by rw [map_sub, ← h2, hu, sub_self]
      obtain ⟨z, hz⟩ := (hfg _).1 this
      refine ⟨Submodule.Quotient.mk z, ?_⟩
      simp only [F, Submodule.mapQ_apply, hz]
      rw [Submodule.Quotient.eq]
      exact ⟨-v, by simp⟩
    · rintro ⟨z, hz⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      simp only [F, Submodule.mapQ_apply] at hz
      rw [Submodule.Quotient.eq'] at hz
      obtain ⟨t, ht⟩ := hz
      refine ⟨g t, ?_⟩
      rw [h2, ht, map_add, map_neg, hfg.apply_apply_eq_zero, neg_zero, zero_add]

end Snake

section Main

variable {O : Type} [CommRing O] [IsDomain O]

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Establish `h1 : q x = ℓ • x`. Rewrite `hx` using `[LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `hx`.

Establish `h2 : ∀ k : ℕ, (q ^ k) x = ℓ ^ k • x`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h1, smul_smul, pow_succ]`.

Establish `h3` using `h2 n`. Rewrite `h3` using `[hq, LinearMap.zero_apply]`. Conclude with `(smul_eq_zero.mp h3.symm).resolve_left (pow_ne_zero n hℓ)`.
-/
theorem sub_smul_one_injective {M : Type} [AddCommGroup M] [Module O M] [IsTorsionFree O M]
    (ℓ : O) (hℓ : ℓ ≠ 0) (q : Module.End O M) (n : ℕ) (hq : q ^ n = 0) :
    Function.Injective (q - ℓ • (1 : Module.End O M)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h1 : q x = ℓ • x := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hx
    exact hx
  have h2 : ∀ k : ℕ, (q ^ k) x = ℓ ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h1, smul_smul, pow_succ]
  have h3 := h2 n
  rw [hq, LinearMap.zero_apply] at h3
  exact (smul_eq_zero.mp h3.symm).resolve_left (pow_ne_zero n hℓ)

/- English proof (translation)
Set `e` to `(Module.finBasis O R).equivFun`. Establish `hmap : (LinearMap.range ((0 : Module.End O R) - ℓ • (1 : Module.End O R))).map (e : R →ₗ[O] (Fin (finrank O R) → O)) = Submodule.pi Set.univ (fun _ => Ideal.span {ℓ})`. Use extensionality with `v`. Simplify using `only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨y, rfl⟩, rfl⟩ i`. Conclude with `⟨-(e y i), by simp [mul_comm]⟩`. Introduce `h choose c hc using h`. Use `⟨_, ⟨e.symm (fun i => -c i), rfl⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i`.

Express the relevant statement in the definitionally equal form `e (((0 : Module.End O R) - ℓ • (1 : Module.End O R)) (e.symm fun i => -c i)) i = v i`. Simplify using `[← hc, mul_comm]`. Rewrite using `[(Submodule.Quotient.equiv _ _ e hmap).length_eq, (Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype]`. Simplify using `[Finset.sum_const, nsmul_eq_mul]`.
-/
theorem len_base (R : Type) [AddCommGroup R] [Module O R] [Module.Free O R] [Module.Finite O R]
    (ℓ : O) :
    Module.length O (R ⧸ LinearMap.range ((0 : Module.End O R) - ℓ • (1 : Module.End O R))) =
      (Module.finrank O R : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  let e := (Module.finBasis O R).equivFun
  have hmap : (LinearMap.range ((0 : Module.End O R) - ℓ • (1 : Module.End O R))).map
      (e : R →ₗ[O] (Fin (finrank O R) → O)) =
      Submodule.pi Set.univ (fun _ => Ideal.span {ℓ}) := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ,
      true_implies, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      exact ⟨-(e y i), by simp [mul_comm]⟩
    · intro h
      choose c hc using h
      refine ⟨_, ⟨e.symm (fun i => -c i), rfl⟩, ?_⟩
      ext i
      change e (((0 : Module.End O R) - ℓ • (1 : Module.End O R)) (e.symm fun i => -c i)) i = v i
      simp [← hc, mul_comm]
  rw [(Submodule.Quotient.equiv _ _ e hmap).length_eq, (Submodule.quotientPi _).length_eq,
    Module.length_pi_of_fintype]
  simp [Finset.sum_const, nsmul_eq_mul]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `R _ _ _ _ q hq`. Rewrite `hq` using `[zero_add, pow_one]`. Substitute `hq` using the available equality.

Conclude with `len_base R ℓ`. Consider the case `succ n ih`. Introduce `R _ _ _ _ q hq`. Establish `hK : ∀ x ∈ LinearMap.ker q, q x ∈ LinearMap.ker q` using `fun x hx => by`. Rewrite using `[LinearMap.mem_ker.mp hx]`.

Conclude with `Submodule.zero_mem _`. Establish `hQ : ∀ x ∈ LinearMap.range q, q x ∈ LinearMap.range q` using `fun x _ => LinearMap.mem_range_self q x`. Set `qK` to `q.restrict hK`. Set `qQ` to `q.restrict hQ`. Establish `hqK : qK = 0`.

Use extensionality with `⟨x, hx⟩`. Simplify `hx` using `[qK]`. Establish `key : ∀ (k : ℕ) (x : LinearMap.range q), (((qQ ^ k) x : LinearMap.range q) : R) = (q ^ k) (x : R)`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ k ihk`. Introduce `x`. Rewrite using `[pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihk]`.

Both sides reduce to the same expression. Establish `hqQ : qQ ^ (n + 1) = 0`. Use extensionality with `⟨x, y, rfl⟩`. Rewrite using `[key, LinearMap.zero_apply, Submodule.coe_zero, ← Module.End.mul_apply, ← pow_succ, hq, LinearMap.zero_apply]`. Establish `hex : Function.Exact (LinearMap.ker q).subtype q.rangeRestrict` using `LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype])`.

Establish `hsn` using `len_coker_add (LinearMap.ker q).subtype q.rangeRestrict (LinearMap.ker q).injective_subtype q.surjective_rangeRestrict hex (qK - ℓ • (1 : Module.End O _)) (q - ℓ • (1 : Module.End O R)) (qQ - ℓ • (1 : Module.End O _)) (fun x => by simp [qK]) (fun y => by ext; simp [qQ]) (sub_smul …`. Rewrite using `[hsn, ih _ qK (by rw [hqK, zero_pow (Nat.succ_ne_zero _)]), ih _ qQ hqQ, ← add_mul, ← Nat.cast_add]`. Use `congr 2`. Establish `h1` using `(LinearMap.ker q).finrank_quotient_add_finrank`. Rewrite `h1` using `[LinearEquiv.finrank_eq q.quotKerEquivRange]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem len_main [IsPrincipalIdealRing O] (ℓ : O) (hℓ : ℓ ≠ 0) (n : ℕ) :
    ∀ (R : Type) [AddCommGroup R] [Module O R] [Module.Free O R] [Module.Finite O R]
      (q : Module.End O R), q ^ (n + 1) = 0 →
      Module.length O (R ⧸ LinearMap.range (q - ℓ • (1 : Module.End O R))) =
        (Module.finrank O R : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  induction n with
  | zero =>
    intro R _ _ _ _ q hq
    rw [zero_add, pow_one] at hq
    subst hq
    exact len_base R ℓ
  | succ n ih =>
    intro R _ _ _ _ q hq
    have hK : ∀ x ∈ LinearMap.ker q, q x ∈ LinearMap.ker q := fun x hx => by
      rw [LinearMap.mem_ker.mp hx]; exact Submodule.zero_mem _
    have hQ : ∀ x ∈ LinearMap.range q, q x ∈ LinearMap.range q :=
      fun x _ => LinearMap.mem_range_self q x
    let qK := q.restrict hK
    let qQ := q.restrict hQ
    have hqK : qK = 0 := by
      ext ⟨x, hx⟩
      simpa [qK] using hx
    have key : ∀ (k : ℕ) (x : LinearMap.range q), (((qQ ^ k) x : LinearMap.range q) : R) =
        (q ^ k) (x : R) := by
      intro k
      induction k with
      | zero => intro x; simp
      | succ k ihk =>
        intro x
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihk]
        rfl
    have hqQ : qQ ^ (n + 1) = 0 := by
      ext ⟨x, y, rfl⟩
      rw [key, LinearMap.zero_apply, Submodule.coe_zero, ← Module.End.mul_apply, ← pow_succ, hq,
        LinearMap.zero_apply]
    have hex : Function.Exact (LinearMap.ker q).subtype q.rangeRestrict :=
      LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype])
    have hsn := len_coker_add (LinearMap.ker q).subtype q.rangeRestrict
      (LinearMap.ker q).injective_subtype q.surjective_rangeRestrict hex
      (qK - ℓ • (1 : Module.End O _)) (q - ℓ • (1 : Module.End O R))
      (qQ - ℓ • (1 : Module.End O _))
      (fun x => by simp [qK]) (fun y => by ext; simp [qQ])
      (sub_smul_one_injective ℓ hℓ qQ (n + 1) hqQ)
    rw [hsn, ih _ qK (by rw [hqK, zero_pow (Nat.succ_ne_zero _)]), ih _ qQ hqQ, ← add_mul,
      ← Nat.cast_add]
    congr 2
    have h1 := (LinearMap.ker q).finrank_quotient_add_finrank
    rw [LinearEquiv.finrank_eq q.quotKerEquivRange] at h1
    omega

end Main

/- English proof (translation)
Introduce `O _ _ _ R _ _ _ _ ℓ hℓ q hq`. Take `⟨n, hn⟩` from `hq`. Conclude with `len_main ℓ hℓ n R q (by rw [pow_succ, hn, zero_mul])`.
-/
theorem length_pi_zero_bound : LenPi0 := by
  intro O _ _ _ R _ _ _ _ ℓ hℓ q hq
  obtain ⟨n, hn⟩ := hq
  exact len_main ℓ hℓ n R q (by rw [pow_succ, hn, zero_mul])

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
