import Mathlib

open Module Submodule

namespace GlobalTheory.HodgeConjLength

section General
variable {R : Type} [CommRing R] {A B C : Type} [AddCommGroup A] [Module R A] [AddCommGroup B]
  [Module R B] [AddCommGroup C] [Module R C]

/- English proof (translation)
Establish `h1 : Module.length R B = Module.length R (LinearMap.ker g) + Module.length R (LinearMap.range g)`. Use `Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict (Submodule.subtype_injective _) g.surjective_rangeRestrict ?_` and prove the remaining obligations. Rewrite using `[LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]`. Rewrite using `[h1]`. Use `add_le_add ?_ (Module.length_le_of_injective _ (Submodule.subtype_injective _))` and prove the remaining obligations.

Conclude with `(Module.length_le_of_injective _ (Submodule.inclusion_injective h)).trans (Module.length_le_of_surjective _ f.surjective_rangeRestrict)`.
-/
theorem length_le_add (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : LinearMap.ker g ≤ LinearMap.range f) :
    Module.length R B ≤ Module.length R A + Module.length R C := by
  have h1 : Module.length R B =
      Module.length R (LinearMap.ker g) + Module.length R (LinearMap.range g) := by
    refine Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
      (Submodule.subtype_injective _) g.surjective_rangeRestrict ?_
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  rw [h1]
  refine add_le_add ?_ (Module.length_le_of_injective _ (Submodule.subtype_injective _))
  exact (Module.length_le_of_injective _ (Submodule.inclusion_injective h)).trans
    (Module.length_le_of_surjective _ f.surjective_rangeRestrict)

def torsMap (f : A →ₗ[R] B) : torsion R A →ₗ[R] torsion R B :=
  f.restrict fun x hx => by
    obtain ⟨r, hr⟩ := (mem_torsion_iff x).1 hx
    refine (mem_torsion_iff _).2 ⟨r, ?_⟩
    rw [Submonoid.smul_def] at hr ⊢
    rw [← map_smul, hr, map_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_torsMap (f : A →ₗ[R] B) (x : torsion R A) : (torsMap f x : B) = f x := rfl

/- English proof (translation)
Use `length_le_add (torsMap f) (torsMap g) fun b hb => ?_` and prove the remaining obligations. Take `⟨a, ha, hab⟩` from `h b b.2 (congrArg Subtype.val hb)`. Conclude with `⟨⟨a, ha⟩, Subtype.ext hab⟩`.
-/
theorem torsLen_le (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : ∀ b ∈ torsion R B, g b = 0 → ∃ a ∈ torsion R A, f a = b) :
    Module.length R (torsion R B) ≤
      Module.length R (torsion R A) + Module.length R (torsion R C) := by
  refine length_le_add (torsMap f) (torsMap g) fun b hb => ?_
  obtain ⟨a, ha, hab⟩ := h b b.2 (congrArg Subtype.val hb)
  exact ⟨⟨a, ha⟩, Subtype.ext hab⟩

/- English proof (translation)
Use `Module.length_eq_add_of_exact (torsMap f) (torsMap g) ?_ ?_ ?_` and prove the remaining obligations. Introduce `x y hxy`. Conclude with `Subtype.ext (hf (congrArg Subtype.val hxy))`. Introduce and unpack `⟨c, hc⟩`. Take `⟨b, rfl⟩` from `hC c hc`.

Take `⟨r, hr⟩` from `(mem_torsion_iff _).1 hc`. Rewrite `hr` using `[Submonoid.smul_def, ← map_smul]`. Establish `: (r : R) • b ∈ LinearMap.range f` using `hfg ▸ hr`. Take `⟨a, ha⟩` from `this`. Take `⟨s, hs⟩` from `(mem_torsion_iff _).1 (hA a)`.

Use `⟨⟨b, (mem_torsion_iff _).2 ⟨s * r, ?_⟩⟩, rfl⟩` and prove the remaining obligations. Rewrite `hs`, the goal using `[Submonoid.smul_def]`. Rewrite using `[Submonoid.coe_mul, mul_smul, ← ha, ← map_smul, hs, map_zero]`. Introduce `b`. Prove the components needed by the constructor for the conclusion.

Introduce `hb`. Establish `: (b : B) ∈ LinearMap.range f` using `hfg ▸ (congrArg Subtype.val hb : g b = 0)`. Take `⟨a, ha⟩` from `this`. Conclude with `⟨⟨a, hA a⟩, Subtype.ext ha⟩`. Introduce and unpack `⟨a, rfl⟩`.

Establish `: f a ∈ LinearMap.ker g` using `hfg ▸ LinearMap.mem_range_self f a`. Conclude with `Subtype.ext this`.
-/
theorem torsLen_eq (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hfg : LinearMap.ker g = LinearMap.range f) (hA : ∀ a : A, a ∈ torsion R A)
    (hC : ∀ c ∈ torsion R C, c ∈ LinearMap.range g) :
    Module.length R (torsion R B) =
      Module.length R (torsion R A) + Module.length R (torsion R C) := by
  refine Module.length_eq_add_of_exact (torsMap f) (torsMap g) ?_ ?_ ?_
  · intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  · rintro ⟨c, hc⟩
    obtain ⟨b, rfl⟩ := hC c hc
    obtain ⟨r, hr⟩ := (mem_torsion_iff _).1 hc
    rw [Submonoid.smul_def, ← map_smul] at hr
    have : (r : R) • b ∈ LinearMap.range f := hfg ▸ hr
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, hs⟩ := (mem_torsion_iff _).1 (hA a)
    refine ⟨⟨b, (mem_torsion_iff _).2 ⟨s * r, ?_⟩⟩, rfl⟩
    rw [Submonoid.smul_def] at hs ⊢
    rw [Submonoid.coe_mul, mul_smul, ← ha, ← map_smul, hs, map_zero]
  · intro b
    constructor
    · intro hb
      have : (b : B) ∈ LinearMap.range f := hfg ▸ (congrArg Subtype.val hb : g b = 0)
      obtain ⟨a, ha⟩ := this
      exact ⟨⟨a, hA a⟩, Subtype.ext ha⟩
    · rintro ⟨a, rfl⟩
      have : f a ∈ LinearMap.ker g := hfg ▸ LinearMap.mem_range_self f a
      exact Subtype.ext this

/- English proof (translation)
Rewrite using `[mem_torsion_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`. Use `⟨r, nonZeroDivisors.coe_ne_zero r, ?_⟩` and prove the remaining obligations. Rewrite `hr` using `[Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis.

Introduce and unpack `⟨r, hr, h⟩`. Use `⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]` and apply the resulting hypothesis.
-/
theorem mk_mem_torsion [IsDomain R] (P : Submodule R A) (x : A) :
    (Submodule.Quotient.mk x : A ⧸ P) ∈ torsion R (A ⧸ P) ↔ ∃ r : R, r ≠ 0 ∧ r • x ∈ P := by
  rw [mem_torsion_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, nonZeroDivisors.coe_ne_zero r, ?_⟩
    rwa [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hr
  · rintro ⟨r, hr, h⟩
    refine ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩, ?_⟩
    rwa [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]

/- English proof (translation)
Establish `hli : LinearIndependent R (fun k => b (f k))` using `b.linearIndependent.comp f f.injective`. Set `h : (κ → R) →ₗ[R] A` to `Fintype.linearCombination R (fun k => b (f k))`. Establish `hh : ∀ x, h x = ∑ k, x k • b (f k)` using `fun x => Fintype.linearCombination_apply _ _ _`. Establish `hinj : Function.Injective h` using `hli.fintypeLinearCombination_injective`. Establish `hmem : ∀ y, y ∈ P ↔ ∃ c : κ → R, h (fun k => c k * a k) = y`.

Introduce `y`. Rewrite using `[hP, Submodule.mem_span_range_iff_exists_fun]`. Simplify using `only [hh, mul_smul]`. Set `Q : Submodule R (κ → R)` to `Submodule.pi Set.univ fun k => Ideal.span {a k}`. Establish `hker : LinearMap.ker (P.mkQ ∘ₗ h) = Q`.

Use extensionality with `x`. Simplify using `only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem, Q, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩ k`. Conclude with `⟨c k, congrFun (hinj hc) k⟩`.

Introduce `hx choose c hc using hx`. Conclude with `⟨c, congrArg h (funext hc)⟩`. Establish `hrange : LinearMap.range (P.mkQ ∘ₗ h) = torsion R (A ⧸ P)`. Use extensionality with `y`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective P y`.

Rewrite using `[mk_mem_torsion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩`. Use `⟨∏ k, a k, Finset.prod_ne_zero_iff.2 fun k _ => ha k, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, ← hx, ← map_smul, ← LinearMap.mem_ker, hker]`.

Introduce `k _`. Conclude with `Ideal.mem_span_singleton.2 ((Finset.dvd_prod_of_mem a (Finset.mem_univ k)).mul_right _)`. Introduce and unpack `⟨r, hr, hy⟩`. Take `⟨c, hc⟩` from `(hmem _).1 hy`. Establish `hy' : y ∈ span R (b '' Set.range f)`.

Rewrite using `[Basis.mem_span_image]`. Introduce `t ht`. Assume the negation of the conclusion as `hn`. Establish `h1 : b.repr (r • y) t = 0`. Rewrite using `[← hc, hh, map_sum, Finsupp.finset_sum_apply]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Establish `: f k ≠ t` using `fun e => hn ⟨k, e⟩`. Simplify using `[Finsupp.single_apply, this]`. Rewrite `h1` using `[map_smul, Finsupp.smul_apply, smul_eq_mul, mul_eq_zero]`. Conclude with `(Finsupp.mem_support_iff.1 ht) (h1.resolve_left hr)`.

Rewrite `hy'` using `[← Set.range_comp, Submodule.mem_span_range_iff_exists_fun]`. Take `⟨x, hx⟩` from `hy'`. Conclude with `⟨x, by simp only [LinearMap.comp_apply, Submodule.mkQ_apply, hh]; exact congrArg _ hx⟩`. Rewrite using `[← hrange, ← (P.mkQ ∘ₗ h).quotKerEquivRange.length_eq, hker, (Submodule.quotientPi fun k => Ideal.span {a k}).length_eq, Module.length_pi_of_fintype]`. Both sides reduce to the same expression.
-/
theorem torsLen_diag [IsDomain R] {ι κ : Type} [Fintype ι] [Fintype κ] (b : Basis ι R A)
    (f : κ ↪ ι) (a : κ → R) (ha : ∀ k, a k ≠ 0) (P : Submodule R A)
    (hP : P = span R (Set.range fun k => a k • b (f k))) :
    Module.length R (torsion R (A ⧸ P)) = ∑ k, Ring.ord R (a k) := by
  classical
  have hli : LinearIndependent R (fun k => b (f k)) := b.linearIndependent.comp f f.injective
  let h : (κ → R) →ₗ[R] A := Fintype.linearCombination R (fun k => b (f k))
  have hh : ∀ x, h x = ∑ k, x k • b (f k) := fun x => Fintype.linearCombination_apply _ _ _
  have hinj : Function.Injective h := hli.fintypeLinearCombination_injective
  have hmem : ∀ y, y ∈ P ↔ ∃ c : κ → R, h (fun k => c k * a k) = y := by
    intro y
    rw [hP, Submodule.mem_span_range_iff_exists_fun]
    simp only [hh, mul_smul]
  let Q : Submodule R (κ → R) := Submodule.pi Set.univ fun k => Ideal.span {a k}
  have hker : LinearMap.ker (P.mkQ ∘ₗ h) = Q := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, hmem, Q, Submodule.mem_pi, Set.mem_univ, true_imp_iff,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩ k
      exact ⟨c k, congrFun (hinj hc) k⟩
    · intro hx
      choose c hc using hx
      exact ⟨c, congrArg h (funext hc)⟩
  have hrange : LinearMap.range (P.mkQ ∘ₗ h) = torsion R (A ⧸ P) := by
    ext y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P y
    rw [mk_mem_torsion]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨∏ k, a k, Finset.prod_ne_zero_iff.2 fun k _ => ha k, ?_⟩
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, ← hx, ← map_smul,
        ← LinearMap.mem_ker, hker]
      intro k _
      exact Ideal.mem_span_singleton.2 ((Finset.dvd_prod_of_mem a (Finset.mem_univ k)).mul_right _)
    · rintro ⟨r, hr, hy⟩
      obtain ⟨c, hc⟩ := (hmem _).1 hy
      have hy' : y ∈ span R (b '' Set.range f) := by
        rw [Basis.mem_span_image]
        intro t ht
        by_contra hn
        have h1 : b.repr (r • y) t = 0 := by
          rw [← hc, hh, map_sum, Finsupp.finset_sum_apply]
          refine Finset.sum_eq_zero fun k _ => ?_
          have : f k ≠ t := fun e => hn ⟨k, e⟩
          simp [Finsupp.single_apply, this]
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_eq_zero] at h1
        exact (Finsupp.mem_support_iff.1 ht) (h1.resolve_left hr)
      rw [← Set.range_comp, Submodule.mem_span_range_iff_exists_fun] at hy'
      obtain ⟨x, hx⟩ := hy'
      exact ⟨x, by simp only [LinearMap.comp_apply, Submodule.mkQ_apply, hh]; exact congrArg _ hx⟩
  rw [← hrange, ← (P.mkQ ∘ₗ h).quotKerEquivRange.length_eq, hker,
    (Submodule.quotientPi fun k => Ideal.span {a k}).length_eq, Module.length_pi_of_fintype]
  rfl

end General

section Rank
variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {A B : Type} [AddCommGroup A]
  [Module R A] [AddCommGroup B] [Module R B] [Module.Finite R A]

/- English proof (translation)
Establish `h1` using `Submodule.finrank_quotient_add_finrank (LinearMap.ker (f ∘ₗ P.subtype))`. Rewrite `h1` using `[(f ∘ₗ P.subtype).quotKerEquivRange.finrank_eq, LinearMap.range_comp, Submodule.range_subtype, ← Submodule.finrank_map_subtype_eq, LinearMap.ker_comp, Submodule.map_comap_subtype]`. Conclude with `h1`.
-/
theorem finrank_map_add (f : A →ₗ[R] B) (P : Submodule R A) :
    finrank R (P.map f) + finrank R (P ⊓ LinearMap.ker f : Submodule R A) = finrank R P := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker (f ∘ₗ P.subtype))
  rw [(f ∘ₗ P.subtype).quotKerEquivRange.finrank_eq, LinearMap.range_comp, Submodule.range_subtype,
    ← Submodule.finrank_map_subtype_eq, LinearMap.ker_comp, Submodule.map_comap_subtype] at h1
  exact h1

/- English proof (translation)
Establish `h` using `Submodule.rank_sup_add_rank_inf_eq P Q`. Simplify using `only [← Module.finrank_eq_rank] at h`. Conclude with `h` after adjusting the coercions.
-/
theorem finrank_sup_add_inf (P Q : Submodule R A) :
    finrank R (P ⊔ Q : Submodule R A) + finrank R (P ⊓ Q : Submodule R A) =
      finrank R P + finrank R Q := by
  have h := Submodule.rank_sup_add_rank_inf_eq P Q
  simp only [← Module.finrank_eq_rank] at h
  exact_mod_cast h

/- English proof (translation)
Establish `h1` using `Submodule.finrank_quotient_add_finrank (P.comap Q.subtype)`. Rewrite `h1` using `[(Submodule.comapSubtypeEquivOfLe h).finrank_eq]`. Establish `h2 : finrank R (Q ⧸ P.comap Q.subtype) = 0` using `by omega`. Rewrite `h2` using `[Module.finrank_eq_zero_iff_isTorsion]`. Establish `h3 : (Submodule.Quotient.mk ⟨x, hx⟩ : Q ⧸ P.comap Q.subtype) ∈ torsion R _` using `(mem_torsion_iff _).2 (@h2 _)`.

Conclude with `(mk_mem_torsion (P.comap Q.subtype) ⟨x, hx⟩).1 h3`.
-/
theorem exists_smul_mem_of_finrank_le {P Q : Submodule R A} (h : P ≤ Q)
    (hr : finrank R Q ≤ finrank R P) (x : A) (hx : x ∈ Q) : ∃ r : R, r ≠ 0 ∧ r • x ∈ P := by
  have h1 := Submodule.finrank_quotient_add_finrank (P.comap Q.subtype)
  rw [(Submodule.comapSubtypeEquivOfLe h).finrank_eq] at h1
  have h2 : finrank R (Q ⧸ P.comap Q.subtype) = 0 := by omega
  rw [Module.finrank_eq_zero_iff_isTorsion] at h2
  have h3 : (Submodule.Quotient.mk ⟨x, hx⟩ : Q ⧸ P.comap Q.subtype) ∈ torsion R _ :=
    (mem_torsion_iff _).2 (@h2 _)
  exact (mk_mem_torsion (P.comap Q.subtype) ⟨x, hx⟩).1 h3

/- English proof (translation)
Establish `h1` using `Submodule.finrank_quotient_add_finrank P`. Establish `h2 : finrank R (A ⧸ P) = 0`. Rewrite using `[Module.finrank_eq_zero_iff_isTorsion]`. Introduce `x`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective P x`.

Conclude with `(mem_torsion_iff _).1 ((mk_mem_torsion P x).2 (h x))`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_eq_of_smul_mem (P : Submodule R A) (h : ∀ x, ∃ r : R, r ≠ 0 ∧ r • x ∈ P) :
    finrank R P = finrank R A := by
  have h1 := Submodule.finrank_quotient_add_finrank P
  have h2 : finrank R (A ⧸ P) = 0 := by
    rw [Module.finrank_eq_zero_iff_isTorsion]
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P x
    exact (mem_torsion_iff _).1 ((mk_mem_torsion P x).2 (h x))
  omega

end Rank

section Twist
variable {R : Type} [CommRing R] {σ : R →+* R} {A B : Type} [AddCommGroup A]
  [Module R A] [AddCommGroup B] [Module R B]

/- English proof (translation)
Use `le_antisymm (span_le.2 ?_) (span_mono (Set.image_mono subset_span))` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul r x _ hx => rw [LinearMap.map_smulₛₗ]`. Conclude with `smul_mem _ _ hx`.
-/
theorem span_image_span (i : A →ₛₗ[σ] B) (S : Set A) :
    span R (i '' (span R S : Set A)) = span R (i '' S) := by
  refine le_antisymm (span_le.2 ?_) (span_mono (Set.image_mono subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact smul_mem _ _ hx

variable [IsDomain R] [IsDiscreteValuationRing R] [Module.Free R A] [Module.Finite R A]

/- English proof (translation)
Take `⟨n, bM, bN, f, a, snf⟩` from `P.smithNormalForm (Module.finBasis R A)`. Establish `ha : ∀ k, a k ≠ 0` using `fun k hk => bN.ne_zero k (Subtype.ext (by rw [snf, hk]; simp))`. Establish `hP : P = span R (Set.range fun k => a k • bM (f k))` using `by conv_lhs => rw [← P.range_subtype, LinearMap.range_eq_map, ← bN.span_eq, Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `k`.

Conclude with `snf k`. Take `⟨hli, hsp⟩` from `hi _ bM`. Set `c : Basis _ R B` to `Basis.mk hli hsp.ge`. Establish `hc : ∀ k, c k = i (bM k)` using `fun k => Basis.mk_apply _ _ _`. Establish `hP1 : span R (i '' (P : Set A)) = span R (Set.range fun k => a k ^ p • c (f k))` using `by conv_lhs => rw [hP, span_image_span, ← Set.range_comp]`.

Use `congr 2`. Use function extensionality and compare the values at `k`. Simplify using `[hc, hσ]`. Establish `ha' : ∀ k, a k ^ p ≠ 0` using `fun k => pow_ne_zero _ (ha k)`. Rewrite using `[torsLen_diag c f _ ha' _ hP1, torsLen_diag bM f a ha P hP]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hP1, finrank_span_eq_card, finrank_eq_card_basis bN]`. Establish `h1 : LinearIndependent R (fun k => c (f k))` using `c.linearIndependent.comp f f.injective`. Rewrite `h1`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg k`.

Simplify using `only [← mul_smul] at hg`. Conclude with `(mul_eq_zero.1 (h1 _ hg k)).resolve_right (ha' k)`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero (ha k)) p`. Use `ENat.sum_ne_top.2 fun k _ => ?_` and prove the remaining obligations.

Conclude with `Module.length_ne_top_iff.2 (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero (ha k)))`.
-/
theorem twist {p : ℕ} (hσ : ∀ r, σ r = r ^ p) (i : A →ₛₗ[σ] B)
    (hi : ∀ (n : ℕ) (b : Basis (Fin n) R A), LinearIndependent R (fun k => i (b k)) ∧
      span R (Set.range fun k => i (b k)) = ⊤) (P : Submodule R A) :
    finrank R (span R (i '' (P : Set A))) = finrank R P ∧
    Module.length R (torsion R (B ⧸ span R (i '' (P : Set A)))) =
      p • Module.length R (torsion R (A ⧸ P)) ∧ Module.length R (torsion R (A ⧸ P)) ≠ ⊤ := by
  obtain ⟨n, bM, bN, f, a, snf⟩ := P.smithNormalForm (Module.finBasis R A)
  have ha : ∀ k, a k ≠ 0 := fun k hk => bN.ne_zero k (Subtype.ext (by rw [snf, hk]; simp))
  have hP : P = span R (Set.range fun k => a k • bM (f k)) := by
    conv_lhs => rw [← P.range_subtype, LinearMap.range_eq_map, ← bN.span_eq, Submodule.map_span,
      ← Set.range_comp]
    congr 2
    funext k
    exact snf k
  obtain ⟨hli, hsp⟩ := hi _ bM
  let c : Basis _ R B := Basis.mk hli hsp.ge
  have hc : ∀ k, c k = i (bM k) := fun k => Basis.mk_apply _ _ _
  have hP1 : span R (i '' (P : Set A)) = span R (Set.range fun k => a k ^ p • c (f k)) := by
    conv_lhs => rw [hP, span_image_span, ← Set.range_comp]
    congr 2
    funext k
    simp [hc, hσ]
  have ha' : ∀ k, a k ^ p ≠ 0 := fun k => pow_ne_zero _ (ha k)
  rw [torsLen_diag c f _ ha' _ hP1, torsLen_diag bM f a ha P hP]
  refine ⟨?_, ?_, ?_⟩
  · rw [hP1, finrank_span_eq_card, finrank_eq_card_basis bN]
    have h1 : LinearIndependent R (fun k => c (f k)) := c.linearIndependent.comp f f.injective
    rw [Fintype.linearIndependent_iff] at h1 ⊢
    intro g hg k
    simp only [← mul_smul] at hg
    exact (mul_eq_zero.1 (h1 _ hg k)).resolve_right (ha' k)
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero (ha k)) p
  · refine ENat.sum_ne_top.2 fun k _ => ?_
    exact Module.length_ne_top_iff.2
      (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero (ha k)))

omit [IsDomain R] [IsDiscreteValuationRing R] in
/- English proof (translation)
Take `⟨hli, hsp⟩` from `hi _ (Module.finBasis R A)`. Set `c : Basis _ R B` to `Basis.mk hli hsp.ge`. Use `⟨?_, Module.Free.of_basis c, Module.Finite.of_basis c, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hsp]`. Conclude with `span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩)`.

Rewrite using `[finrank_eq_card_basis c, Fintype.card_fin]`.
-/
theorem span_image_top [Nontrivial R] (i : A →ₛₗ[σ] B)
    (hi : ∀ (n : ℕ) (b : Basis (Fin n) R A), LinearIndependent R (fun k => i (b k)) ∧
      span R (Set.range fun k => i (b k)) = ⊤) :
    span R (Set.range i) = ⊤ ∧ Module.Free R B ∧ Module.Finite R B ∧ finrank R B = finrank R A := by
  obtain ⟨hli, hsp⟩ := hi _ (Module.finBasis R A)
  let c : Basis _ R B := Basis.mk hli hsp.ge
  refine ⟨?_, Module.Free.of_basis c, Module.Finite.of_basis c, ?_⟩
  · rw [eq_top_iff, ← hsp]
    exact span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩)
  · rw [finrank_eq_card_basis c, Fintype.card_fin]

end Twist

/- English proof (translation)
Introduce `p hp R _ _ _ σ hσ D D₁ E E₁ _ _ _ _ _ _ _ _ _ _ _ _ W U i j F V F' V' φ φ₁ hW _ hi hj kF rV kV kF' rV' kV' hφ₁ hF hV hUW hinj htors`. Take `⟨hiT, _, _, hD₁⟩` from `span_image_top i hi`. Take `⟨hjT, _, _, -⟩` from `span_image_top j hj`. Use `set W₁ := span R (i '' (W : Set D)) with hW₁`. Use `set U₁ := span R (j '' (U : Set E)) with hU₁`.

Establish `hσ0 : ∀ r : R, r ≠ 0 → σ r ≠ 0` using `fun r hr => by rw [hσ]; exact pow_ne_zero _ hr`. Establish `hmap : ∀ P : Submodule R E, span R (i '' (P.map φ : Set D)) = (span R (j '' (P : Set E))).map φ₁`. Introduce `P`. Rewrite using `[Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]`. Simplify using `only [hφ₁]`.

Establish `e1 : span R (i '' (U.map φ : Set D)) = U₁.map φ₁` using `hmap U`. Establish `e2 : span R (i '' (LinearMap.range φ ⊔ W : Submodule R D)) = LinearMap.range φ₁ ⊔ W₁`. Establish `h1 : (LinearMap.range φ ⊔ W : Submodule R D) = span R ((LinearMap.range φ : Set D) ∪ (W : Set D))`. Rewrite using `[span_union, span_eq, span_eq]`. Rewrite using `[h1, span_image_span, Set.image_union, span_union, LinearMap.range_eq_map, hmap ⊤, Submodule.top_coe, Set.image_univ, hjT, ← LinearMap.range_eq_map]`.

Take `⟨ra, la, fa⟩` from `twist hσ i hi (U.map φ)`. Take `⟨-, lb, fb⟩` from `twist hσ i hi (LinearMap.range φ ⊔ W)`. Establish `rW : finrank R W₁ = finrank R W` using `(twist hσ i hi W).1`. Establish `rU : finrank R U₁ = finrank R U` using `(twist hσ j hj U).1`. Rewrite `ra`, `la` using `[e1]`.

Rewrite `lb` using `[e2]`. Establish `rφU : finrank R (U.map φ) = finrank R U`. Establish `h1` using `finrank_map_add φ U`. Establish `h2 : U ⊓ LinearMap.ker φ = ⊥` using `eq_bot_iff.2 fun x hx => hinj x hx.1 hx.2`. Rewrite `h1` using `[h2, finrank_bot]`.

Conclude with `h1`. Establish `hinj₁ : ∀ x ∈ U₁, φ₁ x = 0 → x = 0`. Establish `h1` using `finrank_map_add φ₁ U₁`. Establish `h2 : finrank R (U₁ ⊓ LinearMap.ker φ₁ : Submodule R E₁) = 0` using `by omega`. Rewrite `h2` using `[Module.finrank_zero_iff]`.

Introduce `x hx h0`. Conclude with `congrArg Subtype.val (h2.elim (⟨x, hx, h0⟩ : (U₁ ⊓ LinearMap.ker φ₁ : Submodule R E₁)) 0)`. Establish `hVφ : ∀ x, V (φ x) ∈ U₁.map φ₁` using `fun x => ⟨V' x, rV' ▸ LinearMap.mem_range_self V' x, hV x⟩`. Establish `rF : finrank R (LinearMap.range F) + finrank R W = finrank R D`. Establish `h1` using `finrank_map_add F ⊤`.

Rewrite `h1` using `[top_inf_eq, kF, finrank_top, ← LinearMap.range_eq_map]`. Use linear arithmetic over natural numbers and integers. Establish `rφ : finrank R (LinearMap.range φ) ≤ finrank R U + finrank R (LinearMap.range F)`. Establish `h1` using `finrank_map_add V (LinearMap.range φ)`. Establish `h2 : finrank R ((LinearMap.range φ).map V) ≤ finrank R (U₁.map φ₁)` using `Submodule.finrank_mono (by rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩; exact hVφ x)`.

Establish `h3 : finrank R (LinearMap.range φ ⊓ LinearMap.ker V : Submodule R D) ≤ finrank R (LinearMap.range F)` using `Submodule.finrank_mono (kV ▸ inf_le_right)`. Use linear arithmetic over natural numbers and integers. Establish `hkt : ∀ x ∈ LinearMap.range φ ⊓ W, ∃ r : R, r ≠ 0 ∧ r • x ∈ U.map φ`. Use `exists_smul_mem_of_finrank_le ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `⟨⟨x, rfl⟩, hUW x hx⟩`. Establish `h1` using `finrank_sup_add_inf (LinearMap.range φ) W`. Establish `h2` using `finrank_eq_of_smul_mem _ htors`. Use linear arithmetic over natural numbers and integers. Establish `hup` using `torsLen_le (R := R) (Submodule.factor (LinearMap.map_le_range : U.map φ ≤ LinearMap.range φ)) (Submodule.factor (le_sup_left : LinearMap.range φ ≤ LinearMap.range φ ⊔ W)) (by`.

Introduce `b hb hb0`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`. Take `⟨r, hr, hrx⟩` from `(mk_mem_torsion _ _).1 hb`. Establish `hx : x ∈ LinearMap.range φ ⊔ W` using `(Submodule.Quotient.mk_eq_zero _).1 hb0`. Take `⟨y, hy, w, hw, rfl⟩` from `Submodule.mem_sup.1 hx`.

Establish `h1 : r • w ∈ LinearMap.range φ ⊓ W`. Use `⟨?_, W.smul_mem r hw⟩` and prove the remaining obligations. Rewrite `hrx` using `[smul_add]`. Conclude with `(Submodule.add_mem_iff_right _ (Submodule.smul_mem _ r hy)).1 hrx`. Take `⟨s, hs, hsw⟩` from `hkt _ h1`.

Use `⟨Submodule.Quotient.mk w, (mk_mem_torsion _ _).2 ⟨s * r, mul_ne_zero hs hr, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]` and apply the resulting hypothesis. Use `(Submodule.Quotient.eq _).2 ?_` and prove the remaining obligations. Simplify using `using hy)`. Establish `hle1 : LinearMap.range φ₁ ⊔ W₁ ≤ (LinearMap.range φ).comap F`.

Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨F' x, hF x⟩`. Introduce `x hx`. Establish `: F x = 0` using `by rw [← LinearMap.mem_ker, kF]; exact hx`.

Rewrite using `[Submodule.mem_comap, this]`. Conclude with `zero_mem _`. Establish `hle2 : LinearMap.range φ ≤ (U₁.map φ₁).comap V`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hVφ x`.

Establish `hVF : ∀ x, V (F x) = 0` using `fun x => by`. Rewrite using `[← LinearMap.mem_ker, kV]`. Conclude with `⟨x, rfl⟩`. Establish `hlo` using `torsLen_eq (R := R) (Submodule.mapQ _ _ F hle1) (Submodule.mapQ _ _ V hle2) (by`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`.

Introduce `a ha`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Take `⟨e, he⟩ : F x ∈ LinearMap.range φ` from `(Submodule.Quotient.mk_eq_zero _).1 ha`. Establish `h1 : V' e = 0` using `hinj₁ _ (rV' ▸ LinearMap.mem_range_self V' e) (by rw [hV, he, hVF])`. Take `⟨e', rfl⟩ : e ∈ LinearMap.range F'` from `kV' ▸ h1`.

Use `(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_sup.2 ⟨φ₁ e', ⟨e', rfl⟩, x - φ₁ e', ?_, by abel⟩)` and prove the remaining obligations. Rewrite using `[← kF, LinearMap.mem_ker, map_sub, ← hF, he, sub_self])`. Use the proof step `(by`. Use extensionality with `b`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`.

Prove the components needed by the constructor for the conclusion. Introduce `hb`. Take `⟨u, hu, hux⟩ : V x ∈ U₁.map φ₁` from `(Submodule.Quotient.mk_eq_zero _).1 hb`. Take `⟨e, rfl⟩ : u ∈ LinearMap.range V'` from `rV' ▸ hu`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : x - φ e ∈ LinearMap.range F := by`.

Rewrite using `[← kV, LinearMap.mem_ker, map_sub, ← hV, hux, sub_self]`. Use `⟨Submodule.Quotient.mk y, (Submodule.Quotient.eq _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[hy]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨a, ha⟩`.

Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Rewrite using `[← ha]`. Use `(Submodule.Quotient.mk_eq_zero _).2 ?_` and prove the remaining obligations. Rewrite using `[hVF]`. Conclude with `zero_mem _)`.

Use the proof step `(by`. Introduce `a`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Establish `hx : x ∈ span R (Set.range i)` using `hiT ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨y, rfl⟩` from `hx`. Take `⟨r, hr, hry⟩` from `htors y`. Use `(mk_mem_torsion _ _).2 ⟨σ r, hσ0 r hr, ?_⟩` and prove the remaining obligations. Rewrite using `[← e2, ← LinearMap.map_smulₛₗ]`.

Conclude with `subset_span ⟨_, hry, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [Submodule.Quotient.mk_add]`. Conclude with `add_mem hx hy`. Consider the case `smul r x _ hx => rw [Submodule.Quotient.mk_smul]`.

Conclude with `smul_mem _ _ hx)`. Use the proof step `(by`. Introduce `c hc`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Take `⟨r, hr, hrx⟩` from `(mk_mem_torsion _ _).1 hc`.

Establish `h1 : U₁.map φ₁ ≤ W₁`. Rewrite using `[← e1]`. Use `span_mono (Set.image_mono ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `hUW u hu`.

Establish `h2 : r • F x = 0`. Rewrite using `[← map_smul, ← LinearMap.mem_ker, kF]`. Conclude with `h1 hrx`. Establish `h3 : x ∈ LinearMap.range V`. Rewrite using `[rV, ← kF]`.

Conclude with `(smul_eq_zero.1 h2).resolve_left hr`. Take `⟨y, rfl⟩` from `h3`. Conclude with `⟨Submodule.Quotient.mk y, rfl⟩)`. Rewrite `hup` using `[hlo, la, lb]`. Take `⟨c, hc⟩` from `ENat.ne_top_iff_exists.1 fa`.

Take `⟨c', hc'⟩` from `ENat.ne_top_iff_exists.1 fb`. Rewrite `hup` using `[← hc, ← hc', nsmul_eq_mul, nsmul_eq_mul]`. Establish `hup' : p * c' + p * c ≤ c + c'` using `by exact_mod_cast hup`. Establish `h2` using `hp.out.two_le`. Establish `hc0 : c = 0` using `by nlinarith`.

Establish `hc0' : c' = 0` using `by nlinarith`. Rewrite `hc` using `[hc0, Nat.cast_zero, eq_comm, Module.length_eq_zero_iff]`. Rewrite `hc'` using `[hc0', Nat.cast_zero, eq_comm, Module.length_eq_zero_iff]`. Use `⟨fun r w hr _ hrw => ?_, eq_top_iff.2 fun x _ => ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val (hc.elim ⟨_, (mk_mem_torsion _ w).2 ⟨r, hr, hrw⟩⟩ 0))`.

Conclude with `(Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val (hc'.elim ⟨_, (mk_mem_torsion _ x).2 (htors x)⟩ 0))`.
-/
theorem saturated_and_surjective : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (σ : R →+* R), (∀ r, σ r = r ^ p) → ∀ (D D₁ E E₁ : Type) [AddCommGroup D] [Module R D] [AddCommGroup D₁] [Module R D₁] [AddCommGroup E] [Module R E] [AddCommGroup E₁] [Module R E₁] [Module.Free R D] [Module.Finite R D] [Module.Free R E] [Module.Finite R E] (W : Submodule R D) (U : Submodule R E) (i : D →ₛₗ[σ] D₁) (j : E →ₛₗ[σ] E₁) (F : D₁ →ₗ[R] D) (V : D →ₗ[R] D₁) (F' : E₁ →ₗ[R] E) (V' : E →ₗ[R] E₁) (φ : E →ₗ[R] D) (φ₁ : E₁ →ₗ[R] D₁), (∀ (r : R) (x : D), r ≠ 0 → r • x ∈ W → x ∈ W) → (∀ (r : R) (x : E), r ≠ 0 → r • x ∈ U → x ∈ U) → (∀ (n : ℕ) (b : Module.Basis (Fin n) R D), LinearIndependent R (fun k => i (b k)) ∧ Submodule.span R (Set.range fun k => i (b k)) = ⊤) → (∀ (n : ℕ) (b : Module.Basis (Fin n) R E), LinearIndependent R (fun k => j (b k)) ∧ Submodule.span R (Set.range fun k => j (b k)) = ⊤) → LinearMap.ker F = Submodule.span R (i '' (W : Set D)) → LinearMap.range V = Submodule.span R (i '' (W : Set D)) → LinearMap.ker V = LinearMap.range F → LinearMap.ker F' = Submodule.span R (j '' (U : Set E)) → LinearMap.range V' = Submodule.span R (j '' (U : Set E)) → LinearMap.ker V' = LinearMap.range F' → (∀ x, φ₁ (j x) = i (φ x)) → (∀ x, φ (F' x) = F (φ₁ x)) → (∀ x, φ₁ (V' x) = V (φ x)) → (∀ x ∈ U, φ x ∈ W) → (∀ x ∈ U, φ x = 0 → x = 0) → (∀ x : D, ∃ r : R, r ≠ 0 ∧ r • x ∈ LinearMap.range φ ⊔ W) → (∀ (r : R) (w : D), r ≠ 0 → w ∈ W → r • w ∈ U.map φ → w ∈ U.map φ) ∧ LinearMap.range φ ⊔ W = ⊤ := by
  intro p hp R _ _ _ σ hσ D D₁ E E₁ _ _ _ _ _ _ _ _ _ _ _ _ W U i j F V F' V' φ φ₁ hW _ hi hj
    kF rV kV kF' rV' kV' hφ₁ hF hV hUW hinj htors
  obtain ⟨hiT, _, _, hD₁⟩ := span_image_top i hi
  obtain ⟨hjT, _, _, -⟩ := span_image_top j hj
  set W₁ := span R (i '' (W : Set D)) with hW₁
  set U₁ := span R (j '' (U : Set E)) with hU₁
  have hσ0 : ∀ r : R, r ≠ 0 → σ r ≠ 0 := fun r hr => by rw [hσ]; exact pow_ne_zero _ hr
  have hmap : ∀ P : Submodule R E, span R (i '' (P.map φ : Set D)) =
      (span R (j '' (P : Set E))).map φ₁ := by
    intro P
    rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    simp only [hφ₁]
  have e1 : span R (i '' (U.map φ : Set D)) = U₁.map φ₁ := hmap U
  have e2 : span R (i '' (LinearMap.range φ ⊔ W : Submodule R D)) =
      LinearMap.range φ₁ ⊔ W₁ := by
    have h1 : (LinearMap.range φ ⊔ W : Submodule R D) =
        span R ((LinearMap.range φ : Set D) ∪ (W : Set D)) := by
      rw [span_union, span_eq, span_eq]
    rw [h1, span_image_span, Set.image_union, span_union, LinearMap.range_eq_map, hmap ⊤,
      Submodule.top_coe, Set.image_univ, hjT, ← LinearMap.range_eq_map]
  obtain ⟨ra, la, fa⟩ := twist hσ i hi (U.map φ)
  obtain ⟨-, lb, fb⟩ := twist hσ i hi (LinearMap.range φ ⊔ W)
  have rW : finrank R W₁ = finrank R W := (twist hσ i hi W).1
  have rU : finrank R U₁ = finrank R U := (twist hσ j hj U).1
  rw [e1] at ra la
  rw [e2] at lb

  have rφU : finrank R (U.map φ) = finrank R U := by
    have h1 := finrank_map_add φ U
    have h2 : U ⊓ LinearMap.ker φ = ⊥ := eq_bot_iff.2 fun x hx => hinj x hx.1 hx.2
    rw [h2, finrank_bot] at h1
    exact h1
  have hinj₁ : ∀ x ∈ U₁, φ₁ x = 0 → x = 0 := by
    have h1 := finrank_map_add φ₁ U₁
    have h2 : finrank R (U₁ ⊓ LinearMap.ker φ₁ : Submodule R E₁) = 0 := by omega
    rw [Module.finrank_zero_iff] at h2
    intro x hx h0
    exact congrArg Subtype.val
      (h2.elim (⟨x, hx, h0⟩ : (U₁ ⊓ LinearMap.ker φ₁ : Submodule R E₁)) 0)
  have hVφ : ∀ x, V (φ x) ∈ U₁.map φ₁ := fun x =>
    ⟨V' x, rV' ▸ LinearMap.mem_range_self V' x, hV x⟩
  have rF : finrank R (LinearMap.range F) + finrank R W = finrank R D := by
    have h1 := finrank_map_add F ⊤
    rw [top_inf_eq, kF, finrank_top, ← LinearMap.range_eq_map] at h1
    omega
  have rφ : finrank R (LinearMap.range φ) ≤ finrank R U + finrank R (LinearMap.range F) := by
    have h1 := finrank_map_add V (LinearMap.range φ)
    have h2 : finrank R ((LinearMap.range φ).map V) ≤ finrank R (U₁.map φ₁) :=
      Submodule.finrank_mono (by rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩; exact hVφ x)
    have h3 : finrank R (LinearMap.range φ ⊓ LinearMap.ker V : Submodule R D) ≤
        finrank R (LinearMap.range F) := Submodule.finrank_mono (kV ▸ inf_le_right)
    omega
  have hkt : ∀ x ∈ LinearMap.range φ ⊓ W, ∃ r : R, r ≠ 0 ∧ r • x ∈ U.map φ := by
    refine exists_smul_mem_of_finrank_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, hUW x hx⟩
    · have h1 := finrank_sup_add_inf (LinearMap.range φ) W
      have h2 := finrank_eq_of_smul_mem _ htors
      omega

  have hup := torsLen_le (R := R)
    (Submodule.factor (LinearMap.map_le_range : U.map φ ≤ LinearMap.range φ))
    (Submodule.factor (le_sup_left : LinearMap.range φ ≤ LinearMap.range φ ⊔ W)) (by
      intro b hb hb0
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      obtain ⟨r, hr, hrx⟩ := (mk_mem_torsion _ _).1 hb
      have hx : x ∈ LinearMap.range φ ⊔ W := (Submodule.Quotient.mk_eq_zero _).1 hb0
      obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      have h1 : r • w ∈ LinearMap.range φ ⊓ W := by
        refine ⟨?_, W.smul_mem r hw⟩
        rw [smul_add] at hrx
        exact (Submodule.add_mem_iff_right _ (Submodule.smul_mem _ r hy)).1 hrx
      obtain ⟨s, hs, hsw⟩ := hkt _ h1
      refine ⟨Submodule.Quotient.mk w, (mk_mem_torsion _ _).2 ⟨s * r, mul_ne_zero hs hr, ?_⟩, ?_⟩
      · rwa [mul_smul]
      · refine (Submodule.Quotient.eq _).2 ?_
        simpa using hy)

  have hle1 : LinearMap.range φ₁ ⊔ W₁ ≤ (LinearMap.range φ).comap F := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨F' x, hF x⟩
    · intro x hx
      have : F x = 0 := by rw [← LinearMap.mem_ker, kF]; exact hx
      rw [Submodule.mem_comap, this]
      exact zero_mem _
  have hle2 : LinearMap.range φ ≤ (U₁.map φ₁).comap V := by
    rintro _ ⟨x, rfl⟩
    exact hVφ x
  have hVF : ∀ x, V (F x) = 0 := fun x => by
    rw [← LinearMap.mem_ker, kV]; exact ⟨x, rfl⟩
  have hlo := torsLen_eq (R := R) (Submodule.mapQ _ _ F hle1) (Submodule.mapQ _ _ V hle2)
    (by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro a ha
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨e, he⟩ : F x ∈ LinearMap.range φ := (Submodule.Quotient.mk_eq_zero _).1 ha
      have h1 : V' e = 0 := hinj₁ _ (rV' ▸ LinearMap.mem_range_self V' e) (by rw [hV, he, hVF])
      obtain ⟨e', rfl⟩ : e ∈ LinearMap.range F' := kV' ▸ h1
      refine (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.mem_sup.2 ⟨φ₁ e', ⟨e', rfl⟩, x - φ₁ e', ?_, by abel⟩)
      rw [← kF, LinearMap.mem_ker, map_sub, ← hF, he, sub_self])
    (by
      ext b
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      constructor
      · intro hb
        obtain ⟨u, hu, hux⟩ : V x ∈ U₁.map φ₁ := (Submodule.Quotient.mk_eq_zero _).1 hb
        obtain ⟨e, rfl⟩ : u ∈ LinearMap.range V' := rV' ▸ hu
        obtain ⟨y, hy⟩ : x - φ e ∈ LinearMap.range F := by
          rw [← kV, LinearMap.mem_ker, map_sub, ← hV, hux, sub_self]
        refine ⟨Submodule.Quotient.mk y, (Submodule.Quotient.eq _).2 ?_⟩
        rw [hy]
        simp
      · rintro ⟨a, ha⟩
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ a
        rw [← ha]
        refine (Submodule.Quotient.mk_eq_zero _).2 ?_
        rw [hVF]
        exact zero_mem _)
    (by
      intro a
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      have hx : x ∈ span R (Set.range i) := hiT ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        obtain ⟨r, hr, hry⟩ := htors y
        refine (mk_mem_torsion _ _).2 ⟨σ r, hσ0 r hr, ?_⟩
        rw [← e2, ← LinearMap.map_smulₛₗ]
        exact subset_span ⟨_, hry, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [Submodule.Quotient.mk_add]; exact add_mem hx hy
      | smul r x _ hx => rw [Submodule.Quotient.mk_smul]; exact smul_mem _ _ hx)
    (by
      intro c hc
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      obtain ⟨r, hr, hrx⟩ := (mk_mem_torsion _ _).1 hc
      have h1 : U₁.map φ₁ ≤ W₁ := by
        rw [← e1]
        refine span_mono (Set.image_mono ?_)
        rintro _ ⟨u, hu, rfl⟩
        exact hUW u hu
      have h2 : r • F x = 0 := by
        rw [← map_smul, ← LinearMap.mem_ker, kF]; exact h1 hrx
      have h3 : x ∈ LinearMap.range V := by
        rw [rV, ← kF]; exact (smul_eq_zero.1 h2).resolve_left hr
      obtain ⟨y, rfl⟩ := h3
      exact ⟨Submodule.Quotient.mk y, rfl⟩)
  rw [hlo, la, lb] at hup
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 fa
  obtain ⟨c', hc'⟩ := ENat.ne_top_iff_exists.1 fb
  rw [← hc, ← hc', nsmul_eq_mul, nsmul_eq_mul] at hup
  have hup' : p * c' + p * c ≤ c + c' := by exact_mod_cast hup
  have h2 := hp.out.two_le
  have hc0 : c = 0 := by nlinarith
  have hc0' : c' = 0 := by nlinarith
  rw [hc0, Nat.cast_zero, eq_comm, Module.length_eq_zero_iff] at hc
  rw [hc0', Nat.cast_zero, eq_comm, Module.length_eq_zero_iff] at hc'
  refine ⟨fun r w hr _ hrw => ?_, eq_top_iff.2 fun x _ => ?_⟩
  · exact (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val
      (hc.elim ⟨_, (mk_mem_torsion _ w).2 ⟨r, hr, hrw⟩⟩ 0))
  · exact (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val
      (hc'.elim ⟨_, (mk_mem_torsion _ x).2 (htors x)⟩ 0))

end GlobalTheory.HodgeConjLength
