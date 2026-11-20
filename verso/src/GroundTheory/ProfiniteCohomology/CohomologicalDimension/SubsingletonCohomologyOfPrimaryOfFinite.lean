import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.PrimaryComponentCohomologyEqBotOfScdpLt
import GroundTheory.ProfiniteCohomology.CoinducedModules.CohomologyCoindCokernelIsoHom
import GroundTheory.ProfiniteCohomology.ColimitUnion
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module

section General

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Use extensionality with `n c : 3`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression.
-/
theorem cochainsMap_add {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] (f g : A ⟶ B) :
    cochainsMap (f + g) = cochainsMap f + cochainsMap g := by
  ext n c : 3
  apply Subtype.ext
  funext x
  rfl

/- English proof (translation)
Rewrite using `[cohomologyMap, cochainsMap_add]`. Conclude with `HomologicalComplex.homologyMap_add _ _ _`.
-/
theorem cohomologyMap_add {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] (f g : A ⟶ B)
    (n : ℕ) : cohomologyMap (f + g) n = cohomologyMap f n + cohomologyMap g n := by
  rw [cohomologyMap, cochainsMap_add]
  exact HomologicalComplex.homologyMap_add _ _ _

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [cohomologyMap_zero]`. Consider the case `succ m ih => rw [succ_nsmul, succ_nsmul, cohomologyMap_add, ih]`.
-/
theorem cohomologyMap_nsmul {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] (m : ℕ)
    (f : A ⟶ B) (n : ℕ) : cohomologyMap (m • f) n = m • cohomologyMap f n := by
  induction m with
  | zero => simp [cohomologyMap_zero]
  | succ m ih => rw [succ_nsmul, succ_nsmul, cohomologyMap_add, ih]

/- English proof (translation)
Rewrite using `[cohomologyMap_nsmul, cohomologyMap_id]`. Both sides reduce to the same expression.
-/
theorem cohomologyMap_nsmul_id_apply (A : Rep.{u} k G) [IsDiscreteRep A] (m : ℕ) (n : ℕ)
    (x : cohomology A n) : (cohomologyMap (m • 𝟙 A) n).hom x = m • x := by
  rw [cohomologyMap_nsmul, cohomologyMap_id]
  rfl

/- English proof (translation)
Establish `h0 : m • 𝟙 A = 0`. Use extensionality with `a`. Conclude with `hm a`. Rewrite using `[← cohomologyMap_nsmul_id_apply, h0, cohomologyMap_zero]`. Both sides reduce to the same expression.
-/
theorem nsmul_cohomology_eq_zero (A : Rep.{u} k G) [IsDiscreteRep A] {m : ℕ}
    (hm : ∀ a : A, m • a = 0) (n : ℕ) (x : cohomology A n) : m • x = 0 := by
  have h0 : m • 𝟙 A = 0 := by
    ext a
    exact hm a
  rw [← cohomologyMap_nsmul_id_apply, h0, cohomologyMap_zero]
  rfl

/- English proof (translation)
Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Establish `h` using `nsmul_cohomology_eq_zero A (m := 1) (fun a => Subsingleton.elim _ _) n`. Rewrite using `[← one_nsmul x, ← one_nsmul y, h, h]`.
-/
theorem subsingleton_cohomology_of_subsingleton (A : Rep.{u} k G) [IsDiscreteRep A]
    [Subsingleton A] (n : ℕ) : Subsingleton (cohomology A n) := by
  refine ⟨fun x y => ?_⟩
  have h := nsmul_cohomology_eq_zero A (m := 1) (fun a => Subsingleton.elim _ _) n
  rw [← one_nsmul x, ← one_nsmul y, h, h]

/- English proof (translation)
It suffices to establish `h : ∀ x : cohomology S.X₂ n, x = 0 from ⟨fun x y => by rw [h x, h y]⟩`. Introduce `x`. Take `⟨z, hz⟩` from `(ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS n) x (Subsingleton.elim _ _)`. Rewrite using `[← hz, Subsingleton.elim z 0]`. Conclude with `map_zero _`.
-/
theorem subsingleton_cohomology_X₂ {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (n : ℕ)
    (h₁ : Subsingleton (cohomology S.X₁ n)) (h₃ : Subsingleton (cohomology S.X₃ n)) :
    Subsingleton (cohomology S.X₂ n) := by
  suffices h : ∀ x : cohomology S.X₂ n, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS n) x
    (Subsingleton.elim _ _)
  rw [← hz, Subsingleton.elim z 0]
  exact map_zero _

noncomputable def subQuotShortComplex (A : Rep.{u} k G) (W : Submodule k A)
    (h : ∀ g, W ≤ W.comap (A.ρ g)) : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (Rep.subtype A W h) (Rep.mkQ A W h) (by
    ext w
    exact (Submodule.Quotient.mk_eq_zero _).2 w.2)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/- English proof (translation)
Rewrite using `[← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)), ShortComplex.moduleCat_exact_iff]`. Introduce `a ha`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (p := W) a = 0 at ha`. Conclude with `⟨⟨a, (Submodule.Quotient.mk_eq_zero _).1 ha⟩, rfl⟩`. Use `mono_f := (Rep.mono_iff_injective _).2 Subtype.val_injective`.

Use `epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)`.
-/
theorem subQuotShortComplex_shortExact (A : Rep.{u} k G) (W : Submodule k A)
    (h : ∀ g, W ≤ W.comap (A.ρ g)) : (subQuotShortComplex A W h).ShortExact where
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    intro a ha
    change Submodule.Quotient.mk (p := W) a = 0 at ha
    exact ⟨⟨a, (Submodule.Quotient.mk_eq_zero _).1 ha⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 Subtype.val_injective
  epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

instance (A : Rep.{u} k G) [IsDiscreteRep A] (W : Submodule k A) (h : ∀ g, W ≤ W.comap (A.ρ g)) :
    IsDiscreteRep (subQuotShortComplex A W h).X₁ :=
  isDiscreteRep_subrepresentation A W h

instance (A : Rep.{u} k G) [IsDiscreteRep A] (W : Submodule k A) (h : ∀ g, W ≤ W.comap (A.ρ g)) :
    IsDiscreteRep (subQuotShortComplex A W h).X₂ :=
  (inferInstance : IsDiscreteRep A)

instance (A : Rep.{u} k G) [IsDiscreteRep A] (W : Submodule k A) (h : ∀ g, W ≤ W.comap (A.ρ g)) :
    IsDiscreteRep (subQuotShortComplex A W h).X₃ :=
  isDiscreteRep_quotient A W h

/- English proof (translation)
The claim follows from `subsingleton_cohomology_X₂ (subQuotShortComplex_shortExact A W h) n h₁ h₃`.
-/
theorem subsingleton_cohomology_of_sub_quot (A : Rep.{u} k G) [IsDiscreteRep A] (W : Submodule k A)
    (h : ∀ g, W ≤ W.comap (A.ρ g)) (n : ℕ)
    (h₁ : Subsingleton (cohomology (A.subrepresentation W h) n))
    (h₃ : Subsingleton (cohomology (A.quotient W h) n)) : Subsingleton (cohomology A n) :=
  subsingleton_cohomology_X₂ (subQuotShortComplex_shortExact A W h) n h₁ h₃

end General

section Integers

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Conclude with `⟨fun h x hx => (AddSubgroup.mem_bot).1 (h hx), fun h x hx => (AddSubgroup.mem_bot).2 (h x hx)⟩`.
-/
theorem primaryComponent_eq_bot_iff {M : Type*} [AddCommGroup M] {p : ℕ} :
    AddCommGroup.primaryComponent M p = ⊥ ↔ ∀ x : M, (∃ k : ℕ, p ^ k • x = 0) → x = 0 := by
  rw [eq_bot_iff]
  exact ⟨fun h x hx => (AddSubgroup.mem_bot).1 (h hx),
    fun h x hx => (AddSubgroup.mem_bot).2 (h x hx)⟩

/- English proof (translation)
Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le h`. Rewrite using `[pow_add, mul_comm, mul_smul, ha, smul_zero]`.
-/
theorem pow_nsmul_eq_zero_of_le {M : Type*} [AddCommMonoid M] {p k K : ℕ} {a : M} (h : k ≤ K)
    (ha : p ^ k • a = 0) : p ^ K • a = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_comm, mul_smul, ha, smul_zero]

/- English proof (translation)
Proceed by induction on `k generalizing x with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`. Apply `hp` to reduce the goal to its premises. Apply `ih` to reduce the goal to its premises.

Rewrite using `[← mul_smul, ← pow_succ]`. Conclude with `hx`.
-/
theorem eq_zero_of_pow_nsmul_eq_zero {M : Type*} [AddCommMonoid M] {p : ℕ}
    (hp : ∀ x : M, p • x = 0 → x = 0) (k : ℕ) (x : M) (hx : p ^ k • x = 0) : x = 0 := by
  induction k generalizing x with
  | zero => simpa using hx
  | succ k ih =>
    apply hp
    apply ih
    rw [← mul_smul, ← pow_succ]
    exact hx

/- English proof (translation)
Establish `hmono : Mono (p • 𝟙 A)` using `(Rep.mono_iff_injective _).2 hp.1`. Establish `hepi : Epi (p • 𝟙 A)` using `(Rep.epi_iff_surjective _).2 hp.2`. Establish `: IsIso (p • 𝟙 A)` using `isIso_of_mono_of_epi _`. Establish `key : ∀ z : cohomology A n, (cohomologyMap (inv (p • 𝟙 A)) n).hom (p • z) = z`. Introduce `z`.

Rewrite using `[← cohomologyMap_nsmul_id_apply]`. Express the relevant statement in the definitionally equal form `(cohomologyMap (p • 𝟙 A) n ≫ cohomologyMap (inv (p • 𝟙 A)) n).hom z = z`. Rewrite using `[← cohomologyMap_comp, IsIso.hom_inv_id, cohomologyMap_id]`. Both sides reduce to the same expression. Rewrite using `[primaryComponent_eq_bot_iff]`.

Introduce and unpack `x ⟨k, hk⟩`. Use `eq_zero_of_pow_nsmul_eq_zero (fun y hy => ?_) k x hk` and prove the remaining obligations. Rewrite using `[← key y, hy, map_zero]`.
-/
theorem primaryComponent_cohomology_eq_bot_of_bijective (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep A] {p : ℕ} (hp : Function.Bijective fun a : A => p • a) (n : ℕ) :
    AddCommGroup.primaryComponent (cohomology A n) p = ⊥ := by
  have hmono : Mono (p • 𝟙 A) := (Rep.mono_iff_injective _).2 hp.1
  have hepi : Epi (p • 𝟙 A) := (Rep.epi_iff_surjective _).2 hp.2
  have : IsIso (p • 𝟙 A) := isIso_of_mono_of_epi _
  have key : ∀ z : cohomology A n, (cohomologyMap (inv (p • 𝟙 A)) n).hom (p • z) = z := by
    intro z
    rw [← cohomologyMap_nsmul_id_apply]
    change (cohomologyMap (p • 𝟙 A) n ≫ cohomologyMap (inv (p • 𝟙 A)) n).hom z = z
    rw [← cohomologyMap_comp, IsIso.hom_inv_id, cohomologyMap_id]
    rfl
  rw [primaryComponent_eq_bot_iff]
  rintro x ⟨k, hk⟩
  refine eq_zero_of_pow_nsmul_eq_zero (fun y hy => ?_) k x hk
  rw [← key y, hy, map_zero]

/- English proof (translation)
Rewrite using `[primaryComponent_eq_bot_iff]`. Establish `h1 : ∀ x : cohomology A n, ∃ k : ℕ, p ^ k • x = 0` using `fun x => ⟨1, by rw [pow_one]; exact nsmul_cohomology_eq_zero A hA n x⟩`. Conclude with `⟨fun h => ⟨fun x y => by rw [h x (h1 x), h y (h1 y)]⟩, fun h x _ => Subsingleton.elim _ _⟩`.
-/
theorem primaryComponent_cohomology_eq_bot_iff_of_nsmul (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep A] {p : ℕ} (hA : ∀ a : A, p • a = 0) (n : ℕ) :
    AddCommGroup.primaryComponent (cohomology A n) p = ⊥ ↔ Subsingleton (cohomology A n) := by
  rw [primaryComponent_eq_bot_iff]
  have h1 : ∀ x : cohomology A n, ∃ k : ℕ, p ^ k • x = 0 := fun x =>
    ⟨1, by rw [pow_one]; exact nsmul_cohomology_eq_zero A hA n x⟩
  exact ⟨fun h => ⟨fun x y => by rw [h x (h1 x), h y (h1 y)]⟩,
    fun h x _ => Subsingleton.elim _ _⟩

section Primary

variable {k : Type u} [CommRing k]

omit [IsTopologicalGroup G] in

def primarySubmodule (A : Rep.{u} k G) (p : ℕ) : Submodule k A where
  carrier := {a | ∃ k : ℕ, p ^ k • a = 0}
  add_mem' := fun {a b} ha hb => (AddCommGroup.primaryComponent A p).add_mem ha hb
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := fun r a ⟨k, hk⟩ => ⟨k, by rw [smul_comm, hk, smul_zero]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_primarySubmodule (A : Rep.{u} k G) (p : ℕ) (a : A) :
    a ∈ primarySubmodule A p ↔ ∃ k : ℕ, p ^ k • a = 0 :=
  Iff.rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/- English proof (translation)
Introduce `a ⟨k, hk⟩` and use `⟨k, by rw [← map_nsmul, hk, map_zero]⟩`.
-/
theorem primarySubmodule_le_comap (A : Rep.{u} k G) (p : ℕ) (g : G) :
    primarySubmodule A p ≤ (primarySubmodule A p).comap (A.ρ g) :=
  fun a ⟨k, hk⟩ => ⟨k, by rw [← map_nsmul, hk, map_zero]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in

/- English proof (translation)
Use `set W := primarySubmodule A p`. Prove the components needed by the constructor for the conclusion. Establish `hker : ∀ x : A ⧸ W, p • x = 0 → x = 0`. Introduce `x hx`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Rewrite `hx` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨k, hk⟩` from `hx`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨k + 1, by rw [pow_succ, mul_smul]; exact hk⟩`. Introduce `x y hxy`.

Rewrite using `[← sub_eq_zero]`. Apply `hker` to reduce the goal to its premises. Simplify using `only at hxy`. Rewrite using `[smul_sub, hxy, sub_self]`. Introduce `x`.

Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨m, hm0, hma⟩` from `isOfFinAddOrder_iff_nsmul_eq_zero.1 (hA a)`. Take `⟨e, m', hm', rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' p hp.ne_one`. Establish `hm'0 : m' ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hm0`. Distinguish the cases in `h1 : m' = 1`. Substitute `h1` using the available equality. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_zero]`.

Use `symm`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 ⟨e, by simpa using hma⟩`. Establish `hcop : Nat.Coprime p m'` using `(Nat.Prime.coprime_iff_not_dvd hp).2 hm'`. Take `⟨v, -, hv⟩` from `Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)`. Use `⟨Submodule.Quotient.mk (v • a), ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]`. Use `⟨e, ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩ : ∃ j, p * v = m' * j + 1` from `⟨p * v / m', by`. Use `Nat.div_add_mod (p * v) m'` as an intermediate fact.

Use the proof step `omega⟩`. Establish `: p • v • a - a = (m' * j) • a`. Rewrite using `[← mul_smul, hj, add_smul, one_smul, add_sub_cancel_right]`. Rewrite using `[this, ← mul_smul, ← mul_assoc, mul_comm (p ^ e * m'), mul_smul, hma, smul_zero]`.
-/
theorem bijective_nsmul_quotient_primarySubmodule (A : Rep.{u} k G)
    (hA : IsAddTorsion A) {p : ℕ} (hp : p.Prime) :
    Function.Bijective fun x : A ⧸ primarySubmodule A p => p • x := by
  set W := primarySubmodule A p
  constructor
  · have hker : ∀ x : A ⧸ W, p • x = 0 → x = 0 := by
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨k, hk⟩ := hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨k + 1, by rw [pow_succ, mul_smul]; exact hk⟩
    intro x y hxy
    rw [← sub_eq_zero]
    apply hker
    simp only at hxy
    rw [smul_sub, hxy, sub_self]
  · intro x
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm0, hma⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hA a)
    obtain ⟨e, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' p hp.ne_one
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      simp at hm0
    by_cases h1 : m' = 1
    · subst h1
      refine ⟨0, ?_⟩
      simp only [smul_zero]
      symm
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨e, by simpa using hma⟩
    · have hcop : Nat.Coprime p m' := (Nat.Prime.coprime_iff_not_dvd hp).2 hm'
      obtain ⟨v, -, hv⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
      refine ⟨Submodule.Quotient.mk (v • a), ?_⟩
      simp only
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      refine ⟨e, ?_⟩
      obtain ⟨j, hj⟩ : ∃ j, p * v = m' * j + 1 := ⟨p * v / m', by
        have := Nat.div_add_mod (p * v) m'
        omega⟩
      have : p • v • a - a = (m' * j) • a := by
        rw [← mul_smul, hj, add_smul, one_smul, add_sub_cancel_right]
      rw [this, ← mul_smul, ← mul_assoc, mul_comm (p ^ e * m'), mul_smul, hma, smul_zero]

end Primary

/- English proof (translation)
Rewrite using `[cdp_le_iff]`. Introduce `A _ hA q hq`. Establish `hq' : n < q` using `by exact_mod_cast hq`. Establish `hW` using `primarySubmodule_le_comap A p`. Establish `hTp : ∀ a : A.subrepresentation (primarySubmodule A p) hW, ∃ k : ℕ, p ^ k • a = 0`.

Introduce and unpack `⟨a, k, hk⟩`. Conclude with `⟨k, Subtype.ext hk⟩`. Establish `hT` using `h (A.subrepresentation (primarySubmodule A p) hW) hTp q hq'`. Establish `hQ` using `primaryComponent_cohomology_eq_bot_of_bijective (A.quotient (primarySubmodule A p) hW) (p := p) (bijective_nsmul_quotient_primarySubmodule A hA hp) q`. Rewrite `hQ`, the goal using `[primaryComponent_eq_bot_iff]`.

Introduce and unpack `x ⟨k, hk⟩`. Establish `hx : (cohomologyMap (Rep.mkQ A (primarySubmodule A p) hW) q).hom x = 0` using `hQ _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩`. Take `⟨z, hz⟩` from `(ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ (subQuotShortComplex_shortExact A (primarySubmodule A p) hW) q) x hx`. Rewrite using `[← hz, @Subsingleton.elim _ hT z 0]`. Conclude with `map_zero _`.
-/
theorem cdp_le_of_forall_primary {p : ℕ} (hp : p.Prime) {n : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) →
      ∀ q : ℕ, n < q → Subsingleton (cohomology A q)) :
    cdp p G ≤ n := by
  rw [cdp_le_iff]
  intro A _ hA q hq
  have hq' : n < q := by exact_mod_cast hq
  have hW := primarySubmodule_le_comap A p
  have hTp : ∀ a : A.subrepresentation (primarySubmodule A p) hW, ∃ k : ℕ, p ^ k • a = 0 := by
    rintro ⟨a, k, hk⟩
    exact ⟨k, Subtype.ext hk⟩
  have hT := h (A.subrepresentation (primarySubmodule A p) hW) hTp q hq'
  have hQ := primaryComponent_cohomology_eq_bot_of_bijective
    (A.quotient (primarySubmodule A p) hW) (p := p)
    (bijective_nsmul_quotient_primarySubmodule A hA hp) q
  rw [primaryComponent_eq_bot_iff] at hQ ⊢
  rintro x ⟨k, hk⟩
  have hx : (cohomologyMap (Rep.mkQ A (primarySubmodule A p) hW) q).hom x = 0 :=
    hQ _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (cohomology_exact₂ (subQuotShortComplex_shortExact A (primarySubmodule A p) hW) q) x hx
  rw [← hz, @Subsingleton.elim _ hT z 0]
  exact map_zero _

/- English proof (translation)
The claim follows from `(primaryComponent_cohomology_eq_bot_iff_of_nsmul A hA q).1 (cdp_le_iff.1 h A (fun a => isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨p, hp.pos, hA a⟩) q (by exact_mod_cast hq))`.
-/
theorem subsingleton_cohomology_of_cdp_le {p : ℕ} (hp : p.Prime) {n : ℕ} (h : cdp p G ≤ n)
    (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] (hA : ∀ a : A, p • a = 0) {q : ℕ}
    (hq : n < q) : Subsingleton (cohomology A q) :=
  (primaryComponent_cohomology_eq_bot_iff_of_nsmul A hA q).1
    (cdp_le_iff.1 h A (fun a => isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨p, hp.pos, hA a⟩) q
      (by exact_mod_cast hq))

end Integers

section Devissage

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
It suffices to establish `H : ∀ N : ℕ, ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] [Finite A], (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → Nat.card A = N → Subsingleton (cohomology A m) from H _ A hA rfl`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `A _ _ hA hN`.

Break down `subsingleton_or_nontrivial A with hs | hnt` into its components or cases. Conclude with `subsingleton_cohomology_of_subsingleton A m`. Establish `: Nontrivial (Subrepresentation A.ρ)` using `⟨⟨⊥, ⊤, fun hbt => by`. Take `⟨a, ha⟩` from `exists_ne (0 : A)`. Establish `: a ∈ (⊤ : Subrepresentation A.ρ).toSubmodule` using `Submodule.mem_top`.

Rewrite `this` using `[← hbt]`. Conclude with `ha ((Submodule.mem_bot _).1 this)⟩⟩`. Distinguish the cases in `hsimple : IsSimpleOrder (Subrepresentation A.ρ)`. Apply `h A hsimple` to reduce the goal to its premises. Set `P : Subrepresentation A.ρ` to `{ toSubmodule := LinearMap.range (p • LinearMap.id : A →ₗ[ULift.{u} ℤ] A) apply_mem_toSubmodule := by`.

Introduce and unpack `g _ ⟨b, rfl⟩`. Conclude with `⟨A.ρ g b, by simp [map_nsmul]⟩ }`. Break down `hsimple.eq_bot_or_eq_top P with hP | hP` into its components or cases. Introduce `a`. Establish `: p • a ∈ P.toSubmodule` using `⟨a, by simp⟩`.

Rewrite `this` using `[hP]`. Conclude with `(Submodule.mem_bot _).1 this`. It suffices to derive a contradiction. Establish `hsurj : Function.Surjective fun a : A => p • a`. Introduce `a`.

Establish `: a ∈ (⊤ : Subrepresentation A.ρ).toSubmodule` using `Submodule.mem_top`. Rewrite `this` using `[← hP]`. Take `⟨b, hb⟩` from `this`. Conclude with `⟨b, by simpa using hb⟩`. Establish `hinj` using `Finite.injective_iff_surjective.2 hsurj`.

Take `⟨a, ha⟩` from `exists_ne (0 : A)`. Take `⟨k, hk⟩` from `hA a`. Conclude with `ha (eq_zero_of_pow_nsmul_eq_zero (fun x hx => hinj (hx.trans (smul_zero p).symm)) k a hk)`. Choose the witnesses or unpack the hypotheses as in `⟨W, hW0, hWT⟩ : ∃ W : Subrepresentation A.ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by`. Assume the negation of the conclusion as `hne`.

Use `push Not at hne`. Conclude with `hsimple { toNontrivial := inferInstance, eq_bot_or_eq_top := fun W => (em (W = ⊥)).imp id (hne W) }`. Establish `hst : ∀ g, W.toSubmodule ≤ W.toSubmodule.comap (A.ρ g)` using `fun g v hv => W.apply_mem_toSubmodule g hv`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : A, a ∉ W.toSubmodule := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Conclude with `hWT (Subrepresentation.ext (Submodule.eq_top_iff'.2 hc))`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw, hw0⟩ : ∃ w ∈ W.toSubmodule, w ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hW0 (Subrepresentation.ext ((Submodule.eq_bot_iff _).2 hc))`. Establish `hfinS : Finite (A.subrepresentation W.toSubmodule hst)` using `inferInstanceAs (Finite W.toSubmodule)`. Establish `hfinQ : Finite (A.quotient W.toSubmodule hst)` using `Finite.of_surjective _ (Submodule.mkQ_surjective W.toSubmodule)`. Establish `hcardS : Nat.card (A.subrepresentation W.toSubmodule hst) < N`. Rewrite using `[← hN]`.

Conclude with `Finite.card_subtype_lt ha`. Establish `hone : 1 < Nat.card (A.subrepresentation W.toSubmodule hst)`. Establish `: Nontrivial W.toSubmodule` using `⟨⟨⟨w, hw⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩`. Conclude with `Finite.one_lt_card_iff_nontrivial.2 this`. Establish `hc : Nat.card A = Nat.card (A.quotient W.toSubmodule hst) * Nat.card (A.subrepresentation W.toSubmodule hst)` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup W.toSubmodule.toAddSubgroup`.

Establish `hcardQ : Nat.card (A.quotient W.toSubmodule hst) < N`. Rewrite using `[← hN, hc]`. Conclude with `lt_mul_of_one_lt_right Nat.card_pos hone`. Apply `subsingleton_cohomology_of_sub_quot A W.toSubmodule hst m` to reduce the goal to its premises. Use `ih _ hcardS (A.subrepresentation W.toSubmodule hst) ?_ rfl` and prove the remaining obligations.

Introduce and unpack `⟨b, hb⟩`. Take `⟨k, hk⟩` from `hA b`. Conclude with `⟨k, Subtype.ext hk⟩`. Use `ih _ hcardQ (A.quotient W.toSubmodule hst) ?_ rfl` and prove the remaining obligations. Introduce `x`.

Take `⟨b, rfl⟩` from `Submodule.mkQ_surjective W.toSubmodule x`. Take `⟨k, hk⟩` from `hA b`. Conclude with `⟨k, by rw [← map_nsmul, hk, map_zero]⟩`.
-/
theorem subsingleton_cohomology_of_finite_of_simple {p : ℕ} {m : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], IsSimpleOrder (Subrepresentation A.ρ) →
      (∀ a : A, p • a = 0) → Subsingleton (cohomology A m))
    (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] [Finite A]
    (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) : Subsingleton (cohomology A m) := by
  suffices H : ∀ N : ℕ, ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] [Finite A],
      (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → Nat.card A = N → Subsingleton (cohomology A m) from
    H _ A hA rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A _ _ hA hN
  rcases subsingleton_or_nontrivial A with hs | hnt
  · exact subsingleton_cohomology_of_subsingleton A m
  have : Nontrivial (Subrepresentation A.ρ) := ⟨⟨⊥, ⊤, fun hbt => by
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    have : a ∈ (⊤ : Subrepresentation A.ρ).toSubmodule := Submodule.mem_top
    rw [← hbt] at this
    exact ha ((Submodule.mem_bot _).1 this)⟩⟩
  by_cases hsimple : IsSimpleOrder (Subrepresentation A.ρ)
  · apply h A hsimple
    let P : Subrepresentation A.ρ :=
      { toSubmodule := LinearMap.range (p • LinearMap.id : A →ₗ[ULift.{u} ℤ] A)
        apply_mem_toSubmodule := by
          rintro g _ ⟨b, rfl⟩
          exact ⟨A.ρ g b, by simp [map_nsmul]⟩ }
    rcases hsimple.eq_bot_or_eq_top P with hP | hP
    · intro a
      have : p • a ∈ P.toSubmodule := ⟨a, by simp⟩
      rw [hP] at this
      exact (Submodule.mem_bot _).1 this
    · exfalso
      have hsurj : Function.Surjective fun a : A => p • a := by
        intro a
        have : a ∈ (⊤ : Subrepresentation A.ρ).toSubmodule := Submodule.mem_top
        rw [← hP] at this
        obtain ⟨b, hb⟩ := this
        exact ⟨b, by simpa using hb⟩
      have hinj := Finite.injective_iff_surjective.2 hsurj
      obtain ⟨a, ha⟩ := exists_ne (0 : A)
      obtain ⟨k, hk⟩ := hA a
      exact ha (eq_zero_of_pow_nsmul_eq_zero (fun x hx => hinj (hx.trans (smul_zero p).symm)) k a hk)
  · obtain ⟨W, hW0, hWT⟩ : ∃ W : Subrepresentation A.ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra hne
      push Not at hne
      exact hsimple { toNontrivial := inferInstance,
                      eq_bot_or_eq_top := fun W => (em (W = ⊥)).imp id (hne W) }
    have hst : ∀ g, W.toSubmodule ≤ W.toSubmodule.comap (A.ρ g) :=
      fun g v hv => W.apply_mem_toSubmodule g hv
    obtain ⟨a, ha⟩ : ∃ a : A, a ∉ W.toSubmodule := by
      by_contra hc
      push Not at hc
      exact hWT (Subrepresentation.ext (Submodule.eq_top_iff'.2 hc))
    obtain ⟨w, hw, hw0⟩ : ∃ w ∈ W.toSubmodule, w ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hW0 (Subrepresentation.ext ((Submodule.eq_bot_iff _).2 hc))
    have hfinS : Finite (A.subrepresentation W.toSubmodule hst) :=
      inferInstanceAs (Finite W.toSubmodule)
    have hfinQ : Finite (A.quotient W.toSubmodule hst) :=
      Finite.of_surjective _ (Submodule.mkQ_surjective W.toSubmodule)
    have hcardS : Nat.card (A.subrepresentation W.toSubmodule hst) < N := by
      rw [← hN]
      exact Finite.card_subtype_lt ha
    have hone : 1 < Nat.card (A.subrepresentation W.toSubmodule hst) := by
      have : Nontrivial W.toSubmodule := ⟨⟨⟨w, hw⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
      exact Finite.one_lt_card_iff_nontrivial.2 this
    have hc : Nat.card A = Nat.card (A.quotient W.toSubmodule hst) *
        Nat.card (A.subrepresentation W.toSubmodule hst) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup W.toSubmodule.toAddSubgroup
    have hcardQ : Nat.card (A.quotient W.toSubmodule hst) < N := by
      rw [← hN, hc]
      exact lt_mul_of_one_lt_right Nat.card_pos hone
    apply subsingleton_cohomology_of_sub_quot A W.toSubmodule hst m
    · refine ih _ hcardS (A.subrepresentation W.toSubmodule hst) ?_ rfl
      rintro ⟨b, hb⟩
      obtain ⟨k, hk⟩ := hA b
      exact ⟨k, Subtype.ext hk⟩
    · refine ih _ hcardQ (A.quotient W.toSubmodule hst) ?_ rfl
      intro x
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective W.toSubmodule x
      obtain ⟨k, hk⟩ := hA b
      exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩

omit [IsTopologicalGroup G] in

/- English proof (translation)
Use `Finite.of_surjective (fun x : W₁ × W₂ => (⟨x.1 + x.2, Submodule.add_mem_sup x.1.2 x.2.2⟩ : ↥(W₁ ⊔ W₂))) ?_` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hy`. Conclude with `⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩`.
-/
theorem finite_sup_of_finite {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (W₁ W₂ : Submodule R M) [Finite W₁] [Finite W₂] : Finite ↥(W₁ ⊔ W₂) := by
  refine Finite.of_surjective
    (fun x : W₁ × W₂ => (⟨x.1 + x.2, Submodule.add_mem_sup x.1.2 x.2.2⟩ : ↥(W₁ ⊔ W₂))) ?_
  rintro ⟨y, hy⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

/- English proof (translation)
Set `O : Set A` to `Set.range fun g : G => A.ρ g a`. Establish `hO : O.Finite`. Use `Subgroup.quotient_finite_of_isOpen _ (isOpen_stabilizer A a)` as an intermediate fact. Use `(Set.finite_range fun q : G ⧸ stabilizer A.ρ a => A.ρ q.out a).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`.

Take `⟨s, hgs⟩` from `QuotientGroup.mk_out_eq_mul (stabilizer A.ρ a) g`. Use `⟨(g : G ⧸ stabilizer A.ρ a), ?_⟩` and prove the remaining obligations. Simplify using `only [hgs, map_mul, Module.End.mul_apply]`. Rewrite using `[(mem_stabilizer _ _ _).1 s.2]`. Use `⟨Submodule.span _ O, fun g => Submodule.span_le.2 ?_, ?_, Submodule.subset_span ⟨1, by simp⟩⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨h, rfl⟩ show A.ρ g (A.ρ h a) ∈ Submodule.span _ O`. Conclude with `Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩`. Establish `hsub : (Submodule.span (ULift.{u} ℤ) O : Set A) ⊆ AddSubgroup.closure O`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => exact AddSubgroup.subset_closure hx`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[SetLike.mem_coe, show r = ((r.down : ℤ) : ULift.{u} ℤ) by ext; simp, Int.cast_smul_eq_zsmul]`.

Conclude with `zsmul_mem hx r.down`. Establish `: Finite O` using `hO.to_subtype`. Establish `: Finite (AddSubgroup.closure O)` using `AddCommGroup.finite_of_fg_isAddTorsion (G := AddSubgroup.closure O) fun x => by`. Take `⟨k, hk⟩` from `hA x`. Conclude with `isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨p ^ k, pow_pos hp k, Subtype.ext hk⟩`.

Conclude with `((Set.toFinite (AddSubgroup.closure O : Set A)).subset hsub).to_subtype`.
-/
theorem exists_finite_stable_submodule [CompactSpace G] (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep A] {p : ℕ} (hp : 0 < p) (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) (a : A) :
    ∃ W : Submodule (ULift.{u} ℤ) A, (∀ g, W ≤ W.comap (A.ρ g)) ∧ Finite W ∧ a ∈ W := by
  let O : Set A := Set.range fun g : G => A.ρ g a
  have hO : O.Finite := by
    have := Subgroup.quotient_finite_of_isOpen _ (isOpen_stabilizer A a)
    refine (Set.finite_range fun q : G ⧸ stabilizer A.ρ a => A.ρ q.out a).subset ?_
    rintro _ ⟨g, rfl⟩
    obtain ⟨s, hgs⟩ := QuotientGroup.mk_out_eq_mul (stabilizer A.ρ a) g
    refine ⟨(g : G ⧸ stabilizer A.ρ a), ?_⟩
    simp only [hgs, map_mul, Module.End.mul_apply]
    rw [(mem_stabilizer _ _ _).1 s.2]
  refine ⟨Submodule.span _ O, fun g => Submodule.span_le.2 ?_, ?_, Submodule.subset_span ⟨1, by simp⟩⟩
  · rintro _ ⟨h, rfl⟩
    show A.ρ g (A.ρ h a) ∈ Submodule.span _ O
    exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
  · have hsub : (Submodule.span (ULift.{u} ℤ) O : Set A) ⊆ AddSubgroup.closure O := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact AddSubgroup.subset_closure hx
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul r x _ hx =>
        rw [SetLike.mem_coe, show r = ((r.down : ℤ) : ULift.{u} ℤ) by ext; simp,
          Int.cast_smul_eq_zsmul]
        exact zsmul_mem hx r.down
    have : Finite O := hO.to_subtype
    have : Finite (AddSubgroup.closure O) := AddCommGroup.finite_of_fg_isAddTorsion (G := AddSubgroup.closure O) fun x => by
      obtain ⟨k, hk⟩ := hA x
      exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨p ^ k, pow_pos hp k, Subtype.ext hk⟩
    exact ((Set.toFinite (AddSubgroup.closure O : Set A)).subset hsub).to_subtype

/- English proof (translation)
Set `ι` to `{W : Submodule (ULift.{u} ℤ) A // (∀ g, W ≤ W.comap (A.ρ g)) ∧ Finite W}`. Set `Wf : ι → Submodule (ULift.{u} ℤ) A` to `Subtype.val`. Establish `hW : Monotone Wf` using `fun i j hij => hij`. Establish `hstable : ∀ i g, Wf i ≤ (Wf i).comap (A.ρ g)` using `fun i => i.2.1`. Establish `: Nonempty ι` using `⟨⟨⊥, fun g => bot_le, inferInstance⟩⟩`.

Establish `: IsDirectedOrder ι` using `⟨fun i j => by`. Use `i.2.2` as an intermediate fact. Use `j.2.2` as an intermediate fact. Conclude with `⟨⟨i.1 ⊔ j.1, fun g => sup_le ((i.2.1 g).trans (Submodule.comap_mono le_sup_left)) ((j.2.1 g).trans (Submodule.comap_mono le_sup_right)), finite_sup_of_finite _ _⟩, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩`. Establish `hunion : ∀ a : A, ∃ i, a ∈ Wf i` using `fun a => by`.

Take `⟨W, h1, h2, h3⟩` from `exists_finite_stable_submodule A hp hA a`. Conclude with `⟨⟨W, h1, h2⟩, h3⟩`. It suffices to establish `hz : ∀ x : cohomology A m, x = 0 from ⟨fun x y => by rw [hz x, hz y]⟩`. Introduce `x`. Take `⟨i, z, rfl⟩` from `exists_cohomologyMap_subtype_eq A Wf hW hstable hunion m x`.

Establish `: Finite (A.subrepresentation (Wf i) (hstable i))` using `i.2.2`. Establish `hs` using `h (A.subrepresentation (Wf i) (hstable i)) (by`. Introduce and unpack `⟨b, hb⟩`. Take `⟨k, hk⟩` from `hA b`. Conclude with `⟨k, Subtype.ext hk⟩)`.

Rewrite using `[@Subsingleton.elim _ hs z 0, map_zero]`.
-/
theorem subsingleton_cohomology_of_primary_of_finite [CompactSpace G] {p : ℕ} (hp : 0 < p) {m : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] [Finite A],
      (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → Subsingleton (cohomology A m))
    (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) :
    Subsingleton (cohomology A m) := by
  let ι := {W : Submodule (ULift.{u} ℤ) A // (∀ g, W ≤ W.comap (A.ρ g)) ∧ Finite W}
  let Wf : ι → Submodule (ULift.{u} ℤ) A := Subtype.val
  have hW : Monotone Wf := fun i j hij => hij
  have hstable : ∀ i g, Wf i ≤ (Wf i).comap (A.ρ g) := fun i => i.2.1
  have : Nonempty ι := ⟨⟨⊥, fun g => bot_le, inferInstance⟩⟩
  have : IsDirectedOrder ι := ⟨fun i j => by
    have := i.2.2
    have := j.2.2
    exact ⟨⟨i.1 ⊔ j.1, fun g => sup_le ((i.2.1 g).trans (Submodule.comap_mono le_sup_left))
      ((j.2.1 g).trans (Submodule.comap_mono le_sup_right)), finite_sup_of_finite _ _⟩,
      (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩
  have hunion : ∀ a : A, ∃ i, a ∈ Wf i := fun a => by
    obtain ⟨W, h1, h2, h3⟩ := exists_finite_stable_submodule A hp hA a
    exact ⟨⟨W, h1, h2⟩, h3⟩
  suffices hz : ∀ x : cohomology A m, x = 0 from ⟨fun x y => by rw [hz x, hz y]⟩
  intro x
  obtain ⟨i, z, rfl⟩ := exists_cohomologyMap_subtype_eq A Wf hW hstable hunion m x
  have : Finite (A.subrepresentation (Wf i) (hstable i)) := i.2.2
  have hs := h (A.subrepresentation (Wf i) (hstable i)) (by
    rintro ⟨b, hb⟩
    obtain ⟨k, hk⟩ := hA b
    exact ⟨k, Subtype.ext hk⟩)
  rw [@Subsingleton.elim _ hs z 0, map_zero]

/- English proof (translation)
Set `f' : LocallyConstant G A` to `f`. Establish `: Finite (Set.range f')` using `f'.range_finite.to_subtype`. Use `choose kk hkk using fun v : Set.range f' => hA v`. Take `⟨K, hK⟩` from `(Set.finite_range kk).bddAbove`. Use `⟨K, LocallyConstant.ext fun x => ?_⟩` and prove the remaining obligations.

Use `show p ^ K • f' x = 0`. Conclude with `pow_nsmul_eq_zero_of_le (hK ⟨⟨f' x, x, rfl⟩, rfl⟩) (hkk ⟨f' x, x, rfl⟩)`.
-/
theorem primary_discreteCoind [CompactSpace G] (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A]
    {p : ℕ} (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) (f : discreteCoind (ULift.{u} ℤ) G A) :
    ∃ k : ℕ, p ^ k • f = 0 := by
  let f' : LocallyConstant G A := f
  have : Finite (Set.range f') := f'.range_finite.to_subtype
  choose kk hkk using fun v : Set.range f' => hA v
  obtain ⟨K, hK⟩ := (Set.finite_range kk).bddAbove
  refine ⟨K, LocallyConstant.ext fun x => ?_⟩
  show p ^ K • f' x = 0
  exact pow_nsmul_eq_zero_of_le (hK ⟨⟨f' x, x, rfl⟩, rfl⟩) (hkk ⟨f' x, x, rfl⟩)

/- English proof (translation)
Establish `hepi : Epi (coindCokernelπ A)` using `(coindShortComplex_shortExact A).epi_g`. Take `⟨f, rfl⟩` from `(Rep.epi_iff_surjective (coindCokernelπ A)).1 hepi x`. Take `⟨k, hk⟩` from `primary_discreteCoind A hA f`. Conclude with `⟨k, by rw [← map_nsmul, hk, map_zero]⟩`.
-/
theorem primary_coindCokernel [CompactSpace G] (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A]
    {p : ℕ} (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) (x : coindCokernel A) :
    ∃ k : ℕ, p ^ k • x = 0 := by
  have hepi : Epi (coindCokernelπ A) := (coindShortComplex_shortExact A).epi_g
  obtain ⟨f, rfl⟩ := (Rep.epi_iff_surjective (coindCokernelπ A)).1 hepi x
  obtain ⟨k, hk⟩ := primary_discreteCoind A hA f
  exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact h`. Consider the case `succ j ih`. Introduce `A _ hA`. Establish `h'` using `ih (coindCokernel A) (primary_coindCokernel A hA)`.

Rewrite `h'` using `[show m + 1 + j = m + j + 1 by omega]`. Rewrite using `[show m + 1 + (j + 1) = m + j + 2 by omega]`. Conclude with `(cohomologyCoindCokernelIso A (m + j)).toLinearEquiv.symm.toEquiv.subsingleton`.
-/
theorem subsingleton_cohomology_add_of_primary [CompactSpace G] {p : ℕ} {m : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) →
      Subsingleton (cohomology A (m + 1))) (j : ℕ) :
    ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) →
      Subsingleton (cohomology A (m + 1 + j)) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro A _ hA
    have h' := ih (coindCokernel A) (primary_coindCokernel A hA)
    rw [show m + 1 + j = m + j + 1 by omega] at h'
    rw [show m + 1 + (j + 1) = m + j + 2 by omega]
    exact (cohomologyCoindCokernelIso A (m + j)).toLinearEquiv.symm.toEquiv.subsingleton

end Devissage

section Criteria

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/- English proof (translation)
Use `⟨fun h => ?_, cdp_le_of_forall_primary hp⟩` and prove the remaining obligations. Establish `hsimple : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], IsSimpleOrder (Subrepresentation A.ρ) → (∀ a : A, p • a = 0) → Subsingleton (cohomology A (n + 1))` using `fun A _ _ hA => subsingleton_cohomology_of_cdp_le hp h A hA (Nat.lt_succ_self n)`. Establish `hprim : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → Subsingleton (cohomology A (n + 1))` using `fun A _ hA => subsingleton_cohomology_of_primary_of_finite hp.pos (fun B _ _ hB => subsingleton_cohomology_of_finite_of_simple hsimple B hB) A hA`. Introduce `A _ hA q hq`. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_lt hq`.

Use `subsingleton_cohomology_add_of_primary hprim j A hA` as an intermediate fact. Rewrite `this` using `[show n + 1 + j = n + j + 1 by omega]`. Then use the resulting hypothesis.
-/
theorem cdp_le_iff_forall_primary {p : ℕ} (hp : p.Prime) (n : ℕ) :
    cdp p G ≤ n ↔ ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A],
      (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → ∀ q : ℕ, n < q → Subsingleton (cohomology A q) := by
  refine ⟨fun h => ?_, cdp_le_of_forall_primary hp⟩
  have hsimple : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A],
      IsSimpleOrder (Subrepresentation A.ρ) → (∀ a : A, p • a = 0) →
        Subsingleton (cohomology A (n + 1)) :=
    fun A _ _ hA => subsingleton_cohomology_of_cdp_le hp h A hA (Nat.lt_succ_self n)
  have hprim : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A],
      (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → Subsingleton (cohomology A (n + 1)) :=
    fun A _ hA => subsingleton_cohomology_of_primary_of_finite hp.pos
      (fun B _ _ hB => subsingleton_cohomology_of_finite_of_simple hsimple B hB) A hA
  intro A _ hA q hq
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hq
  have := subsingleton_cohomology_add_of_primary hprim j A hA
  rwa [show n + 1 + j = n + j + 1 by omega] at this

/- English proof (translation)
Use `⟨fun h A _ _ hA => subsingleton_cohomology_of_cdp_le hp h A hA (Nat.lt_succ_self n), fun h => cdp_le_of_forall_primary hp ?_⟩` and prove the remaining obligations. Introduce `A _ hA q hq`. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_lt hq`. Use `subsingleton_cohomology_add_of_primary (fun B _ hB => subsingleton_cohomology_of_primary_of_finite hp.pos (fun C _ _ hC => subsingleton_cohomology_of_finite_of_simple h C hC) B hB) j A hA` as an intermediate fact. Rewrite `this` using `[show n + 1 + j = n + j + 1 by omega]`. Then use the resulting hypothesis.
-/
theorem cdp_le_iff_forall_simple {p : ℕ} (hp : p.Prime) (n : ℕ) :
    cdp p G ≤ n ↔ ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A],
      IsSimpleOrder (Subrepresentation A.ρ) → (∀ a : A, p • a = 0) →
        Subsingleton (cohomology A (n + 1)) := by
  refine ⟨fun h A _ _ hA => subsingleton_cohomology_of_cdp_le hp h A hA (Nat.lt_succ_self n),
    fun h => cdp_le_of_forall_primary hp ?_⟩
  intro A _ hA q hq
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hq
  have := subsingleton_cohomology_add_of_primary
    (fun B _ hB => subsingleton_cohomology_of_primary_of_finite hp.pos
      (fun C _ _ hC => subsingleton_cohomology_of_finite_of_simple h C hC) B hB) j A hA
  rwa [show n + 1 + j = n + j + 1 by omega] at this

end Criteria

section Strict

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
The claim follows from `le_iSup (fun q : Nat.Primes => cdp (q : ℕ) G) ⟨p, hp⟩`.
-/
theorem cdp_le_cd {p : ℕ} (hp : p.Prime) : cdp p G ≤ cd G :=
  le_iSup (fun q : Nat.Primes => cdp (q : ℕ) G) ⟨p, hp⟩

/- English proof (translation)
The claim follows from `le_iSup (fun q : Nat.Primes => scdp (q : ℕ) G) ⟨p, hp⟩`.
-/
theorem scdp_le_scd {p : ℕ} (hp : p.Prime) : scdp p G ≤ scd G :=
  le_iSup (fun q : Nat.Primes => scdp (q : ℕ) G) ⟨p, hp⟩

/- English proof (translation)
Distinguish the cases in `htop : cdp p G = ⊤`. Rewrite using `[htop]`. Simplify using the standard rewrite rules. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.1 htop`. Establish `hcd : cdp p G ≤ n` using `hn ▸ le_rfl`.

Rewrite using `[← hn, scdp_le_iff]`. Introduce `A _ q hq`. Establish `hq' : n + 1 < q` using `by exact_mod_cast hq`. Take `⟨q', rfl⟩ : ∃ q', q = q' + 1` from `⟨q - 1, by omega⟩`. Set `φ : A →ₗ[ULift.{u} ℤ] A` to `p • LinearMap.id`.

Establish `hφ : ∀ g (a : A), φ (A.ρ g a) = A.ρ g (φ a)` using `fun g a => by simp [φ, map_nsmul]`. Set `K` to `LinearMap.ker φ`. Set `I` to `LinearMap.range φ`. Establish `hK : ∀ g, K ≤ K.comap (A.ρ g)`. Introduce `g a ha`.

Simplify using `only [K, LinearMap.mem_ker, Submodule.mem_comap] at ha ⊢`. Rewrite using `[hφ, ha, map_zero]`. Establish `hI : ∀ g, I ≤ I.comap (A.ρ g)`. Introduce and unpack `g _ ⟨b, rfl⟩`. Conclude with `⟨A.ρ g b, hφ g b⟩`.

Set `π : A ⟶ A.subrepresentation I hI` to `Rep.ofHom ⟨φ.rangeRestrict, fun g => LinearMap.ext fun a => Subtype.ext (hφ g a)⟩`. Set `S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)` to `ShortComplex.mk (Rep.subtype A K hK) π (by`. Use extensionality with `w`. Conclude with `LinearMap.mem_ker.1 w.2)`. Establish `: IsDiscreteRep S.X₁` using `isDiscreteRep_subrepresentation A K hK`.

Establish `: IsDiscreteRep S.X₂` using `(inferInstance : IsDiscreteRep A)`. Establish `: IsDiscreteRep S.X₃` using `isDiscreteRep_subrepresentation A I hI`. Establish `hS : S.ShortExact` using `{ exact := by`. Rewrite using `[← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} (ULift.{u} ℤ) G) (ModuleCat.{u} (ULift.{u} ℤ))), ShortComplex.moduleCat_exact_iff]`. Introduce `a ha`.

Conclude with `⟨⟨a, LinearMap.mem_ker.2 (congrArg Subtype.val ha)⟩, rfl⟩`. Use `mono_f := (Rep.mono_iff_injective _).2 Subtype.val_injective`. Use `epi_g := (Rep.epi_iff_surjective _).2 (LinearMap.surjective_rangeRestrict φ) }`. Establish `hKp : ∀ x : A.subrepresentation K hK, p • x = 0` using `fun x => Subtype.ext (LinearMap.mem_ker.1 x.2)`. Establish `hQp : ∀ x : A.quotient I hI, p • x = 0`.

Introduce `x`. Take `⟨a, rfl⟩` from `Submodule.mkQ_surjective I x`. Rewrite using `[← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨a, rfl⟩`. Establish `hKq` using `subsingleton_cohomology_of_cdp_le hp hcd _ hKp (show n < q' + 1 by omega)`.

Establish `hQq` using `subsingleton_cohomology_of_cdp_le hp hcd _ hQp (show n < q' by omega)`. Establish `hπinj : ∀ y : cohomology A (q' + 1), (cohomologyMap π (q' + 1)).hom y = 0 → y = 0`. Introduce `y hy`. Take `⟨z, hz⟩` from `(ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS (q' + 1)) y hy`. Rewrite using `[← hz, @Subsingleton.elim _ hKq z 0]`.

Conclude with `map_zero _`. Establish `hιinj : ∀ y : cohomology (A.subrepresentation I hI) (q' + 1), (cohomologyMap (Rep.subtype A I hI) (q' + 1)).hom y = 0 → y = 0`. Introduce `y hy`. Take `⟨w, hw⟩` from `(ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ (subQuotShortComplex_shortExact A I hI) q' (q' + 1) rfl) y hy`. Rewrite using `[← hw, @Subsingleton.elim _ hQq w 0]`.

Conclude with `map_zero _`. Establish `hcomp : π ≫ Rep.subtype A I hI = p • 𝟙 A`. Use extensionality with `a`. Both sides reduce to the same expression. Establish `hpinj : ∀ x : cohomology A (q' + 1), p • x = 0 → x = 0`.

Introduce `x hx`. Rewrite `hx` using `[← cohomologyMap_nsmul_id_apply, ← hcomp, cohomologyMap_comp]`. Conclude with `hπinj x (hιinj _ hx)`. Rewrite using `[primaryComponent_eq_bot_iff]`. Introduce and unpack `x ⟨k, hk⟩`.

Conclude with `eq_zero_of_pow_nsmul_eq_zero hpinj k x hk`.
-/
theorem scdp_le_cdp_add_one {p : ℕ} (hp : p.Prime) : scdp p G ≤ cdp p G + 1 := by
  by_cases htop : cdp p G = ⊤
  · rw [htop]
    simp
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  have hcd : cdp p G ≤ n := hn ▸ le_rfl
  rw [← hn, scdp_le_iff]
  intro A _ q hq
  have hq' : n + 1 < q := by exact_mod_cast hq
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  let φ : A →ₗ[ULift.{u} ℤ] A := p • LinearMap.id
  have hφ : ∀ g (a : A), φ (A.ρ g a) = A.ρ g (φ a) := fun g a => by simp [φ, map_nsmul]
  let K := LinearMap.ker φ
  let I := LinearMap.range φ
  have hK : ∀ g, K ≤ K.comap (A.ρ g) := by
    intro g a ha
    simp only [K, LinearMap.mem_ker, Submodule.mem_comap] at ha ⊢
    rw [hφ, ha, map_zero]
  have hI : ∀ g, I ≤ I.comap (A.ρ g) := by
    rintro g _ ⟨b, rfl⟩
    exact ⟨A.ρ g b, hφ g b⟩
  let π : A ⟶ A.subrepresentation I hI :=
    Rep.ofHom ⟨φ.rangeRestrict, fun g => LinearMap.ext fun a => Subtype.ext (hφ g a)⟩
  let S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G) :=
    ShortComplex.mk (Rep.subtype A K hK) π (by
      ext w
      exact LinearMap.mem_ker.1 w.2)
  have : IsDiscreteRep S.X₁ := isDiscreteRep_subrepresentation A K hK
  have : IsDiscreteRep S.X₂ := (inferInstance : IsDiscreteRep A)
  have : IsDiscreteRep S.X₃ := isDiscreteRep_subrepresentation A I hI
  have hS : S.ShortExact :=
    { exact := by
        rw [← ShortComplex.exact_map_iff_of_faithful _
          (forget₂ (Rep.{u} (ULift.{u} ℤ) G) (ModuleCat.{u} (ULift.{u} ℤ))),
          ShortComplex.moduleCat_exact_iff]
        intro a ha
        exact ⟨⟨a, LinearMap.mem_ker.2 (congrArg Subtype.val ha)⟩, rfl⟩
      mono_f := (Rep.mono_iff_injective _).2 Subtype.val_injective
      epi_g := (Rep.epi_iff_surjective _).2 (LinearMap.surjective_rangeRestrict φ) }
  have hKp : ∀ x : A.subrepresentation K hK, p • x = 0 := fun x =>
    Subtype.ext (LinearMap.mem_ker.1 x.2)
  have hQp : ∀ x : A.quotient I hI, p • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective I x
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, rfl⟩
  have hKq := subsingleton_cohomology_of_cdp_le hp hcd _ hKp (show n < q' + 1 by omega)
  have hQq := subsingleton_cohomology_of_cdp_le hp hcd _ hQp (show n < q' by omega)
  have hπinj : ∀ y : cohomology A (q' + 1), (cohomologyMap π (q' + 1)).hom y = 0 → y = 0 := by
    intro y hy
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS (q' + 1)) y hy
    rw [← hz, @Subsingleton.elim _ hKq z 0]
    exact map_zero _
  have hιinj : ∀ y : cohomology (A.subrepresentation I hI) (q' + 1),
      (cohomologyMap (Rep.subtype A I hI) (q' + 1)).hom y = 0 → y = 0 := by
    intro y hy
    obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (cohomology_exact₁ (subQuotShortComplex_shortExact A I hI) q' (q' + 1) rfl) y hy
    rw [← hw, @Subsingleton.elim _ hQq w 0]
    exact map_zero _
  have hcomp : π ≫ Rep.subtype A I hI = p • 𝟙 A := by
    ext a
    rfl
  have hpinj : ∀ x : cohomology A (q' + 1), p • x = 0 → x = 0 := by
    intro x hx
    rw [← cohomologyMap_nsmul_id_apply, ← hcomp, cohomologyMap_comp] at hx
    exact hπinj x (hιinj _ hx)
  rw [primaryComponent_eq_bot_iff]
  rintro x ⟨k, hk⟩
  exact eq_zero_of_pow_nsmul_eq_zero hpinj k x hk

/- English proof (translation)
The claim follows from `scd_le_iff.2 fun _ hp => (scdp_le_cdp_add_one hp).trans (add_le_add (cdp_le_cd hp) le_rfl)`.
-/
theorem scd_le_cd_add_one : scd G ≤ cd G + 1 :=
  scd_le_iff.2 fun _ hp => (scdp_le_cdp_add_one hp).trans (add_le_add (cdp_le_cd hp) le_rfl)

end Strict

end GroundTheory.ProfCoh
