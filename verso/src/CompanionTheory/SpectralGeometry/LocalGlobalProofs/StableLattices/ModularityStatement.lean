import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeCoinv

section Action

variable (Γ : Type) {X : Type} [Group Γ] [MulAction Γ X]

def cnt (x y : X) : ℕ := Nat.card {γ : Γ // γ • x = y}

variable {Γ}

/- English proof (translation)
Use `Nat.card_congr ⟨fun γ => ⟨t * γ.1 * s⁻¹, ?_⟩, fun γ => ⟨t⁻¹ * γ.1 * s, ?_⟩, fun γ => ?_, fun γ => ?_⟩` and prove the remaining obligations. Simplify using `[mul_smul, γ.2]`. Rewrite using `[mul_smul, mul_smul, γ.2, inv_smul_smul]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[mul_assoc]`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[mul_assoc]`.
-/
theorem cnt_congr {a b : X} (s t : Γ) : cnt Γ a b = cnt Γ (s • a) (t • b) := by
  refine Nat.card_congr ⟨fun γ => ⟨t * γ.1 * s⁻¹, ?_⟩, fun γ => ⟨t⁻¹ * γ.1 * s, ?_⟩, fun γ => ?_, fun γ => ?_⟩
  · simp [mul_smul, γ.2]
  · rw [mul_smul, mul_smul, γ.2, inv_smul_smul]
  · apply Subtype.ext; simp [mul_assoc]
  · apply Subtype.ext; simp [mul_assoc]

/- English proof (translation)
Distinguish the cases in `hne : Nonempty {γ : Γ // γ • x = y}`. Take `⟨γ0, h0⟩` from `hne`. Use `Finite.of_injective (β := MulAction.stabilizer Γ x) (fun γ => ⟨γ0⁻¹ * γ.1, ?_⟩) ?_` and prove the remaining obligations. Rewrite using `[MulAction.mem_stabilizer_iff, mul_smul, γ.2, ← h0, inv_smul_smul]`. Introduce `a b hab`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using congrArg Subtype.val hab`. Use `haveI := not_nonempty_iff.1 hne infer_instance`.
-/
theorem finite_fib [∀ x : X, Finite (MulAction.stabilizer Γ x)] (x y : X) :
    Finite {γ : Γ // γ • x = y} := by
  by_cases hne : Nonempty {γ : Γ // γ • x = y}
  · obtain ⟨γ0, h0⟩ := hne
    refine Finite.of_injective (β := MulAction.stabilizer Γ x) (fun γ => ⟨γ0⁻¹ * γ.1, ?_⟩) ?_
    · rw [MulAction.mem_stabilizer_iff, mul_smul, γ.2, ← h0, inv_smul_smul]
    · intro a b hab
      apply Subtype.ext
      simpa using congrArg Subtype.val hab
  · haveI := not_nonempty_iff.1 hne
    infer_instance

/- English proof (translation)
Use `haveI := finite_fib (Γ := Γ) x x`. Use `haveI : Nonempty {γ : Γ // γ • x = x} := ⟨⟨1, one_smul _ _⟩⟩`. Conclude with `Nat.card_pos`.
-/
theorem cnt_self_pos [∀ x : X, Finite (MulAction.stabilizer Γ x)] (x : X) : 0 < cnt Γ x x := by
  haveI := finite_fib (Γ := Γ) x x
  haveI : Nonempty {γ : Γ // γ • x = x} := ⟨⟨1, one_smul _ _⟩⟩
  exact Nat.card_pos

/- English proof (translation)
Use `Set.Finite.subset (Set.Finite.biUnion f.support.finite_toSet (t := fun z => {γ : Γ | γ • x = z}) ?_) ?_` and prove the remaining obligations. Introduce `z _`. Conclude with `Set.finite_coe_iff.1 (finite_fib (Γ := Γ) x z)`. Introduce `γ hγ`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq]`.

Conclude with `⟨γ • x, by simpa using hγ, rfl⟩`.
-/
theorem support_finite [∀ x : X, Finite (MulAction.stabilizer Γ x)] (f : X →₀ ℂ) (x : X) :
    (Function.support fun γ : Γ => f (γ • x)).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion f.support.finite_toSet
    (t := fun z => {γ : Γ | γ • x = z}) ?_) ?_
  · intro z _
    exact Set.finite_coe_iff.1 (finite_fib (Γ := Γ) x z)
  · intro γ hγ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨γ • x, by simpa using hγ, rfl⟩

/- English proof (translation)
Rewrite using `[finsum_eq_sum_of_support_subset _ (s := (support_finite (Γ := Γ) f x).toFinset) (by simp)]`. Establish `hmaps : ∀ γ ∈ (support_finite (Γ` using `Γ) f x).toFinset, γ • x ∈ f.support := by`. Introduce `γ hγ`. Simplify using `using hγ`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmaps, Finsupp.sum]`.

Use `Finset.sum_congr rfl fun z hz => ?_` and prove the remaining obligations. Establish `h1 : ∀ γ ∈ (support_finite (Γ` using `Γ) f x).toFinset.filter (fun γ => γ • x = z), f (γ • x) = f z := by`. Introduce `γ hγ`. Rewrite using `[(Finset.mem_filter.1 hγ).2]`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_comm]`.

Use `congr 2`. Establish `H : ∀ γ : Γ, γ • x = z ↔ γ ∈ (support_finite (Γ` using `Γ) f x).toFinset.filter (fun γ => γ • x = z) := by`. Introduce `γ`. Prove the components needed by the constructor for the conclusion. Introduce `hγ`.

Use `Finset.mem_filter.2 ⟨?_, hγ⟩` and prove the remaining obligations. Simplify `Finsupp.mem_support_iff.1 hz` using `[hγ]`. Introduce `hγ`. Conclude with `(Finset.mem_filter.1 hγ).2`. Unfold `cnt`.

Rewrite using `[Nat.card_congr (Equiv.subtypeEquivRight H), Nat.card_eq_fintype_card, Fintype.card_coe]`.
-/
theorem finsum_eq [∀ x : X, Finite (MulAction.stabilizer Γ x)] (f : X →₀ ℂ) (x : X) :
    ∑ᶠ γ : Γ, f (γ • x) = f.sum fun z c => c * (cnt Γ x z : ℂ) := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := (support_finite (Γ := Γ) f x).toFinset) (by simp)]
  have hmaps : ∀ γ ∈ (support_finite (Γ := Γ) f x).toFinset, γ • x ∈ f.support := by
    intro γ hγ
    simpa using hγ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finsupp.sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have h1 : ∀ γ ∈ (support_finite (Γ := Γ) f x).toFinset.filter (fun γ => γ • x = z),
      f (γ • x) = f z := by
    intro γ hγ
    rw [(Finset.mem_filter.1 hγ).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have H : ∀ γ : Γ, γ • x = z ↔ γ ∈ (support_finite (Γ := Γ) f x).toFinset.filter (fun γ => γ • x = z) := by
    intro γ
    constructor
    · intro hγ
      refine Finset.mem_filter.2 ⟨?_, hγ⟩
      simpa [hγ] using Finsupp.mem_support_iff.1 hz
    · intro hγ
      exact (Finset.mem_filter.1 hγ).2
  unfold cnt
  rw [Nat.card_congr (Equiv.subtypeEquivRight H), Nat.card_eq_fintype_card, Fintype.card_coe]

/- English proof (translation)
Set `Q` to `MulAction.orbitRel.Quotient Γ X`. Set `π : X → Q` to `fun x => Quotient.mk'' x`. Set `o : Q → X` to `fun q => q.out`. Establish `hπo : ∀ q, π (o q) = q` using `fun q => Quotient.out_eq' q`. Establish `hrel : ∀ x y, π x = π y → ∃ γ : Γ, γ • y = x`.

Introduce `x y hxy`. Establish `: x ∈ MulAction.orbit Γ y` using `MulAction.orbitRel_apply.1 (Quotient.eq''.1 hxy)`. Conclude with `this`. Set `e : Q ≃ Fin (Nat.card Q)` to `Finite.equivFin Q`. Set `w : Q → ℕ` to `fun q => cnt Γ (o q) (o q)`.

Establish `hw : ∀ q, 0 < w q` using `fun q => cnt_self_pos _`. Set `cf : Q → ℂ` to `fun q => ((Real.sqrt (w q) : ℝ) : ℂ)`. Establish `hcf : ∀ q, conj (cf q) * cf q = (w q : ℂ)`. Introduce `q`. Simplify using `only [cf, Complex.conj_ofReal, ← Complex.ofReal_mul]`.

Rewrite using `[Real.mul_self_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Establish `hcf0 : ∀ q, cf q ≠ 0`. Introduce `q`. Use `Real.sqrt_pos.2 (Nat.cast_pos.2 (hw q) : (0 : ℝ) < w q)` as an intermediate fact.

Conclude with `Complex.ofReal_ne_zero.2 this.ne'`. Set `vec : X → EuclideanSpace ℂ (Fin (Nat.card Q))` to `fun x => EuclideanSpace.single (e (π x)) (cf (π x))`. Use `⟨Nat.card Q, Finsupp.linearCombination ℂ vec, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff]`. Introduce `v _`.

Rewrite using `[← (EuclideanSpace.basisFun (Fin (Nat.card Q)) ℂ).sum_repr v]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `⟨Finsupp.single (o (e.symm i)) (cf (e.symm i))⁻¹, ?_⟩` and prove the remaining obligations. Simplify using `only [Finsupp.linearCombination_single, vec, hπo, Equiv.apply_symm_apply]`. Use extensionality with `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[hcf0]`. Simplify using `[hj]`. Introduce `x y`.

Simplify using `only [Finsupp.linearCombination_single, one_smul, vec]`. Distinguish the cases in `hxy : π x = π y`. Take `⟨γ, hγ⟩` from `hrel (o (π x)) x (hπo _ ▸ rfl)`. Take `⟨γ', hγ'⟩` from `hrel (o (π x)) y (by rw [hπo, hxy])`. Establish `: cnt Γ x y = w (π x)` using `by show _ = cnt Γ (o (π x)) (o (π x)) conv_rhs => rw [← hγ] conv_rhs => rhs; rw [hγ, ← hγ']`.

Conclude with `cnt_congr γ γ'`. Rewrite using `[this, ← hxy, EuclideanSpace.inner_single_left]`. Simplify using `[hcf]`. Establish `hne : e (π x) ≠ e (π y)` using `fun h => hxy (e.injective h)`. Establish `: IsEmpty {γ : Γ // γ • x = y}` using `⟨fun γ => by`.

Take `⟨γ, hγ⟩` from `γ`. Apply `hxy` to reduce the goal to its premises. Rewrite using `[← hγ]`. Conclude with `(Quotient.eq''.2 (MulAction.orbitRel_apply.2 ⟨γ⁻¹, by simp⟩))⟩`. Establish `h0 : cnt Γ x y = 0` using `Nat.card_of_isEmpty`.

Rewrite using `[h0, EuclideanSpace.inner_single_left]`. Simplify using `[hne, Ne.symm hne]`.
-/
theorem exists_phi [Finite (MulAction.orbitRel.Quotient Γ X)] [∀ x : X, Finite (MulAction.stabilizer Γ x)] :
    ∃ (N : ℕ) (φ : (X →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)), Function.Surjective φ ∧
      ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ) := by
  classical
  let Q := MulAction.orbitRel.Quotient Γ X
  let π : X → Q := fun x => Quotient.mk'' x
  let o : Q → X := fun q => q.out
  have hπo : ∀ q, π (o q) = q := fun q => Quotient.out_eq' q
  have hrel : ∀ x y, π x = π y → ∃ γ : Γ, γ • y = x := by
    intro x y hxy
    have : x ∈ MulAction.orbit Γ y := MulAction.orbitRel_apply.1 (Quotient.eq''.1 hxy)
    exact this
  let e : Q ≃ Fin (Nat.card Q) := Finite.equivFin Q
  let w : Q → ℕ := fun q => cnt Γ (o q) (o q)
  have hw : ∀ q, 0 < w q := fun q => cnt_self_pos _
  let cf : Q → ℂ := fun q => ((Real.sqrt (w q) : ℝ) : ℂ)
  have hcf : ∀ q, conj (cf q) * cf q = (w q : ℂ) := by
    intro q
    simp only [cf, Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have hcf0 : ∀ q, cf q ≠ 0 := by
    intro q
    have := Real.sqrt_pos.2 (Nat.cast_pos.2 (hw q) : (0 : ℝ) < w q)
    exact Complex.ofReal_ne_zero.2 this.ne'
  let vec : X → EuclideanSpace ℂ (Fin (Nat.card Q)) := fun x => EuclideanSpace.single (e (π x)) (cf (π x))
  refine ⟨Nat.card Q, Finsupp.linearCombination ℂ vec, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, eq_top_iff]
    intro v _
    rw [← (EuclideanSpace.basisFun (Fin (Nat.card Q)) ℂ).sum_repr v]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    refine ⟨Finsupp.single (o (e.symm i)) (cf (e.symm i))⁻¹, ?_⟩
    simp only [Finsupp.linearCombination_single, vec, hπo, Equiv.apply_symm_apply]
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hcf0]
    · simp [hj]
  · intro x y
    simp only [Finsupp.linearCombination_single, one_smul, vec]
    by_cases hxy : π x = π y
    · obtain ⟨γ, hγ⟩ := hrel (o (π x)) x (hπo _ ▸ rfl)
      obtain ⟨γ', hγ'⟩ := hrel (o (π x)) y (by rw [hπo, hxy])
      have : cnt Γ x y = w (π x) := by
        show _ = cnt Γ (o (π x)) (o (π x))
        conv_rhs => rw [← hγ]
        conv_rhs => rhs; rw [hγ, ← hγ']
        exact cnt_congr γ γ'
      rw [this, ← hxy, EuclideanSpace.inner_single_left]
      simp [hcf]
    · have hne : e (π x) ≠ e (π y) := fun h => hxy (e.injective h)
      have : IsEmpty {γ : Γ // γ • x = y} := ⟨fun γ => by
        obtain ⟨γ, hγ⟩ := γ
        apply hxy
        rw [← hγ]
        exact (Quotient.eq''.2 (MulAction.orbitRel_apply.2 ⟨γ⁻¹, by simp⟩))⟩
      have h0 : cnt Γ x y = 0 := Nat.card_of_isEmpty
      rw [h0, EuclideanSpace.inner_single_left]
      simp [hne, Ne.symm hne]

end Action

section Hecke

variable {G : Type} [Group G] {K : Subgroup G}

def ent (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (x y : G ⧸ K) : ℂ := h (Finsupp.single y 1) x

/- English proof (translation)
Simplify using `[lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]`.
-/
theorem lam_single (g : G) (x : G ⧸ K) (c : ℂ) :
    lam K g (Finsupp.single x c) = Finsupp.single (g • x) c := by
  simp [lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/- English proof (translation)
The claim follows from `Finsupp.mapDomain_apply (MulAction.injective g) f x`.
-/
theorem lam_apply_smul (g : G) (f : (G ⧸ K) →₀ ℂ) (x : G ⧸ K) : lam K g f (g • x) = f x :=
  Finsupp.mapDomain_apply (MulAction.injective g) f x

/- English proof (translation)
Use `(Subalgebra.mem_centralizer_iff ℂ).1 h.2 (lam K g) ⟨g, rfl⟩` as an intermediate fact. Conclude with `(LinearMap.congr_fun this u).symm`.
-/
theorem comm_lam (h : Hk K) (g : G) (u : (G ⧸ K) →₀ ℂ) : h.1 (lam K g u) = lam K g (h.1 u) := by
  have := (Subalgebra.mem_centralizer_iff ℂ).1 h.2 (lam K g) ⟨g, rfl⟩
  exact (LinearMap.congr_fun this u).symm

/- English proof (translation)
Unfold `ent`. Rewrite using `[← lam_single, comm_lam, lam_apply_smul]`.
-/
theorem ent_smul (h : Hk K) (g : G) (x y : G ⧸ K) : ent h.1 (g • x) (g • y) = ent h.1 x y := by
  unfold ent
  rw [← lam_single, comm_lam, lam_apply_smul]

/- English proof (translation)
Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective x`. Use `set A := (h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1)).support with hA`. Use `Set.Finite.subset (Set.Finite.biUnion (s := (A : Set (G ⧸ K))) A.finite_toSet (t := fun a => (fun w => g • w) '' MulAction.orbit K (((Quotient.out a)⁻¹ : G) : G ⧸ K)) (fun a _ => (hp _).image _)) ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨g', rfl⟩` from `QuotientGroup.mk_surjective z`.

Establish `h1 : ent h.1 ((g'⁻¹ * g : G) : G ⧸ K) ((1 : G) : G ⧸ K) ≠ 0`. Establish `h2` using `ent_smul h g'⁻¹ (g : G ⧸ K) (g' : G ⧸ K)`. Establish `h3 : g'⁻¹ • (g : G ⧸ K) = ((g'⁻¹ * g : G) : G ⧸ K)` using `rfl`. Establish `h4 : g'⁻¹ • (g' : G ⧸ K) = ((1 : G) : G ⧸ K)` using `by show ((g'⁻¹ * g' : G) : G ⧸ K) = _`. Simplify using the standard rewrite rules.

Rewrite `h2` using `[h3, h4]`. Rewrite using `[h2]`. Conclude with `hz`. Use `set a : G ⧸ K := ((g'⁻¹ * g : G) : G ⧸ K) with ha`. Establish `haA : a ∈ A` using `Finsupp.mem_support_iff.2 h1`.

Establish `hk : (Quotient.out a : G)⁻¹ * (g'⁻¹ * g) ∈ K` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' a)`. Simplify using `only [Set.mem_iUnion]`. Use `⟨a, haA, ?_⟩` and prove the remaining obligations. Use `⟨(⟨((Quotient.out a : G)⁻¹ * (g'⁻¹ * g))⁻¹, K.inv_mem hk⟩ : K) • (((Quotient.out a)⁻¹ : G) : G ⧸ K), MulAction.mem_orbit _ _, ?_⟩` and prove the remaining obligations. Use `show ((g * (((Quotient.out a : G)⁻¹ * (g'⁻¹ * g))⁻¹ * (Quotient.out a)⁻¹) : G) : G ⧸ K) = _`.

Use `congr 1`. Use `group`.
-/
theorem row_finite (hp : IsHeckePair K) (h : Hk K) (x : G ⧸ K) : {z | ent h.1 x z ≠ 0}.Finite := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  set A := (h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1)).support with hA
  refine Set.Finite.subset (Set.Finite.biUnion (s := (A : Set (G ⧸ K))) A.finite_toSet
    (t := fun a => (fun w => g • w) '' MulAction.orbit K (((Quotient.out a)⁻¹ : G) : G ⧸ K))
    (fun a _ => (hp _).image _)) ?_
  intro z hz
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective z
  have h1 : ent h.1 ((g'⁻¹ * g : G) : G ⧸ K) ((1 : G) : G ⧸ K) ≠ 0 := by
    have h2 := ent_smul h g'⁻¹ (g : G ⧸ K) (g' : G ⧸ K)
    have h3 : g'⁻¹ • (g : G ⧸ K) = ((g'⁻¹ * g : G) : G ⧸ K) := rfl
    have h4 : g'⁻¹ • (g' : G ⧸ K) = ((1 : G) : G ⧸ K) := by
      show ((g'⁻¹ * g' : G) : G ⧸ K) = _
      simp
    rw [h3, h4] at h2
    rw [h2]
    exact hz
  set a : G ⧸ K := ((g'⁻¹ * g : G) : G ⧸ K) with ha
  have haA : a ∈ A := Finsupp.mem_support_iff.2 h1
  have hk : (Quotient.out a : G)⁻¹ * (g'⁻¹ * g) ∈ K := QuotientGroup.eq.1 (QuotientGroup.out_eq' a)
  simp only [Set.mem_iUnion]
  refine ⟨a, haA, ?_⟩
  refine ⟨(⟨((Quotient.out a : G)⁻¹ * (g'⁻¹ * g))⁻¹, K.inv_mem hk⟩ : K) • (((Quotient.out a)⁻¹ : G) : G ⧸ K),
    MulAction.mem_orbit _ _, ?_⟩
  show ((g * (((Quotient.out a : G)⁻¹ * (g'⁻¹ * g))⁻¹ * (Quotient.out a)⁻¹) : G) : G ⧸ K) = _
  congr 1
  group

def rowF (hp : IsHeckePair K) (h : Hk K) (x : G ⧸ K) : (G ⧸ K) →₀ ℂ :=
  Finsupp.ofSupportFinite (fun z => conj (ent h.1 x z)) ((row_finite hp h x).subset fun z hz => by
    simpa using hz)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rowF_apply (hp : IsHeckePair K) (h : Hk K) (x z : G ⧸ K) :
    rowF hp h x z = conj (ent h.1 x z) := rfl

/- English proof (translation)
Use extensionality with `z`. Take `⟨z', rfl⟩ : ∃ z', g • z' = z` from `⟨g⁻¹ • z, smul_inv_smul g z⟩`. Rewrite using `[lam_apply_smul, rowF_apply, rowF_apply, ent_smul]`.
-/
theorem lam_rowF (hp : IsHeckePair K) (h : Hk K) (g : G) (x : G ⧸ K) :
    lam K g (rowF hp h x) = rowF hp h (g • x) := by
  ext z
  obtain ⟨z', rfl⟩ : ∃ z', g • z' = z := ⟨g⁻¹ • z, smul_inv_smul g z⟩
  rw [lam_apply_smul, rowF_apply, rowF_apply, ent_smul]

def starH (hp : IsHeckePair K) (h : Hk K) : Hk K :=
  ⟨Finsupp.linearCombination ℂ (rowF hp h), by
    refine (Subalgebra.mem_centralizer_iff ℂ).2 ?_
    rintro _ ⟨g, rfl⟩
    refine Finsupp.lhom_ext fun a b => ?_
    simp only [Module.End.mul_apply, Finsupp.linearCombination_single, lam_single, map_smul, lam_rowF]⟩

/- English proof (translation)
Simplify using `[starH]`.
-/
theorem starH_single (hp : IsHeckePair K) (h : Hk K) (x : G ⧸ K) :
    (starH hp h).1 (Finsupp.single x 1) = rowF hp h x := by
  simp [starH]

end Hecke

section Form

variable {G : Type} [Group G] {K : Subgroup G}

/- English proof (translation)
Proceed by induction on `f using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb`. Rewrite using `[map_add, inner_add_right, ha, hb, Finsupp.sum_add_index' (by simp) (by intros; ring)]`. Consider the case `single z c`.

Establish `hs : Finsupp.single z c = c • Finsupp.single z (1 : ℂ)` using `by simp`. Rewrite using `[Finsupp.sum_single_index (by simp), hs, map_smul, inner_smul_right, hφ]`.
-/
theorem inner_phi {N : ℕ} (Γ : Subgroup G) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hφ : ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ))
    (x : G ⧸ K) (f : (G ⧸ K) →₀ ℂ) :
    ⟪φ (Finsupp.single x 1), φ f⟫_ℂ = f.sum fun z c => c * (cnt Γ x z : ℂ) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, inner_add_right, ha, hb, Finsupp.sum_add_index' (by simp) (by intros; ring)]
  | single z c =>
    have hs : Finsupp.single z c = c • Finsupp.single z (1 : ℂ) := by simp
    rw [Finsupp.sum_single_index (by simp), hs, map_smul, inner_smul_right, hφ]

/- English proof (translation)
Use `set F := h.1 (Finsupp.single y 1) with hF`. Rewrite using `[starH_single, ← inner_conj_symm (φ (rowF hp h x)), inner_phi Γ φ hφ y, inner_phi Γ φ hφ x, ← finsum_eq, ← finsum_eq]`. Establish `h1 : ∀ γ : Γ, rowF hp h x (γ • y) = conj (F (γ⁻¹ • x))`. Introduce `γ`. Rewrite using `[rowF_apply]`.

Use `congr 1`. Use `ent_smul h (γ : G) ((γ⁻¹ : Γ) • x) y` as an intermediate fact. Establish `h2 : (γ : G) • ((γ⁻¹ : Γ) • x) = x` using `smul_inv_smul γ x`. Rewrite `this` using `[h2]`. Conclude with `this`.

Establish `h3 : ∑ᶠ γ : Γ, rowF hp h x (γ • y) = ∑ᶠ γ : Γ, conj (F (γ • x))`. Simplify using `only [h1]`. Conclude with `finsum_comp_equiv (Equiv.inv Γ) (f := fun γ : Γ => conj (F (γ • x)))`. Rewrite using `[h3]`. Establish `h4` using `AddMonoidHom.map_finsum (starRingEnd ℂ : ℂ →+* ℂ).toAddMonoidHom (support_finite (Γ := Γ) F x)`.

Simplify using `only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h4`. Rewrite using `[← h4]`. Simplify using the standard rewrite rules.
-/
theorem adj_single {N : ℕ} (Γ : Subgroup G) [∀ x : G ⧸ K, Finite (MulAction.stabilizer Γ x)]
    (hp : IsHeckePair K) (h : Hk K) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hφ : ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ)) (x y : G ⧸ K) :
    ⟪φ (Finsupp.single x 1), φ (h.1 (Finsupp.single y 1))⟫_ℂ =
      ⟪φ ((starH hp h).1 (Finsupp.single x 1)), φ (Finsupp.single y 1)⟫_ℂ := by
  set F := h.1 (Finsupp.single y 1) with hF
  rw [starH_single, ← inner_conj_symm (φ (rowF hp h x)), inner_phi Γ φ hφ y, inner_phi Γ φ hφ x,
    ← finsum_eq, ← finsum_eq]
  have h1 : ∀ γ : Γ, rowF hp h x (γ • y) = conj (F (γ⁻¹ • x)) := by
    intro γ
    rw [rowF_apply]
    congr 1
    have := ent_smul h (γ : G) ((γ⁻¹ : Γ) • x) y
    have h2 : (γ : G) • ((γ⁻¹ : Γ) • x) = x := smul_inv_smul γ x
    rw [h2] at this
    exact this
  have h3 : ∑ᶠ γ : Γ, rowF hp h x (γ • y) = ∑ᶠ γ : Γ, conj (F (γ • x)) := by
    simp only [h1]
    exact finsum_comp_equiv (Equiv.inv Γ) (f := fun γ : Γ => conj (F (γ • x)))
  rw [h3]
  have h4 := AddMonoidHom.map_finsum (starRingEnd ℂ : ℂ →+* ℂ).toAddMonoidHom
    (support_finite (Γ := Γ) F x)
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h4
  rw [← h4]
  simp

/- English proof (translation)
Proceed by induction on `v using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, inner_add_right, ha, hb]`. Consider the case `single y c`. Establish `hs : Finsupp.single y c = c • Finsupp.single y (1 : ℂ)` using `by simp`.

Rewrite using `[hs]`. Simplify using `only [map_smul, inner_smul_right]`. Use `congr 1`. Proceed by induction on `u using Finsupp.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, inner_add_left, ha, hb]`. Consider the case `single x d`. Establish `hs' : Finsupp.single x d = d • Finsupp.single x (1 : ℂ)` using `by simp`. Rewrite using `[hs']`. Simplify using `only [map_smul, inner_smul_left]`.

Rewrite using `[adj_single Γ hp h φ hφ]`.
-/
theorem adj {N : ℕ} (Γ : Subgroup G) [∀ x : G ⧸ K, Finite (MulAction.stabilizer Γ x)]
    (hp : IsHeckePair K) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hφ : ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ))
    (h : Hk K) (u v : (G ⧸ K) →₀ ℂ) :
    ⟪φ u, φ (h.1 v)⟫_ℂ = ⟪φ ((starH hp h).1 u), φ v⟫_ℂ := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
  | single y c =>
    have hs : Finsupp.single y c = c • Finsupp.single y (1 : ℂ) := by simp
    rw [hs]
    simp only [map_smul, inner_smul_right]
    congr 1
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]
    | single x d =>
      have hs' : Finsupp.single x d = d • Finsupp.single x (1 : ℂ) := by simp
      rw [hs']
      simp only [map_smul, inner_smul_left]
      rw [adj_single Γ hp h φ hφ]

/- English proof (translation)
Take `⟨σ, hσ⟩` from `φ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)`. Establish `hσ' : ∀ v, φ (σ v) = v` using `fun v => LinearMap.congr_fun hσ v`. Establish `hker : ∀ (h : Hk K) u, φ u = 0 → φ (h.1 u) = 0`. Introduce `h u hu`. Use `hadj h (h.1 u) u` as an intermediate fact.

Rewrite `this` using `[hu, inner_zero_right]`. Conclude with `(inner_self_eq_zero (𝕜 := ℂ)).1 this`. Establish `hdesc : ∀ (h : Hk K) u, φ (h.1 (σ (φ u))) = φ (h.1 u)`. Introduce `h u`. Establish `h1 : φ (σ (φ u) - u) = 0` using `by rw [map_sub, hσ', sub_self]`.

Establish `h2` using `hker h _ h1`. Rewrite `h2` using `[map_sub, map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Set `L : Hk K →ₗ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N))` to `{ toFun := fun h => φ ∘ₗ h.1 ∘ₗ σ map_add' := fun a b => by ext1 v`. Simplify using the standard rewrite rules. Use the proof step `map_smul' := fun c a => by ext1 v`.

Simplify using `}`. Establish `hL : ∀ h u, L h (φ u) = φ (h.1 u)` using `fun h u => hdesc h u`. Set `ρ : Hk K →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N))` to `AlgHom.ofLinearMap L (by ext1 v show φ (σ v) = v`. Conclude with `hσ' v)`. Use the proof step `(fun a b => by ext1 v`.

Take `⟨u, rfl⟩` from `hs v`. Use `show L (a * b) (φ u) = L a (L b (φ u))`. Rewrite using `[hL, hL, hL]`. Use the proof step `rfl)`. Establish `hρ : ∀ h u, ρ h (φ u) = φ (h.1 u)` using `hL`.

Use `⟨ρ, fun h => ⟨starH hp h, fun a b => ?_⟩, hρ⟩` and prove the remaining obligations. Take `⟨u, rfl⟩` from `hs a`. Take `⟨v, rfl⟩` from `hs b`. Rewrite using `[hρ, hρ, ← inner_conj_symm, hadj h v u, inner_conj_symm]`.
-/
theorem exists_rho {N : ℕ} (hp : IsHeckePair K) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hs : Function.Surjective φ)
    (hadj : ∀ (h : Hk K) u v, ⟪φ u, φ (h.1 v)⟫_ℂ = ⟪φ ((starH hp h).1 u), φ v⟫_ℂ) :
    ∃ ρ : Hk K →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N)),
      StarClosed ρ ∧ ∀ h u, ρ h (φ u) = φ (h.1 u) := by
  obtain ⟨σ, hσ⟩ := φ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  have hσ' : ∀ v, φ (σ v) = v := fun v => LinearMap.congr_fun hσ v
  have hker : ∀ (h : Hk K) u, φ u = 0 → φ (h.1 u) = 0 := by
    intro h u hu
    have := hadj h (h.1 u) u
    rw [hu, inner_zero_right] at this
    exact (inner_self_eq_zero (𝕜 := ℂ)).1 this
  have hdesc : ∀ (h : Hk K) u, φ (h.1 (σ (φ u))) = φ (h.1 u) := by
    intro h u
    have h1 : φ (σ (φ u) - u) = 0 := by rw [map_sub, hσ', sub_self]
    have h2 := hker h _ h1
    rwa [map_sub, map_sub, sub_eq_zero] at h2
  let L : Hk K →ₗ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N)) :=
    { toFun := fun h => φ ∘ₗ h.1 ∘ₗ σ
      map_add' := fun a b => by
        ext1 v
        simp
      map_smul' := fun c a => by
        ext1 v
        simp }
  have hL : ∀ h u, L h (φ u) = φ (h.1 u) := fun h u => hdesc h u
  let ρ : Hk K →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N)) := AlgHom.ofLinearMap L
    (by
      ext1 v
      show φ (σ v) = v
      exact hσ' v)
    (fun a b => by
      ext1 v
      obtain ⟨u, rfl⟩ := hs v
      show L (a * b) (φ u) = L a (L b (φ u))
      rw [hL, hL, hL]
      rfl)
  have hρ : ∀ h u, ρ h (φ u) = φ (h.1 u) := hL
  refine ⟨ρ, fun h => ⟨starH hp h, fun a b => ?_⟩, hρ⟩
  obtain ⟨u, rfl⟩ := hs a
  obtain ⟨v, rfl⟩ := hs b
  rw [hρ, hρ, ← inner_conj_symm, hadj h v u, inner_conj_symm]

end Form

/- English proof (translation)
Introduce `G _ K hp hsep h`. Take `⟨Γ, hfin, hstab, hS⟩` from `hsep (h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1)).support`. Take `⟨N, φ, hs, hφ⟩` from `exists_phi (Γ := Γ) (X := G ⧸ K)`. Take `⟨ρ, hstar, hρ⟩` from `exists_rho hp φ hs (adj Γ hp φ hφ)`. Use `⟨N, ρ, hstar, fun h0 => ?_⟩` and prove the remaining obligations.

Use `set f := h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1) with hf`. Establish `hφf : φ f = 0`. Rewrite using `[hf, ← hρ, h0]`. Both sides reduce to the same expression. Establish `hf0 : f = 0`.

Use extensionality with `z`. Assume the negation of the conclusion as `hz`. Establish `hzS : z ∈ f.support` using `Finsupp.mem_support_iff.2 hz`. Establish `h1` using `inner_phi Γ φ hφ z f`. Rewrite `h1` using `[hφf, inner_zero_right, Finsupp.sum, Finset.sum_eq_single z]`.

Establish `h2 : (cnt Γ z z : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (cnt_self_pos z).ne'`. Conclude with `mul_ne_zero hz h2 h1.symm`. Introduce `y hy hyz`. Establish `: IsEmpty {γ : Γ // γ • z = y}` using `⟨fun γ => hyz (hS z hzS y hy γ.1 γ.2).symm⟩`. Establish `h0 : cnt Γ z y = 0` using `Nat.card_of_isEmpty`.

Simplify using `[h0]`. Introduce `hnot`. Conclude with `absurd hzS hnot`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Finsupp.lhom_ext fun a b => ?_` and prove the remaining obligations.

Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective a`. Establish `h1 : Finsupp.single (g : G ⧸ K) b = b • lam K g (Finsupp.single ((1 : G) : G ⧸ K) 1)`. Rewrite using `[lam_single]`. Establish `: g • ((1 : G) : G ⧸ K) = (g : G ⧸ K)` using `by show ((g * 1 : G) : G ⧸ K) = _`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[h1, map_smul, comm_lam, ← hf, hf0]`. Simplify using the standard rewrite rules.
-/
theorem stMod : StMod := by
  intro G _ K hp hsep h
  classical
  obtain ⟨Γ, hfin, hstab, hS⟩ := hsep (h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1)).support
  obtain ⟨N, φ, hs, hφ⟩ := exists_phi (Γ := Γ) (X := G ⧸ K)
  obtain ⟨ρ, hstar, hρ⟩ := exists_rho hp φ hs (adj Γ hp φ hφ)
  refine ⟨N, ρ, hstar, fun h0 => ?_⟩
  set f := h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1) with hf
  have hφf : φ f = 0 := by
    rw [hf, ← hρ, h0]
    rfl
  have hf0 : f = 0 := by
    ext z
    by_contra hz
    have hzS : z ∈ f.support := Finsupp.mem_support_iff.2 hz
    have h1 := inner_phi Γ φ hφ z f
    rw [hφf, inner_zero_right, Finsupp.sum, Finset.sum_eq_single z] at h1
    · have h2 : (cnt Γ z z : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (cnt_self_pos z).ne'
      exact mul_ne_zero hz h2 h1.symm
    · intro y hy hyz
      have : IsEmpty {γ : Γ // γ • z = y} := ⟨fun γ => hyz (hS z hzS y hy γ.1 γ.2).symm⟩
      have h0 : cnt Γ z y = 0 := Nat.card_of_isEmpty
      simp [h0]
    · intro hnot
      exact absurd hzS hnot
  apply Subtype.ext
  refine Finsupp.lhom_ext fun a b => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  have h1 : Finsupp.single (g : G ⧸ K) b = b • lam K g (Finsupp.single ((1 : G) : G ⧸ K) 1) := by
    rw [lam_single]
    have : g • ((1 : G) : G ⧸ K) = (g : G ⧸ K) := by
      show ((g * 1 : G) : G ⧸ K) = _
      simp
    rw [this]
    simp
  rw [h1, map_smul, comm_lam, ← hf, hf0]
  simp

end GlobalTheory.CompanionTheory.HeckeCoinv

end
