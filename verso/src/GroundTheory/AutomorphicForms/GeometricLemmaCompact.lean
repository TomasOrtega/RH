import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemmaOrbit
import GroundTheory.AutomorphicForms.AdmissibleInduction
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Bounds

variable (F) in

abbrev EntryBound (e : ℕ) (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, (uniformizer F : F) ^ e * A i j ∈ 𝒪[F]

/- English proof (translation)
Introduce `i j`. Rewrite using `[mul_apply, Finset.mul_sum]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Use `mul_mem (hA i k) (hB k j)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem EntryBound.mul {a b : ℕ} {A B : Matrix (Fin n) (Fin n) F} (hA : EntryBound F a A)
    (hB : EntryBound F b B) : EntryBound F (a + b) (A * B) := by
  intro i j
  rw [mul_apply, Finset.mul_sum]
  refine sum_mem fun k _ => ?_
  have := mul_mem (hA i k) (hB k j)
  convert this using 1
  ring

/- English proof (translation)
Take `⟨e, he⟩` from `exists_pow_mul_mem_of_isCompact F n (hS.union (hS.image continuous_inv))`. Conclude with `⟨e, fun g hg => ⟨fun i j => he g (Or.inl hg) i j, fun i j => he g⁻¹ (Or.inr ⟨g, hg, rfl⟩) i j⟩⟩`.
-/
theorem entryBound_of_isCompact {S : Set (GL (Fin n) F)} (hS : IsCompact S) :
    ∃ e : ℕ, ∀ g ∈ S, EntryBound F e (g : Matrix (Fin n) (Fin n) F) ∧
      EntryBound F e ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨e, he⟩ := exists_pow_mul_mem_of_isCompact F n (hS.union (hS.image continuous_inv))
  exact ⟨e, fun g hg => ⟨fun i j => he g (Or.inl hg) i j,
    fun i j => he g⁻¹ (Or.inr ⟨g, hg, rfl⟩) i j⟩⟩

/- English proof (translation)
Introduce `i j`. Rewrite using `[leviProj_apply]`. Use `split_ifs`. Conclude with `hp i j`. Rewrite using `[mul_zero]`.

Conclude with `zero_mem _`.
-/
theorem EntryBound.leviProj {γ : Fin n → ℕ} {e : ℕ} {p : blockUpper F n γ}
    (hp : EntryBound F e ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    EntryBound F e (((leviProj F n γ p : levi F n γ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  intro i j
  rw [leviProj_apply]
  split_ifs
  · exact hp i j
  · rw [mul_zero]
    exact zero_mem _

end Bounds

section UnipotentCompact

variable (γ : Fin n → ℕ)

def unipotentCompactG (e : ℕ) : Subgroup (GL (Fin n) F) :=
  (unipotentCompact F n γ e).map (unipotentRadical F n γ).subtype

variable {γ}

/- English proof (translation)
Introduce and unpack `_ ⟨u, -, rfl⟩`. Conclude with `u.2`.
-/
theorem unipotentCompactG_le (e : ℕ) :
    unipotentCompactG (F := F) γ e ≤ unipotentRadical F n γ := by
  rintro _ ⟨u, -, rfl⟩
  exact u.2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `⟨v.2, mem_unipotentCompact.1 hv⟩`. Introduce and unpack `⟨hu, h⟩`. Conclude with `⟨⟨u, hu⟩, mem_unipotentCompact.2 h, rfl⟩`.
-/
theorem mem_unipotentCompactG {e : ℕ} {u : GL (Fin n) F} :
    u ∈ unipotentCompactG γ e ↔ u ∈ unipotentRadical F n γ ∧
      rankTorus F n γ e * u * (rankTorus F n γ e)⁻¹ ∈ integralGL F n := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, mem_unipotentCompact.1 hv⟩
  · rintro ⟨hu, h⟩
    exact ⟨⟨u, hu⟩, mem_unipotentCompact.2 h, rfl⟩

/- English proof (translation)
Rewrite using `[unipotentCompactG, Subgroup.coe_map]`. Conclude with `(isCompact_unipotentCompact e).image continuous_subtype_val`.
-/
theorem isCompact_unipotentCompactG (e : ℕ) :
    IsCompact (unipotentCompactG (F := F) γ e : Set (GL (Fin n) F)) := by
  rw [unipotentCompactG, Subgroup.coe_map]
  exact (isCompact_unipotentCompact e).image continuous_subtype_val

/- English proof (translation)
Use extensionality with `u`. Rewrite using `[mem_unipotentCompactG, Subgroup.mem_inf, Subgroup.mem_comap]`. Both sides reduce to the same expression.
-/
theorem unipotentCompactG_eq (e : ℕ) :
    unipotentCompactG (F := F) γ e = unipotentRadical F n γ ⊓
      (integralGL F n).comap (MulAut.conj (rankTorus F n γ e)).toMonoidHom := by
  ext u
  rw [mem_unipotentCompactG, Subgroup.mem_inf, Subgroup.mem_comap]
  rfl

/- English proof (translation)
The claim follows from `(isOpen_integralGL F n).preimage (conjHomeomorph t).continuous`.
-/
theorem isOpen_conj_integralGL (t : GL (Fin n) F) :
    IsOpen (((integralGL F n).comap (MulAut.conj t).toMonoidHom : Subgroup (GL (Fin n) F)) :
      Set (GL (Fin n) F)) :=
  (isOpen_integralGL F n).preimage (conjHomeomorph t).continuous

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨u, hu⟩, mem_unipotentCompact_of_bound (u := ⟨u, hu⟩) hb hb', rfl⟩`.
-/
theorem mem_unipotentCompactG_of_bound {e : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ unipotentRadical F n γ)
    (hb : EntryBound F e (u : Matrix (Fin n) (Fin n) F))
    (hb' : EntryBound F e ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    u ∈ unipotentCompactG γ e :=
  ⟨⟨u, hu⟩, mem_unipotentCompact_of_bound (u := ⟨u, hu⟩) hb hb', rfl⟩

/- English proof (translation)
Introduce `u hu`. Take `⟨huN, hu'⟩` from `mem_unipotentCompactG.1 hu`. Use `mem_unipotentCompactG.2 ⟨huN, ?_⟩` and prove the remaining obligations. Establish `key : ∀ v ∈ unipotentRadical F n γ, (rankTorus F n γ e * v * (rankTorus F n γ e)⁻¹ : GL (Fin n) F) ∈ integralGL F n → ∀ i j, ((rankTorus F n γ e' * v * (rankTorus F n γ e')⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]`. Introduce `v hv hint i j`.

Establish `hij` using `((mem_integralGL_iff F n).1 hint).1 i j`. Rewrite `hij`, the goal using `[rankTorus_conj_apply]`. Take `⟨hvP, hv1⟩` from `mem_unipotentRadical.1 hv`. Break down `lt_trichotomy (γ i) (γ j) with hlt | heq | hgt` into its components or cases. Establish `hr` using `blockRank_lt hlt`.

Establish `: (((e' * blockRank γ j : ℕ) : ℤ) - ((e' * blockRank γ i : ℕ) : ℤ)) = (((e * blockRank γ j : ℕ) : ℤ) - ((e * blockRank γ i : ℕ) : ℤ)) + (((e' - e) * (blockRank γ j - blockRank γ i) : ℕ) : ℤ)`. Move the coercions through the operations in `[Nat.cast_sub h, Nat.cast_sub hr.le]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, zpow_add₀ uniformizer_ne_zero, zpow_natCast]`. Establish `e1 : ((GLnLocal.uniformizer F : F) ^ ((((e * blockRank γ j : ℕ) : ℤ) - ((e * blockRank γ i : ℕ) : ℤ))) * (GLnLocal.uniformizer F : F) ^ ((e' - e) * (blockRank γ j - blockRank γ i))) * (v : Matrix (Fin n) (Fin n) F) i j = ((GLnLocal.uniformizer F : F) ^ ((((e * blockRank γ j : ℕ) …`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `mul_mem hij (pow_mem (GLnLocal.uniformizer F).2 _)`. Rewrite `hij`, the goal using `[blockRank_eq heq, sub_self]`. Conclude with `hij`.

Rewrite using `[hvP hgt, mul_zero]`. Conclude with `zero_mem _`. Rewrite using `[mem_integralGL_iff F n]`. Use `⟨key u huN hu', ?_⟩` and prove the remaining obligations. Introduce `i j`.

Establish `: (rankTorus F n γ e' * u * (rankTorus F n γ e')⁻¹)⁻¹ = rankTorus F n γ e' * u⁻¹ * (rankTorus F n γ e')⁻¹` using `by group`. Rewrite using `[this]`. Establish `h' : (rankTorus F n γ e * u * (rankTorus F n γ e)⁻¹)⁻¹ = rankTorus F n γ e * u⁻¹ * (rankTorus F n γ e)⁻¹` using `by group`. Establish `hinv` using `(integralGL F n).inv_mem hu'`. Rewrite `hinv` using `[h']`.

Conclude with `key u⁻¹ ((unipotentRadical F n γ).inv_mem huN) hinv i j`.
-/
theorem unipotentCompactG_mono {e e' : ℕ} (h : e ≤ e') :
    unipotentCompactG (F := F) γ e ≤ unipotentCompactG γ e' := by
  intro u hu
  obtain ⟨huN, hu'⟩ := mem_unipotentCompactG.1 hu
  refine mem_unipotentCompactG.2 ⟨huN, ?_⟩
  have key : ∀ v ∈ unipotentRadical F n γ,
      (rankTorus F n γ e * v * (rankTorus F n γ e)⁻¹ : GL (Fin n) F) ∈ integralGL F n →
        ∀ i j, ((rankTorus F n γ e' * v * (rankTorus F n γ e')⁻¹ : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
    intro v hv hint i j
    have hij := ((mem_integralGL_iff F n).1 hint).1 i j
    rw [rankTorus_conj_apply] at hij ⊢
    obtain ⟨hvP, hv1⟩ := mem_unipotentRadical.1 hv
    rcases lt_trichotomy (γ i) (γ j) with hlt | heq | hgt
    · have hr := blockRank_lt hlt
      have : (((e' * blockRank γ j : ℕ) : ℤ) - ((e' * blockRank γ i : ℕ) : ℤ)) =
          (((e * blockRank γ j : ℕ) : ℤ) - ((e * blockRank γ i : ℕ) : ℤ)) +
            (((e' - e) * (blockRank γ j - blockRank γ i) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub h, Nat.cast_sub hr.le]
        ring
      rw [this, zpow_add₀ uniformizer_ne_zero, zpow_natCast]
      have e1 : ((GLnLocal.uniformizer F : F) ^ ((((e * blockRank γ j : ℕ) : ℤ) -
          ((e * blockRank γ i : ℕ) : ℤ))) *
            (GLnLocal.uniformizer F : F) ^ ((e' - e) * (blockRank γ j - blockRank γ i))) *
              (v : Matrix (Fin n) (Fin n) F) i j =
          ((GLnLocal.uniformizer F : F) ^ ((((e * blockRank γ j : ℕ) : ℤ) -
            ((e * blockRank γ i : ℕ) : ℤ))) * (v : Matrix (Fin n) (Fin n) F) i j) *
            (GLnLocal.uniformizer F : F) ^ ((e' - e) * (blockRank γ j - blockRank γ i)) := by
        ring
      rw [e1]
      exact mul_mem hij (pow_mem (GLnLocal.uniformizer F).2 _)
    · rw [blockRank_eq heq, sub_self] at hij ⊢
      exact hij
    · rw [hvP hgt, mul_zero]
      exact zero_mem _
  rw [mem_integralGL_iff F n]
  refine ⟨key u huN hu', ?_⟩
  intro i j
  have : (rankTorus F n γ e' * u * (rankTorus F n γ e')⁻¹)⁻¹ =
      rankTorus F n γ e' * u⁻¹ * (rankTorus F n γ e')⁻¹ := by group
  rw [this]
  have h' : (rankTorus F n γ e * u * (rankTorus F n γ e)⁻¹)⁻¹ =
      rankTorus F n γ e * u⁻¹ * (rankTorus F n γ e)⁻¹ := by group
  have hinv := (integralGL F n).inv_mem hu'
  rw [h'] at hinv
  exact key u⁻¹ ((unipotentRadical F n γ).inv_mem huN) hinv i j

end UnipotentCompact

section Support

variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

/- English proof (translation)
Take `⟨-, K, hKo, hK⟩` from `(mem_parabolicIndSpace σ).1 f.2`. Establish `hnhds : ∀ g : GL (Fin n) F, (fun k => g * k) '' (K : Set (GL (Fin n) F)) ∈ 𝓝 g`. Introduce `g`. Use `(isOpenMap_mul_left g).image_mem_nhds (hKo.mem_nhds K.one_mem)` as an intermediate fact. Simplify using `using this`.

Establish `hval : ∀ g, ∀ x ∈ (fun k => g * k) '' (K : Set (GL (Fin n) F)), (f : GL (Fin n) F → W) x = (f : GL (Fin n) F → W) g`. Introduce and unpack `g _ ⟨k, hk, rfl⟩`. Conclude with `hK k hk g`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`.

Introduce `g hg`. Use `Filter.mem_of_superset (hnhds g) fun x hx => ?_` and prove the remaining obligations. Simplify using `only [mem_compl_iff, mem_ofPred_eq, not_not] at hg ⊢`. Rewrite using `[hval g x hx, hg]`. Rewrite using `[isOpen_iff_mem_nhds]`.

Introduce `g hg`. Use `Filter.mem_of_superset (hnhds g) fun x hx => ?_` and prove the remaining obligations. Simplify using `only [mem_ofPred_eq] at hg ⊢`. Rewrite using `[hval g x hx]`. Conclude with `hg`.
-/
theorem isClopen_support_parabolicInd (f : parabolicIndSpace F n β σ) :
    IsClopen {g : GL (Fin n) F | (f : GL (Fin n) F → W) g ≠ 0} := by
  obtain ⟨-, K, hKo, hK⟩ := (mem_parabolicIndSpace σ).1 f.2
  have hnhds : ∀ g : GL (Fin n) F, (fun k => g * k) '' (K : Set (GL (Fin n) F)) ∈ 𝓝 g := by
    intro g
    have := (isOpenMap_mul_left g).image_mem_nhds (hKo.mem_nhds K.one_mem)
    simpa using this
  have hval : ∀ g, ∀ x ∈ (fun k => g * k) '' (K : Set (GL (Fin n) F)),
      (f : GL (Fin n) F → W) x = (f : GL (Fin n) F → W) g := by
    rintro g _ ⟨k, hk, rfl⟩
    exact hK k hk g
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro g hg
    refine Filter.mem_of_superset (hnhds g) fun x hx => ?_
    simp only [mem_compl_iff, mem_ofPred_eq, not_not] at hg ⊢
    rw [hval g x hx, hg]
  · rw [isOpen_iff_mem_nhds]
    intro g hg
    refine Filter.mem_of_superset (hnhds g) fun x hx => ?_
    simp only [mem_ofPred_eq] at hg ⊢
    rw [hval g x hx]
    exact hg

variable (w : Equiv.Perm (Fin n))

/- English proof (translation)
Use `set C := doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)`. Use `set S := {g : GL (Fin n) F | (f : GL (Fin n) F → W) g ≠ 0}`. Establish `hS` using `isClopen_support_parabolicInd f`. Establish `hSY : S ⊆ Y` using `fun g hg => by`. Assume the negation of the conclusion as `hgY`.

Conclude with `hg (hf g hgY)`. Use `set Kc := (integralGL F n : Set (GL (Fin n) F)) ∩ (S ∩ closure C)`. Establish `hKc : IsCompact Kc` using `(isCompact_integralGL F n).inter_right (hS.1.inter isClosed_closure)`. Establish `hKcC : Kc ⊆ C`. Introduce and unpack `g ⟨-, hgS, hgC⟩`.

Rewrite using `[← hCY]`. Conclude with `⟨hgC, hSY hgS⟩`. Establish `hCl : IsLocallyClosed C` using `⟨Y, closure C, hYo, isClosed_closure, by rw [inter_comm, hCY]⟩`. Take `⟨L, hL, hLQ, hKL⟩` from `exists_isCompact_subset_doubleCoset (Measures.isClosed_blockUpper F n β) (Measures.isClosed_blockUpper F n γ) hCl hKc hKcC`. Use `⟨L, hL, hLQ, fun q hq hfq => ?_⟩` and prove the remaining obligations.

Take `⟨p, hp, k, hk, hpk⟩` from `exists_blockUpper_mul_integralGL' (β := β) (permGL F w * q)`. Establish `hfk : (f : GL (Fin n) F → W) k ≠ 0`. Introduce `h0`. Apply `hfq` to reduce the goal to its premises. Rewrite using `[hpk, ((mem_parabolicIndSpace σ).1 f.2).1 ⟨p, hp⟩ k, h0, map_zero, smul_zero]`.

Establish `hkC : k ∈ C`. Use `mem_doubleCoset.2 ⟨p⁻¹, (blockUpper F n β).inv_mem hp, q, hq, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, hpk, inv_mul_cancel_left]`. Take `⟨p', hp', l, hl, hkl⟩` from `hKL k ⟨hk, hfk, subset_closure hkC⟩`. Use `⟨q * l⁻¹, (blockUpper F n γ).mul_mem hq ((blockUpper F n γ).inv_mem (hLQ hl)), ?_, l, hl, by group⟩` and prove the remaining obligations.

Establish `: permGL F w * (q * l⁻¹) * (permGL F w)⁻¹ = p * p'`. Establish `h1 : permGL F w * q = p * (p' * permGL F w * l)` using `by rw [hpk, hkl]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Conclude with `(blockUpper F n β).mul_mem hp hp'`.
-/
theorem exists_isCompact_support_doubleCoset {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) :
    ∃ L : Set (GL (Fin n) F), IsCompact L ∧ L ⊆ blockUpper F n γ ∧
      ∀ q ∈ blockUpper F n γ, (f : GL (Fin n) F → W) (permGL F w * q) ≠ 0 →
        ∃ x ∈ blockUpper F n γ, permGL F w * x * (permGL F w)⁻¹ ∈ blockUpper F n β ∧
          ∃ l ∈ L, q = x * l := by
  set C := doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)
  set S := {g : GL (Fin n) F | (f : GL (Fin n) F → W) g ≠ 0}
  have hS := isClopen_support_parabolicInd f
  have hSY : S ⊆ Y := fun g hg => by
    by_contra hgY
    exact hg (hf g hgY)
  set Kc := (integralGL F n : Set (GL (Fin n) F)) ∩ (S ∩ closure C)
  have hKc : IsCompact Kc := (isCompact_integralGL F n).inter_right (hS.1.inter isClosed_closure)
  have hKcC : Kc ⊆ C := by
    rintro g ⟨-, hgS, hgC⟩
    rw [← hCY]
    exact ⟨hgC, hSY hgS⟩
  have hCl : IsLocallyClosed C := ⟨Y, closure C, hYo, isClosed_closure, by rw [inter_comm, hCY]⟩
  obtain ⟨L, hL, hLQ, hKL⟩ := exists_isCompact_subset_doubleCoset
    (Measures.isClosed_blockUpper F n β) (Measures.isClosed_blockUpper F n γ) hCl hKc hKcC
  refine ⟨L, hL, hLQ, fun q hq hfq => ?_⟩
  obtain ⟨p, hp, k, hk, hpk⟩ := exists_blockUpper_mul_integralGL' (β := β) (permGL F w * q)
  have hfk : (f : GL (Fin n) F → W) k ≠ 0 := by
    intro h0
    apply hfq
    rw [hpk, ((mem_parabolicIndSpace σ).1 f.2).1 ⟨p, hp⟩ k, h0, map_zero, smul_zero]
  have hkC : k ∈ C := by
    refine mem_doubleCoset.2 ⟨p⁻¹, (blockUpper F n β).inv_mem hp, q, hq, ?_⟩
    rw [mul_assoc, hpk, inv_mul_cancel_left]
  obtain ⟨p', hp', l, hl, hkl⟩ := hKL k ⟨hk, hfk, subset_closure hkC⟩
  refine ⟨q * l⁻¹, (blockUpper F n γ).mul_mem hq ((blockUpper F n γ).inv_mem (hLQ hl)), ?_, l, hl,
    by group⟩
  have : permGL F w * (q * l⁻¹) * (permGL F w)⁻¹ = p * p' := by
    have h1 : permGL F w * q = p * (p' * permGL F w * l) := by rw [hpk, hkl]
    calc permGL F w * (q * l⁻¹) * (permGL F w)⁻¹
        = (permGL F w * q) * l⁻¹ * (permGL F w)⁻¹ := by group
      _ = p * p' := by rw [h1]; group
  rw [this]
  exact (blockUpper F n β).mul_mem hp hp'

/- English proof (translation)
Take `⟨L, hL, hLQ, hsupp⟩` from `exists_isCompact_support_doubleCoset w hYo hCY hf`. Take `⟨e₀, he₀⟩` from `entryBound_of_isCompact hL`. Take `⟨e₁, he₁⟩` from `entryBound_of_isCompact (isCompact_singleton (x := m))`. Take `⟨hmb, hmb'⟩` from `he₁ m rfl`. Use `⟨e₁ + e₀ + e₀ + e₁, fun u hu hfu => ?_⟩` and prove the remaining obligations.

Establish `hmQ : m ∈ blockUpper F n γ` using `levi_le_blockUpper hm`. Establish `huQ : u ∈ blockUpper F n γ` using `unipotentRadical_le_blockUpper hu`. Take `⟨x, hxQ, hxP, l, hl, hum⟩` from `hsupp (u * m) ((blockUpper F n γ).mul_mem huQ hmQ) (by rwa [← mul_assoc])`. Establish `hlQ` using `hLQ hl`. Use `set b : levi F n γ := leviProj F n γ ⟨x, hxQ⟩`.

Use `set c : levi F n γ := leviProj F n γ ⟨l, hlQ⟩`. Establish `hbc : (b : GL (Fin n) F) = m * (c : GL (Fin n) F)⁻¹`. Establish `h1 : leviProj F n γ ⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ = b * c`. Rewrite using `[← map_mul]`. Use `congr 1`.

Conclude with `Subtype.ext hum`. Establish `h2 : leviProj F n γ ⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ = ⟨m, hm⟩`. Establish `: (⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ : blockUpper F n γ) = ⟨u, huQ⟩ * ⟨m, hmQ⟩` using `rfl`. Rewrite using `[this, map_mul, (mem_unipotentRadical_iff_leviProj (p := ⟨u, huQ⟩)).1 hu, one_mul]`. Conclude with `leviProj_of_mem_levi hm`.

Rewrite `h1` using `[h2]`. Use `congrArg (fun z : levi F n γ => (z : GL (Fin n) F)) h1` as an intermediate fact. Simplify using `only [Subgroup.coe_mul] at this`. Rewrite using `[this]`. Use `group`.

Establish `hbQ : (b : GL (Fin n) F) ∈ blockUpper F n γ` using `levi_le_blockUpper b.2`. Establish `haQ : x * (b : GL (Fin n) F)⁻¹ ∈ blockUpper F n γ` using `(blockUpper F n γ).mul_mem hxQ ((blockUpper F n γ).inv_mem hbQ)`. Establish `haN : x * (b : GL (Fin n) F)⁻¹ ∈ unipotentRadical F n γ`. Rewrite using `[show x * (b : GL (Fin n) F)⁻¹ = ((⟨x, hxQ⟩ * (leviIncl b)⁻¹ : blockUpper F n γ) : GL (Fin n) F) from rfl, mem_unipotentRadical_iff_leviProj, map_mul, map_inv, leviProj_leviIncl, mul_inv_cancel]`. Establish `hxβ : x ∈ blockUpper F n (β ∘ w)` using `(conj_permGL_mem_blockUpper_iff w).1 hxP`.

Establish `hbβ : (b : GL (Fin n) F) ∈ blockUpper F n (β ∘ w)`. Introduce `i j hij`. Use `show ((leviProj F n γ ⟨x, hxQ⟩ : levi F n γ) : GL (Fin n) F) i j = 0`. Rewrite using `[leviProj_apply]`. Use `split_ifs`.

Conclude with `hxβ hij`. Both sides reduce to the same expression. Use `⟨x * (b : GL (Fin n) F)⁻¹, haN, (conj_permGL_mem_blockUpper_iff w).2 ((blockUpper F n (β ∘ w)).mul_mem hxβ ((blockUpper F n (β ∘ w)).inv_mem hbβ)), (b : GL (Fin n) F) * l * m⁻¹, ?_, ?_⟩` and prove the remaining obligations. Establish `hv : (b : GL (Fin n) F) * l * m⁻¹ = m * (c : GL (Fin n) F)⁻¹ * l * m⁻¹` using `by rw [hbc]`. Establish `hvN : (b : GL (Fin n) F) * l * m⁻¹ ∈ unipotentRadical F n γ`.

Establish `: (b : GL (Fin n) F) * l * m⁻¹ = (x * (b : GL (Fin n) F)⁻¹)⁻¹ * u`. Rewrite using `[show u = x * l * m⁻¹ by rw [← hum]; group]`. Use `group`. Rewrite using `[this]`. Conclude with `(unipotentRadical F n γ).mul_mem ((unipotentRadical F n γ).inv_mem haN) hu`.

Take `⟨hlb, hlb'⟩` from `he₀ l hl`. Establish `hcinv : ((c : GL (Fin n) F)⁻¹ : GL (Fin n) F) = ((leviProj F n γ ⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩ : levi F n γ) : GL (Fin n) F)`. Rewrite using `[show (⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩ : blockUpper F n γ) = (⟨l, hlQ⟩)⁻¹ from rfl, map_inv]`. Both sides reduce to the same expression. Establish `hcb' : EntryBound F e₀ (((c : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)`.

Rewrite using `[hcinv]`. Conclude with `EntryBound.leviProj (p := ⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩) hlb'`. Establish `hcb : EntryBound F e₀ ((c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)` using `EntryBound.leviProj (p := ⟨l, hlQ⟩) hlb`. Use `mem_unipotentCompactG_of_bound hvN ?_ ?_` and prove the remaining obligations. Rewrite using `[hv]`.

Simplify using `only [Units.val_mul]`. Conclude with `((hmb.mul hcb').mul hlb).mul hmb'`. Establish `: ((b : GL (Fin n) F) * l * m⁻¹)⁻¹ = m * l⁻¹ * (c : GL (Fin n) F) * m⁻¹`. Rewrite using `[hbc]`. Use `group`.

Rewrite using `[this]`. Simplify using `only [Units.val_mul]`. Conclude with `((hmb.mul hlb').mul hcb).mul hmb'`. Rewrite using `[show u = x * l * m⁻¹ by rw [← hum]; group] group`.
-/
theorem exists_unipotentCompactG_support {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) {m : GL (Fin n) F}
    (hm : m ∈ levi F n γ) :
    ∃ e : ℕ, ∀ u ∈ unipotentRadical F n γ, (f : GL (Fin n) F → W) (permGL F w * u * m) ≠ 0 →
      ∃ a ∈ unipotentRadical F n γ, permGL F w * a * (permGL F w)⁻¹ ∈ blockUpper F n β ∧
        ∃ v ∈ unipotentCompactG γ e, u = a * v := by
  obtain ⟨L, hL, hLQ, hsupp⟩ := exists_isCompact_support_doubleCoset w hYo hCY hf
  obtain ⟨e₀, he₀⟩ := entryBound_of_isCompact hL
  obtain ⟨e₁, he₁⟩ := entryBound_of_isCompact (isCompact_singleton (x := m))
  obtain ⟨hmb, hmb'⟩ := he₁ m rfl
  refine ⟨e₁ + e₀ + e₀ + e₁, fun u hu hfu => ?_⟩
  have hmQ : m ∈ blockUpper F n γ := levi_le_blockUpper hm
  have huQ : u ∈ blockUpper F n γ := unipotentRadical_le_blockUpper hu
  obtain ⟨x, hxQ, hxP, l, hl, hum⟩ := hsupp (u * m) ((blockUpper F n γ).mul_mem huQ hmQ)
    (by rwa [← mul_assoc])
  have hlQ := hLQ hl

  set b : levi F n γ := leviProj F n γ ⟨x, hxQ⟩
  set c : levi F n γ := leviProj F n γ ⟨l, hlQ⟩
  have hbc : (b : GL (Fin n) F) = m * (c : GL (Fin n) F)⁻¹ := by
    have h1 : leviProj F n γ ⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ = b * c := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hum
    have h2 : leviProj F n γ ⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ = ⟨m, hm⟩ := by
      have : (⟨u * m, (blockUpper F n γ).mul_mem huQ hmQ⟩ : blockUpper F n γ) =
          ⟨u, huQ⟩ * ⟨m, hmQ⟩ := rfl
      rw [this, map_mul, (mem_unipotentRadical_iff_leviProj (p := ⟨u, huQ⟩)).1 hu, one_mul]
      exact leviProj_of_mem_levi hm
    rw [h2] at h1
    have := congrArg (fun z : levi F n γ => (z : GL (Fin n) F)) h1
    simp only [Subgroup.coe_mul] at this
    rw [this]
    group

  have hbQ : (b : GL (Fin n) F) ∈ blockUpper F n γ := levi_le_blockUpper b.2
  have haQ : x * (b : GL (Fin n) F)⁻¹ ∈ blockUpper F n γ :=
    (blockUpper F n γ).mul_mem hxQ ((blockUpper F n γ).inv_mem hbQ)
  have haN : x * (b : GL (Fin n) F)⁻¹ ∈ unipotentRadical F n γ := by
    rw [show x * (b : GL (Fin n) F)⁻¹ = ((⟨x, hxQ⟩ * (leviIncl b)⁻¹ : blockUpper F n γ) :
      GL (Fin n) F) from rfl, mem_unipotentRadical_iff_leviProj, map_mul, map_inv,
      leviProj_leviIncl, mul_inv_cancel]
  have hxβ : x ∈ blockUpper F n (β ∘ w) := (conj_permGL_mem_blockUpper_iff w).1 hxP
  have hbβ : (b : GL (Fin n) F) ∈ blockUpper F n (β ∘ w) := by
    intro i j hij
    show ((leviProj F n γ ⟨x, hxQ⟩ : levi F n γ) : GL (Fin n) F) i j = 0
    rw [leviProj_apply]
    split_ifs
    · exact hxβ hij
    · rfl
  refine ⟨x * (b : GL (Fin n) F)⁻¹, haN, (conj_permGL_mem_blockUpper_iff w).2
    ((blockUpper F n (β ∘ w)).mul_mem hxβ ((blockUpper F n (β ∘ w)).inv_mem hbβ)),
    (b : GL (Fin n) F) * l * m⁻¹, ?_, ?_⟩
  · have hv : (b : GL (Fin n) F) * l * m⁻¹ = m * (c : GL (Fin n) F)⁻¹ * l * m⁻¹ := by rw [hbc]
    have hvN : (b : GL (Fin n) F) * l * m⁻¹ ∈ unipotentRadical F n γ := by
      have : (b : GL (Fin n) F) * l * m⁻¹ = (x * (b : GL (Fin n) F)⁻¹)⁻¹ * u := by
        rw [show u = x * l * m⁻¹ by rw [← hum]; group]
        group
      rw [this]
      exact (unipotentRadical F n γ).mul_mem ((unipotentRadical F n γ).inv_mem haN) hu
    obtain ⟨hlb, hlb'⟩ := he₀ l hl
    have hcinv : ((c : GL (Fin n) F)⁻¹ : GL (Fin n) F) =
        ((leviProj F n γ ⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩ : levi F n γ) : GL (Fin n) F) := by
      rw [show (⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩ : blockUpper F n γ) = (⟨l, hlQ⟩)⁻¹ from rfl,
        map_inv]
      rfl
    have hcb' : EntryBound F e₀ (((c : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [hcinv]
      exact EntryBound.leviProj (p := ⟨l⁻¹, (blockUpper F n γ).inv_mem hlQ⟩) hlb'
    have hcb : EntryBound F e₀ ((c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
      EntryBound.leviProj (p := ⟨l, hlQ⟩) hlb
    refine mem_unipotentCompactG_of_bound hvN ?_ ?_
    · rw [hv]
      simp only [Units.val_mul]
      exact ((hmb.mul hcb').mul hlb).mul hmb'
    · have : ((b : GL (Fin n) F) * l * m⁻¹)⁻¹ = m * l⁻¹ * (c : GL (Fin n) F) * m⁻¹ := by
        rw [hbc]
        group
      rw [this]
      simp only [Units.val_mul]
      exact ((hmb.mul hlb').mul hcb).mul hmb'
  · rw [show u = x * l * m⁻¹ by rw [← hum]; group]
    group

end Support

end Parabolic

end GroundTheory.Automorphic
