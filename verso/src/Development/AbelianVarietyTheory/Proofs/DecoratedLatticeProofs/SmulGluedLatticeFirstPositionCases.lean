import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiesOnRamOfInvariant
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance

open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)

noncomputable section
namespace GlobalTheory.GluedOrbit
open GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration (interX)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}

/- English proof (translation)
Establish `hqi : (q.1 : k) * q.inv = 1` using `mul_inv_cancel₀ q.ne_zero`. Use extensionality with `y`. Rewrite using `[GlobalTheory.LevelUnfold.mem_gluedS]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Use `⟨⟨_, hq y hy⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩` and prove the remaining obligations. Establish `e : inX k n 1 (y ∘ Sum.inl - (⟨_, hq y hy⟩ : 𝒪[k]) • (m ∘ Sum.inl)) = y - (⟨_, hq y hy⟩ : 𝒪[k]) • m`. Use extensionality with `(j | j)`. Both sides reduce to the same expression. Establish `hj : j = 0` using `Subsingleton.elim _ _`.

Substitute `hj` using the available equality. Express the relevant statement in the definitionally equal form `(0 : k) = y (Sum.inr 0) - (q.1 : k) * y (Sum.inr 0) * m (Sum.inr 0)`. Rewrite using `[hm1, mul_right_comm, hqi, one_mul, sub_self]`. Express the relevant statement in the definitionally equal form `inX k n 1 _ ∈ M`. Rewrite using `[e]`.

Conclude with `sub_mem hy (M.smul_mem _ hm)`. Establish `hi : i = 0` using `Subsingleton.elim _ _`. Substitute `hi` using the available equality. Express the relevant statement in the definitionally equal form `y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))`. Rewrite using `[← mul_assoc, mul_comm q.inv, hqi, one_mul]`.

Introduce and unpack `⟨s, hs, h⟩`. Establish `e : y = inX k n 1 (y ∘ Sum.inl - s • (m ∘ Sum.inl)) + s • m`. Use extensionality with `(j | j)`. Express the relevant statement in the definitionally equal form `y (Sum.inl j) = (y (Sum.inl j) - (s : k) * m (Sum.inl j)) + (s : k) * m (Sum.inl j)`. Expand and normalize the polynomial expressions, which then agree.

Establish `hj : j = 0` using `Subsingleton.elim _ _`. Substitute `hj` using the available equality. Express the relevant statement in the definitionally equal form `y (Sum.inr 0) = 0 + (s : k) * m (Sum.inr 0)`. Rewrite using `[(h 0).1 rfl, hm1, zero_add, mul_comm]`. Rewrite using `[e]`.

Conclude with `add_mem hs (M.smul_mem _ hm)`.
-/
theorem eq_gluedS_of_mem (q : Unif k) {M : Submodule 𝒪[k] (n ⊕ Fin 1 → k)}
    (hq : ∀ x ∈ M, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) {m : n ⊕ Fin 1 → k} (hm : m ∈ M)
    (hm1 : m (Sum.inr 0) = q.inv) : M = gluedS q 1 (interX M) (m ∘ Sum.inl) := by
  have hqi : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  ext y
  rw [GlobalTheory.LevelUnfold.mem_gluedS]
  constructor
  · intro hy
    refine ⟨⟨_, hq y hy⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    · have e : inX k n 1 (y ∘ Sum.inl - (⟨_, hq y hy⟩ : 𝒪[k]) • (m ∘ Sum.inl)) =
          y - (⟨_, hq y hy⟩ : 𝒪[k]) • m := by
        ext (j | j)
        · rfl
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = y (Sum.inr 0) - (q.1 : k) * y (Sum.inr 0) * m (Sum.inr 0)
          rw [hm1, mul_right_comm, hqi, one_mul, sub_self]
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem hy (M.smul_mem _ hm)
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      change y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))
      rw [← mul_assoc, mul_comm q.inv, hqi, one_mul]
  · rintro ⟨s, hs, h⟩
    have e : y = inX k n 1 (y ∘ Sum.inl - s • (m ∘ Sum.inl)) + s • m := by
      ext (j | j)
      · change y (Sum.inl j) = (y (Sum.inl j) - (s : k) * m (Sum.inl j)) + (s : k) * m (Sum.inl j)
        ring
      · have hj : j = 0 := Subsingleton.elim _ _
        subst hj
        change y (Sum.inr 0) = 0 + (s : k) * m (Sum.inr 0)
        rw [(h 0).1 rfl, hm1, zero_add, mul_comm]
    rw [e]
    exact add_mem hs (M.smul_mem _ hm)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = (glue (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last q L)).lat`. Rewrite using `[glue_lat]`. Use `le_antisymm (GlobalTheory.LevelUnfold.gluedS_le_iff.2 ⟨fun y hy => ?_, ?_, fun i hi => absurd hi (by omega)⟩) (sup_le (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_))` and prove the remaining obligations. Use `Submodule.mem_sup_left (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa [inX] using hy, ?_⟩)` and prove the remaining obligations. Simplify using `[inX]`.

Rewrite using `[map_zero, add_zero]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Take `⟨h1, h2⟩` from `GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy`. Use `GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨⟨(q.1 : k) * y (Sum.inr 0), mul_mem q.1.2 h2⟩, by simpa using h1, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩` and prove the remaining obligations. Establish `hi : i = 0` using `Subsingleton.elim _ _`.

Substitute `hi` using the available equality. Express the relevant statement in the definitionally equal form `y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))`. Rewrite using `[← mul_assoc, mul_comm q.inv, GlobalTheory.LevelUnfold.mul_inv_q, one_mul]`. Use `GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := 1) L (0 : n → k)` as an intermediate fact. Rewrite `this` using `[map_zero, add_zero]`. Then use the resulting hypothesis.
-/
theorem gluedS_zero_eq_lastPair_lat (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    gluedS q 1 L 0 = (lastPair q L).lat := by
  change _ = (glue (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last q L)).lat
  rw [glue_lat]
  refine le_antisymm (GlobalTheory.LevelUnfold.gluedS_le_iff.2 ⟨fun y hy => ?_, ?_, fun i hi => absurd hi (by omega)⟩)
    (sup_le (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_))
  · refine Submodule.mem_sup_left (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa [inX] using hy, ?_⟩)
    simp [inX]
  · rw [map_zero, add_zero]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · obtain ⟨h1, h2⟩ := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy
    refine GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨⟨(q.1 : k) * y (Sum.inr 0), mul_mem q.1.2 h2⟩, by simpa using h1,
      fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))
    rw [← mul_assoc, mul_comm q.inv, GlobalTheory.LevelUnfold.mul_inv_q, one_mul]
  · have := GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := 1) L (0 : n → k)
    rwa [map_zero, add_zero] at this

/- English proof (translation)
Introduce `k _ _ _ _ n _ _ q P h hz hq`. Establish `hML : (h • gluedS q 1 P.ker P.vec).IsLattice k` using `inferInstance`. Generalize the expression as in `h • gluedS q 1 P.ker P.vec = M at hz hq hML ⊢`. Use `haveI := hML`. Use `haveI : (interX M).IsLattice k := GlobalTheory.LevelUnfold.isLattice_interX M`.

Establish `hqi : (q.1 : k) * q.inv = 1` using `mul_inv_cancel₀ q.ne_zero`. Distinguish the cases in `hO : ∀ x ∈ M, x (Sum.inr 0) ∈ 𝒪[k]`. Use `Or.inl ⟨interX M, inferInstance, Or.inl ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨?_, hO y hy⟩` and prove the remaining obligations. Establish `e : inX k n 1 (y ∘ Sum.inl) = y - (⟨_, hO y hy⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)`. Use extensionality with `(j | j)`.

Simplify using `[inX]`. Establish `hj : j = 0` using `Subsingleton.elim _ _`. Substitute `hj` using the available equality. Express the relevant statement in the definitionally equal form `(0 : k) = y (Sum.inr 0) - y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `inX k n 1 _ ∈ M`. Rewrite using `[e]`. Conclude with `sub_mem hy (M.smul_mem _ hz)`. Introduce and unpack `⟨h1, h2⟩`. Establish `e : y = inX k n 1 (y ∘ Sum.inl) + (⟨_, h2⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)`.

Use extensionality with `(j | j)`. Simplify using `[inX]`. Establish `hj : j = 0` using `Subsingleton.elim _ _`. Substitute `hj` using the available equality. Express the relevant statement in the definitionally equal form `y (Sum.inr 0) = 0 + y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `add_mem h1 (M.smul_mem _ hz)`. Use `push_neg at hO`. Take `⟨m₀, hm₀, hm₀'⟩` from `hO`.

Establish `ht : IsUnit (⟨_, hq m₀ hm₀⟩ : 𝒪[k])`. Assume the negation of the conclusion as `ht`. Take `⟨s, hs⟩` from `q.mem_max_iff.1 ((IsLocalRing.mem_maximalIdeal _).2 ht)`. Apply `hm₀'` to reduce the goal to its premises. Establish `h' : (q.1 : k) * m₀ (Sum.inr 0) = (q.1 : k) * s` using `congrArg Subtype.val hs`.

Rewrite using `[mul_left_cancel₀ q.ne_zero h']`. Conclude with `s.2`. Take `⟨u, hu⟩` from `ht`. Establish `hu' : ((u : 𝒪[k]) : k) = (q.1 : k) * m₀ (Sum.inr 0)` using `congrArg Subtype.val hu`. Establish `hinv : ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * ((u : 𝒪[k]) : k) = 1`.

Use `congrArg Subtype.val (Units.inv_mul u)` as an intermediate fact. Conclude with `this`. Use `set m : n ⊕ Fin 1 → k := ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • m₀`. Establish `hm : m ∈ M` using `M.smul_mem _ hm₀`. Establish `hm1 : m (Sum.inr 0) = q.inv`.

Express the relevant statement in the definitionally equal form `((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * m₀ (Sum.inr 0) = (q.1 : k)⁻¹`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← hinv, hu']`. Expand and normalize the polynomial expressions, which then agree. Establish `hMeq` using `eq_gluedS_of_mem q hq hm hm1`.

Establish `hqf : q.1 • (m ∘ Sum.inl) ∈ interX M`. Establish `e : inX k n 1 (q.1 • (m ∘ Sum.inl)) = q.1 • m - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)`. Use extensionality with `(j | j)`. Express the relevant statement in the definitionally equal form `(q.1 : k) * m (Sum.inl j) = (q.1 : k) * m (Sum.inl j) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inl j)`. Simplify using the standard rewrite rules.

Establish `hj : j = 0` using `Subsingleton.elim _ _`. Substitute `hj` using the available equality. Express the relevant statement in the definitionally equal form `(0 : k) = (q.1 : k) * m (Sum.inr 0) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)`. Rewrite using `[hm1, hqi]`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `inX k n 1 _ ∈ M`. Rewrite using `[e]`. Conclude with `sub_mem (M.smul_mem _ hm) hz`. Distinguish the cases in `hf : m ∘ Sum.inl ∈ interX M`. Use `Or.inl ⟨interX M, inferInstance, Or.inr ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `Or.inr ?_` and prove the remaining obligations. Establish `hG : IsGlue (interX M) (m ∘ Sum.inl)` using `(isGlue_iff q).2 ⟨inferInstance, hf, hqf⟩`. Take `⟨g, hg1, hg2⟩` from `(GlobalTheory.LevelUnfold.oneOrbit (k := k) (n := n) (c := 1) (q := q)).1 P.ker (interX M) P.vec (m ∘ Sum.inl) (Pair.isGlue P.hasVal_vec) hG`. Use `⟨g, ?_⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.LevelUnfold.embX_smul_gluedS, hg1, GlobalTheory.LevelUnfold.gluedS_congr hg2]`. Conclude with `hMeq`.
-/
theorem smul_gluedS_cases : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (h : GL (n ⊕ Fin 1) k),
    (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ h • gluedS q 1 P.ker P.vec →
    (∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) →
    (∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsLattice k), h • gluedS q 1 P.ker P.vec = lastKer Λ ∨
      h • gluedS q 1 P.ker P.vec = (lastPair q Λ).lat) ∨
    ∃ g : GL n k, h • gluedS q 1 P.ker P.vec = embX 1 g • gluedS q 1 P.ker P.vec := by
  intro k _ _ _ _ n _ _ q P h hz hq
  have hML : (h • gluedS q 1 P.ker P.vec).IsLattice k := inferInstance
  generalize h • gluedS q 1 P.ker P.vec = M at hz hq hML ⊢
  haveI := hML
  haveI : (interX M).IsLattice k := GlobalTheory.LevelUnfold.isLattice_interX M
  have hqi : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  by_cases hO : ∀ x ∈ M, x (Sum.inr 0) ∈ 𝒪[k]
  · refine Or.inl ⟨interX M, inferInstance, Or.inl ?_⟩
    ext y
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    constructor
    · intro hy
      refine ⟨?_, hO y hy⟩
      have e : inX k n 1 (y ∘ Sum.inl) = y - (⟨_, hO y hy⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · simp [inX]
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = y (Sum.inr 0) - y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          simp
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem hy (M.smul_mem _ hz)
    · rintro ⟨h1, h2⟩
      have e : y = inX k n 1 (y ∘ Sum.inl) + (⟨_, h2⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · simp [inX]
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change y (Sum.inr 0) = 0 + y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          simp
      rw [e]
      exact add_mem h1 (M.smul_mem _ hz)
  · push_neg at hO
    obtain ⟨m₀, hm₀, hm₀'⟩ := hO
    have ht : IsUnit (⟨_, hq m₀ hm₀⟩ : 𝒪[k]) := by
      by_contra ht
      obtain ⟨s, hs⟩ := q.mem_max_iff.1 ((IsLocalRing.mem_maximalIdeal _).2 ht)
      apply hm₀'
      have h' : (q.1 : k) * m₀ (Sum.inr 0) = (q.1 : k) * s := congrArg Subtype.val hs
      rw [mul_left_cancel₀ q.ne_zero h']
      exact s.2
    obtain ⟨u, hu⟩ := ht
    have hu' : ((u : 𝒪[k]) : k) = (q.1 : k) * m₀ (Sum.inr 0) := congrArg Subtype.val hu
    have hinv : ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * ((u : 𝒪[k]) : k) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      exact this
    set m : n ⊕ Fin 1 → k := ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • m₀
    have hm : m ∈ M := M.smul_mem _ hm₀
    have hm1 : m (Sum.inr 0) = q.inv := by
      change ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * m₀ (Sum.inr 0) = (q.1 : k)⁻¹
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← hinv, hu']
      ring
    have hMeq := eq_gluedS_of_mem q hq hm hm1
    have hqf : q.1 • (m ∘ Sum.inl) ∈ interX M := by
      have e : inX k n 1 (q.1 • (m ∘ Sum.inl)) = q.1 • m - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · change (q.1 : k) * m (Sum.inl j) = (q.1 : k) * m (Sum.inl j) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inl j)
          simp
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = (q.1 : k) * m (Sum.inr 0) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          rw [hm1, hqi]
          simp
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem (M.smul_mem _ hm) hz
    by_cases hf : m ∘ Sum.inl ∈ interX M
    · refine Or.inl ⟨interX M, inferInstance, Or.inr ?_⟩
      calc M = gluedS q 1 (interX M) (m ∘ Sum.inl) := hMeq
        _ = gluedS q 1 (interX M) 0 := GlobalTheory.LevelUnfold.gluedS_congr (by simpa using hf)
        _ = (lastPair q (interX M)).lat := gluedS_zero_eq_lastPair_lat q _
    · refine Or.inr ?_
      have hG : IsGlue (interX M) (m ∘ Sum.inl) := (isGlue_iff q).2 ⟨inferInstance, hf, hqf⟩
      obtain ⟨g, hg1, hg2⟩ := (GlobalTheory.LevelUnfold.oneOrbit (k := k) (n := n) (c := 1) (q := q)).1 P.ker (interX M)
        P.vec (m ∘ Sum.inl) (Pair.isGlue P.hasVal_vec) hG
      refine ⟨g, ?_⟩
      rw [GlobalTheory.LevelUnfold.embX_smul_gluedS, hg1, GlobalTheory.LevelUnfold.gluedS_congr hg2]
      exact hMeq

end GlobalTheory.GluedOrbit
