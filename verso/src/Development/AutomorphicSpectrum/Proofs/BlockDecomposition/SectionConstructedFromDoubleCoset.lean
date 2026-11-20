import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideTail
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Ylb7.main hC hn h`.
-/
theorem exists_nhds_one_tube {G : Type} [Group G] [TopologicalSpace G] {C : Set G} (hC : IsCompact C)
    {n : Set (G × G)} (hn : IsOpen n) (h : ∀ c ∈ C, (c, (1 : G)) ∈ n) :
    ∃ O ∈ 𝓝 (1 : G), ∀ c ∈ C, ∀ u ∈ O, (c, u) ∈ n :=
  _root_.UpperTheory.Reformulated.B.Ylb7.main hC hn h

/- English proof (translation)
Take `⟨t, -, ht⟩` from `hC.elim_nhds_subcover (fun c => {p : P | c⁻¹ * p ∈ K'}) (fun c _ => by`. Establish `ho : IsOpen {p : P | c⁻¹ * p ∈ K'}` using `hK'.preimage (continuous_const.mul continuous_id)`. Conclude with `ho.mem_nhds (by simp [K'.one_mem]))`. Use `(t.finite_toSet.image φ).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, hp, rfl⟩`.

Take `⟨c, hc, hcp⟩` from `Set.mem_iUnion₂.1 (ht hp)`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Use `hinv c _ hcp` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Conclude with `this.symm`.
-/
theorem finite_image_of_rightInvariant {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] {W : Type}
    (φ : P → W) (K' : Subgroup P) (hK' : IsOpen (K' : Set P)) (hinv : ∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p)
    {C : Set P} (hC : IsCompact C) : (φ '' C).Finite := by
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => {p : P | c⁻¹ * p ∈ K'}) (fun c _ => by
    have ho : IsOpen {p : P | c⁻¹ * p ∈ K'} := hK'.preimage (continuous_const.mul continuous_id)
    exact ho.mem_nhds (by simp [K'.one_mem]))
  refine (t.finite_toSet.image φ).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨c, hc, hcp⟩ := Set.mem_iUnion₂.1 (ht hp)
  refine ⟨c, hc, ?_⟩
  have := hinv c _ hcp
  rw [mul_inv_cancel_left] at this
  exact this.symm

/- English proof (translation)
Introduce `hL σ hσ φ hφ K' hK' hinv C hC Y hY hCY`. Establish `hfin : (φ '' C).Finite` using `finite_image_of_rightInvariant φ K' hK' hinv hC`. Establish `hopenQ : IsOpen {q : Q | ∀ v ∈ φ '' C, σ q v = v}`. Establish `e : {q : Q | ∀ v ∈ φ '' C, σ q v = v} = ⋂ v ∈ φ '' C, {q : Q | σ q v = v}`. Use extensionality with `q`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter]`. Rewrite using `[e]`. Conclude with `hfin.isOpen_biInter fun v _ => hσ v`. Take `⟨UQ, hUQ, hUQe⟩` from `isOpen_induced_iff.1 hopenQ`. Establish `h1UQ : (1 : G) ∈ UQ`.

Establish `: (1 : Q) ∈ (Subtype.val : Q → G) ⁻¹' UQ`. Rewrite using `[hUQe]`. Introduce `v _`. Simplify using the standard rewrite rules. Conclude with `this`.

Establish `hfix : ∀ s : Q, (s : G) ∈ UQ → ∀ c ∈ C, σ s (φ c) = φ c`. Introduce `s hs c hc`. Establish `: s ∈ (Subtype.val : Q → G) ⁻¹' UQ` using `hs`. Rewrite `this` using `[hUQe]`. Conclude with `this _ ⟨c, hc, rfl⟩`.

Take `⟨U, hU, hUe⟩` from `isOpen_induced_iff.1 hK'`. Establish `h1U : (1 : G) ∈ U`. Establish `: (1 : P) ∈ (Subtype.val : P → G) ⁻¹' U`. Rewrite using `[hUe]`. Conclude with `K'.one_mem`.

Conclude with `this`. Establish `hC' : IsCompact ((Subtype.val : P → G) '' C)` using `hC.image continuous_subtype_val`. Take `⟨OP, hOP, hOPc⟩` from `exists_nhds_one_tube hC' (n := {z : G × G | z.1⁻¹ * z.2 * z.1 ∈ U}) (hU.preimage (by fun_prop)) (by`. Introduce and unpack `_ ⟨c, -, rfl⟩`. Simplify using `using h1U)`.

Take `⟨O, hO, hOs⟩` from `hL UQ (hUQ.mem_nhds h1UQ) OP hOP`. Take `⟨O₁, hO₁, hO₁c⟩` from `exists_nhds_one_tube hC' (n := {z : G × G | z.1 * z.2 * z.1⁻¹ ∈ interior O ∧ x * z.1 * z.2 ∈ Y}) ((isOpen_interior.preimage (by fun_prop)).inter (hY.preimage (by fun_prop))) (by`. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `using mem_interior_iff_mem_nhds.2 hO`.

Simplify using `using hCY c hc)`. Take `⟨V, hV⟩` from `NonarchimedeanGroup.is_nonarchimedean O₁ hO₁`. Establish `hVc : ∀ c ∈ C, ∀ κ ∈ (V : Subgroup G), (c : G) * κ * (c : G)⁻¹ ∈ interior O ∧ x * (c : G) * κ ∈ Y` using `fun c hc κ hκ => hO₁c _ ⟨c, hc, rfl⟩ κ (hV hκ)`. Use `⟨(V : Subgroup G), V.isOpen, fun c hc κ hκ => (hVc c hc κ hκ).2, ?_⟩` and prove the remaining obligations. Introduce `c hc κ hκ q p' hq`.

Establish `huO : (c : G) * κ * (c : G)⁻¹ ∈ O` using `interior_subset (hVc c hc κ hκ).1`. Establish `hmem : x * ((c : G) * κ * (c : G)⁻¹) ∈ dcos Q P x`. Use `⟨(q : G)⁻¹, Q.inv_mem q.2, (p' : G) * (c : G)⁻¹, P.mul_mem p'.2 (P.inv_mem c.2), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Take `⟨s, hsQ, hsU, p₂, hp₂, hp₂O, he⟩` from `hOs _ huO hmem`.

Establish `hconj : (c : G)⁻¹ * p₂ * (c : G) ∈ U` using `hOPc _ ⟨c, hc, rfl⟩ p₂ hp₂O`. Establish `hκ' : (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ K'`. Establish `: (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ (Subtype.val : P → G) ⁻¹' U` using `hconj`. Rewrite `this` using `[hUe]`. Conclude with `this`.

Establish `hval : φ (⟨p₂, hp₂⟩ * c) = φ c`. Use `hinv c _ hκ'` as an intermediate fact. Rewrite `this` using `[show c * (c⁻¹ * ⟨p₂, hp₂⟩ * c) = ⟨p₂, hp₂⟩ * c by group]`. Then use the resulting hypothesis. Establish `hrel : (((⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q)) : G) * x * ((⟨p₂, hp₂⟩ * c : P) : G) = x * (p' : G)`. Establish `: (q : G) * s * x * (p₂ * (c : G)) = (q : G) * (s * x * p₂) * (c : G)` using `by group`.

Use `show (q : G) * s * x * (p₂ * (c : G)) = x * (p' : G)`. Rewrite using `[this, ← he, ← hq]`. Use `group`. Establish `hsplit : (⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q) = q * ⟨s, hsQ⟩` using `rfl`. Rewrite using `[hφ _ _ _ hrel, hval, hsplit, map_mul, Module.End.mul_apply, hfix ⟨s, hsQ⟩ hsU c hc]`.
-/
theorem exists_openSubgroup_consistent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NonarchimedeanGroup G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} :
    LocSec Q P x → ∀ (σ : Representation ℂ Q W₁), IsSmooth σ → ∀ (φ : P → W₁),
    (∀ (q : Q) (p p' : P), (q : G) * x * (p : G) = x * (p' : G) → φ p' = σ q (φ p)) →
    ∀ (K' : Subgroup P), IsOpen (K' : Set P) → (∀ (p : P), ∀ κ ∈ K', φ (p * κ) = φ p) →
    ∀ (C : Set P), IsCompact C → ∀ (Y : Set G), IsOpen Y → (∀ c ∈ C, x * (c : G) ∈ Y) →
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (∀ c ∈ C, ∀ κ ∈ K, x * (c : G) * κ ∈ Y) ∧
      ∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c) := by
  intro hL σ hσ φ hφ K' hK' hinv C hC Y hY hCY
  have hfin : (φ '' C).Finite := finite_image_of_rightInvariant φ K' hK' hinv hC

  have hopenQ : IsOpen {q : Q | ∀ v ∈ φ '' C, σ q v = v} := by
    have e : {q : Q | ∀ v ∈ φ '' C, σ q v = v} = ⋂ v ∈ φ '' C, {q : Q | σ q v = v} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [e]
    exact hfin.isOpen_biInter fun v _ => hσ v
  obtain ⟨UQ, hUQ, hUQe⟩ := isOpen_induced_iff.1 hopenQ
  have h1UQ : (1 : G) ∈ UQ := by
    have : (1 : Q) ∈ (Subtype.val : Q → G) ⁻¹' UQ := by
      rw [hUQe]
      intro v _
      simp
    exact this
  have hfix : ∀ s : Q, (s : G) ∈ UQ → ∀ c ∈ C, σ s (φ c) = φ c := by
    intro s hs c hc
    have : s ∈ (Subtype.val : Q → G) ⁻¹' UQ := hs
    rw [hUQe] at this
    exact this _ ⟨c, hc, rfl⟩

  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hK'
  have h1U : (1 : G) ∈ U := by
    have : (1 : P) ∈ (Subtype.val : P → G) ⁻¹' U := by
      rw [hUe]
      exact K'.one_mem
    exact this
  have hC' : IsCompact ((Subtype.val : P → G) '' C) := hC.image continuous_subtype_val
  obtain ⟨OP, hOP, hOPc⟩ := exists_nhds_one_tube hC' (n := {z : G × G | z.1⁻¹ * z.2 * z.1 ∈ U})
    (hU.preimage (by fun_prop)) (by
      rintro _ ⟨c, -, rfl⟩
      simpa using h1U)
  obtain ⟨O, hO, hOs⟩ := hL UQ (hUQ.mem_nhds h1UQ) OP hOP
  obtain ⟨O₁, hO₁, hO₁c⟩ := exists_nhds_one_tube hC'
    (n := {z : G × G | z.1 * z.2 * z.1⁻¹ ∈ interior O ∧ x * z.1 * z.2 ∈ Y})
    ((isOpen_interior.preimage (by fun_prop)).inter (hY.preimage (by fun_prop))) (by
      rintro _ ⟨c, hc, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa using mem_interior_iff_mem_nhds.2 hO
      · simpa using hCY c hc)
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean O₁ hO₁
  have hVc : ∀ c ∈ C, ∀ κ ∈ (V : Subgroup G),
      (c : G) * κ * (c : G)⁻¹ ∈ interior O ∧ x * (c : G) * κ ∈ Y := fun c hc κ hκ =>
    hO₁c _ ⟨c, hc, rfl⟩ κ (hV hκ)
  refine ⟨(V : Subgroup G), V.isOpen, fun c hc κ hκ => (hVc c hc κ hκ).2, ?_⟩
  intro c hc κ hκ q p' hq
  have huO : (c : G) * κ * (c : G)⁻¹ ∈ O := interior_subset (hVc c hc κ hκ).1

  have hmem : x * ((c : G) * κ * (c : G)⁻¹) ∈ dcos Q P x := by
    refine ⟨(q : G)⁻¹, Q.inv_mem q.2, (p' : G) * (c : G)⁻¹, P.mul_mem p'.2 (P.inv_mem c.2), ?_⟩
    calc x * ((c : G) * κ * (c : G)⁻¹) = (q : G)⁻¹ * ((q : G) * x * (c : G) * κ) * (c : G)⁻¹ := by group
      _ = (q : G)⁻¹ * x * ((p' : G) * (c : G)⁻¹) := by rw [hq]; group
  obtain ⟨s, hsQ, hsU, p₂, hp₂, hp₂O, he⟩ := hOs _ huO hmem

  have hconj : (c : G)⁻¹ * p₂ * (c : G) ∈ U := hOPc _ ⟨c, hc, rfl⟩ p₂ hp₂O
  have hκ' : (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ K' := by
    have : (c⁻¹ * ⟨p₂, hp₂⟩ * c : P) ∈ (Subtype.val : P → G) ⁻¹' U := hconj
    rw [hUe] at this
    exact this
  have hval : φ (⟨p₂, hp₂⟩ * c) = φ c := by
    have := hinv c _ hκ'
    rwa [show c * (c⁻¹ * ⟨p₂, hp₂⟩ * c) = ⟨p₂, hp₂⟩ * c by group] at this
  have hrel : (((⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q)) : G) * x * ((⟨p₂, hp₂⟩ * c : P) : G) = x * (p' : G) := by
    have : (q : G) * s * x * (p₂ * (c : G)) = (q : G) * (s * x * p₂) * (c : G) := by group
    show (q : G) * s * x * (p₂ * (c : G)) = x * (p' : G)
    rw [this, ← he, ← hq]
    group
  have hsplit : (⟨(q : G) * s, Q.mul_mem q.2 hsQ⟩ : Q) = q * ⟨s, hsQ⟩ := rfl
  rw [hφ _ _ _ hrel, hval, hsplit, map_mul, Module.End.mul_apply, hfix ⟨s, hsQ⟩ hsU c hc]

end GlobalTheory.CompanionTheory.BZRes
