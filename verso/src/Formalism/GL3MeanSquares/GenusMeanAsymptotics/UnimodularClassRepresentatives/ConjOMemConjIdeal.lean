import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapConjO

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

structure IsStep (P : Ideal (𝓞 K)) (A B : Submodule (𝓞 K) V) (y : V) : Prop where
  le : A ≤ B
  mem : y ∈ B
  notMem : y ∉ A
  smul : ∀ π ∈ P, π • y ∈ A
  gen : ∀ x ∈ B, ∃ c : 𝓞 K, x - c • y ∈ A

def col (I : Ideal (𝓞 K)) (z : 𝓞 K) : Ideal (𝓞 K) where
  carrier := {c | c * z ∈ I}
  add_mem' := fun {a c} ha hc => by
    change (a + c) * z ∈ I
    rw [add_mul]; exact I.add_mem ha hc
  zero_mem' := by change (0 : 𝓞 K) * z ∈ I; rw [zero_mul]; exact I.zero_mem
  smul_mem' := fun c a ha => by
    change (c • a) * z ∈ I
    rw [smul_eq_mul, mul_assoc]; exact I.mul_mem_left c ha

omit [StarRing K] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_col {I : Ideal (𝓞 K)} {z c : 𝓞 K} : c ∈ col I z ↔ c * z ∈ I := Iff.rfl

omit [StarRing K] in
/- English proof (translation)
Establish `h1 : (1 : 𝓞 K) ∈ col I z`. Rewrite using `[h]`. Conclude with `Submodule.mem_top`. Simplify using `using (mem_col.1 h1)`.
-/
theorem mem_of_col_eq_top {I : Ideal (𝓞 K)} {z : 𝓞 K} (h : col I z = ⊤) : z ∈ I := by
  have h1 : (1 : 𝓞 K) ∈ col I z := by
    rw [h]; exact Submodule.mem_top
  simpa using (mem_col.1 h1)

namespace IsStep

variable {P : Ideal (𝓞 K)} {A B : Submodule (𝓞 K) V} {y : V}

omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Assume the negation of the conclusion as `hcP`. Take `⟨r, π, hπ, hrc⟩` from `hP.exists_inv hcP`. Apply `S.notMem` to reduce the goal to its premises. Establish `e : y = r • (c • y) + π • y`. Rewrite using `[smul_smul, ← add_smul, hrc, one_smul]`.

Rewrite using `[e]`. Conclude with `A.add_mem (A.smul_mem r hc) (S.smul π hπ)`.
-/
theorem mem_of_smul_mem (S : IsStep P A B y) (hP : P.IsMaximal) {c : 𝓞 K} (hc : c • y ∈ A) :
    c ∈ P := by
  by_contra hcP
  obtain ⟨r, π, hπ, hrc⟩ := hP.exists_inv hcP
  apply S.notMem
  have e : y = r • (c • y) + π • y := by
    rw [smul_smul, ← add_smul, hrc, one_smul]
  rw [e]
  exact A.add_mem (A.smul_mem r hc) (S.smul π hπ)

omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Take `⟨c, hc⟩` from `S.gen x₀ hx`. Establish `hcP : c ∉ P`. Introduce `hcP`. Apply `hn` to reduce the goal to its premises. Establish `h0` using `A.add_mem hc (S.smul c hcP)`.

Simplify using `using h0`. Take `⟨r, π, hπ, hrc⟩` from `hP.exists_inv hcP`. Use `⟨S.le, hx, hn, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Establish `h1 : p • x₀ = p • (x₀ - c • y) + c • (p • y)`.

Rewrite using `[smul_sub, smul_comm p c y, sub_add_cancel]`. Rewrite using `[h1]`. Conclude with `A.add_mem (A.smul_mem p hc) (A.smul_mem c (S.smul p hp))`. Introduce `x hxB`. Take `⟨d, hd⟩` from `S.gen x hxB`.

Use `⟨d * r, ?_⟩` and prove the remaining obligations. Establish `key : d • y = (d * r * c) • y + (d * π) • y`. Rewrite using `[← add_smul, show d * r * c + d * π = d * (r * c + π) by ring, hrc, mul_one]`. Establish `h2 : x - (d * r) • x₀ = (x - d • y) - (d * r) • (x₀ - c • y) + d • (π • y)`. Rewrite using `[smul_sub, smul_smul (d * r) c y, smul_smul d π y, key]`.

Normalize the expressions using the abelian group laws. Rewrite using `[h2]`. Conclude with `A.add_mem (A.sub_mem hd (A.smul_mem _ hc)) (A.smul_mem d (S.smul π hπ))`.
-/
theorem change (S : IsStep P A B y) (hP : P.IsMaximal) {x₀ : V} (hx : x₀ ∈ B) (hn : x₀ ∉ A) :
    IsStep P A B x₀ := by
  obtain ⟨c, hc⟩ := S.gen x₀ hx
  have hcP : c ∉ P := by
    intro hcP
    apply hn
    have h0 := A.add_mem hc (S.smul c hcP)
    simpa using h0
  obtain ⟨r, π, hπ, hrc⟩ := hP.exists_inv hcP
  refine ⟨S.le, hx, hn, ?_, ?_⟩
  · intro p hp
    have h1 : p • x₀ = p • (x₀ - c • y) + c • (p • y) := by
      rw [smul_sub, smul_comm p c y, sub_add_cancel]
    rw [h1]
    exact A.add_mem (A.smul_mem p hc) (A.smul_mem c (S.smul p hp))
  · intro x hxB
    obtain ⟨d, hd⟩ := S.gen x hxB
    refine ⟨d * r, ?_⟩
    have key : d • y = (d * r * c) • y + (d * π) • y := by
      rw [← add_smul, show d * r * c + d * π = d * (r * c + π) by ring, hrc, mul_one]
    have h2 : x - (d * r) • x₀ = (x - d • y) - (d * r) • (x₀ - c • y) + d • (π • y) := by
      rw [smul_sub, smul_smul (d * r) c y, smul_smul d π y, key]
      abel
    rw [h2]
    exact A.add_mem (A.sub_mem hd (A.smul_mem _ hc)) (A.smul_mem d (S.smul π hπ))

end IsStep

omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Rewrite using `[Basis.det_apply, Basis.det_apply, ← Matrix.det_transpose, ← Matrix.det_transpose (b.toMatrix x)]`. Use `Matrix.det_eq_of_forall_row_eq_smul_add_const (fun k => e k) i₀ he ?_` and prove the remaining obligations. Introduce `i j`. Simplify using `[Matrix.transpose_apply, Basis.toMatrix_apply, map_add, map_smul]`.
-/
theorem det_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (x : ι → V)
    (e : ι → K) (i₀ : ι) (he : e i₀ = 0) : b.det (fun k => x k + e k • x i₀) = b.det x := by
  rw [Basis.det_apply, Basis.det_apply, ← Matrix.det_transpose,
    ← Matrix.det_transpose (b.toMatrix x)]
  refine Matrix.det_eq_of_forall_row_eq_smul_add_const (fun k => e k) i₀ he ?_
  intro i j
  simp [Matrix.transpose_apply, Basis.toMatrix_apply, map_add, map_smul]

/- English proof (translation)
Apply `Ideal.subset_span` to reduce the goal to its premises. Apply the tactic sequence `exact ⟨π, hπ, by first | rfl | simp [conjO]⟩`.
-/
theorem conjO_mem_conjIdeal {P : Ideal (𝓞 K)} {π : 𝓞 K} (hπ : π ∈ P) :
    conjO K π ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  apply Ideal.subset_span
  exact ⟨π, hπ, by first | rfl | simp [conjO]⟩

/- English proof (translation)
Establish `h3` using `Ideal.mul_mem_mul (Ideal.mul_mem_mul h₂ (conjO_mem_conjIdeal h₁)) hz`. Rewrite `h3` using `[mul_comm p₂ (conjO K p₁)]`. Then use the resulting hypothesis.
-/
theorem term_mem {P I : Ideal (𝓞 K)} {p₁ p₂ z : 𝓞 K} (h₁ : p₁ ∈ P) (h₂ : p₂ ∈ P) (hz : z ∈ I) :
    conjO K p₁ * p₂ * z ∈ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * I := by
  have h3 := Ideal.mul_mem_mul (Ideal.mul_mem_mul h₂ (conjO_mem_conjIdeal h₁)) hz
  rwa [mul_comm p₂ (conjO K p₁)] at h3

/- English proof (translation)
Establish `hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A` using `fun x hx w hw => hB x (S.le hx) w (S.le hw)`. Establish `key : ∀ π ∈ P, ∀ ρ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P, ∀ z ∈ discrIdeal h B, π * ρ * z ∈ discrIdeal h A := by`. Introduce `π hπ ρ hρ`. Rewrite `hρ` using `[conjIdeal_eq_comap, Ideal.mem_comap]`. It suffices to establish `hle : discrIdeal h B ≤ Submodule.comap (LinearMap.mulLeft (𝓞 K) (π * ρ)) (discrIdeal h A) from fun z hz => hle hz`.

Use `discrIdeal_le b fun x hx z hz => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `π * ρ * z ∈ discrIdeal h A`. Distinguish the cases in `hall : ∀ i, x i ∈ A`. Conclude with `Ideal.mul_mem_left _ _ (mem_discrIdeal b hall hz)`. Use `push Not at hall`.

Take `⟨i₀, hi₀⟩` from `hall`. Establish `S'` using `S.change hP (hx i₀) hi₀`. Use `choose c hc using fun k => S'.gen (x k) (hx k)`. Set `e : Fin (finrank K V) → K` to `fun k => if k = i₀ then 0 else - algebraMap (𝓞 K) K (c k)`. Set `x' : Fin (finrank K V) → V` to `fun k => x k + e k • x i₀`.

Establish `hdet : b.det x' = b.det x` using `det_add_smul b x e i₀ (by simp [e])`. Establish `hx'0 : x' i₀ = x i₀` using `by simp [x', e]`. Establish `hx' : ∀ k, k ≠ i₀ → x' k ∈ A`. Introduce `k hk`. Establish `: x' k = x k - c k • x i₀`.

Simplify using `only [x', e, if_neg hk, neg_smul, algebraMap_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `hc k`. Establish `hup : ∀ a : 𝓞 K, b.det (Function.update x' i₀ (a • x i₀)) = algebraMap (𝓞 K) K a * b.det x`.

Introduce `a`. Rewrite using `[← algebraMap_smul K a (x i₀), AlternatingMap.map_update_smul, ← hx'0, Function.update_eq_self, hdet, smul_eq_mul]`. Use `mixed_mem hK hA b hx' (S'.smul _ hρ) (S'.smul _ hπ) ?_` and prove the remaining obligations. Rewrite using `[hup, hup, map_mul, map_mul, hz, algebraMap_conjO, star_mul', star_star]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Ideal.mul_le]`. Introduce `r hr z hz`. Proceed by induction on `hr using Submodule.mul_induction_on' with`. Consider the case `mem_mul_mem π hπ ρ hρ => exact key π hπ ρ hρ z hz`. Consider the case `add a _ c _ ha hc => rw [add_mul]`.

Conclude with `Ideal.add_mem _ ha hc`.
-/
theorem step_ge (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {A B : Submodule (𝓞 K) V} {y : V} (S : IsStep P A B y)
    (hB : Formalism.HermitianLatticesTheory.IsIntegralLat h B) (b : Basis (Fin (finrank K V)) K V) :
    P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B ≤ discrIdeal h A := by
  have hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A := fun x hx w hw => hB x (S.le hx) w (S.le hw)
  have key : ∀ π ∈ P, ∀ ρ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P, ∀ z ∈ discrIdeal h B,
      π * ρ * z ∈ discrIdeal h A := by
    intro π hπ ρ hρ
    rw [conjIdeal_eq_comap, Ideal.mem_comap] at hρ
    suffices hle : discrIdeal h B ≤ Submodule.comap (LinearMap.mulLeft (𝓞 K) (π * ρ))
        (discrIdeal h A) from fun z hz => hle hz
    refine discrIdeal_le b fun x hx z hz => ?_
    change π * ρ * z ∈ discrIdeal h A
    by_cases hall : ∀ i, x i ∈ A
    · exact Ideal.mul_mem_left _ _ (mem_discrIdeal b hall hz)
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have S' := S.change hP (hx i₀) hi₀
      choose c hc using fun k => S'.gen (x k) (hx k)
      let e : Fin (finrank K V) → K := fun k => if k = i₀ then 0 else - algebraMap (𝓞 K) K (c k)
      let x' : Fin (finrank K V) → V := fun k => x k + e k • x i₀
      have hdet : b.det x' = b.det x := det_add_smul b x e i₀ (by simp [e])
      have hx'0 : x' i₀ = x i₀ := by simp [x', e]
      have hx' : ∀ k, k ≠ i₀ → x' k ∈ A := by
        intro k hk
        have : x' k = x k - c k • x i₀ := by
          simp only [x', e, if_neg hk, neg_smul, algebraMap_smul]
          abel
        rw [this]; exact hc k
      have hup : ∀ a : 𝓞 K, b.det (Function.update x' i₀ (a • x i₀)) =
          algebraMap (𝓞 K) K a * b.det x := by
        intro a
        rw [← algebraMap_smul K a (x i₀), AlternatingMap.map_update_smul, ← hx'0,
          Function.update_eq_self, hdet, smul_eq_mul]
      refine mixed_mem hK hA b hx' (S'.smul _ hρ) (S'.smul _ hπ) ?_
      rw [hup, hup, map_mul, map_mul, hz, algebraMap_conjO, star_mul', star_star]
      ring
  rw [Ideal.mul_le]
  intro r hr z hz
  induction hr using Submodule.mul_induction_on' with
  | mem_mul_mem π hπ ρ hρ => exact key π hπ ρ hρ z hz
  | add a _ c _ ha hc => rw [add_mul]; exact Ideal.add_mem _ ha hc

end Formalism.HermitianLattices.Ext.L3.BallB
