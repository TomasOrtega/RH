import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetRelPermAndCompactVanish
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlWordJetRelationsMultiplicationEquivariantStatement

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

section

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] {n : ℕ} {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ}
  {u : V} {j : W →ₗᵢ[ℂ] V}

/- English proof (translation)
Rewrite using `[← hL.2.2.2.2]`. Conclude with `⟨x, rfl⟩`.
-/
theorem LowData.mem_kSpan (hL : LowData ε E Λ u j) (x : W) : j x ∈ Formalism.REAL.kSpan ε E u := by
  rw [← hL.2.2.2.2]; exact ⟨x, rfl⟩

/- English proof (translation)
Rewrite `hv` using `[← hL.2.2.2.2]`. Conclude with `hv`.
-/
theorem LowData.exists_of_mem (hL : LowData ε E Λ u j) {v : V} (hv : v ∈ Formalism.REAL.kSpan ε E u) :
    ∃ x : W, j x = v := by
  rw [← hL.2.2.2.2] at hv
  exact hv

/- English proof (translation)
Establish `h` using `hL.2.2.2.1`. Rewrite `h` using `[← hL.2.2.2.2]`. Conclude with `(LinearEquiv.ofInjective j.toLinearMap j.injective).symm.finiteDimensional`.
-/
theorem LowData.finiteDimensional (hL : LowData ε E Λ u j) : FiniteDimensional ℂ W := by
  have h := hL.2.2.2.1
  rw [← hL.2.2.2.2] at h
  exact (LinearEquiv.ofInjective j.toLinearMap j.injective).symm.finiteDimensional

/- English proof (translation)
Establish `h : ∀ α, ∃ x : W, j x = F α`. Introduce `α`. Establish `h1` using `(mem_admissibleArrays ε E u F).mp hF α`. Apply `hL.exists_of_mem` to reduce the goal to its premises. Use `split_ifs at h1`.

Conclude with `h1`. Rewrite using `[(Submodule.mem_bot ℂ).mp h1]`. Conclude with `Submodule.zero_mem _`. Use `choose G hG using h`. Conclude with `⟨G, indexArray_ext fun α => hG α⟩`.
-/
theorem LowData.exists_arr (hL : LowData ε E Λ u j) {k : ℕ} {F : Arr V n k} (hF : F ∈ arrV0 ε E u k) :
    ∃ G : (Fin k → Fin n × Fin n) → W, arrTo V n k (fun α => j (G α)) = F := by
  have h : ∀ α, ∃ x : W, j x = F α := by
    intro α
    have h1 := (mem_admissibleArrays ε E u F).mp hF α
    apply hL.exists_of_mem
    split_ifs at h1
    · exact h1
    · rw [(Submodule.mem_bot ℂ).mp h1]; exact Submodule.zero_mem _
  choose G hG using h
  exact ⟨G, indexArray_ext fun α => hG α⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem arrTo_apply_jet {k : ℕ} (f : (Fin k → Fin n × Fin n) → V) (α : Fin k → Fin n × Fin n) :
    arrTo V n k f α = f α := rfl

/- English proof (translation)
Take `⟨hperm, hcomp⟩` from `jetRel_perm_and_compact_vanish V W n ε E Λ u j B m hL hB h0`. Establish `hz : ∀ α : Fin (m + 1) → Fin n × Fin n, (∃ i, ε (α i).1 = ε (α i).2) → g α = 0`. Introduce and unpack `α ⟨i, hi⟩`. Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `x`.

Rewrite using `[hg, hcomp _ (by simp) ⟨α i, by rw [List.mem_reverse, List.mem_ofFn]; exact ⟨i, rfl⟩, hi⟩]`. Simplify using the standard rewrite rules. Establish `hV0 : arrTo V n (m + 1) (fun α => j (g α)) ∈ arrV0 ε E u (m + 1)`. Rewrite using `[mem_admissibleArrays]`. Introduce `α`.

Rewrite using `[arrTo_apply_jet]`. Use `split_ifs with h`. Conclude with `hL.mem_kSpan _`. Use `push Not at h`. Rewrite using `[hz α h]`.

Simplify using the standard rewrite rules. Use `⟨⟨hV0, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [symSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`. Introduce `σ`. Apply `indexArray_ext` to reduce the goal to its premises.

Introduce `α`. Rewrite using `[permutePositions_apply, arrTo_apply_jet, arrTo_apply_jet]`. Use `congr 1`. Apply `ext_inner_right ℂ` to reduce the goal to its premises. Introduce `x`.

Rewrite using `[hg, hg, hperm _ (List.ofFn α).reverse _ (by simp)]`. Conclude with `(List.reverse_perm _).trans ((Equiv.Perm.ofFn_comp_perm σ α).trans (List.reverse_perm _).symm)`. Simplify using `only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]`. Introduce `α'`. Take `⟨horth, hsup⟩` from `typesSplit V n ε E Λ u hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1`.

Use `set S := sliceLin V n α' (arrTo V n (m + 1) (fun α => j (g α))) with hS`. Establish `hSa : ∀ β, S β = j (g (Fin.cons (β 0) α'))` using `fun β => by`. Rewrite using `[hS, firstPositionSlice_apply, arrTo_apply_jet]`. Establish `hS0 : S ∈ arrV0 ε E u 1`. Rewrite using `[mem_admissibleArrays]`.

Introduce `β`. Rewrite using `[hSa]`. Use `split_ifs with h`. Conclude with `hL.mem_kSpan _`. Use `push Not at h`.

Take `⟨i, hi⟩` from `h`. Rewrite using `[hz _ ⟨0, by simpa [Subsingleton.elim i 0] using hi⟩]; simp`. Establish `hSo : ∀ Q ∈ Vminus ε E Λ u, ⟪S, Q⟫_ℂ = 0`. Introduce `Q hQ`. Establish `hQ0 : Q ∈ arrV0 ε E u 1` using `by rw [← hsup]; exact Submodule.mem_sup_right hQ`.

Take `⟨G, hG⟩` from `hL.exists_arr hQ0`. Establish `hQe : arr1 j (fun p => G fun _ => p) = Q`. Rewrite using `[← hG]`. Apply `indexArray_ext` to reduce the goal to its premises. Introduce `β`.

Establish `: (fun _ : Fin 1 => β 0) = β` using `funext fun i => by rw [Subsingleton.elim i 0]`. Simplify using `only [arr1, arrTo_apply_jet, this]`. Establish `h4` using `hB.2.2.2 (List.ofFn α').reverse (fun p => G fun _ => p) (hQe ▸ hQ) y`. Rewrite using `[← h4, indexArray_inner, ← hQe]`. Use `Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun β => ?_` and prove the remaining obligations.

Rewrite using `[hSa, arr1, arrTo_apply_jet, LinearIsometry.inner_map_map, hg]`. Simplify using `[List.ofFn_succ]`. Rewrite `hS0` using `[← hsup]`. Take `⟨P, hP, Q, hQ, hPQ⟩` from `Submodule.mem_sup.mp hS0`. Establish `h1` using `hSo Q hQ`.

Rewrite `h1` using `[← hPQ, inner_add_left, horth P hP Q hQ, zero_add, inner_self_eq_zero]`. Rewrite using `[← hPQ, h1, add_zero]`. Conclude with `hP`.
-/
theorem riesz_arr_mem_Nset {B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} {m : ℕ} (hL : LowData ε E Λ u j)
    (hB : JetRel ε E Λ u j B) (h0 : ∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0) (y : W)
    (g : (Fin (m + 1) → Fin n × Fin n) → W)
    (hg : ∀ α x, ⟪g α, x⟫_ℂ = B (List.ofFn α).reverse y x) :
    arrTo V n (m + 1) (fun α => j (g α)) ∈ Nset ε E Λ u m := by
  obtain ⟨hperm, hcomp⟩ := jetRel_perm_and_compact_vanish V W n ε E Λ u j B m hL hB h0
  have hz : ∀ α : Fin (m + 1) → Fin n × Fin n, (∃ i, ε (α i).1 = ε (α i).2) → g α = 0 := by
    rintro α ⟨i, hi⟩
    apply ext_inner_right ℂ
    intro x
    rw [hg, hcomp _ (by simp) ⟨α i, by rw [List.mem_reverse, List.mem_ofFn]; exact ⟨i, rfl⟩, hi⟩]
    simp
  have hV0 : arrTo V n (m + 1) (fun α => j (g α)) ∈ arrV0 ε E u (m + 1) := by
    rw [mem_admissibleArrays]
    intro α
    rw [arrTo_apply_jet]
    split_ifs with h
    · exact hL.mem_kSpan _
    · push Not at h
      rw [hz α h]; simp
  refine ⟨⟨hV0, ?_⟩, ?_⟩
  · simp only [symSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    intro σ
    apply indexArray_ext
    intro α
    rw [permutePositions_apply, arrTo_apply_jet, arrTo_apply_jet]
    congr 1
    apply ext_inner_right ℂ
    intro x
    rw [hg, hg, hperm _ (List.ofFn α).reverse _ (by simp)]
    exact (List.reverse_perm _).trans ((Equiv.Perm.ofFn_comp_perm σ α).trans (List.reverse_perm _).symm)
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
    intro α'
    obtain ⟨horth, hsup⟩ := typesSplit V n ε E Λ u hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1
    set S := sliceLin V n α' (arrTo V n (m + 1) (fun α => j (g α))) with hS
    have hSa : ∀ β, S β = j (g (Fin.cons (β 0) α')) := fun β => by
      rw [hS, firstPositionSlice_apply, arrTo_apply_jet]
    have hS0 : S ∈ arrV0 ε E u 1 := by
      rw [mem_admissibleArrays]
      intro β
      rw [hSa]
      split_ifs with h
      · exact hL.mem_kSpan _
      · push Not at h
        obtain ⟨i, hi⟩ := h
        rw [hz _ ⟨0, by simpa [Subsingleton.elim i 0] using hi⟩]; simp
    have hSo : ∀ Q ∈ Vminus ε E Λ u, ⟪S, Q⟫_ℂ = 0 := by
      intro Q hQ
      have hQ0 : Q ∈ arrV0 ε E u 1 := by rw [← hsup]; exact Submodule.mem_sup_right hQ
      obtain ⟨G, hG⟩ := hL.exists_arr hQ0
      have hQe : arr1 j (fun p => G fun _ => p) = Q := by
        rw [← hG]
        apply indexArray_ext
        intro β
        have : (fun _ : Fin 1 => β 0) = β := funext fun i => by rw [Subsingleton.elim i 0]
        simp only [arr1, arrTo_apply_jet, this]
      have h4 := hB.2.2.2 (List.ofFn α').reverse (fun p => G fun _ => p) (hQe ▸ hQ) y
      rw [← h4, indexArray_inner, ← hQe]
      refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun β => ?_
      rw [hSa, arr1, arrTo_apply_jet, LinearIsometry.inner_map_map, hg]
      simp [List.ofFn_succ]
    rw [← hsup] at hS0
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := Submodule.mem_sup.mp hS0
    have h1 := hSo Q hQ
    rw [← hPQ, inner_add_left, horth P hP Q hQ, zero_add, inner_self_eq_zero] at h1
    rw [← hPQ, h1, add_zero]
    exact hP

/- English proof (translation)
Establish `hpair : ∀ G : (Fin (m + 1) → Fin n × Fin n) → W, ⟪F, arrTo V n (m + 1) (fun α => j (G α))⟫_ℂ = ∑ α, B (List.ofFn α).reverse y (G α)`. Introduce `G`. Rewrite using `[indexArray_inner, ← hF]`. Simplify using `only [arrTo_apply_jet, LinearIsometry.inner_map_map, hg]`. Establish `hst` using `compact_span_compact_stable ε E u`.

Establish `hy : ∀ c d : Fin n, ∃ z : W, j z = (if ε c = ε d then E c d (E d c (j y)) else 0) ∧ ⟪F, if ε c = ε d then arrE E (m + 1) c d (arrE E (m + 1) d c F) else 0⟫_ℂ = ∑ α, B (List.ofFn α).reverse z (g α)`. Introduce `c d`. Use `split_ifs with h`. Establish `h1` using `nStable V n ε E Λ u m d c h.symm F hN`. Establish `h2` using `nStable V n ε E Λ u m c d h _ h1`.

Take `⟨G₁, hG₁⟩` from `hL.exists_arr h1.1.1`. Take `⟨G₂, hG₂⟩` from `hL.exists_arr h2.1.1`. Take `⟨y₁, hy₁⟩` from `hL.exists_of_mem (hst d c h.symm _ (hL.mem_kSpan y))`. Take `⟨y₂, hy₂⟩` from `hL.exists_of_mem (hst c d h _ (hL.mem_kSpan y₁))`. Use `⟨y₂, by rw [hy₂, hy₁], ?_⟩` and prove the remaining obligations.

Rewrite using `[← hG₂, hpair, GlobalTheory.T.glWordJetRelations_multiplication_equivariant V W n ε E Λ u j B (m + 1) hL hB c d h y y₁ hy₁ G₁ G₂ (by rw [hG₂, hG₁]), GlobalTheory.T.glWordJetRelations_multiplication_equivariant V W n ε E Λ u j B (m + 1) hL hB d c h.symm y₁ y₂ hy₂ g G₁ (by rw [hG₁, …`. Conclude with `⟨0, by simp, by simp⟩`. Use `choose z hz hz' using hy`. Establish `hsum : ∑ c, ∑ d, z c d = ((ckv ε Λ : ℝ) : ℂ) • y`. Apply `j.injective` to reduce the goal to its premises.

Rewrite using `[map_smul, ← kCasSpan V n ε E Λ u (glRel_kRel ε E hL.1) hL.2.2.1 _ (hL.mem_kSpan y), compactCasimir_apply]`. Simplify using `only [map_sum, hz]`. Establish `hFF : ⟪F, F⟫_ℂ = ∑ α, B (List.ofFn α).reverse y (g α)`. Rewrite using `[← hpair, hF]`. Rewrite using `[compactCasimir_apply, hFF]`.

Simplify using `only [inner_sum, hz']`. Rewrite using `[Finset.mul_sum]`. Establish `hα : ∀ α : Fin (m + 1) → Fin n × Fin n, ((ckv ε Λ : ℝ) : ℂ) * B (List.ofFn α).reverse y (g α) = ∑ c, ∑ d, B (List.ofFn α).reverse (z c d) (g α)`. Introduce `α`. Use `congrArg (fun w => B (List.ofFn α).reverse w (g α)) hsum` as an intermediate fact.

Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal] at this`. Conclude with `this.symm`. Simplify using `only [hα]`. Rewrite using `[Finset.sum_comm (s := Finset.univ (α := Fin (m + 1) → Fin n × Fin n))]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`.
-/
theorem riesz_arr_casimir {B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} {m : ℕ} (hL : LowData ε E Λ u j)
    (hB : JetRel ε E Λ u j B) (y : W) (g : (Fin (m + 1) → Fin n × Fin n) → W)
    (hg : ∀ α x, ⟪g α, x⟫_ℂ = B (List.ofFn α).reverse y x) (F : Arr V n (m + 1))
    (hF : arrTo V n (m + 1) (fun α => j (g α)) = F) (hN : F ∈ Nset ε E Λ u m) :
    ⟪F, CasK ε (arrE E (m + 1)) F⟫_ℂ = ((ckv ε Λ : ℝ) : ℂ) * ⟪F, F⟫_ℂ := by
  have hpair : ∀ G : (Fin (m + 1) → Fin n × Fin n) → W,
      ⟪F, arrTo V n (m + 1) (fun α => j (G α))⟫_ℂ = ∑ α, B (List.ofFn α).reverse y (G α) := by
    intro G
    rw [indexArray_inner, ← hF]
    simp only [arrTo_apply_jet, LinearIsometry.inner_map_map, hg]
  have hst := compact_span_compact_stable ε E u
  have hy : ∀ c d : Fin n, ∃ z : W, j z = (if ε c = ε d then E c d (E d c (j y)) else 0) ∧
      ⟪F, if ε c = ε d then arrE E (m + 1) c d (arrE E (m + 1) d c F) else 0⟫_ℂ =
        ∑ α, B (List.ofFn α).reverse z (g α) := by
    intro c d
    split_ifs with h
    · have h1 := nStable V n ε E Λ u m d c h.symm F hN
      have h2 := nStable V n ε E Λ u m c d h _ h1
      obtain ⟨G₁, hG₁⟩ := hL.exists_arr h1.1.1
      obtain ⟨G₂, hG₂⟩ := hL.exists_arr h2.1.1
      obtain ⟨y₁, hy₁⟩ := hL.exists_of_mem (hst d c h.symm _ (hL.mem_kSpan y))
      obtain ⟨y₂, hy₂⟩ := hL.exists_of_mem (hst c d h _ (hL.mem_kSpan y₁))
      refine ⟨y₂, by rw [hy₂, hy₁], ?_⟩
      rw [← hG₂, hpair,
        GlobalTheory.T.glWordJetRelations_multiplication_equivariant V W n ε E Λ u j B (m + 1) hL hB c d h y y₁ hy₁ G₁ G₂ (by rw [hG₂, hG₁]),
        GlobalTheory.T.glWordJetRelations_multiplication_equivariant V W n ε E Λ u j B (m + 1) hL hB d c h.symm y₁ y₂ hy₂ g G₁ (by rw [hG₁, hF])]
    · exact ⟨0, by simp, by simp⟩
  choose z hz hz' using hy
  have hsum : ∑ c, ∑ d, z c d = ((ckv ε Λ : ℝ) : ℂ) • y := by
    apply j.injective
    rw [map_smul, ← kCasSpan V n ε E Λ u (glRel_kRel ε E hL.1) hL.2.2.1 _ (hL.mem_kSpan y), compactCasimir_apply]
    simp only [map_sum, hz]
  have hFF : ⟪F, F⟫_ℂ = ∑ α, B (List.ofFn α).reverse y (g α) := by
    rw [← hpair, hF]
  rw [compactCasimir_apply, hFF]
  simp only [inner_sum, hz']
  rw [Finset.mul_sum]
  have hα : ∀ α : Fin (m + 1) → Fin n × Fin n,
      ((ckv ε Λ : ℝ) : ℂ) * B (List.ofFn α).reverse y (g α) =
        ∑ c, ∑ d, B (List.ofFn α).reverse (z c d) (g α) := by
    intro α
    have := congrArg (fun w => B (List.ofFn α).reverse w (g α)) hsum
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      Complex.conj_ofReal] at this
    exact this.symm
  simp only [hα]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin (m + 1) → Fin n × Fin n))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

end

/- English proof (translation)
Introduce `V W _ _ _ _ n ε E lam u j B hL hgap hB hnil`. Use `haveI := hL.finiteDimensional`. Use `haveI : CompleteSpace W := FiniteDimensional.complete ℂ W`. Establish `key : ∀ m : ℕ, ∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero`. Introduce `l hl`. Rewrite using `[List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]`. Conclude with `hnil`.

Consider the case `succ m ih`. Introduce `l hl`. Break down `Nat.lt_or_ge m l.length with hlt | hle` into its components or cases. Use `swap`. Conclude with `ih l hle`.

Establish `hlen : l.reverse.length = m + 1` using `by rw [List.length_reverse]; omega`. Use extensionality with `y x`. Establish `hex : ∀ α : Fin (m + 1) → Fin n × Fin n, ∃ w : W, ∀ x, ⟪w, x⟫_ℂ = B (List.ofFn α).reverse y x` using `fun α => ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap (B (List.ofFn α).reverse y)), fun x => by`. Rewrite using `[InnerProductSpace.toDual_symm_apply]`. Use the proof step `rfl⟩`.

Use `choose g hg using hex`. Establish `hN` using `riesz_arr_mem_Nset hL hB ih y g hg`. Establish `hc` using `riesz_arr_casimir hL hB y g hg _ rfl hN`. Establish `hp` using `nPos V n ε E lam (2 * (n : ℝ) + 1) u m hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1 hgap _ hN`. Use `set F := arrTo V n (m + 1) (fun α => j (g α)) with hF`.

Rewrite `hp` using `[hc, inner_self_eq_norm_sq_to_K]`. Establish `hre : (((ckv ε (LamOf ε lam) : ℝ) : ℂ) * ((‖F‖ : ℝ) : ℂ) ^ 2).re = ckv ε (LamOf ε lam) * ‖F‖ ^ 2`. Rewrite using `[← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]`. Establish `hp' : (ckv ε (LamOf ε lam) + 2 * ((m : ℝ) + 1) * (2 * (n : ℝ) + 1 - 2 * (n : ℝ))) * ‖F‖ ^ 2 ≤ ckv ε (LamOf ε lam) * ‖F‖ ^ 2` using `hp.trans_eq hre`. Establish `hF0 : F = 0`.

Establish `hm : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Establish `: ‖F‖ ^ 2 ≤ 0` using `by nlinarith [sq_nonneg ‖F‖, mul_nonneg hm (sq_nonneg ‖F‖)]`. Conclude with `norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _)))`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α : Fin (m + 1) → Fin n × Fin n, List.ofFn α = l.reverse := by`. Generalize the expression as in `l.reverse = l' at hlen`.

Generalize the expression as in `m + 1 = k at hlen`. Substitute `hlen` using the available equality. Conclude with `⟨l'.get, List.ofFn_get l'⟩`. Establish `hgα : g α = 0`. Apply `j.injective` to reduce the goal to its premises.

Establish `: F α = j (g α)` using `rfl`. Rewrite using `[← this, hF0, map_zero]`. Both sides reduce to the same expression. Use `hg α x` as an intermediate fact. Rewrite `this` using `[hgα, hα, List.reverse_reverse, inner_zero_left]`.

Rewrite using `[← this]`. Both sides reduce to the same expression. Conclude with `fun l => key l.length l le_rfl`.
-/
theorem jetRel_eq_zero_of_nil :
    ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), LowData ε E (LamOf ε lam) u j → (∀ a b : Fin n, a < b → ε a ≠ ε b → 2 * (n : ℝ) + 1 ≤ lam a - lam b) → JetRel ε E (LamOf ε lam) u j B → B [] = 0 → ∀ l, B l = 0 := by
  intro V W _ _ _ _ n ε E lam u j B hL hgap hB hnil
  haveI := hL.finiteDimensional
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have key : ∀ m : ℕ, ∀ l : List (Fin n × Fin n), l.length ≤ m → B l = 0 := by
    intro m
    induction m with
    | zero =>
      intro l hl
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
      exact hnil
    | succ m ih =>
      intro l hl
      rcases Nat.lt_or_ge m l.length with hlt | hle
      swap
      · exact ih l hle
      have hlen : l.reverse.length = m + 1 := by rw [List.length_reverse]; omega
      ext y x
      have hex : ∀ α : Fin (m + 1) → Fin n × Fin n, ∃ w : W, ∀ x, ⟪w, x⟫_ℂ = B (List.ofFn α).reverse y x :=
        fun α => ⟨(InnerProductSpace.toDual ℂ W).symm
          (LinearMap.toContinuousLinearMap (B (List.ofFn α).reverse y)), fun x => by
            rw [InnerProductSpace.toDual_symm_apply]; rfl⟩
      choose g hg using hex
      have hN := riesz_arr_mem_Nset hL hB ih y g hg
      have hc := riesz_arr_casimir hL hB y g hg _ rfl hN
      have hp := nPos V n ε E lam (2 * (n : ℝ) + 1) u m hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1 hgap _ hN
      set F := arrTo V n (m + 1) (fun α => j (g α)) with hF
      rw [hc, inner_self_eq_norm_sq_to_K] at hp
      have hre : (((ckv ε (LamOf ε lam) : ℝ) : ℂ) * ((‖F‖ : ℝ) : ℂ) ^ 2).re = ckv ε (LamOf ε lam) * ‖F‖ ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      have hp' : (ckv ε (LamOf ε lam) + 2 * ((m : ℝ) + 1) * (2 * (n : ℝ) + 1 - 2 * (n : ℝ))) * ‖F‖ ^ 2 ≤
          ckv ε (LamOf ε lam) * ‖F‖ ^ 2 := hp.trans_eq hre
      have hF0 : F = 0 := by
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have : ‖F‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖F‖, mul_nonneg hm (sq_nonneg ‖F‖)]
        exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _)))
      obtain ⟨α, hα⟩ : ∃ α : Fin (m + 1) → Fin n × Fin n, List.ofFn α = l.reverse := by
        generalize l.reverse = l' at hlen
        generalize m + 1 = k at hlen
        subst hlen
        exact ⟨l'.get, List.ofFn_get l'⟩
      have hgα : g α = 0 := by
        apply j.injective
        have : F α = j (g α) := rfl
        rw [← this, hF0, map_zero]; rfl
      have := hg α x
      rw [hgα, hα, List.reverse_reverse, inner_zero_left] at this
      rw [← this]; rfl
  exact fun l => key l.length l le_rfl

end GlobalTheory.SphJet
