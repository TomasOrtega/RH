import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.AlgDirMom

/- English proof (translation)
Establish `hc : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)`. Take `⟨z, hz0, hz⟩` from `hc.exists_integral_multiple`. Use `⟨z.natAbs, Int.natAbs_pos.2 hz0, ?_⟩` and prove the remaining obligations. Rewrite `hz` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq z with h | h` into its components or cases.

Rewrite `hz` using `[h]`. Simplify using `using hz`. Rewrite `hz` using `[h]`. Use `hz.neg` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz0, hz⟩ := hc.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz0, ?_⟩
  rw [zsmul_eq_mul] at hz
  rcases Int.natAbs_eq z with h | h
  · rw [h] at hz; simpa using hz
  · rw [h] at hz
    have := hz.neg
    simpa using this

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (L' : Set (Fin n → E))` using `hL' ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations. Establish `e : ((a * b : ℕ) : E) • (x + y) = b • ((a : E) • x) + a • ((b : E) • y)`. Rewrite using `[smul_add, ← Nat.cast_smul_eq_nsmul E b, ← Nat.cast_smul_eq_nsmul E a, smul_smul, smul_smul]`.

Use `push_cast`. Rewrite using `[mul_comm (b : E) (a : E)]`. Rewrite using `[e]`. Conclude with `L'.add_mem (L'.toAddSubmonoid.nsmul_mem hax b) (L'.toAddSubmonoid.nsmul_mem hby a)`. Consider the case `smul c x _ hx`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨m, hm, hint⟩` from `exists_nat_mul_isIntegral c`. Use `⟨m * a, Nat.mul_pos hm ha, ?_⟩` and prove the remaining obligations. Establish `h2 : (⟨(m : E) * c, hint⟩ : 𝓞 E) • ((a : E) • x) ∈ L'` using `L'.smul_mem _ hax`. Rewrite `h2` using `[← algebraMap_smul E]`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `_ = ((m : E) * c) • ((a : E) • x)`. Rewrite using `[smul_smul, smul_smul]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L' : Submodule (𝓞 E) (Fin n → E))
    (hL' : Submodule.span E (L' : Set (Fin n → E)) = ⊤) (v : Fin n → E) :
    ∃ k : ℕ, 0 < k ∧ (k : E) • v ∈ L' := by
  have hv : v ∈ Submodule.span E (L' : Set (Fin n → E)) := hL' ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have e : ((a * b : ℕ) : E) • (x + y) = b • ((a : E) • x) + a • ((b : E) • y) := by
      rw [smul_add, ← Nat.cast_smul_eq_nsmul E b, ← Nat.cast_smul_eq_nsmul E a, smul_smul, smul_smul]
      push_cast
      rw [mul_comm (b : E) (a : E)]
    rw [e]
    exact L'.add_mem (L'.toAddSubmonoid.nsmul_mem hax b) (L'.toAddSubmonoid.nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨m, hm, hint⟩ := exists_nat_mul_isIntegral c
    refine ⟨m * a, Nat.mul_pos hm ha, ?_⟩
    have h2 : (⟨(m : E) * c, hint⟩ : 𝓞 E) • ((a : E) • x) ∈ L' := L'.smul_mem _ hax
    rw [← algebraMap_smul E] at h2
    convert h2 using 1
    change _ = ((m : E) * c) • ((a : E) • x)
    rw [smul_smul, smul_smul]
    push_cast
    ring_nf

/- English proof (translation)
Take `⟨s, hs⟩` from `hL`. Establish `hk : ∀ g ∈ s, ∃ k : ℕ, 0 < k ∧ (k : E) • y.mulVec g ∈ L'` using `fun g _ => exists_nat_smul_mem L' hL' _`. Use `choose! kf hkpos hkmem using hk`. Use `⟨∏ g ∈ s, kf g, Finset.prod_pos fun g hg => hkpos g hg, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[← hs]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem g hg`. Rewrite using `[Matrix.smul_mulVec]`. Rewrite using `[← Finset.mul_prod_erase s kf hg]`.

Use `push_cast`. Rewrite using `[mul_comm, ← smul_smul]`. Rewrite using `[← Nat.cast_prod, Nat.cast_smul_eq_nsmul]`. Conclude with `L'.toAddSubmonoid.nsmul_mem (hkmem g hg) _`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add]`. Conclude with `L'.add_mem hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[Matrix.mulVec_smul]`. Conclude with `L'.smul_mem r hx`.
-/
theorem exists_nat_smul_maps {E : Type} [Field E] [NumberField E] {N N' : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) (hL : L.FG)
    (hL' : Submodule.span E (L' : Set (Fin N' → E)) = ⊤) (y : Matrix (Fin N') (Fin N) E) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ L, ((k : E) • y).mulVec x ∈ L' := by
  obtain ⟨s, hs⟩ := hL
  have hk : ∀ g ∈ s, ∃ k : ℕ, 0 < k ∧ (k : E) • y.mulVec g ∈ L' := fun g _ => exists_nat_smul_mem L' hL' _
  choose! kf hkpos hkmem using hk
  refine ⟨∏ g ∈ s, kf g, Finset.prod_pos fun g hg => hkpos g hg, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    rw [Matrix.smul_mulVec]
    rw [← Finset.mul_prod_erase s kf hg]
    push_cast
    rw [mul_comm, ← smul_smul]
    rw [← Nat.cast_prod, Nat.cast_smul_eq_nsmul]
    exact L'.toAddSubmonoid.nsmul_mem (hkmem g hg) _
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact L'.add_mem hx hy
  | smul r x _ hx =>
    rw [Matrix.mulVec_smul]
    exact L'.smul_mem r hx

end GlobalTheory.AlgDirMom

namespace GlobalTheory.AlgDirMom

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, Base.tor, tor0]`.
-/
theorem embV_natCast_smul {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {N N' : ℕ} (n : ℕ)
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D B.tor ((n : D.host.E) • y) = (n : ℂ) • embV D B.tor y := by
  funext τ i j
  simp [embV, Base.tor, tor0]

/- English proof (translation)
Introduce `D cc δ δ₀ B N N' L L' hcc hadm hq hq0 g S e he y`. Establish `hδ : δ ≠ 0` using `fun h => hq0 (by simp [h])`. Establish `hδ₀ : δ₀ ≠ 0` using `fun h => hq0 (by simp [h])`. Take `⟨-, -, ⟨hLfg, -, -⟩, ⟨-, hL'sp, -⟩⟩` from `hadm`. Take `⟨n, hn, hnmap⟩` from `exists_nat_smul_maps L L' hLfg hL'sp y`.

Establish `hNc : Ideal.absNorm cc ≠ 0` using `fun h => hcc.1 (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `hA : (n : D.host.E) • y ∈ YYl D L L'` using `Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, _, Submodule.subset_span (fun x hx => hnmap x hx), (one_smul _ _).symm⟩`. Establish `hw : δ * (Ideal.absNorm cc : ℂ) ∈ B.tor.abelian₂`. Express the relevant statement in the definitionally equal form `_ ∈ lamOf D cc δ`. Conclude with `AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp⟩`.

Establish `hx : (δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y) ∈ La D B.tor L L'` using `AddSubgroup.subset_closure ⟨_, hw, _, hA, rfl⟩`. Establish `hu` using `(he _).2 hx`. Establish `hc : (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)) ∈ JMB.Qbar`. Establish `h1 : δ₀ / δ = (δ / δ₀)⁻¹` using `(inv_div δ δ₀).symm`. Rewrite using `[h1]`.

Conclude with `div_mem (inv_mem hq) (mul_mem (natCast_mem _ n) (natCast_mem _ _))`. Use `⟨1, fun _ => (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)), fun _ => e ((δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y)), fun _ => hc, fun _ => hu, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_one, embV_natCast_smul, smul_smul, map_smul, map_smul, smul_smul, smul_smul]`. Use `congr 1`. Establish `hn0 : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`.

Establish `hN0 : (Ideal.absNorm cc : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hNc`. Clear the denominators using the available nonvanishing facts.
-/
theorem algDir_smul_embV : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsCurveIdeal D cc → admitted D N N' L L' → δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → ∀ y : Matrix (Fin N') (Fin N) D.host.E, S.AlgDir ((δ₀ / δ) • e (δ • embV D B.tor y)) := by
  intro D cc δ δ₀ B N N' L L' hcc hadm hq hq0 g S e he y
  have hδ : δ ≠ 0 := fun h => hq0 (by simp [h])
  have hδ₀ : δ₀ ≠ 0 := fun h => hq0 (by simp [h])
  obtain ⟨-, -, ⟨hLfg, -, -⟩, ⟨-, hL'sp, -⟩⟩ := hadm
  obtain ⟨n, hn, hnmap⟩ := exists_nat_smul_maps L L' hLfg hL'sp y
  have hNc : Ideal.absNorm cc ≠ 0 := fun h => hcc.1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hA : (n : D.host.E) • y ∈ YYl D L L' :=
    Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, _, Submodule.subset_span (fun x hx => hnmap x hx),
      (one_smul _ _).symm⟩
  have hw : δ * (Ideal.absNorm cc : ℂ) ∈ B.tor.abelian₂ := by
    change _ ∈ lamOf D cc δ
    exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp⟩
  have hx : (δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y) ∈ La D B.tor L L' :=
    AddSubgroup.subset_closure ⟨_, hw, _, hA, rfl⟩
  have hu := (he _).2 hx
  have hc : (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)) ∈ JMB.Qbar := by
    have h1 : δ₀ / δ = (δ / δ₀)⁻¹ := (inv_div δ δ₀).symm
    rw [h1]
    exact div_mem (inv_mem hq) (mul_mem (natCast_mem _ n) (natCast_mem _ _))
  refine ⟨1, fun _ => (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)),
    fun _ => e ((δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y)), fun _ => hc, fun _ => hu, ?_⟩
  rw [Fin.sum_univ_one, embV_natCast_smul, smul_smul, map_smul, map_smul, smul_smul, smul_smul]
  congr 1
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hN0 : (Ideal.absNorm cc : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNc
  field_simp

end GlobalTheory.AlgDirMom
