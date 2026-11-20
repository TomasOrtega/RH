import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Formalism.CoboundaryTransfers

/- English proof (translation)
Introduce `O A _ _ _ B M D _ _ _ _ W I _ k b hk hMb hQI hφI n hn`. Take `⟨v, hv⟩` from `hk`. Take `⟨d, hd⟩ : ∃ d, k * b = M + 1 + d` from `⟨k * b - (M + 1), by omega⟩`. Establish `hmem : ∀ x : W.N, (B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (x : D)) ∈ W.N` using `fun x => W.N.smul_mem _ (W.φ_N x x.2)`. Set `g : W.N →+ W.N` to `{ toFun := fun x => ⟨_, hmem x⟩ map_zero' := by ext; simp map_add' := fun x y => by ext; simp [smul_add] }`.

Establish `hg : ∀ x : W.N, W.φ (B.X ^ b • (x : D)) = B.X ^ b • ((g x : W.N) : D)`. Introduce `x`. Use `show _ = B.X ^ b • ((B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (x : D)))`. Rewrite using `[W.φ_smul, map_pow, hv, smul_smul, smul_smul]`. Use `congr 1`.

Rewrite using `[mul_pow, mul_pow, ← pow_mul, hd]`. Expand and normalize the polynomial expressions, which then agree. Establish `hφpow : ∀ (j : ℕ) (r : A), r ∈ I ^ j → B.φ r ∈ I ^ j`. Introduce `j r hr`. Establish `h1 : Ideal.map (B.φ : A →+* A) I ≤ I` using `Ideal.map_le_iff_le_comap.2 (fun a ha => hφI a ha)`.

Establish `h2 : (B.φ : A →+* A) r ∈ Ideal.map (B.φ : A →+* A) (I ^ j)` using `Ideal.mem_map_of_mem _ hr`. Rewrite `h2` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono h1 j h2`. Establish `hcontr : ∀ j : ℕ, ∀ x ∈ (I ^ j • ⊤ : Submodule A W.N), g x ∈ (I ^ (j + 1) • ⊤ : Submodule A W.N)`. Introduce `j x hx`.

Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `r hr m _`. Establish `e : g (r • m) = (B.φ r * B.Q) • (⟨(B.Q ^ d * v ^ b) • (B.Q ^ M • W.φ (m : D)), W.N.smul_mem _ (W.φ_N m m.2)⟩ : W.N)`. Use `ext`. Use `show (B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (r • (m : D))) = _`.

Rewrite using `[W.φ_smul]`. Simplify using `only [SetLike.mk_smul_mk, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `Submodule.smul_mem_smul ?_ Submodule.mem_top` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul (hφpow j r hr) hQI`. Introduce `x y hx hy`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Establish `hbij` using `_root_.subIdBijectiveOfContracting_holds A W.N I g hcontr`. Take `⟨z, hz⟩` from `hbij.2 (-(⟨n, hn⟩ : W.N))`. Use `⟨z, z.2, ?_⟩` and prove the remaining obligations. Rewrite using `[hg z, ← smul_sub]`.

Use `congr 1`. Establish `: ((g z - z : W.N) : D) = -n`. Use `congrArg (fun t : W.N => (t : D)) hz` as an intermediate fact. Simplify using `using this`. Establish `h3 : ((g z : W.N) : D) - (z : D) = -n` using `by simpa using this`.

Rewrite using `[← neg_sub, h3, neg_neg]`.
-/
theorem phi_map_surjective : StatPhiOnto := by
  intro O A _ _ _ B M D _ _ _ _ W I _ k b hk hMb hQI hφI n hn
  obtain ⟨v, hv⟩ := hk
  obtain ⟨d, hd⟩ : ∃ d, k * b = M + 1 + d := ⟨k * b - (M + 1), by omega⟩

  have hmem : ∀ x : W.N, (B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (x : D)) ∈ W.N :=
    fun x => W.N.smul_mem _ (W.φ_N x x.2)
  let g : W.N →+ W.N :=
    { toFun := fun x => ⟨_, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  have hg : ∀ x : W.N, W.φ (B.X ^ b • (x : D)) = B.X ^ b • ((g x : W.N) : D) := by
    intro x
    show _ = B.X ^ b • ((B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (x : D)))
    rw [W.φ_smul, map_pow, hv, smul_smul, smul_smul]
    congr 1
    rw [mul_pow, mul_pow, ← pow_mul, hd]
    ring
  have hφpow : ∀ (j : ℕ) (r : A), r ∈ I ^ j → B.φ r ∈ I ^ j := by
    intro j r hr
    have h1 : Ideal.map (B.φ : A →+* A) I ≤ I :=
      Ideal.map_le_iff_le_comap.2 (fun a ha => hφI a ha)
    have h2 : (B.φ : A →+* A) r ∈ Ideal.map (B.φ : A →+* A) (I ^ j) := Ideal.mem_map_of_mem _ hr
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 j h2
  have hcontr : ∀ j : ℕ, ∀ x ∈ (I ^ j • ⊤ : Submodule A W.N), g x ∈ (I ^ (j + 1) • ⊤ : Submodule A W.N) := by
    intro j x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m _
      have e : g (r • m) = (B.φ r * B.Q) •
          (⟨(B.Q ^ d * v ^ b) • (B.Q ^ M • W.φ (m : D)), W.N.smul_mem _ (W.φ_N m m.2)⟩ : W.N) := by
        ext
        show (B.Q * (B.Q ^ d * v ^ b)) • (B.Q ^ M • W.φ (r • (m : D))) = _
        rw [W.φ_smul]
        simp only [SetLike.mk_smul_mk, smul_smul]
        congr 1
        ring
      rw [e]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [pow_succ]
      exact Ideal.mul_mem_mul (hφpow j r hr) hQI
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  have hbij := _root_.subIdBijectiveOfContracting_holds A W.N I g hcontr
  obtain ⟨z, hz⟩ := hbij.2 (-(⟨n, hn⟩ : W.N))
  refine ⟨z, z.2, ?_⟩
  rw [hg z, ← smul_sub]
  congr 1
  have : ((g z - z : W.N) : D) = -n := by
    have := congrArg (fun t : W.N => (t : D)) hz
    simpa using this
  have h3 : ((g z : W.N) : D) - (z : D) = -n := by simpa using this
  rw [← neg_sub, h3, neg_neg]

end Formalism.RepresentationBoundsCohomology.N2
