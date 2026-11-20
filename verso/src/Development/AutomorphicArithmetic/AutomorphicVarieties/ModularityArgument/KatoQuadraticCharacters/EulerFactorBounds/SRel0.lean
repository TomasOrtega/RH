import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

/- English proof (translation)
Introduce `l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he c₀ Y hY r n`. Take `⟨bB, hL, b, hb, hC⟩` from `hY r n`. Take `⟨-, -, -, -, hadd, -, -, heq, -⟩` from `hA`. Establish `hN : 0 < N` using `Nat.pos_of_ne_zero (NeZero.ne N)`. Establish `h2 : 2 * e + 1 - 2 = 2 * e - 1` using `by omega`.

Rewrite `hL` using `[h2]`. Take `⟨-, -, -, -, -, -, -, hcy⟩` from `sSlD Ω ε X N hN`. Establish `hfix : ∀ (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (topM l n r (N * N)))ˣ), (repM (topM l n r (N * N)) y)⁻¹ * s * repM (topM l n r (N * N)) (y * (cycM (topM l n r (N * N)) s)⁻¹) ∈ fixMu Ω (topMu l n r N)`. Introduce `s y`. Establish `hm : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM (topM l n r (N * N)) (s * t) = cycM (topM l n r (N * N)) s * cycM (topM l n r (N * N)) t` using `fun s t => (hcy (topM l n r (N * N)) s).2.1 t`.

Establish `hr` using `(hcy (topM l n r (N * N)) s).2.2.1`. Use `(hcy (topM l n r (N * N)) _).2.2.2.1.2 ?_` and prove the remaining obligations. Establish `h1 : y * cycM (topM l n r (N * N)) ((repM (topM l n r (N * N)) y)⁻¹ * s) = cycM (topM l n r (N * N)) s` using `by conv_lhs => rw [← hr y]`. Rewrite using `[← hm, hr, mul_inv_cancel_left]`. Rewrite using `[hm, hr, eq_inv_mul_of_mul_eq h1]`.

Simplify using `[mul_comm, mul_left_comm]`. Establish `hB` using `sBStab Ω ε X l N (2 * e - 1) hN`. Take `⟨-, -, -, hsum, -, -, hgal, -⟩` from `sApi Ω ε X l n`. Set `P : X.Fn l →+ (Fin 2 → Qbar l)` to `AddMonoidHom.mk' pr hadd`. Use `⟨GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB), b, fun s y => ⟨?_, ?_⟩, hb, fun s y => ?_⟩` and prove the remaining obligations.

Conclude with `Submodule.sum_mem _ fun y' _ => (hB _ (hL _ (hfix s y')).1).1 _`. Establish `h1` using `hsum _ (Finset.univ.filter fun y' => redM l n r (N * N) y' = y) _ _ (fun y' _ => hgal (repM (topM l n r (N * N)) y') _ (((l : ℤ_[l]) ^ c₀) • _) (hL _ (hfix s y')).2)`. Establish `h3 : (∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) s y) = ∑ y' ∈ Finset.univ.filter (fun y' => redM l n r (N * N) y' = y), shB X l (topM l n r (N * N)) (clsBmu X l n r N x c d (2 * e + 1) gm) s y'`. Simplify using `only [Y0, GlobalTheory.KA.push, shB, clsBmu_eq, h2, map_sum]`. Conclude with `Finset.sum_comm`.

Simplify using `only [map_smul, ← Finset.smul_sum] at h1`. Use `beta_reduce`. Rewrite using `[h3]`. Conclude with `h1`. Establish `h4 : pr (GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB) s y) = YfB X l pr W e ψ n r N bB s y`.

Use `(map_sum P _ _).trans (Finset.sum_congr rfl fun y' _ => ?_)` and prove the remaining obligations. Conclude with `heq _ _ (hL _ (hfix s y')).1`. Rewrite using `[h4]`. Conclude with `hC s y`.
-/
theorem UpperTheory.V.Z.Kato.Nb.sRel0 :
    UpperTheory.V.Z.Kato.Nb.SRel0 := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he c₀ Y hY r n
  obtain ⟨bB, hL, b, hb, hC⟩ := hY r n
  obtain ⟨-, -, -, -, hadd, -, -, heq, -⟩ := hA
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h2 : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  rw [h2] at hL
  obtain ⟨-, -, -, -, -, -, -, hcy⟩ := sSlD Ω ε X N hN
  have hfix : ∀ (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (topM l n r (N * N)))ˣ),
      (repM (topM l n r (N * N)) y)⁻¹ * s * repM (topM l n r (N * N)) (y * (cycM (topM l n r (N * N)) s)⁻¹) ∈
        fixMu Ω (topMu l n r N) := by
    intro s y
    have hm : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM (topM l n r (N * N)) (s * t) = cycM (topM l n r (N * N)) s * cycM (topM l n r (N * N)) t :=
      fun s t => (hcy (topM l n r (N * N)) s).2.1 t
    have hr := (hcy (topM l n r (N * N)) s).2.2.1
    refine (hcy (topM l n r (N * N)) _).2.2.2.1.2 ?_
    have h1 : y * cycM (topM l n r (N * N)) ((repM (topM l n r (N * N)) y)⁻¹ * s) = cycM (topM l n r (N * N)) s := by
      conv_lhs => rw [← hr y]
      rw [← hm, hr, mul_inv_cancel_left]
    rw [hm, hr, eq_inv_mul_of_mul_eq h1]
    simp [mul_comm, mul_left_comm]
  have hB := sBStab Ω ε X l N (2 * e - 1) hN
  obtain ⟨-, -, -, hsum, -, -, hgal, -⟩ := sApi Ω ε X l n
  let P : X.Fn l →+ (Fin 2 → Qbar l) := AddMonoidHom.mk' pr hadd
  refine ⟨GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB), b, fun s y => ⟨?_, ?_⟩, hb, fun s y => ?_⟩
  · exact Submodule.sum_mem _ fun y' _ => (hB _ (hL _ (hfix s y')).1).1 _
  · have h1 := hsum _ (Finset.univ.filter fun y' => redM l n r (N * N) y' = y) _ _
      (fun y' _ => hgal (repM (topM l n r (N * N)) y') _ (((l : ℤ_[l]) ^ c₀) • _) (hL _ (hfix s y')).2)
    have h3 : (∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) s y) =
        ∑ y' ∈ Finset.univ.filter (fun y' => redM l n r (N * N) y' = y),
          shB X l (topM l n r (N * N)) (clsBmu X l n r N x c d (2 * e + 1) gm) s y' := by
      simp only [Y0, GlobalTheory.KA.push, shB, clsBmu_eq, h2, map_sum]
      exact Finset.sum_comm
    simp only [map_smul, ← Finset.smul_sum] at h1
    beta_reduce
    rw [h3]
    exact h1
  · have h4 : pr (GlobalTheory.KA.push (redM l n r (N * N)) (shB X l (topM l n r (N * N)) bB) s y) = YfB X l pr W e ψ n r N bB s y := by
      refine (map_sum P _ _).trans (Finset.sum_congr rfl fun y' _ => ?_)
      exact heq _ _ (hL _ (hfix s y')).1
    rw [h4]
    exact hC s y
