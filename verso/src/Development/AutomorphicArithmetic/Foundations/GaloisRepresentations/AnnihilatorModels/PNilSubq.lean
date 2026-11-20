import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalInterAlt
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Proceed by induction on `n generalizing x with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]`.
-/
private theorem pow_inter {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (c : M →ₗ[L] N) (f : End L M) (g : End L N) (h : ∀ x, c (f x) = g (c x)) (n : ℕ) (x : M) :
    c ((f ^ n) x) = (g ^ n) (c x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qi58.aeval_inter c f g h Q x`.
-/
private theorem aeval_inter {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (c : M →ₗ[L] N) (f : End L M) (g : End L N) (h : ∀ x, c (f x) = g (c x)) (Q : Polynomial L) (x : M) :
    c (Polynomial.aeval f Q x) = Polynomial.aeval g Q (c x) :=
  _root_.UpperTheory.Reformulated.B.Qi58.aeval_inter c f g h Q x

/- English proof (translation)
Introduce `hA hE F G B _ _ _ _ σ ψ L _ _ e hB V W _ _ _ _ _ _ _ _ _ ρ ρ' hS hAdm`. Take `⟨U, _, _, ρU, i, p, hi, hinj, hp, hsurj⟩` from `hS`. Use `letI : Module F U := Module.compHom U (algebraMap F L)`. Use `haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Use `haveI : Module.Finite L U := Module.Finite.of_injective i hinj`.

Use `haveI : Module.Finite L W := Module.Finite.of_surjective p hsurj`. Establish `hU : admitted σ e ρU` using `(hA F G B σ L e hB U V ρU ρ i hi).1 hinj hAdm`. Take `⟨hW, hmap⟩` from `(hA F G B σ L e hB U W ρU ρ' p hp).2 hsurj hU`. Use `⟨hW, fun Q hQ => ?_⟩` and prove the remaining obligations. Take `⟨N, hN⟩ : NilD σ ψ ρU Q` from `hE F G B σ ψ L U ρU Unit (fun _ => V) (fun _ => ρ) (fun _ => i) (fun _ => hi) (fun v h => hinj (by simpa using h ())) Q (fun _ => hQ)`.

Use `⟨N, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[← hmap]`. Take `⟨x, hx, rfl⟩` from `hy`. Establish `h1 : ∀ z : U ⊗[F] B, AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) (onPer ψ L U z) = onPer ψ L W (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) z)`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul u b => simp [onPer]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Rewrite using `[← pow_inter _ _ _ (fun z => aeval_inter _ _ _ h1 Q z) N x, hN x hx, map_zero]`.
-/
theorem UpperTheory.Gal.crystallineComparison.nilSubq_of :
    AdmExact → NilEmb → NilSubq := by
  intro hA hE F G B _ _ _ _ σ ψ L _ _ e hB V W _ _ _ _ _ _ _ _ _ ρ ρ' hS hAdm
  obtain ⟨U, _, _, ρU, i, p, hi, hinj, hp, hsurj⟩ := hS
  letI : Module F U := Module.compHom U (algebraMap F L)
  haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite L U := Module.Finite.of_injective i hinj
  haveI : Module.Finite L W := Module.Finite.of_surjective p hsurj
  have hU : admitted σ e ρU := (hA F G B σ L e hB U V ρU ρ i hi).1 hinj hAdm
  obtain ⟨hW, hmap⟩ := (hA F G B σ L e hB U W ρU ρ' p hp).2 hsurj hU
  refine ⟨hW, fun Q hQ => ?_⟩
  obtain ⟨N, hN⟩ : NilD σ ψ ρU Q :=
    hE F G B σ ψ L U ρU Unit (fun _ => V) (fun _ => ρ) (fun _ => i) (fun _ => hi)
      (fun v h => hinj (by simpa using h ())) Q (fun _ => hQ)
  refine ⟨N, fun y hy => ?_⟩
  rw [← hmap] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have h1 : ∀ z : U ⊗[F] B, AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) (onPer ψ L U z) =
      onPer ψ L W (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul u b => simp [onPer]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← pow_inter _ _ _ (fun z => aeval_inter _ _ _ h1 Q z) N x, hN x hx, map_zero]
