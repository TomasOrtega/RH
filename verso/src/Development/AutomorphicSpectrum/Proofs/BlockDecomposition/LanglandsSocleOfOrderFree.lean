import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseInvolutionApplyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleContragredientSocleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosocles
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.LSocle

section General

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Introduce `w`. Take `⟨v, rfl⟩` from `hf w`. Set `S : Subgroup G` to `{ carrier := {g | σ g (f v) = f v} one_mem' := by simp mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`.

Use the proof step `inv_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Establish `h1 : σ a⁻¹ (σ a (f v)) = f v`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[ha] at h1 }` and apply the resulting hypothesis. Set `T : Subgroup G` to `{ carrier := {g | ρ g v = v} one_mem' := by simp mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `inv_mem' := fun {a} ha => by`.

Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Establish `h1 : ρ a⁻¹ (ρ a v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules. Rewrite using `[ha] at h1 }` and apply the resulting hypothesis.

Establish `hT : IsOpen (T : Set G)` using `hρ v`. Establish `hTS : T ≤ S` using `fun g hg => by`. Establish `hg' : ρ g v = v` using `hg`. Use `show σ g (f v) = f v`. Rewrite using `[← f.isIntertwining, hg']`.

Conclude with `Subgroup.isOpen_mono hTS hT`.
-/
theorem isSmooth_of_surjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) : IsSmooth σ := by
  intro w
  obtain ⟨v, rfl⟩ := hf w
  let S : Subgroup G :=
    { carrier := {g | σ g (f v) = f v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : σ a⁻¹ (σ a (f v)) = f v := by
          rw [← Module.End.mul_apply, ← map_mul]; simp
        rwa [ha] at h1 }
  let T : Subgroup G :=
    { carrier := {g | ρ g v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ρ a⁻¹ (ρ a v) = v := by
          rw [← Module.End.mul_apply, ← map_mul]; simp
        rwa [ha] at h1 }
  have hT : IsOpen (T : Set G) := hρ v
  have hTS : T ≤ S := fun g hg => by
    have hg' : ρ g v = v := hg
    show σ g (f v) = f v
    rw [← f.isIntertwining, hg']
  exact Subgroup.isOpen_mono hTS hT

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `g` and use `⟨thetaW k N g, GlobalTheory.T.transpose_inverse_involution_apply N g⟩`.
-/
theorem thetaW_surjective (N : ℕ) : Function.Surjective (thetaW k N) :=
  fun g => ⟨thetaW k N g, GlobalTheory.T.transpose_inverse_involution_apply N g⟩

/- English proof (translation)
The claim follows from `MonoidHom.ext fun g => by show π (thetaW k N (thetaW k N g)) = π g rw [GlobalTheory.T.transpose_inverse_involution_apply N g]`.
-/
theorem comp_thetaW_thetaW {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) : (π.comp (thetaW k N)).comp (thetaW k N) = π :=
  MonoidHom.ext fun g => by
    show π (thetaW k N (thetaW k N g)) = π g
    rw [GlobalTheory.T.transpose_inverse_involution_apply N g]

/- English proof (translation)
Apply `GlobalTheory.FieldTransport.isCosocle_of_comp (thetaW_surjective N)` to reduce the goal to its premises. Use `show IsCosocle ((σ.comp (thetaW k N)).comp (thetaW k N)) _`. Rewrite using `[comp_thetaW_thetaW σ]`. Conclude with `h`.
-/
theorem isCosocle_comp_thetaW {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin N) k) W} {π : Representation ℂ (GL (Fin N) k) V}
    (h : IsCosocle σ (π.comp (thetaW k N))) : IsCosocle (σ.comp (thetaW k N)) π := by
  apply GlobalTheory.FieldTransport.isCosocle_of_comp (thetaW_surjective N)
  show IsCosocle ((σ.comp (thetaW k N)).comp (thetaW k N)) _
  rw [comp_thetaW_thetaW σ]
  exact h

/- English proof (translation)
Establish `E` using `GlobalTheory.T.gelfand_kazhdan_contragredient hGK N (σ.comp (thetaW k N)) hs hi`. Rewrite `E` using `[comp_thetaW_thetaW σ]`. Then use the resulting hypothesis.
-/
theorem equiv_contra_comp_thetaW (hGK : GKLocal k) {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin N) k) W) (hs : IsSmooth (σ.comp (thetaW k N)))
    (hi : Representation.IsIrreducible (σ.comp (thetaW k N))) : Nonempty (σ.Equiv (contra (σ.comp (thetaW k N)))) := by
  have E := GlobalTheory.T.gelfand_kazhdan_contragredient hGK N (σ.comp (thetaW k N)) hs hi
  rwa [comp_thetaW_thetaW σ] at E

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `⟨Representation.Equiv.refl _⟩`.
-/
theorem prodIrr_congr {h N : ℕ} {x y : Fin h → IrrGL k} (e : x = y) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Take `⟨hd2, ⟨E2⟩⟩` from `GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK y hdy`. Take `⟨E3⟩` from `prodIrr_congr e3 hd2 hd0`. Establish `hc1 : IsCosocle π ((prodIrr y hdy).comp (thetaW k N))` using `hc.of_equiv (Representation.Equiv.refl _) (E2.trans E3).symm`. Establish `hc2 : IsCosocle (π.comp (thetaW k N)) (prodIrr y hdy)` using `isCosocle_comp_thetaW hc1`. Establish `hs : IsSmooth (π.comp (thetaW k N))`.

Take `⟨-, f, hf, -⟩` from `hc2`. Conclude with `isSmooth_of_surjective (isSmooth_prodIrr y hdy) f hf`. Establish `hsoc` using `GlobalTheory.T.cosocle_contragredient_socle hA (π.comp (thetaW k N)) (prodIrr y hdy) (isSmooth_prodIrr y hdy) (GlobalTheory.T.product_irreducible_finite_length hA y hdy) hc2`. Take `⟨E4⟩` from `equiv_contra_comp_thetaW hGK π hs hc2.1`. Take `⟨hd5, ⟨E5⟩⟩` from `GlobalTheory.T.contragredient_product_irreducible hA y hdy`.

Take `⟨E6⟩` from `prodIrr_congr e6 hd5 hd`. Conclude with `hsoc.of_equiv E4.symm (E5.trans E6)`.
-/
theorem isSocle_rev_of_isCosocle (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ}
    (x y : Fin h → IrrGL k) (hd0 : ∑ a, (x a).1 = N) (hd : ∑ a, ((x ∘ Fin.rev) a).1 = N) (hdy : ∑ a, (y a).1 = N)
    (e3 : (fun a => dualCl (y (Fin.rev a))) = x) (e6 : (fun a => dualCl (y a)) = x ∘ Fin.rev)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hc : IsCosocle π (prodIrr x hd0)) : IsSocle π (prodIrr (x ∘ Fin.rev) hd) := by
  obtain ⟨hd2, ⟨E2⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK y hdy
  obtain ⟨E3⟩ := prodIrr_congr e3 hd2 hd0
  have hc1 : IsCosocle π ((prodIrr y hdy).comp (thetaW k N)) :=
    hc.of_equiv (Representation.Equiv.refl _) (E2.trans E3).symm
  have hc2 : IsCosocle (π.comp (thetaW k N)) (prodIrr y hdy) := isCosocle_comp_thetaW hc1
  have hs : IsSmooth (π.comp (thetaW k N)) := by
    obtain ⟨-, f, hf, -⟩ := hc2
    exact isSmooth_of_surjective (isSmooth_prodIrr y hdy) f hf
  have hsoc := GlobalTheory.T.cosocle_contragredient_socle hA (π.comp (thetaW k N)) (prodIrr y hdy) (isSmooth_prodIrr y hdy)
    (GlobalTheory.T.product_irreducible_finite_length hA y hdy) hc2
  obtain ⟨E4⟩ := equiv_contra_comp_thetaW hGK π hs hc2.1
  obtain ⟨hd5, ⟨E5⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA y hdy
  obtain ⟨E6⟩ := prodIrr_congr e6 hd5 hd
  exact hsoc.of_equiv E4.symm (E5.trans E6)

/- English proof (translation)
Introduce `k _ _ _ _ hA hGK hLO 𝔪 h N x hd hx V _ _ π hπ`. Establish `hd0 : ∑ a, (x a).1 = N`. Rewrite using `[← hd]`. Conclude with `(Equiv.sum_comp Fin.revPerm (fun a => (x a).1)).symm`. Establish `hc` using `hLO 𝔪 h N x hd0 hx π hπ`.

Take `⟨hdy, -⟩` from `GlobalTheory.T.contragredient_product_irreducible hA (x ∘ Fin.rev) hd`. Conclude with `isSocle_rev_of_isCosocle hA hGK x (fun a => dualCl ((x ∘ Fin.rev) a)) hd0 hd hdy (funext fun a => by`. Simplify using `only [Function.comp_apply, Fin.rev_rev]`. Conclude with `GlobalTheory.T.dual_class_involutive hA (x a))`. Use the proof step `(funext fun a => GlobalTheory.T.dual_class_involutive hA (x (Fin.rev a))) π hc`.
-/
theorem lSocleGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k → LOrderFree k → LSocleGL k := by
  intro k _ _ _ _ hA hGK hLO 𝔪 h N x hd hx V _ _ π hπ
  have hd0 : ∑ a, (x a).1 = N := by
    rw [← hd]
    exact (Equiv.sum_comp Fin.revPerm (fun a => (x a).1)).symm
  have hc := hLO 𝔪 h N x hd0 hx π hπ
  obtain ⟨hdy, -⟩ := GlobalTheory.T.contragredient_product_irreducible hA (x ∘ Fin.rev) hd
  exact isSocle_rev_of_isCosocle hA hGK x (fun a => dualCl ((x ∘ Fin.rev) a)) hd0 hd hdy
    (funext fun a => by
      simp only [Function.comp_apply, Fin.rev_rev]
      exact GlobalTheory.T.dual_class_involutive hA (x a))
    (funext fun a => GlobalTheory.T.dual_class_involutive hA (x (Fin.rev a))) π hc

end GlobalTheory.CompanionTheory.LSocle
