import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairSubGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleave
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel Zc
open PositivityTheory.Pf1.SegRepC.SegTwo

namespace PositivityTheory.RgGu.SRC

namespace SrRev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨hv, f, id, id⟩`.
-/
theorem transfer {N : ℕ} {v w : Fin 2 → IrrGL k} (h : v = w) (hv : ∑ a, (v a).1 = N) {W : Type}
    [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ (GL (Fin N) k) W} (f : ω.IntertwiningMap (prodIrr v hv)) :
    ∃ (hw : ∑ a, (w a).1 = N) (f' : ω.IntertwiningMap (prodIrr w hw)),
      (Function.Injective f → Function.Injective f') ∧ (Function.Surjective f' → Function.Surjective f) := by
  subst h
  exact ⟨hv, f, id, id⟩

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem jmc {h N : ℕ} {x x' : Fin h → IrrGL k} (e : x = x') (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst e
  rfl

end SrRev

open SrRev

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Assume the negation of the conclusion as `h2`. Establish `hA` using `GlobalTheory.CompanionTheory.BZCuspPair.irrAdm`. Set `x : IrrGL k` to `IrrGL.of σ.ρ σ.smooth σ.irr`. Establish `hx : x.IsCusp` using `⟨hd, isCuspidal_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) hσ⟩`. Set `u : Fin 2 → IrrGL k` to `fun a => x.nu ((a : ℕ) : ℂ)`.

Establish `hu1 : ∀ a, (u a).1 = d` using `fun _ => rfl`. Establish `hu : ∑ a, (u a).1 = 2 * d` using `by simp only [hu1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Establish `hu' : ∑ a, (u (Fin.rev a)).1 = 2 * d`. Simplify using `only [hu1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Establish `he : stdBlocks (fun a => (u a).1) hu = consecBlocks 2 d`.

Use `Equiv.ext ?_` and prove the remaining obligations. Introduce and unpack `⟨a, j⟩`. Use `Fin.ext ?_` and prove the remaining obligations. Use `(Eq.trans ?_ (consecBlocks_val 2 d a j).symm)` and prove the remaining obligations. Rewrite using `[stdBlocks_val]`.

Apply the tactic sequence `fin_cases a <;> simp [hu1, Fin.sum_univ_two, mul_comm, add_comm]`. Establish `he' : stdBlocks (fun a => (u (Fin.rev a)).1) hu' = consecBlocks 2 d`. Use `Equiv.ext ?_` and prove the remaining obligations. Introduce and unpack `⟨a, j⟩`. Use `Fin.ext ?_` and prove the remaining obligations.

Use `(Eq.trans ?_ (consecBlocks_val 2 d a j).symm)` and prove the remaining obligations. Rewrite using `[stdBlocks_val]`. Apply the tactic sequence `fin_cases a <;> simp [hu1, Fin.sum_univ_two, mul_comm, add_comm]`. Set `φ : ∀ a, (segTerm σ.ρ 2 a).Equiv (u a).rep` to `fun a => (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) _).trans (x.twEquiv _ (isSmoothChar_absPow _))`. Establish `Φ : (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)).Equiv (prodIrr u hu)`.

Unfold `prodIrr`. Rewrite using `[he]`. Conclude with `multiProdEquiv (consecBlocks 2 d) φ`. Set `ι : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2))` to `⟨S.toSubmodule.subtype, fun _ => rfl⟩`. Set `f : S.toRepresentation.IntertwiningMap (prodIrr u hu)` to `Φ.toIntertwiningMap.comp ι`.

Establish `hf : Function.Injective f` using `Φ.toLinearEquiv.injective.comp Subtype.val_injective`. Establish `j1 : 1 ≤ jm u hu S.toRepresentation`. Establish `: jm u hu S.toRepresentation = 1`. Unfold `jm`. Rewrite using `[he]`.

Conclude with `(jhMult_congr_left (piTensorEquiv φ) _).symm.trans h1`. Rewrite using `[this]`. Establish `j2 : 1 ≤ jm (fun a => u (Fin.rev a)) hu' S.toRepresentation`. Establish `: jm (fun a => u (Fin.rev a)) hu' S.toRepresentation ≠ 0`. Unfold `jm`.

Rewrite using `[he']`. Conclude with `fun h => h2 ((jhMult_congr_left (piTensorEquiv fun a => φ (Fin.rev a)) _).trans h)`. Conclude with `Order.one_le_iff_ne_zero.2 this`. Establish `hux : u = ![x, x.nu 1]`. Use function extensionality and compare the values at `a`.

Use `fin_cases a`. Simplify using `[u]`. Simplify using `[u]`. Establish `hux' : (fun a => u (Fin.rev a)) = ![x.nu 1, x]`. Use function extensionality and compare the values at `a`.

Use `fin_cases a`. Simplify using `[u]`. Simplify using `[u]`. Take `⟨hw, f', hf', hs'⟩` from `transfer hux hu f`. Establish `hw' : ∑ a, (![x.nu 1, x] a).1 = 2 * d` using `by rw [← hux']; exact hu'`.

Establish `hnx : x ≠ x.nu 1`. Introduce `h`. Establish `h0 : x.nu ((0 : ℕ) : ℂ) = x.nu ((1 : ℕ) : ℂ)` using `by simpa using h`. Conclude with `absurd ((GlobalTheory.LocGL.IrrGL.nu_natCast_inj hd).1 h0) (by decide)`. Establish `hsurj` using `GlobalTheory.CompanionTheory.CuspPairSub.surjective_of_jm hA hx (hx.nu 1) hnx hw hw' f' (hf' hf) (by rw [← jmc hux hu hw]; exact j1) (by rw [← jmc hux' hu' hw']; exact j2)`.

Establish `hsf` using `hs' hsurj`. Establish `hι : Function.Surjective ι`. Introduce `v`. Take `⟨w, hw⟩` from `hsf (Φ v)`. Conclude with `⟨w, Φ.toLinearEquiv.injective hw⟩`.

Establish `htop : S = ⊤`. Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `hι v`. Conclude with `w.2`. Substitute `htop` using the available equality.

Conclude with `hR k d hd σ hσ (GlobalTheory.Parabolic.isIrreducible_of_equiv (topEquiv _) hS)`.
-/
theorem jhMult_rev_jac_sub (hG : GeometricLemma) (hR : RhoNuRhoReducible) {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)))
    (hS : S.toRepresentation.IsIrreducible)
    (h1 : jhMult (piTensor (segTerm σ.ρ 2)) (jac (consecBlocks 2 d) S.toRepresentation) = 1) :
    jhMult (revTensor σ) (jac (consecBlocks 2 d) S.toRepresentation) = 0 := by
  by_contra h2
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  let x : IrrGL k := IrrGL.of σ.ρ σ.smooth σ.irr
  have hx : x.IsCusp := ⟨hd, isCuspidal_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) hσ⟩
  let u : Fin 2 → IrrGL k := fun a => x.nu ((a : ℕ) : ℂ)
  have hu1 : ∀ a, (u a).1 = d := fun _ => rfl
  have hu : ∑ a, (u a).1 = 2 * d := by simp only [hu1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hu' : ∑ a, (u (Fin.rev a)).1 = 2 * d := by
    simp only [hu1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have he : stdBlocks (fun a => (u a).1) hu = consecBlocks 2 d := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (Eq.trans ?_ (consecBlocks_val 2 d a j).symm)
    rw [stdBlocks_val]
    fin_cases a <;> simp [hu1, Fin.sum_univ_two, mul_comm, add_comm]
  have he' : stdBlocks (fun a => (u (Fin.rev a)).1) hu' = consecBlocks 2 d := by
    refine Equiv.ext ?_
    rintro ⟨a, j⟩
    refine Fin.ext ?_
    refine (Eq.trans ?_ (consecBlocks_val 2 d a j).symm)
    rw [stdBlocks_val]
    fin_cases a <;> simp [hu1, Fin.sum_univ_two, mul_comm, add_comm]
  let φ : ∀ a, (segTerm σ.ρ 2 a).Equiv (u a).rep := fun a =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) _).trans (x.twEquiv _ (isSmoothChar_absPow _))
  have Φ : (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)).Equiv (prodIrr u hu) := by
    unfold prodIrr
    rw [he]
    exact multiProdEquiv (consecBlocks 2 d) φ
  let ι : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let f : S.toRepresentation.IntertwiningMap (prodIrr u hu) := Φ.toIntertwiningMap.comp ι
  have hf : Function.Injective f := Φ.toLinearEquiv.injective.comp Subtype.val_injective
  have j1 : 1 ≤ jm u hu S.toRepresentation := by
    have : jm u hu S.toRepresentation = 1 := by
      unfold jm
      rw [he]
      exact (jhMult_congr_left (piTensorEquiv φ) _).symm.trans h1
    rw [this]
  have j2 : 1 ≤ jm (fun a => u (Fin.rev a)) hu' S.toRepresentation := by
    have : jm (fun a => u (Fin.rev a)) hu' S.toRepresentation ≠ 0 := by
      unfold jm
      rw [he']
      exact fun h => h2 ((jhMult_congr_left (piTensorEquiv fun a => φ (Fin.rev a)) _).trans h)
    exact Order.one_le_iff_ne_zero.2 this
  have hux : u = ![x, x.nu 1] := by
    funext a
    fin_cases a
    · simp [u]
    · simp [u]
  have hux' : (fun a => u (Fin.rev a)) = ![x.nu 1, x] := by
    funext a
    fin_cases a
    · simp [u]
    · simp [u]
  obtain ⟨hw, f', hf', hs'⟩ := transfer hux hu f
  have hw' : ∑ a, (![x.nu 1, x] a).1 = 2 * d := by rw [← hux']; exact hu'
  have hnx : x ≠ x.nu 1 := by
    intro h
    have h0 : x.nu ((0 : ℕ) : ℂ) = x.nu ((1 : ℕ) : ℂ) := by simpa using h
    exact absurd ((GlobalTheory.LocGL.IrrGL.nu_natCast_inj hd).1 h0) (by decide)
  have hsurj := GlobalTheory.CompanionTheory.CuspPairSub.surjective_of_jm hA hx (hx.nu 1) hnx hw hw' f' (hf' hf)
    (by rw [← jmc hux hu hw]; exact j1) (by rw [← jmc hux' hu' hw']; exact j2)
  have hsf := hs' hsurj
  have hι : Function.Surjective ι := by
    intro v
    obtain ⟨w, hw⟩ := hsf (Φ v)
    exact ⟨w, Φ.toLinearEquiv.injective hw⟩
  have htop : S = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨w, rfl⟩ := hι v
    exact w.2
  subst htop
  exact hR k d hd σ hσ (GlobalTheory.Parabolic.isIrreducible_of_equiv (topEquiv _) hS)

end PositivityTheory.RgGu.SRC

end
