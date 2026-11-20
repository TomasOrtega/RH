import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomLiftResiduePointFiniteFlatStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.TateResidue

open WithConv

/- English proof (translation)
The claim follows from `(IsUnit.of_pow_eq_one (G.pts_pow_self n b) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mul_right_cancel (h.trans (one_mul _).symm)`.
-/
theorem conv_eq_one_of_mul {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)
    {B : Type} [CommRing B] [Algebra O B] (n : ℕ) (a b : WithConv (G.A n →ₐ[O] B))
    (h : a * b = b) : a = 1 :=
  (IsUnit.of_pow_eq_one (G.pts_pow_self n b)
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mul_right_cancel (h.trans (one_mul _).symm)

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ hv G`. Establish `: IsIntegrallyClosedIn O C` using `isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h)⟩`. Use `set k := IsLocalRing.ResidueField O`. Use `set π := G.tatePush (Algebra.ofId O k)`. Establish `hlift : ∀ (n : ℕ) (c : G.A n →ₐ[O] k), ∃ t : G.Tate, (π t).pt n = c`.

Introduce `n c`. Take `⟨x, hx⟩` from `GlobalTheory.T.exists_algHom_lift_residuePoint_finite_flat p C v O hv (G.A n) c`. Take `⟨t, ht⟩` from `G.pt_surjective C n x`. Use `⟨t, AlgHom.ext fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[tatePush_pt]`.

Express the relevant statement in the definitionally equal form `IsLocalRing.residue O (t.pt n a) = c a`. Rewrite using `[show t.pt n = x from ht]`. Conclude with `hx a`. Use `⟨fun n c => ?_, ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `hlift n c`.

Conclude with `⟨π t, ht⟩`. Use `G.finite_tate C` as an intermediate fact. Establish `hπ : Function.Surjective π`. Use `TateFree.surjective_of_mod π TateOver.eq_zero_of_forall_pow_smul fun y => ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `hlift 1 (y.pt 1)`.

Take `⟨z, hz⟩` from `(TateOver.conv_eq_one_iff (y - π x) 1).1 <| by`. Establish `h1 : (y - π x + π x).conv 1 = y.conv 1` using `by rw [sub_add_cancel]`. Rewrite `h1` using `[TateOver.add_conv]`. Establish `h2 : (π x).conv 1 = y.conv 1` using `congrArg toConv hx`. Rewrite `h1` using `[h2]`.

Conclude with `conv_eq_one_of_mul G _ _ _ h1`. Conclude with `⟨x, z, by rwa [pow_one] at hz⟩`. Establish `: Module.Finite ℤ_[p] (G.TateOver k)` using `Module.Finite.of_surjective π hπ`. Establish `: Module.Free ℤ_[p] (G.TateOver k)` using `inferInstance`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`.

Use `⟨s, fun t => LinearMap.congr_fun hs t, fun n t t' h => ?_⟩` and prove the remaining obligations. Establish `hd : (t - t').conv n = 1`. Establish `h1 : (t - t' + t').conv n = t.conv n` using `by rw [sub_add_cancel]`. Rewrite `h1` using `[TateOver.add_conv, show t'.conv n = t.conv n from congrArg toConv h.symm]`. Conclude with `conv_eq_one_of_mul G _ _ _ h1`.

Take `⟨u, hu⟩` from `(TateOver.conv_eq_one_iff (t - t') n).1 hd`. Establish `h3 : (s t - s t').conv n = 1`. Rewrite using `[← map_sub, ← hu, map_smul]`. Conclude with `(TateOver.conv_eq_one_iff _ n).2 ⟨_, rfl⟩`. Establish `h4 : (s t - s t' + s t').conv n = (s t).conv n` using `by rw [sub_add_cancel]`.

Rewrite `h4` using `[TateOver.add_conv, h3, one_mul]`. Conclude with `congrArg ofConv h4.symm`.
-/
theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O), ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c) ∧ ∃ s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate, (∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t) ∧ ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)), t.pt n = t'.pt n → (s t).pt n = (s t').pt n := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h)⟩
  set k := IsLocalRing.ResidueField O
  set π := G.tatePush (Algebra.ofId O k)

  have hlift : ∀ (n : ℕ) (c : G.A n →ₐ[O] k), ∃ t : G.Tate, (π t).pt n = c := by
    intro n c
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_algHom_lift_residuePoint_finite_flat p C v O hv (G.A n) c
    obtain ⟨t, ht⟩ := G.pt_surjective C n x
    refine ⟨t, AlgHom.ext fun a => ?_⟩
    rw [tatePush_pt]
    change IsLocalRing.residue O (t.pt n a) = c a
    rw [show t.pt n = x from ht]
    exact hx a
  refine ⟨fun n c => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hlift n c
    exact ⟨π t, ht⟩
  have := G.finite_tate C
  have hπ : Function.Surjective π := by
    refine TateFree.surjective_of_mod π TateOver.eq_zero_of_forall_pow_smul fun y => ?_
    obtain ⟨x, hx⟩ := hlift 1 (y.pt 1)
    obtain ⟨z, hz⟩ := (TateOver.conv_eq_one_iff (y - π x) 1).1 <| by
      have h1 : (y - π x + π x).conv 1 = y.conv 1 := by rw [sub_add_cancel]
      rw [TateOver.add_conv] at h1
      have h2 : (π x).conv 1 = y.conv 1 := congrArg toConv hx
      rw [h2] at h1
      exact conv_eq_one_of_mul G _ _ _ h1
    exact ⟨x, z, by rwa [pow_one] at hz⟩
  have : Module.Finite ℤ_[p] (G.TateOver k) := Module.Finite.of_surjective π hπ
  have : Module.Free ℤ_[p] (G.TateOver k) := inferInstance
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨s, fun t => LinearMap.congr_fun hs t, fun n t t' h => ?_⟩
  have hd : (t - t').conv n = 1 := by
    have h1 : (t - t' + t').conv n = t.conv n := by rw [sub_add_cancel]
    rw [TateOver.add_conv, show t'.conv n = t.conv n from congrArg toConv h.symm] at h1
    exact conv_eq_one_of_mul G _ _ _ h1
  obtain ⟨u, hu⟩ := (TateOver.conv_eq_one_iff (t - t') n).1 hd
  have h3 : (s t - s t').conv n = 1 := by
    rw [← map_sub, ← hu, map_smul]
    exact (TateOver.conv_eq_one_iff _ n).2 ⟨_, rfl⟩
  have h4 : (s t - s t' + s t').conv n = (s t).conv n := by rw [sub_add_cancel]
  rw [TateOver.add_conv, h3, one_mul] at h4
  exact congrArg ofConv h4.symm

end GlobalTheory.TateResidue
