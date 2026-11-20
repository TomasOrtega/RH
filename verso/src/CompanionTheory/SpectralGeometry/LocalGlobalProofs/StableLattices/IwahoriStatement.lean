import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsPiecesPiece
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriUpperLowerFactorizationStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntiInvolutionSwapsUpperLowerStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruenceStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HermitianAdjointExistsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceEndomorphismInverseExistsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UpperTriangularInverseIsUpperStatement

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

/- English proof (translation)
Use `⟨?_, ?_, ?_, GlobalTheory.T.congruence_endomorphism_inverse_exists Λ hΛ π hπ⟩` and prove the remaining obligations. Introduce `x hx y hy v hv`. Take `⟨z, hz, e1⟩` from `hy v hv`. Take `⟨w, hw, e2⟩` from `hx z hz`. Use `⟨π • w, lat_smul hΛ hπ.le hw, ?_⟩` and prove the remaining obligations.

Simplify using `[Module.End.mul_apply, e1, e2]`. Introduce `i x hx v hv`. Take `⟨z, hz, e1⟩` from `hx v hv`. Conclude with `⟨P i z, hP i z hz, by simp [Module.End.mul_apply, e1]⟩`. Introduce `i x hx v hv`.

Conclude with `hx _ (hP i v hv)`.
-/
theorem isCongIdeal_congJ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] {Λ : AddSubgroup V} (hΛ : IsLat L Λ)
    {π : L} (hπ : ‖π‖ < 1) {ι : Type} (P : ι → Module.End L V)
    (hP : ∀ i, ∀ x ∈ Λ, P i x ∈ Λ) : IsCongIdeal (congJ Λ π) P := by
  refine ⟨?_, ?_, ?_, GlobalTheory.T.congruence_endomorphism_inverse_exists Λ hΛ π hπ⟩
  · intro x hx y hy v hv
    obtain ⟨z, hz, e1⟩ := hy v hv
    obtain ⟨w, hw, e2⟩ := hx z hz
    refine ⟨π • w, lat_smul hΛ hπ.le hw, ?_⟩
    simp [Module.End.mul_apply, e1, e2]
  · intro i x hx v hv
    obtain ⟨z, hz, e1⟩ := hx v hv
    exact ⟨P i z, hP i z hz, by simp [Module.End.mul_apply, e1]⟩
  · intro i x hx v hv
    exact hx _ (hP i v hv)

/- English proof (translation)
Introduce `v hv`. Take `⟨z, hz, e1⟩` from `hx v hv`. Use `⟨c • z, lat_smul hΛ hc hz, ?_⟩` and prove the remaining obligations. Simplify using `[e1, smul_comm c π z]`.
-/
theorem congJ_smul {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (π : L) (c : L) (hc : ‖c‖ ≤ 1) (x : Module.End L V)
    (hx : x ∈ congJ Λ π) : c • x ∈ congJ Λ π := by
  intro v hv
  obtain ⟨z, hz, e1⟩ := hx v hv
  refine ⟨c • z, lat_smul hΛ hc hz, ?_⟩
  simp [e1, smul_comm c π z]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H i j hij`. Conclude with `H i j (by have := wt_le i; have := wt_le j; simp only; omega)`. Introduce `H i j hij`. Use `H i j ?_` and prove the remaining obligations.

Use `wt_le i` as an intermediate fact. Use `wt_le j` as an intermediate fact. Simplify using `only at hij`. Use linear arithmetic over natural numbers and integers.
-/
theorem isUpper_rev_iff {E : Type} [Ring E] {l : ℕ} (P : Idx l → E) (b : E) :
    IsUpper (fun i => 2 * l - wt i) P b ↔ IsLower wt P b := by
  constructor
  · intro H i j hij
    exact H i j (by have := wt_le i; have := wt_le j; simp only; omega)
  · intro H i j hij
    refine H i j ?_
    have := wt_le i; have := wt_le j
    simp only at hij
    omega

/- English proof (translation)
Introduce `L _ _ _ _ s hs δ hδ V _ _ _ h hh l e f W Λ hF hΛ hA π hπ k hk hc`. Establish `hδ0 : δ ≠ 0` using `hδ.1`. Use `set P := piece hh δ e f with hPdef`. Establish `hP : IsPieces P` using `isPieces_piece hh hδ0 hF`. Establish `hJ : IsCongIdeal (congJ Λ π) P` using `isCongIdeal_congJ hΛ hπ P fun i x hx => piece_mem hΛ hA hh hδ0 hF i hx`.

Take `⟨st, hst, st_mul, st_one, st_zero, st_P⟩` from `exists_star (δ := δ) (e := e) (f := f) (l := l) hs hh (GlobalTheory.T.hermitian_adjoint_exists s hs h hh)`. Establish `hk1 : (k.toLinearMap : Module.End L V) - 1 ∈ congJ Λ π` using `fun x hx => by`. Take `⟨y, hy, e1⟩` from `hc x hx`. Conclude with `⟨y, hy, by simpa using e1⟩`. Take `⟨a, b, ha, hb, hup, hlo, hab⟩` from `GlobalTheory.T.iwahori_upper_lower_factorization wt wt_injective P hP _ hJ _ hk1`.

Take `⟨ya, hya, ia1, ia2⟩` from `hJ.inv _ ha`. Take `⟨yb, hyb, ib1, ib2⟩` from `hJ.inv _ hb`. Rewrite `ia1`, `ia2`, `ib1`, `ib2` using `[add_sub_cancel]`. Establish `hkk : ∀ y, st (k.toLinearMap) (k y) = y` using `fun y => by`. Use `eq_of_pair hh fun x => ?_` and prove the remaining obligations.

Use `hst k.toLinearMap x (k y)` as an intermediate fact. Simplify using `only [LinearEquiv.coe_coe] at this`. Rewrite using `[← this, hk x y]`. Establish `hk2 : st (k.toLinearMap) * (k.toLinearMap) = 1`. Use extensionality with `y`.

Conclude with `hkk y`. Establish `hk3 : (k.toLinearMap : Module.End L V) * st (k.toLinearMap) = 1`. Use extensionality with `y`. Take `⟨z, rfl⟩` from `k.surjective y`. Simplify using `[Module.End.mul_apply, hkk z]`.

Rewrite `hk2`, `hk3` using `[hab]`. Take `⟨ua, ub⟩` from `GlobalTheory.T.unitary_factors_of_unitary_upper_mul_lowerUni wt P hP rev rev_rev (fun i j hij => by have := wt_rev i; have := wt_rev j; omega) wt_injective st st_mul st_one st_zero st_P (fun a a' h1 h2 h3 => GlobalTheory.T.upper_triangular_inverse_is_upper wt P hP a a' h1 h2 h3) …`. Set `A : V ≃ₗ[L] V` to `LinearEquiv.ofLinear a (1 + ya) ia1 ia2`. Set `B : V ≃ₗ[L] V` to `LinearEquiv.ofLinear b (1 + yb) ib1 ib2`. Establish `isoOf : ∀ (g : V ≃ₗ[L] V), st (g.toLinearMap) * g.toLinearMap = 1 → IsIso h g` using `fun g hg x y => by`.

Use `hst g.toLinearMap x (g y)` as an intermediate fact. Simplify using `only [LinearEquiv.coe_coe] at this`. Rewrite using `[this]`. Establish `h2 : st g.toLinearMap (g y) = y`. Use `congrArg (fun m : Module.End L V => m y) hg` as an intermediate fact.

Simplify `this` using `[Module.End.mul_apply]`. Rewrite using `[h2]`. Use `⟨A, B, isoOf A ua, isoOf B ub, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Use `congrArg (fun m : Module.End L V => m x) hab` as an intermediate fact.

Simplify `this` using `[A, B, Module.End.mul_apply]`. Introduce `u t hu0 hm h1 ht`. Establish `hT` using `fun i => tor_piece (δ := δ) hh hδ0 hF ht i`. Establish `key` using `GlobalTheory.T.torus_conjugation_preserves_congruence wt P hP _ hJ (congJ_smul hΛ π) (t.toLinearMap) (t.symm.toLinearMap) (tau s u) (tau_ne hu0) (by ext y; simp [Module.End.mul_apply]) (by ext y; simp [Module.End.mul_apply]) (fun i => (hT i).1) (fun i => (hT i).2) (tau_mono hs hu …`. Prove the components needed by the constructor for the conclusion.

Introduce `x hx`. Take `⟨y, hy, e1⟩` from `key.1 x hx`. Conclude with `⟨y, hy, by simpa [A, Module.End.mul_apply] using e1⟩`. Introduce `x hx`. Take `⟨y, hy, e1⟩` from `key.2 x hx`.

Conclude with `⟨y, hy, by simpa [B, Module.End.mul_apply] using e1⟩`.
-/
theorem stIwahori : StIwahori := by
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh l e f W Λ hF hΛ hA π hπ k hk hc
  have hδ0 : δ ≠ 0 := hδ.1
  set P := piece hh δ e f with hPdef
  have hP : IsPieces P := isPieces_piece hh hδ0 hF
  have hJ : IsCongIdeal (congJ Λ π) P :=
    isCongIdeal_congJ hΛ hπ P fun i x hx => piece_mem hΛ hA hh hδ0 hF i hx
  obtain ⟨st, hst, st_mul, st_one, st_zero, st_P⟩ :=
    exists_star (δ := δ) (e := e) (f := f) (l := l) hs hh (GlobalTheory.T.hermitian_adjoint_exists s hs h hh)
  have hk1 : (k.toLinearMap : Module.End L V) - 1 ∈ congJ Λ π := fun x hx => by
    obtain ⟨y, hy, e1⟩ := hc x hx
    exact ⟨y, hy, by simpa using e1⟩
  obtain ⟨a, b, ha, hb, hup, hlo, hab⟩ := GlobalTheory.T.iwahori_upper_lower_factorization wt wt_injective P hP _ hJ _ hk1

  obtain ⟨ya, hya, ia1, ia2⟩ := hJ.inv _ ha
  obtain ⟨yb, hyb, ib1, ib2⟩ := hJ.inv _ hb
  rw [add_sub_cancel] at ia1 ia2 ib1 ib2
  have hkk : ∀ y, st (k.toLinearMap) (k y) = y := fun y => by
    refine eq_of_pair hh fun x => ?_
    have := hst k.toLinearMap x (k y)
    simp only [LinearEquiv.coe_coe] at this
    rw [← this, hk x y]
  have hk2 : st (k.toLinearMap) * (k.toLinearMap) = 1 := by
    ext y; exact hkk y
  have hk3 : (k.toLinearMap : Module.End L V) * st (k.toLinearMap) = 1 := by
    ext y
    obtain ⟨z, rfl⟩ := k.surjective y
    simp [Module.End.mul_apply, hkk z]
  rw [hab] at hk2 hk3
  obtain ⟨ua, ub⟩ := GlobalTheory.T.unitary_factors_of_unitary_upper_mul_lowerUni wt P hP rev rev_rev
    (fun i j hij => by have := wt_rev i; have := wt_rev j; omega) wt_injective st st_mul st_one st_zero st_P
    (fun a a' h1 h2 h3 => GlobalTheory.T.upper_triangular_inverse_is_upper wt P hP a a' h1 h2 h3)
    (fun a a' h1 h2 h3 => (isUpper_rev_iff P a').1 (GlobalTheory.T.upper_triangular_inverse_is_upper _ P hP a a' h1 h2 ((isUpper_rev_iff P a).2 h3)))
    a (1 + ya) b (1 + yb) ia1 ia2 ib1 ib2 hup hlo hk2 hk3
  let A : V ≃ₗ[L] V := LinearEquiv.ofLinear a (1 + ya) ia1 ia2
  let B : V ≃ₗ[L] V := LinearEquiv.ofLinear b (1 + yb) ib1 ib2
  have isoOf : ∀ (g : V ≃ₗ[L] V), st (g.toLinearMap) * g.toLinearMap = 1 → IsIso h g := fun g hg x y => by
    have := hst g.toLinearMap x (g y)
    simp only [LinearEquiv.coe_coe] at this
    rw [this]
    have h2 : st g.toLinearMap (g y) = y := by
      have := congrArg (fun m : Module.End L V => m y) hg
      simpa [Module.End.mul_apply] using this
    rw [h2]
  refine ⟨A, B, isoOf A ua, isoOf B ub, ?_, ?_⟩
  · ext x
    have := congrArg (fun m : Module.End L V => m x) hab
    simpa [A, B, Module.End.mul_apply] using this
  · intro u t hu0 hm h1 ht
    have hT := fun i => tor_piece (δ := δ) hh hδ0 hF ht i
    have key := GlobalTheory.T.torus_conjugation_preserves_congruence wt P hP _ hJ (congJ_smul hΛ π) (t.toLinearMap) (t.symm.toLinearMap) (tau s u)
      (tau_ne hu0) (by ext y; simp [Module.End.mul_apply]) (by ext y; simp [Module.End.mul_apply])
      (fun i => (hT i).1) (fun i => (hT i).2)
      (tau_mono hs hu0 hm h1) a b ha hb hup hlo.1
    constructor
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.1 x hx
      exact ⟨y, hy, by simpa [A, Module.End.mul_apply] using e1⟩
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.2 x hx
      exact ⟨y, hy, by simpa [B, Module.End.mul_apply] using e1⟩

end GlobalTheory.CompanionTheory.Iwahori

end
