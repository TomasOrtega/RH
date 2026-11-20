import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.OneAddPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameRelationCocycleSquareZeroInertiaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAndResidualTrivComplexConj

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrimeRel

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, ih, Nat.cast_succ]`. Take the linear combination `(n : B) * hx`.
-/
theorem one_add_pow_of_sq {B : Type} [CommRing B] {x : B} (hx : x * x = 0) (n : ℕ) : (1 + x) ^ n = 1 + (n : B) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    linear_combination (n : B) * hx

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}

/- English proof (translation)
Use `X.lPrime i` as an intermediate fact. Take `⟨h0, -, hn, -, hd, hσ', hγ, hdγ⟩` from `hp`. Establish `h8 : normV p % (2 * X.l i ^ (nu X i + 1)) = 1` using `KStar.Tree.mod_two_mul_pow_of_le (X.lPrime i).out (by omega) hn`. Conclude with `(GlobalTheory.T.tame_relation_cocycle_squareZero_inertia hT D.host.E N.Om (X.l i) (N.plOm.1 p) p (N.plOm.2 p) (fun h => h0 p (Or.inl rfl) (X.twistExcludedPlaces_contains_residueChar i h)) (nu X i + 1) h8 M d γ σ (by omega) hd hγ hdγ hσ' R W ρ a b h4 hb hI hσ z).1`.
-/
theorem tame_rel (hT : TameQuotient) (_hl : 0 < nu X i) {M : ℕ} {L : Subgroup (GE N)} {p : PlE D.host}
    {d : GE N →* Multiplicative (ZMod (X.l i ^ M))} {σ γ : GE N} (hM : nu X i + 2 ≤ M) (hp : NewPl i M L p d σ γ)
    {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W]
    (ρ : Representation R (GE N) W) (a b : R) (h4 : ∀ m : W, (X.l i ^ (nu X i + 1)) • m = 0) (hb : b * b = 0)
    (hI : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), ∀ m, ρ τ m = m + (((Multiplicative.toAdd (d τ)).val : R) * b) • m)
    (hσ : ∀ m, ρ σ m = m + a • m) (z : Z1 ρ) : a • z.1 γ = b • z.1 σ := by
  have := X.lPrime i
  obtain ⟨h0, -, hn, -, hd, hσ', hγ, hdγ⟩ := hp
  have h8 : normV p % (2 * X.l i ^ (nu X i + 1)) = 1 :=
    KStar.Tree.mod_two_mul_pow_of_le (X.lPrime i).out (by omega) hn
  exact (GlobalTheory.T.tame_relation_cocycle_squareZero_inertia hT D.host.E N.Om (X.l i) (N.plOm.1 p) p (N.plOm.2 p)
    (fun h => h0 p (Or.inl rfl) (X.twistExcludedPlaces_contains_residueChar i h)) (nu X i + 1) h8 M d γ σ (by omega) hd hγ hdγ hσ' R W ρ a b h4 hb hI hσ z).1

/- English proof (translation)
Introduce `hT D N X bkP i s hl M L z₀ p d σ γ hM hL hp B _ _ κ x y hK hκ hx hI hσ Q a Φ Z hU j`. Set `Y` to `(Fin a → B) ⧸ what₂ Φ`. Use `letI : TopologicalSpace Y := ⊥`. Use `haveI : DiscreteTopology Y := ⟨rfl⟩`. Set `mk : (Fin a → B) →ₗ[B] Y` to `(what₂ Φ).mkQ`.

Establish `hmk : ∀ v ∈ what₂ Φ, mk v = 0` using `fun v hv => (Submodule.Quotient.mk_eq_zero _).2 hv`. Set `x0 : Fin a → Y` to `fun j => mk (Pi.single j 1)`. Establish `hrow : ∀ (r : ℕ) (A : Matrix (Fin r) (Fin a) B) (c : Fin r), ∑ j, A c j • x0 j = mk (A c)`. Introduce `r A c`. Simplify using `only [x0, ← map_smul, ← map_sum]`.

Use `congr 1`. Use extensionality with `j`. Simplify using `[Pi.single_apply]`. Establish `hx0 : matAct Φ x0 = 0`. Use extensionality with `c`.

Express the relevant statement in the definitionally equal form `∑ j, Φ c j • x0 j = 0`. Rewrite using `[hrow]`. Conclude with `hmk _ (Submodule.subset_span ⟨c, rfl⟩)`. Establish `hrect : ∀ g c, rect (Z g) x0 c = mk (Z g c)` using `fun g c => hrow _ _ _`. Take `⟨z, hz, -⟩` from `(hU Y).1 x0 hx0`.

Establish `h4 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0` using `fun m => by`. Establish `h1` using `hK _ (GlobalTheory.Growth.sq_mem_idl (X := X) (i := i))`. Rewrite `h1` using `[map_natCast]`. Rewrite using `[← Nat.cast_smul_eq_nsmul B]`. Conclude with `(congrArg (· • m) h1).trans (zero_smul _ _)`.

Establish `htr : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Bˣ) : B) • m` using `fun g hg => (GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z₀ (by omega) hL B κ _ hK (isDual_dualRep i s) Y g hg).1`. Establish `hdec : DecV N p ≤ L` using `hp.2.2.2.1`. Establish `hIL : ∀ τ ∈ Ine (F` using `D.host.E) (N.plOm.1 p), τ ∈ L := fun τ hτ => hdec (Ine_le_Dec _ hτ)`. Establish `hσL : σ ∈ L` using `hdec hp.2.2.2.2.2.1.1`. Establish `hcL : ∀ g, g ∈ L → cConj X g ∈ L` using `fun g hg => (hL.1.2.2.1 g _ (cConj_apply X g)).1 hg`.

Establish `hIv : ∀ τ ∈ Ine (F` using `D.host.E) (N.plOm.1 p), ((κ τ : Bˣ) : B) * (1 + ((Multiplicative.toAdd (d τ)).val : B) * x) = 1 := fun τ hτ => by`. Rewrite using `[← one_add_pow_of_sq hx]`. Conclude with `hI τ hτ`. Establish `r1` using `tame_rel hT.1 hl hM hp (repOn (Tgl i s) κ Y) (-(y * ((κ σ : Bˣ) : B))) (-x) h4 (by rw [neg_mul_neg, hx]) (fun τ hτ m => by`. Establish `h` using `hIv τ hτ`.

Establish `hκτ : ((κ τ : Bˣ) : B) = 1 + ((Multiplicative.toAdd (d τ)).val : B) * -x`. Take the linear combination `(1 - ((Multiplicative.toAdd (d τ)).val : B) * x) * h + ((Multiplicative.toAdd (d τ)).val : B) * ((Multiplicative.toAdd (d τ)).val : B) * ((κ τ : Bˣ) : B) * hx`. Rewrite using `[htr τ (hIL τ hτ), hκτ, add_smul, one_smul])`. Use the proof step `(fun m => by`. Establish `hκσ : ((κ σ : Bˣ) : B) = 1 + -(y * ((κ σ : Bˣ) : B))` using `by linear_combination hσ`.

Rewrite using `[htr σ hσL]`. Use `nth_rw 1 [hκσ]`. Rewrite using `[add_smul, one_smul]) z`. Establish `hcont : Continuous (cConj X)` using `GlobalTheory.ResConjTriv.continuous_cConj X`. Set `z' : Z1 ((repOn (Tgl i s) κ Y).comp (cConj X))` to `⟨fun g => z.1 (cConj X g), z.2.1.comp hcont, fun g h => by`.

Express the relevant statement in the definitionally equal form `z.1 (cConj X (g * h)) = _`. Rewrite using `[map_mul]`. Conclude with `z.2.2 _ _⟩`. Establish `r2` using `tame_rel hT.1 hl hM hp ((repOn (Tgl i s) κ Y).comp (cConj X)) y x h4 hx (fun τ hτ m => by`. Express the relevant statement in the definitionally equal form `repOn (Tgl i s) κ Y (cConj X τ) m = _`.

Rewrite using `[htr _ (hcL τ (hIL τ hτ)), antiHom_cConj X hκ, Units.inv_eq_of_mul_eq_one_right (hIv τ hτ), add_smul, one_smul])`. Use the proof step `(fun m => by`. Express the relevant statement in the definitionally equal form `repOn (Tgl i s) κ Y (cConj X σ) m = _`. Rewrite using `[htr _ (hcL σ hσL), antiHom_cConj X hκ, Units.inv_eq_of_mul_eq_one_right hσ, add_smul, one_smul]) z'`. Take `⟨b, c⟩` from `j`.

Establish `key : ∀ (u v : B) (g h : GE N), u • z.1 g = v • z.1 h → u • Z g c - v • Z h c ∈ what₂ Φ`. Introduce `u v g h e`. Establish `e'` using `congrFun e c`. Simplify using `only [Pi.smul_apply, hz, hrect] at e'`. Rewrite using `[← Submodule.Quotient.mk_eq_zero (what₂ Φ)]`.

Express the relevant statement in the definitionally equal form `mk (u • Z g c - v • Z h c) = 0`. Rewrite using `[map_sub, map_smul, map_smul, e', sub_self]`. Consider the cases of `b`. Simplify using `only [two, Bool.false_eq_true, ↓reduceIte, mul_one]`. Apply `key` to reduce the goal to its premises.

Use `r1` as an intermediate fact. Rewrite `this` using `[neg_smul, neg_smul, neg_inj]`. Conclude with `this.symm`. Simplify using `only [two, ↓reduceIte, mul_one]`. Apply `key` to reduce the goal to its premises.

Conclude with `r2.symm`.
-/
theorem rel : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (κ : GE N →* Bˣ) (x y : B), Kills i B → AntiHom X.cc κ → x * x = 0 → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), ((κ τ : Bˣ) : B) * (1 + x) ^ (Multiplicative.toAdd (d τ)).val = 1) → ((κ σ : Bˣ) : B) * (1 + y) = 1 → ∀ (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) B) Z, Univ bkP i s κ Q Φ Z → ∀ j : Bool × Fin D.R.r, x • Z (two X σ j.1) j.2 - (y * (if j.1 then 1 else ((κ σ : Bˣ) : B))) • Z (two X γ j.1) j.2 ∈ what₂ Φ := by
  intro hT D N X bkP i s hl M L z₀ p d σ γ hM hL hp B _ _ κ x y hK hκ hx hI hσ Q a Φ Z hU j

  let Y := (Fin a → B) ⧸ what₂ Φ
  letI : TopologicalSpace Y := ⊥
  haveI : DiscreteTopology Y := ⟨rfl⟩
  let mk : (Fin a → B) →ₗ[B] Y := (what₂ Φ).mkQ
  have hmk : ∀ v ∈ what₂ Φ, mk v = 0 := fun v hv => (Submodule.Quotient.mk_eq_zero _).2 hv

  let x0 : Fin a → Y := fun j => mk (Pi.single j 1)
  have hrow : ∀ (r : ℕ) (A : Matrix (Fin r) (Fin a) B) (c : Fin r), ∑ j, A c j • x0 j = mk (A c) := by
    intro r A c
    simp only [x0, ← map_smul, ← map_sum]
    congr 1
    ext j
    simp [Pi.single_apply]
  have hx0 : matAct Φ x0 = 0 := by
    ext c
    change ∑ j, Φ c j • x0 j = 0
    rw [hrow]
    exact hmk _ (Submodule.subset_span ⟨c, rfl⟩)
  have hrect : ∀ g c, rect (Z g) x0 c = mk (Z g c) := fun g c => hrow _ _ _

  obtain ⟨z, hz, -⟩ := (hU Y).1 x0 hx0

  have h4 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0 := fun m => by
    have h1 := hK _ (GlobalTheory.Growth.sq_mem_idl (X := X) (i := i))
    rw [map_natCast] at h1
    rw [← Nat.cast_smul_eq_nsmul B]
    exact (congrArg (· • m) h1).trans (zero_smul _ _)
  have htr : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Bˣ) : B) • m := fun g hg =>
    (GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z₀ (by omega) hL B κ _ hK (isDual_dualRep i s) Y g hg).1
  have hdec : DecV N p ≤ L := hp.2.2.2.1
  have hIL : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), τ ∈ L := fun τ hτ => hdec (Ine_le_Dec _ hτ)
  have hσL : σ ∈ L := hdec hp.2.2.2.2.2.1.1
  have hcL : ∀ g, g ∈ L → cConj X g ∈ L := fun g hg => (hL.1.2.2.1 g _ (cConj_apply X g)).1 hg

  have hIv : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p),
      ((κ τ : Bˣ) : B) * (1 + ((Multiplicative.toAdd (d τ)).val : B) * x) = 1 := fun τ hτ => by
    rw [← one_add_pow_of_sq hx]
    exact hI τ hτ

  have r1 := tame_rel hT.1 hl hM hp (repOn (Tgl i s) κ Y) (-(y * ((κ σ : Bˣ) : B))) (-x) h4 (by rw [neg_mul_neg, hx])
    (fun τ hτ m => by
      have h := hIv τ hτ
      have hκτ : ((κ τ : Bˣ) : B) = 1 + ((Multiplicative.toAdd (d τ)).val : B) * -x := by
        linear_combination (1 - ((Multiplicative.toAdd (d τ)).val : B) * x) * h +
          ((Multiplicative.toAdd (d τ)).val : B) * ((Multiplicative.toAdd (d τ)).val : B) * ((κ τ : Bˣ) : B) * hx
      rw [htr τ (hIL τ hτ), hκτ, add_smul, one_smul])
    (fun m => by
      have hκσ : ((κ σ : Bˣ) : B) = 1 + -(y * ((κ σ : Bˣ) : B)) := by linear_combination hσ
      rw [htr σ hσL]
      nth_rw 1 [hκσ]
      rw [add_smul, one_smul]) z

  have hcont : Continuous (cConj X) := GlobalTheory.ResConjTriv.continuous_cConj X
  let z' : Z1 ((repOn (Tgl i s) κ Y).comp (cConj X)) :=
    ⟨fun g => z.1 (cConj X g), z.2.1.comp hcont, fun g h => by
      change z.1 (cConj X (g * h)) = _
      rw [map_mul]
      exact z.2.2 _ _⟩
  have r2 := tame_rel hT.1 hl hM hp ((repOn (Tgl i s) κ Y).comp (cConj X)) y x h4 hx
    (fun τ hτ m => by
      change repOn (Tgl i s) κ Y (cConj X τ) m = _
      rw [htr _ (hcL τ (hIL τ hτ)), antiHom_cConj X hκ, Units.inv_eq_of_mul_eq_one_right (hIv τ hτ), add_smul, one_smul])
    (fun m => by
      change repOn (Tgl i s) κ Y (cConj X σ) m = _
      rw [htr _ (hcL σ hσL), antiHom_cConj X hκ, Units.inv_eq_of_mul_eq_one_right hσ, add_smul, one_smul]) z'

  obtain ⟨b, c⟩ := j
  have key : ∀ (u v : B) (g h : GE N), u • z.1 g = v • z.1 h → u • Z g c - v • Z h c ∈ what₂ Φ := by
    intro u v g h e
    have e' := congrFun e c
    simp only [Pi.smul_apply, hz, hrect] at e'
    rw [← Submodule.Quotient.mk_eq_zero (what₂ Φ)]
    change mk (u • Z g c - v • Z h c) = 0
    rw [map_sub, map_smul, map_smul, e', sub_self]
  cases b
  · simp only [two, Bool.false_eq_true, ↓reduceIte, mul_one]
    apply key
    have := r1
    rw [neg_smul, neg_smul, neg_inj] at this
    exact this.symm
  · simp only [two, ↓reduceIte, mul_one]
    apply key
    exact r2.symm

end GlobalTheory.NewPrimeRel
