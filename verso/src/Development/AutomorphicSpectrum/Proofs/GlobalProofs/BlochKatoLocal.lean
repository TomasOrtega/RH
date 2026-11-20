import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.TmulOneMemDcris
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCocycle
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCoboundary
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicCupTwoCochainLocallyConstant
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLattices
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasis
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycle
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.BkMain
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTop
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTopEuler
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CupFlip
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TateDualityH2FiniteCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRhamStatement

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.BK

open PositivityTheory.LocalTateOrthogonality.Bk in

/- English proof (translation)
Introduce `l _ Lp K hfin hZ LL _ _ _ O _ _ hO A LA ϖ hϖ r hI`. Take `⟨⟨hD, hV, hF⟩, -⟩` from `id hO`. Take `⟨-, hB, -⟩` from `latTop l Lp K LL O hO A LA ϖ hϖ`. Establish `hW : (fun x => ϖ ^ r • x) '' (LA.T : Set A.V) ∈ nhds (0 : A.V)` using `hB.mem_of_mem trivial`. Use `hfin LL O hO A LA` as an intermediate fact.

Use `hZ LL O hO A LA ϖ hϖ r hI` as an intermediate fact. Establish `: Finite (QuotientCohomology LA _ hI)` using `Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)`. Rewrite using `[pow_mul, ← GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_pow ϖ hϖ.ne_zero r]`. Use `card_pow_le (ϖ ^ r) (fun c : ↥(latticeCocycles LA) => (Submodule.Quotient.mk c : LatticeCohomology LA)) (Submodule.Quotient.mk_surjective _) (fun c => (Submodule.Quotient.mk ⟨redT LA _ c, redT_mem A LA hW hI c⟩ : QuotientCohomology LA _ hI)) ?_` and prove the remaining obligations. Introduce `x y h`.

Rewrite using `[← Submodule.Quotient.mk_sub]`. Use `exists_div_class A LA (pow_ne_zero r hϖ.ne_zero) hI _ ?_` and prove the remaining obligations. Rewrite using `[map_sub]`. Establish `h'` using `(Submodule.Quotient.eq _).1 h`. Conclude with `h'`.
-/
theorem card1Lower : ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), TateFiniteness (Lp.PD K) → FinZQ (Lp.PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ ϖ : O, Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank O (LatticeCohomology LA)) ≤ Nat.card (QuotientCohomology LA _ hI) := by
  intro l _ Lp K hfin hZ LL _ _ _ O _ _ hO A LA ϖ hϖ r hI
  obtain ⟨⟨hD, hV, hF⟩, -⟩ := id hO
  obtain ⟨-, hB, -⟩ := latTop l Lp K LL O hO A LA ϖ hϖ
  have hW : (fun x => ϖ ^ r • x) '' (LA.T : Set A.V) ∈ nhds (0 : A.V) := hB.mem_of_mem trivial
  have := hfin LL O hO A LA
  have := hZ LL O hO A LA ϖ hϖ r hI
  have : Finite (QuotientCohomology LA _ hI) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  rw [pow_mul, ← GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_pow ϖ hϖ.ne_zero r]
  refine card_pow_le (ϖ ^ r) (fun c : ↥(latticeCocycles LA) => (Submodule.Quotient.mk c : LatticeCohomology LA))
    (Submodule.Quotient.mk_surjective _)
    (fun c => (Submodule.Quotient.mk ⟨redT LA _ c, redT_mem A LA hW hI c⟩ : QuotientCohomology LA _ hI)) ?_
  intro x y h
  rw [← Submodule.Quotient.mk_sub]
  refine exists_div_class A LA (pow_ne_zero r hϖ.ne_zero) hI _ ?_
  rw [map_sub]
  have h' := (Submodule.Quotient.eq _).1 h
  exact h'

open PositivityTheory.LocalTateOrthogonality.Bk in
set_option maxHeartbeats 2000000 in
/- English proof (translation)
Introduce `l _ Lp K LL _ _ _ O _ _ hG A A' LA LA' P hd ϖ hϖ r`. Establish `hG0 : ∃ hO : IsDomain O, @IsDiscreteValuationRing O _ hO ∧ IsFractionRing O LL` using `hG.1`. Establish `hO : IsDomain O` using `hG0.choose`. Establish `hF : IsFractionRing O LL` using `hG0.choose_spec.2`. Establish `h1 : ∀ y, y ∈ LA'.T ↔ ∀ x ∈ LA.T, ∃ a : O, P x y = algebraMap O LL a` using `hd.2`.

Establish `h2 : ∀ x, x ∈ LA.T ↔ ∀ y ∈ LA'.T, ∃ a : O, P.flip y x = algebraMap O LL a` using `((latTop l Lp K LL O hG A LA ϖ hϖ).2.2.2.2 A' LA' P hd).2`. Simplify using `only [LinearMap.flip_apply] at h2`. Conclude with `GlobalTheory.CompanionTheory.LocDual.Q.pairing_exists LL O A.V A'.V LA.T LA'.T P ϖ hϖ.ne_zero r h1 h2`.
-/
theorem pairOL : ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (Lp.PD K) LA LA' P → ∀ ϖ : O, Irreducible ϖ → ∀ r : ℕ, ∃ B : (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) →ₗ[O] (↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ r}), (∀ (x : ↥LA.T) (y : ↥LA'.T) (p : O), P x y = algebraMap O LL p → B (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Ideal.Quotient.mk _ p) ∧ (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) := by
  intro l _ Lp K LL _ _ _ O _ _ hG A A' LA LA' P hd ϖ hϖ r
  have hG0 : ∃ hO : IsDomain O, @IsDiscreteValuationRing O _ hO ∧ IsFractionRing O LL := hG.1
  have hO : IsDomain O := hG0.choose
  have hF : IsFractionRing O LL := hG0.choose_spec.2
  have h1 : ∀ y, y ∈ LA'.T ↔ ∀ x ∈ LA.T, ∃ a : O, P x y = algebraMap O LL a := hd.2
  have h2 : ∀ x, x ∈ LA.T ↔ ∀ y ∈ LA'.T, ∃ a : O, P.flip y x = algebraMap O LL a :=
    ((latTop l Lp K LL O hG A LA ϖ hϖ).2.2.2.2 A' LA' P hd).2
  simp only [LinearMap.flip_apply] at h2
  exact GlobalTheory.CompanionTheory.LocDual.Q.pairing_exists LL O A.V A'.V LA.T LA'.T P ϖ hϖ.ne_zero r h1 h2

open PositivityTheory.LocalTateOrthogonality.Bk PositivityTheory.LocalTateOrthogonality.Bk.Eul in

/- English proof (translation)
Establish `hcyc : GlobalTheory.Cyc.IsCyc Lp.χQ` using `Lp.χQ_cyc`. Set `χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ` to `(cyclotomicCharacter (PadicAlgCl l) l).comp (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))`. Establish `hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (Lp.χQ (K.1.fixingSubgroupEquiv.symm g : GQ l) : ℚ_[l])` using `fun g => by`. Rewrite using `[GlobalTheory.Cyc.TwistLift.isCyc_unique hcyc (GlobalTheory.Cyc.isCyc_cycChar l)]`. Both sides reduce to the same expression.

Use `⟨(χZ (K.1.fixingSubgroupEquiv g) : ℤ_[l]), ?_, rfl⟩` and prove the remaining obligations. Establish `h1` using `hχZ (K.1.fixingSubgroupEquiv g)`. Rewrite `h1` using `[show K.1.fixingSubgroupEquiv.symm (K.1.fixingSubgroupEquiv g) = g from K.1.fixingSubgroupEquiv.symm_apply_apply g, ← Lp.PD_χ K g]`. Conclude with `h1`.
-/
theorem chiTie (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l) (n : ℕ) (g : ↥(GK K)) :
    ∃ u : ℤ_[l], (u : ℚ_[l]) = (((Lp.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧
      PadicInt.toZModPow n u = (Formalism.GaloisCohomology.cycK l K.1 n (K.1.fixingSubgroupEquiv g) : ZMod (l ^ n)) := by
  have hcyc : GlobalTheory.Cyc.IsCyc Lp.χQ := Lp.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) =
      (Lp.χQ (K.1.fixingSubgroupEquiv.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [GlobalTheory.Cyc.TwistLift.isCyc_unique hcyc (GlobalTheory.Cyc.isCyc_cycChar l)]; rfl
  refine ⟨(χZ (K.1.fixingSubgroupEquiv g) : ℤ_[l]), ?_, rfl⟩
  have h1 := hχZ (K.1.fixingSubgroupEquiv g)
  rw [show K.1.fixingSubgroupEquiv.symm (K.1.fixingSubgroupEquiv g) = g from K.1.fixingSubgroupEquiv.symm_apply_apply g, ← Lp.PD_χ K g] at h1
  exact h1

open PositivityTheory.LocalTateOrthogonality.Bk PositivityTheory.LocalTateOrthogonality.Bk.Eul in

/- English proof (translation)
Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective I x`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective I' y`. Take `⟨p, hp⟩` from `(hd.2 y).1 y.2 x x.2`. Establish `h1 : P (actT LA g x) (actT LA' g y) = algebraMap O LL (ι u * p)`. Express the relevant statement in the definitionally equal form `P (A.ρ g x) (A'.ρ g y) = _`.

Rewrite using `[hd.1.1 g x y, hp, map_mul, hι, hu]`. Both sides reduce to the same expression. Rewrite using `[hB x y p hp, ← map_mul]`. Conclude with `hB _ _ _ h1`.
-/
theorem equivB (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (ι : ℤ_[l] →+* O)
    (hι : ∀ a, algebraMap O LL (ι a) = algebraMap ℚ_[l] LL a) (A A' : GRep ↥(GK K) ℚ_[l] LL O)
    (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (hd : IsDualLat1 (Lp.PD K) LA LA' P) (J : Ideal O) (I : Submodule O ↥LA.T)
    (I' : Submodule O ↥LA'.T) (hI : StableSub LA I) (hI' : StableSub LA' I')
    (B : (↥LA.T ⧸ I) →ₗ[O] (↥LA'.T ⧸ I') →ₗ[O] (O ⧸ J))
    (hB : ∀ (x : ↥LA.T) (y : ↥LA'.T) (p : O), P x y = algebraMap O LL p →
      B (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Ideal.Quotient.mk _ p)
    (g : ↥(GK K)) (x : ↥LA.T ⧸ I) (y : ↥LA'.T ⧸ I') (u : ℤ_[l])
    (hu : (u : ℚ_[l]) = (((Lp.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])) :
    B (actQ LA I hI g x) (actQ LA' I' hI' g y) = Ideal.Quotient.mk _ (ι u) * B x y := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective I x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I' y
  obtain ⟨p, hp⟩ := (hd.2 y).1 y.2 x x.2
  have h1 : P (actT LA g x) (actT LA' g y) = algebraMap O LL (ι u * p) := by
    change P (A.ρ g x) (A'.ρ g y) = _
    rw [hd.1.1 g x y, hp, map_mul, hι, hu]
    rfl
  rw [hB x y p hp, ← map_mul]
  exact hB _ _ _ h1

open PositivityTheory.LocalTateOrthogonality.Bk PositivityTheory.LocalTateOrthogonality.Bk.Eul in
set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `hT hE l _ Lp K LL _ _ _ O _ _ hO A A' LA LA' P hd ϖ hϖ r hI hI'`. Take `⟨-, hqf, -, ⟨-, hl, -⟩, -, -⟩` from `GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ`. Take `⟨ι, hι⟩` from `GlobalTheory.TateTop.exists_ringHom hO`. Take `⟨⟨hdom, hdvr, hfr⟩, -⟩` from `id hO`. Use `hdom` as an intermediate fact.

Use `hdvr` as an intermediate fact. Use `hfr` as an intermediate fact. Use `hqf` as an intermediate fact. Establish `hfinO : Finite (O ⧸ Ideal.span {ϖ ^ r})`. Use `Ideal.finite_quotient_pow (I := Ideal.span {ϖ}) ⟨{ϖ}, by simp⟩ r` as an intermediate fact.

Rewrite `this` using `[Ideal.span_singleton_pow]`. Then use the resulting hypothesis. Establish `hpos : 0 < l ^ (r + 1)` using `pow_pos (Fact.out : l.Prime).pos _`. Establish `hN : ((l ^ (r + 1) : ℕ) : O) ∈ Ideal.span {ϖ ^ r}`. Establish `h1 : (l : O) ^ r ∈ Ideal.span {ϖ ^ r}`. Rewrite using `[← Ideal.span_singleton_pow]`.

Conclude with `Ideal.pow_mem_pow hl r`. Rewrite using `[Nat.cast_pow, pow_succ]`. Conclude with `Ideal.mul_mem_right _ _ h1`. Take `⟨hW, hcW⟩` from `cardQ l K LL O hO A LA ϖ hϖ r`. Take `⟨hW', -⟩` from `cardQ l K LL O hO A' LA' ϖ hϖ r`.

Take `⟨ψ₀, hψ, -⟩` from `GlobalTheory.T.exists_perfect_character_quotient O ϖ hϖ r (l ^ (r + 1)) hpos hfinO hN`. Take `⟨B, hB, hBl, hBr⟩` from `pairOL l Lp K LL O hO A A' LA LA' P hd ϖ hϖ r`. Take `⟨Pb, hPb, hL, hR⟩` from `exists_pair _ _ B ψ₀ hψ hBl hBr`. Establish `hlc` using `actLoc l Lp K LL O hO A LA ϖ hϖ r hI`. Establish `heq : ∀ g x y, Pb ((actQ LA _ hI g).toAddMonoidHom x) ((actQ LA' _ hI' g).toAddMonoidHom y) = (Formalism.GaloisCohomology.cycK l K.1 (r + 1) (K.1.fixingSubgroupEquiv g) : ZMod (l ^ (r + 1))) * Pb x y`.

Introduce `g x y`. Take `⟨u, hu, hu'⟩` from `chiTie l Lp K (r + 1) g`. Take `⟨b, hb⟩` from `Ideal.Quotient.mk_surjective (B x y)`. Establish `e1` using `equivB l Lp K LL O ι hι A A' LA LA' P hd _ _ _ hI hI' B hB g x y u hu`. Rewrite `e1` using `[← hb, ← map_mul]`.

Establish `e3` using `psi_unit ι _ (r + 1) hN ψ₀ u b`. Rewrite `e3` using `[hu', hb, ← hPb, ← e1, ← hPb]`. Conclude with `e3`. Establish `hZ` using `cocycles hT hE l K (r + 1) (Nat.succ_pos r) _ (fun g => (actQ LA _ hI g).toAddMonoidHom) (actQ_one' LA _ hI) (fun g h m => actQ_mul' LA _ hI g h m) hlc (quot_killed _ _ hN) _ (fun g => (actQ LA' _ hI' g).toAddMonoidHom) (actQ_one' LA' _ hI') (fun g h m => actQ_mul' LA' _ hI' g h …`. Establish `hC` using `h1count l K LL O A LA _ hI hW hlc`.

Conclude with `final_count _ _ _ _ _ _ _ _ Nat.card_pos hcW hC hZ`.
-/
theorem eulerQuot : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (Lp.PD K) LA LA' P → ∀ ϖ : O, Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), ∀ hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL A.V * finrank ℚ_[l] ↥K.1) := by
  intro hT hE l _ Lp K LL _ _ _ O _ _ hO A A' LA LA' P hd ϖ hϖ r hI hI'
  obtain ⟨-, hqf, -, ⟨-, hl, -⟩, -, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ
  obtain ⟨ι, hι⟩ := GlobalTheory.TateTop.exists_ringHom hO
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := id hO
  have := hdom
  have := hdvr
  have := hfr
  have := hqf
  have hfinO : Finite (O ⧸ Ideal.span {ϖ ^ r}) := by
    have := Ideal.finite_quotient_pow (I := Ideal.span {ϖ}) ⟨{ϖ}, by simp⟩ r
    rwa [Ideal.span_singleton_pow] at this
  have hpos : 0 < l ^ (r + 1) := pow_pos (Fact.out : l.Prime).pos _
  have hN : ((l ^ (r + 1) : ℕ) : O) ∈ Ideal.span {ϖ ^ r} := by
    have h1 : (l : O) ^ r ∈ Ideal.span {ϖ ^ r} := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_mem_pow hl r
    rw [Nat.cast_pow, pow_succ]
    exact Ideal.mul_mem_right _ _ h1
  obtain ⟨hW, hcW⟩ := cardQ l K LL O hO A LA ϖ hϖ r
  obtain ⟨hW', -⟩ := cardQ l K LL O hO A' LA' ϖ hϖ r
  obtain ⟨ψ₀, hψ, -⟩ := GlobalTheory.T.exists_perfect_character_quotient O ϖ hϖ r (l ^ (r + 1)) hpos hfinO hN
  obtain ⟨B, hB, hBl, hBr⟩ := pairOL l Lp K LL O hO A A' LA LA' P hd ϖ hϖ r
  obtain ⟨Pb, hPb, hL, hR⟩ := exists_pair _ _ B ψ₀ hψ hBl hBr
  have hlc := actLoc l Lp K LL O hO A LA ϖ hϖ r hI
  have heq : ∀ g x y, Pb ((actQ LA _ hI g).toAddMonoidHom x) ((actQ LA' _ hI' g).toAddMonoidHom y) =
      (Formalism.GaloisCohomology.cycK l K.1 (r + 1) (K.1.fixingSubgroupEquiv g) : ZMod (l ^ (r + 1))) * Pb x y := by
    intro g x y
    obtain ⟨u, hu, hu'⟩ := chiTie l Lp K (r + 1) g
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (B x y)
    have e1 := equivB l Lp K LL O ι hι A A' LA LA' P hd _ _ _ hI hI' B hB g x y u hu
    rw [← hb, ← map_mul] at e1
    have e3 := psi_unit ι _ (r + 1) hN ψ₀ u b
    rw [hu', hb, ← hPb, ← e1, ← hPb] at e3
    exact e3
  have hZ := cocycles hT hE l K (r + 1) (Nat.succ_pos r) _
    (fun g => (actQ LA _ hI g).toAddMonoidHom) (actQ_one' LA _ hI) (fun g h m => actQ_mul' LA _ hI g h m)
    hlc (quot_killed _ _ hN) _
    (fun g => (actQ LA' _ hI' g).toAddMonoidHom) (actQ_one' LA' _ hI') (fun g h m => actQ_mul' LA' _ hI' g h m)
    Pb hL hR heq
  have hC := h1count l K LL O A LA _ hI hW hlc
  exact final_count _ _ _ _ _ _ _ _ Nat.card_pos hcW hC hZ

open PositivityTheory.LocalTateOrthogonality.Bk in

/- English proof (translation)
Establish `hZ` using `finZQ hT hE l Lp K`. Take `⟨-, hLat⟩` from `dualLat l Lp K`. Take `⟨LA, LA', hd, -⟩` from `hLat LL O hG A A' P hP`. Take `⟨hfin, hrank⟩` from `finrank_H1_rational_eq_lattice l Lp K hZ`. Take `⟨-, hr⟩` from `hrank LL O hG A LA`.

Take `⟨⟨hdom, hdvr, -⟩, -⟩` from `id hG`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨-, hres, -⟩` from `GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ`. Establish `hq : 2 ≤ Nat.card (O ⧸ Ideal.span {ϖ})`. Establish `: Nontrivial (O ⧸ Ideal.span {ϖ})` using `Ideal.Quotient.nontrivial_iff.mpr (by`.

Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Conclude with `hϖ.not_isUnit)`. Conclude with `Finite.one_lt_card`. Take `⟨C, h0⟩` from `H0_torsion_growth_bound l Lp K hfin LL O hG A LA ϖ hϖ`. Take `⟨C', h0'⟩` from `H0_torsion_growth_bound l Lp K hfin LL O hG A' LA' ϖ hϖ`.

Establish `h1` using `card1Lower l Lp K hfin hZ LL O hG A LA ϖ hϖ`. Establish `hE'` using `eulerQuot hT hE l Lp K LL O hG A A' LA LA' P hd ϖ hϖ`. Establish `key : finrank O (LatticeCohomology LA) ≤ finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank LL A.V * finrank ℚ_[l] ↥K.1` using `growth_le (C := C) (C' := C') hq fun r =>`. Establish `hI` using `stable_pow LA ϖ r`. Establish `hI'` using `stable_pow LA' ϖ r`.

Use the proof step `⟨_, _, _, (h0 r hI).2, (h0' r hI').2, h1 r hI, hE' r hI hI'⟩`. Rewrite using `[hr, Nat.mul_comm (finrank ℚ_[l] ↥K.1)]`. Conclude with `key`.
-/
theorem eulerLe (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL] (hG : GoodO (Qp := ℚ_[l]) LL O)
    (A A' : GRep ↥(GK K) ℚ_[l] LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (hP : IsDual1 (Lp.PD K) A.ρ A'.ρ P) :
    finrank LL (H1V A.ρ) ≤
      finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V := by
  have hZ := finZQ hT hE l Lp K
  obtain ⟨-, hLat⟩ := dualLat l Lp K
  obtain ⟨LA, LA', hd, -⟩ := hLat LL O hG A A' P hP
  obtain ⟨hfin, hrank⟩ := finrank_H1_rational_eq_lattice l Lp K hZ
  obtain ⟨-, hr⟩ := hrank LL O hG A LA
  obtain ⟨⟨hdom, hdvr, -⟩, -⟩ := id hG
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hres, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ
  have hq : 2 ≤ Nat.card (O ⧸ Ideal.span {ϖ}) := by
    have : Nontrivial (O ⧸ Ideal.span {ϖ}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by
        rw [Ne, Ideal.span_singleton_eq_top]
        exact hϖ.not_isUnit)
    exact Finite.one_lt_card
  obtain ⟨C, h0⟩ := H0_torsion_growth_bound l Lp K hfin LL O hG A LA ϖ hϖ
  obtain ⟨C', h0'⟩ := H0_torsion_growth_bound l Lp K hfin LL O hG A' LA' ϖ hϖ
  have h1 := card1Lower l Lp K hfin hZ LL O hG A LA ϖ hϖ
  have hE' := eulerQuot hT hE l Lp K LL O hG A A' LA LA' P hd ϖ hϖ
  have key : finrank O (LatticeCohomology LA) ≤ finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) +
      finrank LL A.V * finrank ℚ_[l] ↥K.1 :=
    growth_le (C := C) (C' := C') hq fun r =>
      have hI := stable_pow LA ϖ r
      have hI' := stable_pow LA' ϖ r
      ⟨_, _, _, (h0 r hI).2, (h0' r hI').2, h1 r hI, hE' r hI hI'⟩
  rw [hr, Nat.mul_comm (finrank ℚ_[l] ↥K.1)]
  exact key

open PositivityTheory.LocalTateOrthogonality.Bk ExactAnn in
open ExactAnn in

/- English proof (translation)
Introduce `LL _ _ _ O _ _ hO A A' P hP S S' hBS hSZ hBS' hSZ' horth hdim`. Take `⟨-, hF⟩` from `cupFlip l Lp K LL O hO A A' P hP`. Establish `hnd` using `hNd LL O hO A A' P hP`. Take `⟨LA, LA', -⟩` from `(dualLat l Lp K).2 LL O hO A A' P hP`. Establish `hE1 : Module.Finite LL (H1V A.ρ)` using `((finrank_H1_rational_eq_lattice l Lp K hZ).2 LL O hO A LA).1`.

Establish `hE2 : Module.Finite LL (H1V A'.ρ)` using `((finrank_H1_rational_eq_lattice l Lp K hZ).2 LL O hO A' LA').1`. Distinguish the cases in `hall : ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, CobL (Lp.PD K) (cupL A'.ρ P a b)`. Conclude with `⟨fun a ha _ => hBS (hnd.1 a ha fun b hb => hall a ha b hb), fun b hb _ => hBS' (hnd.2 b hb fun a ha => hall a ha b hb)⟩`. Use `push Not at hall`. Take `⟨a0, ha0, b0, hb0, hz0⟩` from `hall`.

Establish `: IsTopologicalRing LL` using `hO.2.2.2.1`. Take `⟨Φ, hΦ⟩` from `exists_pairing (continuousCocycles A.ρ) (continuousCocycles A'.ρ) (cocSub (Lp.PD K) LL) (cobSub (Lp.PD K) LL) (cupBil A'.ρ P) (fun a ha b hb => ⟨(hF a ha b hb).1, (hF a ha b hb).2.1⟩) (cupL A'.ρ P a0 b0) hz0 (fun z hz => hTop LL O hO _ z (hF a0 ha0 b0 hb0).1 hz.1 (hF a0 ha0 b0 hb …`. Establish `res` using `ann_of_pairing (continuousCocycles A.ρ) (B1 A.ρ) S (continuousCocycles A'.ρ) (B1 A'.ρ) S' Φ (fun a ha b => (hΦ a b).2 ((hF a a.2 b b.2).2.2.2 (Or.inl ha))) (fun b hb a => (hΦ a b).2 ((hF a a.2 b b.2).2.2.2 (Or.inr hb))) (fun a h => hnd.1 a a.2 fun b hb => (hΦ a ⟨b, hb⟩).1 (h _)) …`. Conclude with `⟨fun a ha h => res.1 ⟨a, ha⟩ fun b hb => (hΦ _ _).2 (h b hb), fun b hb h => res.2 ⟨b, hb⟩ fun a ha => (hΦ _ _).2 (h a ha)⟩`.
-/
theorem dualLOf (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l) (hZ : FinZQ (Lp.PD K))
    (hTop : TopLine (Lp.PD K)) (hNd : NondegL (Lp.PD K)) : DualL (Lp.PD K) := by
  intro LL _ _ _ O _ _ hO A A' P hP S S' hBS hSZ hBS' hSZ' horth hdim
  obtain ⟨-, hF⟩ := cupFlip l Lp K LL O hO A A' P hP
  have hnd := hNd LL O hO A A' P hP
  obtain ⟨LA, LA', -⟩ := (dualLat l Lp K).2 LL O hO A A' P hP
  have hE1 : Module.Finite LL (H1V A.ρ) := ((finrank_H1_rational_eq_lattice l Lp K hZ).2 LL O hO A LA).1
  have hE2 : Module.Finite LL (H1V A'.ρ) := ((finrank_H1_rational_eq_lattice l Lp K hZ).2 LL O hO A' LA').1
  by_cases hall : ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, CobL (Lp.PD K) (cupL A'.ρ P a b)
  · exact ⟨fun a ha _ => hBS (hnd.1 a ha fun b hb => hall a ha b hb),
      fun b hb _ => hBS' (hnd.2 b hb fun a ha => hall a ha b hb)⟩
  push Not at hall
  obtain ⟨a0, ha0, b0, hb0, hz0⟩ := hall
  have : IsTopologicalRing LL := hO.2.2.2.1
  obtain ⟨Φ, hΦ⟩ := exists_pairing (continuousCocycles A.ρ) (continuousCocycles A'.ρ) (cocSub (Lp.PD K) LL)
    (cobSub (Lp.PD K) LL) (cupBil A'.ρ P)
    (fun a ha b hb => ⟨(hF a ha b hb).1, (hF a ha b hb).2.1⟩) (cupL A'.ρ P a0 b0) hz0
    (fun z hz => hTop LL O hO _ z (hF a0 ha0 b0 hb0).1 hz.1 (hF a0 ha0 b0 hb0).2.1 hz.2 hz0)
  have res := ann_of_pairing (continuousCocycles A.ρ) (B1 A.ρ) S (continuousCocycles A'.ρ) (B1 A'.ρ) S' Φ
    (fun a ha b => (hΦ a b).2 ((hF a a.2 b b.2).2.2.2 (Or.inl ha)))
    (fun b hb a => (hΦ a b).2 ((hF a a.2 b b.2).2.2.2 (Or.inr hb)))
    (fun a h => hnd.1 a a.2 fun b hb => (hΦ a ⟨b, hb⟩).1 (h _))
    (fun b h => hnd.2 b b.2 fun a ha => (hΦ ⟨a, ha⟩ b).1 (h _))
    hBS hSZ hBS' hSZ'
    (fun a b ha hb => (hΦ a b).2 (horth a ha b hb)) hdim
  exact ⟨fun a ha h => res.1 ⟨a, ha⟩ fun b hb => (hΦ _ _).2 (h b hb),
    fun b hb h => res.2 ⟨b, hb⟩ fun a ha => (hΦ _ _).2 (h a ha)⟩

open PositivityTheory.LocalTateOrthogonality.Bk in

/- English proof (translation)
Establish `hFin : FinZQ (Lp.PD K)` using `finZQ hT hE l Lp K`. Establish `hTop : TopInj (Lp.PD K)` using `topInj hT l Lp K`. Establish `hQ : DualQ (Lp.PD K)` using `dualQ hT l Lp K hTop`. Establish `hD : DualD (Lp.PD K)` using `dualDL l Lp K hFin hQ`. Establish `hCob : CobLO (Lp.PD K)` using `cobLO l Lp K hFin hTop`.

Establish `hH2 : LocalTateTopDegree (Lp.PD K)` using `tate_duality_H2_finite_coefficients hT l Lp K`. Establish `hLine : TopLine (Lp.PD K)` using `topLine l Lp K hH2 hCob`. Establish `hNd : NondegL (Lp.PD K)` using `nondegLL l Lp K hD hCob`. Conclude with `⟨hFin, hTop, hQ, hD, hCob, hLine, hNd, dualLOf l Lp K hFin hLine hNd⟩`.
-/
theorem formsL (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l) :
    FinZQ (Lp.PD K) ∧ TopInj (Lp.PD K) ∧ DualQ (Lp.PD K) ∧
      DualD (Lp.PD K) ∧ CobLO (Lp.PD K) ∧ TopLine (Lp.PD K) ∧
      NondegL (Lp.PD K) ∧ DualL (Lp.PD K) := by
  have hFin : FinZQ (Lp.PD K) := finZQ hT hE l Lp K
  have hTop : TopInj (Lp.PD K) := topInj hT l Lp K
  have hQ : DualQ (Lp.PD K) := dualQ hT l Lp K hTop
  have hD : DualD (Lp.PD K) := dualDL l Lp K hFin hQ
  have hCob : CobLO (Lp.PD K) := cobLO l Lp K hFin hTop
  have hH2 : LocalTateTopDegree (Lp.PD K) := tate_duality_H2_finite_coefficients hT l Lp K
  have hLine : TopLine (Lp.PD K) := topLine l Lp K hH2 hCob
  have hNd : NondegL (Lp.PD K) := nondegLL l Lp K hD hCob
  exact ⟨hFin, hTop, hQ, hD, hCob, hLine, hNd, dualLOf l Lp K hFin hLine hNd⟩

open PositivityTheory.LocalTateOrthogonality.Bk in

/- English proof (translation)
Introduce `LL _ _ _ O _ _ hO A A' m hdR hm`. Establish `ho` using `PositivityTheory.LocalTateOrthogonality.Orth.orthL_tied l Lp AI T K LL O hO A A' m hm hdR`. Use `haveI := hO.2.1`. Establish `hdR'` using `(GlobalTheory.TateDualFil.tateDual l Lp AI T K LL A.ρ A'.ρ m hdR hm).1`. Establish `e1` using `hdim LL O hO A hdR`.

Establish `e2` using `hdim LL O hO A' hdR'`. Establish `e3` using `(GlobalTheory.TateDualFil.tateDual l Lp AI T K LL A.ρ A'.ρ m hdR hm).2`. Establish `e4` using `hEu LL O hO A A' m hm`. Establish `e6` using `hm.2.2.2`. Unfold `IsDR at hdR hdR'`.

Rewrite `hdR'` using `[← e6]`. Establish `hc : finrank LL (H1V A.ρ) ≤ finrank LL (FiniteCohomology (Lp.PD K) A.ρ) + finrank LL (FiniteCohomology (Lp.PD K) A'.ρ)`. Use linear arithmetic over natural numbers and integers. Take `⟨h1, h2⟩` from `hL LL O hO A A' m hm (finiteCocycles (Lp.PD K) A.ρ) (finiteCocycles (Lp.PD K) A'.ρ) (B1_le_Z1f _ A) (fun _ h => h.1) (B1_le_Z1f _ A') (fun _ h => h.1) ho hc`. Conclude with `⟨fun a ha => ⟨ho a, h1 a ha⟩, fun b hb => ⟨fun h a ha => ho a ha b h, h2 b hb⟩⟩`.
-/
theorem bkAL (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (AI : LocAinf l Lp) (T : LocTied l Lp AI) (K : FinExt l)
    (hL : DualL (Lp.PD K))
    (hEu : ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O]
      [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
      ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL),
        IsDual1 (Lp.PD K) A.ρ A'.ρ P →
        finrank LL (H1V A.ρ) ≤
          finrank LL ↥(H0V A.ρ) + finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V)
    (hdim : LocalSituation.bkADim (Lp.PD K)) : bkACore (Lp.PD K) := by
  intro LL _ _ _ O _ _ hO A A' m hdR hm
  have ho := PositivityTheory.LocalTateOrthogonality.Orth.orthL_tied l Lp AI T K LL O hO A A' m hm hdR
  haveI := hO.2.1
  have hdR' := (GlobalTheory.TateDualFil.tateDual l Lp AI T K LL A.ρ A'.ρ m hdR hm).1
  have e1 := hdim LL O hO A hdR
  have e2 := hdim LL O hO A' hdR'
  have e3 := (GlobalTheory.TateDualFil.tateDual l Lp AI T K LL A.ρ A'.ρ m hdR hm).2
  have e4 := hEu LL O hO A A' m hm
  have e6 := hm.2.2.2
  unfold IsDR at hdR hdR'
  rw [← e6] at hdR'
  have hc : finrank LL (H1V A.ρ) ≤
      finrank LL (FiniteCohomology (Lp.PD K) A.ρ) + finrank LL (FiniteCohomology (Lp.PD K) A'.ρ) := by
    omega
  obtain ⟨h1, h2⟩ := hL LL O hO A A' m hm (finiteCocycles (Lp.PD K) A.ρ) (finiteCocycles (Lp.PD K) A'.ρ)
    (B1_le_Z1f _ A) (fun _ h => h.1) (B1_le_Z1f _ A') (fun _ h => h.1) ho hc
  exact ⟨fun a ha => ⟨ho a, h1 a ha⟩, fun b hb => ⟨fun h a ha => ho a ha b h, h2 b hb⟩⟩

open PositivityTheory.LocalTateOrthogonality.Bk in

/- English proof (translation)
Introduce `LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hdR hm`. Take `⟨hA1, -⟩` from `hA LL O hO A A' m hdR hm.1`. Use `hO.2.2.2.1` as an intermediate fact. Establish `hO' : IsOpen (L1.T : Set LL)` using `by rw [hL1]; exact hO.2.2.2.2`. Take `⟨⟨hdom, hdvr, -⟩, -⟩` from `id hO`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hTo : IsOpen (LA'.T : Set A'.V)` using `(latTop l Lp K LL O hO A' LA' ϖ hϖ).1`. Take `⟨-, hF⟩` from `cupFlip l Lp K LL O hO A A' m hm.1`. Establish `h1 : ∀ d ∈ latticeFiniteCocycles (Lp.PD K) LA, ∀ s ∈ HfD (Lp.PD K) LA', CobO (Lp.PD K) L1 (cupLD LA' m d s)` using `fun d hd s hs => by`. Take `⟨b, hb, rfl⟩` from `exists_of_mem_HfD hs`.

Rewrite using `[cobO_cup_iff hL1 hm d fun g => hd.1.2 g trivial]`. Conclude with `cobO_of_cobL hO' ((hA1 d hd.1.1).1 hd.2 b hb)`. Establish `h2 : ∀ d ∈ latticeCocycles LA, (∀ s ∈ HfD (Lp.PD K) LA', CobO (Lp.PD K) L1 (cupLD LA' m d s)) → d ∈ latticeFiniteCocycles (Lp.PD K) LA` using `fun d hd H => by`. Use `⟨hd, (hA1 d hd.1).2 fun b hb => ?_⟩` and prove the remaining obligations. Use `(hC LL O hO L1 hL1 _ (hF d hd.1 b hb.1).1).2 fun u => ?_` and prove the remaining obligations.

Establish `h3` using `(cobO_cup_iff hL1 hm d (fun g => hd.2 g trivial) (u • b)).1 (H _ (Submodule.mem_sup_left ⟨u • b, (finiteCocycles (Lp.PD K) A'.ρ).smul_mem u hb, rfl⟩))`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[cupL]`. Use `⟨fun s hs => ⟨fun h d hd => h1 d hd s h, fun H => ?_⟩, fun d hd => ⟨fun h s _ hs => h1 d h s hs, fun H => h2 d hd fun s hs => H s (hfD_le hTo hs) hs⟩⟩` and prove the remaining obligations.

Conclude with `hD LL O hO L1 hL1 A A' LA LA' m hm _ le_sup_right (hfD_le hTo) s hs fun d hd H' => H d (h2 d hd H')`.
-/
theorem bkBL (l : ℕ) [Fact l.Prime] (Lp : LocPrime l) (K : FinExt l) (hD : DualD (Lp.PD K))
    (hC : CobLO (Lp.PD K)) (hA : bkACore (Lp.PD K)) : bkBCore (Lp.PD K) := by
  intro LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hdR hm
  obtain ⟨hA1, -⟩ := hA LL O hO A A' m hdR hm.1
  have := hO.2.2.2.1
  have hO' : IsOpen (L1.T : Set LL) := by rw [hL1]; exact hO.2.2.2.2
  obtain ⟨⟨hdom, hdvr, -⟩, -⟩ := id hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hTo : IsOpen (LA'.T : Set A'.V) := (latTop l Lp K LL O hO A' LA' ϖ hϖ).1
  obtain ⟨-, hF⟩ := cupFlip l Lp K LL O hO A A' m hm.1
  have h1 : ∀ d ∈ latticeFiniteCocycles (Lp.PD K) LA, ∀ s ∈ HfD (Lp.PD K) LA',
      CobO (Lp.PD K) L1 (cupLD LA' m d s) := fun d hd s hs => by
    obtain ⟨b, hb, rfl⟩ := exists_of_mem_HfD hs
    rw [cobO_cup_iff hL1 hm d fun g => hd.1.2 g trivial]
    exact cobO_of_cobL hO' ((hA1 d hd.1.1).1 hd.2 b hb)
  have h2 : ∀ d ∈ latticeCocycles LA, (∀ s ∈ HfD (Lp.PD K) LA', CobO (Lp.PD K) L1 (cupLD LA' m d s)) →
      d ∈ latticeFiniteCocycles (Lp.PD K) LA := fun d hd H => by
    refine ⟨hd, (hA1 d hd.1).2 fun b hb => ?_⟩
    refine (hC LL O hO L1 hL1 _ (hF d hd.1 b hb.1).1).2 fun u => ?_
    have h3 := (cobO_cup_iff hL1 hm d (fun g => hd.2 g trivial) (u • b)).1
      (H _ (Submodule.mem_sup_left ⟨u • b, (finiteCocycles (Lp.PD K) A'.ρ).smul_mem u hb, rfl⟩))
    convert h3 using 1
    funext p
    simp [cupL]
  refine ⟨fun s hs => ⟨fun h d hd => h1 d hd s h, fun H => ?_⟩,
    fun d hd => ⟨fun h s _ hs => h1 d h s hs, fun H => h2 d hd fun s hs => H s (hfD_le hTo hs) hs⟩⟩
  exact hD LL O hO L1 hL1 A A' LA LA' m hm _ le_sup_right (hfD_le hTo) s hs
    fun d hd H' => H d (h2 d hd H')

/- English proof (translation)
Introduce `l _ Lp AI T K`. Establish `hT` using `PositivityTheory.LocalTateOrthogonality.Gcoh.top_tate`. Establish `hE` using `PositivityTheory.LocalTateOrthogonality.Gcoh.top_euler`. Take `⟨-, -, -, hD, hC, -, -, hL⟩` from `formsL hT hE l Lp K`. Establish `hdim` using `GlobalTheory.CompanionTheory.BKDim.bkADim_of_tied l Lp AI T K`.

Establish `hA` using `bkAL l Lp AI T K hL (eulerLe hT hE l Lp K) hdim`. Establish `hB` using `bkBL l Lp K hD hC hA`. Use `⟨?_, GlobalTheory.Published.BlochKato.rationalDuality_of_allCoefficients hA, GlobalTheory.Published.BlochKato.integralDuality_of_allCoefficients hB⟩` and prove the remaining obligations. Introduce `V _ _ _ _ _ _ _ ρ hc hdR`. Use `letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])`.

Use `haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Conclude with `GlobalTheory.T.finrank_H1f_de_rham l Lp AI T K ℚ_[l] ℤ_[l] GlobalTheory.Published.BlochKato.goodO_padicInt { V := V, ρ := ρ, cont := hc } hdR`.
-/
theorem blochKatoLocal : GlobalTheory.Published.BlochKatoLocal := by
  intro l _ Lp AI T K
  have hT := PositivityTheory.LocalTateOrthogonality.Gcoh.top_tate
  have hE := PositivityTheory.LocalTateOrthogonality.Gcoh.top_euler
  obtain ⟨-, -, -, hD, hC, -, -, hL⟩ := formsL hT hE l Lp K
  have hdim := GlobalTheory.CompanionTheory.BKDim.bkADim_of_tied l Lp AI T K
  have hA := bkAL l Lp AI T K hL (eulerLe hT hE l Lp K) hdim
  have hB := bkBL l Lp K hD hC hA
  refine ⟨?_, GlobalTheory.Published.BlochKato.rationalDuality_of_allCoefficients hA,
    GlobalTheory.Published.BlochKato.integralDuality_of_allCoefficients hB⟩
  intro V _ _ _ _ _ _ _ ρ hc hdR
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact GlobalTheory.T.finrank_H1f_de_rham l Lp AI T K ℚ_[l] ℤ_[l] GlobalTheory.Published.BlochKato.goodO_padicInt
    { V := V, ρ := ρ, cont := hc } hdR

end GlobalTheory.CompanionTheory.Hypotheses₂.BK
