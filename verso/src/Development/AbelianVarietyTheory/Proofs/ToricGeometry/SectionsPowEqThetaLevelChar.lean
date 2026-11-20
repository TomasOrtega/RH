import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfComplexPoints

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped BigOperators Real

namespace GlobalTheory.ThetaBundleSec

open ThetaBundleSym

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

/- English proof (translation)
Establish `hW : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((lbPow L n).U j ⊓ (lbPow L n).U j')` using `fun p hp => ⟨hj hp, hj' hp⟩`. Establish `hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)` using `Cartier.lbPow_U L n j ▸ hj`. Establish `hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j' PUnit.unit)` using `Cartier.lbPow_U L n j' ▸ hj'`. Establish `hW' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))` using `fun p hp => ⟨hi hp, hi' hp⟩`. Establish `h3` using `valAt'_res (u.ex z).left (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le) (L.g (j PUnit.unit) (j' PUnit.unit)).val hW`.

Establish `hc : ((lbPow L n).g j j').val = (resG A.left (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le) (L.g (j PUnit.unit) (j' PUnit.unit)).val) ^ n` using `(congrArg Units.val (Cartier.lbPow_g L n j j')).trans (Units.val_pow_eq_pow_val _ _)`. Rewrite using `[hc, valAt'_pow _ hW, h3, u.fr_compat _ _ z hW', mul_pow]`.
-/
theorem fr_pow_compat (u : HolUnif A L g) (z : Fin g → ℂ) (n : ℕ) (j j' : (lbPow L n).ι)
    (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j) (hj' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j') :
    u.fr (j PUnit.unit) z ^ n =
      valAt' (u.ex z).left ((lbPow L n).U j ⊓ (lbPow L n).U j') ((lbPow L n).g j j').val *
        u.fr (j' PUnit.unit) z ^ n := by
  have hW : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((lbPow L n).U j ⊓ (lbPow L n).U j') :=
    fun p hp => ⟨hj hp, hj' hp⟩
  have hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit) := Cartier.lbPow_U L n j ▸ hj
  have hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j' PUnit.unit) := Cartier.lbPow_U L n j' ▸ hj'
  have hW' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
    fun p hp => ⟨hi hp, hi' hp⟩
  have h3 := valAt'_res (u.ex z).left (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le)
    (L.g (j PUnit.unit) (j' PUnit.unit)).val hW
  have hc : ((lbPow L n).g j j').val =
      (resG A.left (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le)
        (L.g (j PUnit.unit) (j' PUnit.unit)).val) ^ n :=
    (congrArg Units.val (Cartier.lbPow_g L n j j')).trans (Units.val_pow_eq_pow_val _ _)
  rw [hc, valAt'_pow _ hW, h3, u.fr_compat _ _ z hW', mul_pow]

/- English proof (translation)
Establish `hcov : ∀ z, ∃ j : (lbPow L n).ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j`. Introduce `z`. Establish `hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i`. Rewrite using `[hL.cover]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hmem`. Use `⟨fun _ => i, ?_⟩` and prove the remaining obligations. Rewrite using `[Cartier.lbPow_U]`. Conclude with `(top_le_preimage_iff_mem _ _).2 hi`. Establish `hU : ∀ z (j : (lbPow L n).ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j → ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)` using `fun z j hj => Cartier.lbPow_U L n j ▸ hj`.

Use `choose c hc using hcov`. Set `θ : (Fin g → ℂ) → ℂ` to `fun z => valAt' (u.ex z).left ((lbPow L n).U (c z)) (s.f (c z)) / u.fr (c z PUnit.unit) z ^ n`. Establish `hθ : ∀ (j : (lbPow L n).ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j → θ z = valAt' (u.ex z).left ((lbPow L n).U j) (s.f j) / u.fr (j PUnit.unit) z ^ n` using `fun j z hj => SectionTheta.quot_eq u z (valAt'_rules _ _).2.1 (valAt'_rules _ _).2.2.1 n s _ _ (hc z) hj`. Establish `hfn : u.IsFnPow n s θ`. Introduce `j z hj`.

Rewrite using `[hθ j z hj, div_mul_cancel₀ _ (pow_ne_zero n (u.fr_ne _ z (hU z j hj)))]`. Use `⟨θ, fun z => ?_, hfn, fun θ' hθ' => ?_, fun z w k hzw hk => ?_⟩` and prove the remaining obligations. Take `⟨ho, hd⟩` from `u.hol _ (s.f (c z))`. Establish `hn` using `ho.mem_nhds (hc z)`. Establish `hd2 : DifferentiableOn ℂ (u.fr (c z PUnit.unit)) {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (lbPow L n).U (c z)}` using `(u.fr_hol _).mono fun w hw => hU w _ hw`.

Establish `hq` using `(hd.differentiableAt hn).mul (((hd2.differentiableAt hn).pow n).inv (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))))`. Use `hq.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hn] with w hw`. Conclude with `(hθ _ w hw).trans (div_eq_mul_inv _ _)`. Use function extensionality and compare the values at `z`.

Establish `h1` using `hfn (c z) z (hc z)`. Rewrite `h1` using `[hθ' (c z) z (hc z)]`. Conclude with `mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))) h1`. Establish `h1` using `hfn (c z) z (hc z)`. Establish `hc' : ⊤ ≤ (u.ex w).left ⁻¹ᵁ (lbPow L n).U (c z)`.

Rewrite using `[hzw]`. Conclude with `hc z`. Establish `h2` using `hfn (c z) w hc'`. Rewrite `h2` using `[hzw, h1, hk _ (hU z _ (hc z)), mul_pow, ← _root_.mul_assoc]`. Establish `h3` using `mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ _ (hU _ _ hc'))) h2`.

Rewrite using `[← h3, _root_.mul_comm]`.
-/
theorem exists_fn (u : HolUnif A L g) (hL : L.IsLB) (n : ℕ) (s : (lbPow L n).Sec) :
    ∃ θ, Differentiable ℂ θ ∧ u.IsFnPow n s θ ∧ (∀ θ', u.IsFnPow n s θ' → θ' = θ) ∧
      ∀ z w c, u.ex w = u.ex z → (∀ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = c * u.fr i w) →
        θ w = c ^ n * θ z := by
  have hcov : ∀ z, ∃ j : (lbPow L n).ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j := by
    intro z
    have hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
      rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    refine ⟨fun _ => i, ?_⟩
    rw [Cartier.lbPow_U]
    exact (top_le_preimage_iff_mem _ _).2 hi
  have hU : ∀ z (j : (lbPow L n).ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit) := fun z j hj => Cartier.lbPow_U L n j ▸ hj
  choose c hc using hcov
  let θ : (Fin g → ℂ) → ℂ := fun z =>
    valAt' (u.ex z).left ((lbPow L n).U (c z)) (s.f (c z)) / u.fr (c z PUnit.unit) z ^ n
  have hθ : ∀ (j : (lbPow L n).ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j →
      θ z = valAt' (u.ex z).left ((lbPow L n).U j) (s.f j) / u.fr (j PUnit.unit) z ^ n :=
    fun j z hj => SectionTheta.quot_eq u z (valAt'_rules _ _).2.1 (valAt'_rules _ _).2.2.1 n s _ _ (hc z) hj
  have hfn : u.IsFnPow n s θ := by
    intro j z hj
    rw [hθ j z hj, div_mul_cancel₀ _ (pow_ne_zero n (u.fr_ne _ z (hU z j hj)))]
  refine ⟨θ, fun z => ?_, hfn, fun θ' hθ' => ?_, fun z w k hzw hk => ?_⟩
  · obtain ⟨ho, hd⟩ := u.hol _ (s.f (c z))
    have hn := ho.mem_nhds (hc z)
    have hd2 : DifferentiableOn ℂ (u.fr (c z PUnit.unit))
        {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (lbPow L n).U (c z)} :=
      (u.fr_hol _).mono fun w hw => hU w _ hw
    have hq := (hd.differentiableAt hn).mul (((hd2.differentiableAt hn).pow n).inv
      (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))))
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [hn] with w hw
    exact (hθ _ w hw).trans (div_eq_mul_inv _ _)
  · funext z
    have h1 := hfn (c z) z (hc z)
    rw [hθ' (c z) z (hc z)] at h1
    exact mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))) h1
  · have h1 := hfn (c z) z (hc z)
    have hc' : ⊤ ≤ (u.ex w).left ⁻¹ᵁ (lbPow L n).U (c z) := by
      rw [hzw]; exact hc z
    have h2 := hfn (c z) w hc'
    rw [hzw, h1, hk _ (hU z _ (hc z)), mul_pow, ← _root_.mul_assoc] at h2
    have h3 := mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ _ (hU _ _ hc'))) h2
    rw [← h3, _root_.mul_comm]

/- English proof (translation)
Establish `hf : s.f = s'.f`. Use function extensionality and compare the values at `j`. Use `eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom A inferInstance inferInstance _ _ _ fun x hx => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `u.ex_onto x`. Rewrite using `[hs j z hx, hs' j z hx]`.

Consider the cases of `s`. Consider the cases of `s'`. Consider the cases of `hf`. Both sides reduce to the same expression.
-/
theorem sec_unique [IsReduced A.left] [LocallyOfFiniteType A.hom] (u : HolUnif A L g) (n : ℕ)
    {θ : (Fin g → ℂ) → ℂ} {s s' : (lbPow L n).Sec} (hs : u.IsFnPow n s θ) (hs' : u.IsFnPow n s' θ) : s = s' := by
  have hf : s.f = s'.f := by
    funext j
    refine eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom A inferInstance inferInstance _ _ _
      fun x hx => ?_
    obtain ⟨z, rfl⟩ := u.ex_onto x
    rw [hs j z hx, hs' j z hx]
  cases s
  cases s'
  cases hf
  rfl

/- English proof (translation)
Introduce `g τ hτ N hN X ex D hX hrat hNe _ hadd a b ha hb L u hL hu _ _ n`. Take `⟨hint, hprop, hex, hlat, -⟩` from `hX`. Take `⟨rfl, -, hlaw, hfr⟩` from `hu`. Establish `hext'` using `eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom X inferInstance inferInstance`. Use `⟨fun s => ?_, fun θ hθ => ?_⟩` and prove the remaining obligations.

Take `⟨θ, hd, hfn, huniq, haut⟩` from `exists_fn u hL n s`. Use `⟨θ, ⟨mem_thetaLevelChar_iff_autFactor.2 ⟨hd, fun m m' z => ?_⟩, hfn⟩, fun θ' h => huniq θ' h.2⟩` and prove the remaining obligations. Use `haut z _ _ ((hlat _ _).2 ?_) fun i hi => hlaw m m' i z hi` and prove the remaining obligations. Conclude with `⟨m, m', by abel⟩`. Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `⟨N - 1, by omega⟩`.

Use `choose h F hh hF hF' hU using hfr`. Establish `fh : ∀ i, HasFactor τ a b 0 (M + 1) (h i)` using `fun i => ⟨(hh i).1, fun n n' z => by`. Rewrite using `[(hh i).2, ThetaBundleSym.eC_nat_mul, pow_zero, _root_.one_mul]`. Use the proof step `rfl⟩`. Establish `fF : ∀ i, HasFactor τ a b 1 (M + 2) (F i)` using `fun i => ⟨hF i, fun n n' z => by`.

Rewrite using `[hF' i, ThetaBundleSym.eC_nat_mul, autFactor_eq]`. Express the relevant statement in the definitionally equal form `_ * basicFactor τ n z ^ (M + 1) * _ = _`. Use the proof step `ring⟩`. Establish `fθ : HasFactor τ a b n n θ` using `⟨hθ.1, fun m m' z => by`. Rewrite using `[(mem_thetaLevelChar_iff_autFactor.1 hθ).2, autFactor_eq, mul_pow]⟩`.

Establish `hev : Even (n * (M + 1))` using `hNe.mul_left n`. Take `⟨s, hs⟩` from `exists_sec hex hext' (lbPow L n) (fun j z => θ z * u.fr (j PUnit.unit) z ^ n) (fun j => by`. Take `⟨W, ψ, hψ⟩` from `hrat (n * (M + 2)) _ _ (((fθ.mul ((fh (j PUnit.unit)).pow n)).mul ((fF (j PUnit.unit)).pow (n * M))).level ha hb (by convert hev using 1; ring) _ (by ring)) (((fF (j PUnit.unit)).pow (n * (M + 1))).level ha hb (by convert hev using 1; ring) _ (by ring))`. Use `⟨W, ψ, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)` using `Cartier.lbPow_U L n j ▸ hz`.

Take `⟨a0, b0⟩` from `(hU _ z).1.1 hz'`. Establish `hq : F (j PUnit.unit) z ^ (n * (M + 1)) ≠ 0` using `pow_ne_zero _ b0`. Use `⟨(hψ z).1.2 hq, ((hψ z).2 hq).trans ?_⟩` and prove the remaining obligations. Rewrite using `[(hU _ z).2, div_pow]`. Clear the denominators using the available nonvanishing facts.

Use the proof step `ring)`. Use the proof step `(fun j j' z hj hj' => by`. Rewrite using `[fr_pow_compat u z n j j' hj hj']`. Use the proof step `ring)`. Conclude with `⟨s, hs, fun s' hs' => sec_unique u n hs' hs⟩`.
-/
theorem sections_pow_eq_thetaLevelChar :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z + w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ) ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n + ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n' : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n' : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠ 0) ∧ u.fr i z = h z / F z)) → IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → (∀ n : ℕ, (∀ s, ∃! θ, θ ∈ thetaLevelChar a b n τ ∧ u.IsFnPow n s θ) ∧ ∀ θ ∈ thetaLevelChar a b n τ, ∃! s, u.IsFnPow n s θ) := by
  intro g τ hτ N hN X ex D hX hrat hNe _ hadd a b ha hb L u hL hu _ _ n
  obtain ⟨hint, hprop, hex, hlat, -⟩ := hX
  obtain ⟨rfl, -, hlaw, hfr⟩ := hu
  have hext' := eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom X inferInstance inferInstance
  refine ⟨fun s => ?_, fun θ hθ => ?_⟩
  · obtain ⟨θ, hd, hfn, huniq, haut⟩ := exists_fn u hL n s
    refine ⟨θ, ⟨mem_thetaLevelChar_iff_autFactor.2 ⟨hd, fun m m' z => ?_⟩, hfn⟩, fun θ' h => huniq θ' h.2⟩
    refine haut z _ _ ((hlat _ _).2 ?_) fun i hi => hlaw m m' i z hi
    exact ⟨m, m', by abel⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  choose h F hh hF hF' hU using hfr
  have fh : ∀ i, HasFactor τ a b 0 (M + 1) (h i) := fun i => ⟨(hh i).1, fun n n' z => by
    rw [(hh i).2, ThetaBundleSym.eC_nat_mul, pow_zero, _root_.one_mul]; rfl⟩
  have fF : ∀ i, HasFactor τ a b 1 (M + 2) (F i) := fun i => ⟨hF i, fun n n' z => by
    rw [hF' i, ThetaBundleSym.eC_nat_mul, autFactor_eq]
    change _ * basicFactor τ n z ^ (M + 1) * _ = _
    ring⟩
  have fθ : HasFactor τ a b n n θ := ⟨hθ.1, fun m m' z => by
    rw [(mem_thetaLevelChar_iff_autFactor.1 hθ).2, autFactor_eq, mul_pow]⟩
  have hev : Even (n * (M + 1)) := hNe.mul_left n
  obtain ⟨s, hs⟩ := exists_sec hex hext' (lbPow L n) (fun j z => θ z * u.fr (j PUnit.unit) z ^ n)
    (fun j => by
      obtain ⟨W, ψ, hψ⟩ := hrat (n * (M + 2)) _ _
        (((fθ.mul ((fh (j PUnit.unit)).pow n)).mul ((fF (j PUnit.unit)).pow (n * M))).level ha hb
          (by convert hev using 1; ring) _ (by ring))
        (((fF (j PUnit.unit)).pow (n * (M + 1))).level ha hb (by convert hev using 1; ring) _ (by ring))
      refine ⟨W, ψ, fun z hz => ?_⟩
      have hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit) := Cartier.lbPow_U L n j ▸ hz
      obtain ⟨a0, b0⟩ := (hU _ z).1.1 hz'
      have hq : F (j PUnit.unit) z ^ (n * (M + 1)) ≠ 0 := pow_ne_zero _ b0
      refine ⟨(hψ z).1.2 hq, ((hψ z).2 hq).trans ?_⟩
      rw [(hU _ z).2, div_pow]
      field_simp
      ring)
    (fun j j' z hj hj' => by
      rw [fr_pow_compat u z n j j' hj hj']
      ring)
  exact ⟨s, hs, fun s' hs' => sec_unique u n hs' hs⟩

end GlobalTheory.ThetaBundleSec
