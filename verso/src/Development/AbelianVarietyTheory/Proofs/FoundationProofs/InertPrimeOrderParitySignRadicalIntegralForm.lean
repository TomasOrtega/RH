import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitPart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackFirstGroupRationalPointEqSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneScalarAvoidingMatrixEigenvalues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrameEmbeddingUniqueFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfEquivariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RelIndexImageOneSubComplexLinearEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtInertComponent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RelIndexNeZeroOfMoves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdSqNormEmbT
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetRationalMatrixTwoSidedMulEqProdEmbeddings
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalMatrixMulThetaLattices

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.OddRank

open GlobalTheory.VacuumScalar GlobalTheory.NormSum.VacMove

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 D.host.E) w`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Use `⟨a, b, ?_, hb0, div_mul_cancel₀ _ (by simpa using hb0)⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hw`.
-/
theorem present {w : D.host.E} (hw : w ≠ 0) : ∃ w₁ c : 𝓞 D.host.E, w₁ ≠ 0 ∧ c ≠ 0 ∧ w * c = w₁ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) w
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨a, b, ?_, hb0, div_mul_cancel₀ _ (by simpa using hb0)⟩
  rintro rfl
  simp at hw

def sN (y : 𝓞 D.host.E) : ℂ := sgn D (Ideal.absNorm (Ideal.span {y}))

/- English proof (translation)
Establish `h0 : Ideal.span {y} ≠ ⊥` using `by simpa using hy`. Use `haveI : Finite (𝓞 D.host.E ⧸ Ideal.span {y}) := Ideal.finiteQuotientOfFreeOfNeBot _ h0`. Conclude with `⟨(GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card D (𝓞 D.host.E ⧸ Ideal.span {y})).1, Ideal.absNorm_eq_zero_iff.not.2 h0⟩`.
-/
theorem ev_norm {y : 𝓞 D.host.E} (hy : y ≠ 0) :
    Ev D (Ideal.absNorm (Ideal.span {y})) ∧ Ideal.absNorm (Ideal.span {y}) ≠ 0 := by
  have h0 : Ideal.span {y} ≠ ⊥ := by simpa using hy
  haveI : Finite (𝓞 D.host.E ⧸ Ideal.span {y}) := Ideal.finiteQuotientOfFreeOfNeBot _ h0
  exact ⟨(GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card D (𝓞 D.host.E ⧸ Ideal.span {y})).1, Ideal.absNorm_eq_zero_iff.not.2 h0⟩

/- English proof (translation)
Use `sgn_of_eq ?_ (ev_norm hc).1 hi (ev_norm h1).1 (ev_norm hc).2 hi0 (ev_norm h1).2` and prove the remaining obligations. Establish `: (n : ℝ) * (Ideal.absNorm (Ideal.span {c}) : ℝ) ^ k = (i : ℝ) ^ k * (Ideal.absNorm (Ideal.span {w₁}) : ℝ) ^ k`. Rewrite using `[hn, ← GlobalTheory.TypeNormProduct.prod_sq_norm_embT, ← GlobalTheory.TypeNormProduct.prod_sq_norm_embT, ← h, mul_assoc, ← mul_pow, ← Finset.prod_mul_distrib]`. Simplify using `only [map_mul, norm_mul, mul_pow]`. Conclude with `this` after adjusting the coercions.
-/
theorem inertPrimeOrderParitySign_radical_integral_form {n i k : ℕ} {w : D.host.E} {w₁ c : 𝓞 D.host.E} (h1 : w₁ ≠ 0) (hc : c ≠ 0) (h : w * c = w₁)
    (hi : Ev D i) (hi0 : i ≠ 0) (hn : (n : ℝ) = (i : ℝ) ^ k * (∏ τ, ‖embT D τ w‖ ^ 2) ^ k) :
    sgn D n = sgn D i ^ k * (sN w₁ * sN c) ^ k := by
  refine sgn_of_eq ?_ (ev_norm hc).1 hi (ev_norm h1).1 (ev_norm hc).2 hi0 (ev_norm h1).2
  have : (n : ℝ) * (Ideal.absNorm (Ideal.span {c}) : ℝ) ^ k =
      (i : ℝ) ^ k * (Ideal.absNorm (Ideal.span {w₁}) : ℝ) ^ k := by
    rw [hn, ← GlobalTheory.TypeNormProduct.prod_sq_norm_embT, ← GlobalTheory.TypeNormProduct.prod_sq_norm_embT, ← h, mul_assoc, ← mul_pow, ← Finset.prod_mul_distrib]
    simp only [map_mul, norm_mul, mul_pow]
  exact_mod_cast this

/- English proof (translation)
Rewrite using `[mul_pow, sN, sN, sgn_pow_even _ hk, sgn_pow_even _ hk, one_mul]`.
-/
theorem sN_pow_even (a b : 𝓞 D.host.E) {k : ℕ} (hk : Even k) : (sN a * sN b) ^ k = 1 := by
  rw [mul_pow, sN, sN, sgn_pow_even _ hk, sgn_pow_even _ hk, one_mul]

/- English proof (translation)
Break down `hk with hk | hk` into its components or cases. Take `⟨w₁, c', a1, a2, a3⟩` from `present hw`. Rewrite using `[inertPrimeOrderParitySign_radical_integral_form a1 a2 a3 hi hi0 hn, sN_pow_even _ _ hk, sN_pow_even _ _ hk]`. Conclude with `inertPrimeOrderParitySign_radical_integral_form h1 hc h hi hi0 (by simpa only [hk] using hn)`.
-/
theorem sgn_rad {n i k : ℕ} {w y : D.host.E} {y₁ c : 𝓞 D.host.E} (hw : w ≠ 0) (h1 : y₁ ≠ 0) (hc : c ≠ 0)
    (h : y * c = y₁) (hk : Even k ∨ ∀ τ, ‖embT D τ y‖ = ‖embT D τ w‖)
    (hi : Ev D i) (hi0 : i ≠ 0) (hn : (n : ℝ) = (i : ℝ) ^ k * (∏ τ, ‖embT D τ w‖ ^ 2) ^ k) :
    sgn D n = sgn D i ^ k * (sN y₁ * sN c) ^ k := by
  rcases hk with hk | hk
  · obtain ⟨w₁, c', a1, a2, a3⟩ := present hw
    rw [inertPrimeOrderParitySign_radical_integral_form a1 a2 a3 hi hi0 hn, sN_pow_even _ _ hk, sN_pow_even _ _ hk]
  · exact inertPrimeOrderParitySign_radical_integral_form h1 hc h hi hi0 (by simpa only [hk] using hn)

/- English proof (translation)
Use `haveI : Finite (stdL D n ⧸ Submodule.comap (stdL D n).subtype L) := Nat.finite_of_card_ne_zero h`. Conclude with `(GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card D _).1`.
-/
theorem ev_idx {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : idx D L ≠ 0) : Ev D (idx D L) := by
  haveI : Finite (stdL D n ⧸ Submodule.comap (stdL D n).subtype L) := Nat.finite_of_card_ne_zero h
  exact (GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card D _).1

def prin {y : D.host.E} (hy : y ≠ 0) : (AE D)ˣ := Units.map (inc D).toMonoidHom (Units.mk0 y hy)

section Idem

variable {e : AE D} (h1 : e * e = e) (h2 : sgA D e = e)
  (h3 : ∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q e) ∧ (¬ InertQ D q → ZeroAt D q (1 - e)))

include h3 in
/- English proof (translation)
Use `GlobalTheory.InertValue.character_at_inert_component D n χ y _ hy fun q hq => ⟨fun hi => ?_, fun hi => ?_⟩` and prove the remaining obligations. Use `zeroAt_mul D hq ((h3 q hq).1 hi) (1 - inc D y) using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `(1 - e) * inc D y + (1 - (1 - e)) * 1 - _ = _`. Expand and normalize the polynomial expressions, which then agree. Use `zeroAt_mul D hq ((h3 q hq).2 hi) (inc D y - 1) using 1` and compare the differences between its conclusion and the goal.

Express the relevant statement in the definitionally equal form `(1 - e) * inc D y + (1 - (1 - e)) * 1 - _ = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chi_inert {n : ℕ} (χ : HeckeU D n) {y : 𝓞 D.host.E} (hy : y ≠ 0) (hy' : (y : D.host.E) ≠ 0) :
    ((χ.f (Units.map (cut (1 - e) (compl_idem h1)) (prin hy')) : ℂˣ) : ℂ) = sN y ^ n := by
  refine GlobalTheory.InertValue.character_at_inert_component D n χ y _ hy fun q hq => ⟨fun hi => ?_, fun hi => ?_⟩
  · convert zeroAt_mul D hq ((h3 q hq).1 hi) (1 - inc D y) using 1
    change (1 - e) * inc D y + (1 - (1 - e)) * 1 - _ = _
    ring
  · convert zeroAt_mul D hq ((h3 q hq).2 hi) (inc D y - 1) using 1
    change (1 - e) * inc D y + (1 - (1 - e)) * 1 - _ = _
    ring

include h3 in

/- English proof (translation)
Establish `b1 : (y₁ : D.host.E) ≠ 0` using `by simpa using a1`. Establish `b2 : (c : D.host.E) ≠ 0` using `by simpa using a2`. Establish `hp : prin hy * prin b2 = prin b1` using `Units.ext (by`. Express the relevant statement in the definitionally equal form `inc D y * inc D c = inc D y₁`. Rewrite using `[← map_mul, h])`.

Establish `hsplit : prin hy = Units.map (cut e h1) (prin hy) * Units.map (cut (1 - e) (compl_idem h1)) (prin hy)` using `Units.ext (cut_mul_cut e h1 ((prin hy : (AE D)ˣ) : AE D)).1.symm`. Establish `c1` using `chi_inert h1 h3 χ a1 b1`. Rewrite `c1` using `[← hp, map_mul, map_mul, Units.val_mul, chi_inert h1 h3 χ a2 b2]`. Establish `ha : ((χ.f (prin hy) : ℂˣ) : ℂ) * ∏ τ, (embT D τ y / (‖embT D τ y‖ : ℂ)) ^ χ.n τ = 1` using `χ.aut (Units.mk0 y hy)`. Rewrite `ha` using `[hsplit, map_mul, Units.val_mul]`.

Establish `s1 : sN y₁ ^ n * sN y₁ ^ n = 1` using `by rw [← mul_pow, sN, sgn_mul_self, one_pow]`. Simplify using `only [zpow_neg, Finset.prod_inv_distrib]`. Rewrite using `[← eq_inv_of_mul_eq_one_left ha, mul_pow]`. Take the linear combination `(-(sN y₁ ^ n) * ((χ.f (Units.map (cut e h1) (prin hy)) : ℂˣ) : ℂ)) * c1 - ((χ.f (Units.map (cut e h1) (prin hy)) : ℂˣ) : ℂ) * s1`.
-/
theorem chi_split {n : ℕ} (χ : HeckeU D n) {y : D.host.E} (hy : y ≠ 0) {y₁ c : 𝓞 D.host.E} (a1 : y₁ ≠ 0)
    (a2 : c ≠ 0) (h : y * c = y₁) :
    ((χ.f (Units.map (cut e h1) (prin hy)) : ℂˣ) : ℂ) =
      (sN y₁ * sN c) ^ n * ∏ τ, (embT D τ y / (‖embT D τ y‖ : ℂ)) ^ (-(χ.n τ)) := by
  have b1 : (y₁ : D.host.E) ≠ 0 := by simpa using a1
  have b2 : (c : D.host.E) ≠ 0 := by simpa using a2
  have hp : prin hy * prin b2 = prin b1 := Units.ext (by
    change inc D y * inc D c = inc D y₁
    rw [← map_mul, h])
  have hsplit : prin hy = Units.map (cut e h1) (prin hy) * Units.map (cut (1 - e) (compl_idem h1)) (prin hy) :=
    Units.ext (cut_mul_cut e h1 ((prin hy : (AE D)ˣ) : AE D)).1.symm
  have c1 := chi_inert h1 h3 χ a1 b1
  rw [← hp, map_mul, map_mul, Units.val_mul, chi_inert h1 h3 χ a2 b2] at c1
  have ha : ((χ.f (prin hy) : ℂˣ) : ℂ) * ∏ τ, (embT D τ y / (‖embT D τ y‖ : ℂ)) ^ χ.n τ = 1 := χ.aut (Units.mk0 y hy)
  rw [hsplit, map_mul, Units.val_mul] at ha
  have s1 : sN y₁ ^ n * sN y₁ ^ n = 1 := by rw [← mul_pow, sN, sgn_mul_self, one_pow]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  rw [← eq_inv_of_mul_eq_one_left ha, mul_pow]
  linear_combination (-(sN y₁ ^ n) * ((χ.f (Units.map (cut e h1) (prin hy)) : ℂˣ) : ℂ)) * c1 -
    ((χ.f (Units.map (cut e h1) (prin hy)) : ℂˣ) : ℂ) * s1

include h3 in
/- English proof (translation)
Use `set d : AE D := ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) with hdef`. Establish `hxv : (x : AE D) = d * sgA D x` using `congrArg Units.val hx`. Use `⟨fun q hq hi => ?_, Units.ext ?_⟩` and prove the remaining obligations. Use `zeroAt_mul D hq ((h3 q hq).1 hi) (x - 1) using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `e * x + (1 - e) * 1 - 1 = _`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Units.val_mul, det_cutG, ← hdef]`. Express the relevant statement in the definitionally equal form `e * x + (1 - e) * 1 = _ * sgA D (e * x + (1 - e) * 1)`. Rewrite using `[map_add, map_mul, map_mul, map_sub, map_one, h2]`. Take the linear combination `e * hxv + (d + sgA D x - 1 - d * sgA D x) * h1`.
-/
theorem split_part (g : GA D N) {x : (AE D)ˣ}
    (hx : x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x) :
    (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q (((Units.map (cut e h1) x : (AE D)ˣ) : AE D) - 1)) ∧
      Units.map (cut e h1) x = Matrix.GeneralLinearGroup.det ((cutG e h1 h2 g : GA D N) : GL (Fin N) (AE D)) *
        sgU D (Units.map (cut e h1) x) := by
  set d : AE D := ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) with hdef
  have hxv : (x : AE D) = d * sgA D x := congrArg Units.val hx
  refine ⟨fun q hq hi => ?_, Units.ext ?_⟩
  · convert zeroAt_mul D hq ((h3 q hq).1 hi) (x - 1) using 1
    change e * x + (1 - e) * 1 - 1 = _
    ring
  · rw [Units.val_mul, det_cutG, ← hdef]
    change e * x + (1 - e) * 1 = _ * sgA D (e * x + (1 - e) * 1)
    rw [map_add, map_mul, map_mul, map_sub, map_one, h2]
    linear_combination e * hxv + (d + sgA D x - 1 - d * sgA D x) * h1

include h2 h3 in

/- English proof (translation)
Take `⟨b1, b2⟩` from `split_part h1 h2 h3 g hx`. Take `⟨c1, c2⟩` from `split_part h1 h2 h3 g' hx'`. Take `⟨c, hO⟩` from `GlobalTheory.VacuumEven.exists_scalar hc he W hL hL'`. Take `⟨Ls, hLs⟩` from `exists_moves (cutG e h1 h2 g)`. Take `⟨Ls', hLs'⟩` from `exists_moves (cutG e h1 h2 g')`.

Take `⟨Li, hLi⟩` from `exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g)`. Take `⟨Li', hLi'⟩` from `exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g')`. Establish `hs : ∀ {n : ℕ} (k : GA D n), SuppSplit D ((cutG e h1 h2 k : GA D n) : GL (Fin n) (AE D))` using `fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).1 hi)`. Establish `hi : ∀ {n : ℕ} (k : GA D n), SuppInert D ((cutG (1 - e) (compl_idem h1) (compl_fixed h2) k : GA D n) : GL (Fin n) (AE D))` using `fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).2 hi)`. Establish `hcc` using `scalar_mul hc he W (cutG_mul e h1 h2 g).1 (cutG_mul e h1 h2 g).2 (cutG_mul e h1 h2 g').1 (cutG_mul e h1 h2 g').2 (hs g) (hs g') (hi g) (hi g') hL hL' hLs hLs' hLi hLi' hO (W.split _ _ _ _ Ls Ls' (hs g) (hs g') (fun q hq h => ⟨b1 q hq h, c1 q hq h⟩) b2 c2 hLs hLs') (GlobalTheory.I …`.

Establish `l1` using `GlobalTheory.InertParity.LengthSign.neg_one_pow_lenQ D N _ _ Li L (hs g) (hi g) hLi (by rwa [(cutG_mul e h1 h2 g).2])`. Establish `l2` using `GlobalTheory.InertParity.LengthSign.neg_one_pow_lenQ D N' _ _ Li' L' (hs g') (hi g') hLi' (by rwa [(cutG_mul e h1 h2 g').2])`. Rewrite using `[hO, hcc, pow_add, mul_comm N, mul_comm N', pow_mul, pow_mul, l1, l2]`. Simplify using `only [Units.val_mul, Units.val_zpow_eq_zpow_val]`.
-/
theorem vac (hc : Crv D cc δ) (hN : Even (N * N')) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) {g : GA D N} {g' : GA D N'}
    {x x' : (AE D)ˣ} {L L'} (hx : x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x)
    (hx' : x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin N') (AE D)) * sgU D x')
    (hL : Moves D (g : GL (Fin N) (AE D)) L) (hL' : Moves D (g' : GL (Fin N') (AE D)) L') :
    W.Om g g' e0 = (sgn D (idx D L') ^ N * sgn D (idx D L) ^ N' *
      (((W.chV.f (Units.map (cut e h1) x') : ℂˣ) : ℂ) ^ W.ep * ((W.chV'.f (Units.map (cut e h1) x) : ℂˣ) : ℂ) ^ W.ep')) •
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 := by
  obtain ⟨b1, b2⟩ := split_part h1 h2 h3 g hx
  obtain ⟨c1, c2⟩ := split_part h1 h2 h3 g' hx'
  obtain ⟨c, hO⟩ := GlobalTheory.VacuumEven.exists_scalar hc he W hL hL'
  obtain ⟨Ls, hLs⟩ := exists_moves (cutG e h1 h2 g)
  obtain ⟨Ls', hLs'⟩ := exists_moves (cutG e h1 h2 g')
  obtain ⟨Li, hLi⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g)
  obtain ⟨Li', hLi'⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g')
  have hs : ∀ {n : ℕ} (k : GA D n), SuppSplit D ((cutG e h1 h2 k : GA D n) : GL (Fin n) (AE D)) :=
    fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).1 hi)
  have hi : ∀ {n : ℕ} (k : GA D n),
      SuppInert D ((cutG (1 - e) (compl_idem h1) (compl_fixed h2) k : GA D n) : GL (Fin n) (AE D)) :=
    fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).2 hi)
  have hcc := scalar_mul hc he W (cutG_mul e h1 h2 g).1 (cutG_mul e h1 h2 g).2 (cutG_mul e h1 h2 g').1
    (cutG_mul e h1 h2 g').2 (hs g) (hs g') (hi g) (hi g') hL hL' hLs hLs' hLi hLi' hO
    (W.split _ _ _ _ Ls Ls' (hs g) (hs g') (fun q hq h => ⟨b1 q hq h, c1 q hq h⟩) b2 c2 hLs hLs')
    (GlobalTheory.InertSign.vacuum_inert D cc δ hc N N' hN e0 he W _ _ Li Li' (hi g) (hi g') hLi hLi')
  have l1 := GlobalTheory.InertParity.LengthSign.neg_one_pow_lenQ D N _ _ Li L (hs g) (hi g) hLi (by rwa [(cutG_mul e h1 h2 g).2])
  have l2 := GlobalTheory.InertParity.LengthSign.neg_one_pow_lenQ D N' _ _ Li' L' (hs g') (hi g') hLi' (by rwa [(cutG_mul e h1 h2 g').2])
  rw [hO, hcc, pow_add, mul_comm N, mul_comm N', pow_mul, pow_mul, l1, l2]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]

end Idem

/- English proof (translation)
Take `⟨ε, -, a1, a2, h3⟩` from `exists_half_idem D`. Use `⟨_, ?_, by rw [map_add, sgA_sgA, add_comm], h3⟩` and prove the remaining obligations. Establish `a3 : sgA D ε * sgA D ε = sgA D ε` using `by rw [← map_mul, a1]`. Take the linear combination `a1 + a3 + 2 * a2`.
-/
theorem exists_idem (D : D7) : ∃ e : AE D, e * e = e ∧ sgA D e = e ∧
    ∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q e) ∧ (¬ InertQ D q → ZeroAt D q (1 - e)) := by
  obtain ⟨ε, -, a1, a2, h3⟩ := exists_half_idem D
  refine ⟨_, ?_, by rw [map_add, sgA_sgA, add_comm], h3⟩
  have a3 : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, a1]
  linear_combination a1 + a3 + 2 * a2

/- English proof (translation)
Establish `: (‖w‖ : ℂ) ≠ 0` using `by simpa using hw`. Rewrite using `[div_eq_div_iff this hw, mul_comm, Complex.mul_conj', sq]`.
-/
theorem phase_conj {w : ℂ} (hw : w ≠ 0) : starRingEnd ℂ w / (‖w‖ : ℂ) = (‖w‖ : ℂ) / w := by
  have : (‖w‖ : ℂ) ≠ 0 := by simpa using hw
  rw [div_eq_div_iff this hw, mul_comm, Complex.mul_conj', sq]

/- English proof (translation)
Establish `hw' : D.host.conj w ≠ 0` using `by simpa using hw`. Establish `hτ : ∀ τ, embT D τ w ≠ 0` using `fun τ => by simpa using hw`. Break down `Nat.even_or_odd n with h0 | h0` into its components or cases. Use `⟨D.host.conj w, hw', by rw [conj_conj, h, h0.neg_one_pow, one_mul], ?_, Or.inr fun τ => by rw [embT_conj, Complex.norm_conj]⟩` and prove the remaining obligations. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[embT_conj, Complex.norm_conj, phase_conj (hτ τ)]`. Establish `hk : Even k` using `(Nat.even_mul.1 hn).resolve_left (Nat.not_even_iff_odd.2 h0)`. Establish `hr` using `Formalism.MainNotions.BoundaryLocalData.sqrtMinusD_sq D`. Establish `hr'` using `Formalism.MainNotions.BoundaryLocalData.conj_sqrtMinusD D`. Use `set r := D.host.sqrtMinusD`.

Establish `hd : (D.host.d : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 D.host.hyp.2.1.ne_zero`. Establish `hr0 : r ≠ 0`. Introduce `h0`. Rewrite `hr` using `[h0]`. Conclude with `hd (by linear_combination hr)`.

Use `⟨r * D.host.conj w, mul_ne_zero hr0 hw', ?_, ?_, Or.inl hk⟩` and prove the remaining obligations. Rewrite using `[map_mul, conj_conj, hr', h, h0.neg_one_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hρ : ∀ τ, (embT D τ r / (‖embT D τ r‖ : ℂ)) ^ 2 = -1`. Introduce `τ`.

Establish `h0 : embT D τ r ≠ 0` using `by simpa using hr0`. Rewrite using `[div_pow, ← Complex.mul_conj', ← embT_conj, hr', map_neg]`. Clear the denominators using the available nonvanishing facts. Take `⟨j, rfl⟩` from `hk`. Establish `: ∀ τ, (embT D τ (r * D.host.conj w) / (‖embT D τ (r * D.host.conj w)‖ : ℂ)) ^ (j + j) = (-1) ^ j * ((‖embT D τ w‖ : ℂ) / embT D τ w) ^ (j + j)`.

Introduce `τ`. Rewrite using `[← hρ τ, ← pow_mul, two_mul, ← mul_pow, ← phase_conj (hτ τ), map_mul, norm_mul, embT_conj, Complex.norm_conj, Complex.ofReal_mul, mul_div_mul_comm]`. Simplify using `only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`. Rewrite using `[← pow_mul, ((show Even (Fintype.card D.what₂.Tau) from D.what₂.card_Tau ▸ even_two_mul _).mul_left j).neg_one_pow, one_mul]`.
-/
theorem exists_sol {n k : ℕ} (hn : Even (n * k)) {g w : D.host.E} (hw : w ≠ 0)
    (h : D.host.conj w = (-1) ^ n * g * w) :
    ∃ y, y ≠ 0 ∧ y = g * D.host.conj y ∧
      ∏ τ, ((‖embT D τ w‖ : ℂ) / embT D τ w) ^ k = ∏ τ, (embT D τ y / (‖embT D τ y‖ : ℂ)) ^ k ∧
      (Even k ∨ ∀ τ, ‖embT D τ y‖ = ‖embT D τ w‖) := by
  have hw' : D.host.conj w ≠ 0 := by simpa using hw
  have hτ : ∀ τ, embT D τ w ≠ 0 := fun τ => by simpa using hw
  rcases Nat.even_or_odd n with h0 | h0
  · refine ⟨D.host.conj w, hw', by rw [conj_conj, h, h0.neg_one_pow, one_mul], ?_,
      Or.inr fun τ => by rw [embT_conj, Complex.norm_conj]⟩
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [embT_conj, Complex.norm_conj, phase_conj (hτ τ)]
  · have hk : Even k := (Nat.even_mul.1 hn).resolve_left (Nat.not_even_iff_odd.2 h0)
    have hr := Formalism.MainNotions.BoundaryLocalData.sqrtMinusD_sq D
    have hr' := Formalism.MainNotions.BoundaryLocalData.conj_sqrtMinusD D
    set r := D.host.sqrtMinusD
    have hd : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 D.host.hyp.2.1.ne_zero
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0] at hr
      exact hd (by linear_combination hr)
    refine ⟨r * D.host.conj w, mul_ne_zero hr0 hw', ?_, ?_, Or.inl hk⟩
    · rw [map_mul, conj_conj, hr', h, h0.neg_one_pow]; ring
    · have hρ : ∀ τ, (embT D τ r / (‖embT D τ r‖ : ℂ)) ^ 2 = -1 := by
        intro τ
        have h0 : embT D τ r ≠ 0 := by simpa using hr0
        rw [div_pow, ← Complex.mul_conj', ← embT_conj, hr', map_neg]
        field_simp
      obtain ⟨j, rfl⟩ := hk
      have : ∀ τ, (embT D τ (r * D.host.conj w) / (‖embT D τ (r * D.host.conj w)‖ : ℂ)) ^ (j + j) =
          (-1) ^ j * ((‖embT D τ w‖ : ℂ) / embT D τ w) ^ (j + j) := by
        intro τ
        rw [← hρ τ, ← pow_mul, two_mul, ← mul_pow, ← phase_conj (hτ τ), map_mul, norm_mul, embT_conj,
          Complex.norm_conj, Complex.ofReal_mul, mul_div_mul_comm]
      simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      rw [← pow_mul, ((show Even (Fintype.card D.what₂.Tau) from D.what₂.card_Tau ▸ even_two_mul _).mul_left j).neg_one_pow, one_mul]

/- English proof (translation)
Establish `h1 : S ^ ε = S`. Break down `hε with rfl | rfl` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[zpow_neg_one]`. Conclude with `(eq_inv_of_mul_eq_one_left hS).symm`.

Rewrite using `[mul_zpow, h1, mul_left_comm, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hg, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ (hθ i)]`. Use `congr 1`.

Use `push_cast`. Take the linear combination `ha i`.
-/
theorem scalar_id {ι : Type} [Fintype ι] {θ g : ι → ℂ} {n a : ι → ℤ} {S : ℂ} {ε k : ℤ} (hθ : ∀ i, θ i ≠ 0)
    (hg : ∀ i, g i = θ i ^ 2) (ha : ∀ i, 2 * a i = ε * n i + k) (hS : S * S = 1) (hε : ε = 1 ∨ ε = -1) :
    (S * ∏ i, θ i ^ (-(n i))) ^ ε = (∏ i, g i ^ (-(a i))) * (S * ∏ i, θ i ^ k) := by
  have h1 : S ^ ε = S := by
    rcases hε with rfl | rfl
    · simp
    · rw [zpow_neg_one]; exact (eq_inv_of_mul_eq_one_left hS).symm
  rw [mul_zpow, h1, mul_left_comm, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hg, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ (hθ i)]
  congr 1
  push_cast
  linear_combination ha i

/- English proof (translation)
Establish `h0 : embT D τ y ≠ 0` using `by simpa using hy`. Establish `h0' : starRingEnd ℂ (embT D τ y) ≠ 0` using `by simpa using hy`. Use `congrArg (embT D τ) h` as an intermediate fact. Rewrite `this` using `[map_mul, embT_conj]`. Rewrite using `[div_pow, ← Complex.mul_conj', eq_div_iff (mul_ne_zero h0 h0')]`.

Take the linear combination `(-embT D τ y) * this`.
-/
theorem sq_phase {g y : D.host.E} (hy : y ≠ 0) (h : y = g * D.host.conj y) (τ : D.what₂.Tau) :
    embT D τ g = (embT D τ y / (‖embT D τ y‖ : ℂ)) ^ 2 := by
  have h0 : embT D τ y ≠ 0 := by simpa using hy
  have h0' : starRingEnd ℂ (embT D τ y) ≠ 0 := by simpa using hy
  have := congrArg (embT D τ) h
  rw [map_mul, embT_conj] at this
  rw [div_pow, ← Complex.mul_conj', eq_div_iff (mul_ne_zero h0 h0')]
  linear_combination (-embT D τ y) * this

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Unfold `IsRat at hr`. Rewrite using `[Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, hr, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Express the relevant statement in the definitionally equal form `inc D y = _ * sgA D (inc D y)`. Rewrite using `[PtsMem.sgA_inc, ← map_mul, ← h]`.
-/
theorem prin_eq {n : ℕ} {g : GA D n} {γ : Matrix (Fin n) (Fin n) D.host.E} (hr : IsRat D (g : GL (Fin n) (AE D)) γ)
    {y : D.host.E} (hy : y ≠ 0) (h : y = γ.det * D.host.conj y) :
    prin hy = Matrix.GeneralLinearGroup.det (g : GL (Fin n) (AE D)) * sgU D (prin hy) := by
  refine Units.ext ?_
  unfold IsRat at hr
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, hr, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  change inc D y = _ * sgA D (inc D y)
  rw [PtsMem.sgA_inc, ← map_mul, ← h]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem one_eq (n : ℕ) : (1 : (AE D)ˣ) =
    Matrix.GeneralLinearGroup.det ((1 : GA D n) : GL (Fin n) (AE D)) * sgU D 1 := by simp

open GlobalTheory.RatRow (adj_adj klat isRat_one hf_unitary det_adj adj_one_sub)

/- English proof (translation)
Use `(GlobalTheory.ThetaStab.mulV_theta_lattices D cc δ hc N N').1 _ _ (fun i j => ?_) GlobalTheory.RatRow.integral_one` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, Matrix.one_apply]`. Use `split_ifs`. Rewrite using `[smul_eq_mul, mul_one]`. Conclude with `b.2`.

Simplify using `using isIntegral_zero`.
-/
theorem scal_mem (hc : Crv D cc δ) (b : 𝓞 D.host.E) :
    ∀ x ∈ La0 D (tor0 D cc δ) N N', scal D N N' (b : D.host.E) x ∈ La0 D (tor0 D cc δ) N N' := by
  refine (GlobalTheory.ThetaStab.mulV_theta_lattices D cc δ hc N N').1 _ _ (fun i j => ?_) GlobalTheory.RatRow.integral_one
  rw [Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · rw [smul_eq_mul, mul_one]; exact b.2
  · simpa using isIntegral_zero

/- English proof (translation)
Simplify using `only [scal, mulV_mulV, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]`.
-/
theorem scal_comm (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E) (b : D.host.E)
    (x : VC D N N') : mulV D M' M (scal D N N' b x) = scal D N N' b (mulV D M' M x) := by
  simp only [scal, mulV_mulV, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/- English proof (translation)
Establish `k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N')` using `klat _ (moves_one D N) (moves_one D N')`. Establish `hd0 : LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0`. Rewrite using `[hd]`. Conclude with `Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ((map_ne_zero _).2 hw)`. Establish `h2` using `(GlobalTheory.ThetaCovIndex.relIndex_one_sub D cc δ hc N N' _ _ k0 k1 u hu hA hd0 hm).2`.

Rewrite using `[GlobalTheory.EquivConst.const_of_equivariant D cc δ hc N N' _ _ k0 k1 u hu hA hd0 hm (scal_mem hc) hs th hth, sgn_rad (i := i) (k := k) hw a1 a2 h hk hiv hi0 (by`. Rewrite using `[h2, hi, hd, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow]`. Simplify using `only [norm_pow, ← pow_mul, mul_comm k 2, Nat.cast_pow]),`. Use the proof step `hd, norm_prod, Complex.ofReal_prod, ← Finset.prod_div_distrib, mul_assoc]`. Simplify using `only [norm_pow, Complex.ofReal_pow, div_pow]`.
-/
theorem const (hc : Crv D cc δ) {A₁ : AddSubgroup (VC D N N')} (k1 : KLat D (tor0 D cc δ) A₁)
    (u : VC D N N' ≃ₗ[ℂ] VC D N N') (hu : ∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w)
    (hA : ∀ x, x ∈ La0 D (tor0 D cc δ) N N' ↔ u x ∈ A₁) {w : D.host.E} (hw : w ≠ 0) {k i : ℕ}
    (hd : LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) = ∏ τ, embT D τ w ^ k)
    (hm : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ La0 D (tor0 D cc δ) N N', ∃ y ∈ La0 D (tor0 D cc δ) N N',
      u.symm y ∈ La0 D (tor0 D cc δ) N N' ∧ m • x = y - u.symm y)
    (hs : ∀ (b : D.host.E) x, u (scal D N N' b x) = scal D N N' b (u x))
    (hi : A₁.relIndex (La0 D (tor0 D cc δ) N N') = i ^ k) (hi0 : i ≠ 0) (hiv : Ev D i)
    {y : D.host.E} {y₁ c : 𝓞 D.host.E} (a1 : y₁ ≠ 0) (a2 : c ≠ 0) (h : y * c = y₁)
    (hk : Even k ∨ ∀ τ, ‖embT D τ y‖ = ‖embT D τ w‖) {th : VC D N N' → ℂ}
    (hth : th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) :
    (fun z => th (u.symm z)) = (sgn D i ^ k * ((sN y₁ * sN c) ^ k * ∏ τ, ((‖embT D τ w‖ : ℂ) / embT D τ w) ^ k)) •
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') A₁ th := by
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := klat _ (moves_one D N) (moves_one D N')
  have hd0 : LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 := by
    rw [hd]; exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ((map_ne_zero _).2 hw)
  have h2 := (GlobalTheory.ThetaCovIndex.relIndex_one_sub D cc δ hc N N' _ _ k0 k1 u hu hA hd0 hm).2
  rw [GlobalTheory.EquivConst.const_of_equivariant D cc δ hc N N' _ _ k0 k1 u hu hA hd0 hm (scal_mem hc) hs th hth,
    sgn_rad (i := i) (k := k) hw a1 a2 h hk hiv hi0 (by
      rw [h2, hi, hd, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow]
      simp only [norm_pow, ← pow_mul, mul_comm k 2, Nat.cast_pow]),
    hd, norm_prod, Complex.ofReal_prod, ← Finset.prod_div_distrib, mul_assoc]
  simp only [norm_pow, Complex.ofReal_pow, div_pow]

/- English proof (translation)
The claim follows from `div_ne_zero (by simpa using hy) (by simpa using hy)`.
-/
theorem phase_ne {y : D.host.E} (hy : y ≠ 0) (τ : D.what₂.Tau) : embT D τ y / (‖embT D τ y‖ : ℂ) ≠ 0 :=
  div_ne_zero (by simpa using hy) (by simpa using hy)

/- English proof (translation)
Rewrite using `[← pow_add]`. Conclude with `sN_pow_even a b ⟨k, rfl⟩`.
-/
theorem sN_sq (a b : 𝓞 D.host.E) (k : ℕ) : (sN a * sN b) ^ k * (sN a * sN b) ^ k = 1 := by
  rw [← pow_add]; exact sN_pow_even a b ⟨k, rfl⟩

/- English proof (translation)
Establish `h1 : γ * adj D γ = 1` using `(mem_ratG_intG D N').2.2.2.1 γA γ hr`. Establish `h2 : adj D γ * γ = 1` using `mul_eq_one_comm.1 h1`. Take `⟨L, hL⟩` from `exists_moves γA`. Take `⟨-, st2, st3⟩` from `GlobalTheory.ThetaStab.mulV_theta_lattices D cc δ hc N N'`. Set `u : VC D N N' ≃ₗ[ℂ] VC D N N'` to `LinearEquiv.ofLinear (mulV D γ 1) (mulV D (adj D γ) 1) (LinearMap.ext fun x => by simp [mulV_mulV, h1, mulV_one]) (LinearMap.ext fun x => by simp [mulV_mulV, h2, mulV_one])`.

Establish `hu : ∀ x, u x = mulV D γ 1 x` using `fun x => rfl`. Establish `hsub : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D (1 - adj D γ) 1` using `LinearMap.ext fun x => by`. Rewrite using `[mulV_sub_left, mulV_one]`. Both sides reduce to the same expression. Establish `hd : (1 - adj D γ).det = D.host.conj (1 - γ).det` using `by rw [← adj_one_sub, det_adj]`.

Establish `hd0 : (1 - adj D γ).det ≠ 0`. Rewrite using `[hd]`. Conclude with `(map_ne_zero _).2 hdet`. Take `⟨y, hy, hy1, hy2, hy3⟩` from `exists_sol (n := N') (k := N) (g := γ.det) (by rwa [mul_comm]) hd0 (by`. Rewrite using `[mul_assoc, ← Matrix.det_mul, mul_sub, h1, mul_one, hd, conj_conj, ← neg_sub γ 1, Matrix.det_neg, Fintype.card_fin])`.

Take `⟨y₁, c, a1, a2, a3⟩` from `present hy`. Take `⟨i0, i1⟩` from `(GlobalTheory.ThetaLatIndex.theta_lattice_index D cc δ hc N N').1 L (sd_of_moves hL)`. Establish `key` using `const hc (klat _ (moves_one D N) hL) u (fun z w => by rw [hu, hu, Hf_mulV, mulV_mulV, h2, adj_one, mul_one, mulV_one]) (fun x => by rw [st3 1 γA 1 γ _ _ (isRat_one D N) hr (moves_one D N) hL x, adj_one, hu]) hd0 (by rw [hsub, GlobalTheory.TwoSidedDet.det_mulV]; simp) (by`. Take `⟨m, hm, hm'⟩` from `st2 (1 - adj D γ)⁻¹ 1`. Establish `e : ∀ x : VC D N N', m • x = m • mulV D (1 - adj D γ)⁻¹ 1 x - u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x)`.

Introduce `x`. Use `LinearMap.congr_fun hsub (m • mulV D (1 - adj D γ)⁻¹ 1 x)` as an intermediate fact. Rewrite `this` using `[map_nsmul (mulV D (1 - adj D γ) 1), mulV_mulV, Matrix.mul_nonsing_inv _ (Ne.isUnit hd0), mul_one, mulV_one]`. Conclude with `this.symm`. Use `⟨m, hm, fun x hx => ⟨_, hm' x hx, ?_, e x⟩⟩` and prove the remaining obligations.

Establish `: u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x) = m • mulV D (1 - adj D γ)⁻¹ 1 x - m • x`. Rewrite using `[e x]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `sub_mem (hm' x hx) (nsmul_mem hx m))`.

Use the proof step `(scal_comm γ 1) i1 i0 (ev_idx i0) a1 a2 a3 hy3 he`. Establish `hp : pull D (tor0 D cc δ) 1 γ e0 = _` using `(pull_eq D cc δ 1 γ e0).trans key`. Take `⟨e, e1, e2, e3⟩` from `exists_idem D`. Rewrite using `[vac e1 e2 e3 hc hN he W (one_eq N) (prin_eq hr hy hy1) (moves_one D N) hL, hp, chi_split e1 e3 _ hy a1 a2 a3, scalar_id (phase_ne hy) (sq_phase hy hy1) ha (sN_sq _ _ _) W.ep_pm.1, hy2, idx_std, sgn_one]`. Use function extensionality and compare the values at `z`.

Simplify using `only [map_one, Units.val_one, one_zpow, one_pow, mul_one, Pi.smul_apply, smul_eq_mul, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem col (hc : Crv D cc δ) (hN : Even (N * N')) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) {γA : GA D N'}
    {γ : Matrix (Fin N') (Fin N') D.host.E} (hr : IsRat D (γA : GL (Fin N') (AE D)) γ) (hdet : (1 - γ).det ≠ 0)
    {a : D.what₂.Tau → ℤ} (ha : ∀ τ, 2 * a τ = W.ep * W.chV.n τ + (N : ℤ)) :
    W.Om 1 γA e0 = fun z => (∏ τ, embT D τ γ.det ^ (-(a τ))) * pull D (tor0 D cc δ) 1 γ e0 z := by
  have h1 : γ * adj D γ = 1 := (mem_ratG_intG D N').2.2.2.1 γA γ hr
  have h2 : adj D γ * γ = 1 := mul_eq_one_comm.1 h1
  obtain ⟨L, hL⟩ := exists_moves γA
  obtain ⟨-, st2, st3⟩ := GlobalTheory.ThetaStab.mulV_theta_lattices D cc δ hc N N'
  let u : VC D N N' ≃ₗ[ℂ] VC D N N' := LinearEquiv.ofLinear (mulV D γ 1) (mulV D (adj D γ) 1)
    (LinearMap.ext fun x => by simp [mulV_mulV, h1, mulV_one])
    (LinearMap.ext fun x => by simp [mulV_mulV, h2, mulV_one])
  have hu : ∀ x, u x = mulV D γ 1 x := fun x => rfl
  have hsub : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D (1 - adj D γ) 1 :=
    LinearMap.ext fun x => by
      rw [mulV_sub_left, mulV_one]; rfl
  have hd : (1 - adj D γ).det = D.host.conj (1 - γ).det := by rw [← adj_one_sub, det_adj]
  have hd0 : (1 - adj D γ).det ≠ 0 := by
    rw [hd]; exact (map_ne_zero _).2 hdet
  obtain ⟨y, hy, hy1, hy2, hy3⟩ := exists_sol (n := N') (k := N) (g := γ.det) (by rwa [mul_comm]) hd0 (by
    rw [mul_assoc, ← Matrix.det_mul, mul_sub, h1, mul_one, hd, conj_conj, ← neg_sub γ 1, Matrix.det_neg,
      Fintype.card_fin])
  obtain ⟨y₁, c, a1, a2, a3⟩ := present hy
  obtain ⟨i0, i1⟩ := (GlobalTheory.ThetaLatIndex.theta_lattice_index D cc δ hc N N').1 L (sd_of_moves hL)
  have key := const hc (klat _ (moves_one D N) hL) u
    (fun z w => by rw [hu, hu, Hf_mulV, mulV_mulV, h2, adj_one, mul_one, mulV_one])
    (fun x => by rw [st3 1 γA 1 γ _ _ (isRat_one D N) hr (moves_one D N) hL x, adj_one, hu]) hd0
    (by rw [hsub, GlobalTheory.TwoSidedDet.det_mulV]; simp)
    (by
      obtain ⟨m, hm, hm'⟩ := st2 (1 - adj D γ)⁻¹ 1
      have e : ∀ x : VC D N N', m • x = m • mulV D (1 - adj D γ)⁻¹ 1 x - u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x) := by
        intro x
        have := LinearMap.congr_fun hsub (m • mulV D (1 - adj D γ)⁻¹ 1 x)
        rw [map_nsmul (mulV D (1 - adj D γ) 1), mulV_mulV, Matrix.mul_nonsing_inv _ (Ne.isUnit hd0), mul_one,
          mulV_one] at this
        exact this.symm
      refine ⟨m, hm, fun x hx => ⟨_, hm' x hx, ?_, e x⟩⟩
      have : u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x) = m • mulV D (1 - adj D γ)⁻¹ 1 x - m • x := by
        rw [e x]; abel
      rw [this]
      exact sub_mem (hm' x hx) (nsmul_mem hx m))
    (scal_comm γ 1) i1 i0 (ev_idx i0) a1 a2 a3 hy3 he
  have hp : pull D (tor0 D cc δ) 1 γ e0 = _ := (pull_eq D cc δ 1 γ e0).trans key
  obtain ⟨e, e1, e2, e3⟩ := exists_idem D
  rw [vac e1 e2 e3 hc hN he W (one_eq N) (prin_eq hr hy hy1) (moves_one D N) hL, hp, chi_split e1 e3 _ hy a1 a2 a3,
    scalar_id (phase_ne hy) (sq_phase hy hy1) ha (sN_sq _ _ _) W.ep_pm.1, hy2, idx_std, sgn_one]
  funext z
  simp only [map_one, Units.val_one, one_zpow, one_pow, mul_one, Pi.smul_apply, smul_eq_mul, zpow_natCast]
  ring

/- English proof (translation)
Establish `hu : γ * adj D γ = 1` using `(mem_ratG_intG D N).2.2.2.1 γA γ hr`. Establish `hu' : adj D γ * γ = 1` using `mul_eq_one_comm.1 hu`. Take `⟨L, hL⟩` from `exists_moves γA`. Take `⟨-, hden, hmov⟩` from `GlobalTheory.ThetaStab.mulV_theta_lattices D cc δ hc N N'`. Set `u : VC D N N' ≃ₗ[ℂ] VC D N N'` to `LinearEquiv.ofLinear (mulV D 1 (adj D γ)) (mulV D 1 γ) (LinearMap.ext fun z => by simp [mulV_mulV, hu, mulV_one]) (LinearMap.ext fun z => by simp [mulV_mulV, hu', mulV_one])`.

Establish `us : ∀ z, u.symm z = mulV D 1 γ z` using `fun _ => rfl`. Establish `hid : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D 1 (1 - γ)` using `LinearMap.ext fun z => by rw [mulV_sub_right, mulV_one]; rfl`. Take `⟨y, hy, hy1, hy2, hy3⟩` from `exists_sol (n := N) (k := N') (g := γ.det) (w := D.host.conj (1 - γ).det) hN ((map_ne_zero _).2 hdet) (by`. Rewrite using `[conj_conj, mul_assoc, ← det_adj, adj_one_sub, ← Matrix.det_mul, Matrix.mul_sub, hu, Matrix.mul_one, ← neg_sub γ 1, Matrix.det_neg, Fintype.card_fin])`. Simplify using `only [embT_conj, Complex.norm_conj] at hy2 hy3`.

Take `⟨y₁, c, a1, a2, a3⟩` from `present hy`. Take `⟨i0, i1⟩` from `(GlobalTheory.ThetaLatIndex.theta_lattice_index D cc δ hc N N').2 L (sd_of_moves hL)`. Establish `key` using `const hc (klat _ hL (moves_one D N')) u (hf_unitary _ (by rw [adj_one, Matrix.one_mul]) (by rw [adj_adj, hu'])) (hmov γA 1 γ 1 L _ hr (isRat_one D N') hL (moves_one D N')) hdet (by rw [hid, GlobalTheory.TwoSidedDet.det_mulV]; simp) (by`. Take `⟨m₁, h₁, g₁⟩` from `hden 1 (1 - γ)⁻¹`. Take `⟨m₂, h₂, g₂⟩` from `hden 1 ((1 - γ)⁻¹ * γ)`.

Establish `e : ∀ x : VC D N N', u.symm ((m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x) = (m₁ * m₂) • mulV D 1 ((1 - γ)⁻¹ * γ) x`. Introduce `x`. Rewrite using `[map_nsmul, us, mulV_mulV, Matrix.one_mul]`. Use `⟨m₁ * m₂, Nat.mul_pos h₁ h₂, fun x hx => ⟨(m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `nsmul_mem (g₁ x hx) _`. Rewrite using `[e, mul_smul]`. Conclude with `nsmul_mem (g₂ x hx) _`. Establish `h1 : (1 - γ)⁻¹ - (1 - γ)⁻¹ * γ = 1`. Use `Matrix.nonsing_inv_mul (1 - γ) (Ne.isUnit hdet)` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_sub, Matrix.mul_one]`. Then use the resulting hypothesis. Rewrite using `[e, ← smul_sub, ← mulV_sub_right, h1, mulV_one])`. Use the proof step `(scal_comm 1 (adj D γ)) i1 i0 (ev_idx i0) a1 a2 a3 hy3 he`. Establish `hp : pull D (tor0 D cc δ) γ 1 e0 = _` using `(show pull D (tor0 D cc δ) γ 1 e0 = fun z => e0 (u.symm z) by rw [pull_eq, adj_one]; rfl).trans key`. Establish `hy4 : ∏ τ, ((‖embT D τ (1 - γ).det‖ : ℂ) / embT D τ (1 - γ).det) ^ N' = ∏ τ, (embT D τ y / (‖embT D τ y‖ : ℂ)) ^ (-(N' : ℤ))`.

Simplify using `only [zpow_neg, zpow_natCast, Finset.prod_inv_distrib]`. Rewrite using `[← hy2, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← inv_pow, inv_div, phase_conj ((map_ne_zero _).2 hdet)]`. Take `⟨e, e1, e2, e3⟩` from `exists_idem D`.

Rewrite using `[vac e1 e2 e3 hc hN he W (prin_eq hr hy hy1) (one_eq N') hL (moves_one D N'), hp, chi_split e1 e3 _ hy a1 a2 a3, scalar_id (k := -(N' : ℤ)) (phase_ne hy) (sq_phase hy hy1) (fun τ => by rw [ha τ]; ring) (sN_sq _ _ _) W.ep_pm.2, hy4, idx_std, sgn_one]`. Use function extensionality and compare the values at `z`. Simplify using `only [map_one, Units.val_one, one_zpow, one_pow, one_mul, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem row (hc : Crv D cc δ) (hN : Even (N * N')) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) {γA : GA D N}
    {γ : Matrix (Fin N) (Fin N) D.host.E} (hr : IsRat D (γA : GL (Fin N) (AE D)) γ) (hdet : (1 - γ).det ≠ 0)
    {a : D.what₂.Tau → ℤ} (ha : ∀ τ, 2 * a τ = W.ep' * W.chV'.n τ - (N' : ℤ)) :
    W.Om γA 1 e0 = fun z => (∏ τ, embT D τ γ.det ^ (-(a τ))) * pull D (tor0 D cc δ) γ 1 e0 z := by
  have hu : γ * adj D γ = 1 := (mem_ratG_intG D N).2.2.2.1 γA γ hr
  have hu' : adj D γ * γ = 1 := mul_eq_one_comm.1 hu
  obtain ⟨L, hL⟩ := exists_moves γA
  obtain ⟨-, hden, hmov⟩ := GlobalTheory.ThetaStab.mulV_theta_lattices D cc δ hc N N'
  let u : VC D N N' ≃ₗ[ℂ] VC D N N' := LinearEquiv.ofLinear (mulV D 1 (adj D γ)) (mulV D 1 γ)
    (LinearMap.ext fun z => by simp [mulV_mulV, hu, mulV_one])
    (LinearMap.ext fun z => by simp [mulV_mulV, hu', mulV_one])
  have us : ∀ z, u.symm z = mulV D 1 γ z := fun _ => rfl
  have hid : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D 1 (1 - γ) :=
    LinearMap.ext fun z => by rw [mulV_sub_right, mulV_one]; rfl
  obtain ⟨y, hy, hy1, hy2, hy3⟩ := exists_sol (n := N) (k := N') (g := γ.det) (w := D.host.conj (1 - γ).det) hN
    ((map_ne_zero _).2 hdet) (by
      rw [conj_conj, mul_assoc, ← det_adj, adj_one_sub, ← Matrix.det_mul, Matrix.mul_sub, hu, Matrix.mul_one,
        ← neg_sub γ 1, Matrix.det_neg, Fintype.card_fin])
  simp only [embT_conj, Complex.norm_conj] at hy2 hy3
  obtain ⟨y₁, c, a1, a2, a3⟩ := present hy
  obtain ⟨i0, i1⟩ := (GlobalTheory.ThetaLatIndex.theta_lattice_index D cc δ hc N N').2 L (sd_of_moves hL)
  have key := const hc (klat _ hL (moves_one D N')) u
    (hf_unitary _ (by rw [adj_one, Matrix.one_mul]) (by rw [adj_adj, hu']))
    (hmov γA 1 γ 1 L _ hr (isRat_one D N') hL (moves_one D N')) hdet
    (by rw [hid, GlobalTheory.TwoSidedDet.det_mulV]; simp)
    (by
      obtain ⟨m₁, h₁, g₁⟩ := hden 1 (1 - γ)⁻¹
      obtain ⟨m₂, h₂, g₂⟩ := hden 1 ((1 - γ)⁻¹ * γ)
      have e : ∀ x : VC D N N', u.symm ((m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x) =
          (m₁ * m₂) • mulV D 1 ((1 - γ)⁻¹ * γ) x := by
        intro x
        rw [map_nsmul, us, mulV_mulV, Matrix.one_mul]
      refine ⟨m₁ * m₂, Nat.mul_pos h₁ h₂, fun x hx => ⟨(m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x, ?_, ?_, ?_⟩⟩
      · rw [mul_comm, mul_smul]; exact nsmul_mem (g₁ x hx) _
      · rw [e, mul_smul]; exact nsmul_mem (g₂ x hx) _
      · have h1 : (1 - γ)⁻¹ - (1 - γ)⁻¹ * γ = 1 := by
          have := Matrix.nonsing_inv_mul (1 - γ) (Ne.isUnit hdet)
          rwa [Matrix.mul_sub, Matrix.mul_one] at this
        rw [e, ← smul_sub, ← mulV_sub_right, h1, mulV_one])
    (scal_comm 1 (adj D γ)) i1 i0 (ev_idx i0) a1 a2 a3 hy3 he
  have hp : pull D (tor0 D cc δ) γ 1 e0 = _ :=
    (show pull D (tor0 D cc δ) γ 1 e0 = fun z => e0 (u.symm z) by rw [pull_eq, adj_one]; rfl).trans key
  have hy4 : ∏ τ, ((‖embT D τ (1 - γ).det‖ : ℂ) / embT D τ (1 - γ).det) ^ N' =
      ∏ τ, (embT D τ y / (‖embT D τ y‖ : ℂ)) ^ (-(N' : ℤ)) := by
    simp only [zpow_neg, zpow_natCast, Finset.prod_inv_distrib]
    rw [← hy2, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← inv_pow, inv_div, phase_conj ((map_ne_zero _).2 hdet)]
  obtain ⟨e, e1, e2, e3⟩ := exists_idem D
  rw [vac e1 e2 e3 hc hN he W (prin_eq hr hy hy1) (one_eq N') hL (moves_one D N'), hp, chi_split e1 e3 _ hy a1 a2 a3,
    scalar_id (k := -(N' : ℤ)) (phase_ne hy) (sq_phase hy hy1) (fun τ => by rw [ha τ]; ring) (sN_sq _ _ _) W.ep_pm.2,
    hy4, idx_std, sgn_one]
  funext z
  simp only [map_one, Units.val_one, one_zpow, one_pow, one_mul, Pi.smul_apply, smul_eq_mul]
  ring

def Ex {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N')
    (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (c : ℂ) : Prop :=
  ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om g g' F = fun z => c * pull D (tor0 D cc δ) γ γ' F z

/- English proof (translation)
Introduce `F hF`. Rewrite using `[W.mul _ _ _ _ F hF, h₁ _ (W.maps _ _ F hF), h₂ F hF]`. Use function extensionality and compare the values at `z`. Simplify using `only [pull_eq, mulV_mulV, adj_mul, mul_assoc]`.
-/
theorem Ex.mul {e0 : VC D N N' → ℂ} {W : WeilO D cc δ N N' e0} {g₁ g₂ : GA D N} {g₁' g₂' : GA D N'}
    {γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E} {γ₁' γ₂' : Matrix (Fin N') (Fin N') D.host.E} {c₁ c₂ : ℂ}
    (h₁ : Ex W g₁ g₁' γ₁ γ₁' c₁) (h₂ : Ex W g₂ g₂' γ₂ γ₂' c₂) :
    Ex W (g₁ * g₂) (g₁' * g₂') (γ₁ * γ₂) (γ₁' * γ₂') (c₁ * c₂) := by
  intro F hF
  rw [W.mul _ _ _ _ F hF, h₁ _ (W.maps _ _ F hF), h₂ F hF]
  funext z
  simp only [pull_eq, mulV_mulV, adj_mul, mul_assoc]

/- English proof (translation)
Take `⟨z, hz, hz1, hd⟩` from `GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero D n γ`. Establish `hu : γ * adj D γ = 1` using `(mem_ratG_intG D n).2.2.2.1 g γ hr`. Establish `hs : ∀ (t : D.host.E) (M : Matrix (Fin n) (Fin n) D.host.E), adj D (t • M) = D.host.conj t • adj D M`. Introduce `t M`. Use extensionality with `i j`.

Simplify using `[adj]`. Take `⟨g₁, h₁⟩` from `PtsMem.exists_isRat D (z • γ) (by`. Express the relevant statement in the definitionally equal form `_ * adj D _ = _`. Rewrite using `[hs, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz, one_smul, hu])`. Take `⟨g₂, h₂⟩` from `PtsMem.exists_isRat D (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)) (by`.

Express the relevant statement in the definitionally equal form `_ * adj D _ = _`. Rewrite using `[hs, adj_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← map_mul, hz, map_one, one_smul, mul_one])`. Establish `e : γ = z • γ * D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz, one_smul, mul_one]`. Use `⟨g₁, g₂, _, _, h₁, h₂, hd, ?_, ?_, e⟩` and prove the remaining obligations.

Establish `: (1 : Matrix (Fin n) (Fin n) D.host.E) - D.host.conj z • 1 = (1 - D.host.conj z) • 1`. Rewrite using `[sub_smul, one_smul]`. Rewrite using `[this, Matrix.det_smul, Matrix.det_one, mul_one]`. Use `pow_ne_zero _ (sub_ne_zero.2 fun h => hz1 ?_)` and prove the remaining obligations. Rewrite `hz` using `[← h, mul_one]`. Then use the resulting hypothesis.

Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations. Unfold `IsRat at hr h₁ h₂`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, h₁, h₂, ← Matrix.map_mul, ← e, hr]`.
-/
theorem factor {n : ℕ} {g : GA D n} {γ : Matrix (Fin n) (Fin n) D.host.E} (hr : IsRat D (g : GL (Fin n) (AE D)) γ) :
    ∃ (g₁ g₂ : GA D n) (γ₁ γ₂ : Matrix (Fin n) (Fin n) D.host.E), IsRat D (g₁ : GL (Fin n) (AE D)) γ₁ ∧
      IsRat D (g₂ : GL (Fin n) (AE D)) γ₂ ∧ (1 - γ₁).det ≠ 0 ∧ (1 - γ₂).det ≠ 0 ∧ g = g₁ * g₂ ∧ γ = γ₁ * γ₂ := by
  obtain ⟨z, hz, hz1, hd⟩ := GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero D n γ
  have hu : γ * adj D γ = 1 := (mem_ratG_intG D n).2.2.2.1 g γ hr
  have hs : ∀ (t : D.host.E) (M : Matrix (Fin n) (Fin n) D.host.E), adj D (t • M) = D.host.conj t • adj D M := by
    intro t M
    ext i j
    simp [adj]
  obtain ⟨g₁, h₁⟩ := PtsMem.exists_isRat D (z • γ) (by
    change _ * adj D _ = _
    rw [hs, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz, one_smul, hu])
  obtain ⟨g₂, h₂⟩ := PtsMem.exists_isRat D (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)) (by
    change _ * adj D _ = _
    rw [hs, adj_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← map_mul, hz, map_one, one_smul, mul_one])
  have e : γ = z • γ * D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz, one_smul, mul_one]
  refine ⟨g₁, g₂, _, _, h₁, h₂, hd, ?_, ?_, e⟩
  · have : (1 : Matrix (Fin n) (Fin n) D.host.E) - D.host.conj z • 1 = (1 - D.host.conj z) • 1 := by
      rw [sub_smul, one_smul]
    rw [this, Matrix.det_smul, Matrix.det_one, mul_one]
    refine pow_ne_zero _ (sub_ne_zero.2 fun h => hz1 ?_)
    rwa [← h, mul_one] at hz
  · refine Subtype.ext (Units.ext ?_)
    unfold IsRat at hr h₁ h₂
    rw [Subgroup.coe_mul, Units.val_mul, h₁, h₂, ← Matrix.map_mul, ← e, hr]

/- English proof (translation)
Introduce `W g g' γ γ' a a' hr hr' ha' ha`. Establish `ext` using `GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum D cc δ hc N N' e0 he (GlobalTheory.ThetaSpan.theta_span D cc δ hc N N' e0 he W.nz) W`. Take `⟨g₁, g₂, γ₁, γ₂, r1, r2, d1, d2, rfl, rfl⟩` from `factor hr`. Take `⟨g₁', g₂', γ₁', γ₂', r1', r2', d1', d2', rfl, rfl⟩` from `factor hr'`. Establish `x1 : Ex W _ _ _ _ _` using `ext _ _ _ _ _ r1 (isRat_one D N') (row hc hN he W r1 d1 ha)`.

Establish `x2 : Ex W _ _ _ _ _` using `ext _ _ _ _ _ r2 (isRat_one D N') (row hc hN he W r2 d2 ha)`. Establish `x3 : Ex W _ _ _ _ _` using `ext _ _ _ _ _ (isRat_one D N) r1' (col hc hN he W r1' d1' ha')`. Establish `x4 : Ex W _ _ _ _ _` using `ext _ _ _ _ _ (isRat_one D N) r2' (col hc hN he W r2' d2' ha')`. Establish `x` using `(x1.mul x2).mul (x3.mul x4)`. Simplify using `only [mul_one, one_mul] at x`.

Introduce `F hF`. Rewrite using `[x F hF]`. Simplify using `only [Matrix.det_mul, map_mul, mul_zpow, Finset.prod_mul_distrib]`.
-/
theorem oddEq_of_mem (hc : Crv D cc δ) (hN : Even (N * N')) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) : oddEq D cc δ N N' e0 := by
  intro W g g' γ γ' a a' hr hr' ha' ha
  have ext := GlobalTheory.NormSum.RatExtend.om_eq_pull_of_vacuum D cc δ hc N N' e0 he
    (GlobalTheory.ThetaSpan.theta_span D cc δ hc N N' e0 he W.nz) W
  obtain ⟨g₁, g₂, γ₁, γ₂, r1, r2, d1, d2, rfl, rfl⟩ := factor hr
  obtain ⟨g₁', g₂', γ₁', γ₂', r1', r2', d1', d2', rfl, rfl⟩ := factor hr'
  have x1 : Ex W _ _ _ _ _ := ext _ _ _ _ _ r1 (isRat_one D N') (row hc hN he W r1 d1 ha)
  have x2 : Ex W _ _ _ _ _ := ext _ _ _ _ _ r2 (isRat_one D N') (row hc hN he W r2 d2 ha)
  have x3 : Ex W _ _ _ _ _ := ext _ _ _ _ _ (isRat_one D N) r1' (col hc hN he W r1' d1' ha')
  have x4 : Ex W _ _ _ _ _ := ext _ _ _ _ _ (isRat_one D N) r2' (col hc hN he W r2' d2' ha')
  have x := (x1.mul x2).mul (x3.mul x4)
  simp only [mul_one, one_mul] at x
  intro F hF
  rw [x F hF]
  simp only [Matrix.det_mul, map_mul, mul_zpow, Finset.prod_mul_distrib]

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ hc _ hN hv` and use `oddEq_of_mem hc hN hv.1`.
-/
theorem exact_equivariance : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ),
    Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (N * N') → oddE0 D cc δ t0 N N' e0 → oddEq D cc δ N N' e0 :=
  fun _ _ _ _ _ _ _ hc _ hN hv => oddEq_of_mem hc hN hv.1

/- English proof (translation)
Introduce `D cc δ hc N N' hN e0 he W`. Establish `h : ∀ (ε n : ℤ) (k : ℕ), (ε = 1 ∨ ε = -1) → Even (n - k) → (∃ a, 2 * a = ε * n + k) ∧ ∃ a, 2 * a = ε * n - k`. Introduce and unpack `ε n k (rfl | rfl) ⟨j, hj⟩`. Conclude with `⟨⟨j + k, by omega⟩, ⟨j, by omega⟩⟩`. Conclude with `⟨⟨-j, by omega⟩, ⟨-j - k, by omega⟩⟩`.

Use `choose a' ha' using fun τ => (h _ _ N W.ep_pm.1 (W.chV.par τ)).1`. Use `choose a ha using fun τ => (h _ _ N' W.ep_pm.2 (W.chV'.par τ)).2`. Conclude with `⟨a, a', fun g g' γ γ' hr hr' => oddEq_of_mem hc hN he W g g' γ γ' a a' hr hr' ha' ha⟩`.
-/
theorem poisson : ∀ D : D7, admissible_poisson D := by
  intro D cc δ hc N N' hN e0 he W
  have h : ∀ (ε n : ℤ) (k : ℕ), (ε = 1 ∨ ε = -1) → Even (n - k) →
      (∃ a, 2 * a = ε * n + k) ∧ ∃ a, 2 * a = ε * n - k := by
    rintro ε n k (rfl | rfl) ⟨j, hj⟩
    · exact ⟨⟨j + k, by omega⟩, ⟨j, by omega⟩⟩
    · exact ⟨⟨-j, by omega⟩, ⟨-j - k, by omega⟩⟩
  choose a' ha' using fun τ => (h _ _ N W.ep_pm.1 (W.chV.par τ)).1
  choose a ha using fun τ => (h _ _ N' W.ep_pm.2 (W.chV'.par τ)).2
  exact ⟨a, a', fun g g' γ γ' hr hr' => oddEq_of_mem hc hN he W g g' γ γ' a a' hr hr' ha' ha⟩

end GlobalTheory.OddRank
