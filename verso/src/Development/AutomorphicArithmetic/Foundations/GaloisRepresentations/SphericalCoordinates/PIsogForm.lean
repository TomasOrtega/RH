import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntAfIntCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromP

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Simplify using `[hermForm, Matrix.mulVec_add, dotProduct_add]`.
-/
private theorem herm_add_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (x a b : Fin g → ℂ) :
    hermForm M x (a + b) = hermForm M x a + hermForm M x b := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `[hermForm, add_dotProduct]`.
-/
private theorem herm_add_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (a b y : Fin g → ℂ) :
    hermForm M (a + b) y = hermForm M a y + hermForm M b y := by
  simp [hermForm, add_dotProduct]

/- English proof (translation)
Simplify using `[hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
private theorem herm_smul_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (x a : Fin g → ℂ) :
    hermForm M x (c • a) = star c * hermForm M x a := by
  simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [hermForm, smul_dotProduct, smul_eq_mul]`.
-/
private theorem herm_smul_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (a y : Fin g → ℂ) :
    hermForm M (c • a) y = c * hermForm M a y := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Simplify using `[hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]`.
-/
private theorem herm_sub_smul {g : ℕ} (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (x y : Fin g → ℂ) :
    hermForm (H₁ - t • H₂) x y = hermForm H₁ x y - t * hermForm H₂ x y := by
  simp [hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]

/- English proof (translation)
Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
private theorem real_smul_eq {g : ℕ} (c : ℝ) (a : Fin g → ℂ) : c • a = (c : ℂ) • a := by
  ext i; simp

/- English proof (translation)
Establish `key : ∀ w ∈ s, ∀ z, (hermForm M z w).im = 0`. Introduce `w hw z`. Establish `hz : z ∈ Submodule.span ℝ s` using `by rw [hs]; trivial`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx w hw`.

Consider the case `zero => simp [hermForm]`. Consider the case `add a b _ _ ha hb => rw [herm_add_left]`. Simplify using `[ha, hb]`. Consider the case `smul c a _ ha => rw [real_smul_eq, herm_smul_left]`. Simplify using `[ha]`.

Establish `hw : w ∈ Submodule.span ℝ s` using `by rw [hs]; trivial`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem y hy => exact key y hy z`. Consider the case `zero => simp [hermForm]`. Consider the case `add a b _ _ ha hb => rw [herm_add_right]`.

Simplify using `[ha, hb]`. Consider the case `smul c a _ ha => rw [real_smul_eq, herm_smul_right]`. Simplify using `[ha]`.
-/
private theorem herm_im_zero {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ x ∈ s, ∀ y ∈ s, (hermForm M x y).im = 0) (z w : Fin g → ℂ) :
    (hermForm M z w).im = 0 := by
  have key : ∀ w ∈ s, ∀ z, (hermForm M z w).im = 0 := by
    intro w hw z
    have hz : z ∈ Submodule.span ℝ s := by rw [hs]; trivial
    induction hz using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [hermForm]
    | add a b _ _ ha hb => rw [herm_add_left]; simp [ha, hb]
    | smul c a _ ha => rw [real_smul_eq, herm_smul_left]; simp [ha]
  have hw : w ∈ Submodule.span ℝ s := by rw [hs]; trivial
  induction hw using Submodule.span_induction with
  | mem y hy => exact key y hy z
  | zero => simp [hermForm]
  | add a b _ _ ha hb => rw [herm_add_right]; simp [ha, hb]
  | smul c a _ ha => rw [real_smul_eq, herm_smul_right]; simp [ha]

/- English proof (translation)
Use `⟨Bf x e' + Bf e y + n * Bf e e', ?_⟩` and prove the remaining obligations. Simplify using `[map_add, map_nsmul, LinearMap.add_apply, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem bil_dvd {M : Type} [AddCommGroup M] (Bf : LinearMap.BilinForm ℤ M) (n : ℕ) (x y e e' : M) :
    (n : ℤ) ∣ Bf (x + n • e) (y + n • e') - Bf x y := by
  refine ⟨Bf x e' + Bf e y + n * Bf e e', ?_⟩
  simp [map_add, map_nsmul, LinearMap.add_apply, nsmul_eq_mul]
  ring

/- English proof (translation)
Establish `h1` using `MultScale.EFA_actG L h (inAf D a) (inAf D a')`. Rewrite `h1` using `[e, e', MultScale.EFA_inAf]`. Simplify using `only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, MultScale.EFA_inAf] at h1`. Establish `hn : IsIntAf (n : AfP p)`. Use `MultScale.isIntAf_intCast (p := p) (n : ℤ)` as an intermediate fact.

Simplify using `using this`. Use `⟨-(MultScale.EFA D (inAf D b) w' + MultScale.EFA D w (inAf D b') + (n : AfP p) * MultScale.EFA D w w'), ?_, ?_⟩` and prove the remaining obligations. Conclude with `MultScale.isIntAf_neg (MultScale.isIntAf_add (MultScale.isIntAf_add (MultScale.isIntAf_EFA D (MultScale.inAf_mem D b) hw') (MultScale.isIntAf_EFA D hw (MultScale.inAf_mem D b'))) (MultScale.isIntAf_mul hn (MultScale.isIntAf_EFA D hw hw')))`. Take the linear combination `h1`.
-/
private theorem form_step {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf) (n : ℕ)
    {a a' b b' : D.La} {w w' : AfP p ⊗[ℚ] VQ D} (hw : w ∈ LaHat D) (hw' : w' ∈ LaHat D)
    (e : L.actG h (inAf D a) = inAf D b + n • w) (e' : L.actG h (inAf D a') = inAf D b' + n • w') :
    ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
      ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
  have h1 := MultScale.EFA_actG L h (inAf D a) (inAf D a')
  rw [e, e', MultScale.EFA_inAf] at h1
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul,
    MultScale.EFA_inAf] at h1
  have hn : IsIntAf (n : AfP p) := by
    have := MultScale.isIntAf_intCast (p := p) (n : ℤ)
    simpa using this
  refine ⟨-(MultScale.EFA D (inAf D b) w' + MultScale.EFA D w (inAf D b') +
    (n : AfP p) * MultScale.EFA D w w'), ?_, ?_⟩
  · exact MultScale.isIntAf_neg (MultScale.isIntAf_add (MultScale.isIntAf_add
      (MultScale.isIntAf_EFA D (MultScale.inAf_mem D b) hw')
      (MultScale.isIntAf_EFA D hw (MultScale.inAf_mem D b')))
      (MultScale.isIntAf_mul hn (MultScale.isIntAf_EFA D hw hw')))
  · linear_combination h1

/- English proof (translation)
Unfold `IsWit at hf hf''`. Establish `hX : ∀ x x' : D'.La, ∃ b b' a a' : D.La, (D''.EF (inc x) (inc x') ≡ nu'' n * (2 * D.EF b b') [ZMOD n]) ∧ (D'.EF x x' ≡ nu n * (2 * D.EF a a') [ZMOD n]) ∧ ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) = ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : …`. Introduce `x x'`. Take `⟨a, e, rfl⟩` from `(hf.2 n hn hc).2.2.2.1 x`. Take `⟨a', e', rfl⟩` from `(hf.2 n hn hc).2.2.2.1 x'`.

Take `⟨b, E, hb⟩` from `(hf''.2 n hn hc).2.2.2.1 (inc (f n a))`. Take `⟨b', E', hb'⟩` from `(hf''.2 n hn hc).2.2.2.1 (inc (f n a'))`. Take `⟨w, hw, hwe⟩` from `(hyp n hn hc a b).1 ⟨E, hb⟩`. Take `⟨w', hw', hwe'⟩` from `(hyp n hn hc a' b').1 ⟨E', hb'⟩`. Use `⟨b, b', a, a', ?_, ?_, form_step L h n hw hw' hwe hwe'⟩` and prove the remaining obligations.

Establish `h1 : inc (f n a + n • e) = f'' n b + n • (E + inc e)`. Rewrite using `[map_add, map_nsmul, hb, smul_add, add_assoc]`. Establish `h2 : inc (f n a' + n • e') = f'' n b' + n • (E' + inc e')`. Rewrite using `[map_add, map_nsmul, hb', smul_add, add_assoc]`. Rewrite using `[h1, h2]`.

Conclude with `(Int.modEq_iff_dvd.mpr (bil_dvd D''.EF n _ _ _ _)).symm.trans (Int.modEq_iff_dvd.mpr ((hf''.2 n hn hc).2.2.2.2 b b')).symm`. Conclude with `(Int.modEq_iff_dvd.mpr (bil_dvd D'.EF n _ _ _ _)).symm.trans (Int.modEq_iff_dvd.mpr ((hf.2 n hn hc).2.2.2.2 a a')).symm`. Take `⟨b1, b2, a1, a2, hX1, hY1, i12, hi12, he12⟩` from `hX u₁ u₂`. Take `⟨b3, b4, a3, a4, hX3, hY3, i34, hi34, he34⟩` from `hX u₃ u₄`. Establish `hZ : (n : ℤ) ∣ D.EF b1 b2 * D.EF a3 a4 - D.EF b3 b4 * D.EF a1 a2`.

Apply `IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hc _ (i12 * ((D.EF a3 a4 : ℤ) : AfP p) - i34 * ((D.EF a1 a2 : ℤ) : AfP p))` to reduce the goal to its premises. Rewrite using `[sub_eq_add_neg]`. Conclude with `MultScale.isIntAf_add (MultScale.isIntAf_mul hi12 (MultScale.isIntAf_intCast _)) (MultScale.isIntAf_neg (MultScale.isIntAf_mul hi34 (MultScale.isIntAf_intCast _)))`. Rewrite using `[map_intCast]`. Use `push_cast`.

Take the linear combination `((D.EF a3 a4 : ℤ) : AfP p) * he12 - ((D.EF a1 a2 : ℤ) : AfP p) * he34`. Establish `h0 : nu'' n * (2 * D.EF b1 b2) * (nu n * (2 * D.EF a3 a4)) - nu'' n * (2 * D.EF b3 b4) * (nu n * (2 * D.EF a1 a2)) ≡ 0 [ZMOD n]`. Apply `Int.modEq_zero_iff_dvd.mpr` to reduce the goal to its premises. Take `⟨k, hk⟩` from `hZ`. Conclude with `⟨4 * nu'' n * nu n * k, by linear_combination (4 * nu'' n * nu n) * hk⟩`.

Conclude with `Int.modEq_zero_iff_dvd.mp (((hX1.mul hY3).sub (hX3.mul hY1)).trans h0)`.
-/
private theorem cross_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) :
    (n : ℤ) ∣ D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  unfold IsWit at hf hf''
  have hX : ∀ x x' : D'.La, ∃ b b' a a' : D.La,
      (D''.EF (inc x) (inc x') ≡ nu'' n * (2 * D.EF b b') [ZMOD n]) ∧
      (D'.EF x x' ≡ nu n * (2 * D.EF a a') [ZMOD n]) ∧
      ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
        ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
    intro x x'
    obtain ⟨a, e, rfl⟩ := (hf.2 n hn hc).2.2.2.1 x
    obtain ⟨a', e', rfl⟩ := (hf.2 n hn hc).2.2.2.1 x'
    obtain ⟨b, E, hb⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a))
    obtain ⟨b', E', hb'⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a'))
    obtain ⟨w, hw, hwe⟩ := (hyp n hn hc a b).1 ⟨E, hb⟩
    obtain ⟨w', hw', hwe'⟩ := (hyp n hn hc a' b').1 ⟨E', hb'⟩
    refine ⟨b, b', a, a', ?_, ?_, form_step L h n hw hw' hwe hwe'⟩
    · have h1 : inc (f n a + n • e) = f'' n b + n • (E + inc e) := by
        rw [map_add, map_nsmul, hb, smul_add, add_assoc]
      have h2 : inc (f n a' + n • e') = f'' n b' + n • (E' + inc e') := by
        rw [map_add, map_nsmul, hb', smul_add, add_assoc]
      rw [h1, h2]
      exact (Int.modEq_iff_dvd.mpr (bil_dvd D''.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf''.2 n hn hc).2.2.2.2 b b')).symm
    · exact (Int.modEq_iff_dvd.mpr (bil_dvd D'.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf.2 n hn hc).2.2.2.2 a a')).symm
  obtain ⟨b1, b2, a1, a2, hX1, hY1, i12, hi12, he12⟩ := hX u₁ u₂
  obtain ⟨b3, b4, a3, a4, hX3, hY3, i34, hi34, he34⟩ := hX u₃ u₄
  have hZ : (n : ℤ) ∣ D.EF b1 b2 * D.EF a3 a4 - D.EF b3 b4 * D.EF a1 a2 := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hc _
      (i12 * ((D.EF a3 a4 : ℤ) : AfP p) - i34 * ((D.EF a1 a2 : ℤ) : AfP p))
    · rw [sub_eq_add_neg]
      exact MultScale.isIntAf_add (MultScale.isIntAf_mul hi12 (MultScale.isIntAf_intCast _))
        (MultScale.isIntAf_neg (MultScale.isIntAf_mul hi34 (MultScale.isIntAf_intCast _)))
    · rw [map_intCast]
      push_cast
      linear_combination ((D.EF a3 a4 : ℤ) : AfP p) * he12 - ((D.EF a1 a2 : ℤ) : AfP p) * he34
  have h0 : nu'' n * (2 * D.EF b1 b2) * (nu n * (2 * D.EF a3 a4)) -
      nu'' n * (2 * D.EF b3 b4) * (nu n * (2 * D.EF a1 a2)) ≡ 0 [ZMOD n] := by
    apply Int.modEq_zero_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hZ
    exact ⟨4 * nu'' n * nu n * k, by linear_combination (4 * nu'' n * nu n) * hk⟩
  exact Int.modEq_zero_iff_dvd.mp (((hX1.mul hY3).sub (hX3.mul hY1)).trans h0)

/- English proof (translation)
Use `set d := D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ with hd`. It suffices to establish `hz : d = 0 by exact sub_eq_zero.mp hz`. Establish `hn : 0 < p * d.natAbs + 1` using `Nat.succ_pos _`. Establish `hc : (p * d.natAbs + 1).Coprime p` using `((Nat.coprime_mul_left_add_right p 1 d.natAbs).mpr (Nat.coprime_one_right p)).symm`. Establish `hdvd` using `cross_dvd L h inc hf hf'' hyp u₁ u₂ u₃ u₄ _ hn hc`.

Apply `Int.eq_zero_of_abs_lt_dvd hdvd` to reduce the goal to its premises. Establish `hp : (2 : ℤ) ≤ p` using `by exact_mod_cast (Fact.out : p.Prime).two_le`. Rewrite using `[Int.abs_eq_natAbs]`. Use `push_cast`. Use polynomial arithmetic with `[Int.natCast_nonneg d.natAbs]`.
-/
private theorem cross {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) :
    D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ = D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  set d := D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ with hd
  suffices hz : d = 0 by exact sub_eq_zero.mp hz
  have hn : 0 < p * d.natAbs + 1 := Nat.succ_pos _
  have hc : (p * d.natAbs + 1).Coprime p :=
    ((Nat.coprime_mul_left_add_right p 1 d.natAbs).mpr (Nat.coprime_one_right p)).symm
  have hdvd := cross_dvd L h inc hf hf'' hyp u₁ u₂ u₃ u₄ _ hn hc
  apply Int.eq_zero_of_abs_lt_dvd hdvd
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  rw [Int.abs_eq_natAbs]
  push_cast
  nlinarith [Int.natCast_nonneg d.natAbs]

/- English proof (translation)
Introduce `_ p _ D G L h ρ D' D'' P P'' inc hP hP'' hPinc f nu f'' nu'' hf hf'' hyp`. Distinguish the cases in `hall : ∀ u u' : D'.La, D'.EF u u' = 0`. Use `⟨1, one_pos, fun u u' => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ x : D'.La, x = 0` using `fun x => D'.nondeg x (hall x)`. Rewrite using `[h0 u]`.

Simplify using the standard rewrite rules. Use `push_neg at hall`. Take `⟨u₃, u₄, hne⟩` from `hall`. Establish `hrel : ∀ u u' : D'.La, ((D''.EF (inc u) (inc u') : ℤ) : ℚ) = ((D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ)) * (D'.EF u u' : ℚ)`. Introduce `u u'`.

Establish `hcq : ((D'.EF u₃ u₄ : ℤ) : ℚ) ≠ 0` using `by exact_mod_cast hne`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff hcq]`. Conclude with `cross L h inc hf hf'' hyp u u' u₃ u₄` after adjusting the coercions. Use `⟨(D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ), ?_, hrel⟩` and prove the remaining obligations. Unfold `PELU.IsPeriod at hP hP''`.

Take `⟨-, hPinj, -, hspan, H1, -, hpos1, him1⟩` from `hP`. Take `⟨-, -, -, -, H2, -, hpos2, him2⟩` from `hP''`. Use `set q : ℚ := (D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ) with hq`. Establish `hzero : ∀ z w, (hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w).im = 0`. Apply `herm_im_zero _ (Set.range P) hspan` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨y, rfl⟩`. Rewrite using `[herm_sub_smul, Complex.sub_im, Complex.im_ofReal_mul, him1, ← hPinc x, ← hPinc y, him2]`. Establish `hr : ((D''.EF (inc x) (inc y) : ℤ) : ℝ) = (q : ℝ) * ((D'.EF x y : ℤ) : ℝ)`. Use `congrArg (fun t : ℚ => (t : ℝ)) (hrel x y)` as an intermediate fact. Simplify `this` using `[hq]`.

Rewrite using `[hr]`. Expand and normalize the polynomial expressions, which then agree. Establish `hM : ∀ z w, hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w = 0`. Introduce `z w`. Apply `Complex.ext` to reduce the goal to its premises.

Use `hzero (Complex.I • z) w` as an intermediate fact. Rewrite `this` using `[herm_smul_left]`. Simplify using `using this`. Simplify using `using hzero z w`. Establish `hu3 : P u₃ ≠ 0`.

Introduce `h0`. Establish `hu : u₃ = 0` using `hPinj (by rw [h0, map_zero])`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hu]`. Simplify using the standard rewrite rules.

Establish `e` using `hM (P u₃) (P u₃)`. Rewrite `e` using `[herm_sub_smul, sub_eq_zero]`. Establish `p1` using `hpos1 _ hu3`. Establish `p2` using `hpos2 _ hu3`. Rewrite `p2` using `[e, Complex.re_ofReal_mul]`.

Establish `hpos : (0 : ℝ) < (q : ℝ)` using `lt_of_not_ge (fun hle => by nlinarith)`. Conclude with `Rat.cast_pos.mp hpos`.
-/
theorem UpperTheory.Gal.W2.isogForm_of :
    UpperTheory.Gal.W2.RdForm → UpperTheory.Gal.W2.IsogForm := by
  intro _ p _ D G L h ρ D' D'' P P'' inc hP hP'' hPinc f nu f'' nu'' hf hf'' hyp
  by_cases hall : ∀ u u' : D'.La, D'.EF u u' = 0
  · refine ⟨1, one_pos, fun u u' => ?_⟩
    have h0 : ∀ x : D'.La, x = 0 := fun x => D'.nondeg x (hall x)
    rw [h0 u]
    simp
  push_neg at hall
  obtain ⟨u₃, u₄, hne⟩ := hall
  have hrel : ∀ u u' : D'.La, ((D''.EF (inc u) (inc u') : ℤ) : ℚ) =
      ((D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ)) * (D'.EF u u' : ℚ) := by
    intro u u'
    have hcq : ((D'.EF u₃ u₄ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hne
    rw [div_mul_eq_mul_div, eq_div_iff hcq]
    exact_mod_cast cross L h inc hf hf'' hyp u u' u₃ u₄
  refine ⟨(D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ), ?_, hrel⟩
  unfold PELU.IsPeriod at hP hP''
  obtain ⟨-, hPinj, -, hspan, H1, -, hpos1, him1⟩ := hP
  obtain ⟨-, -, -, -, H2, -, hpos2, him2⟩ := hP''
  set q : ℚ := (D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ) with hq
  have hzero : ∀ z w, (hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w).im = 0 := by
    apply herm_im_zero _ (Set.range P) hspan
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [herm_sub_smul, Complex.sub_im, Complex.im_ofReal_mul, him1, ← hPinc x, ← hPinc y, him2]
    have hr : ((D''.EF (inc x) (inc y) : ℤ) : ℝ) = (q : ℝ) * ((D'.EF x y : ℤ) : ℝ) := by
      have := congrArg (fun t : ℚ => (t : ℝ)) (hrel x y)
      simpa [hq] using this
    rw [hr]
    ring
  have hM : ∀ z w, hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w = 0 := by
    intro z w
    apply Complex.ext
    · have := hzero (Complex.I • z) w
      rw [herm_smul_left] at this
      simpa using this
    · simpa using hzero z w
  have hu3 : P u₃ ≠ 0 := by
    intro h0
    have hu : u₃ = 0 := hPinj (by rw [h0, map_zero])
    apply hne
    rw [hu]
    simp
  have e := hM (P u₃) (P u₃)
  rw [herm_sub_smul, sub_eq_zero] at e
  have p1 := hpos1 _ hu3
  have p2 := hpos2 _ hu3
  rw [e, Complex.re_ofReal_mul] at p2
  have hpos : (0 : ℝ) < (q : ℝ) := lt_of_not_ge (fun hle => by nlinarith)
  exact Rat.cast_pos.mp hpos
