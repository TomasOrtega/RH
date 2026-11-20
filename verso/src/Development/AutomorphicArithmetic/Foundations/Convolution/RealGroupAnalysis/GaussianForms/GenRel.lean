import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GrpRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBigCellGenericRelations

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private def upperP (F : Type) [Field F] [NumberField F] : Subgroup (G1 F) where
  carrier := {g | g 1 0 = 0}
  mul_mem' := by
    intro g h hg hh
    have hg' : g.1 1 0 = 0 := hg
    have hh' : h.1 1 0 = 0 := hh
    show (g * h).1 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg', hh']
    simp
  one_mem' := by
    show (1 : G1 _).1 1 0 = 0
    simp
  inv_mem' := by
    intro g hg
    have hg' : g.1 1 0 = 0 := hg
    show (g⁻¹).1 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hg']

/- English proof (translation)
Rewrite using `[hR.N_add, hR.M_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem bor {F : Type} [Field F] [NumberField F] {H : Type} [Monoid H]
    {N : A F → H} {M : (A F)ˣ → H} {W : H} (hR : Rel N M W) (b b' : A F) (a a' : (A F)ˣ) :
    (N b * M a) * (N b' * M a') = N (b + (a : A F) ^ 2 * b') * M (a * a') := by
  rw [hR.N_add, hR.M_mul]
  calc N b * M a * (N b' * M a') = N b * (M a * N b') * M a' := by simp only [mul_assoc]
    _ = _ := by rw [hR.MN]; simp only [mul_assoc]

/- English proof (translation)
Establish `h1 : M a * W = W * M a⁻¹`. Use `hR.WM a⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Conclude with `this.symm`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem gen_rel {F : Type} [Field F] [NumberField F] {H : Type} [Monoid H]
    {N : A F → H} {M : (A F)ˣ → H} {W : H} (hR : Rel N M W) (hG : Gauss N M W) (t a : (A F)ˣ) :
    W * (N (t : A F) * M a) * W =
      (N (-((t⁻¹ : (A F)ˣ) : A F)) * M (-t⁻¹)) * W * (N (-((t⁻¹ : (A F)ˣ) : A F)) * M a⁻¹) := by
  have h1 : M a * W = W * M a⁻¹ := by
    have := hR.WM a⁻¹
    rw [inv_inv] at this
    exact this.symm
  calc W * (N (t : A F) * M a) * W = W * N (t : A F) * (M a * W) := by simp only [mul_assoc]
    _ = W * N (t : A F) * W * M a⁻¹ := by rw [h1]; simp only [mul_assoc]
    _ = _ := by rw [hG t]; simp only [mul_assoc]

/- English proof (translation)
Establish `h' : !![(0 : A F), 1; -1, 0] * (!![1, b; 0, 1] * !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)]) = !![1, c; 0, 1] * !![(d : A F), 0; 0, ((d⁻¹ : (A F)ˣ) : A F)] * !![(0 : A F), 1; -1, 0]` using `congrArg Subtype.val h`. Establish `e11` using `congrFun (congrFun h' 1) 1`. Establish `e01` using `congrFun (congrFun h' 0) 1`. Establish `e00` using `congrFun (congrFun h' 0) 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two] at e11 e01 e00`.

Conclude with `⟨e11, e00, (Units.ext e01).symm⟩`.
-/
private theorem w_small {F : Type} [Field F] [NumberField F] {b c : A F} {a d : (A F)ˣ}
    (h : wW F * (nU b * mD a) = nU c * mD d * wW F) : b = 0 ∧ c = 0 ∧ d = a⁻¹ := by
  have h' : !![(0 : A F), 1; -1, 0] * (!![1, b; 0, 1] * !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)]) =
      !![1, c; 0, 1] * !![(d : A F), 0; 0, ((d⁻¹ : (A F)ˣ) : A F)] * !![(0 : A F), 1; -1, 0] :=
    congrArg Subtype.val h
  have e11 := congrFun (congrFun h' 1) 1
  have e01 := congrFun (congrFun h' 0) 1
  have e00 := congrFun (congrFun h' 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e11 e01 e00
  exact ⟨e11, e00, (Units.ext e01).symm⟩

/- English proof (translation)
Establish `h' : !![(0 : A F), 1; -1, 0] * (!![1, b; 0, 1] * !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)]) * !![(0 : A F), 1; -1, 0] = !![1, c; 0, 1] * !![(d : A F), 0; 0, ((d⁻¹ : (A F)ˣ) : A F)] * !![(0 : A F), 1; -1, 0] * (!![1, c'; 0, 1] * !![(d' : A F), 0; 0, ((d'⁻¹ : (A F)ˣ) : A F)])` using `congrArg Subtype.val h`. Establish `e` using `congrFun (congrFun h' 1) 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two] at e`. Establish `hu : IsUnit (b * ((a⁻¹ : (A F)ˣ) : A F))`. Rewrite using `[e, ← Units.val_mul]`.

Conclude with `(d⁻¹ * d').isUnit.neg`. Conclude with `isUnit_of_mul_isUnit_left hu`.
-/
private theorem w_big {F : Type} [Field F] [NumberField F] {b c c' : A F} {a d d' : (A F)ˣ}
    (h : wW F * (nU b * mD a) * wW F = nU c * mD d * wW F * (nU c' * mD d')) : IsUnit b := by
  have h' : !![(0 : A F), 1; -1, 0] * (!![1, b; 0, 1] * !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)]) * !![(0 : A F), 1; -1, 0] =
      !![1, c; 0, 1] * !![(d : A F), 0; 0, ((d⁻¹ : (A F)ˣ) : A F)] * !![(0 : A F), 1; -1, 0] *
        (!![1, c'; 0, 1] * !![(d' : A F), 0; 0, ((d'⁻¹ : (A F)ˣ) : A F)]) :=
    congrArg Subtype.val h
  have e := congrFun (congrFun h' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e
  have hu : IsUnit (b * ((a⁻¹ : (A F)ˣ) : A F)) := by
    rw [e, ← Units.val_mul]
    exact (d⁻¹ * d').isUnit.neg
  exact isUnit_of_mul_isUnit_left hu

/- English proof (translation)
Introduce `F _ _ H _ N M W hR hG hgen`. Take `⟨gR, gG, gP, gU, gC⟩` from `grpRel F`. Take `⟨N', hN'⟩ : ∃ N' : A F → Hˣ, ∀ b, (N' b : H) = N b` from `⟨fun b => ⟨N b, N (-b), by rw [← hR.N_add]; simp [hR.N_zero], by rw [← hR.N_add]; simp [hR.N_zero]⟩, fun _ => rfl⟩`. Take `⟨M', hM'⟩ : ∃ M' : (A F)ˣ → Hˣ, ∀ a, (M' a : H) = M a` from `⟨fun a => ⟨M a, M a⁻¹, by rw [← hR.M_mul]; simp [hR.M_one], by rw [← hR.M_mul]; simp [hR.M_one]⟩, fun _ => rfl⟩`. Take `⟨W', hW'⟩ : ∃ W' : Hˣ, (W' : H) = W` from `hR.W_unit`.

Establish `memP : ∀ b a, nU b * mD a ∈ upperP F` using `fun b a => (gP _).2 ⟨b, a, rfl⟩`. Establish `memN : ∀ b, nU b ∈ upperP F` using `fun b => (gP _).2 ⟨b, 1, by rw [gR.M_one, mul_one]⟩`. Establish `memM : ∀ a, mD a ∈ upperP F` using `fun a => (gP _).2 ⟨0, a, by rw [gR.N_zero, one_mul]⟩`. Establish `hex : ∀ p : upperP F, ∃ b a, (p : G1 F) = nU b * mD a` using `fun p => (gP p).1 p.2`. Use `choose bb aa hba using hex`.

Establish `huniq : ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a → bb p = b ∧ aa p = a` using `fun p b a h => gU _ _ _ _ ((hba p).symm.trans h)`. Choose the witnesses or unpack the hypotheses as in `⟨ρ, hρ⟩ : ∃ ρ : upperP F →* Hˣ, ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a → ρ p = N' b * M' a := by`. Use `⟨MonoidHom.mk' (fun p => N' (bb p) * M' (aa p)) ?_, ?_⟩` and prove the remaining obligations. Introduce `p q`. Take `⟨e1, e2⟩` from `huniq (p * q) (bb p + (aa p : A F) ^ 2 * bb q) (aa p * aa q) (by`.

Rewrite using `[Subgroup.coe_mul, hba p, hba q, bor gR])`. Rewrite using `[e1, e2]`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, hN', hM']`. Conclude with `(bor hR _ _ _ _).symm`.

Introduce `p b a h`. Take `⟨e1, e2⟩` from `huniq p b a h`. Simplify using `[e1, e2]`. Establish `ρv : ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a → ((ρ p : Hˣ) : H) = N b * M a`. Introduce `p b a h`.

Rewrite using `[hρ p b a h, Units.val_mul, hN', hM']`. Establish `c1 : ∀ p q : upperP F, wW F * p = q * wW F → W' * ρ p = ρ q * W'`. Introduce `p q h`. Rewrite `h` using `[hba p, hba q]`. Take `⟨hb, hc, hd⟩` from `w_small h`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, ρv p _ _ (hba p), ρv q _ _ (hba q), hb, hc, hd, hW', hR.N_zero, one_mul, one_mul]`. Conclude with `hR.WM _`. Establish `c2 : ∀ p : upperP F, (∃ p₁ p₂ : upperP F, wW F * p * wW F = p₁ * wW F * p₂) → ∃ p₁ p₂ : upperP F, wW F * p * wW F = p₁ * wW F * p₂ ∧ W' * ρ p * W' = ρ p₁ * W' * ρ p₂`. Introduce and unpack `p ⟨p₁, p₂, h⟩`.

Rewrite `h` using `[hba p, hba p₁, hba p₂]`. Take `⟨t, ht⟩` from `w_big h`. Use `⟨⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (-t⁻¹)⟩, ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (aa p)⁻¹⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hba p, ← ht]`. Conclude with `gen_rel gR gG t (aa p)`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul]`. Rewrite using `[ρv p _ _ (hba p), ρv ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (-t⁻¹)⟩ _ _ rfl, ρv ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (aa p)⁻¹⟩ _ _ rfl, hW', ← ht]`. Conclude with `gen_rel hR hG t (aa p)`. Establish `c3 : ∀ s : Finset (G1 F), ∃ u : G1 F, ∀ g ∈ s, ∃ p₁ p₂ : upperP F, g * u = p₁ * wW F * p₂`.

Introduce `s`. Take `⟨u, hu⟩` from `hgen s`. Use `⟨u, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨b, a, b', e⟩` from `(gC _).1 (hu g hg)`. Conclude with `⟨⟨_, memP b a⟩, ⟨_, memN b'⟩, e⟩`.

Take `⟨Φ, h1, h2⟩` from `GlobalTheory.bigCell_hom (G1 F) Hˣ (upperP F) (wW F) ρ W' c1 c2 c3`. Use `⟨(Units.coeHom H).comp Φ, fun b => ?_, fun a => ?_, ?_⟩` and prove the remaining obligations. Use `h1 ⟨_, memN b⟩` as an intermediate fact. Simplify using `only [MonoidHom.comp_apply, Units.coeHom_apply]`. Rewrite using `[show Φ (nU b) = ρ ⟨_, memN b⟩ from this, ρv ⟨_, memN b⟩ b 1 (by rw [gR.M_one, mul_one]), hR.M_one, mul_one]`.

Use `h1 ⟨_, memM a⟩` as an intermediate fact. Simplify using `only [MonoidHom.comp_apply, Units.coeHom_apply]`. Rewrite using `[show Φ (mD a) = ρ ⟨_, memM a⟩ from this, ρv ⟨_, memM a⟩ 0 a (by rw [gR.N_zero, one_mul]), hR.N_zero, one_mul]`. Simplify using `only [MonoidHom.comp_apply, Units.coeHom_apply]`. Rewrite using `[h2, hW']`.
-/
theorem UpperTheory.ConvolutionTheory.R2.C.chunk :
    ∀ (F : Type) [Field F] [NumberField F] (H : Type) [Monoid H] (N : A F → H) (M : (A F)ˣ → H) (W : H), Rel N M W → Gauss N M W →
    (∀ s : Finset (G1 F), ∃ u : G1 F, ∀ g ∈ s, IsUnit ((g * u) 1 0)) →
    ∃ Φ : G1 F →* H, (∀ b, Φ (nU b) = N b) ∧ (∀ a, Φ (mD a) = M a) ∧ Φ (wW F) = W := by
  intro F _ _ H _ N M W hR hG hgen
  obtain ⟨gR, gG, gP, gU, gC⟩ := grpRel F
  obtain ⟨N', hN'⟩ : ∃ N' : A F → Hˣ, ∀ b, (N' b : H) = N b :=
    ⟨fun b => ⟨N b, N (-b), by rw [← hR.N_add]; simp [hR.N_zero],
      by rw [← hR.N_add]; simp [hR.N_zero]⟩, fun _ => rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : (A F)ˣ → Hˣ, ∀ a, (M' a : H) = M a :=
    ⟨fun a => ⟨M a, M a⁻¹, by rw [← hR.M_mul]; simp [hR.M_one],
      by rw [← hR.M_mul]; simp [hR.M_one]⟩, fun _ => rfl⟩
  obtain ⟨W', hW'⟩ : ∃ W' : Hˣ, (W' : H) = W := hR.W_unit
  have memP : ∀ b a, nU b * mD a ∈ upperP F := fun b a => (gP _).2 ⟨b, a, rfl⟩
  have memN : ∀ b, nU b ∈ upperP F := fun b => (gP _).2 ⟨b, 1, by rw [gR.M_one, mul_one]⟩
  have memM : ∀ a, mD a ∈ upperP F := fun a => (gP _).2 ⟨0, a, by rw [gR.N_zero, one_mul]⟩
  have hex : ∀ p : upperP F, ∃ b a, (p : G1 F) = nU b * mD a := fun p => (gP p).1 p.2
  choose bb aa hba using hex
  have huniq : ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a → bb p = b ∧ aa p = a :=
    fun p b a h => gU _ _ _ _ ((hba p).symm.trans h)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : upperP F →* Hˣ, ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a →
      ρ p = N' b * M' a := by
    refine ⟨MonoidHom.mk' (fun p => N' (bb p) * M' (aa p)) ?_, ?_⟩
    · intro p q
      obtain ⟨e1, e2⟩ := huniq (p * q) (bb p + (aa p : A F) ^ 2 * bb q) (aa p * aa q) (by
        rw [Subgroup.coe_mul, hba p, hba q, bor gR])
      rw [e1, e2]
      apply Units.ext
      simp only [Units.val_mul, hN', hM']
      exact (bor hR _ _ _ _).symm
    · intro p b a h
      obtain ⟨e1, e2⟩ := huniq p b a h
      simp [e1, e2]
  have ρv : ∀ (p : upperP F) b a, (p : G1 F) = nU b * mD a → ((ρ p : Hˣ) : H) = N b * M a := by
    intro p b a h
    rw [hρ p b a h, Units.val_mul, hN', hM']
  have c1 : ∀ p q : upperP F, wW F * p = q * wW F → W' * ρ p = ρ q * W' := by
    intro p q h
    rw [hba p, hba q] at h
    obtain ⟨hb, hc, hd⟩ := w_small h
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ρv p _ _ (hba p), ρv q _ _ (hba q), hb, hc, hd, hW', hR.N_zero,
      one_mul, one_mul]
    exact hR.WM _
  have c2 : ∀ p : upperP F, (∃ p₁ p₂ : upperP F, wW F * p * wW F = p₁ * wW F * p₂) →
      ∃ p₁ p₂ : upperP F, wW F * p * wW F = p₁ * wW F * p₂ ∧ W' * ρ p * W' = ρ p₁ * W' * ρ p₂ := by
    rintro p ⟨p₁, p₂, h⟩
    rw [hba p, hba p₁, hba p₂] at h
    obtain ⟨t, ht⟩ := w_big h
    refine ⟨⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (-t⁻¹)⟩, ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (aa p)⁻¹⟩, ?_, ?_⟩
    · rw [hba p, ← ht]
      exact gen_rel gR gG t (aa p)
    · apply Units.ext
      simp only [Units.val_mul]
      rw [ρv p _ _ (hba p), ρv ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (-t⁻¹)⟩ _ _ rfl,
        ρv ⟨_, memP (-((t⁻¹ : (A F)ˣ) : A F)) (aa p)⁻¹⟩ _ _ rfl, hW', ← ht]
      exact gen_rel hR hG t (aa p)
  have c3 : ∀ s : Finset (G1 F), ∃ u : G1 F, ∀ g ∈ s, ∃ p₁ p₂ : upperP F, g * u = p₁ * wW F * p₂ := by
    intro s
    obtain ⟨u, hu⟩ := hgen s
    refine ⟨u, fun g hg => ?_⟩
    obtain ⟨b, a, b', e⟩ := (gC _).1 (hu g hg)
    exact ⟨⟨_, memP b a⟩, ⟨_, memN b'⟩, e⟩
  obtain ⟨Φ, h1, h2⟩ := GlobalTheory.bigCell_hom (G1 F) Hˣ (upperP F) (wW F) ρ W' c1 c2 c3
  refine ⟨(Units.coeHom H).comp Φ, fun b => ?_, fun a => ?_, ?_⟩
  · have := h1 ⟨_, memN b⟩
    simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [show Φ (nU b) = ρ ⟨_, memN b⟩ from this,
      ρv ⟨_, memN b⟩ b 1 (by rw [gR.M_one, mul_one]), hR.M_one, mul_one]
  · have := h1 ⟨_, memM a⟩
    simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [show Φ (mD a) = ρ ⟨_, memM a⟩ from this,
      ρv ⟨_, memM a⟩ 0 a (by rw [gR.N_zero, one_mul]), hR.N_zero, one_mul]
  · simp only [MonoidHom.comp_apply, Units.coeHom_apply]
    rw [h2, hW']
