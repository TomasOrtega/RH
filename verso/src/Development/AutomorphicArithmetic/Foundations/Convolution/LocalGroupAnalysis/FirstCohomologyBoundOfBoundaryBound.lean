import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.PowComp
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmCent
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalExt
open PositivityTheory.Rg.Tf.Geo

open Polynomial NumberField IsDedekindDomain UpperTheory.ConvolutionTheory.D
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.G

section Abstract

variable {n : ℕ}

private def IntGL {R : Type} [CommRing R] (S : Subring R) (g : GL (Fin n) R) : Prop :=
  (∀ i j, g i j ∈ S) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ S

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Set `A : Matrix (Fin n) (Fin n) S` to `Matrix.of fun i j => ⟨g i j, h1 i j⟩`. Set `B : Matrix (Fin n) (Fin n) S` to `Matrix.of fun i j => ⟨(g⁻¹ : GL (Fin n) R) i j, h2 i j⟩`. Establish `hinj : Function.Injective (RingHom.mapMatrix (m` using `Fin n) S.subtype) := fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)`.

Establish `hA : RingHom.mapMatrix S.subtype A = (g : Matrix (Fin n) (Fin n) R)` using `rfl`. Establish `hB : RingHom.mapMatrix S.subtype B = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)` using `rfl`. Conclude with `⟨⟨A, B, hinj (by rw [map_mul, map_one, hA, hB, Units.mul_inv]), hinj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])⟩, Units.ext hA⟩`. Introduce and unpack `⟨u, rfl⟩`. Use `⟨fun i j => (u i j).2, fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_inv]`. Conclude with `((u⁻¹ : GL (Fin n) S) i j).2`.
-/
private theorem intGL_iff {R : Type} [CommRing R] (S : Subring R) (g : GL (Fin n) R) :
    IntGL S g ↔ ∃ u : GL (Fin n) S, Matrix.GeneralLinearGroup.map S.subtype u = g := by
  constructor
  · rintro ⟨h1, h2⟩
    let A : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨g i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨(g⁻¹ : GL (Fin n) R) i j, h2 i j⟩
    have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) S.subtype) :=
      fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
    have hA : RingHom.mapMatrix S.subtype A = (g : Matrix (Fin n) (Fin n) R) := rfl
    have hB : RingHom.mapMatrix S.subtype B = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := rfl
    exact ⟨⟨A, B, hinj (by rw [map_mul, map_one, hA, hB, Units.mul_inv]),
      hinj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])⟩, Units.ext hA⟩
  · rintro ⟨u, rfl⟩
    refine ⟨fun i j => (u i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((u⁻¹ : GL (Fin n) S) i j).2

variable {k R : Type} [Field k] [CommRing R] [Algebra k R]

/- English proof (translation)
Establish `hp : ∀ (j : ℕ) x, ((e.symm.trans (σ.trans e)) ^ j) (e x) = e ((σ ^ j) x)`. Introduce `j x`. Proceed by induction on `j with`. Consider the case `zero => rfl`. Consider the case `succ j ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]`.

Simplify using the standard rewrite rules. Take `⟨s, x, y, hxy⟩` from `h.sep`. Use `⟨h.pos, AlgEquiv.ext fun z => ?_, fun a b hab => h.inj (e.injective (by rw [e.commutes, e.commutes, hab])), fun z hz => ?_, s, fun i => e (x i), fun i => e (y i), fun j hj => ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `e.surjective z`. Rewrite using `[hp, h.pow]`.

Both sides reduce to the same expression. Take `⟨z, rfl⟩` from `e.surjective z`. Take `⟨c, rfl⟩` from `h.fix z (e.injective (by simpa using hz))`. Conclude with `⟨c, (e.commutes c).symm⟩`. Apply the tactic sequence `simp only [hp, ← map_mul, ← map_sum, hxy j hj] split_ifs <;> simp`.
-/
private theorem isGal_equiv {R' : Type} [CommRing R'] [Algebra k R'] (e : R ≃ₐ[k] R') {σ : R ≃ₐ[k] R} {q : ℕ}
    (h : IsGal σ q) : IsGal (e.symm.trans (σ.trans e)) q := by
  have hp : ∀ (j : ℕ) x, ((e.symm.trans (σ.trans e)) ^ j) (e x) = e ((σ ^ j) x) := by
    intro j x
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]; simp
  obtain ⟨s, x, y, hxy⟩ := h.sep
  refine ⟨h.pos, AlgEquiv.ext fun z => ?_, fun a b hab => h.inj (e.injective (by rw [e.commutes, e.commutes, hab])),
    fun z hz => ?_, s, fun i => e (x i), fun i => e (y i), fun j hj => ?_⟩
  · obtain ⟨z, rfl⟩ := e.surjective z
    rw [hp, h.pow]; rfl
  · obtain ⟨z, rfl⟩ := e.surjective z
    obtain ⟨c, rfl⟩ := h.fix z (e.injective (by simpa using hz))
    exact ⟨c, (e.commutes c).symm⟩
  · simp only [hp, ← map_mul, ← map_sum, hxy j hj]
    split_ifs <;> simp

/- English proof (translation)
Establish `hpow : ∀ (m : ℕ), ∀ r ∈ S, (σ ^ m) r ∈ S`. Introduce `m r hr`. Proceed by induction on `m with`. Consider the case `zero => exact hr`. Consider the case `succ m ih => rw [pow_succ', AlgEquiv.mul_apply]`.

Conclude with `hS _ ih`. Establish `hinv : ∀ r ∈ S, σ.symm r ∈ S`. Introduce `r hr`. Establish `h1 : σ ^ (q - 1) * σ = 1` using `by rw [← pow_succ, Nat.sub_add_cancel hσ.pos, hσ.pow]`. Establish `h2 : σ.symm r = (σ ^ (q - 1)) r`.

Rewrite using `[eq_inv_of_mul_eq_one_left h1]`. Both sides reduce to the same expression. Rewrite using `[h2]`. Conclude with `hpow _ _ hr`. Use `letI : Algebra O S := (((algebraMap k R).comp O.subtype).codRestrict S fun c => (hOS _).2 c.2).toAlgebra`.

Establish `hji : ∀ c : O, S.subtype (algebraMap O S c) = algebraMap k R (O.subtype c)` using `fun _ => rfl`. Set `s : S ≃ₐ[O] S` to `{ toFun := fun r => ⟨σ r, hS _ r.2⟩ invFun := fun r => ⟨σ.symm r, hinv _ r.2⟩ left_inv := fun r => Subtype.ext (σ.symm_apply_apply _) right_inv := fun r => Subtype.ext (σ.apply_symm_apply _) map_mul' := fun r r' => Subtype.ext (map_mul σ _ _) map_add' := fun r r' => Subtype.ext ( …`. Establish `hjs : ∀ r, S.subtype (s r) = σ (S.subtype r)` using `fun _ => rfl`. Establish `hjp : ∀ (m : ℕ) r, S.subtype ((s ^ m) r) = (σ ^ m) (S.subtype r)`. Introduce `m r`.

Proceed by induction on `m with`. Consider the case `zero => rfl`. Consider the case `succ m ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, hjs, ih]`. Establish `hj` using `S.subtype_injective`. Establish `hsG : IsGal s q`.

Take `⟨m, x, y, hm, hxy⟩` from `hsep`. Use `⟨hσ.pos, AlgEquiv.ext fun r => hj (by rw [hjp, hσ.pow]; rfl), fun c c' h => Subtype.ext (hσ.inj (congrArg S.subtype h)), fun r hr => ?_, m, fun i => ⟨x i, (hm i).1⟩, fun i => ⟨y i, (hm i).2⟩, fun j hj' => hj ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hσ.fix r (congrArg S.subtype hr)`. Conclude with `⟨⟨c, (hOS c).1 (hc ▸ r.2)⟩, Subtype.ext hc⟩`. Simplify using `only [map_sum, map_mul, hjp]`.

Use `(hxy j hj').trans ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Take `⟨a, rfl⟩` from `(intGL_iff S a).1 ha`. Take `⟨γ, rfl⟩` from `(intGL_iff O γ).1 hγ`. Establish `hcp : cp (Matrix.GeneralLinearGroup.map O.subtype γ) = (cp γ).map O.subtype`.

Unfold `cp`. Rewrite using `[← Matrix.charpoly_map]`. Both sides reduce to the same expression. Take `⟨u, w, hu, hw, huw⟩` from `hs`. Establish `hsep0 : (cp γ).Separable`.

Take `⟨u, rfl⟩` from `(mem_lifts _).1 hu`. Take `⟨w, rfl⟩` from `(mem_lifts _).1 hw`. Use `⟨u, w, map_injective _ O.subtype_injective ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← derivative_map, ← hcp, huw, Polynomial.map_one]`. Establish `hsg : ∀ (m : ℕ) (g : GL (Fin n) S), Matrix.GeneralLinearGroup.map S.subtype (sg (s ^ m) g) = sg (σ ^ m) (Matrix.GeneralLinearGroup.map S.subtype g)` using `fun m g => by`.

Use extensionality with `a b`. Conclude with `hjp m _`. Establish `hN0 : nm s q a = up S γ`. Establish `h1 : Matrix.GeneralLinearGroup.map S.subtype (nm s q a) = Matrix.GeneralLinearGroup.map S.subtype (up S γ)`. Use `Eq.trans ?_ (hN.trans (by ext; rfl))` and prove the remaining obligations.

Unfold `nm`. Rewrite using `[map_list_prod, List.map_map]`. Use `congr 1`. Conclude with `List.map_congr_left fun m _ => hsg m a`. Use extensionality with `b c`.

Conclude with `congrArg (fun g : GL (Fin n) R => g b c) h1`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨a', ha'⟩` from `(intGL_iff S _).1 h`. Take `⟨t, u, ht, hx⟩` from `nmInt O S k R O.subtype S.subtype s σ q hsG hσ hj hjs hji n a a' γ hsep0 hN0 x ha'.symm`.

Conclude with `⟨t, ht, _, (intGL_iff S _).2 ⟨u, rfl⟩, hx⟩`. Introduce and unpack `⟨t, ht, y, hy, rfl⟩`. Take `⟨y, rfl⟩` from `(intGL_iff S y).1 hy`. Establish `h1` using `(nmCent k R σ q hσ n _ _ ⟨u, w, huw⟩ hN (up R t)).2 ⟨t, ht, rfl⟩`. Use `(intGL_iff S _).2 ⟨sgConj s y a, ?_⟩` and prove the remaining obligations.

Establish `h2` using `hsg 1 y`. Rewrite `h2` using `[pow_one, pow_one]`. Rewrite `h1` using `[sgConj]`. Rewrite using `[sgConj, sgConj, map_mul, map_mul, map_inv, h2, map_mul, mul_inv_rev]`. Use `conv_lhs => rw [← h1]`.

Use `group`.
-/
private theorem abstract_hilbert90 (σ : R ≃ₐ[k] R) (q : ℕ) (hσ : IsGal σ q) (O : Subring k) [IsLocalRing O] (S : Subring R)
    (hOS : ∀ x, algebraMap k R x ∈ S ↔ x ∈ O) (hS : ∀ r ∈ S, σ r ∈ S)
    (hsep : ∃ (s : ℕ) (x y : Fin s → R), (∀ i, x i ∈ S ∧ y i ∈ S) ∧
      ∀ j < q, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0)
    (a : GL (Fin n) R) (γ : GL (Fin n) k) (ha : IntGL S a) (hγ : IntGL O γ)
    (hs : ∃ u w : k[X], u ∈ lifts O.subtype ∧ w ∈ lifts O.subtype ∧ u * cp γ + w * derivative (cp γ) = 1)
    (hN : nm σ q a = up R γ) (x : GL (Fin n) R) :
    IntGL S (sgConj σ x a) ↔ ∃ t : GL (Fin n) k, t * γ = γ * t ∧ ∃ y, IntGL S y ∧ x = up R t * y := by
  have hpow : ∀ (m : ℕ), ∀ r ∈ S, (σ ^ m) r ∈ S := by
    intro m r hr
    induction m with
    | zero => exact hr
    | succ m ih => rw [pow_succ', AlgEquiv.mul_apply]; exact hS _ ih
  have hinv : ∀ r ∈ S, σ.symm r ∈ S := by
    intro r hr
    have h1 : σ ^ (q - 1) * σ = 1 := by rw [← pow_succ, Nat.sub_add_cancel hσ.pos, hσ.pow]
    have h2 : σ.symm r = (σ ^ (q - 1)) r := by
      rw [eq_inv_of_mul_eq_one_left h1]; rfl
    rw [h2]; exact hpow _ _ hr
  letI : Algebra O S := (((algebraMap k R).comp O.subtype).codRestrict S fun c => (hOS _).2 c.2).toAlgebra
  have hji : ∀ c : O, S.subtype (algebraMap O S c) = algebraMap k R (O.subtype c) := fun _ => rfl
  let s : S ≃ₐ[O] S :=
    { toFun := fun r => ⟨σ r, hS _ r.2⟩
      invFun := fun r => ⟨σ.symm r, hinv _ r.2⟩
      left_inv := fun r => Subtype.ext (σ.symm_apply_apply _)
      right_inv := fun r => Subtype.ext (σ.apply_symm_apply _)
      map_mul' := fun r r' => Subtype.ext (map_mul σ _ _)
      map_add' := fun r r' => Subtype.ext (map_add σ _ _)
      commutes' := fun c => Subtype.ext (σ.commutes _) }
  have hjs : ∀ r, S.subtype (s r) = σ (S.subtype r) := fun _ => rfl
  have hjp : ∀ (m : ℕ) r, S.subtype ((s ^ m) r) = (σ ^ m) (S.subtype r) := by
    intro m r
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, hjs, ih]
  have hj := S.subtype_injective
  have hsG : IsGal s q := by
    obtain ⟨m, x, y, hm, hxy⟩ := hsep
    refine ⟨hσ.pos, AlgEquiv.ext fun r => hj (by rw [hjp, hσ.pow]; rfl),
      fun c c' h => Subtype.ext (hσ.inj (congrArg S.subtype h)), fun r hr => ?_,
      m, fun i => ⟨x i, (hm i).1⟩, fun i => ⟨y i, (hm i).2⟩, fun j hj' => hj ?_⟩
    · obtain ⟨c, hc⟩ := hσ.fix r (congrArg S.subtype hr)
      exact ⟨⟨c, (hOS c).1 (hc ▸ r.2)⟩, Subtype.ext hc⟩
    · simp only [map_sum, map_mul, hjp]
      refine (hxy j hj').trans ?_
      split_ifs <;> simp
  obtain ⟨a, rfl⟩ := (intGL_iff S a).1 ha
  obtain ⟨γ, rfl⟩ := (intGL_iff O γ).1 hγ
  have hcp : cp (Matrix.GeneralLinearGroup.map O.subtype γ) = (cp γ).map O.subtype := by
    unfold cp
    rw [← Matrix.charpoly_map]
    rfl
  obtain ⟨u, w, hu, hw, huw⟩ := hs
  have hsep0 : (cp γ).Separable := by
    obtain ⟨u, rfl⟩ := (mem_lifts _).1 hu
    obtain ⟨w, rfl⟩ := (mem_lifts _).1 hw
    refine ⟨u, w, map_injective _ O.subtype_injective ?_⟩
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← derivative_map, ← hcp, huw, Polynomial.map_one]
  have hsg : ∀ (m : ℕ) (g : GL (Fin n) S), Matrix.GeneralLinearGroup.map S.subtype (sg (s ^ m) g) =
      sg (σ ^ m) (Matrix.GeneralLinearGroup.map S.subtype g) := fun m g => by
    ext a b
    exact hjp m _
  have hN0 : nm s q a = up S γ := by
    have h1 : Matrix.GeneralLinearGroup.map S.subtype (nm s q a) = Matrix.GeneralLinearGroup.map S.subtype (up S γ) := by
      refine Eq.trans ?_ (hN.trans (by ext; rfl))
      unfold nm
      rw [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left fun m _ => hsg m a
    ext b c
    exact congrArg (fun g : GL (Fin n) R => g b c) h1
  constructor
  · intro h
    obtain ⟨a', ha'⟩ := (intGL_iff S _).1 h
    obtain ⟨t, u, ht, hx⟩ := nmInt O S k R O.subtype S.subtype s σ q hsG hσ hj hjs hji n a a' γ hsep0 hN0 x ha'.symm
    exact ⟨t, ht, _, (intGL_iff S _).2 ⟨u, rfl⟩, hx⟩
  · rintro ⟨t, ht, y, hy, rfl⟩
    obtain ⟨y, rfl⟩ := (intGL_iff S y).1 hy
    have h1 := (nmCent k R σ q hσ n _ _ ⟨u, w, huw⟩ hN (up R t)).2 ⟨t, ht, rfl⟩
    refine (intGL_iff S _).2 ⟨sgConj s y a, ?_⟩
    have h2 := hsg 1 y
    rw [pow_one, pow_one] at h2
    rw [sgConj] at h1
    rw [sgConj, sgConj, map_mul, map_mul, map_inv, h2, map_mul, mul_inv_rev]
    conv_lhs => rw [← h1]
    group

end Abstract

section Concrete

open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.Tf.Loc ValuativeRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h : valuation (w.adicCompletion E) x ≤ valuation (w.adicCompletion E) 1 ↔ Valued.v x ≤ Valued.v (1 : w.adicCompletion E)`. Rewrite using `[← Valuation.Compatible.vle_iff_le]`. Conclude with `Iff.rfl`. Express the relevant statement in the definitionally equal form `valuation _ x ≤ 1 ↔ _`. Simplify using `using h`.
-/
private theorem mem_O {w : HeightOneSpectrum (𝓞 E)} (x : w.adicCompletion E) :
    x ∈ 𝒪[w.adicCompletion E] ↔ Valued.v x ≤ 1 := by
  have h : valuation (w.adicCompletion E) x ≤ valuation (w.adicCompletion E) 1 ↔
      Valued.v x ≤ Valued.v (1 : w.adicCompletion E) := by
    rw [← Valuation.Compatible.vle_iff_le]
    exact Iff.rfl
  change valuation _ x ≤ 1 ↔ _
  simpa using h

omit [NumberField F] in
/- English proof (translation)
Establish `h1 : ‖galHom σ w w' h y‖ = ‖y‖`. Use `(HeightOneSpectrum.denseRange_algebraMap E w).equalizer (continuous_norm.comp (continuous_galHom σ w w' h)) continuous_norm (funext fun x ↦ by` as an intermediate fact. Substitute `h` using the available equality. Simplify using `only [Function.comp_apply, galHom_algebraMap, norm_algebraMap_smul])`. Conclude with `congrFun this y`.

Rewrite `hy`, the goal using `[mem_O, ← Valued.toNormedField.norm_le_one_iff]`. Conclude with `h1.trans_le hy`.
-/
private theorem galHom_mem (σ : E ≃ₐ[F] E) (w w' : HeightOneSpectrum (𝓞 E)) (h : w' = σ • w)
    (y : w.adicCompletion E) (hy : y ∈ 𝒪[w.adicCompletion E]) : galHom σ w w' h y ∈ 𝒪[w'.adicCompletion E] := by
  have h1 : ‖galHom σ w w' h y‖ = ‖y‖ := by
    have := (HeightOneSpectrum.denseRange_algebraMap E w).equalizer
      (continuous_norm.comp (continuous_galHom σ w w' h)) continuous_norm
      (funext fun x ↦ by
        subst h
        simp only [Function.comp_apply, galHom_algebraMap, norm_algebraMap_smul])
    exact congrFun this y
  rw [mem_O, ← Valued.toNormedField.norm_le_one_iff] at hy ⊢
  exact h1.trans_le hy

variable (E) in

private noncomputable def intOver (v : HeightOneSpectrum (𝓞 F)) : Subring (CompletionsOver E v) :=
  ⨅ w : PlacesOver E v, (𝒪[w.1.adicCompletion E]).comap
    (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)

/- English proof (translation)
Simplify using `[intOver, Subring.mem_iInf]`.
-/
private theorem mem_intOver {v : HeightOneSpectrum (𝓞 F)} (y : CompletionsOver E v) :
    y ∈ intOver E v ↔ ∀ w, y w ∈ 𝒪[w.1.adicCompletion E] := by
  simp [intOver, Subring.mem_iInf]

/- English proof (translation)
Simplify using `only [unitSet, Set.mem_setOf_eq, GLnLocal.mem_integralGL_iff, IntGL, mem_intOver, ← map_inv]`. Conclude with `⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩, fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩`.
-/
private theorem mem_unitSet {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} (g : GL (Fin n) (CompletionsOver E v)) :
    g ∈ unitSet E n v ↔ IntGL (intOver E v) g := by
  simp only [unitSet, Set.mem_setOf_eq, GLnLocal.mem_integralGL_iff, IntGL, mem_intOver, ← map_inv]
  exact ⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩,
    fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩

private noncomputable def sigLoc (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    CompletionsOver E v ≃ₐ[v.adicCompletion F] CompletionsOver E v :=
  (tensorEquiv E v).symm.trans ((ext (v.adicCompletion F) σ).trans (tensorEquiv E v))

/- English proof (translation)
Take `⟨x, rfl⟩` from `(tensorEquiv E v).surjective y`. Rewrite using `[← tensorEquiv_map_gal, sigLoc, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
private theorem sigLoc_eq_piGal (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (y : CompletionsOver E v) :
    sigLoc σ v y = piGal v σ y := by
  obtain ⟨x, rfl⟩ := (tensorEquiv E v).surjective y
  rw [← tensorEquiv_map_gal, sigLoc, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rfl

/- English proof (translation)
Rewrite using `[← tensorEquiv_one_tmul, ← tensorEquiv_one_tmul, sigLoc, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
private theorem sigLoc_algebraMap (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    sigLoc σ v (algebraMap E _ x) = algebraMap E _ (σ x) := by
  rw [← tensorEquiv_one_tmul, ← tensorEquiv_one_tmul, sigLoc, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rfl

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rfl`. Consider the case `succ m ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, sigLoc_algebraMap]`.
-/
private theorem sigLoc_pow (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (x : E) :
    (sigLoc σ v ^ m) (algebraMap E _ x) = algebraMap E _ ((σ ^ m) x) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih, sigLoc_algebraMap]

/- English proof (translation)
Use `RingHom.ext fun y => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `(tensorEquiv' E v).surjective y`. Establish `h : galFin σ v (tensorEquiv' E v x) = tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _) x)`. Simplify using `[galFin, galOf]`. Rewrite using `[h]`.

Use `clear h`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Rewrite using `[Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, map_mul]`.

Use `congr 1`. Conclude with `(sigLoc_algebraMap σ v a).symm`. Conclude with `((sigLoc σ v).commutes b).symm`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add, map_add, map_add, ha, hb]`.
-/
private theorem galFin_eq (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    galFin σ v = (sigLoc σ v : CompletionsOver E v →+* CompletionsOver E v) := by
  refine RingHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (tensorEquiv' E v).surjective y
  have h : galFin σ v (tensorEquiv' E v x) =
      tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _) x) := by
    simp [galFin, galOf]
  rw [h]
  clear h
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, map_mul]
    congr 1
    · exact (sigLoc_algebraMap σ v a).symm
    · exact ((sigLoc σ v).commutes b).symm
  | add a b ha hb =>
    rw [map_add, map_add, map_add, map_add, ha, hb]

/- English proof (translation)
Use `(HeightOneSpectrum.Support.finite (𝓞 F) t).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `hv ((mem_O _).2 ?_)` and prove the remaining obligations. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t).trans_le (not_lt.1 h)`.
-/
private theorem ev_elt (t : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (v.adicCompletion F) t ∈ 𝒪[v.adicCompletion F] := by
  refine (HeightOneSpectrum.Support.finite (𝓞 F) t).subset fun v hv => ?_
  by_contra h
  refine hv ((mem_O _).2 ?_)
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t).trans_le (not_lt.1 h)

/- English proof (translation)
Use `filter_upwards [(Filter.eventually_all_finset p.support).2 fun i _ => ev_elt (p.coeff i)] with v hv`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `i`. Rewrite using `[coeff_map]`. Distinguish the cases in `hi : i ∈ p.support`.

Conclude with `⟨⟨_, hv i hi⟩, rfl⟩`. Rewrite using `[notMem_support_iff.1 hi]`. Conclude with `⟨0, by simp⟩`.
-/
private theorem ev_poly (p : F[X]) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    p.map (algebraMap F (v.adicCompletion F)) ∈ lifts (𝒪[v.adicCompletion F]).subtype := by
  filter_upwards [(Filter.eventually_all_finset p.support).2 fun i _ => ev_elt (p.coeff i)] with v hv
  rw [lifts_iff_coeff_lifts]
  intro i
  rw [coeff_map]
  by_cases hi : i ∈ p.support
  · exact ⟨⟨_, hv i hi⟩, rfl⟩
  · rw [notMem_support_iff.1 hi]
    exact ⟨0, by simp⟩

/- English proof (translation)
Use `((Filter.eventually_cofinite.1 (ev_elt t)).image (below F)).subset fun v hv => ?_` and prove the remaining obligations. Rewrite `hv` using `[Set.mem_compl_iff, Set.mem_setOf_eq, mem_intOver, not_forall]`. Take `⟨w, hw⟩` from `hv`. Conclude with `⟨w.1, hw, (below_eq_iff _ _).2 w.2⟩`.
-/
private theorem ev_over (t : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap E (CompletionsOver E v) t ∈ intOver E v := by
  refine ((Filter.eventually_cofinite.1 (ev_elt t)).image (below F)).subset fun v hv => ?_
  rw [Set.mem_compl_iff, Set.mem_setOf_eq, mem_intOver, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, (below_eq_iff _ _).2 w.2⟩

/- English proof (translation)
Establish `hv : ∀ w : PlacesOver E v, algebraMap _ (CompletionsOver E v) c w ∈ 𝒪[w.1.adicCompletion E] ↔ c ∈ 𝒪[v.adicCompletion F]` using `fun w => by`. Rewrite using `[mem_O, mem_O, Pi.algebraMap_apply, algebraMap_completion_eq, valued_completionMap, pow_le_one_iff (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 F)).ne']`. Rewrite using `[mem_intOver]`. Use `⟨fun h => ?_, fun h w => (hv w).2 h⟩` and prove the remaining obligations. Break down `isEmpty_or_nonempty (PlacesOver E v) with h0 | ⟨⟨w⟩⟩` into its components or cases.

Conclude with `absurd (hinj (Subsingleton.elim _ _)) (zero_ne_one (α := v.adicCompletion F))`. Conclude with `(hv w).1 (h w)`.
-/
private theorem alg_mem {v : HeightOneSpectrum (𝓞 F)}
    (hinj : Function.Injective (algebraMap (v.adicCompletion F) (CompletionsOver E v))) (c : v.adicCompletion F) :
    algebraMap _ (CompletionsOver E v) c ∈ intOver E v ↔ c ∈ 𝒪[v.adicCompletion F] := by
  have hv : ∀ w : PlacesOver E v, algebraMap _ (CompletionsOver E v) c w ∈ 𝒪[w.1.adicCompletion E] ↔
      c ∈ 𝒪[v.adicCompletion F] := fun w => by
    rw [mem_O, mem_O, Pi.algebraMap_apply, algebraMap_completion_eq, valued_completionMap,
      pow_le_one_iff (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 F)).ne']
  rw [mem_intOver]
  refine ⟨fun h => ?_, fun h w => (hv w).2 h⟩
  rcases isEmpty_or_nonempty (PlacesOver E v) with h0 | ⟨⟨w⟩⟩
  · exact absurd (hinj (Subsingleton.elim _ _)) (zero_ne_one (α := v.adicCompletion F))
  · exact (hv w).1 (h w)

/- English proof (translation)
Introduce `r hr`. Rewrite `hr`, the goal using `[mem_intOver]`. Introduce `w`. Rewrite using `[sigLoc_eq_piGal, piGal_apply, galEquiv_apply]`. Conclude with `galHom_mem _ _ _ _ _ (hr _)`.
-/
private theorem sigLoc_mem (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    ∀ r ∈ intOver E v, sigLoc σ v r ∈ intOver E v := by
  intro r hr
  rw [mem_intOver] at hr ⊢
  intro w
  rw [sigLoc_eq_piGal, piGal_apply, galEquiv_apply]
  exact galHom_mem _ _ _ _ _ (hr _)

/- English proof (translation)
Establish `h` using `congrArg (mapGL n (algebraMap E (CompletionsOver E v))) hN`. Rewrite `h` using `[normGL, twNorm, map_list_prod, List.map_map]`. Use `Eq.trans ?_ (h.trans ?_)` and prove the remaining obligations. Unfold `nm`. Use `congrArg List.prod (List.map_congr_left fun m _ => ?_)` and prove the remaining obligations.

Rewrite using `[Function.comp_apply, ← sigmaGL_pow]`. Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Conclude with `sigLoc_pow σ v m _`. Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Conclude with `(IsScalarTower.algebraMap_apply F E (CompletionsOver E v) _).symm.trans (IsScalarTower.algebraMap_apply F (v.adicCompletion F) (CompletionsOver E v) _)`.
-/
private theorem nm_loc (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (δ : GL (Fin n) E) (γ : GL (Fin n) F)
    (hN : normGL σ δ = incl γ) :
    nm (sigLoc σ v) (Module.finrank F E) (mapGL n (algebraMap E (CompletionsOver E v)) δ) =
      up (CompletionsOver E v) (mapGL n (algebraMap F (v.adicCompletion F)) γ) := by
  have h := congrArg (mapGL n (algebraMap E (CompletionsOver E v))) hN
  rw [normGL, twNorm, map_list_prod, List.map_map] at h
  refine Eq.trans ?_ (h.trans ?_)
  · unfold nm
    refine congrArg List.prod (List.map_congr_left fun m _ => ?_)
    rw [Function.comp_apply, ← sigmaGL_pow]
    refine Units.ext (Matrix.ext fun a b => ?_)
    exact sigLoc_pow σ v m _
  · refine Units.ext (Matrix.ext fun a b => ?_)
    exact (IsScalarTower.algebraMap_apply F E (CompletionsOver E v) _).symm.trans
      (IsScalarTower.algebraMap_apply F (v.adicCompletion F) (CompletionsOver E v) _)

/- English proof (translation)
Unfold `cp`. Rewrite using `[← Matrix.charpoly_map]`. Both sides reduce to the same expression.
-/
private theorem cp_map {S R : Type} [CommRing S] [CommRing R] {n : ℕ} (j : S →+* R) (g : GL (Fin n) S) :
    cp (mapGL n j g) = (g : Matrix (Fin n) (Fin n) S).charpoly.map j := by
  unfold cp
  rw [← Matrix.charpoly_map]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, by rw [← map_inv]; exact h'⟩`.
-/
private theorem intGL_map {S R : Type} [CommRing S] [CommRing R] {n : ℕ} (j : S →+* R) (T : Subring R)
    (g : GL (Fin n) S) (h : ∀ a b, j (g a b) ∈ T) (h' : ∀ a b, j ((g⁻¹ : GL (Fin n) S) a b) ∈ T) :
    IntGL T (mapGL n j g) :=
  ⟨h, by rw [← map_inv]; exact h'⟩

end Concrete

end UpperTheory.ConvolutionTheory.G

open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic GroundTheory.Automorphic.Reduction PositivityTheory.Rg.Tf.Loc ValuativeRel in
/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ hgen n _ δ γ hγ hN`. Establish `hG` using `galField F E σ hgen`. Take `⟨s, x, y, hxy⟩` from `hG.sep`. Take `⟨u, w, huw⟩` from `hγ`. Use `filter_upwards [Filter.eventually_all.2 fun i => ev_over (F := F) (x i), Filter.eventually_all.2 fun i => ev_over (F := F) (y i), Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_over (F := F) (δ i j), Filter.eventually_all.2 fun i => Filter.eventually_all.2 f …`.

Establish `hσ : IsGal (sigLoc σ v) (Module.finrank F E)` using `isGal_equiv (tensorEquiv E v) (galExt F E _ σ _ hG)`. Establish `e1 : mapGL n (atFin v) (AdelicGLn.diagonal E n δ) = mapGL n (algebraMap E (CompletionsOver E v)) δ` using `Units.ext (Matrix.ext fun _ _ => rfl)`. Establish `e2 : finAt v (AdelicGLn.diagonal F n γ) = mapGL n (algebraMap F (v.adicCompletion F)) γ` using `Units.ext (Matrix.ext fun _ _ => rfl)`. Establish `e3 : mapGL n (galFin σ v) = sg (sigLoc σ v)` using `by rw [galFin_eq, sg]`. Establish `e4 : mapGL n (incFin E v) = up (k` using `v.adicCompletion F) (CompletionsOver E v) := by`.

Rewrite using `[up]`. Conclude with `congrArg (mapGL n) (RingHom.ext fun _ => rfl)`. Establish `key` using `abstract_hilbert90 (sigLoc σ v) _ hσ 𝒪[v.adicCompletion F] (intOver E v) (alg_mem hσ.inj) (sigLoc_mem σ v) ⟨s, fun i => algebraMap E _ (x i), fun i => algebraMap E _ (y i), fun i => ⟨hx i, hy i⟩, fun j hj => by`. Simplify using `only [sigLoc_pow, ← map_mul, ← map_sum, hxy j hj]`. Apply the tactic sequence `split_ifs <;> simp⟩ _ _`.

Use the proof step `(intGL_map _ _ δ hδ hδ') (intGL_map _ _ γ hγ hγ') ⟨_, _, hu, hw, by`. Rewrite using `[cp_map, derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, huw, Polynomial.map_one]⟩ (nm_loc σ v δ γ hN) z`. Rewrite `key` using `[sgConj]`. Rewrite using `[e1, e2, e3, e4]`. Simplify using `only [mem_unitSet]`.

Conclude with `key`.
-/
theorem UpperTheory.ConvolutionTheory.G.firstCohomologyBound_of_boundaryBound :
    K1 := by
  intro F E _ _ _ _ _ _ σ hgen n _ δ γ hγ hN
  have hG := galField F E σ hgen
  obtain ⟨s, x, y, hxy⟩ := hG.sep
  obtain ⟨u, w, huw⟩ := hγ
  filter_upwards [Filter.eventually_all.2 fun i => ev_over (F := F) (x i),
    Filter.eventually_all.2 fun i => ev_over (F := F) (y i),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_over (F := F) (δ i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_over (F := F) ((δ⁻¹ : GL (Fin n) E) i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_elt (γ i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_elt ((γ⁻¹ : GL (Fin n) F) i j),
    ev_poly u, ev_poly w] with v hx hy hδ hδ' hγ hγ' hu hw z
  have hσ : IsGal (sigLoc σ v) (Module.finrank F E) :=
    isGal_equiv (tensorEquiv E v) (galExt F E _ σ _ hG)
  have e1 : mapGL n (atFin v) (AdelicGLn.diagonal E n δ) = mapGL n (algebraMap E (CompletionsOver E v)) δ :=
    Units.ext (Matrix.ext fun _ _ => rfl)
  have e2 : finAt v (AdelicGLn.diagonal F n γ) = mapGL n (algebraMap F (v.adicCompletion F)) γ :=
    Units.ext (Matrix.ext fun _ _ => rfl)
  have e3 : mapGL n (galFin σ v) = sg (sigLoc σ v) := by rw [galFin_eq, sg]
  have e4 : mapGL n (incFin E v) = up (k := v.adicCompletion F) (CompletionsOver E v) := by
    rw [up]
    exact congrArg (mapGL n) (RingHom.ext fun _ => rfl)
  have key := abstract_hilbert90 (sigLoc σ v) _ hσ 𝒪[v.adicCompletion F] (intOver E v) (alg_mem hσ.inj) (sigLoc_mem σ v)
    ⟨s, fun i => algebraMap E _ (x i), fun i => algebraMap E _ (y i), fun i => ⟨hx i, hy i⟩, fun j hj => by
      simp only [sigLoc_pow, ← map_mul, ← map_sum, hxy j hj]
      split_ifs <;> simp⟩ _ _
    (intGL_map _ _ δ hδ hδ') (intGL_map _ _ γ hγ hγ') ⟨_, _, hu, hw, by
      rw [cp_map, derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, huw,
        Polynomial.map_one]⟩ (nm_loc σ v δ γ hN) z
  rw [sgConj] at key
  rw [e1, e2, e3, e4]
  simp only [mem_unitSet]
  exact key
