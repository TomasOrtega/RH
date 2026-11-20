import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAugmentationTheoremStatement

noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR.Av

section Zp

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]

def zmodTo (n : ℕ) : ZMod (p ^ n) →+* R ⧸ (Ideal.span {(p : R)}) ^ n :=
  (Ideal.Quotient.lift (Ideal.span {((p ^ n : ℕ) : ℤ)})
    (Int.castRingHom (R ⧸ (Ideal.span {(p : R)}) ^ n)) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
      have h0 : ((p : R) ^ n) ∈ (Ideal.span {(p : R)}) ^ n :=
        Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n
      have h1 : (Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ n)) ((p : R) ^ n) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 h0
      have h2 : (((p ^ n : ℕ) : ℤ) : R ⧸ (Ideal.span {(p : R)}) ^ n) = 0 := by
        rw [← h1]; simp
      simp only [Int.coe_castRingHom, Int.cast_mul, h2, zero_mul])).comp (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom

def zpLift (hc : IsAdicComplete (Ideal.span {(p : R)}) R) : ℤ_[p] →+* R :=
  IsAdicComplete.liftRingHom (Ideal.span {(p : R)})
    (fun n => (zmodTo p R n).comp (PadicInt.toZModPow n)) (by
      intro m n hle
      rw [← RingHom.comp_assoc, ← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc]
      congr 1
      exact RingHom.ext_zmod _ _)

end Zp

section Tr

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {X N : Type} [AddCommGroup X] [AddCommGroup N] (e : N ≃+ X)

abbrev trL (R C : Type) [Field C] [CommRing R] [Algebra R C] {X N : Type} [AddCommGroup X]
    [AddCommGroup N] (e : N ≃+ X) : (X → C) ≃ₗ[R] (N → C) :=
  LinearEquiv.funCongrLeft R C e.toEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trL_apply (f : X → C) : trL R C e f = f ∘ e := rfl

include e in
/- English proof (translation)
Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem comp_symm (f : N → C) : (f ∘ e.symm) ∘ e = f := by
  ext x; simp

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl⟩`. Conclude with `(h f).1 hf`. Introduce `hg`.

Conclude with `⟨g ∘ e.symm, (h _).2 (by rwa [comp_symm]), comp_symm e g⟩`.
-/
theorem map_trL {A : Submodule R (X → C)} {B : Submodule R (N → C)}
    (h : ∀ f, f ∈ A ↔ f ∘ e ∈ B) : A.map (trL R C e : (X → C) →ₗ[R] (N → C)) = B := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (h f).1 hf
  · intro hg
    exact ⟨g ∘ e.symm, (h _).2 (by rwa [comp_symm]), comp_symm e g⟩

/- English proof (translation)
Substitute `h` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Conclude with `⟨f, hf, rfl⟩`. Introduce and unpack `⟨f', hf', h'⟩`.

Establish `: f' = f` using `(trL R C e).injective h'`. Rewrite using `[← this]` and apply the resulting hypothesis.
-/
theorem iff_of_map {A : Submodule R (X → C)} {B : Submodule R (N → C)}
    (h : A.map (trL R C e : (X → C) →ₗ[R] (N → C)) = B) (f : X → C) : f ∈ A ↔ f ∘ e ∈ B := by
  subst h
  constructor
  · intro hf
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f', hf', h'⟩
    have : f' = f := (trL R C e).injective h'
    rwa [← this]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x`. Conclude with `h (e x)`. Introduce `h x`. Take `⟨r, hr⟩` from `h (e.symm x)`.

Conclude with `⟨r, by simpa using hr⟩`.
-/
theorem intFun_iff (f : X → C) : f ∈ intFun (C := C) R X ↔ f ∘ e ∈ intFun (C := C) R N := by
  constructor
  · intro h x
    exact h (e x)
  · intro h x
    obtain ⟨r, hr⟩ := h (e.symm x)
    exact ⟨r, by simpa using hr⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x y`. Simplify using `using h (e x) (e y)`. Introduce `h x y`. Simplify using `using h (e.symm x) (e.symm y)`.
-/
theorem addFun_iff (p : ℕ) (f : X → C) : f ∈ addFun (C := C) R p X ↔ f ∘ e ∈ addFun (C := C) R p N := by
  constructor
  · intro h x y
    simpa using h (e x) (e y)
  · intro h x y
    simpa using h (e.symm x) (e.symm y)

/- English proof (translation)
The claim follows from `and_congr (intFun_iff e f) (addFun_iff e p f)`.
-/
theorem linFun_iff (p : ℕ) (f : X → C) :
    f ∈ linFun (C := C) R p X ↔ f ∘ e ∈ linFun (C := C) R p N :=
  and_congr (intFun_iff e f) (addFun_iff e p f)

/- English proof (translation)
Simplify using `only [pFun, Submodule.mem_pi, Set.mem_univ, true_imp_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Conclude with `h (e x)`. Introduce `h x`.

Simplify using `using h (e.symm x)`.
-/
theorem pFun_iff (p : ℕ) (f : X → C) : f ∈ pFun (C := C) R p X ↔ f ∘ e ∈ pFun (C := C) R p N := by
  simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  constructor
  · intro h x
    exact h (e x)
  · intro h x
    simpa using h (e.symm x)

variable {M : Submodule R (X → C)} {M' : Submodule R (N → C)}

/- English proof (translation)
The claim follows from `and_congr (h f) (addFun_iff e p f)`.
-/
theorem afFun_iff (h : ∀ f, f ∈ M ↔ f ∘ e ∈ M') (p : ℕ) (f : X → C) :
    f ∈ afFun p M ↔ f ∘ e ∈ afFun p M' :=
  and_congr (h f) (addFun_iff e p f)

/- English proof (translation)
Use `iff_of_map e ?_ f` and prove the remaining obligations. Rewrite using `[Submodule.map_sup, map_trL e (afFun_iff e h p), map_trL e (pFun_iff e p)]`.
-/
theorem afp_iff (h : ∀ f, f ∈ M ↔ f ∘ e ∈ M') (p : ℕ) (f : X → C) :
    f ∈ afFun p M ⊔ pFun (C := C) R p X ↔ f ∘ e ∈ afFun p M' ⊔ pFun (C := C) R p N := by
  refine iff_of_map e ?_ f
  rw [Submodule.map_sup, map_trL e (afFun_iff e h p), map_trL e (pFun_iff e p)]

/- English proof (translation)
Use `and_congr (h f) ?_` and prove the remaining obligations. Simplify using `[LinearMap.mem_ker]`.
-/
theorem augIdeal_iff (h : ∀ f, f ∈ M ↔ f ∘ e ∈ M') (f : X → C) :
    f ∈ augIdeal M ↔ f ∘ e ∈ augIdeal M' := by
  refine and_congr (h f) ?_
  simp [LinearMap.mem_ker]

/- English proof (translation)
Use `iff_of_map e ?_ f` and prove the remaining obligations. Rewrite using `[sqIdeal, sqIdeal, Submodule.map_span]`. Use `congr 1`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩`. Conclude with `⟨a ∘ e, (h a).1 ha, b ∘ e, (h b).1 hb, rfl⟩`. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Use `⟨(a ∘ e.symm) * (b ∘ e.symm), ⟨_, (h _).2 (by rwa [comp_symm]), _, (h _).2 (by rwa [comp_symm]), rfl⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Simplify using `[trL_apply]`.
-/
theorem sqIdeal_iff {I : Submodule R (X → C)} {I' : Submodule R (N → C)}
    (h : ∀ f, f ∈ I ↔ f ∘ e ∈ I') (f : X → C) : f ∈ sqIdeal I ↔ f ∘ e ∈ sqIdeal I' := by
  refine iff_of_map e ?_ f
  rw [sqIdeal, sqIdeal, Submodule.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨a ∘ e, (h a).1 ha, b ∘ e, (h b).1 hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨(a ∘ e.symm) * (b ∘ e.symm), ⟨_, (h _).2 (by rwa [comp_symm]), _,
      (h _).2 (by rwa [comp_symm]), rfl⟩, ?_⟩
    ext x
    simp [trL_apply]

def quotTr {A A₁ : Submodule R (X → C)} {B B₁ : Submodule R (N → C)}
    (hA : ∀ f, f ∈ A ↔ f ∘ e ∈ B) (hA₁ : ∀ f, f ∈ A₁ ↔ f ∘ e ∈ B₁) :
    (A ⧸ A₁.comap A.subtype) ≃ₗ[R] (B ⧸ B₁.comap B.subtype) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofSubmodules (trL R C e) A B (map_trL e hA)) (by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨⟨x, hx⟩, hxP, hxy⟩
      have h1 : x ∘ e = y := congrArg Subtype.val hxy
      show y ∈ B₁
      rw [← h1]
      exact (hA₁ x).1 hxP
    · intro hy1
      have hy1' : y ∈ B₁ := hy1
      refine ⟨⟨y ∘ e.symm, (hA _).2 (by rwa [comp_symm])⟩, ?_, Subtype.ext (comp_symm e y)⟩
      show y ∘ e.symm ∈ A₁
      exact (hA₁ _).2 (by rwa [comp_symm]))

/- English proof (translation)
Take `⟨B, hB, hv⟩` from `hc`. Use `⟨B.submatrix e e, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_trL e h, hB, Submodule.map_span]`. Use `congr 1`. Use extensionality with `g`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨j, rfl⟩, rfl⟩`. Conclude with `⟨e.symm j, by ext x; simp [trL_apply]⟩`. Introduce and unpack `⟨j, rfl⟩`. Conclude with `⟨_, ⟨e j, rfl⟩, by ext x; simp [trL_apply]⟩`.

Rewrite using `[show B.submatrix e e = B.submatrix e.toEquiv e.toEquiv from rfl, Matrix.det_submatrix_equiv_self, hv]`.
-/
theorem hasColen_tr [Fintype X] [DecidableEq X] [Fintype N] [DecidableEq N]
    (v : Valuation C NNReal) (h : ∀ f, f ∈ M ↔ f ∘ e ∈ M') {c : NNReal}
    (hc : HasColen R v M c) : HasColen R v M' c := by
  obtain ⟨B, hB, hv⟩ := hc
  refine ⟨B.submatrix e e, ?_, ?_⟩
  · rw [← map_trL e h, hB, Submodule.map_span]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨e.symm j, by ext x; simp [trL_apply]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨e j, rfl⟩, by ext x; simp [trL_apply]⟩
  · rw [show B.submatrix e e = B.submatrix e.toEquiv e.toEquiv from rfl,
      Matrix.det_submatrix_equiv_self, hv]

def trA (R C : Type) [Field C] [CommRing R] [Algebra R C] {X N : Type} [AddCommGroup X]
    [AddCommGroup N] (e : N ≃+ X) : (X → C) →ₐ[R] (N → C) where
  toFun f := f ∘ e
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.1`. Introduce `h`. Use `⟨h, fun x k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.mem_bot.1 hk, add_zero]`.
-/
theorem invFun_bot (f : X → C) : f ∈ invFun M ⊥ ↔ f ∈ M := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun x k hk => ?_⟩
    rw [AddSubgroup.mem_bot.1 hk, add_zero]

/- English proof (translation)
Establish `hinv : ∀ f, f ∈ invFun M ⊥ ↔ f ∘ e ∈ invFun M' ⊥` using `fun f => by`. Rewrite using `[invFun_bot, invFun_bot]`. Conclude with `h f`. Introduce `f hf`. Establish `h1 : f ∘ e.symm ∈ invFun M ⊥` using `(hinv _).2 (by rwa [comp_symm])`.

Establish `h2` using `hG h1`. Establish `h3 : trA R C e (f ∘ e.symm) ∈ (Algebra.adjoin R ((afFun p (invFun M ⊥) : Submodule R (X → C)) : Set (X → C))).map (trA R C e)` using `⟨_, h2, rfl⟩`. Rewrite `h3` using `[AlgHom.map_adjoin]`. Establish `h4 : trA R C e (f ∘ e.symm) = f` using `comp_symm e f`. Rewrite `h3` using `[h4]`.

Use `Algebra.adjoin_mono ?_ h3` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `(afFun_iff e hinv p a).1 ha`.
-/
theorem genAF_tr (h : ∀ f, f ∈ M ↔ f ∘ e ∈ M') (p : ℕ) (hG : GenAF p M ⊥) : GenAF p M' ⊥ := by
  have hinv : ∀ f, f ∈ invFun M ⊥ ↔ f ∘ e ∈ invFun M' ⊥ := fun f => by
    rw [invFun_bot, invFun_bot]; exact h f
  intro f hf
  have h1 : f ∘ e.symm ∈ invFun M ⊥ := (hinv _).2 (by rwa [comp_symm])
  have h2 := hG h1
  have h3 : trA R C e (f ∘ e.symm) ∈ (Algebra.adjoin R
      ((afFun p (invFun M ⊥) : Submodule R (X → C)) : Set (X → C))).map (trA R C e) :=
    ⟨_, h2, rfl⟩
  rw [AlgHom.map_adjoin] at h3
  have h4 : trA R C e (f ∘ e.symm) = f := comp_symm e f
  rw [h4] at h3
  refine Algebra.adjoin_mono ?_ h3
  rintro _ ⟨a, ha, rfl⟩
  exact (afFun_iff e hinv p a).1 ha

/- English proof (translation)
Take `⟨cA, cN, cO, hA, hN, hO, h1, h2⟩` from `hT`. Establish `hcard : Fintype.card N = Fintype.card X` using `Fintype.card_congr e.toEquiv`. Use `⟨cA, cN, cO, ?_, hasColen_tr e v h hN, ?_, by rwa [hcard], by rwa [hcard]⟩` and prove the remaining obligations. Take `⟨m, c, ⟨f⟩, hx⟩` from `hA`. Conclude with `⟨m, c, ⟨(quotTr e (linFun_iff e p) (afp_iff e h p)).symm.trans f⟩, hx⟩`.

Take `⟨m, c, ⟨f⟩, hx⟩` from `hO`. Conclude with `⟨m, c, ⟨(quotTr e (augIdeal_iff e h) (sqIdeal_iff e (augIdeal_iff e h))).symm.trans f⟩, hx⟩`.
-/
theorem isTight_tr [Fintype X] [DecidableEq X] [Fintype N] [DecidableEq N]
    (v : Valuation C NNReal) (h : ∀ f, f ∈ M ↔ f ∘ e ∈ M') (p : ℕ) (hT : IsTight v p M) :
    IsTight v p M' := by
  obtain ⟨cA, cN, cO, hA, hN, hO, h1, h2⟩ := hT
  have hcard : Fintype.card N = Fintype.card X := Fintype.card_congr e.toEquiv
  refine ⟨cA, cN, cO, ?_, hasColen_tr e v h hN, ?_, by rwa [hcard], by rwa [hcard]⟩
  · obtain ⟨m, c, ⟨f⟩, hx⟩ := hA
    exact ⟨m, c, ⟨(quotTr e (linFun_iff e p) (afp_iff e h p)).symm.trans f⟩, hx⟩
  · obtain ⟨m, c, ⟨f⟩, hx⟩ := hO
    exact ⟨m, c, ⟨(quotTr e (augIdeal_iff e h) (sqIdeal_iff e (augIdeal_iff e h))).symm.trans f⟩, hx⟩

end Tr

section Pts

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {p : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Use `⟨a, fun x φ hφ => ha (e x) φ ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, hpt]`. Introduce and unpack `⟨a, ha⟩`.

Use `⟨a, fun y φ hφ => ?_⟩` and prove the remaining obligations. Use `ha (e.symm y) φ (by rw [hφ, ← hpt]; simp)` as an intermediate fact. Simplify using `using this`.
-/
theorem tors_iff (C : Type) [Field C] [Algebra R C] (T : TorsRep G p) {X N : Type}
    (e : N ≃ X) {pt₀ : X → (sp (R₀ := R) R ⟶ G)} {pt : N → (sp (R₀ := R) R ⟶ G)}
    (hpt : ∀ x, pt₀ (e x) = pt x) (f : X → C) :
    f ∈ torsFun C T pt₀ ↔ f ∘ e ∈ torsFun C T pt := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun x φ hφ => ha (e x) φ ?_⟩
    rw [hφ, hpt]
  · rintro ⟨a, ha⟩
    refine ⟨a, fun y φ hφ => ?_⟩
    have := ha (e.symm y) φ (by rw [hφ, ← hpt]; simp)
    simpa using this

/- English proof (translation)
Use `choose f hf using fun x => (h₀.range (pt x)).1 ((h.range _).2 ⟨x, rfl⟩)`. Use `choose f' hf' using fun y => (h.range (pt₀ y)).1 ((h₀.range _).2 ⟨y, rfl⟩)`. Conclude with `⟨{ toFun := f invFun := f' left_inv := fun x => h.inj (by rw [hf', hf]) right_inv := fun y => h₀.inj (by rw [hf, hf']) map_add' := fun x y => h₀.inj (by rw [hf, h₀.add, hf, hf, h.add]) }, hf⟩`.
-/
theorem exists_addEquiv {X N : Type} [AddCommGroup X] [AddCommGroup N]
    {pt₀ : X → (sp (R₀ := R) R ⟶ G)} {pt : N → (sp (R₀ := R) R ⟶ G)}
    (h₀ : IsTorsPts G p pt₀) (h : IsTorsPts G p pt) :
    ∃ e : N ≃+ X, ∀ x, pt₀ (e x) = pt x := by
  choose f hf using fun x => (h₀.range (pt x)).1 ((h.range _).2 ⟨x, rfl⟩)
  choose f' hf' using fun y => (h.range (pt₀ y)).1 ((h₀.range _).2 ⟨y, rfl⟩)
  exact ⟨{ toFun := f
           invFun := f'
           left_inv := fun x => h.inj (by rw [hf', hf])
           right_inv := fun y => h₀.inj (by rw [hf, hf'])
           map_add' := fun x y => h₀.inj (by rw [hf, h₀.add, hf, hf, h.add]) }, hf⟩

end Pts

end GlobalTheory.CompanionTheory.Ar.GR.Av

namespace GlobalTheory.CompanionTheory.Ar.GR

/- English proof (translation)
Introduce `hHT p _ C _ _ _ v R _ _ hint hp hc P T N _ _ _ pt hpt`. Use `letI : Algebra ℤ_[p] R := (Av.zpLift p R hc).toAlgebra`. Take `⟨-, cp, US, H, pt₀, h₀, hT⟩` from `hHT p C v R hint hp hc P`. Take `⟨e, he⟩` from `Av.exists_addEquiv h₀ hpt`. Establish `key` using `GlobalTheory.T.polarised_augmentation_theorem p P.g C v R ℤ_[p] AlgEquiv.refl cp US H`.

Simplify using `only at key`. Take `⟨-, -, -, -, -, -, -, hG, hTi⟩` from `key`. Rewrite `hG`, `hTi` using `[hT T]`. Establish `hiff` using `Av.tors_iff C T e.toEquiv he`. Conclude with `⟨Av.genAF_tr e hiff p hG, Av.isTight_tr e v hiff p hTi⟩`.
-/
theorem gp_polAV : HodgeTateDatumStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R →
    ∀ (P : Out.PolAV (Spec (CommRingCat.of R))), ∀ (T : TorsRep P.A p) (N : Type) [AddCommGroup N]
      [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ P.A)), IsTorsPts P.A p pt →
      GenAF p (torsFun C T pt) ⊥ ∧ IsTight v p (torsFun C T pt) := by
  intro hHT p _ C _ _ _ v R _ _ hint hp hc P T N _ _ _ pt hpt
  letI : Algebra ℤ_[p] R := (Av.zpLift p R hc).toAlgebra
  obtain ⟨-, cp, US, H, pt₀, h₀, hT⟩ := hHT p C v R hint hp hc P
  obtain ⟨e, he⟩ := Av.exists_addEquiv h₀ hpt
  have key := GlobalTheory.T.polarised_augmentation_theorem p P.g C v R ℤ_[p] AlgEquiv.refl cp US H
  dsimp only at key
  obtain ⟨-, -, -, -, -, -, -, hG, hTi⟩ := key
  rw [hT T] at hG hTi
  have hiff := Av.tors_iff C T e.toEquiv he
  exact ⟨Av.genAF_tr e hiff p hG, Av.isTight_tr e v hiff p hTi⟩

end GlobalTheory.CompanionTheory.Ar.GR
