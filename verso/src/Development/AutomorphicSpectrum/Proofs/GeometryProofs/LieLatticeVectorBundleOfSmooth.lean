import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOnDualAndBidual

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

section Alg

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {g : ℕ}

def IsCoord (d : Fin g → Derivation A B B) (w : Fin g → B →₀ B) : Prop :=
  (∀ i k, (w i).sum (fun b a => a * d k b) = if k = i then 1 else 0) ∧
  ∀ (T M : Type) [CommRing T] [AddCommGroup M] [Module T M] (ε : B →+* T) (δ : B →+ M),
    (∀ a b, δ (a * b) = ε a • δ b + ε b • δ a) → (∀ a, δ (algebraMap A B a) = 0) →
    ∀ b, δ b = ∑ k, ε (d k b) • (w k).sum (fun b' a => ε a • δ b')

/- English proof (translation)
Establish `hw : ∀ i, ∃ w : B →₀ B, (w.sum fun b a => a • KaehlerDifferential.D A B b) = c i`. Introduce `i`. Establish `: c i ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B))`. Rewrite using `[KaehlerDifferential.span_range_derivation]`. Discharge the goal by the elementary cases of `trivial`.

Conclude with `(Finsupp.mem_span_range_iff_exists_finsupp).1 this`. Use `choose w hw using hw`. Use `⟨fun k => (c.coord k).compDer (KaehlerDifferential.D A B), w, ?_, ?_⟩` and prove the remaining obligations. Introduce `i k`. Use `congrArg (c.coord k) (hw i)` as an intermediate fact.

Rewrite `this` using `[Finsupp.sum, map_sum]`. Rewrite using `[Finsupp.sum]`. Simplify using `only [map_smul, smul_eq_mul] at this`. Use `Eq.trans (Finset.sum_congr rfl fun x _ => rfl) (this.trans ?_)` and prove the remaining obligations. Simplify using `[Finsupp.single_apply, eq_comm]`.

Introduce `T M _ _ _ ε δ hL hA b`. Use `letI : Module B M := Module.compHom M ε`. Use `letI : Module A M := Module.compHom M (ε.comp (algebraMap A B))`. Use `haveI : IsScalarTower A B M := ⟨fun a b m => by`. Express the relevant statement in the definitionally equal form `ε (a • b) • m = ε (algebraMap A B a) • ε b • m`.

Rewrite using `[Algebra.smul_def, map_mul, mul_smul]⟩`. Set `δl : B →ₗ[A] M` to `{ toFun := δ map_add' := δ.map_add map_smul' := fun a b => by`. Express the relevant statement in the definitionally equal form `δ (a • b) = ε (algebraMap A B a) • δ b`. Rewrite using `[Algebra.smul_def, hL, hA, smul_zero, add_zero] }`. Set `δ' : Derivation A B M` to `Derivation.mk' δl (fun a b => hL a b)`.

Set `L` to `δ'.liftKaehlerDifferential`. Establish `hLD : ∀ b, L (KaehlerDifferential.D A B b) = δ b` using `fun b => by`. Simplify using `[L, δ', δl]`. Establish `hc : ∀ k, L (c k) = (w k).sum (fun b' a => ε a • δ b')`. Introduce `k`.

Rewrite using `[← hw k, Finsupp.sum, map_sum, Finsupp.sum]`. Use `Finset.sum_congr rfl fun b' _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hLD]`. Both sides reduce to the same expression. Rewrite using `[← hLD b]`.

Use `conv_lhs => rw [← c.sum_repr (KaehlerDifferential.D A B b)]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hc]`. Both sides reduce to the same expression.
-/
theorem exists_isCoord (c : Module.Basis (Fin g) B Ω[B⁄A]) :
    ∃ (d : Fin g → Derivation A B B) (w : Fin g → B →₀ B), IsCoord d w := by
  have hw : ∀ i, ∃ w : B →₀ B, (w.sum fun b a => a • KaehlerDifferential.D A B b) = c i := by
    intro i
    have : c i ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    exact (Finsupp.mem_span_range_iff_exists_finsupp).1 this
  choose w hw using hw
  refine ⟨fun k => (c.coord k).compDer (KaehlerDifferential.D A B), w, ?_, ?_⟩
  · intro i k
    have := congrArg (c.coord k) (hw i)
    rw [Finsupp.sum, map_sum] at this
    rw [Finsupp.sum]
    simp only [map_smul, smul_eq_mul] at this
    refine Eq.trans (Finset.sum_congr rfl fun x _ => rfl) (this.trans ?_)
    simp [Finsupp.single_apply, eq_comm]
  · intro T M _ _ _ ε δ hL hA b
    letI : Module B M := Module.compHom M ε
    letI : Module A M := Module.compHom M (ε.comp (algebraMap A B))
    haveI : IsScalarTower A B M := ⟨fun a b m => by
      change ε (a • b) • m = ε (algebraMap A B a) • ε b • m
      rw [Algebra.smul_def, map_mul, mul_smul]⟩
    let δl : B →ₗ[A] M :=
      { toFun := δ
        map_add' := δ.map_add
        map_smul' := fun a b => by
          change δ (a • b) = ε (algebraMap A B a) • δ b
          rw [Algebra.smul_def, hL, hA, smul_zero, add_zero] }
    let δ' : Derivation A B M := Derivation.mk' δl (fun a b => hL a b)
    let L := δ'.liftKaehlerDifferential
    have hLD : ∀ b, L (KaehlerDifferential.D A B b) = δ b := fun b => by
      simp [L, δ', δl]
    have hc : ∀ k, L (c k) = (w k).sum (fun b' a => ε a • δ b') := by
      intro k
      rw [← hw k, Finsupp.sum, map_sum, Finsupp.sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [map_smul, hLD]
      rfl
    rw [← hLD b]
    conv_lhs => rw [← c.sum_repr (KaehlerDifferential.D A B b)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hc]
    rfl

end Alg

section Rep

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {T T' : Type} [CommRing T] [CommRing T']
  {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  {J : Spec (CommRingCat.of B) ⟶ G.left} [IsOpenImmersion J]
  {J₀ : Spec (CommRingCat.of A) ⟶ X} [IsOpenImmersion J₀]
  {x : Spec (CommRingCat.of T) ⟶ X} {ε : B →+* T}
  {M N : Type} [AddCommGroup M] [Module T M] [Module Tᵐᵒᵖ M] [IsCentralScalar T M]
  [AddCommGroup N] [Module T N] [Module Tᵐᵒᵖ N] [IsCentralScalar T N]

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spec_comp' {P Q R : Type} [CommRing P] [CommRing Q] [CommRing R] (f : P →+* Q) (g : Q →+* R) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Use `Spec.map_injective ((cancel_mono K).1 h)` as an intermediate fact. Conclude with `CommRingCat.hom_ext_iff.1 this |> fun e => by simpa using e`.
-/
theorem spec_cancel {P Q : Type} [CommRing P] [CommRing Q] {Z : Scheme.{0}} (K : Spec (CommRingCat.of P) ⟶ Z)
    [Mono K] {φ ψ : P →+* Q}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ K = Spec.map (CommRingCat.ofHom ψ) ≫ K) : φ = ψ := by
  have := Spec.map_injective ((cancel_mono K).1 h)
  exact CommRingCat.hom_ext_iff.1 this |> fun e => by simpa using e

/- English proof (translation)
Introduce `p`. Set `q : PrimeSpectrum T` to `PrimeSpectrum.comap (algebraMap T (TrivSqZeroExt T M)) p`. Use `⟨q, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap T (TrivSqZeroExt T M) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal`. Use `set b := algebraMap T (TrivSqZeroExt T M) a.fst with hb`.

Establish `h0 : (b - a).fst = 0` using `by simp [hb, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hm : b - a ∈ p.asIdeal`. Use `p.isPrime.mem_of_pow_mem 2 ?_` and prove the remaining obligations. Establish `: (b - a) ^ 2 = 0`. Rewrite using `[pow_two]`.

Apply the tactic sequence `ext1 <;> simp [h0]`. Rewrite using `[this]`. Conclude with `zero_mem _`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Simplify using `using p.asIdeal.sub_mem h hm`. Introduce `h`. Simplify using `using p.asIdeal.add_mem hm h`.
-/
theorem surj_fst :
    Function.Surjective (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T T M).toRingHom)) := by
  intro p
  let q : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T (TrivSqZeroExt T M)) p
  refine ⟨q, PrimeSpectrum.ext (Ideal.ext fun a =>  ?_)⟩
  change algebraMap T (TrivSqZeroExt T M) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal
  set b := algebraMap T (TrivSqZeroExt T M) a.fst with hb
  have h0 : (b - a).fst = 0 := by simp [hb, TrivSqZeroExt.algebraMap_eq_inl]
  have hm : b - a ∈ p.asIdeal := by
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : (b - a) ^ 2 = 0 := by
      rw [pow_two]
      ext1 <;> simp [h0]
    rw [this]; exact zero_mem _
  constructor
  · intro h; simpa using p.asIdeal.sub_mem h hm
  · intro h; simpa using p.asIdeal.add_mem hm h

variable (J J₀) in

def IsChart : Prop := J ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ J₀

variable (J x ε) in

def IsUnitIn : Prop := Spec.map (CommRingCat.ofHom ε) ≫ J = (1 : Over.mk x ⟶ G).left

variable (A ε) in

def Lifts (f : B →+* TrivSqZeroExt T M) : Prop :=
  (∀ b, (f b).fst = ε b) ∧ ∀ a, (f (algebraMap A B a)).snd = 0

/- English proof (translation)
Rewrite using `[← Category.assoc, hε]`. Conclude with `(Over.w (1 : Over.mk x ⟶ G)).symm`.
-/
theorem point_eq (hε : IsUnitIn J x ε) : x = Spec.map (CommRingCat.ofHom ε) ≫ J ≫ G.hom := by
  rw [← Category.assoc, hε]
  exact (Over.w (1 : Over.mk x ⟶ G)).symm

/- English proof (translation)
Rewrite using `[← spec_comp', Category.assoc, ← hc]`. Conclude with `point_eq hε`.
-/
theorem point_eq' (hc : IsChart J J₀) (hε : IsUnitIn J x ε) :
    x = Spec.map (CommRingCat.ofHom (ε.comp (algebraMap A B))) ≫ J₀ := by
  rw [← spec_comp', Category.assoc, ← hc]
  exact point_eq hε

/- English proof (translation)
Establish `e : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T T M).toRingHom) ≫ u.left = Spec.map (CommRingCat.ofHom ε) ≫ J`. Rewrite using `[hε]`. Conclude with `congrArg (fun k : Over.mk x ⟶ G => k.left) hu`. Establish `hr : Set.range u.left ⊆ Set.range J`. Introduce and unpack `_ ⟨y, rfl⟩`.

Take `⟨z, rfl⟩` from `surj_fst (M := M) y`. Use `⟨Spec.map (CommRingCat.ofHom ε) z, ?_⟩` and prove the remaining obligations. Use `congrArg (fun k : Spec (CommRingCat.of T) ⟶ G.left => k z) e` as an intermediate fact. Simplify using `using this.symm`. Establish `hL` using `IsOpenImmersion.lift_fac J u.left hr`.

Take `⟨f, hf⟩ : ∃ f : B →+* TrivSqZeroExt T M, Spec.map (CommRingCat.ofHom f) = IsOpenImmersion.lift J u.left hr` from `⟨(Spec.preimage (IsOpenImmersion.lift J u.left hr)).hom, by simpa using Spec.map_preimage _⟩`. Establish `hu' : u.left = Spec.map (CommRingCat.ofHom f) ≫ J` using `by rw [hf, hL]`. Use `⟨f, hu', ?_, ?_⟩` and prove the remaining obligations. Establish `: (TrivSqZeroExt.fstHom T T M).toRingHom.comp f = ε`. Apply `spec_cancel J` to reduce the goal to its premises.

Rewrite using `[← spec_comp', Category.assoc, ← hu', e]`. Conclude with `fun b => congrArg (fun k : B →+* T => k b) this`. Establish `: f.comp (algebraMap A B) = (algebraMap T (TrivSqZeroExt T M)).comp (ε.comp (algebraMap A B))`. Apply `spec_cancel J₀` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← spec_comp', Category.assoc]`. Use `_ = u.left ≫ G.hom := by rw [← hc, hu', Category.assoc]`. Use `_ = Spec.map (CommRingCat.ofHom (algebraMap T (TrivSqZeroExt T M))) ≫ x := Over.w u`. Use `_ = _ := by rw [point_eq' hc hε, ← Category.assoc, spec_comp']`. Introduce `a`.

Use `congrArg (fun k : A →+* TrivSqZeroExt T M => (k a).snd) this` as an intermediate fact. Simplify `this` using `[TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem exists_rep (hc : IsChart J J₀) (hε : IsUnitIn J x ε) (u : LieEx.ob x M ⟶ G)
    (hu : LieEx.zsec x ≫ u = 1) :
    ∃ f : B →+* TrivSqZeroExt T M, u.left = Spec.map (CommRingCat.ofHom f) ≫ J ∧ Lifts A ε f := by
  have e : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T T M).toRingHom) ≫ u.left =
      Spec.map (CommRingCat.ofHom ε) ≫ J := by
    rw [hε]
    exact congrArg (fun k : Over.mk x ⟶ G => k.left) hu
  have hr : Set.range u.left ⊆ Set.range J := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := surj_fst (M := M) y
    refine ⟨Spec.map (CommRingCat.ofHom ε) z, ?_⟩
    have := congrArg (fun k : Spec (CommRingCat.of T) ⟶ G.left => k z) e
    simpa using this.symm
  have hL := IsOpenImmersion.lift_fac J u.left hr
  obtain ⟨f, hf⟩ : ∃ f : B →+* TrivSqZeroExt T M, Spec.map (CommRingCat.ofHom f) =
      IsOpenImmersion.lift J u.left hr :=
    ⟨(Spec.preimage (IsOpenImmersion.lift J u.left hr)).hom, by simpa using Spec.map_preimage _⟩
  have hu' : u.left = Spec.map (CommRingCat.ofHom f) ≫ J := by rw [hf, hL]
  refine ⟨f, hu', ?_, ?_⟩
  · have : (TrivSqZeroExt.fstHom T T M).toRingHom.comp f = ε := by
      apply spec_cancel J
      rw [← spec_comp', Category.assoc, ← hu', e]
    exact fun b => congrArg (fun k : B →+* T => k b) this
  · have : f.comp (algebraMap A B) =
        (algebraMap T (TrivSqZeroExt T M)).comp (ε.comp (algebraMap A B)) := by
      apply spec_cancel J₀
      calc Spec.map (CommRingCat.ofHom (f.comp (algebraMap A B))) ≫ J₀
          = Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ J₀ := by
            rw [← spec_comp', Category.assoc]
        _ = u.left ≫ G.hom := by rw [← hc, hu', Category.assoc]
        _ = Spec.map (CommRingCat.ofHom (algebraMap T (TrivSqZeroExt T M))) ≫ x := Over.w u
        _ = _ := by rw [point_eq' hc hε, ← Category.assoc, spec_comp']
    intro a
    have := congrArg (fun k : A →+* TrivSqZeroExt T M => (k a).snd) this
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

/- English proof (translation)
Establish `h1 : (TrivSqZeroExt.fstHom T T M).toRingHom.comp f = ε` using `RingHom.ext hf.1`. Establish `h2 : f.comp (algebraMap A B) = (algebraMap T (TrivSqZeroExt T M)).comp (ε.comp (algebraMap A B))`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Use `ext`. Simplify `hf.1 _` using `[TrivSqZeroExt.algebraMap_eq_inl]`.

Simplify `hf.2 a` using `[TrivSqZeroExt.algebraMap_eq_inl]`. Use `⟨Over.homMk (Spec.map (CommRingCat.ofHom f) ≫ J) ?_, rfl, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Spec.map (CommRingCat.ofHom f) ≫ J) ≫ G.hom = Spec.map _ ≫ x`. Rewrite using `[Category.assoc, hc, ← Category.assoc, spec_comp', h2, point_eq' hc hε, ← Category.assoc, spec_comp']`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map (CommRingCat.ofHom f) ≫ J = _`. Rewrite using `[← Category.assoc, spec_comp', h1, hε]`.
-/
theorem mk_rep (hc : IsChart J J₀) (hε : IsUnitIn J x ε) (f : B →+* TrivSqZeroExt T M) (hf : Lifts A ε f) :
    ∃ u : LieEx.ob x M ⟶ G, u.left = Spec.map (CommRingCat.ofHom f) ≫ J ∧ LieEx.zsec x ≫ u = 1 := by
  have h1 : (TrivSqZeroExt.fstHom T T M).toRingHom.comp f = ε := RingHom.ext hf.1
  have h2 : f.comp (algebraMap A B) =
      (algebraMap T (TrivSqZeroExt T M)).comp (ε.comp (algebraMap A B)) := by
    refine RingHom.ext fun a => ?_
    ext
    · simpa [TrivSqZeroExt.algebraMap_eq_inl] using hf.1 _
    · simpa [TrivSqZeroExt.algebraMap_eq_inl] using hf.2 a
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom f) ≫ J) ?_, rfl, ?_⟩
  · change (Spec.map (CommRingCat.ofHom f) ≫ J) ≫ G.hom = Spec.map _ ≫ x
    rw [Category.assoc, hc, ← Category.assoc, spec_comp', h2, point_eq' hc hε, ← Category.assoc, spec_comp']
  · apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom f) ≫ J = _
    rw [← Category.assoc, spec_comp', h1, hε]

variable {g : ℕ} {d : Fin g → Derivation A B B} {w : Fin g → B →₀ B}

variable (ε w) in

def yco (δ : B → M) (i : Fin g) : M := (w i).sum fun b a => ε a • δ b

variable (A J ε w) in

def Co (v : LieEx.ob x M ⟶ G) (y : Fin g → M) : Prop :=
  ∃ f : B →+* TrivSqZeroExt T M, v.left = Spec.map (CommRingCat.ofHom f) ≫ J ∧ Lifts A ε f ∧
    ∀ i, y i = yco ε w (fun b => (f b).snd) i

/- English proof (translation)
The claim follows from `hd.2 T M ε (AddMonoidHom.mk' (fun b => (f b).snd) (fun a b => by simp)) (fun a b => by simp [map_mul, TrivSqZeroExt.snd_mul, hf.1]) hf.2 b`.
-/
theorem snd_formula (hd : IsCoord d w) (f : B →+* TrivSqZeroExt T M) (hf : Lifts A ε f) (b : B) :
    (f b).snd = ∑ k, ε (d k b) • yco ε w (fun b => (f b).snd) k :=
  hd.2 T M ε (AddMonoidHom.mk' (fun b => (f b).snd) (fun a b => by simp))
    (fun a b => by simp [map_mul, TrivSqZeroExt.snd_mul, hf.1]) hf.2 b

/- English proof (translation)
Take `⟨f, h, hf⟩` from `exists_rep hc hε v hv`. Conclude with `⟨_, f, h, hf, fun _ => rfl⟩`.
-/
theorem co_exists (hc : IsChart J J₀) (hε : IsUnitIn J x ε) (v : LieEx.ob x M ⟶ G)
    (hv : LieEx.zsec x ≫ v = 1) : ∃ y : Fin g → M, Co A J ε w v y := by
  obtain ⟨f, h, hf⟩ := exists_rep hc hε v hv
  exact ⟨_, f, h, hf, fun _ => rfl⟩

/- English proof (translation)
Take `⟨f, e, hf, hy⟩` from `h`. Take `⟨f', e', hf', hy'⟩` from `h'`. Establish `: f = f'`. Use `RingHom.ext fun b => TrivSqZeroExt.ext ((hf.1 b).trans (hf'.1 b).symm) ?_` and prove the remaining obligations. Rewrite using `[snd_formula hd f hf, snd_formula hd f' hf']`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← hy, ← hy']`. Substitute `this` using the available equality. Conclude with `Over.OverMorphism.ext (e.trans e'.symm)`.
-/
theorem co_inj (hd : IsCoord d w) {v v' : LieEx.ob x M ⟶ G} {y : Fin g → M}
    (h : Co A J ε w v y) (h' : Co A J ε w v' y) : v = v' := by
  obtain ⟨f, e, hf, hy⟩ := h
  obtain ⟨f', e', hf', hy'⟩ := h'
  have : f = f' := by
    refine RingHom.ext fun b => TrivSqZeroExt.ext ((hf.1 b).trans (hf'.1 b).symm) ?_
    rw [snd_formula hd f hf, snd_formula hd f' hf']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hy, ← hy']
  subst this
  exact Over.OverMorphism.ext (e.trans e'.symm)

/- English proof (translation)
Take `⟨f, e, hf, hy⟩` from `h`. Take `⟨f', e', hf', hy'⟩` from `h'`. Establish `: f = f'` using `spec_cancel J (e.symm.trans e')`. Substitute `this` using the available equality. Use function extensionality and compare the values at `i`.

Rewrite using `[hy, hy']`.
-/
theorem co_unique {v : LieEx.ob x M ⟶ G} {y y' : Fin g → M}
    (h : Co A J ε w v y) (h' : Co A J ε w v y') : y = y' := by
  obtain ⟨f, e, hf, hy⟩ := h
  obtain ⟨f', e', hf', hy'⟩ := h'
  have : f = f' := spec_cancel J (e.symm.trans e')
  subst this
  funext i
  rw [hy, hy']

def defo (d : Fin g → Derivation A B B) (ε : B →+* T) (y : Fin g → M) : B →+* TrivSqZeroExt T M where
  toFun b := TrivSqZeroExt.inl (ε b) + TrivSqZeroExt.inr (∑ k, ε (d k b) • y k)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by
    ext
    · simp
    · simp [add_smul, Finset.sum_add_distrib]
  map_mul' a b := by
    ext
    · simp
    · simp [TrivSqZeroExt.snd_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

/- English proof (translation)
Establish `hl : Lifts A ε (defo d ε y)` using `⟨fun b => by simp [defo], fun a => by simp [defo]⟩`. Take `⟨u, hu, hz⟩` from `mk_rep hc hε _ hl`. Use `⟨u, hz, _, hu, hl, fun i => ?_⟩` and prove the remaining obligations. Establish `key : ∀ k, ε ((w i).sum fun b a => a * d k b) = if k = i then 1 else 0` using `fun k => by`. Apply the tactic sequence `rw [hd.1 i k]; split_ifs <;> simp`.

Establish `e : yco ε w (fun b => (defo d ε y b).snd) i = ∑ k, ε ((w i).sum fun b a => a * d k b) • y k`. Simplify using `only [yco, defo, Finsupp.sum, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, Finset.smul_sum, map_sum, Finset.sum_smul, map_mul, mul_smul]`. Conclude with `Finset.sum_comm`. Rewrite using `[e]`. Simplify using `[key]`.
-/
theorem co_onto (hc : IsChart J J₀) (hε : IsUnitIn J x ε) (hd : IsCoord d w) (y : Fin g → M) :
    ∃ v : LieEx.ob x M ⟶ G, LieEx.zsec x ≫ v = 1 ∧ Co A J ε w v y := by
  have hl : Lifts A ε (defo d ε y) := ⟨fun b => by simp [defo], fun a => by simp [defo]⟩
  obtain ⟨u, hu, hz⟩ := mk_rep hc hε _ hl
  refine ⟨u, hz, _, hu, hl, fun i => ?_⟩
  have key : ∀ k, ε ((w i).sum fun b a => a * d k b) = if k = i then 1 else 0 := fun k => by
    rw [hd.1 i k]; split_ifs <;> simp
  have e : yco ε w (fun b => (defo d ε y b).snd) i =
      ∑ k, ε ((w i).sum fun b a => a * d k b) • y k := by
    simp only [yco, defo, Finsupp.sum, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, Finset.smul_sum, map_sum,
      Finset.sum_smul, map_mul, mul_smul]
    exact Finset.sum_comm
  rw [e]
  simp [key]

/- English proof (translation)
Take `⟨f, e, hf, hy⟩` from `h`. Use `⟨(TrivSqZeroExt.map l).toRingHom.comp f, ?_, ⟨fun b => ?_, fun a => ?_⟩, fun i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ v.left = _`. Rewrite using `[e, ← Category.assoc, spec_comp']`. Simplify using `using hf.1 b`.

Simplify using `[hf.2 a]`. Express the relevant statement in the definitionally equal form `l (y i) = _`. Rewrite using `[hy, yco, yco, Finsupp.sum, Finsupp.sum, map_sum]`. Simplify using the standard rewrite rules.
-/
theorem co_hom (l : M →ₗ[T] N) {v : LieEx.ob x M ⟶ G} {y : Fin g → M} (h : Co A J ε w v y) :
    Co A J ε w (LieEx.hom x l ≫ v) (fun i => l (y i)) := by
  obtain ⟨f, e, hf, hy⟩ := h
  refine ⟨(TrivSqZeroExt.map l).toRingHom.comp f, ?_, ⟨fun b => ?_, fun a => ?_⟩, fun i => ?_⟩
  · change Spec.map _ ≫ v.left = _
    rw [e, ← Category.assoc, spec_comp']
  · simpa using hf.1 b
  · simp [hf.2 a]
  · change l (y i) = _
    rw [hy, yco, yco, Finsupp.sum, Finsupp.sum, map_sum]
    simp

/- English proof (translation)
Establish `z : ∀ u : LieEx.ob x T ⟶ G, LieEx.zsec x ≫ u = 1 → LieEx.hom x (0 : T →ₗ[T] T) ≫ u = 1` using `fun u hu => by`. Rewrite using `[LieEx.hom_zero, Category.assoc, hu, MonObj.comp_one]`. Use `set u : LieEx.ob x (T × T) ⟶ G := (LieEx.hom x (LinearMap.inl T T T) ≫ v) * (LieEx.hom x (LinearMap.inr T T T) ≫ v') with hu`. Establish `hz : LieEx.zsec x ≫ u = 1`. Rewrite using `[hu, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, LieEx.zsec_hom, LieEx.zsec_hom, hv, hv', _root_.mul_one]`.

Take `⟨Y, hY⟩` from `co_exists (w := w) hc hε u hz`. Establish `h1 : LieEx.hom x (LinearMap.fst T T T) ≫ u = v`. Simplify using `only [hu, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, LieEx.hom_id, Category.id_comp, z v' hv', _root_.mul_one]`. Establish `h2 : LieEx.hom x (LinearMap.snd T T T) ≫ u = v'`. Simplify using `only [hu, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, LieEx.hom_id, Category.id_comp, z v hv, _root_.one_mul]`.

Establish `h3 : LieEx.hom x (LinearMap.fst T T T + LinearMap.snd T T T) ≫ u = v * v'`. Simplify using `only [hu, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.add_comp, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, add_zero, zero_add, LieEx.hom_id, Category.id_comp]`. Establish `a1` using `co_hom (LinearMap.fst T T T) hY`. Establish `a2` using `co_hom (LinearMap.snd T T T) hY`. Establish `a3` using `co_hom (LinearMap.fst T T T + LinearMap.snd T T T) hY`.

Rewrite `a1` using `[h1]`. Rewrite `a2` using `[h2]`. Rewrite `a3` using `[h3]`. Establish `b1` using `co_unique a1 h`. Establish `b2` using `co_unique a2 h'`.

Use `a3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[← b1, ← b2]`. Simplify using the standard rewrite rules.
-/
theorem co_mul (hc : IsChart J J₀) (hε : IsUnitIn J x ε) {v v' : LieEx.ob x T ⟶ G} {y y' : Fin g → T}
    (hv : LieEx.zsec x ≫ v = 1) (hv' : LieEx.zsec x ≫ v' = 1)
    (h : Co A J ε w v y) (h' : Co A J ε w v' y') : Co A J ε w (v * v') (y + y') := by
  have z : ∀ u : LieEx.ob x T ⟶ G, LieEx.zsec x ≫ u = 1 → LieEx.hom x (0 : T →ₗ[T] T) ≫ u = 1 := fun u hu => by
    rw [LieEx.hom_zero, Category.assoc, hu, MonObj.comp_one]
  set u : LieEx.ob x (T × T) ⟶ G :=
    (LieEx.hom x (LinearMap.inl T T T) ≫ v) * (LieEx.hom x (LinearMap.inr T T T) ≫ v') with hu
  have hz : LieEx.zsec x ≫ u = 1 := by
    rw [hu, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, LieEx.zsec_hom, LieEx.zsec_hom, hv, hv',
      _root_.mul_one]
  obtain ⟨Y, hY⟩ := co_exists (w := w) hc hε u hz
  have h1 : LieEx.hom x (LinearMap.fst T T T) ≫ u = v := by
    simp only [hu, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.fst_comp_inl,
      LinearMap.fst_comp_inr, LieEx.hom_id, Category.id_comp, z v' hv', _root_.mul_one]
  have h2 : LieEx.hom x (LinearMap.snd T T T) ≫ u = v' := by
    simp only [hu, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.snd_comp_inl,
      LinearMap.snd_comp_inr, LieEx.hom_id, Category.id_comp, z v hv, _root_.one_mul]
  have h3 : LieEx.hom x (LinearMap.fst T T T + LinearMap.snd T T T) ≫ u = v * v' := by
    simp only [hu, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.add_comp,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr,
      add_zero, zero_add, LieEx.hom_id, Category.id_comp]
  have a1 := co_hom (LinearMap.fst T T T) hY
  have a2 := co_hom (LinearMap.snd T T T) hY
  have a3 := co_hom (LinearMap.fst T T T + LinearMap.snd T T T) hY
  rw [h1] at a1
  rw [h2] at a2
  rw [h3] at a3
  have b1 := co_unique a1 h
  have b2 := co_unique a2 h'
  convert a3 using 1
  funext i
  rw [← b1, ← b2]
  simp

/- English proof (translation)
The claim follows from `co_hom _ h`.
-/
theorem co_smul (c : T) {v : LieEx.ob x T ⟶ G} {y : Fin g → T} (h : Co A J ε w v y) :
    Co A J ε w (LieEx.hom x (c • (LinearMap.id : T →ₗ[T] T)) ≫ v) (c • y) :=
  co_hom _ h

/- English proof (translation)
Take `⟨f, e, hf, hy⟩` from `h`. Use `⟨(dualMap φ).comp f, ?_, ⟨fun b => ?_, fun a => ?_⟩, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[e', e, ← Category.assoc, spec_comp']`. Simplify `congrArg φ (hf.1 b)` using `[dualMap]`. Simplify using `[dualMap, hf.2 a]`.

Express the relevant statement in the definitionally equal form `φ (y i) = _`. Rewrite using `[hy, yco, yco, Finsupp.sum, Finsupp.sum, map_sum]`. Simplify using `[dualMap]`.
-/
theorem co_base (φ : T →+* T') {x' : Spec (CommRingCat.of T') ⟶ X} {v : LieEx.ob x T ⟶ G}
    {v' : LieEx.ob x' T' ⟶ G} {y : Fin g → T}
    (e' : v'.left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left) (h : Co A J ε w v y) :
    Co A J (φ.comp ε) w v' (fun i => φ (y i)) := by
  obtain ⟨f, e, hf, hy⟩ := h
  refine ⟨(dualMap φ).comp f, ?_, ⟨fun b => ?_, fun a => ?_⟩, fun i => ?_⟩
  · rw [e', e, ← Category.assoc, spec_comp']
  · simpa [dualMap] using congrArg φ (hf.1 b)
  · simp [dualMap, hf.2 a]
  · change φ (y i) = _
    rw [hy, yco, yco, Finsupp.sum, Finsupp.sum, map_sum]
    simp [dualMap]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, he⟩ i`. Take `⟨t, ht⟩` from `co_exists (w := w) hc hε v ((LieEx.isTanAt_iff _ G _).1 hv)`. Rewrite using `[co_unique hv₀ (co_base φ he ht)]`. Conclude with `⟨t i, rfl⟩`.

Introduce `h choose t ht using h`. Take `⟨v, hz, hv⟩` from `co_onto hc hε hd t`. Use `⟨v, (LieEx.isTanAt_iff _ G _).2 hz, ?_⟩` and prove the remaining obligations. Establish `hb` using `co_base (x' := x') (v' := (LieCarrier.epsHom φ x x' hφ ≫ v : epsAt x' ⟶ G)) φ rfl hv`. Establish `e1 : y = fun i => φ (t i)` using `funext fun i => (ht i).symm`.

Establish `e2 : v₀ = LieCarrier.epsHom φ x x' hφ ≫ v` using `co_inj hd hv₀ (e1 ▸ hb)`. Conclude with `congrArg (fun k : epsAt x' ⟶ G => k.left) e2`.
-/
theorem tan_iff (φ : T →+* T') {x' : Spec (CommRingCat.of T') ⟶ X}
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (hc : IsChart J J₀) (hd : IsCoord d w)
    (hε : IsUnitIn J x ε) (y : Fin g → T') (v₀ : LieEx.ob x' T' ⟶ G) (hv₀ : Co A J (φ.comp ε) w v₀ y) :
    (∃ v : epsAt x ⟶ G, IsTanAt G x v ∧ v₀.left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left) ↔
      ∀ i, y i ∈ φ.range := by
  constructor
  · rintro ⟨v, hv, he⟩ i
    obtain ⟨t, ht⟩ := co_exists (w := w) hc hε v ((LieEx.isTanAt_iff _ G _).1 hv)
    rw [co_unique hv₀ (co_base φ he ht)]
    exact ⟨t i, rfl⟩
  · intro h
    choose t ht using h
    obtain ⟨v, hz, hv⟩ := co_onto hc hε hd t
    refine ⟨v, (LieEx.isTanAt_iff _ G _).2 hz, ?_⟩
    have hb := co_base (x' := x') (v' := (LieCarrier.epsHom φ x x' hφ ≫ v : epsAt x' ⟶ G)) φ rfl hv
    have e1 : y = fun i => φ (t i) := funext fun i => (ht i).symm
    have e2 : v₀ = LieCarrier.epsHom φ x x' hφ ≫ v := co_inj hd hv₀ (e1 ▸ hb)
    exact congrArg (fun k : epsAt x' ⟶ G => k.left) e2

/- English proof (translation)
Substitute `hφ` using the available equality. Unfold `IsUnitIn at hε ⊢`. Rewrite using `[← spec_comp', Category.assoc, hε]`. Use `MonObj.comp_one (M := G) (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ x) ⟶ Over.mk x)` as an intermediate fact. Conclude with `congrArg (fun k : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ x) ⟶ G => k.left) this`.
-/
theorem unit_base (φ : T →+* T') {x' : Spec (CommRingCat.of T') ⟶ X}
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (hε : IsUnitIn J x ε) : IsUnitIn J x' (φ.comp ε) := by
  subst hφ
  unfold IsUnitIn at hε ⊢
  rw [← spec_comp', Category.assoc, hε]
  have := MonObj.comp_one (M := G)
    (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ x) ⟶ Over.mk x)
  exact congrArg (fun k : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ x) ⟶ G => k.left) this

end Rep

section Main

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {Ω : Type} [Field Ω]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
  {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  {J : Spec (CommRingCat.of B) ⟶ G.left} [IsOpenImmersion J]
  {J₀ : Spec (CommRingCat.of A) ⟶ X} [IsOpenImmersion J₀]
  {g : ℕ} {d : Fin g → Derivation A B B} {w : Fin g → B →₀ B} {ε : B →+* Ω}

/- English proof (translation)
Establish `tz : ∀ e, LieEx.zsec ξ ≫ (M.pt e : LieEx.ob ξ Ω ⟶ G) = 1` using `fun e => (LieEx.isTanAt_iff ξ G _).1 (M.tan e)`. Establish `hex : ∀ e, ∃ y : Fin g → Ω, Co A J ε w (M.pt e : LieEx.ob ξ Ω ⟶ G) y` using `fun e => co_exists hc hε _ (tz e)`. Use `choose Θ hΘ using hex`. Establish `hadd : ∀ e e', Θ (e + e') = Θ e + Θ e'` using `fun e e' => by`. Establish `h` using `co_mul hc hε (tz e) (tz e') (hΘ e) (hΘ e')`.

Establish `h2` using `hΘ (e + e')`. Rewrite `h2` using `[M.add]`. Conclude with `co_unique h2 h`. Establish `hsmul : ∀ (c : Ω) e, Θ (c • e) = c • Θ e` using `fun c e => by`. Establish `e1 : M.pt (c • e) = LieEx.hom ξ (c • (LinearMap.id : Ω →ₗ[Ω] Ω)) ≫ M.pt e` using `Over.OverMorphism.ext (M.smul c e)`.

Establish `h2` using `hΘ (c • e)`. Rewrite `h2` using `[e1]`. Conclude with `co_unique h2 (co_smul c (hΘ e))`. Establish `hinj : Function.Injective Θ` using `fun e e' h => M.inj (co_inj hd (hΘ e) (h ▸ hΘ e'))`. Establish `hsurj : Function.Surjective Θ` using `fun y => by`.

Take `⟨v, hz, hv⟩` from `co_onto hc hε hd y`. Take `⟨e, rfl⟩` from `M.onto v ((LieEx.isTanAt_iff ξ G _).2 hz)`. Conclude with `⟨e, co_unique (hΘ e) hv⟩`. Set `Θl : E ≃ₗ[Ω] (Fin g → Ω)` to `LinearEquiv.ofBijective { toFun := Θ, map_add' := hadd, map_smul' := hsmul } ⟨hinj, hsurj⟩`. Set `Bs : Module.Basis (Fin g) Ω E` to `(Pi.basisFun Ω (Fin g)).map Θl.symm`.

Establish `hrepr : ∀ e i, Bs.repr e i = Θ e i` using `fun e i => by`. Simplify using `[Bs, Θl]`. Both sides reduce to the same expression. Use `⟨Bs, fun q εq hq hεq => ?_⟩` and prove the remaining obligations. Establish `hgen` using `LieCarrier.genMap_fromSpecStalk q`.

Use extensionality with `e`. Rewrite using `[(lieLat_carrier X G Ω ξ E M q).1 e, LatDual.mem_span_basis_iff]`. Substitute `hεq` using the available equality. Simplify using `only [hrepr]`. Conclude with `tan_iff (genMap ξ q) hgen hc hd hq (Θ e) (M.pt e) (hΘ e)`.
-/
theorem lat_coord (hc : IsChart J J₀) (hd : IsCoord d w) (hε : IsUnitIn J ξ ε) (M : LieModel G ξ E) :
    ∃ Bs : Module.Basis (Fin g) Ω E, ∀ (q : Cpt ξ) (εq : B →+* X.presheaf.stalk q.1),
      IsUnitIn J (T := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) εq → ε = (genMap ξ q).comp εq →
      M.lat q = Submodule.span (regAt ξ q) (Set.range Bs) := by
  have tz : ∀ e, LieEx.zsec ξ ≫ (M.pt e : LieEx.ob ξ Ω ⟶ G) = 1 :=
    fun e => (LieEx.isTanAt_iff ξ G _).1 (M.tan e)
  have hex : ∀ e, ∃ y : Fin g → Ω, Co A J ε w (M.pt e : LieEx.ob ξ Ω ⟶ G) y :=
    fun e => co_exists hc hε _ (tz e)
  choose Θ hΘ using hex
  have hadd : ∀ e e', Θ (e + e') = Θ e + Θ e' := fun e e' => by
    have h := co_mul hc hε (tz e) (tz e') (hΘ e) (hΘ e')
    have h2 := hΘ (e + e')
    rw [M.add] at h2
    exact co_unique h2 h
  have hsmul : ∀ (c : Ω) e, Θ (c • e) = c • Θ e := fun c e => by
    have e1 : M.pt (c • e) = LieEx.hom ξ (c • (LinearMap.id : Ω →ₗ[Ω] Ω)) ≫ M.pt e :=
      Over.OverMorphism.ext (M.smul c e)
    have h2 := hΘ (c • e)
    rw [e1] at h2
    exact co_unique h2 (co_smul c (hΘ e))
  have hinj : Function.Injective Θ := fun e e' h =>
    M.inj (co_inj hd (hΘ e) (h ▸ hΘ e'))
  have hsurj : Function.Surjective Θ := fun y => by
    obtain ⟨v, hz, hv⟩ := co_onto hc hε hd y
    obtain ⟨e, rfl⟩ := M.onto v ((LieEx.isTanAt_iff ξ G _).2 hz)
    exact ⟨e, co_unique (hΘ e) hv⟩
  let Θl : E ≃ₗ[Ω] (Fin g → Ω) := LinearEquiv.ofBijective
    { toFun := Θ, map_add' := hadd, map_smul' := hsmul } ⟨hinj, hsurj⟩
  let Bs : Module.Basis (Fin g) Ω E := (Pi.basisFun Ω (Fin g)).map Θl.symm
  have hrepr : ∀ e i, Bs.repr e i = Θ e i := fun e i => by
    simp [Bs, Θl]
    rfl
  refine ⟨Bs, fun q εq hq hεq => ?_⟩
  have hgen := LieCarrier.genMap_fromSpecStalk q
  ext e
  rw [(lieLat_carrier X G Ω ξ E M q).1 e, LatDual.mem_span_basis_iff]
  subst hεq
  simp only [hrepr]
  exact tan_iff (genMap ξ q) hgen hc hd hq (Θ e) (M.pt e) (hΘ e)

/- English proof (translation)
Set `s : X ⟶ G.left` to `(1 : Over.mk (𝟙 X) ⟶ G).left`. Establish `hs1 : ∀ {T : Type} [CommRing T] (x : Spec (CommRingCat.of T) ⟶ X), (1 : Over.mk x ⟶ G).left = x ≫ s`. Introduce `T _ x`. Use `MonObj.comp_one (M := G) (Over.homMk x (by simp) : Over.mk x ⟶ Over.mk (𝟙 X))` as an intermediate fact. Conclude with `(congrArg (fun k : Over.mk x ⟶ G => k.left) this).symm`.

Take `⟨U, hU, V, hV, hx, e, hsm⟩` from `hs.exists_isStandardSmoothOfRelativeDimension (s p.1)`. Use `letI : Algebra Γ(X, U) Γ(G.left, V) := (G.hom.appLE U V e).hom.toAlgebra`. Use `haveI : Algebra.IsStandardSmoothOfRelativeDimension g Γ(X, U) Γ(G.left, V) := hsm`. Use `haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g (R := Γ(X, U)) (S := Γ(G.left, V))`. Use `haveI : Nonempty V := ⟨⟨s p.1, hx⟩⟩`.

Use `haveI : Nontrivial Γ(G.left, V) := inferInstance`. Establish `hfr : Module.finrank Γ(G.left, V) Ω[Γ(G.left, V)⁄Γ(X, U)] = g`. Rewrite using `[Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g]`. Simplify using the standard rewrite rules. Set `c : Module.Basis (Fin g) Γ(G.left, V) Ω[Γ(G.left, V)⁄Γ(X, U)]` to `Module.finBasisOfFinrankEq _ _ hfr`.

Take `⟨d, w, hd⟩` from `exists_isCoord c`. Establish `hc : IsChart (A` using `Γ(X, U)) (B := Γ(G.left, V)) hV.fromSpec hU.fromSpec := (IsAffineOpen.SpecMap_appLE_fromSpec G.hom hU hV e).symm`. Establish `hpt : ∀ {T : Type} [CommRing T] (x : Spec (CommRingCat.of T) ⟶ X), Set.range x ⊆ (s ⁻¹ᵁ V : Set X) → ∃ ε : Γ(G.left, V) →+* T, IsUnitIn (B` using `Γ(G.left, V)) hV.fromSpec x ε := by`. Introduce `T _ x hx`. Establish `hr : Set.range (x ≫ s) ⊆ Set.range hV.fromSpec`.

Rewrite using `[hV.range_fromSpec]`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hx ⟨y, rfl⟩`. Use `⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec (x ≫ s) hr)).hom, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom _) ≫ _ = _`.

Rewrite using `[hs1, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]`. Establish `hst : ∀ q : Cpt ξ, q.1 ∈ s ⁻¹ᵁ V → Set.range (X.fromSpecStalk q.1) ⊆ (s ⁻¹ᵁ V : Set X)`. Introduce `q hq`. Rewrite using `[Scheme.range_fromSpecStalk]`. Introduce `y hy`.

Conclude with `Specializes.mem_open hy (s ⁻¹ᵁ V).isOpen hq`. Establish `hbase : ∀ (q : Cpt ξ) (εq : Γ(G.left, V) →+* X.presheaf.stalk q.1), IsUnitIn (B` using `Γ(G.left, V)) (T := X.presheaf.stalk q.1) hV.fromSpec (X.fromSpecStalk q.1) εq → IsUnitIn (B := Γ(G.left, V)) hV.fromSpec ξ ((genMap ξ q).comp εq) := fun q εq h => unit_base (genMap ξ q) (LieCarrier.genMap_fromSpecStalk q) h`. Establish `hp : p.1 ∈ s ⁻¹ᵁ V` using `hx`. Take `⟨εp, hεp⟩` from `hpt (X.fromSpecStalk p.1) (hst p hp)`. Take `⟨Bs, hB⟩` from `lat_coord hc hd (hbase p εp hεp) M`.

Use `⟨s ⁻¹ᵁ V, hp, Bs, fun q hq => ?_⟩` and prove the remaining obligations. Take `⟨εq, hεq⟩` from `hpt (X.fromSpecStalk q.1) (hst q hq)`. Conclude with `hB q εq hεq (spec_cancel hV.fromSpec ((hbase p εp hεp).trans (hbase q εq hεq).symm))`.
-/
theorem frame_at (hs : SmoothOfRelativeDimension g G.hom) (M : LieModel G ξ E) (p : Cpt ξ) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∃ Bs : Module.Basis (Fin g) Ω E, ∀ q : Cpt ξ, q.1 ∈ U →
      M.lat q = Submodule.span (regAt ξ q) (Set.range Bs) := by
  let s : X ⟶ G.left := (1 : Over.mk (𝟙 X) ⟶ G).left
  have hs1 : ∀ {T : Type} [CommRing T] (x : Spec (CommRingCat.of T) ⟶ X),
      (1 : Over.mk x ⟶ G).left = x ≫ s := by
    intro T _ x
    have := MonObj.comp_one (M := G) (Over.homMk x (by simp) : Over.mk x ⟶ Over.mk (𝟙 X))
    exact (congrArg (fun k : Over.mk x ⟶ G => k.left) this).symm
  obtain ⟨U, hU, V, hV, hx, e, hsm⟩ := hs.exists_isStandardSmoothOfRelativeDimension (s p.1)
  letI : Algebra Γ(X, U) Γ(G.left, V) := (G.hom.appLE U V e).hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g Γ(X, U) Γ(G.left, V) := hsm
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g (R := Γ(X, U)) (S := Γ(G.left, V))
  haveI : Nonempty V := ⟨⟨s p.1, hx⟩⟩
  haveI : Nontrivial Γ(G.left, V) := inferInstance
  have hfr : Module.finrank Γ(G.left, V) Ω[Γ(G.left, V)⁄Γ(X, U)] = g := by
    rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g]
    simp
  let c : Module.Basis (Fin g) Γ(G.left, V) Ω[Γ(G.left, V)⁄Γ(X, U)] := Module.finBasisOfFinrankEq _ _ hfr
  obtain ⟨d, w, hd⟩ := exists_isCoord c
  have hc : IsChart (A := Γ(X, U)) (B := Γ(G.left, V)) hV.fromSpec hU.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec G.hom hU hV e).symm
  have hpt : ∀ {T : Type} [CommRing T] (x : Spec (CommRingCat.of T) ⟶ X), Set.range x ⊆ (s ⁻¹ᵁ V : Set X) →
      ∃ ε : Γ(G.left, V) →+* T, IsUnitIn (B := Γ(G.left, V)) hV.fromSpec x ε := by
    intro T _ x hx
    have hr : Set.range (x ≫ s) ⊆ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      rintro _ ⟨y, rfl⟩
      exact hx ⟨y, rfl⟩
    refine ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec (x ≫ s) hr)).hom, ?_⟩
    change Spec.map (CommRingCat.ofHom _) ≫ _ = _
    rw [hs1, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hst : ∀ q : Cpt ξ, q.1 ∈ s ⁻¹ᵁ V → Set.range (X.fromSpecStalk q.1) ⊆ (s ⁻¹ᵁ V : Set X) := by
    intro q hq
    rw [Scheme.range_fromSpecStalk]
    intro y hy
    exact Specializes.mem_open hy (s ⁻¹ᵁ V).isOpen hq
  have hbase : ∀ (q : Cpt ξ) (εq : Γ(G.left, V) →+* X.presheaf.stalk q.1),
      IsUnitIn (B := Γ(G.left, V)) (T := X.presheaf.stalk q.1) hV.fromSpec (X.fromSpecStalk q.1) εq →
      IsUnitIn (B := Γ(G.left, V)) hV.fromSpec ξ ((genMap ξ q).comp εq) :=
    fun q εq h => unit_base (genMap ξ q) (LieCarrier.genMap_fromSpecStalk q) h
  have hp : p.1 ∈ s ⁻¹ᵁ V := hx
  obtain ⟨εp, hεp⟩ := hpt (X.fromSpecStalk p.1) (hst p hp)
  obtain ⟨Bs, hB⟩ := lat_coord hc hd (hbase p εp hεp) M
  refine ⟨s ⁻¹ᵁ V, hp, Bs, fun q hq => ?_⟩
  obtain ⟨εq, hεq⟩ := hpt (X.fromSpecStalk q.1) (hst q hq)
  exact hB q εq hεq (spec_cancel hV.fromSpec ((hbase p εp hεp).trans (hbase q εq hεq).symm))

end Main

end GlobalTheory.CompanionTheory.Ar.LieVB

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

/- English proof (translation)
Introduce `X G _ _ g Ω _ ξ E _ _ M _ hs`. Establish `h : M.lat.IsVB g ⊤` using `fun p _ => by`. Take `⟨U, hU, Bs, hB⟩` from `LieVB.frame_at hs M p`. Conclude with `⟨U, hU, Bs, Bs.span_eq, fun q _ hq => ⟨Bs.linearIndependent, hB q hq⟩⟩`. Conclude with `⟨h, (Lat.isVBOn_dual_and_bidual X Ω ξ E M.lat Set.univ g h).1⟩`.
-/
theorem lieLat_isVB : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E), IsCptGen ξ → SmoothOfRelativeDimension g G.hom → M.lat.IsVB g ⊤ ∧ M.omLat.IsVB g ⊤ := by
  intro X G _ _ g Ω _ ξ E _ _ M _ hs
  have h : M.lat.IsVB g ⊤ := fun p _ => by
    obtain ⟨U, hU, Bs, hB⟩ := LieVB.frame_at hs M p
    exact ⟨U, hU, Bs, Bs.span_eq, fun q _ hq => ⟨Bs.linearIndependent, hB q hq⟩⟩
  exact ⟨h, (Lat.isVBOn_dual_and_bidual X Ω ξ E M.lat Set.univ g h).1⟩

end GlobalTheory.CompanionTheory.Ar
