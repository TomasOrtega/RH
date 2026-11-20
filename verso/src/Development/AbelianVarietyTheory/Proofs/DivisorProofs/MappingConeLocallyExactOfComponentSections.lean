import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ConeSec

variable {R : Type} [CommRing R]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma smap_comp {F G K : Shv R} (a : F ⟶ G) (b : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma smap_add {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a + b) x = Sec.map a x + Sec.map b x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma smap_neg {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (-a) x = -Sec.map a x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma smap_sub {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a - b) x = Sec.map a x - Sec.map b x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma smap_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

/- English proof (translation)
The claim follows from `(a.hom.app (op U)).hom.map_add x y`.
-/
lemma smap_add' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map a (x + y) = Sec.map a x + Sec.map a y := (a.hom.app (op U)).hom.map_add x y

/- English proof (translation)
The claim follows from `(a.hom.app (op U)).hom.map_neg x`.
-/
lemma smap_neg' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map a (-x) = -Sec.map a x := (a.hom.app (op U)).hom.map_neg x

/- English proof (translation)
Use `a.hom.naturality g.op` as an intermediate fact. Conclude with `congrArg (fun t => t.hom x) this.symm`.
-/
lemma sres_map {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  have := a.hom.naturality g.op
  exact congrArg (fun t => t.hom x) this.symm

/- English proof (translation)
The claim follows from `(a.hom.app (op U)).hom.map_zero`.
-/
lemma smap_zero {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} :
    Sec.map a (0 : Sec F U) = 0 := (a.hom.app (op U)).hom.map_zero

/- English proof (translation)
The claim follows from `(F.obj.map g.op).hom.map_add x y`.
-/
lemma sres_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := (F.obj.map g.op).hom.map_add x y

end GlobalTheory.EtC.ConeSec

open GlobalTheory.EtC.ConeSec in

/- English proof (translation)
Introduce `R _ I J f U n hyp b hb`. Take `⟨b₁, hb₁⟩ : ∃ x, Sec.map ((mappingCone.fst f).1.v n (n + 1) rfl) b = x` from `⟨_, rfl⟩`. Take `⟨b₂, hb₂⟩ : ∃ x, Sec.map ((mappingCone.snd f).v n n (add_zero n)) b = x` from `⟨_, rfl⟩`. Establish `h1 : Sec.map (I.d (n + 1) (n + 2)) b₁ = 0`. Establish `e` using `congrArg (fun φ => Sec.map φ b) (mappingCone.d_fst_v f n (n + 1) (n + 2) rfl (by ring))`.

Simplify using `only [smap_comp, smap_neg, hb, smap_zero, hb₁] at e`. Conclude with `neg_eq_zero.mp e.symm`. Establish `h2 : Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0`. Establish `e` using `congrArg (fun φ => Sec.map φ b) (mappingCone.d_snd_v f n (n + 1) rfl)`. Simplify using `only [smap_comp, smap_add, hb, smap_zero, hb₁, hb₂] at e`.

Conclude with `e.symm`. Establish `hid` using `congrArg (fun φ => Sec.map φ b) (mappingCone.id_X f n (n + 1) rfl)`. Simplify using `only [smap_comp, smap_add, smap_id, hb₁, hb₂] at hid`. Take `⟨S, hS, h⟩` from `hyp b₁ b₂ h1 h2`. Use `⟨S, hS, fun V g hg => ?_⟩` and prove the remaining obligations.

Take `⟨a₁, a₂, e1, e2⟩` from `h V g hg`. Use `⟨Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁ + Sec.map ((mappingCone.inr f).f (n - 1)) a₂, ?_⟩` and prove the remaining obligations. Establish `k1 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁) = Sec.map ((mappingCone.inr f).f n) (Sec.map (f.f n) a₁) - Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.map (I.d n (n + 1)) a₁)`. Rewrite using `[← smap_comp, mappingCone.inl_v_d f n (n - 1) (n + 1) (by ring) (by ring), smap_sub, smap_comp, smap_comp]`. Establish `k2 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inr f).f (n - 1)) a₂) = Sec.map ((mappingCone.inr f).f n) (Sec.map (J.d (n - 1) n) a₂)`.

Rewrite using `[← smap_comp, mappingCone.inr_f_d, smap_comp]`. Establish `k3 : Sec.res g b = Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.res g b₁) + Sec.map ((mappingCone.inr f).f n) (Sec.res g b₂)`. Rewrite using `[← hid, sres_add, sres_map, sres_map]`. Rewrite using `[smap_add', k1, k2, e1, k3, ← e2, smap_add', smap_neg']`. Normalize the expressions using the abelian group laws.
-/
theorem GlobalTheory.EtC.cone_sec_exact : ∀ (R : Type) [CommRing R] {I J : Cx R} (f : I ⟶ J) (U : Scheme.{0}) (n : ℤ), (∀ (b₁ : Sec (I.X (n + 1)) U) (b₂ : Sec (J.X n) U), Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 → Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec (I.X n) V) (a₂ : Sec (J.X (n - 1)) V), Sec.map (I.d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map (f.f n) a₁ + Sec.map (J.d (n - 1) n) a₂ = Sec.res g b₂) → ∀ b : Sec ((mappingCone f).X n) U, Sec.map ((mappingCone f).d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec ((mappingCone f).X (n - 1)) V, Sec.map ((mappingCone f).d (n - 1) n) a = Sec.res g b := by
  intro R _ I J f U n hyp b hb
  obtain ⟨b₁, hb₁⟩ : ∃ x, Sec.map ((mappingCone.fst f).1.v n (n + 1) rfl) b = x := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ x, Sec.map ((mappingCone.snd f).v n n (add_zero n)) b = x := ⟨_, rfl⟩
  have h1 : Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 := by
    have e := congrArg (fun φ => Sec.map φ b) (mappingCone.d_fst_v f n (n + 1) (n + 2) rfl (by ring))
    simp only [smap_comp, smap_neg, hb, smap_zero, hb₁] at e
    exact neg_eq_zero.mp e.symm
  have h2 : Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 := by
    have e := congrArg (fun φ => Sec.map φ b) (mappingCone.d_snd_v f n (n + 1) rfl)
    simp only [smap_comp, smap_add, hb, smap_zero, hb₁, hb₂] at e
    exact e.symm
  have hid := congrArg (fun φ => Sec.map φ b) (mappingCone.id_X f n (n + 1) rfl)
  simp only [smap_comp, smap_add, smap_id, hb₁, hb₂] at hid
  obtain ⟨S, hS, h⟩ := hyp b₁ b₂ h1 h2
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨a₁, a₂, e1, e2⟩ := h V g hg
  refine ⟨Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁ + Sec.map ((mappingCone.inr f).f (n - 1)) a₂, ?_⟩
  have k1 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁) =
      Sec.map ((mappingCone.inr f).f n) (Sec.map (f.f n) a₁) -
        Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.map (I.d n (n + 1)) a₁) := by
    rw [← smap_comp, mappingCone.inl_v_d f n (n - 1) (n + 1) (by ring) (by ring), smap_sub, smap_comp, smap_comp]
  have k2 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inr f).f (n - 1)) a₂) =
      Sec.map ((mappingCone.inr f).f n) (Sec.map (J.d (n - 1) n) a₂) := by
    rw [← smap_comp, mappingCone.inr_f_d, smap_comp]
  have k3 : Sec.res g b = Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.res g b₁) +
      Sec.map ((mappingCone.inr f).f n) (Sec.res g b₂) := by
    rw [← hid, sres_add, sres_map, sres_map]
  rw [smap_add', k1, k2, e1, k3, ← e2, smap_add', smap_neg']
  abel
