import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootOrbit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qi49.root_orbit φ ψ h b`.
-/
private theorem root_orbit {A B G Ω : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] [Field Ω] (φ ψ : B →+* Ω)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B)) (b : B) : ∃ g : G, ψ b = φ (g • b) :=
  _root_.UpperTheory.Reformulated.B.Qi49.root_orbit φ ψ h b

/- English proof (translation)
Set `Q : Ideal B` to `RingHom.ker φ`. Use `haveI : Q.IsPrime := RingHom.ker_isPrime φ`. Set `P : Ideal A` to `Q.under A`. Use `haveI : Q.LiesOver P := ⟨rfl⟩`. Set `φb : B ⧸ Q →+* Ω` to `Ideal.Quotient.lift Q φ (fun a ha => ha)`.

Set `ψb : B ⧸ Q →+* Ω` to `Ideal.Quotient.lift Q ψ (fun a ha => by`. Establish `: a ∈ RingHom.ker ψ` using `hk ▸ ha`. Conclude with `this)`. Establish `φm : ∀ b, φb (Ideal.Quotient.mk Q b) = φ b` using `fun b => Ideal.Quotient.lift_mk _ _ _`. Establish `ψm : ∀ b, ψb (Ideal.Quotient.mk Q b) = ψ b` using `fun b => Ideal.Quotient.lift_mk _ _ _`.

Establish `inj : ∀ f : B ⧸ Q →+* Ω, (∀ b, f (Ideal.Quotient.mk Q b) = 0 → b ∈ Q) → Function.Injective f`. Introduce `f hf`. Use `(injective_iff_map_eq_zero f).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hf b hx)`.

Establish `φi : Function.Injective φb` using `inj φb fun b hb => by`. Rewrite `hb` using `[φm]`. Conclude with `hb`. Establish `ψi : Function.Injective ψb` using `inj ψb fun b hb => by`. Rewrite `hb` using `[ψm]`.

Establish `h' : b ∈ RingHom.ker ψ` using `hb`. Rewrite `h'` using `[← hk]`. Conclude with `h'`. Establish `hr : ψb.range = φb.range`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨g, hg⟩` from `root_orbit (G := G) φ ψ h b`. Conclude with `⟨Ideal.Quotient.mk Q (g • b), by rw [φm, ψm, hg]⟩`.

Introduce and unpack `⟨x, rfl⟩`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨g, hg⟩` from `root_orbit (G := G) ψ φ h.symm b`. Conclude with `⟨Ideal.Quotient.mk Q (g • b), by rw [φm, ψm, hg]⟩`. Set `eφ : B ⧸ Q ≃+* φb.range` to `RingEquiv.ofBijective φb.rangeRestrict ⟨fun x y e => φi (congrArg Subtype.val e), φb.rangeRestrict_surjective⟩`.

Set `eψ : B ⧸ Q ≃+* ψb.range` to `RingEquiv.ofBijective ψb.rangeRestrict ⟨fun x y e => ψi (congrArg Subtype.val e), ψb.rangeRestrict_surjective⟩`. Set `τ0 : B ⧸ Q ≃+* B ⧸ Q` to `(eψ.trans (RingEquiv.subringCongr hr)).trans eφ.symm`. Establish `hτ : ∀ x, φb (τ0 x) = ψb x`. Introduce `x`. Establish `e : eφ (τ0 x) = RingEquiv.subringCongr hr (eψ x)` using `eφ.apply_symm_apply _`.

Conclude with `congrArg Subtype.val e`. Set `τ : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)` to `AlgEquiv.ofRingEquiv (f := τ0) (fun a => by`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Apply `φi` to reduce the goal to its premises. Rewrite using `[hτ]`.

Express the relevant statement in the definitionally equal form `ψb (Ideal.Quotient.mk Q (algebraMap A B a)) = φb (Ideal.Quotient.mk Q (algebraMap A B a))`. Rewrite using `[φm, ψm]`. Conclude with `(congrArg (fun f => f a) h).symm)`. Take `⟨g, hg⟩` from `Ideal.Quotient.stabilizerHom_surjective G P Q τ`. Use `⟨g.1, fun b => ?_⟩` and prove the remaining obligations.

Establish `e1 : Ideal.Quotient.stabilizerHom Q P G g (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g.1 • b)` using `Ideal.Quotient.stabilizerHom_apply Q P G g b`. Rewrite `e1` using `[hg]`. Establish `e2` using `hτ (Ideal.Quotient.mk Q b)`. Rewrite `e2` using `[ψm]`. Rewrite using `[← e2, ← φm]`.

Conclude with `congrArg φb e1`.
-/
private theorem same_ker {A B G Ω : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] [Field Ω] (φ ψ : B →+* Ω)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B)) (hk : RingHom.ker φ = RingHom.ker ψ) :
    ∃ g : G, ∀ b, ψ b = φ (g • b) := by
  let Q : Ideal B := RingHom.ker φ
  haveI : Q.IsPrime := RingHom.ker_isPrime φ
  let P : Ideal A := Q.under A
  haveI : Q.LiesOver P := ⟨rfl⟩
  let φb : B ⧸ Q →+* Ω := Ideal.Quotient.lift Q φ (fun a ha => ha)
  let ψb : B ⧸ Q →+* Ω := Ideal.Quotient.lift Q ψ (fun a ha => by
    have : a ∈ RingHom.ker ψ := hk ▸ ha
    exact this)
  have φm : ∀ b, φb (Ideal.Quotient.mk Q b) = φ b := fun b => Ideal.Quotient.lift_mk _ _ _
  have ψm : ∀ b, ψb (Ideal.Quotient.mk Q b) = ψ b := fun b => Ideal.Quotient.lift_mk _ _ _
  have inj : ∀ f : B ⧸ Q →+* Ω, (∀ b, f (Ideal.Quotient.mk Q b) = 0 → b ∈ Q) → Function.Injective f := by
    intro f hf
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hf b hx)
  have φi : Function.Injective φb := inj φb fun b hb => by
    rw [φm] at hb
    exact hb
  have ψi : Function.Injective ψb := inj ψb fun b hb => by
    rw [ψm] at hb
    have h' : b ∈ RingHom.ker ψ := hb
    rw [← hk] at h'
    exact h'
  have hr : ψb.range = φb.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨g, hg⟩ := root_orbit (G := G) φ ψ h b
      exact ⟨Ideal.Quotient.mk Q (g • b), by rw [φm, ψm, hg]⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨g, hg⟩ := root_orbit (G := G) ψ φ h.symm b
      exact ⟨Ideal.Quotient.mk Q (g • b), by rw [φm, ψm, hg]⟩
  let eφ : B ⧸ Q ≃+* φb.range := RingEquiv.ofBijective φb.rangeRestrict
    ⟨fun x y e => φi (congrArg Subtype.val e), φb.rangeRestrict_surjective⟩
  let eψ : B ⧸ Q ≃+* ψb.range := RingEquiv.ofBijective ψb.rangeRestrict
    ⟨fun x y e => ψi (congrArg Subtype.val e), ψb.rangeRestrict_surjective⟩
  let τ0 : B ⧸ Q ≃+* B ⧸ Q := (eψ.trans (RingEquiv.subringCongr hr)).trans eφ.symm
  have hτ : ∀ x, φb (τ0 x) = ψb x := by
    intro x
    have e : eφ (τ0 x) = RingEquiv.subringCongr hr (eψ x) := eφ.apply_symm_apply _
    exact congrArg Subtype.val e
  let τ : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := τ0) (fun a => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply φi
    rw [hτ]
    change ψb (Ideal.Quotient.mk Q (algebraMap A B a)) = φb (Ideal.Quotient.mk Q (algebraMap A B a))
    rw [φm, ψm]
    exact (congrArg (fun f => f a) h).symm)
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q τ
  refine ⟨g.1, fun b => ?_⟩
  have e1 : Ideal.Quotient.stabilizerHom Q P G g (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g.1 • b) :=
    Ideal.Quotient.stabilizerHom_apply Q P G g b
  rw [hg] at e1
  have e2 := hτ (Ideal.Quotient.mk Q b)
  rw [ψm] at e2
  rw [← e2, ← φm]
  exact congrArg φb e1

end UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `A B G Ω _ _ _ _ _ _ _ _ _ φ φ' h`. Use `haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ`. Use `haveI : (RingHom.ker φ').IsPrime := RingHom.ker_isPrime φ'`. Establish `hu : (RingHom.ker φ).under A = (RingHom.ker φ').under A`. Use extensionality with `a`.

Express the relevant statement in the definitionally equal form `φ (algebraMap A B a) = 0 ↔ φ' (algebraMap A B a) = 0`. Rewrite using `[show φ (algebraMap A B a) = φ' (algebraMap A B a) from congrArg (fun f => f a) h]`. Take `⟨g0, hg0⟩` from `Algebra.IsInvariant.exists_smul_of_under_eq A B G _ _ hu`. Set `ψ : B →+* Ω` to `φ'.comp (MulSemiringAction.toRingHom G B g0)`. Establish `hψ : ∀ b, ψ b = φ' (g0 • b)` using `fun _ => rfl`.

Establish `hk : RingHom.ker φ = RingHom.ker ψ`. Use extensionality with `b`. Establish `e : g0 • b ∈ RingHom.ker φ' ↔ b ∈ RingHom.ker φ`. Rewrite using `[hg0]`. Conclude with `Ideal.smul_mem_pointwise_smul_iff`.

Rewrite using `[← e, RingHom.mem_ker, RingHom.mem_ker, hψ]`. Establish `hA : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B)`. Use extensionality with `a`. Establish `e : φ (algebraMap A B a) = φ' (algebraMap A B a)` using `congrArg (fun f => f a) h`. Simplify using `[hψ, e, smul_algebraMap]`.

Take `⟨g, hg⟩` from `same_ker (G := G) φ ψ hA hk`. Use `⟨g * g0⁻¹, fun b => ?_⟩` and prove the remaining obligations. Establish `e` using `hg (g0⁻¹ • b)`. Rewrite `e` using `[hψ, smul_inv_smul, ← mul_smul]`. Conclude with `e`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.invTrans_of :
    InvTrans := by
  intro A B G Ω _ _ _ _ _ _ _ _ _ φ φ' h
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  haveI : (RingHom.ker φ').IsPrime := RingHom.ker_isPrime φ'
  have hu : (RingHom.ker φ).under A = (RingHom.ker φ').under A := by
    ext a
    change φ (algebraMap A B a) = 0 ↔ φ' (algebraMap A B a) = 0
    rw [show φ (algebraMap A B a) = φ' (algebraMap A B a) from congrArg (fun f => f a) h]
  obtain ⟨g0, hg0⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G _ _ hu
  let ψ : B →+* Ω := φ'.comp (MulSemiringAction.toRingHom G B g0)
  have hψ : ∀ b, ψ b = φ' (g0 • b) := fun _ => rfl
  have hk : RingHom.ker φ = RingHom.ker ψ := by
    ext b
    have e : g0 • b ∈ RingHom.ker φ' ↔ b ∈ RingHom.ker φ := by
      rw [hg0]
      exact Ideal.smul_mem_pointwise_smul_iff
    rw [← e, RingHom.mem_ker, RingHom.mem_ker, hψ]
  have hA : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) := by
    ext a
    have e : φ (algebraMap A B a) = φ' (algebraMap A B a) := congrArg (fun f => f a) h
    simp [hψ, e, smul_algebraMap]
  obtain ⟨g, hg⟩ := same_ker (G := G) φ ψ hA hk
  refine ⟨g * g0⁻¹, fun b => ?_⟩
  have e := hg (g0⁻¹ • b)
  rw [hψ, smul_inv_smul, ← mul_smul] at e
  exact e
