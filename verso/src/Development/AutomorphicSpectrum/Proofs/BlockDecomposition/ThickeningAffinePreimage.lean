import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

/- English proof (translation)
Establish `ex : Function.Exact (Submodule.subtype (RingHom.ker (algebraMap A A'))) (Algebra.linearMap A A')` using `fun a => by`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Conclude with `⟨⟨a, ha⟩, rfl⟩`. Introduce and unpack `⟨b, rfl⟩`.

Conclude with `b.2`. Establish `hs' : Function.Surjective (Algebra.linearMap A A')` using `hs`. Establish `ex2` using `rTensor_exact M ex hs'`. Establish `h0 : LinearMap.rTensor M (Algebra.linearMap A A') ((1 : A) ⊗ₜ[A] x) = 0`. Simplify using `using h`.

Take `⟨z, hz⟩` from `(ex2 _).1 h0`. Establish `key : ∀ z : (RingHom.ker (algebraMap A A')) ⊗[A] M, TensorProduct.lid A M (LinearMap.rTensor M (Submodule.subtype (RingHom.ker (algebraMap A A'))) z) ∈ (RingHom.ker (algebraMap A A')) • (⊤ : Submodule A M)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simpa only [map_add] using add_mem ha hb`. Consider the case `tmul a m => simpa using Submodule.smul_mem_smul a.2 Submodule.mem_top`. Use `key z` as an intermediate fact. Rewrite `this` using `[hz]`. Simplify using `using this`.
-/
theorem mem_ker_smul_top_of_one_tmul_eq_zero {A A' M : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    (hs : Function.Surjective (algebraMap A A')) [AddCommGroup M] [Module A M] (x : M)
    (h : (1 : A') ⊗ₜ[A] x = 0) :
    x ∈ (RingHom.ker (algebraMap A A')) • (⊤ : Submodule A M) := by
  have ex : Function.Exact (Submodule.subtype (RingHom.ker (algebraMap A A')))
      (Algebra.linearMap A A') := fun a => by
    constructor
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact b.2
  have hs' : Function.Surjective (Algebra.linearMap A A') := hs
  have ex2 := rTensor_exact M ex hs'
  have h0 : LinearMap.rTensor M (Algebra.linearMap A A') ((1 : A) ⊗ₜ[A] x) = 0 := by
    simpa using h
  obtain ⟨z, hz⟩ := (ex2 _).1 h0
  have key : ∀ z : (RingHom.ker (algebraMap A A')) ⊗[A] M,
      TensorProduct.lid A M (LinearMap.rTensor M
        (Submodule.subtype (RingHom.ker (algebraMap A A'))) z) ∈
        (RingHom.ker (algebraMap A A')) • (⊤ : Submodule A M) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using add_mem ha hb
    | tmul a m => simpa using Submodule.smul_mem_smul a.2 Submodule.mem_top
  have := key z
  rw [hz] at this
  simpa using this

/- English proof (translation)
Use `appLE_cst (f := f ≫ Spec.map (CommRingCat.ofHom q)) (f' := f) (π := 𝟙 X) (g := q) (by simp) (V := V) (V' := V) le_rfl r` as an intermediate fact. Establish `e : (𝟙 X : X ⟶ X).appLE V V le_rfl = 𝟙 _`. Simplify using `[Scheme.Hom.appLE]`. Conclude with `X.presheaf.map_id _`. Rewrite `this` using `[e]`.

Conclude with `this`.
-/
theorem cst_comp_spec {X : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) (q : R →+* A) (V : X.Opens) (r : R) :
    cst (f ≫ Spec.map (CommRingCat.ofHom q)) V r = cst f V (q r) := by
  have := appLE_cst (f := f ≫ Spec.map (CommRingCat.ofHom q)) (f' := f) (π := 𝟙 X) (g := q)
    (by simp) (V := V) (V' := V) le_rfl r
  have e : (𝟙 X : X ⟶ X).appLE V V le_rfl = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
    exact X.presheaf.map_id _
  rw [e] at this
  exact this

/- English proof (translation)
Use `letI := g.toAlgebra`. Establish `hb` using `SecOnR.baseChangeHom_bijective (R := A) (R' := A') hM H hV rfl`. Prove the components needed by the constructor for the conclusion. Introduce `y`. Take `⟨z, hz⟩` from `hb.2 y`.

Take `⟨x, rfl⟩` from `TensorProduct.mk_surjective A (SecOnR f M V) A' hg z`. Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `h` using `(SecOnR.baseChangeHom_tmul (R := A) (R' := A') H.w le_rfl 1 x).symm.trans hz`. Rewrite `h` using `[one_smul]`. Conclude with `h`.

Introduce `s hs`. Use `mem_ker_smul_top_of_one_tmul_eq_zero hg s (hb.1 ?_)` and prove the remaining obligations. Rewrite using `[map_zero, SecOnR.baseChangeHom_tmul, one_smul]`. Conclude with `hs`.
-/
theorem pull_surjective_ker {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : Function.Surjective g) {X X' : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of A)}
    {f' : X' ⟶ Spec (CommRingCat.of A')} {π : X' ⟶ X}
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) {M : LB X} (hM : M.IsLB)
    {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (SecOn.pullLE M π V _ le_rfl) ∧
      ∀ s : SecOnR f M V, SecOn.pullLE M π V _ le_rfl ((SecOnR.of f M V).symm s) = 0 →
        s ∈ (RingHom.ker g) • (⊤ : Submodule A (SecOnR f M V)) := by
  letI := g.toAlgebra
  have hb := SecOnR.baseChangeHom_bijective (R := A) (R' := A') hM H hV rfl
  constructor
  · intro y
    obtain ⟨z, hz⟩ := hb.2 y
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective A (SecOnR f M V) A' hg z
    refine ⟨x, ?_⟩
    have h := (SecOnR.baseChangeHom_tmul (R := A) (R' := A') H.w le_rfl 1 x).symm.trans hz
    rw [one_smul] at h
    exact h
  · intro s hs
    refine mem_ker_smul_top_of_one_tmul_eq_zero hg s (hb.1 ?_)
    rw [map_zero, SecOnR.baseChangeHom_tmul, one_smul]
    exact hs

/- English proof (translation)
Proceed by induction on `hs using Submodule.smul_induction_on' with`. Consider the case `smul a ha m _`. Take `⟨r, hr, rfl⟩` from `hK a ha`. Establish `e : SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V ((SecOnR.of f M V).symm (q r • m)) = r • SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V ((SecOnR.of f M V).symm m)`. Rewrite using `[SecOnR.smul_def r, cst_comp_spec]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`. Consider the case `add x _ y _ hx hy`. Rewrite using `[map_add, map_add]`.

Conclude with `add_mem hx hy`.
-/
theorem mem_smul_top_of_comp {X : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) (q : R →+* A) (M : LB X) (V : X.Opens) (J : Ideal A)
    (K : Ideal R) (hK : ∀ a ∈ J, ∃ r ∈ K, q r = a) (s : SecOnR f M V)
    (hs : s ∈ J • (⊤ : Submodule A (SecOnR f M V))) :
    SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V ((SecOnR.of f M V).symm s) ∈
      K • (⊤ : Submodule R (SecOnR (f ≫ Spec.map (CommRingCat.ofHom q)) M V)) := by
  induction hs using Submodule.smul_induction_on' with
  | smul a ha m _ =>
    obtain ⟨r, hr, rfl⟩ := hK a ha
    have e : SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V
        ((SecOnR.of f M V).symm (q r • m)) =
        r • SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V ((SecOnR.of f M V).symm m) := by
      rw [SecOnR.smul_def r, cst_comp_spec]
      rfl
    rw [e]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  | add x _ y _ hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy

/- English proof (translation)
Introduce `R _ I Y β hβ L w hL e V V' h hV`. Substitute `h` using the available equality. Establish `hle : I ^ (e + 1 + 1) ≤ I ^ (e + 1)` using `Ideal.pow_le_pow_right (Nat.le_succ (e + 1))`. Establish `hq : Function.Surjective (Ideal.Quotient.factor hle)` using `Ideal.Quotient.factor_surjective hle`. Take `⟨h1, h2⟩` from `pull_surjective_ker (Ideal.Quotient.factor hle) hq (hβ e) (hL (e + 1)).1 hV`.

Set `E` to `SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e) (hL e).2 (β e ⁻¹ᵁ V))`. Establish `hred (s) : redL I Y β hβ L w hL e V _ le_rfl s = E.symm (SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V _ le_rfl s)` using `rfl`. Use `⟨fun y => ?_, le_antisymm (fun s hs => ?_) (Submodule.smul_le.2 fun r hr s _ => ?_)⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `h1 (E y)`. Conclude with `⟨x, (hred x).trans ((E.symm_apply_eq).2 hx)⟩`.

Establish `hs0` using `(E.symm.map_eq_zero_iff).1 ((hred s).symm.trans (LinearMap.mem_ker.1 hs))`. Use `mem_smul_top_of_comp (Y (e + 1)).hom (Ideal.Quotient.mk (I ^ (e + 1 + 1))) (L (e + 1)) V (RingHom.ker (Ideal.Quotient.factor hle)) (I ^ (e + 1)) (fun a ha => ?_) s (h2 s hs0)` and prove the remaining obligations. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Use `⟨r, ?_, rfl⟩` and prove the remaining obligations. Rewrite `ha` using `[RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `ha`. Rewrite using `[LinearMap.mem_ker, map_smul, SecOnR.smul_def]`. Establish `e0 : cst (toR I Y e) (β e ⁻¹ᵁ V) r = 0`. Rewrite using `[toR, cst_comp_spec, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]`. Rewrite using `[e0, zero_smul]`.
-/
theorem redL_surjective_ker : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens) (V' : (Y e).left.Opens) (h : β e ⁻¹ᵁ V = V'), IsAffineOpen V → Function.Surjective (redL I Y β hβ L w hL e V V' h.ge) ∧ LinearMap.ker (redL I Y β hβ L w hL e V V' h.ge) = I ^ (e + 1) • ⊤ := by
  intro R _ I Y β hβ L w hL e V V' h hV
  subst h
  have hle : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (Nat.le_succ (e + 1))
  have hq : Function.Surjective (Ideal.Quotient.factor hle) := Ideal.Quotient.factor_surjective hle
  obtain ⟨h1, h2⟩ := pull_surjective_ker (Ideal.Quotient.factor hle) hq (hβ e) (hL (e + 1)).1 hV
  let E := SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 (β e ⁻¹ᵁ V))
  have hred (s) : redL I Y β hβ L w hL e V _ le_rfl s =
      E.symm (SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V _ le_rfl s) := rfl
  refine ⟨fun y => ?_, le_antisymm (fun s hs => ?_) (Submodule.smul_le.2 fun r hr s _ => ?_)⟩
  · obtain ⟨x, hx⟩ := h1 (E y)
    exact ⟨x, (hred x).trans ((E.symm_apply_eq).2 hx)⟩
  · have hs0 := (E.symm.map_eq_zero_iff).1 ((hred s).symm.trans (LinearMap.mem_ker.1 hs))
    refine mem_smul_top_of_comp (Y (e + 1)).hom (Ideal.Quotient.mk (I ^ (e + 1 + 1))) (L (e + 1)) V
      (RingHom.ker (Ideal.Quotient.factor hle)) (I ^ (e + 1)) (fun a ha => ?_) s (h2 s hs0)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨r, ?_, rfl⟩
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
    exact ha
  · rw [LinearMap.mem_ker, map_smul, SecOnR.smul_def]
    have e0 : cst (toR I Y e) (β e ⁻¹ᵁ V) r = 0 := by
      rw [toR, cst_comp_spec, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
    rw [e0, zero_smul]

end GlobalTheory.CompanionTheory.FormalAlg.Lift
