import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleTateTwistSheafFlat

open Polynomial

noncomputable section
set_option linter.unusedSectionVars false

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable {q : ℕ} {A : Type} [CommRing A]

/- English proof (translation)
Take `⟨g, hg⟩` from `cyclotomic.dvd_X_pow_sub_one q ℤ`. Establish `h` using `congrArg (aeval ζ.1) hg`. Rewrite `h` using `[map_mul, ζ.2.2, zero_mul, map_sub, map_pow, aeval_X, map_one]`. Conclude with `sub_eq_zero.1 h`.
-/
theorem prim_pow_q (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, aeval_X, map_one] at h
  exact sub_eq_zero.1 h

/- English proof (translation)
Use `conv_rhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, prim_pow_q, one_pow, one_mul]`.
-/
theorem pow_mod_q (ζ : Prim q A) (n : ℕ) : ζ.1 ^ (n % q) = ζ.1 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, prim_pow_q, one_pow, one_mul]

/- English proof (translation)
Rewrite using `[ZMod.val_one_eq_one_mod, pow_mod_q, pow_one]`.
-/
theorem pow_val_one (ζ : Prim q A) : ζ.1 ^ (1 : ZMod q).val = ζ.1 := by
  rw [ZMod.val_one_eq_one_mod, pow_mod_q, pow_one]

/- English proof (translation)
Rewrite using `[ZMod.val_mul, pow_mod_q, pow_mul]`.
-/
theorem pow_val_mul (ζ : Prim q A) (a b : ZMod q) : ζ.1 ^ (a * b).val = (ζ.1 ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, pow_mod_q, pow_mul]

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal A`. Set `π : A →+* A ⧸ m` to `Ideal.Quotient.mk m`. Establish `: NeZero ((q : ℕ) : A ⧸ m)` using `⟨by`. Establish `hu` using `ζ.2.1.map π`. Rewrite `hu` using `[map_natCast]`.

Conclude with `hu.ne_zero⟩`. Establish `hr : IsRoot (cyclotomic q (A ⧸ m)) (π ζ.1)`. Establish `h2` using `aeval_algHom_apply π.toIntAlgHom ζ.1 (cyclotomic q ℤ)`. Rewrite `h2` using `[ζ.2.2, map_zero]`. Rewrite using `[IsRoot, ← map_cyclotomic q (algebraMap ℤ (A ⧸ m)), eval_map_algebraMap]`.

Conclude with `h2`. Establish `hp : IsPrimitiveRoot (π ζ.1) q` using `(isRoot_cyclotomic_iff).1 hr`. Establish `h3 : (π ζ.1) ^ a.val = (π ζ.1) ^ b.val` using `by rw [← map_pow, ← map_pow, h]`. Conclude with `ZMod.val_injective q (hp.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h3)`.
-/
theorem val_inj [NeZero q] [Nontrivial A] (ζ : Prim q A) (a b : ZMod q) (h : ζ.1 ^ a.val = ζ.1 ^ b.val) : a = b := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let π : A →+* A ⧸ m := Ideal.Quotient.mk m
  have : NeZero ((q : ℕ) : A ⧸ m) := ⟨by
    have hu := ζ.2.1.map π
    rw [map_natCast] at hu
    exact hu.ne_zero⟩
  have hr : IsRoot (cyclotomic q (A ⧸ m)) (π ζ.1) := by
    have h2 := aeval_algHom_apply π.toIntAlgHom ζ.1 (cyclotomic q ℤ)
    rw [ζ.2.2, map_zero] at h2
    rw [IsRoot, ← map_cyclotomic q (algebraMap ℤ (A ⧸ m)), eval_map_algebraMap]
    exact h2
  have hp : IsPrimitiveRoot (π ζ.1) q := (isRoot_cyclotomic_iff).1 hr
  have h3 : (π ζ.1) ^ a.val = (π ζ.1) ^ b.val := by rw [← map_pow, ← map_pow, h]
  exact ZMod.val_injective q (hp.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h3)

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable (q : ℕ) [NeZero q] (A : Type) [CommRing A]

def Rel (ζ ξ : Prim q A) : Prop := ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val

def St : Setoid (Prim q A) where
  r := Rel q A
  iseqv := by
    refine ⟨fun ζ => ⟨1, by rw [Units.val_one, pow_val_one]⟩, ?_, ?_⟩
    · rintro ζ ξ ⟨a, h⟩
      refine ⟨a⁻¹, ?_⟩
      rw [h, ← pow_val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, pow_val_one]
    · rintro ζ ξ η ⟨a, h⟩ ⟨b, h'⟩
      exact ⟨a * b, by rw [h', h, Units.val_mul, pow_val_mul]⟩

variable {q A}

def rep (ξ : Prim q A) : Prim q A := (Quotient.mk (St q A) ξ).out

/- English proof (translation)
The claim follows from `Quotient.mk_out (s := St q A) ξ`.
-/
theorem rep_rel (ξ : Prim q A) : Rel q A (rep ξ) ξ := Quotient.mk_out (s := St q A) ξ

def cc (ξ : Prim q A) : (ZMod q)ˣ := (rep_rel ξ).choose

/- English proof (translation)
The claim follows from `(rep_rel ξ).choose_spec`.
-/
theorem cc_spec (ξ : Prim q A) : ξ.1 = (rep ξ).1 ^ (cc ξ : ZMod q).val := (rep_rel ξ).choose_spec

/- English proof (translation)
Unfold `rep`. Rewrite using `[Quotient.sound (s := St q A) h]`.
-/
theorem rep_eq {ζ ξ : Prim q A} (h : Rel q A ζ ξ) : rep ζ = rep ξ := by
  unfold rep; rw [Quotient.sound (s := St q A) h]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `val_inj (rep ξ)` to reduce the goal to its premises. Rewrite using `[← cc_spec ξ, Units.val_mul, pow_val_mul, ← rep_eq ⟨a, h⟩, ← cc_spec ζ, h]`.
-/
theorem cc_mul [Nontrivial A] {ζ ξ : Prim q A} (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    cc ξ = cc ζ * a := by
  apply Units.ext
  apply val_inj (rep ξ)
  rw [← cc_spec ξ, Units.val_mul, pow_val_mul, ← rep_eq ⟨a, h⟩, ← cc_spec ζ, h]

/- English proof (translation)
Establish `hr : rep o.out = o.out` using `by show (Quotient.mk (St q A) o.out).out = o.out`. Rewrite using `[Quotient.out_eq]`. Apply `Units.ext` to reduce the goal to its premises. Apply `val_inj o.out` to reduce the goal to its premises. Establish `h` using `cc_spec o.out`.

Rewrite `h` using `[hr]`. Rewrite using `[← h, Units.val_one, pow_val_one]`.
-/
theorem cc_out [Nontrivial A] (o : Quotient (St q A)) : cc o.out = 1 := by
  have hr : rep o.out = o.out := by
    show (Quotient.mk (St q A) o.out).out = o.out
    rw [Quotient.out_eq]
  apply Units.ext
  apply val_inj o.out
  have h := cc_spec o.out
  rw [hr] at h
  rw [← h, Units.val_one, pow_val_one]

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable {q : ℕ} [NeZero q] {A : Type} [CommRing A]

def wt (i : ℤ) (ξ : Prim q A) : ULift.{1} (ZMod q) := ULift.up (((cc ξ ^ i : (ZMod q)ˣ)) : ZMod q)

def psi0 (i : ℤ) : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] (Quotient (St q A) →₀ ULift.{1} (ZMod q)) :=
  Finsupp.linearCombination _ fun ξ => Finsupp.single (Quotient.mk (St q A) ξ) (wt i ξ)

/- English proof (translation)
Rewrite using `[psi0, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul]`.
-/
theorem primitive_roots_twisted_weight_map_single (i : ℤ) (ξ : Prim q A) (r : ULift.{1} (ZMod q)) :
    psi0 i (Finsupp.single ξ r) = Finsupp.single (Quotient.mk (St q A) ξ) (r * wt i ξ) := by
  rw [psi0, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul]

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨ζ, ξ, a, h, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, primitive_roots_twisted_weight_map_single]`. Rewrite using `[sub_eq_zero, Quotient.sound (s := St q A) (⟨a, h⟩ : Rel q A ζ ξ)]`. Use `congr 1`.

Apply `ULift.ext` to reduce the goal to its premises. Simplify using `only [wt, ULift.mul_down, cc_mul a h, mul_zpow, Units.val_mul, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rel_le [Nontrivial A] (i : ℤ) : twRel q i A ≤ LinearMap.ker (psi0 i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, primitive_roots_twisted_weight_map_single]
  rw [sub_eq_zero, Quotient.sound (s := St q A) (⟨a, h⟩ : Rel q A ζ ξ)]
  congr 1
  apply ULift.ext
  simp only [wt, ULift.mul_down, cc_mul a h, mul_zpow, Units.val_mul, one_mul]
  ring

def phi [Nontrivial A] (i : ℤ) : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)]
    (Quotient (St q A) →₀ ULift.{1} (ZMod q)) := (twRel q i A).liftQ (psi0 i) (rel_le i)

def theta (i : ℤ) : (Quotient (St q A) →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)]
    ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  (twRel q i A).mkQ ∘ₗ Finsupp.lmapDomain _ _ (fun o : Quotient (St q A) => o.out)

/- English proof (translation)
Use `Finsupp.lhom_ext fun o r => ?_` and prove the remaining obligations. Simplify using `only [theta, phi, LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Submodule.mkQ_apply, Submodule.liftQ_apply, primitive_roots_twisted_weight_map_single, LinearMap.id_apply]`. Rewrite using `[Quotient.out_eq]`. Use `congr 1`. Rewrite using `[wt, cc_out, one_zpow, Units.val_one]`.

Apply `ULift.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem phi_theta [Nontrivial A] (i : ℤ) : phi i ∘ₗ theta (q := q) (A := A) i = LinearMap.id := by
  refine Finsupp.lhom_ext fun o r => ?_
  simp only [theta, phi, LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Submodule.mkQ_apply, Submodule.liftQ_apply, primitive_roots_twisted_weight_map_single, LinearMap.id_apply]
  rw [Quotient.out_eq]
  congr 1
  rw [wt, cc_out, one_zpow, Units.val_one]
  apply ULift.ext
  simp

/- English proof (translation)
Use `Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ξ r => ?_)` and prove the remaining obligations. Simplify using `only [theta, phi, LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Submodule.mkQ_apply, Submodule.liftQ_apply, primitive_roots_twisted_weight_map_single, LinearMap.id_apply]`. Use `(Submodule.Quotient.eq _).2 ?_` and prove the remaining obligations. Establish `hm : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single (rep ξ) (ULift.up ((cc ξ ^ i : (ZMod q)ˣ) : ZMod q)) ∈ twRel q i A` using `Submodule.subset_span ⟨rep ξ, ξ, cc ξ, cc_spec ξ, rfl⟩`. Establish `h2` using `Submodule.smul_mem _ r hm`.

Rewrite `h2` using `[smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]`. Rewrite using `[← neg_mem_iff, neg_sub]`. Conclude with `h2`.
-/
theorem theta_phi [Nontrivial A] (i : ℤ) : theta i ∘ₗ phi (q := q) (A := A) i = LinearMap.id := by
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ξ r => ?_)
  simp only [theta, phi, LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Submodule.mkQ_apply, Submodule.liftQ_apply, primitive_roots_twisted_weight_map_single, LinearMap.id_apply]
  refine (Submodule.Quotient.eq _).2 ?_
  have hm : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single (rep ξ) (ULift.up ((cc ξ ^ i : (ZMod q)ˣ) : ZMod q))
      ∈ twRel q i A := Submodule.subset_span ⟨rep ξ, ξ, cc ξ, cc_spec ξ, rfl⟩
  have h2 := Submodule.smul_mem _ r hm
  rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one] at h2
  rw [← neg_mem_iff, neg_sub]
  exact h2

/- English proof (translation)
The claim follows from `Module.Flat.of_linearEquiv (LinearEquiv.ofLinearMap (phi i) (theta i) (phi_theta i) (theta_phi i))`.
-/
theorem flat_of_nontrivial [Nontrivial A] (i : ℤ) :
    Module.Flat (ULift.{1} (ZMod q)) ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  Module.Flat.of_linearEquiv (LinearEquiv.ofLinearMap (phi i) (theta i) (phi_theta i) (theta_phi i))

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `U y`. Use `⟨Presheaf.imageSieve (toSheafify Scheme.etaleTopology P) y, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y, ?_⟩` and prove the remaining obligations. Introduce and unpack `V g ⟨t, ht⟩`. Conclude with `⟨t, ht⟩`.

Introduce `U x hx`. Establish `h : (toSheafify Scheme.etaleTopology P).app (op U) x = (toSheafify Scheme.etaleTopology P).app (op U) 0`. Express the relevant statement in the definitionally equal form `((toSheafify Scheme.etaleTopology P).app (op U)).hom x = ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0`. Rewrite using `[hx, map_zero]`. Use `⟨Presheaf.equalizerSieve (F := P) (X := op U) x 0, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h, ?_⟩` and prove the remaining obligations.

Introduce `V g hg`. Establish `hg' : (P.map g.op).hom x = (P.map g.op).hom 0` using `hg`. Rewrite using `[hg', map_zero]`.
-/
theorem shf_loc (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U),
      Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 →
      Loc U fun _ g => (P.map g.op).hom x = 0) := by
  constructor
  · intro U y
    refine ⟨Presheaf.imageSieve (toSheafify Scheme.etaleTopology P) y,
      Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y, ?_⟩
    rintro V g ⟨t, ht⟩
    exact ⟨t, ht⟩
  · intro U x hx
    have h : (toSheafify Scheme.etaleTopology P).app (op U) x = (toSheafify Scheme.etaleTopology P).app (op U) 0 := by
      change ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0
      rw [hx, map_zero]
    refine ⟨Presheaf.equalizerSieve (F := P) (X := op U) x 0,
      Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h, ?_⟩
    intro V g hg
    have hg' : (P.map g.op).hom x = (P.map g.op).hom 0 := hg
    rw [hg', map_zero]

end LateralTheory.EtaleFoundations.TwFlat

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC in

/- English proof (translation)
Introduce `q _ i`. Take `⟨h1, h2⟩` from `LateralTheory.EtaleFoundations.TwFlat.shf_loc (ZMod q) (Scheme.Γ ⋙ twF q i)`. Use `⟨Scheme.Γ ⋙ twF q i, toSheafify Scheme.etaleTopology _, h1, h2, fun U hU => ?_⟩` and prove the remaining obligations. Establish `: Nonempty (⊤ : U.Opens)` using `⟨⟨hU.some, trivial⟩⟩`. Conclude with `LateralTheory.EtaleFoundations.TwFlat.flat_of_nontrivial (A := Γ(U, ⊤)) i`.
-/
theorem LateralTheory.EtaleFoundations.etale_tate_twist_sections_flat_of_quotient_iso : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := by
  intro q _ i
  obtain ⟨h1, h2⟩ := LateralTheory.EtaleFoundations.TwFlat.shf_loc (ZMod q) (Scheme.Γ ⋙ twF q i)
  refine ⟨Scheme.Γ ⋙ twF q i, toSheafify Scheme.etaleTopology _, h1, h2, fun U hU => ?_⟩
  have : Nonempty (⊤ : U.Opens) := ⟨⟨hU.some, trivial⟩⟩
  exact LateralTheory.EtaleFoundations.TwFlat.flat_of_nontrivial (A := Γ(U, ⊤)) i
