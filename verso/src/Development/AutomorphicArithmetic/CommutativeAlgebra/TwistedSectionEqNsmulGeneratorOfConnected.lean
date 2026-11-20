import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCover
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

/- English proof (translation)
Establish `h : ((q : ℕ) : ULift.{1} (ZMod q)) = 0`. Apply `ULift.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), h, zero_smul]`.
-/
private theorem tw_q_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) : q • a = 0 := by
  have h : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), h, zero_smul]

/- English proof (translation)
Use `conv_lhs => rw [← Nat.mod_add_div n q]`. Rewrite using `[add_nsmul, mul_comm, mul_nsmul, tw_q_nsmul, add_zero]`.
-/
private theorem tw_nsmul_mod {q : ℕ} {i : ℤ} {U : Scheme.{0}} (a : Sec (tw q i) U) (n : ℕ) :
    n • a = (n % q) • a := by
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_nsmul, mul_comm, mul_nsmul, tw_q_nsmul, add_zero]

/- English proof (translation)
Establish `hq : 1 ≤ q` using `NeZero.pos q`. Establish `h1 : (q - 1) * c' + c' = q * c'`. Establish `: (q - 1) * c' + c' = ((q - 1) + 1) * c'` using `by ring`. Rewrite using `[this, Nat.sub_add_cancel hq]`. Establish `h0 : (c + (q - 1) * c') • twGen i ζ = 0`.

Rewrite using `[add_nsmul, h, ← add_nsmul, add_comm, h1, mul_comm, mul_nsmul, tw_q_nsmul]`. Take `⟨k, hk⟩` from `(GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ _ h0`. Establish `h2 : c + q * c' = c' + q * k`. Rewrite using `[← hk, ← h1]`. Expand and normalize the polynomial expressions, which then agree.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mod_eq_of_nsmul_eq {q : ℕ} [NeZero q] {i : ℤ} {U : Scheme.{0}} [Nonempty U]
    (ζ : Prim q Γ(U, ⊤)) {c c' : ℕ} (h : c • twGen i ζ = c' • twGen i ζ) : c % q = c' % q := by
  have hq : 1 ≤ q := NeZero.pos q
  have h1 : (q - 1) * c' + c' = q * c' := by
    have : (q - 1) * c' + c' = ((q - 1) + 1) * c' := by ring
    rw [this, Nat.sub_add_cancel hq]
  have h0 : (c + (q - 1) * c') • twGen i ζ = 0 := by
    rw [add_nsmul, h, ← add_nsmul, add_comm, h1, mul_comm, mul_nsmul, tw_q_nsmul]
  obtain ⟨k, hk⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ _ h0
  have h2 : c + q * c' = c' + q * k := by
    rw [← hk, ← h1]
    ring
  calc c % q = (c + q * c') % q := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (c' + q * k) % q := by rw [h2]
    _ = c' % q := Nat.add_mul_mod_self_left _ _ _

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (a : Sec F U) : Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

/- English proof (translation)
The claim follows from `map_nsmul (F.obj.map k.op).hom n a`.
-/
private theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

/- English proof (translation)
Rewrite using `[(GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1]`. Use `congr 1`.
-/
private theorem res_gen {q : ℕ} [NeZero q] {i : ℤ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (ζ : Prim q Γ(U, ⊤)) :
    Sec.res k (twGen i (ζ.map g.appTop.hom)) = twGen i (ζ.map (k ≫ g).appTop.hom) := by
  rw [(GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1]
  congr 1

/- English proof (translation)
Introduce `q _ i X _ ζ y`. Take `⟨S, hS, hP⟩` from `(GlobalTheory.T.tateTwist_sections_locally_generated q i).2.1 X ζ y`. Establish `hpts` using `(loc_iff_etale_affine_points X (fun V g => S.arrows g) (fun V W g k h => S.downward_closed h k)).1 ⟨S, hS, fun _ _ h => h⟩`. Use `choose V g hA hE hx hS' using hpts`. Use `choose c hc using fun x => hP (V x) (g x) (hS' x)`.

Establish `hlc : IsLocallyConstant (fun x => c x % q)`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `haveI := hE x`. Use `⟨Set.range (g x), (g x).isOpenMap.isOpen_range, hx x, ?_⟩` and prove the remaining obligations.

Introduce and unpack `x' ⟨v, hv⟩`. Take `⟨v', hv'⟩` from `hx x'`. Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := g x) (g := g x') v v' (hv.trans hv'.symm)`. Use `haveI : Nonempty ↥(pullback (g x) (g x')) := ⟨z⟩`. Establish `e1` using `congrArg (Sec.res (pullback.fst (g x) (g x'))) (hc x)`.

Establish `e2` using `congrArg (Sec.res (pullback.snd (g x) (g x'))) (hc x')`. Rewrite `e1`, `e2` using `[← res_comp, res_nsmul, res_gen]`. Rewrite `e1` using `[pullback.condition]`. Conclude with `(mod_eq_of_nsmul_eq _ (e1.symm.trans e2)).symm`. Take `⟨x0⟩ : Nonempty X` from `inferInstance`.

Establish `hconst : ∀ x, c x % q = c x0 % q` using `fun x => hlc.apply_eq_of_preconnectedSpace x x0`. Use `⟨c x0, (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) X).1 _ _ ?_⟩` and prove the remaining obligations. Use `(loc_iff_etale_affine_points X _ ?_).2 fun x => ⟨V x, g x, hA x, hE x, hx x, ?_⟩` and prove the remaining obligations. Introduce `V W g k h`. Rewrite using `[res_comp, res_comp, h]`.

Rewrite using `[hc, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1, tw_nsmul_mod, hconst x, ← tw_nsmul_mod]`.
-/
theorem UpperTheory.twisted_section_eq_nsmul_generator_of_connected :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}) [ConnectedSpace X] (ζ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X), ∃ c : ℕ, y = c • twGen i ζ := by
  intro q _ i X _ ζ y
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.1 X ζ y
  have hpts := (loc_iff_etale_affine_points X (fun V g => S.arrows g)
    (fun V W g k h => S.downward_closed h k)).1 ⟨S, hS, fun _ _ h => h⟩
  choose V g hA hE hx hS' using hpts
  choose c hc using fun x => hP (V x) (g x) (hS' x)
  have hlc : IsLocallyConstant (fun x => c x % q) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    haveI := hE x
    refine ⟨Set.range (g x), (g x).isOpenMap.isOpen_range, hx x, ?_⟩
    rintro x' ⟨v, hv⟩
    obtain ⟨v', hv'⟩ := hx x'
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g x) (g := g x') v v' (hv.trans hv'.symm)
    haveI : Nonempty ↥(pullback (g x) (g x')) := ⟨z⟩
    have e1 := congrArg (Sec.res (pullback.fst (g x) (g x'))) (hc x)
    have e2 := congrArg (Sec.res (pullback.snd (g x) (g x'))) (hc x')
    rw [← res_comp, res_nsmul, res_gen] at e1 e2
    rw [pullback.condition] at e1
    exact (mod_eq_of_nsmul_eq _ (e1.symm.trans e2)).symm
  obtain ⟨x0⟩ : Nonempty X := inferInstance
  have hconst : ∀ x, c x % q = c x0 % q := fun x => hlc.apply_eq_of_preconnectedSpace x x0
  refine ⟨c x0, (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) X).1 _ _ ?_⟩
  refine (loc_iff_etale_affine_points X _ ?_).2 fun x => ⟨V x, g x, hA x, hE x, hx x, ?_⟩
  · intro V W g k h
    rw [res_comp, res_comp, h]
  · rw [hc, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1, tw_nsmul_mod, hconst x, ← tw_nsmul_mod]
