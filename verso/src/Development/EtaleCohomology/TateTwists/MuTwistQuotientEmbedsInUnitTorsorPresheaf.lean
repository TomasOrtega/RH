import Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistIntoTorsorSheafOfMuQuotientAndPreshe

open CategoryTheory GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations.KTP

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (Finsupp.lmapDomain _ _ _ (Finsupp.single ζ 1)) = _`. Simplify using `[Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]`. Both sides reduce to the same expression.
-/
theorem twGenR_nat {q : ℕ} (A B : CommRingCat.{0}) (f : A ⟶ B) (ζ : Prim q A) :
    ((twF q 1).map f).hom (twGenR A ζ) = twGenR B (Prim.map f.hom ζ) := by
  change Submodule.Quotient.mk (Finsupp.lmapDomain _ _ _ (Finsupp.single ζ 1)) = _
  simp [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

/- English proof (translation)
Take `⟨p, hp⟩` from `Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ`. Establish `h` using `congrArg (Polynomial.aeval ζ.1) hp`. Simplify using `only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h`. Conclude with `sub_eq_zero.1 h`.
-/
theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.1 h

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => simp [mul_pow, prim_pow, ih]`.
-/
theorem list_pow {q : ℕ} {A : Type} [CommRing A] (l : List (Prim q A)) : ((l.map fun ζ => ζ.1).prod) ^ q = 1 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [mul_pow, prim_pow, ih]

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]`. Establish `: ((q : ℕ) : ULift.{1} (ZMod q)) = 0`. Apply `ULift.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[this, zero_smul]`.
-/
theorem q_smul {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext; simp
  rw [this, zero_smul]

variable {q : ℕ} {A : Type} [CommRing A] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]

/- English proof (translation)
Establish `hq : 1 ≤ q` using `Nat.one_le_iff_ne_zero.2 (NeZero.ne q)`. Use `hl (l1 ++ (List.replicate (q - 1) l2).flatten) (by` as an intermediate fact. Simplify using `only [List.map_append, List.prod_append, List.map_flatten, List.map_replicate, List.prod_flatten, List.prod_replicate, h, ← pow_succ']`. Rewrite using `[Nat.sub_add_cancel hq, list_pow])`. Simplify using `only [List.map_append, List.sum_append, List.map_flatten, List.map_replicate, List.sum_flatten, List.sum_replicate] at this`.

Establish `h2` using `q_smul (q := q) (l2.map τ').sum`. Establish `h3 : q • (l2.map τ').sum = (q - 1) • (l2.map τ').sum + (l2.map τ').sum`. Rewrite using `[← succ_nsmul, Nat.sub_add_cancel hq]`. Rewrite `h2` using `[h3]`. Use `this.trans h2.symm` as an intermediate fact.

Rewrite `this` using `[add_comm ((q-1) • _) _]`. Conclude with `add_left_cancel (a := (q-1) • (l2.map τ').sum) (by rw [add_comm _ (List.sum _), this, add_comm])`.
-/
theorem sum_eq_of_prod_eq [NeZero q] (τ' : Prim q A → M)
    (hl : ∀ l : List (Prim q A), (l.map fun ζ => ζ.1).prod = 1 → (l.map τ').sum = 0)
    (l1 l2 : List (Prim q A)) (h : (l1.map fun ζ => ζ.1).prod = (l2.map fun ζ => ζ.1).prod) :
    (l1.map τ').sum = (l2.map τ').sum := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have := hl (l1 ++ (List.replicate (q - 1) l2).flatten) (by
    simp only [List.map_append, List.prod_append, List.map_flatten, List.map_replicate, List.prod_flatten,
      List.prod_replicate, h, ← pow_succ']
    rw [Nat.sub_add_cancel hq, list_pow])
  simp only [List.map_append, List.sum_append, List.map_flatten, List.map_replicate, List.sum_flatten,
    List.sum_replicate] at this
  have h2 := q_smul (q := q) (l2.map τ').sum
  have h3 : q • (l2.map τ').sum = (q - 1) • (l2.map τ').sum + (l2.map τ').sum := by
    rw [← succ_nsmul, Nat.sub_add_cancel hq]
  rw [h3] at h2
  have := this.trans h2.symm
  rw [add_comm ((q-1) • _) _] at this
  exact add_left_cancel (a := (q-1) • (l2.map τ').sum) (by rw [add_comm _ (List.sum _), this, add_comm])

def rel (q : ℕ) [NeZero q] (A : Type) [CommRing A] : Setoid Aˣ where
  r x y := ∃ l : List (Prim q A), (y : A) = (l.map fun ζ => ζ.1).prod * x
  iseqv := by
    refine ⟨fun x => ⟨[], by simp⟩, ?_, ?_⟩
    · rintro x y ⟨l, hl⟩
      refine ⟨(List.replicate (q - 1) l).flatten, ?_⟩
      have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
      simp only [List.map_flatten, List.map_replicate, List.prod_flatten, List.prod_replicate, hl, ← mul_assoc,
        ← pow_succ]
      rw [Nat.sub_add_cancel hq, list_pow, one_mul]
    · rintro x y z ⟨l, hl⟩ ⟨m, hm⟩
      exact ⟨m ++ l, by simp [hm, hl, mul_assoc]⟩

/- English proof (translation)
Set `S` to `rel q A`. Set `r : Aˣ → Aˣ` to `fun x => Quotient.out (s := S) (Quotient.mk S x)`. Establish `hr : ∀ x, S.r (r x) x` using `fun x => Quotient.exact (s := S) (Quotient.out_eq (s := S) (Quotient.mk S x))`. Set `L : Aˣ → List (Prim q A)` to `fun x => Classical.choose (hr x)`. Establish `hL : ∀ x : Aˣ, (x : A) = ((L x).map fun ζ => ζ.1).prod * (r x : A)` using `fun x => Classical.choose_spec (hr x)`.

Use `⟨fun x => ((L x).map τ').sum, ?_⟩` and prove the remaining obligations. Introduce `ζ v w h`. Establish `hvw : S.r v w` using `⟨[ζ], by simp [h]⟩`. Establish `hrr : r w = r v` using `by show Quotient.out (s := S) (Quotient.mk S w) = Quotient.out (s := S) (Quotient.mk S v)`. Rewrite using `[Quotient.sound (s := S) (S.iseqv.symm hvw)]`.

Establish `key : ((L w).map fun ζ => ζ.1).prod = ((ζ :: L v).map fun ζ => ζ.1).prod`. Establish `e1` using `hL w`. Rewrite `e1` using `[h, hL v, hrr, ← mul_assoc]`. Simplify using `only [List.map_cons, List.prod_cons]`. Conclude with `((Units.isUnit (r v)).mul_left_inj).1 e1.symm`.

Use `show ((L w).map τ').sum = ((L v).map τ').sum + τ' ζ`. Rewrite using `[sum_eq_of_prod_eq τ' hl _ _ key]`. Simplify using `[add_comm]`.
-/
theorem exists_chi [NeZero q] (τ' : Prim q A → M)
    (hl : ∀ l : List (Prim q A), (l.map fun ζ => ζ.1).prod = 1 → (l.map τ').sum = 0) :
    ∃ χ : Aˣ → M, ∀ (ζ : Prim q A) (v w : Aˣ), (w : A) = ζ.1 * v → χ w = χ v + τ' ζ := by
  classical
  let S := rel q A
  let r : Aˣ → Aˣ := fun x => Quotient.out (s := S) (Quotient.mk S x)
  have hr : ∀ x, S.r (r x) x := fun x => Quotient.exact (s := S) (Quotient.out_eq (s := S) (Quotient.mk S x))
  let L : Aˣ → List (Prim q A) := fun x => Classical.choose (hr x)
  have hL : ∀ x : Aˣ, (x : A) = ((L x).map fun ζ => ζ.1).prod * (r x : A) := fun x => Classical.choose_spec (hr x)
  refine ⟨fun x => ((L x).map τ').sum, ?_⟩
  intro ζ v w h
  have hvw : S.r v w := ⟨[ζ], by simp [h]⟩
  have hrr : r w = r v := by
    show Quotient.out (s := S) (Quotient.mk S w) = Quotient.out (s := S) (Quotient.mk S v)
    rw [Quotient.sound (s := S) (S.iseqv.symm hvw)]
  have key : ((L w).map fun ζ => ζ.1).prod = ((ζ :: L v).map fun ζ => ζ.1).prod := by
    have e1 := hL w
    rw [h, hL v, hrr, ← mul_assoc] at e1
    simp only [List.map_cons, List.prod_cons]
    exact ((Units.isUnit (r v)).mul_left_inj).1 e1.symm
  show ((L w).map τ').sum = ((L v).map τ').sum + τ' ζ
  rw [sum_eq_of_prod_eq τ' hl _ _ key]
  simp [add_comm]

noncomputable section Cons
variable (q : ℕ) (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T)

abbrev R := ULift.{1} (ZMod q)

abbrev Mo (A : CommRingCat.{0}) := (T.obj A) × ((A : Type)ˣ →₀ R q)

def Idx (A : CommRingCat.{0}) := {p : Prim q A × (A : Type)ˣ × (A : Type)ˣ // ((p.2.2 : (A : Type))) = p.1.1 * p.2.1}

def relv (A : CommRingCat.{0}) (p : Idx q A) : Mo q T A :=
  (-(τ.app A).hom (twGenR A p.1.1), Finsupp.single p.1.2.2 1 - Finsupp.single p.1.2.1 1)

def N (A : CommRingCat.{0}) : Submodule (R q) (Mo q T A) := Submodule.span (R q) (Set.range (relv q T τ A))

def Gm {A B : CommRingCat.{0}} (f : A ⟶ B) : Mo q T A →ₗ[R q] Mo q T B :=
  (T.map f).hom.prodMap (Finsupp.lmapDomain (R q) (R q) (Units.map f.hom.toMonoidHom))

/- English proof (translation)
Rewrite using `[← twGenR_nat]`. Conclude with `congrArg (fun g => ModuleCat.Hom.hom g (twGenR A ζ)) (τ.naturality f)`.
-/
theorem tau_nat {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) :
    (τ.app B).hom (twGenR B (Prim.map f.hom ζ)) = (T.map f).hom ((τ.app A).hom (twGenR A ζ)) := by
  rw [← twGenR_nat]
  exact congrArg (fun g => ModuleCat.Hom.hom g (twGenR A ζ)) (τ.naturality f)

/- English proof (translation)
Rewrite using `[N, Submodule.span_le]`. Introduce and unpack `_ ⟨p, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨⟨(Prim.map f.hom p.1.1, Units.map f.hom.toMonoidHom p.1.2.1, Units.map f.hom.toMonoidHom p.1.2.2), ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `[Units.coe_map, p.2, Prim.map]`.

Simplify using `[relv, Gm, tau_nat, Finsupp.mapDomain_sub, Finsupp.mapDomain_single]`.
-/
theorem N_le {A B : CommRingCat.{0}} (f : A ⟶ B) : N q T τ A ≤ (N q T τ B).comap (Gm q T f) := by
  rw [N, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨(Prim.map f.hom p.1.1, Units.map f.hom.toMonoidHom p.1.2.1, Units.map f.hom.toMonoidHom p.1.2.2), ?_⟩, ?_⟩
  · simp [Units.coe_map, p.2, Prim.map]
  · simp [relv, Gm, tau_nat, Finsupp.mapDomain_sub, Finsupp.mapDomain_single]

def Gf : CommRingCat.{0} ⥤ ModuleCat.{1} (R q) where
  obj A := ModuleCat.of (R q) (Mo q T A ⧸ N q T τ A)
  map f := ModuleCat.ofHom ((N q T τ _).mapQ (N q T τ _) (Gm q T f) (N_le q T τ f))
  map_id A := by
    ext x <;> simp [Gm]
  map_comp f g := by
    ext x <;> (simp [Gm]; try rfl)

def iota : T ⟶ Gf q T τ where
  app A := ModuleCat.ofHom ((N q T τ A).mkQ ∘ₗ LinearMap.inl (R q) _ _)
  naturality A B f := by
    ext x
    change (Submodule.Quotient.mk ((T.map f).hom x, (0 : (B : Type)ˣ →₀ R q)) : Mo q T B ⧸ N q T τ B) =
      Submodule.Quotient.mk (Gm q T f (x, 0))
    simp [Gm]

def sec (A : CommRingCat.{0}) (v : (A : Type)ˣ) : (Gf q T τ).obj A :=
  Submodule.Quotient.mk (p := N q T τ A) ((0 : T.obj A), Finsupp.single v 1)

/- English proof (translation)
Use `show (Submodule.Quotient.mk (Gm q T f (0, Finsupp.single v 1)) : Mo q T B ⧸ N q T τ B) = Submodule.Quotient.mk (0, Finsupp.single _ 1)`. Simplify using `[Gm, Finsupp.mapDomain_single]`.
-/
theorem sec_nat (A B : CommRingCat.{0}) (f : A ⟶ B) (v : (A : Type)ˣ) :
    ((Gf q T τ).map f).hom (sec q T τ A v) = sec q T τ B (Units.map f.hom.toMonoidHom v) := by
  show (Submodule.Quotient.mk (Gm q T f (0, Finsupp.single v 1)) : Mo q T B ⧸ N q T τ B) =
    Submodule.Quotient.mk (0, Finsupp.single _ 1)
  simp [Gm, Finsupp.mapDomain_single]

/- English proof (translation)
Establish `hm : relv q T τ A ⟨(ζ, v, w), h⟩ ∈ N q T τ A` using `Submodule.subset_span ⟨_, rfl⟩`. Establish `key : (Submodule.Quotient.mk (0, Finsupp.single w 1) : Mo q T A ⧸ N q T τ A) = Submodule.Quotient.mk (0, Finsupp.single v 1) + Submodule.Quotient.mk ((τ.app A).hom (twGenR A ζ), 0)`. Rewrite using `[← Submodule.Quotient.mk_add, Submodule.Quotient.eq]`. Use `hm using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext <;> simp [relv]`.

Conclude with `key`.
-/
theorem sec_rel (A : CommRingCat.{0}) (ζ : Prim q A) (v w : (A : Type)ˣ) (h : (w : (A : Type)) = ζ.1 * v) :
    sec q T τ A w = sec q T τ A v + ((iota q T τ).app A).hom ((τ.app A).hom (twGenR A ζ)) := by
  have hm : relv q T τ A ⟨(ζ, v, w), h⟩ ∈ N q T τ A := Submodule.subset_span ⟨_, rfl⟩
  have key : (Submodule.Quotient.mk (0, Finsupp.single w 1) : Mo q T A ⧸ N q T τ A) =
      Submodule.Quotient.mk (0, Finsupp.single v 1) + Submodule.Quotient.mk ((τ.app A).hom (twGenR A ζ), 0) := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    convert hm using 1
    ext <;> simp [relv]
  exact key

/- English proof (translation)
Take `⟨χ, hχ⟩` from `exists_chi (M := T.obj A) (fun ζ => (τ.app A).hom (twGenR A ζ)) (hl A)`. Set `φ : Mo q T A →ₗ[R q] T.obj A` to `LinearMap.fst _ _ _ + (Finsupp.linearCombination (R q) χ) ∘ₗ LinearMap.snd _ _ _`. Establish `hN : N q T τ A ≤ LinearMap.ker φ`. Rewrite using `[N, Submodule.span_le]`. Introduce and unpack `_ ⟨⟨⟨ζ, v, w⟩, h⟩, rfl⟩`.

Simplify using `[φ, relv, hχ ζ v w h]`. Introduce `a b hab`. Establish `hab' : (Submodule.Quotient.mk (a, 0) : Mo q T A ⧸ N q T τ A) = Submodule.Quotient.mk (b, 0)` using `hab`. Rewrite `hab'` using `[Submodule.Quotient.eq]`. Use `hN hab'` as an intermediate fact.

Simplify `this` using `[φ, sub_eq_zero]`.
-/
theorem iota_inj [NeZero q]
    (hl : ∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0) (A : CommRingCat.{0}) :
    Function.Injective ((iota q T τ).app A).hom := by
  obtain ⟨χ, hχ⟩ := exists_chi (M := T.obj A) (fun ζ => (τ.app A).hom (twGenR A ζ)) (hl A)
  let φ : Mo q T A →ₗ[R q] T.obj A :=
    LinearMap.fst _ _ _ + (Finsupp.linearCombination (R q) χ) ∘ₗ LinearMap.snd _ _ _
  have hN : N q T τ A ≤ LinearMap.ker φ := by
    rw [N, Submodule.span_le]
    rintro _ ⟨⟨⟨ζ, v, w⟩, h⟩, rfl⟩
    simp [φ, relv, hχ ζ v w h]
  intro a b hab
  have hab' : (Submodule.Quotient.mk (a, 0) : Mo q T A ⧸ N q T τ A) = Submodule.Quotient.mk (b, 0) := hab
  rw [Submodule.Quotient.eq] at hab'
  have := hN hab'
  simpa [φ, sub_eq_zero] using this

end Cons

/- English proof (translation)
Introduce `q _ T τ hl`. Conclude with `⟨Gf q T τ, iota q T τ, iota_inj q T τ hl, sec q T τ, sec_nat q T τ, sec_rel q T τ⟩`.
-/
theorem main : MuTwistQuotientEmbedsInUnitTorsorPresheaf := by
  intro q _ T τ hl
  exact ⟨Gf q T τ, iota q T τ, iota_inj q T τ hl, sec q T τ, sec_nat q T τ, sec_rel q T τ⟩
end LateralTheory.EtaleFoundations.KTP

namespace LateralTheory.EtaleFoundations
/- English proof (translation)
The claim follows from `KTP.main`.
-/
theorem mu_twist_quotient_embeds_in_unit_torsor_presheaf : MuTwistQuotientEmbedsInUnitTorsorPresheaf := KTP.main
end LateralTheory.EtaleFoundations
